From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth.
From cap_machine Require Export cap_lang iris_extra stdpp_extra.
From iris.algebra Require Import frac gmap.


Definition entryR : cmra :=
  (agreeR (leibnizO nat)).

Class entryGpreS Σ := EntryGpreS {
  entryPreG_invPreG : invGpreS Σ;
  entryPreG_rel :: inG Σ entryR;
}.

Class entryGS Σ := EntryGS {
  entryG_rel :: inG Σ entryR;
  γentry : Word -> gname
}.

Definition entryPreΣ :=
  #[ GFunctor entryR ].

Instance subG_entryPreΣ {Σ} :
  subG entryPreΣ Σ →
  invGpreS Σ →
  entryGpreS Σ.
Proof. solve_inG. Qed.

Section ENTRY_defs.
  Context {Σ:gFunctors} {entryg : entryGS Σ}.

  Definition ENTRY_def (w : Word) (n : nat) : iProp Σ :=
    own (γentry w) (to_agree n).
  Definition ENTRY_aux : { x | x = @ENTRY_def }. by eexists. Qed.
  Definition ENTRY := proj1_sig ENTRY_aux.
  Definition ENTRY_eq : @ENTRY = @ENTRY_def := proj2_sig ENTRY_aux.
  Notation "w ↦□ₑ n" :=(ENTRY w n) (at level 20) : bi_scope.

  Lemma entry_agree w n1 n2:
    w ↦□ₑ n1 -∗ w ↦□ₑ n2 -∗ ⌜n1 = n2⌝.
  Proof.
    iIntros "H1 H2".
    rewrite ENTRY_eq /ENTRY_def.
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as "%".
    apply to_agree_op_inv in H.
    done.
  Qed.
  Global Instance persistent_entry w n : Persistent (w ↦□ₑ n)%I.
  Proof.
    rewrite ENTRY_eq /ENTRY_def.
    apply _.
  Defined.


End ENTRY_defs.
Notation "w ↦□ₑ n" :=  (ENTRY w n) (at level 20) : bi_scope.

Section entryPre.
  Context {Σ:gFunctors} {entrypreg : entryGpreS Σ}.


  Lemma entry_rel_init (m : gmap Word nat) :
    ⊢ |==> (∃ γentry, ([∗ map] w↦n ∈ m, own (γentry w) (to_agree n))).
  Proof.

    induction m using map_ind.
    - iModIntro.
      iExists ( λ w, encode w).
      by iApply big_sepM_empty.
    - iMod IHm as (γentry) "IH".
      iMod (own_alloc (A:= entryR) (to_agree x)) as (γx) "Hrel" ; first done.
      iModIntro.
      iExists (λ w, if (bool_decide (w = i)) then γx else γentry w).
      iApply (big_sepM_insert with "[IH Hrel]");auto.
      rewrite bool_decide_eq_true_2; auto; iFrame.
      iApply (big_sepM_mono with "IH").
      iIntros (k n Hk) "H".
      rewrite bool_decide_eq_false_2; [done|].
      by intros ->; rewrite H in Hk.
  Qed.

  Lemma entry_init m :
    ⊢ |==> ∃ (entryg: entryGS Σ), ([∗ map] w↦n ∈ m, w ↦□ₑ n).
  Proof.
    iMod entry_rel_init as (γ) "H".
    iExists (EntryGS _ _ _).
    by rewrite ENTRY_eq /ENTRY_def.
  Qed.

End entryPre.

(* CMRA for Cerise *)
Class ceriseG Σ :=
  CeriseG {
      cerise_invG : invGS Σ;
      mem_gen_memG :: gen_heapGS Addr Word Σ; (* memory *)
      reg_gen_regG :: gen_heapGS RegName Word Σ; (* register *)
      sreg_gen_regG :: gen_heapGS SRegName Word Σ; (* system register *)
      entryG :: entryGS Σ (* entry point *)
    }.

(* invariants for memory, and a state interpretation for (mem,reg) *)
Global Instance memG_irisG `{MachineParameters} `{!ceriseG Σ} : irisGS cap_lang Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ := (((gen_heap_interp (reg σ))
                            ∗ (gen_heap_interp (sreg σ)))
                            ∗ (gen_heap_interp (mem σ)))%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(* Points to predicates for registers *)
Notation "r ↦ᵣ{ q } w" := (pointsto (L:=RegName) (V:=Word) r q w)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  w") : bi_scope.
Notation "r ↦ᵣ w" := (pointsto (L:=RegName) (V:=Word) r (DfracOwn 1) w) (at level 20) : bi_scope.

(* Points to predicates for system registers *)
Notation "sr ↦ₛᵣ{ q } w" := (pointsto (L:=SRegName) (V:=Word) sr q w)
  (at level 20, q at level 50, format "sr  ↦ₛᵣ{ q }  w") : bi_scope.
Notation "sr ↦ₛᵣ w" := (pointsto (L:=SRegName) (V:=Word) sr (DfracOwn 1) w) (at level 20) : bi_scope.

(* Points to predicates for memory *)
Notation "a ↦ₐ{ q } w" := (pointsto (L:=Addr) (V:=Word) a q w)
  (at level 20, q at level 50, format "a  ↦ₐ{ q }  w") : bi_scope.
Notation "a ↦ₐ w" := (pointsto (L:=Addr) (V:=Word) a (DfracOwn 1) w) (at level 20) : bi_scope.

(* --------------------------- LTAC DEFINITIONS ----------------------------------- *)

Ltac inv_base_step :=
  repeat match goal with
         | _ => progress simplify_map_eq/= (* simplify memory stuff *)
         | H : to_val _ = Some _ |- _ => apply of_to_val in H
         | H : _ = of_val ?v |- _ =>
           is_var v; destruct v; first[discriminate H|injection H as H]
         | H : cap_lang.prim_step ?e _ _ _ _ _ |- _ =>
           try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
           (*    and can thus better be avoided. *)
           let φ := fresh "φ" in
           inversion H as [| φ]; subst φ; clear H
         end.

Section cap_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.


  (* Conditionally unify on the read register value *)
  Definition read_reg_inr  (regs : Reg) (r : RegName) p g b e a :=
    match regs !! r with
      | Some (WCap p' g' b' e' a') => WCap p' g' b' e' a' = WCap p g b e a
      | Some _ => True
      | None => False end.

  (* ------------------------- registers points-to --------------------------------- *)

  Lemma regname_dupl_false r w1 w2 :
    r ↦ᵣ w1 -∗ r ↦ᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (pointsto_valid_2 with "Hr1 Hr2") as %?.
    destruct H. eapply dfrac_full_exclusive in H. auto.
  Qed.

  Lemma regname_neq r1 r2 w1 w2 :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst r1. iApply (regname_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_regs_1 (r1: RegName) (w1: Word) :
    r1 ↦ᵣ w1 -∗
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y).
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma regs_of_map_1 (r1: RegName) (w1: Word) :
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y) -∗
    r1 ↦ᵣ w1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma map_of_regs_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: RegName) (w1 w2: Word) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    + by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    + apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r2 ≠ r3 ⌝.
  Proof.
    iIntros "H1 H2 H3".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗ r3 ↦ᵣ w3 -∗ r4 ↦ᵣ w4 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) ∗
     ⌜ r1 ≠ r2 ∧ r1 ≠ r3 ∧ r1 ≠ r4 ∧ r2 ≠ r3 ∧ r2 ≠ r4 ∧ r3 ≠ r4 ⌝.
  Proof.
    iIntros "H1 H2 H3 H4".
    iPoseProof (regname_neq with "H1 H2") as "%".
    iPoseProof (regname_neq with "H1 H3") as "%".
    iPoseProof (regname_neq with "H1 H4") as "%".
    iPoseProof (regname_neq with "H2 H3") as "%".
    iPoseProof (regname_neq with "H2 H4") as "%".
    iPoseProof (regname_neq with "H3 H4") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: Word) :
    r1 ≠ r2 → r1 ≠ r3 → r1 ≠ r4 → r2 ≠ r3 → r2 ≠ r4 → r3 ≠ r4 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> (<[r4:=w4]> ∅)))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3 ∗ r4 ↦ᵣ w4.
  Proof.
    intros. iIntros "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & ? & _)"; iFrame.
  Qed.

  (* ------------------------- system registers points-to --------------------------------- *)

  Lemma sregname_dupl_false (sr : SRegName) (w1 w2 : Word) :
    sr ↦ₛᵣ w1 -∗ sr ↦ₛᵣ w2 -∗ False.
  Proof.
    iIntros "Hr1 Hr2".
    iDestruct (pointsto_valid_2 with "Hr1 Hr2") as %?.
    destruct H. eapply dfrac_full_exclusive in H. auto.
  Qed.

  Lemma sregname_neq (sr1 sr2 : SRegName) (w1 w2 : Word) :
    sr1 ↦ₛᵣ w1 -∗ sr2 ↦ₛᵣ w2 -∗ ⌜ sr1 ≠ sr2 ⌝.
  Proof.
    iIntros "H1 H2" (?). subst sr1. iApply (sregname_dupl_false with "H1 H2").
  Qed.

  Lemma map_of_sregs_1 (sr1: SRegName) (w1: Word) :
    sr1 ↦ₛᵣ w1 -∗
    ([∗ map] k↦y ∈ {[sr1 := w1]}, k ↦ₛᵣ y).
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma sregs_of_map_1 (sr1: SRegName) (w1: Word) :
    ([∗ map] k↦y ∈ {[sr1 := w1]}, k ↦ₛᵣ y) -∗
    sr1 ↦ₛᵣ w1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  (* ------------------------- memory points-to --------------------------------- *)

  Lemma addr_dupl_false a w1 w2 :
    a ↦ₐ w1 -∗ a ↦ₐ w2 -∗ False.
  Proof.
    iIntros "Ha1 Ha2".
    iDestruct (pointsto_valid_2 with "Ha1 Ha2") as %?.
    destruct H. eapply dfrac_full_exclusive in H.
    auto.
  Qed.

  (* -------------- semantic heap + a map of pointsto -------------------------- *)

  Lemma gen_heap_valid_inSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (l : L) (q : Qp) (v : V),
      σ' !! l = Some v →
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', pointsto k (DfracOwn q) y) -∗
      ⌜σ !! l = Some v⌝.
  Proof.
    intros * Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "? [? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inSepM':
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', pointsto k (DfracOwn q) y) -∗
      ⌜forall (l: L) (v: V), σ' !! l = Some v → σ !! l = Some v⌝.
  Proof.
    intros *. iIntros "? Hmap" (l v Hσ').
    rewrite (big_sepM_delete _ σ' l) //. iDestruct "Hmap" as "[? ?]".
    iApply (gen_heap_valid with "[$]"). eauto.
  Qed.

  Lemma gen_heap_valid_inclSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', pointsto k (DfracOwn q) y) -∗
      ⌜σ' ⊆ σ⌝.
  Proof.
    intros *. iIntros "Hσ Hmap".
    iDestruct (gen_heap_valid_inSepM' with "Hσ Hmap") as "#H".
    iDestruct "H" as %Hincl. iPureIntro. intro l.
    unfold option_relation.
    destruct (σ' !! l) eqn:HH'; destruct (σ !! l) eqn:HH; naive_solver.
  Qed.

  Lemma gen_heap_valid_allSepM:
    ∀ (L V : Type) (EqDecision0 : EqDecision L) (H : Countable L)
      (EV: Equiv V) (REV: Reflexive EV) (LEV: @LeibnizEquiv V EV)
      (Σ : gFunctors) (gen_heapG0 : gen_heapGS L V Σ)
      (σ σ' : gmap L V) (q : Qp),
      (forall (l:L), is_Some (σ' !! l)) →
      gen_heap_interp σ -∗
      ([∗ map] k↦y ∈ σ', pointsto k (DfracOwn q) y) -∗
      ⌜ σ = σ' ⌝.
  Proof.
    intros * ? ? * Hσ'. iIntros "A B".
    iAssert (⌜ forall l, σ !! l = σ' !! l ⌝)%I with "[A B]" as %HH.
    { iIntros (l).
      specialize (Hσ' l). unfold is_Some in Hσ'. destruct Hσ' as [v Hσ'].
      rewrite Hσ'.
      eapply (gen_heap_valid_inSepM _ _ _ _ _ _ σ σ') in Hσ'.
      iApply (Hσ' with "[$]"). eauto. }
    iPureIntro. eapply map_leibniz. intro.
    eapply leibniz_equiv_iff. auto.
    Unshelve.
    unfold equiv. unfold Reflexive. intros [ x |].
    { unfold option_equiv. constructor. apply REV. } constructor.
  Qed.

  Lemma gen_heap_update_inSepM :
    ∀ {L V : Type} {EqDecision0 : EqDecision L}
      {H : Countable L} {Σ : gFunctors}
      {gen_heapG0 : gen_heapGS L V Σ}
      (σ σ' : gmap L V) (l : L) (v : V),
      is_Some (σ' !! l) →
      gen_heap_interp σ
      -∗ ([∗ map] k↦y ∈ σ', pointsto k (DfracOwn 1) y)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ [∗ map] k↦y ∈ (<[l:=v]> σ'), pointsto k (DfracOwn 1) y.
  Proof.
    intros * Hσ'. destruct Hσ'.
    rewrite (big_sepM_delete _ σ' l) //. iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]". iModIntro.
    iSplitL "Hh"; eauto.
    rewrite (big_sepM_delete _ (<[l:=v]> σ') l).
    { rewrite delete_insert_delete. iFrame. }
    rewrite lookup_insert //.
  Qed.

  Program Definition wp_lift_atomic_base_step_no_fork_determ {s E Φ} e1 :
    to_val e1 = None →
    (∀ (σ1:cap_lang.state) ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
     ∃ κ e2 (σ2:cap_lang.state) efs, ⌜cap_lang.prim_step e1 σ1 κ e2 σ2 efs⌝ ∗
      (▷ |==> (state_interp σ2 (S ns) κs nt ∗ from_option Φ False (to_val e2))))
      ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns κ κs nt)  "Hσ1 /=".
    iMod ("H" $! σ1 ns κ κs nt with "[Hσ1]") as "H"; auto.
    iDestruct "H" as (κ' e2 σ2 efs) "[H1 H2]".
    iModIntro. iSplit.
    - rewrite /base_reducible /=.
      iExists κ', e2, σ2, efs. auto.
    - iNext. iIntros (? ? ?) "H".
      iDestruct "H" as %Hs1.
      iDestruct "H1" as %Hs2.
      destruct (cap_lang_determ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2) as [Heq1 [Heq2 [Heq3 Heq4]]].
      subst. iMod "H2". iIntros "_".
      iModIntro. iFrame. inv Hs1; auto.
  Qed.

  (* -------------- predicates on memory maps -------------------------- *)

  Lemma extract_sep_if_split a pc_a P Q R:
     (if (a =? pc_a)%a then P else Q ∗ R)%I ≡
     ((if (a =? pc_a)%a then P else Q) ∗
     if (a =? pc_a)%a then emp else R)%I.
  Proof.
    destruct (a =? pc_a)%a; auto.
    iSplit; auto. iIntros "[H1 H2]"; auto.
  Qed.

  Lemma memMap_resource_0  :
        True ⊣⊢ ([∗ map] a↦w ∈ ∅, a ↦ₐ w).
  Proof.
    by rewrite big_sepM_empty.
  Qed.

  Lemma memMap_resource_1 (a : Addr) (w : Word)  :
        a ↦ₐ w  ⊣⊢ ([∗ map] a↦w ∈ <[a:=w]> ∅, a ↦ₐ w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_1_dq (a : Addr) (w : Word) dq :
        a ↦ₐ{dq} w  ⊣⊢ ([∗ map] a↦w ∈ <[a:=w]> ∅, a ↦ₐ{dq} w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite delete_insert; last by auto. rewrite big_sepM_empty.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_2ne (a1 a2 : Addr) (w1 w2 : Word)  :
    a1 ≠ a2 → ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↦ₐ w)%I ⊣⊢ a1 ↦ₐ w1 ∗ a2 ↦ₐ w2.
  Proof.
    intros.
    rewrite big_sepM_delete; last by apply lookup_insert.
    rewrite (big_sepM_delete _ _ a2 w2); rewrite delete_insert; try by rewrite lookup_insert_ne. 2: by rewrite lookup_insert.
    rewrite delete_insert; auto.
    rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iDestruct "HH" as "[H1 [H2 _ ] ]".  iFrame.
    - iDestruct "HH" as "[H1 H2]". iFrame.
  Qed.

  Lemma address_neq a1 a2 w1 w2 :
    a1 ↦ₐ w1 -∗ a2 ↦ₐ w2 -∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "Ha1 Ha2".
    destruct (finz_eq_dec a1 a2); auto. subst.
    iExFalso. iApply (addr_dupl_false with "[$Ha1] [$Ha2]").
  Qed.

  Lemma big_sepL2_disjoint_pointsto (la1 : list Addr) (lw1 : list Word)
    (a : Addr) (w : Word) :
    ⊢ ([∗ list] a1;w1 ∈ la1;lw1, a1 ↦ₐ w1) ∗ a ↦ₐ w -∗ ⌜ a ∉ la1 ⌝.
  Proof.
    generalize dependent lw1.
    induction la1 as [|a1 la1]; iIntros (lw1) "[Hla1 Ha]".
    - iPureIntro ; set_solver.
    - destruct lw1; first done.
      rewrite big_sepL2_cons.
      iDestruct "Hla1" as "[Ha1 Hla1]".
      iDestruct (address_neq with "[$] [$]") as "%".
      rewrite not_elem_of_cons.
      iSplit ; first done.
      iApply IHla1; last iFrame.
  Qed.

  Lemma big_sepL2_nodup (la : list Addr) (lw : list Word):
    ⊢ ([∗ list] a;w ∈ la;lw, a ↦ₐ w) -∗ ⌜NoDup la ⌝.
  Proof.
    generalize dependent lw.
    induction la as [|a la]; iIntros (lw) "Hla".
    - iPureIntro ; by apply NoDup_nil.
    - destruct lw; first done.
      rewrite big_sepL2_cons.
      iDestruct "Hla" as "[Ha Hla]".
      iDestruct (big_sepL2_disjoint_pointsto with "[$]") as "%Hnotin".
      iDestruct (IHla with "[$]") as "%Hnodup".
      rewrite NoDup_cons.
      iSplit ; done.
  Qed.


  Lemma big_sepL2_disjoint (la1 la2 : list Addr) (lw1 lw2 : list Word) :
    ⊢ ([∗ list] a1;w1 ∈ la1;lw1, a1 ↦ₐ w1) ∗ ([∗ list] a2;w2 ∈ la2;lw2, a2 ↦ₐ w2) -∗ ⌜ la1 ## la2 ⌝.
  Proof.
    generalize dependent lw2.
    induction la2 as [|a2 la2]; iIntros (lw2) "[Hla1 Hla2]".
    - iPureIntro ; set_solver.
    - destruct lw2; first done.
      rewrite big_sepL2_cons.
      iDestruct "Hla2" as "[Ha2 Hla2]".
      iDestruct (big_sepL2_disjoint_pointsto with "[$Hla1 $Ha2]") as "%Ha_l1".
      rewrite /disjoint /set_disjoint_instance.
      iIntros (a Ha Ha').
      iDestruct (IHla2 with "[$Hla1 $Hla2]") as "%Hla_disjoint"; auto.
      exfalso.
      apply elem_of_cons in Ha'.
      destruct Ha' as [->|Ha']; first congruence.
      by apply Hla_disjoint in Ha.
  Qed.



  Lemma memMap_resource_2ne_apply (a1 a2 : Addr) (w1 w2 : Word)  :
    a1 ↦ₐ w1 -∗ a2 ↦ₐ w2 -∗ ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↦ₐ w) ∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "Hi Hr2a".
    iDestruct (address_neq  with "Hi Hr2a") as %Hne; auto.
    iSplitL; last by auto.
    iApply memMap_resource_2ne; auto. iSplitL "Hi"; auto.
  Qed.

  Lemma memMap_resource_2gen (a1 a2 : Addr) (w1 w2 : Word)  :
    ( ∃ mem, ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∧
       ⌜ if  (a2 =? a1)%a
       then mem =  (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)⌝
    )%I ⊣⊢ (a1 ↦ₐ w1 ∗ if (a2 =? a1)%a then emp else a2 ↦ₐ w2) .
  Proof.
    destruct (a2 =? a1)%a eqn:Heq.
    - apply Z.eqb_eq, finz_to_z_eq in Heq. rewrite memMap_resource_1.
      iSplit.
      * iDestruct 1 as (mem) "[HH ->]".  by iSplit.
      * iDestruct 1 as "[Hmap _]". iExists (<[a1:=w1]> ∅); iSplitL; auto.
    - apply Z.eqb_neq in Heq.
      rewrite -memMap_resource_2ne; auto. 2 : congruence.
      iSplit.
      * iDestruct 1 as (mem) "[HH ->]". done.
      * iDestruct 1 as "Hmap". iExists (<[a1:=w1]> (<[a2:=w2]> ∅)); iSplitL; auto.
  Qed.

  Lemma memMap_resource_2gen_d (Φ : Addr → Word → iProp Σ) (a1 a2 : Addr) (w1 w2 : Word)  :
    ( ∃ mem, ([∗ map] a↦w ∈ mem, Φ a w) ∧
       ⌜ if  (a2 =? a1)%a
       then mem =  (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)⌝
    ) -∗ (Φ a1 w1 ∗ if (a2 =? a1)%a then emp else Φ a2 w2) .
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (mem) "[Hmem Hif]".
    destruct ((a2 =? a1)%a) eqn:Heq.
    - iDestruct "Hif" as %->.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne;auto. apply Z.eqb_neq in Heq. solve_addr. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.

  Lemma memMap_resource_2gen_d_dq (Φ : Addr → dfrac → Word → iProp Σ) (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : Word)  :
    ( ∃ mem dfracs, ([∗ map] a↦wq ∈ prod_merge dfracs mem, Φ a wq.1 wq.2) ∧
       ⌜ (if  (a2 =? a1)%a
       then mem =  (<[a1:=w1]> ∅)
          else mem = <[a1:=w1]> (<[a2:=w2]> ∅)) ∧
       (if  (a2 =? a1)%a
       then dfracs = (<[a1:=dq1]> ∅)
       else dfracs = <[a1:=dq1]> (<[a2:=dq2]> ∅))⌝
    ) -∗ (Φ a1 dq1 w1 ∗ if (a2 =? a1)%a then emp else Φ a2 dq2 w2) .
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (mem dfracs) "[Hmem [Hif Hif'] ]".
    destruct ((a2 =? a1)%a) eqn:Heq.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1));auto. rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1));auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,w2));auto.
      rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne;auto. apply Z.eqb_neq in Heq. solve_addr. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.


  (* Not the world's most beautiful lemma, but it does avoid us having to fiddle around with a later under an if in proofs *)
  Lemma memMap_resource_2gen_clater (a1 a2 : Addr) (w1 w2 : Word) (Φ : Addr -> Word -> iProp Σ)  :
    (▷ Φ a1 w1) -∗
    (if (a2 =? a1)%a then emp else ▷ Φ a2 w2) -∗
    (∃ mem, ▷ ([∗ map] a↦w ∈ mem, Φ a w) ∗
       ⌜if  (a2 =? a1)%a
       then mem =  (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)⌝
    )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (a2 =? a1)%a eqn:Heq.
    - iExists (<[a1:= w1]> ∅); iSplitL; auto. iNext. iApply big_sepM_insert;[|by iFrame].
      auto.
    - iExists (<[a1:=w1]> (<[a2:=w2]> ∅)); iSplitL; auto.
      iNext.
      iApply big_sepM_insert;[|iFrame].
      { apply Z.eqb_neq in Heq. rewrite lookup_insert_ne//. congruence. }
      iApply big_sepM_insert;[|by iFrame]. auto.
  Qed.

  Lemma memMap_resource_2gen_clater_dq (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : Word) (Φ : Addr -> dfrac → Word -> iProp Σ)  :
    (▷ Φ a1 dq1 w1) -∗
    (if (a2 =? a1)%a then emp else ▷ Φ a2 dq2 w2) -∗
    (∃ mem dfracs, ▷ ([∗ map] a↦wq ∈ prod_merge dfracs mem, Φ a wq.1 wq.2) ∗
       ⌜(if  (a2 =? a1)%a
       then mem = (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)) ∧
       (if  (a2 =? a1)%a
       then dfracs = (<[a1:=dq1]> ∅)
       else dfracs = <[a1:=dq1]> (<[a2:=dq2]> ∅))⌝
    )%I.
  Proof.
    iIntros "Hc1 Hc2".
    destruct (a2 =? a1)%a eqn:Heq.
    - iExists (<[a1:= w1]> ∅),(<[a1:= dq1]> ∅); iSplitL; auto. iNext.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1));auto. rewrite merge_empty.
      iApply big_sepM_insert;[|by iFrame].
      auto.
    - iExists (<[a1:=w1]> (<[a2:=w2]> ∅)),(<[a1:=dq1]> (<[a2:=dq2]> ∅)); iSplitL; auto.
      iNext.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1));auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,w2));auto.
      rewrite merge_empty.
      iApply big_sepM_insert;[|iFrame].
      { apply Z.eqb_neq in Heq. rewrite lookup_insert_ne//. congruence. }
      iApply big_sepM_insert;[|by iFrame]. auto.
  Qed.

  Lemma memMap_delete:
    ∀(a : Addr) (w : Word) mem0,
      mem0 !! a = Some w →
      ([∗ map] a↦w ∈ mem0, a ↦ₐ w) ⊣⊢ (a ↦ₐ w ∗ ([∗ map] k↦y ∈ delete a mem0, k ↦ₐ y)).
  Proof.
    intros a w mem0 Hmem0a.
    rewrite -(big_sepM_delete _ _ a); auto.
  Qed.

  Lemma mem_remove_dq mem dq :
    ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ⊣⊢
    ([∗ map] a↦dw ∈ (prod_merge (create_gmap_default (elements (dom mem)) dq) mem), a ↦ₐ{dw.1} dw.2).
  Proof.
    iInduction (mem) as [|a k mem] "IH" using map_ind.
    - rewrite big_sepM_empty dom_empty_L elements_empty
              /= /prod_merge merge_empty big_sepM_empty. done.
    - rewrite dom_insert_L.
      assert (elements ({[a]} ∪ dom mem) ≡ₚ a :: elements (dom mem)) as Hperm.
      { apply elements_union_singleton. apply not_elem_of_dom. auto. }
      apply (create_gmap_default_permutation _ _ dq) in Hperm. rewrite Hperm /=.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq,k)) //.
      iSplit.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        iApply big_sepM_insert.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom mem)) dq !! a);auto; rewrite H;auto. }
        iFrame. iApply "IH". iFrame.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]";auto.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom mem)) dq !! a);auto; rewrite H;auto. }
        iApply big_sepM_insert; auto.
        iFrame. iApply "IH". iFrame.
  Qed.

  Lemma gen_mem_valid_inSepM:
    ∀ mem0 (m : Mem) (a : Addr) (w : Word),
      mem0 !! a = Some w →
      gen_heap_interp m
                   -∗ ([∗ map] a↦w ∈ mem0, a ↦ₐ w)
                   -∗ ⌜m !! a = Some w⌝.
  Proof.
    iIntros (mem0 m a w Hmem_pc) "Hm Hmem".
    iDestruct (memMap_delete a with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto.
  Qed.

  (* a more general version of load to work also with any fraction and persistent points tos *)
  Lemma gen_mem_valid_inSepM_general:
    ∀ mem0 (m : Mem) (a : Addr) (w : Word) dq,
      mem0 !! a = Some (dq,w) →
      gen_heap_interp m
                   -∗ ([∗ map] a↦dqw ∈ mem0, pointsto a dqw.1 dqw.2)
                   -∗ ⌜m !! a = Some w⌝.
  Proof.
    iIntros (mem0 m a w dq Hmem_pc) "Hm Hmem".
    iDestruct (big_sepM_delete _ _ a with "Hmem") as "[Hpc_a Hmem]"; eauto.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %?; auto.
  Qed.

  Lemma gen_mem_update_inSepM :
    ∀ {Σ : gFunctors} {gen_heapG0 : gen_heapGS Addr Word Σ}
      (σ : gmap Addr Word) mem0 (l : Addr) (v' v : Word),
      mem0 !! l = Some v' →
      gen_heap_interp σ
      -∗ ([∗ map] a↦w ∈ mem0, a ↦ₐ w)
      ==∗ gen_heap_interp (<[l:=v]> σ)
          ∗ ([∗ map] a↦w ∈ <[l:=v]> mem0, a ↦ₐ w).
  Proof.
    intros.
    rewrite (big_sepM_delete _ _ l);[|eauto].
    iIntros "Hh [Hl Hmap]".
    iMod (gen_heap_update with "Hh Hl") as "[Hh Hl]"; eauto.
    iModIntro.
    iSplitL "Hh"; eauto.
    iDestruct (big_sepM_insert _ _ l with "[$Hmap $Hl]") as "H".
    { apply lookup_delete. }
    rewrite insert_delete_insert. iFrame.
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)
  (* Bind Scope expr_scope with language.expr cap_lang. *)

  Lemma wp_notCorrectPC:
    forall E w,
      ~ isCorrectPC w ->
      {{{ PC ↦ᵣ w }}}
         Instr Executable @ E
        {{{ RET FailedV; PC ↦ᵣ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "Hσ1 /="; destruct σ1; simpl;
    iDestruct "Hσ1" as "[ [Hr Hsr] Hm ]".
    iDestruct (@gen_heap_valid with "Hr HPC") as %?.
    iApply fupd_frame_l.
    iSplit; first (by iPureIntro; apply normal_always_base_reducible).
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn. by iApply "Hϕ".
  Qed.

  (* Subcases for respectively permissions and bounds *)

  Lemma wp_notCorrectPC_perm E pc_p pc_g pc_b pc_e pc_a :
    executeAllowed pc_p = false ->
    {{{ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");
      [apply not_isCorrectPC_perm;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  Lemma wp_notCorrectPC_range E pc_p pc_g pc_b pc_e pc_a :
       ¬ (pc_b <= pc_a < pc_e)%a →
      {{{ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a}}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC with "[HPC]");
      [apply not_isCorrectPC_bounds;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a w :
    decodeInstrW w = Halt →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "Hσ1 /=" ; destruct σ1 as [ [regs sregs] mem] ; cbn.
    iDestruct "Hσ1" as "[ [Hr Hsr] Hm ]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn. iApply "Hφ"; iFrame.
  Qed.

  Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a w :
    decodeInstrW w = Fail →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "Hσ1 /=" ; destruct σ1 as [ [regs sregs] mem] ; cbn.
    iDestruct "Hσ1" as "[ [Hr Hsr] Hm ]".
    iDestruct (@gen_heap_valid with "Hr Hpc") as %?.
    iDestruct (@gen_heap_valid with "Hm Hpca") as %?.
    iModIntro.
    iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iIntros (e2 σ2 efs Hstep).
    eapply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_exec_inv in Hstep; eauto. cbn in Hstep. simplify_eq.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iFrame. cbn. iApply "Hφ"; iFrame.
   Qed.

  (* ----------------------------------- PURE RULES ---------------------------------- *)

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  Local Ltac solve_exec_pure := intros ?; apply nsteps_once, pure_base_step_pure_step;
                                constructor; [solve_exec_safe|]; intros;
                                (match goal with
                                | H : base_step _ _ _ _ _ _ |- _ => inversion H end).

  Global Instance pure_seq_failed :
    PureExec True 1 (Seq (Instr Failed)) (Instr Failed).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_halted :
    PureExec True 1 (Seq (Instr Halted)) (Instr Halted).
  Proof. by solve_exec_pure. Qed.

  Global Instance pure_seq_done :
    PureExec True 1 (Seq (Instr NextI)) (Seq (Instr Executable)).
  Proof. by solve_exec_pure. Qed.

End cap_lang_rules.

(* Used to close the failing cases of the ftlr.
  - Hcont is the (iris) name of the closing hypothesis (usually "Hφ")
  - fail_case_name is one constructor of the spec_name,
    indicating the appropriate error case
 *)
Ltac iFailCore fail_case_name :=
      iPureIntro;
      econstructor; eauto;
      eapply fail_case_name ; eauto.

Ltac iFailWP Hcont fail_case_name :=
  by (cbn; iFrame; iApply Hcont; iFrame; iFailCore fail_case_name).

(* ----------------- useful definitions to factor out the wp specs ---------------- *)

(*--- register equality ---*)
  Lemma addr_ne_reg_ne {regs : leibnizO Reg} {r1 r2 : RegName}
        {p0 g0 b0 e0 a0 p g b e a}:
    regs !! r1 = Some (WCap p0 g0 b0 e0 a0)
    → regs !! r2 = Some (WCap p g b e a)
    → a0 ≠ a → r1 ≠ r2.
  Proof.
    intros Hr1 Hr2 Hne.
    destruct (decide (r1 = r2)); simplify_eq; auto.
  Qed.

(*--- regs_of ---*)

Definition regs_of_argument (arg: Z + RegName): gset RegName :=
  match arg with
  | inl _ => ∅
  | inr r => {[ r ]}
  end.

Definition regs_of (i: instr): gset RegName :=
  match i with
  | Lea r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | GetP r1 r2 => {[ r1; r2 ]}
  | GetB r1 r2 => {[ r1; r2 ]}
  | GetE r1 r2 => {[ r1; r2 ]}
  | GetA r1 r2 => {[ r1; r2 ]}
  | GetL r1 r2 => {[ r1; r2 ]}
  | GetOType dst src => {[ dst; src ]}
  | GetWType dst src => {[ dst; src ]}
  | machine_base.Add r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Sub r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Mul r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | LAnd r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | LOr r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | LShiftL r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | LShiftR r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Lt r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Mov r arg => {[ r ]} ∪ regs_of_argument arg
  | Restrict r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Subseg r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
  | Load r1 r2 => {[ r1; r2 ]}
  | Store r1 arg => {[ r1 ]} ∪ regs_of_argument arg
  | Jnz arg1 r2 => {[ r2 ]} ∪ regs_of_argument arg1
  | Jmp arg => regs_of_argument arg
  | Jalr rdst rsrc => {[ rdst; rsrc ]}
  | Seal dst r1 r2 => {[dst; r1; r2]}
  | UnSeal dst r1 r2 => {[dst; r1; r2]}
  | ReadSR dst _ => {[ dst ]}
  | WriteSR _ src => {[ src ]}
  | _ => ∅
  end.

Lemma indom_regs_incl D (regs regs': Reg) :
  D ⊆ dom regs →
  regs ⊆ regs' →
  ∀ r, r ∈ D →
       ∃ (w:Word), (regs !! r = Some w) ∧ (regs' !! r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (regs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset RegName); first typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
Qed.

Definition sregs_of (i: instr): gset SRegName :=
  match i with
  | ReadSR _ src => {[ src ]}
  | WriteSR dst _ => {[ dst ]}
  | _ => ∅
  end.

Lemma indom_sregs_incl D (sregs sregs': SReg) :
  D ⊆ dom sregs →
  sregs ⊆ sregs' →
  ∀ sr, sr ∈ D →
       ∃ (w:Word), (sregs !! sr = Some w) ∧ (sregs' !! sr = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (sregs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset SRegName); first typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
Qed.

(*--- incrementPC ---*)

Definition incrementPC_gen (regs: Reg) (n : Z) : option Reg :=
  match regs !! PC with
  | Some (WCap p g b e a) =>
    match (a + n)%a with
    | Some a' => Some (<[ PC := WCap p g b e a' ]> regs)
    | None => None
    end
  | _ => None
  end.

Definition incrementPC (regs: Reg) : option Reg := incrementPC_gen regs 1.

Lemma incrementPC_gen_Some_inv regs regs' n :
  incrementPC_gen regs n = Some regs' ->
  exists p g b e a a',
    regs !! PC = Some (WCap p g b e a) ∧
    (a + n)%a = Some a' ∧
    regs' = <[ PC := WCap p g b e a' ]> regs.
Proof.
  unfold incrementPC_gen.
  destruct (regs !! PC) ; try congruence.
  destruct_word w;try congruence.
  case_eq (a+n)%a; try congruence. intros ? ?. inversion 1.
  do 6 eexists. split; eauto.
Qed.
Lemma incrementPC_Some_inv regs regs' :
  incrementPC regs = Some regs' ->
  exists p g b e a a',
    regs !! PC = Some (WCap p g b e a) ∧
    (a + 1)%a = Some a' ∧
    regs' = <[ PC := WCap p g  b e a' ]> regs.
Proof. apply incrementPC_gen_Some_inv. Qed.

Lemma incrementPC_gen_None_inv regs p g b e a n :
  incrementPC_gen regs n = None ->
  regs !! PC = Some (WCap p g b e a) ->
  (a + n)%a = None.
Proof.
  unfold incrementPC_gen.
  destruct (regs !! PC) ; try congruence.
  destruct_word w;try congruence.
  case_eq (a0+n)%a; try congruence.
Qed.
Lemma incrementPC_None_inv regs p g b e a :
  incrementPC regs = None ->
  regs !! PC = Some (WCap p g b e a) ->
  (a + 1)%a = None.
Proof. apply incrementPC_gen_None_inv. Qed.

Lemma incrementPC_gen_overflow_mono regs regs' n :
  incrementPC_gen regs n = None →
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  incrementPC_gen regs' n = None.
Proof.
  intros Hi HPC Hincl. unfold incrementPC_gen in *. destruct HPC as [c HPC].
  pose proof (lookup_weaken _ _ _ _ HPC Hincl) as HPC'.
  rewrite HPC HPC' in Hi |- *. destruct c as [| [? ? ? ? aa | ] | | ]; auto.
  destruct (aa+n)%a; last by auto. congruence.
Qed.
Lemma incrementPC_overflow_mono regs regs' :
  incrementPC regs = None →
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  incrementPC regs' = None.
Proof. apply incrementPC_gen_overflow_mono. Qed.

Lemma incrementPC_gen_fail_updatePC_gen regs sregs m n :
   incrementPC_gen regs n = None ->
   updatePC_gen (regs, sregs, m) n = None.
Proof.
   rewrite /incrementPC_gen /updatePC_gen /=; cbn.
   destruct (regs !! PC) as [X|]; auto.
   destruct X as [| [? ? ? ? a' | ] | |]; auto.
   destruct (a' + n)%a; auto. congruence.
Qed.
Lemma incrementPC_fail_updatePC regs sregs m :
   incrementPC regs = None ->
   updatePC (regs, sregs, m) = None.
Proof. apply incrementPC_gen_fail_updatePC_gen. Qed.

Lemma incrementPC_gen_success_updatePC_gen regs sregs m regs' n :
  incrementPC_gen regs n = Some regs' ->
  ∃ p g b e a a',
    regs !! PC = Some (WCap p g b e a) ∧
    (a + n)%a = Some a' ∧
    updatePC_gen (regs, sregs, m) n = Some (NextI, (<[ PC := WCap p g b e a' ]> regs, sregs, m)) ∧
    regs' = <[ PC := WCap p g b e a' ]> regs.
Proof.
  rewrite /incrementPC_gen /updatePC_gen /update_reg /=; cbn.
  destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
  destruct X as [| [? ? ? ? a'|]| |] eqn:?; try congruence; [].
  destruct (a' + n)%a eqn:?; [| congruence]. inversion 1; subst regs'.
  do 6 eexists. repeat split; auto.
Qed.
Lemma incrementPC_success_updatePC regs sregs m regs' :
  incrementPC regs = Some regs' ->
  ∃ p g b e a a',
    regs !! PC = Some (WCap p g b e a) ∧
    (a + 1)%a = Some a' ∧
    updatePC (regs, sregs, m) = Some (NextI, (<[ PC := WCap p g b e a' ]> regs, sregs, m)) ∧
    regs' = <[ PC := WCap p g b e a' ]> regs.
Proof. apply incrementPC_gen_success_updatePC_gen. Qed.

Lemma updatePC_gen_success_incl m m' regs regs' sregs sregs' w n :
  regs ⊆ regs' →
  updatePC_gen (regs, sregs, m) n = Some (NextI, (<[ PC := w ]> regs, sregs, m)) →
  updatePC_gen (regs', sregs', m') n = Some (NextI, (<[ PC := w ]> regs', sregs', m')).
Proof.
  intros * Hincl Hu. rewrite /updatePC_gen /= in Hu |- *.
  cbn in *.
  destruct (regs !! PC) as [ w1 |] eqn:Hrr.
  { pose proof (lookup_weaken _ _ _ _ Hrr Hincl) as Hregs'. rewrite Hregs'.
    destruct w1 as [|[ ? ? ? ? a1|] | | ]; simplify_eq.
    destruct (a1 + n)%a eqn:Ha1; simplify_eq. rewrite /update_reg /=.
    f_equal. f_equal.
    assert (HH: forall (reg1 reg2:Reg), reg1 = reg2 -> reg1 !! PC = reg2 !! PC)
      by (intros * ->; auto).
    apply HH in Hu. rewrite !lookup_insert in Hu. by simplify_eq. }
  {  inversion Hu. }
Qed.

Lemma updatePC_success_incl m m' regs regs' sregs sregs' w :
  regs ⊆ regs' →
  updatePC (regs, sregs, m) = Some (NextI, (<[ PC := w ]> regs, sregs, m)) →
  updatePC (regs', sregs', m') = Some (NextI, (<[ PC := w ]> regs', sregs', m')).
Proof. apply updatePC_gen_success_incl. Qed.

Lemma updatePC_gen_fail_incl m m' regs regs' sregs sregs' n :
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  updatePC_gen (regs, sregs, m) n = None →
  updatePC_gen (regs', sregs', m') n = None.
Proof.
  intros [w HPC] Hincl Hfail. rewrite /updatePC_gen /= in Hfail |- *.
  cbn in *.
  rewrite !HPC in Hfail. have -> := lookup_weaken _ _ _ _ HPC Hincl.
  destruct w as [| [? ? ? ? a1 | ]| |]; simplify_eq; auto;[].
  destruct (a1 + n)%a; simplify_eq; auto.
Qed.

Lemma updatePC_fail_incl m m' regs regs' sregs sregs' :
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  updatePC (regs, sregs, m) = None →
  updatePC (regs', sregs', m') = None.
Proof. apply updatePC_gen_fail_incl. Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H
  end; simplify_eq.

Tactic Notation "incrementPC_inv" "as" simple_intropattern(pat):=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as pat
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H
  | H : incrementPC_gen _ _ = Some _ |- _ =>
    apply incrementPC_gen_Some_inv in H as pat
  | H : incrementPC_gen _ _ = None |- _ =>
    eapply incrementPC_gen_None_inv in H
  end; simplify_eq.
