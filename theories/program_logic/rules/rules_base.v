From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants na_invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap.
From griotte Require Export iris_extra stdpp_extra griotte_lang.
From griotte Require Export machine_base cerise_instance register_file machine_instructions.

(* --------------------------- LTAC DEFINITIONS ----------------------------------- *)

Ltac inv_base_step :=
  repeat match goal with
         | _ => progress simplify_map_eq/= (* simplify memory stuff *)
         | H : to_val _ = Some _ |- _ => apply of_to_val in H
         | H : _ = of_val ?v |- _ =>
           is_var v; destruct v; first[discriminate H|injection H as H]
         | H : griotte_lang.prim_step ?e _ _ _ _ _ |- _ =>
           try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
           (*    and can thus better be avoided. *)
           let φ := fresh "φ" in
           inversion H as [| φ]; subst φ; clear H
         end.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.


  (* Conditionally unify on the read register value *)
  Definition read_reg_inr  (regs : LReg) (r : RegName) (t : bool) p g b e a :=
    match regs !! r with
      | Some (WCap t' p' g' b' e' a' @@? _) => WCap t' p' g' b' e' a' = WCap t p g b e a
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

  Lemma map_of_regs_1 (r1: RegName) (w1: LWord) :
    r1 ↦ᵣ w1 -∗
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y).
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma regs_of_map_1 (r1: RegName) (w1: LWord) :
    ([∗ map] k↦y ∈ {[r1 := w1]}, k ↦ᵣ y) -∗
    r1 ↦ᵣ w1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma map_of_regs_2 (r1 r2: RegName) (w1 w2: LWord) :
    r1 ↦ᵣ w1 -∗ r2 ↦ᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) ∗ ⌜ r1 ≠ r2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (regname_neq with "H1 H2") as "%".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma regs_of_map_2 (r1 r2: RegName) (w1 w2: LWord) :
    r1 ≠ r2 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> ∅)), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2.
  Proof.
    iIntros (?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    + by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    + apply lookup_insert_None; split; eauto.
  Qed.

  Lemma map_of_regs_3 (r1 r2 r3: RegName) (w1 w2 w3: LWord) :
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

  Lemma regs_of_map_3 (r1 r2 r3: RegName) (w1 w2 w3: LWord) :
    r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
    ([∗ map] k↦y ∈ (<[r1:=w1]> (<[r2:=w2]> (<[r3:=w3]> ∅))), k ↦ᵣ y) -∗
    r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ r3 ↦ᵣ w3.
  Proof.
    iIntros (? ? ?) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; simplify_map_eq; eauto.
    iDestruct "Hmap" as "(? & ? & ? & _)"; iFrame.
  Qed.

  Lemma map_of_regs_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: LWord) :
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

  Lemma regs_of_map_4 (r1 r2 r3 r4: RegName) (w1 w2 w3 w4: LWord) :
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
    { rewrite delete_insert_eq. iFrame. }
    rewrite lookup_insert_eq //.
  Qed.

  Program Definition wp_lift_atomic_base_step_no_fork_determ {s E Φ} e1 :
    to_val e1 = None →
    (∀ (σ1:griotte_lang.state) ns κ κs nt, state_interp σ1 ns (κ ++ κs) nt ={E}=∗
     ∃ κ e2 (σ2:griotte_lang.state) efs, ⌜griotte_lang.prim_step e1 σ1 κ e2 σ2 efs⌝ ∗
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
      destruct (griotte_lang_determ _ _ _ _ _ _ _ _ _ _ Hs1 Hs2) as [Heq1 [Heq2 [Heq3 Heq4]]].
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

  Lemma memMap_resource_1 (a : Addr) (w : LWord)  :
        a ↦ₐ w  ⊣⊢ ([∗ map] a↦w ∈ <[a:=w]> ∅, a ↦ₐ w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert_eq.
    rewrite delete_insert_id; last by auto. rewrite -memMap_resource_0.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_1_dq (a : Addr) (w : LWord) dq :
        a ↦ₐ{dq} w  ⊣⊢ ([∗ map] a↦w ∈ <[a:=w]> ∅, a ↦ₐ{dq} w)%I.
  Proof.
    rewrite big_sepM_delete; last by apply lookup_insert_eq.
    rewrite delete_insert_id; last by auto. rewrite big_sepM_empty.
    iSplit; iIntros "HH".
    - iFrame.
    - by iDestruct "HH" as "[HH _]".
  Qed.

  Lemma memMap_resource_2ne (a1 a2 : Addr) (w1 w2 : LWord)  :
    a1 ≠ a2 → ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↦ₐ w)%I ⊣⊢ a1 ↦ₐ w1 ∗ a2 ↦ₐ w2.
  Proof.
    intros.
    rewrite big_sepM_delete; last by apply lookup_insert_eq.
    rewrite (big_sepM_delete _ _ a2 w2); rewrite delete_insert_id; try by rewrite lookup_insert_ne. 2: by rewrite lookup_insert_eq.
    rewrite delete_insert_id; auto.
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

  Lemma big_sepL2_disjoint_pointsto (la1 : list Addr) (lw1 : list LWord)
    (a : Addr) (w : LWord) :
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

  Lemma big_sepL2_nodup (la : list Addr) (lws : list LWord):
    ⊢ ([∗ list] a;w ∈ la;lws, a ↦ₐ w) -∗ ⌜NoDup la ⌝.
  Proof.
    generalize dependent lws.
    induction la as [|a la]; iIntros (lws) "Hla".
    - iPureIntro ; by apply NoDup_nil.
    - destruct lws; first done.
      rewrite big_sepL2_cons.
      iDestruct "Hla" as "[Ha Hla]".
      iDestruct (big_sepL2_disjoint_pointsto with "[$]") as "%Hnotin".
      iDestruct (IHla with "[$]") as "%Hnodup".
      rewrite NoDup_cons.
      iSplit ; done.
  Qed.


  Lemma big_sepL2_disjoint (la1 la2 : list Addr) (lw1 lw2 : list LWord) :
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



  Lemma memMap_resource_2ne_apply (a1 a2 : Addr) (w1 w2 : LWord)  :
    a1 ↦ₐ w1 -∗ a2 ↦ₐ w2 -∗ ([∗ map] a↦w ∈  <[a1:=w1]> (<[a2:=w2]> ∅), a ↦ₐ w) ∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "Hi Hr2a".
    iDestruct (address_neq  with "Hi Hr2a") as %Hne; auto.
    iSplitL; last by auto.
    iApply memMap_resource_2ne; auto. iSplitL "Hi"; auto.
  Qed.

  Lemma memMap_resource_2gen (a1 a2 : Addr) (w1 w2 : LWord)  :
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

  Lemma memMap_resource_2gen_d (Φ : Addr → LWord → iProp Σ) (a1 a2 : Addr) (w1 w2 : LWord)  :
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

  Lemma memMap_resource_2gen_d_dq (Φ : Addr → dfrac → LWord → iProp Σ) (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : LWord)  :
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
  Lemma memMap_resource_2gen_clater (a1 a2 : Addr) (w1 w2 : LWord) (Φ : Addr -> LWord -> iProp Σ)  :
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

  Lemma memMap_resource_2gen_clater_dq (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : LWord) (Φ : Addr -> dfrac → LWord -> iProp Σ)  :
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
    ∀(a : Addr) (w : LWord) mem0,
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
    ∀ mem0 (m : LMem) (a : Addr) (w : LWord),
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
    ∀ mem0 (m : LMem) (a : Addr) (w : LWord) dq,
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
    ∀ {Σ : gFunctors} {gen_heapG0 : gen_heapGS Addr LWord Σ}
      (σ : gmap Addr LWord) mem0 (l : Addr) (v' v : LWord),
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
    { apply lookup_delete_eq. }
    rewrite insert_delete_eq. iFrame.
  Qed.

  (* ------------------------- the state interpretation --------------------------- *)

  Lemma PC_not_cnull : PC ≠ cnull.
  Proof. done. Qed.

  (** The common start of every instruction rule: the logical PC and the
      instruction word give the physical ones, and the instruction is decoded
      from the physical copy. The continuation closes the state
      interpretation after the physical step. *)
  Lemma wp_instr_step E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (lreg : LReg) (lmem : LMem)
       (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag) (σ' : ExecConf),
       ⌜erasure R C (r, sr, m, st) lreg lmem⌝ -∗
       ⌜regs ⊆ lreg⌝ -∗
       ⌜lregs_erase regs ⊆ r⌝ -∗
       ⌜lmem !! pc_a = Some w⌝ -∗
       ⌜exec (decodeInstrW w.(lw)) pc_p (r, sr, m, st) = (c, σ')⌝ -∗
       gen_heap_interp lreg -∗ gen_heap_interp sr -∗ gen_heap_interp lmem -∗
       gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
       pc_a ↦ₐ{dq} w -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ==∗
       cerise_state_interp σ' ∗ from_option Φ False (to_val (Instr c)))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc HPC) "Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ /=". destruct σ1 as [[[r sr] m] st]; cbn.
    iDestruct "Hσ" as (lreg lmem R C) "(Hr & Hsr & Hm & Hst & HR & HC & %Her)".
    iMod "Hpc_a". iMod "Hmap".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %Hpc_a.
    pose proof (erasure_regs_incl _ _ _ _ _ _ Her Hregs) as Hregs'.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ Her Hpc_a) as (pw & Hpw & Hok).
    assert (r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a)) as HPCr.
    { eapply lookup_weaken; last exact Hregs'. by rewrite lookup_lregs_erase HPC. }
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; first done.
    eapply step_exec_inv in Hstep; eauto; cbn in Hstep.
    rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hstep.
    iApply ("Hcont" with "[//] [//] [//] [//] [//] Hr Hsr Hm Hst HR HC Hpc_a Hmap").
  Qed.

  (** Updates of the state interpretation that ride on any instruction step:
      ghost steps that need the registry or the claims authority. *)
  Lemma wp_si_update E e Φ P Q :
    to_val e = None →
    (∀ σ, cerise_state_interp σ -∗ P ==∗ cerise_state_interp σ ∗ Q) →
    P -∗ (Q -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hupd) "HP Hwp". rewrite !wp_unfold /wp_pre /= He.
    iIntros (σ ns κ κs nt) "Hσ".
    iMod (Hupd with "Hσ HP") as "[Hσ HQ]".
    iSpecialize ("Hwp" with "HQ").
    iApply ("Hwp" $! σ ns κ κs nt with "Hσ").
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)
  (* Bind Scope expr_scope with language.expr griotte_lang. *)

  Lemma wp_notCorrectPC:
    forall E (w : LWord),
      ~ isCorrectPC w.(lw) ->
      {{{ PC ↦ᵣ w }}}
         Instr Executable @ E
        {{{ RET FailedV; PC ↦ᵣ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "Hσ1 /="; destruct σ1 as [[[r sr] m] st]; simpl.
    iDestruct "Hσ1" as (lreg lmem R C) "(Hr & Hsr & Hm & Hst & HR & HC & %Her)".
    iDestruct (@gen_heap_valid with "Hr HPC") as %HPC.
    pose proof (erasure_lookup_reg _ _ _ _ _ _ _ Her HPC) as HPCr.
    iApply fupd_frame_l.
    iSplit; first (by iPureIntro; apply normal_always_base_reducible).
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iSplitR "Hϕ HPC"; last by iApply "Hϕ".
    iExists lreg, lmem, R, C. by iFrame.
  Qed.

  Lemma wp_notCorrectPC_tag E (w : LWord) :
    get_tag w.(lw) = false →
    {{{ PC ↦ᵣ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ w }}}.
  Proof.
    iIntros (Htag φ) "HPC Hφ".
    iApply (wp_notCorrectPC with "HPC").
    { by apply not_isCorrectPC_untagged. }
    iNext. iIntros "HPC". by iApply "Hφ".
  Qed.

  (* Subcases for respectively permissions and bounds *)

  Lemma wp_notCorrectPC_perm E (t : bool) pc_p pc_g pc_b pc_e pc_a pc_π :
    executeAllowed pc_p = false ->
    {{{ PC ↦ᵣ WCap t pc_p pc_g pc_b pc_e pc_a @@? pc_π }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC _ (WCap t pc_p pc_g pc_b pc_e pc_a @@? pc_π) with "[HPC]");
      [apply not_isCorrectPC_perm;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  Lemma wp_notCorrectPC_range E (t : bool) pc_p pc_g pc_b pc_e pc_a pc_π :
       ¬ (pc_b <= pc_a < pc_e)%a →
      {{{ PC ↦ᵣ WCap t pc_p pc_g pc_b pc_e pc_a @@? pc_π }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hperm φ) "HPC Hwp".
    iApply (wp_notCorrectPC _ (WCap t pc_p pc_g pc_b pc_e pc_a @@? pc_π) with "[HPC]");
      [apply not_isCorrectPC_bounds;eauto|iFrame|].
    iNext. iIntros "HPC /=".
    by iApply "Hwp".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a pc_π w :
    decodeInstrW w.(lw) = Halt →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iDestruct (map_of_regs_1 with "Hpc") as "Hmap".
    iApply (wp_instr_step with "Hpca Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hregs Hregs' Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpca Hmap".
    rewrite Hinstr /exec /= in Hstep. simplify_eq.
    iDestruct (regs_of_map_1 with "Hmap") as "Hpc".
    iModIntro. iSplitR "Hφ Hpc Hpca"; last (cbn; iApply "Hφ"; iFrame).
    iExists lreg, lmem, R, C. by iFrame.
  Qed.

  Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a pc_π w :
    decodeInstrW w.(lw) = Fail →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iDestruct (map_of_regs_1 with "Hpc") as "Hmap".
    iApply (wp_instr_step with "Hpca Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hregs Hregs' Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpca Hmap".
    rewrite Hinstr /exec /= in Hstep. simplify_eq.
    iDestruct (regs_of_map_1 with "Hmap") as "Hpc".
    iModIntro. iSplitR "Hφ Hpc Hpca"; last (cbn; iApply "Hφ"; iFrame).
    iExists lreg, lmem, R, C. by iFrame.
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

End griotte_lang_rules.

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
        {t0 t : bool} {p0 g0 b0 e0 a0 p g b e a}:
    regs !! r1 = Some (WCap t0 p0 g0 b0 e0 a0)
    → regs !! r2 = Some (WCap t p g b e a)
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
  | GetTag dst src => {[ dst; src ]}
  | ClearTag dst src => {[ dst; src ]}
  | machine_instructions.Add r arg1 arg2 => {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2
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
  | Load r1 r2 _ => {[ r1; r2 ]}
  | Store r1 arg _ => {[ r1 ]} ∪ regs_of_argument arg
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
       ∃ (w:Word), (regs !!ᵣ r = Some w) ∧ (regs' !!ᵣ r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (regs !!ᵣ rr)) as [w Hw].
  { eapply elem_of_dom_reg.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_reg_weaken; eauto.
Qed.

Lemma indom_lregs_incl D (regs regs': LReg) :
  D ⊆ dom regs →
  regs ⊆ regs' →
  ∀ r, r ∈ D →
       ∃ (w:LWord), (regs !!ₗ r = Some w) ∧ (regs' !!ₗ r = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (regs !!ₗ rr)) as [w Hw].
  { eapply elem_of_dom_lreg.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply llookup_reg_weaken; eauto.
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

(* The logical PC increment: the PC keeps its identifier. *)
Definition incrementPC_gen (regs: LReg) (n : Z) : option LReg :=
  match regs !! PC with
  | Some (WCap t p g b e a @@? π) =>
    match (a + n)%a with
    | Some a' => Some (<[ PC := WCap t p g b e a' @@? π ]> regs)
    | None => None
    end
  | _ => None
  end.

Definition incrementPC (regs: LReg) : option LReg := incrementPC_gen regs 1.

Lemma incrementPC_gen_Some_inv regs regs' n :
  incrementPC_gen regs n = Some regs' ->
  exists t p g b e a a' π,
    regs !! PC = Some (WCap t p g b e a @@? π) ∧
    (a + n)%a = Some a' ∧
    regs' = <[ PC := WCap t p g b e a' @@? π ]> regs.
Proof.
  unfold incrementPC_gen.
  destruct (regs !! PC) as [[w π]|]; try congruence.
  destruct_word w; try congruence.
  case_eq (a+n)%a; try congruence. intros ? ?. inversion 1.
  do 8 eexists. split; eauto.
Qed.
Lemma incrementPC_Some_inv regs regs' :
  incrementPC regs = Some regs' ->
  exists t p g b e a a' π,
    regs !! PC = Some (WCap t p g b e a @@? π) ∧
    (a + 1)%a = Some a' ∧
    regs' = <[ PC := WCap t p g b e a' @@? π ]> regs.
Proof. apply incrementPC_gen_Some_inv. Qed.

Lemma incrementPC_gen_None_inv regs (t : bool) p g b e a π n :
  incrementPC_gen regs n = None ->
  regs !! PC = Some (WCap t p g b e a @@? π) ->
  (a + n)%a = None.
Proof.
  unfold incrementPC_gen. intros Hi HPC. rewrite HPC in Hi.
  destruct (a+n)%a; congruence.
Qed.
Lemma incrementPC_None_inv regs (t : bool) p g b e a π :
  incrementPC regs = None ->
  regs !! PC = Some (WCap t p g b e a @@? π) ->
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
  rewrite HPC HPC' in Hi |- *. destruct c as [[| [? ? ? ? ? aa | ] | | ] ?]; auto.
  destruct (aa+n)%a; last by auto. congruence.
Qed.
Lemma incrementPC_overflow_mono regs regs' :
  incrementPC regs = None →
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  incrementPC regs' = None.
Proof. apply incrementPC_gen_overflow_mono. Qed.

(* Relation with the physical [updatePC], on physical registers that
   include the erased logical ones. *)
Lemma incrementPC_gen_fail_updatePC_gen (regs : LReg) (r : Reg) sregs m shadow n :
  lregs_erase regs ⊆ r →
  is_Some (regs !! PC) →
  incrementPC_gen regs n = None ->
  updatePC_gen (r, sregs, m, shadow) n = None.
Proof.
  intros Hincl [[w π] HPC] Hi.
  assert (r !! PC = Some w) as HPCr.
  { eapply lookup_weaken; last exact Hincl. by rewrite lookup_lregs_erase HPC. }
  rewrite /incrementPC_gen HPC in Hi.
  rewrite /updatePC_gen /= HPCr.
  destruct w as [| [? ? ? ? ? a' | ] | |]; auto.
  destruct (a' + n)%a; auto. congruence.
Qed.
Lemma incrementPC_fail_updatePC (regs : LReg) (r : Reg) sregs m shadow :
  lregs_erase regs ⊆ r →
  is_Some (regs !! PC) →
  incrementPC regs = None ->
  updatePC (r, sregs, m, shadow) = None.
Proof. apply incrementPC_gen_fail_updatePC_gen. Qed.

Lemma incrementPC_gen_success_updatePC_gen (regs : LReg) (r : Reg) sregs m shadow regs' n :
  lregs_erase regs ⊆ r →
  incrementPC_gen regs n = Some regs' ->
  ∃ t p g b e a a' π,
    regs !! PC = Some (WCap t p g b e a @@? π) ∧
    (a + n)%a = Some a' ∧
    updatePC_gen (r, sregs, m, shadow) n =
      Some (NextI, (<[ PC := WCap t p g b e a' ]> r, sregs, m, shadow)) ∧
    regs' = <[ PC := WCap t p g b e a' @@? π ]> regs.
Proof.
  intros Hincl Hi. apply incrementPC_gen_Some_inv in Hi as (t & p & g & b & e & a & a' & π & HPC & Ha' & ->).
  assert (r !! PC = Some (WCap t p g b e a)) as HPCr.
  { eapply lookup_weaken; last exact Hincl. by rewrite lookup_lregs_erase HPC. }
  exists t, p, g, b, e, a, a', π. repeat split; auto.
  rewrite /updatePC_gen /update_reg /= HPCr Ha'. done.
Qed.
Lemma incrementPC_success_updatePC (regs : LReg) (r : Reg) sregs m shadow regs' :
  lregs_erase regs ⊆ r →
  incrementPC regs = Some regs' ->
  ∃ t p g b e a a' π,
    regs !! PC = Some (WCap t p g b e a @@? π) ∧
    (a + 1)%a = Some a' ∧
    updatePC (r, sregs, m, shadow) =
      Some (NextI, (<[ PC := WCap t p g b e a' ]> r, sregs, m, shadow)) ∧
    regs' = <[ PC := WCap t p g b e a' @@? π ]> regs.
Proof. apply incrementPC_gen_success_updatePC_gen. Qed.

Lemma updatePC_gen_success_incl m m' shadow shadow' regs regs' sregs sregs' w n :
  regs ⊆ regs' →
  updatePC_gen (regs, sregs, m, shadow) n = Some (NextI, (<[ PC := w ]> regs, sregs, m, shadow)) →
  updatePC_gen (regs', sregs', m', shadow') n = Some (NextI, (<[ PC := w ]> regs', sregs', m', shadow')).
Proof.
  intros * Hincl Hu. rewrite /updatePC_gen /= in Hu |- *.
  cbn in *.
  destruct (regs !! PC) as [ w1 |] eqn:Hrr.
  { pose proof (lookup_weaken _ _ _ _ Hrr Hincl) as Hregs'. rewrite Hregs'.
    destruct w1 as [|[ ? ? ? ? ? a1|] | | ]; simplify_eq.
    destruct (a1 + n)%a eqn:Ha1; simplify_eq. rewrite /update_reg /=.
    f_equal. f_equal.
    assert (HH: forall (reg1 reg2:Reg), reg1 = reg2 -> reg1 !! PC = reg2 !! PC)
      by (intros * ->; auto).
    apply HH in Hu. rewrite !lookup_insert_eq in Hu. by simplify_eq. }
  {  inversion Hu. }
Qed.

Lemma updatePC_success_incl m m' shadow shadow' regs regs' sregs sregs' w :
  regs ⊆ regs' →
  updatePC (regs, sregs, m, shadow) = Some (NextI, (<[ PC := w ]> regs, sregs, m, shadow)) →
  updatePC (regs', sregs', m', shadow') = Some (NextI, (<[ PC := w ]> regs', sregs', m', shadow')).
Proof. apply updatePC_gen_success_incl. Qed.

Lemma updatePC_gen_fail_incl m m' shadow shadow' regs regs' sregs sregs' n :
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  updatePC_gen (regs, sregs, m, shadow) n = None →
  updatePC_gen (regs', sregs', m', shadow') n = None.
Proof.
  intros [w HPC] Hincl Hfail. rewrite /updatePC_gen /= in Hfail |- *.
  cbn in *.
  rewrite !HPC in Hfail. have -> := lookup_weaken _ _ _ _ HPC Hincl.
  destruct w as [| [? ? ? ? ? a1 | ]| |]; simplify_eq; auto;[].
  destruct (a1 + n)%a; simplify_eq; auto.
Qed.

Lemma updatePC_fail_incl m m' shadow shadow' regs regs' sregs sregs' :
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  updatePC (regs, sregs, m, shadow) = None →
  updatePC (regs', sregs', m', shadow') = None.
Proof. apply updatePC_gen_fail_incl. Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H
  end; simplify_lmap_eq.

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
  end; simplify_lmap_eq.

Section logical_lookups.
  Context `{MP : MachineParameters}.

  Lemma llookup_reg_incl (regs : LReg) (r : Reg) x (v : LWord) :
    lregs_erase regs ⊆ r → regs !!ₗ x = Some v → lookup_reg x r = Some v.(lw).
  Proof.
    intros Hincl Hx. eapply lookup_reg_weaken; last exact Hincl.
    by rewrite lookup_reg_erase Hx.
  Qed.

  Lemma lz_of_argument_incl (regs : LReg) (r : Reg) arg z :
    lregs_erase regs ⊆ r → lz_of_argument regs arg = Some z → z_of_argument r arg = Some z.
  Proof. intros Hincl Hz. eapply z_of_arg_mono; first exact Hincl. by rewrite z_of_argument_erase. Qed.

  Lemma lz_of_argument_None (regs : LReg) (r : Reg) arg :
    lregs_erase regs ⊆ r → (∀ x, arg = inr x → x ∈ dom regs) →
    lz_of_argument regs arg = None → z_of_argument r arg = None.
  Proof.
    intros Hincl Hdom Hz. destruct arg as [z|x]; cbn in *; first done.
    destruct (regs !!ₗ x) as [v|] eqn:Hx.
    - rewrite (llookup_reg_incl _ _ _ _ Hincl Hx). by destruct v as [[] ?].
    - exfalso. assert (is_Some (regs !!ₗ x)) as [? ?]; last congruence.
      apply elem_of_dom_lreg. by apply Hdom.
  Qed.

  Lemma lz_of_argument_phys (regs : LReg) (r : Reg) arg :
    lregs_erase regs ⊆ r →
    (∀ x, arg = inr x → x ∈ dom regs) →
    z_of_argument r arg = lz_of_argument regs arg.
  Proof.
    intros Hincl Hdom. destruct arg as [z|x]; first done. cbn.
    assert (is_Some (regs !!ₗ x)) as [v Hv].
    { apply elem_of_dom_lreg. by apply Hdom. }
    rewrite (llookup_reg_incl _ _ _ _ Hincl Hv) Hv. by destruct v as [[] ?].
  Qed.

  Lemma llookup_reg_cap (regs : LReg) r t p g b e a :
    lw <$> regs !!ₗ r = Some (WCap t p g b e a) →
    r ≠ cnull ∧ ∃ π, regs !! r = Some (WCap t p g b e a @@? π).
  Proof.
    intros H. unfold llookup_reg in H.
    destruct (regs !! r) as [[w π]|] eqn:Hr; cbn in H; last done.
    destruct (decide (r = cnull)) as [->|Hne]; cbn in H; simplify_eq.
    split; first done. exists π. done.
  Qed.
End logical_lookups.

Section erasure_PC.
  Context `{MP : MachineParameters}.

  (* The PC increment keeps erasure: the incremented PC keeps the bounds, the
     tag and the identifier of the PC. *)
  Lemma erasure_incrementPC_gen R C (r : Reg) sr m st (lreg : LReg) lmem (regs regs' : LReg) n :
    erasure R C (r, sr, m, st) lreg lmem →
    regs ⊆ lreg →
    incrementPC_gen regs n = Some regs' →
    ∃ t p g b e a a' π,
      regs !! PC = Some (WCap t p g b e a @@? π) ∧
      (a + n)%a = Some a' ∧
      regs' = <[ PC := WCap t p g b e a' @@? π ]> regs ∧
      updatePC_gen (r, sr, m, st) n =
        Some (NextI, (<[ PC := WCap t p g b e a' ]> r, sr, m, st)) ∧
      erasure R C (<[ PC := WCap t p g b e a' ]> r, sr, m, st)
        (<[ PC := WCap t p g b e a' @@? π ]> lreg) lmem.
  Proof.
    intros Her Hincl Hi.
    pose proof (erasure_regs_incl _ _ _ _ _ _ Her Hincl) as Hincl'.
    destruct (incrementPC_gen_success_updatePC_gen _ _ sr m st _ _ Hincl' Hi)
      as (t & p & g & b & e & a & a' & π & HPC & Ha' & Hu & ->).
    exists t, p, g, b, e, a, a', π. do 4 (split; first done).
    apply (erasure_insert_reg _ _ _ _ _ _ _ _ PC (WCap t p g b e a' @@? π)); auto.
    pose proof (lookup_weaken _ _ _ _ HPC Hincl) as HPC'.
    pose proof (er_reg_words _ _ _ _ _ Her _ _ HPC') as Hok.
    apply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); auto.
  Qed.

  Lemma erasure_incrementPC R C (r : Reg) sr m st (lreg : LReg) lmem (regs regs' : LReg) :
    erasure R C (r, sr, m, st) lreg lmem →
    regs ⊆ lreg →
    incrementPC regs = Some regs' →
    ∃ t p g b e a a' π,
      regs !! PC = Some (WCap t p g b e a @@? π) ∧
      (a + 1)%a = Some a' ∧
      regs' = <[ PC := WCap t p g b e a' @@? π ]> regs ∧
      updatePC (r, sr, m, st) =
        Some (NextI, (<[ PC := WCap t p g b e a' ]> r, sr, m, st)) ∧
      erasure R C (<[ PC := WCap t p g b e a' ]> r, sr, m, st)
        (<[ PC := WCap t p g b e a' @@? π ]> lreg) lmem.
  Proof. apply erasure_incrementPC_gen. Qed.
End erasure_PC.

Section instruction_closing.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (** Closes a failed instruction: the state is unchanged. *)
  Lemma instr_close_fail (r : Reg) sr m st (lreg : LReg) lmem R C
      (regs : LReg) (Φ : griotte_lang.val → iProp Σ) :
    erasure R C (r, sr, m, st) lreg lmem →
    gen_heap_interp lreg -∗ gen_heap_interp sr -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ FailedV) ==∗
    cerise_state_interp (r, sr, m, st) ∗ from_option Φ False (to_val (Instr Failed)).
  Proof.
    iIntros (Her) "Hr Hsr Hm Hst HR HC Hmap Hφ". iModIntro.
    iSplitR "Hφ Hmap"; last by iApply "Hφ".
    iExists lreg, lmem, R, C. by iFrame.
  Qed.

  (** Closes an instruction that writes one register then increments the PC,
      as the physical [updatePC (update_reg φ dst v)]. The spec [P] holds of
      the new owned registers on success, and of the old ones on failure. *)
  Lemma instr_close_reg_update (r : Reg) sr m st (lreg : LReg) lmem R C
      (regs : LReg) dst (v : LWord) c σ' (Φ : griotte_lang.val → iProp Σ)
      (P : LReg → griotte_lang.val → Prop) :
    erasure R C (r, sr, m, st) lreg lmem →
    regs ⊆ lreg →
    dst ∈ dom regs →
    is_Some (regs !! PC) →
    reg_word_ok R C v →
    (match updatePC (update_reg (r, sr, m, st) dst v.(lw)) with
     | Some conf => conf | None => (Failed, (r, sr, m, st)) end) = (c, σ') →
    (∀ regs', incrementPC (<[dst := v]ₗ> regs) = Some regs' → P regs' NextIV) →
    (incrementPC (<[dst := v]ₗ> regs) = None → P regs FailedV) →
    gen_heap_interp lreg -∗ gen_heap_interp sr -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ regs' retv, ⌜P regs' retv⌝ -∗ ([∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗ Φ retv) ==∗
    cerise_state_interp σ' ∗ from_option Φ False (to_val (Instr c)).
  Proof.
    iIntros (Her Hlregs Hdst HPC Hok Hstep HPs HPf) "Hr Hsr Hm Hst HR HC Hmap Hφ".
    pose proof (erasure_regs_incl _ _ _ _ _ _ Her Hlregs) as Hregs.
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ dst v Her Hok) as Her1.
    assert (<[dst := v]ₗ> regs ⊆ <[dst := v]ₗ> lreg) as Hlregs1 by by apply linsert_reg_mono.
    rewrite /update_reg /= in Hstep.
    destruct (incrementPC (<[dst := v]ₗ> regs)) as [regs'|] eqn:Hi.
    - destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ Her1 Hlregs1 Hi)
        as (t & p & g & b & e & a & a' & π & HPC1 & Ha' & -> & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      assert (is_Some (regs !! dst)) as [vold Hvold] by by apply elem_of_dom.
      iMod (gen_heap_update_inSepM _ _ dst (if decide (dst = cnull) then lnull else v)
        with "Hr Hmap") as "[Hr Hmap]"; first eauto.
      iMod (gen_heap_update_inSepM _ _ PC (WCap t p g b e a' @@? π)
        with "Hr Hmap") as "[Hr Hmap]".
      { by rewrite lookup_insert_is_Some'; right. }
      iModIntro. iSplitR "Hφ Hmap".
      + iExists _, lmem, R, C. iFrame. iPureIntro. exact Her2.
      + iApply ("Hφ" with "[%] Hmap"). by apply HPs.
    - rewrite (incrementPC_fail_updatePC (<[dst := v]ₗ> regs) (insert_reg dst v.(lw) r) sr m st) in Hstep;
        last done.
      + simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
        iIntros "Hmap". iApply ("Hφ" with "[%] Hmap"). by apply HPf.
      + rewrite -insert_reg_erase. rewrite /insert_reg /linsert_reg. by apply insert_mono.
      + rewrite /linsert_reg. destruct (decide (dst = PC)) as [->|Hne].
        * by rewrite lookup_insert_eq.
        * by rewrite lookup_insert_ne.
  Qed.

End instruction_closing.

Section instruction_outcomes.

  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (* A failed instruction rolls back every tentative write. The premise is
     about all physical register files that include the erased owned
     registers, so no absent register or memory address can be mistaken for
     evidence of runtime failure. *)
  Local Lemma wp_instr_failed_map E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) i (regs : LReg) :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    (∀ r sr m st, lregs_erase regs ⊆ r →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hfailed φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hregs Hregs' Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr (Hfailed r sr m st Hregs') in Hstep. simplify_eq.
    iModIntro. iSplitR "Hφ Hpc_a Hmap"; last (cbn; iApply "Hφ"; iFrame).
    iExists lreg, lmem, R, C. by iFrame.
  Qed.

  (* Failure with PC alone; all resources are returned unchanged. *)
  Lemma wp_instr_failed_0 E pc_p pc_g pc_b pc_e pc_a pc_π w i :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_instr_failed_map _ _ _ _ _ _ _ _ _
      (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π]> ∅)
      with "[$Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - by rewrite lookup_insert_eq.
    - intros r sr m st Hincl. apply Hfailed.
      all: eapply lookup_weaken; last exact Hincl.
      all: rewrite lookup_lregs_erase ?lookup_insert ?lookup_empty; repeat case_decide; try congruence.
      all: done.
    - iNext. iIntros "(Hmem & Hmap)".
      iDestruct (regs_of_map_1 with "Hmap") as "HPC".
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 1 explicit register; all resources are returned unchanged. *)
  Lemma wp_instr_failed_1 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
       r !! r1 = Some w1.(lw) →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ r1 ↦ᵣ w1 ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ r1 ↦ᵣ w1 ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hmem) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (wp_instr_failed_map _ _ _ _ _ _ _ _ _
      (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π]> (<[r1 := w1]> ∅))
      with "[$Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - by rewrite lookup_insert_eq.
    - intros r sr m st Hincl. apply Hfailed.
      all: eapply lookup_weaken; last exact Hincl.
      all: rewrite lookup_lregs_erase ?lookup_insert ?lookup_empty; repeat case_decide; try congruence.
      all: done.
    - iNext. iIntros "(Hmem & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "(HPC & Hr1)"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 2 explicit registers; all resources are returned unchanged. *)
  Lemma wp_instr_failed_2 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 r2 w2 :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
       r !! r1 = Some w1.(lw) →
       r !! r2 = Some w2.(lw) →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ r1 ↦ᵣ w1 ∗ ▷ r2 ↦ᵣ w2 ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hr2 & >Hmem) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (Hne0 & Hne1 & Hne2).
    iApply (wp_instr_failed_map _ _ _ _ _ _ _ _ _
      (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π]> (<[r1 := w1]> (<[r2 := w2]> ∅)))
      with "[$Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - by rewrite lookup_insert_eq.
    - intros r sr m st Hincl. apply Hfailed.
      all: eapply lookup_weaken; last exact Hincl.
      all: rewrite lookup_lregs_erase ?lookup_insert ?lookup_empty; repeat case_decide; try congruence.
      all: done.
    - iNext. iIntros "(Hmem & Hmap)".
      iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hr1 & Hr2)"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 3 explicit registers; all resources are returned unchanged. *)
  Lemma wp_instr_failed_3 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 r2 w2 r3 w3 :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
       r !! r1 = Some w1.(lw) →
       r !! r2 = Some w2.(lw) →
       r !! r3 = Some w3.(lw) →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          ▷ r1 ↦ᵣ w1 ∗
          ▷ r2 ↦ᵣ w2 ∗
          ▷ r3 ↦ᵣ w3 ∗
          ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          r1 ↦ᵣ w1 ∗
          r2 ↦ᵣ w2 ∗
          r3 ↦ᵣ w3 ∗
          pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hr2 & >Hr3 & >Hmem) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (Hne0 & Hne1 & Hne2 & Hne3 & Hne4 & Hne5).
    iApply (wp_instr_failed_map _ _ _ _ _ _ _ _ _
      (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π]>
         (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅))))
      with "[$Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - by rewrite lookup_insert_eq.
    - intros r sr m st Hincl. apply Hfailed.
      all: eapply lookup_weaken; last exact Hincl.
      all: rewrite lookup_lregs_erase ?lookup_insert ?lookup_empty; repeat case_decide; try congruence.
      all: done.
    - iNext. iIntros "(Hmem & Hmap)".
      iDestruct (regs_of_map_4 with "Hmap") as "(HPC & Hr1 & Hr2 & Hr3)"; eauto.
      iApply "Hφ". iFrame.
  Qed.
End instruction_outcomes.
