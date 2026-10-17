From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants na_invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap.
From griotte Require Export iris_extra stdpp_extra griotte_lang.
From griotte Require Export machine_base cerise_instance register_file machine_instructions.
From griotte Require Export named_props_extra.

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

  Lemma map_of_regs_0 : ⊢ [∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y.
  Proof. by rewrite big_sepM_empty. Qed.

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

  (* ------------------------- system registers points-to --------------------------------- *)

  Lemma map_of_sregs_1 (sr1: SRegName) (w1: LWord) :
    sr1 ↦ₛᵣ w1 -∗
    ([∗ map] k↦y ∈ {[sr1 := w1]}, k ↦ₛᵣ y).
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma sregs_of_map_1 (sr1: SRegName) (w1: LWord) :
    ([∗ map] k↦y ∈ {[sr1 := w1]}, k ↦ₛᵣ y) -∗
    sr1 ↦ₛᵣ w1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma sregname_neq sr1 sr2 w1 w2 :
    sr1 ↦ₛᵣ w1 -∗ sr2 ↦ₛᵣ w2 -∗ ⌜ sr1 ≠ sr2 ⌝.
  Proof.
    iIntros "H1 H2" (->).
    iDestruct (pointsto_valid_2 with "H1 H2") as %[Hv _].
    by apply dfrac_full_exclusive in Hv.
  Qed.

  Lemma map_of_sregs_2 (sr1 sr2: SRegName) (w1 w2: LWord) :
    sr1 ↦ₛᵣ w1 -∗ sr2 ↦ₛᵣ w2 -∗
    ([∗ map] k↦y ∈ (<[sr1:=w1]> (<[sr2:=w2]> ∅)), k ↦ₛᵣ y) ∗ ⌜ sr1 ≠ sr2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (sregname_neq with "H1 H2") as "%Hne".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma sregs_of_map_2 (sr1 sr2: SRegName) (w1 w2: LWord) :
    sr1 ≠ sr2 →
    ([∗ map] k↦y ∈ (<[sr1:=w1]> (<[sr2:=w2]> ∅)), k ↦ₛᵣ y) -∗
    sr1 ↦ₛᵣ w1 ∗ sr2 ↦ₛᵣ w2.
  Proof.
    iIntros (Hne) "Hmap". rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    + by iDestruct "Hmap" as "(? & ? & _)"; iFrame.
    + apply lookup_insert_None; split; eauto.
  Qed.

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

  Lemma memMap_resource_2ne_dq (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : LWord) :
    a1 ≠ a2 →
    ([∗ map] a↦dw ∈ prod_merge (<[a1:=dq1]> (<[a2:=dq2]> ∅)) (<[a1:=w1]> (<[a2:=w2]> ∅)),
       a ↦ₐ{dw.1} dw.2)%I ⊣⊢ a1 ↦ₐ{dq1} w1 ∗ a2 ↦ₐ{dq2} w2.
  Proof.
    intros Hne.
    rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1)); auto.
    rewrite -(insert_merge _ _ _ _ (dq2,w2)); auto.
    rewrite merge_empty big_sepM_insert; last by rewrite lookup_insert_ne.
    by rewrite big_sepM_insert // big_sepM_empty right_id.
  Qed.

  (* The fetched instruction word may be shared, the other cell is exclusive. *)
  Lemma memMap_resource_2ne_apply_dq (a1 a2 : Addr) (dq : dfrac) (w1 w2 : LWord) :
    a1 ↦ₐ{dq} w1 -∗ a2 ↦ₐ w2 -∗
    ([∗ map] a↦dw ∈ prod_merge (<[a1:=dq]> (<[a2:=DfracOwn 1]> ∅)) (<[a1:=w1]> (<[a2:=w2]> ∅)),
       a ↦ₐ{dw.1} dw.2) ∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (pointsto_ne with "H2 H1") as %Hne.
    rewrite memMap_resource_2ne_dq; last done.
    iFrame. iPureIntro. done.
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

  (* ------------------------- the state interpretation --------------------------- *)

  (** The common start of every instruction rule: the logical PC and the
      instruction word give the physical ones, and the instruction is decoded
      from the physical copy. The continuation closes the state
      interpretation after the physical step. *)
  Lemma wp_instr_step E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    ▷ PC ↦ₚ (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (lreg : LReg) (lsreg : LSReg) (lmem : LMem)
       (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag) (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)
                    (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg lsreg lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ gen_heap_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "HPC" ∷ PC ↦ₚ (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       cerise_state_interp σ' ∗ from_option Φ False (to_val (Instr c)))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ /=". destruct σ1 as [[[[pc r] sr] m] st]; cbn.
    iNamed "Hσ".
    iMod "HPC". iMod "Hpc_a". iMod "Hmap".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %Hpc_a.
    pose proof (erasure_regs_incl _ _ _ _ _ _ _ _ Her Hregs) as Hregs'.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hpc_a) as (pw & Hpw & Hok).
    pose proof (erasure_pc_correct _ _ _ _ _ _ _ Her Hvpc) as HPCr. cbn in HPCr. subst pc.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; first done.
    eapply step_exec_inv in Hstep; eauto; cbn in Hstep.
    rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hstep.
    iApply ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $HPC $Hpc_a $Hmap]").
    by iFrame "%".
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)
  (* Bind Scope expr_scope with language.expr griotte_lang. *)

  Lemma wp_notCorrectPC:
    forall E (w : LWord),
      ~ isCorrectPC w.(lw) ->
      {{{ PC ↦ₚ w }}}
         Instr Executable @ E
        {{{ RET FailedV; PC ↦ₚ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "Hσ1 /="; destruct σ1 as [[[[pc r] sr] m] st]; simpl.
    iNamed "Hσ1".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    pose proof (erasure_pc_not_correct _ _ _ _ _ _ _ Her Hnpc) as Hnpc'. cbn in Hnpc'.
    iApply fupd_frame_l.
    iSplit; first (by iPureIntro; apply normal_always_base_reducible).
    iModIntro. iIntros (e1 σ2 efs Hstep).
    apply prim_step_exec_inv in Hstep as (-> & -> & (c & -> & Hstep)).
    eapply step_fail_inv in Hstep as [-> ->]; eauto.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iSplitR "Hϕ HPC"; last by iApply "Hϕ".
    iExists w, lreg, lsreg, lmem, R, C. by iFrame.
  Qed.

  Lemma wp_notCorrectPC_tag E (w : LWord) :
    get_tag w.(lw) = false →
    {{{ PC ↦ₚ w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ₚ w }}}.
  Proof.
    iIntros (Htag φ) "HPC Hφ".
    iApply (wp_notCorrectPC with "HPC").
    { by apply not_isCorrectPC_untagged. }
    iNext. iIntros "HPC". by iApply "Hφ".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a pc_π w dq :
    decodeInstrW w.(lw) = Halt →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply (wp_instr_step _ _ _ _ _ _ _ _ _ ∅ with "Hpc Hpca [] "); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec /= in Hstep. simplify_eq.
    iModIntro. iSplitR "Hφ HPC Hpc_a"; last (cbn; iApply "Hφ"; iFrame).
    iExists _, lreg, lsreg, lmem, R, C. by iFrame.
  Qed.

  Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a pc_π w dq :
    decodeInstrW w.(lw) = Fail →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply (wp_instr_step _ _ _ _ _ _ _ _ _ ∅ with "Hpc Hpca [] "); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec /= in Hstep. simplify_eq.
    iModIntro. iSplitR "Hφ HPC Hpc_a"; last (cbn; iApply "Hφ"; iFrame).
    iExists _, lreg, lsreg, lmem, R, C. by iFrame.
  Qed.

  (* ----------------------------------- PURE RULES ---------------------------------- *)

  #[local] Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  #[local] Ltac solve_exec_puredet := simpl; intros; by inv_base_step.
  #[local] Ltac solve_exec_pure := intros ?; apply nsteps_once, pure_base_step_pure_step;
                                constructor; [solve_exec_safe|]; intros;
                                (match goal with
                                | H : base_step _ _ _ _ _ _ |- _ => inversion H end).

  #[global] Instance pure_seq_failed :
    PureExec True 1 (Seq (Instr Failed)) (Instr Failed).
  Proof. by solve_exec_pure. Qed.

  #[global] Instance pure_seq_halted :
    PureExec True 1 (Seq (Instr Halted)) (Instr Halted).
  Proof. by solve_exec_pure. Qed.

  #[global] Instance pure_seq_done :
    PureExec True 1 (Seq (Instr NextI)) (Seq (Instr Executable)).
  Proof. by solve_exec_pure. Qed.

End griotte_lang_rules.

(* Splits the points-to of a register map built by inserts into one
   points-to per register; the inserted keys must be provably distinct. *)
Ltac iRegsMap H :=
  iRename H into "Hregs_map";
  rewrite -?insert_empty;
  repeat (
    iDestruct (big_sepM_insert_delete with "Hregs_map") as "[? Hregs_map]";
    repeat first [ rewrite delete_insert_eq
                 | rewrite delete_insert_ne; [|first [done | by apply not_eq_sym]]
                 | rewrite delete_empty ]);
  iClear "Hregs_map".

(* ----------------- useful definitions to factor out the wp specs ---------------- *)

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
  | CLoad r1 r2 _ => {[ r1; r2 ]}
  | Store r1 arg _ => {[ r1 ]} ∪ regs_of_argument arg
  | Jnz arg1 r2 => {[ r2 ]} ∪ regs_of_argument arg1
  | Jmp arg => regs_of_argument arg
  | Jalr rdst rsrc => {[ rdst; rsrc ]}
  | Seal dst r1 r2 => {[dst; r1; r2]}
  | UnSeal dst r1 r2 => {[dst; r1; r2]}
  (* [cnull] is neither read nor written by [SpecialRW]. *)
  | SpecialRW dst _ src => ({[ dst ]} ∪ regs_of_argument src) ∖ {[ cnull ]}
  | Auipcc dst _ => {[ dst ]}
  | _ => ∅
  end.

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
  | SpecialRW _ sr _ => {[ sr ]}
  | SetMIE _ => {[ MSTATUS ]}
  | Mret => {[ MEPCC; MSTATUS ]}
  | _ => ∅
  end.

Lemma indom_sregs_incl D (sregs sregs': LSReg) :
  D ⊆ dom sregs →
  sregs ⊆ sregs' →
  ∀ sr, sr ∈ D →
       ∃ (w:LWord), (sregs !! sr = Some w) ∧ (sregs' !! sr = Some w).
Proof.
  intros * HD Hincl rr Hr.
  assert (is_Some (sregs !! rr)) as [w Hw].
  { eapply @elem_of_dom with (D := gset SRegName); first typeclasses eauto.
    eapply elem_of_subseteq; eauto. }
  exists w. split; auto. eapply lookup_weaken; eauto.
Qed.

(*--- incrementPC ---*)

(* The logical PC increment: the PC keeps its identifier. *)
Definition incrementPC_gen (lpc : LWord) (n : Z) : option LWord :=
  match lpc with
  | WCap t p g b e a @@? π =>
    match (a + n)%a with
    | Some a' => Some (WCap t p g b e a' @@? π)
    | None => None
    end
  | _ => None
  end.

Definition incrementPC (lpc : LWord) : option LWord := incrementPC_gen lpc 1.

Lemma incrementPC_gen_Some_inv lpc lpc' n :
  incrementPC_gen lpc n = Some lpc' ->
  exists t p g b e a a' π,
    lpc = WCap t p g b e a @@? π ∧
    (a + n)%a = Some a' ∧
    lpc' = WCap t p g b e a' @@? π.
Proof.
  unfold incrementPC_gen. destruct lpc as [w π].
  destruct_word w; try congruence.
  case_eq (a+n)%a; try congruence. intros ? ?. inversion 1.
  do 8 eexists. split; eauto.
Qed.
Lemma incrementPC_Some_inv lpc lpc' :
  incrementPC lpc = Some lpc' ->
  exists t p g b e a a' π,
    lpc = WCap t p g b e a @@? π ∧
    (a + 1)%a = Some a' ∧
    lpc' = WCap t p g b e a' @@? π.
Proof. apply incrementPC_gen_Some_inv. Qed.

Lemma incrementPC_gen_None_inv lpc (t : bool) p g b e a π n :
  incrementPC_gen lpc n = None ->
  lpc = WCap t p g b e a @@? π ->
  (a + n)%a = None.
Proof.
  unfold incrementPC_gen. intros Hi ->.
  destruct (a+n)%a; congruence.
Qed.
Lemma incrementPC_None_inv lpc (t : bool) p g b e a π :
  incrementPC lpc = None ->
  lpc = WCap t p g b e a @@? π ->
  (a + 1)%a = None.
Proof. apply incrementPC_gen_None_inv. Qed.

Lemma incrementPC_add (t : bool) p g b e a a' π :
  (a + 1)%a = Some a' →
  incrementPC (WCap t p g b e a @@? π) = Some (WCap t p g b e a' @@? π).
Proof. intros Ha. by rewrite /incrementPC /incrementPC_gen /= Ha. Qed.

Ltac incrementPC_inv :=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?&?&?&?)
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H; [|reflexivity]
  end; simplify_lmap_eq.

Tactic Notation "incrementPC_inv" "as" simple_intropattern(pat):=
  match goal with
  | H : incrementPC _ = Some _ |- _ =>
    apply incrementPC_Some_inv in H as pat
  | H : incrementPC _ = None |- _ =>
    eapply incrementPC_None_inv in H; [|reflexivity]
  | H : incrementPC_gen _ _ = Some _ |- _ =>
    apply incrementPC_gen_Some_inv in H as pat
  | H : incrementPC_gen _ _ = None |- _ =>
    eapply incrementPC_gen_None_inv in H; [|reflexivity]
  end; simplify_lmap_eq.

Section logical_lookups.
  Context `{MP : MachineParameters}.

  (** A register read: the physical word is a copy of the logical one. *)
  Lemma llookup_reg_phys R (regs : LReg) (r : Reg) x (v : LWord) :
    lregs_phys R regs r → regs !!ₗ x = Some v →
    ∃ s, lookup_reg x r = Some (and_tag s v.(lw)) ∧ reg_phys R v (and_tag s v.(lw)).
  Proof.
    intros Hincl Hx. rewrite /llookup_reg in Hx.
    destruct (regs !! x) as [v'|] eqn:Hv'; cbn in Hx; last done.
    destruct (Hincl x v' Hv') as (w & Hw & Hrel).
    rewrite /lookup_reg Hw /=. case_decide; simplify_eq.
    - exists true. split; first done. apply reg_phys_lnull.
    - destruct (reg_phys_and_tag _ _ _ Hrel) as [s ->]. by exists s.
  Qed.

  (** Integer reads are exact. *)
  Lemma llookup_reg_phys_int R (regs : LReg) (r : Reg) x z π :
    lregs_phys R regs r → regs !!ₗ x = Some (MkLWord (WInt z) π) → lookup_reg x r = Some (WInt z).
  Proof. intros Hincl Hx. by destruct (llookup_reg_phys _ _ _ _ _ Hincl Hx) as (s & -> & _). Qed.

  Lemma lz_of_argument_incl R (regs : LReg) (r : Reg) arg z :
    lregs_phys R regs r → lz_of_argument regs arg = Some z → z_of_argument r arg = Some z.
  Proof.
    intros Hincl Hz. destruct arg as [z'|x]; cbn in *; first done.
    destruct (regs !!ₗ x) as [v|] eqn:Hx; last done. simplify_eq.
    destruct (llookup_reg_phys _ _ _ _ _ Hincl Hx) as (s & -> & _).
    by rewrite /= get_a_and_tag.
  Qed.

  Lemma lz_of_argument_None R (regs : LReg) (r : Reg) arg :
    lregs_phys R regs r → (∀ x, arg = inr x → x ∈ dom regs) →
    lz_of_argument regs arg = None → z_of_argument r arg = None.
  Proof.
    intros Hincl Hdom Hz. destruct arg as [z|x]; cbn in *; first done.
    destruct (regs !!ₗ x) as [v|] eqn:Hx.
    - done.
    - exfalso. assert (is_Some (regs !!ₗ x)) as [? ?]; last congruence.
      apply elem_of_dom_lreg. by apply Hdom.
  Qed.

  (** An operand whose register is in the map has an integer view. *)
  Lemma lz_of_argument_dom (regs : LReg) arg :
    (∀ x, arg = inr x → x ∈ dom regs) → is_Some (lz_of_argument regs arg).
  Proof.
    intros Hdom. apply lz_of_argument_is_Some. intros x Hx.
    apply elem_of_dom_lreg. by apply Hdom.
  Qed.

  Lemma lz_of_argument_phys R (regs : LReg) (r : Reg) arg :
    lregs_phys R regs r →
    (∀ x, arg = inr x → x ∈ dom regs) →
    z_of_argument r arg = lz_of_argument regs arg.
  Proof.
    intros Hincl Hdom. destruct (lz_of_argument regs arg) eqn:Hz.
    - by eapply lz_of_argument_incl.
    - by eapply lz_of_argument_None.
  Qed.

  (** A word argument: a register read, or an exact integer. *)
  Lemma lword_of_argument_phys R (regs : LReg) (r : Reg) arg (v : LWord) :
    lregs_phys R regs r → lword_of_argument regs arg = Some v →
    ∃ s, word_of_argument r arg = Some (and_tag s v.(lw)) ∧ reg_phys R v (and_tag s v.(lw)).
  Proof.
    intros Hincl Hv. destruct arg as [z|x]; cbn in Hv.
    - simplify_eq. exists true. split; first done. apply reg_phys_lword_of_word.
    - by eapply llookup_reg_phys.
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

  (** The identifier of the word read from a register, if it is a
      capability; like [read_reg_inr] for its other fields. *)
  Definition read_reg_prov (regs : LReg) (r : RegName) (π : option AId) : Prop :=
    match regs !! r with
    | Some (WCap _ _ _ _ _ _ @@? π') => π' = π
    | _ => True
    end.

  Lemma read_reg_prov_cap (regs : LReg) r p g b e a π :
    lw <$> regs !!ₗ r = Some (WCap true p g b e a) →
    read_reg_prov regs r π →
    regs !! r = Some (WCap true p g b e a @@? π).
  Proof.
    intros Hinr Hπ.
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hinr) as (_ & π' & Hr).
    rewrite /read_reg_prov Hr in Hπ. by subst π'.
  Qed.

End logical_lookups.

Section erasure_PC.
  Context `{MP : MachineParameters}.

  (* The PC increment on a copy of the PC gives the same copy of the
     incremented PC. *)
  Lemma incrementPC_gen_phys R (lpc lpc' : LWord) pc (r : Reg) sr m st n :
    reg_phys R lpc pc →
    incrementPC_gen lpc n = Some lpc' →
    ∃ pc', updatePC_gen (pc, r, sr, m, st) n = Some (NextI, (pc', r, sr, m, st)) ∧
           reg_phys R lpc' pc'.
  Proof.
    intros Hpc Hi.
    apply incrementPC_gen_Some_inv in Hi as (t & p & g & b & e & a & a' & π & -> & Ha' & ->).
    destruct (reg_phys_and_tag _ _ _ Hpc) as [s ->].
    exists (and_tag s (WCap t p g b e a')). split.
    - rewrite /updatePC_gen /update_pcc /= Ha'. done.
    - by apply (reg_phys_derive _ (WCap t p g b e a @@? π)).
  Qed.

  Lemma incrementPC_gen_phys_fail R (lpc : LWord) pc (r : Reg) sr m st n :
    reg_phys R lpc pc →
    incrementPC_gen lpc n = None →
    updatePC_gen (pc, r, sr, m, st) n = None.
  Proof.
    intros Hpc Hi. destruct (reg_phys_and_tag _ _ _ Hpc) as [s ->].
    rewrite /incrementPC_gen in Hi. rewrite /updatePC_gen /=.
    destruct lpc as [w π]; cbn in *.
    destruct w as [| [? ? ? ? ? a' | ] | |]; cbn; auto.
    destruct (a' + n)%a; auto. congruence.
  Qed.

  (* The PC increment keeps erasure: the incremented PC keeps the bounds, the
     tag and the identifier of the PC. *)
  Lemma erasure_incrementPC_gen R C (pc : Word) (r : Reg) sr m st lpc lpc' (lreg : LReg) lsreg lmem n :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    incrementPC_gen lpc n = Some lpc' →
    ∃ pc', updatePC_gen (pc, r, sr, m, st) n = Some (NextI, (pc', r, sr, m, st)) ∧
           erasure R C (pc', r, sr, m, st) lpc' lreg lsreg lmem.
  Proof.
    intros Her Hi.
    destruct (incrementPC_gen_phys _ _ _ _ r sr m st _ (er_pc _ _ _ _ _ _ _ Her) Hi)
      as (pc' & Hu & Hpc').
    exists pc'. split; first done.
    apply incrementPC_gen_Some_inv in Hi as (t & p & g & b & e & a & a' & π & -> & Ha' & ->).
    destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio Hpc Hpcw Hpcok].
    constructor; cbn in *; try done.
  Qed.

  Lemma erasure_incrementPC R C (pc : Word) (r : Reg) sr m st lpc lpc' (lreg : LReg) lsreg lmem :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    incrementPC lpc = Some lpc' →
    ∃ pc', updatePC (pc, r, sr, m, st) = Some (NextI, (pc', r, sr, m, st)) ∧
           erasure R C (pc', r, sr, m, st) lpc' lreg lsreg lmem.
  Proof. apply erasure_incrementPC_gen. Qed.

  Lemma erasure_incrementPC_fail R C (pc : Word) (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem n :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    incrementPC_gen lpc n = None →
    updatePC_gen (pc, r, sr, m, st) n = None.
  Proof. intros Her. apply incrementPC_gen_phys_fail with R, Her. Qed.
End erasure_PC.

(** ** Dereference witnesses

    A Load source, a Store destination or a GetTag source is read exactly
    while its identifier is live: the witness is a status share of the
    identifier, or the absence of an identifier. *)
Inductive deref_witness := DerefNoId | DerefLive (ι : AId) (q : Qp).

Definition deref_id (dw : deref_witness) : option AId :=
  match dw with DerefNoId => None | DerefLive ι _ => Some ι end.

(** The witness for an identifier [π], with share [q] if [π] is some. *)
Definition deref_witness_of (π : option AId) (q : Qp) : deref_witness :=
  match π with None => DerefNoId | Some ι => DerefLive ι q end.

Lemma deref_id_witness_of π q : deref_id (deref_witness_of π q) = π.
Proof. by destruct π. Qed.

(** The share of a witness, [1] without an identifier. *)
Definition deref_share (dw : deref_witness) : Qp :=
  match dw with DerefNoId => 1%Qp | DerefLive _ q => q end.

Section deref_witness.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  Definition deref_witness_res (dw : deref_witness) : iProp Σ :=
    match dw with
    | DerefNoId => emp
    | DerefLive ι q => ι ↦st{q} ALive
    end%I.

  #[global] Instance deref_witness_res_timeless dw : Timeless (deref_witness_res dw).
  Proof. destruct dw; apply _. Qed.

  (** The dereference resource of a capability with identifier [π]:
      nothing without an identifier, a share [q] of a live status
      otherwise. The share [q] is irrelevant when [π] is [None]. *)
  Definition deref_res (π : option AId) (q : Qp) : iProp Σ :=
    match π with
    | None => emp
    | Some ι => ι ↦st{q} ALive
    end%I.

  #[global] Instance deref_res_timeless π q : Timeless (deref_res π q).
  Proof. destruct π; apply _. Qed.

  (* Kept folded by instance search, so that [deref_res None q] is not taken
     for [emp] before its share is determined. *)
  #[global] Typeclasses Opaque deref_res.

  Lemma deref_res_witness π q :
    deref_res π q = deref_witness_res (deref_witness_of π q).
  Proof. by destruct π. Qed.

  (** The resource of an identifier-less capability, with share [1]. *)
  Lemma deref_res_none : ⊢ deref_res None 1.
  Proof. done. Qed.

  (** A witness is the dereference resource of its identifier. *)
  Lemma deref_witness_res_deref_res dw :
    deref_witness_res dw = deref_res (deref_id dw) (deref_share dw).
  Proof. by destruct dw. Qed.

  Definition deref_witness_ok (R : RegState) (dw : deref_witness) : Prop :=
    match dw with
    | DerefNoId => True
    | DerefLive ι _ => ∃ x, R !! ι = Some x ∧ re_status x = ALive
    end.

  Lemma deref_witness_lookup R dw :
    reg_auth R -∗ deref_witness_res dw -∗ ⌜deref_witness_ok R dw⌝.
  Proof.
    iIntros "HR Hw". destruct dw as [|ι q]; cbn; first done.
    iDestruct (reg_lookup_own with "HR Hw") as %(b & e & γ & HRι).
    iPureIntro. eexists. split; first done. done.
  Qed.

  Lemma deref_witness_not_stale R dw (v : LWord) :
    deref_witness_ok R dw → v.(lprov) = deref_id dw → ¬ stale_id R v.
  Proof.
    intros Hok Hπ (ι & x & Hι & Hx & Hs). destruct dw as [|ι' q]; cbn in *; first congruence.
    destruct Hok as (x' & Hx' & Hs'). simplify_eq; congruence.
  Qed.

  (** A word read under its witness is exact. *)
  Lemma deref_exact R dw (v : LWord) w :
    deref_witness_ok R dw → v.(lprov) = deref_id dw → load_exact_cond v →
    reg_phys R v w → w = v.(lw).
  Proof.
    intros Hok Hπ Hcond Hw. eapply reg_phys_exact_cond; eauto.
    by eapply deref_witness_not_stale.
  Qed.

  (** A tagged word with non-empty bounds has authority or no heap base. *)
  Lemma nonempty_exact_cond (v : LWord) b e :
    memory_cap_bounds v.(lw) = Some (b, e) → (b < e)%a → load_exact_cond v.
  Proof.
    intros Hb Hlt Ht. destruct (is_heap_address b) eqn:Hh.
    - left. split; first done. exists b. apply heap_authority_base_memory_cap_bounds. eauto.
    - right. by rewrite /heap_cap_base memory_cap_base_bounds Hb /= Hh.
  Qed.
End deref_witness.

Lemma reg_phys_derive_eq `{MachineParameters} R (v : LWord) s w' w'' :
  reg_phys R v (and_tag s v.(lw)) →
  memory_cap_bounds w' = memory_cap_bounds v.(lw) →
  (get_tag w' = true → get_tag v.(lw) = true) →
  and_tag s w' = w'' →
  reg_phys R (MkLWord w' v.(lprov)) w''.
Proof. intros ? ? ? <-. by apply reg_phys_derive. Qed.

Section instruction_closing.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (** Closes a failed instruction: the state is unchanged. *)
  Lemma instr_close_fail pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) (Φ : griotte_lang.val → iProp Σ) :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ gen_heap_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ FailedV) ==∗
    cerise_state_interp (pc, r, sr, m, st) ∗ from_option Φ False (to_val (Instr Failed)).
  Proof.
    iIntros (Her) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ". iModIntro.
    iSplitR "Hφ HPC Hmap"; last by iApply ("Hφ" with "HPC").
    iExists lpc, lreg, lsreg, lmem, R, C. by iFrame.
  Qed.

  (** Closes an instruction that only moves the PC by [n], as the physical
      [updatePC_gen φ n]. The spec [P] holds of the new PC on success, and of
      the old one on failure. *)
  Lemma instr_close_pc_update pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) n c σ' (Φ : griotte_lang.val → iProp Σ)
      (P : LWord → griotte_lang.val → Prop) :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    (match updatePC_gen (pc, r, sr, m, st) n with
     | Some conf => conf | None => (Failed, (pc, r, sr, m, st)) end) = (c, σ') →
    (∀ lpc', incrementPC_gen lpc n = Some lpc' → P lpc' NextIV) →
    (incrementPC_gen lpc n = None → P lpc FailedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ gen_heap_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' retv, ⌜P lpc' retv⌝ -∗ PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ retv) ==∗
    cerise_state_interp σ' ∗ from_option Φ False (to_val (Instr c)).
  Proof.
    iIntros (Her Hstep HPs HPf) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    destruct (incrementPC_gen lpc n) as [lpc'|] eqn:Hi.
    - destruct (erasure_incrementPC_gen _ _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) as (pc' & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
      iModIntro. iSplitR "Hφ HPC Hmap".
      + iExists lpc', _, _, lmem, R, C. iFrame. iPureIntro. exact Her2.
      + iApply ("Hφ" with "[%] HPC Hmap"). by apply HPs.
    - rewrite (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) in Hstep.
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply ("Hφ" with "[%] HPC Hmap"). by apply HPf.
  Qed.

  (** Closes an instruction that writes one register then increments the PC,
      as the physical [updatePC (update_reg φ dst v)]. The spec [P] holds of
      the new PC and owned registers on success, and of the old ones on
      failure. *)
  Lemma instr_close_reg_update pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) c σ' (Φ : griotte_lang.val → iProp Σ)
      (P : LWord → LReg → griotte_lang.val → Prop) :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    regs ⊆ lreg →
    dst ∈ dom regs →
    reg_word_ok R C v →
    (match updatePC (update_reg (pc, r, sr, m, st) dst w) with
     | Some conf => conf | None => (Failed, (pc, r, sr, m, st)) end) = (c, σ') →
    reg_phys R v w →
    (∀ lpc', incrementPC lpc = Some lpc' → P lpc' (<[dst := v]ₗ> regs) NextIV) →
    (incrementPC lpc = None → P lpc regs FailedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ gen_heap_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' regs' retv, ⌜P lpc' regs' retv⌝ -∗ PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗ Φ retv) ==∗
    cerise_state_interp σ' ∗ from_option Φ False (to_val (Instr c)).
  Proof.
    iIntros (Her Hlregs Hdst Hok Hstep Hw HPs HPf) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ dst v w Her Hok Hw) as Her1.
    rewrite /update_reg /= in Hstep.
    destruct (incrementPC lpc) as [lpc'|] eqn:Hi.
    - destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      assert (is_Some (regs !! dst)) as [vold Hvold] by by apply elem_of_dom.
      iMod (gen_heap_update_inSepM _ _ dst (if decide (dst = cnull) then lnull else v)
        with "Hr Hmap") as "[Hr Hmap]"; first eauto.
      iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
      iModIntro. iSplitR "Hφ HPC Hmap".
      + iExists lpc', _, _, lmem, R, C. iFrame. iPureIntro. exact Her2.
      + iApply ("Hφ" with "[%] HPC [Hmap]"); first by apply HPs.
        by rewrite /linsert_reg.
    - pose proof (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as Hfail.
      rewrite /updatePC Hfail in Hstep.
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply ("Hφ" with "[%] HPC Hmap"). by apply HPf.
  Qed.

  (** Closes an instruction that sets the PC to [lpc'] and writes one
      register, as the physical [update_reg (update_pcc φ pc') dst w]. *)
  Lemma instr_close_reg_set_pc pc (r : Reg) sr m st lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) (lpc' : LWord) (pc' : Word)
      (Φ : griotte_lang.val → iProp Σ) :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    dst ∈ dom regs →
    reg_word_ok R C v →
    reg_phys R v w →
    reg_word_ok R C lpc' →
    reg_phys R lpc' pc' →
    pc_ok lpc'.(lw) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ gen_heap_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc' -∗ ([∗ map] k↦y ∈ <[dst := v]ₗ> regs, k ↦ᵣ y) -∗ Φ NextIV) ==∗
    cerise_state_interp (update_reg (update_pcc (pc, r, sr, m, st) pc') dst w) ∗
    from_option Φ False (to_val (Instr NextI)).
  Proof.
    iIntros (Her Hdst Hok Hw Hokpc Hwpc Hpcok)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ dst v w Her Hok Hw) as Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ lpc' pc' Her1 Hokpc Hwpc Hpcok) as Her2.
    assert (is_Some (regs !! dst)) as [vold Hvold] by by apply elem_of_dom.
    iMod (gen_heap_update_inSepM _ _ dst (if decide (dst = cnull) then lnull else v)
      with "Hr Hmap") as "[Hr Hmap]"; first eauto.
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplitR "Hφ HPC Hmap".
    - iExists lpc', _, _, lmem, R, C. iFrame. iPureIntro. exact Her2.
    - iApply ("Hφ" with "HPC [Hmap]"). by rewrite /linsert_reg.
  Qed.

End instruction_closing.

(** Closes the failing branch of a general rule with [instr_close_fail], then
    the rule's continuation ["Hφ"], and leaves the spec as a pure goal. A
    tactic rather than a lemma: it passes the state hypotheses that
    [wp_instr_step] (and the lifting of the Load and Store rules) introduce
    under fixed names. *)
Ltac instr_fail_close :=
  try iApply bupd_fupd;
  iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|];
  iIntros "HPC Hmap"; iApply "Hφ"; iFrame; iPureIntro.

(** The same, after substituting the failed configuration given by
    [Hstep : (Failed, φ) = (c, σ')]. *)
Ltac instr_fail Hstep :=
  first [injection Hstep as <- <- | simplify_eq]; instr_fail_close.

(** Pure side conditions of the map-form rules ([wp_Get_next], …) applied to
    register maps built by [map_of_regs_k]: a small closed set of goals
    (instruction decoding, register lookups and domains, the PC increment).
    A tactic because the goals vary with the instruction class. *)
Ltac solve_next_side :=
  first [ done
        | by apply incrementPC_add
        | by rewrite /regs_of /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver+
        | by simplify_map_eq
        | by eapply llookup_reg_cnull; simplify_map_eq
        | by rewrite /lz_of_argument /=; simplify_map_eq ].

(** Splits the register map of a post after the write of one register, as
    [iRegsMap]. *)
Ltac iRegsMapWrite H :=
  rewrite ?linsert_reg_cnull ?linsert_reg_not_cnull // ?insert_insert_eq ?insert_singleton;
  iRegsMap H.

Lemma lregs_phys_lookup `{MachineParameters} R (regs : LReg) (r : Reg) x (v : LWord) :
  lregs_phys R regs r → regs !! x = Some v → ∃ s, r !! x = Some (and_tag s v.(lw)).
Proof.
  intros Hincl Hv. destruct (Hincl x v Hv) as (w & Hw & Hrel).
  destruct (reg_phys_and_tag _ _ _ Hrel) as [s ->]. by exists s.
Qed.

Section instruction_outcomes.

  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (* A failed instruction rolls back every tentative write. The premise is
     about all physical register files that include the erased owned
     registers, so no absent register or memory address can be mistaken for
     evidence of runtime failure. *)
  #[local] Lemma wp_instr_failed_map E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) i (regs : LReg) dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ R r sr m st, lregs_phys R regs r →
       exec i pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr (Hfailed R r sr m st Hregs) in Hstep. simplify_eq.
    iModIntro. iSplitR "Hφ HPC Hpc_a Hmap"; last (cbn; iApply "Hφ"; iFrame).
    iExists _, lreg, lsreg, lmem, R, C. by iFrame.
  Qed.

  (* Failure with PC alone; all resources are returned unchanged. *)
  Lemma wp_instr_failed_0 E pc_p pc_g pc_b pc_e pc_a pc_π w i dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st,
       exec i pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hmem) Hφ".
    iApply (wp_instr_failed_map _ _ _ _ _ _ _ _ _ ∅ with "[$HPC $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st _. apply Hfailed.
    - by rewrite big_sepM_empty.
    - iNext. iIntros "(HPC & Hmem & _)".
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 1 explicit register; all resources are returned unchanged. *)
  Lemma wp_instr_failed_1 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st s1, r !! r1 = Some (and_tag s1 w1.(lw)) →
       exec i pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ r1 ↦ᵣ w1 ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ r1 ↦ᵣ w1 ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (wp_instr_failed_map _ _ _ _ _ _ _ _ _ (<[r1 := w1]> ∅)
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st Hincl.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_1 with "Hmap") as "Hr1"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 2 explicit registers; all resources are returned unchanged. *)
  Lemma wp_instr_failed_2 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 r2 w2 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st s1 s2, r !! r1 = Some (and_tag s1 w1.(lw)) →
       r !! r2 = Some (and_tag s2 w2.(lw)) →
       exec i pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ r1 ↦ᵣ w1 ∗ ▷ r2 ↦ᵣ w2 ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hr2 & >Hmem) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (wp_instr_failed_map _ _ _ _ _ _ _ _ _ (<[r1 := w1]> (<[r2 := w2]> ∅))
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st Hincl.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r2 w2 Hincl) as [s2 Hl2]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "(Hr1 & Hr2)"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 3 explicit registers; all resources are returned unchanged. *)
  Lemma wp_instr_failed_3 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 r2 w2 r3 w3 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st s1 s2 s3, r !! r1 = Some (and_tag s1 w1.(lw)) →
       r !! r2 = Some (and_tag s2 w2.(lw)) →
       r !! r3 = Some (and_tag s3 w3.(lw)) →
       exec i pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
         (Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st))) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          ▷ r1 ↦ᵣ w1 ∗
          ▷ r2 ↦ᵣ w2 ∗
          ▷ r3 ↦ᵣ w3 ∗
          ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          r1 ↦ᵣ w1 ∗
          r2 ↦ᵣ w2 ∗
          r3 ↦ᵣ w3 ∗
          pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hr2 & >Hr3 & >Hmem) Hφ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (wp_instr_failed_map _ _ _ _ _ _ _ _ _
      (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅)))
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st Hincl.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r2 w2 Hincl) as [s2 Hl2]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r3 w3 Hincl) as [s3 Hl3]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_3 with "Hmap") as "(Hr1 & Hr2 & Hr3)"; eauto.
      iApply "Hφ". iFrame.
  Qed.
End instruction_outcomes.
