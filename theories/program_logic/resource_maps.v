From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac auth gmap.
From griotte Require Export iris_extra stdpp_extra machine_base resources.

(** * Maps of points-to

    The register, system-register and memory maps of points-to, and their
    relation to the heaps of the state interpretation. No WP. *)

Section resource_maps.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
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
    sr1 ↦ₓ w1 -∗
    ([∗ map] k↦y ∈ {[sr1 := w1]}, k ↦ₓ y).
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma sregs_of_map_1 (sr1: SRegName) (w1: LWord) :
    ([∗ map] k↦y ∈ {[sr1 := w1]}, k ↦ₓ y) -∗
    sr1 ↦ₓ w1.
  Proof. rewrite big_sepM_singleton; auto. Qed.

  Lemma sregname_neq sr1 sr2 w1 w2 :
    sr1 ↦ₓ w1 -∗ sr2 ↦ₓ w2 -∗ ⌜ sr1 ≠ sr2 ⌝.
  Proof.
    iIntros "H1 H2" (->).
    iDestruct (pointsto_valid_2 with "H1 H2") as %[Hv _].
    by apply dfrac_full_exclusive in Hv.
  Qed.

  Lemma map_of_sregs_2 (sr1 sr2: SRegName) (w1 w2: LWord) :
    sr1 ↦ₓ w1 -∗ sr2 ↦ₓ w2 -∗
    ([∗ map] k↦y ∈ (<[sr1:=w1]> (<[sr2:=w2]> ∅)), k ↦ₓ y) ∗ ⌜ sr1 ≠ sr2 ⌝.
  Proof.
    iIntros "H1 H2". iPoseProof (sregname_neq with "H1 H2") as "%Hne".
    rewrite !big_sepM_insert ?big_sepM_empty; eauto.
    2: by apply lookup_insert_None; split; eauto.
    iFrame. eauto.
  Qed.

  Lemma sregs_of_map_2 (sr1 sr2: SRegName) (w1 w2: LWord) :
    sr1 ≠ sr2 →
    ([∗ map] k↦y ∈ (<[sr1:=w1]> (<[sr2:=w2]> ∅)), k ↦ₓ y) -∗
    sr1 ↦ₓ w1 ∗ sr2 ↦ₓ w2.
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

End resource_maps.
