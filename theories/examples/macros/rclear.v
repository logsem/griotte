From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine.proofmode Require Import tactics_helpers map_simpl solve_pure.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.

Section Rclear.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
  Definition rclear_instrs (r : list RegName) := map (λ r_i, move_z r_i 0) r.

  Lemma rclear_instrs_cons rr r: rclear_instrs (rr :: r) = move_z rr 0 :: rclear_instrs r.
  Proof. reflexivity. Qed.

  Definition rclear (a : list Addr) (r : list RegName) : iProp Σ :=
      ([∗ list] k↦a_i;w_i ∈ a;(rclear_instrs r), a_i ↦ₐ w_i)%I.

  Lemma rclear_spec (a : list Addr) (r: list RegName) (rmap : gmap RegName Word) p b e a1 an φ :
    contiguous_between a a1 an →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC_range p b e a1 an →
    list_to_set r = dom rmap →

      ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    ∗ ▷ PC ↦ᵣ WCap p b e a1
    ∗ ▷ rclear a r
    ∗ ▷ (PC ↦ᵣ WCap p b e an ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ WInt 0%Z)
            ∗ rclear a r -∗
            WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Ha Hne Hhd Hvpc Hrdom) "(>Hreg & >HPC & >Hrclear & Hφ)".
    iDestruct (big_sepL2_length with "Hrclear") as %Har.
    iRevert (Hne Har Hhd Hvpc Ha Hrdom).
    iInduction (a) as [| a1'] "IH" forall (r rmap a1 an).
    { iIntros (Hne Har Hhd Hvpc Ha Hrdom). by inversion Hhd; simplify_eq. }
    iIntros (Hne Har Hhd Hvpc Ha Hrdom).
    iApply (wp_bind (fill [SeqCtx])). rewrite /rclear /=.
    (* rewrite -(beq_nat_refl (length r)).  *)destruct r; inversion Har.
    rewrite rclear_instrs_cons.
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    rewrite list_to_set_cons in Hrdom.
    assert (is_Some (rmap !! r)) as [rv ?].
    { rewrite -elem_of_dom -Hrdom. set_solver. }
    iDestruct (big_sepM_delete _ _ r with "Hreg") as "[Hr Hreg]". eauto.
    pose proof (contiguous_between_cons_inv _ _ _ _ Ha) as [-> [a2 [? Hcont'] ] ].
    iApply (wp_move_success_z with "[$HPC $Hr $Ha1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 an|eauto|..].
    iNext. iIntros "(HPC & Ha1 & Hr)". iApply wp_pure_step_later; auto.
    iNext; iIntros "_".
    destruct a.
    { iApply "Hφ". iFrame. inversion Hcont'; subst. iFrame.
      destruct r0; inversion Har. simpl in Hrdom.
      iApply (big_sepM_delete _ _ r). eauto.
      rewrite (_: delete r rmap = ∅). rewrite !big_sepM_empty. eauto.
      apply map_empty. intro. eapply (@not_elem_of_dom _ _ (gset RegName)).
      typeclasses eauto. rewrite dom_delete_L -Hrdom. set_solver. }

    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont') as ->.
    assert (PC ∉ r0). { apply not_elem_of_cons in Hne as [? ?]. auto. }

    destruct (decide (r ∈ r0)).
    { iDestruct (big_sepM_insert with "[$Hreg $Hr]") as "Hreg".
        by rewrite lookup_delete. rewrite insert_delete_insert.
      iApply ("IH" with "Hreg HPC Hrclear [Hφ Ha1]"); eauto.
      { iNext. iIntros "(? & Hreg & ?)". iApply "Hφ". iFrame.
        iApply (big_sepM_delete _ _ r). eauto.
        iDestruct (big_sepM_delete _ _ r with "Hreg") as "[? ?]".
        rewrite lookup_insert //. iFrame. rewrite delete_insert_delete //. }
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_insert_L -Hrdom. set_solver. } }
    { iApply ("IH" with "Hreg HPC Hrclear [Hφ Ha1 Hr]"); eauto.
      { iNext. iIntros "(? & ? & ?)". iApply "Hφ". iFrame.
        iApply (big_sepM_delete _ _ r). eauto. iFrame. }
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_delete_L -Hrdom. set_solver. } }
  Qed.

End Rclear.
