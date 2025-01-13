From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel stack_macros_helpers.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.
From cap_machine Require Import macros.
From cap_machine.binary_model.rules_binary Require Import rules_binary rules_binary_StoreU_derived.

(** This file contains specification side specs for macros.
    The file contains pushz, rclear and prepstack (for now, only the macros needed by example)
 *)

Ltac iPrologue_s prog :=
  (try iPrologue_pre);
  iDestruct prog as "[Hi Hprog]".

Ltac iEpilogue_s :=
   iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj";auto;
   iSimpl in "Hj".

Section macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.


  (* --------------------------------------------------------------------------------- *)
  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition rclear_s (a : list Addr) (r : list RegName) : iProp Σ :=
      ([∗ list] k↦a_i;w_i ∈ a;(rclear_instrs r), a_i ↣ₐ w_i)%I.

  Lemma rclear_s_spec E (a : list Addr) (r: list RegName) (rmap : gmap RegName Word) p g b e a1 an :
    contiguous_between a a1 an →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC_range p g b e a1 an →
    list_to_set r = dom (gset RegName) rmap →
     nclose specN ⊆ E →

     spec_ctx
    ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↣ᵣ w_i)
    ∗ ▷ PC ↣ᵣ inr (p,g,b,e,a1)
    ∗ ▷ rclear_s a r
     ={E}=∗ ⤇ Seq (Instr Executable)
         ∗ PC ↣ᵣ inr (p,g,b,e,an)
         ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↣ᵣ inl 0%Z)
         ∗ rclear_s a r.
  Proof.
    iIntros (Ha Hne Hhd Hvpc Hrdom Hnclose) "(#Hspec & Hj & >Hreg & >HPC & >Hrclear)".
    iDestruct (big_sepL2_length with "Hrclear") as %Har.
    iRevert (Hne Har Hhd Hvpc Ha Hrdom).
    iInduction (a) as [| a1'] "IH" forall (r rmap a1 an).
    { iIntros (Hne Har Hhd Hvpc Ha Hrdom). by inversion Hhd; simplify_eq. }
    iIntros (Hne Har Hhd Hvpc Ha Hrdom).
    rewrite /rclear_s /=.
    (* rewrite -(beq_nat_refl (length r)).  *)destruct r; inversion Har.
    rewrite rclear_instrs_cons.
    iDestruct (big_sepL2_cons with "Hrclear") as "[Ha1 Hrclear]".
    rewrite list_to_set_cons in Hrdom.
    assert (is_Some (rmap !! r)) as [rv ?].
    { rewrite elem_of_gmap_dom -Hrdom. set_solver. }
    iDestruct (big_sepM_delete _ _ r with "Hreg") as "[Hr Hreg]". eauto.
    pose proof (contiguous_between_cons_inv _ _ _ _ Ha) as [-> [a2 [? Hcont'] ] ].
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hr $Ha1]")
      as "(Hj & HPC & Ha1 & Hr)";
      [apply decode_encode_instrW_inv|iCorrectPC a1 an|eauto|auto..].
    iEpilogue_s.
    destruct a.
    { iFrame. inversion Hcont'; subst. iFrame.
      destruct r0; inversion Har. simpl in Hrdom.
      iApply (big_sepM_delete _ _ r). eauto.
      rewrite (_: delete r rmap = ∅). rewrite !big_sepM_empty. eauto.
      apply map_empty. intro. eapply (@not_elem_of_dom _ _ (gset RegName)).
      typeclasses eauto. rewrite dom_delete_L -Hrdom. set_solver. }

    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont') as ->.
    assert (PC ∉ r0). { apply not_elem_of_cons in Hne as [? ?]. auto. }

    destruct (decide (r ∈ r0)).
    { iDestruct (big_sepM_insert with "[$Hreg $Hr]") as "Hreg".
        by rewrite lookup_delete. rewrite insert_delete.
      (* iCombine "Ha1" "Hrclear" as "Hrclear". *) iSimpl. iFrame "Ha1".
      iMod ("IH" with "Hj Hreg HPC Hrclear [] [] [] [] [] []") as "($&$&Hregs&$)";iFrame;eauto.
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_insert_L -Hrdom. set_solver. }
      { iApply (big_sepM_delete _ _ r). eauto.
        iDestruct (big_sepM_delete _ _ r with "Hregs") as "[? ?]".
        rewrite lookup_insert //. iFrame. rewrite delete_insert_delete //. } }
    { iMod ("IH" with "Hj Hreg HPC Hrclear [] [] [] [] [] []") as "($&$&Hregs&$)";iFrame;eauto.
      { iPureIntro. intros ? [? ?]. apply Hvpc. solve_addr. }
      { iPureIntro. rewrite dom_delete_L -Hrdom. set_solver. }
      iApply (big_sepM_delete _ _ r). eauto. iFrame. done.
    }
  Qed.

  (* Lemma used to fit the rclear spec to the value relation *)
  Lemma rmap_zero_extract (rmap : Reg) :
    ([∗ map] r_i↦_ ∈ rmap, r_i ↣ᵣ inl 0%Z) -∗
       ∃ rmap', ([∗ map] r_i↦y ∈ rmap', r_i ↣ᵣ y %Z) ∗ ⌜dom (gset RegName) rmap' = dom (gset RegName) rmap ∧ (∀ x : RegName, x ∈ (dom (gset RegName) rmap') → rmap' !! x = Some (inl 0)%Z)⌝.
  Proof.
       iIntros "Hmap".
       assert (∃ rlist, map_to_list rmap ≡ₚ rlist) as [rlist HPerm]. eexists; eauto.
       pose proof (NoDup_fst_map_to_list rmap) as HnoDup.
       iRevert (HPerm HnoDup). iInduction (rlist) as [| a_head a_tail] "IH" forall (rmap); iIntros (HPerm HnoDup).
       - iExists ∅. apply (map_to_list_empty_inv_alt rmap) in HPerm as ->. auto.
       - eapply NoDup_map_to_cons in HnoDup; eauto.
         destruct a_head.
         apply (map_to_list_insert_inv rmap) in HPerm as ->.
         cbn in HnoDup. inversion HnoDup as [| r' l' Hne HdoDup]. simplify_eq.
         iDestruct (big_sepM_insert with "Hmap") as "[Ha Htail]".
         {
           apply not_elem_of_list_to_map_1.
           revert Hne; clear. induction a_tail.
           - intros H HFalse. by inversion HFalse.
           - intros HnotIn. rewrite fmap_cons.
             rewrite !not_elem_of_cons in HnotIn |- * => HnotIn. destruct HnotIn as [Hnota HnotTail].
             split; auto. }

         iSpecialize ("IH" $! (list_to_map a_tail) with "Htail").
         assert (map_to_list (list_to_map a_tail) ≡ₚ a_tail) as Hinv.
         { apply map_to_list_to_map. done. }
         unshelve iSpecialize ("IH" $! Hinv _).
         { rewrite map_to_list_to_map; auto. }
         iDestruct "IH" as  (rmap0) "[Heq' [HnoDup' IH]]".
         iExists (<[r:=inl 0%Z]> rmap0).
         iSplitL "Ha Heq'".
         iAssert (⌜rmap0 !! r = None⌝)%I as %HrNone.
         { destruct (rmap0!!r) eqn:Hr; last auto.
           iDestruct (big_sepM_delete with "Heq'") as "[Heq' _]"; eauto.
           iDestruct (regname_dupl_false with "Ha Heq'") as "HFalse"; auto.
         }
         iDestruct (big_sepM_insert with "[$Heq' $Ha]") as "Hmap"; eauto.
         iSplitL "HnoDup'".
         + rewrite !dom_insert_L. iDestruct "HnoDup'" as %->. iPureIntro. reflexivity.
         + iDestruct "IH" as %IH. iPureIntro. intros x Hdom.
           destruct (decide (r = x)).
           ++ simplify_eq; by rewrite /RegLocate lookup_insert.
           ++ rewrite /RegLocate lookup_insert_ne; [|auto].
               rewrite dom_insert_L elem_of_union in Hdom |- * => Hdom.
               destruct Hdom as [Hsin | Hrest].
           * apply elem_of_singleton in Hsin. simpl in Hsin. simplify_map_eq.
             apply elem_of_singleton in Hsin. congruence.
           * specialize (IH x Hrest); auto.
  Qed.

  (* rclear spec in terms of a new map; this one should be a bit more practical in proofs *)
  Lemma rclear_s_spec_gmap E (a : list Addr) (r: list RegName) (rmap : gmap RegName Word) p g b e a1 an :
    contiguous_between a a1 an →
    ¬ PC ∈ r → hd_error a = Some a1 →
    isCorrectPC_range p g b e a1 an →
    list_to_set r = dom (gset RegName) rmap →
    nclose specN ⊆ E →

    spec_ctx
      ∗ ⤇ Seq (Instr Executable)
      ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↣ᵣ w_i)
      ∗ ▷ PC ↣ᵣ inr ((p,g),b,e,a1)
      ∗ ▷ rclear_s a r
      ={E}=∗ ⤇ Seq (Instr Executable)
          ∗ PC ↣ᵣ inr ((p,g),b,e,an) ∗
          (∃ rmap', ([∗ map] r_i↦y ∈ rmap', r_i ↣ᵣ y %Z) ∗ ⌜dom (gset RegName) rmap' = (list_to_set r) ∧ (∀ x : RegName, x ∈ (dom (gset RegName) rmap') → rmap' !! x = Some (inl 0%Z))⌝)
          ∗ rclear_s a r.
   Proof.
     iIntros (Ha Hne Hhd Hvpc Hrdom Hnclose) "(#Hspec & Hj & >Hreg & >HPC & >Hrclear)".
     iMod (rclear_s_spec with "[- $Hspec $Hj $Hreg $HPC $Hrclear]") as "(?&?&Hreg&?)"; eauto.
     iDestruct (rmap_zero_extract with "Hreg") as "Hreg'"; auto.
     iDestruct "Hreg'" as (rmap') "(Hreg & Hdom & Hinl0)".
     rewrite -Hrdom. iFrame. iExists rmap'. iFrame. iSplitL "Hdom"; iFrame;done.
   Qed.

End macros.
