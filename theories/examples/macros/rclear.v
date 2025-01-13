From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (* -------------------------------------- RCLEAR ----------------------------------- *)
  (* the following macro clears registers in r. a denotes the list of addresses
     containing the instructions for the clear: |a| = |r| *)
     Definition rclear_instrs (r : list RegName) := map (λ r_i, move_z r_i 0) r.

     Lemma rclear_instrs_cons rr r: rclear_instrs (rr :: r) = move_z rr 0 :: rclear_instrs r.
     Proof. reflexivity. Qed.

     Definition rclear (a : list Addr) (r : list RegName) : iProp Σ :=
         ([∗ list] k↦a_i;w_i ∈ a;(rclear_instrs r), a_i ↦ₐ w_i)%I.

     Lemma rclear_spec (a : list Addr) (r: list RegName) (rmap : gmap RegName Word) p g b e a1 an φ :
       contiguous_between a a1 an →
       ¬ PC ∈ r → hd_error a = Some a1 →
       isCorrectPC_range p g b e a1 an →
       list_to_set r = dom (gset RegName) rmap →

         ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
       ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
       ∗ ▷ rclear a r
       ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,an) ∗ ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ inl 0%Z)
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
       { rewrite elem_of_gmap_dom -Hrdom. set_solver. }
       iDestruct (big_sepM_delete _ _ r with "Hreg") as "[Hr Hreg]". eauto.
       pose proof (contiguous_between_cons_inv _ _ _ _ Ha) as [-> [a2 [? Hcont'] ] ].
       iApply (wp_move_success_z with "[$HPC $Hr $Ha1]");
         [apply decode_encode_instrW_inv|iCorrectPC a1 an|eauto|..].
       iNext. iIntros "(HPC & Ha1 & Hr)". iApply wp_pure_step_later; auto. iNext.
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
           by rewrite lookup_delete. rewrite insert_delete.
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

     (* Lemma used to fit the rclear spec to the value relation *)
     Lemma rmap_zero_extract (rmap : Reg) :
       ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ inl 0%Z) -∗
       ∃ rmap', ([∗ map] r_i↦y ∈ rmap', r_i ↦ᵣ y %Z) ∗ ⌜dom (gset RegName) rmap' = dom (gset RegName) rmap ∧ (∀ x : RegName, x ∈ (dom (gset RegName) rmap') → rmap' !! x = Some (inl 0)%Z)⌝.
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

   (* Slightly shorter, constructive version of the same proof, that requires an auxiliary list. *)
     Lemma rmap_zero_extract_list (rmap : Reg) l :
       dom (gset RegName) rmap = (list_to_set l : gset RegName) → ([∗ map] r_i↦_ ∈ rmap, r_i ↦ᵣ inl 0%Z) -∗
       ∃ rmap', ([∗ map] r_i↦y ∈ rmap', r_i ↦ᵣ y %Z) ∗ ⌜dom (gset RegName) rmap' = list_to_set l ∧ (∀ x : RegName, x ∈ (dom (gset RegName) rmap') → rmap' !! x = Some (inl 0)%Z)⌝.
     Proof.
       set (rmap' := ((create_gmap_default l (inl 0%Z : Word)) : Reg)).
       iIntros (Hdom) "Hmap".
       iExists rmap'.
       iSplitL.
       - iApply (big_sepM_mono (λ k _, k ↦ᵣ inl 0%Z))%I.
         {
           iIntros (k x Hcreate) "Hzero".
           pose proof (create_gmap_default_dom l (inl 0%Z : Word)) as Hdom'.
           assert (k ∈ l) as HkDom.
           { assert (k ∈ (list_to_set l : gset RegName) ). rewrite -Hdom'. eapply elem_of_dom_2; eauto. apply (elem_of_list_to_set k l) in H; auto. }
           rewrite (create_gmap_default_lookup _ (inl 0%Z : Word) k) in HkDom |- * => HkDom. subst rmap'.
           rewrite Hcreate in HkDom. inversion HkDom; done.
         }
         rewrite !big_sepM_dom.
         rewrite create_gmap_default_dom Hdom. iExact "Hmap".
       - iPureIntro. split.
         * by rewrite create_gmap_default_dom.
         * intros x Hxdom. subst rmap'.
           rewrite create_gmap_default_dom (elem_of_list_to_set _ l) in Hxdom |- * => HxDom.
           rewrite /RegLocate. apply (create_gmap_default_lookup l (inl 0%Z :Word) x) in HxDom. by rewrite HxDom.
     Qed.

     (* rclear spec in terms of a new map; this one should be a bit more practical in proofs - should also help rewrite parts of the awkward example *)
     Lemma rclear_spec_gmap (a : list Addr) (r: list RegName) (rmap : gmap RegName Word) p g b e a1 an φ :
     contiguous_between a a1 an →
     ¬ PC ∈ r → hd_error a = Some a1 →
     isCorrectPC_range p g b e a1 an →
     list_to_set r = dom (gset RegName) rmap →

       ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
     ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a1)
     ∗ ▷ rclear a r
     ∗ ▷ (PC ↦ᵣ inr ((p,g),b,e,an) ∗
             (∃ rmap', ([∗ map] r_i↦y ∈ rmap', r_i ↦ᵣ y %Z) ∗ ⌜dom (gset RegName) rmap' = (list_to_set r) ∧ (∀ x : RegName, x ∈ (dom (gset RegName) rmap') → rmap' !! x = Some (inl 0%Z))⌝)
             ∗ rclear a r -∗
             WP Seq (Instr Executable) {{ φ }})
     ⊢ WP Seq (Instr Executable) {{ φ }}.
   Proof.
     iIntros (Ha Hne Hhd Hvpc Hrdom) "(>Hreg & >HPC & >Hrclear & Hφ)".
     iApply (rclear_spec with "[- $Hreg $HPC $Hrclear]"); eauto.
     iNext. iIntros "(HPC & Hreg & Hrclear)".
     iDestruct (rmap_zero_extract with "Hreg") as "Hreg'"; auto.
     iDestruct "Hreg'" as (rmap') "(Hreg & Hdom & Hinl0)".
     rewrite -Hrdom.
     iApply "Hφ". iFrame. iExists rmap'. iFrame. iSplitL "Hdom"; iFrame.
   Qed.

End stack_macros.
