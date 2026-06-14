From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_ghost_theory world_std_revocation.
From griotte Require Import world_interp_stack.
From griotte Require Import stack_object_helpers.

Section Stack_Object_Return_Repair.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  Lemma stack_object_repair_world_for_return
      (W0 W3 W4 : WORLD) (C : CmptName)
      (object_b object_e csp_b csp_e a_stk1 a_stk2 : Addr)
      (l0 l4 : list Addr)
      (stk_head0 : Word) (stk_tail : list Word) :
    let W5 := revoke W4 in
    let object_temps := so_object_temporaries W0 object_b object_e in
    let l0_rest := so_revoked_without_object W0 object_b object_e l0 in
    let l4_no_fresh := filter (fun a => a <> a_stk1) l4 in
    let l4_object := filter (fun a => a ∈ object_temps) l4_no_fresh in
    let l4_rest := filter (fun a => a ∉ object_temps) l4_no_fresh in
    let closing_revoked := l0 ++ l4_rest in
    let closing := closing_revoked ++ finz.seq_between csp_b csp_e in
    extract_temporaries_condition
      W0 (l0 ++ finz.seq_between csp_b csp_e) ->
    extract_temporaries_condition
      W4 (l4 ++ finz.seq_between (a_stk2 ^+ 4)%a csp_e) ->
    W3 = reinstate
      (close_list object_temps (revoke W0)) [a_stk1] ->
    std W3 !! a_stk1 = Some Temporary ->
    related_sts_priv_world W0 W3 ->
    related_sts_pub_world W3 W4 ->
    so_object_addresses object_b object_e
      ## finz.seq_between csp_b csp_e ->
    (csp_b + 1)%a = Some a_stk1 ->
    (a_stk1 + 1)%a = Some a_stk2 ->
    (a_stk2 <= csp_e)%a ->
    (csp_b <= a_stk2 ^+ 4)%a /\
      (a_stk2 ^+ 4 <= csp_e)%a /\
      (a_stk2 + 4)%a = Some (a_stk2 ^+ 4)%a ->
    revoked_addresses W5 l4 ->
    Forall (fun a => std W5 !! a = Some Revoked) l0_rest ->
    Forall (fun a => std W5 !! a = Some Revoked)
      (finz.seq_between a_stk2 csp_e) ->
    std W5 !! csp_b = Some Revoked ->
    world_interp W5 C
    ∗ RevokedResources W0 C l0_rest
    ∗ RevokedResources W4 C l4
    ∗ csp_b ↦ₐ stk_head0
    ∗ [[a_stk2, csp_e]] ↦ₐ [[stk_tail]]
    ==∗
      ∃ stk_head1,
        world_interp W5 C
        ∗ ⌜related_sts_pub_world W0 (close_list closing W5)⌝
        ∗ ⌜NoDup closing⌝
        ∗ ⌜forall a,
             std W0 !! a = Some Temporary -> a ∈ closing⌝
        ∗ close_list_resources_gen
            C W5 closing closing_revoked false
        ∗ [[csp_b, csp_e]] ↦ₐ
            [[stk_head0 :: stk_head1 :: stk_tail]].
  Proof.
    intros W5 object_temps l0_rest l4_no_fresh l4_object l4_rest
      closing_revoked closing.
    intros Hextract0 Hextract4 HW3 Hfresh_W3 Hpriv Hpub Hobject_stack
      Hfresh Hnext Hnext_end Hreturned_bounds Hl4_W5
      Hl0_rest_W5 Hstack_W5 Hhead_W5.
    destruct Hextract0 as [Hl0_nodup Hl0_temporaries].
    destruct Hextract4 as [Hl4_nodup Hl4_temporaries].
    destruct Hreturned_bounds as
      (Hcsp_b_ret & Hret_csp_e & Hret_add).
    iIntros "(Hworld & Hl0_rest & Hl4 & Hhead0 & Htail)".
    subst W3.

    (* Recover the original split between the incoming object's temporary
       addresses and the other addresses revoked from [W0]. *)
    assert (object_temps ⊆ l0) as Htemps_l0.
    { intros x Hx.
      subst object_temps.
      apply list_elem_of_filter in Hx as [Hx_temp Hx_object].
      apply Hl0_temporaries in Hx_temp.
      apply elem_of_app in Hx_temp as [Hx_temp|Hx_temp]; first done.
      rewrite elem_of_disjoint in Hobject_stack.
      exfalso; eapply Hobject_stack; eauto.
    }
    assert (object_temps ≡ₚ
      filter (fun a => a ∈ object_temps) l0) as Htemps_filter.
    { apply NoDup_subset_filter_membership.
      - apply so_object_temporaries_NoDup.
      - apply NoDup_app in Hl0_nodup as [? _]. done.
      - exact Htemps_l0.
    }
    assert (l0 ≡ₚ object_temps ++ l0_rest) as Hl0_partition.
    { subst l0_rest.
      rewrite {1}Htemps_filter.
      apply filter_complement_list.
    }

    (* The incoming object's temporary cells were reinstated before the
       adversary call and remain temporary in its public future [W4]. *)
    assert (Forall (fun x => std W4 !! x = Some Temporary)
      object_temps) as Hobject_temps_W4.
    { apply Forall_forall. intros x Hx.
      apply region_state_pub_temp with
        (reinstate (close_list object_temps (revoke W0)) [a_stk1]); auto.
      rewrite close_list_lookup_not_in.
      - apply close_list_lookup_in.
        + cbn. apply revoke_lookup_Monotemp.
          subst object_temps.
          by apply list_elem_of_filter in Hx as [? _].
        + exact Hx.
      - intro Hx_fresh.
        apply list_elem_of_singleton in Hx_fresh; subst x.
        rewrite elem_of_disjoint in Hobject_stack.
        eapply Hobject_stack.
        + subst object_temps.
          by apply list_elem_of_filter in Hx as [_ ?].
        + apply elem_of_finz_seq_between.
          solve_addr+Hfresh Hnext Hnext_end.
    }

    (* The fresh one-cell object is temporary in [W4], so revocation puts it
       in [l4].  Split it out before closing the returned resources. *)
    assert (a_stk1 ∈ l4) as Hfresh_l4.
    { assert (a_stk1 ∉ finz.seq_between (a_stk2 ^+ 4)%a csp_e).
      { apply not_elem_of_finz_seq_between.
        solve_addr+Hfresh Hnext Hnext_end Hcsp_b_ret Hret_csp_e Hret_add. }
      assert (std W4 !! a_stk1 = Some Temporary) as Htemp.
      { eapply region_state_pub_temp; eauto. }
      apply Hl4_temporaries in Htemp.
      apply elem_of_app in Htemp as [?|?]; done.
    }

    assert (l4 ≡ₚ a_stk1 :: l4_no_fresh) as Hl4_partition.
    { apply NoDup_Permutation.
      - apply NoDup_app in Hl4_nodup as [? _]. exact H.
      - apply NoDup_cons; split.
        + subst l4_no_fresh. rewrite list_elem_of_filter.
          intros [Hneq _]. by apply Hneq.
        + apply NoDup_filter.
          apply NoDup_app in Hl4_nodup as [? _]. exact H.
      - intros x. subst l4_no_fresh.
        rewrite elem_of_cons list_elem_of_filter.
        destruct (decide (x = a_stk1)) as [->|Hneq]; set_solver.
    }
    assert (a_stk1 ∉ l4_no_fresh) as Hfresh_not_l4_no_fresh.
    { subst l4_no_fresh. rewrite list_elem_of_filter.
      intros [Hneq _]. by apply Hneq. }
    assert (l4_no_fresh ≡ₚ l4_object ++ l4_rest)
      as Hl4_no_fresh_partition.
    { subst l4_object l4_rest.
      apply filter_complement_list. }

    (* The only overlap between the initial and returned revoked lists is the
       incoming object's temporary portion. *)
    assert (object_temps ≡ₚ l4_object) as Hobject_l4_object.
    { apply NoDup_Permutation.
      - apply so_object_temporaries_NoDup.
      - subst l4_object. apply NoDup_filter.
        subst l4_no_fresh. apply NoDup_filter.
        apply NoDup_app in Hl4_nodup as [? _]. exact H.
      - intros x; split; intros Hx.
        + subst l4_object.
          apply list_elem_of_filter; split; first exact Hx.
          subst l4_no_fresh.
          apply list_elem_of_filter; split.
          * intros Heq; subst x.
            rewrite elem_of_disjoint in Hobject_stack.
            eapply Hobject_stack.
            { subst object_temps.
              by apply list_elem_of_filter in Hx as [_ ?]. }
            apply elem_of_finz_seq_between.
            solve_addr+Hfresh Hnext Hnext_end.
          * assert (std W4 !! x = Some Temporary) as Hx_temp.
            { rewrite Forall_forall in Hobject_temps_W4.
              by apply Hobject_temps_W4. }
            apply Hl4_temporaries in Hx_temp.
            apply elem_of_app in Hx_temp as [Hx_l4|Hx_tail]; first exact Hx_l4.
            exfalso.
            rewrite elem_of_disjoint in Hobject_stack.
            eapply Hobject_stack.
            { subst object_temps.
              by apply list_elem_of_filter in Hx as [_ ?]. }
            apply elem_of_finz_seq_between in Hx_tail.
            apply elem_of_finz_seq_between.
            solve_addr+Hx_tail Hfresh Hnext Hcsp_b_ret Hret_csp_e Hret_add.
        + subst l4_object.
          by apply list_elem_of_filter in Hx as [? _].
    }
    assert (l0 ≡ₚ l0_rest ++ l4_object) as Hl0_repair_partition.
    { rewrite Hl0_partition Hobject_l4_object. apply Permutation_app_comm. }

    assert (forall x, x ∈ l0 ++ finz.seq_between csp_b csp_e ->
      std W5 !! x = Some Revoked) as Hinitial_W5.
    { intros x Hx.
      apply elem_of_app in Hx as [Hx|Hx].
      - rewrite Hl0_partition in Hx.
        apply elem_of_app in Hx as [Hx|Hx].
        + cbn. apply revoke_lookup_Monotemp.
          rewrite Forall_forall in Hobject_temps_W4.
          by apply Hobject_temps_W4.
        + rewrite Forall_forall in Hl0_rest_W5.
          by apply Hl0_rest_W5.
      - rewrite (finz_seq_between_cons csp_b csp_e) in Hx;
          last solve_addr+Hfresh Hnext Hnext_end.
        apply elem_of_cons in Hx as [->|Hx]; first exact Hhead_W5.
        replace (csp_b ^+ 1)%a with a_stk1 in Hx by solve_addr+Hfresh.
        rewrite (finz_seq_between_cons a_stk1 csp_e) in Hx;
          last solve_addr+Hnext Hnext_end.
        apply elem_of_cons in Hx as [->|Hx].
        + rewrite /revoked_addresses Forall_forall in Hl4_W5.
          by apply Hl4_W5.
        + replace (a_stk1 ^+ 1)%a with a_stk2 in Hx by solve_addr+Hnext.
          rewrite Forall_forall in Hstack_W5.
          by apply Hstack_W5.
    }

    iDestruct (RevokedResources_disjoint with "[$Hl0_rest $Hl4]")
      as %Hrest_l4_disjoint.
    iAssert (RevokedResources W4 C l4_no_fresh
             ∗ RevokedResources W4 C [a_stk1])%I
      with "[Hl4]" as "[Hl4 Hfresh_resource]".
    { rewrite Hl4_partition.
      replace (a_stk1 :: l4_no_fresh) with
        ([a_stk1] ++ l4_no_fresh) by done.
      iDestruct (RevokedResources_app with "Hl4") as "[$ $]". }

    (* First view the repaired world as a public future of [W4].  This
       justifies converting all returned revoked resources for [closing]. *)
    assert (related_sts_pub_world W4 (close_list closing W5)) as Hpub4.
    { subst W5.
      assert (l4 ++ finz.seq_between (a_stk2 ^+ 4)%a csp_e
        ⊆ closing) as Hsubset.
      { intros x Hx.
        apply elem_of_app in Hx as [Hx|Hx].
        - rewrite Hl4_partition in Hx.
          apply elem_of_cons in Hx as [->|Hx].
          + apply elem_of_app; right.
            apply elem_of_finz_seq_between.
            solve_addr+Hfresh Hnext Hnext_end.
          + rewrite Hl4_no_fresh_partition in Hx.
            apply elem_of_app in Hx as [Hx|Hx].
            * apply elem_of_app; left.
              subst closing_revoked.
              apply elem_of_app; left.
              rewrite Hl0_repair_partition.
              apply elem_of_app; right; exact Hx.
            * apply elem_of_app; left.
              subst closing_revoked.
              apply elem_of_app; right; exact Hx.
        - apply elem_of_app; right.
          apply elem_of_finz_seq_between in Hx.
          apply elem_of_finz_seq_between.
          solve_addr+Hx Hfresh Hnext Hcsp_b_ret Hret_csp_e Hret_add.
      }
      destruct W4 as [ [W4std W4cus] W4seals]; cbn.
      split; [|split];
        [|apply related_sts_pub_refl|apply related_sts_seals_std_refl]; cbn.
      split.
      - setoid_rewrite <- close_list_dom_eq.
        setoid_rewrite <- revoke_dom_eq. done.
      - intros x ρ4 ρ5 Hx4 Hx5.
        destruct ρ4.
        + assert (x ∈ l4 ++ finz.seq_between (a_stk2 ^+ 4)%a csp_e)
            as Hx_close by (apply Hl4_temporaries; auto).
          rewrite close_list_std_sta_revoked in Hx5; auto.
          * simplify_eq; apply rtc_refl.
          * by apply revoke_lookup_Monotemp.
        + apply revoke_lookup_Perm in Hx4.
          rewrite -close_list_std_sta_same_alt in Hx5; [|intro];
            simplify_eq; apply rtc_refl.
        + destruct ρ5; try apply rtc_refl; apply rtc_once; econstructor.
    }
    iAssert (close_list_resources_gen
      C W5 closing l4_no_fresh false)%I with "[Hl4]" as "Hl4".
    { iApply close_list_resources_gen_eq; eauto.
      rewrite world_ghost_theory.RevokedResources_eq. done. }

    (* The same repaired world must also be a public future of the switcher
       frame's original world [W0]. *)
    assert (related_sts_pub_world W0 (close_list closing W5)) as Hpub0.
    { subst W5.
      assert (l0 ++ finz.seq_between csp_b csp_e ⊆ closing) as Hsubset.
      { intros x Hx. apply elem_of_app in Hx as [Hx|Hx].
        - apply elem_of_app; left. subst closing_revoked.
          by apply elem_of_app; left.
        - by apply elem_of_app; right. }
      destruct W0 as [ [W0std W0cus] W0seals].
      destruct W4 as [ [W4std W4cus] W4seals]. cbn in *.
      split; [|split]; cbn; cycle 1.
      - destruct Hpriv as (_ & Hcus03 & _).
        destruct Hpub as (_ & Hcus34 & _).
        clear -Hcus03 Hcus34.
        cbn in *.
        eapply related_sts_pub_trans; eauto.
        apply related_sts_pub_refl.
      - destruct Hpriv as (_ & _ & Hseals03).
        destruct Hpub as (_ & _ & Hseals34).
        clear -Hseals03 Hseals34.
        cbn in *.
        eapply related_sts_seals_trans; eauto.
      - split.
        + destruct Hpriv as [ [Hdom03 _] _].
          destruct Hpub as [ [Hdom34 _] _].
          clear -Hdom03 Hdom34.
          setoid_rewrite <- close_list_dom_eq.
          setoid_rewrite <- revoke_dom_eq. set_solver.
        + intros x ρ0 ρ5 Hx0 Hx5.
          destruct ρ0.
          * assert (x ∈ l0 ++ finz.seq_between csp_b csp_e)
              as Hx_close by (apply Hl0_temporaries; auto).
            specialize (Hinitial_W5 x Hx_close).
            rewrite close_list_std_sta_revoked in Hx5; auto.
            simplify_eq; apply rtc_refl.
          * assert (std (W4std, W4cus, W4seals) !! x = Some Permanent)
              as Hx4.
            { eapply region_state_priv_perm.
              - eapply related_sts_priv_pub_trans_world; eauto.
              - exact Hx0. }
            apply revoke_lookup_Perm in Hx4.
            rewrite -close_list_std_sta_same_alt in Hx5;
              [|intro Hcontra]; cbn; simplify_eq.
            { rewrite Hx4 in Hx5; simplify_eq; apply rtc_refl. }
            rewrite Hx4 in Hcontra; done.
          * destruct ρ5; try apply rtc_refl; apply rtc_once; econstructor.
    }
    iAssert (close_list_resources_gen
      C W5 closing l0_rest false)%I with "[Hl0_rest]" as "Hl0_rest".
    { iApply close_list_resources_gen_eq; eauto.
      rewrite world_ghost_theory.RevokedResources_eq. done. }

    (* Separate the returned resources into the overlap already represented
       by [l0] and the genuinely new revoked addresses. *)
    iAssert (close_list_resources_gen C W5 closing l4_rest false
             ∗ close_list_resources_gen C W5 closing l4_object false)%I
      with "[Hl4]" as "[Hl4_rest Hl4_object]".
    { rewrite /close_list_resources_gen Hl4_no_fresh_partition.
      iDestruct (big_sepL_app with "Hl4") as "[Hobject Hrest]".
      iFrame. }
    iDestruct (close_list_resources_gen_separation
      with "[$Hhead0] [$Hl4_rest]") as %Hhead_not_rest.
    iDestruct (close_addr_list_gen_resources_separation
      with "[Hfresh_resource] [$Hl4_rest]") as %Hfresh_not_rest.
    { iClear "#".
      rewrite /RevokedResources /close_addr_resources /=.
      iDestruct "Hfresh_resource"
        as "[(%pa & %Pa & $ & $ & (%va & $ & $ & $ & ?)) _]".
      by rewrite mono_temporary_eq. }
    iDestruct (close_list_resources_gen_separation_many
      with "[$Htail] [$Hl4_rest]") as %Htail_not_rest.

    iAssert (close_list_resources_gen C W5 closing l0 false)%I
      with "[Hl0_rest Hl4_object]" as "Hl0".
    { rewrite /close_list_resources_gen Hl0_repair_partition.
      iApply big_sepL_app; iFrame. }
    iAssert (close_list_resources_gen C W5 closing closing_revoked false)%I
      with "[Hl0 Hl4_rest]" as "Hclosing".
    { subst closing_revoked.
      rewrite /close_list_resources_gen. iApply big_sepL_app; iFrame. }

    (* Resource separation supplies the cross-list disjointness needed to
       show that the final closing list has no duplicates. *)
    assert (NoDup closing) as Hclosing_nodup.
    { subst closing closing_revoked.
      apply NoDup_app. split; [|split].
      - apply NoDup_app. split; [|split].
        + apply NoDup_app in Hl0_nodup as [? _]. exact H.
        + intros x Hx0 Hx4.
          apply list_elem_of_filter in Hx4 as
            [Hx_not_object Hx_l4_no_fresh].
          rewrite Hl0_partition in Hx0.
          apply elem_of_app in Hx0 as [Hx0|Hx0].
          * by apply Hx_not_object.
          * rewrite elem_of_disjoint in Hrest_l4_disjoint.
            eapply Hrest_l4_disjoint; eauto.
            subst l4_no_fresh.
            by apply list_elem_of_filter in Hx_l4_no_fresh as [_ ?].
        + subst l4_rest l4_no_fresh.
          repeat apply NoDup_filter.
          apply NoDup_app in Hl4_nodup as [? _]. exact H.
      - intros x Hx Hx_stack.
        apply elem_of_app in Hx as [Hx|Hx].
        + apply NoDup_app in Hl0_nodup as (_ & Hdisjoint & _).
          eapply Hdisjoint; eauto.
        + rewrite (finz_seq_between_cons csp_b csp_e) in Hx_stack;
            last solve_addr+Hfresh Hnext Hnext_end.
          apply elem_of_cons in Hx_stack as [->|Hx_stack].
          { exact (Hhead_not_rest Hx). }
          replace (csp_b ^+ 1)%a with a_stk1 in Hx_stack
            by solve_addr+Hfresh.
          rewrite (finz_seq_between_cons a_stk1 csp_e) in Hx_stack;
            last solve_addr+Hnext Hnext_end.
          apply elem_of_cons in Hx_stack as [->|Hx_stack].
          { exact (Hfresh_not_rest Hx). }
          replace (a_stk1 ^+ 1)%a with a_stk2 in Hx_stack
            by solve_addr+Hnext.
          rewrite elem_of_disjoint in Htail_not_rest.
          eapply Htail_not_rest; eauto.
      - apply finz_seq_between_NoDup.
    }
    assert (forall x, std W0 !! x = Some Temporary -> x ∈ closing)
      as Htemps_closing.
    { intros x Hx. apply Hl0_temporaries in Hx.
      apply elem_of_app in Hx as [Hx|Hx].
      - apply elem_of_app; left. subst closing_revoked.
        by apply elem_of_app; left.
      - by apply elem_of_app; right. }

    (* Finally recover the fresh cell's points-to assertion and join the
       secret head, fresh cell, and returned tail into one stack region. *)
    iDestruct "Hfresh_resource"
      as "[(%pa & %Pa & _ & _ & (%va & _ & Hfresh_pointsto & _ & _)) _]".
    iDestruct (region_pointsto_cons a_stk1 a_stk2 csp_e
      with "[$Hfresh_pointsto $Htail]") as "Hstack";
      [exact Hnext|exact Hnext_end|].
    iDestruct (region_pointsto_cons csp_b a_stk1 csp_e
      with "[$Hhead0 $Hstack]") as "Hstack";
      [exact Hfresh|solve_addr+Hnext Hnext_end|].

    iModIntro. iExists va. iFrame "Hworld".
    iSplit; first (iPureIntro; exact Hpub0).
    iSplit; first (iPureIntro; exact Hclosing_nodup).
    iSplit; first (iPureIntro; exact Htemps_closing).
    iFrame.
  Qed.

End Stack_Object_Return_Repair.
