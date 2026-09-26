From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_ghost_theory world_std_revocation.
From griotte Require Import world_interp_stack.
From griotte Require Import stack_object_helpers.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import wp_rules_interp.

Section Stack_Object_Return_Repair.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP : MachineParameters}.
  Lemma stack_object_revoked_pointsto_disjoint
      (W : WORLD) (C : CmptName) (l : list Addr)
      (a : Addr) (v : Word) :
    heap_cell_live (heap_std W) a ->
    a ↦ₐ v -∗ RevokedResources W C l -∗ ⌜a ∉ l⌝.
  Proof.
    iIntros (Hlive) "Ha Hl".
    destruct (decide (a ∈ l)) as [Hin|Hnotin]; last by iPureIntro.
    iDestruct (big_sepL_elem_of with "Hl") as "Hcell"; first exact Hin.
    iDestruct "Hcell" as (p φ) "(_ & _ & Hcell)".
    rewrite /heap_cell_live in Hlive.
    iEval (rewrite Hlive) in "Hcell".
    iDestruct "Hcell" as (w) "(_ & Hw & _)".
    iDestruct (pointsto_valid_2 with "Ha Hw") as %[Hbad _]. done.
  Qed.

  Lemma stack_object_revoked_pointsto_disjoint_frame
      (W : WORLD) (C : CmptName) (l : list Addr)
      (a : Addr) (v : Word) :
    heap_cell_live (heap_std W) a ->
    a ↦ₐ v ∗ RevokedResources W C l -∗
    a ↦ₐ v ∗ RevokedResources W C l ∗ ⌜a ∉ l⌝.
  Proof.
    iIntros (Hlive) "[Ha Hl]".
    iDestruct (stack_object_revoked_pointsto_disjoint W C l a v Hlive
      with "[$Ha] [$Hl]") as %Hnot.
    iFrame. iPureIntro. exact Hnot.
  Qed.

  Lemma stack_object_revoked_region_disjoint_frame
      (W : WORLD) (C : CmptName)
      (la l : list Addr) (lv : list Word) :
    Forall (heap_cell_live (heap_std W)) la ->
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗ RevokedResources W C l -∗
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗ RevokedResources W C l ∗
      ⌜la ## l⌝.
  Proof.
    iIntros (Hlive) "[Hregion Hl]".
    iInduction (la) as [|a la] "IH" forall (lv Hlive).
    - iFrame. iPureIntro. set_solver.
    - apply Forall_cons in Hlive as [Ha_live Hla_live].
      iDestruct (big_sepL2_length with "Hregion") as %Hlength.
      destruct lv as [|v lv]; first by cbn in Hlength.
      iDestruct "Hregion" as "[Ha Hregion]".
      iDestruct (stack_object_revoked_pointsto_disjoint_frame
        with "[$Ha $Hl]") as "(Ha & Hl & %Hnot)"; first exact Ha_live.
      iDestruct ("IH" $! lv with "[] Hregion Hl")
        as "(Hregion & Hl & %Hdisjoint)".
      { iPureIntro. exact Hla_live. }
      iFrame. iPureIntro. set_solver.
  Qed.
  Lemma stack_object_framed_resources_live
      (Worig Wcur : WORLD) (C : CmptName) (l : list Addr) :
    Forall (heap_cell_live (heap_std Worig)) l ->
    Forall (fun a => is_Some (heap_cell_status (heap_std Wcur) a)) l ->
    allocator_ctx ∗ world_interp Wcur C ∗ RevokedResources Worig C l
    ={⊤}=∗
      allocator_ctx ∗ world_interp Wcur C ∗ RevokedResources Worig C l ∗
      ⌜Forall (heap_cell_live (heap_std Wcur)) l⌝.
  Proof.
    induction l as [|a l IH]; intros Hlive Hsome;
      iIntros "(#Halloc & Hworld & Hl)".
    - iModIntro. iFrame "∗#". iPureIntro. constructor.
    - apply Forall_cons in Hlive as [Ha_live Hl_live].
      apply Forall_cons in Hsome as [Ha_some Hl_some].
      iDestruct "Hl" as "[Hitem Hl]".
      iDestruct "Hitem" as (p φ) "(%Hpers & Hrel & Hcell)".
      rewrite /heap_cell_live in Ha_live.
      iEval (rewrite Ha_live) in "Hcell".
      iDestruct "Hcell" as (v) "(%HpO & Ha & Hφ & Hmono)".
      iMod (framed_cell_live Wcur C a v Ha_some
        with "[$Halloc $Hworld $Ha]")
        as "(_ & Hworld & Ha & %Ha_cur)".
      iAssert (RevokedResources Worig C [a])%I
        with "[Hrel Ha Hφ Hmono]" as "Hitem".
      { rewrite /RevokedResources /= Ha_live.
        iSplitL "Hrel Ha Hφ Hmono"; last done.
        iExists p, φ. iFrame "Hrel". iSplit; first done.
        iExists v. rewrite /TmpRes. iFrame "Ha Hφ Hmono". done. }
      iMod (IH Hl_live Hl_some with "[$Halloc $Hworld $Hl]")
        as "(_ & Hworld & Hl & %Hl_cur)".
      iAssert (RevokedResources Worig C (a :: l))%I
        with "[Hitem Hl]" as "Hl".
      { replace (a :: l) with ([a] ++ l) by done.
        rewrite RevokedResources_app. iFrame. }
      iModIntro. iFrame "∗#". iPureIntro. constructor; assumption.
  Qed.

  Lemma stack_object_repair_world_for_return
      (W0 W3 W4 : WORLD) (C : CmptName)
      (object_b object_e csp_b csp_e a_stk1 a_stk2 : Addr)
      (l0 l0_live l0_quarantined l4 : list Addr)
      (stk_head0 : Word) (stk_tail : list Word) :
    let W5 := revoke W4 in
    let object_temps := so_object_temporaries W0 object_b object_e in
    let l0_rest := so_revoked_without_object W0 object_b object_e l0 in
    let l4_no_fresh := filter (fun a => a <> a_stk1) l4 in
    let l4_object := filter (fun a => a ∈ object_temps) l4_no_fresh in
    let l4_rest := filter (fun a => a ∉ object_temps) l4_no_fresh in
    let l4_unique := filter (fun a => a ∉ l0_live) l4_no_fresh in
    let closing_revoked := l0_live ++ l4_unique in
    let closing := closing_revoked ++ finz.seq_between csp_b csp_e in
    extract_temporaries_condition
      W0 (l0 ++ finz.seq_between csp_b csp_e) ->
    extract_temporaries_condition
      W4 (l4 ++ finz.seq_between (a_stk2 ^+ 4)%a csp_e) ->
    W3 = reinstate
      (close_list l0_quarantined
        (close_list object_temps (revoke W0))) [a_stk1] ->
    std W3 !! a_stk1 = Some Temporary ->
    related_sts_priv_world W0 W3 ->
    related_sts_pub_world W3 W4 ->
    Permutation l0_rest (l0_live ++ l0_quarantined) ->
    Forall (heap_cell_live (heap_std W0)) l0_live ->
    Forall
      (fun a => heap_cell_status (heap_std W0) a = Some AllocObjectQuarantined)
      l0_quarantined ->
    Forall (heap_cell_live (heap_std W5)) l0_live ->
    so_object_addresses object_b object_e
      ## finz.seq_between csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + 1)%a = Some a_stk1 ->
    (a_stk1 + 1)%a = Some a_stk2 ->
    (a_stk2 <= csp_e)%a ->
    (csp_b <= a_stk2 ^+ 4)%a /\
      (a_stk2 ^+ 4 <= csp_e)%a /\
      (a_stk2 + 4)%a = Some (a_stk2 ^+ 4)%a ->
    revoked_addresses W5 l4 ->
    Forall (fun a => std W5 !! a = Some Revoked) l0_live ->
    Forall (fun a => std W5 !! a = Some Revoked)
      (finz.seq_between a_stk2 csp_e) ->
    std W5 !! csp_b = Some Revoked ->
    world_interp W5 C
    ∗ RevokedResources W0 C l0_live
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
        ∗ RevokedResources (close_list closing W5) C closing_revoked
        ∗ [[csp_b, csp_e]] ↦ₐ
            [[stk_head0 :: stk_head1 :: stk_tail]].
  Proof.
    intros W5 object_temps l0_rest l4_no_fresh l4_object l4_rest
      l4_unique
      closing_revoked closing.
    intros Hextract0 Hextract4 HW3 Hfresh_W3 Hpriv Hpub
      Hrest_partition Hlive0 Hquarantined0 Hlive5 Hobject_stack Hstack_heap
      Hfresh Hnext Hnext_end Hreturned_bounds Hl4_W5
      Hl0_live_W5 Hstack_W5 Hhead_W5.
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
      eapply region_state_pub_temp; eauto.
      rewrite close_list_lookup_not_in.
      - rewrite close_list_lookup_not_in.
        + apply close_list_lookup_in.
          * cbn. apply revoke_lookup_Monotemp.
            subst object_temps.
            by apply list_elem_of_filter in Hx as [? _].
          * exact Hx.
        + intro Hxq.
          assert (x ∈ l0_rest) as Hxr.
          { rewrite Hrest_partition. apply elem_of_app. right. exact Hxq. }
          subst l0_rest.
          apply list_elem_of_filter in Hxr as [Hnot _]. contradiction.
      - intro Hx_fresh.
        apply list_elem_of_singleton in Hx_fresh; subst x.
        rewrite elem_of_disjoint in Hobject_stack.
        eapply Hobject_stack.
        + subst object_temps.
          by apply list_elem_of_filter in Hx as [_ ?].
        + apply elem_of_finz_seq_between.
          solve_addr+Hfresh Hnext Hnext_end.
    }

    (* The quarantined cells were also reinstated before the call.  Their
       public future therefore keeps them Temporary, even without memory
       resources for those cells. *)
    assert (Forall (fun x => std W4 !! x = Some Temporary)
      l0_quarantined) as Hquarantined_W4.
    { apply Forall_forall. intros x Hx.
      assert (x ∈ l0_rest) as Hxrest.
      { rewrite Hrest_partition. apply elem_of_app. right. exact Hx. }
      assert (x ∈ l0) as Hxl0.
      { rewrite Hl0_partition. apply elem_of_app. right. exact Hxrest. }
      assert (x ∉ object_temps) as Hnot_object.
      { subst l0_rest. apply list_elem_of_filter in Hxrest as [Hnot _].
        exact Hnot. }
      eapply region_state_pub_temp; eauto.
      rewrite close_list_lookup_not_in.
      - apply close_list_lookup_in.
        + rewrite close_list_lookup_not_in.
          * apply revoke_lookup_Monotemp.
            apply Hl0_temporaries. apply elem_of_app. left. exact Hxl0.
          * exact Hnot_object.
        + exact Hx.
      - intro Hfresh_x. apply list_elem_of_singleton in Hfresh_x.
        subst x. apply NoDup_app in Hl0_nodup as (_ & Hdisj & _).
        apply (Hdisj a_stk1 Hxl0).
        apply elem_of_finz_seq_between. solve_addr+Hfresh Hnext Hnext_end.
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
        destruct (decide (x = a_stk1)) as [->|Hneq].
        + split; intros; first by left.
          exact Hfresh_l4.
        + split; intros H.
          * right. split; assumption.
          * destruct H as [Heq|Hboth]; first contradiction.
            destruct Hboth as [_ Hin]. exact Hin.
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

    assert (l0_quarantined ⊆ l4_no_fresh) as Hquarantined_l4.
    { intros x Hx.
      assert (x ∈ l0_rest) as Hxrest.
      { rewrite Hrest_partition. apply elem_of_app. right. exact Hx. }
      assert (x ∈ l0) as Hxl0.
      { rewrite Hl0_partition. apply elem_of_app. right. exact Hxrest. }
      assert (x ∉ finz.seq_between csp_b csp_e) as Hnot_stack.
      { apply NoDup_app in Hl0_nodup as (_ & Hdisj & _).
        exact (Hdisj x Hxl0). }
      assert (x ∈ l4) as Hxl4.
      { rewrite Forall_forall in Hquarantined_W4.
        pose proof (Hquarantined_W4 x Hx) as Hx_temp.
        apply Hl4_temporaries in Hx_temp.
        apply elem_of_app in Hx_temp as [Hxl4|Hxtail];
          first exact Hxl4.
        exfalso. apply Hnot_stack.
        apply elem_of_finz_seq_between in Hxtail.
        apply elem_of_finz_seq_between.
        solve_addr+Hxtail Hfresh Hnext Hcsp_b_ret Hret_csp_e Hret_add. }
      subst l4_no_fresh. apply list_elem_of_filter. split; last exact Hxl4.
      intros Heq; subst x. apply Hnot_stack.
      apply elem_of_finz_seq_between. solve_addr+Hfresh Hnext Hnext_end.
    }
    assert (l0 ⊆ closing_revoked) as Hl0_closing_revoked.
    { intros x Hx.
      subst closing_revoked l4_unique.
      apply elem_of_app.
      destruct (decide (x ∈ l0_live)) as [Hlive_x|Hnot_live]; first by left.
      right. apply list_elem_of_filter. split; first exact Hnot_live.
      rewrite Hl0_partition in Hx.
      apply elem_of_app in Hx as [Hobject_x|Hrest_x].
      - rewrite Hobject_l4_object in Hobject_x.
        subst l4_object. by apply list_elem_of_filter in Hobject_x as [_ ?].
      - rewrite Hrest_partition in Hrest_x.
        apply elem_of_app in Hrest_x as [Hlive_x|Hquarantined_x].
        + contradiction.
        + by apply Hquarantined_l4.
    }

    assert (forall x, x ∈ l0 ++ finz.seq_between csp_b csp_e ->
      std W5 !! x = Some Revoked) as Hinitial_W5.
    { intros x Hx.
      apply elem_of_app in Hx as [Hx|Hx].
      - rewrite Hl0_partition in Hx.
        apply elem_of_app in Hx as [Hx|Hx].
        + cbn. apply revoke_lookup_Monotemp.
          rewrite Forall_forall in Hobject_temps_W4.
          by apply Hobject_temps_W4.
        + rewrite Hrest_partition in Hx.
          apply elem_of_app in Hx as [Hx|Hx].
          * rewrite Forall_forall in Hl0_live_W5.
            by apply Hl0_live_W5.
          * cbn. apply revoke_lookup_Monotemp.
            rewrite Forall_forall in Hquarantined_W4.
            by apply Hquarantined_W4.
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
          + apply elem_of_app; left.
            subst closing_revoked l4_unique.
            apply elem_of_app.
            destruct (decide (x ∈ l0_live)) as [Hin|Hnotin].
            * left. exact Hin.
            * right. apply list_elem_of_filter. split; assumption.
        - apply elem_of_app; right.
          apply elem_of_finz_seq_between in Hx.
          apply elem_of_finz_seq_between.
          solve_addr+Hx Hfresh Hnext Hcsp_b_ret Hret_csp_e Hret_add.
      }
      destruct W4 as [ [ [W4std W4cus] W4seals] W_heap4 ]; cbn.
      split; [|split];
        [|apply related_sts_pub_refl|split; [apply related_sts_seals_std_refl|apply related_sts_heap_std_refl] ]; cbn.
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
    (* The same repaired world must also be a public future of the switcher
       frame's original world [W0]. *)
    assert (related_sts_pub_world W0 (close_list closing W5)) as Hpub0.
    { subst W5.
      assert (l0 ++ finz.seq_between csp_b csp_e ⊆ closing) as Hsubset.
      { intros x Hx. apply elem_of_app in Hx as [Hx|Hx].
        - apply elem_of_app; left. by apply Hl0_closing_revoked.
        - by apply elem_of_app; right. }
      destruct W0 as [ [ [W0std W0cus] W0seals] W_heap0 ].
      destruct W4 as [ [ [W4std W4cus] W4seals] W_heap4 ]. cbn in *.
      split; [|split]; cbn; cycle 1.
      - destruct Hpriv as (_ & Hcus03 & _).
        destruct Hpub as (_ & Hcus34 & _).
        clear -Hcus03 Hcus34.
        cbn in *.
        eapply related_sts_pub_trans; eauto.
        apply related_sts_pub_refl.
      - destruct Hpriv as (_ & _ & Hseals03 & Hheap03).
        destruct Hpub as (_ & _ & Hseals34 & Hheap34).
        clear -Hseals03 Hseals34 Hheap03 Hheap34.
        cbn in *.
        split; [eapply related_sts_seals_trans|eapply related_sts_heap_std_trans]; eauto.
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
          * assert (std (W4std, W4cus, W4seals, W_heap4) !! x = Some Permanent)
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
    (* Every stack cell is outside the heap.  The mixed revoked resources
       therefore carry physical ownership at any stack address. *)
    assert (Forall (heap_cell_live (heap_std W4))
      (finz.seq_between csp_b csp_e)) as Hstack_live4.
    { apply Forall_forall. intros x Hx.
      apply heap_cell_live_nonheap.
      apply not_true_is_false. intros Hheap_x.
      rewrite /disjoint_from_heap elem_of_disjoint in Hstack_heap.
      eapply Hstack_heap; first exact Hx.
      apply elem_of_finz_seq_between.
      by apply withinBounds_true_iff in Hheap_x. }
    assert (heap_cell_live (heap_std W4) a_stk1) as Hfresh_live4.
    { rewrite Forall_forall in Hstack_live4. apply Hstack_live4.
      apply elem_of_finz_seq_between. solve_addr+Hfresh Hnext Hnext_end. }
    assert (heap_cell_live (heap_std W4) csp_b) as Hhead_live4.
    { rewrite Forall_forall in Hstack_live4. apply Hstack_live4.
      apply elem_of_finz_seq_between. solve_addr+Hfresh Hnext Hnext_end. }
    assert (Forall (heap_cell_live (heap_std W4))
      (finz.seq_between a_stk2 csp_e)) as Htail_live4.
    { apply Forall_forall. intros x Hx.
      rewrite Forall_forall in Hstack_live4. apply Hstack_live4.
      apply elem_of_finz_seq_between.
      apply elem_of_finz_seq_between in Hx. solve_addr. }
    rewrite /heap_cell_live in Hfresh_live4.
    iEval (rewrite /RevokedResources /= Hfresh_live4) in "Hfresh_resource".
    iDestruct "Hfresh_resource" as "[Hfresh_resource _]".
    iDestruct "Hfresh_resource" as (pa Pa) "(_ & _ & Hfresh_resource)".
    iDestruct "Hfresh_resource" as (va) "(_ & Hfresh_pointsto & _)".
    iDestruct (stack_object_revoked_pointsto_disjoint_frame
      with "[$Hhead0 $Hl4]") as "(Hhead0 & Hl4 & %Hhead_not_l4)";
      first exact Hhead_live4.
    iDestruct (stack_object_revoked_pointsto_disjoint_frame
      with "[$Hfresh_pointsto $Hl4]") as
      "(Hfresh_pointsto & Hl4 & %Hfresh_not_l4)";
      first exact Hfresh_live4.
    iDestruct (stack_object_revoked_region_disjoint_frame
      with "[$Htail $Hl4]") as "(Htail & Hl4 & %Htail_not_l4)";
      first exact Htail_live4.

    (* The new list filters every address already represented by the live
       frame, and the stack is disjoint from both resource lists. *)
    assert (NoDup closing) as Hclosing_nodup.
    { subst closing closing_revoked.
      apply NoDup_app. split; [|split].
      - apply NoDup_app. split; [|split].
        + assert (NoDup l0_rest) as Hrest_nodup.
          { subst l0_rest. apply NoDup_filter.
            apply NoDup_app in Hl0_nodup as [? _]. exact H. }
          rewrite Hrest_partition in Hrest_nodup.
          apply NoDup_app in Hrest_nodup as [? _]. exact H.
        + intros x Hx0 Hx4.
          subst l4_unique.
          apply list_elem_of_filter in Hx4 as [Hnot _]. contradiction.
        + subst l4_unique l4_no_fresh.
          repeat apply NoDup_filter.
          apply NoDup_app in Hl4_nodup as [? _]. exact H.
      - intros x Hx Hx_stack.
        apply elem_of_app in Hx as [Hx|Hx].
        + assert (x ∈ l0) as Hxl0.
          { rewrite Hl0_partition. apply elem_of_app. right.
            rewrite Hrest_partition. apply elem_of_app. left. exact Hx. }
          apply NoDup_app in Hl0_nodup as (_ & Hdisjoint & _).
          eapply Hdisjoint; eauto.
        + rewrite (finz_seq_between_cons csp_b csp_e) in Hx_stack;
            last solve_addr+Hfresh Hnext Hnext_end.
          apply elem_of_cons in Hx_stack as [->|Hx_stack].
          { apply Hhead_not_l4.
            subst l4_unique. by apply list_elem_of_filter in Hx as [_ ?]. }
          replace (csp_b ^+ 1)%a with a_stk1 in Hx_stack
            by solve_addr+Hfresh.
          rewrite (finz_seq_between_cons a_stk1 csp_e) in Hx_stack;
            last solve_addr+Hnext Hnext_end.
          apply elem_of_cons in Hx_stack as [->|Hx_stack].
          { apply Hfresh_not_l4.
            subst l4_unique. by apply list_elem_of_filter in Hx as [_ ?]. }
          replace (a_stk1 ^+ 1)%a with a_stk2 in Hx_stack
            by solve_addr+Hnext.
          rewrite elem_of_disjoint in Htail_not_l4.
          eapply Htail_not_l4; [exact Hx_stack|].
          subst l4_unique. by apply list_elem_of_filter in Hx as [_ ?].
      - apply finz_seq_between_NoDup.
    }
    assert (forall x, std W0 !! x = Some Temporary -> x ∈ closing)
      as Htemps_closing.
    { intros x Hx. apply Hl0_temporaries in Hx.
      apply elem_of_app in Hx as [Hx|Hx].
      - apply elem_of_app; left. by apply Hl0_closing_revoked.
      - by apply elem_of_app; right. }

    (* Retain only returned cells not already present in the live frame.
       Monotonicity carries each origin's mixed resources to the repaired
       public future. *)
    set (l4_overlap := filter (fun a => a ∈ l0_live) l4_no_fresh).
    assert (l4_no_fresh ≡ₚ l4_unique ++ l4_overlap) as Hl4_unique_partition.
    { subst l4_unique l4_overlap.
      transitivity
        (filter (fun a => a ∈ l0_live) l4_no_fresh ++
         filter (fun a => a ∉ l0_live) l4_no_fresh).
      - apply filter_complement_list.
      - apply Permutation_app_comm. }
    iEval (rewrite Hl4_unique_partition /RevokedResources big_sepL_app
      -/RevokedResources) in "Hl4".
    iDestruct "Hl4" as "[Hl4_unique Hl4_overlap]".
    iClear "Hl4_overlap".
    iDestruct (world_interp_heap_wf with "Hworld") as %Hheap_wf5.
    assert (heap_wf (heap_std (close_list closing W5)))
      as Hheap_wf_fixed by (rewrite close_list_heap; exact Hheap_wf5).
    iDestruct (RevokedResources_mono_pub W0 (close_list closing W5)
      C l0_live [] Hheap_wf_fixed Hpub0 with "Hl0_rest") as "Hl0_fixed".
    iDestruct (RevokedResources_mono_pub W4 (close_list closing W5)
      C l4_unique [] Hheap_wf_fixed Hpub4 with "Hl4_unique") as "Hl4_fixed".
    iAssert (RevokedResources (close_list closing W5) C closing_revoked)%I
      with "[Hl0_fixed Hl4_fixed]" as "Hclosing".
    { subst closing_revoked. rewrite RevokedResources_app. iFrame. }

    (* Join the secret head, fresh cell, and returned tail. *)
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
