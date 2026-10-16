From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_interp_stack.
From griotte Require Import counter_spec_states.

(** * Repair of the world before the return of [counter]

    The lemmas of this file do not execute code. They are used after the
    call to [C_f] in the proof of [counter_spec]:
    - [related_pub_W0_Wfixed]: the world obtained by closing the revoked
      addresses of the final world is a public future world of the
      initial world,
    - [counter_world_return]: the live keys revoked before the call, the
      keys revoked by the callee and the stack frame are revoked after the
      call, and the world can be repaired for the return. *)

Section Counter_World_Return.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma related_pub_W0_Wfixed (W0 W2 : WORLD) (csp_b csp_e : Addr ) (l : list LAddr):
    let W1 := revoke W0 in
    let W3 := revoke W2 in
    (∀ a : LAddr, std W0 !! a = Some Temporary ↔ a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    Forall (λ a : LAddr, std W3 !! a = Some Revoked) (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    related_sts_pub_world W1 W2 ->
    related_sts_pub_world W0 (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) W3).
  Proof.
    intros * Htemporaries_W0 Hrevoked_W3 Hrelated_pub_W1_W2.

    destruct W0 as [ [ [W0_std W0_cus] W0_seals] W_heap0 ],
               W2 as [ [ [W2_std W2_cus] W2_seals] W_heap2 ]; cbn.
    destruct Hrelated_pub_W1_W2 as (HW1_W2_std & HW1_W2_cus & HW1_W2_seals & HW1_W2_heap).
    split;[|split];cbn; cycle 1.
    { eapply related_sts_pub_trans; eauto; eapply related_sts_pub_refl. }
    { split; [exact HW1_W2_seals | exact HW1_W2_heap]. }
    destruct HW1_W2_std as [HW1_W2_std_dom HW1_W2_std_t].
    cbn in *.
    split.
    {
      intros a Ha.
      rewrite elem_of_dom -close_list_std_sta_is_Some -revoke_std_sta_lookup_Some -elem_of_dom.
      apply HW1_W2_std_dom.
      by rewrite elem_of_dom -revoke_std_sta_lookup_Some -elem_of_dom.
    }
    intros a ρ0 ρ2 Ha0 Ha2.
    destruct ρ0; cycle 1.
    - (* the initial a was in the Permanent state *)
      assert (a ∉ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) as Ha_notin.
      { destruct (Htemporaries_W0 a) as [_ ?].
        intro Hcontra; apply H in Hcontra. by rewrite Ha0 in Hcontra.
      }
      apply revoke_lookup_Perm in Ha0.
      assert (std (revoke ((W0_std, W0_cus, W0_seals, W_heap0))) !! a = Some Permanent) as Ha0' by done.
      rewrite -(std_sta_update_multiple_lookup_same_k _ (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary)
        in Ha0'.
      2: {
        intro Hcontra; apply Ha_notin.
        rewrite elem_of_app; right.
        apply list_elem_of_fmap in Hcontra as [a' [-> Hcontra] ].
        apply elem_of_LNonHeap_fmap.
        rewrite !elem_of_finz_seq_between in Hcontra |- *.
        solve_addr.
      }
      rewrite -close_list_std_sta_same in Ha2; last done.
      destruct ρ2.
      + by apply revoke_std_sta_lookup_non_temp in Ha2.
      + done.
      + apply anti_revoke_lookup_Revoked in Ha2.
        destruct Ha2 as [Ha2|Ha2]; first eapply HW1_W2_std_t in Ha0; eauto.
        eapply HW1_W2_std_t in Ha0; last eauto.
        inversion Ha0 as [|??? Hcontra]; simplify_eq.
        inversion Hcontra.
    - (* the initial a was in the Revoked state *)
      destruct ρ2; last apply rtc_refl; apply rtc_once; constructor.
    - (* the initial a was in the Temporary state *)
      assert (a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) as Ha_in.
      { destruct (Htemporaries_W0 a) as [? _]; by apply Htemporaries_W0. }
      apply revoke_lookup_Monotemp in Ha0.
      assert (std (revoke ((W0_std, W0_cus, W0_seals, W_heap0))) !! a = Some Revoked) as Ha0' by done.
      assert (
          std ((std_update_multiple (revoke (W0_std, W0_cus, W0_seals, W_heap0)) (finz.seq_between (csp_b ^+ 4)%a csp_e)
                  Temporary)) !! a =
          Some (if (decide (a ∈ LNonHeap <$> (finz.seq_between (csp_b ^+ 4)%a csp_e)))
                then Temporary
                else Revoked
        )).
      {
        destruct (decide (a ∈ LNonHeap <$> (finz.seq_between (csp_b ^+ 4)%a csp_e))) as [Ha_in_stk | Ha_in_stk].
        + apply std_sta_update_multiple_lookup_in_k; eauto.
        + rewrite std_sta_update_multiple_lookup_same_k; eauto.
      }
      pose proof Ha_in as Ha_in'.
      rewrite Forall_forall in Hrevoked_W3.
      eapply Hrevoked_W3 in Ha_in;eauto.
      eapply close_list_std_sta_revoked in Ha_in; last apply Ha_in'.
      rewrite Ha_in in Ha2; simplify_eq.
      apply rtc_refl.
  Qed.


  (** After the call to [C_f], in the world [revoke W2]: the live keys
      [l_live] revoked before the call, the keys [l'] revoked by the
      callee and the stack frame are revoked. Closing them yields a
      public future world of the initial world [W0]. *)
  Lemma counter_world_return W0 W2 C (csp_b csp_e : Addr) (l l_live l_q l' : list LAddr)
    (stk_mem : list LWord) :
    extract_temporaries_condition W0 (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    l ≡ₚ l_live ++ l_q ->
    Forall (λ a, heap_key_live (heap_std W0) a) l_live ->
    revoked_keys (revoke W0) l ->
    revoked_addresses (close_list l_q (revoke W0)) (finz.seq_between csp_b csp_e) ->
    related_sts_pub_world
      (std_update_multiple (close_list l_q (revoke W0)) (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary)
      W2 ->
    extract_temporaries_condition W2 (l' ++ (LNonHeap <$> finz.seq_between (csp_b ^+ 4)%a csp_e)) ->
    (csp_b <= (csp_b ^+ 4)%a ∧ (csp_b ^+ 4)%a <= csp_e ∧ (csp_b + 4) = Some (csp_b ^+ 4)%a)%a ->
    world_interp (revoke W2) C -∗
    RevokedResources W0 C l_live -∗
    RevokedResources W2 C l' -∗
    [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
    ==∗
    ∃ (closing_revoked : list LAddr),
      world_interp (revoke W2) C ∗
      RevokedResources
        (close_list (closing_revoked ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) (revoke W2))
        C closing_revoked ∗
      [[csp_b, csp_e]] ↦ₐ [[stk_mem]] ∗
      ⌜related_sts_pub_world W0
         (close_list (closing_revoked ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) (revoke W2))⌝ ∗
      ⌜NoDup (closing_revoked ++ (LNonHeap <$> finz.seq_between csp_b csp_e))⌝ ∗
      ⌜∀ a, std W0 !! a = Some Temporary ->
            a ∈ closing_revoked ++ (LNonHeap <$> finz.seq_between csp_b csp_e)⌝.
  Proof.
    iIntros (Hl_unk Hperm_l Hlive_l Hrevoked_l Hrevoked_stk_W1q Hpub_ext Hl_unk' Hcsp_bounds)
      "Hworld_interp_C Hrevoked_live Hrevoked_l' Hstk".
    rewrite /revoked_keys in Hrevoked_l.
    set (W1 := revoke W0).
    set (W1q := close_list l_q W1).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1
        by eapply revoke_related_sts_priv_world.
    assert (related_sts_priv_world W0 W1q) as Hpriv_W0_W1q.
    { eapply related_sts_priv_trans_world; [exact Hrelared_priv_W0_W1 |].
      apply related_sts_pub_priv_world, close_list_related_sts_pub. }
    assert (l_q ## (LNonHeap <$> finz.seq_between csp_b csp_e)) as Hq_stack.
    { destruct Hl_unk as [Hnd _]. apply NoDup_app in Hnd.
      destruct Hnd as (_ & Hdisj & _).
      intros x Hx Hxs. apply (Hdisj x);
        [rewrite Hperm_l; apply elem_of_app; right; exact Hx | exact Hxs]. }
    assert (related_sts_pub_world W1q W2) as Hrelated_pub_W1q_W2.
    {
      eapply related_sts_pub_trans_world; last exact Hpub_ext.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros a Ha.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stk_W1q.
      apply Hrevoked_stk_W1q.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
    }

    assert (Forall (fun a => std W1q !! a = Some Temporary) l_q) as Hq_temp_W1q.
    { apply Forall_forall. intros a Ha. rewrite /W1q /close_list /=.
      apply close_list_std_sta_revoked; first exact Ha.
      rewrite Forall_forall in Hrevoked_l. apply Hrevoked_l.
      rewrite Hperm_l. apply elem_of_app. right. exact Ha. }
    assert (Forall (fun a => std W2 !! a = Some Temporary) l_q) as Hq_temp_W2.
    { apply Forall_forall. intros a Ha.
      eapply region_state_pub_temp; [exact Hrelated_pub_W1q_W2 |].
      rewrite Forall_forall in Hq_temp_W1q. by apply Hq_temp_W1q. }

    set (W3 := revoke W2).
    assert (Forall (fun a => a ∈ dom (std W3)) l_live) as Hdom_live_W3.
    { apply Forall_forall; intros a Ha.
      subst W3. rewrite -revoke_dom_eq.
      eapply elem_of_mono_pub; eauto.
      rewrite /W1q -close_list_dom_eq /W1 -revoke_dom_eq.
      rewrite elem_of_dom. exists Temporary.
      destruct Hl_unk as [_ Htemp]. apply Htemp.
      rewrite Hperm_l. apply elem_of_app. left.
      apply elem_of_app. by left. }
    iEval (rewrite world_interp_eq /world_interp_def) in "Hworld_interp_C".
    iNamed "Hworld_interp_C".
    iDestruct (region_addrs_status_some W3 C l_live Hdom_live_W3 with "Hr")
      as "[Hr %Hstatuses_live_W3]".
    iAssert (world_interp W3 C) with "[Hr Hsts Hseals]" as "Hworld_interp_C".
    { rewrite world_interp_eq /world_interp_def. iFrame. }
    iDestruct (counter_framed_resources_live W0 W3 C l_live Hlive_l Hstatuses_live_W3
      with "[$Hworld_interp_C $Hrevoked_live]")
      as "(Hworld_interp_C & Hrevoked_live & %Hlive_W3)".
    iMod (world_interp_revoked_by_separation_many_with_RevokedResources
      W0 W3 C l_live Hlive_l Hlive_W3 Hdom_live_W3
      with "[$Hworld_interp_C $Hrevoked_live]")
      as "(Hworld_interp_C & Hrevoked_live & %Hrevoked_live_W3)".

    iMod (world_interp_revoked_by_separation_many with "[$Hworld_interp_C $Hstk]")
      as "(Hworld_interp_C & Hstk & %Hrevoked_stk_W3)".
    { apply Forall_forall; intros x Hx.
      rewrite revoke_heap. apply heap_key_live_nonheap. }
    { apply Forall_forall; intros x Hx.
      subst W3. rewrite -revoke_dom_eq.
      eapply elem_of_mono_pub; eauto.
      rewrite /W1q -close_list_dom_eq /W1 -revoke_dom_eq.
      rewrite elem_of_dom. exists Temporary.
      destruct Hl_unk as [_ Htemp]. apply Htemp.
      apply elem_of_app. by right. }

    assert (l_q ⊆ l') as Hq_in_l'.
    { intros x Hx.
      rewrite Forall_forall in Hq_temp_W2.
      pose proof (Hq_temp_W2 x Hx) as Hx_temp.
      destruct Hl_unk' as [_ Htemp2]. apply Htemp2 in Hx_temp.
      apply elem_of_app in Hx_temp as [Hxl'|Hxtail]; first exact Hxl'.
      exfalso. apply (Hq_stack x Hx).
      apply list_elem_of_fmap in Hxtail as [x' [-> Hxtail] ].
      apply elem_of_LNonHeap_fmap.
      apply elem_of_finz_seq_between in Hxtail.
      apply elem_of_finz_seq_between. solve_addr+Hxtail Hcsp_bounds. }
    assert (l_live ## l_q) as Hlive_q_disjoint.
    { destruct Hl_unk as [Hnd _]. rewrite Hperm_l in Hnd.
      apply NoDup_app in Hnd as [Hnd_l _].
      apply NoDup_app in Hnd_l as (_ & Hdisj & _). exact Hdisj. }
    assert (l_live ## (LNonHeap <$> finz.seq_between csp_b csp_e)) as Hlive_stack.
    { destruct Hl_unk as [Hnd _]. apply NoDup_app in Hnd as (_ & Hdisj & _).
      intros x Hx Hxs. apply (Hdisj x);
        [rewrite Hperm_l; apply elem_of_app; by left | exact Hxs]. }
    assert (Forall (fun a => std W3 !! a = Some Revoked) l_q) as Hrevoked_q_W3.
    { apply Forall_forall. intros x Hx. subst W3.
      apply revoke_lookup_Monotemp.
      rewrite Forall_forall in Hq_temp_W2. by apply Hq_temp_W2. }
    assert (Forall (fun a => std W3 !! a = Some Revoked)
      (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e))) as Hrevoked_initial_W3.
    { apply Forall_forall. intros x Hx. apply elem_of_app in Hx as [Hx|Hx].
      - rewrite Hperm_l in Hx. apply elem_of_app in Hx as [Hx|Hx].
        + rewrite Forall_forall in Hrevoked_live_W3. by apply Hrevoked_live_W3.
        + rewrite Forall_forall in Hrevoked_q_W3. by apply Hrevoked_q_W3.
      - apply list_elem_of_fmap in Hx as [x' [-> Hx] ].
        rewrite Forall_forall in Hrevoked_stk_W3. by apply Hrevoked_stk_W3. }

    set (l'_fresh := filter
      (fun a => a ∉ l_live ∧ a ∉ LNonHeap <$> finz.seq_between csp_b csp_e) l').
    set (closing_revoked := l_live ++ l'_fresh).
    set (closing := closing_revoked ++ (LNonHeap <$> finz.seq_between csp_b csp_e)).
    assert (l ⊆ closing_revoked) as Hinitial_in_closing.
    { intros x Hx. subst closing_revoked. apply elem_of_app.
      rewrite Hperm_l in Hx. apply elem_of_app in Hx as [Hlive|Hq]; first by left.
      right. subst l'_fresh. apply list_elem_of_filter. split.
      - split.
        + intros Hlive. apply (Hlive_q_disjoint x Hlive Hq).
        + intros Hstack. apply (Hq_stack x Hq Hstack).
      - by apply Hq_in_l'. }
    assert (l' ++ (LNonHeap <$> finz.seq_between (csp_b ^+ 4)%a csp_e) ⊆ closing)
      as Hreturned_in_closing.
    { intros x Hx. subst closing closing_revoked.
      apply elem_of_app in Hx as [Hxl'|Hxtail].
      - destruct (decide (x ∈ LNonHeap <$> finz.seq_between csp_b csp_e)) as [Hstack|Hnotstack].
        + apply elem_of_app. by right.
        + apply elem_of_app. left. apply elem_of_app.
          destruct (decide (x ∈ l_live)) as [Hlive|Hnotlive]; first by left.
          right. subst l'_fresh. apply list_elem_of_filter.
          split; [split; assumption|assumption].
      - apply elem_of_app. right.
        apply list_elem_of_fmap in Hxtail as [x' [-> Hxtail] ].
        apply elem_of_LNonHeap_fmap.
        apply elem_of_finz_seq_between in Hxtail.
        apply elem_of_finz_seq_between. solve_addr+Hxtail Hcsp_bounds. }
    assert (NoDup closing) as Hclosing_nodup.
    { subst closing closing_revoked. apply NoDup_app. split; [|split].
      - apply NoDup_app. split; [|split].
        + destruct Hl_unk as [Hnd _]. rewrite Hperm_l in Hnd.
          apply NoDup_app in Hnd as [Hnd_l _].
          apply NoDup_app in Hnd_l as [Hnd_live _]. exact Hnd_live.
        + intros x Hlive Hfresh. subst l'_fresh.
          apply list_elem_of_filter in Hfresh as [Hpred _].
          destruct Hpred as [Hnotlive _]. contradiction.
        + subst l'_fresh. apply NoDup_filter.
          destruct Hl_unk' as [Hnd _]. apply NoDup_app in Hnd as [Hnd_l' _]. exact Hnd_l'.
      - intros x Hx Hstack. apply elem_of_app in Hx as [Hlive|Hfresh].
        + by apply (Hlive_stack x Hlive Hstack).
        + subst l'_fresh. apply list_elem_of_filter in Hfresh as [Hpred _].
          destruct Hpred as [_ Hnotstack]. contradiction.
      - apply NoDup_LNonHeap_fmap, finz_seq_between_NoDup. }
    assert (∀ x, std W0 !! x = Some Temporary -> x ∈ closing) as Htemp0_cover.
    { intros x Hx. destruct Hl_unk as [_ Htemp]. apply Htemp in Hx.
      apply elem_of_app in Hx as [Hxl|Hxstack].
      - subst closing. apply elem_of_app. left. by apply Hinitial_in_closing.
      - subst closing. apply elem_of_app. by right. }

    set (Wfixed := close_list closing W3).
    assert (related_sts_pub_world W2 Wfixed) as Hpub2.
    { subst Wfixed W3.
      destruct W2 as [ [ [W2std W2cus] W2seals] W2heap ]; cbn.
      split; [|split]; cbn.
      - split.
        + setoid_rewrite <- close_list_dom_eq.
          setoid_rewrite <- revoke_dom_eq. done.
        + intros x ρ2 ρf Hx2 Hxf.
          destruct ρ2.
          * assert (x ∈ l' ++ (LNonHeap <$> finz.seq_between (csp_b ^+ 4)%a csp_e)) as Hx_close.
            { destruct Hl_unk' as [_ Htemp]. apply Htemp. exact Hx2. }
            rewrite close_list_std_sta_revoked in Hxf; auto.
            { simplify_eq; apply rtc_refl. }
            by apply revoke_lookup_Monotemp.
          * apply revoke_lookup_Perm in Hx2.
            rewrite -close_list_std_sta_same_alt in Hxf; [|intro];
              simplify_eq; apply rtc_refl.
          * destruct ρf; try apply rtc_refl; apply rtc_once; econstructor.
      - apply related_sts_pub_refl.
      - split; [apply related_sts_seals_std_refl|apply related_sts_heap_std_refl]. }
    assert (related_sts_priv_world W0 W2) as Hpriv02.
    { eapply related_sts_priv_pub_trans_world; eauto. }
    assert (related_sts_pub_world W0 Wfixed) as Hpub0.
    { subst Wfixed W3.
      destruct W0 as [ [ [W0std W0cus] W0seals] W0heap ].
      destruct W2 as [ [ [W2std W2cus] W2seals] W2heap ]. cbn in *.
      split; [|split]; cbn.
      - split.
        + destruct Hpriv02 as ((Hdom02 & _) & _ & _ & _).
          setoid_rewrite <- close_list_dom_eq.
          setoid_rewrite <- revoke_dom_eq. exact Hdom02.
        + intros x ρ0 ρf Hx0 Hxf.
          destruct ρ0.
          * assert (x ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) as Hx_close.
            { destruct Hl_unk as [_ Htemp]. apply Htemp. exact Hx0. }
            rewrite close_list_std_sta_revoked in Hxf; auto.
            { simplify_eq; apply rtc_refl. }
            rewrite Forall_forall in Hrevoked_initial_W3.
            by apply Hrevoked_initial_W3.
          * assert (std (W2std, W2cus, W2seals, W2heap) !! x = Some Permanent) as Hx2.
            { eapply region_state_priv_perm; [exact Hpriv02|exact Hx0]. }
            apply revoke_lookup_Perm in Hx2.
            rewrite -close_list_std_sta_same_alt in Hxf;
              [|intro Hcontra]; cbn; simplify_eq.
            { rewrite Hx2 in Hxf; simplify_eq; apply rtc_refl. }
            rewrite Hx2 in Hcontra; done.
          * destruct ρf; try apply rtc_refl; apply rtc_once; econstructor.
      - destruct Hpriv_W0_W1q as (_ & Hcus01 & _).
        destruct Hrelated_pub_W1q_W2 as (_ & Hcus12 & _).
        eapply related_sts_pub_trans; eauto.
        apply related_sts_pub_refl.
      - destruct Hpriv02 as (_ & _ & Hseals02 & Hheap02).
        split; assumption. }

    set (l'_dropped := filter
      (fun a => ¬(a ∉ l_live ∧ a ∉ LNonHeap <$> finz.seq_between csp_b csp_e)) l').
    assert (l' ≡ₚ l'_fresh ++ l'_dropped) as Hl'_partition.
    { subst l'_fresh l'_dropped. apply filter_complement_list. }
    iAssert (RevokedResources W2 C (l'_fresh ++ l'_dropped))%I
      with "[Hrevoked_l']" as "Hrevoked_parts".
    { rewrite -Hl'_partition. iExact "Hrevoked_l'". }
    iDestruct (RevokedResources_app with "Hrevoked_parts")
      as "[Hrevoked_fresh Hrevoked_dropped]".
    iClear "Hrevoked_dropped".
    iDestruct (RevokedResources_mono_pub W0 Wfixed C l_live [] Hpub0
      with "Hrevoked_live") as "Hrevoked_live_fixed".
    iDestruct (RevokedResources_mono_pub W2 Wfixed C l'_fresh [] Hpub2
      with "Hrevoked_fresh") as "Hrevoked_fresh_fixed".
    iAssert (RevokedResources Wfixed C closing_revoked)%I
      with "[Hrevoked_live_fixed Hrevoked_fresh_fixed]" as "Hclosing_resources".
    { subst closing_revoked. rewrite RevokedResources_app. iFrame. }
    iModIntro.
    iExists closing_revoked.
    iFrame "Hworld_interp_C Hclosing_resources Hstk".
    iPureIntro; split; [exact Hpub0|split; [exact Hclosing_nodup | exact Htemp0_cover] ].
  Qed.

End Counter_World_Return.
