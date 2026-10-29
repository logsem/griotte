From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import region_invariants_revocation interp_weakening monotone.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import vae_spec_states vae_spec_closure_repair.

(** * Repair of the world before the return of [awkward]

    The lemmas of this file do not execute code. They are used after the
    second call to [g] in the proof of [vae_awkward_spec]:
    - [related_pub_W0_Wfixed]: the world obtained by closing the revoked
      addresses of the final world is a public future world of the
      initial world,
    - [vae_world_return]: the flag is still [true] after the second call,
      and the world can be repaired for the return. *)

Section VAE_World_Return.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma related_pub_W0_Wfixed (W0 W3 W6 : WORLD) (l : list LAddr) (csp_b csp_e : Addr)
    (b : bool) (i : positive) :
    let W1 := revoke W0 in
    let W2 := <l[i:=false]l>W1 in
    let W4 := revoke W3 in
    let W5 := <l[i:=true]l>W4 in
    let W7 := revoke W6 in
    (* initial revocation W0 *)
    (∀ a : LAddr, std W0 !! a = Some Temporary ↔ a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    (* final revocation W7 *)
    Forall (λ a : LAddr, std W7 !! a = Some Revoked) (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e))->
    (* world transition of the first call *)
    related_sts_pub_world W2 W3 ->
    (* world transition of the second call *)
    related_sts_pub_world W5 W6 ->
    (* custom invariant `i` in initial world W0 *)
    loc W1 !! i = Some (encode b) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (* custom invariant `i` in final world W7 *)
    loc W7 !! i = Some (encode true) ->
    wrel W7 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (* public transition between initial and fixed *)
    related_sts_pub_world W0 (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) W7).
  Proof.
    eapply awk_two_call_world_repair
      with (closing := l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)); eauto.
  Qed.

  (** After the second call to [g], in the world [W6]: the flag is still
      [true]. The live keys [l0_live] revoked at the entry of [awkward], the
      live keys [l1_live] revoked by the first call, the keys [l2] revoked by
      the second call and the stack frame are revoked in [revoke W6].
      Closing them yields a public future world of the initial world [W0]. *)
  Lemma vae_world_return (W0 W3 W6 : WORLD) (C : CmptName) (i : positive) (b : bool)
    (l l0_live l0_quarantined l1 l1_live l1_quarantined l2 : list LAddr)
    (csp_b csp_e : Addr) :
    let stk_frame_addrs := finz.seq_between csp_b csp_e in
    let W2 := <l[i:=false]l>(revoke W0) in
    let W2q := close_list l0_quarantined W2 in
    let W5 := <l[i:=true]l>(revoke W3) in
    let W5q := close_list l1_quarantined W5 in
    disjoint_from_heap csp_b csp_e ->
    callee_stk_bounds csp_b csp_e (stk_start_a csp_b csp_e) ->
    extract_temporaries_condition W0 (l ++ (LNonHeap <$> stk_frame_addrs)) ->
    revoked_keys (revoke W0) l ->
    l ≡ₚ l0_live ++ l0_quarantined ->
    Forall (λ a, ∃ x ι, a = LHeap x ι) l0_quarantined ->
    extract_temporaries_condition W3 (l1 ++ (LNonHeap <$> callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e))) ->
    revoked_keys (revoke W3) l1 ->
    l1 ≡ₚ l1_live ++ l1_quarantined ->
    Forall (λ a, ∃ x ι, a = LHeap x ι) l1_quarantined ->
    extract_temporaries_condition W6 (l2 ++ (LNonHeap <$> callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e))) ->
    revoked_keys (revoke W6) l2 ->
    revoked_addresses (revoke W6) stk_frame_addrs ->
    related_sts_priv_world W0 W2 ->
    related_sts_pub_world W2q W3 ->
    related_sts_pub_world (revoke W3) W5 ->
    related_sts_priv_world W3 W5 ->
    related_sts_pub_world W5q W6 ->
    loc (revoke W0) !! i = Some (encode b) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    wrel W3 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    sts_rel_loc C i awk_rel_pub awk_rel_priv -∗
    world_interp (revoke W6) C -∗
    RevokedCells W0 C l0_live -∗
    RevokedCells W3 C l1_live -∗
    RevokedResources W6 C l2
    ={⊤}=∗
    ∃ closing_revoked,
      world_interp (revoke W6) C ∗
      RevokedResources
        (close_list (closing_revoked ++ (LNonHeap <$> stk_frame_addrs)) (revoke W6))
        C closing_revoked ∗
      ⌜loc (revoke W6) !! i = Some (encode true)⌝ ∗
      ⌜related_sts_pub_world W0
         (close_list (closing_revoked ++ (LNonHeap <$> stk_frame_addrs)) (revoke W6))⌝ ∗
      ⌜NoDup (closing_revoked ++ (LNonHeap <$> stk_frame_addrs))⌝ ∗
      ⌜∀ a, std W0 !! a = Some Temporary ->
            a ∈ closing_revoked ++ (LNonHeap <$> stk_frame_addrs)⌝.
  Proof.
    intros stk_frame_addrs W2 W2q W5 W5q.
    iIntros (Hstk_heap Hcsp_bounds Hl_unk Hrevoked_l Hl0_partition Hl0_quarantined
             Hl1_unk Hl1_revoked_W4 Hl1_partition Hl1_quarantined
             Hl2_unk Hl2_revoked_W7 Hstack_revoked_W6
             Hrelated_priv_W0_W2 Hrelated_pub_W2q_W3 Hrelated_pub_W4_W5 Hrelated_priv_W3_W5
             Hrelated_pub_W5q_W6 Hwst_i Hwrel_i Hwrel_i_W3)
      "#Hsts_rel Hworld_interp_C Hl0_live Hl1_live Hrevoked_l2".
    rewrite /revoked_keys in Hrevoked_l.
    set (W1 := revoke W0).
    set (W4 := revoke W3).
    assert (related_sts_priv_world W0 W2q) as Hrelated_priv_W0_W2q.
    { eapply related_sts_priv_pub_trans_world; [exact Hrelated_priv_W0_W2|].
      subst W2q. apply close_list_related_sts_pub. }
    assert (related_sts_priv_world W3 W5q) as Hrelated_priv_W3_W5q.
    { eapply related_sts_priv_pub_trans_world; [exact Hrelated_priv_W3_W5|].
      subst W5q. apply close_list_related_sts_pub. }
    assert (related_sts_pub_world W5 W6) as Hrelated_pub_W5_W6.
    { eapply related_sts_pub_trans_world;
        [subst W5q; apply close_list_related_sts_pub|exact Hrelated_pub_W5q_W6]. }
    assert (related_sts_pub_world W2 W3) as Hrelated_pub_W2_W3.
    { eapply related_sts_pub_trans_world;
        [subst W2q; apply close_list_related_sts_pub|exact Hrelated_pub_W2q_W3]. }

    iAssert (⌜ Forall (λ a : LAddr, a ∈ dom (std W6)) l ⌝)%I as "%Hl_revoked_W6".
    {
      iPureIntro; apply Forall_forall; intros a Ha.
      rewrite Forall_forall in Hrevoked_l.
      apply Hrevoked_l in Ha.
      cbn.
      assert (a ∈ dom (std W2q)) as Ha2.
      { subst W2q W2.
        cbn. rewrite -close_list_dom_eq.
        rewrite elem_of_dom. exists Revoked. exact Ha. }
      destruct Hrelated_pub_W5q_W6 as [ [Hdom_5_6 _] _ ].
      apply Hdom_5_6.
      subst W5q W5 W4. cbn.
      rewrite -close_list_dom_eq.
      rewrite -revoke_dom_eq.
      destruct Hrelated_pub_W2q_W3 as [ [Hdom_2_3 _] _ ].
      by apply Hdom_2_3.
    }

    set (W7 := revoke W6).

    assert (l0_quarantined ## (LNonHeap <$> stk_frame_addrs)) as Hq0_stack.
    { by apply vae_quarantined_disjoint_stack. }
    assert (l1_quarantined ## (LNonHeap <$> stk_frame_addrs)) as Hq1_stack.
    { by apply vae_quarantined_disjoint_stack. }
    assert (l0_quarantined ⊆ l1) as Hq0_l1.
    { intros a Ha.
      assert (std W2q !! a = Some Temporary) as Htemp2q.
      { subst W2q W2 W1.
        apply close_list_lookup_in; last exact Ha.
        cbn. rewrite Forall_forall in Hrevoked_l.
        apply Hrevoked_l.
        rewrite Hl0_partition. apply elem_of_app; right; exact Ha. }
      pose proof (region_state_pub_temp W2q W3 a
        Hrelated_pub_W2q_W3 Htemp2q) as Htemp3.
      destruct Hl1_unk as [_ Htemp1].
      apply Htemp1 in Htemp3.
      apply elem_of_app in Htemp3 as [Hin|Htail]; first exact Hin.
      exfalso.
      apply list_elem_of_fmap in Htail as [a' [-> Htail] ].
      rewrite elem_of_disjoint in Hq0_stack.
      eapply (Hq0_stack (LNonHeap a')); first exact Ha.
      apply elem_of_LNonHeap_fmap.
      apply elem_of_finz_seq_between.
      exact (callee_stk_region_incl _ _ _ _ Hcsp_bounds Htail). }
    assert (l1_quarantined ⊆ l2) as Hq1_l2.
    { intros a Ha.
      assert (std W5q !! a = Some Temporary) as Htemp5q.
      { subst W5q W5 W4.
        apply close_list_lookup_in; last exact Ha.
        cbn. rewrite /revoked_keys Forall_forall in Hl1_revoked_W4.
        apply Hl1_revoked_W4.
        rewrite Hl1_partition. apply elem_of_app; right; exact Ha. }
      pose proof (region_state_pub_temp W5q W6 a
        Hrelated_pub_W5q_W6 Htemp5q) as Htemp6.
      destruct Hl2_unk as [_ Htemp2].
      apply Htemp2 in Htemp6.
      apply elem_of_app in Htemp6 as [Hin|Htail]; first exact Hin.
      exfalso.
      apply list_elem_of_fmap in Htail as [a' [-> Htail] ].
      rewrite elem_of_disjoint in Hq1_stack.
      eapply (Hq1_stack (LNonHeap a')); first exact Ha.
      apply elem_of_LNonHeap_fmap.
      apply elem_of_finz_seq_between.
      exact (callee_stk_region_incl _ _ _ _ Hcsp_bounds Htail). }

    set (l1_unique :=
      filter (fun a => a ∉ l0_live ++ (LNonHeap <$> stk_frame_addrs)) l1_live).
    iDestruct (vae_revoked_cells_filter W3 C l1_live
      (l0_live ++ (LNonHeap <$> stk_frame_addrs)) with "Hl1_live") as "Hl1_unique".

    set (l2_unique :=
      filter (fun a => a ∉ l0_live ++ l1_unique ++ (LNonHeap <$> stk_frame_addrs)) l2).
    iDestruct (vae_revoked_resources_filter W6 C l2
      (l0_live ++ l1_unique ++ (LNonHeap <$> stk_frame_addrs))
      with "Hrevoked_l2") as "Hl2_unique".

    set (closing_revoked := l0_live ++ l1_unique ++ l2_unique).
    set (closing := closing_revoked ++ (LNonHeap <$> stk_frame_addrs)).

    assert (Forall (λ a, a ∈ dom (std W7)) l0_live) as Hl0_dom_W7.
    { apply Forall_forall; intros a Ha.
      subst W7. cbn. rewrite -revoke_dom_eq.
      rewrite Forall_forall in Hl_revoked_W6.
      apply Hl_revoked_W6.
      rewrite Hl0_partition. apply elem_of_app; left; exact Ha. }
    iMod (vae_framed_resources_revoked W0 W7 C l0_live
      Hl0_dom_W7 with "[$Hworld_interp_C $Hl0_live]")
      as "(Hworld_interp_C & Hl0_live & %Hl0_live_revoked_W7)".

    assert (Forall (λ a, a ∈ dom (std W7)) l1_unique)
      as Hl1_unique_dom_W7.
    { apply Forall_forall; intros a Ha.
      subst W7. cbn. rewrite -revoke_dom_eq.
      destruct Hrelated_pub_W5q_W6 as [ [Hdom56 _] _ ].
      apply Hdom56.
      destruct Hrelated_priv_W3_W5q as [ [Hdom35 _] _ ].
      apply Hdom35.
      rewrite elem_of_dom. exists Temporary.
      destruct Hl1_unk as [_ Htemp1].
      apply Htemp1. apply elem_of_app; left.
      rewrite Hl1_partition. apply elem_of_app; left.
      subst l1_unique. by apply list_elem_of_filter in Ha as [_ Ha]. }
    iMod (vae_framed_resources_revoked W3 W7 C l1_unique
      Hl1_unique_dom_W7
      with "[$Hworld_interp_C $Hl1_unique]")
      as "(Hworld_interp_C & Hl1_unique & %Hl1_unique_revoked_W7)".

    assert (Forall (fun a => std W7 !! a = Some Revoked) closing)
      as Hclosing_revoked_W7.
    { subst closing closing_revoked.
      repeat (apply Forall_app; split).
      - exact Hl0_live_revoked_W7.
      - exact Hl1_unique_revoked_W7.
      - apply Forall_forall; intros a Ha.
        rewrite /revoked_keys Forall_forall in Hl2_revoked_W7.
        apply Hl2_revoked_W7.
        subst l2_unique. by apply list_elem_of_filter in Ha as [_ Ha].
      - by apply Forall_fmap. }

    assert (NoDup closing ∧ l1_live ⊆ closing ∧ l2 ⊆ closing)
      as (Hclosing_nodup & Hl1_closing & Hl2_closing).
    { apply (vae_closing_lists l0_live l1_live l2 (LNonHeap <$> stk_frame_addrs)).
      - destruct Hl_unk as [Hnodup0 _].
        apply NoDup_app in Hnodup0 as (Hnodup_l & Hdisj & Hnodup_stack).
        rewrite Hl0_partition in Hnodup_l.
        apply NoDup_app in Hnodup_l as [Hnodup_live _].
        apply NoDup_app. split; first exact Hnodup_live.
        split; last exact Hnodup_stack.
        intros a Ha Hstack. apply (Hdisj a); last exact Hstack.
        rewrite Hl0_partition. apply elem_of_app; left; exact Ha.
      - destruct Hl1_unk as [Hnodup1 _].
        apply NoDup_app in Hnodup1 as [Hnodup_l1 _].
        rewrite Hl1_partition in Hnodup_l1.
        by apply NoDup_app in Hnodup_l1 as [Hnodup_live _].
      - destruct Hl2_unk as [Hnodup2 _].
        by apply NoDup_app in Hnodup2 as [Hnodup_l2 _]. }
    assert (forall a, std W0 !! a = Some Temporary -> a ∈ closing)
      as Hclosing_covers_W0.
    { intros a Htemp.
      destruct Hl_unk as [_ Htemp0].
      apply Htemp0 in Htemp.
      apply elem_of_app in Htemp as [Ha|Ha].
      - rewrite Hl0_partition in Ha.
        apply elem_of_app in Ha as [Ha|Ha].
        + subst closing closing_revoked. set_solver + Ha.
        + apply Hq0_l1 in Ha.
          rewrite Hl1_partition in Ha.
          apply elem_of_app in Ha as [Ha|Ha].
          * apply Hl1_closing; exact Ha.
          * apply Hl2_closing, Hq1_l2; exact Ha.
      - subst closing stk_frame_addrs. set_solver + Ha. }
    assert (forall a, std W3 !! a = Some Temporary -> a ∈ closing)
      as Hclosing_covers_W3.
    { intros a Htemp.
      destruct Hl1_unk as [_ Htemp1].
      apply Htemp1 in Htemp.
      apply elem_of_app in Htemp as [Ha|Ha].
      - rewrite Hl1_partition in Ha.
        apply elem_of_app in Ha as [Ha|Ha].
        + apply Hl1_closing; exact Ha.
        + apply Hl2_closing, Hq1_l2; exact Ha.
      - subst closing stk_frame_addrs.
        apply elem_of_app; right.
        apply list_elem_of_fmap in Ha as [a' [-> Ha] ].
        apply elem_of_LNonHeap_fmap.
        apply elem_of_finz_seq_between.
        exact (callee_stk_region_incl _ _ _ _ Hcsp_bounds Ha). }
    assert (forall a, std W6 !! a = Some Temporary -> a ∈ closing)
      as Hclosing_covers_W6.
    { intros a Htemp.
      destruct Hl2_unk as [_ Htemp2].
      apply Htemp2 in Htemp.
      apply elem_of_app in Htemp as [Ha|Ha].
      - apply Hl2_closing; exact Ha.
      - subst closing stk_frame_addrs.
        apply elem_of_app; right.
        apply list_elem_of_fmap in Ha as [a' [-> Ha] ].
        apply elem_of_LNonHeap_fmap.
        apply elem_of_finz_seq_between.
        exact (callee_stk_region_incl _ _ _ _ Hcsp_bounds Ha). }



    assert (loc W5 !! i = Some (encode true)) as Hwst_i_W5.
    { subst W5. cbn. apply lookup_insert_eq. }
    pose proof (awk_loc_true_mono_pub W5 W6 i Hrelated_pub_W5_W6
      Hwst_i_W5 Hwrel_i_W3) as Hwst_i_W6.
    assert (loc W7 !! i = Some (encode true)) as Hwst_i_W7.
    { subst W7. exact Hwst_i_W6. }
    iDestruct (world_interp_rel_loc_valid
      with "Hworld_interp_C Hsts_rel") as "%Hwrel_i_W7".

    assert (Forall (fun a => std W7 !! a = Some Revoked)
      (l ++ (LNonHeap <$> stk_frame_addrs))) as Horig_revoked_W7.
    { apply Forall_forall. intros a Ha.
      rewrite Forall_forall in Hclosing_revoked_W7.
      apply Hclosing_revoked_W7.
      apply Hclosing_covers_W0.
      destruct Hl_unk as [_ Htemp0].
      apply Htemp0. exact Ha. }
    assert (related_sts_pub_world W0
      (close_list (l ++ (LNonHeap <$> stk_frame_addrs)) W7)) as Hpub0_orig.
    { subst stk_frame_addrs.
      eapply (related_pub_W0_Wfixed W0 W3 W6 l); eauto.
      destruct Hl_unk as [_ Htemp0]. exact Htemp0. }
    assert (related_sts_priv_world W0 W6) as Hpriv_W0_W6.
    { eapply related_sts_priv_trans_world;
        [exact Hrelated_priv_W0_W2q|].
      eapply related_sts_priv_trans_world;
        [apply related_sts_pub_priv_world; exact Hrelated_pub_W2q_W3|].
      eapply related_sts_priv_trans_world;
        [exact Hrelated_priv_W3_W5q|].
      apply related_sts_pub_priv_world; exact Hrelated_pub_W5q_W6. }
    assert (related_sts_priv_world W3 W6) as Hpriv_W3_W6.
    { eapply related_sts_priv_trans_world;
        [exact Hrelated_priv_W3_W5q|].
      apply related_sts_pub_priv_world; exact Hrelated_pub_W5q_W6. }
    assert (related_sts_pub (loc W0) (loc W6)
      (wrel W0) (wrel W6)) as Hcus0_W6.
    { destruct Hpub0_orig as (_ & Hcus & _).
      exact Hcus. }
    assert (related_sts_pub (loc W3) (loc W6)
      (wrel W3) (wrel W6)) as Hcus3_W6.
    { assert (related_sts_pub (loc W3) (loc W5q)
        (wrel W3) (wrel W5q)) as Hcus3_W5q.
      { destruct Hrelated_pub_W4_W5 as (_ & Hcus & _).
        subst W5q W5 W4. cbn in *. exact Hcus. }
      destruct Hrelated_pub_W5q_W6 as (_ & Hcus5_W6 & _).
      eapply related_sts_pub_trans; eauto. }
    assert (related_sts_pub_world W0 (close_list closing W7))
      as Hpub0_fixed.
    { subst W7.
      eapply vae_repair_public_world; eauto. }
    assert (related_sts_pub_world W3 (close_list closing W7))
      as Hpub3_fixed.
    { subst W7.
      eapply vae_repair_public_world; eauto. }
    assert (related_sts_pub_world W6 (close_list closing W7))
      as Hpub6_fixed.
    { subst W7.
      eapply vae_repair_public_world.
      - apply related_sts_priv_refl_world.
      - apply related_sts_pub_refl.
      - exact Hclosing_covers_W6.
      - exact Hclosing_revoked_W7. }
    iDestruct (RevokedCells_RevokedResources with "Hl0_live") as "Hl0_live".
    iDestruct (RevokedCells_RevokedResources with "Hl1_unique") as "Hl1_unique".
    iDestruct (RevokedResources_mono_pub W0 (close_list closing W7)
      C l0_live [] Hpub0_fixed with "Hl0_live")
      as "Hl0_fixed".
    iDestruct (RevokedResources_mono_pub W3 (close_list closing W7)
      C l1_unique [] Hpub3_fixed with "Hl1_unique")
      as "Hl1_fixed".
    iDestruct (RevokedResources_mono_pub W6 (close_list closing W7)
      C l2_unique [] Hpub6_fixed with "Hl2_unique")
      as "Hl2_fixed".
    iAssert (RevokedResources (close_list closing W7) C closing_revoked)%I
      with "[Hl0_fixed Hl1_fixed Hl2_fixed]" as "Hrevoked".
    { subst closing_revoked. rewrite !RevokedResources_app. iFrame. }
    iModIntro.
    iExists closing_revoked.
    iFrame "Hworld_interp_C Hrevoked".
    iPureIntro.
    split; first exact Hwst_i_W6.
    split; first exact Hpub0_fixed.
    split; first exact Hclosing_nodup.
    exact Hclosing_covers_W0.
  Qed.

End VAE_World_Return.
