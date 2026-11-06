From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl register_tactics.
From griotte Require Import logrel rules.
From griotte Require Import world_interp_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_base.
From griotte Require Import locks locks_spec.
From griotte Require Import
  kvs kvs_preamble kvs_spec_check_uint16 kvs_spec_addOrUpdate.
From iris.base_logic Require Import ghost_map.

Section KVS_spec_addOrUpdate_safe.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf}
    {LK : locksLayout}
    (kvs_users : gmap user_key_t CmptName)
  .

  (* TODO: move to logrel/interp_world_free.v *)
  (** A word stored through a capability that is not write-local is valid
      in every world, at every thread: it is either untagged or not local. *)
  Lemma interp_store_every_thread W C p w :
    isWL p = false →
    interp W C w -∗ ∀ t : Thread, safeGC (interp_in_mem (th := t) RWL) (C, lstore_word p w).
  Proof.
    iIntros (Hwl) "#Hw". iIntros (t).
    iApply (interp_to_in_mem (th := t)).
    destruct (canStore p w.(lw)) eqn:Hcs.
    - rewrite lstore_word_canStore //.
      rewrite -(interp_global_thread_world_free th t W ∅ C w); first done.
      by eapply canStore_global_nonisWL.
    - assert (lstore_word p w = lclear_tag w) as ->.
      { by rewrite /lstore_word /lclear_tag /lift_word /store_word Hcs. }
      iApply interp_clear_tag.
  Qed.

  (*** Specification from unknown *)
  Lemma KVS_addOrupdate_spec_safe
    (Wca W : WORLD) (C : CmptName)
    (wret wca0 wca1 wca2 : LWord)
    (F : coPset)
    (mie : InterruptStatus)
    :

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_heap_address kvs_lock_addr = false ->
    is_heap_address b_locks = false ->

    related_sts_priv_world Wca W ->
    jalr_target_ok cnull cra wret.(lw) = true ->
    th ≠ CtxSwitch ->
    route_pre th mie ->

    ( KVS_OTYPE ↪ₒ{SealGlobal} kvs_otype_propC kvs_users ∗
      kvs_static ∗
      kvs_lock kvs_users ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      MIE ↦ₜ[th] mie ∗
      held (th := th) mie ∗
      ca0 ↦ᵣ[th] wca0 ∗ interp Wca C wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] wca1 ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ interp Wca C wca2 ∗ (* New value *)
      cs0 ↦ᵣ[th] - ∗ (* scratch: the lock *)
      cs1 ↦ᵣ[th] - ∗ (* scratch *)
      ct0 ↦ᵣ[th] - ∗ (* scratch *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      world_resources W C ∗

      ( ▷ (na_own (tpool th) F ∗
           PC ↦ₚ[th] lupdatePcPerm wret ∗
           cgp ↦ᵣ[th] - ∗
           cra ↦ᵣ[th] - ∗
           MIE ↦ₜ[th] default mie (jalr_target_mie wret.(lw)) ∗
           held (th := th) (default mie (jalr_target_mie wret.(lw))) ∗
           (ca0 ↦ᵣ[th] WInt ASM_TRUE ∨ ca0 ↦ᵣ[th] WInt ASM_FALSE) ∗
           ca1 ↦ᵣ[th] WInt 0 ∗
           ca2 ↦ᵣ[th] - ∗
           cs0 ↦ᵣ[th] - ∗
           cs1 ↦ᵣ[th] - ∗
           ct0 ↦ᵣ[th] - ∗
           ctp ↦ᵣ[th] - ∗
           ct1 ↦ᵣ[th] - ∗
           ct2 ↦ᵣ[th] - ∗

           world_resources W C

           -∗ safe[th]
        ) ∧
        (* The load after the failed unsealing of the user key faults *)
        ▷ ( ∀ a,
            na_own (tpool th) F ∗
            cgp ↦ᵣ[th] - ∗
            cra ↦ᵣ[th] - ∗
            MIE ↦ₜ[th] mie ∗
            held (th := th) mie ∗
            ca0 ↦ᵣ[th] - ∗
            ca1 ↦ᵣ[th] - ∗
            ca2 ↦ᵣ[th] - ∗
            cs0 ↦ᵣ[th] - ∗
            cs1 ↦ᵣ[th] - ∗
            ct0 ↦ᵣ[th] - ∗
            ctp ↦ᵣ[th] - ∗
            ct1 ↦ᵣ[th] - ∗
            ct2 ↦ᵣ[th] - ∗
            world_resources W C -∗
            trap_safe (Cap RX Global KVS_pcc_b KVS_pcc_e a) ⊤
              (HO th) ) )
      ⊢ safe[th])%I.
  Proof.
    iIntros (Hunsealing_shadow Hlock_heap Hlocks_heap Hrelated_Wca_W Htgt Hth Hroute)
      "(#Hspred & #Hkvs_static & #Hlock & Hna & HPC & Hcgp & Hcra &
        Hmie & Hheld & Hca0 & #Hinterp_wca0
      & Hca1 & Hca2 & #Hinterp_wca2 & Hcs0 & Hcs1 & Hct0 & Hctp & Hct1 & Hct2 & Hworld & Hpost)".

    (* Destruct validity map key *)
    destruct (decide (word_is_uint16 wca1.(lw))) as [Hwca1_uint16|Hwca1_uint16]; cycle 1.
    { (* the map key argument is not a uint16 *)
      iDestruct "Hpost" as "[Hpost _]".
      iApply (KVS_addOrUpdate_spec_not_uint16_map_key wret wca1 F mie with
               "[- $Hkvs_static $Hna $HPC $Hcra $Hmie $Hheld $Hca0 $Hca1 $Hct1]");
        [exact Hwca1_uint16 | exact Htgt | exact Hth | exact Hroute |].
      iNext; iIntros "(Hna & HPC & Hcra & Hmie & Hheld & Hca0 & Hca1 & Hct1)".
      iApply "Hpost"; iFrame.
    }
    destruct wca1 as [ [nkey| | | ] πnkey]; cbn in Hwca1_uint16; try done.

    (* Untagged user keys fail at UnSeal, before opening seal resources. *)
    destruct (get_tag wca0.(lw)) eqn:Hwca0_tag; cycle 1.
    { iApply (KVS_addOrUpdate_spec_invalid_sealed_user_key wret wca0 nkey πnkey F
               with "[$Hkvs_static $Hna $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hctp
                      Hworld Hpost Hca2 Hcs0 Hcs1 Hct0 Hmie Hheld]");
        [exact Hunsealing_shadow | exact Hwca1_uint16
        | right; exact Hwca0_tag |].
      iNext; iIntros (a_fault) "(Hna & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[$]"). }

    (* Destruct validity user key *)
    destruct ( is_sealed_with_o wca0.(lw) KVS_OTYPE ) eqn:Hwca0_sealed_with_kvs_ot; cycle 1.
    { (* the user key argument is not a valid sealed user key *)
      iApply (KVS_addOrUpdate_spec_invalid_sealed_user_key wret wca0 nkey πnkey F
               with "[$Hkvs_static $Hna $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hctp
                      Hworld Hpost Hca2 Hcs0 Hcs1 Hct0 Hmie Hheld]");
        [exact Hunsealing_shadow | exact Hwca1_uint16
        | left; exact Hwca0_sealed_with_kvs_ot |].
      iNext; iIntros (a_fault) "(Hna & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[$]").
    }
    (* The inputs are valid. *)
    iDestruct "Hpost" as "[Hpost _]".
    (* The key word and the user of the sealed user key *)
    iMod (kvs_otype_acc kvs_users ⊤ Wca C wca0 Hwca0_tag Hwca0_sealed_with_kvs_ot
           with "Hspred Hinterp_wca0")
      as (l_user_key a uk) "(%Heq_sb & %Hbounds & %Huser_key_shadow & #Ha & %Huk)".
    subst wca0.
    assert (nkey ∈ kvs_all_map_keys) as Hnkey_is_map_key by rewrite -is_uint16_in_kvs_all_map_keys //.

    iApply (KVS_addOrUpdate_spec_layer_0 kvs_users wret wca2 uk nkey πnkey l_user_key a DfracDiscarded mie
              (λ _, True)%I with "[-]").
    1: exact Hunsealing_shadow. 1: exact Huser_key_shadow. 1: exact Hlock_heap. 1: exact Hlocks_heap.
    1: exact Hbounds. 1: exact Hwca1_uint16. 1: exact Htgt. 1: exact Hth. 1: exact Hroute.
    iFrame "Hkvs_static Hlock HPC Hcgp Hcra Hmie Hheld Hca1 Hca2 Hcs0 Hcs1 Hct0 Hctp Hct1 Hct2".
    iSplitL "Hca0"; first iExact "Hca0".
    iSplitR; first iExact "Ha".
    iSplitR.
    - (* the critical section: the map of the user [uk], valid in [C] *)
      iIntros "(Hphys & Hlog & Husers)".
      iDestruct (big_sepM_lookup_acc with "Husers") as "[ [Huser Hpts] Husers_close]"; first exact Huk.
      iDestruct (big_sepS_delete _ _ nkey with "Hpts") as "[Hnk Hpts]"; first done.
      iAssert (∃ o, (uk, nkey) ↦(UKVS) o ∗
                 ∀ b : bool, (uk, nkey) ↦(UKVS) (if b then Some (lstore_word RW wca2) else o) -∗
                   safe_kvs_pointsto C uk nkey)%I
        with "[Hnk]" as (o) "[Hk Hk_close]".
      { iDestruct "Hnk" as "[ (%w & Hk & #Hw) | Hk ]".
        - iExists (Some w). iFrame "Hk". iIntros (b) "Hk". iLeft.
          destruct b; iExists _; iFrame "Hk"; last iExact "Hw".
          by iApply (interp_store_every_thread with "Hinterp_wca2").
        - iExists None. iFrame "Hk". iIntros (b) "Hk".
          destruct b; [iLeft; iExists _; iFrame "Hk" | by iRight].
          by iApply (interp_store_every_thread with "Hinterp_wca2"). }
      iDestruct (kvs_addOrUpdate_ghost uk nkey (lstore_word RW wca2) o Hwca1_uint16
                  with "[$Hphys $Hlog $Huser $Hk]") as (pkvs) "[HPKVS Hclose]".
      iModIntro. iExists pkvs. iFrame "HPKVS".
      iIntros (pkvs' b Hout) "HPKVS".
      iMod ("Hclose" $! pkvs' b Hout with "HPKVS") as "(Hphys & Hlog & Huser & Hk)".
      iModIntro. iSplit; last done. iFrame "Hphys Hlog".
      iApply "Husers_close". iFrame "Huser".
      iApply (big_sepS_delete _ _ nkey); first done.
      (* the other entries by name: framing the set of all keys is slow *)
      iSplitR "Hpts"; [by iApply "Hk_close" | iExact "Hpts"].
    - iNext. iIntros (b) "(_ & HPC & Hcgp & Hcra & Hmie & Hheld & Hca0 & Hca1 & Hca2
                         & Hcs0 & Hcs1 & Hct0 & Hctp & Hct1 & Hct2 & _)".
      iApply "Hpost".
      iFrame "Hna HPC Hcgp Hcra Hmie Hheld Hca1 Hca2 Hcs0 Hcs1 Hct0 Hctp Hct1 Hct2 Hworld".
      destruct b; [iLeft | iRight]; iFrame.
  Qed.

  (*** Safe entry point *)

  (** The entry of [addOrUpdate] at the thread [th] of [C]. *)
  Lemma kvs_addOrUpdate_exec_entry_point (W : WORLD) (C : CmptName) :
    KVS_pcc_b ≠ b_switcher ->
    is_heap_address kvs_lock_addr = false ->
    is_heap_address b_locks = false ->
    KVS_OTYPE ↪ₒ{SealGlobal} kvs_otype_propC kvs_users ∗
    kvs_static ∗
    kvs_lock kvs_users ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    no_handler b_kvs_exp_tbl -∗
    execute_entry_point b_kvs_exp_tbl
      (Cap RX Global KVS_pcc_b KVS_pcc_e (KVS_pcc_b ^+ kvs_addOrUpdate_pcc_off))
      (Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b)
      kvs_addOrUpdate_nargs kvs_addOrUpdate_min_stack InterruptEnabled W C.
  Proof.
    iIntros (Hpc_switcher Hlock_heap Hlocks_heap)
      "(#Hspred & #Hkvs_static & #Hlock & #Hinv_switcher & #Hswitcher_static & [#Hkvs_exp_eh #Hkvs_exp_ehs])".
    iIntros (cstk Ws Cs rmap csp_b csp_e).
    iIntros "(#Hthread & _ & HK & %Hframe_match & %Htop_tbl & HPC & Hregister_state & Hrmap
      & Hworld_C & _ & %Hsync_csp & _ & Hcstk & Hna & %Hroute & Hmie & Hheld)".
    iAssert (no_handler (top_export_tbl cstk) ∗
             ⌜(top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)⌝)%I as "#Hno_handler".
    { destruct Htop_tbl as (_ & -> & _ & Htbl_ok). iFrame "Hkvs_exp_eh Hkvs_exp_ehs".
      iPureIntro. by apply tf_export_tbl_ok_nonzero. }
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /stk_start_a in Hcsp |- *.
    rewrite /registers_pointsto.

    (* Extract the registers that we will need *)
    assert ( is_Some (rmap !! ctp) ) as [wctp Hwctp] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct2) ) as [wct2 Hwct2] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! cs0) ) as [wcs0 Hwcs0] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! cs1) ) as [wcs1 Hwcs1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca2) ) as [wca2 Hwca2] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    iExtractList "Hrmap" [cgp; cra ; csp ] as ["Hcgp"; "Hcra"; "Hcsp"].
    iExtractList "Hrmap" [cs0; cs1; ct0; ct1; ct2; ctp; ca0; ca1; ca2]
      as ["Hcs0"; "Hcs1"; "Hct0"; "Hct1"; "Hct2"; "Hctp"; "Hca0"; "Hca1"; "Hca2"].

    iAssert (interp W C wca0) as "#Hinterp_wca0".
    { iApply "Hinterp_rmap"; eauto; by rewrite /kvs_addOrUpdate_nargs. }
    iAssert (interp W C wca2) as "#Hinterp_wca2".
    { iApply "Hinterp_rmap"; eauto; by rewrite /kvs_addOrUpdate_nargs. }

    iAssert ([∗ list] a ∈ finz.seq_between csp_b csp_e, ⌜std W !! LNonHeap a = Some Temporary⌝)%I
      as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap_nonheap with "Hinterp_W0_csp"); eauto. }
    (* The callee's stack, revoked in the local map of [C] *)
    iEval (rewrite world_resources_split) in "Hworld_C".
    iDestruct "Hworld_C" as "[Hlocal_C Hperm_C]".
    iMod (local_revoke_stack with "[$Hinterp_W0_csp $Hlocal_C]")
        as (l) "(%Hl_unk & Hlocal_C & #Hstack_revoked_W0 & _ & >[%stk_mem Hstk] & [Hrevoked_l _])".
    iAssert (world_resources (revoke W) C) with "[Hlocal_C Hperm_C]" as "Hworld_C".
    { rewrite world_resources_split. iFrame. }
    assert (related_sts_priv_world W (revoke W)) as Hrelated_priv_W0_W1 by eapply revoke_related_sts_priv_world.

    assert (is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false)
      as Hunsealing_shadow.
    { eapply disjoint_from_shadow_not_in; first exact KVS_pcc_disjoint_from_shadow.
      apply withinBounds_true_iff.
      pose proof KVS_size_imports as Himports.
      pose proof KVS_size_code as Hcode_size.
      rewrite /length_kvs_imports in Himports.
      rewrite /UNSEALING_USER_KEY_OFFSET; solve_addr+Himports Hcode_size. }
    (* The world fixed by the return through the switcher *)
    set (Wfixed := (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) (revoke W))).
    destruct Hl_unk as [ Hnodup Htemps ]; auto.
    assert (related_sts_pub_world W Wfixed) as Hrelated_pub_W0_Wfixed.
    { subst Wfixed. apply related_pub_revoke_close_list; exact Htemps. }
    iDestruct (RevokedResources_mono_pub W Wfixed C l l
      Hrelated_pub_W0_Wfixed with "Hrevoked_l") as "Hrevoked_l".

    iApply (KVS_addOrupdate_spec_safe W (revoke W) C
              (Sentry (ret_kind InterruptEnabled) XSRW_ Local b_switcher e_switcher
                a_switcher_return)
              wca0 wca1 wca2 ⊤ InterruptEnabled Hunsealing_shadow Hlock_heap Hlocks_heap
              Hrelated_priv_W0_W1
             with "[$Hspred $Hkvs_static $Hlock $Hna $HPC $Hcgp $Hcra
               $Hmie $Hheld $Hca0 $Hinterp_wca0 $Hca1 $Hca2 $Hinterp_wca2 $Hcs0 $Hcs1 $Hct0
               $Hctp $Hct1 $Hct2 $Hworld_C Hrmap Hcsp Hstk Hcstk HK Hrevoked_l]");
      [ apply jalr_target_ok_switcher_return_sentry
      | intros ->; by specialize (Hroute eq_refl) | exact Hroute |].
    iSplit.
    - iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hmie & Hheld & Hca0 & Hca1 & Hca2 & Hcs0 & Hcs1 & Hct0
        & Hctp & Hct1 & Hct2 & Hworld_C)".
      iAssert (∃ zca0, ca0 ↦ᵣ WInt zca0)%I with "[Hca0]" as "[%zca0 Hca0]".
      { iDestruct "Hca0" as "[$|$]". }
      iDestruct "Hca2" as "[% Hca2]"; iDestruct (big_sepM_insert _ _ ca2 with "[$Hrmap $Hca2]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct2" as "[% Hct2]"; iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct1" as "[% Hct1]"; iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hctp" as "[% Hctp]"; iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct0" as "[% Hct0]"; iDestruct (big_sepM_insert _ _ ct0 with "[$Hrmap $Hct0]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcs1" as "[% Hcs1]"; iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcs0" as "[% Hcs0]"; iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcra" as "[% Hcra]"; iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcgp" as "[% Hcgp]"; iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      map_simpl "Hrmap".
      iApply (switcher_ret_specification_shared W (revoke W)
               with
               "[ $Hthread $Hinv_switcher $Hswitcher_static $Hstk $Hcstk $HK $Hworld_C $Hna $HPC $Hrevoked_l
               $Hrmap $Hca0 $Hca1 $Hcsp $Hmie]"
             ); last iFrame "∗#".
      { exact Hrelated_pub_W0_Wfixed. }
      { apply lregmap_full_dom in Hrmap_init.
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hrmap_init. set_solver+. }
      { exact Hframe_match. }
      { exact Hsync_csp. }
      { exact Hnodup. }
      { intros a Ha; apply Htemps; done. }
      { iSplit; iApply interp_int. }
    - (* The invalid user key faults: return ECOMPARTMENTFAIL to the caller *)
      iNext; iIntros (a_fault) "(Hna & Hcgp & Hcra & Hmie & Hheld & Hca0 & Hca1 & Hca2 & Hcs0 & Hcs1
        & Hct0 & Hctp & Hct1 & Hct2 & Hworld_C)".
      iDestruct "Hca2" as "[% Hca2]"; iDestruct (big_sepM_insert _ _ ca2 with "[$Hrmap $Hca2]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct2" as "[% Hct2]"; iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct1" as "[% Hct1]"; iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hctp" as "[% Hctp]"; iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct0" as "[% Hct0]"; iDestruct (big_sepM_insert _ _ ct0 with "[$Hrmap $Hct0]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcs1" as "[% Hcs1]"; iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcs0" as "[% Hcs0]"; iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcra" as "[% Hcra]"; iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcgp" as "[% Hcgp]"; iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      map_simpl "Hrmap".
      iApply (trap_safe_return_shared W (revoke W) C _ csp_e csp_b l stk_mem cstk Ws Cs _
               with "Hthread Hinv_switcher Hswitcher_static Hno_handler [-]");
        last (iModIntro; iFrame "∗ %").
      { exact Hrelated_pub_W0_Wfixed. }
      { apply lregmap_full_dom in Hrmap_init.
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hrmap_init. set_solver+. }
      { exact Hframe_match. }
      { exact Hsync_csp. }
      { exact Hnodup. }
      { intros a Ha; apply Htemps; done. }
      { by apply trap_no_resume_cap. }
  Qed.

End KVS_spec_addOrUpdate_safe.

Section KVS_addOrUpdate_entry_point.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf}
    {LK : locksLayout}
    (kvs_users : gmap user_key_t CmptName)
  .

  (** The entry of [addOrUpdate], at every thread of [C]: the entry runs on
      its own thread, and the resources of the KVS do not depend on it. *)
  Lemma kvs_addOrUpdate_entry_point_spec
    (g_kvs_exp_tbl : Locality)

    (W : WORLD)
    (C : CmptName)

    :

    let a_kvs_exp_tbl_cgp := (b_kvs_exp_tbl ^+ ExportTable_offset_cgp) in
    KVS_pcc_b ≠ b_switcher ->
    is_heap_address kvs_lock_addr = false ->
    is_heap_address b_locks = false ->
    KVS_OTYPE ↪ₒ{SealGlobal} kvs_otype_propC kvs_users ∗
    kvs_static ∗
    kvs_lock kvs_users ∗
    switcher_threads C ∗
    b_kvs_exp_tbl ↦ₐ□ Cap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b ∗
    a_kvs_exp_tbl_cgp ↦ₐ□ Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
    no_handler b_kvs_exp_tbl ∗
    kvs_addOrUpdate_exp_tbl_addr ↦ₐ□ kvs_exp_tbl_entry_addOrUpdate
    -∗
    ot_switcher_prop W C (Cap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
  Proof.
    intros a_kvs_exp_tbl_cgp Hpc_switcher Hlock_heap Hlocks_heap.
    subst a_kvs_exp_tbl_cgp.
    iIntros
      "(#Hspred & #Hkvs_static & #Hlock & #Hswitcher_threads
      & #Hkvs_exp_PCC
      & #Hkvs_exp_CGP
      & [#Hkvs_exp_eh #Hkvs_exp_ehs]
      & #Hkvs_exp_addOrRead
      )".
    iExists g_kvs_exp_tbl, b_kvs_exp_tbl, e_kvs_exp_tbl, kvs_addOrUpdate_exp_tbl_addr,
    KVS_pcc_b, KVS_pcc_e, KVS_cgp_b, KVS_cgp_e, kvs_addOrUpdate_nargs, kvs_addOrUpdate_min_stack,
    kvs_addOrUpdate_pcc_off, InterruptEnabled, ExportTable_no_handler, ExportTable_no_handler.
    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    (* The table's words by name: [iFrame "#"] would try the other hypotheses on the entry *)
    iFrame "Hkvs_exp_PCC Hkvs_exp_CGP Hkvs_exp_eh Hkvs_exp_ehs Hkvs_exp_addOrRead".
    iSplit; first done.
    iSplit; first (iPureIntro; exact kvs_exp_tbl_disjoint_from_shadow).
    iSplit; first by (iPureIntro; rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off
                        /kvs_entry_addOrUpdate; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off
                        /kvs_entry_addOrUpdate; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off
                        /kvs_entry_addOrUpdate; solve_addr).
    iSplit; first (iPureIntro; rewrite /kvs_addOrUpdate_nargs; lia).
    iSplit; first (iPureIntro; rewrite /kvs_addOrUpdate_min_stack; lia).
    iSplit; first (iPureIntro; exists KVS_pcc_b'; exact KVS_size_imports).
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact kvs_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff.
        rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off /kvs_entry_addOrUpdate; solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact kvs_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff; solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact kvs_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff; solve_addr. }
    iSplit; first (iPureIntro; exact KVS_pcc_base_not_heap).
    iSplit; first (iPureIntro; exact KVS_cgp_base_not_heap).
    (* At each thread of [C], the entry at that thread *)
    iIntros "!>" (t') "#Ht'".
    iDestruct ("Hswitcher_threads" $! t' with "Ht'") as "[#Hswitcher' #Hswitcher_static']".
    iDestruct (kvs_static_thread_indep th t' with "Hkvs_static") as "#Hkvs_static'".
    iIntros (W0).
    iNext.
    iApply (kvs_addOrUpdate_exec_entry_point (th := t') kvs_users W0 C
              Hpc_switcher Hlock_heap Hlocks_heap).
    iFrame "Hspred Hkvs_static' Hlock Hswitcher' Hswitcher_static'".
    iSplit.
    - iApply (handler_stackful_thread_indep th t' with "Hkvs_exp_eh").
    - iApply (handler_stackless_thread_indep th t' with "Hkvs_exp_ehs").
  Qed.

End KVS_addOrUpdate_entry_point.
