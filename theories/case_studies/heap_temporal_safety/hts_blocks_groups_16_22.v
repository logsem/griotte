From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec_blocks.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region wp_rules_interp
  hts_blocks_groups_0_5 hts_blocks_groups_6_10 hts_blocks_groups_11_15.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import region_invariants heap_ghost logrel rules.
From griotte Require Import proofmode register_tactics map_simpl.

Section Heap_Temporal_Safety_Blocks.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    {allocator_historyg : allocatorHistoryG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {C : CmptName}.

  Lemma hts_phase_16_22
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (C_f : Sealable) (W_init_C : WORLD)
    (Ws : list WORLD) (Cs : list CmptName)
    (Nassert Nswitcher : namespace) (cstk : CSTK) :
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    disjoint_from_shadow cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    hts_phase16_pre (C:=C) pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nassert Nswitcher cstk
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap
      HsubBounds Hcgp_contiguous) "Hphase16".
    rewrite /hts_phase16_pre.
    iDestruct "Hphase16" as
      (b a_freecall a_free_result Wshare Wret Wfree wcs0 wcs1
       rmap_free stk_after l lret) "Hphase16".
    iDestruct "Hphase16" as
      "(%Hbounds & %Hsucc & %Ha_free_result & %Hrelated_init_share
        & %Hrelated_share_ext_ret & %HWfree
        & %Hdom_rmap_free & %Hcs0_nonheap & %Hcs1_nonheap
        & %Hstk_shadow & %Hstk_heap & %Hstack_revoked_W0
        & #Hstack_revoked_W0 & Hstack_revoked_ret
        & %Hstack_revoked_ret & #Hassert & #Halloc & #Hservice
        & #Hswitcher & #Hexport_pcc & #Hexport_cgp
        & #Hexport_malloc & #Hexport_free
        & #Hadv & #Hentry & #Hinterp_csp & HK
        & Himport_assert & Himport_adv & Himport_free
        & Himports_tail & Hp & Himport_switcher & Himport_malloc
        & Hworld & Hrevoked_l & Hrevoked_lret & Hna & Hcra
        & Hcs0 & Hcs1 & Hcsp & Hstk & Hcstk & Hallocation
        & Hrmap & Hca1 & Hcgp & Hsaved & HPC & Hca0 & Hcode)".
    iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
    iEval (cbv [fmap list_fmap concat]) in "Hcode".
    (* Block 16: clear the second adversary argument. *)
    focus_block 16 "Hcode" as a_zero Ha_zero "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Mov ca0 0. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    (* Block 17: fetch the switcher entry. *)
    focus_block 17 "Hcode" as a_fetch17 Ha_fetch17 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp;ct2] as
      ["[Hctp %Hwctp]";"[Hct2 %Hwct2]"].
    iExtractList "Hrmap" [ct0] as ["[Hct0 %Hwct0]"].
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch17
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ _ with "[- $HPC $Hctp $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { exact H0. }
    { rewrite /hts_switcher_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply switcher_call_sentry_not_heap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_switcher_offset)%a with pc_b
      by (rewrite /hts_switcher_offset; solve_addr).
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & Hct0 & Hct2 & Hfetch & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 18: fetch the adversary entry. *)
    focus_block 18 "Hcode" as a_fetch18 Ha_fetch18 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["[Hct1 %Hwct1]"].
    iApply (fetch_spec hts_adv_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch18 (WSealed ot_switcher C_f)
      _ _ _ _ with "[- $HPC $Hct1 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { exact H0. }
    { rewrite /hts_adv_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { exact Hadv_nonheap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_adv_offset)%a with (pc_b ^+ 2)%a by reflexivity.
    iFrame "Himport_adv".
    iNext; iIntros "(HPC & Hct1 & Hct0 & Hct2 & Hfetch & Himport_adv)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 19: call the adversary with zero. *)
    focus_block 19 "Hcode" as a_advcall2 Ha_advcall2 "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr_success "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    assert (related_sts_priv_world Wret Wfree) as Hrelated_ret_free.
    { rewrite HWfree.
      eapply related_sts_priv_pub_trans_world.
      - apply revoke_related_sts_priv_world.
      - apply related_sts_pub_world_heap_update.
        apply heap_quarantine_future. }
    iDestruct (StackRevokedResources_mono_priv Wret Wfree C
      (finz.seq_between csp_b csp_e) Hrelated_ret_free
      with "Hstack_revoked_ret") as "Hstack_revoked_free".
    assert (revoked_addresses Wfree (finz.seq_between csp_b csp_e))
      as Hstack_revoked_free.
    { rewrite HWfree /revoked_addresses /=.
      exact Hstack_revoked_ret. }

    iAssert (interp Wfree C (WSealed ot_switcher C_f))
      as "#Hinterp_adv_free".
    { destruct C_f as [t p g base endp off | t p g ob oe oa].
      - destruct t.
        + rewrite !fixpoint_interp1_eq /= /interp_sb.
          iDestruct "Hadv" as "[$ %Hvalid]".
          iPureIntro.
          destruct (isO p); first done.
          rewrite /heap_cap_valid in Hvalid |- *.
          intros Hlt.
          specialize (Hvalid Hlt).
          rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
            in Hadv_nonheap.
          destruct (is_heap_address base) eqn:Hheap; first discriminate.
          rewrite /heap_cap_live Hheap in Hvalid |- *.
          exact Hvalid.
        + iApply interp_untagged. reflexivity.
      - destruct t.
        + rewrite !fixpoint_interp1_eq /= /interp_sb.
          iDestruct "Hadv" as "[$ _]".
        + iApply interp_untagged. reflexivity. }
    iAssert (interp Wfree C (WInt 0)) as "#Hinterp_zero".
    { iApply interp_int. }
    clear Ha_zero Ha_fetch17 Ha_fetch18.
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %Hwca2]";"[Hca3 %Hwca3]";
       "[Hca4 %Hwca4]";"[Hca5 %Hwca5]"].
    subst wca2 wca3 wca4 wca5.
    set (adv_arg := ({[ca0 := WInt 0; ca1 := WInt 0;
      ca2 := WInt 0; ca3 := WInt 0; ca4 := WInt 0;
      ca5 := WInt 0; ct0 := WInt 0]} : Reg)).
    iAssert ([∗ map] rarg↦warg ∈ adv_arg,
      rarg ↦ᵣ warg ∗ if decide (rarg ∈ dom_arg_rmap 1)
        then interp Wfree C warg else True)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hadv_arg".
    { subst adv_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct2].
    set (adv_other := <[ct2:=WInt 0]>
      (<[ctp:=WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap_free)))))))).
    iApply (switcher_cc_specification Nswitcher Wfree C
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_advcall2 ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b C_f
      (region_addrs_zeroes csp_b csp_e)
      adv_arg adv_other cstk Ws Cs 1
      with "[- $Halloc $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp
        $Hct1 $Hentry $Hcs0 $Hcs1 $Hadv_arg $Hrmap $Hstk
        $Hworld $Hstack_revoked_free $Hcstk $HK $Hinterp_adv_free]").
    { exact Hstk_shadow. }
    { exact Hstk_heap. }
    { subst adv_other. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap_free /dom_arg_rmap /=. set_solver+. }
    { subst adv_arg. rewrite /is_arg_rmap /dom_arg_rmap /=. reflexivity. }
    iSplitR; first (iPureIntro; exact Hstack_revoked_free).
    iNext.
    iIntros (Wret2 rmap_after2 stk_after2 lret2 rcgp rcra rcs0 rcs1)
      "(%Hlret2_unk & Hrevoked_lret2 & %Hrevoked_lret2
       & %Hrelated_free_ext_ret2 & Hrel_stk_ret2 & %Hdom_rmap_after2
       & Hstack_revoked_ret2 & %Hstack_revoked_ret2
       & Hna & %Hcsp_bounds_ret2 & Hworld & Hcstk
       & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
       & [%warg0 [Hca0 _]] & [%warg1 [Hca1 _]]
       & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hgp_ret2 & Hra_ret2 & Hs0_ret2 & Hs1_ret2).
    apply load_heap_nonheap in Hgp_ret2.
    2: { destruct Hcgp_heap as [Hcgp_nonheap _].
         rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hcgp_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hra_ret2.
    2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hpc_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hs0_ret2; [|exact Hcs0_nonheap].
    apply load_heap_nonheap in Hs1_ret2; [|exact Hcs1_nonheap].
    subst rcgp rcra rcs0 rcs1.
    iEval (cbn) in "HPC".

    (* Block 20: load the private p cell and prepare zero for assertion. *)
    focus_block 20 "Hcode" as a_prep Ha_prep "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct0;ct1] as
      ["[Hct0 %Hwct0_after2]";"[Hct1 %Hwct1_after2]"].
    iApply (hts_assert_prep_spec pc_b pc_e a_prep cgp_b cgp_e _ _
      with "[- $HPC $Hcgp $Hct0 $Hct1 $Hp $Hblock]").
    { exact Hcgp_shadow. }
    { rewrite /hts_main_data in Hcgp_contiguous. solve_addr. }
    { exact H0. }
    iNext. iIntros "(HPC & Hcgp & Hct0 & Hct1 & Hp & Hblock)".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 21: fetch and call the assertion service. *)
    focus_block 21 "Hcode" as a_assert Ha_assert "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct2;ct3;ct4;cnull] as
      ["[Hct2 %Hwct2_after2]";"[Hct3 %Hwct3_after2]";
       "[Hct4 %Hwct4_after2]";"[Hcnull %Hwcnull_after2]"].
    iApply (assert_success_spec with
      "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1
        $Hcnull $Hcra $Hblock $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0
      & Hct1 & Hcnull & Hblock & Himport_assert)".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 22: terminate with the assertion service token restored. *)
    focus_block 22 "Hcode" as a_halt Ha_halt "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Halt. *)
    iInstr "Hblock".
    wp_end; iIntros "_"; iFrame.
  Qed.
End Heap_Temporal_Safety_Blocks.
