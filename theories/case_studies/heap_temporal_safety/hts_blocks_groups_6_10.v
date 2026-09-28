From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec_blocks.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region wp_rules_interp hts_blocks_groups_0_5.
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

  (* Boundary after the successful free result and quarantine transition. *)
  Definition hts_phase16_pre
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (C_f : Sealable) (W_init_C : WORLD) (Ws : list WORLD)
    (Cs : list CmptName) (Nassert Nswitcher : namespace) (cstk : CSTK)
    : iProp Σ :=
    (∃ (b a_freecall a_free_result : Addr)
       (Wshare Wret Wfree : WORLD) (wcs0 wcs1 : Word)
       (rmap_free : Reg) (stk_after : list Word) (l lret : list Addr),
      ⌜((heap_b < b)%a ∧ (b < b ^+ 1)%a ∧ (b ^+ 1 <= heap_e)%a) ∧
        ((b ^+ 1)%a - b)%Z = 1%Z⌝ ∗
      ⌜(b + 1)%a = Some (b ^+ 1)%a⌝ ∗
      ⌜(pc_a + length
        (concat (take 15 (encodeInstrsW <$> assembled_hts_main))))%a =
        Some a_free_result⌝ ∗
      ⌜related_sts_priv_world W_init_C Wshare⌝ ∗
      ⌜related_sts_pub_world
        (std_update_multiple Wshare
          (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) Wret⌝ ∗
      ⌜Wfree = heap_std_update (revoke Wret)
        (heap_quarantine (heap_std (revoke Wret)) b)⌝ ∗
      ⌜dom rmap_free = all_registers_s ∖
        {[ PC; csp; cgp; cra; cs0; cs1; ca0; ca1 ]}⌝ ∗
      ⌜is_heap_cap wcs0 = false⌝ ∗
      ⌜is_heap_cap wcs1 = false⌝ ∗
      ⌜disjoint_from_shadow csp_b csp_e⌝ ∗
      ⌜disjoint_from_heap csp_b csp_e⌝ ∗
      ⌜Forall (λ a, std (revoke W_init_C) !! a = Some Revoked)
        (finz.seq_between csp_b csp_e)⌝ ∗
      StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e) ∗
      StackRevokedResources Wret C (finz.seq_between csp_b csp_e) ∗
      ⌜revoked_addresses (revoke Wret) (finz.seq_between csp_b csp_e)⌝ ∗
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
      allocator_ctx ∗ allocator_service_ctx ∗
      na_inv cerise_nais Nswitcher switcher_inv ∗
      inv (export_table_PCCN hts_allocator_exp_tblN)
        (allocator_exp_tbl_b ↦ₐ WCap true RX Global
          allocator_pcc_b allocator_pcc_e allocator_pcc_b) ∗
      inv (export_table_CGPN hts_allocator_exp_tblN)
        ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global
          allocator_cgp_b allocator_cgp_e allocator_cgp_b) ∗
      inv (export_table_entryN hts_allocator_exp_tblN
        (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a)
        ((allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a ↦ₐ
          WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off)) ∗
      inv (export_table_entryN hts_allocator_exp_tblN
        (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a)
        ((allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ
          WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)) ∗
      interp W_init_C C (WSealed ot_switcher C_f) ∗
      (WSealed ot_switcher C_f) ↦□ₑ 1 ∗
      interp W_init_C C (WCap true RWL Local csp_b csp_e csp_b) ∗
      interp_continuation cstk Ws Cs ∗
      (pc_b ^+ 1)%a ↦ₐ WSentry true RX Global b_assert e_assert b_assert ∗
      (pc_b ^+ 2)%a ↦ₐ WSealed ot_switcher C_f ∗
      (pc_b ^+ 4)%a ↦ₐ WSealed ot_switcher (allocator_free Global) ∗
      [[(pc_b ^+ 5)%a,pc_a]] ↦ₐ [[ [] ]] ∗
      cgp_b ↦ₐ WInt 0 ∗
      pc_b ↦ₐ WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
      (pc_b ^+ 3)%a ↦ₐ WSealed ot_switcher (allocator_malloc Global) ∗
      world_interp Wfree C ∗
      RevokedResources W_init_C C l ∗
      RevokedResources Wret C lret ∗
      na_own cerise_nais ⊤ ∗
      cra ↦ᵣ WSentry true RX Global pc_b pc_e (a_freecall ^+ 1)%a ∗
      cs0 ↦ᵣ wcs0 ∗ cs1 ↦ᵣ wcs1 ∗
      csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b ∗
      [[csp_b,csp_e]] ↦ₐ [[region_addrs_zeroes csp_b csp_e]] ∗
      cstack_frag cstk ∗
      allocator_allocation b (b ^+ 1)%a (0%Z, 0%Z) ∗
      ([∗ map] k↦y ∈ rmap_free, k ↦ᵣ y ∗ ⌜y = WInt 0⌝) ∗
      ca1 ↦ᵣ WInt 0 ∗
      cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
      (cgp_b ^+ 1)%a ↦ₐ WCap true RW Global b (b ^+ 1)%a b ∗
      PC ↦ᵣ WCap true RX Global pc_b pc_e
        (a_free_result ^+ length hts_free_result_instrs)%a ∗
      ca0 ↦ᵣ WInt 0 ∗
      codefrag pc_a hts_main_code)%I.

  (* Boundary after the live-buffer check, before the private store. *)
  Definition hts_phase11_pre
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (C_f : Sealable) (W_init_C : WORLD) (Ws : list WORLD)
    (Cs : list CmptName) (Nassert Nswitcher : namespace) (cstk : CSTK)
    : iProp Σ :=
    (∃ (b a_reload a_check : Addr) (Wshare Wret : WORLD)
       (obj_ret : AllocObject) (wcs0 wcs1 warg1 v_b : Word)
       (rmap_after : Reg) (stk_after : list Word) (l lret : list Addr),
      ⌜((heap_b < b)%a ∧ (b < b ^+ 1)%a ∧ (b ^+ 1 <= heap_e)%a) ∧
        ((b ^+ 1)%a - b)%Z = 1%Z⌝ ∗
      ⌜(b + 1)%a = Some (b ^+ 1)%a⌝ ∗
      ⌜(pc_a + length
        (concat (take 10 (encodeInstrsW <$> assembled_hts_main))))%a =
        Some a_check⌝ ∗
      ⌜related_sts_priv_world W_init_C Wshare⌝ ∗
      ⌜related_sts_pub_world
        (std_update_multiple Wshare
          (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) Wret⌝ ∗
      ⌜heap_wf (heap_std Wret)⌝ ∗
      ⌜heap_lookup_addr (heap_std (revoke Wret)) b = Some (b,obj_ret)⌝ ∗
      ⌜alloc_object_future
        (MkAllocObject b (b ^+ 1)%a AllocObjectLive) obj_ret⌝ ∗
      ⌜alloc_object_status obj_ret = AllocObjectLive⌝ ∗
      ⌜std (revoke Wret) !! b = Some Permanent⌝ ∗
      ⌜is_heap_address b = true⌝ ∗
      ⌜dom rmap_after = all_registers_s ∖
        {[ PC; cgp; cra; csp; ca0; ca1; cs0; cs1 ]}⌝ ∗
      ⌜is_heap_cap wcs0 = false⌝ ∗
      ⌜is_heap_cap wcs1 = false⌝ ∗
      ⌜disjoint_from_shadow csp_b csp_e⌝ ∗
      ⌜disjoint_from_heap csp_b csp_e⌝ ∗
      ⌜Forall (λ a, std (revoke W_init_C) !! a = Some Revoked)
        (finz.seq_between csp_b csp_e)⌝ ∗
      ⌜∀ a, (allocator_exp_tbl_b <= a < allocator_exp_tbl_e)%a →
        is_shadow_address a = false⌝ ∗
      ⌜revoked_addresses (revoke Wret) (finz.seq_between csp_b csp_e)⌝ ∗
      ⌜revoked_addresses (revoke Wret) lret⌝ ∗
      StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e) ∗
      StackRevokedResources Wret C (finz.seq_between csp_b csp_e) ∗
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
      allocator_ctx ∗ allocator_service_ctx ∗
      na_inv cerise_nais Nswitcher switcher_inv ∗
      inv (export_table_PCCN hts_allocator_exp_tblN)
        (allocator_exp_tbl_b ↦ₐ WCap true RX Global
          allocator_pcc_b allocator_pcc_e allocator_pcc_b) ∗
      inv (export_table_CGPN hts_allocator_exp_tblN)
        ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global
          allocator_cgp_b allocator_cgp_e allocator_cgp_b) ∗
      inv (export_table_entryN hts_allocator_exp_tblN
        (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a)
        ((allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a ↦ₐ
          WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off)) ∗
      inv (export_table_entryN hts_allocator_exp_tblN
        (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a)
        ((allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ
          WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)) ∗
      interp W_init_C C (WSealed ot_switcher C_f) ∗
      interp Wshare C (WSealed ot_switcher C_f) ∗
      (WSealed ot_switcher C_f) ↦□ₑ 1 ∗
      interp W_init_C C (WCap true RWL Local csp_b csp_e csp_b) ∗
      interp_continuation cstk Ws Cs ∗
      (pc_b ^+ 1)%a ↦ₐ WSentry true RX Global b_assert e_assert b_assert ∗
      (pc_b ^+ 2)%a ↦ₐ WSealed ot_switcher C_f ∗
      (pc_b ^+ 4)%a ↦ₐ WSealed ot_switcher (allocator_free Global) ∗
      [[(pc_b ^+ 5)%a,pc_a]] ↦ₐ [[ [] ]] ∗
      cgp_b ↦ₐ WInt 0 ∗
      pc_b ↦ₐ WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
      (pc_b ^+ 3)%a ↦ₐ WSealed ot_switcher (allocator_malloc Global) ∗
      world_interp_open (revoke Wret) C [b] ∗
      sts_state_std C b Permanent ∗
      rel C b RW interp_in_memC ∗
      b ↦ₐ v_b ∗
      RevokedResources W_init_C C l ∗
      RevokedResources Wret C lret ∗
      na_own cerise_nais ⊤ ∗
      cra ↦ᵣ WSentry true RX Global pc_b pc_e a_reload ∗
      cs0 ↦ᵣ wcs0 ∗ cs1 ↦ᵣ wcs1 ∗
      csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b ∗
      [[csp_b,csp_e]] ↦ₐ [[stk_after]] ∗
      cstack_frag cstk ∗
      allocator_allocation b (b ^+ 1)%a (0%Z, 0%Z) ∗
      ([∗ map] k↦y ∈ delete ct0 rmap_after, k ↦ᵣ y ∗ ⌜y = WInt 0⌝) ∗
      ca1 ↦ᵣ warg1 ∗
      cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
      (cgp_b ^+ 1)%a ↦ₐ WCap true RW Global b (b ^+ 1)%a b ∗
      PC ↦ᵣ WCap true RX Global pc_b pc_e
        (a_check ^+ length hts_check_buffer_instrs)%a ∗
      ca0 ↦ᵣ WCap true RW Global b (b ^+ 1)%a b ∗
      ct0 ↦ᵣ WInt 1 ∗
      codefrag pc_a hts_main_code)%I.
  Lemma hts_phase_6_10
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (rmap : Reg) (C_f : Sealable) (W_init_C : WORLD)
    (Ws : list WORLD) (Cs : list CmptName)
    (Nassert Nswitcher : namespace) (cstk : CSTK) :
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    disjoint_from_shadow cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    heap_std W_init_C = ∅ ->
    (hts_phase6_pre (C:=C) pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nassert Nswitcher cstk rmap ∗
     ▷ (hts_phase11_pre pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
       C_f W_init_C Ws Cs Nassert Nswitcher cstk -∗
       WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}))
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap
      HsubBounds Hcgp_contiguous Hheap_empty) "[Hphase6 Hcontinue]".
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    rewrite /hts_phase6_pre.
    iDestruct "Hphase6" as
      (b a_result a_store wcs0 wcs1 rmap_ret l)
      "(%Hbounds & %Ha_store & %Hsucc & %Hdom_rmap_ret
        & %Hcs0_nonheap & %Hcs1_nonheap & %Hstk_shadow & %Hstk_heap
        & %Hstack_revoked_W0 & %Hexport_shadow & #Hstack_revoked_W0
        & #Hassert & #Halloc & #Hservice & #Hswitcher
        & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
        & #Hadv & #Hentry & #Hinterp_csp & HK & Himport_assert
        & Himport_adv & Himport_free & Himports_tail & Hp
        & Himport_switcher & Himport_malloc & Hworld & Hrevoked_l
        & Hna & Hcra & Hcs0 & Hcs1 & Hcsp & Hstk & Hcstk
        & Hallocation & Hrmap & Hca1 & Hct0 & Hcgp & Hsaved
        & HPC & Hca0 & Hb & Hcode)".
    change ((pc_a + length
      (concat (take 5 (encodeInstrsW <$> assembled_hts_main))))%a = Some a_store)
      in Ha_store.
    iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
    iEval (cbv [fmap list_fmap concat]) in "Hcode".
    (* Block 6: fetch switcher for first adversary call. *)
    focus_block 6 "Hcode" as a_fetch6 Ha_fetch6 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp;ct2] as
      ["[Hctp %Hwctp]";"[Hct2 %Hwct2]"].
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch6
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ _ with "[- $HPC $Hctp $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { change (SubBounds pc_b pc_e a_fetch6 (a_fetch6 ^+ 9)%a).
      exact H0. }
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

    (* Block 7: fetch adversary entry. *)
    focus_block 7 "Hcode" as a_fetch7 Ha_fetch7 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["[Hct1 %Hwct1]"].
    iApply (fetch_spec hts_adv_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch7 (WSealed ot_switcher C_f)
      _ _ _ _ with "[- $HPC $Hct1 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
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

    (* Block 8: call adversary with buffer. *)
    focus_block 8 "Hcode" as a_advcall Ha_advcall "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr_success "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    assert (is_heap_address b = true) as Hb_heap.
    { apply withinBounds_true_iff. clear -Hbounds. solve_addr. }
    assert (heap_std (revoke W_init_C) = ∅) as Hheap_revoke.
    { rewrite revoke_heap. exact Hheap_empty. }
    iDestruct (hts_world_empty_heap_fresh (revoke W_init_C) C b
      Hb_heap Hheap_revoke with "Hworld") as %Hb_fresh.
    iMod (hts_world_heap_allocate_empty (revoke W_init_C) C b (b ^+ 1)%a
      with "Hworld") as "Hworld".
    { exact Hheap_revoke. }
    { exact (proj1 (proj2 (proj1 Hbounds))). }

    set (Wbuf := heap_std_update (revoke W_init_C)
      (heap_allocate ∅ b (b ^+ 1)%a)).
    iDestruct (init_PermRes Wbuf C b RW interp_in_memC (WInt 0)
      with "[] Hb []") as "Hbuf_perm".
    { done. }
    { iApply future_priv_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm Wbuf C b (WInt 0) RW interp_in_memC
      with "Hworld Hbuf_perm") as "(Hworld & #Hrel_b)".
    { rewrite /heap_addr_live /heap_addr_status Hb_heap /Wbuf
        /heap_std_update /=.
      assert (heap_fresh (∅ : Heap) b (b ^+ 1)%a) as Hfresh_buf.
      { split; first apply lookup_empty.
        split; first exact (proj1 (proj2 (proj1 Hbounds))).
        intros c o a Hc. rewrite lookup_empty in Hc. discriminate. }
      pose proof (heap_allocate_wf ∅ b (b ^+ 1)%a heap_wf_empty Hfresh_buf)
        as Hwf_buf.
      rewrite (heap_lookup_addr_complete (heap_allocate ∅ b (b ^+ 1)%a)
        b b (MkAllocObject b (b ^+ 1)%a AllocObjectLive) Hwf_buf).
      { reflexivity. }
      { rewrite /heap_allocate lookup_insert.
        case_decide; [reflexivity|congruence]. }
      { unfold alloc_object_contains; cbn.
        split; [clear -Hbounds; solve_addr|exact (proj1 (proj2 (proj1 Hbounds)))]. } }
    { subst Wbuf. rewrite /heap_std_update /=. exact Hb_fresh. }

    set (Wshare := <s[b := Permanent]s> Wbuf).
    iAssert (interp Wshare C (hts_buffer b)) as "#Hinterp_buf".
    { iEval (rewrite /hts_buffer fixpoint_interp1_eq /=).
      iSplitL.
      { rewrite (finz_seq_between_cons b); last solve_addr.
        rewrite (finz_seq_between_empty _ (b ^+ 1)%a); last solve_addr.
        iApply big_sepL_singleton.
        iExists RW, (interp_in_mem RWL). iEval (cbn).
        iSplit; first done. iSplit.
        { iPureIntro; intros WCv; tc_solve. }
        iSplit; first iFrame "Hrel_b".
        iSplit; first iApply zcond_interp_in_mem.
        iSplit; first iApply rcond_interp_in_mem.
        iSplit; first iApply wcond_interp_in_mem.
        iSplit; first iApply monoReq_interp_in_mem.
        - subst Wshare; cbn; simplify_map_eq; reflexivity.
        - by intro.
        - iPureIntro. subst Wshare; cbn; simplify_map_eq; reflexivity. }
      iPureIntro. split.
      { rewrite /disjoint_from_shadow elem_of_disjoint.
        intros a Ha Hsh.
        pose proof heap_shadow_disjoint as Hdisj.
        rewrite elem_of_disjoint in Hdisj.
        eapply Hdisj; last exact Hsh.
        apply elem_of_finz_seq_between.
        apply elem_of_finz_seq_between in Ha. solve_addr. }
      intros _. rewrite /heap_cap_live Hb_heap.
      rewrite /Wshare /Wbuf /heap_std_update /=.
      assert (heap_fresh (∅ : Heap) b (b ^+ 1)%a) as Hfresh_buf.
      { split; first apply lookup_empty.
        split; first exact (proj1 (proj2 (proj1 Hbounds))).
        intros c o a Hc. rewrite lookup_empty in Hc. discriminate. }
      pose proof (heap_allocate_wf ∅ b (b ^+ 1)%a heap_wf_empty Hfresh_buf)
        as Hwf_buf.
      rewrite (heap_lookup_addr_complete (heap_allocate ∅ b (b ^+ 1)%a)
        b b (MkAllocObject b (b ^+ 1)%a AllocObjectLive) Hwf_buf).
      { cbn. repeat split; try reflexivity; solve_addr. }
      { rewrite /heap_allocate lookup_insert.
        case_decide; [reflexivity|congruence]. }
      { unfold alloc_object_contains; cbn.
        split; [clear -Hbounds; solve_addr|exact (proj1 (proj2 (proj1 Hbounds)))]. } }

    assert (heap_fresh (∅ : Heap) b (b ^+ 1)%a) as Hfresh_buf.
    { split; first apply lookup_empty.
        split; first exact (proj1 (proj2 (proj1 Hbounds))).
      intros c o a Hc. rewrite lookup_empty in Hc. discriminate. }
    assert (related_sts_priv_world W_init_C Wshare) as Hrelated_init_share.
    { eapply related_sts_priv_pub_trans_world.
      - apply revoke_related_sts_priv_world.
      - eapply related_sts_pub_trans_world.
        + subst Wbuf. apply related_sts_pub_world_heap_update.
          rewrite revoke_heap Hheap_empty. apply heap_allocate_future.
          exact Hfresh_buf.
        + subst Wshare. apply related_sts_pub_world_fresh.
          subst Wbuf. rewrite /heap_std_update /=. exact Hb_fresh. }
    assert (heap_wf (heap_std Wshare)) as Hwf_share.
    { subst Wshare Wbuf. rewrite /heap_std_update /=.
      apply heap_allocate_wf; [apply heap_wf_empty|exact Hfresh_buf]. }
    assert (heap_authority_base (WSealed ot_switcher C_f) = None)
      as Hsealed_base.
    { destruct (heap_authority_base (WSealed ot_switcher C_f))
        as [base|] eqn:Hbase; last done.
      apply heap_authority_base_heap_cap_base in Hbase.
      rewrite /is_heap_cap Hbase in Hadv_nonheap. discriminate. }
    iAssert (interp Wshare C (WSealed ot_switcher C_f))
      as "#Hinterp_adv_share".
    { destruct (get_tag (WSealed ot_switcher C_f)) eqn:Htag;
        last by iApply interp_untagged.
      iApply (interp_monotone_sd_retained W_init_C Wshare C
        ot_switcher C_f with "Hadv");
        [exact Hwf_share|exact Hrelated_init_share|exact Htag|].
      apply filter_heap_nonheap. exact Hsealed_base. }
    iDestruct (StackRevokedResources_mono_priv W_init_C Wshare C
      stk_frame_addrs Hrelated_init_share with "Hstack_revoked_W0")
      as "Hstack_revoked_share".
    assert (b ∉ stk_frame_addrs) as Hb_not_stack.
    { rewrite /disjoint_from_heap elem_of_disjoint in Hstk_heap.
      intros Hb_stk. eapply (Hstk_heap b Hb_stk).
      apply elem_of_finz_seq_between.
      apply withinBounds_true_iff in Hb_heap. exact Hb_heap. }
    assert (revoked_addresses Wshare stk_frame_addrs)
      as Hstack_revoked_share.
    { rewrite /revoked_addresses Forall_forall. intros a Ha.
      subst Wshare Wbuf. rewrite lookup_insert_ne.
      - cbn. rewrite /revoked_addresses Forall_forall in Hstack_revoked_W0.
        apply Hstack_revoked_W0. exact Ha.
      - intros ->. exact (Hb_not_stack Ha). }

    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["Hca2";"Hca3";"Hca4";"Hca5"].
    iDestruct "Hca2" as "[Hca2 %Hca2]".
    iDestruct "Hca3" as "[Hca3 %Hca3]".
    iDestruct "Hca4" as "[Hca4 %Hca4]".
    iDestruct "Hca5" as "[Hca5 %Hca5]".
    subst wca2 wca3 wca4 wca5.
    set (adv_arg := ({[ca0 := hts_buffer b; ca1 := WInt 0;
      ca2 := WInt 0; ca3 := WInt 0; ca4 := WInt 0;
      ca5 := WInt 0; ct0 := WInt 0]} : Reg)).
    iAssert ([∗ map] rarg↦warg ∈ adv_arg,
      rarg ↦ᵣ warg ∗ if decide (rarg ∈ dom_arg_rmap 1)
        then interp Wshare C warg else True)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hadv_arg".
    { subst adv_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct2].
    set (adv_other := <[ct2:=WInt 0]>
      (<[ctp:=WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap_ret)))))))).
    iApply (switcher_cc_specification Nswitcher Wshare C
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_advcall ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b C_f
      (region_addrs_zeroes csp_b csp_e)
      adv_arg adv_other cstk Ws Cs 1
      with "[- $Halloc $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp
        $Hct1 $Hentry $Hcs0 $Hcs1 $Hadv_arg $Hrmap $Hstk
        $Hworld $Hstack_revoked_share $Hcstk $HK $Hinterp_adv_share]").
    { exact Hstk_shadow. }
    { exact Hstk_heap. }
    { subst adv_other. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap_ret /dom_arg_rmap /=. set_solver+. }
    { subst adv_arg. rewrite /is_arg_rmap /dom_arg_rmap /=. reflexivity. }
    iSplitR; first (iPureIntro; exact Hstack_revoked_share).
    iNext.
    (* First unknown-call return: the switcher gives a public future Wret and
       revokes its temporaries. Keep Hp and Hsaved outside the call frame;
       the adversary may quarantine b, so Hrel_b alone cannot supply Hb. *)
    iIntros (Wret rmap_after stk_after lret rcgp rcra rcs0 rcs1)
      "(%Hlret_unk & Hrevoked_lret & %Hrevoked_lret
       & %Hrelated_share_ext_ret & Hrel_stk_ret & %Hdom_rmap_after
       & Hstack_revoked_ret & %Hstack_revoked_ret
       & Hna & %Hcsp_bounds_ret & Hworld & Hcstk
       & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
       & [%warg0 [Hca0 _]] & [%warg1 [Hca1 _]]
       & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hgp_ret & Hra_ret & Hs0_ret & Hs1_ret).
    apply load_heap_nonheap in Hgp_ret.
    2: { destruct Hcgp_heap as [Hcgp_nonheap _].
         rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hcgp_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hra_ret.
    2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hpc_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hs0_ret; [|exact Hcs0_nonheap].
    apply load_heap_nonheap in Hs1_ret; [|exact Hcs1_nonheap].
    subst rcgp rcra rcs0 rcs1.
    iEval (cbn) in "HPC".

    (* Block 9: reload the saved buffer, allowing the heap load to clear its
       tag when the adversary has quarantined it. *)
    focus_block 9 "Hcode" as a_reload Ha_reload "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    rewrite world_interp_eq /world_interp_def.
    iDestruct "Hworld" as "(Hregion & Hsts & Hseals)".
    (* Load ca0 cgp 1. *)
    iApply (load_read_retained_imm (revoke Wret) C pc_b pc_e a_reload
      cgp_b cgp_e (cgp_b ^+ 1)%a (hts_buffer b) _ 1
      with "[- $Halloc $HPC $Hcgp $Hca0 $Hsaved $Hblock $Hregion]").
    { exact Hcgp_shadow. }
    { rewrite /hts_buffer /is_heap_cap /heap_cap_base
        /memory_cap_base /= Hb_heap. reflexivity. }
    { rewrite /hts_main_data in Hcgp_contiguous. solve_addr. }
    { apply withinBounds_true_iff.
      rewrite /hts_main_data in Hcgp_contiguous. solve_addr. }
    { solve_addr. }
    iNext. iIntros (actual Hloaded)
      "(HPC & Hcgp & Hca0 & Hsaved & Hblock & Hregion)".
    iAssert (world_interp (revoke Wret) C) with "[Hregion Hsts Hseals]"
      as "Hworld".
    { rewrite world_interp_eq /world_interp_def. iFrame. }
    destruct Hloaded as [Hloaded Hfilter].
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    (* Block 10: check the tag of the reloaded buffer. *)
    destruct Hloaded as [Hsame|Hcleared].
    2: { destruct Hcleared as [_ Hclear]. subst actual.
      focus_block 10 "Hcode" as a_check Ha_check "Hblock" "Hcont";
        iHide "Hcont" as hcont.
      iExtractList "Hrmap" [ct0] as ["[Hct0 %Hwct0_after]"].
      iApply (hts_check_quarantined_buffer_spec pc_b pc_e a_check
        b (b ^+ 1)%a b _ with "[- $HPC $Hca0 $Hct0 $Hblock $Hna]").
      { solve_addr. } }
    subst actual.
    (* The retained tagged load proves that the adversary left b live.
       Open its world entry and keep it open through the store and free. *)
    rewrite world_interp_eq /world_interp_def.
    iDestruct "Hworld" as "(Hregion & Hsts & Hseals)".
    iDestruct (sts_full_world_heap_wf with "Hsts") as %Hwf_ret.
    iAssert (world_interp (revoke Wret) C) with "[Hregion Hsts Hseals]"
      as "Hworld".
    { rewrite world_interp_eq /world_interp_def. iFrame. }
    rewrite revoke_heap in Hwf_ret.
    assert (heap_lookup_addr (heap_std Wshare) b =
      Some (b, MkAllocObject b (b ^+ 1)%a AllocObjectLive)) as Hlookup_share.
    { subst Wshare Wbuf. rewrite /heap_std_update /=.
      pose proof (heap_allocate_wf ∅ b (b ^+ 1)%a heap_wf_empty Hfresh_buf)
        as Hwf_buf.
      rewrite (heap_lookup_addr_complete (heap_allocate ∅ b (b ^+ 1)%a)
        b b (MkAllocObject b (b ^+ 1)%a AllocObjectLive) Hwf_buf).
      - reflexivity.
      - rewrite /heap_allocate lookup_insert.
        case_decide; [reflexivity|congruence].
      - unfold alloc_object_contains; cbn.
        split; [clear -Hbounds; solve_addr|exact (proj1 (proj2 (proj1 Hbounds)))]. }
    assert (related_sts_heap_std (heap_std Wshare) (heap_std Wret))
      as Hheap_future.
    { rewrite -(std_update_multiple_heap Wshare
        (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary).
      exact (proj2 (proj2 (proj2 Hrelated_share_ext_ret))). }
    destruct (heap_lookup_addr_future (heap_std Wshare) (heap_std Wret)
      b b (MkAllocObject b (b ^+ 1)%a AllocObjectLive)
      Hwf_ret Hheap_future Hlookup_share)
      as (obj_ret & Hlookup_ret & Hobj_future).
    assert (heap_lookup_addr (heap_std (revoke Wret)) b =
      Some (b,obj_ret)) as Hlookup_rev
      by (rewrite revoke_heap; exact Hlookup_ret).
    assert (heap_authority_base (hts_buffer b) = Some b) as Hauth_buf.
    { rewrite /hts_buffer /heap_authority_base.
      case_decide.
      - rewrite /heap_cap_base /memory_cap_base /= Hb_heap. reflexivity.
      - solve_addr. }
    assert (alloc_object_status obj_ret = AllocObjectLive) as Hlive_ret.
    { destruct (alloc_object_status obj_ret) eqn:Hstatus;
        first reflexivity.
      exfalso.
      pose proof (filter_heap_quarantined (revoke Wret)
        (hts_buffer b) b b obj_ret Hauth_buf Hlookup_rev Hstatus) as Hqu.
      rewrite Hqu in Hfilter.
      apply (f_equal get_tag) in Hfilter.
      rewrite /hts_buffer /= in Hfilter. discriminate. }
    assert (b ∉ finz.seq_between (csp_b ^+ 4)%a csp_e) as Hb_not_callstk.
    { intros Hin. apply Hb_not_stack.
      apply elem_of_finz_seq_between in Hin.
      apply elem_of_finz_seq_between. solve_addr. }
    assert (std Wshare !! b = Some Permanent) as Hstd_share.
    { rewrite /Wshare lookup_insert.
      case_decide; [reflexivity|congruence]. }
    assert (std (std_update_multiple Wshare
      (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) !! b =
      Some Permanent) as Hstd_source.
    { rewrite std_sta_update_multiple_lookup_same_i;
        [exact Hstd_share|exact Hb_not_callstk]. }
    assert (b ∈ dom (std (std_update_multiple Wshare
      (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary))) as Hb_dom_source.
    { rewrite elem_of_dom. eexists. exact Hstd_source. }
    assert (b ∈ dom (std Wret)) as Hb_dom_ret.
    { apply (proj1 (proj1 Hrelated_share_ext_ret)).
      exact Hb_dom_source. }
    rewrite elem_of_dom in Hb_dom_ret.
    destruct Hb_dom_ret as [ρ Hρ].
    pose proof (proj2 (proj1 Hrelated_share_ext_ret)
      b Permanent ρ Hstd_source Hρ) as Hrtc.
    assert (ρ = Permanent) as Hperm
      by (eapply std_rel_pub_rtc_Permanent; eauto).
    subst ρ.
    assert (std (revoke Wret) !! b = Some Permanent) as Hstd_rev.
    { apply revoke_lookup_Perm. exact Hρ. }
    iDestruct (open_world_interp_live_heap (revoke Wret) C b RW
      interp_in_memC Permanent b obj_ret Hb_heap Hlookup_rev Hlive_ret
      (or_intror eq_refl) Hstd_rev with "Hrel_b Hworld")
      as "(Hworld_open & Hstate_b & Hres_b)".
    focus_block 10 "Hcode" as a_check Ha_check "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct0] as ["[Hct0 %Hwct0_after]"].
    iApply (hts_check_live_buffer_spec pc_b pc_e a_check
      b (b ^+ 1)%a b _ with "[- $HPC $Hca0 $Hct0 $Hblock]").
    { change (SubBounds pc_b pc_e a_check (a_check ^+ 3)%a).
      exact H0. }
    iNext. iIntros "(HPC & Hca0 & Hct0 & Hblock)".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    iDestruct "Hres_b" as (v_b) "Hres_b".
    iDestruct "Hres_b" as "(%Hp_nonO & Hb_phys & #Hinterp_old & Hmono_b)".
    iApply "Hcontinue".
    rewrite /hts_phase11_pre.
    iExists b, a_reload, a_check, Wshare, Wret, obj_ret,
      wcs0, wcs1, warg1, v_b, rmap_after, stk_after, l, lret.
    iSplit; first (iPureIntro; exact Hbounds).
    iSplit; first (iPureIntro; exact Hsucc).
    iSplit; first (iPureIntro; change ((pc_a + length
      (concat (take 10 (encodeInstrsW <$> assembled_hts_main))))%a =
      Some a_check) in Ha_check; exact Ha_check).
    iSplit; first (iPureIntro; exact Hrelated_init_share).
    iSplit; first (iPureIntro; exact Hrelated_share_ext_ret).
    iSplit; first (iPureIntro; exact Hwf_ret).
    iSplit; first (iPureIntro; exact Hlookup_rev).
    iSplit; first (iPureIntro; exact Hobj_future).
    iSplit; first (iPureIntro; exact Hlive_ret).
    iSplit; first (iPureIntro; exact Hstd_rev).
    iSplit; first (iPureIntro; exact Hb_heap).
    iSplit; first (iPureIntro; exact Hdom_rmap_after).
    iSplit; first (iPureIntro; exact Hcs0_nonheap).
    iSplit; first (iPureIntro; exact Hcs1_nonheap).
    iSplit; first (iPureIntro; exact Hstk_shadow).
    iSplit; first (iPureIntro; exact Hstk_heap).
    iSplit; first (iPureIntro; exact Hstack_revoked_W0).
    iSplit; first (iPureIntro; exact Hexport_shadow).
    iSplit; first (iPureIntro; exact Hstack_revoked_ret).
    iSplit; first (iPureIntro; exact Hrevoked_lret).
    iFrame "∗#".
  Qed.
End Heap_Temporal_Safety_Blocks.
