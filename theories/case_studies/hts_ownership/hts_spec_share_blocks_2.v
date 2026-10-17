From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte.case_studies.hts_ownership Require Import hts_spec_states hts_spec_world.

(** * Segment (b): blocks 5-9

    Check the malloc result (halting on failure), save the buffer in the
    stack slot below the callee frames and initialize it (faulting on an
    empty stack), share the buffer in the world, and call [adv(buf)]. *)

Section HTS_Spec_Share.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (owner_a : Addr) (W_init_C : WORLD).
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (Nswitcher : namespace) (cstk : CSTK).

  #[local] Notation hts_ctx := (hts_main_ctx C C_f W_init_C Nswitcher).
  #[local] Notation malloc_ret := (hts_malloc_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs cstk).
  #[local] Notation adv1_ret := (hts_adv1_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs cstk).

  Lemma hts_spec_share :
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    not_heap_range cgp_b cgp_e ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    (pc_b + hts_label ".Lhts_main")%a = Some pc_a ->
    heap_std W_init_C = ∅ ->
    hts_ctx ∗
    malloc_ret ∗
    (adv1_ret -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_heap Hstk_shadow Hstk_heap
      HsubBounds Himports_contiguous Hheap_empty) "(#Hctx & Hret & Hcontinue)".
    iDestruct "Hctx" as "(#Hassert & #Hservice & #Hservice_static & #Hswitcher & #Hswitcher_static
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
       & #Hadv & #Hentry)".
    iDestruct "Hret" as "[Herr|Hok]".
    { (* Block 5: halt when malloc returned an integer. *)
      iDestruct "Herr" as (z) "(Hna & HPC & Hca0 & [%w Hct0] & Hcode_main)".
      codefrag_facts "Hcode_main". clear H0.
      unfold_code hts_main_code "Hcode_main".
      focus_block (hts_block ".Lhts_malloc_result") "Hcode_main" of hts_main_blocks at pc_a as a_result Ha_result "Hcode" "Hcont".
      (* GetTag ct0 ca0. *)
      iInstr "Hcode".
      (* Jnz 2 ct0. *)
      iInstr "Hcode".
      (* Halt. *)
      iInstr "Hcode".
      wp_end. iIntros (_). iFrame "Hna". }
    iDestruct "Hok" as (ι b) "(%Hbounds & Hframe & Hca0 & Hca1 & Hregs & Hstk
      & Hworld & #Hstack_revoked & %Hstack_revoked & HK & Howner & #Hobj
      & Hright & Hb)".
    iDestruct "Hb" as "[Hb Hb_share]".
    iDestruct "Hframe" as "(Hna & HPC & Hcra & Hcgp & Hcsp & [%wcs0 Hcs0]
      & [%wcs1 Hcs1] & Hcstk & Himports & Hcode_main & Hp & Howner_word)".
    iDestruct "Himports" as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himport_alloc_cap)".
    iDestruct "Hregs" as (rmap Hdom_rmap) "Hrmap".
    pose proof Hbounds as Hbnd; rewrite /hts_buffer_bounds in Hbnd.
    codefrag_facts "Hcode_main". clear H0.
    unfold_code hts_main_code "Hcode_main".
    iEval (rewrite /hts_buffer) in "Hca0".

    (* Block 5: the malloc result is tagged. *)
    focus_block (hts_block ".Lhts_malloc_result") "Hcode_main" of hts_main_blocks at pc_a as a_result Ha_result "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct0] as ["[Hct0 _]"].
    (* The share of the buffer cell is the dereference witness of [ι]. *)
    iDestruct (key_share_deref (Some ι) b with "Hb_share") as (dw Hdw) "[Hdw Hdw_close]".
    destruct dw as [|ι' q]; cbn in Hdw; [done|]. injection Hdw as <-.
    iSimpl in "Hdw".
    (* GetTag ct0 ca0. *)
    iInstr "Hcode".
    { eapply nonempty_exact_cond; [done|solve_addr]. }
    (* Jnz 2 ct0. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 6: save the buffer in the stack slot below the callee frames,
       and initialize it. *)
    focus_block (hts_block ".Lhts_share") "Hcode_main" of hts_main_blocks at pc_a as a_store Ha_store "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    destruct (decide (csp_b < csp_e)%a) as [Hstk_nonempty|Hstk_empty]; cycle 1.
    { (* Empty stack: the store to the stack slot faults. *)
      (* Store csp ca0 0. *)
      iInstrApply "Hcode" (wp_store_fail_reg_imm _ 0 RX Global pc_b pc_e a_store None None _ csp ca0
        RWL Local csp_b csp_e csp_b csp_b) with "[$HPC $Hca0 $Hcsp]" as "_".
      { solve_addr. }
      { destruct (withinBounds csp_b csp_e csp_b) eqn:Hwb; last done.
        apply withinBounds_true_iff in Hwb. solve_addr. }
      wp_end. by iIntros (?). }
    assert (region_addrs_zeroes csp_b csp_e =
      lword_of_word (WInt 0) :: region_addrs_zeroes (csp_b ^+ 1)%a csp_e) as Hzeroes.
    { rewrite (region_addrs_zeroes_split csp_b (csp_b ^+ 1)%a csp_e); last solve_addr.
      pose proof (proj1 (finz_incr_iff_dist csp_b (csp_b ^+ 1)%a 1)
        ltac:(solve_addr)) as [_ Hdist].
      rewrite /region_addrs_zeroes Hdist. reflexivity. }
    iEval (rewrite Hzeroes) in "Hstk".
    assert ((csp_b + 1)%a = Some (csp_b ^+ 1)%a) as Hcsp_succ by solve_addr.
    assert ((csp_b ^+ 1)%a <= csp_e)%a as Hcsp_le by solve_addr.
    iDestruct (region_pointsto_cons _ _ _ _ _ Hcsp_succ Hcsp_le with "Hstk")
      as "[Hslot Hstk]".
    (* Store csp ca0 0. *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in;
        [exact (disjoint_from_mmio_shadow _ _ Hstk_shadow)|rewrite /withinBounds; solve_addr]. }
    { apply withinBounds_true_iff; solve_addr. }
    (* Lea csp 1. *)
    iInstr "Hcode".
    (* Store ca0 0 0. *)
    iInstr "Hcode".
    { apply hts_heap_not_shadow. solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iDestruct ("Hdw_close" with "Hdw") as "Hb_share".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 7: fetch the switcher for the first adversary call. *)
    focus_block (hts_block ".Lhts_fetch_switcher_adv_1") "Hcode_main" of hts_main_blocks at pc_a as a_fetch7 Ha_fetch7 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp] as ["[Hctp _]"].
    iApply (fetch_spec 0 _ ctp RX Global
      pc_b pc_e a_fetch7
      (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ with "[- $HPC $Hctp $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply switcher_call_sentry_not_heap. }
    { done. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & _ & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 8: fetch the adversary entry. *)
    focus_block (hts_block ".Lhts_fetch_adv_1") "Hcode_main" of hts_main_blocks at pc_a as a_fetch8 Ha_fetch8 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["[Hct1 _]"].
    iApply (fetch_spec 2 _ ct1 RX Global
      pc_b pc_e a_fetch8 (WSealed ot_switcher C_f)
      _ _ _ with "[- $HPC $Hct1 $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { exact Hadv_nonheap. }
    { done. }
    iFrame "Himport_adv".
    iNext; iIntros "(HPC & Hct1 & _ & Himport_adv)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 9: call the adversary with the buffer. *)
    focus_block (hts_block ".Lhts_call_adv_1") "Hcode_main" of hts_main_blocks at pc_a as a_advcall Ha_advcall "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr_success "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_advcall ^+ 1)%a = (pc_a ^+ hts_label_offset ".Lhts_reload")%a) as Ha_next
      by (offsets_compute; solve_addr).
    rewrite Ha_next.
    clear Ha_result Ha_store Ha_fetch7 Ha_fetch8.

    (* Share the buffer in the world. *)
    rewrite (finz_seq_between_cons csp_b csp_e) in Hstack_revoked;
      last solve_addr.
    apply Forall_cons in Hstack_revoked as [_ Hstack_revoked].
    iEval (rewrite (finz_seq_between_cons csp_b csp_e); last solve_addr)
      in "Hstack_revoked".
    iEval (rewrite (StackRevokedResources_app _ _ [csp_b])) in "Hstack_revoked".
    iDestruct "Hstack_revoked" as "[_ Hstack_revoked_W0]".
    iAssert (b ↦ₕ[ι] WInt 0)%I with "[Hb Hb_share]" as "Hb"; first iFrame.
    iMod (hts_world_share_buffer C csp_b csp_e W_init_C _ ι b
      with "Hobj Hb Hworld Hstack_revoked_W0")
      as "(Hworld & #Hrel_b & #Hinterp_buf & Hstack_revoked_share
        & %Hstack_revoked_share)".
    { exact Hheap_empty. }
    { exact Hbounds. }
    { exact Hstk_heap. }
    { exact Hstack_revoked. }
    iDestruct (hts_interp_adv_world C C_f W_init_C (hts_Wshare W_init_C ι b)
      Hadv_nonheap with "Hadv") as "#Hinterp_adv_share".

    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %Hca2]";"[Hca3 %Hca3]";"[Hca4 %Hca4]";"[Hca5 %Hca5]"].
    subst wca2 wca3 wca4 wca5.
    set (adv_arg := ({[ca0 := hts_buffer b @@ ι; ca1 := lword_of_word (WInt 0);
      ca2 := lword_of_word (WInt 0); ca3 := lword_of_word (WInt 0);
      ca4 := lword_of_word (WInt 0); ca5 := lword_of_word (WInt 0);
      ct0 := lword_of_word (WInt 1)]} : LReg)).
    iAssert ([∗ map] rarg↦warg ∈ adv_arg,
      rarg ↦ᵣ warg ∗ if decide (rarg ∈ dom_arg_rmap 1)
        then interp (hts_Wshare W_init_C ι b) C warg else True)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hadv_arg".
    { subst adv_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp].
    set (adv_other :=
      <[ctp:=lword_of_word (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap))))))).
    iApply (switcher_cc_specification Nswitcher (hts_Wshare W_init_C ι b) C
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry (ret_kind InterruptDisabled) true RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_reload")%a)
      wcs0 wcs1 csp_b csp_e (csp_b ^+ 1)%a C_f
      (region_addrs_zeroes (csp_b ^+ 1)%a csp_e)
      adv_arg adv_other cstk Ws Cs 1
      with "[- $Hswitcher $Hswitcher_static $Hna $HPC $Hcgp $Hcra $Hcsp
        $Hct1 $Hentry $Hcs0 $Hcs1 $Hadv_arg $Hrmap $Hstk
        $Hworld $Hstack_revoked_share $Hcstk $HK $Hinterp_adv_share]").
    { exact Hstk_shadow. }
    { exact Hstk_heap. }
    { subst adv_other. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap /dom_arg_rmap /=. set_solver+. }
    { subst adv_arg. rewrite /is_arg_rmap /dom_arg_rmap /=. reflexivity. }
    iSplitR; first (iPureIntro; exact Hstack_revoked_share).
    iNext.
    iIntros (Wret rmap_after stk_after lret rcgp rcra rcs0 rcs1)
      "(_ & _ & _ & %Hrelated_share_ret & _ & %Hdom_rmap_after
       & Hstack_revoked_ret & %Hstack_revoked_ret
       & Hna & _ & Hworld & Hcstk
       & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
       & [%warg0 [Hca0 _]] & [%warg1 [Hca1 _]]
       & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hgp_ret & Hra_ret & _ & _).
    apply load_heap_nonheap in Hgp_ret.
    2: { destruct Hcgp_heap as [Hcgp_nonheap _].
         rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hcgp_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hra_ret.
    2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hpc_nonheap /=. reflexivity. }
    subst rcgp rcra.
    iEval (cbn) in "HPC".
    iApply "Hcontinue".
    iExists ι, b, Wret.
    iFrame "∗#%".
  Qed.
End HTS_Spec_Share.
