From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte Require Import hts_spec_states hts_spec_world.

(** * Segment (b): blocks 5-9

    Check the malloc result (halting on failure), save the buffer in the
    stack slot below the callee frames and initialize it (faulting on an
    empty stack), share the buffer in the world, and call [adv(buf)]. *)

Section HTS_Spec_Share.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (owner_a : Addr) (W_init_C : WORLD).
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (Nassert Nswitcher : namespace) (cstk : CSTK).

  Local Notation hts_ctx := (hts_main_ctx C C_f W_init_C Nassert Nswitcher).
  Local Notation malloc_ret := (hts_malloc_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs cstk).
  Local Notation adv1_ret := (hts_adv1_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs cstk).

  Lemma hts_spec_share :
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    not_heap_range cgp_b cgp_e ->
    disjoint_from_shadow csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    heap_std W_init_C = ∅ ->
    hts_ctx ∗
    malloc_ret ∗
    (adv1_ret -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_heap Hstk_shadow Hstk_heap
      HsubBounds Hheap_empty) "(#Hctx & Hret & Hcontinue)".
    iDestruct "Hctx" as "(#Hassert & #Halloc & #Hservice & #Hswitcher
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
       & #Hadv & #Hentry)".
    iDestruct "Hret" as (a_ret Ha_ret) "[Herr|Hok]".
    { (* Block 5: halt when malloc returned an integer. *)
      iDestruct "Herr" as (z) "(Hna & HPC & Hca0 & [%w Hct0] & Hcode)".
      codefrag_facts "Hcode". clear H0.
      iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
      iEval (cbv [fmap list_fmap concat]) in "Hcode".
      hts_focus_entry_block 5 "Hcode" as a_result Ha_result "Hblock" "Hcont"
        from Ha_ret.
      (* GetTag ct0 ca0. *)
      iInstr "Hblock".
      (* Jnz 2 ct0. *)
      iInstr "Hblock".
      (* Halt. *)
      iInstr "Hblock".
      wp_end. iIntros (_). iFrame "Hna". }
    iDestruct "Hok" as (b) "(%Hbounds & Hframe & Hca0 & Hca1 & Hregs & Hstk
      & Hworld & #Hstack_revoked & %Hstack_revoked & HK & Howner & Hright
      & #Hallocation & Hb)".
    iDestruct "Hframe" as "(Hna & HPC & Hcra & Hcgp & Hcsp & [%wcs0 Hcs0]
      & [%wcs1 Hcs1] & Hcstk & Himports & Hcode & Hp & Howner_word)".
    iDestruct "Himports" as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himport_alloc_cap)".
    iDestruct "Hregs" as (rmap Hdom_rmap) "Hrmap".
    pose proof Hbounds as Hbnd; rewrite /hts_buffer_bounds in Hbnd.
    codefrag_facts "Hcode". clear H0.
    iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
    iEval (cbv [fmap list_fmap concat]) in "Hcode".
    iEval (rewrite /hts_buffer) in "Hca0".

    (* Block 5: the malloc result is tagged. *)
    hts_focus_entry_block 5 "Hcode" as a_result Ha_result "Hblock" "Hcont"
      from Ha_ret.
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct0] as ["[Hct0 _]"].
    (* GetTag ct0 ca0. *)
    iInstr "Hblock".
    (* Jnz 2 ct0. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 6: save the buffer in the stack slot below the callee frames,
       and initialize it. *)
    focus_block 6 "Hcode" as a_store Ha_store "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    destruct (decide (csp_b < csp_e)%a) as [Hstk_nonempty|Hstk_empty]; cycle 1.
    { (* Empty stack: the store to the stack slot faults. *)
      iInstr_lookup "Hblock" as "Hi" "Hblock".
      wp_instr.
      iApply (wp_store_fail_reg_imm _ 0 RX Global pc_b pc_e a_store _ csp ca0
        RWL Local csp_b csp_e csp_b csp_b with "[$HPC $Hi $Hca0 $Hcsp]").
      { rewrite decode_encode_instrW_inv. reflexivity. }
      { solve_pure. }
      { solve_addr. }
      { destruct (withinBounds csp_b csp_e csp_b) eqn:Hwb; last done.
        apply withinBounds_true_iff in Hwb. solve_addr. }
      { done. }
      { done. }
      iNext. iIntros "_". wp_pure. wp_end. by iIntros (?). }
    assert (region_addrs_zeroes csp_b csp_e =
      WInt 0 :: region_addrs_zeroes (csp_b ^+ 1)%a csp_e) as Hzeroes.
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
    iInstr "Hblock".
    (* Lea csp 1. *)
    iInstr "Hblock".
    (* Store ca0 0 0. *)
    iInstr_success "Hblock".
    { apply hts_heap_not_shadow. solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 7: fetch the switcher for the first adversary call. *)
    focus_block 7 "Hcode" as a_fetch7 Ha_fetch7 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp;ct2] as ["[Hctp _]";"[Hct2 _]"].
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch7
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ _ with "[- $HPC $Hctp $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
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

    (* Block 8: fetch the adversary entry. *)
    focus_block 8 "Hcode" as a_fetch8 Ha_fetch8 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["[Hct1 _]"].
    iApply (fetch_spec hts_adv_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch8 (WSealed ot_switcher C_f)
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

    (* Block 9: call the adversary with the buffer. *)
    focus_block 9 "Hcode" as a_advcall Ha_advcall "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr_success "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    assert (hts_block_addr pc_a 10 (a_advcall ^+ 1)%a) as Ha_next.
    { rewrite /hts_block_addr. solve_addr. }
    clear Ha_result Ha_store Ha_fetch7 Ha_fetch8.

    (* Share the buffer in the world. *)
    rewrite (finz_seq_between_cons csp_b csp_e) in Hstack_revoked;
      last solve_addr.
    apply Forall_cons in Hstack_revoked as [_ Hstack_revoked].
    iEval (rewrite (finz_seq_between_cons csp_b csp_e); last solve_addr)
      in "Hstack_revoked".
    iEval (rewrite (StackRevokedResources_app _ _ [csp_b])) in "Hstack_revoked".
    iDestruct "Hstack_revoked" as "[_ Hstack_revoked_W0]".
    iMod (hts_world_share_buffer C csp_b csp_e W_init_C _ b
      with "Hallocation Hb Hworld Hstack_revoked_W0")
      as "(Hworld & #Hrel_b & #Hinterp_buf & Hstack_revoked_share
        & %Hstack_revoked_share)".
    { exact Hheap_empty. }
    { exact Hbounds. }
    { exact Hstk_heap. }
    { exact Hstack_revoked. }
    iDestruct (hts_interp_adv_world C C_f W_init_C (hts_Wshare W_init_C b)
      Hadv_nonheap with "Hadv") as "#Hinterp_adv_share".

    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %Hca2]";"[Hca3 %Hca3]";"[Hca4 %Hca4]";"[Hca5 %Hca5]"].
    subst wca2 wca3 wca4 wca5.
    set (adv_arg := ({[ca0 := hts_buffer b; ca1 := WInt 0;
      ca2 := WInt 0; ca3 := WInt 0; ca4 := WInt 0;
      ca5 := WInt 0; ct0 := WInt 0]} : Reg)).
    iAssert ([∗ map] rarg↦warg ∈ adv_arg,
      rarg ↦ᵣ warg ∗ if decide (rarg ∈ dom_arg_rmap 1)
        then interp (hts_Wshare W_init_C b) C warg else True)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hadv_arg".
    { subst adv_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct2].
    set (adv_other := <[ct2:=WInt 0]>
      (<[ctp:=WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap)))))))).
    iApply (switcher_cc_specification Nswitcher (hts_Wshare W_init_C b) C
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_advcall ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e (csp_b ^+ 1)%a C_f
      (region_addrs_zeroes (csp_b ^+ 1)%a csp_e)
      adv_arg adv_other cstk Ws Cs 1
      with "[- $Halloc $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp
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
    iExists b, (a_advcall ^+ 1)%a, Wret.
    iFrame "∗#%".
  Qed.
End HTS_Spec_Share.
