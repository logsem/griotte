From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl register_tactics.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_base.
From griotte Require Import
  error_handling_spec_states error_handling_spec_read_blocks error_handling_spec_handler
  error_handling_spec_read.

(** * The entry [stats_read] for an unknown caller

    The export of [stats_read] satisfies [ot_switcher_prop]: for any
    pointer that is safe ([interp]), [stats_read] returns a safe word.
    - When the load succeeds, the pointer is a valid capability of the
      caller's world, and the loaded word is safe.
    - When it faults, [stats_read_fault_safe] closes the fault through the
      handler of [stats], which resumes it with [EINVAL]. The stack of the
      callee, revoked by the entry, holds the slot of the [ErrorState]. The
      return happens at count 2.
    In both cases, the return goes through [switcher_ret_specification]. *)

Section Error_Handling_Read_Safe.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {statslayout : statsLayout} {statslayoutwf : statsLayoutWf}
  .

  (** The load of [stats_read] through a safe pointer: it faults, or it
      loads a safe word. *)
  Lemma stats_read_load_interp_spec (W : WORLD) (C : CmptName) (wptr : LWord) :
    PC ↦ₚ stats_pcc stats_load_addr ∗
    ca0 ↦ᵣ wptr ∗
    interp W C wptr ∗
    world_interp W C ∗
    codefrag_pers STATS_pcc_b stats_code ∗
    ( (ca0 ↦ᵣ wptr -∗
       world_interp W C -∗
       trap_safe (stats_pcc stats_load_addr) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I) ∧
      ▷ (∀ wload,
           PC ↦ₚ stats_pcc stats_release_addr -∗
           ca0 ↦ᵣ wload -∗
           interp W C wload -∗
           world_interp W C -∗
           WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hca0 & #Hinterp & Hworld & Hcode_stats & Hcont)".
    pose proof stats_code_bounds_layout as (HsubBounds & Hpc_shadow & Hpc_nonheap).
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.
    rewrite /stats_pcc /stats_load_addr /stats_release_addr.
    (* Block 2: the load *)
    focus_block (stats_block ".Lread_load") "Hcode_stats" of stats_blocks at STATS_pcc_b
      as a_load Ha_load "Hcode" "Hcont_code".
    (* CLoad ca0 ca0 0 *)
    iInstrApply "Hcode" (wp_load_interp_same _ W C ca0)
      with "[$HPC $Hca0 $Hinterp $Hworld]"
      as (retv) "[(-> & HPC & Hca0 & Hworld) | (%wload & -> & HPC & Hca0 & #Hwload & Hworld)]".
    - iDestruct "Hcont" as "[Hfailed _]".
      iApply (wp_trap with "HPC").
      iApply ("Hfailed" with "Hca0 Hworld").
    - iDestruct "Hcont" as "[_ Hcont]".
      unfocus_block "Hcode" "Hcont_code" as "Hcode_stats".
      assert ((a_load ^+ 1)%a = (STATS_pcc_b ^+ stats_label ".Lread_release")%a) as ->
        by (offsets_compute; solve_addr).
      iApply ("Hcont" with "HPC Hca0 Hwload Hworld").
  Qed.

  (** The return of [stats_read] to an unknown caller, once the callee's
      stack is revoked: [switcher_ret_specification], with safe return
      values. *)
  Lemma stats_read_ret_logrel (W0 : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (rmap : LReg)
    (b_stk e_stk : Addr) (l : list LAddr) (stk_mem : list LWord) :
    frame_match Ws Cs cstk W0 C →
    csp_sync cstk b_stk e_stk →
    extract_temporaries_condition W0 (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) →
    (∀ r, is_Some (rmap !! r)) →
    rmap !!! csp = lword_of_word (WCap true RWL Local b_stk e_stk (stk_start_a b_stk e_stk)) →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    interp W0 C (rmap !!! ca0) -∗
    interp W0 C (rmap !!! ca1) -∗
    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
    registers_pointsto rmap -∗
    [[ b_stk , e_stk ]] ↦ₐ [[ stk_mem ]] -∗
    cstack_frag cstk -∗
    interp_continuation cstk Ws Cs -∗
    world_interp (revoke W0) C -∗
    RevokedResources W0 C l -∗
    na_own cerise_nais ⊤ -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hframe_match Hsync_csp Hl_unk Hfull Hcsp)
      "#Hinv_switcher #Hswitcher_static #Hinterp_ca0 #Hinterp_ca1 HPC Hregs Hstk Hcstk HK
       Hworld_C Hrevoked_l Hna".
    destruct Hl_unk as [Hnodup Htemps].
    set (Wfixed := close_list (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) (revoke W0)).
    assert (related_sts_pub_world W0 Wfixed) as Hrelated_pub_W0_Wfixed.
    { subst Wfixed. apply related_pub_revoke_close_list; exact Htemps. }
    iDestruct (RevokedResources_mono_pub W0 Wfixed C l l Hrelated_pub_W0_Wfixed
                with "Hrevoked_l") as "Hrevoked_l".
    iDestruct (registers_pointsto_ret_spec with "Hregs") as (rest) "(%Hdom_rest & Hcsp & Hca0 & Hca1 & Hrest)";
      first exact Hfull.
    iApply (switcher_ret_specification W0 (revoke W0) C rest e_stk b_stk l stk_mem
              cstk Ws Cs
             with "[$Hinv_switcher $Hswitcher_static $Hstk $Hcstk $HK $Hworld_C $Hna $HPC
                    $Hrevoked_l $Hrest $Hca0 $Hca1 $Hcsp]").
    { exact Hrelated_pub_W0_Wfixed. }
    { exact Hdom_rest. }
    { exact Hframe_match. }
    { exact Hsync_csp. }
    { exact Hnodup. }
    { intros a Ha; apply Htemps; done. }
    iSplit.
    - iApply (monotone.interp_monotone_same_heap W0 with "[] Hinterp_ca0"); done.
    - iApply (monotone.interp_monotone_same_heap W0 with "[] Hinterp_ca1"); done.
  Qed.

  (** The export of [stats_read] is safe: it satisfies [ot_switcher_prop]
      in any world, for any compartment. *)
  Lemma stats_read_entry_point_spec
    (g_tbl : Locality) (W : WORLD) (C : CmptName) :
    STATS_pcc_b ≠ b_switcher →
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv cerise_nais Nstats stats_inv
    -∗
    ot_switcher_prop W C
      (WCap true RO g_tbl b_stats_exp_tbl e_stats_exp_tbl stats_read_exp_tbl_addr).
  Proof.
    iIntros (Hswitcher)
      "(#Hinv_switcher & #Hswitcher_static & #Hstatic & #Hinv_stats)".
    iPoseProof "Hstatic" as "Hstatic'". iNamed "Hstatic'".
    pose proof stats_exp_tbl_size as Hstats_exp_tbl_size.
    rewrite /length_stats_exports_tbl /stats_nb_exports in Hstats_exp_tbl_size.
    iExists g_tbl, b_stats_exp_tbl, e_stats_exp_tbl, stats_read_exp_tbl_addr,
      STATS_pcc_b, STATS_pcc_e, STATS_cgp_b, STATS_cgp_e, stats_read_nargs,
      stats_read_min_stack, (Z.of_nat stats_read_pcc_off), InterruptDisabled,
      (Z.of_nat stats_handler_pcc_off), ExportTable_no_handler.
    iFrame "Htbl_pcc Htbl_cgp Htbl_eh Htbl_ehs Htbl_read".
    iSplit; first done.
    iSplit; first (iPureIntro; exact stats_exp_tbl_disjoint_from_shadow).
    iSplit.
    { iPureIntro. rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read.
      solve_addr. }
    iSplit.
    { iPureIntro. rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read.
      solve_addr. }
    iSplit.
    { iPureIntro. rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read.
      solve_addr. }
    iSplit; first (iPureIntro; rewrite /stats_read_nargs; lia).
    iSplit; first (iPureIntro; rewrite /stats_read_min_stack; lia).
    iSplit.
    { iPureIntro.
      pose proof STATS_size_imports as Hsize_imports.
      pose proof STATS_size_code as Hsize_code.
      rewrite stats_read_pcc_off_eq. cbn in Hsize_code. solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact stats_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff.
        rewrite /stats_read_exp_tbl_addr /stats_read_exp_tbl_off /stats_entry_read; solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact stats_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff; solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact stats_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff; solve_addr. }
    iSplit; first (iPureIntro; exact STATS_pcc_base_not_heap).
    iSplit; first (iPureIntro; exact STATS_cgp_base_not_heap).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %b_stk %e_stk".
    iIntros "(HK & %Hframe_match & %Htop_tbl & HPC & Hregister_state & Hrmap & Hworld_C &
      %Hsync_csp & %Hminstk & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hfull & %Hcgp & [%mie_ret %Hcra] & %Hcsp & #Hinterp_csp & #Hinterp_rmap & _)".
    set (cur := stk_start_a b_stk e_stk).
    destruct Htop_tbl as (Hframes & Htbl & Hcount & Htbl_ok).
    rewrite /stats_read_min_stack in Hminstk.
    set (wret :=
      WSentry (ret_kind mie_ret) true XSRW_ Local b_switcher e_switcher a_switcher_return).
    rewrite /interp_conf.
    destruct (Hfull ca0) as [wptr Hwptr].
    iAssert (interp W0 C wptr) as "#Hinterp_wptr".
    { iApply "Hinterp_rmap"; iPureIntro; last exact Hwptr.
      rewrite /stats_read_nargs /dom_arg_rmap /=. set_solver+. }
    (* The cell of the frame's table holds the table *)
    pose proof (tf_export_tbl_ok_nonzero _ Htbl_ok) as Htbl_set.

    (* Open [stats_inv], take the lock *)
    iApply (stats_read_take_open rmap with "Hinv_stats Hstatic HPC Hrmap Hna"); [done | done |].
    iNext. iIntros "HPC Hregs Hlock Hna Hclose".
    set (rtake := <[ct0:=lword_of_word (WInt 0)]> (rmap : LReg)).
    assert (∀ r, is_Some (rtake !! r)) as Hfull_take.
    { intros r. rewrite /rtake lookup_insert_is_Some'. by right. }
    assert (rtake !! cgp = Some stats_wcgp) as Hcgp_take.
    { by rewrite /rtake lookup_insert_ne. }
    assert (rtake !!! csp = lword_of_word (WCap true RWL Local b_stk e_stk cur)) as Hcsp_take.
    { rewrite /rtake lookup_total_alt. by simplify_map_eq. }
    assert (rtake !!! cra = lword_of_word wret) as Hcra_take.
    { rewrite /rtake lookup_total_alt. by simplify_map_eq. }
    assert (rtake !! ca0 = Some wptr) as Hca0_take.
    { by rewrite /rtake lookup_insert_ne. }
    clearbody rtake.
    iDestruct (registers_pointsto_extract _ ca0 with "Hregs") as "[Hca0 Hregs]"; first exact Hca0_take.
    (* The slot of the [ErrorState], below the cursor of the stack *)
    set (es := (cur ^+ (- ErrorState_size))%a).
    assert ((b_stk <= es)%a ∧ (es + 16)%a = Some cur ∧ (cur <= e_stk)%a) as
      (Hb_es & Hes_cur & Hcur_e).
    { rewrite /es /cur /stk_start_a /ErrorState_size /StackEntry_reserved_space in Hminstk |- *.
      split_and!; solve_addr. }
    iDestruct (interp_cap_regions with "Hinterp_csp") as %[Hcsp_mmio _]; first done.
    pose proof (disjoint_from_mmio_shadow _ _ Hcsp_mmio) as Hstk_shadow.

    (* The load *)
    iApply (stats_read_load_interp_spec with "[$HPC $Hca0 $Hinterp_wptr $Hworld_C $Hcode_stats
                                               Hregs Hlock Hna Hclose Hcstk HK]").
    iSplit.
    - (* The load faults: revoke the stack, lend the slot of the [ErrorState] *)
      iIntros "Hca0 Hworld_C".
      iDestruct ("Hregs" with "Hca0") as "Hregs".
      rewrite insert_id; last exact Hca0_take.
      iApply trap_safe_fupd. iSplitL; last by iIntros "!> %Hv".
      iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_C]")
        as (l) "(%Hl_unk & Hworld_C & _ & _ & >[%stk_mem Hstk] & Hrevoked_l & _)".
      iDestruct (big_sepL2_length with "Hstk") as %Hlen_stk.
      rewrite finz_seq_between_length in Hlen_stk.
      rewrite -(take_drop (Z.to_nat (es - b_stk)) stk_mem).
      iDestruct (region_pointsto_split b_stk e_stk es with "Hstk") as "[Hstk_lo Hstk]".
      { solve_addr. }
      { rewrite length_take /finz.dist. rewrite /finz.dist in Hlen_stk. solve_addr. }
      set (stk_hi := drop (Z.to_nat (es - b_stk)) stk_mem).
      rewrite -(take_drop (Z.to_nat ErrorState_size) stk_hi).
      iDestruct (region_pointsto_split es e_stk cur with "Hstk") as "[Hslot Hstk_hi]".
      { solve_addr. }
      { rewrite length_take /stk_hi length_drop /finz.dist.
        rewrite /finz.dist in Hlen_stk. rewrite /ErrorState_size. solve_addr. }
      iModIntro.
      iApply (stats_read_fault_safe cstk rtake Local b_stk e_stk cur
               with "Hinv_switcher Hswitcher_static Hstatic Hregs Hcstk Hna Hclose Hlock [Hslot]").
      1-3: done.
      { by apply lookup_total_correct. }
      { rewrite Hcra_take. apply jalr_target_ok_switcher_return_sentry. }
      { rewrite /ErrorState_size. solve_addr. }
      { done. }
      { apply (disjoint_from_shadow_weaken b_stk e_stk es cur); [done | done | exact Hstk_shadow]. }
      { done. }
      { done. }
      { exact Htbl_set. }
      { rewrite /error_state_area Hcsp_take /=. iExists _. iFrame "Hslot".
        iPureIntro. rewrite length_take /stk_hi length_drop /finz.dist.
        rewrite /finz.dist in Hlen_stk. rewrite /ErrorState_size. solve_addr. }
      (* The installed context released the lock: the return, at count 2 *)
      iNext. iIntros "HPC Hregs Harea Hcstk Hna".
      rewrite /error_state_area Hcsp_take /=.
      iDestruct "Harea" as (ws) "[%Hws Hslot]".
      iDestruct (region_pointsto_split es e_stk cur with "[$Hslot $Hstk_hi]") as "Hstk".
      { solve_addr. }
      { rewrite Hws /finz.dist /ErrorState_size. solve_addr. }
      iDestruct (region_pointsto_split b_stk e_stk es with "[$Hstk_lo $Hstk]") as "Hstk".
      { solve_addr. }
      { rewrite length_take /finz.dist. rewrite /finz.dist in Hlen_stk. solve_addr. }
      rewrite /stats_resumed_regs.
      set (M := <[ca1:=lword_of_word (WInt 0)]> (<[ca0:=lword_of_word (WInt EINVAL)]>
                  (<[cnull:=lword_of_word (WInt 0)]> rtake))).
      iEval (rewrite Hcra_take /=) in "HPC".
      iApply (stats_read_ret_logrel W0 C _ Ws Cs M b_stk e_stk l
               with "Hinv_switcher Hswitcher_static [] [] HPC Hregs Hstk Hcstk [HK] Hworld_C
                     Hrevoked_l Hna").
      { by apply frame_match_set_top_count. }
      { by rewrite csp_sync_set_top_count. }
      { exact Hl_unk. }
      { intros r. rewrite /M !lookup_insert_is_Some'. by right; right; right. }
      { rewrite /M -Hcsp_take !lookup_total_alt. by simplify_map_eq. }
      { rewrite /M lookup_total_alt. simplify_map_eq. iApply interp_int. }
      { rewrite /M lookup_total_alt. simplify_map_eq. iApply interp_int. }
      { by rewrite interp_cont_set_top_count. }
    - (* The load succeeds: revoke the stack, release, and return *)
      iNext. iIntros (wload) "HPC Hca0 #Hinterp_wload Hworld_C".
      iDestruct ("Hregs" with "Hca0") as "Hregs".
      iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_C]")
        as (l) "(%Hl_unk & Hworld_C & _ & _ & Hstk & Hrevoked_l & _)".
      iApply (stats_read_release_close with "Hstatic HPC Hregs Hlock Hna Hclose").
      { intros r. rewrite lookup_insert_is_Some'. by right. }
      { by rewrite lookup_insert_ne. }
      { rewrite lookup_total_insert_ne // Hcra_take. apply jalr_target_ok_switcher_return_sentry. }
      iNext. iIntros "HPC Hregs Hna".
      iDestruct "Hstk" as (stk_mem) "Hstk".
      set (M := <[ca1:=lword_of_word (WInt 0)]> (<[ca0:=wload]> rtake)).
      assert (<[ca0:=wload]> rtake !!! cra = lword_of_word wret) as Hret_cra.
      { rewrite -Hcra_take !lookup_total_alt. by simplify_map_eq. }
      iEval (rewrite Hret_cra /=) in "HPC".
      iApply (stats_read_ret_logrel W0 C cstk Ws Cs M b_stk e_stk l
               with "Hinv_switcher Hswitcher_static [] [] HPC Hregs Hstk Hcstk HK Hworld_C
                     Hrevoked_l Hna").
      { exact Hframe_match. }
      { exact Hsync_csp. }
      { exact Hl_unk. }
      { intros r. rewrite /M !lookup_insert_is_Some'. by right; right. }
      { rewrite /M -Hcsp_take !lookup_total_alt. by simplify_map_eq. }
      { rewrite /M lookup_total_alt. by simplify_map_eq. }
      { rewrite /M lookup_total_alt. simplify_map_eq. iApply interp_int. }
  Qed.

End Error_Handling_Read_Safe.
