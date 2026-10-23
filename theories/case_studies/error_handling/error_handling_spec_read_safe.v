From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl register_tactics.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_preamble switcher_spec_return.
From griotte Require Import switcher_error_handler switcher_exception.
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

  (** A load whose result the opsem gives as a fault: the registers and the
      memory are unchanged. *)
  #[local] Ltac stats_load_fault :=
    iApply (wp_instr_faulted_1 with "[$HPC $Hsrc $Hi]"); [done | done | | ];
    [ intros ? ? ? ? s1 Hrr; rewrite /exec /= /lookup_reg Hrr /= decide_False //;
      destruct s1; cbn; try done
    | iIntros "!> (HPC & Hsrc & Hi)"; iApply "Hφ"; iLeft; by iFrame ].

  (** A load through a safe word into the register that holds it: it
      faults, or it loads a safe word ([wp_load_interp] for one register,
      with any fraction of the instruction). *)
  Lemma stats_wp_load_interp_same (E : coPset) (W : WORLD) (C : CmptName) (r : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (wi wsrc : LWord) (dq : dfrac) :
    decodeInstrW wi.(lw) = CLoad r r 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    {{{ interp W C wsrc ∗
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ wsrc ∗
        world_interp W C }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        ( ⌜retv = FaultedV⌝ ∗
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ wsrc ∗
          world_interp W C ) ∨
        ( ∃ wload,
          ⌜retv = NextIV⌝ ∗
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↦ₐ{dq} wi ∗
          r ↦ᵣ wload ∗ interp W C wload ∗
          world_interp W C ) }}}.
  Proof.
    iIntros (Hdecode Hcorrect_pc Hpca' Hr φ)
      "(#Hinterp_src & HPC & Hi & Hsrc & Hworld_interp) Hφ".
    destruct wsrc as [wsrc π].
    (* The load faults unless [wsrc] is a tagged capability that allows it *)
    destruct wsrc as [z | [ [] p g b e a | ] | | ];
      try (stats_load_fault; fail).
    destruct (readAllowed p) eqn:Hra;
      last (stats_load_fault; by rewrite addr_add_0 /= Hra).
    destruct (withinBounds b e a) eqn:Hwb;
      last (stats_load_fault; by rewrite addr_add_0 /= Hwb andb_false_r).
    apply withinBounds_true_iff in Hwb as Hbounds.
    (* Open the region of [a], as [wp_load_interp_imm] *)
    iDestruct (read_allowed_inv _ _ a with "Hinterp_src")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & Hmono)"; [solve_addr | auto |..].
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ a with "Hinterp_src")
      as %(ρ & Hρ & Hρ_not_revoked); [done | done |].
    iDestruct (interp_cap_addr_live _ _ _ _ _ _ _ a with "Hinterp_src") as %Hlive;
      [by eapply readAllowed_nonO | done |].
    iDestruct (open_world_interp W C (addr_key π a) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%w & WorldRes))";
      [exact Hlive | destruct ρ; auto; contradiction | exact Hρ |].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes ]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ a with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO | done |].
    iDestruct (world_interp_open_heap_provenance with "Hworld_interp") as "[Hworld_interp #Hprov]".
    iDestruct (heap_provenance_load_witness W w with "Hprov") as "Hwit".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm E pc_p pc_g pc_b pc_e pc_a None r r 0 wi
      (<[pc_a:=wi]> (<[a:=w]> ∅)) _ _ ∅ DfracDiscarded _ dw
      with "[$HPC $Hmem $Hshadow $Hmap $Hwit $Hdw]").
    { exact Hdecode. }
    { exact Hcorrect_pc. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite addr_add_0 in Haddr. injection Haddr as <-.
      rewrite Hnot_shadow.
      case_match; first done.
      eexists. by simplify_map_eq. }
    { by rewrite !dom_insert_L. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & Hdw & Hmap)".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc ->
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |Hfail -> ->].
    2,3: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite addr_add_0 in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { iDestruct (regs_of_map_1 with "Hmap") as "Hsrc".
         iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; auto.
         iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
         iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
         iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes")
           as "Hworld_interp"; eauto.
         { destruct ρ; auto; contradiction. }
         iApply "Hφ". iLeft. by iFrame. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
    rewrite addr_add_0 in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    pose proof (Hpers (W, C, w)) as Hpers_w.
    iDestruct "Hinterp" as "#HφV /=".
    iDestruct ("Hrcond" with "HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C w)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre filter_heap_load_word).
      iApply (interp_weakening_word_load W C p p' (filter_heap W w)); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre filter_heap_load_word) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hload_interp"; first exact Hpost.
    rewrite linsert_reg_not_cnull //.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpca' in Hapc. injection Hapc as <-.
    rewrite insert_insert_eq.
    iDestruct (regs_of_map_1 with "Hmap") as "Hsrc".
    iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; auto.
    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hrel WorldRes")
      as "Hworld_interp"; eauto.
    { destruct ρ; auto; contradiction. }
    iApply "Hφ"; iRight. iExists loadv'. iFrame "∗#%". done.
  Qed.

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
    iInstrApply "Hcode" (stats_wp_load_interp_same _ W C ca0)
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

  (** The registers of a full register map, as [switcher_ret_specification]
      takes them. *)
  Lemma stats_ret_regs (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    registers_pointsto rmap ⊢
    ∃ rest : LReg,
      ⌜dom rest = all_registers_s ∖ {[ csp ; ca0 ; ca1 ]}⌝ ∗
      csp ↦ᵣ (rmap !!! csp) ∗ ca0 ↦ᵣ (rmap !!! ca0) ∗ ca1 ↦ᵣ (rmap !!! ca1) ∗
      ([∗ map] r↦w ∈ rest, r ↦ᵣ w).
  Proof.
    iIntros (Hfull) "Hregs". rewrite /registers_pointsto.
    pose proof (lregmap_full_dom _ Hfull) as Hdom.
    iExists (delete ca1 (delete ca0 (delete csp rmap))).
    iSplit.
    { iPureIntro. rewrite !dom_delete_L Hdom. set_solver+. }
    iDestruct (big_sepM_delete _ _ csp with "Hregs") as "[Hcsp Hregs]".
    { apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hregs") as "[Hca0 Hregs]".
    { rewrite lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hregs") as "[Hca1 Hregs]".
    { rewrite !lookup_delete_ne //. apply lookup_lookup_total, Hfull. }
    iFrame.
  Qed.

  (** The return of [stats_read] to an unknown caller, once the callee's
      stack is revoked: [switcher_ret_specification], with safe return
      values. *)
  Lemma stats_read_ret_logrel (Nswitcher : namespace) (W0 : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (rmap : LReg)
    (a_stk e_stk : Addr) (l : list LAddr) (stk_mem : list LWord) :
    let a_stk4 := (a_stk ^+ 4)%a in
    Nswitcher ## N_trap →
    frame_match Ws Cs cstk W0 C →
    csp_sync cstk a_stk e_stk ∧ a_stk = (a_stk4 ^+ -4)%a →
    extract_temporaries_condition W0 (l ++ (LNonHeap <$> finz.seq_between a_stk4 e_stk)) →
    (∀ r, is_Some (rmap !! r)) →
    rmap !!! csp = lword_of_word (WCap true RWL Local a_stk4 e_stk a_stk4) →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    interp W0 C (rmap !!! ca0) -∗
    interp W0 C (rmap !!! ca1) -∗
    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
    registers_pointsto rmap -∗
    [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem ]] -∗
    cstack_frag cstk -∗
    interp_continuation cstk Ws Cs -∗
    world_interp (revoke W0) C -∗
    RevokedResources W0 C l -∗
    na_own cerise_nais ⊤ -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_stk4.
    iIntros (HNtrap Hframe_match Hsync_csp Hl_unk Hfull Hcsp)
      "#Hinv_switcher #Hswitcher_static #Hinterp_ca0 #Hinterp_ca1 HPC Hregs Hstk Hcstk HK
       Hworld_C Hrevoked_l Hna".
    destruct Hl_unk as [Hnodup Htemps].
    set (Wfixed := close_list (l ++ (LNonHeap <$> finz.seq_between a_stk4 e_stk)) (revoke W0)).
    assert (related_sts_pub_world W0 Wfixed) as Hrelated_pub_W0_Wfixed.
    { subst Wfixed. apply related_pub_revoke_close_list; exact Htemps. }
    iDestruct (RevokedResources_mono_pub W0 Wfixed C l l Hrelated_pub_W0_Wfixed
                with "Hrevoked_l") as "Hrevoked_l".
    iDestruct (stats_ret_regs with "Hregs") as (rest) "(%Hdom_rest & Hcsp & Hca0 & Hca1 & Hrest)";
      first exact Hfull.
    iApply (switcher_ret_specification Nswitcher W0 (revoke W0) C rest e_stk a_stk4 l stk_mem
              cstk Ws Cs
             with "[$Hinv_switcher $Hswitcher_static $Hstk $Hcstk $HK $Hworld_C $Hna $HPC
                    $Hrevoked_l $Hrest $Hca0 $Hca1 $Hcsp]").
    { exact Hrelated_pub_W0_Wfixed. }
    { exact Hdom_rest. }
    { exact Hframe_match. }
    { destruct Hsync_csp as [Hsync_csp Ha_stk]. by rewrite -Ha_stk. }
    { exact Hnodup. }
    { intros a Ha; apply Htemps; done. }
    { exact HNtrap. }
    iSplit.
    - iApply (monotone.interp_monotone_same_heap W0 with "[] Hinterp_ca0"); done.
    - iApply (monotone.interp_monotone_same_heap W0 with "[] Hinterp_ca1"); done.
  Qed.

  (** The export of [stats_read] is safe: it satisfies [ot_switcher_prop]
      in any world, for any compartment. *)
  Lemma stats_read_entry_point_spec
    (g_tbl : Locality) (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap →
    Nswitcher ## Nstats →
    STATS_pcc_b ≠ b_switcher →
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    stats_static ∗
    na_inv cerise_nais Nstats stats_inv
    -∗
    ot_switcher_prop W C
      (WCap true RO g_tbl b_stats_exp_tbl e_stats_exp_tbl stats_read_exp_tbl_addr).
  Proof.
    iIntros (HNtrap Hdisj_stats Hswitcher)
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
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %a_stk %e_stk".
    iIntros "(HK & %Hframe_match & %Htop_tbl & HPC & Hregister_state & Hrmap & Hworld_C &
      %Hsync_csp & %Hminstk & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hfull & %Hcgp & [%mie_ret %Hcra] & %Hcsp & #Hinterp_csp & #Hinterp_rmap & _)".
    set (a_stk4 := (a_stk ^+ 4)%a).
    destruct Htop_tbl as (Hframes & Htbl & Hcount & Htbl_ok).
    rewrite /stats_read_min_stack in Hminstk.
    set (wret := WSentry (ret_kind mie_ret) true XSRW_ Local b_switcher e_switcher a_switcher_return).
    rewrite /interp_conf.
    destruct (Hfull ca0) as [wptr Hwptr].
    iAssert (interp W0 C wptr) as "#Hinterp_wptr".
    { iApply "Hinterp_rmap"; iPureIntro; last exact Hwptr.
      rewrite /stats_read_nargs /dom_arg_rmap /=. set_solver+. }
    (* The cell of the frame's table holds the table *)
    assert ((top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)) as Htbl_set.
    { destruct Htbl_ok as [Hexp _]. intros Heq. rewrite Heq /exp_tbl_cap /= in Hexp. naive_solver. }

    (* Open [stats_inv], take the lock *)
    iApply (stats_read_take_open rmap with "Hinv_stats Hstatic HPC Hrmap Hna"); [done | done |].
    iNext. iIntros "HPC Hregs Hlock Hna Hclose".
    set (rtake := <[ct0:=lword_of_word (WInt 0)]> (rmap : LReg)).
    assert (∀ r, is_Some (rtake !! r)) as Hfull_take.
    { intros r. rewrite /rtake lookup_insert_is_Some'. by right. }
    assert (rtake !! cgp = Some stats_wcgp) as Hcgp_take.
    { by rewrite /rtake lookup_insert_ne. }
    assert (rtake !!! csp = lword_of_word (WCap true RWL Local a_stk4 e_stk a_stk4)) as Hcsp_take.
    { rewrite /rtake lookup_total_alt. by simplify_map_eq. }
    assert (rtake !!! cra = lword_of_word wret) as Hcra_take.
    { rewrite /rtake lookup_total_alt. by simplify_map_eq. }
    assert (rtake !! ca0 = Some wptr) as Hca0_take.
    { by rewrite /rtake lookup_insert_ne. }
    clearbody rtake.
    iDestruct (stats_regs_extract _ ca0 with "Hregs") as "[Hca0 Hregs]"; first exact Hca0_take.
    assert (a_stk4 + ErrorState_size <= e_stk)%Z as Hroom.
    { rewrite /ErrorState_size /a_stk4. lia. }
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
      rewrite -(take_drop (Z.to_nat ErrorState_size) stk_mem).
      iDestruct (region_pointsto_split a_stk4 e_stk (a_stk4 ^+ ErrorState_size)%a with "Hstk")
        as "[Hslot Hstk]".
      { rewrite /ErrorState_size in Hroom |- *; solve_addr. }
      { rewrite length_take /finz.dist. rewrite /finz.dist in Hlen_stk.
        rewrite /ErrorState_size in Hroom |- *. solve_addr. }
      iModIntro.
      iApply (stats_read_fault_safe Nswitcher cstk rtake Local a_stk4 e_stk a_stk4
               with "Hinv_switcher Hswitcher_static Hstatic Hregs Hcstk Hna Hclose Hlock [Hslot]").
      1-5: done.
      { by apply lookup_total_correct. }
      { rewrite Hcra_take. apply jalr_target_ok_switcher_return_sentry. }
      { solve_addr. }
      { exact Hroom. }
      { apply (stats_disjoint_from_shadow_sub a_stk4 e_stk); [solve_addr | | exact Hstk_shadow].
        rewrite /ErrorState_size in Hroom |- *; solve_addr. }
      { done. }
      { done. }
      { exact Htbl_set. }
      { rewrite /error_state_area Hcsp_take /=. iExists _. iFrame "Hslot".
        iPureIntro. rewrite length_take /finz.dist. rewrite /finz.dist in Hlen_stk.
        rewrite /ErrorState_size in Hroom |- *. solve_addr. }
      (* The installed context released the lock: the return, at count 2 *)
      iNext. iIntros "HPC Hregs Harea Hcstk Hna".
      rewrite /error_state_area Hcsp_take /=.
      iDestruct "Harea" as (ws) "[%Hws Hslot]".
      iDestruct (region_pointsto_split a_stk4 e_stk (a_stk4 ^+ ErrorState_size)%a
                   with "[$Hslot $Hstk]") as "Hstk".
      { rewrite /ErrorState_size in Hroom |- *; solve_addr. }
      { rewrite Hws /finz.dist. rewrite /ErrorState_size in Hroom |- *. solve_addr. }
      rewrite /stats_resumed_regs.
      set (M := <[ca1:=lword_of_word (WInt 0)]> (<[ca0:=lword_of_word (WInt EINVAL)]>
                  (<[cnull:=lword_of_word (WInt 0)]> rtake))).
      iEval (rewrite Hcra_take /=) in "HPC".
      iApply (stats_read_ret_logrel Nswitcher W0 C _ Ws Cs M a_stk e_stk l
               with "Hinv_switcher Hswitcher_static [] [] HPC Hregs Hstk Hcstk [HK] Hworld_C
                     Hrevoked_l Hna").
      { exact HNtrap. }
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
      iApply (stats_read_ret_logrel Nswitcher W0 C cstk Ws Cs M a_stk e_stk l
               with "Hinv_switcher Hswitcher_static [] [] HPC Hregs Hstk Hcstk HK Hworld_C
                     Hrevoked_l Hna").
      { exact HNtrap. }
      { exact Hframe_match. }
      { exact Hsync_csp. }
      { exact Hl_unk. }
      { intros r. rewrite /M !lookup_insert_is_Some'. by right; right. }
      { rewrite /M -Hcsp_take !lookup_total_alt. by simplify_map_eq. }
      { rewrite /M lookup_total_alt. by simplify_map_eq. }
      { rewrite /M lookup_total_alt. simplify_map_eq. iApply interp_int. }
  Qed.

End Error_Handling_Read_Safe.
