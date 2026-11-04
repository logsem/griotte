From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import logrel monotone wp_rules_interp.
From griotte Require Import switcher_preamble switcher_exception_states.
From griotte Require Import handoff pool switcher_link.
From griotte Require Import context_switch_layout_instance common_context_install.
From griotte Require Import context_switching_support context_switching_hyps.
From griotte Require Import context_switching_install.

(** * The resume path of the context-switch thread

    The return from the scheduler: the context-switch thread unseals the
    handle in [ca0] with the key of the trusted stacks, reads the slot of
    the thread whose trusted stack it holds, installs that trusted stack in
    mtdc, computes the PC to resume, and installs the thread's context. A
    handle that is not a trusted stack sealed with that key faults, mtdc
    still zero, to the trap vector. *)

Section ctx_resume.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    (C_sched : CmptName) (w_pcc w_cgp w_csp : LWord).

  (** The world part of the resume: at a public future [W] of the call's
      world [W0], the scheduler's stack valid at [W0] and the jump's
      premises at [W] give the scheduler's state. *)
  Lemma ctx_resume_world (W0 W : WORLD) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    related_sts_pub_world W0 W →
    frame_match Ws Cs cstk W C_sched →
    saved_prop_own γ_scheduler DfracDiscarded (scheduler_concrete C_sched w_csp) -∗
    interp (th := CtxSwitch) W0 C_sched w_csp -∗
    world_resources (th := CtxSwitch) W C_sched -∗
    shared_credit C_sched -∗
    ◯(CSTK)[CtxSwitch] cstk -∗
    interp_continuation (th := CtxSwitch) cstk Ws Cs -∗
    top_cmpt_untrusted (th := CtxSwitch) (interp (th := CtxSwitch)) W C_sched cstk -∗
    scheduler_state.
  Proof.
    iIntros (Hpub Hframe) "#Hsched #Hcsp Hworld Hcred Hcstk Hcont #Htop".
    iExists (scheduler_concrete C_sched w_csp). iFrame "Hsched".
    iApply bi.later_intro.
    iExists W, cstk, Ws, Cs. iFrame "Hworld Hcred Hcstk Hcont Htop".
    iSplit; first done.
    by iApply (interp_monotone W0 W).
  Qed.

  (** A valid word sealed, with its tag, by the trusted-stack otype holds
      the trusted stack of a thread below [swl_nthreads], with no
      identifier. The sealing invariant is taken at any thread: only its
      trusted-stack predicate, which is thread-free, is used. *)
  Lemma tstack_handle_unsealed (t : Thread) (W : WORLD) (C : CmptName) (sb : Sealable) π :
    get_tag_sealable sb = true →
    switcher_sealing_inv (th := t) -∗
    interp (th := CtxSwitch) W C (WSealed ot_trusted_stacks sb @@? π) -∗
    ◇ ⌜∃ (B : nat) (g : Locality),
         B < swl_nthreads ∧ π = None ∧
         sb = SCap true RWL g (@b_trusted_stack (tlayout_of (UserThread B)))
                (@e_trusted_stack (tlayout_of (UserThread B)))
                (@b_trusted_stack (tlayout_of (UserThread B)))⌝.
  Proof.
    iIntros (Htag) "#Hseal #Hw".
    iEval (rewrite /switcher_sealing_inv) in "Hseal". iNamed "Hseal".
    iEval (rewrite interp_unfold /= Htag /interp_sb) in "Hw".
    iDestruct "Hw" as "[(%κ & %P & #Hs & #Hok & #HP) _]".
    iDestruct (seal_pred_agree with "Hp_ot_tstacks Hs") as "[<- Heq]".
    iSpecialize ("Heq" $! (CtxSwitch, W, C, norm SealGlobal (WSealable sb @@? π))).
    iAssert (▷ tstack_handle_propC (CtxSwitch, W, C, norm SealGlobal (WSealable sb @@? π)))%I
      as "HP'".
    { iNext. by iRewrite "Heq". }
    iEval (rewrite /tstack_handle_propC /tstack_handle_prop /=) in "HP'".
    iMod "HP'" as %(B & HB & Heqw).
    iModIntro. iPureIntro.
    rewrite /lforce_global /lift_word /= in Heqw.
    destruct sb as [tg p g b e a | ]; simplify_eq/=.
    exists B, g. by rewrite /tlayout_of /=.
  Qed.

  (** From the return sentry's target to the unseal of [ca0] with the
      trusted-stack key. A handle sealed with that otype, with its tag,
      leaves the trusted stack in [csp]; any other word leaves [csp]
      untagged, and the next [clw] faults. *)
  Lemma ctx_resume_unseal_spec (wcsp wca0 : LWord) :
    PC ↦ₚ[CtxSwitch] ctx_resume_pc ∗
    switcher_code_at CtxSwitch ∗
    b_switcher ↦ₐ□ SealRange (true,true) Global ot_trusted_stacks (ot_trusted_stacks ^+ 1)
                     ot_trusted_stacks ∗
    csp ↦ᵣ[CtxSwitch] wcsp ∗
    ca0 ↦ᵣ[CtxSwitch] wca0 ∗
    ( ▷ ( ∀ (sb : Sealable) π,
          ⌜wca0 = WSealed ot_trusted_stacks sb @@? π⌝ ∗
          ⌜get_tag_sealable sb = true⌝ ∗
          PC ↦ₚ[CtxSwitch] switcher_pc (switcher_label_offset ".Lexception_scheduler_return" + 3) ∗
          csp ↦ᵣ[CtxSwitch] WSealable sb @@? π ∗
          ca0 ↦ᵣ[CtxSwitch] wca0 -∗
          safe[CtxSwitch] ) ∧
      ( ⌜¬ ∃ sb π, wca0 = WSealed ot_trusted_stacks sb @@? π ∧ get_tag_sealable sb = true⌝ ∗
        csp ↦ᵣ[CtxSwitch] - ∗
        ca0 ↦ᵣ[CtxSwitch] wca0 -∗
        trap_safe (switcher_pc (switcher_label_offset ".Lexception_scheduler_return" + 3)) ⊤
          (HO CtxSwitch) ) )
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros "(HPC & #Hswitcher & #Hkey & Hcsp & Hca0 & Hpost)".
    pin_thread_instances CtxSwitch.
    assert (a_sched_return =
            a_switcher_call ^+ switcher_label_offset ".Lexception_scheduler_return")%a as Hret.
    { pose proof a_sched_return_label as Hlbl. clear -Hlbl. offsets_compute. solve_addr. }
    iEval (rewrite /ctx_resume_pc Hret) in "HPC".
    switcher_open_label ".Lexception_scheduler_return" "Hswitcher" as "Hcode" a_ret Ha_ret.
    switcher_hide "Hpost" as hpost.
    (* Auipcc csp .sealing_key_trusted_stacks *)
    iInstr "Hcode".
    { instantiate (1 := b_switcher). switcher_addr_eq. }
    (* CLoad csp csp 0 *)
    iInstr "Hcode".
    { pose proof (switcher_data_not_shadow 0 ltac:(lia)) as Hs.
      by rewrite finz_add_0_default in Hs. }
    { done. }
    assert (∀ w : LWord, lload_word XSRW_ w = w) as Hload.
    { intros [w π]. rewrite /lload_word /lift_word /= load_word_no_dl_dro //. }
    iEval (rewrite Hload) in "Hcsp".
    (* UnSeal csp csp ca0 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown_sealed_dst_key (th := CtxSwitch) (CL := crit_link_full) _ _ _ _ _ _
              (a_ret ^+ 3) with "[$HPC $Hi $Hcsp $Hca0]"); try done; try solve_pure.
    { pose proof ot_trusted_stacks_size. solve_addr. }
    iIntros "!>" (ret)
      "[(-> & HPC & Hi & Hcsp & Hca0 & %Hnot_sealed) |
       [(%o & %wsb & %π & -> & HPC & Hi & Hcsp & Hca0 & %Hwca0 & %Htag & %Hrange)
       |(%o & %sb & %π & -> & HPC & Hi & Hcsp & Hca0 & %Hwca0 & %Hinvalid)] ]".
    { (* The handle is not sealed: [csp] loses its tag, and the next load
         faults *)
      wp_pure. iClear "Hi".
      iDestruct "Hpost" as "[_ Hfailed]".
      iDestruct (big_sepM_singleton (λ k y, k ↦ᵣ[CtxSwitch] y)%I csp with "Hcsp") as "Hmap".
      (* CLoad ct0 csp TrustedStack_offset_mcause *)
      iInstrApply "Hcode" (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (lclear_tag wca0))
        with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { by rewrite llookup_reg_not_cnull // lookup_singleton_eq. }
      iDestruct (big_sepM_singleton (λ k y, k ↦ᵣ[CtxSwitch] y)%I csp with "Hmap") as "Hcsp".
      switcher_set_pc
        (a_switcher_call ^+ (switcher_label_offset ".Lexception_scheduler_return" + 3))%a.
      iTrap with "Hfailed".
      iPureIntro. intros (sb & π & -> & _). done. }
    2: { (* The unsealed handle is not a valid trusted stack: the next load
            faults *)
      subst wca0. wp_pure. iClear "Hi".
      iDestruct "Hpost" as "[_ Hfailed]".
      iDestruct (big_sepM_singleton (λ k y, k ↦ᵣ[CtxSwitch] y)%I csp with "Hcsp") as "Hmap".
      (* CLoad ct0 csp TrustedStack_offset_mcause *)
      iInstrApply "Hcode"
        (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _
           (WSealable (clear_tag_sealable (unseal_sb Global sb)) @@? π))
        with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { by rewrite llookup_reg_not_cnull // lookup_singleton_eq. }
      iDestruct (big_sepM_singleton (λ k y, k ↦ᵣ[CtxSwitch] y)%I csp with "Hmap") as "Hcsp".
      switcher_set_pc
        (a_switcher_call ^+ (switcher_label_offset ".Lexception_scheduler_return" + 3))%a.
      iTrap with "Hfailed".
      iPureIntro. intros (sb' & π' & Heq & Htag'). simplify_eq.
      rewrite Htag' /= in Hinvalid.
      rewrite /withinBounds in Hinvalid. pose proof ot_trusted_stacks_size. solve_addr. }
    (* The trusted stack, unsealed *)
    subst wca0.
    apply withinBounds_le_addr in Hrange.
    assert (o = ot_trusted_stacks) as -> by (pose proof ot_trusted_stacks_size; solve_addr).
    iEval (rewrite unseal_global) in "Hcsp".
    wp_pure. iClear "Hi".
    iDestruct "Hpost" as "[Hpost _]".
    switcher_set_pc
      (a_switcher_call ^+ (switcher_label_offset ".Lexception_scheduler_return" + 3))%a.
    iApply "Hpost". iFrame "HPC Hcsp Hca0". done.
  Qed.

  (** From the [clw] of the saved mcause to the install, for the thread [B]
      whose trusted stack is in [csp]: the read step makes [B] Resuming, mtdc
      receives [B]'s trusted stack, and [ct2] the PC to resume, one word
      further after an [ecall]. *)
  Lemma ctx_resume_read_spec (ts : list nat) (B : nat) (g : Locality) (lreg : LReg) :
    NoDup ts →
    B ∈ ts →
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    mtdc_home_at (th := UserThread B) = tstack_home B →
    dom lreg = all_registers_s →
    lreg !! csp = Some (lword_of_word (tstack_cap g B)) →
    PC ↦ₚ[CtxSwitch] switcher_pc (switcher_label_offset ".Lexception_scheduler_return" + 3) ∗
    switcher_code_at CtxSwitch ∗
    inv Npool (Pool ts) ∗
    inv_CtxSwitch ∗
    regs[CtxSwitch] lreg ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    mtdc_lent_at (th := CtxSwitch) ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    handover_res (ceriseg := ceriseG_of CtxSwitch) ∗
    na_own (tpool CtxSwitch) ⊤ ∗
    ▷ ( ∀ (ws : list LWord) (v : resume_vals) (wpc : LWord) (lreg' : LReg),
        ⌜resume_ok_full ws v⌝ ∗
        ⌜dom lreg' = all_registers_s⌝ ∗
        ⌜lreg' !! csp = Some (lword_of_word (tstack_cap g B))⌝ ∗
        ⌜lreg' !! ct2 = Some wpc⌝ ∗
        ⌜legalise_pc wpc.(lw) = resume_pc_word ws⌝ ∗
        PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lcommon_context_install" ∗
        regs[CtxSwitch] lreg' ∗
        ⌜saved_mie_ok ws⌝ ∗
        save_area_holed (UserThread B) ws ∗
        mtdc_lent_at (th := UserThread B) ∗
        mtdc ↦ₜ[CtxSwitch] mtdc_home_at (th := UserThread B) ∗
        MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
        handover_res (ceriseg := ceriseG_of CtxSwitch) ∗
        cur_frag (Some (UserThread B, Resuming v)) ∗
        na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
        close_Nact ∗
        ▷ ((if v.(rv_mie) is InterruptEnabled then True
            else posture_res_gen (ceriseg := ceriseG_of (UserThread B)) (th := UserThread B)
                   None None None None) -∗
           £ 1 -∗
           safe[u B]) -∗
        safe[CtxSwitch] )
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hnd HB Hhome_ctx Hhome Hdom Hcsp)
      "(HPC & #Hswitcher & #Hpool & #Hact & Hregs & Hmtdc & Hlent & HMIE & Hho & Hna & Hpost)".
    pin_thread_instances CtxSwitch.
    (* The open pool token: [cur] is [None] *)
    iMod (na_inv_acc with "Hact Hna") as "(>Hcur & Hna & Hclose)"; [done | done |].
    (* The slot of [B]: [B] becomes Resuming *)
    iMod (pool_read ts B ⊤ Hnd HB with "Hpool Hcur")
      as (ws v) "(Hcur & %Hok & Hsa & HlentB & Hcont)"; first done.
    apply resume_ok_full_eq in Hok.
    iEval (rewrite save_area_at_full) in "Hsa".
    iDestruct "Hsa" as ">[%Hsaved Hsave]".
    iMod "HlentB".
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread B))) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    assert (length ws = 21%nat) as Hlen21.
    { rewrite -Hlen. tstack_unfold. solve_addr. }
    clear Hlen.
    iEval (rewrite handover_res_unfold) in "Hho".
    iDestruct "Hho" as (vepcc vc z b) "(Hcrit & HU & Hvol)".
    assert (∀ r, is_Some (lreg !! r)) as Hsome.
    { intros r. apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
    destruct (Hsome ct0) as [wct0 Hct0]. destruct (Hsome ct1) as [wct1 Hct1].
    destruct (Hsome ct2) as [wct2 Hct2].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ csp with "Hregs")
      as "[Hcsp Hregs]"; first exact Hcsp.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct0 with "Hregs")
      as "[Hct0 Hregs]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct1 with "Hregs")
      as "[Hct1 Hregs]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct2 with "Hregs")
      as "[Hct2 Hregs]"; first by simplify_map_eq.
    iDestruct (save_area_holed_cell (UserThread B) ws TrustedStack_offset_mcause with "Hsave")
      as "[Hs18 Hsave]"; [rewrite /TrustedStack_offset_mcause /TSTACK_REGFRAME_SZ; lia | done |].
    pose proof (tstack_save_cell_ok (th := UserThread B) TrustedStack_offset_mcause
                  ltac:(unfold TrustedStack_offset_mcause; lia))
      as (Hts_18 & Hts_18_bounds & Hts_18_shadow).
    iEval (rewrite /tstack_cap) in "Hcsp".
    switcher_open_label ".Lexception_scheduler_return" "Hswitcher" as "Hcode" a_ret Ha_ret.
    switcher_hide "Hpost" as hpost.
    switcher_set_pc (a_ret ^+ 3)%a.
    (* The saved words may be heap capabilities: they are loaded exactly *)
    iAssert (load_witness_res LoadPlain) as "Hwit"; first done.
    (* CLoad ct0 csp TrustedStack_offset_mcause *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ ct0 csp TrustedStack_offset_mcause)
      with "[$HPC $Hct0 $Hcsp $Hs18 $Hwit]" as (w18) "(%Hload & HPC & Hct0 & Hcsp & Hs18 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst w18.
    iDestruct ("Hsave" with "Hs18") as "Hsave".
    (* SpecialRW cnull mtdc (inr csp) *)
    iInstrApply "Hcode"
      (wp_writesr_mtdc_ctx_open _ _ _ _ _ _ _ _ _ _ _ (tstack_home B))
      with "[$HPC $Hcsp $Hmtdc $Hlent $HU]" as "(HPC & Hcsp & Hmtdc & HU)".
    { by exists g. }
    (* Mov ct1 11 *)
    iInstr "Hcode".
    (* The write of [iInstr] leaves the [cnull] case of the destination. *)
    destruct (decide (ct1 = cnull)) as [Hn|_]; first done.
    iDestruct (save_area_holed_cell (UserThread B) ws TrustedStack_offset_mepcc with "Hsave")
      as "[Hs0 Hsave]"; [rewrite /TrustedStack_offset_mepcc /TSTACK_REGFRAME_SZ; lia | done |].
    pose proof (tstack_save_cell_ok (th := UserThread B) TrustedStack_offset_mepcc
                  ltac:(unfold TrustedStack_offset_mepcc; lia))
      as (Hts_0 & Hts_0_bounds & Hts_0_shadow).
    assert ((@b_trusted_stack (tlayout_of (UserThread B)) ^+ TrustedStack_offset_mepcc)%a =
            @b_trusted_stack (tlayout_of (UserThread B))) as Hb0.
    { rewrite /TrustedStack_offset_mepcc. solve_addr. }
    rewrite Hb0 in Hts_0 Hts_0_bounds Hts_0_shadow.
    iEval (rewrite Hb0) in "Hs0 Hsave".
    (* CLoad ct2 csp TrustedStack_offset_mepcc *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ ct2 csp TrustedStack_offset_mepcc)
      with "[$HPC $Hct2 $Hcsp $Hs0 $Hwit]" as (w0) "(%Hload & HPC & Hct2 & Hcsp & Hs0 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst w0.
    iDestruct ("Hsave" with "Hs0") as "Hsave".
    pose proof (resume_pc_word_install ws Hlen21) as [Hecall Hother].
    (* The install, from either branch of the cause test *)
    iAssert (∀ wpc : LWord, ⌜legalise_pc wpc.(lw) = resume_pc_word ws⌝ -∗
             PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lcommon_context_install" -∗
             ct0 ↦ᵣ[CtxSwitch] save_area_word ws TrustedStack_offset_mcause -∗
             ct1 ↦ᵣ[CtxSwitch] lword_of_word (WInt 11) -∗
             ct2 ↦ᵣ[CtxSwitch] wpc -∗
             safe[CtxSwitch])%I
      with "[- HPC Hct0 Hct1 Hct2]" as "Hend".
    { iIntros (wpc Hwpc) "HPC Hct0 Hct1 Hct2".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct2 Hregs") as "Hregs".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct1 Hregs") as "Hregs".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct0 Hregs") as "Hregs".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcsp Hregs") as "Hregs".
      subst hpost.
      iApply ("Hpost" with "[-]").
      iFrame "HPC Hregs Hsave HlentB HMIE Hcur Hna Hclose".
      iSplit; first done.
      iSplit.
      { iPureIntro. rewrite !dom_insert_L !dom_delete_L Hdom.
        pose proof (all_registers_s_correct csp). pose proof (all_registers_s_correct ct0).
        pose proof (all_registers_s_correct ct1). pose proof (all_registers_s_correct ct2).
        set_solver. }
      iSplit; first by rewrite lookup_insert_eq.
      iSplit; first by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_ne //
                            lookup_insert_eq.
      iSplit; first done.
      iSplit; first done.
      iSplitL "Hmtdc"; first by rewrite Hhome.
      iSplitL "Hcrit HU Hvol".
      { iApply handover_res_intro. rewrite /handover_at. iFrame. }
      by iApply bi.later_intro. }
    destruct (decide (get_a (save_area_word ws TrustedStack_offset_mcause).(lw) =
                      MCAUSE_ECALL_MACHINE)) as [Hc | Hc].
    - (* After an ecall, the PC to resume is one word further *)
      (* Jne 2 ct0 ct1 *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hct0 $Hct1]"
        as "(HPC & Hct0 & Hct1)".
      { cbn [jcond_test]. rewrite Hc. reflexivity. }
      destruct (lea_result_is_Some (save_area_word ws TrustedStack_offset_mepcc) 1)
        as [wpc Hlea].
      (* Lea ct2 ct2 1 *)
      iInstrApply "Hcode" wp_lea_success_z_any with "[$HPC $Hct2]" as "(HPC & Hct2)".
      { exact Hlea. }
      switcher_change_pc_label ".Lcommon_context_install".
      iApply ("Hend" $! wpc with "[%] HPC Hct0 Hct1 Hct2").
      rewrite (lea_result_lw _ _ _ Hlea). by apply Hecall.
    - (* Jne 2 ct0 ct1 *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hct0 $Hct1]"
        as "(HPC & Hct0 & Hct1)".
      { cbn [jcond_test]. apply negb_true_iff, Z.eqb_neq. exact Hc. }
      switcher_change_pc_label ".Lcommon_context_install".
      iApply ("Hend" with "[%] HPC Hct0 Hct1 Hct2").
      by apply Hother.
  Qed.

  (** The return from the scheduler: from any state that the return
      sentry's target receives, in the public futures of the call's world
      where the scheduler's stack is valid, the context-switch thread
      resumes a thread of the pool or faults to the trap vector. *)
  Lemma ctx_resume_specs_hold (ts : list nat) :
    ts ≠ [] →
    ctx_switch_env C_sched w_pcc w_cgp w_csp ts -∗
    ctx_resume_specs C_sched w_csp.
  Proof.
    iIntros (Hne) "#Henv". iNamed "Henv".
    (* The switcher's code and keys, from the static part of any thread *)
    assert (∃ B0, B0 ∈ ts) as [B0 HB0].
    { destruct ts as [|B0 ts0]; first done. exists B0. apply list_elem_of_here. }
    iDestruct (big_sepL_elem_of with "Hstatic") as "Hstatic0"; first exact HB0.
    iEval (rewrite /switcher_static) in "Hstatic0". iNamed "Hstatic0".
    iPoseProof (codefrag_pers_thread_indep (UserThread B0) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher".
    iEval (rewrite /ctx_resume_specs). iIntros "!>" (W0) "#Hcsp0".
    iEval (rewrite /ctx_resume_spec). iIntros (W Hpub).
    iIntros (cstk Ws Cs regs)
      "(Hth & Huts & #Hreg & #Htop & HPC & Hregs & Hworld & Hcred & Hcont & Hna & Hcstk
        & %Hframe & %Hroute & HMIE & Hheld)".
    iEval (rewrite held_disabled) in "Hheld".
    iDestruct "Hheld" as "[Hho [Hmtdc Hlent] ]".
    iDestruct "Hreg" as "[%Hfull #Hregv]".
    assert (dom regs = all_registers_s) as Hdom.
    { apply set_eq. intros r. rewrite elem_of_dom. split; intros _;
        [apply all_registers_s_correct | apply Hfull]. }
    destruct (Hfull csp) as [wcsp Hcsp]. destruct (Hfull ca0) as [wca0 Hca0].
    iEval (rewrite /registers_pointsto) in "Hregs".
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ csp with "Hregs")
      as "[Hcsp Hregs]"; first exact Hcsp.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca0 with "Hregs")
      as "[Hca0 Hregs]"; first by simplify_map_eq.
    iApply (ctx_resume_unseal_spec wcsp wca0
             with "[- $HPC $Hswitcher $Htstacks_key $Hcsp $Hca0]").
    iSplit.
    - (* The handle is a trusted stack sealed with the key: it is [B]'s *)
      iNext. iIntros (sb π) "(%Hw & %Htag & HPC & Hcsp & Hca0)".
      iAssert (interp (th := CtxSwitch) W C_sched wca0) as "#Hwca0".
      { by iApply "Hregv". }
      subst wca0.
      iMod (tstack_handle_unsealed (UserThread B0) W C_sched sb π Htag
              with "Hswitcher_sealing Hwca0") as %(B & g & HB & -> & ->).
      assert (B ∈ ts) as HBin by (by apply Hts).
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca0 Hregs") as "Hregs".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcsp Hregs") as "Hregs".
      (* The scheduler's state, at the world of the return *)
      iDestruct (ctx_resume_world W0 W cstk Ws Cs Hpub Hframe
                  with "Hsched Hcsp0 Hworld Hcred Hcstk Hcont Htop") as "Hsched_st".
      iApply (ctx_resume_read_spec ts B g _ Hnd HBin Hhome_ctx (Hhomes B HBin)
               with "[- $HPC $Hswitcher $Hpool $Hact $Hregs $Hmtdc $Hlent $HMIE $Hho $Hna]").
      { rewrite !dom_insert_L !dom_delete_L Hdom.
        pose proof (all_registers_s_correct csp). pose proof (all_registers_s_correct ca0).
        set_solver. }
      { by rewrite lookup_insert_eq. }
      iNext. iIntros (ws v wpc lreg')
        "(%Hok & %Hdom' & %Hcsp' & %Hct2' & %Hwpc & HPC & Hregs & %Hsaved & Hsave & HlentB
          & Hmtdc & HMIE & Hho & Hcur & Hna & Hclose & Hcont)".
      iEval (rewrite handover_res_unfold) in "Hho".
      iDestruct "Hho" as (p c zz bb) "Hho".
      (* The [iNext] stripped the later inside the scheduler's state *)
      iAssert scheduler_state with "[Hsched_st]" as "Hsched_st".
      { iDestruct "Hsched_st" as (P) "[#Hsched_own HP]". iExists P. iFrame "Hsched_own".
        by iApply bi.later_intro. }
      iApply (ctx_install_spec B g lreg' wpc p c ws v zz bb (Hhomes B HBin) Hok Hdom' Hcsp'
                Hct2' Hwpc
               with "[$HPC $Hswitcher $Hregs $Hsave $HlentB $HMIE $Hmtdc $Hho $Hcur $Hsched_st
                      $Hna $Hclose $Hcont]").
      done.
    - (* Any other word: the [clw] faults, mtdc still zero, to the trap
         vector *)
      iIntros "(%Hnot & Hcsp & Hca0)".
      iDestruct "Hcsp" as (wcsp') "Hcsp".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca0 Hregs") as "Hregs".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcsp Hregs") as "Hregs".
      iApply (interp_trap_safe (th := CtxSwitch) _ cstk
                (<[csp := wcsp']> (<[ca0 := wca0]> (delete ca0 (delete csp regs))))
               with "Htrap").
      { intros r. destruct (decide (r = csp)) as [->|Hr1]; first by rewrite lookup_insert_eq.
        rewrite lookup_insert_ne //.
        destruct (decide (r = ca0)) as [->|Hr2]; first by rewrite lookup_insert_eq.
        rewrite lookup_insert_ne // !lookup_delete_ne //. }
      iModIntro. iFrame "Hregs Hna Hcstk". iSplitR; first by iRight.
      iExists InterruptDisabled. iFrame "HMIE". iSplitL; last done.
      rewrite held_disabled. iFrame.
  Qed.

End ctx_resume.
