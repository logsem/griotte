From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import switcher_preamble handoff switcher_link context_switch_layout.
From griotte Require Import context_switch_layout_instance common_context_install.
From griotte Require Import context_switching_support.

(** * The install at the context-switch thread

    The context-switch thread installs the context of the register save
    area of user thread [B], whose trusted stack is in mtdc, and resumes it
    with [mret]: the registers receive [B]'s saved words, MEPCC the PC to
    resume, and the thread hands [B]'s turn over ([ResumedV]). *)

Section ctx_install.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** A register map over all the registers, as the list of its words. *)
  #[local] Lemma regs_all_list (th : Thread) (lreg : LReg) :
    dom lreg = all_registers_s →
    regs[th] lreg ⊣⊢
    [∗ list] r ∈ cnull :: exception_spill_regs ++ [csp], r ↦ᵣ[th] default lnull (lreg !! r).
  Proof.
    intros Hdom.
    rewrite {1}(_ : lreg = list_to_map ((λ r, (r, default lnull (lreg !! r))) <$> all_registers)).
    - rewrite big_sepM_list_to_map; last first.
      { rewrite -list_fmap_compose. apply all_registers_NoDup. }
      rewrite big_sepL_fmap.
      by rewrite (big_opL_permutation _ all_registers (cnull :: exception_spill_regs ++ [csp]));
        last by apply (bool_decide_unpack _).
    - apply map_eq. intros r.
      assert (is_Some (lreg !! r)) as [w Hw].
      { apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
      rewrite Hw. symmetry. apply elem_of_list_to_map_1.
      { rewrite -list_fmap_compose. apply all_registers_NoDup. }
      apply list_elem_of_fmap. exists r. split; last apply all_registers_correct.
      by rewrite Hw.
  Qed.

  (** The resuming [mret] of the context-switch thread, as a triple. *)
  #[local] Lemma wp_mret_resume_ctx_triple E pc_p pc_g pc_b pc_e pc_a pc_π w (vepcc lpc' c : LWord)
      (z : Z) (q : InterruptStatus) dq p' b e a :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    lpc'.(lw) = vepcc.(lw) →
    (get_tag lpc'.(lw) = true → lpc'.(lprov) = None) →
    {{{ ▷ PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
        ▷ mtdc ↦ₜ[CtxSwitch] (Capₗ p' _ b e a) ∗
        ▷ handover_at (ceriseg := ceriseG_of CtxSwitch) vepcc c z q }}}
      Instr Executable @[CtxSwitch] E
    {{{ RET ResumedV;
        @PC_fragq Σ (@cerise_pcG Σ (ceriseG_of CtxSwitch)) (pc_dq q) lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        MIE ↦ₜ[CtxSwitch] q ∗
        mtdc ↦ₜ[CtxSwitch] (Capₗ p' _ b e a) ∗
        (if q is InterruptEnabled then True
         else handover_at (ceriseg := ceriseG_of CtxSwitch) vepcc c z InterruptEnabled) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hlw Hprov Φ) "(HPC & Hpc_a & HMIE & Hmtdc & Hho) HΦ".
    iApply (wp_mret_resume_ctx with "[$HPC $Hpc_a $HMIE $Hmtdc $Hho HΦ]"); try done.
    iNext. iIntros "HPC Hpc_a HMIE Hmtdc Hho". iApply "HΦ". iFrame.
  Qed.

  (** The install of user thread [B]'s context and the resuming [mret], at
      the context-switch thread, mtdc at [B]'s home: the registers receive
      [B]'s save area, MEPCC the resume PC, and the thread reaches
      [ResumedV]; [B]'s continuation receives its posture (when it resumes
      with interrupts disabled) and a credit. *)
  Lemma ctx_install_spec (B : nat) (g_tstk : Locality) (lreg : LReg) (wpc vepcc vc : LWord)
      (ws : list LWord) (v : resume_vals) (z : Z) (b : InterruptStatus) :
    mtdc_home_at (th := UserThread B) = tstack_home B →
    resume_ok_full ws v →
    dom lreg = all_registers_s →
    lreg !! csp = Some (lword_of_word (tstack_cap g_tstk B)) →
    lreg !! ct2 = Some wpc →
    legalise_pc wpc.(lw) = resume_pc_word ws →
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lcommon_context_install" ∗
    switcher_code_at CtxSwitch ∗
    regs[CtxSwitch] lreg ∗
    ⌜saved_mie_ok ws⌝ ∗
    save_area_holed (UserThread B) ws ∗
    mtdc_lent_at (th := UserThread B) ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    mtdc ↦ₜ[CtxSwitch] mtdc_home_at (th := UserThread B) ∗
    handover_at (ceriseg := ceriseG_of CtxSwitch) vepcc vc z b ∗
    cur_frag (Some (UserThread B, Resuming v)) ∗
    scheduler_state ∗
    na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
    close_Nact ∗
    ▷ ((if v.(rv_mie) is InterruptEnabled then True
        else posture_res_gen (ceriseg := ceriseG_of (UserThread B)) (th := UserThread B)
               None None None None) -∗
       £ 1 -∗
       safe[u B])
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hhome Hok Hdom Hcsp Hct2 Hpc)
      "(HPC & #Hswitcher & Hregs & %Hsaved & Hsave & Hlent & HMIE & Hmtdc & Hho & Hcur & Hsched
        & Hna & Hclose & Hcont)".
    pin_thread_instances CtxSwitch.
    destruct Hok as (Hregs_v & Hmie_v & Hpc_v & Hprov_v).
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread B))) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    assert (length ws = 21%nat) as Hlen21.
    { rewrite -Hlen. tstack_unfold. solve_addr. }
    clear Hlen.
    (* The registers, one by one; [cnull] holds [lnull] *)
    iEval (rewrite regs_all_list //) in "Hregs".
    iEval (cbn [big_opL exception_spill_regs app]) in "Hregs".
    iEval (rewrite Hcsp Hct2) in "Hregs".
    iDestruct "Hregs" as
      "(Hnull & Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hcsp & _)".
    iMod (cnull_lnull (ceriseg := ceriseG_of CtxSwitch) ⊤ with "Hnull") as "[Hnull %Hwnull]".
    iEval (rewrite /handover_at /volatile_csr_at) in "Hho".
    iDestruct "Hho" as "(Hcrit & HU & Hmepcc & Hmcause & Hmtval & Hmpie)".
    (* The install, up to the [mret], from [B]'s save area *)
    iPoseProof (codefrag_pers_thread_indep CtxSwitch (UserThread B) with "Hswitcher")
      as "#Hswitcher_B".
    iApply (common_context_reload_spec (th := CtxSwitch) (UserThread B) g_tstk wpc vepcc ws b
             with "[$HPC $Hcsp $Hcra $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                    $Hca3 $Hca4 $Hca5 $Hsave $HMIE $Hmepcc $Hmpie $Hswitcher_B
                    Hnull Hlent Hmtdc Hcrit HU Hmcause Hmtval Hcur Hsched Hna Hclose Hcont]");
      [done | done |].
    iNext. iIntros "(HPC & Hregs & Hsave & HMIE & Hmepcc & Hmpie & Hlc)".
    iClear "Hswitcher_B".
    iEval (rewrite Hhome /tstack_home) in "Hmtdc".
    rewrite -Hmie_v.
    switcher_open_label ".Lcommon_context_install" "Hswitcher" as "Hcode" pc_a Hpc_a.
    switcher_set_pc (pc_a ^+ 18%nat)%a.
    iAssert (handover_at (ceriseg := ceriseG_of CtxSwitch) (llegalise mepcc wpc) vc z v.(rv_mie))
      with "[Hcrit HU Hmepcc Hmcause Hmtval Hmpie]" as "Hho".
    { rewrite /handover_at /volatile_csr_at. iFrame. }
    (* Mret *)
    iInstrApply "Hcode"
      (wp_mret_resume_ctx_triple _ _ _ _ _ _ _ _ (llegalise mepcc wpc) v.(rv_pc) vc z v.(rv_mie))
      with "[$HPC $HMIE $Hmtdc $Hho]" as "(HPC & HMIE & Hmtdc & Hho)".
    { rewrite Hpc_v lw_llegalise. cbn [legalise]. by rewrite Hpc. }
    iClear "Hcode".
    (* [B] resumes *)
    iApply wp_value.
    rewrite HO_resumed. iSplit; first done.
    iAssert (regs[CtxSwitch] v.(rv_regs))%I with "[Hnull Hregs]" as "Hregs".
    { rewrite Hregs_v -regs_resume_regs_of //. rewrite Hwnull. iFrame. }
    iAssert (@posture_part Σ MP (ceriseG_of (UserThread B)) (UserThread B)
               (crit_link_full (UserThread B)) (crit_route_full (UserThread B)))
      with "[Hsave Hlent]" as "Hpart".
    { rewrite csl_full_posture_part. iFrame. iPureIntro. exact Hsaved. }
    iDestruct "Hsched" as (P) "[#Hsched_own HP]".
    iExists B, v.
    iFrame "Hcur Hregs HPC HMIE Hna Hclose".
    iSplitR.
    { iPureIntro. rewrite Hregs_v. apply resume_regs_of_dom. }
    iSplitL "Hmtdc".
    { rewrite Hhome /tstack_home. iFrame. }
    iAssert scheduler_state with "[HP]" as "Hsched".
    { iExists P. iFrame "Hsched_own". by iNext. }
    iFrame "Hsched".
    destruct (rv_mie v).
    - iFrame "Hpart". iNext. rewrite safe_unfold. iApply ("Hcont" with "[//] Hlc").
    - iSplitR; first done. iNext. rewrite safe_unfold. iApply ("Hcont" with "[Hpart Hho] Hlc").
      rewrite posture_res_gen_unfold. iFrame "Hpart".
      iExists (llegalise mepcc wpc), vc, z, InterruptEnabled.
      rewrite (handover_at_thread_indep (UserThread B) CtxSwitch).
      by iFrame "Hho".
  Qed.

End ctx_install.
