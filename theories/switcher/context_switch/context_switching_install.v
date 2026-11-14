From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import switcher_preamble handoff pool switcher_link context_switch_layout.
From griotte Require Import switcher_exception_states context_switch_layout_instance.
From griotte Require Import common_context_install.
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

  (** From [.Lcommon_context_install + 2] at the context-switch thread, the
      window of the high-water mark, for the save area [ws] of user thread
      [B], read with the values [v]: MSHWM receives [B]'s saved MSHWM, which
      opens the window at [B]'s MSHWMB, the lent set becomes [B]'s zone and
      the halves of the last owner [o], if there is one and it is not [B],
      go back to its slot; MSHWMB receives
      [B]'s saved MSHWMB, which closes the window. From the opening write on,
      the lent set is [B]'s zone and there is no last owner; nothing
      rebuilds [hwm_res_ctx] before the hand-back. *)
  Lemma ctx_install_window_spec (ts : list nat) (B : nat) (g_tstk : Locality) (ws : list LWord)
      (v : resume_vals) (wcra : LWord) (hbP hP : Z) (o : option (nat * gset Addr)) :
    NoDup ts →
    length ws = 21%nat →
    resume_ok_full ws v →
    zone_covers v.(rv_hwmb) v.(rv_hwm) v.(rv_zone) →
    (∀ zn, o = Some (B, zn) → zn = v.(rv_zone)) →
    PC ↦ₚ[CtxSwitch] switcher_pc (switcher_label_offset ".Lcommon_context_install" + 2) ∗
    switcher_code_at CtxSwitch ∗
    inv Npool (Pool ts) ∗
    csp ↦ᵣ[CtxSwitch] tstack_cap g_tstk B ∗
    cra ↦ᵣ[CtxSwitch] wcra ∗
    save_area_holed (UserThread B) ws ∗
    mshwmb ↦ₜ[CtxSwitch] hbP ∗
    mshwm ↦ₜ[CtxSwitch] hP ∗
    pend_frag[CtxSwitch] None ∗
    lent_frag[CtxSwitch] (last_owner_zone o) ∗
    ctx_last_owner_frag o ∗
    ▷ (if o is Some (B', _) then
         (if decide (B' = B) then True else zone_halves[CtxSwitch] v.(rv_zone))
       else zone_halves[CtxSwitch] v.(rv_zone)) ∗
    cur_frag (Some (UserThread B, Resuming v)) ∗
    ▷ ( PC ↦ₚ[CtxSwitch] switcher_pc (switcher_label_offset ".Lcommon_context_install" + 6) ∗
        csp ↦ᵣ[CtxSwitch] tstack_cap g_tstk B ∗
        cra ↦ᵣ[CtxSwitch] save_area_word ws TrustedStack_offset_mshwmb ∗
        save_area_holed (UserThread B) ws ∗
        mshwmb ↦ₜ[CtxSwitch] v.(rv_hwmb) ∗
        mshwm ↦ₜ[CtxSwitch] v.(rv_hwm) ∗
        pend_frag[CtxSwitch] None ∗
        lent_frag[CtxSwitch] v.(rv_zone) ∗
        ctx_last_owner_frag None ∗
        cur_frag (Some (UserThread B, Resuming v)) -∗
        safe[CtxSwitch] )
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hnd Hlen Hok Hcov Hlast_owner_B)
      "(HPC & #Hswitcher & #Hpool & Hcsp & Hcra & Hsave & Hhwmb & Hhwm & Hpend & Hlentf & Hlast_owner
        & Hhalves & Hcur & Hpost)".
    pin_thread_instances CtxSwitch.
    destruct Hok as (_ & _ & _ & Hhb_v & Hh_v).
    (* The halves to lend, and their return to the last owner *)
    iAssert (∃ swap : bool,
               ⌜swap = false → v.(rv_zone) = last_owner_zone o⌝ ∗
               ▷ (if swap then zone_halves[CtxSwitch] v.(rv_zone) else True) ∗
               ((if swap then zone_halves[CtxSwitch] (last_owner_zone o) else True) -∗
                ctx_last_owner_frag o -∗
                cur_frag (Some (UserThread B, Resuming v)) ={⊤}=∗
                ctx_last_owner_frag None ∗ cur_frag (Some (UserThread B, Resuming v))))%I
      with "[Hhalves]" as (swap) "(%Hswap & Hhalves & Hunlend)".
    { destruct o as [ [P zn] | ].
      - destruct (decide (P = B)) as [-> | HPB].
        + iExists false. iSplit.
          { iPureIntro. intros _. by rewrite (Hlast_owner_B zn eq_refl). }
          iSplitR; first done.
          iIntros "_ Hlast_owner Hcur".
          iMod (pool_unlend ts B v B zn ⊤ Hnd with "Hpool Hcur Hlast_owner []") as "[$ $]";
            [solve_ndisj | by rewrite decide_True |].
          done.
        + iExists true. iSplit; first (iPureIntro; discriminate).
          iFrame "Hhalves".
          iIntros "Hzn Hlast_owner Hcur".
          iMod (pool_unlend ts B v P zn ⊤ Hnd with "Hpool Hcur Hlast_owner [Hzn]") as "[$ $]";
            [solve_ndisj | by rewrite decide_False |].
          done.
      - iExists true. iSplit; first (iPureIntro; discriminate).
        iFrame "Hhalves". iIntros "_ $ $". done. }
    pose proof (tstack_save_cell_ok (th := UserThread B) TrustedStack_offset_mshwm
                  ltac:(unfold TrustedStack_offset_mshwm; lia))
      as (Hts_19 & Hts_19_bounds & Hts_19_shadow).
    pose proof (tstack_save_cell_ok (th := UserThread B) TrustedStack_offset_mshwmb
                  ltac:(unfold TrustedStack_offset_mshwmb; lia))
      as (Hts_20 & Hts_20_bounds & Hts_20_shadow).
    iDestruct (save_area_holed_cell (UserThread B) ws TrustedStack_offset_mshwm with "Hsave")
      as "[Hs19 Hsave]"; [rewrite /TrustedStack_offset_mshwm /TSTACK_REGFRAME_SZ; lia | done |].
    iEval (rewrite /tstack_cap) in "Hcsp".
    switcher_open_label ".Lcommon_context_install" "Hswitcher" as "Hcode" pc_a Hpc_a.
    switcher_hide "Hpost" as hpost.
    switcher_set_pc (pc_a ^+ 2%nat)%a.
    iAssert (load_witness_res LoadPlain) as "Hwit"; first done.
    (* CLoad cra csp 19 *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ cra csp TrustedStack_offset_mshwm)
      with "[$HPC $Hcra $Hcsp $Hs19 $Hwit]" as (w19) "(%Hload & HPC & Hcra & Hcsp & Hs19 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst w19.
    iDestruct ("Hsave" with "Hs19") as "Hsave".
    iDestruct (save_area_holed_cell (UserThread B) ws TrustedStack_offset_mshwmb with "Hsave")
      as "[Hs20 Hsave]"; [rewrite /TrustedStack_offset_mshwmb /TSTACK_REGFRAME_SZ; lia | done |].
    iPoseProof (codefrag_lookup_acc_pers _ _ 4 with "Hcode") as "Hi4".
    iPoseProof (codefrag_lookup_acc_pers _ _ 5 with "Hcode") as "Hi5".
    (* SpecialRW cnull mshwm (inr cra) *)
    iInstrApply "Hcode"
      (wp_csrw_mshwm_open _ _ _ _ _ _ _ (pc_a ^+ 4%nat)%a (pc_a ^+ 5%nat)%a _ _ _ _ _ _
         TrustedStack_offset_mshwmb _ hbP hP v.(rv_hwmb) (last_owner_zone o) v.(rv_zone) swap)
      with "[$HPC $Hcra $Hcsp $Hs20 $Hhwmb $Hhwm $Hpend $Hlentf $Hhalves $Hi4 $Hi5]"
      as "(HPC & Hcra & Hcsp & Hs20 & Hhwmb & Hhwm & Hpend & Hlentf & Hhalves)".
    1: done.
    1: solve_addr.
    1: (eexists _, _, _, _, _; split_and!; [reflexivity | done | exact Hts_20 | exact Hts_20_bounds]).
    1: { (* The trusted stack is outside the heap *)
         rewrite /heap_cap_base /=.
         assert (withinBounds (@b_trusted_stack (tlayout_of (UserThread B)))
                   (@e_trusted_stack (tlayout_of (UserThread B)))
                   (@b_trusted_stack (tlayout_of (UserThread B))) = true) as Hb.
         { clear -Hts_20 Hts_20_bounds. rewrite /TrustedStack_offset_mshwmb in Hts_20 Hts_20_bounds.
           apply withinBounds_true_iff in Hts_20_bounds.
           apply withinBounds_true_iff. solve_addr. }
         by rewrite (disjoint_from_heap_not_in _ _ _
                       (trusted_stack_disjoint_from_heap (tlayout := tlayout_of (UserThread B))) Hb). }
    1: by rewrite -Hh_v.
    (* The halves of the last owner go back to its slot *)
    iMod ("Hunlend" with "Hhalves Hlast_owner Hcur") as "[Hlast_owner Hcur]".
    (* CLoad cra csp 20 *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ cra csp TrustedStack_offset_mshwmb)
      with "[$HPC $Hcra $Hcsp $Hs20 $Hwit]" as (w20) "(%Hload & HPC & Hcra & Hcsp & Hs20 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst w20.
    iDestruct ("Hsave" with "Hs20") as "Hsave".
    (* SpecialRW cnull mshwmb (inr cra) *)
    iInstrApply "Hcode" (wp_csrw_mshwmb_close _ _ _ _ _ _ _ _ _ _ hbP v.(rv_hwmb))
      with "[$HPC $Hcra $Hhwmb $Hpend]" as "(HPC & Hcra & Hhwmb & Hpend)".
    1: done.
    1: by rewrite Hhb_v.
    iClear "Hcode".
    switcher_change_pc (switcher_label_offset ".Lcommon_context_install" + 6)%Z.
    subst hpost. iApply "Hpost". rewrite -Hh_v. iFrame.
  Qed.

  (** The install of user thread [B]'s context and the resuming [mret], at
      the context-switch thread, mtdc at [B]'s home: the registers receive
      [B]'s save area, MEPCC the resume PC, and the thread reaches
      [ResumedV]; [B]'s continuation receives its posture (when it resumes
      with interrupts disabled) and a credit. *)
  Lemma ctx_install_spec (ts : list nat) (B : nat) (g_tstk : Locality) (lreg : LReg)
      (wpc vepcc vc : LWord) (ws : list LWord) (v : resume_vals) (z : Z) (b : InterruptStatus)
      (hbP hP : Z) (o : option (nat * gset Addr)) :
    NoDup ts →
    mtdc_home_at (th := UserThread B) = tstack_home B →
    resume_ok_full ws v →
    zone_covers v.(rv_hwmb) v.(rv_hwm) v.(rv_zone) →
    (∀ zn, o = Some (B, zn) → zn = v.(rv_zone)) →
    dom lreg = all_registers_s →
    lreg !! csp = Some (lword_of_word (tstack_cap g_tstk B)) →
    lreg !! ct2 = Some wpc →
    legalise_pc wpc.(lw) = resume_pc_word ws →
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lcommon_context_install" ∗
    switcher_code_at CtxSwitch ∗
    inv Npool (Pool ts) ∗
    regs[CtxSwitch] lreg ∗
    ⌜saved_mie_ok ws⌝ ∗
    (∃ mshwmb_v : Z, ⌜ws !! 20%nat = Some (lword_of_word (WInt mshwmb_v))⌝ ∗ hwm_base[u B] mshwmb_v) ∗
    save_area_holed (UserThread B) ws ∗
    mtdc_lent_at (th := UserThread B) ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    mshwmb ↦ₜ[CtxSwitch] hbP ∗
    mshwm ↦ₜ[CtxSwitch] hP ∗
    pend_frag[CtxSwitch] None ∗
    lent_frag[CtxSwitch] (last_owner_zone o) ∗
    ctx_last_owner_frag o ∗
    ▷ (if o is Some (B', _) then
         (if decide (B' = B) then True else zone_halves[CtxSwitch] v.(rv_zone))
       else zone_halves[CtxSwitch] v.(rv_zone)) ∗
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
    iIntros (Hnd Hhome Hok Hcov Hlast_owner_B Hdom Hcsp Hct2 Hpc)
      "(HPC & #Hswitcher & #Hpool & Hregs & %Hsaved & Hbase & Hsave & Hlent & HMIE & Hhwmb & Hhwm
        & Hpend & Hlentf & Hlast_owner & Hhalves & Hmtdc & Hho & Hcur & Hsched & Hna & Hclose & Hcont)".
    pin_thread_instances CtxSwitch.
    pose proof Hok as Hok'.
    destruct Hok' as (Hregs_v & Hmie_v & [Hpc_v Hprov_v] & _ & _).
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
    iPoseProof (codefrag_pers_thread_indep CtxSwitch (UserThread B) with "Hswitcher")
      as "#Hswitcher_B".
    (* mstatus, from [B]'s save area *)
    iApply (common_context_mstatus_spec (th := CtxSwitch) (UserThread B) g_tstk ws b _ Hlen21 Hsaved
             with "[-]").
    iFrame "HPC Hcsp Hcra Hsave HMIE Hmpie Hswitcher_B".
    iNext. iIntros "(HPC & Hcsp & Hcra & Hsave & HMIE & Hmpie)".
    (* The window: MSHWM and MSHWMB, from [B]'s save area *)
    iApply (ctx_install_window_spec ts B g_tstk ws v _ hbP hP o Hnd Hlen21 Hok Hcov Hlast_owner_B
             with "[-]").
    iFrame "HPC Hswitcher Hpool Hcsp Hcra Hsave Hhwmb Hhwm Hpend Hlentf Hlast_owner Hhalves Hcur".
    iNext. iIntros "(HPC & Hcsp & Hcra & Hsave & Hhwmb & Hhwm & Hpend & Hlentf & Hlast_owner & Hcur)".
    (* The install, up to the [mret], from [B]'s save area *)
    iApply (common_context_reload_spec (th := CtxSwitch) (UserThread B) g_tstk wpc vepcc ws
             with "[$HPC $Hcsp $Hcra $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                    $Hca3 $Hca4 $Hca5 $Hsave $HMIE $Hmepcc $Hswitcher_B
                    Hnull Hlent Hmtdc Hcrit HU Hmcause Hmtval Hmpie Hbase Hhwmb Hhwm Hpend Hlentf
                    Hlast_owner Hcur Hsched Hna Hclose Hcont]"); first done.
    iNext. iIntros "(HPC & Hregs & Hsave & HMIE & Hmepcc & Hlc)".
    iClear "Hswitcher_B".
    iEval (rewrite Hhome /tstack_home) in "Hmtdc".
    iEval (rewrite -Hmie_v) in "Hmpie".
    switcher_open_label ".Lcommon_context_install" "Hswitcher" as "Hcode" pc_a Hpc_a.
    switcher_set_pc (pc_a ^+ 22%nat)%a.
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
      with "[Hsave Hlent Hbase]" as "Hpart".
    { rewrite csl_full_posture_part. iFrame. iPureIntro. exact Hsaved. }
    iDestruct "Hsched" as (P) "[#Hsched_own HP]".
    iExists B, v.
    iFrame "Hcur Hregs HPC HMIE Hna Hclose Hhwmb Hhwm Hpend Hlentf Hlast_owner".
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
