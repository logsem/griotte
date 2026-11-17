From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules traps.vcsr proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_exception_states trusted_spill_registers_spec.
From griotte Require Import context_switch_layout_instance.

(** * Exception path: [.Lcommon_context_install]

    [.Lcommon_context_install] installs the context of the register save
    area and resumes it, at InterruptDisabled with the posture of the
    thread: it restores mstatus (whose MIE, saved by the exception entry,
    is InterruptDisabled), MSHWM and MSHWMB, writes the PC to resume (in
    [ct2]) to MEPCC, reloads the registers (the stack pointer last, as it
    overwrites the trusted stack), and returns from the trap with [mret],
    which moves the posture to the saved MPIE. *)

Section Save_Area_Cells.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

End Save_Area_Cells.

Section Common_Context_Install.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The code of [.Lcommon_context_install], around the reload of the
      registers. *)
  #[local] Definition common_context_install_instrs : list Word :=
    encodeInstrsW [machine_instructions.CLoad cra csp TrustedStack_offset_mstatus;
                   SpecialRW cnull mstatus (inr cra);
                   machine_instructions.CLoad cra csp TrustedStack_offset_mshwm;
                   SpecialRW cnull mshwm (inr cra);
                   machine_instructions.CLoad cra csp TrustedStack_offset_mshwmb;
                   SpecialRW cnull mshwmb (inr cra);
                   SpecialRW cnull mepcc (inr ct2)] ++
    trusted_reload_registers_instrs exception_spill_regs ++
    encodeInstrsW [machine_instructions.CLoad csp csp TrustedStack_offset_csp; Mret].

  (** From [.Lcommon_context_install]: [cra] receives the word [mstatus] of
      the save area of [o], and mstatus that word, whose MIE is
      InterruptDisabled; MPIE becomes its saved MPIE. *)
  Lemma common_context_mstatus_spec (o : Thread) (g_tstk : Locality) (ws : list LWord)
      (q : InterruptStatus) (wcra : LWord) :
    length ws = 21%nat →
    saved_mie_ok ws →
    PC ↦ₚ[th] switcher_label_pc ".Lcommon_context_install" ∗
    csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                 (@b_trusted_stack (tlayout_of o)) ∗
    cra ↦ᵣ[th] wcra ∗
    save_area_holed o ws ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    MPIE_frag q ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] switcher_pc (switcher_label_offset ".Lcommon_context_install" + 2) ∗
        csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                     (@b_trusted_stack (tlayout_of o)) ∗
        cra ↦ᵣ[th] save_area_word ws TrustedStack_offset_mstatus ∗
        save_area_holed o ws ∗
        MIE ↦ₜ[th] InterruptDisabled ∗
        MPIE_frag (mpie_of (get_a (save_area_word ws TrustedStack_offset_mstatus).(lw))) -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hlen Hsaved) "(HPC & Hcsp & Hcra & Hsave & Hmie & Hmpie & #Hswitcher & Hpost)".
    (* The code at the instance of [th]; a local copy of [th] is found first
       by the instance search, before [o]. *)
    iEval (rewrite (codefrag_pers_thread_indep o th)) in "Hswitcher".
    pose (th_pin := th).
    destruct ws as
      [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
      [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    clear Hlen.
    (* The saved MIE is InterruptDisabled *)
    pose proof (Hsaved s17 eq_refl) as Hs17_mie.
    iEval (rewrite save_area_holed_explicit) in "Hsave".
    iDestruct "Hsave" as "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
      & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs17 & Hs18 & Hs19 & Hs20)".
    switcher_open_label ".Lcommon_context_install" "Hswitcher" as "Hcode" pc_a Hpc_a.
    pose proof (tstack_save_cell_ok (th := o) TrustedStack_offset_mstatus
                  ltac:(unfold TrustedStack_offset_mstatus; lia))
      as (Hts_17 & Hts_17_bounds & Hts_17_shadow).
    (* The saved words may be heap capabilities: they are loaded exactly *)
    iAssert (load_witness_res LoadPlain) as "Hwit"; first done.
    (* CLoad cra csp TrustedStack_offset_mstatus *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ cra csp TrustedStack_offset_mstatus)
      with "[$HPC $Hcra $Hcsp $Hs17 $Hwit]" as (wst) "(%Hload & HPC & Hcra & Hcsp & Hs17 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst wst.
    (* SpecialRW cnull mstatus cra *)
    iInstrApply "Hcode" (wp_csrw_mstatus _ _ _ _ _ _ _ _ _ _ _ q)
      with "[$HPC $Hcra $Hmie $Hmpie]" as "(HPC & Hcra & Hmie & Hmpie)".
    iClear "Hcode".
    switcher_change_pc (switcher_label_offset ".Lcommon_context_install" + 2)%Z.
    iApply "Hpost".
    iFrame "HPC Hcsp Hcra Hmie Hmpie".
    rewrite save_area_holed_explicit. iFrame.
  Qed.

  (** From [.Lcommon_context_install + 2] at a user thread: MSHWM receives
      the saved MSHWM, which lowers it or is below MSHWMB, and MSHWMB the
      saved MSHWMB, which is MSHWMB. *)
  #[local] Lemma common_context_hwm_restore_spec (o : Thread) (g_tstk : Locality)
      (ws : list LWord) (wcra : LWord) (mshwmb_v : Addr) (mshwm_v : Z) :
    th ≠ CtxSwitch →
    length ws = 21%nat →
    (mshwmb_v <= get_a (save_area_word ws TrustedStack_offset_mshwm).(lw) <= mshwm_v ∨
     get_a (save_area_word ws TrustedStack_offset_mshwm).(lw) < mshwmb_v)%Z →
    get_a (save_area_word ws TrustedStack_offset_mshwmb).(lw) = mshwmb_v →
    PC ↦ₚ[th] switcher_pc (switcher_label_offset ".Lcommon_context_install" + 2) ∗
    csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                 (@b_trusted_stack (tlayout_of o)) ∗
    cra ↦ᵣ[th] wcra ∗
    save_area_holed o ws ∗
    hwm_regs (ceriseg := ceriseG_of th) mshwmb_v mshwm_v ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] switcher_pc (switcher_label_offset ".Lcommon_context_install" + 6) ∗
        csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                     (@b_trusted_stack (tlayout_of o)) ∗
        cra ↦ᵣ[th] save_area_word ws TrustedStack_offset_mshwmb ∗
        save_area_holed o ws ∗
        hwm_regs (ceriseg := ceriseG_of th) mshwmb_v
          (get_a (save_area_word ws TrustedStack_offset_mshwm).(lw)) -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hth Hlen Hsh Hsb) "(HPC & Hcsp & Hcra & Hsave & Hhwm & #Hswitcher & Hpost)".
    iEval (rewrite (codefrag_pers_thread_indep o th)) in "Hswitcher".
    pose (th_pin := th).
    destruct ws as
      [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
      [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    clear Hlen.
    rewrite /save_area_word /TrustedStack_offset_mshwm /TrustedStack_offset_mshwmb /= in Hsh Hsb.
    iEval (rewrite save_area_holed_explicit) in "Hsave".
    iDestruct "Hsave" as "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
      & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs17 & Hs18 & Hs19 & Hs20)".
    switcher_open_label ".Lcommon_context_install" "Hswitcher" as "Hcode" pc_a Hpc_a.
    switcher_set_pc (pc_a ^+ 2%nat)%a.
    pose proof (tstack_save_cell_ok (th := o) TrustedStack_offset_mshwm
                  ltac:(unfold TrustedStack_offset_mshwm; lia))
      as (Hts_19 & Hts_19_bounds & Hts_19_shadow).
    pose proof (tstack_save_cell_ok (th := o) TrustedStack_offset_mshwmb
                  ltac:(unfold TrustedStack_offset_mshwmb; lia))
      as (Hts_20 & Hts_20_bounds & Hts_20_shadow).
    iAssert (load_witness_res LoadPlain) as "Hwit"; first done.
    (* CLoad cra csp TrustedStack_offset_mshwm *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ cra csp TrustedStack_offset_mshwm)
      with "[$HPC $Hcra $Hcsp $Hs19 $Hwit]" as (wsh) "(%Hload & HPC & Hcra & Hcsp & Hs19 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst wsh.
    (* SpecialRW cnull mshwm cra *)
    iInstrApply "Hcode" wp_csrw_mshwm_lower with "[$HPC $Hcra $Hhwm]" as "(HPC & Hcra & Hhwm)".
    iDestruct "Hhwm" as "[Hmshwmb Hmshwm]".
    (* CLoad cra csp TrustedStack_offset_mshwmb *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ cra csp TrustedStack_offset_mshwmb)
      with "[$HPC $Hcra $Hcsp $Hs20 $Hwit]" as (wsb) "(%Hload & HPC & Hcra & Hcsp & Hs20 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst wsb.
    (* SpecialRW cnull mshwmb cra *)
    iInstrApply "Hcode" (wp_csrw_mshwmb _ _ _ _ _ _ _ _ _ _ _ mshwmb_v)
      with "[$HPC $Hcra $Hmshwmb]" as "(HPC & Hcra & Hmshwmb)".
    { by apply kind_of_user. }
    iClear "Hcode".
    switcher_change_pc (switcher_label_offset ".Lcommon_context_install" + 6)%Z.
    iApply "Hpost".
    iFrame "HPC Hcsp Hcra Hmshwmb Hmshwm".
    rewrite save_area_holed_explicit. iFrame.
  Qed.

  (** From [.Lcommon_context_install + 6] to its [mret], at any thread and
      for the register save area of [o]: MEPCC receives the word in [ct2],
      legalised, and the registers the words of the save area, the stack
      pointer last. Its word [hazardPointers] is not read. *)
  Lemma common_context_reload_spec (o : Thread) (g_tstk : Locality) (wpc vepcc : LWord)
      (ws : list LWord)
      (wcra wcgp wctp wct0 wct1 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    length ws = 21%nat →
    PC ↦ₚ[th] switcher_pc (switcher_label_offset ".Lcommon_context_install" + 6) ∗
    csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                 (@b_trusted_stack (tlayout_of o)) ∗
    cra ↦ᵣ[th] wcra ∗
    cgp ↦ᵣ[th] wcgp ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wpc ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    ca3 ↦ᵣ[th] wca3 ∗
    ca4 ↦ᵣ[th] wca4 ∗
    ca5 ↦ᵣ[th] wca5 ∗
    save_area_holed o ws ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    mepcc ↦ₓ vepcc ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] switcher_pc (switcher_label_offset ".Lcommon_context_install" + 22) ∗
        ([∗ list] r ∈ exception_spill_regs ++ [csp],
           r ↦ᵣ[th] save_area_word ws (TrustedStack_offset_reg r)) ∗
        save_area_holed o ws ∗
        MIE ↦ₜ[th] InterruptDisabled ∗
        mepcc ↦ₓ llegalise mepcc wpc ∗
        £ 1 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hlen)
      "(HPC & Hcsp & Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hsave & Hmie & Hmepcc & #Hswitcher
       & Hpost)".
    (* The code at the instance of [th]; a local copy of [th] is found first
       by the instance search, before [o]. *)
    iEval (rewrite (codefrag_pers_thread_indep o th)) in "Hswitcher".
    pose (th_pin := th).
    destruct ws as
      [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
      [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    clear Hlen.
    iEval (rewrite save_area_holed_explicit) in "Hsave".
    iDestruct "Hsave" as "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
      & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs17 & Hs18 & Hs19 & Hs20)".
    switcher_open_label ".Lcommon_context_install" "Hswitcher" as "Hcode" pc_a Hpc_a.
    switcher_set_pc (pc_a ^+ 6%nat)%a.
    (* The reload of the registers but the stack pointer is the macro *)
    iAssert (codefrag_pers pc_a common_context_install_instrs) as "Hcode_all";
      first iExact "Hcode".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hreload _]".
    iAssert (vcsr_frag (ceriseg := ceriseG_of th) mepcc vepcc) with "[Hmepcc]" as "Hmepcc".
    { rewrite vcsr_frag_pointsto. iExact "Hmepcc". }
    (* SpecialRW cnull mepcc ct2 *)
    iInstrApply "Hcode" with "Hlc" wp_cspecialw_mepcc
      with "[$HPC $Hct2 $Hmepcc]" as "(HPC & Hct2 & Hmepcc)".
    iEval (rewrite vcsr_frag_pointsto) in "Hmepcc".
    switcher_hide "Hpost" as hpost.
    (* The reload of the registers but the stack pointer *)
    rewrite (_ : pc_a ^+ length (encodeInstrsW
                   [machine_instructions.CLoad cra csp TrustedStack_offset_mstatus;
                    SpecialRW cnull mstatus (inr cra);
                    machine_instructions.CLoad cra csp TrustedStack_offset_mshwm;
                    SpecialRW cnull mshwm (inr cra);
                    machine_instructions.CLoad cra csp TrustedStack_offset_mshwmb;
                    SpecialRW cnull mshwmb (inr cra);
                    SpecialRW cnull mepcc (inr ct2)]) =
                 (pc_a ^+ 6%nat) ^+ 1); last (clear; solve_addr).
    iApply (trusted_reload_registers_spec (ceriseg := ceriseG_of th) (th := th)
              (CL := crit_link_full th) _ _ _ _ _ _ _ _ _ exception_spill_regs
              [wcra; wcgp; wctp; wct0; wct1; wpc; wcs0; wcs1; wca0; wca1; wca2; wca3; wca4; wca5]
              [s1; s3; s4; s5; s6; s7; s8; s9; s10; s11; s12; s13; s14; s15]
             with "[- $HPC $Hcsp $Hreload]").
    { done. }
    { done. }
    { rewrite trusted_reload_registers_instrs_length /=. solve_addr. }
    { apply (trusted_save_cells_ok_exception (th := o)). }
    { by apply (bool_decide_unpack _). }
    { by apply (bool_decide_unpack _). }
    iSplitL "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
    { cbn. iFrame "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5". }
    iSplitL "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15".
    { cbn. iFrame "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15". }
    iNext; iIntros "(HPC & Hcsp & Hregs & Hcells & _)".
    iEval (cbn [big_sepL2 exception_spill_regs]) in "Hregs Hcells".
    iDestruct "Hregs" as
      "(Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & _)".
    iDestruct "Hcells" as
      "(Hs1 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
       & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & _)".
    pose proof (tstack_save_cell_ok (th := o) TrustedStack_offset_csp
                  ltac:(unfold TrustedStack_offset_csp; lia))
      as (Hts_2 & Hts_2_bounds & Hts_2_shadow).
    rewrite (_ : ((pc_a ^+ 6%nat) ^+ 1) ^+ length exception_spill_regs =
                 pc_a ^+ (7 + length exception_spill_regs)%nat); last (clear; solve_addr).
    (* CLoad csp csp TrustedStack_offset_csp *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_same_inbounds _ _ _ _ _ _ _ csp TrustedStack_offset_csp
         _ _ _ _ _ _ _ _ _ LoadPlain)
      with "[$HPC $Hcsp $Hs2 //]" as (wcsp) "(%Hload & HPC & Hcsp & Hs2 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst wcsp.
    iClear "Hcode Hcode_all Hcode_rest Hreload".
    switcher_change_pc (switcher_label_offset ".Lcommon_context_install" + 22)%Z.
    subst hpost. iApply "Hpost".
    iFrame "HPC Hmie Hlc Hmepcc".
    iSplitL "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hcsp".
    { rewrite /save_area_word. cbn [big_opL exception_spill_regs app].
      iFrame "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hcsp". }
    rewrite save_area_holed_explicit. iFrame.
  Qed.

  (** From [.Lcommon_context_install], at InterruptDisabled with the
      posture, but its save area joined with the word [hazardPointers]:
      the registers receive the words of the register save area, and the PC
      the word in [ct2], as MEPCC holds it. The posture goes to the saved
      MPIE [p] (the MPIE of the word [mstatus] of the register save area),
      and the save area back into it; [hazardPointers] is given back. MSHWM
      is restored to a value at most its logical one, or below MSHWMB, and
      MSHWMB to its own value. *)
  Lemma common_context_install_spec (g_tstk : Locality) (wpc : LWord) (save_area : list LWord)
    (wcra wcgp wctp wct0 wct1 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord)
    (mshwmb_v : Addr) (mshwm_v : Z) :
    th ≠ CtxSwitch ->
    length save_area = 21%nat ->
    saved_mie_ok save_area ->
    (* the saved MSHWM lowers MSHWM, or is below MSHWMB *)
    (mshwmb_v <= get_a (save_area !!! Z.to_nat TrustedStack_offset_mshwm).(lw) <= mshwm_v ∨
     get_a (save_area !!! Z.to_nat TrustedStack_offset_mshwm).(lw) < mshwmb_v)%Z ->
    (* the saved MSHWMB is MSHWMB *)
    save_area !! Z.to_nat TrustedStack_offset_mshwmb = Some (lword_of_word (WInt mshwmb_v)) ->

    PC ↦ₚ[th] switcher_label_pc ".Lcommon_context_install" ∗
    csp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
    cra ↦ᵣ[th] wcra ∗
    cgp ↦ᵣ[th] wcgp ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wpc ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    ca3 ↦ᵣ[th] wca3 ∗
    ca4 ↦ᵣ[th] wca4 ∗
    ca5 ↦ᵣ[th] wca5 ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    hwm_regs mshwmb_v mshwm_v ∗
    hwm_base[th] mshwmb_v ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    handover_res ∗
    mtdc_lent ∗
    switcher_code ∗
    ▷ ( let p := mpie_of (get_a (save_area !!! Z.to_nat TrustedStack_offset_mstatus).(lw)) in
        PC ↦ₚ[th] llegalise mepcc wpc ∗
        cra ↦ᵣ[th] (save_area !!! 1%nat) ∗
        csp ↦ᵣ[th] (save_area !!! 2%nat) ∗
        cgp ↦ᵣ[th] (save_area !!! 3%nat) ∗
        ctp ↦ᵣ[th] (save_area !!! 4%nat) ∗
        ct0 ↦ᵣ[th] (save_area !!! 5%nat) ∗
        ct1 ↦ᵣ[th] (save_area !!! 6%nat) ∗
        ct2 ↦ᵣ[th] (save_area !!! 7%nat) ∗
        cs0 ↦ᵣ[th] (save_area !!! 8%nat) ∗
        cs1 ↦ᵣ[th] (save_area !!! 9%nat) ∗
        ca0 ↦ᵣ[th] (save_area !!! 10%nat) ∗
        ca1 ↦ᵣ[th] (save_area !!! 11%nat) ∗
        ca2 ↦ᵣ[th] (save_area !!! 12%nat) ∗
        ca3 ↦ᵣ[th] (save_area !!! 13%nat) ∗
        ca4 ↦ᵣ[th] (save_area !!! 14%nat) ∗
        ca5 ↦ᵣ[th] (save_area !!! 15%nat) ∗
        tstack_hazard_cell ↦ₐ (save_area !!! Z.to_nat TrustedStack_offset_hazardPointers) ∗
        hwm_regs mshwmb_v (get_a (save_area !!! Z.to_nat TrustedStack_offset_mshwm).(lw)) ∗
        ⌜route_pre th p⌝ ∗
        MIE ↦ₜ[th] p ∗
        held (th := th) p ∗
        £ 1 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hth Hlen Hsaved Hsh Hsb)
      "(HPC & Hcsp & Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hsave & Hhwm & Hhb & Hmie & Hho & Hlent
       & #Hswitcher & Hpost)".
    assert (Hsb20 : save_area !! 20%nat = Some (lword_of_word (WInt mshwmb_v))) by exact Hsb.
    assert (Hsb_a : get_a (save_area_word save_area TrustedStack_offset_mshwmb).(lw) = mshwmb_v)
      by rewrite /save_area_word Hsb //.
    clear Hsb.
    destruct save_area as
      [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
      [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    clear Hlen.
    set (save := [s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; s12; s13; s14; s15; s16;
                  s17; s18; s19; s20]).
    (* The save area, split at its word [hazardPointers] *)
    rewrite /tstack_save_end.
    iDestruct (save_area_split save s16 with "Hsave") as "[Hholed Hhazard]"; first done.
    (* The volatile registers *)
    iDestruct (handover_res_unfold with "Hho")
      as (vepcc vcause vtval vmpie) "(Hcrit & HU & Hmepcc & Hmcause & Hmtval & Hmpie)".
    (* mstatus *)
    iApply (common_context_mstatus_spec th g_tstk save vmpie
             with "[$HPC $Hcsp $Hcra $Hholed $Hmie $Hmpie $Hswitcher
                    Hpost Hcrit HU Hmepcc Hmcause Hmtval Hlent Hhazard Hhwm Hhb Hcgp Hctp Hct0 Hct1
                    Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5]"); [done | done |].
    iNext. iIntros "(HPC & Hcsp & Hcra & Hholed & Hmie & Hmpie)".
    (* MSHWM and MSHWMB *)
    iApply (common_context_hwm_restore_spec th g_tstk save _ mshwmb_v mshwm_v
             with "[$HPC $Hcsp $Hcra $Hholed $Hhwm $Hswitcher
                    Hpost Hcrit HU Hmepcc Hmcause Hmtval Hlent Hhazard Hmie Hmpie Hhb Hcgp Hctp Hct0
                    Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5]"); [done | done | done | done |].
    iNext. iIntros "(HPC & Hcsp & Hcra & Hholed & Hhwm)".
    (* The reload, up to the [mret] *)
    iApply (common_context_reload_spec th g_tstk wpc vepcc save
             with "[$HPC $Hcsp $Hcra $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                    $Hca3 $Hca4 $Hca5 $Hholed $Hmie $Hmepcc $Hswitcher
                    Hpost Hcrit HU Hmcause Hmtval Hlent Hhazard Hmpie Hhwm Hhb]"); [done |].
    iNext. iIntros "(HPC & Hregs & Hholed & Hmie & Hmepcc & Hlc)".
    switcher_hide "Hpost" as hpost.
    iEval (rewrite /save_area_word; cbn [big_opL exception_spill_regs app]) in "Hregs".
    iDestruct "Hregs" as
      "(Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hcsp & _)".
    iEval (rewrite /save_area_word /=) in "Hmpie".
    switcher_open_label ".Lcommon_context_install" "Hswitcher" as "Hcode" pc_a Hpc_a.
    switcher_set_pc (pc_a ^+ 22%nat)%a.
    (* The save area goes back into the posture *)
    iAssert (@posture_part _ _ _ th _ (crit_route_full th)) with "[Hholed Hlent Hhb]" as "Hpart".
    { rewrite posture_part_user //. iFrame "Hlent". iExists save. iFrame "Hholed".
      iSplit; first (iPureIntro; exact Hsaved). iExists mshwmb_v. iFrame "Hhb".
      iPureIntro. exact Hsb20. }
    set (p := mpie_of (get_a s17.(lw))).
    iAssert (posture_res_gen (th := th) (Some p) (Some (llegalise mepcc wpc)) None None)
      with "[Hcrit HU Hmepcc Hmcause Hmtval Hmpie Hpart]" as "Hposture".
    { rewrite posture_res_gen_unfold. iFrame "Hpart".
      iExists (llegalise mepcc wpc), vcause, vtval, p. by iFrame. }
    (* Mret *)
    iInstrApply "Hcode" with "Hlc"
      (wp_mret_success_posture _ _ _ _ _ _ _ _ (llegalise mepcc wpc) p)
      with "[$HPC $Hmie $Hposture]" as "(HPC & Hmie & Hheld)".
    subst hpost. iApply "Hpost".
    iDestruct (lc_weaken 1 with "Hlc") as "Hlc"; first lia.
    iFrame "HPC Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5
            Hhazard Hhwm Hmie Hheld Hlc".
    iPureIntro. by intros Hc.
  Qed.

End Common_Context_Install.
