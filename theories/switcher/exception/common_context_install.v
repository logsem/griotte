From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_exception_states trusted_spill_registers_spec.

(** * Exception path: [.Lcommon_context_install]

    [.Lcommon_context_install] installs the context of the register save
    area and resumes it: it restores mstatus, borrows the volatile
    registers back from the trap-entry token to write the PC to resume (in
    [ct2]) to MEPCC, reloads the registers (the stack pointer last, as it
    overwrites the trusted stack), and returns from the trap with [mret],
    which gives the volatile registers back. The interrupt status after
    [mret] is that of mstatus's MPIE, which the specification does not
    track. *)

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
                   SpecialRW cnull mstatus (inr cra); SpecialRW cnull mepcc (inr ct2)] ++
    trusted_reload_registers_instrs exception_spill_regs ++
    encodeInstrsW [machine_instructions.CLoad csp csp TrustedStack_offset_csp; Mret].

  (** From [.Lcommon_context_install]: the registers receive the words of
      the register save area, and the PC the word in [ct2], as MEPCC holds
      it. *)
  Lemma common_context_install_spec (g_tstk : Locality) (wpc : LWord) (save_area : list LWord)
    (wcra wcgp wctp wct0 wct1 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    length save_area = 21%nat ->

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
    trap_entry_res ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] llegalise mepcc wpc ∗
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
        [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
        trap_entry_res -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hlen)
      "(HPC & Hcsp & Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hsave & Htok & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    destruct save_area as
      [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
      [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    rewrite /tstack_save_end.
    assert ((b_trusted_stack + 21%nat)%a = Some (b_trusted_stack ^+ TSTACK_REGFRAME_SZ))
      as Hsave_end by (tstack_unfold; solve_addr).
    iRegionSplit "Hsave" as
      "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
       & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs16 & Hs17 & Hs18 & Hs19 & Hs20)".
    switcher_open_label ".Lcommon_context_install" "Hswitcher" as "Hcode" pc_a Hpc_a.
    (* The block has no exit by label: the equation of its address is not needed *)
    clear Hpc_a.
    (* The reload of the registers but the stack pointer is the macro *)
    iAssert (codefrag_pers pc_a common_context_install_instrs) as "Hcode_all";
      first iExact "Hcode".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hreload _]".
    pose proof (tstack_save_cell_ok TrustedStack_offset_mstatus
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
    iInstrApply "Hcode" wp_csrw_mstatus with "[$HPC $Hcra]" as "(HPC & Hcra)".
    (* The trap-entry token, without its part for mtval, lends MEPCC and
       mcause *)
    iDestruct (trap_entry_res_vcsr_tval with "Htok") as "[Htok Htval]".
    iApply (wp_vcsr_lend with "Htok"); first done.
    iIntros (wepcc wcause) "Hmepcc Hmcause".
    (* SpecialRW cnull mepcc ct2 *)
    iInstrApply "Hcode" wp_cspecialw_mepcc with "[$HPC $Hct2 $Hmepcc]" as "(HPC & Hct2 & Hmepcc)".
    (* The reload of the registers but the stack pointer *)
    rewrite (_ : pc_a ^+ length (encodeInstrsW
                   [machine_instructions.CLoad cra csp TrustedStack_offset_mstatus;
                    SpecialRW cnull mstatus (inr cra); SpecialRW cnull mepcc (inr ct2)]) =
                 pc_a ^+ 1 ^+ 1 ^+ 1); last (clear; solve_addr).
    iApply (trusted_reload_registers_spec _ _ _ _ _ _ _ _ _ exception_spill_regs
              [s17; wcgp; wctp; wct0; wct1; wpc; wcs0; wcs1; wca0; wca1; wca2; wca3; wca4; wca5]
              [s1; s3; s4; s5; s6; s7; s8; s9; s10; s11; s12; s13; s14; s15]
             with "[- $HPC $Hcsp $Hreload]").
    { done. }
    { done. }
    { rewrite trusted_reload_registers_instrs_length /=. solve_addr. }
    { apply trusted_save_cells_ok_exception. }
    { rewrite /exception_spill_regs. set_solver. }
    { rewrite /exception_spill_regs. set_solver. }
    iSplitL "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
    { cbn. iFrame "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5". }
    iSplitL "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15".
    { cbn. iFrame "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15". }
    iNext; iIntros "(HPC & Hcsp & Hregs & Hcells & _)".
    cbn.
    iDestruct "Hregs" as
      "(Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & _)".
    iDestruct "Hcells" as
      "(Hs1 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
       & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & _)".
    pose proof (tstack_save_cell_ok TrustedStack_offset_csp
                  ltac:(unfold TrustedStack_offset_csp; lia))
      as (Hts_2 & Hts_2_bounds & Hts_2_shadow).
    rewrite (_ : (((pc_a ^+ 1) ^+ 1) ^+ 1) ^+ length exception_spill_regs =
                 pc_a ^+ (3 + length exception_spill_regs)%nat); last (clear; solve_addr).
    (* CLoad csp csp TrustedStack_offset_csp *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_same_inbounds _ _ _ _ _ _ _ csp TrustedStack_offset_csp
         _ _ _ _ _ _ _ _ _ LoadPlain)
      with "[$HPC $Hcsp $Hs2 //]" as (wcsp) "(%Hload & HPC & Hcsp & Hs2 & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst wcsp.
    (* Mret *)
    iInstrApply "Hcode" wp_mret_vcsr with "[$HPC $Hmepcc $Hmcause]" as "(HPC & Htok)".
    iDestruct (trap_entry_res_vcsr_tval with "[$Htok $Htval]") as "Htok".
    iApply "Hpost".
    iFrame "HPC Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Htok".
    iRegionMerge. iFrame.
  Qed.

End Common_Context_Install.
