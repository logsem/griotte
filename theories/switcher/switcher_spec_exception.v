From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Export logrel switcher switcher_preamble.
From griotte Require Import switcher_exception_states switcher_exception_blocks_1
  switcher_exception_blocks_2 switcher_exception_blocks_3 switcher_call_blocks_6.
From griotte Require Import map_simpl register_tactics.

(** * Exception path of the switcher

    From the exception entry, with any register file, the switcher spills
    the interrupted context in the register save area and gives the volatile
    registers back to the state interpretation. A fault of the first spill
    of the call path (when [trap_no_resume] fails) resumes the interrupted
    context with the return values [-ENOTENOUGHSTACK] and 0, at
    [.Lswitch_just_return], a return to [cra]. Any other trap forces the
    unwind of the faulting compartment's call: the switcher sets the return
    values and jumps to the return routine. The path opens the invariant of
    the switcher: it needs the non-atomic token without [N_trap], which trap
    entry holds, and gives back the whole token. No instruction of the path
    faults. *)

Section Switcher_Spec_Exception.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_exception_path_spec
    (Nswitcher : namespace) (F : coPset) (rmap : LReg) (w : LWord) :
    ↑Nswitcher ⊆ F ->
    ↑N_trap ⊆ F ->
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->

    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    PC ↦ₚ lword_of_word mtcc_vec ∗
    registers_pointsto rmap ∗
    trap_entry_out w ∗
    na_own cerise_nais (F ∖ ↑N_trap) ∗
    ▷ ( ( ⌜trap_no_resume w⌝ -∗
          ∀ (rmap' : LReg),
          ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
          ⌜rmap' !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
          ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
          registers_pointsto rmap' -∗
          na_own cerise_nais F -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜¬ trap_no_resume w⌝ -∗
          ∀ (rmap' : LReg),
          ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
          ⌜∀ r, r ≠ ca0 → r ≠ ca1 → rmap' !! r = rmap !! r⌝ -∗
          ⌜rmap' !! ca0 = Some (WInt ENOTENOUGHSTACK : LWord)⌝ -∗
          ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
          PC ↦ₚ switcher_label_pc ".Lswitch_just_return" -∗
          registers_pointsto rmap' -∗
          na_own cerise_nais F -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant, with the token without [N_trap];
       - [switcher_exception_blocks_21_23_spec]: spill the registers, MEPCC,
         mstatus and mcause, and give the volatile registers back;
       - [switcher_exception_blocks_24_25_spec]: restore mtdc, and test for
         a fault of the first spill of the call path;
       - otherwise, [switcher_call_block_18_spec]: set the return values;
       - for such a fault, [switcher_exception_block_28_spec]: install the
         context, with the return values overwritten;
       - close the switcher invariant, and recombine the token. *)
    iIntros (HF HFtrap Hdisj Hfull)
      "(#Hinv_switcher & #Hstatic & HPC & Hrmap & Hout & Hna & Hpost)".
    iPoseProof "Hstatic" as "(#Hcode & _ & %Hmtcc)".
    rewrite Hmtcc.
    iMod (na_inv_acc with "Hinv_switcher Hna") as "(Hswitcher_inv & Hna & Hclose)";
      [done | solve_ndisj |].
    iModNamed switcher_inv_open "Hswitcher_inv".
    iDestruct (tstack_save_area_length with "Hsave_area") as %Hsave_len.
    rewrite /registers_pointsto.
    getRegValList [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca0;ca1;ca2;ca3;ca4;ca5].
    iExtractList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca0;ca1;ca2;ca3;ca4;ca5]
      as ["Hcra";"Hcsp";"Hcgp";"Hctp";"Hct0";"Hct1";"Hct2";"Hcs0";"Hcs1";
          "Hca0";"Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].

    (* Blocks 21-23: the exception entry *)
    iApply (switcher_exception_blocks_21_23_spec with
             "[- $HPC $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hmtdc $Hsave_area $Hout $Hcode]");
      first done.
    iNext; iIntros (wst cause zca0)
      "(%Hcause & HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hmtdc & Hsave_area & Htok & _)".

    (* Blocks 24-25: [.Lhandle_error] *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    (* The close of the switcher invariant, and the recombination of the
       token, for any content of the register save area *)
    iAssert (∀ save' : list LWord,
               mtdc ↦ₛᵣ tstack_cap -∗
               [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save' ]] -∗
               (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a
                 ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) -∗
               trap_entry_res
               ={⊤}=∗
               na_own cerise_nais F)%I
      with "[HthreadID Htstk Hcstk_full Hstk_interp Hclose Hna]" as "Hclose".
    { iIntros (save') "Hmtdc Hsave_area Hframeoffset Htok".
      iMod ("Hclose" with
             "[Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hcstk_full Hstk_interp $Hna]")
        as "Hna".
      { iNext. rewrite /switcher_inv /tstack_cap /tstack_save_end.
        iExists a_tstk, cstk', _, tstk_next. iFrame "∗ # %". iPureIntro. by split. }
      iModIntro.
      iApply (trap_entry_res_split F with "[$Htok $Hna]"); first done. }
    iApply (switcher_exception_blocks_24_25_spec _ _ (lmepcc_of_pc w) with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hctp $Hca0 $Hca1 $Hct2 $Hmtdc $Hsave_area
                 $Hframeoffset $Hcode]").
    { by apply exception_spill_length. }
    { done. }
    iNext; iSplit.
    - (* Any other trap: block 18, the forced unwind *)
      iIntros (Hno_resume wct0' wct1' wctp')
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hsave_area
          & Hframeoffset & _)".
      iApply (switcher_call_block_18_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
      iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
      iMod ("Hclose" with "Hmtdc Hsave_area Hframeoffset Htok") as "Hna".
      (* The return values are inserted last *)
      iInsertList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca2;ca3;ca4;ca5;ca0;ca1].
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[] [] [] [] HPC Hrmap Hna").
      + iPureIntro. exact Hno_resume.
      + iPureIntro. intros r.
        repeat (rewrite lookup_insert_is_Some'; right).
        apply Hfull.
      + iPureIntro. rewrite lookup_insert_ne //. apply lookup_insert_eq.
      + iPureIntro. apply lookup_insert_eq.
    - (* A fault of the first spill of the call path: block 28, the context
         install, resumes the interrupted context *)
      iIntros (Hresume wct0' wct1' wctp')
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hsave_area
          & Hframeoffset & _)".
      iApply (switcher_exception_block_28_spec with
               "[- $HPC $Hcsp $Hcra $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                   $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hsave_area $Htok $Hcode]").
      { rewrite !length_insert. by apply exception_spill_length. }
      iNext; iIntros
        "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
          & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hsave_area & Htok & _)".
      (* The PC to resume is a valid PC: MEPCC keeps it *)
      rewrite (_ : llegalise MEPCC (switcher_label_pc ".Lswitch_just_return") =
                   switcher_label_pc ".Lswitch_just_return"); last reflexivity.
      iMod ("Hclose" with "Hmtdc Hsave_area Hframeoffset Htok") as "Hna".
      rewrite /exception_spill /TrustedStack_offset_ca0 /TrustedStack_offset_ca1 /=.
      (* The other registers get their words back: the register map is the
         original one, with the return values inserted last *)
      iInsertList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca2;ca3;ca4;ca5;ca0;ca1].
      rewrite (insert_id _ _ _ Hwcra) (insert_id _ _ _ Hwcsp) (insert_id _ _ _ Hwcgp)
        (insert_id _ _ _ Hwctp) (insert_id _ _ _ Hwct0) (insert_id _ _ _ Hwct1)
        (insert_id _ _ _ Hwct2) (insert_id _ _ _ Hwcs0) (insert_id _ _ _ Hwcs1)
        (insert_id _ _ _ Hwca2) (insert_id _ _ _ Hwca3) (insert_id _ _ _ Hwca4)
        (insert_id _ _ _ Hwca5).
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[] [] [] [] [] HPC Hrmap Hna").
      + iPureIntro. destruct Hresume as [Hb Ha]. by intros [Hb' | Ha'].
      + iPureIntro. intros r.
        repeat (rewrite lookup_insert_is_Some'; right).
        apply Hfull.
      + iPureIntro. intros r Hr0 Hr1. rewrite !lookup_insert_ne //.
      + iPureIntro. rewrite lookup_insert_ne //. apply lookup_insert_eq.
      + iPureIntro. apply lookup_insert_eq.
  Qed.

End Switcher_Spec_Exception.
