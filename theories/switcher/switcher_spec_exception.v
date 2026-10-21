From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Export logrel switcher switcher_preamble.
From griotte Require Import switcher_exception_states switcher_exception_blocks_1
  switcher_exception_blocks_2 switcher_call_blocks_6.
From griotte Require Import map_simpl register_tactics.

(** * Exception path of the switcher

    From the exception entry, with any register file, the switcher spills
    the interrupted context in the register save area, gives the volatile
    registers back to the state interpretation, and forces the unwind of
    the faulting compartment's call: it sets the return values and jumps to
    the return routine. The path opens the invariant of the switcher: it
    needs the non-atomic token without [N_trap], which trap entry holds,
    and gives back the whole token. No instruction of the path faults. *)

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
    ▷ ( ∀ (rmap' : LReg),
          ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
          ⌜rmap' !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
          ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
          registers_pointsto rmap' -∗
          na_own cerise_nais F -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant, with the token without [N_trap];
       - [switcher_exception_blocks_21_23_spec]: spill the registers, MEPCC,
         mstatus and mcause, and give the volatile registers back;
       - [switcher_exception_blocks_24_25_spec]: restore mtdc;
       - [switcher_call_block_18_spec]: set the return values;
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
    iApply (switcher_exception_blocks_24_25_spec with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hctp $Hmtdc $Hsave_area $Hframeoffset $Hcode]").
    { by apply exception_spill_length. }
    iNext; iIntros (wct0' wct1' wctp')
      "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hmtdc & Hsave_area & Hframeoffset & _)".

    (* Block 18: the forced unwind *)
    iApply (switcher_call_block_18_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".

    (* Close the switcher invariant, and recombine the token *)
    iMod ("Hclose" with
           "[Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hcstk_full Hstk_interp $Hna]")
      as "Hna".
    { iNext. rewrite /switcher_inv /tstack_cap /tstack_save_end.
      iExists a_tstk, cstk', _, tstk_next. iFrame "∗ # %". done. }
    iDestruct (trap_entry_res_split F with "[$Htok $Hna]") as "Hna"; first done.
    iInsertList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca0;ca1;ca2;ca3;ca4;ca5].
    iApply ("Hpost" with "[] [] [] HPC Hrmap Hna").
    - iPureIntro. intros r. rewrite !lookup_insert_is_Some'. naive_solver.
    - iPureIntro. by simplify_map_eq.
    - iPureIntro. by simplify_map_eq.
  Qed.

End Switcher_Spec_Exception.
