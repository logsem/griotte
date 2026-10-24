From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Export logrel switcher switcher_preamble switcher_error_handler.
From griotte Require Import switcher_exception_states.
From griotte.switcher.exception Require Import common_context_install
  handle_error_handler_invoke handle_error_install_context.
From griotte Require Import map_simpl register_tactics.

(** * Installation of the context of an error handler

    When an error handler returns with [ca0] zero, the switcher installs the
    context that the handler leaves in its [ErrorState], at its stack
    pointer [csp]: the return ([.Lhandle_error_handler_return]) continues
    at [.Lhandle_error_install_context], which loads the [ErrorState],
    copies words 1-15 to the register save area, increments the error
    handler count of the topmost frame, and jumps to the context install
    [.Lcommon_context_install], which resumes the context with [mret].

    The specification is generic in the source of the [ErrorState]: a
    resource [L i ls], which holds once the first [i] words [ls] are
    loaded, and a load accessor ([cells_load_acc]) that the caller provides.
    The installation opens the invariant of the switcher, and gives the
    trap-entry token to the context install. *)

Section Switcher_Spec_Install.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The continuations of [switcher_install_context_spec]. *)

  (** A fault of the installation, at the switcher's PC of offset [off],
      with the invariant of the switcher closed: the cell of the export
      table in the topmost frame is cleared, or the handler's [csp] in
      [rmap] does not allow the loads of the [ErrorState]
      ([install_skipped]); a load faults once [i] words [ls] are loaded. *)
  Definition install_nested_k (F : coPset) (cstk : CSTK) (rmap : LReg)
    (L : nat → list LWord → iProp Σ) : iProp Σ :=
    ⌜install_skipped cstk rmap⌝ -∗
    ∀ (off : Z) (rmap' : LReg) (i : nat) (ls : list LWord),
      ⌜trap_no_resume (switcher_pc off)⌝ -∗
      ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
      registers_pointsto rmap' -∗
      cstack_frag cstk -∗
      L i ls -∗
      na_own cerise_nais F -∗
      trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.

  (** The context is installed: the PC is the PCC [wpcc] of the topmost
      table with the address of the first loaded word, the registers hold
      the 15 others, and the error handler count of the topmost frame is
      incremented. *)
  Definition install_resume_k (F : coPset) (cstk : CSTK) (rmap : LReg) (wpcc : LWord)
    (L : nat → list LWord → iProp Σ) : iProp Σ :=
    ∀ ls : list LWord,
      ⌜length ls = Z.to_nat ErrorState_size⌝ -∗
      PC ↦ₚ llegalise MEPCC (resumed_pc wpcc (get_a (ls !!! 0%nat).(lw))) -∗
      registers_pointsto (error_state_install rmap (drop 1 ls)) -∗
      cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
      L (Z.to_nat ErrorState_size) ls -∗
      na_own cerise_nais F -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  (** ** Auxiliary lemma *)

  (** A fault of the installation, at the switcher's PC of offset [off],
      once the closing of the invariant of the switcher is ready: the
      registers are rebuilt from any fifteen words. *)
  #[local] Lemma switcher_install_nested_finish
    (F : coPset) (cstk : CSTK) (off : Z) (rmap : LReg) (L : nat → list LWord → iProp Σ)
    (i : nat) (ls : list LWord)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume (switcher_pc off) ->
    install_skipped cstk rmap ->

    ([∗ map] k↦y ∈ delete ca5 (delete ca4 (delete ca3 (delete ca2 (delete ca1 (delete ca0
       (delete cs1 (delete cs0 (delete ct2 (delete ct1 (delete ct0 (delete ctp (delete cgp
       (delete csp (delete cra rmap)))))))))))))), k ↦ᵣ y) ∗
    cra ↦ᵣ wcra ∗
    csp ↦ᵣ wcsp ∗
    cgp ↦ᵣ wcgp ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca2 ↦ᵣ wca2 ∗
    ca3 ↦ᵣ wca3 ∗
    ca4 ↦ᵣ wca4 ∗
    ca5 ↦ᵣ wca5 ∗
    (|={⊤}=> na_own cerise_nais F) ∗
    cstack_frag cstk ∗
    L i ls ∗
    install_nested_k F cstk rmap L
    ⊢ trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hfull Hno_resume Hskipped)
      "(Hrmap & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hclose & Hcstk & HL & Hnested)".
    iApply trap_safe_fupd. iSplitL; last (iNext; by iIntros).
    iMod "Hclose" as "Hna". iModIntro.
    iDestruct (error_state_install_pointsto with
                "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
      as "Hrmap".
    iApply ("Hnested" with "[//] [//] [] Hrmap Hcstk HL Hna").
    iPureIntro. by apply error_state_install_full.
  Qed.

  (** ** The installation *)

  (** From the handler's return, with [ca0] zero, for the call stack
      [cstk] whose topmost table has the PCC [wpcc], at a token [F] that
      contains the switcher's invariant and the trap-entry part: the
      [ErrorState] is read at the handler's [csp] through the accessor,
      and the context it holds is resumed, or a load faults. *)
  Lemma switcher_install_context_spec
    (Nswitcher : namespace) (F : coPset) (cstk : CSTK) (rmap : LReg) (wpcc : LWord)
    (L : nat → list LWord → iProp Σ) :
    ↑Nswitcher ⊆ F ->
    ↑N_trap ⊆ F ->
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    nonZero (rmap !!! ca0).(lw) = false ->

    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_return" ∗
    registers_pointsto rmap ∗
    na_own cerise_nais F ∗
    cstack_frag cstk ∗
    top_export_tbl cstk ↦ₐ□ wpcc ∗
    L 0 [] ∗
    (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
       ⌜rmap !!! csp = WCap true p g b e a @@? π⌝ -∗
       ⌜readAllowed p = true ∧ (b <= a)%a⌝ -∗
       cells_load_acc L p e a π (Z.to_nat ErrorState_size)) ∗
    ▷ ( install_nested_k F cstk rmap L ∧
        install_resume_k F cstk rmap wpcc L )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HF HFtrap Hdisj Hfull Hnz)
      "(#Hinv_switcher & #Hstatic & HPC & Hrmap & Hna & Hcstk & #Hpcc & HL & Hacc & Hpost)".
    iPoseProof "Hstatic" as "(#Hcode & _ & _)".
    iMod (na_inv_acc with "Hinv_switcher Hna") as "(Hswitcher_inv & Hna & Hclose)";
      [done | done |].
    iModNamed switcher_inv_open "Hswitcher_inv".
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iDestruct (tstack_save_area_length with "Hsave_area") as %Hsave_len.
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    rewrite /registers_pointsto.
    getRegValList [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca0;ca1;ca2;ca3;ca4;ca5].
    iExtractList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca0;ca1;ca2;ca3;ca4;ca5]
      as ["Hcra";"Hcsp";"Hcgp";"Hctp";"Hct0";"Hct1";"Hct2";"Hcs0";"Hcs1";
          "Hca0";"Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].
    assert (rmap !!! ca0 = wca0) as Hrmap_ca0 by (rewrite lookup_total_alt Hwca0; done).
    assert (rmap !!! csp = wcsp) as Hrmap_csp by (rewrite lookup_total_alt Hwcsp; done).
    rewrite Hrmap_ca0 in Hnz. rewrite Hrmap_csp.

    (* [.Lhandle_error_handler_return]: the handler's return, with [ca0] zero *)
    iApply (handle_error_handler_return_spec with "[- $HPC $Hca0 $Hcode]").
    iNext; iSplit.
    { iIntros (Hnz') "_". by rewrite Hnz in Hnz'. }
    iIntros (_) "(HPC & Hca0)".

    (* The close of the switcher invariant, for any content of the register
       save area and any error handler count of the topmost frame *)
    iAssert (∀ (save' : list LWord) (n' : Z),
               mtdc ↦ₛᵣ tstack_cap -∗
               [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save' ]] -∗
               (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a
                 ↦ₐ WInt (tstack_frameoffset (length cstk.(cstk_frames))) -∗
               cstack_full (cstack_set_top_count cstk n') -∗
               cstack_interp (cstack_set_top_count cstk n') a_tstk -∗
               na_own cerise_nais (F ∖ ↑Nswitcher)
               ={⊤}=∗
               na_own cerise_nais F)%I
      with "[HthreadID Htstk Hclose]" as "Hclose".
    { iIntros (save' n') "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Hna".
      iApply ("Hclose" with "[- $Hna]").
      iNext. rewrite /switcher_inv /tstack_cap /tstack_save_end.
      iExists a_tstk, (cstack_set_top_count cstk n'), _, tstk_next.
      rewrite cstack_set_top_count_frames_length.
      iFrame "Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hcstk_full Hstk_interp
              Hp_ot_switcher".
      iPureIntro. split; [exact Hot_bounds | by split]. }
    iAssert (cstack_full (cstack_set_top_count cstk (top_error_count cstk)))
      with "[Hcstk_full]" as "Hcstk_full"; first by rewrite cstack_set_top_count_id.

    (* The cells of the topmost frame *)
    iDestruct (cstack_interp_open_top with "Hstk_interp") as "[Htf Hstk_close]".
    iDestruct (trusted_frame_interp_open with "Htf")
      as (dq) "(Hcsp_cell & Hcell & Hcnt & %Hwcell & Htf_close)".
    iEval (fold (top_error_count cstk)) in "Hcnt".

    (* [.Lhandle_error_install_context]: the loads of the [ErrorState] and
       the count *)
    iApply (handle_error_install_context_spec (length cstk.(cstk_frames)) a_tstk
              (top_export_tbl cstk) (top_error_count cstk) save_area wpcc
              (top_tframe cstk).(tf_export_tbl) wcsp
              _ _ _ _ _ _ _ _ _ _ dq L
             with "[- $HPC $Hcsp $Hcra $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca2 $Hca3 $Hca4
                     $Hmtdc $Hframeoffset $Hcell $Hcnt $Hsave_area $Hcode $HL $Hacc]").
    { exact Hlen_cstk. }
    { exact Ha_tstk_e. }
    { exact Hsave_len. }
    { destruct Hwcell as [Hz | (Hexp & Hprov)]; [by left | by right]. }
    iSplitR; first (iIntros "_"; iExact "Hpcc").
    iNext; iSplit.
    - (* A load faults: the invariant is closed, the count unchanged *)
      iIntros (Hwhy off i ls save' Hoff Hsave')
        "(Hcsp & [%wcra_f Hcra] & [%wctp_f Hctp] & [%wct0_f Hct0] & [%wct1_f Hct1]
          & [%wct2_f Hct2] & [%wcs0_f Hcs0] & [%wcs1_f Hcs1] & [%wca2_f Hca2]
          & [%wca3_f Hca3] & [%wca4_f Hca4] & Hmtdc & Hframeoffset & Hcell & Hcnt
          & Hsave_area & HL)".
      iDestruct ("Htf_close" $! (top_error_count cstk) with "Hcsp_cell Hcell Hcnt") as "Htf".
      iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
      iSpecialize ("Hclose" with "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Hna").
      iDestruct "Hpost" as "[Hnested _]".
      iApply (switcher_install_nested_finish F cstk off rmap L i ls with
               "[$Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                 $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hclose $Hcstk $HL $Hnested]");
        [done | done |].
      (* The reason of the fault *)
      rewrite /install_skipped Hrmap_csp. exact Hwhy.
    - (* The [ErrorState] is loaded: the count is incremented *)
      iIntros (ls Hls Htbl)
        "(HPC & Hcsp & [%wcra_r Hcra] & [%wctp_r Hctp] & [%wct0_r Hct0] & Hct1 & Hct2
          & [%wcs0_r Hcs0] & [%wcs1_r Hcs1] & [%wca2_r Hca2] & [%wca3_r Hca3] & [%wca4_r Hca4]
          & Hmtdc & Hframeoffset & Hcell & Hcnt & Hsave_area & HL)".
      iMod (cstack_update _ _ (cstack_set_top_count cstk (top_error_count cstk + 1)%Z)
             with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
      iDestruct ("Htf_close" $! (top_error_count cstk + 1)%Z with "Hcsp_cell Hcell Hcnt")
        as "Htf".
      iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
      (* [.Lcommon_context_install], with the trap-entry token *)
      iDestruct (trap_entry_res_split (F ∖ ↑Nswitcher) with "Hna") as "[Htok Hna]";
        first solve_ndisj.
      iApply (common_context_install_spec with
               "[- $HPC $Hcsp $Hcra $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                   $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hsave_area $Htok $Hcode]").
      { rewrite /= length_app !length_drop Hls Hsave_len. reflexivity. }
      iNext; iIntros
        "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
          & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hsave_area & Htok)".
      (* After [mret]: the token is recombined, the invariant closed *)
      iDestruct (trap_entry_res_split (F ∖ ↑Nswitcher) with "[$Htok $Hna]") as "Hna";
        first solve_ndisj.
      iMod ("Hclose" with "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Hna") as "Hna".
      (* The registers receive words 1-15 of the [ErrorState] *)
      destruct ls as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12
                     [|w13 [|w14 [|w15 [|w16 ls] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
        rewrite /ErrorState_size /= in Hls; try lia.
      iDestruct (error_state_install_pointsto with
                  "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1
                   Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
        as "Hrmap".
      iDestruct "Hpost" as "[_ Hresume]".
      iApply ("Hresume" with "[] HPC Hrmap Hcstk HL Hna").
      iPureIntro. rewrite /ErrorState_size. reflexivity.
  Qed.

End Switcher_Spec_Install.
