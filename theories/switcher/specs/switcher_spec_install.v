From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules traps.vcsr proofmode.
From griotte Require Export logrel switcher switcher_preamble switcher_error_handler.
From griotte Require Import switcher_exception_states.
From griotte.switcher.exception Require Import common_context_install
  handle_error_install_context.
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
    The handler returns with interrupts enabled; the return disables them,
    and the posture comes back from the link. The installation opens the
    trusted-stack invariant, joins the save area of the posture with its
    word [hazardPointers], and the context install resumes the context at
    the saved MPIE. *)

Section Switcher_Spec_Install.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The continuations of [switcher_install_context_spec]. *)

  (** A fault of the installation, at the switcher's PC of offset [off],
      with the trusted-stack invariant closed, at InterruptDisabled with the
      posture: the handler's [csp] in [rmap] does not allow the loads of the
      [ErrorState] ([install_skipped]); a load faults once [i] words [ls]
      are loaded. MSHWM is unchanged, at [mshwm_v]. *)
  Definition install_nested_k (F : coPset) (cstk : CSTK) (rmap : LReg)
    (L : nat → list LWord → iProp Σ) (mshwm_v : Z) : iProp Σ :=
    ⌜install_skipped rmap⌝ -∗
    ∀ (off : Z) (rmap' : LReg) (i : nat) (ls : list LWord),
      ⌜trap_no_resume (switcher_pc off)⌝ -∗
      ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
      registers_pointsto rmap' -∗
      ◯(CSTK)[th] cstk -∗
      hwm_res cstk mshwm_v -∗
      L i ls -∗
      na_own (tpool th) F -∗
      MIE ↦ₜ[th] InterruptDisabled -∗
      held (th := th) InterruptDisabled -∗
      trap_safe (switcher_pc off) ⊤ (HO th).

  (** The context is installed: the PC is the PCC [wpcc] of the topmost
      table with the address of the first loaded word, the registers hold
      the 15 others, the error handler count of the topmost frame is
      incremented, and the posture is the saved MPIE [p]. MSHWM is restored
      to its value [mshwm_v] at the installation. *)
  Definition install_resume_k (F : coPset) (cstk : CSTK) (rmap : LReg) (wpcc : LWord)
    (L : nat → list LWord → iProp Σ) (mshwm_v : Z) : iProp Σ :=
    ∀ (ls : list LWord) (p : InterruptStatus),
      ⌜length ls = Z.to_nat ErrorState_size⌝ -∗
      PC ↦ₚ[th] llegalise mepcc (resumed_pc wpcc (get_a (ls !!! 0%nat).(lw))) -∗
      registers_pointsto (error_state_install rmap (drop 1 ls)) -∗
      ◯(CSTK)[th] (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
      hwm_res cstk mshwm_v -∗
      L (Z.to_nat ErrorState_size) ls -∗
      na_own (tpool th) F -∗
      ⌜route_pre th p⌝ -∗
      MIE ↦ₜ[th] p -∗
      held (th := th) p -∗
      £ 1 -∗
      safe[th].

  (** ** Auxiliary lemmas *)

  (** Two save areas that agree from the word [hazardPointers] on agree on
      [hazardPointers] and on [mstatus]. *)
  #[local] Lemma save_area_drop16_lookup (save save' : list LWord) (k : nat) :
    drop 16 save' = drop 16 save → (16 ≤ k)%nat → save' !! k = save !! k.
  Proof.
    intros Hd Hk. replace k with (16 + (k - 16))%nat by lia. by rewrite -!lookup_drop Hd.
  Qed.

  (** A fault of the installation, at the switcher's PC of offset [off],
      once the closing of the trusted-stack invariant is ready: the
      registers are rebuilt from any fifteen words. *)
  #[local] Lemma switcher_install_nested_finish
    (F : coPset) (cstk : CSTK) (off : Z) (rmap : LReg) (L : nat → list LWord → iProp Σ)
    (i : nat) (ls : list LWord) (mshwm_v : Z)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume (switcher_pc off) ->
    install_skipped rmap ->

    regs[th] delete ca5 (delete ca4 (delete ca3 (delete ca2 (delete ca1 (delete ca0 (delete cs1 (delete cs0 (delete ct2 (delete ct1 (delete ct0 (delete ctp (delete cgp (delete csp (delete cra rmap)))))))))))))) ∗
    cra ↦ᵣ[th] wcra ∗
    csp ↦ᵣ[th] wcsp ∗
    cgp ↦ᵣ[th] wcgp ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    ca3 ↦ᵣ[th] wca3 ∗
    ca4 ↦ᵣ[th] wca4 ∗
    ca5 ↦ᵣ[th] wca5 ∗
    (|={⊤}=> na_own (tpool th) F) ∗
    ◯(CSTK)[th] cstk ∗
    hwm_res cstk mshwm_v ∗
    L i ls ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    held (th := th) InterruptDisabled ∗
    install_nested_k F cstk rmap L mshwm_v
    ⊢ trap_safe (switcher_pc off) ⊤ (HO th).
  Proof.
    iIntros (Hfull Hno_resume Hskipped)
      "(Hrmap & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hclose & Hcstk & Hhwm & HL & Hmie & Hheld
       & Hnested)".
    iApply trap_safe_fupd.
    iMod "Hclose" as "Hna". iModIntro.
    iDestruct (error_state_install_pointsto with
                "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
      as "Hrmap".
    iApply ("Hnested" with "[//] [//] [] Hrmap Hcstk Hhwm HL Hna Hmie Hheld").
    iPureIntro. by apply error_state_install_full.
  Qed.

  (** ** The installation *)

  (** From [.Lhandle_error_install_context], once the handler's return has
      disabled interrupts with [ca0] zero ([handle_error_handler_return_spec]),
      for the call stack [cstk] whose topmost table has the PCC [wpcc] and
      whose topmost frame's table word is set, at a token [F] that contains
      the trusted-stack invariant: the [ErrorState] is read at the handler's
      [csp] through the accessor, and the context it holds is resumed, or a
      load faults. The caller may hold the critical-section token, lent out
      of the posture: it gives the posture without it ([posture_lent]), a
      resource [crit_loan], a later credit (for the trusted-stack invariant), and
      a closing hook, which the installation calls
      before the [mret] and before a fault; the hook gives the token back and
      turns the source into [Lc], which the continuations receive. MSHWM
      is [mshwm_v]. *)
  Lemma switcher_install_context_spec
    (F : coPset) (cstk : CSTK) (rmap : LReg) (wpcc : LWord)
    (L : nat → list LWord → iProp Σ) (crit_loan : iProp Σ) (Lc : nat → list LWord → iProp Σ)
    (mshwm_v : Z) :
    ↑Ntstack ⊆ F ->
    (∀ r, is_Some (rmap !! r)) ->
    nonZero (rmap !!! ca0).(lw) = false ->
    (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0) ->

    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_install_context" ∗
    registers_pointsto rmap ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    posture_lent (th := th) None None None None ∗
    crit_loan ∗
    £ 1 ∗
    na_own (tpool th) F ∗
    ◯(CSTK)[th] cstk ∗
    hwm_res cstk mshwm_v ∗
    top_export_tbl cstk ↦ₐ□ wpcc ∗
    L 0 [] ∗
    (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
       ⌜rmap !!! csp = Cap p g b e a @@? π⌝ -∗
       ⌜readAllowed p = true ∧ (b <= a)%a⌝ -∗
       cells_load_acc L p e a π (Z.to_nat ErrorState_size)) ∗
    ▷ ( ∀ i ls, crit_loan -∗ L i ls ={⊤}=∗ na_own crit ⊤ ∗ Lc i ls ) ∗
    ▷ ( install_nested_k F cstk rmap Lc mshwm_v ∧
        install_resume_k F cstk rmap wpcc Lc mshwm_v )
    ⊢ safe[th].
  Proof.
    iIntros (HF Hfull Hnz Htbl_set)
      "(#Hinv_switcher & #Hstatic & HPC & Hrmap & Hmie & Hposture & Hcrit_loan & Hlc_inv & Hna
       & Hcstk & Hhwm & #Hpcc & HL & Hacc & Hhook & Hpost)".
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hhwm_ord) #Hts]".
    iEval (rewrite /switcher_static) in "Hstatic".
    iNamed "Hstatic".
    iRename "Hswitcher_code" into "Hcode".
    iDestruct "Hhwm_base" as (hb_s es_s) "[#Hhb_s #Hts_s]".
    iDestruct (thread_stack_bounds_agree with "Hts_s Hts") as %[-> _].
    iMod (na_inv_acc with "Hinv_switcher Hna") as "(Hswitcher_inv & Hna & Hclose)";
      [done | done |].
    iModNamed trusted_stack_inv_open "Hswitcher_inv".
    iMod (lc_fupd_elim_later with "Hlc_inv Hstk_interp") as "Hstk_interp".
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    rewrite /registers_pointsto.
    getRegValList [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca0;ca1;ca2;ca3;ca4;ca5].
    iExtractList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca0;ca1;ca2;ca3;ca4;ca5]
      as ["Hcra";"Hcsp";"Hcgp";"Hctp";"Hct0";"Hct1";"Hct2";"Hcs0";"Hcs1";
          "Hca0";"Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].
    assert (rmap !!! ca0 = wca0) as Hrmap_ca0 by (rewrite lookup_total_alt Hwca0; done).
    assert (rmap !!! csp = wcsp) as Hrmap_csp by (rewrite lookup_total_alt Hwcsp; done).
    rewrite Hrmap_ca0 in Hnz. rewrite Hrmap_csp.

    (* The save area of the posture, joined with [hazardPointers] *)
    iDestruct "Hposture"
      as "[(%vepcc & %vcause & %vtval & %vmpie & _ & _ & _ & _ & HU & Hvol) Hpart]".
    iEval (rewrite posture_part_user //) in "Hpart".
    iDestruct "Hpart" as "[(%ws & %Hws_ok & (%hb20 & %Hws20 & #Hhb20) & Hholed) Hlent]".
    iDestruct (hwm_base_agree with "Hhb20 Hhb_s") as %->.
    iDestruct (save_area_join with "[$Hholed $Hhazard_cell]") as "Hsave_area".
    set (save_area := <[Z.to_nat TrustedStack_offset_hazardPointers :=
                         lword_of_word hazard_slots_cap]> ws).
    iDestruct (tstack_save_area_length with "Hsave_area") as %Hsave_len.
    assert (length ws = 21%nat) as Hws_len.
    { by rewrite /save_area length_insert in Hsave_len. }
    (* The save area with MSHWM, as the installation stores it *)
    set (save1 := <[Z.to_nat TrustedStack_offset_mshwm := lword_of_word (WInt mshwm_v)]> save_area).
    (* A save area that agrees with [save1] from [hazardPointers] on goes
       back into the posture *)
    assert (∀ save' : list LWord, drop 16 save' = drop 16 save1 →
              save' !! Z.to_nat TrustedStack_offset_hazardPointers =
                Some (lword_of_word hazard_slots_cap) ∧ saved_mie_ok save' ∧
              save' !! 20%nat = Some (lword_of_word (WInt (cstk_hwm_base cstk))))
      as Hdrop_ok.
    { intros save' Hd. split_and!.
      - rewrite (save_area_drop16_lookup save1 save');
          [|done|rewrite /TrustedStack_offset_hazardPointers; lia].
        rewrite /save1 list_lookup_insert_ne;
          last (rewrite /TrustedStack_offset_mshwm /TrustedStack_offset_hazardPointers; lia).
        apply list_lookup_insert_eq.
        rewrite Hws_len /TrustedStack_offset_hazardPointers. lia.
      - intros w Hw. apply (saved_mie_ok_insert_hazard ws hazard_slots_cap); first done.
        rewrite -(list_lookup_insert_ne _ (Z.to_nat TrustedStack_offset_mshwm) _
                    (lword_of_word (WInt mshwm_v)));
          last (rewrite /TrustedStack_offset_mshwm /TrustedStack_offset_mstatus; lia).
        rewrite -(save_area_drop16_lookup save1 save') //.
        rewrite /TrustedStack_offset_mstatus. lia.
      - rewrite (save_area_drop16_lookup save1 save'); [|done|lia].
        rewrite /save1 /save_area list_lookup_insert_ne;
          last (rewrite /TrustedStack_offset_mshwm; lia).
        rewrite list_lookup_insert_ne; last (rewrite /TrustedStack_offset_hazardPointers; lia).
        exact Hws20. }
    clearbody save_area.

    (* The close of the trusted-stack invariant, for any error handler count
       of the topmost frame *)
    iAssert (∀ n' : Z,
               mtdc ↦ₜ Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack -∗
               tstack_hazard_cell ↦ₐ hazard_slots_cap -∗
               (b_trusted_stack ^+ TrustedStack_offset_frameoffset)
                 ↦ₐ WInt (tstack_frameoffset (length cstk.(cstk_frames))) -∗
               cstack_full (cstack_set_top_count cstk n') -∗
               cstack_interp (cstack_set_top_count cstk n') a_tstk
               ={⊤}=∗
               na_own (tpool th) F)%I
      with "[HthreadID Hhazard_slots Htstk Hclose Hna]" as "Hclose".
    { iIntros (n') "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp".
      iApply ("Hclose" with "[- $Hna]").
      iNext. rewrite /trusted_stack_inv.
      iExists a_tstk, (cstack_set_top_count cstk n'), tstk_next.
      rewrite cstack_set_top_count_frames_length.
      iFrame "Hmtdc Hhazard_cell Hhazard_slots Hframeoffset HthreadID Htstk Hcstk_full
              Hstk_interp".
      iPureIntro. split_and!; done. }
    iAssert (cstack_full (cstack_set_top_count cstk (top_error_count cstk)))
      with "[Hcstk_full]" as "Hcstk_full"; first by rewrite cstack_set_top_count_id.

    (* The cells of the topmost frame *)
    iDestruct (cstack_interp_open_top with "Hstk_interp") as "[Htf Hstk_close]".
    iDestruct (trusted_frame_interp_open with "Htf")
      as (dq wcell) "(Hcsp_cell & Hcell & Hcnt & %Hwcell & Htf_close)".
    (* The frame's table word is set: the cell holds it *)
    destruct Hwcell as [Hz | (-> & Hexp & Hprov)]; first (exfalso; by apply Htbl_set).
    iEval (fold (top_error_count cstk)) in "Hcnt".
    iCombine "Hmshwmb Hmshwm" as "Hhwm_regs".

    (* [.Lhandle_error_install_context]: the loads of the [ErrorState] and
       the count *)
    iApply (handle_error_install_context_spec (length cstk.(cstk_frames)) a_tstk
              (top_export_tbl cstk) (top_error_count cstk) save_area wpcc
              (top_tframe cstk).(tf_export_tbl) wcsp
              _ _ _ _ _ _ _ _ _ _ dq L (cstk_hwm_base cstk) mshwm_v
             with "[- $HPC $Hcsp $Hcra $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca2 $Hca3 $Hca4
                     $Hmtdc $Hframeoffset $Hcell $Hcnt $Hsave_area $Hhwm_regs $Hcode $HL $Hacc]").
    { exact Hlen_cstk. }
    { exact Ha_tstk_e. }
    { exact Hsave_len. }
    { by right. }
    iSplitR; first (iIntros "_"; iExact "Hpcc").
    iSplitR; first by iApply hwm_closed_user.
    iNext; iSplit.
    - (* A load faults: the posture is given back, the invariant closed,
         the count unchanged *)
      iIntros (Hwhy off i ls save' Hoff Hsave' Hdrop)
        "(Hcsp & [%wcra_f Hcra] & [%wctp_f Hctp] & [%wct0_f Hct0] & [%wct1_f Hct1]
          & [%wct2_f Hct2] & [%wcs0_f Hcs0] & [%wcs1_f Hcs1] & [%wca2_f Hca2]
          & [%wca3_f Hca3] & [%wca4_f Hca4] & Hmtdc & Hframeoffset & Hcell & Hcnt
          & Hsave_area & [Hmshwmb Hmshwm] & HL) _".
      iDestruct ("Htf_close" $! (top_error_count cstk) with "Hcsp_cell Hcell Hcnt") as "Htf".
      iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
      destruct (Hdrop_ok save' Hdrop) as (Hhz' & Hok' & Hhb').
      (* The closing hook gives the token back *)
      iApply trap_safe_fupd.
      iMod ("Hhook" with "Hcrit_loan HL") as "[Hcrit HL]".
      iModIntro.
      iDestruct (handover_res_intro with "[Hcrit $HU $Hvol]") as "Hho"; first iExact "Hcrit".
      iDestruct (save_area_release with "[] Hsave_area Hho Hlent") as "[Hheld Hhazard_cell]";
        [done | done | done | by iFrame "Hhb_s" |].
      iSpecialize ("Hclose" with "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp").
      iDestruct "Hpost" as "[Hnested _]".
      iApply (switcher_install_nested_finish F cstk off rmap Lc i ls with
               "[$Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                 $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hclose $Hcstk $HL $Hmie $Hheld $Hnested
                 Hmshwmb Hmshwm]");
        [done | done | | by iFrame "Hmshwmb Hmshwm Hts"].
      (* The reason of the fault *)
      rewrite /install_skipped Hrmap_csp.
      destruct Hwhy as [Hz | Hnok]; [exfalso; by apply Htbl_set | exact Hnok].
    - (* The [ErrorState] is loaded: the count is incremented *)
      iIntros (g_tstk ls Hls Htbl)
        "(HPC & Hcsp & [%wcra_r Hcra] & [%wctp_r Hctp] & [%wct0_r Hct0] & Hct1 & Hct2
          & [%wcs0_r Hcs0] & [%wcs1_r Hcs1] & [%wca2_r Hca2] & [%wca3_r Hca3] & [%wca4_r Hca4]
          & Hmtdc & Hframeoffset & Hcell & Hcnt & Hsave_area & Hhwm_regs & HL)".
      iMod (cstack_update _ _ (cstack_set_top_count cstk (top_error_count cstk + 1)%Z)
             with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
      iDestruct ("Htf_close" $! (top_error_count cstk + 1)%Z with "Hcsp_cell Hcell Hcnt")
        as "Htf".
      iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
      set (save'' := save_area !!! 0%nat :: drop 1 ls ++ drop 16 save1).
      assert (drop 16 save'' = drop 16 save1) as Hdrop''.
      { rewrite /save''. cbn [drop]. rewrite drop_app_length' // length_drop Hls.
        by vm_compute. }
      destruct (Hdrop_ok save'' Hdrop'') as (Hhz'' & Hok'' & Hhb'').
      (* The register save area holds MSHWM, stored by the installation *)
      assert (save'' !!! Z.to_nat TrustedStack_offset_mshwm = lword_of_word (WInt mshwm_v))
        as Hret_mshwm.
      { apply list_lookup_total_correct.
        rewrite (save_area_drop16_lookup save1 save''); [|done|rewrite /TrustedStack_offset_mshwm; lia].
        apply list_lookup_insert_eq.
        rewrite Hsave_len /TrustedStack_offset_mshwm. lia. }
      assert (save'' !!! Z.to_nat TrustedStack_offset_hazardPointers =
                lword_of_word hazard_slots_cap) as Hhz_total.
      { by apply list_lookup_total_correct. }
      (* The closing hook gives the token back *)
      iMod ("Hhook" with "Hcrit_loan HL") as "[Hcrit HL]".
      iDestruct (handover_res_intro with "[Hcrit $HU $Hvol]") as "Hho"; first iExact "Hcrit".
      (* [.Lcommon_context_install], at InterruptDisabled with the posture *)
      iApply (common_context_install_spec with
               "[- $HPC $Hcsp $Hcra $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                   $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hsave_area $Hhwm_regs $Hhb_s $Hmie $Hho
                   $Hlent $Hcode]").
      { done. }
      { rewrite /save'' /= length_app !length_drop Hls /save1 length_insert Hsave_len.
        reflexivity. }
      { exact Hok''. }
      { left. rewrite Hret_mshwm /=. lia. }
      { exact Hhb''. }
      iNext; cbv zeta; rewrite Hhz_total Hret_mshwm; iIntros
        "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
          & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hhazard_cell & [Hmshwmb Hmshwm] & %Hpre
          & Hmie & Hheld & Hlc)".
      (* After [mret]: the invariant is closed *)
      iMod ("Hclose" with "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp") as "Hna".
      subst save''.
      (* The registers receive words 1-15 of the [ErrorState] *)
      destruct ls as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12
                     [|w13 [|w14 [|w15 [|w16 ls] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
        rewrite /ErrorState_size /= in Hls; try lia.
      iDestruct (error_state_install_pointsto with
                  "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1
                   Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
        as "Hrmap".
      iDestruct "Hpost" as "[_ Hresume]".
      iApply ("Hresume" with "[] HPC Hrmap Hcstk [Hmshwmb Hmshwm] HL Hna [//] Hmie Hheld Hlc").
      { iPureIntro. rewrite /ErrorState_size. reflexivity. }
      by iFrame "Hmshwmb Hmshwm Hts".
  Qed.

End Switcher_Spec_Install.
