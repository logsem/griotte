From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Export logrel switcher switcher_preamble switcher_error_handler.
From griotte Require Import switcher_exception_states switcher_exception_blocks_1
  switcher_exception_blocks_2 switcher_exception_blocks_3 switcher_exception_blocks_4
  switcher_exception_blocks_5 switcher_exception_blocks_6 switcher_call_blocks_6.
From griotte Require Import map_simpl register_tactics.

(** * Exception path of the switcher

    From the exception entry, with any register file, the switcher spills
    the interrupted context in the register save area and gives the volatile
    registers back to the state interpretation. A fault of the first spill
    of the call path (when [trap_no_resume] fails) resumes the interrupted
    context with the return values [-ENOTENOUGHSTACK] and 0, at
    [.Lswitch_just_return], a return to [cra]. Any other fault of the
    switcher forces the unwind of the faulting compartment's call: the
    switcher sets the return values and jumps to the return routine.

    A fault outside the switcher looks for an error handler in the export
    table of the topmost frame of the trusted stack ([handler_header]). With
    no handler, or for a fault of a running handler (an odd error handler
    count), or after too many faults, the unwind is forced. A stackless
    handler is invoked, with the error handler count incremented; stackful
    handlers are not supported yet: the unwind is forced. Two kinds of
    instruction of the path fault: the loads of the header through a
    cleared cell of the export table, and the [cjalr] to a word that is not
    a valid target.

    The path opens the invariant of the switcher: it needs the non-atomic
    token without [N_trap], which trap entry holds, and gives back the whole
    token, before the [cjalr]. *)

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

  (** The header of the export table of the topmost frame of [cstk]: its
      handler offsets, and its PCC and CGP when a handler may be invoked. *)
  Definition handler_header (cstk : CSTK) : iProp Σ :=
    ∃ eh ehs : Z,
      top_export_tbl cstk ↦ₕ□{stackful} eh ∗
      top_export_tbl cstk ↦ₕ□{stackless} ehs ∗
      (⌜(eh ≠ ExportTable_no_handler ∨ ehs ≠ ExportTable_no_handler) ∧
        Z.even (top_error_count cstk) = true⌝ →
         ∃ wpcc wcgp : LWord,
           top_export_tbl cstk ↦ₐ□ wpcc ∗
           (top_export_tbl cstk ^+ ExportTable_offset_cgp)%a ↦ₐ□ wcgp).

  #[global] Instance handler_header_persistent cstk : Persistent (handler_header cstk).
  Proof. rewrite /handler_header. apply _. Qed.

  (** The continuations of [switcher_exception_path_spec]. *)

  (** The forced unwind: the return routine, with the error values, and the
      call stack at any error handler count of the topmost frame. *)
  Definition path_unwind_k (F : coPset) (cstk : CSTK) (w : LWord) : iProp Σ :=
    ⌜trap_no_resume w⌝ -∗
    ∀ (n : Z) (rmap' : LReg),
      ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
      ⌜rmap' !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
      ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
      PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
      registers_pointsto rmap' -∗
      cstack_frag (cstack_set_top_count cstk n) -∗
      na_own cerise_nais F -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  (** The resumption of a fault of the first spill of the call path, with
      the resource [R_resume] that the path received in place of the
      call-stack fragment. *)
  Definition path_resume_k (F : coPset) (R_resume : iProp Σ) (rmap : LReg) (w : LWord)
    : iProp Σ :=
    ⌜¬ trap_no_resume w⌝ -∗
    ∀ rmap' : LReg,
      ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
      ⌜∀ r, r ≠ ca0 → r ≠ ca1 → rmap' !! r = rmap !! r⌝ -∗
      ⌜rmap' !! ca0 = Some (WInt ENOTENOUGHSTACK : LWord)⌝ -∗
      ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
      PC ↦ₚ switcher_label_pc ".Lswitch_just_return" -∗
      registers_pointsto rmap' -∗
      R_resume -∗
      na_own cerise_nais F -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  (** A fault of the path itself, at the switcher's PC of offset [off],
      with the invariant of the switcher closed... *)
  Definition path_nested_fault (F : coPset) (cstk : CSTK) : iProp Σ :=
    ∀ (off n : Z) (rmap' : LReg),
      ⌜trap_no_resume (switcher_pc off)⌝ -∗
      ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
      registers_pointsto rmap' -∗
      cstack_frag (cstack_set_top_count cstk n) -∗
      na_own cerise_nais F -∗
      trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.

  (** ... which only happens for a fault outside the switcher. *)
  Definition path_nested_k (F : coPset) (cstk : CSTK) (w : LWord) : iProp Σ :=
    ⌜¬ switcher_fault_pc w⌝ -∗ path_nested_fault F cstk.

  (** The stack of the caller of the topmost pushed frame, from the cursor
      of the frame's stack pointer: the switcher's spill area is below the
      cursor. *)
  Definition top_frame_stack_ok (cstk : CSTK) : Prop :=
    cstk.(cstk_frames) ≠ [] →
    ∃ b_stk e_stk a_stk : Addr,
      (top_tframe cstk).(tf_csp) = lword_of_word (WCap true RWL Local b_stk e_stk (a_stk ^+ 4)%a) ∧
      (b_stk <= a_stk)%a ∧
      is_Some (a_stk + 4)%a.

  (** The [cjalr] to a stackless handler succeeded. The table's PCC [wpcc]
      and CGP [wcgp] are loaded through the frame's capability to the
      table, which is neither deep-local nor deep-read-only: the handler
      gets the words of the table. *)
  Definition path_invoke_k (F : coPset) (cstk : CSTK) (rmap : LReg) (w : LWord) : iProp Σ :=
    ∀ (wpcc wcgp wpc : LWord) (ehs mcause mtval : Z) (regs : LReg),
      ⌜¬ switcher_fault_pc w⌝ -∗
      ⌜Z.even (top_error_count cstk) = true⌝ -∗
      ⌜top_frame_stack_ok cstk⌝ -∗
      ⌜ehs ≠ ExportTable_no_handler⌝ -∗
      ⌜mcause_ok mcause⌝ -∗
      ⌜handler_entry wpcc ehs = Some wpc⌝ -∗
      ⌜handler_invocation_regs Stackless cstk wcgp rmap mcause mtval regs⌝ -∗
      top_export_tbl cstk ↦ₐ□ wpcc -∗
      (top_export_tbl cstk ^+ ExportTable_offset_cgp)%a ↦ₐ□ wcgp -∗
      top_export_tbl cstk ↦ₕ□{stackless} ehs -∗
      PC ↦ₚ wpc -∗
      registers_pointsto regs -∗
      cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) -∗
      na_own cerise_nais F -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  (** ** Auxiliary lemmas *)

  (** The register file, after the path took fifteen registers out of
      [rmap] and gives them back. *)
  #[local] Definition regs_rebuild (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord)
    : LReg :=
    <[ca1 := wca1]> (<[ca0 := wca0]> (<[ca5 := wca5]> (<[ca4 := wca4]> (<[ca3 := wca3]>
    (<[ca2 := wca2]> (<[cs1 := wcs1]> (<[cs0 := wcs0]> (<[ct2 := wct2]> (<[ct1 := wct1]>
    (<[ct0 := wct0]> (<[ctp := wctp]> (<[cgp := wcgp]> (<[csp := wcsp]>
    (<[cra := wcra]> rmap)))))))))))))).

  #[local] Lemma regs_rebuild_full (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) →
    ∀ r, is_Some (regs_rebuild rmap wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1
                    wca0 wca1 wca2 wca3 wca4 wca5 !! r).
  Proof.
    intros Hfull r. rewrite /regs_rebuild.
    repeat (rewrite lookup_insert_is_Some'; right). apply Hfull.
  Qed.

  #[local] Lemma regs_rebuild_pointsto (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    ([∗ map] k↦y ∈ delete ca5 (delete ca4 (delete ca3 (delete ca2 (delete ca1 (delete ca0
       (delete cs1 (delete cs0 (delete ct2 (delete ct1 (delete ct0 (delete ctp (delete cgp
       (delete csp (delete cra rmap)))))))))))))), k ↦ᵣ y) -∗
    cra ↦ᵣ wcra -∗
    csp ↦ᵣ wcsp -∗
    cgp ↦ᵣ wcgp -∗
    ctp ↦ᵣ wctp -∗
    ct0 ↦ᵣ wct0 -∗
    ct1 ↦ᵣ wct1 -∗
    ct2 ↦ᵣ wct2 -∗
    cs0 ↦ᵣ wcs0 -∗
    cs1 ↦ᵣ wcs1 -∗
    ca0 ↦ᵣ wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    ca2 ↦ᵣ wca2 -∗
    ca3 ↦ᵣ wca3 -∗
    ca4 ↦ᵣ wca4 -∗
    ca5 ↦ᵣ wca5 -∗
    registers_pointsto (regs_rebuild rmap wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1
                          wca0 wca1 wca2 wca3 wca4 wca5).
  Proof.
    iIntros "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
    iInsertList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca2;ca3;ca4;ca5;ca0;ca1].
    rewrite /registers_pointsto /regs_rebuild. iFrame.
  Qed.

  (** The registers of a map over all registers but [cra], [csp], [cgp],
      [ca0], [ca1] and [ca2], and those six. *)
  #[local] Lemma regs_six_full (rmap : LReg) (wcra wcsp wcgp wca0 wca1 wca2 : LWord) :
    dom rmap = all_registers_s ∖ list_to_set [cra; csp; cgp; ca0; ca1; ca2] →
    ∀ r, is_Some ((<[cra := wcra]> (<[csp := wcsp]> (<[cgp := wcgp]> (<[ca0 := wca0]>
                   (<[ca1 := wca1]> (<[ca2 := wca2]> rmap)))))) !! r).
  Proof.
    intros Hdom r.
    destruct (decide (r ∈ (list_to_set [cra; csp; cgp; ca0; ca1; ca2] : gset RegName)))
      as [Hin | Hnin].
    - rewrite !elem_of_list_to_set !elem_of_cons elem_of_nil in Hin.
      repeat (destruct Hin as [-> | Hin]); try done;
        repeat (rewrite lookup_insert_ne; [|done]); by rewrite lookup_insert_eq.
    - repeat (rewrite lookup_insert_is_Some'; right).
      apply elem_of_dom. rewrite Hdom. pose proof (all_registers_s_correct r). set_solver.
  Qed.

  (** Insert those six registers into such a map. *)
  #[local] Lemma regs_six_insert (rmap : LReg) (wcra wcsp wcgp wca0 wca1 wca2 : LWord) :
    dom rmap = all_registers_s ∖ list_to_set [cra; csp; cgp; ca0; ca1; ca2] →
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    cra ↦ᵣ wcra -∗
    csp ↦ᵣ wcsp -∗
    cgp ↦ᵣ wcgp -∗
    ca0 ↦ᵣ wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    ca2 ↦ᵣ wca2 -∗
    registers_pointsto (<[cra := wcra]> (<[csp := wcsp]> (<[cgp := wcgp]> (<[ca0 := wca0]>
                          (<[ca1 := wca1]> (<[ca2 := wca2]> rmap)))))).
  Proof.
    iIntros (Hdom) "Hm Hcra Hcsp Hcgp Hca0 Hca1 Hca2".
    assert (∀ r, r ∈ [cra; csp; cgp; ca0; ca1; ca2] → rmap !! r = None) as Hnone.
    { intros r Hr. apply not_elem_of_dom. rewrite Hdom.
      apply not_elem_of_difference; right. by apply elem_of_list_to_set. }
    rewrite /registers_pointsto.
    rewrite big_sepM_insert; last (rewrite ?lookup_insert_ne //; apply Hnone; set_solver).
    iFrame "Hcra".
    rewrite big_sepM_insert; last (rewrite ?lookup_insert_ne //; apply Hnone; set_solver).
    iFrame "Hcsp".
    rewrite big_sepM_insert; last (rewrite ?lookup_insert_ne //; apply Hnone; set_solver).
    iFrame "Hcgp".
    rewrite big_sepM_insert; last (rewrite ?lookup_insert_ne //; apply Hnone; set_solver).
    iFrame "Hca0".
    rewrite big_sepM_insert; last (rewrite ?lookup_insert_ne //; apply Hnone; set_solver).
    iFrame "Hca1".
    rewrite big_sepM_insert; last (apply Hnone; set_solver).
    iFrame "Hca2 Hm".
  Qed.

  (** The cause word of the register save area after the spill. *)
  #[local] Lemma exception_spill_cause save wmepcc wregs wst wcause :
    length save = 21%nat →
    length wregs = 15%nat →
    exception_spill save wmepcc wregs wst wcause !!! 18%nat = wcause.
  Proof.
    intros Hsave Hregs.
    apply list_lookup_total_correct.
    rewrite /exception_spill lookup_cons.
    rewrite lookup_app_r; last lia. rewrite Hregs.
    rewrite lookup_app_r; last (rewrite length_take length_drop; lia).
    rewrite length_take length_drop Hsave /=. reflexivity.
  Qed.

  (** The stack pointer of the topmost pushed frame is a capability whose
      cursor is in its bounds. *)
  #[local] Lemma cstack_interp_top_csp (cstk : CSTK) (a_tstk : Addr) :
    cstack_interp cstk a_tstk -∗
    ⌜cstk.(cstk_frames) ≠ [] →
     ∃ (p : Perm) (g : Locality) (b e a : Addr),
       (top_tframe cstk).(tf_csp) = lword_of_word (WCap true p g b e a) ∧
       (b <= a)%a ∧ (a <= e)%a ∧
       disjoint_from_heap b e⌝.
  Proof.
    destruct cstk as [ef [|frm frms] ]; first by iIntros "_ %".
    rewrite /cstack_interp /=.
    iIntros "[_ Hcf]". iNamed "Hcf". iDestruct "Hcf" as (b_stk e_stk a_stk) "Hcf". iNamed "Hcf".
    destruct Hcf_csp as (Hcsp & Hba & Hae & [a4 Ha4] & _ & Hheap & _).
    iPureIntro. intros _. rewrite /top_tframe /= Hcsp.
    eexists _, _, b_stk, e_stk, (a_stk ^+ 4)%a. split_and!; [done | solve_addr.. | done].
  Qed.

  (** The stack of the caller of the topmost pushed frame. *)
  #[local] Lemma cstack_interp_top_stack (cstk : CSTK) (a_tstk : Addr) :
    cstack_interp cstk a_tstk -∗
    ⌜top_frame_stack_ok cstk⌝.
  Proof.
    destruct cstk as [ef [|frm frms] ]; first by iIntros "_ %".
    rewrite /cstack_interp /=.
    iIntros "[_ Hcf]". iNamed "Hcf". iDestruct "Hcf" as (b_stk e_stk a_stk) "Hcf". iNamed "Hcf".
    destruct Hcf_csp as (Hcsp & Hba & _ & Ha4 & _).
    iPureIntro. intros _. rewrite /top_tframe /= Hcsp.
    by exists b_stk, e_stk, a_stk.
  Qed.

  (** The cells of a frame of the trusted stack: the cell of the export
      table, of any fraction, is cleared or holds a capability to the table,
      without identifier. *)
  #[local] Lemma trusted_frame_interp_open (entry : bool) (tf : trusted_frame) (a_tstk : Addr) :
    trusted_frame_interp entry tf a_tstk -∗
    ∃ (wcell : LWord) (dq : dfrac),
      (a_tstk ^+ TrustedStackFrame_offset_csp)%a ↦ₐ tf.(tf_csp) ∗
      (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a ↦ₐ{dq} wcell ∗
      (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a ↦ₐ WInt tf.(tf_error_count) ∗
      ⌜wcell = lword_of_word (WInt 0) ∨
       (wcell = tf.(tf_export_tbl) ∧
        exp_tbl_cap (tf_export_tbl_b tf) wcell.(lw) ∧ wcell.(lprov) = None)⌝ ∗
      (∀ n : Z,
         (a_tstk ^+ TrustedStackFrame_offset_csp)%a ↦ₐ tf.(tf_csp) -∗
         (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a ↦ₐ{dq} wcell -∗
         (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a ↦ₐ WInt n -∗
         trusted_frame_interp entry (tf_set_count tf n) a_tstk).
  Proof.
    rewrite /trusted_frame_interp.
    iIntros "Htf". iNamed "Htf".
    destruct entry.
    - iDestruct "Htf_tbl" as "[#Htbl %Hok]".
      iExists _, DfracDiscarded. iFrame "Htf_csp Htbl Htf_cnt".
      iSplit; first (iPureIntro; right; split; [done | exact Hok]).
      iIntros (n) "Hcsp _ Hcnt". iFrame "Hcsp Hcnt". iPureIntro. exact Hok.
    - iDestruct "Htf_tbl" as (w) "[Htbl %Hw]".
      iExists w, (DfracOwn 1). iFrame "Htf_csp Htbl Htf_cnt".
      iSplit.
      { iPureIntro.
        destruct Hw as [-> | [-> Hok] ]; [by left | right; split; [done | exact Hok] ]. }
      iIntros (n) "Hcsp Htbl Hcnt". iFrame "Hcsp Hcnt". iExists w. iFrame "Htbl".
      iPureIntro. exact Hw.
  Qed.

  (** The forced unwind, from [.Lcommon_force_unwind], once the closing of
      the invariant of the switcher is ready. *)
  #[local] Lemma switcher_exception_unwind_finish
    (F : coPset) (cstk : CSTK) (n : Z) (rmap : LReg) (w : LWord)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume w ->

    PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
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
    switcher_code ∗
    (|={⊤}=> na_own cerise_nais F) ∗
    cstack_frag (cstack_set_top_count cstk n) ∗
    path_unwind_k F cstk w
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfull Hno_resume)
      "(HPC & Hrmap & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & #Hswitcher & Hclose & Hcstk & Hunwind)".
    iApply (switcher_call_block_18_spec with "[- $HPC $Hca0 $Hca1 $Hswitcher]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iMod "Hclose" as "Hna".
    iDestruct (regs_rebuild_pointsto with
                "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
      as "Hrmap".
    iApply ("Hunwind" with "[//] [] [] [] HPC Hrmap Hcstk Hna").
    - iPureIntro. by apply regs_rebuild_full.
    - iPureIntro. rewrite /regs_rebuild lookup_insert_ne //. apply lookup_insert_eq.
    - iPureIntro. rewrite /regs_rebuild. apply lookup_insert_eq.
  Qed.

  (** A fault of the path, at the switcher's PC of offset [off], once the
      closing of the invariant of the switcher is ready. *)
  #[local] Lemma switcher_exception_nested_finish
    (F : coPset) (cstk : CSTK) (off n : Z) (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume (switcher_pc off) ->

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
    cstack_frag (cstack_set_top_count cstk n) ∗
    path_nested_fault F cstk
    ⊢ trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hfull Hno_resume)
      "(Hrmap & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hclose & Hcstk & Hnested)".
    iApply trap_safe_fupd. iSplitL; last (iNext; by iIntros).
    iMod "Hclose" as "Hna". iModIntro.
    iDestruct (regs_rebuild_pointsto with
                "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
      as "Hrmap".
    iApply ("Hnested" with "[//] [] Hrmap Hcstk Hna").
    iPureIntro. by apply regs_rebuild_full.
  Qed.

  (** ** The exception path *)

  (** From the exception entry, for a fault at [w] with the registers [rmap]
      and the call stack [cstk], the path reaches one of its four
      continuations: the forced unwind, the resumption of a fault of the
      first spill of the call path, a fault of the path itself, and the
      invocation of a stackless handler. The header of the table of the
      topmost frame is needed for a fault outside the switcher. *)
  Lemma switcher_exception_path_spec
    (Nswitcher : namespace) (F : coPset) (cstk : CSTK) (R_resume : iProp Σ) (rmap : LReg)
    (w : LWord) :
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
    (if decide (trap_no_resume w) then cstack_frag cstk else R_resume) ∗
    (⌜¬ switcher_fault_pc w⌝ → handler_header cstk) ∗
    ▷ ( path_unwind_k F cstk w ∧
        path_resume_k F R_resume rmap w ∧
        path_nested_k F cstk w ∧
        path_invoke_k F cstk rmap w )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant, with the token without [N_trap];
       - [switcher_exception_blocks_21_23_spec]: spill the registers, MEPCC,
         mstatus and mcause, and give the volatile registers back;
       - [switcher_exception_blocks_24_36_spec]: restore mtdc, and test for
         a fault of the switcher, and of the first spill of the call path;
       - for any other fault of the switcher, [switcher_call_block_18_spec]:
         set the return values; for a fault of the first spill,
         [switcher_context_install_spec]: install the context, with the
         return values overwritten;
       - for a fault outside the switcher, [switcher_handler_lookup_spec]:
         look for a handler in the export table of the topmost frame;
         [switcher_handler_found_spec]: count the fault, update the logical
         call stack, compute the handler's PC and CGP; then the setup and
         the invocation of a stackless handler;
       - close the switcher invariant, and recombine the token. *)
    iIntros (HF HFtrap Hdisj Hfull)
      "(#Hinv_switcher & #Hstatic & HPC & Hrmap & Hout & Hna & Hcstk & #Hheader & Hpost)".
    iPoseProof "Hstatic" as "(#Hcode & _ & %Hmtcc)".
    rewrite Hmtcc.
    iMod (na_inv_acc with "Hinv_switcher Hna") as "(Hswitcher_inv & Hna & Hclose)";
      [done | solve_ndisj |].
    iModNamed switcher_inv_open "Hswitcher_inv".
    (* The call stack of the invariant is [cstk], unless the fault is
       resumed *)
    iAssert ⌜trap_no_resume w → cstk' = cstk⌝%I as %Hcstk_eq.
    { destruct (decide (trap_no_resume w)) as [Hno | Hno].
      - iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->. done.
      - iPureIntro. by intros. }
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

    (* Blocks 24 and 36: [.Lhandle_error] *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    (* The close of the switcher invariant, and the recombination of the
       token, for any content of the register save area and any error
       handler count of the topmost frame *)
    iAssert (∀ (save' : list LWord) (n' : Z),
               mtdc ↦ₛᵣ tstack_cap -∗
               [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save' ]] -∗
               (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a
                 ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) -∗
               cstack_full (cstack_set_top_count cstk' n') -∗
               cstack_interp (cstack_set_top_count cstk' n') a_tstk -∗
               trap_entry_res
               ={⊤}=∗
               na_own cerise_nais F)%I
      with "[HthreadID Htstk Hclose Hna]" as "Hclose".
    { iIntros (save' n') "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Htok".
      iMod ("Hclose" with
             "[Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hcstk_full Hstk_interp $Hna]")
        as "Hna".
      { iNext. rewrite /switcher_inv /tstack_cap /tstack_save_end.
        iExists a_tstk, (cstack_set_top_count cstk' n'), _, tstk_next.
        rewrite cstack_set_top_count_frames_length.
        iFrame "∗ # %". iPureIntro. by split. }
      iModIntro.
      iApply (trap_entry_res_split F with "[$Htok $Hna]"); first done. }
    iAssert (cstack_full (cstack_set_top_count cstk' (top_error_count cstk')))
      with "[Hcstk_full]" as "Hcstk_full"; first by rewrite cstack_set_top_count_id.
    iApply (switcher_exception_blocks_24_36_spec _ _ _ (lmepcc_of_pc w) with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hctp $Hca0 $Hca1 $Hct2 $Hmtdc $Hsave_area
                 $Hframeoffset $Hcode]").
    { exact Hlen_cstk. }
    { by apply exception_spill_length. }
    { done. }
    iNext; iSplit; [|iSplit].
    - (* Any other fault of the switcher: the forced unwind *)
      iIntros (Hswitcher_fault wct0' wct1' wctp')
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hsave_area
          & Hframeoffset & _)".
      pose proof (Hcstk_eq (or_intror (proj2 Hswitcher_fault))) as Heq_cstk; subst cstk'.
      rewrite decide_True; last exact (or_intror (proj2 Hswitcher_fault)).
      iSpecialize ("Hclose" with "Hmtdc Hsave_area Hframeoffset Hcstk_full [Hstk_interp] Htok").
      { by rewrite cstack_set_top_count_id. }
      iDestruct "Hpost" as "[Hunwind _]".
      iApply (switcher_exception_unwind_finish _ _ (top_error_count cstk) with
               "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                 $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hclose $Hunwind Hcstk]");
        [done | right; apply Hswitcher_fault |].
      by rewrite cstack_set_top_count_id.
    - (* A fault of the first spill of the call path: the context install
         resumes the interrupted context *)
      iIntros (Hresume wct0' wct1' wctp')
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hsave_area
          & Hframeoffset & _)".
      iApply (switcher_context_install_spec with
               "[- $HPC $Hcsp $Hcra $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                   $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hsave_area $Htok $Hcode]").
      { rewrite !length_insert. by apply exception_spill_length. }
      iNext; iIntros
        "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
          & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hsave_area & Htok & _)".
      (* The PC to resume is a valid PC: MEPCC keeps it *)
      rewrite (_ : llegalise MEPCC (switcher_label_pc ".Lswitch_just_return") =
                   switcher_label_pc ".Lswitch_just_return"); last reflexivity.
      iMod ("Hclose" with "Hmtdc Hsave_area Hframeoffset Hcstk_full [Hstk_interp] Htok") as "Hna".
      { by rewrite cstack_set_top_count_id. }
      rewrite /exception_spill /TrustedStack_offset_ca0 /TrustedStack_offset_ca1 /=.
      (* The other registers get their words back: the register map is the
         original one, with the return values inserted last *)
      iInsertList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca2;ca3;ca4;ca5;ca0;ca1].
      rewrite (insert_id _ _ _ Hwcra) (insert_id _ _ _ Hwcsp) (insert_id _ _ _ Hwcgp)
        (insert_id _ _ _ Hwctp) (insert_id _ _ _ Hwct0) (insert_id _ _ _ Hwct1)
        (insert_id _ _ _ Hwct2) (insert_id _ _ _ Hwcs0) (insert_id _ _ _ Hwcs1)
        (insert_id _ _ _ Hwca2) (insert_id _ _ _ Hwca3) (insert_id _ _ _ Hwca4)
        (insert_id _ _ _ Hwca5).
      assert (¬ trap_no_resume w) as Hresume'.
      { destruct Hresume as [Hb Ha]. by intros [Hb' | Ha']. }
      rewrite decide_False; last exact Hresume'.
      iDestruct "Hpost" as "[_ [Hresume_k _] ]".
      iApply ("Hresume_k" with "[] [] [] [] [] HPC Hrmap Hcstk Hna").
      + done.
      + iPureIntro. intros r.
        repeat (rewrite lookup_insert_is_Some'; right).
        apply Hfull.
      + iPureIntro. intros r Hr0 Hr1. rewrite !lookup_insert_ne //.
      + iPureIntro. rewrite lookup_insert_ne //. apply lookup_insert_eq.
      + iPureIntro. apply lookup_insert_eq.
    - (* A fault outside the switcher: the lookup of an error handler *)
      iIntros (Hnot_in wct1')
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hsave_area
          & Hframeoffset & _)".
      assert (¬ switcher_fault_pc w) as Hnot_switcher by exact Hnot_in.
      assert (trap_no_resume w) as Hno_resume by (by left).
      pose proof (Hcstk_eq Hno_resume) as Heq_cstk; subst cstk'.
      rewrite decide_True; last exact Hno_resume.
      iDestruct ("Hheader" with "[//]") as (eh ehs) "(#Heh & #Hehs & #Hpcc_cgp)".
      (* The topmost frame *)
      iDestruct (cstack_interp_top_csp with "Hstk_interp") as %Hframe_csp.
      iDestruct (cstack_interp_top_stack with "Hstk_interp") as %Hframe_stack.
      pose proof (exception_spill_cause save_area (lmepcc_of_pc w)
                    [wcra; wcsp; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1; wca0;
                     wca1; wca2; wca3; wca4; wca5] wst (WInt cause) Hsave_len eq_refl)
        as Hsave'_cause.
      pose proof (exception_spill_length save_area (lmepcc_of_pc w)
                    [wcra; wcsp; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1; wca0;
                     wca1; wca2; wca3; wca4; wca5] wst (WInt cause) Hsave_len eq_refl)
        as Hsave'_len.
      remember (exception_spill save_area (lmepcc_of_pc w)
                  [wcra; wcsp; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1; wca0;
                   wca1; wca2; wca3; wca4; wca5] wst (WInt cause)) as save' eqn:Hsave'.
      iDestruct (cstack_interp_open_top with "Hstk_interp") as "[Htf Hstk_close]".
      iDestruct (trusted_frame_interp_open with "Htf")
        as (wcell dq) "(Hcsp_cell & Hcell & Hcnt & %Hwcell & Htf_close)".
      iEval (fold (top_error_count cstk)) in "Hcnt".
      (* Blocks 25-29: the lookup *)
      iApply (switcher_handler_lookup_spec cstk a_tstk (top_export_tbl cstk) eh ehs _ wcell
               with "[- $HPC $Hcsp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                       $Hcsp_cell $Hcell $Hcode]").
      { exact Hlen_cstk. }
      { exact Ha_tstk_e. }
      { exact Hframe_csp. }
      { destruct Hwcell as [-> | (_ & Hexp & Hprov)]; [by left | by right]. }
      iSplitR; first (iIntros "_"; iFrame "Heh Hehs").
      iNext; iSplit; [|iSplit].
      + (* The cell of the export table is cleared: the load of the header
           faults *)
        iIntros (Hz off Hoff)
          "(Hcsp & Hctp & [%wct0_f Hct0] & [%wct1_f Hct1] & [%wct2_f Hct2] & [%wcs0_f Hcs0]
            & [%wcs1_f Hcs1] & Hca0 & Hca1 & Hca2 & Hcsp_cell & Hcell & _)".
        iDestruct ("Htf_close" $! (top_error_count cstk) with "Hcsp_cell Hcell Hcnt") as "Htf".
        iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
        iSpecialize ("Hclose" with "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Htok").
        iDestruct "Hpost" as "(_ & _ & Hnested & _)".
        iSpecialize ("Hnested" with "[//]").
        iApply (switcher_exception_nested_finish _ _ off (top_error_count cstk) with
                 "[$Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                   $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hclose $Hnested Hcstk]");
          [done | done |].
        by rewrite cstack_set_top_count_id.
      + (* No handler: the forced unwind *)
        iIntros (_ wct0_u wct1_u wct2_u wcs0_u wcs1_u)
          "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca0 & Hca1 & Hca2
            & Hcsp_cell & Hcell & _)".
        iDestruct ("Htf_close" $! (top_error_count cstk) with "Hcsp_cell Hcell Hcnt") as "Htf".
        iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
        iSpecialize ("Hclose" with "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Htok").
        iDestruct "Hpost" as "[Hunwind _]".
        iApply (switcher_exception_unwind_finish _ _ (top_error_count cstk) with
                 "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                   $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hclose $Hunwind Hcstk]");
          [done | done |].
        by rewrite cstack_set_top_count_id.
      + (* A handler is found, at offset [off] *)
        iIntros (p g e a off z0 wct0_h wct2_h wcs1_h wca1_h wca2_h Hw Hfound)
          "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca0 & Hca1 & Hca2
            & Hcsp_cell & Hcell & _)".
        destruct Hwcell as [Hz | (Htf_tbl & Hexp & _)].
        { exfalso. rewrite Hw in Hz. by inversion Hz. }
        rewrite Hw /= in Hexp.
        assert (exp_tbl_cap (top_export_tbl cstk)
                  (WCap true p g (top_export_tbl cstk) e (top_export_tbl cstk))) as Htbl.
        { destruct Hexp as (p' & g' & e' & a' & Heq & Hread & Hbnd & Hshadow & Hdl & Hdro).
          injection Heq as <- <- <- _. by exists p, g, e, (top_export_tbl cstk). }
        (* The loads through the table's capability give the words of the table *)
        assert (∀ v, lload_word p v = v) as Hload.
        { destruct Htbl as (p' & g' & e' & a' & Heq & _ & _ & _ & Hdl & Hdro).
          injection Heq as <- _ _ _. intros v. by apply lload_word_no_dl_dro. }
        assert (eh ≠ ExportTable_no_handler ∨ ehs ≠ ExportTable_no_handler) as Hsome_handler.
        { destruct Hfound as [(_ & _ & _ & _ & Heh_some) | (_ & _ & _ & Hehs_some & _)];
            [by left | by right]. }
        (* The PCC and the CGP of the table, for an even count *)
        iAssert (∃ wpcc wcgp' : LWord,
                   ⌜Z.even (top_error_count cstk) = true⌝ →
                   top_export_tbl cstk ↦ₐ□ wpcc ∗
                   (top_export_tbl cstk ^+ ExportTable_offset_cgp)%a ↦ₐ□ wcgp')%I
          as (wpcc wcgp') "#Hcells".
        { destruct (Z.even (top_error_count cstk)) eqn:Hev.
          - iDestruct ("Hpcc_cgp" with "[]") as (wpcc wcgp') "[Hpcc Hcgp']";
              first (iPureIntro; by split).
            iExists wpcc, wcgp'. iIntros "_". iFrame "Hpcc Hcgp'".
          - iExists (WInt 0 : LWord), (WInt 0 : LWord). iIntros "%". done. }
        (* Block 30: count the fault *)
        iApply (switcher_handler_found_spec (length cstk.(cstk_frames)) a_tstk
                  (top_export_tbl cstk) e p g (top_error_count cstk) off z0 wpcc wcgp'
                 with "[- $HPC $Hctp $Hct1 $Hct2 $Hcs0 $Hcs1 $Hcra $Hcgp $Hca0 $Hcnt
                         $Hcells $Hcode]");
          [exact Hlen_cstk | exact Ha_tstk_e | exact Htbl |].
        iNext; iSplit.
        * (* An odd count, or too many faults: the forced unwind *)
          iIntros (Hcount wcra_u)
            "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcra & Hcgp & Hca0 & Hcnt & _)".
          iMod (cstack_update _ _ (cstack_set_top_count cstk (top_error_count cstk + 1)%Z)
                 with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
          iDestruct ("Htf_close" $! (top_error_count cstk + 1)%Z with "Hcsp_cell Hcell Hcnt")
            as "Htf".
          iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
          iSpecialize ("Hclose" with "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Htok").
          iDestruct "Hpost" as "[Hunwind _]".
          iApply (switcher_exception_unwind_finish _ _ (top_error_count cstk + 1)%Z with
                   "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                     $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hclose $Hunwind $Hcstk]");
            [done | done].
        * (* The setup of the handler *)
          iIntros ([Hev Hmax] lbl wct2_s wcs1_s Hlbl)
            "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcra & Hcgp & Hca0 & Hcnt & _)".
          iMod (cstack_update _ _ (cstack_set_top_count cstk (top_error_count cstk + 1)%Z)
                 with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
          iDestruct ("Htf_close" $! (top_error_count cstk + 1)%Z with "Hcsp_cell Hcell Hcnt")
            as "Htf".
          iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
          destruct Hlbl as [(Hz0 & ->) | (-> & ->)].
          -- (* Block 31: a stackless handler *)
             destruct Hfound as [(-> & _) | (_ & -> & -> & Hehs_some & _)]; first done.
             iApply (switcher_stackless_setup_spec with
                      "[- $HPC $Hcsp $Hct0 $Hca0 $Hca1 $Hca2 $Hsave_area $Hcode]");
               first exact Hsave'_len.
             iNext; iIntros (mtval) "(HPC & Hcsp & Hct0 & Hca0 & Hca1 & Hca2 & Hsave_area & _)".
             rewrite Hsave'_cause.
             (* The invariant is closed before the [cjalr] *)
             iMod ("Hclose" with "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Htok")
               as "Hna".
             (* The registers to clear *)
             iDestruct (regs_rebuild_pointsto with
                         "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2
                          Hca3 Hca4 Hca5") as "Hregs".
             set (regs1 := regs_rebuild rmap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
             assert (∀ r, is_Some (regs1 !! r)) as Hregs_full
               by (apply regs_rebuild_full, Hfull).
             rewrite /registers_pointsto.
             iDestruct (big_sepM_delete _ _ cra with "Hregs") as "[Hcra Hregs]";
               first (rewrite /regs1 /regs_rebuild ?lookup_delete_ne //;
                      repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq).
             iDestruct (big_sepM_delete _ _ csp with "Hregs") as "[Hcsp Hregs]";
               first (rewrite /regs1 /regs_rebuild ?lookup_delete_ne //;
                      repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq).
             iDestruct (big_sepM_delete _ _ cgp with "Hregs") as "[Hcgp Hregs]";
               first (rewrite /regs1 /regs_rebuild ?lookup_delete_ne //;
                      repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq).
             iDestruct (big_sepM_delete _ _ ca0 with "Hregs") as "[Hca0 Hregs]";
               first (rewrite /regs1 /regs_rebuild ?lookup_delete_ne //;
                      repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq).
             iDestruct (big_sepM_delete _ _ ca1 with "Hregs") as "[Hca1 Hregs]";
               first (rewrite /regs1 /regs_rebuild ?lookup_delete_ne //;
                      repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq).
             iDestruct (big_sepM_delete _ _ ca2 with "Hregs") as "[Hca2 Hregs]";
               first (rewrite /regs1 /regs_rebuild ?lookup_delete_ne //;
                      repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq).
             assert (dom regs1 = all_registers_s) as Hdom_regs1.
             { apply set_eq. intros r. rewrite elem_of_dom.
               split; [intros; apply all_registers_s_correct | intros; apply Hregs_full]. }
             assert (dom (delete ca2 (delete ca1 (delete ca0 (delete cgp (delete csp
                       (delete cra regs1)))))) =
                     all_registers_s ∖ list_to_set [cra; csp; cgp; ca0; ca1; ca2]) as Hdom_cleared.
             { rewrite !dom_delete_L Hdom_regs1. clear. set_solver. }
             (* Block 33: the invocation *)
             iApply (switcher_handler_invoke_spec with "[- $HPC $Hcra $Hregs $Hcode]");
               first exact Hdom_cleared.
             iNext; iSplit.
             ++ (* The [cjalr] succeeds: the handler runs *)
                iIntros (Htgt mie rmap' Hdom') "(HPC & Hcra & Hrmap' & _)".
                rewrite Hdom_cleared in Hdom'.
                rewrite !Hload in Htgt |- *.
                destruct (handler_entry wpcc ehs) as [wpc|] eqn:Hentry;
                  last first.
                { exfalso. by rewrite (handler_word_none _ _ Hentry) in Htgt. }
                rewrite (handler_word_entry _ _ _ Hentry).
                assert (lupdatePcPerm wpc = wpc) as ->.
                { revert Hentry. rewrite /handler_entry.
                  destruct wpcc as [ww ππ]. destruct_word ww; try done.
                  destruct (_ + ehs)%a; cbn; last done. intros [=<-]. done. }
                iDestruct (big_sepM_sep with "Hrmap'") as "[Hrmap' Hzero]".
                iDestruct (big_sepM_pure_1 with "Hzero") as %Hzero.
                iDestruct (regs_six_insert with "Hrmap' Hcra Hcsp Hcgp Hca0 Hca1 Hca2") as "Hrmap'";
                  first exact Hdom'.
                iDestruct ("Hcells" with "[//]") as "[Hpcc Hcgp_cell]".
                iDestruct "Hpost" as "(_ & _ & _ & Hinvoke)".
                iApply ("Hinvoke" $! wpcc wcgp' wpc ehs cause mtval with
                         "[//] [//] [//] [//] [//] [//] [] Hpcc Hcgp_cell Hehs HPC Hrmap'
                          Hcstk Hna").
                iPureIntro. rewrite /handler_invocation_regs.
                split_and!.
                ** by apply regs_six_full.
                ** exists mie. repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
                ** repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
                ** repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
                ** repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
                ** repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
                ** repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
                ** intros r Hr.
                   assert (r ≠ cra ∧ r ≠ cgp ∧ r ≠ csp ∧ r ≠ ca0 ∧ r ≠ ca1 ∧ r ≠ ca2)
                     as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hr6) by (clear -Hr; set_solver).
                   rewrite !lookup_insert_ne; try (by apply not_eq_sym).
                   assert (is_Some (rmap' !! r)) as [wr Hwr].
                   { apply elem_of_dom. rewrite Hdom'. apply elem_of_difference.
                     split; first apply all_registers_s_correct.
                     rewrite elem_of_list_to_set !elem_of_cons elem_of_nil.
                     intros [-> | [-> | [-> | [-> | [-> | [-> | [] ] ] ] ] ] ]; done. }
                   rewrite Hwr. f_equal. exact (Hzero r wr Hwr).
             ++ (* The [cjalr] faults *)
                iIntros (Htgt rmap' Hdom') "(Hcra & Hrmap' & _)".
                rewrite Hdom_cleared in Hdom'.
                iDestruct (big_sepM_sep with "Hrmap'") as "[Hrmap' _]".
                iDestruct (regs_six_insert with "Hrmap' Hcra Hcsp Hcgp Hca0 Hca1 Hca2") as "Hrmap'";
                  first exact Hdom'.
                iDestruct "Hpost" as "(_ & _ & Hnested & _)".
                iApply ("Hnested" with "[//] [] [] Hrmap' Hcstk Hna").
                { iPureIntro. apply trap_no_resume_switcher_pc. by vm_compute. }
                iPureIntro. by apply regs_six_full.
          -- (* Block 32: a stackful handler, not supported yet *)
             iApply (switcher_stack_setup_placeholder_spec with "[- $HPC $Hcode]").
             iNext; iIntros "(HPC & _)".
             iSpecialize ("Hclose" with
                           "Hmtdc Hsave_area Hframeoffset Hcstk_full Hstk_interp Htok").
             iDestruct "Hpost" as "[Hunwind _]".
             iApply (switcher_exception_unwind_finish _ _ (top_error_count cstk + 1)%Z with
                      "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                        $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hclose $Hunwind $Hcstk]");
               [done | done].
  Qed.

End Switcher_Spec_Exception.
