From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules traps.vcsr proofmode.
From griotte Require Export logrel switcher switcher_preamble switcher_error_handler.
From griotte Require Import switcher_exception_states copy_context_spec switcher_registers.
From griotte.switcher.failure Require Import common_force_unwind.
From griotte.switcher.exception Require Import exception_entry handle_error
  common_context_install handle_error_stack_oob handle_error_found handle_error_stack_setup
  handle_error_handler_invoke.
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
    count), or after too many faults, the unwind is forced. Otherwise the
    handler is invoked, with the error handler count incremented. Before a
    stackful handler, the switcher writes the [ErrorState] below the
    faulting [csp]: the path performs these stores through a destination
    resource [error_state_written] and a store accessor ([path_es_acc])
    that the caller provides; [error_state_written i] holds once [i] words
    are written, and every continuation gets the destination back. Three
    kinds of instruction of the path fault: the loads of the header
    through a cleared cell of the export table, the stores of the
    [ErrorState] (the first one, or the one at the end of the faulting
    [csp]), and the [cjalr] to a word that is not a valid target.

    The path runs at InterruptDisabled, with the whole posture of the
    thread from the trap vector: it joins the save area of the posture with
    the word [hazardPointers] of the trusted-stack invariant, which it
    opens, and gives the posture back (the save area but that word) before
    it closes the invariant. A handler is invoked with interrupts enabled:
    the posture goes into the link. *)

(** The word [hazardPointers] of the register save area, after the spill
    of the exception entry and the stores of the return values. *)
Ltac save_area_hazard :=
  repeat (rewrite list_lookup_insert_ne; last by vm_compute);
  try match goal with
      | H : ?l = exception_spill _ _ _ _ _ |- context [?l !! _] => is_var l; rewrite H
      end;
  rewrite exception_spill_hazard //.

Section Switcher_Spec_Exception.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The header of the export table of the topmost frame of [cstk]: the
      frame's table word is set (not [WInt 0]), the table's handler offsets,
      and its PCC and CGP when a handler may be invoked. *)
  Definition handler_header (cstk : CSTK) : iProp Σ :=
    ⌜(top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)⌝ ∗
    ∃ eh ehs : Z,
      top_export_tbl cstk ↦ₑ□{stackful} eh ∗
      top_export_tbl cstk ↦ₑ□{stackless} ehs ∗
      (⌜(eh ≠ ExportTable_no_handler ∨ ehs ≠ ExportTable_no_handler) ∧
        Z.even (top_error_count cstk) = true⌝ →
         ∃ wpcc wcgp : LWord,
           top_export_tbl cstk ↦ₐ□ wpcc ∗
           (top_export_tbl cstk ^+ ExportTable_offset_cgp) ↦ₐ□ wcgp).

  #[global] Instance handler_header_persistent cstk : Persistent (handler_header cstk).
  Proof. rewrite /handler_header. apply _. Qed.

  (** The stores of the [ErrorState] for a stackful handler: when the
      fault is outside the switcher, the count of the topmost frame even,
      its table declares a stackful handler, and the switcher's first store
      through the faulting [csp] succeeds, the destination
      [error_state_written] takes the words of [error_state_src] below the
      cursor of [csp], each one below the end of [csp]. *)
  Definition path_es_acc (cstk : CSTK) (w : LWord) (rmap : LReg)
    (error_state_written : nat → iProp Σ) : iProp Σ :=
    □ ∀ (eh : Z) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
      ⌜¬ switcher_fault_pc w⌝ -∗
      ⌜Z.even (top_error_count cstk) = true⌝ -∗
      top_export_tbl cstk ↦ₑ□{stackful} eh -∗
      ⌜eh ≠ ExportTable_no_handler⌝ -∗
      ⌜rmap !!! csp = Cap p g b e a @@? π⌝ -∗
      ⌜error_state_first_store_ok (rmap !!! csp)⌝ -∗
      cells_store_acc error_state_written p e (a ^+ (- ErrorState_size)) π
        (error_state_src w rmap).

  #[global] Instance path_es_acc_persistent cstk w rmap error_state_written :
    Persistent (path_es_acc cstk w rmap error_state_written).
  Proof. rewrite /path_es_acc. apply _. Qed.

  (** The continuations of [switcher_exception_path_spec]. *)

  (** The forced unwind: the return routine, with the error values, and the
      call stack at any error handler count of the topmost frame. The
      stackful handler was not invoked for the fault at [w] with the
      registers [rmap]. *)
  Definition path_unwind_k (F : coPset) (cstk : CSTK) (w : LWord) (rmap : LReg)
    (error_state_written : nat → iProp Σ) : iProp Σ :=
    ⌜trap_no_resume w⌝ -∗
    handler_skipped cstk w rmap -∗
    ∀ (n : Z) (rmap' : LReg),
      ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
      ⌜rmap' !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
      ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
      PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_return -∗
      registers_pointsto rmap' -∗
      ◯(CSTK)[th] (cstack_set_top_count cstk n) -∗
      error_state_written 0 -∗
      na_own (tpool th) F -∗
      MIE ↦ₜ[th] InterruptDisabled -∗
      held (th := th) InterruptDisabled -∗
      safe[th].

  (** The resumption of a fault of the first spill of the call path, with
      the resource [R_resume] that the path received in place of the
      call-stack fragment, at the posture [b] of the fault. *)
  Definition path_resume_k (F : coPset) (R_resume : iProp Σ) (rmap : LReg) (w : LWord)
    (b : InterruptStatus) (error_state_written : nat → iProp Σ) : iProp Σ :=
    ⌜¬ trap_no_resume w⌝ -∗
    ⌜th ≠ CtxSwitch⌝ -∗
    ∀ rmap' : LReg,
      ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
      ⌜∀ r, r ≠ ca0 → r ≠ ca1 → rmap' !! r = rmap !! r⌝ -∗
      ⌜rmap' !! ca0 = Some (WInt ENOTENOUGHSTACK : LWord)⌝ -∗
      ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
      PC ↦ₚ[th] switcher_label_pc ".Lswitch_just_return" -∗
      registers_pointsto rmap' -∗
      R_resume -∗
      error_state_written 0 -∗
      na_own (tpool th) F -∗
      MIE ↦ₜ[th] b -∗
      held (th := th) b -∗
      £ 1 -∗
      safe[th].

  (** A fault of the path itself, at the switcher's PC of offset [off],
      with the trusted-stack invariant closed, after [k] stores of the
      [ErrorState], at a posture [m], and the stackful handler not invoked
      for the fault at [w] with the registers [rmap]... *)
  Definition path_nested_fault (F : coPset) (cstk : CSTK) (w : LWord) (rmap : LReg)
    (error_state_written : nat → iProp Σ) : iProp Σ :=
    handler_skipped cstk w rmap -∗
    ∀ (off n : Z) (rmap' : LReg),
      ⌜trap_no_resume (switcher_pc off)⌝ -∗
      ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
      registers_pointsto rmap' -∗
      ◯(CSTK)[th] (cstack_set_top_count cstk n) -∗
      (∃ k : nat, ⌜(k <= Z.to_nat ErrorState_size)%nat⌝ ∗ error_state_written k) -∗
      na_own (tpool th) F -∗
      ∀ m : InterruptStatus,
      MIE ↦ₜ[th] m -∗
      held (th := th) m -∗
      ⌜route_pre th m⌝ -∗
      trap_safe (switcher_pc off) ⊤ (HO th).

  (** ... which only happens for a fault outside the switcher. *)
  Definition path_nested_k (F : coPset) (cstk : CSTK) (w : LWord) (rmap : LReg)
    (error_state_written : nat → iProp Σ) : iProp Σ :=
    ⌜¬ switcher_fault_pc w⌝ -∗ path_nested_fault F cstk w rmap error_state_written.

  (** The [cjalr] to a handler of kind [kind], at offset [off], succeeded.
      The table's PCC [wpcc] and CGP [wcgp] are loaded through the frame's
      capability to the table, which is neither deep-local nor
      deep-read-only: the handler gets the words of the table. The
      destination holds the words of the [ErrorState] that the switcher
      wrote for this kind. A stackless handler is invoked only when the
      stackful one is not. The cause satisfies the cause predicate
      [P_mcause], the value the value predicate [P_mtval]. The handler
      starts with interrupts enabled. *)
  Definition path_invoke_k (P_mcause P_mtval : Z → Prop) (F : coPset) (cstk : CSTK)
    (rmap : LReg) (w : LWord)
    (error_state_written : nat → iProp Σ) : iProp Σ :=
    ∀ (kind : handler_kind) (wpcc wcgp wpc : LWord) (off mcause mtval : Z) (regs : LReg),
      ⌜¬ switcher_fault_pc w⌝ -∗
      ⌜Z.even (top_error_count cstk) = true⌝ -∗
      ⌜top_frame_stack_ok cstk⌝ -∗
      ⌜off ≠ ExportTable_no_handler⌝ -∗
      ⌜P_mcause mcause⌝ -∗
      ⌜P_mtval mtval⌝ -∗
      ⌜handler_entry wpcc off = Some wpc⌝ -∗
      ⌜handler_invocation_regs kind cstk wcgp rmap mcause mtval regs⌝ -∗
      (⌜kind = Stackless⌝ → handler_skipped cstk w rmap) -∗
      top_export_tbl cstk ↦ₐ□ wpcc -∗
      (top_export_tbl cstk ^+ ExportTable_offset_cgp) ↦ₐ□ wcgp -∗
      handler_offset kind (top_export_tbl cstk) off -∗
      PC ↦ₚ[th] wpc -∗
      registers_pointsto regs -∗
      ◯(CSTK)[th] (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) -∗
      error_state_written (error_state_size kind) -∗
      na_own (tpool th) F -∗
      ⌜route_pre th InterruptEnabled⌝ -∗
      MIE ↦ₜ[th] InterruptEnabled -∗
      £ 1 -∗
      safe[th].

  (** ** Auxiliary lemmas *)

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
    (regs[th] rmap) -∗
    cra ↦ᵣ[th] wcra -∗
    csp ↦ᵣ[th] wcsp -∗
    cgp ↦ᵣ[th] wcgp -∗
    ca0 ↦ᵣ[th] wca0 -∗
    ca1 ↦ᵣ[th] wca1 -∗
    ca2 ↦ᵣ[th] wca2 -∗
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

  (** The word [mstatus] of the register save area after the spill. *)
  #[local] Lemma exception_spill_mstatus save wmepcc wregs wst wcause :
    length save = 21%nat →
    length wregs = 15%nat →
    exception_spill save wmepcc wregs wst wcause !!! Z.to_nat TrustedStack_offset_mstatus = wst.
  Proof.
    intros Hsave Hregs.
    apply list_lookup_total_correct.
    rewrite /exception_spill /TrustedStack_offset_mstatus /=.
    rewrite lookup_app_r Hregs; last lia. cbn.
    destruct (lookup_lt_is_Some_2 save 16) as [w16 Hw16]; first lia.
    rewrite (drop_S _ w16 16) //=.
  Qed.

  (** A store to another word than [mstatus] keeps the saved MIE. *)
  #[local] Lemma saved_mie_ok_insert_ne (ws : list LWord) (i : nat) (w : LWord) :
    i ≠ Z.to_nat TrustedStack_offset_mstatus →
    saved_mie_ok ws →
    saved_mie_ok (<[i := w]> ws).
  Proof. intros Hi Hok w'. rewrite list_lookup_insert_ne //. apply Hok. Qed.

  (** The reasons why the switcher does not invoke the stackful handler. *)
  #[local] Lemma handler_skipped_pure (cstk : CSTK) (w : LWord) (rmap : LReg) :
    (∀ eh wpcc, ¬ stackful_handler_runs cstk w rmap eh wpcc) →
    ⊢ handler_skipped cstk w rmap.
  Proof.
    iIntros (Hnot) "!> (%eh & %wpcc & _ & _ & %Hruns)". iPureIntro. by apply (Hnot eh wpcc).
  Qed.

  (** A fault of the switcher. *)
  #[local] Lemma handler_skipped_switcher_fault (cstk : CSTK) (w : LWord) (rmap : LReg) :
    switcher_fault_pc w → ⊢ handler_skipped cstk w rmap.
  Proof. intros Hsw. apply handler_skipped_pure. by intros ?? [Hnsw _]. Qed.

  (** An odd count, or too many faults. *)
  #[local] Lemma handler_skipped_count (cstk : CSTK) (w : LWord) (rmap : LReg) :
    Z.even (top_error_count cstk) = false ∨
      (MAX_FAULTS_PER_COMPARTMENT_CALL < top_error_count cstk + 1)%Z →
    ⊢ handler_skipped cstk w rmap.
  Proof.
    intros Hcount. apply handler_skipped_pure.
    intros ?? (_ & _ & Hev & Hmax & _). destruct Hcount as [Hodd | Hover]; [congruence | lia].
  Qed.

  (** The switcher's stores of the [ErrorState] fault, or reach an exposed
      device. *)
  #[local] Lemma handler_skipped_stores (cstk : CSTK) (w : LWord) (rmap : LReg) :
    ¬ error_state_stores_ok (rmap !!! csp) ∨ ¬ error_state_mmio_free (rmap !!! csp) →
    ⊢ handler_skipped cstk w rmap.
  Proof.
    intros Hnok. apply handler_skipped_pure.
    intros ?? (_ & _ & _ & _ & _ & Hok & Hfree & _). by destruct Hnok.
  Qed.

  (** No stackful handler is declared, there is no room for the
      [ErrorState], or the tag of the stack pointer can be stripped. *)
  #[local] Lemma handler_skipped_no_stackful (cstk : CSTK) (w : LWord) (rmap : LReg) (eh : Z) :
    (error_state_fits (rmap !!! csp) →
     eh = ExportTable_no_handler ∨ tag_strippable (rmap !!! csp)) →
    top_export_tbl cstk ↦ₑ□{stackful} eh -∗
    handler_skipped cstk w rmap.
  Proof.
    iIntros (Hcond) "#Heh !> (%eh' & %wpcc & #Heh' & _ & %Hruns)".
    iDestruct (handler_stackful_agree with "Heh Heh'") as %<-.
    destruct Hruns as (_ & _ & _ & _ & Hsome & Hok & _ & Hstrip & _).
    destruct Hcond as [Hnone | Hstrip']; [|done|done].
    move: Hok. rewrite /error_state_stores_ok /error_state_fits.
    repeat case_match; naive_solver.
  Qed.

  (** The target of the [cjalr] to the stackful handler is not valid. *)
  #[local] Lemma handler_skipped_jump (cstk : CSTK) (w : LWord) (rmap : LReg)
    (eh : Z) (wpcc : LWord) :
    jalr_target_ok cra cra (handler_word wpcc eh).(lw) = false →
    top_export_tbl cstk ↦ₑ□{stackful} eh -∗
    top_export_tbl cstk ↦ₐ□ wpcc -∗
    handler_skipped cstk w rmap.
  Proof.
    iIntros (Htgt) "#Heh #Hpcc !> (%eh' & %wpcc' & #Heh' & #Hpcc' & %Hruns)".
    iDestruct (handler_stackful_agree with "Heh Heh'") as %<-.
    iDestruct (pointsto_agree with "Hpcc Hpcc'") as %<-.
    destruct Hruns as (_ & _ & _ & _ & _ & _ & _ & _ & Htgt'). congruence.
  Qed.

  (** The forced unwind, from [.Lcommon_force_unwind], once the closing of
      the trusted-stack invariant is ready. *)
  #[local] Lemma switcher_exception_unwind_finish
    (F : coPset) (cstk : CSTK) (n : Z) (rmap : LReg) (w : LWord)
    (error_state_written : nat → iProp Σ)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume w ->

    PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
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
    switcher_code ∗
    (|={⊤}=> na_own (tpool th) F) ∗
    ◯(CSTK)[th] (cstack_set_top_count cstk n) ∗
    error_state_written 0 ∗
    handler_skipped cstk w rmap ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    held (th := th) InterruptDisabled ∗
    path_unwind_k F cstk w rmap error_state_written
    ⊢ safe[th].
  Proof.
    iIntros (Hfull Hno_resume)
      "(HPC & Hrmap & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & #Hswitcher & Hclose & Hcstk & Hwritten
       & Hskip & Hmie & Hheld & Hunwind)".
    iApply (common_force_unwind_spec with "[- $HPC $Hca0 $Hca1 $Hswitcher]").
    iNext; iIntros "(HPC & Hca0 & Hca1)".
    iEval (rewrite -switcher_return_offset) in "HPC".
    iMod "Hclose" as "Hna".
    iDestruct (regs_rebuild_pointsto with
                "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
      as "Hrmap".
    iApply ("Hunwind" with "[//] Hskip [] [] [] HPC Hrmap Hcstk Hwritten Hna Hmie Hheld").
    - iPureIntro. by apply regs_rebuild_full.
    - iPureIntro. rewrite /regs_rebuild lookup_insert_ne //. apply lookup_insert_eq.
    - iPureIntro. rewrite /regs_rebuild. apply lookup_insert_eq.
  Qed.

  (** A fault of the path, at the switcher's PC of offset [off], once the
      closing of the trusted-stack invariant is ready. *)
  #[local] Lemma switcher_exception_nested_finish
    (F : coPset) (cstk : CSTK) (off n : Z) (rmap : LReg) (w : LWord)
    (error_state_written : nat → iProp Σ) (m : InterruptStatus)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume (switcher_pc off) ->
    route_pre th m ->

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
    ◯(CSTK)[th] (cstack_set_top_count cstk n) ∗
    (∃ k : nat, ⌜(k <= Z.to_nat ErrorState_size)%nat⌝ ∗ error_state_written k) ∗
    handler_skipped cstk w rmap ∗
    MIE ↦ₜ[th] m ∗
    held (th := th) m ∗
    path_nested_fault F cstk w rmap error_state_written
    ⊢ trap_safe (switcher_pc off) ⊤ (HO th).
  Proof.
    iIntros (Hfull Hno_resume Hpre)
      "(Hrmap & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hclose & Hcstk & Hwritten & Hskip
       & Hmie & Hheld & Hnested)".
    iApply trap_safe_fupd.
    iMod "Hclose" as "Hna". iModIntro.
    iDestruct (regs_rebuild_pointsto with
                "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
      as "Hrmap".
    iApply ("Hnested" with "Hskip [//] [] Hrmap Hcstk Hwritten Hna Hmie Hheld [//]").
    iPureIntro. by apply regs_rebuild_full.
  Qed.

  (** The words of the [ErrorState] in the register save area after the
      spill of the registers of [rmap], for a fault at [w]. *)
  #[local] Lemma exception_spill_error_state_src save w rmap wregs wst wcause :
    wregs = (λ r, rmap !!! r) <$> error_state_regs →
    let save' := exception_spill save (lmepcc_of_pc w) wregs wst wcause in
    lclear_tag (save' !!! 0%nat) :: take 15 (drop 1 save') = error_state_src w rmap.
  Proof.
    intros -> save'. subst save'.
    rewrite /exception_spill /error_state_src /=.
    f_equal.
  Qed.

  (** The arguments of a handler of kind [kind], in [csp], [ca0], [ca1] and
      [ca2]. *)
  #[local] Definition handler_args (kind : handler_kind) (cstk : CSTK) (rmap : LReg)
    (mcause mtval : Z) (wcsp wca0 wca1 wca2 : LWord) : Prop :=
    match kind with
    | Stackful =>
        error_state_stores_ok (rmap !!! csp) ∧
        stackful_regs (rmap !!! csp) = Some (wcsp, wca0) ∧
        wca1 = lword_of_word (WInt mcause) ∧
        wca2 = lword_of_word (WInt mtval)
    | Stackless =>
        wcsp = stackless_csp cstk ∧
        wca0 = lword_of_word (WInt mcause) ∧
        wca1 = lword_of_word (WInt mtval) ∧
        wca2 = lword_of_word (WInt 0)
    end.

  (** From [.Lhandle_error_handler_invoke], for a handler of kind
      [kind] at offset [off], once the trusted-stack invariant is closed:
      the registers are cleared but the handler's, and the [cjalr] invokes
      the handler or faults. *)
  #[local] Lemma switcher_exception_invoke (P_mcause P_mtval : Z → Prop)
    (F : coPset) (cstk : CSTK) (rmap : LReg) (w : LWord) (error_state_written : nat → iProp Σ)
    (kind : handler_kind) (p : Perm) (off mcause mtval : Z) (wpcc wcgp : LWord)
    (wcsp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    (∀ v, lload_word p v = v) ->
    ¬ switcher_fault_pc w ->
    Z.even (top_error_count cstk) = true ->
    top_frame_stack_ok cstk ->
    off ≠ ExportTable_no_handler ->
    P_mcause mcause ->
    P_mtval mtval ->
    handler_args kind cstk rmap mcause mtval wcsp wca0 wca1 wca2 ->
    route_pre th InterruptEnabled ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_invoke" ∗
    regs[th] delete ca5 (delete ca4 (delete ca3 (delete ca2 (delete ca1 (delete ca0 (delete cs1 (delete cs0 (delete ct2 (delete ct1 (delete ct0 (delete ctp (delete cgp (delete csp (delete cra rmap)))))))))))))) ∗
    cra ↦ᵣ[th] handler_word (lload_word p wpcc) off ∗
    csp ↦ᵣ[th] wcsp ∗
    cgp ↦ᵣ[th] lload_word p wcgp ∗
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
    switcher_code ∗
    top_export_tbl cstk ↦ₐ□ wpcc ∗
    (top_export_tbl cstk ^+ ExportTable_offset_cgp) ↦ₐ□ wcgp ∗
    handler_offset kind (top_export_tbl cstk) off ∗
    ◯(CSTK)[th] (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) ∗
    error_state_written (error_state_size kind) ∗
    na_own (tpool th) F ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    held (th := th) InterruptDisabled ∗
    (⌜kind = Stackless⌝ → handler_skipped cstk w rmap) ∗
    (⌜jalr_target_ok cra cra (handler_word wpcc off).(lw) = false⌝ →
       handler_skipped cstk w rmap) ∗
    (path_nested_k F cstk w rmap error_state_written ∧
     path_invoke_k P_mcause P_mtval F cstk rmap w error_state_written)
    ⊢ safe[th].
  Proof.
    iIntros (Hfull Hload Hnot_switcher Hev Hframe_stack Hoff Hcause Htval Hargs Hpre)
      "(HPC & Hrmap & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & #Hcode & #Hpcc & #Hcgp_cell & #Hoff
       & Hcstk & Hwritten & Hna & Hmie & Hheld & #Hskip_sl & #Hskip_jump & Hpost)".
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
    (* The invocation *)
    iApply (handle_error_handler_invoke_spec with "[- $HPC $Hcra $Hregs $Hcode $Hmie $Hheld]");
      [exact Hdom_cleared | exact Hpre |].
    iNext; iSplit.
    - (* The [cjalr] succeeds: the handler runs, with interrupts enabled *)
      iIntros (Htgt rmap' Hdom') "(HPC & Hcra & Hrmap' & Hmie & _ & Hlc)".
      rewrite Hdom_cleared in Hdom'.
      rewrite !Hload in Htgt |- *.
      destruct (handler_entry wpcc off) as [wpc|] eqn:Hentry;
        last first.
      { exfalso. by rewrite (handler_word_none _ _ Hentry) in Htgt. }
      rewrite (handler_word_entry _ _ _ Hentry).
      assert (lupdatePcPerm wpc = wpc ∧ jalr_target_mie wpc.(lw) = None) as [-> ->].
      { revert Hentry. rewrite /handler_entry.
        destruct wpcc as [ww ππ]. destruct_word ww; try done.
        destruct (_ + off)%a; cbn; last done. intros [=<-]. done. }
      iDestruct (big_sepM_sep with "Hrmap'") as "[Hrmap' Hzero]".
      iDestruct (big_sepM_pure_1 with "Hzero") as %Hzero.
      iDestruct (regs_six_insert with "Hrmap' Hcra Hcsp Hcgp Hca0 Hca1 Hca2") as "Hrmap'";
        first exact Hdom'.
      iDestruct "Hpost" as "[_ Hinvoke]".
      iApply ("Hinvoke" $! kind wpcc wcgp wpc off mcause mtval with
               "[//] [//] [//] [//] [//] [//] [//] [] Hskip_sl Hpcc Hcgp_cell Hoff HPC Hrmap' Hcstk
                Hwritten Hna [//] Hmie Hlc").
      iPureIntro. rewrite /handler_invocation_regs.
      split_and!.
      + by apply regs_six_full.
      + repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
      + repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
      + destruct kind; rewrite /handler_args in Hargs.
        * destruct Hargs as (Hok & Hregs & -> & ->).
          split; first exact Hok.
          exists wcsp, wca0. split; first exact Hregs.
          split_and!; repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
        * destruct Hargs as (-> & -> & -> & ->).
          split_and!; repeat (rewrite lookup_insert_ne; [|done]); apply lookup_insert_eq.
      + intros r Hr.
        assert (r ≠ cra ∧ r ≠ cgp ∧ r ≠ csp ∧ r ≠ ca0 ∧ r ≠ ca1 ∧ r ≠ ca2)
          as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5 & Hr6) by (clear -Hr; set_solver).
        rewrite !lookup_insert_ne; try (by apply not_eq_sym).
        assert (is_Some (rmap' !! r)) as [wr Hwr].
        { apply elem_of_dom. rewrite Hdom'. apply elem_of_difference.
          split; first apply all_registers_s_correct.
          rewrite elem_of_list_to_set !elem_of_cons elem_of_nil.
          intros [-> | [-> | [-> | [-> | [-> | [-> | [] ] ] ] ] ] ]; done. }
        rewrite Hwr. f_equal. exact (Hzero r wr Hwr).
    - (* The [cjalr] faults *)
      iIntros (Htgt rmap' Hdom') "(Hcra & Hrmap' & Hmie)".
      rewrite Hdom_cleared in Hdom'.
      iDestruct (big_sepM_sep with "Hrmap'") as "[Hrmap' _]".
      iDestruct (regs_six_insert with "Hrmap' Hcra Hcsp Hcgp Hca0 Hca1 Hca2") as "Hrmap'";
        first exact Hdom'.
      iDestruct "Hpost" as "[Hnested _]".
      rewrite !Hload in Htgt.
      iApply ("Hnested" with "[//] [] [] [] Hrmap' Hcstk [Hwritten] Hna Hmie [] [//]").
      + by iApply "Hskip_jump".
      + iPureIntro. apply trap_no_resume_switcher_pc. by vm_compute.
      + iPureIntro. by apply regs_six_full.
      + iExists (error_state_size kind). iFrame "Hwritten". iPureIntro.
        destruct kind; cbn; lia.
      + done.
  Qed.

  (** ** The exception path *)

  (** From the exception entry, for a fault at [w] with the registers [rmap]
      and the call stack [cstk], at InterruptDisabled with the whole posture
      of the thread (MPIE [b], the posture of the fault, the cause [cause]
      and the value [tval] of the trap), the path reaches one of its four
      continuations: the forced unwind, the resumption of a fault of the
      first spill of the call path, a fault of the path itself, and the
      invocation of a handler. The header of the table of the topmost frame
      is needed for a fault outside the switcher. The destination
      [error_state_written] of the [ErrorState] goes to the continuation
      reached. The cause satisfies the cause predicate [P_mcause] of fault
      causes, the value the value predicate [P_mtval]. The caller may hold
      the critical-section token, lent out of the posture: it gives the
      posture without it ([posture_lent]), a resource [crit_loan], and a closing
      hook, which the path calls, at any number of stores, before every
      change of the posture and every nested fault; the hook gives the
      token back and turns the destination into [error_state_closed],
      which the continuations receive. *)
  Lemma switcher_exception_path_spec (P_mcause P_mtval : Z → Prop)
    (F : coPset) (cstk : CSTK) (R_resume : iProp Σ)
    (error_state_written : nat → iProp Σ) (crit_loan : iProp Σ)
    (error_state_closed : nat → iProp Σ) (rmap : LReg) (w : LWord)
    (b : InterruptStatus) (cause tval : Z) :
    (∀ c, P_mcause c → mcause_ok c) ->
    ↑Ntstack ⊆ F ->
    (∀ r, is_Some (rmap !! r)) ->
    P_mcause cause ->
    P_mtval tval ->

    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    PC ↦ₚ[th] lword_of_word mtcc_vec ∗
    registers_pointsto rmap ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    posture_lent (th := th) (Some b) (Some (lmepcc_of_pc w))
      (Some (lword_of_word (WInt cause))) (Some tval) ∗
    crit_loan ∗
    na_own (tpool th) F ∗
    (if decide (trap_no_resume w) then ◯(CSTK)[th] cstk else R_resume) ∗
    (⌜¬ switcher_fault_pc w⌝ → handler_header cstk) ∗
    error_state_written 0 ∗
    path_es_acc cstk w rmap error_state_written ∗
    ▷ ( ∀ k, crit_loan -∗ error_state_written k ={⊤}=∗ na_own crit ⊤ ∗ error_state_closed k ) ∗
    ▷ ( path_unwind_k F cstk w rmap error_state_closed ∧
        path_resume_k F R_resume rmap w b error_state_closed ∧
        path_nested_k F cstk w rmap error_state_closed ∧
        path_invoke_k P_mcause P_mtval F cstk rmap w error_state_closed )
    ⊢ safe[th].
  Proof.
    (* Outline of the proof:
       - open the trusted-stack invariant, and join the save area of the
         posture with its word [hazardPointers];
       - [exception_entry_asm_spec]: lend mtdc, spill the registers, MEPCC,
         mstatus and mcause;
       - [handle_error_spec]: restore mtdc, and test for a fault of the
         switcher, and of the first spill of the call path;
       - for any other fault of the switcher, [common_force_unwind_spec]:
         set the return values; for a fault of the first spill,
         [common_context_install_spec]: install the context, with the
         return values overwritten, at the posture of the fault;
       - for a fault outside the switcher, [handle_error_stack_oob_spec]:
         look for a handler in the export table of the topmost frame;
         [handle_error_found_spec]: count the fault, update the logical call
         stack, compute the handler's PC and CGP; then the setup of a
         stackless handler, or the setup of a stackful handler with the
         stores of the [ErrorState]; then the invocation;
       - give the save area back to the posture, and close the
         trusted-stack invariant. *)
    iIntros (HP_mcause HF Hfull Hcause Htval)
      "(#Hinv_switcher & #Hstatic & HPC & Hrmap & Hmie & Hposture & Hcrit_loan & Hna & Hcstk
       & #Hheader & Hwritten & #Hes_acc & Hhook & Hpost)".
    iPoseProof "Hstatic" as "(#Hcode & _ & %Hmtcc & _)".
    rewrite Hmtcc.
    iMod (na_inv_acc with "Hinv_switcher Hna") as "(Hswitcher_inv & Hna & Hclose)";
      [done | solve_ndisj |].
    iModNamed trusted_stack_inv_open "Hswitcher_inv".
    (* The call stack of the invariant is [cstk], unless the fault is
       resumed *)
    iAssert ⌜trap_no_resume w → cstk' = cstk⌝%I as %Hcstk_eq.
    { destruct (decide (trap_no_resume w)) as [Hno | Hno].
      - iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->. done.
      - iPureIntro. by intros. }
    (* The posture: the volatile registers, the save area and the mtdc
       token *)
    iDestruct "Hposture"
      as "[(%vepcc & %vcause & %vtval & %vmpie & %Hb & %Hp & %Hc & %Hv
            & HU & Hmepcc & Hmcause & Hmtval & Hmpie) Hpart]".
    cbn in Hb, Hp, Hc, Hv. subst vepcc vcause vtval vmpie.
    iEval (rewrite posture_part_user //) in "Hpart".
    iDestruct "Hpart" as "[(%ws & %Hws_ok & Hholed) Hlent]".
    iDestruct (save_area_join with "[$Hholed $Hhazard_cell]") as "Hsave_area".
    set (save_area := <[Z.to_nat TrustedStack_offset_hazardPointers :=
                         lword_of_word hazard_slots_cap]> ws).
    iDestruct (tstack_save_area_length with "Hsave_area") as %Hsave_len.
    assert (save_area !! Z.to_nat TrustedStack_offset_hazardPointers =
              Some (lword_of_word hazard_slots_cap)) as Hsave_hz.
    { apply list_lookup_insert_eq. rewrite /save_area length_insert in Hsave_len.
      rewrite Hsave_len /TrustedStack_offset_hazardPointers. lia. }
    clearbody save_area.
    getRegValList [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca0;ca1;ca2;ca3;ca4;ca5].
    iDestruct (regs_extract with "Hrmap") as
      "(Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hrmap)"; try eassumption.

    (* The exception entry *)
    iApply (exception_entry_asm_spec b cause with
             "[- $HPC $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hmtdc $Hlent $Hsave_area $Hmie $Hmpie
                $Hmepcc $Hmcause $Hcode]");
      [by apply HP_mcause | done | done | done |].
    iNext; iIntros (g_tstk zca0)
      "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hmtdc & Hsave_area & Hmie & Hmpie
       & Hmepcc & Hmcause)".
    set (wst := lword_of_word (WInt (mstatus_enc InterruptDisabled b))).
    set (wregs := [wcra; wcsp; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1; wca0;
                   wca1; wca2; wca3; wca4; wca5]).
    (* The saved MIE of the spilled save area is InterruptDisabled *)
    assert (saved_mie_ok (exception_spill save_area (lmepcc_of_pc w) wregs wst (WInt cause)))
      as Hspill_ok.
    { apply exception_spill_saved_mie_ok; [done | done |].
      by rewrite /wst /= mie_of_mstatus_enc. }

    (* [.Lhandle_error] *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    (* The close of the trusted-stack invariant, for any error handler count
       of the topmost frame *)
    iAssert (∀ n' : Z,
               mtdc ↦ₜ Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack -∗
               tstack_hazard_cell ↦ₐ hazard_slots_cap -∗
               (b_trusted_stack ^+ TrustedStack_offset_frameoffset)
                 ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) -∗
               cstack_full (cstack_set_top_count cstk' n') -∗
               cstack_interp (cstack_set_top_count cstk' n') a_tstk
               ={⊤}=∗
               na_own (tpool th) F)%I
      with "[HthreadID Hhazard_slots Htstk Hclose Hna]" as "Hclose".
    { iIntros (n') "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp".
      iApply ("Hclose" with "[- $Hna]").
      iNext. rewrite /trusted_stack_inv.
      iExists a_tstk, (cstack_set_top_count cstk' n'), tstk_next.
      rewrite cstack_set_top_count_frames_length.
      iFrame "Hmtdc Hhazard_cell Hhazard_slots Hframeoffset HthreadID Htstk Hcstk_full
              Hstk_interp".
      iPureIntro. split_and!; done. }
    iAssert (cstack_full (cstack_set_top_count cstk' (top_error_count cstk')))
      with "[Hcstk_full]" as "Hcstk_full"; first by rewrite cstack_set_top_count_id.
    iApply (handle_error_spec _ _ _ _ (lmepcc_of_pc w) with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hctp $Hca0 $Hca1 $Hct2 $Hmtdc $Hsave_area
                 $Hframeoffset $Hcode]").
    { done. }
    { done. }
    { exact Hlen_cstk. }
    { by apply exception_spill_length. }
    { done. }
    iNext; iSplit; [|iSplit].
    - (* Any other fault of the switcher: the forced unwind *)
      iIntros (Hswitcher_fault wct0' wct1' wctp')
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hlent & Hsave_area
          & Hframeoffset)".
      pose proof (Hcstk_eq (or_intror (proj2 Hswitcher_fault))) as Heq_cstk; subst cstk'.
      rewrite decide_True; last exact (or_intror (proj2 Hswitcher_fault)).
      iMod ("Hhook" with "Hcrit_loan Hwritten") as "[Hcrit Hwritten]".
      iDestruct (handover_res_intro with "[Hcrit $HU $Hmepcc $Hmcause $Hmtval $Hmpie]")
        as "Hho"; first iExact "Hcrit".
      iDestruct (save_area_release with "Hsave_area Hho Hlent") as "[Hheld Hhazard_cell]";
        [done | save_area_hazard | done |].
      iSpecialize ("Hclose" with "Hmtdc Hhazard_cell Hframeoffset Hcstk_full [Hstk_interp]").
      { by rewrite cstack_set_top_count_id. }
      iDestruct "Hpost" as "[Hunwind _]".
      iPoseProof (handler_skipped_switcher_fault cstk w rmap (proj1 Hswitcher_fault)) as "Hskip".
      iApply (switcher_exception_unwind_finish _ _ (top_error_count cstk) with
               "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                 $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hclose $Hunwind $Hwritten $Hskip
                 $Hmie $Hheld Hcstk]");
        [done | right; apply Hswitcher_fault |].
      by rewrite cstack_set_top_count_id.
    - (* A fault of the first spill of the call path: the context install
         resumes the interrupted context, at the posture of the fault *)
      iIntros (Hresume wct0' wct1' wctp')
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hlent & Hsave_area
          & Hframeoffset)".
      iMod ("Hhook" with "Hcrit_loan Hwritten") as "[Hcrit Hwritten]".
      iDestruct (handover_res_intro with "[Hcrit $HU $Hmepcc $Hmcause $Hmtval $Hmpie]")
        as "Hho"; first iExact "Hcrit".
      iApply (common_context_install_spec with
               "[- $HPC $Hcsp $Hcra $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                   $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hsave_area $Hmie $Hho $Hlent $Hcode]").
      { done. }
      { rewrite !length_insert. by apply exception_spill_length. }
      { apply saved_mie_ok_insert_ne; first by vm_compute.
        apply saved_mie_ok_insert_ne; first by vm_compute.
        exact Hspill_ok. }
      (* The posture after [mret] is the saved MPIE, that of the fault *)
      set (save'' := <[Z.to_nat TrustedStack_offset_ca0 := (WInt ENOTENOUGHSTACK : LWord)]>
                       (<[Z.to_nat TrustedStack_offset_ca1 := (WInt 0 : LWord)]>
                          (exception_spill save_area (lmepcc_of_pc w) wregs wst (WInt cause)))).
      assert (mpie_of (get_a (save'' !!! Z.to_nat TrustedStack_offset_mstatus).(lw)) = b) as Hp.
      { rewrite /save'' !list_lookup_total_insert_ne; [|by vm_compute..].
        rewrite exception_spill_mstatus //. by rewrite /wst /= mpie_of_mstatus_enc. }
      assert (save'' !!! Z.to_nat TrustedStack_offset_hazardPointers =
                lword_of_word hazard_slots_cap) as Hhz''.
      { apply list_lookup_total_correct. rewrite /save''. save_area_hazard. }
      iNext; cbv zeta; rewrite Hp Hhz''; iIntros
        "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
          & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hhazard_cell & _ & Hmie & Hheld & Hlc)".
      subst save''.
      (* The PC to resume is a valid PC: MEPCC keeps it *)
      rewrite (_ : llegalise mepcc (switcher_label_pc ".Lswitch_just_return") =
                   switcher_label_pc ".Lswitch_just_return"); last reflexivity.
      iMod ("Hclose" with "Hmtdc Hhazard_cell Hframeoffset Hcstk_full [Hstk_interp]") as "Hna".
      { by rewrite cstack_set_top_count_id. }
      subst wregs wst.
      rewrite /exception_spill /TrustedStack_offset_ca0 /TrustedStack_offset_ca1 /=.
      (* The other registers get their words back: the register map is the
         original one, with the return values inserted last *)
      iDestruct (regs_insert_return_values with
                  "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4
                   Hca5") as "Hrmap"; try eassumption.
      assert (¬ trap_no_resume w) as Hresume'.
      { destruct Hresume as [Hb Ha]. by intros [Hb' | Ha']. }
      rewrite decide_False; last exact Hresume'.
      iDestruct "Hpost" as "[_ [Hresume_k _] ]".
      iApply ("Hresume_k" with "[] [//] [] [] [] [] HPC Hrmap Hcstk Hwritten Hna Hmie Hheld Hlc").
      + done.
      + iPureIntro. intros r.
        repeat (rewrite lookup_insert_is_Some'; right).
        apply Hfull.
      + iPureIntro. intros r Hr0 Hr1. rewrite !lookup_insert_ne //.
      + iPureIntro. rewrite lookup_insert_ne //. apply lookup_insert_eq.
      + iPureIntro. apply lookup_insert_eq.
    - (* A fault outside the switcher: the lookup of an error handler *)
      iIntros (Hnot_in wct0_l wct1' Hlea)
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hlent & Hsave_area
          & Hframeoffset)".
      assert (¬ switcher_fault_pc w) as Hnot_switcher by exact Hnot_in.
      assert (trap_no_resume w) as Hno_resume by (by left).
      pose proof (Hcstk_eq Hno_resume) as Heq_cstk; subst cstk'.
      rewrite decide_True; last exact Hno_resume.
      iDestruct ("Hheader" with "[//]") as (Htbl_set eh ehs) "(#Heh & #Hehs & #Hpcc_cgp)".
      (* The topmost frame *)
      iDestruct (cstack_interp_top_csp with "Hstk_interp") as %Hframe_csp.
      iDestruct (cstack_interp_top_stack with "Hstk_interp") as %Hframe_stack.
      pose proof (exception_spill_cause save_area (lmepcc_of_pc w) wregs wst (WInt cause)
                    Hsave_len eq_refl)
        as Hsave'_cause.
      pose proof (exception_spill_length save_area (lmepcc_of_pc w) wregs wst (WInt cause)
                    Hsave_len eq_refl)
        as Hsave'_len.
      (* The words of the [ErrorState] in the register save area *)
      assert (wregs = (λ r, rmap !!! r) <$> error_state_regs) as Hwregs.
      { rewrite /wregs /error_state_regs /= !lookup_total_alt Hwcra Hwcsp Hwcgp Hwctp Hwct0
          Hwct1 Hwct2 Hwcs0 Hwcs1 Hwca0 Hwca1 Hwca2 Hwca3 Hwca4 Hwca5 //. }
      pose proof (exception_spill_error_state_src save_area w rmap _ wst (WInt cause) Hwregs)
        as Hsave'_src; cbv zeta in Hsave'_src.
      assert (save_area_hazard_spill :
                exception_spill save_area (lmepcc_of_pc w) wregs wst (WInt cause)
                  !! Z.to_nat TrustedStack_offset_hazardPointers =
                Some (lword_of_word hazard_slots_cap)) by save_area_hazard.
      remember (exception_spill save_area (lmepcc_of_pc w) wregs wst (WInt cause))
        as save' eqn:Hsave'.
      assert (save' !!! 2%nat = wcsp) as Hsave'_csp by (rewrite Hsave'; reflexivity).
      rewrite Hsave'_csp in Hlea.
      assert (rmap !!! csp = wcsp) as Hrmap_csp by (rewrite lookup_total_alt Hwcsp; done).
      iDestruct (cstack_interp_open_top with "Hstk_interp") as "[Htf Hstk_close]".
      iDestruct (trusted_frame_interp_open with "Htf")
        as (dq wcell) "(Hcsp_cell & Hcell & Hcnt & %Hwcell & Htf_close)".
      (* The frame's table word is set: the cell holds it *)
      destruct Hwcell as [Hz | (-> & Hexp & Hprov)]; first (exfalso; by apply Htbl_set).
      iEval (fold (top_error_count cstk)) in "Hcnt".
      (* The lookup of an error handler *)
      iApply (handle_error_stack_oob_spec _ cstk a_tstk (top_export_tbl cstk) eh ehs wcsp wct0_l
                (top_tframe cstk).(tf_export_tbl)
               with "[- $HPC $Hcsp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                       $Hcsp_cell $Hcell $Hcode]").
      { exact Hlen_cstk. }
      { exact Ha_tstk_e. }
      { exact Hframe_csp. }
      { by right. }
      { exact Hlea. }
      iSplitR; first (iIntros "_"; iFrame "Heh Hehs").
      iNext; iSplit; [|iSplit].
      + (* The cell of the export table holds the frame's set word *)
        iIntros (Hz). exfalso. by apply Htbl_set.
      + (* No handler: the forced unwind *)
        iIntros ([_ Hno_stackful] wct0_u wct1_u wct2_u wcs0_u wcs1_u)
          "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca0 & Hca1 & Hca2
            & Hcsp_cell & Hcell)".
        iDestruct ("Htf_close" $! (top_error_count cstk) with "Hcsp_cell Hcell Hcnt") as "Htf".
        iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
        iMod ("Hhook" with "Hcrit_loan Hwritten") as "[Hcrit Hwritten]".
        iDestruct (handover_res_intro with "[Hcrit $HU $Hmepcc $Hmcause $Hmtval $Hmpie]")
          as "Hho"; first iExact "Hcrit".
        iDestruct (save_area_release with "Hsave_area Hho Hlent") as "[Hheld Hhazard_cell]";
          [done | done | done |].
        iSpecialize ("Hclose" with "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp").
        iDestruct "Hpost" as "[Hunwind _]".
        iPoseProof (handler_skipped_no_stackful cstk w rmap eh with "Heh") as "Hskip";
          first by rewrite Hrmap_csp.
        iApply (switcher_exception_unwind_finish _ _ (top_error_count cstk) with
                 "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                   $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hclose $Hunwind $Hwritten $Hskip
                   $Hmie $Hheld Hcstk]");
          [done | done |].
        by rewrite cstack_set_top_count_id.
      + (* A handler is found, at offset [off] *)
        iIntros (p g e a off z0 wct0_h wct2_h wcs1_h wca1_h wca2_h Hw Hfound)
          "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca0 & Hca1 & Hca2
            & Hcsp_cell & Hcell)".
        rewrite Hw /= in Hexp.
        assert (exp_tbl_cap (top_export_tbl cstk)
                  (Cap p g (top_export_tbl cstk) e (top_export_tbl cstk))) as Htbl.
        { destruct Hexp as (p' & g' & e' & a' & Heq & Hread & Hbnd & Hshadow & Hdl & Hdro).
          injection Heq as <- <- <- _. by exists p, g, e, (top_export_tbl cstk). }
        (* The loads through the table's capability give the words of the table *)
        assert (∀ v, lload_word p v = v) as Hload.
        { destruct Htbl as (p' & g' & e' & a' & Heq & _ & _ & _ & Hdl & Hdro).
          injection Heq as <- _ _ _. intros v. by apply lload_word_no_dl_dro. }
        (* The PCC and the CGP of the table, for an even count *)
        iAssert (∃ wpcc wcgp' : LWord,
                   ⌜Z.even (top_error_count cstk) = true⌝ →
                   top_export_tbl cstk ↦ₐ□ wpcc ∗
                   (top_export_tbl cstk ^+ ExportTable_offset_cgp) ↦ₐ□ wcgp')%I
          as (wpcc wcgp') "#Hcells".
        { destruct (Z.even (top_error_count cstk)) eqn:Hev.
          - iDestruct ("Hpcc_cgp" with "[]") as (wpcc wcgp') "[Hpcc Hcgp']".
            { iPureIntro. split; last done.
              destruct Hfound as [(_ & _ & _ & _ & Heh_some) | (_ & _ & _ & Hehs_some & _)];
                [by left | by right]. }
            iExists wpcc, wcgp'. iIntros "_". iFrame "Hpcc Hcgp'".
          - iExists (WInt 0 : LWord), (WInt 0 : LWord). iIntros "%". done. }
        (* Count the fault *)
        iApply (handle_error_found_spec _ (length cstk.(cstk_frames)) a_tstk
                  (top_export_tbl cstk) e p g (top_error_count cstk) off z0 wpcc wcgp'
                 with "[- $HPC $Hctp $Hct1 $Hct2 $Hcs0 $Hcs1 $Hcra $Hcgp $Hca0 $Hcnt
                         $Hcells $Hcode]");
          [exact Hlen_cstk | exact Ha_tstk_e | exact Htbl |].
        iNext; iSplit; [|iSplit].
        * (* An odd count, or too many faults: the forced unwind *)
          iIntros (Hcount wcra_u)
            "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcra & Hcgp & Hca0 & Hcnt)".
          iMod (cstack_update _ _ (cstack_set_top_count cstk (top_error_count cstk + 1)%Z)
                 with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
          iDestruct ("Htf_close" $! (top_error_count cstk + 1)%Z with "Hcsp_cell Hcell Hcnt")
            as "Htf".
          iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
          iMod ("Hhook" with "Hcrit_loan Hwritten") as "[Hcrit Hwritten]".
          iDestruct (handover_res_intro with "[Hcrit $HU $Hmepcc $Hmcause $Hmtval $Hmpie]")
            as "Hho"; first iExact "Hcrit".
          iDestruct (save_area_release with "Hsave_area Hho Hlent") as "[Hheld Hhazard_cell]";
            [done | done | done |].
          iSpecialize ("Hclose" with "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp").
          iDestruct "Hpost" as "[Hunwind _]".
          iPoseProof (handler_skipped_count cstk w rmap Hcount) as "Hskip".
          iApply (switcher_exception_unwind_finish _ _ (top_error_count cstk + 1)%Z with
                   "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                     $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hclose $Hcstk $Hunwind
                     $Hwritten $Hskip $Hmie $Hheld]");
            [done | done].
        * (* A stackless handler *)
          iIntros ([Hev Hmax] Hz0 wct2_s wcs1_s)
            "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcra & Hcgp & Hca0 & Hcnt)".
          iMod (cstack_update _ _ (cstack_set_top_count cstk (top_error_count cstk + 1)%Z)
                 with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
          iDestruct ("Htf_close" $! (top_error_count cstk + 1)%Z with "Hcsp_cell Hcell Hcnt")
            as "Htf".
          iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
          iDestruct ("Hcells" with "[//]") as "[Hpcc Hcgp_cell]".
          iDestruct "Hpost" as "(_ & _ & Hpost)".
          destruct Hfound as [(-> & _) | (_ & -> & -> & Hehs_some & Hno_stackful)];
            first done.
          iPoseProof (handler_skipped_no_stackful cstk w rmap eh with "Heh") as "#Hskip";
            first by rewrite Hrmap_csp.
          iApply (handle_error_stackless_setup_spec with
                   "[- $HPC $Hcsp $Hct0 $Hca0 $Hca1 $Hca2 $Hsave_area $Hmtval $Hcode]");
            first exact Hsave'_len.
          iNext; iIntros "(HPC & Hcsp & Hct0 & Hca0 & Hca1 & Hca2 & Hsave_area & Hmtval)".
          rewrite Hsave'_cause.
          (* The posture is given back, and the invariant closed, before the
             [cjalr] *)
          iMod ("Hhook" with "Hcrit_loan Hwritten") as "[Hcrit Hwritten]".
          iDestruct (handover_res_intro with "[Hcrit $HU $Hmepcc $Hmcause $Hmtval $Hmpie]")
            as "Hho"; first iExact "Hcrit".
          iDestruct (save_area_release with "Hsave_area Hho Hlent") as "[Hheld Hhazard_cell]";
            [done | done | done |].
          iMod ("Hclose" with "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp")
            as "Hna".
          (* The invocation *)
          iApply (switcher_exception_invoke _ _ _ _ _ _ error_state_closed Stackless p ehs
                    cause tval
                   with "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                          $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hpcc $Hcgp_cell $Hehs
                          $Hcstk $Hwritten $Hna $Hmie $Hheld $Hpost]").
          1-8: done.
          { by rewrite /handler_args. }
          { intros Hc; by destruct Huser. }
          iSplit; iIntros "_ !>"; iExact "Hskip".
        * (* A stackful handler, the [ErrorState] below [csp] *)
          iIntros ([Hev Hmax] Hz0 wct2_s wcs1_s)
            "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcra & Hcgp & Hca0 & Hcnt)".
          subst z0.
          iMod (cstack_update _ _ (cstack_set_top_count cstk (top_error_count cstk + 1)%Z)
                 with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
          iDestruct ("Htf_close" $! (top_error_count cstk + 1)%Z with "Hcsp_cell Hcell Hcnt")
            as "Htf".
          iDestruct ("Hstk_close" with "Htf") as "Hstk_interp".
          iDestruct ("Hcells" with "[//]") as "[Hpcc Hcgp_cell]".
          iDestruct "Hpost" as "(_ & _ & Hpost)".
          destruct Hfound as [(_ & -> & -> & Hfits & Heh_some) | (Hn & _)]; last done.
          (* The stores of the [ErrorState], from the words of the register
             save area *)
          iAssert (∀ (p' : Perm) (g' : Locality) (b' e' a' : Addr) (π' : option AId),
                     ⌜wcsp = Cap p' g' b' e' a' @@? π'⌝ -∗
                     ⌜error_state_first_store_ok wcsp⌝ -∗
                     cells_store_acc error_state_written p' e' (a' ^+ (- ErrorState_size)) π'
                       (lclear_tag (save' !!! 0%nat) :: take 15 (drop 1 save')))%I
            as "Hacc".
          { iIntros (p' g' b' e' a' π' Hwcsp' Hok).
            rewrite Hsave'_src.
            iApply ("Hes_acc" with "[//] [//] Heh [//] [] []"); iPureIntro;
              by rewrite Hrmap_csp. }
          iApply (handle_error_stack_setup_spec _ save' wcsp wct0_l _ _ _ _ _ _
                    error_state_written with
                   "[- $HPC $Hcsp $Hct0 $Hcs1 $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hsave_area
                       $Hmtval $Hcode $Hwritten $Hacc]");
            [exact Hsave'_len | exact Hlea | exact Hfits |].
          iNext; iSplit.
          ++ (* A store faults, after [k] words: the posture is given back,
                the invariant closed *)
             iIntros (Hnok k off Hk Hoff)
               "(Hcsp & Hct0 & [%wcs1_f Hcs1] & Hca0 & Hca1 & [%wca2_f Hca2] & [%wca3_f Hca3]
                 & [%wca4_f Hca4] & Hsave_area & Hwritten & Hmtval)".
             iApply trap_safe_fupd.
             iMod ("Hhook" with "Hcrit_loan Hwritten") as "[Hcrit Hwritten]".
             iModIntro.
             iDestruct (handover_res_intro with "[Hcrit $HU $Hmepcc $Hmcause $Hmtval $Hmpie]")
               as "Hho"; first iExact "Hcrit".
             iDestruct (save_area_release with "Hsave_area Hho Hlent")
               as "[Hheld Hhazard_cell]"; [done | done | done |].
             iSpecialize ("Hclose" with
                           "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp").
             iDestruct "Hpost" as "[Hnested _]".
             iSpecialize ("Hnested" with "[//]").
             iPoseProof (handler_skipped_stores cstk w rmap) as "Hskip";
               first by rewrite Hrmap_csp.
             iApply (switcher_exception_nested_finish _ _ _ (top_error_count cstk + 1)%Z with
                      "[$Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                        $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hclose $Hcstk $Hskip $Hnested
                        $Hmie $Hheld Hwritten]");
               [done | exact Hoff | intros Hc; by destruct Huser |].
             iExists k. iFrame "Hwritten". iPureIntro. lia.
          ++ (* The stores succeed: the posture is given back, and the
                invariant closed, before the [cjalr] *)
             iIntros (Hok wcs1' wca3' wca4')
               "(HPC & Hcsp & Hct0 & Hcs1 & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hsave_area
                 & Hwritten & Hmtval)".
             rewrite Hsave'_cause.
             iMod ("Hhook" with "Hcrit_loan Hwritten") as "[Hcrit Hwritten]".
             iDestruct (handover_res_intro with "[Hcrit $HU $Hmepcc $Hmcause $Hmtval $Hmpie]")
               as "Hho"; first iExact "Hcrit".
             iDestruct (save_area_release with "Hsave_area Hho Hlent")
               as "[Hheld Hhazard_cell]"; [done | done | done |].
             iMod ("Hclose" with "Hmtdc Hhazard_cell Hframeoffset Hcstk_full Hstk_interp")
               as "Hna".
             (* The invocation *)
             iApply (switcher_exception_invoke _ _ _ _ _ _ error_state_closed Stackful p eh
                       cause tval
                      with "[$HPC $Hrmap $Hcra $Hcsp $Hcgp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1
                             $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hcode $Hpcc $Hcgp_cell $Heh
                             $Hcstk $Hwritten $Hna $Hmie $Hheld $Hpost]").
             1-8: done.
             { rewrite /handler_args Hrmap_csp.
               split_and!; [done | by apply stackful_regs_lea | done | done]. }
             { intros Hc; by destruct Huser. }
             iSplit; first by iIntros "%".
             iIntros (Htgt). by iApply (handler_skipped_jump with "Heh Hpcc").
  Qed.

End Switcher_Spec_Exception.
