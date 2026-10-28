From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export logrel switcher switcher_preamble.

(** * Shared interfaces of the return routine of the switcher

    The proofs of [switcher_ret_specification_gen] (functional
    specification) and [interp_expr_switcher_return] (validity of the return
    entry point) run the same code. They share the block lemmas of
    [callback/], one file per region of the code, named after its entry
    label, and their compositions in [callback_path]:
    - [switcher_after_compartment_call]: pop the topmost frame of the
      trusted stack, and restore the callee-save registers;
    - [switcher_zero_callee_frame]: clear the stack frame and the
      registers, and jump back to the caller.

    The block lemmas start and end at labels of the code [switcher_instrs],
    whose offsets are given by [switcher_label_offset] (see
    [switcher_tactics]).

    This file also holds the closing of the trusted-stack invariant at the
    exits of the routine, shared by the proofs and by the known-to-known
    specification. *)

Section Switcher_Return_States.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The return entry point is the first address of block 13. *)
  Lemma switcher_return_block_13 :
    a_switcher_return = (a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call")%a.
  Proof. rewrite switcher_return_offset. by offsets_compute. Qed.

  (** The trusted-stack invariant, opened by the return routine, closes again
      with the trusted stack unchanged: after the thread exit. *)
  Lemma switcher_return_exit_close
    (F : coPset) (cstk : CSTK) (a_tstk : Addr) (save_area tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    (b_trusted_stack + tstack_frame_offset (length cstk.(cstk_frames)))%a = Some a_tstk ∧
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->
    save_area !! Z.to_nat TrustedStack_offset_hazardPointers = Some (lword_of_word hazard_slots_cap) ->

    (▷ trusted_stack_inv ∗ na_own (tpool th) (F ∖ ↑Ntstack) ={⊤}=∗ na_own (tpool th) F) -∗
    na_own (tpool th) (F ∖ ↑Ntstack) -∗
    mtdc ↦ₜ[th] TStack (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) -∗
    (tstack_hazard_cell ↦ₐ hazard_slots_cap -∗ [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]]) -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk.(cstk_frames))) -∗
    switcher_hazard -∗
    (∃ w, a_threadID ↦ₐ w) -∗
    [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    ●(CSTK)[th] cstk -∗
    ▷ cstack_interp cstk a_tstk
    ={⊤}=∗
    na_own (tpool th) F.
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next.
    subst a_frameoffset a_save_end a_threadID a_next.
    iIntros (Hlen Hot Hsave_hazard) "Hclose Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID
      Htstk Hcstk_full Hstk_interp".
    iDestruct "Hhazard" as "[Hhazard_cell Hhazard_slots]".
    iSpecialize ("Hsave_area" with "Hhazard_cell").
    iApply ("Hclose" with "[- $Hna]").
    iNext. iExists a_tstk, cstk, save_area, tstk_next.
    iFrame "Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Htstk Hcstk_full Hstk_interp".
    iSplit; iPureIntro; done.
  Qed.

  (** The trusted-stack invariant, opened by the return routine, closes again
      after the pop of the topmost frame [frm], at [a_tstk]. *)
  Lemma switcher_return_pop_close
    (F : coPset) (frm : cframe) (cstk : CSTK) (a_tstk : Addr)
    (save_area tstk_next : list LWord) (w0 w1 w2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_prev := (a_tstk ^+ - TrustedStackFrame_size)%a in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    (b_trusted_stack + tstack_frame_offset (S (length cstk.(cstk_frames))))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->
    save_area !! Z.to_nat TrustedStack_offset_hazardPointers = Some (lword_of_word hazard_slots_cap) ->

    (▷ trusted_stack_inv ∗ na_own (tpool th) (F ∖ ↑Ntstack) ={⊤}=∗ na_own (tpool th) F) -∗
    na_own (tpool th) (F ∖ ↑Ntstack) -∗
    mtdc ↦ₜ[th] TStack (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) -∗
    (tstack_hazard_cell ↦ₐ hazard_slots_cap -∗ [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]]) -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk.(cstk_frames))) -∗
    switcher_hazard -∗
    (∃ w, a_threadID ↦ₐ w) -∗
    a_csp ↦ₐ w0 -∗
    a_export_table ↦ₐ w1 -∗
    a_error_count ↦ₐ w2 -∗
    [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    ●(CSTK)[th] (cstack_push frm cstk) -∗
    ◯(CSTK)[th] (cstack_push frm cstk) -∗
    ▷ cstack_interp cstk a_prev
    ={⊤}=∗
    na_own (tpool th) F ∗ ◯(CSTK)[th] cstk.
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next a_prev a_csp a_export_table a_error_count.
    subst a_frameoffset a_save_end a_threadID a_next a_prev a_csp a_export_table a_error_count.
    iIntros (Ha_tstk Ha_tstk_e Hot Hsave_hazard) "Hclose Hna Hmtdc Hsave_area Hframeoffset
      Hhazard HthreadID Hframe_csp Hframe_tbl Hframe_cnt Htstk Hcstk_full Hcstk Hstk_interp".
    iDestruct "Hhazard" as "[Hhazard_cell Hhazard_slots]".
    iSpecialize ("Hsave_area" with "Hhazard_cell").
    iMod (cstack_update _ _ cstk with "Hcstk_full Hcstk") as "[Hcstk_full $]".
    iApply ("Hclose" with "[- $Hna]").
    iNext.
    iApply (trusted_stack_inv_pop_frame _ cstk with
             "Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Hframe_csp Hframe_tbl
              Hframe_cnt Htstk Hcstk_full Hstk_interp"); done.
  Qed.

End Switcher_Return_States.
