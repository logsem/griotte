From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_call_states.
From griotte.switcher.call Require Export
  switch_csp_check switch_entry_first_spill switcher_trusted_stack_push switch_stack_chop
  switch_unseal_entry switcher_clear_unused_args.
From griotte.switcher.callback Require Export switcher_zero_callee_frame.
From griotte.switcher.failure Require Export
  switch_trusted_stack_exhausted common_force_unwind switch_stack_too_small.

(** * Call routine of the switcher: paths

    The compositions of the blocks of the call routine that the functional
    and the logical-relation specifications share: from the call entry
    point [.Lswitch_csp_check] to the decoding of the entry point, from
    [.Lswitcher_decode_entry] to the callee, and from
    [.Lswitch_trusted_stack_exhausted] back to the caller. Between the
    first two, the specifications reason on the world to obtain the export
    table of the callee. *)

Section Call_Path.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_csp_check], the call entry point, to
      [.Lswitcher_decode_entry]: check the stack pointer, spill the
      callee-save registers below the cursor [a] of the caller's stack, push
      a frame with the stack pointer on the trusted stack, whose topmost
      frame is at [a_tstk], restrict the stack capability to the callee's
      stack and clear it, and unseal the entry point [wct1].

      The stack pointer is a [RWL] [Local] capability, so the checks pass.
      There is one continuation per exit, in this order: the entry point is
      unsealed, at [.Lswitcher_decode_entry]; the unsealing faults, with the
      frame pushed; the trusted stack is exhausted, at
      [.Lswitch_trusted_stack_exhausted]; the first store of the spill
      faults, with nothing written. The first continuation comes under one
      more later, for the logical steps between the push and the callee. *)
  Lemma switcher_call_path_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wct2 wctp wcs0 wcs1 wcra wcgp wct1 : LWord)
    (d : nat) (a_tstk : Addr) (tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    let a_free := (a_next ^+ TrustedStackFrame_size) in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp) in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount) in
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->
    stk_cursor_ok b e a ->
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_csp_check" ∗
    csp ↦ᵣ[th] Cap RWL Local b e a ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] wctp ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    cra ↦ᵣ[th] wcra ∗
    cgp ↦ᵣ[th] wcgp ∗
    ct1 ↦ᵣ[th] wct1 ∗
    [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    switcher_hazard ∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    (b_switcher ^+ 1) ↦ₐ□ SealRange (true,true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
    switcher_code ∗
    ▷ ( (* The entry point is unsealed *)
        ▷ ( ∀ (g_tstk : Locality) wsb π,
          ⌜ wct1 = WSealed ot_switcher wsb @@? π ⌝ ∗
          ⌜ get_tag_sealable wsb = true ⌝ ∗
          ⌜ switcher_stk_bounds b e a ⌝ ∗
          ⌜ (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_next ⌝ ∗
          ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitcher_decode_entry" ∗
          cs0 ↦ᵣ[th] SealRange (true,true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
          (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
          (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
          ctp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack a_next ∗
          csp ↦ᵣ[th] chopped_csp b e a ∗
          cra ↦ᵣ[th] wcra ∗
          cgp ↦ᵣ[th] wcgp ∗
          ct1 ↦ᵣ[th] WSealable wsb @@? π ∗
          switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
          [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ 0…0 ]] ∗
          mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
          switcher_hazard ∗
          a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
          a_export_table ↦ₐ - ∗
          a_error_count ↦ₐ WInt 0 ∗
          (∃ tstk_next', [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]]) ∗
          £ 2 -∗
          safe[th] )
        ∧
        (* The unsealing faults *)
        ( ∀ g_tstk : Locality,
          ⌜ ¬ ∃ wsb π, wct1 = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ ∗
          ⌜ switcher_stk_bounds b e a ⌝ ∗
          ⌜ (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_next ⌝ ∗
          ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
          cs0 ↦ᵣ[th] SealRange (true,true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
          (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
          (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
          ctp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack a_next ∗
          csp ↦ᵣ[th] chopped_csp b e a ∗
          cra ↦ᵣ[th] wcra ∗
          cgp ↦ᵣ[th] wcgp ∗
          ct1 ↦ᵣ[th] - ∗
          switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
          [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ 0…0 ]] ∗
          mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
          switcher_hazard ∗
          a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
          a_export_table ↦ₐ - ∗
          a_error_count ↦ₐ WInt 0 ∗
          (∃ tstk_next', [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]]) ∗
          £ 2 -∗
          trap_safe (switcher_label_pc ".Lswitcher_decode_entry") ⊤
            (HO th) )
        ∧
        (* The trusted stack is exhausted *)
        ( ∀ g_tstk : Locality,
          ⌜ switcher_stk_bounds b e a ⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
          cs0 ↦ᵣ[th] WInt (e_trusted_stack - b_trusted_stack) ∗
          cs1 ↦ᵣ[th] wcs1 ∗
          ctp ↦ᵣ[th] WInt (tstack_frameoffset d) ∗
          ct2 ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          csp ↦ᵣ[th] Cap RWL Local b e (stk_saved_a a) ∗
          cra ↦ᵣ[th] wcra ∗
          cgp ↦ᵣ[th] wcgp ∗
          ct1 ↦ᵣ[th] wct1 ∗
          switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
          [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem_callee stk_mem ]] ∗
          mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          switcher_hazard ∗
          [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
          safe[th] )
        ∧
        (* The first store of the spill faults *)
        ( ⌜ ¬ stk_spill_fits b e a ⌝ ∗
          csp ↦ᵣ[th] Cap RWL Local b e a ∗
          ct2 ↦ᵣ[th] WInt COMPARTMENT_STACK_LOCALITY ∗
          ctp ↦ᵣ[th] WInt COMPARTMENT_STACK_LOCALITY ∗
          cs0 ↦ᵣ[th] wcs0 ∗
          cs1 ↦ᵣ[th] wcs1 ∗
          cra ↦ᵣ[th] wcra ∗
          cgp ↦ᵣ[th] wcgp ∗
          ct1 ↦ᵣ[th] wct1 ∗
          [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ stk_mem ]] ∗
          mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          switcher_hazard ∗
          [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
          trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
            (HO th) ) )
    ⊢ safe[th].
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hstk_mmio Hstk_heap Hcursor Ha_tstk Ha_tstk_e)
      "(HPC & Hcsp & Hct2 & Hctp & Hcs0 & Hcs1 & Hcra & Hcgp & Hct1 & Hstk
      & Hmtdc & Hframeoffset & Hhazard & Htstk & #Hb_switcher & #Hswitcher & Hpost)".
    (* [.Lswitch_csp_check]: checks on the stack pointer *)
    iApply (switch_csp_check_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hswitcher]").
    iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp) | (%Hcontra & _)]";
      last (exfalso; apply Hcontra, switcher_csp_checked_stk).
    (* [.Lswitch_entry_first_spill]: spill the callee-save registers *)
    iApply (switch_entry_first_spill_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hcsp $Hstk $Hswitcher]"); [done|done|].
    iSplit; cycle 1.
    { iIntros (Hnfits) "(Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hstk)".
      iDestruct "Hpost" as "(_ & _ & _ & Hpost)".
      iApply "Hpost".
      iFrame "Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1 Hstk Hmtdc Hframeoffset Hhazard Htstk".
      done. }
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hcells & Hstk & %Hbounds)".
    (* [.Lswitch_trusted_stack_load]: read the trusted stack, clear the hazard slots *)
    iApply (switcher_trusted_stack_load_spec with "[- $HPC $Hctp $Hct2 $Hmtdc $Hhazard $Hswitcher]").
    iNext; iIntros (g_tstk) "(HPC & Hctp & Hct2 & Hmtdc & Hhazard_cell & Hslots)".
    iAssert switcher_hazard with "[Hhazard_cell Hslots]" as "Hhazard".
    { iFrame "Hhazard_cell Hslots". }
    (* [.Lswitch_trusted_stack_push]: push the frame *)
    iApply (switcher_trusted_stack_push_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hctp $Hct2 $Hcsp $Hframeoffset $Htstk $Hswitcher]");
      [done|done|].
    iNext.
    iIntros "[
      (%tstk_next' & %Ha_next & %Ha_next_e & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp
        & Hframeoffset & Hframe_csp & Hframe_tbl & Hframe_cnt & Htstk & Hlc)
      |
      (HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hframeoffset & Htstk)
    ]"; cycle 1.
    { iDestruct "Hpost" as "(_ & _ & Hpost & _)".
      iApply ("Hpost" $! g_tstk).
      iFrame "HPC Hcs0 Hcs1 Hctp Hct2 Hcsp Hcra Hcgp Hct1 Hcells Hstk Hmtdc Hframeoffset Hhazard
        Htstk".
      done. }
    (* [.Lswitch_stack_chop]: restrict the stack to the callee's and clear it *)
    iApply (switch_stack_chop_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct2 $Hcsp $Hstk $Hb_switcher $Hswitcher]"); [done|done|done|].
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hct2 & Hcsp & Hstk)".
    (* [.Lswitch_unseal_entry]: unseal the entry point *)
    iApply (switch_unseal_entry_spec with "[- $HPC $Hcs0 $Hct1 $Hswitcher]").
    iSplit; cycle 1.
    { iIntros "(%Hnot_entry & Hcs0 & Hct1)".
      iDestruct "Hpost" as "(_ & Hpost & _)".
      iApply ("Hpost" $! g_tstk).
      iFrame "Hcs0 Hcs1 Hct2 Hctp Hcsp Hcra Hcgp Hct1 Hcells Hstk Hmtdc Hframeoffset
        Hhazard Hframe_csp Hframe_tbl Hframe_cnt Hlc".
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iSplit; first done.
      iExists tstk_next'; iExact "Htstk". }
    iNext; iIntros (wsb π) "(-> & %Htag & HPC & Hcs0 & Hct1)".
    iDestruct "Hpost" as "(Hpost & _)".
    iApply ("Hpost" $! g_tstk wsb π).
    iFrame "HPC Hcs0 Hcs1 Hct2 Hctp Hcsp Hcra Hcgp Hct1 Hcells Hstk Hmtdc Hframeoffset
      Hhazard Hframe_csp Hframe_tbl Hframe_cnt Hlc".
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iExists tstk_next'; iExact "Htstk".
  Qed.

  (** From [.Lswitcher_decode_entry]: read the entry of the export table,
      check the size of the callee's stack, load the callee, clear the
      registers that the callee does not use, enable interrupts if its
      posture asks for it, and jump to the callee. When the callee's stack
      is smaller than the minimum stack size of the entry plus the space
      reserved at its top, the PC is at [.Lswitch_stack_too_small]
      instead. *)
  Lemma switcher_decode_entry_path_spec
    (W : WORLD) (C : CmptName)
    (wcs0 wcs1 wct2 wcgp wcra : LWord) (g_tstk : Locality) (a_frame : Addr) (wtbl : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (b_stk e_stk a_stk : Addr)
    (posture : InterruptStatus) (nargs minstk : nat) (off : Z)
    (arg_rmap rmap : LReg) :
    let a_export_table := (a_frame ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_tbl_cgp := (b_tbl ^+ ExportTable_offset_cgp) in
    (a_tbl ∈ₐ [b_tbl, e_tbl)) ->
    (a_tbl_cgp < a_tbl)%a ->
    is_Some (bpcc + off)%a ->
    (nargs <= 7) ->
    (minstk <= 255) ->
    is_shadow_address a_tbl = false ->
    is_shadow_address b_tbl = false ->
    is_shadow_address a_tbl_cgp = false ->
    is_heap_address bpcc = false ->
    is_heap_cap wcgp_tgt = false ->
    (b_trusted_stack <= a_frame)%a ->
    (a_export_table < e_trusted_stack)%a ->
    a_stk = e_stk ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    b_tbl ↦ₐ□ Cap RX Global bpcc epcc bpcc ∗
    a_tbl_cgp ↦ₐ□ wcgp_tgt ∗
    a_tbl ↦ₐ□ WInt (encode_entry_point posture (Z.of_nat nargs) (Z.of_nat minstk) off) ∗
    PC ↦ₚ[th] switcher_label_pc ".Lswitcher_decode_entry" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ct1 ↦ᵣ[th] Cap RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack a_frame ∗
    a_export_table ↦ₐ wtbl ∗
    cgp ↦ᵣ[th] wcgp ∗
    cra ↦ᵣ[th] wcra ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
    ( [∗ map] r↦w ∈ arg_rmap,
        r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
    regs[th] rmap ∗
    switcher_code ∗
    ▷ ( ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
          ⌜ (Z.of_nat minstk + StackEntry_reserved_space <= e_stk - b_stk)%Z ⌝ ∗
          ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
          ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
          PC ↦ₚ[th] Cap RX Global bpcc epcc (bpcc ^+ off) ∗
          cgp ↦ᵣ[th] wcgp_tgt ∗
          cra ↦ᵣ[th] Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return ∗
          csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (a_stk ^+ (- StackEntry_reserved_space)) ∗
          a_export_table ↦ₐ Cap RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap',
              r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
          regs₀[th] rmap' -∗
          safe[th] )
        ∧
        ( ⌜ (e_stk - b_stk < Z.of_nat minstk + StackEntry_reserved_space)%Z ⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_too_small" ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
          a_export_table ↦ₐ Cap RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap,
              r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
          regs[th] rmap -∗
          safe[th] ) )
    ⊢ safe[th].
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow
               Hbpcc_heap Hwcgp_heap Ha_frame_b Ha_frame_e Ha_stk Hargs Hdom)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp
      & Ha_export_table & Hcgp & Hcra & Hcsp & Hargs & Hregs & #Hswitcher & Hpost)".
    iApply (switcher_decode_entry_spec with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Ha_export_table
          $Hcgp $Hcra $Hcsp $Hswitcher]");
      [done..|].
    iNext; iIntros "[(%Hbig & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Ha_export_table & Hcgp
                     & Hcra & Hcsp)
                   | (%Hsmall & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Ha_export_table & Hcgp
                     & Hcra & Hcsp)]"; cycle 1.
    { (* The callee's stack is too small *)
      iDestruct "Hpost" as "[_ Hpost]".
      iApply "Hpost".
      iFrame "HPC Hcs0 Hcs1 Hct1 Hct2 Hctp Hcgp Hcra Hcsp Ha_export_table Hargs Hregs".
      done. }
    iDestruct "Hpost" as "[Hpost _]".
    iApply (switcher_clear_unused_args_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hargs $Hregs $Hswitcher]");
      [done..|].
    iNext; iIntros (mie arg_rmap' rmap') "(%Harg_rmap' & %Hrmap' & HPC & Hcra & Hargs & Hregs)".
    iApply ("Hpost" $! mie arg_rmap' rmap').
    iFrame "HPC Hcgp Hcra Hcsp Ha_export_table Hargs Hregs".
    done.
  Qed.

  (** Variant of [switcher_decode_entry_path_spec] for a known callee, whose
      arguments are not required to be valid: the argument registers that
      are not cleared keep their initial values. *)
  Lemma switcher_decode_entry_path_known_spec
    (wcs0 wcs1 wct2 wcgp wcra : LWord) (g_tstk : Locality) (a_frame : Addr) (wtbl : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (b_stk e_stk a_stk : Addr)
    (posture : InterruptStatus) (nargs minstk : nat) (off : Z)
    (arg_rmap rmap : LReg) :
    let a_export_table := (a_frame ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_tbl_cgp := (b_tbl ^+ ExportTable_offset_cgp) in
    (a_tbl ∈ₐ [b_tbl, e_tbl)) ->
    (a_tbl_cgp < a_tbl)%a ->
    is_Some (bpcc + off)%a ->
    (nargs <= 7) ->
    (minstk <= 255) ->
    is_shadow_address a_tbl = false ->
    is_shadow_address b_tbl = false ->
    is_shadow_address a_tbl_cgp = false ->
    is_heap_address bpcc = false ->
    is_heap_cap wcgp_tgt = false ->
    (b_trusted_stack <= a_frame)%a ->
    (a_export_table < e_trusted_stack)%a ->
    a_stk = e_stk ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    b_tbl ↦ₐ□ Cap RX Global bpcc epcc bpcc ∗
    a_tbl_cgp ↦ₐ□ wcgp_tgt ∗
    a_tbl ↦ₐ□ WInt (encode_entry_point posture (Z.of_nat nargs) (Z.of_nat minstk) off) ∗
    PC ↦ₚ[th] switcher_label_pc ".Lswitcher_decode_entry" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ct1 ↦ᵣ[th] Cap RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack a_frame ∗
    a_export_table ↦ₐ wtbl ∗
    cgp ↦ᵣ[th] wcgp ∗
    cra ↦ᵣ[th] wcra ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
    regs[th] arg_rmap ∗
    regs[th] rmap ∗
    switcher_code ∗
    ▷ ( ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
          ⌜ (Z.of_nat minstk + StackEntry_reserved_space <= e_stk - b_stk)%Z ⌝ ∗
          ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
          ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
          PC ↦ₚ[th] Cap RX Global bpcc epcc (bpcc ^+ off) ∗
          cgp ↦ᵣ[th] wcgp_tgt ∗
          cra ↦ᵣ[th] Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return ∗
          csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (a_stk ^+ (- StackEntry_reserved_space)) ∗
          a_export_table ↦ₐ Cap RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap',
              r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs)
                       then ⌜ arg_rmap !! r = Some w ⌝
                       else ⌜ w = WInt 0 ⌝ ) ∗
          regs₀[th] rmap' -∗
          safe[th] )
        ∧
        ( ⌜ (e_stk - b_stk < Z.of_nat minstk + StackEntry_reserved_space)%Z ⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_too_small" ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
          a_export_table ↦ₐ Cap RO g_tbl b_tbl e_tbl a_tbl ∗
          regs[th] arg_rmap ∗
          regs[th] rmap -∗
          safe[th] ) )
    ⊢ safe[th].
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow
               Hbpcc_heap Hwcgp_heap Ha_frame_b Ha_frame_e Ha_stk Hargs Hdom)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp
      & Ha_export_table & Hcgp & Hcra & Hcsp & Hargs & Hregs & #Hswitcher & Hpost)".
    iApply (switcher_decode_entry_spec with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Ha_export_table
          $Hcgp $Hcra $Hcsp $Hswitcher]");
      [done..|].
    iNext; iIntros "[(%Hbig & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Ha_export_table & Hcgp
                     & Hcra & Hcsp)
                   | (%Hsmall & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Ha_export_table & Hcgp
                     & Hcra & Hcsp)]"; cycle 1.
    { (* The callee's stack is too small *)
      iDestruct "Hpost" as "[_ Hpost]".
      iApply "Hpost".
      iFrame "HPC Hcs0 Hcs1 Hct1 Hct2 Hctp Hcgp Hcra Hcsp Ha_export_table Hargs Hregs".
      done. }
    iDestruct "Hpost" as "[Hpost _]".
    iApply (switcher_clear_unused_args_known_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hargs $Hregs $Hswitcher]");
      [done..|].
    iNext; iIntros (mie arg_rmap' rmap') "(%Harg_rmap' & %Hrmap' & HPC & Hcra & Hargs & Hregs)".
    iApply ("Hpost" $! mie arg_rmap' rmap').
    iFrame "HPC Hcgp Hcra Hcsp Ha_export_table Hargs Hregs".
    done.
  Qed.

  (** From [.Lswitch_trusted_stack_exhausted]: the trusted stack is
      exhausted. Restore the callee-save registers, clear the registers and
      jump back to the caller with the error code [ENOTENOUGHTRUSTEDSTACK].
      Each restored register is the result of a load, which may clear the
      tag of a saved heap capability. *)
  Lemma switch_trusted_stack_exhausted_path_spec
    (b e a : Addr) (wcs0 wcs1 wcra wcgp : LWord) (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0', cs0 ↦ᵣ[th] wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ[th] wcgp') ∗
    (∃ wcra', cra ↦ᵣ[th] wcra') ∗
    (∃ wca0, ca0 ↦ᵣ[th] wca0) ∗
    (∃ wca1, ca1 ↦ᵣ[th] wca1) ∗
    csp ↦ᵣ[th] Cap RWL Local b e (stk_saved_a a) ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    regs[th] rmap ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs0 rcs1,
        ⌜ load_heap wcgp rcgp ∧ load_heap wcra rcra ∧
          load_heap wcs0 rcs0 ∧ load_heap wcs1 rcs1 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cs0 ↦ᵣ[th] rcs0 ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        cgp ↦ᵣ[th] rcgp ∗
        cra ↦ᵣ[th] rcra ∗
        ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ[th] WInt 0 ∗
        csp ↦ᵣ[th] Cap RWL Local b e a ∗
        switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
        regs₀[th] rmap' ∗
        £ 1 -∗
        ( PC ↦ₚ[th] lupdatePcPerm rcra ∗
          £ 1 -∗
          safe[th] ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
            (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Hcells & Hrmap & #Hswitcher & Hpost)".
    rewrite /stk_saved_a -/(stk_spill_a a).
    assert (stk_spill_a a ^+ SpillSlot_size = a) as Hspill_top
      by (clear -Ha4; revert Ha4; stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size))
      as Hspill4 by (clear -Ha4; revert Ha4; stk_unfold; solve_addr).
    iApply (switch_trusted_stack_exhausted_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp $Hcells $Hswitcher]");
      [done|done|exact (proj2 Hba3)|exact Hspill4|].
    iNext.
    iIntros (rcgp rcra rcs0 rcs1 Hrestored)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp & Hcells & Hlc)".
    iEval (rewrite Hspill_top) in "Hcsp".
    iApply (switch_callee_dead_zeros_spec with "[- $HPC $Hcra $Hrmap $Hswitcher]"); first done.
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1).
    iFrame "Hcs0 Hcs1 Hcgp Hcra Hca0 Hca1 Hcsp Hcells Hrmap Hlc".
    done.
  Qed.

  (** Variant of [switch_trusted_stack_exhausted_path_spec] in a world [W]:
      each restored register retains its authority in [W]. *)
  Lemma switch_trusted_stack_exhausted_path_world_spec
    (W : WORLD) (C : CmptName)
    (b e a : Addr) (wcs0 wcs1 wcra wcgp : LWord) (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0', cs0 ↦ᵣ[th] wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ[th] wcgp') ∗
    (∃ wcra', cra ↦ᵣ[th] wcra') ∗
    (∃ wca0, ca0 ↦ᵣ[th] wca0) ∗
    (∃ wca1, ca1 ↦ᵣ[th] wca1) ∗
    csp ↦ᵣ[th] Cap RWL Local b e (stk_saved_a a) ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    world_interp W C ∗
    regs[th] rmap ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs0 rcs1,
        ⌜ load_heap_in_world W wcgp rcgp ∧ load_heap_in_world W wcra rcra ∧
          load_heap_in_world W wcs0 rcs0 ∧ load_heap_in_world W wcs1 rcs1 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        world_interp W C ∗
        cs0 ↦ᵣ[th] rcs0 ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        cgp ↦ᵣ[th] rcgp ∗
        cra ↦ᵣ[th] rcra ∗
        ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ[th] WInt 0 ∗
        csp ↦ᵣ[th] Cap RWL Local b e a ∗
        switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
        regs₀[th] rmap' ∗
        £ 1 -∗
        ( PC ↦ₚ[th] lupdatePcPerm rcra ∗
          £ 1 -∗
          safe[th] ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
            (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Hcells & Hworld & Hrmap & #Hswitcher & Hpost)".
    rewrite /stk_saved_a -/(stk_spill_a a).
    assert (stk_spill_a a ^+ SpillSlot_size = a) as Hspill_top
      by (clear -Ha4; revert Ha4; stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size))
      as Hspill4 by (clear -Ha4; revert Ha4; stk_unfold; solve_addr).
    iApply (switch_trusted_stack_exhausted_world_spec W C with
      "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp $Hcells $Hworld $Hswitcher]");
      [done|done|exact (proj2 Hba3)|exact Hspill4|].
    iNext.
    iIntros (rcgp rcra rcs0 rcs1 Hrestored)
      "(Hworld & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp & Hcells & Hlc)".
    iEval (rewrite Hspill_top) in "Hcsp".
    iApply (switch_callee_dead_zeros_spec with "[- $HPC $Hcra $Hrmap $Hswitcher]"); first done.
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1).
    iFrame "Hworld Hcs0 Hcs1 Hcgp Hcra Hca0 Hca1 Hcsp Hcells Hrmap Hlc".
    done.
  Qed.

End Call_Path.
