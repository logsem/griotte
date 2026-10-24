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
    and the logical-relation specifications share: from
    [.Lswitch_entry_first_spill] to the chop of the stack, from
    [.Lswitch_stack_chop] to the decoding of the entry point, from
    [.Lswitcher_decode_entry] to the callee, and from
    [.Lswitch_trusted_stack_exhausted] back to the caller. *)

Section Call_Path.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_entry_first_spill]: spill the callee-save registers in
      the spill area of the caller's stack, below its cursor [a], and push a
      frame with the stack pointer on the trusted stack, whose topmost frame
      is at [a_tstk]. The cursor is not above the top of the stack: the
      spill faults only when it does not fit, at its first store, with
      nothing written. *)
  Lemma switch_entry_first_spill_path_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp wctp wct2 : LWord)
    (d : nat) (a_tstk : Addr) (tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_free := (a_next ^+ TrustedStackFrame_size)%a in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    disjoint_from_mmio b e ->
    stk_cursor_ok b e a ->
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->

    PC ↦ₚ switcher_label_pc ".Lswitch_entry_first_spill" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    cgp ↦ᵣ wcgp ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b e a ∗
    [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_code ∗
    ▷ ( ⌜ switcher_stk_bounds b e a ⌝ ∗
        cra ↦ᵣ wcra ∗
        cgp ↦ᵣ wcgp ∗
        csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
        switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem_callee stk_mem ]] ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        switcher_code ∗
        ( ( ⌜ (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_next ⌝ ∗
            ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
            PC ↦ₚ switcher_label_pc ".Lswitch_stack_chop" ∗
            cs0 ↦ᵣ WInt (tstack_frameoffset (S d)) ∗
            cs1 ↦ᵣ WInt b_trusted_stack ∗
            ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_next ∗
            ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
            a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
            a_csp ↦ₐ WCap true RWL Local b e (stk_saved_a a) ∗
            a_export_table ↦ₐ WInt 0 ∗
            a_error_count ↦ₐ WInt 0 ∗
            (∃ tstk_next', [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]]) ∗
            £ 2 )
          ∨
          ( PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
            cs0 ↦ᵣ WInt 0 ∗
            cs1 ↦ᵣ WInt b_trusted_stack ∗
            ctp ↦ᵣ WInt (tstack_frameoffset d) ∗
            ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
            a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
            [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ) )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
    ( ⌜ ¬ stk_spill_fits b e a ⌝ -∗
        cs0 ↦ᵣ wcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cra ↦ᵣ wcra ∗
        cgp ↦ᵣ wcgp ∗
        ctp ↦ᵣ wctp ∗
        ct2 ↦ᵣ wct2 ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ stk_mem ]] ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
        trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hstk_mmio Hcursor Ha_tstk Ha_tstk_e)
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hctp & Hct2 & Hcsp & Hstk
      & Hmtdc & Hframeoffset & Htstk & #Hswitcher & Hpost)".
    iApply (switch_entry_first_spill_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hcsp $Hstk $Hswitcher]"); [done|done|].
    iSplit; cycle 1.
    { iIntros (Hnfits) "(Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hstk)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[//]").
      iFrame "Hcs0 Hcs1 Hcra Hcgp Hctp Hct2 Hcsp Hstk Hmtdc Hframeoffset Htstk". }
    iDestruct "Hpost" as "[Hpost _]".
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hcells & Hstk & %Hbounds)".
    iApply (switcher_trusted_stack_push_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hctp $Hct2 $Hcsp $Hmtdc $Hframeoffset $Htstk $Hswitcher]");
      [done|done|].
    iNext.
    iIntros "[
      (%tstk_next' & %Ha_frame & %Ha_frame_e & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hmtdc
        & Hframeoffset & Hframe_csp & Hframe_tbl & Hframe_cnt & Htstk & Hlc)
      |
      (HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hmtdc & Hframeoffset & Htstk)
    ]".
    - iApply "Hpost".
      iFrame "Hcra Hcgp Hcsp Hcells Hstk Hmtdc Hswitcher".
      iSplit; first done.
      iLeft.
      iFrame "HPC Hcs0 Hcs1 Hctp Hct2 Hframeoffset Hframe_csp Hframe_tbl Hframe_cnt Htstk Hlc".
      done.
    - iApply "Hpost".
      iFrame "Hcra Hcgp Hcsp Hcells Hstk Hmtdc Hswitcher".
      iSplit; first done.
      iRight.
      iFrame "HPC Hcs0 Hcs1 Hctp Hct2 Hframeoffset Htstk".
  Qed.

  (** From [.Lswitch_stack_chop]: restrict the stack capability to the
      callee's stack, below the spill area, clear it, load the unsealing
      capability, and unseal the entry point [wct1]. The load of
      [.Lswitcher_decode_entry] faults when [wct1] is not a valid entry
      point sealed by the switcher. *)
  Lemma switch_stack_chop_path_spec
    (b e a : Addr) (stk_mem : list LWord) (wcs0 wcs1 wct1 wct2 : LWord) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->

    PC ↦ₚ switcher_label_pc ".Lswitch_stack_chop" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    b_switcher ↦ₐ□ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    ct1 ↦ᵣ wct1 ∗
    switcher_code ∗
    ▷ ( ∀ wsb π,
        ⌜ wct1 = WSealed ot_switcher wsb @@? π ⌝ ∗
        ⌜ get_tag_sealable wsb = true ⌝ ∗
        PC ↦ₚ switcher_label_pc ".Lswitcher_decode_entry" ∗
        cs0 ↦ᵣ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
        (∃ wct2', ct2 ↦ᵣ wct2') ∗
        csp ↦ᵣ callee_csp b e a ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
        b_switcher ↦ₐ□ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        ct1 ↦ᵣ WSealable wsb @@? π ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
    ( ⌜ ¬ ∃ wsb π, wct1 = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ -∗
      cs0 ↦ᵣ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
      (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
      (∃ wct2', ct2 ↦ᵣ wct2') ∗
      csp ↦ᵣ callee_csp b e a ∗
      [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
        [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
      ct1 ↦ᵣ - -∗
      trap_safe (switcher_label_pc ".Lswitcher_decode_entry") ⊤
        (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hbounds Hstk_mmio Hstk_heap)
      "(HPC & Hcs0 & Hcs1 & Hct2 & Hcsp & Hstk & #Hb_switcher & Hct1 & #Hswitcher & Hpost)".
    iApply (switch_stack_chop_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct2 $Hcsp $Hstk $Hb_switcher $Hswitcher]"); [done|done|done|].
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hct2 & Hcsp & Hstk)".
    iApply (switch_unseal_entry_spec with "[- $HPC $Hcs0 $Hct1 $Hswitcher]").
    iSplit; cycle 1.
    { iIntros "(%Hnot_entry & Hcs0 & Hct1)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[//]").
      iFrame "Hcs0 Hcs1 Hct2 Hcsp Hstk Hct1". }
    iDestruct "Hpost" as "[Hpost _]".
    iNext; iIntros (wsb π) "(-> & %Htag & HPC & Hcs0 & Hct1)".
    iApply "Hpost".
    iFrame "HPC Hcs0 Hcs1 Hct2 Hcsp Hstk Hb_switcher Hct1 Hswitcher".
    done.
  Qed.

  (** From [.Lswitcher_decode_entry]: read the entry of the export table,
      check the size of the callee's stack, load the callee, clear the
      registers that the callee does not use, enable interrupts if its
      posture asks for it, and jump to the callee. When the callee's stack
      is smaller than the minimum stack size of the entry, the PC is at
      [.Lswitch_stack_too_small] instead. *)
  Lemma switcher_decode_entry_path_spec
    (W : WORLD) (C : CmptName)
    (wcs0 wcs1 wct2 wcgp wcra : LWord) (a_frame : Addr) (wtbl : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (b_stk e_stk a_stk : Addr)
    (posture : InterruptStatus) (nargs minstk : nat) (off : Z)
    (arg_rmap rmap : LReg) :
    let a_export_table := (a_frame ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_tbl_cgp := (b_tbl ^+ ExportTable_offset_cgp)%a in
    (b_tbl <= a_tbl < e_tbl)%a ->
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
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    b_tbl ↦ₐ□ WCap true RX Global bpcc epcc bpcc ∗
    a_tbl_cgp ↦ₐ□ wcgp_tgt ∗
    a_tbl ↦ₐ□ WInt (encode_entry_point posture (Z.of_nat nargs) (Z.of_nat minstk) off) ∗
    PC ↦ₚ switcher_label_pc ".Lswitcher_decode_entry" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_frame ∗
    a_export_table ↦ₐ wtbl ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
    ( [∗ map] r↦w ∈ arg_rmap,
        r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
          ⌜ (Z.of_nat minstk <= e_stk - b_stk)%Z ⌝ ∗
          ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
          ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
          PC ↦ₚ WCap true RX Global bpcc epcc (bpcc ^+ off)%a ∗
          cgp ↦ᵣ wcgp_tgt ∗
          cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
          a_export_table ↦ₐ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap',
              r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
          ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
        ∧
        ( ⌜ (e_stk - b_stk < Z.of_nat minstk)%Z ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitch_stack_too_small" ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
          a_export_table ↦ₐ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap,
              r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
          ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow
               Hbpcc_heap Hwcgp_heap Ha_frame_b Ha_frame_e Hargs Hdom)
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
      iFrame "HPC Hcs0 Hcs1 Hct1 Hct2 Hctp Hcgp Hcra Hcsp Ha_export_table Hargs Hregs
        Hswitcher".
      done. }
    iDestruct "Hpost" as "[Hpost _]".
    iApply (switcher_clear_unused_args_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hargs $Hregs $Hswitcher]");
      [done..|].
    iNext; iIntros (mie arg_rmap' rmap') "(%Harg_rmap' & %Hrmap' & HPC & Hcra & Hargs & Hregs)".
    iApply ("Hpost" $! mie arg_rmap' rmap').
    iFrame "HPC Hcgp Hcra Hcsp Ha_export_table Hargs Hregs Hswitcher".
    done.
  Qed.

  (** Variant of [switcher_decode_entry_path_spec] for a known callee, whose
      arguments are not required to be valid: the argument registers that
      are not cleared keep their initial values. *)
  Lemma switcher_decode_entry_path_known_spec
    (wcs0 wcs1 wct2 wcgp wcra : LWord) (a_frame : Addr) (wtbl : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (b_stk e_stk a_stk : Addr)
    (posture : InterruptStatus) (nargs minstk : nat) (off : Z)
    (arg_rmap rmap : LReg) :
    let a_export_table := (a_frame ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_tbl_cgp := (b_tbl ^+ ExportTable_offset_cgp)%a in
    (b_tbl <= a_tbl < e_tbl)%a ->
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
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    b_tbl ↦ₐ□ WCap true RX Global bpcc epcc bpcc ∗
    a_tbl_cgp ↦ₐ□ wcgp_tgt ∗
    a_tbl ↦ₐ□ WInt (encode_entry_point posture (Z.of_nat nargs) (Z.of_nat minstk) off) ∗
    PC ↦ₚ switcher_label_pc ".Lswitcher_decode_entry" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_frame ∗
    a_export_table ↦ₐ wtbl ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
    ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w ) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
          ⌜ (Z.of_nat minstk <= e_stk - b_stk)%Z ⌝ ∗
          ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
          ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
          PC ↦ₚ WCap true RX Global bpcc epcc (bpcc ^+ off)%a ∗
          cgp ↦ᵣ wcgp_tgt ∗
          cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
          a_export_table ↦ₐ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap',
              r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs)
                       then ⌜ arg_rmap !! r = Some w ⌝
                       else ⌜ w = WInt 0 ⌝ ) ∗
          ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
        ∧
        ( ⌜ (e_stk - b_stk < Z.of_nat minstk)%Z ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitch_stack_too_small" ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
          a_export_table ↦ₐ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w ) ∗
          ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow
               Hbpcc_heap Hwcgp_heap Ha_frame_b Ha_frame_e Hargs Hdom)
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
      iFrame "HPC Hcs0 Hcs1 Hct1 Hct2 Hctp Hcgp Hcra Hcsp Ha_export_table Hargs Hregs
        Hswitcher".
      done. }
    iDestruct "Hpost" as "[Hpost _]".
    iApply (switcher_clear_unused_args_known_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hargs $Hregs $Hswitcher]");
      [done..|].
    iNext; iIntros (mie arg_rmap' rmap') "(%Harg_rmap' & %Hrmap' & HPC & Hcra & Hargs & Hregs)".
    iApply ("Hpost" $! mie arg_rmap' rmap').
    iFrame "HPC Hcgp Hcra Hcsp Ha_export_table Hargs Hregs Hswitcher".
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

    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs0 rcs1,
        ⌜ load_heap wcgp rcgp ∧ load_heap wcra rcra ∧
          load_heap wcs0 rcs0 ∧ load_heap wcs1 rcs1 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cs0 ↦ᵣ rcs0 ∗
        cs1 ↦ᵣ rcs1 ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ WInt 0 ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 1 -∗
        ( PC ↦ₚ lupdatePcPerm rcra ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Hcells & Hrmap & #Hswitcher & Hpost)".
    rewrite /stk_saved_a -/(stk_spill_a a).
    assert ((stk_spill_a a ^+ SpillSlot_size)%a = a) as Hspill_top
      by (clear -Ha4; revert Ha4; stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size)%a)
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
    iFrame "Hcs0 Hcs1 Hcgp Hcra Hca0 Hca1 Hcsp Hcells Hrmap Hswitcher Hlc".
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

    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    world_interp W C ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs0 rcs1,
        ⌜ load_heap_in_world W wcgp rcgp ∧ load_heap_in_world W wcra rcra ∧
          load_heap_in_world W wcs0 rcs0 ∧ load_heap_in_world W wcs1 rcs1 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        world_interp W C ∗
        cs0 ↦ᵣ rcs0 ∗
        cs1 ↦ᵣ rcs1 ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ WInt 0 ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 1 -∗
        ( PC ↦ₚ lupdatePcPerm rcra ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Hcells & Hworld & Hrmap & #Hswitcher & Hpost)".
    rewrite /stk_saved_a -/(stk_spill_a a).
    assert ((stk_spill_a a ^+ SpillSlot_size)%a = a) as Hspill_top
      by (clear -Ha4; revert Ha4; stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size)%a)
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
    iFrame "Hworld Hcs0 Hcs1 Hcgp Hcra Hca0 Hca1 Hcsp Hcells Hrmap Hswitcher Hlc".
    done.
  Qed.

End Call_Path.
