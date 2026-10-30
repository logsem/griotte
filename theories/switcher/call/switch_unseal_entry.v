From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_preamble wp_rules_interp.

(** * Call routine: unseal and decode the entry point

    [.Lswitch_unseal_entry] unseals the entry point of the callee with the
    unsealing capability of the switcher. [.Lswitcher_decode_entry] reads
    the offset of the entry, stores the export table in the new frame,
    reads the minimum stack size of the entry and checks that the callee's
    stack holds it plus the space reserved at its top
    ([StackEntry_reserved_space]): otherwise, it jumps to
    [.Lswitch_stack_too_small]. On success, it moves the cursor of the stack
    below the reserved space, reads the flags of the entry and moves the
    export table to its base. [.Lswitch_callee_load] loads the CGP and the
    PCC of the callee, and falls through to
    [.Lswitch_load_zero_arguments_start]. *)

Section Switch_Unseal_Entry.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_unseal_entry]: unseal the entry point [wct1]. When
      [wct1] is not a valid entry point sealed by the switcher, the load of
      [.Lswitcher_decode_entry] faults. *)
  Lemma switch_unseal_entry_spec (wct1 : LWord) :
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_unseal_entry" ∗
    cs0 ↦ᵣ[th] SealRange (true, true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
    ct1 ↦ᵣ[th] wct1 ∗
    switcher_code ∗
    ( ▷ ( ∀ wsb π,
          ⌜ wct1 = WSealed ot_switcher wsb @@? π ⌝ ∗
          ⌜ get_tag_sealable wsb = true ⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitcher_decode_entry" ∗
          cs0 ↦ᵣ[th] SealRange (true, true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
          ct1 ↦ᵣ[th] WSealable wsb @@? π -∗
          safe[th] ) ∧
      ( ⌜ ¬ ∃ wsb π, wct1 = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ ∗
        cs0 ↦ᵣ[th] SealRange (true, true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
        ct1 ↦ᵣ[th] - -∗
        trap_safe (switcher_label_pc ".Lswitcher_decode_entry") ⊤
          (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros "(HPC & Hcs0 & Hct1 & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitch_unseal_entry" "Hswitcher" as "Hcode" a_unseal Ha_unseal.
    assert (a_unseal ^+ 1 =
            (a_switcher_call ^+ switcher_label_offset ".Lswitcher_decode_entry")%a)
      as Hpc_decode by switcher_addr_eq.
    (* UnSeal ct1 cs0 ct1 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown_sealed _ _ _ _ _ _
              (a_unseal ^+ 1)
             with "[$HPC $Hi $Hcs0 $Hct1]"); try done; try solve_pure.
    { pose proof ot_switcher_size; solve_addr. }
    iIntros "!>" (ret)
      "[(-> & HPC & Hi & Hcs0 & Hct1 & %Hnot_sealed) |
       [(%o & %wsb & %π & -> & HPC & Hi & Hcs0 & Hct1 & %Hwct1 & %Htag & %Hrange)
       |(%ot & %sb & %π & -> & HPC & Hi & Hcs0 & Hct1 & %Hwct1 & %Hinvalid)] ]".
    { (* The operand is not sealed: it loses its tag, and the next load
         faults *)
      wp_pure.
      iClear "Hi".
      iDestruct "Hpost" as "[_ Hfailed]".
      iDestruct (map_of_regs_2 with "Hcs0 Hct1") as "[Hmap %Hne]".
      (* CLoad cs0 ct1 0 *)
      iInstrApply "Hcode" (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (lclear_tag wct1))
        with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
      iDestruct (regs_of_map_2 with "Hmap") as "[Hcs0 Hct1]"; first done.
      rewrite Hpc_decode.
      iTrap with "Hfailed".
      iPureIntro; intros (wsb & π & -> & _); done. }
    2: { (* The unsealed entry point is invalid: the next load faults *)
         simplify_eq.
         wp_pure.
         iClear "Hi".
         iDestruct "Hpost" as "[_ Hfailed]".
         iDestruct (map_of_regs_2 with "Hcs0 Hct1") as "[Hmap %Hne]".
         (* CLoad cs0 ct1 0 *)
         iInstrApply "Hcode"
           (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _
              (WSealable (clear_tag_sealable (unseal_sb Global sb)) @@? π))
           with "[$HPC $Hmap]" as "(HPC & Hmap)".
         { rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
         iDestruct (regs_of_map_2 with "Hmap") as "[Hcs0 Hct1]"; first done.
         rewrite Hpc_decode.
         iTrap with "Hfailed".
         iPureIntro; intros (wsb & π0 & Heq & Htag); simplify_eq.
         rewrite Htag /= in Hinvalid.
         rewrite /withinBounds in Hinvalid; pose proof ot_switcher_size; solve_addr. }
    simplify_eq.
    apply withinBounds_le_addr in Hrange.
    assert (o = ot_switcher) as -> by solve_addr.
    iEval (rewrite unseal_global) in "Hct1".
    wp_pure.
    iClear "Hi".
    iDestruct "Hpost" as "[Hpost _]".
    iEval (rewrite Hpc_decode) in "HPC".
    iApply "Hpost"; iFrame "HPC Hcs0 Hct1"; done.
  Qed.

  (** From [.Lswitcher_decode_entry]: read the entry of the export table,
      store the export table in the frame at [a_frame], check the size of
      the callee's stack, whose cursor is at its top, move the cursor below
      the reserved space, write the cursor to MSHWM, read the flags of the
      entry, and load the CGP and the PCC of the callee. A raise of MSHWM
      takes the cells of the zone between MSHWMB, or the old MSHWM when it is
      above, and the new value. When the callee's stack is smaller than the
      minimum stack size of the entry plus the reserved space, the PC is at
      [.Lswitch_stack_too_small]. *)
  Lemma switcher_decode_entry_spec
    (wcs0 wcs1 wct2 wcgp wcra : LWord) (g_tstk : Locality) (a_frame : Addr) (wtbl : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (b_stk e_stk a_stk : Addr)
    (posture : InterruptStatus) (nargs minstk : nat) (off : Z)
    (hb h : Z) (lo : Addr) :
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
    (Z.max hb h = lo)%Z ->

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
    hwm_regs hb h ∗
    (* the cells that a raise of MSHWM to the callee's stack pointer covers *)
    ([∗ list] a' ∈ finz.seq_between lo (a_stk ^+ (- StackEntry_reserved_space)),
       zone_cell[th] a') ∗
    switcher_code ∗
    ▷ ( ( ⌜ (Z.of_nat minstk + StackEntry_reserved_space <= e_stk - b_stk)%Z ⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitch_load_zero_arguments_start" ∗
          cs0 ↦ᵣ[th] WInt off ∗
          cs1 ↦ᵣ[th] WInt b_tbl ∗
          ct1 ↦ᵣ[th] Cap RO g_tbl b_tbl e_tbl b_tbl ∗
          ct2 ↦ᵣ[th] WInt (e_stk - b_stk) ∗
          ctp ↦ᵣ[th] WInt (entry_point_flags posture (Z.of_nat nargs)) ∗
          a_export_table ↦ₐ Cap RO g_tbl b_tbl e_tbl a_tbl ∗
          cgp ↦ᵣ[th] wcgp_tgt ∗
          cra ↦ᵣ[th] Cap RX Global bpcc epcc (bpcc ^+ off) ∗
          csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (a_stk ^+ (- StackEntry_reserved_space)) ∗
          hwm_regs hb (a_stk ^+ (- StackEntry_reserved_space)) ∗
          ([∗ list] a' ∈ finz.seq_between lo (a_stk ^+ (- StackEntry_reserved_space)),
             zone_cell[th] a') )
        ∨
        ( ⌜ (e_stk - b_stk < Z.of_nat minstk + StackEntry_reserved_space)%Z ⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_too_small" ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗
          a_export_table ↦ₐ Cap RO g_tbl b_tbl e_tbl a_tbl ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
          hwm_regs hb h ∗
          ([∗ list] a' ∈ finz.seq_between lo (a_stk ^+ (- StackEntry_reserved_space)),
             zone_cell[th] a') )
        -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow
               Hbpcc_heap Hwcgp_heap Ha_frame_b Ha_frame_e Ha_stk Hlo)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2
      & Hctp & Ha_export_table & Hcgp & Hcra & Hcsp & Hhwm & Hcells & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_load"; first iFrame "Hswitcher".
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((a_frame + TrustedStackFrame_offset_calleeExportTable)%a
            = Some (a_frame ^+ TrustedStackFrame_offset_calleeExportTable))
      as Ha_export_table by (tstack_unfold; solve_addr).

    (* [.Lswitcher_decode_entry] *)
    switcher_open_label ".Lswitch_unseal_entry" "Hswitcher" as "Hcode".
    switcher_pc_in_block ".Lswitch_unseal_entry" ".Lswitcher_decode_entry" "HPC".
    switcher_hide "Hpost" as hpost.
    (* CLoad cs0 ct1 0 *)
    iInstr "Hcode".
    { done. }
    { split; auto. rewrite /withinBounds. solve_addr. }
    (* LShiftR cs0 cs0 ExportEntry_functionStart_shift *)
    iInstr "Hcode".
    rewrite encode_entry_point_eq_off.
    (* Store ctp ct1 TrustedStackFrame_offset_calleeExportTable *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    rewrite lstore_word_isWL; last reflexivity.
    (* CLoad ctp ct1 0 *)
    iInstr "Hcode".
    { done. }
    { split; auto. rewrite /withinBounds. solve_addr. }
    (* LShiftR ctp ctp ExportEntry_minimumStackSize_shift *)
    iInstr "Hcode".
    (* LAnd ctp ctp ExportEntry_byte_mask *)
    iInstr "Hcode".
    (* GetLen ct2 csp *)
    iInstr "Hcode".
    (* Add ctp ctp StackEntry_reserved_space *)
    iInstr "Hcode".
    rewrite encode_entry_point_eq_minstk; last lia.
    (* The instruction tactics unfold [StackEntry_reserved_space] to [2]: fold it back. *)
    iEval (change 2%Z with StackEntry_reserved_space) in "Hctp".
    destruct (decide (e_stk - b_stk < Z.of_nat minstk + StackEntry_reserved_space)%Z)
      as [Hsmall|Hsmall].
    { (* Jlt .Lswitch_stack_too_small ct2 ctp *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hct2 $Hctp]"
        as "(HPC & Hct2 & Hctp)".
      { cbn [jcond_test get_a lw]; apply Z.ltb_lt; lia. }
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lswitch_stack_too_small")%a
          by switcher_addr_eq. }
      subst hpost.
      iApply "Hpost"; iRight.
      iFrame "HPC Hcs0 Hcs1 Hct1 Hct2 Hctp Ha_export_table Hcgp Hcra Hcsp Hhwm Hcells".
      done. }
    (* Jlt .Lswitch_stack_too_small ct2 ctp *)
    iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hct2 $Hctp]"
      as "(HPC & Hct2 & Hctp)".
    { cbn [jcond_test get_a lw]; apply Z.ltb_ge; lia. }
    (* Lea csp csp (- StackEntry_reserved_space) *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ (- StackEntry_reserved_space))); last reflexivity.
      clear -Ha_stk Hsmall; subst a_stk; unfold StackEntry_reserved_space in *; solve_addr. }
    (* SpecialRW cnull MSHWM (inr csp) *)
    iInstrApply "Hcode" wp_csrw_mshwm_gen with "[$HPC $Hcsp $Hhwm $Hcells]"
      as "(HPC & Hcsp & Hhwm & Hcells)".
    { done. }
    (* CLoad ctp ct1 0 *)
    iInstr "Hcode".
    { done. }
    { split; auto. rewrite /withinBounds. solve_addr. }
    (* LAnd ctp ctp ExportEntry_byte_mask *)
    iInstr "Hcode".
    rewrite encode_entry_point_eq_flags.
    (* GetB cs1 ct1 *)
    iInstr "Hcode".
    (* SetA ct1 ct1 cs1 *)
    iInstr "Hcode".

    (* [.Lswitch_callee_load] *)
    switcher_open_label ".Lswitch_callee_load" "Hswitcher_load" as "Hcode_load".
    assert (is_heap_cap (Cap RX Global bpcc epcc bpcc) = false) as Hpcc_not_heap.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbpcc_heap /=.
      reflexivity. }
    assert ((b_tbl + ExportTable_offset_cgp)%a = Some (b_tbl ^+ ExportTable_offset_cgp))
      as Htbl_cgp_addr by solve_addr.
    assert ((b_tbl + ExportTable_offset_pcc)%a = Some b_tbl) as Htbl_pcc_addr by solve_addr.
    (* CLoad cgp ct1 ExportTable_offset_cgp *)
    iInstr "Hcode_load".
    { split; auto. rewrite /withinBounds; solve_addr. }
    (* CLoad cra ct1 ExportTable_offset_pcc *)
    iInstr "Hcode_load".
    { split; auto. rewrite /withinBounds; solve_addr. }
    destruct Hentry as [a_entry Hentry].
    (* Lea cra cra cs0 *)
    iInstr "Hcode_load".
    replace a_entry with (bpcc ^+ off) by solve_addr.
    switcher_change_pc_label ".Lswitch_load_zero_arguments_start".
    subst hpost.
    iApply "Hpost"; iLeft.
    iFrame "HPC Hcs0 Hcs1 Hct1 Hct2 Hctp Ha_export_table Hcgp Hcra Hcsp Hhwm Hcells".
    iPureIntro; lia.
  Qed.

End Switch_Unseal_Entry.
