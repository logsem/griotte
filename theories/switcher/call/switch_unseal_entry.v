From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_preamble wp_rules_interp.

(** * Call routine: unseal and decode the entry point

    [.Lswitch_unseal_entry] unseals the entry point of the callee with the
    unsealing capability of the switcher. [.Lswitcher_decode_entry] reads
    the entry of the export table, stores the export table in the new
    frame, decodes the number of arguments, the interrupt posture and the
    minimum stack size, and checks that the callee's stack holds the
    minimum stack size plus the space reserved at its top
    ([StackEntry_reserved_space]): otherwise,
    [.Lswitch_stack_too_small_branch] jumps to [.Lswitch_stack_too_small].
    On success, it moves the cursor of the stack below the reserved space.
    [.Lswitcher_prepare_callee] loads the PCC and the CGP of the callee, and
    falls through to [.Lswitcher_clear_unused_args]. *)

Section Switch_Unseal_Entry.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_unseal_entry]: unseal the entry point [wct1]. When
      [wct1] is not a valid entry point sealed by the switcher, the load of
      [.Lswitcher_decode_entry] faults. *)
  Lemma switch_unseal_entry_spec (wct1 : LWord) :
    PC ↦ₚ switcher_label_pc ".Lswitch_unseal_entry" ∗
    cs0 ↦ᵣ WSealRange true (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    ct1 ↦ᵣ wct1 ∗
    switcher_code ∗
    ( ▷ ( ∀ wsb π,
          ⌜ wct1 = WSealed ot_switcher wsb @@? π ⌝ ∗
          ⌜ get_tag_sealable wsb = true ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitcher_decode_entry" ∗
          cs0 ↦ᵣ WSealRange true (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
          ct1 ↦ᵣ WSealable wsb @@? π -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
      ( ⌜ ¬ ∃ wsb π, wct1 = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ ∗
        cs0 ↦ᵣ WSealRange true (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        ct1 ↦ᵣ - -∗
        trap_safe (switcher_label_pc ".Lswitcher_decode_entry") ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hcs0 & Hct1 & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitch_unseal_entry" "Hswitcher" as "Hcode" a_unseal Ha_unseal.
    assert ((a_unseal ^+ 1)%a =
            (a_switcher_call ^+ switcher_label_offset ".Lswitcher_decode_entry")%a)
      as Hpc_decode by switcher_addr_eq.
    (* UnSeal ct1 cs0 ct1 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown_sealed _ _ _ _ _ _
              (a_unseal ^+ 1)%a
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
      the reserved space, and load the PCC and CGP of the callee. When the
      callee's stack is smaller than the minimum stack size of the entry
      plus the reserved space, the PC is at [.Lswitch_stack_too_small]. *)
  Lemma switcher_decode_entry_spec
    (wcs0 wcs1 wct2 wcgp wcra : LWord) (a_frame : Addr) (wtbl : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (b_stk e_stk a_stk : Addr)
    (posture : InterruptStatus) (nargs minstk : nat) (off : Z) :
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
    a_stk = e_stk ->

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
    switcher_code ∗
    ▷ ( ( ⌜ (Z.of_nat minstk + StackEntry_reserved_space <= e_stk - b_stk)%Z ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitcher_clear_unused_args" ∗
          cs0 ↦ᵣ WInt off ∗
          cs1 ↦ᵣ WInt (Z.of_nat minstk + StackEntry_reserved_space) ∗
          ct1 ↦ᵣ WCap true RO g_tbl b_tbl e_tbl a_tbl_cgp ∗
          ct2 ↦ᵣ WInt (Z.of_nat nargs + 1) ∗
          ctp ↦ᵣ WInt (entry_point_posture posture) ∗
          a_export_table ↦ₐ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          cgp ↦ᵣ wcgp_tgt ∗
          cra ↦ᵣ WCap true RX Global bpcc epcc (bpcc ^+ off)%a ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ (- StackEntry_reserved_space))%a )
        ∨
        ( ⌜ (e_stk - b_stk < Z.of_nat minstk + StackEntry_reserved_space)%Z ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitch_stack_too_small" ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          a_export_table ↦ₐ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow
               Hbpcc_heap Hwcgp_heap Ha_frame_b Ha_frame_e Ha_stk)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2
      & Hctp & Ha_export_table & Hcgp & Hcra & Hcsp & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_prep"; first iFrame "Hswitcher".
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((a_frame + TrustedStackFrame_offset_calleeExportTable)%a
            = Some (a_frame ^+ TrustedStackFrame_offset_calleeExportTable)%a)
      as Ha_export_table by (tstack_unfold; solve_addr).

    (* [.Lswitcher_decode_entry] *)
    switcher_open_label ".Lswitch_unseal_entry" "Hswitcher" as "Hcode".
    switcher_pc_in_block ".Lswitch_unseal_entry" ".Lswitcher_decode_entry" "HPC".
    switcher_hide "Hpost" as hpost.
    (* CLoad cs0 ct1 0 *)
    iInstr "Hcode".
    { done. }
    { split; auto. rewrite /withinBounds. solve_addr. }
    (* Store ctp ct1 TrustedStackFrame_offset_calleeExportTable *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    rewrite lstore_word_isWL; last reflexivity.
    (* LAnd ct2 cs0 7 *)
    iInstr "Hcode".
    (* LAnd ctp cs0 entry_point_irq_disabled_mask *)
    iInstr "Hcode".
    (* LShiftR cs1 cs0 8 *)
    iInstr "Hcode".
    (* LAnd cs1 cs1 255 *)
    iInstr "Hcode".
    (* GetE cgp csp *)
    iInstr "Hcode".
    (* GetB cra csp *)
    iInstr "Hcode".
    (* Sub cgp cgp cra *)
    iInstr "Hcode".
    (* Add cs1 cs1 StackEntry_reserved_space *)
    iInstr "Hcode".
    (* Lt cra cgp cs1 *)
    iInstr "Hcode".
    rewrite encode_entry_point_eq_posture.
    rewrite encode_entry_point_eq_minstk; last lia.
    rewrite encode_entry_point_eq_nargs; last lia.
    (* The instruction tactics unfold [StackEntry_reserved_space] to [2]: fold it back. *)
    iEval (change 2%Z with StackEntry_reserved_space) in "Hcs1 Hcra".
    destruct (e_stk - b_stk <? Z.of_nat minstk + StackEntry_reserved_space)%Z eqn:Hsmall;
      iEval (cbn) in "Hcra".
    { apply Z.ltb_lt in Hsmall.
      (* Jne .Lswitch_stack_too_small cra 0 *)
      iInstr "Hcode".
      { switcher_jump_label ".Lswitch_stack_too_small". }
      subst hpost.
      iApply "Hpost"; iRight.
      iFrame "HPC Hcs0 Hcs1 Hct1 Hct2 Hctp Ha_export_table Hcgp Hcra Hcsp".
      done. }
    apply Z.ltb_ge in Hsmall.
    (* Jne .Lswitch_stack_too_small cra 0 *)
    iInstr "Hcode".
    (* Lea csp csp (- StackEntry_reserved_space) *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ (- StackEntry_reserved_space))%a); last reflexivity.
      clear -Ha_stk Hsmall; subst a_stk; unfold StackEntry_reserved_space in *; solve_addr. }
    (* LShiftR cs0 cs0 16 *)
    iInstr "Hcode".
    rewrite encode_entry_point_eq_off.

    (* [.Lswitcher_prepare_callee] *)
    switcher_open_label ".Lswitcher_prepare_callee" "Hswitcher_prep" as "Hcode_prep".
    (* GetB cgp ct1 *)
    iInstr "Hcode_prep".
    (* SetA ct1 ct1 cgp *)
    iInstr "Hcode_prep".
    assert (is_heap_cap (WCap true RX Global bpcc epcc bpcc) = false) as Hpcc_not_heap.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbpcc_heap /=.
      reflexivity. }
    (* CLoad cra ct1 ExportTable_offset_pcc *)
    iInstr "Hcode_prep".
    { split; auto. rewrite /withinBounds; solve_addr. }
    (* Lea ct1 ct1 ExportTable_offset_cgp *)
    iInstr "Hcode_prep".
    { instantiate (1 := (b_tbl ^+ ExportTable_offset_cgp)%a); solve_addr. }
    (* CLoad cgp ct1 0 *)
    iInstr "Hcode_prep".
    { split; auto. rewrite /withinBounds; solve_addr. }
    destruct Hentry as [a_entry Hentry].
    (* Lea cra cra cs0 *)
    iInstr "Hcode_prep".
    (* Add ct2 ct2 1 *)
    iInstr "Hcode_prep".
    replace a_entry with (bpcc ^+ off)%a by solve_addr.
    switcher_change_pc_label ".Lswitcher_clear_unused_args".
    subst hpost.
    iApply "Hpost"; iLeft.
    iFrame "HPC Hcs0 Hcs1 Hct1 Hct2 Hctp Ha_export_table Hcgp Hcra Hcsp".
    done.
  Qed.

End Switch_Unseal_Entry.
