From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_call_states.

(** * Call routine, blocks 7-12: load the callee and jump to it

    After the unsealing of the entry point, block 7 reads the entry of the
    export table and checks that the callee's stack is at least the minimum
    stack size of the entry (otherwise, the execution jumps to block 20, see
    [switcher_call_blocks_6]), block 8 loads the PCC and CGP of the callee, block 9 clears
    the unused argument registers, block 10 enables interrupts unless the
    entry point asks for them disabled, block 11 clears the other registers,
    and block 12 jumps to the callee. *)

Section Switcher_Call_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (* Spec for block 7 starting after unsealing the entry point.
     The responsibility of unsealing is left to the caller of this lemma,
     because the guarantees we have about the entry point come from the world.
     Block 7 decodes the entry and checks that the callee's stack is at least
     its minimum stack size; otherwise, it jumps to [a_small]. *)
  Lemma switcher_call_block_7_after_unseal_spec
    pc_b pc_e pc_a a_small
    wcs0 wcs1 wct2 wcgp wcra a_frame wtbl
    (g : Locality)
    btbl_tgt etbl_tgt atbl_tgt
    b_stk e_stk a_stk
    posture (nargs minstk off_tgt : Z) :
    let a_export_table := (a_frame ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let switcher_instrs_7 := switcher_instrs_n 7 in
    let len_switcher_7 := length switcher_instrs_7 in
    is_shadow_address atbl_tgt = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_7)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    (0 ≤ nargs ≤ 7)%Z ->
    (0 ≤ minstk ≤ 255)%Z ->
    (b_trusted_stack <= a_frame)%a ->
    (a_export_table < e_trusted_stack)%a ->
    (pc_a ^+ 11 +
       asm_label_offset switcher_asm ".Lswitch_stack_too_small_branch"
         ".Lswitch_stack_too_small")%a = Some a_small ->

    atbl_tgt ↦ₐ□ WInt (encode_entry_point posture nargs minstk off_tgt) ∗
    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 1)%a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ WCap true RO g btbl_tgt etbl_tgt atbl_tgt ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_frame ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
    a_export_table ↦ₐ wtbl ∗
    codefrag_pers pc_a switcher_instrs_7 ∗
    ▷ ( ( ⌜ (minstk <= e_stk - b_stk)%Z ⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_7)%a ∗
          cs0 ↦ᵣ WInt off_tgt ∗
          cs1 ↦ᵣ WInt minstk ∗
          ct1 ↦ᵣ WCap true RO g btbl_tgt etbl_tgt atbl_tgt ∗
          ct2 ↦ᵣ WInt nargs ∗
          ctp ↦ᵣ WInt (entry_point_posture posture) ∗
          cgp ↦ᵣ WInt (e_stk - b_stk) ∗
          cra ↦ᵣ WInt 0 ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
          a_export_table ↦ₐ
            WCap true RO g btbl_tgt etbl_tgt atbl_tgt ∗
          codefrag_pers pc_a switcher_instrs_7 )
        ∨
        ( ⌜ (e_stk - b_stk < minstk)%Z ⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local pc_b pc_e a_small ∗
          cs0 ↦ᵣ WInt (encode_entry_point posture nargs minstk off_tgt) ∗
          cs1 ↦ᵣ WInt minstk ∗
          ct1 ↦ᵣ WCap true RO g btbl_tgt etbl_tgt atbl_tgt ∗
          ct2 ↦ᵣ WInt nargs ∗
          ctp ↦ᵣ WInt (entry_point_posture posture) ∗
          cgp ↦ᵣ WInt (e_stk - b_stk) ∗
          cra ↦ᵣ WInt 1 ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
          a_export_table ↦ₐ
            WCap true RO g btbl_tgt etbl_tgt atbl_tgt ∗
          codefrag_pers pc_a switcher_instrs_7 )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_export_table; subst a_export_table.
    intros switcher_instrs_7 len_switcher_7.
    subst switcher_instrs_7 len_switcher_7.
    iIntros (Hatbl_shadow Hsub_reg atbl_tgt_inbounds Hnargs Hminstk Ha_frame_b Ha_frame_e Ha_small)
      "(#Ha_tbl & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcgp & Hcra & Hcsp
      & Ha_export_table & #Hcode & Hpost)".
    (* Compute the distance to the block of the too small stack. *)
    offsets_compute.
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((a_frame + TrustedStackFrame_offset_calleeExportTable)%a
            = Some (a_frame ^+ TrustedStackFrame_offset_calleeExportTable)%a) as Ha_export_table
      by (tstack_unfold; solve_addr).

    (* CLoad cs0 ct1 0. *)
    iInstr "Hcode".
    { done. }
    { split; auto. rewrite /withinBounds. solve_addr. }

    (* Store ctp ct1 1 *)
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

    (* Lt cra cgp cs1 *)
    iInstr "Hcode".

    rewrite encode_entry_point_eq_posture.
    rewrite encode_entry_point_eq_minstk; last lia.
    rewrite encode_entry_point_eq_nargs; last lia.
    destruct (e_stk - b_stk <? minstk)%Z eqn:Hsmall; iEval (cbn) in "Hcra".
    - apply Z.ltb_lt in Hsmall.
      (* Jne ".Lswitch_stack_too_small" cra 0 *)
      iInstr "Hcode".
      iApply "Hpost"; iRight.
      iFrame "∗ Hcode".
      done.
    - apply Z.ltb_ge in Hsmall.
      (* Jne ".Lswitch_stack_too_small" cra 0 *)
      iInstr "Hcode".

      (* LShiftR cs0 cs0 16 *)
      iInstr "Hcode".

      rewrite encode_entry_point_eq_off.
      iApply "Hpost"; iLeft.
      iFrame "∗ Hcode".
      done.
  Qed.

  Lemma switcher_call_block_8_spec
    pc_b pc_e pc_a
    wcs1 wcgp wcra
    (g : Locality)
    btbl_tgt etbl_tgt atbl_tgt
    (bpcc_tgt epcc_tgt : Addr) (wcgp_tgt : Word)
    nargs off_tgt :
    let switcher_instrs_8 := (switcher_instrs_n 8) in
    let len_switcher_8 := length switcher_instrs_8 in
    let wct1 := WCap true RO g btbl_tgt etbl_tgt atbl_tgt in
    let a_tbl_cgp := (btbl_tgt ^+ ExportTable_offset_cgp)%a in
    is_shadow_address btbl_tgt = false ->
    is_shadow_address a_tbl_cgp = false ->
    is_heap_address bpcc_tgt = false ->
    is_heap_cap wcgp_tgt = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_8)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    (a_tbl_cgp < atbl_tgt)%a ->
    is_Some (bpcc_tgt + off_tgt)%a ->

    btbl_tgt ↦ₐ□ WCap true RX Global bpcc_tgt epcc_tgt bpcc_tgt ∗
    a_tbl_cgp ↦ₐ□ wcgp_tgt ∗
    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ WInt off_tgt ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ WInt nargs ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    codefrag_pers pc_a switcher_instrs_8 ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_8)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        cs1 ↦ᵣ wcs1 ∗
        ct1 ↦ᵣ WCap true RO g btbl_tgt etbl_tgt a_tbl_cgp ∗
        ct2 ↦ᵣ WInt (nargs + 1) ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cra ↦ᵣ WCap true RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a ∗
        codefrag_pers pc_a switcher_instrs_8 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_8 len_switcher_8 wct1 a_tbl_cgp;
      subst switcher_instrs_8 len_switcher_8 wct1 a_tbl_cgp.
    iIntros (Hbtbl_shadow Hbtbl_cgp_shadow Hbpcc_nonheap Hwcgp_nonheap Hsub_reg atbl_tgt_inbounds Hbtbl_tgt_cgp Hentry)
      "(#Hb_tbl & #Hb_tbl1 & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- GetB cgp ct1 --- *)
    iInstr "Hcode".

    (* --- SetA ct1 ct1 cgp --- *)
    iInstr "Hcode".

    (* CLoad cra ct1 0. *)
    assert (is_heap_cap (WCap true RX Global bpcc_tgt epcc_tgt bpcc_tgt) = false)
      as Hpcc_not_heap.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbpcc_nonheap /=.
      reflexivity. }
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds; solve_addr. }

    (* --- Lea ct1 ct1 ExportTable_offset_cgp --- *)
    iInstr "Hcode".
    { instantiate (1:=(btbl_tgt ^+ ExportTable_offset_cgp)%a); solve_addr. }

    (* CLoad cgp ct1 0. *)
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds; solve_addr. }

    (* --- Lea cra cra cs0 --- *)
    destruct Hentry as [a_entry Hentry].
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    replace a_entry with (bpcc_tgt ^+ off_tgt)%a by solve_addr.
    iApply "Hpost"; iFrame "∗ Hcode".
  Qed.


  (** Blocks 7-8: read the entry of the export table, check the size of
      the callee's stack, and load the PCC and CGP of the callee. When the
      callee's stack is smaller than the minimum stack size of the entry,
      jump to block 20. *)
  Lemma switcher_call_blocks_7_8_spec
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

    b_tbl ↦ₐ□ WCap true RX Global bpcc epcc bpcc ∗
    a_tbl_cgp ↦ₐ□ wcgp_tgt ∗
    a_tbl ↦ₐ□ WInt (encode_entry_point posture (Z.of_nat nargs) (Z.of_nat minstk) off) ∗
    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_decode_entry") ∗
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
    ▷ ( ( ⌜ (Z.of_nat minstk <= e_stk - b_stk)%Z ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitcher_clear_unused_args" ∗
          cs0 ↦ᵣ WInt off ∗
          cs1 ↦ᵣ WInt (Z.of_nat minstk) ∗
          ct1 ↦ᵣ WCap true RO g_tbl b_tbl e_tbl a_tbl_cgp ∗
          ct2 ↦ᵣ WInt (Z.of_nat nargs + 1) ∗
          ctp ↦ᵣ WInt (entry_point_posture posture) ∗
          a_export_table ↦ₐ
            WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          cgp ↦ᵣ wcgp_tgt ∗
          cra ↦ᵣ WCap true RX Global bpcc epcc (bpcc ^+ off)%a ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
          switcher_code )
        ∨
        ( ⌜ (e_stk - b_stk < Z.of_nat minstk)%Z ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitch_stack_too_small" ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          a_export_table ↦ₐ
            WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
          switcher_code )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow Hbpcc_heap
               Hwcgp_heap Ha_frame_b Ha_frame_e)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2
      & Hctp & Ha_export_table & Hcgp & Hcra & Hcsp & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 7: read the entry of the export table and check the stack *)
    switcher_focus_block (switcher_block ".Lswitcher_unseal_entry") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    change_pc_to ((a_switcher_call ^+ switcher_label_offset ".Lswitcher_unseal_entry") ^+ 1)%a.
    iApply (switcher_call_block_7_after_unseal_spec _ _ _
              (a_switcher_call ^+ switcher_label_offset ".Lswitch_stack_too_small")%a
             with
      "[- $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcgp $Hcra $Hcsp $Ha_export_table $Hcode]");
      [done|done|done|lia|lia|done|done| |].
    { offsets_compute; solve_addr. }
    iNext; iIntros "[(%Hbig & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcgp & Hcra & Hcsp
                     & Ha_export_table & _)
                   | (%Hsmall & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcgp & Hcra & Hcsp
                     & Ha_export_table & _)]";
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher; cycle 1.
    { (* The callee's stack is too small *)
      iApply "Hpost"; iRight.
      iFrame "∗ Hswitcher".
      done. }

    (* Block 8: load the PCC and CGP of the callee *)
    switcher_focus_block (switcher_block ".Lswitcher_prepare_callee") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_8_spec with
      "[- $Htbl_pcc $Htbl_cgp $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hcgp $Hcra $Hcode]");
      [done..|].
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_clear_unused_args").
    iApply "Hpost"; iLeft; iFrame "∗ Hswitcher".
    done.
  Qed.

  (** Block 10: enable interrupts unless the posture of the callee, in
      [ctp], asks for them disabled. *)
  Lemma switcher_call_block_10_spec
    pc_b pc_e pc_a
    (posture : InterruptStatus) :
    let switcher_instrs_10 := switcher_instrs_n 10 in
    let len_switcher_10 := length switcher_instrs_10 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_10)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    ctp ↦ᵣ WInt (entry_point_posture posture) ∗
    codefrag_pers pc_a switcher_instrs_10 ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 2)%a ∗
        ctp ↦ᵣ WInt (entry_point_posture posture) ∗
        codefrag_pers pc_a switcher_instrs_10 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_10 len_switcher_10.
    subst switcher_instrs_10 len_switcher_10.
    iIntros (Hsub_reg) "(HPC & Hctp & #Hcode & Hpost)".
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n.
    destruct posture; cbn [entry_point_posture].
    - (* --- Jne 2 ctp 0 --- *)
      iInstr "Hcode".
      (* --- SetMIE InterruptEnabled --- *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame "∗ Hcode".
    - (* --- Jne 2 ctp 0 --- *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame "∗ Hcode".
  Qed.

  (** Blocks 10-12: enable interrupts if the posture of the callee asks for
      it, clear the registers that are not arguments, and jump to the callee. *)
  Lemma switcher_call_blocks_10_12_spec
    (wcs0 wcs1 wct1 wct2 : LWord) (posture : InterruptStatus)
    (bpcc epcc a_tgt : Addr) (rmap : LReg) :
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_enable_interrupts" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ WInt (entry_point_posture posture) ∗
    cra ↦ᵣ WCap true RX Global bpcc epcc a_tgt ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ WCap true RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdom) "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hregs & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    pose proof switcher_return_offset.
    switcher_unfold_code "Hswitcher".

    (* Block 10: enable interrupts, unless the posture says otherwise *)
    switcher_focus_block (switcher_block ".Lswitcher_enable_interrupts") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_10_spec with "[- $HPC $Hctp $Hcode]"); first done.
    iIntros "!> (HPC & Hctp & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_clear_registers").

    (* Block 11: clear the other registers *)
    switcher_focus_block (switcher_block ".Lswitcher_clear_registers") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcs1] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcs0] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs";[iFrame|].
    iApply (clear_registers_pre_call_spec with "[- $HPC $Hcode $Hregs]"); try solve_pure.
    { rewrite !dom_insert_L Hdom. set_solver-. }
    iIntros "!> (%rmap' & %Hrmap' & HPC & Hregs & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 12: jump to the callee *)
    switcher_focus_block (switcher_block ".Lswitcher_call_callee") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    (* Jalr cra cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    rewrite (_ : ((a_switcher_call ^+ switcher_label_offset ".Lswitcher_call_callee") ^+ 1)%a = a_switcher_return);
      last (rewrite switcher_return_offset; offsets_compute; solve_addr).
    iApply ("Hpost" $! mie rmap'); iFrame "∗ Hswitcher"; done.
  Qed.

  (** Blocks 7-12: read the entry of the export table, check the size of
      the callee's stack, load the callee, enable interrupts, clear the
      registers and jump to the callee. When the callee's stack is smaller
      than the minimum stack size of the entry, jump to block 20 instead. *)
  Lemma switcher_call_blocks_4_spec
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
    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_decode_entry") ∗
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
          a_export_table ↦ₐ
            WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
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
          a_export_table ↦ₐ
            WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap,
              r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
          ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow Hbpcc_heap
               Hwcgp_heap Ha_frame_b Ha_frame_e Hargs Hdom)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp
      & Ha_export_table & Hcgp & Hcra & Hcsp & Hargs & Hregs & #Hswitcher & Hpost)".

    (* Blocks 7-8: check the callee's stack and load the callee *)
    iApply (switcher_call_blocks_7_8_spec with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Ha_export_table
          $Hcgp $Hcra $Hcsp $Hswitcher]");
      [done..|].
    iNext; iIntros "[(%Hbig & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Ha_export_table & Hcgp
                     & Hcra & Hcsp & _)
                   | (%Hsmall & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Ha_export_table & Hcgp
                     & Hcra & Hcsp & _)]"; cycle 1.
    { (* The callee's stack is too small *)
      iDestruct "Hpost" as "[_ Hpost]".
      iApply "Hpost"; iFrame "∗ Hswitcher"; done. }
    iDestruct "Hpost" as "[Hpost _]".

    (* Block 9: clear the unused argument registers *)
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lswitcher_clear_unused_args") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (clear_registers_pre_call_skip_spec _ _ _ _ _ arg_rmap (nargs+1)
             with "[- $HPC $Hcode]"); try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame "Hct2 Hargs".
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Blocks 10-12: enable interrupts, clear the other registers and jump to the callee *)
    switcher_change_pc (switcher_label_offset ".Lswitcher_enable_interrupts").
    iApply (switcher_call_blocks_10_12_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs]"); first done.
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (mie rmap') "(%Hrmap' & HPC & Hcra & Hregs & _)".
    iApply ("Hpost" $! mie arg_rmap' rmap'); iFrame "∗ Hswitcher"; done.
  Qed.

  (** Variant of [switcher_call_blocks_4_spec] for a known callee, whose
      arguments are not required to be valid: the argument registers that
      are not cleared keep their initial values. *)
  Lemma switcher_call_blocks_4_known_spec
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
    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_decode_entry") ∗
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
          a_export_table ↦ₐ
            WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
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
          a_export_table ↦ₐ
            WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
          ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w ) ∗
          ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_export_table a_tbl_cgp; subst a_export_table a_tbl_cgp.
    iIntros (Htbl Htbl_cgp Hentry Hnargs Hminstk Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow Hbpcc_heap
               Hwcgp_heap Ha_frame_b Ha_frame_e Hargs Hdom)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp
      & Ha_export_table & Hcgp & Hcra & Hcsp & Hargs & Hregs & #Hswitcher & Hpost)".

    (* Blocks 7-8: check the callee's stack and load the callee *)
    iApply (switcher_call_blocks_7_8_spec with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Ha_export_table
          $Hcgp $Hcra $Hcsp $Hswitcher]");
      [done..|].
    iNext; iIntros "[(%Hbig & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Ha_export_table & Hcgp
                     & Hcra & Hcsp & _)
                   | (%Hsmall & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Ha_export_table & Hcgp
                     & Hcra & Hcsp & _)]"; cycle 1.
    { (* The callee's stack is too small *)
      iDestruct "Hpost" as "[_ Hpost]".
      iApply "Hpost"; iFrame "∗ Hswitcher"; done. }
    iDestruct "Hpost" as "[Hpost _]".

    (* Block 9: clear the unused argument registers *)
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lswitcher_clear_unused_args") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (clear_registers_pre_call_skip_spec_known _ _ _ _ _ arg_rmap (nargs+1)
             with "[- $HPC $Hcode]"); try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame "Hct2 Hargs".
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Blocks 10-12: enable interrupts, clear the other registers and jump to the callee *)
    switcher_change_pc (switcher_label_offset ".Lswitcher_enable_interrupts").
    iApply (switcher_call_blocks_10_12_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs]"); first done.
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (mie rmap') "(%Hrmap' & HPC & Hcra & Hregs & _)".
    iApply ("Hpost" $! mie arg_rmap' rmap'); iFrame "∗ Hswitcher"; done.
  Qed.

End Switcher_Call_Blocks_4.
