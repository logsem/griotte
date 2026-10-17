From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_call_states.

(** * Call routine, blocks 7-11: load the callee and jump to it

    After the unsealing of the entry point, block 7 reads the entry of the
    export table, block 8 loads the PCC and CGP of the callee, blocks 9-10
    clear the unused argument registers and the other registers, and block 11
    jumps to the callee. *)

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
     because the guarantees we have about the entry point come from the world. *)
  Lemma switcher_call_block_7_after_unseal_spec
    pc_b pc_e pc_a
    wcs0 wct2
    (g : Locality)
    btbl_tgt etbl_tgt atbl_tgt
    nargs off_tgt :
    let switcher_instrs_7 := switcher_instrs_n 7 in
    let len_switcher_7 := length switcher_instrs_7 in
    is_shadow_address atbl_tgt = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_7)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    0 ≤ nargs ≤ 7 ->

    atbl_tgt ↦ₐ□ WInt (encode_entry_point nargs off_tgt) ∗
    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 1)%a ∗
    cs0 ↦ᵣ wcs0 ∗
    ct1 ↦ᵣ WCap true RO g btbl_tgt etbl_tgt atbl_tgt ∗
    ct2 ↦ᵣ wct2 ∗
    codefrag_pers pc_a switcher_instrs_7 ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_7)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        ct1 ↦ᵣ WCap true RO g btbl_tgt etbl_tgt atbl_tgt ∗
        ct2 ↦ᵣ WInt nargs ∗
        codefrag_pers pc_a switcher_instrs_7 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_7 len_switcher_7.
    subst switcher_instrs_7 len_switcher_7.
    iIntros (Hatbl_shadow Hsub_reg atbl_tgt_inbounds Hnargs)
      "(#Ha_tbl & HPC & Hcs0 & Hct1 & Hct2 & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* CLoad cs0 ct1 0. *)
    iInstr "Hcode".
    { done. }
    { split; auto. rewrite /withinBounds. solve_addr. }

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    rewrite encode_entry_point_eq_off.
    rewrite encode_entry_point_eq_nargs; last lia.
    iApply "Hpost"; iFrame "∗ Hcode".
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
    is_shadow_address btbl_tgt = false ->
    is_shadow_address (btbl_tgt ^+ 1)%a = false ->
    is_heap_address bpcc_tgt = false ->
    is_heap_cap wcgp_tgt = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_8)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    (btbl_tgt ^+ 1 < atbl_tgt)%a ->
    is_Some (bpcc_tgt + off_tgt)%a ->

    btbl_tgt ↦ₐ□ WCap true RX Global bpcc_tgt epcc_tgt bpcc_tgt ∗
    (btbl_tgt ^+ 1)%a ↦ₐ□ wcgp_tgt ∗
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
        cs1 ↦ᵣ WInt (btbl_tgt - atbl_tgt) ∗
        ct1 ↦ᵣ WCap true RO g btbl_tgt etbl_tgt (btbl_tgt ^+ 1)%a ∗
        ct2 ↦ᵣ WInt (nargs + 1) ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cra ↦ᵣ WCap true RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a ∗
        codefrag_pers pc_a switcher_instrs_8 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_8 len_switcher_8 wct1; subst switcher_instrs_8 len_switcher_8 wct1.
    iIntros (Hbtbl_shadow Hbtbl1_shadow Hbpcc_nonheap Hwcgp_nonheap Hsub_reg atbl_tgt_inbounds Hbtbl_tgt1 Hentry)
      "(#Hb_tbl & #Hb_tbl1 & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- GetB cgp ct1 --- *)
    iInstr "Hcode".

    (* --- GetA cs1 ct1 --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cgp cs1 --- *)
    iInstr "Hcode".

    (* --- Lea ct1 cs1 --- *)
    iInstr "Hcode".
    { instantiate (1:=btbl_tgt); solve_addr. }

    (* CLoad cra ct1 0. *)
    assert (is_heap_cap (WCap true RX Global bpcc_tgt epcc_tgt bpcc_tgt) = false)
      as Hpcc_not_heap.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbpcc_nonheap /=.
      reflexivity. }
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds; solve_addr. }

    (* --- Lea ct1 1 --- *)
    iInstr "Hcode".
    { instantiate (1:=(btbl_tgt ^+ 1)%a); solve_addr. }

    (* CLoad cgp ct1 0. *)
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds; solve_addr. }

    (* --- Lea cra cs0 --- *)
    destruct Hentry as [a_entry Hentry].
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    replace a_entry with (bpcc_tgt ^+ off_tgt)%a by solve_addr.
    iApply "Hpost"; iFrame "∗ Hcode".
  Qed.


  (** Blocks 7-8: read the entry of the export table and load the PCC and
      CGP of the callee. *)
  Lemma switcher_call_blocks_7_8_spec
    (wcs0 wcs1 wct2 wcgp wcra : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (nargs : nat) (off : Z) :
    (b_tbl <= a_tbl < e_tbl)%a ->
    (b_tbl ^+ 1 < a_tbl)%a ->
    is_Some (bpcc + off)%a ->
    (nargs <= 7) ->
    is_shadow_address a_tbl = false ->
    is_shadow_address b_tbl = false ->
    is_shadow_address (b_tbl ^+ 1)%a = false ->
    is_heap_address bpcc = false ->
    is_heap_cap wcgp_tgt = false ->

    b_tbl ↦ₐ□ WCap true RX Global bpcc epcc bpcc ∗
    (b_tbl ^+ 1)%a ↦ₐ□ wcgp_tgt ∗
    a_tbl ↦ₐ□ WInt (encode_entry_point (Z.of_nat nargs) off) ∗
    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_decode_entry") ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ wct2 ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lswitcher_clear_unused_args" ∗
        cs0 ↦ᵣ WInt off ∗
        cs1 ↦ᵣ WInt (b_tbl - a_tbl) ∗
        ct1 ↦ᵣ WCap true RO g_tbl b_tbl e_tbl (b_tbl ^+ 1)%a ∗
        ct2 ↦ᵣ WInt (Z.of_nat nargs + 1) ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cra ↦ᵣ WCap true RX Global bpcc epcc (bpcc ^+ off)%a ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Htbl Htbl1 Hentry Hnargs Hatbl_shadow Hbtbl_shadow Hbtbl1_shadow Hbpcc_heap Hwcgp_heap)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2
      & Hcgp & Hcra & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 7: read the entry of the export table *)
    switcher_focus_block (switcher_block ".Lswitcher_unseal_entry") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    change_pc_to ((a_switcher_call ^+ switcher_label_offset ".Lswitcher_unseal_entry") ^+ 1)%a.
    iApply (switcher_call_block_7_after_unseal_spec with
      "[- $Htbl_entry $HPC $Hcs0 $Hct1 $Hct2 $Hcode]"); [done|done|done|lia|].
    iNext; iIntros "(HPC & Hcs0 & Hct1 & Hct2 & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 8: load the PCC and CGP of the callee *)
    switcher_focus_block (switcher_block ".Lswitcher_prepare_callee") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_8_spec with
      "[- $Htbl_pcc $Htbl_cgp $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hcgp $Hcra $Hcode]");
      [done..|].
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_clear_unused_args").
    iApply "Hpost"; iFrame "∗ Hswitcher".
  Qed.

  (** Blocks 10-11: clear the registers that are not arguments, and jump
      to the callee. *)
  Lemma switcher_call_blocks_10_11_spec
    (wcs0 wcs1 wct1 wct2 wctp : LWord) (bpcc epcc a_tgt : Addr) (rmap : LReg) :
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_clear_registers" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ wctp ∗
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

    (* Block 10: clear the other registers *)
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

    (* Block 11: jump to the callee *)
    switcher_focus_block (switcher_block ".Lswitcher_call_callee") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    (* Jalr cra cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    rewrite (_ : ((a_switcher_call ^+ switcher_label_offset ".Lswitcher_call_callee") ^+ 1)%a = a_switcher_return);
      last (rewrite switcher_return_offset; offsets_compute; solve_addr).
    iApply ("Hpost" $! mie rmap'); iFrame "∗ Hswitcher"; done.
  Qed.

  (** Blocks 7-11: read the entry of the export table, load the callee,
      clear the registers and jump to the callee. *)
  Lemma switcher_call_blocks_4_spec
    (W : WORLD) (C : CmptName)
    (wcs0 wcs1 wct2 wctp wcgp wcra : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (nargs : nat) (off : Z)
    (arg_rmap rmap : LReg) :
    (b_tbl <= a_tbl < e_tbl)%a ->
    (b_tbl ^+ 1 < a_tbl)%a ->
    is_Some (bpcc + off)%a ->
    (nargs <= 7) ->
    is_shadow_address a_tbl = false ->
    is_shadow_address b_tbl = false ->
    is_shadow_address (b_tbl ^+ 1)%a = false ->
    is_heap_address bpcc = false ->
    is_heap_cap wcgp_tgt = false ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    b_tbl ↦ₐ□ WCap true RX Global bpcc epcc bpcc ∗
    (b_tbl ^+ 1)%a ↦ₐ□ wcgp_tgt ∗
    a_tbl ↦ₐ□ WInt (encode_entry_point (Z.of_nat nargs) off) ∗
    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_decode_entry") ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ wctp ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    ( [∗ map] r↦w ∈ arg_rmap,
        r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ WCap true RX Global bpcc epcc (bpcc ^+ off)%a ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Htbl Htbl1 Hentry Hnargs Hatbl_shadow Hbtbl_shadow Hbtbl1_shadow Hbpcc_heap Hwcgp_heap Hargs Hdom)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp
      & Hcgp & Hcra & Hargs & Hregs & #Hswitcher & Hpost)".

    (* Blocks 7-8: load the callee *)
    iApply (switcher_call_blocks_7_8_spec with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hcgp $Hcra $Hswitcher]");
      [done..|].
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & _)".

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

    (* Blocks 10-11: clear the other registers and jump to the callee *)
    switcher_change_pc (switcher_label_offset ".Lswitcher_clear_registers").
    iApply (switcher_call_blocks_10_11_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs]"); first done.
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (mie rmap') "(%Hrmap' & HPC & Hcra & Hregs & _)".
    iApply ("Hpost" $! mie arg_rmap' rmap'); iFrame "∗ Hswitcher"; done.
  Qed.

  (** Variant of [switcher_call_blocks_4_spec] for a known callee, whose
      arguments are not required to be valid: the argument registers that
      are not cleared keep their initial values. *)
  Lemma switcher_call_blocks_4_known_spec
    (wcs0 wcs1 wct2 wctp wcgp wcra : LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (nargs : nat) (off : Z)
    (arg_rmap rmap : LReg) :
    (b_tbl <= a_tbl < e_tbl)%a ->
    (b_tbl ^+ 1 < a_tbl)%a ->
    is_Some (bpcc + off)%a ->
    (nargs <= 7) ->
    is_shadow_address a_tbl = false ->
    is_shadow_address b_tbl = false ->
    is_shadow_address (b_tbl ^+ 1)%a = false ->
    is_heap_address bpcc = false ->
    is_heap_cap wcgp_tgt = false ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    b_tbl ↦ₐ□ WCap true RX Global bpcc epcc bpcc ∗
    (b_tbl ^+ 1)%a ↦ₐ□ wcgp_tgt ∗
    a_tbl ↦ₐ□ WInt (encode_entry_point (Z.of_nat nargs) off) ∗
    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_decode_entry") ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ wctp ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w ) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ WCap true RX Global bpcc epcc (bpcc ^+ off)%a ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs)
                     then ⌜ arg_rmap !! r = Some w ⌝
                     else ⌜ w = WInt 0 ⌝ ) ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Htbl Htbl1 Hentry Hnargs Hatbl_shadow Hbtbl_shadow Hbtbl1_shadow Hbpcc_heap Hwcgp_heap Hargs Hdom)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp
      & Hcgp & Hcra & Hargs & Hregs & #Hswitcher & Hpost)".

    (* Blocks 7-8: load the callee *)
    iApply (switcher_call_blocks_7_8_spec with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hcgp $Hcra $Hswitcher]");
      [done..|].
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & _)".

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

    (* Blocks 10-11: clear the other registers and jump to the callee *)
    switcher_change_pc (switcher_label_offset ".Lswitcher_clear_registers").
    iApply (switcher_call_blocks_10_11_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs]"); first done.
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (mie rmap') "(%Hrmap' & HPC & Hcra & Hregs & _)".
    iApply ("Hpost" $! mie arg_rmap' rmap'); iFrame "∗ Hswitcher"; done.
  Qed.

End Switcher_Call_Blocks_4.
