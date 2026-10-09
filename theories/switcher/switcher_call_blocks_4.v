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
    {stsg : STSG Addr region_type Σ}
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
    Nexp_tbl nargs off_tgt :
    let switcher_instrs_7 := switcher_instrs_n 7 in
    let len_switcher_7 := length switcher_instrs_7 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_7)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    0 ≤ nargs ≤ 7 ->

    inv (export_table_entryN Nexp_tbl atbl_tgt)
      (atbl_tgt ↦ₐ WInt (encode_entry_point nargs off_tgt)) ∗
    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 1)%a ∗
    cs0 ↦ᵣ wcs0 ∗
    ct1 ↦ᵣ WCap RO g btbl_tgt etbl_tgt atbl_tgt ∗
    ct2 ↦ᵣ wct2 ∗
    codefrag pc_a switcher_instrs_7 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_7)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        ct1 ↦ᵣ WCap RO g btbl_tgt etbl_tgt atbl_tgt ∗
        ct2 ↦ᵣ WInt nargs ∗
        codefrag pc_a switcher_instrs_7 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_7 len_switcher_7.
    subst switcher_instrs_7 len_switcher_7.
    iIntros (Hsub_reg atbl_tgt_inbounds Hnargs)
      "(#Hinv_exp_tbl_entry & HPC & Hcs0 & Hct1 & Hct2 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Hinv_exp_tbl_entry" as ">Ha_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split; auto. rewrite /withinBounds. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    rewrite encode_entry_point_eq_off.
    rewrite encode_entry_point_eq_nargs; last lia.
    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_call_block_7_spec
    pc_b pc_e pc_a
    wct2 o
    btbl_tgt etbl_tgt atbl_tgt
    Nexp_tbl nargs off_tgt :
    let switcher_instrs_7 := (switcher_instrs_n 7) in
    let len_switcher_7 := length switcher_instrs_7 in
    let wct1 := WSealed o (SCap RO Global btbl_tgt etbl_tgt atbl_tgt) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_7)%a ->
    (o < o ^+ 1)%ot ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    0 ≤ nargs ≤ 7 ->

    inv (export_table_entryN Nexp_tbl atbl_tgt)
      (atbl_tgt ↦ₐ WInt (encode_entry_point nargs off_tgt)) ∗
    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ WSealRange (true, true) Global o (o ^+ 1)%ot o ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    codefrag pc_a switcher_instrs_7 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_7)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        ct1 ↦ᵣ WCap RO Global btbl_tgt etbl_tgt atbl_tgt ∗
        ct2 ↦ᵣ WInt nargs ∗
        codefrag pc_a switcher_instrs_7 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_7 len_switcher_7 wct1; subst switcher_instrs_7 len_switcher_7 wct1.
    iIntros (Hsub_reg Hot_bounds atbl_tgt_inbounds Hnargs)
      "(#Hinv_exp_tbl_entry & HPC & Hcs0 & Hct1 & wtc2 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    iInstr "Hcode";[done|..].
    { rewrite /withinBounds; solve_addr. }


    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Hinv_exp_tbl_entry" as ">Ha_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    rewrite encode_entry_point_eq_off.
    rewrite encode_entry_point_eq_nargs; last lia.
    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_call_block_8_spec
    pc_b pc_e pc_a
    wcs1 wcgp wcra
    (g : Locality)
    btbl_tgt etbl_tgt atbl_tgt
    (bpcc_tgt epcc_tgt : Addr) wcgp_tgt
    Nexp_tbl nargs off_tgt :
    let switcher_instrs_8 := (switcher_instrs_n 8) in
    let len_switcher_8 := length switcher_instrs_8 in
    let wct1 := WCap RO g btbl_tgt etbl_tgt atbl_tgt in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_8)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    (btbl_tgt ^+ 1 < atbl_tgt)%a ->

    inv (export_table_PCCN Nexp_tbl) (btbl_tgt ↦ₐ WCap RX Global bpcc_tgt epcc_tgt bpcc_tgt) ∗
    inv (export_table_CGPN Nexp_tbl) ((btbl_tgt ^+ 1)%a ↦ₐ wcgp_tgt) ∗
    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ WInt off_tgt ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ WInt nargs ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    codefrag pc_a switcher_instrs_8 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_8)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        cs1 ↦ᵣ WInt (btbl_tgt - atbl_tgt) ∗
        ct1 ↦ᵣ WCap RO g btbl_tgt etbl_tgt (btbl_tgt ^+ 1)%a ∗
        ct2 ↦ᵣ WInt (nargs + 1) ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cra ↦ᵣ WCap RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a ∗
        codefrag pc_a switcher_instrs_8 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_8 len_switcher_8 wct1; subst switcher_instrs_8 len_switcher_8 wct1.
    iIntros (Hsub_reg atbl_tgt_inbounds Hbtbl_tgt1)
      "(#Hinv_exp_tbl_pcc & Hinv_exp_tbl_cgp & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & Hcode & Hpost)".
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

    (* --- Load cra ct1 --- *)
    wp_instr.
    iInv "Hinv_exp_tbl_pcc" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds; solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_"; iModIntro.
    wp_pure.

    (* --- Lea ct1 1 --- *)
    iInstr "Hcode".
    { instantiate (1:=(btbl_tgt ^+ 1)%a); solve_addr. }

    (* --- Load cgp ct1 --- *)
    wp_instr.
    iInv "Hinv_exp_tbl_cgp" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds; solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_"; iModIntro.
    wp_pure.

    (* --- Lea cra cs0 --- *)
    destruct (bpcc_tgt + off_tgt)%a eqn:Hentry;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    replace f with (bpcc_tgt ^+ off_tgt)%a by solve_addr.
    iApply "Hpost"; iFrame.
  Qed.


  (** Blocks 7-11: read the entry of the export table, load the callee,
      clear the registers and jump to the callee. *)
  Lemma switcher_call_blocks_4_spec
    (W : WORLD) (C : CmptName)
    (wcs0 wcs1 wct2 wctp wcgp wcra : Word)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (Nexp_tbl : namespace) (nargs : nat) (off : Z)
    (arg_rmap rmap : Reg) :
    (b_tbl <= a_tbl < e_tbl)%a ->
    (b_tbl ^+ 1 < a_tbl)%a ->
    (nargs <= 7) ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    inv (export_table_PCCN Nexp_tbl) (b_tbl ↦ₐ WCap RX Global bpcc epcc bpcc) ∗
    inv (export_table_CGPN Nexp_tbl) ((b_tbl ^+ 1)%a ↦ₐ wcgp_tgt) ∗
    inv (export_table_entryN Nexp_tbl a_tbl)
      (a_tbl ↦ₐ WInt (encode_entry_point (Z.of_nat nargs) off)) ∗
    PC ↦ᵣ switcher_pc (switcher_block_offset 7 + 1) ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ WCap RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ wctp ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    ( [∗ map] r↦w ∈ arg_rmap,
        r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (arg_rmap' rmap' : Reg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ᵣ WCap RX Global bpcc epcc (bpcc ^+ off)%a ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cra ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Htbl Htbl1 Hnargs Hargs Hdom)
      "(#Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp
      & Hcgp & Hcra & Hargs & Hregs & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    pose proof switcher_return_offset.
    switcher_unfold_code "Hcode".

    (* Block 7: read the entry of the export table *)
    switcher_focus_block 7 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    change_pc_to ((a_switcher_call ^+ switcher_block_offset 7) ^+ 1)%a.
    iApply (switcher_call_block_7_after_unseal_spec with
      "[- $Htbl_entry $HPC $Hcs0 $Hct1 $Hct2 $Hcode]"); [done|done|lia|].
    iNext; iIntros "(HPC & Hcs0 & Hct1 & Hct2 & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 8: load the PCC and CGP of the callee *)
    switcher_focus_block 8 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_8_spec with
      "[- $Htbl_pcc $Htbl_cgp $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hcgp $Hcra $Hcode]");
      [done|done|done|].
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 9: clear the unused argument registers *)
    switcher_focus_block 9 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (clear_registers_pre_call_skip_spec _ _ _ _ _ arg_rmap (nargs+1)
             with "[- $HPC $Hcode]"); try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame "Hct2 Hargs".
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 10: clear the other registers *)
    switcher_focus_block 10 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcs1] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcs0] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs";[iFrame|].
    iApply (clear_registers_pre_call_spec with "[- $HPC $Hcode $Hregs]"); try solve_pure.
    { rewrite !dom_insert_L Hdom. set_solver-. }
    iIntros "!> (%rmap' & %Hrmap' & HPC & Hregs & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 11: jump to the callee *)
    switcher_focus_block 11 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    (* Jalr cra cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 11) ^+ 1)%a = a_switcher_return);
      last (rewrite switcher_return_offset; offsets_compute; solve_addr).
    iApply ("Hpost" $! arg_rmap' rmap'); iFrame; done.
  Qed.

End Switcher_Call_Blocks_4.
