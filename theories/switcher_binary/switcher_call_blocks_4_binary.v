From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary.
From griotte Require Import switcher_call_states_binary.

(** * Call routine, blocks 7-11: load the callee and jump to it, binary model

    After the unsealing of the entry point, block 7 reads the entry of the
    export table, block 8 loads the PCC and CGP of the callee, blocks 9-10
    clear the unused argument registers and the other registers, and block 11
    jumps to the callee, in both runs. Both runs read the same export
    table. *)

Section Switcher_Call_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (* Spec for block 7 starting after unsealing the entry point. *)
  Lemma switcher_call_block_7_after_unseal_spec
    pc_a
    wcs0 swcs0 wct2 swct2
    (g : Locality)
    btbl_tgt etbl_tgt atbl_tgt
    Nexp_tbl nargs off_tgt :
    let switcher_instrs_7 := switcher_instrs_n 7 in
    let len_switcher_7 := length switcher_instrs_7 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_7)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    0 ≤ nargs ≤ 7 ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    inv (export_table_entryN Nexp_tbl atbl_tgt)
      (atbl_tgt ↦ₐ WInt (encode_entry_point nargs off_tgt)
       ∗ atbl_tgt ↣ₐ WInt (encode_entry_point nargs off_tgt)) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    ct1 ↦ᵣ WCap RO g btbl_tgt etbl_tgt atbl_tgt ∗
    ct1 ↣ᵣ WCap RO g btbl_tgt etbl_tgt atbl_tgt ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    codefrag pc_a switcher_instrs_7 ∗
    spec_codefrag pc_a switcher_instrs_7 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_7)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_7)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        cs0 ↣ᵣ WInt off_tgt ∗
        ct1 ↦ᵣ WCap RO g btbl_tgt etbl_tgt atbl_tgt ∗
        ct1 ↣ᵣ WCap RO g btbl_tgt etbl_tgt atbl_tgt ∗
        ct2 ↦ᵣ WInt nargs ∗
        ct2 ↣ᵣ WInt nargs ∗
        codefrag pc_a switcher_instrs_7 ∗
        spec_codefrag pc_a switcher_instrs_7 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_7 len_switcher_7.
    subst switcher_instrs_7 len_switcher_7.
    iIntros (Hsub_reg atbl_tgt_inbounds Hnargs)
      "(#Hspec & Hj & #Hinv_exp_tbl_entry & HPC & HsPC & Hcs0 & Hscs0 & Hct1 & Hsct1 & Hct2 & Hsct2
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    wp_instr.
    iInv "Hinv_exp_tbl_entry" as ">[Ha_tbl Hsa_tbl]" "Hcls_tbl".
    (* Load cs0 ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; auto; rewrite /withinBounds; solve_addr.
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.
    (* LAnd ct2 cs0 7 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* LShiftR cs0 cs0 3 *)
    iInstr_lockstep "Hscode" "Hcode".

    rewrite encode_entry_point_eq_off.
    rewrite encode_entry_point_eq_nargs; last lia.
    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_call_block_8_spec
    pc_a
    wcs1 swcs1 wcgp swcgp wcra swcra
    (g : Locality)
    btbl_tgt etbl_tgt atbl_tgt
    (bpcc_tgt epcc_tgt : Addr) wcgp_tgt
    Nexp_tbl nargs off_tgt :
    let switcher_instrs_8 := switcher_instrs_n 8 in
    let len_switcher_8 := length switcher_instrs_8 in
    let wct1 := WCap RO g btbl_tgt etbl_tgt atbl_tgt in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_8)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    (btbl_tgt ^+ 1 < atbl_tgt)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    inv (export_table_PCCN Nexp_tbl)
      (btbl_tgt ↦ₐ WCap RX Global bpcc_tgt epcc_tgt bpcc_tgt
       ∗ btbl_tgt ↣ₐ WCap RX Global bpcc_tgt epcc_tgt bpcc_tgt) ∗
    inv (export_table_CGPN Nexp_tbl)
      ((btbl_tgt ^+ 1)%a ↦ₐ wcgp_tgt ∗ (btbl_tgt ^+ 1)%a ↣ₐ wcgp_tgt) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    cs0 ↦ᵣ WInt off_tgt ∗
    cs0 ↣ᵣ WInt off_tgt ∗
    cs1 ↦ᵣ wcs1 ∗
    cs1 ↣ᵣ swcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct1 ↣ᵣ wct1 ∗
    ct2 ↦ᵣ WInt nargs ∗
    ct2 ↣ᵣ WInt nargs ∗
    cgp ↦ᵣ wcgp ∗
    cgp ↣ᵣ swcgp ∗
    cra ↦ᵣ wcra ∗
    cra ↣ᵣ swcra ∗
    codefrag pc_a switcher_instrs_8 ∗
    spec_codefrag pc_a switcher_instrs_8 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_8)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_8)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        cs0 ↣ᵣ WInt off_tgt ∗
        cs1 ↦ᵣ WInt (btbl_tgt - atbl_tgt) ∗
        cs1 ↣ᵣ WInt (btbl_tgt - atbl_tgt) ∗
        ct1 ↦ᵣ WCap RO g btbl_tgt etbl_tgt (btbl_tgt ^+ 1)%a ∗
        ct1 ↣ᵣ WCap RO g btbl_tgt etbl_tgt (btbl_tgt ^+ 1)%a ∗
        ct2 ↦ᵣ WInt (nargs + 1) ∗
        ct2 ↣ᵣ WInt (nargs + 1) ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cgp ↣ᵣ wcgp_tgt ∗
        cra ↦ᵣ WCap RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a ∗
        cra ↣ᵣ WCap RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a ∗
        codefrag pc_a switcher_instrs_8 ∗
        spec_codefrag pc_a switcher_instrs_8 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_8 len_switcher_8 wct1; subst switcher_instrs_8 len_switcher_8 wct1.
    iIntros (Hsub_reg atbl_tgt_inbounds Hbtbl_tgt1)
      "(#Hspec & Hj & #Hinv_exp_tbl_pcc & #Hinv_exp_tbl_cgp & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1
      & Hct1 & Hsct1 & Hct2 & Hsct2 & Hcgp & Hscgp & Hcra & Hscra & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* GetB cgp ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* GetA cs1 ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Sub cs1 cgp cs1 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Lea ct1 cs1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:=btbl_tgt); solve_addr.

    wp_instr.
    iInv "Hinv_exp_tbl_pcc" as ">[Hb_tbl Hsb_tbl]" "Hcls_tbl".
    (* Load cra ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; auto; rewrite /withinBounds; solve_addr.
    iMod ("Hcls_tbl" with "[$]") as "_"; iModIntro.
    wp_pure.

    (* Lea ct1 1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:=(btbl_tgt ^+ 1)%a); solve_addr.

    wp_instr.
    iInv "Hinv_exp_tbl_cgp" as ">[Hb_tbl Hsb_tbl]" "Hcls_tbl".
    (* Load cgp ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; auto; rewrite /withinBounds; solve_addr.
    iMod ("Hcls_tbl" with "[$]") as "_"; iModIntro.
    wp_pure.

    destruct (bpcc_tgt + off_tgt)%a eqn:Hentry; cycle 1.
    { (* Lea cra cs0 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    (* Lea cra cs0 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Add ct2 ct2 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    replace f with (bpcc_tgt ^+ off_tgt)%a by solve_addr.
    iApply "Hpost"; iFrame.
  Qed.


  (** Blocks 7-11: read the entry of the export table, load the callee,
      clear the registers and jump to the callee. *)
  Lemma switcher_call_blocks_4_spec
    (W : WORLD) (C : CmptName)
    (wcs0 swcs0 wcs1 swcs1 wct2 swct2 wctp swctp wcgp swcgp wcra swcra : Word)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl bpcc epcc : Addr) (wcgp_tgt : Word)
    (Nexp_tbl : namespace) (nargs : nat) (off : Z)
    (arg_rmap arg_smap rmap smap : Reg) :
    (b_tbl <= a_tbl < e_tbl)%a ->
    (b_tbl ^+ 1 < a_tbl)%a ->
    (nargs <= 7) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    inv (export_table_PCCN Nexp_tbl)
      (b_tbl ↦ₐ WCap RX Global bpcc epcc bpcc ∗ b_tbl ↣ₐ WCap RX Global bpcc epcc bpcc) ∗
    inv (export_table_CGPN Nexp_tbl)
      ((b_tbl ^+ 1)%a ↦ₐ wcgp_tgt ∗ (b_tbl ^+ 1)%a ↣ₐ wcgp_tgt) ∗
    inv (export_table_entryN Nexp_tbl a_tbl)
      (a_tbl ↦ₐ WInt (encode_entry_point (Z.of_nat nargs) off)
       ∗ a_tbl ↣ₐ WInt (encode_entry_point (Z.of_nat nargs) off)) ∗
    PC ↦ᵣ switcher_pc (switcher_block_offset 7 + 1) ∗
    PC ↣ᵣ switcher_pc (switcher_block_offset 7 + 1) ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cs1 ↣ᵣ swcs1 ∗
    ct1 ↦ᵣ WCap RO g_tbl b_tbl e_tbl a_tbl ∗
    ct1 ↣ᵣ WCap RO g_tbl b_tbl e_tbl a_tbl ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    cgp ↦ᵣ wcgp ∗
    cgp ↣ᵣ swcgp ∗
    cra ↦ᵣ wcra ∗
    cra ↣ᵣ swcra ∗
    ( [∗ map] r↦w;s ∈ arg_rmap;arg_smap,
        r ↦ᵣ w ∗ r ↣ᵣ s ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C (w, s) else True ) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    ( [∗ map] r↦w ∈ smap, r ↣ᵣ w ) ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ∀ (arg_rmap' arg_smap' rmap' smap' : Reg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ is_arg_rmap arg_smap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ⌝ ∗
        ⌜ dom smap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ⌝ ∗
        ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap RX Global bpcc epcc (bpcc ^+ off)%a ∗
        PC ↣ᵣ WCap RX Global bpcc epcc (bpcc ^+ off)%a ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cgp ↣ᵣ wcgp_tgt ∗
        cra ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        cra ↣ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w;s ∈ arg_rmap';arg_smap',
            r ↦ᵣ w ∗ r ↣ᵣ s ∗
            if decide (r ∈ dom_arg_rmap nargs)
            then interp W C (w, s)
            else ⌜ w = WInt 0 ∧ s = WInt 0 ⌝ ) ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        ( [∗ map] r↦w ∈ smap', r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        switcher_spec_code -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros (Htbl Htbl1 Hnargs Hargs Hsargs Hdom Hsdom)
      "(#Hspec & Hj & #Htbl_pcc & #Htbl_cgp & #Htbl_entry & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1
      & Hct1 & Hsct1 & Hct2 & Hsct2 & Hctp & Hsctp & Hcgp & Hscgp & Hcra & Hscra
      & Hargs & Hregs & Hsregs & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    pose proof switcher_return_offset.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".

    (* Block 7: read the entry of the export table *)
    switcher_focus_block_lockstep 7 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    change_pc_to ((a_switcher_call ^+ switcher_block_offset 7) ^+ 1)%a.
    iApply (switcher_call_block_7_after_unseal_spec with
      "[- $Hspec $Hj $Htbl_entry $HPC $HsPC $Hcs0 $Hscs0 $Hct1 $Hsct1 $Hct2 $Hsct2 $Hcode $Hscode]");
      [done|done|lia|].
    iNext; iIntros "(Hj & HPC & HsPC & Hcs0 & Hscs0 & Hct1 & Hsct1 & Hct2 & Hsct2 & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Block 8: load the PCC and CGP of the callee *)
    switcher_focus_block_lockstep 8 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_8_spec with
      "[- $Hspec $Hj $Htbl_pcc $Htbl_cgp $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hct1 $Hsct1
        $Hct2 $Hsct2 $Hcgp $Hscgp $Hcra $Hscra $Hcode $Hscode]");
      [done|done|done|].
    iNext; iIntros "(Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hct1 & Hsct1 & Hct2 & Hsct2
      & Hcgp & Hscgp & Hcra & Hscra & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Block 9: clear the unused argument registers *)
    switcher_focus_block_lockstep 9 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (clear_registers_pre_call_skip_spec _ _ _ _ _ arg_rmap arg_smap (nargs+1)
             with "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode]"); try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame "Hct2 Hsct2 Hargs".
    iIntros "!> (%arg_rmap' & %arg_smap' & %Harg_rmap' & %Harg_smap' & Hj & HPC & HsPC
      & Hct2 & Hsct2 & Hargs & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Block 10: clear the other registers *)
    switcher_focus_block_lockstep 10 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iInsertList "Hregs" [ct1;ctp;ct2;cs1;cs0].
    iInsertListSpec "Hsregs" [ct1;ctp;ct2;cs1;cs0].
    iApply (clear_registers_pre_call_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode $Hregs $Hsregs]"); try solve_pure.
    { rewrite !dom_insert_L Hdom. set_solver-. }
    { rewrite !dom_insert_L Hsdom. set_solver-. }
    iIntros "!> (%rmap' & %smap' & %Hrmap' & %Hsmap' & Hj & HPC & HsPC & Hregs & Hsregs
      & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Block 11: jump to the callee *)
    switcher_focus_block_lockstep 11 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    (* Jalr cra cra *)
    iInstr_lockstep "Hscode" "Hcode".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 11) ^+ 1)%a = a_switcher_return);
      last (rewrite switcher_return_offset; offsets_compute; solve_addr).
    iApply ("Hpost" $! arg_rmap' arg_smap' rmap' smap'); iFrame; done.
  Qed.

End Switcher_Call_Blocks_4.
