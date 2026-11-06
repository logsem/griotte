From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_compiled_spec_states.

(** * Compiled cmdc, blocks 2-3 and 6-7: assertions after the calls

    On return from the call [c], the first block loads the global that was
    not shared with the callee, through [cs1] (resp. [cs0]), and the
    expected value, and the second block calls the compiled assert library
    on them. *)

Section CMDC_Compiled_Check_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  (** The proof of [cmdc_compiled_check_blocks_3_spec], for the call that
      returns at the label [l_ret], followed by the call to the assert
      library at [l_assert], at the offset [off] from the import of the
      library, and by the code at [l_next]: the code of the two calls only
      differs by the checked global and the expected value. *)
  #[local] Ltac cmdc_compiled_check_blocks_proof l_ret l_assert off l_next pc_a :=
    let hcont := fresh "hcont" in
    let a_ret := fresh "a_ret" in
    let a_assert := fresh "a_assert" in
    let Ha_ret := fresh "Ha_ret" in
    let Ha_assert := fresh "Ha_assert" in
    (* Return from the call: load the checked global and the expected value *)
    focus_block (cmdc_compiled_block l_ret) "Hcode_main" of cmdc_compiled_main_blocks
      at pc_a as a_ret Ha_ret "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    (* CLoad ca0 cs1 0, resp. CLoad ca0 cs0 0 *)
    iInstr "Hcode";
    [ by apply not_mmio_not_shadow
    | done
    | split; [done | rewrite /withinBounds; solve_addr]
    | ];
    iEval (rewrite lload_word_no_dl_dro //) in "Hca0";
    (* GetA ca0 ca0 *)
    iInstr "Hcode";
    (* Mov ca1 0, resp. Mov ca1 42 *)
    iInstr "Hcode";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";

    (* Call the assert library *)
    focus_block (cmdc_compiled_block l_assert) "Hcode_main" of cmdc_compiled_main_blocks
      at pc_a as a_assert Ha_assert "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    iApply (assert_compiled_call_success_spec 1 off ct2 with
             "[- $Hassert $HPC $Hct2 $Hcra $Hca0 $Hca1 $Hmie $Hheld $Hcode $Himport_assert]");
    [ done
    | cbn; solve_addr
    | offsets_compute; solve_addr
    | rewrite /withinBounds; solve_addr
    | done | done | done | done
    | ];
    iNext; iIntros "(HPC & Hct2 & Hcra & Hca0 & Hca1 & Hmie & Hheld & _ & _)";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";
    change_pc_to (pc_a ^+ cmdc_compiled_label_offset l_next);
    iApply "Hpost"; iFrame "∗ Hcode_main Himport_assert".

  Lemma cmdc_compiled_check_blocks_3_spec (c : cmdc_compiled_call)
    (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable)
    (b_lib e_lib a_flag a_chk : Addr)
    (wca0 wca1 wct2 wcra : LWord) (b : InterruptStatus) :
    let rchk := cmdc_compiled_call_checked c in
    cmdc_compiled_code_bounds pc_b pc_e pc_a B_f C_g ->
    (a_chk + 1)%a = Some (a_chk ^+ 1) ->
    is_mmio_address a_chk = false ->
    route_pre th b ->
    assert_compiled_static b_lib e_lib a_flag ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e
      (pc_a ^+ cmdc_compiled_label_offset (cmdc_compiled_return_label c)) ∗
    rchk ↦ᵣ[th] Cap RW Global a_chk (a_chk ^+ 1) a_chk ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cra ↦ᵣ[th] wcra ∗
    a_chk ↦ₐ WInt (cmdc_compiled_call_expected c) ∗
    (pc_b ^+ 1) ↦ₐ□ assert_compiled_entry_of Global b_lib e_lib ∗
    codefrag_pers pc_a cmdc_compiled_main_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ▷ ( PC ↦ₚ[th] Cap RX Global pc_b pc_e
          (pc_a ^+ cmdc_compiled_label_offset (cmdc_compiled_next_label c)) ∗
        rchk ↦ᵣ[th] Cap RW Global a_chk (a_chk ^+ 1) a_chk ∗
        ca0 ↦ᵣ[th] WInt (cmdc_compiled_call_expected c) ∗
        ca1 ↦ᵣ[th] WInt (cmdc_compiled_call_expected c) ∗
        (∃ w, ct2 ↦ᵣ[th] w) ∗
        (∃ w, cra ↦ᵣ[th] w) ∗
        a_chk ↦ₐ WInt (cmdc_compiled_call_expected c) ∗
        (pc_b ^+ 1) ↦ₐ□ assert_compiled_entry_of Global b_lib e_lib ∗
        codefrag_pers pc_a cmdc_compiled_main_code ∗
        MIE ↦ₜ[th] b ∗
        held (th := th) b
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    intros rchk; subst rchk.
    destruct c; cbn [cmdc_compiled_call_checked cmdc_compiled_return_label
                       cmdc_compiled_next_label cmdc_compiled_call_expected].
    all: iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & HB_f_nonheap
                   & HC_g_nonheap) Ha_chk Ha_chk_mmio Hroute)
      "(#Hassert & HPC & Hchk & Hca0 & Hca1 & Hct2 & Hcra & Hchk_val & #Himport_assert
      & Hcode_main & Hmie & Hheld & Hpost)".
    all: rewrite /cmdc_compiled_main_run_offset in Himports_contiguous.
    all: codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    all: unfold_code cmdc_compiled_main_code "Hcode_main".
    - (* Return from [B.f], blocks 2-3 *)
      cmdc_compiled_check_blocks_proof
        ".Lcmdc_run_return_B_f"%string ".Lcmdc_run_assert_1"%string (-26)%Z
        ".Lcmdc_run_return_assert_1"%string pc_a.
    - (* Return from [C.g], blocks 6-7 *)
      cmdc_compiled_check_blocks_proof
        ".Lcmdc_run_return_C_g"%string ".Lcmdc_run_assert_2"%string (-40)%Z
        ".Lcmdc_run_return_assert_2"%string pc_a.
  Qed.

End CMDC_Compiled_Check_Blocks_3.
