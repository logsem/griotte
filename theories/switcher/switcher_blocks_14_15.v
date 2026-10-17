From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Export switcher_preamble.

(** * Blocks 14-15 of the switcher

    Blocks 14-15 clear the registers and jump back to the caller. They are
    shared by the return routine ([switcher_return_blocks_2]) and by the call
    routine when the trusted stack is exhausted ([switcher_call_blocks_5]). *)

Section Switcher_Blocks_14_15.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_return_block_15_spec
    pc_b pc_e pc_a
    wret
    (rmap : LReg) :
    let switcher_instrs_15 := switcher_instrs_n 15 in
    let len_switcher_15 := length switcher_instrs_15 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_15)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    cra ↦ᵣ wret ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝) ∗
    codefrag_pers pc_a switcher_instrs_15 ∗
    ▷ ( PC ↦ₚ lupdatePcPerm wret ∗
        cra ↦ᵣ wret ∗
        ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝) ∗
        codefrag_pers pc_a switcher_instrs_15 ∗
        £ 1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_15 len_switcher_15.
    subst switcher_instrs_15 len_switcher_15.
    iIntros (Hsub_reg) "(HPC & Hcra & Hrmap & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    destruct (jalr_target_ok cnull cra wret.(lw)) eqn:Htgt; cycle 1.
    { (* --- Jalr cnull cra --- *)
      iInstr_fail "Hcode".
      wp_end; by iIntros (?). }
    (* --- Jalr cnull cra --- *)
    iInstr "Hcode" with "Hlc".
    iApply "Hpost"; iFrame "∗ Hcode".
  Qed.

  (** Blocks 14-15: clear the registers and jump to [wcra]. *)
  Lemma switcher_blocks_14_15_spec (wcra : LWord) (rmap : LReg) :
    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ switcher_label_pc ".Lswitch_callee_dead_zeros" ∗
    cra ↦ᵣ wcra ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        PC ↦ₚ lupdatePcPerm wcra ∗
        cra ↦ᵣ wcra ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdom) "(HPC & Hcra & Hrmap & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 14: clear the registers *)
    switcher_focus_block (switcher_block ".Lswitch_callee_dead_zeros") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]");
      try solve_pure.
    iNext; iIntros "(%rmap' & %Hrmap' & HPC & Hrmap & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 15: jump to the caller *)
    switcher_focus_block (switcher_block ".Lswitcher_return_to_caller") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_return_block_15_spec with "[- $HPC $Hcra $Hrmap $Hcode]").
    { done. }
    iNext; iIntros "(HPC & Hcra & Hrmap & _ & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    iApply ("Hpost" $! rmap'); iFrame "∗ Hswitcher"; done.
  Qed.

End Switcher_Blocks_14_15.
