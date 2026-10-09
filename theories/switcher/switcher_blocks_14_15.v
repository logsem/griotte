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
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_return_block_15_spec
    pc_b pc_e pc_a
    wret
    (rmap : Reg) :
    let switcher_instrs_15 := switcher_instrs_n 15 in
    let len_switcher_15 := length switcher_instrs_15 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_15)%a ->
    is_Some (rmap !! cnull) ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cra ↦ᵣ wret ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝) ∗
    codefrag pc_a switcher_instrs_15 ∗
    ▷ ( PC ↦ᵣ updatePcPerm wret ∗
        cra ↦ᵣ wret ∗
        ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝) ∗
        codefrag pc_a switcher_instrs_15 ∗
        £ 1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_15 len_switcher_15.
    subst switcher_instrs_15 len_switcher_15.
    iIntros (Hsub_reg Hcnull_in) "(HPC & Hcra & Hrmap & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    iAssert (⌜map_Forall (λ (_ : RegName) (x : Word), x = WInt 0) rmap⌝)%I
      as "%Hrmap_zeroes".
    { iDestruct (big_sepM_sep with "Hrmap") as "[_ %]"; auto. }
    destruct Hcnull_in as [wcnull Hcnull_in].
    iExtract "Hrmap" cnull as "[Hcnull %]".

    (* --- Jalr cnull cra --- *)
    iInstr "Hcode" with "Hlc".

    iAssert (∃ wnull, cnull ↦ᵣ wnull ∗ ⌜wnull = WInt 0⌝)%I
      with "[Hcnull]" as (wnull) "Hcnull".
    { iFrame; done. }
    iInsert "Hrmap" cnull.
    iAssert (⌜<[cnull := wnull]> rmap = rmap⌝)%I as "%Hrmap_id".
    { iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hint]".
      iPureIntro.
      clear -Hcnull_in Hint Hrmap_zeroes.
      apply insert_id.
      pose proof (map_Forall_insert_1_1 _ _ _ _ Hint); cbn in *.
      rewrite H.
      rewrite Hcnull_in.
      by eapply map_Forall_lookup in Hcnull_in; eauto; cbn in *; simplify_map_eq.
    }
    rewrite Hrmap_id.
    clear dependent Hrmap_id Hrmap_zeroes wcnull wnull.
    iApply "Hpost"; iFrame.
  Qed.

  (** Blocks 14-15: clear the registers and jump to [wcra]. *)
  Lemma switcher_blocks_14_15_spec (wcra : Word) (rmap : Reg) :
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ᵣ switcher_block_pc 14 ∗
    cra ↦ᵣ wcra ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : Reg),
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        PC ↦ᵣ updatePcPerm wcra ∗
        cra ↦ᵣ wcra ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdom) "(HPC & Hcra & Hrmap & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".

    (* Block 14: clear the registers *)
    switcher_focus_block 14 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]");
      try solve_pure.
    iNext; iIntros "(%rmap' & %Hrmap' & HPC & Hrmap & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 15: jump to the caller *)
    switcher_focus_block 15 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_return_block_15_spec with "[- $HPC $Hcra $Hrmap $Hcode]").
    { done. }
    { apply elem_of_dom; rewrite Hrmap'; set_solver. }
    iNext; iIntros "(HPC & Hcra & Hrmap & Hcode & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    iApply ("Hpost" $! rmap'); iFrame; done.
  Qed.

End Switcher_Blocks_14_15.
