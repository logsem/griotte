From iris.proofmode Require Import proofmode.
From griotte Require Import logrel_binary memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary.
From griotte Require Export switcher_preamble_binary.

(** * Blocks 14-15 of the switcher, binary model

    Blocks 14-15 clear the registers and jump back to the caller, in both
    runs. Both register files are cleared, hence equal. They are shared by
    the return routine ([switcher_return_blocks_2_binary]) and by the call
    routine when the trusted stack is exhausted
    ([switcher_call_blocks_5_binary]). *)

Section Switcher_Blocks_14_15.
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

  Lemma switcher_return_block_15_spec
    pc_a
    wret swret
    (rmap : Reg) :
    let switcher_instrs_15 := switcher_instrs_n 15 in
    let len_switcher_15 := length switcher_instrs_15 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_15)%a ->
    is_Some (rmap !! cnull) ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    cra ↦ᵣ wret ∗
    cra ↣ᵣ swret ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝) ∗
    codefrag pc_a switcher_instrs_15 ∗
    spec_codefrag pc_a switcher_instrs_15 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ updatePcPerm wret ∗
        PC ↣ᵣ updatePcPerm swret ∗
        cra ↦ᵣ wret ∗
        cra ↣ᵣ swret ∗
        ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝) ∗
        codefrag pc_a switcher_instrs_15 ∗
        spec_codefrag pc_a switcher_instrs_15 ∗
        £ 1 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_15 len_switcher_15.
    subst switcher_instrs_15 len_switcher_15.
    iIntros (Hsub_reg [wcnull Hcnull]) "(#Hspec & Hj & HPC & HsPC & Hcra & Hscra & Hrmap
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    iDestruct (big_sepM_delete _ _ cnull with "Hrmap") as "[(Hcnull & Hscnull & %Hw) Hrmap]";
      first exact Hcnull.
    subst wcnull.

    (* Jalr cnull cra *)
    iInstr_spec "Hscode".
    (* Jalr cnull cra *)
    iInstr "Hcode" with "Hlc".

    iDestruct (big_sepM_delete _ _ cnull with "[$Hrmap $Hcnull $Hscnull]") as "Hrmap";
      [done|done|].
    iApply "Hpost"; iFrame.
  Qed.

  (** Blocks 14-15: clear the registers and jump to [wcra]. *)
  Lemma switcher_blocks_14_15_spec (wcra swcra : Word) (rmap smap : Reg) :
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    dom smap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ switcher_block_pc 14 ∗
    PC ↣ᵣ switcher_block_pc 14 ∗
    cra ↦ᵣ wcra ∗
    cra ↣ᵣ swcra ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    ( [∗ map] r↦w ∈ smap, r ↣ᵣ w ) ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ∀ (rmap' : Reg),
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ updatePcPerm wcra ∗
        PC ↣ᵣ updatePcPerm swcra ∗
        cra ↦ᵣ wcra ∗
        cra ↣ᵣ swcra ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        switcher_spec_code ∗
        £ 1 -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros (Hdom Hsdom) "(#Hspec & Hj & HPC & HsPC & Hcra & Hscra & Hrmap & Hsmap
      & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".

    (* Block 14: clear the registers *)
    switcher_focus_block_lockstep 14 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (clear_registers_post_call_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hrmap $Hsmap $Hcode $Hscode]"); try solve_pure.
    iNext; iIntros "(%rmap' & %smap' & %Hrmap' & %Hsmap' & Hj & HPC & HsPC & Hrmap & Hsmap
      & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Both register files are cleared: they are the same map *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hrmap_zero]".
    iDestruct (big_sepM_sep with "Hsmap") as "[Hsmap %Hsmap_zero]".
    assert (smap' = rmap') as ->.
    { apply zero_rmaps_eq; auto. by rewrite Hrmap' Hsmap'. }
    iAssert ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝)%I
      with "[Hrmap Hsmap]" as "Hrmap".
    { iDestruct (big_sepM_sep with "[$Hrmap $Hsmap]") as "Hrmap".
      iApply (big_sepM_impl with "Hrmap").
      iIntros "!> %r %w %Hr [$ $]". iPureIntro. by apply (Hrmap_zero r w). }

    (* Block 15: jump to the caller *)
    switcher_focus_block_lockstep 15 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_return_block_15_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcra $Hscra $Hrmap $Hcode $Hscode]").
    { done. }
    { apply elem_of_dom; rewrite Hrmap'; set_solver. }
    iNext; iIntros "(Hj & HPC & HsPC & Hcra & Hscra & Hrmap & Hcode & Hscode & Hlc)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    iApply ("Hpost" $! rmap'); iFrame; done.
  Qed.

End Switcher_Blocks_14_15.
