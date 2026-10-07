From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_call_states switcher_blocks_14_15.

(** * Call routine, block 16 and blocks 14-15: trusted stack exhausted

    When the trusted stack is exhausted (block 3), block 16 restores the
    callee-save registers, and blocks 14-15 clear the registers and jump
    back to the caller. *)

Section Switcher_Call_Blocks_5.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_call_block_16_spec
    pc_b pc_e pc_a
    wcgp wcra wcs0 wcs1 b_stk e_stk a_stk :
    let switcher_instrs_16 := (switcher_instrs_n 16) in
    let len_switcher_16 := length switcher_instrs_16 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_16)%a ->

    (pc_a ^+ 10 + -36)%a = Some (pc_a ^+ -26)%a ->

    (b_stk <= a_stk)%a ->
    (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag pc_a switcher_instrs_16 ∗
    ▷  (( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ -26)%a ∗
             cs0 ↦ᵣ wcs0 ∗
             cs1 ↦ᵣ wcs1 ∗
             cgp ↦ᵣ wcgp ∗
             cra ↦ᵣ wcra ∗
             ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
             ca1 ↦ᵣ WInt 0 ∗
             csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
             a_stk ↦ₐ wcs0 ∗
             (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
             (a_stk ^+ 2)%a ↦ₐ wcra ∗
             (a_stk ^+ 3)%a ↦ₐ wcgp ∗
             codefrag pc_a switcher_instrs_16 ∗
             £ 1 -∗
             WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
           )
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_16 len_switcher_16; subst switcher_instrs_16 len_switcher_16.
    iIntros (Hsub_reg Hpca_next Hbstk Hbstk')
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0] & [%wca1 Hca1]
      & Hcsp & Hastk0 & Hastk1 & Hastk2 & Hastk3 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 3)%a) ; solve_addr. }
    (* Load cgp csp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 2)%a) ; solve_addr. }
    (* Load cra csp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 1)%a) ; solve_addr. }
    (* Load cs1 csp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some a_stk ) ; solve_addr. }
    (* Load cs0 csp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    (* Mov ca0 (inl (-141)%Z); *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull))as [|_]; first done.
    (* Mov ca1 (inl 0%Z); *)
    iInstr "Hcode" with "Hlc".
    (* Jmp (inl (-36)%Z) *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.


  (** Block 16, then blocks 14-15: the trusted stack is exhausted. Restore
      the callee-save registers, clear the registers and jump back to the
      caller with the error code [ENOTENOUGHTRUSTEDSTACK]. *)
  Lemma switcher_call_blocks_5_spec
    (b e a : Addr) (wcs0 wcs1 wcra wcgp : Word) (rmap : Reg) :
    switcher_stk_bounds b e a ->
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ᵣ switcher_block_pc 16 ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : Reg),
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        PC ↦ᵣ updatePcPerm wcra ∗
        cs0 ↦ᵣ wcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cgp ↦ᵣ wcgp ∗
        cra ↦ᵣ wcra ∗
        ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ WInt 0 ∗
        csp ↦ᵣ WCap RWL Local b e a ∗
        switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hdom)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hrmap & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".

    (* Block 16: restore the callee-save registers *)
    switcher_focus_block 16 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_16_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hcode]");
      [done|offsets_compute; solve_addr|done|done|].
    iNext.
    iIntros "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Blocks 14-15: clear the registers and jump to the caller *)
    switcher_change_pc (switcher_block_offset 14).
    iApply (switcher_blocks_14_15_spec with "[- $HPC $Hcra $Hrmap]"); first done.
    iSplitL "Hcode"; first iFrame "Hcode".
    iNext; iIntros (rmap') "(%Hrmap' & HPC & Hcra & Hrmap & Hcode & Hlc')".
    iCombine "Hlc Hlc'" as "Hlc".
    iApply ("Hpost" $! rmap'); iFrame "∗ %".
  Qed.

End Switcher_Call_Blocks_5.
