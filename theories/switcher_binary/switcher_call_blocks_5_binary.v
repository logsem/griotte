From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import register_tactics register_tactics_binary.
From griotte Require Import switcher_call_states_binary switcher_blocks_14_15_binary.

(** * Call routine, block 16 and blocks 14-15: trusted stack exhausted, binary model

    When the trusted stack is exhausted (block 3), block 16 restores the
    callee-save registers of each run from its own stack frame, and blocks
    14-15 clear the registers and jump back to the caller. *)

Section Switcher_Call_Blocks_5.
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

  Lemma switcher_call_block_16_spec
    pc_a
    wcgp swcgp wcra swcra wcs0 swcs0 wcs1 swcs1 b_stk e_stk a_stk :
    let switcher_instrs_16 := switcher_instrs_n 16 in
    let len_switcher_16 := length switcher_instrs_16 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_16)%a ->
    (pc_a ^+ 10 + -36)%a = Some (pc_a ^+ -26)%a ->
    (b_stk <= a_stk)%a ->
    (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    (∃ w sw, cs0 ↦ᵣ w ∗ cs0 ↣ᵣ sw) ∗
    (∃ w sw, cs1 ↦ᵣ w ∗ cs1 ↣ᵣ sw) ∗
    (∃ w sw, cgp ↦ᵣ w ∗ cgp ↣ᵣ sw) ∗
    (∃ w sw, cra ↦ᵣ w ∗ cra ↣ᵣ sw) ∗
    (∃ w sw, ca0 ↦ᵣ w ∗ ca0 ↣ᵣ sw) ∗
    (∃ w sw, ca1 ↦ᵣ w ∗ ca1 ↣ᵣ sw) ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    csp ↣ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcra wcgp ∗
    switcher_stk_cells_spec a_stk swcs0 swcs1 swcra swcgp ∗
    codefrag pc_a switcher_instrs_16 ∗
    spec_codefrag pc_a switcher_instrs_16 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ -26)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ -26)%a ∗
        cs0 ↦ᵣ wcs0 ∗
        cs0 ↣ᵣ swcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cs1 ↣ᵣ swcs1 ∗
        cgp ↦ᵣ wcgp ∗
        cgp ↣ᵣ swcgp ∗
        cra ↦ᵣ wcra ∗
        cra ↣ᵣ swcra ∗
        ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca0 ↣ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ WInt 0 ∗
        ca1 ↣ᵣ WInt 0 ∗
        csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcra wcgp ∗
        switcher_stk_cells_spec a_stk swcs0 swcs1 swcra swcgp ∗
        codefrag pc_a switcher_instrs_16 ∗
        spec_codefrag pc_a switcher_instrs_16 ∗
        £ 1 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_16 len_switcher_16; subst switcher_instrs_16 len_switcher_16.
    iIntros (Hsub_reg Hpca_next Hbstk Hbstk')
      "(#Hspec & Hj & HPC & HsPC & (% & % & Hcs0 & Hscs0) & (% & % & Hcs1 & Hscs1)
      & (% & % & Hcgp & Hscgp) & (% & % & Hcra & Hscra) & (% & % & Hca0 & Hsca0)
      & (% & % & Hca1 & Hsca1) & Hcsp & Hscsp
      & (Hastk0 & Hastk1 & Hastk2 & Hastk3) & (Hsastk0 & Hsastk1 & Hsastk2 & Hsastk3)
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (a_stk ^+ 3)%a); solve_addr.
    (* Load cgp csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; solve_addr.
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (a_stk ^+ 2)%a); solve_addr.
    (* Load cra csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; solve_addr.
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (a_stk ^+ 1)%a); solve_addr.
    (* Load cs1 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; solve_addr.
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some a_stk); solve_addr.
    (* Load cs0 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; solve_addr.
    (* Mov ca0 ENOTENOUGHTRUSTEDSTACK *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Mov ca1 0 *)
    iInstr_spec "Hscode".
    (* Mov ca1 0 *)
    iInstr "Hcode" with "Hlc".
    (* Jmp (".Lswitch_callee_dead_zeros")%asm *)
    iInstr_lockstep "Hscode" "Hcode".

    iApply "Hpost"; iFrame.
  Qed.


  (** Block 16, then blocks 14-15: the trusted stack is exhausted. Restore
      the callee-save registers, clear the registers and jump back to the
      caller with the error code [ENOTENOUGHTRUSTEDSTACK]. *)
  Lemma switcher_call_blocks_5_spec
    (b e a : Addr) (wcs0 swcs0 wcs1 swcs1 wcra swcra wcgp swcgp : Word) (rmap smap : Reg) :
    switcher_stk_bounds b e a ->
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    dom smap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ switcher_block_pc 16 ∗
    PC ↣ᵣ switcher_block_pc 16 ∗
    (∃ w sw, cs0 ↦ᵣ w ∗ cs0 ↣ᵣ sw) ∗
    (∃ w sw, cs1 ↦ᵣ w ∗ cs1 ↣ᵣ sw) ∗
    (∃ w sw, cgp ↦ᵣ w ∗ cgp ↣ᵣ sw) ∗
    (∃ w sw, cra ↦ᵣ w ∗ cra ↣ᵣ sw) ∗
    (∃ w sw, ca0 ↦ᵣ w ∗ ca0 ↣ᵣ sw) ∗
    (∃ w sw, ca1 ↦ᵣ w ∗ ca1 ↣ᵣ sw) ∗
    csp ↦ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    csp ↣ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    switcher_stk_cells_spec a swcs0 swcs1 swcra swcgp ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    ( [∗ map] r↦w ∈ smap, r ↣ᵣ w ) ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ∀ (rmap' : Reg),
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ updatePcPerm wcra ∗
        PC ↣ᵣ updatePcPerm swcra ∗
        cs0 ↦ᵣ wcs0 ∗
        cs0 ↣ᵣ swcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cs1 ↣ᵣ swcs1 ∗
        cgp ↦ᵣ wcgp ∗
        cgp ↣ᵣ swcgp ∗
        cra ↦ᵣ wcra ∗
        cra ↣ᵣ swcra ∗
        ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca0 ↣ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ WInt 0 ∗
        ca1 ↣ᵣ WInt 0 ∗
        csp ↦ᵣ WCap RWL Local b e a ∗
        csp ↣ᵣ WCap RWL Local b e a ∗
        switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
        switcher_stk_cells_spec a swcs0 swcs1 swcra swcgp ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        switcher_spec_code ∗
        £ 2 -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hdom Hsdom)
      "(#Hspec & Hj & HPC & HsPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp & Hscsp
      & Hcells & Hscells & Hrmap & Hsmap & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".

    (* Block 16: restore the callee-save registers *)
    switcher_focus_block_lockstep 16 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_16_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp $Hscsp
        $Hcells $Hscells $Hcode $Hscode]");
      [done|offsets_compute; solve_addr|done|done|].
    iNext.
    iIntros "(Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcgp & Hscgp & Hcra & Hscra
      & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcsp & Hscsp & Hcells & Hscells & Hcode & Hscode & Hlc)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Blocks 14-15: clear the registers and jump to the caller *)
    switcher_change_pc (switcher_block_offset 14).
    iApply (switcher_blocks_14_15_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcra $Hscra $Hrmap $Hsmap]"); [done|done|].
    iSplitL "Hcode"; first iExact "Hcode".
    iSplitL "Hscode"; first iExact "Hscode".
    iNext; iIntros (rmap') "(%Hrmap' & Hj & HPC & HsPC & Hcra & Hscra & Hrmap & Hcode & Hscode & Hlc')".
    iCombine "Hlc Hlc'" as "Hlc".
    iApply ("Hpost" $! rmap'); iFrame "∗ %".
  Qed.

End Switcher_Call_Blocks_5.
