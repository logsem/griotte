From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics logrel switcher_load_spec.
From griotte Require Import switcher_call_states switcher_blocks_15_16.

(** * Call routine, block 17 and blocks 15-16: trusted stack exhausted

    When the trusted stack is exhausted (block 3), block 17 restores the
    callee-save registers, and blocks 15-16 clear the registers and jump
    back to the caller. *)

Section Switcher_Call_Blocks_5.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Exhausting the trusted stack restores the saved registers before
      returning the error code. As on a regular return, each load may
      clear the tag of a saved heap capability. *)
  Lemma switcher_call_block_17_spec
    pc_b pc_e pc_a
    wcgp wcra wcs0 wcs1 b_stk e_stk a_stk :
    let switcher_instrs_17 := (switcher_instrs_n 17) in
    let len_switcher_17 := length switcher_instrs_17 in
    (* The distance from this block to the block that clears the registers. *)
    let off_dead_zeros :=
      asm_label_offset switcher_asm ".Lswitch_trusted_stack_exhausted" ".Lswitch_callee_dead_zeros" in
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_17)%a ->

    (pc_a ^+ 10 +
       asm_label_offset switcher_asm ".Lswitch_trusted_stack_exhausted_return"
         ".Lswitch_callee_dead_zeros")%a =
      Some (pc_a ^+ off_dead_zeros)%a ->

    (b_stk <= a_stk)%a ->
    (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag_pers pc_a switcher_instrs_17 ∗
    ▷ (∀ rcgp rcra rcs0 rcs1,
        ⌜load_heap wcgp rcgp ∧ load_heap wcra rcra ∧
          load_heap wcs0 rcs0 ∧ load_heap wcs1 rcs1⌝ -∗
        ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ off_dead_zeros)%a ∗
             cs0 ↦ᵣ rcs0 ∗
             cs1 ↦ᵣ rcs1 ∗
             cgp ↦ᵣ rcgp ∗
             cra ↦ᵣ rcra ∗
             ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
             ca1 ↦ᵣ WInt 0 ∗
             csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
             a_stk ↦ₐ wcs0 ∗
             (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
             (a_stk ^+ 2)%a ↦ₐ wcra ∗
             (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag_pers pc_a switcher_instrs_17 ∗
             £ 1 -∗
             WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
           )
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_17 len_switcher_17 off_dead_zeros;
      subst switcher_instrs_17 len_switcher_17 off_dead_zeros.
    iIntros (Hstk_shadow Hsub_reg Hpca_next Hbstk Hbstk')
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0] & [%wca1 Hca1]
      & Hcsp & Hastk0 & Hastk1 & Hastk2 & Hastk3 & #Hcode & Hpost)".
    (* Compute the distance to the block that clears the registers. *)
    offsets_compute.
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 3)%a ) ; solve_addr. }
    (* CLoad cgp csp; *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 2)%a cgp csp
      _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Hastk3]"
      as (rcgp) "(%Hrcgp & HPC & Hcgp & Hcsp & Hastk3)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 2)%a ) ; solve_addr. }
    (* CLoad cra csp; *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 4)%a cra csp
      _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Hastk2]"
      as (rcra) "(%Hrcra & HPC & Hcra & Hcsp & Hastk2)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 1)%a ) ; solve_addr. }
    (* CLoad cs1 csp; *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 6)%a cs1 csp
      _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Hastk1]"
      as (rcs1) "(%Hrcs1 & HPC & Hcs1 & Hcsp & Hastk1)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some a_stk ) ; solve_addr. }
    (* CLoad cs0 csp; *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 8)%a cs0 csp
      _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Hastk0]"
      as (rcs0) "(%Hrcs0 & HPC & Hcs0 & Hcsp & Hastk0)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Mov ca0 (inl (-141)%Z); *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull))as [|_]; first done.
    (* Mov ca1 (inl 0%Z); *)
    iInstr "Hcode" with "Hlc".
    (* Jmp (inl (-20)%Z) *)
    iInstr "Hcode".

    iApply ("Hpost" $! rcgp rcra rcs0 rcs1 with "[%]"); first done. iFrame "∗ Hcode".
  Qed.

  (** Saved words may become stale if their heap addresses are freed during a
      callback. Each restored register records its actual load result and
      whether that result retains authority in the current world. *)
  Lemma switcher_call_block_17_world_spec
    W C
    pc_b pc_e pc_a
    wcgp wcra wcs0 wcs1 b_stk e_stk a_stk :
    let switcher_instrs_17 := (switcher_instrs_n 17) in
    let len_switcher_17 := length switcher_instrs_17 in
    (* The distance from this block to the block that clears the registers. *)
    let off_dead_zeros :=
      asm_label_offset switcher_asm ".Lswitch_trusted_stack_exhausted" ".Lswitch_callee_dead_zeros" in
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_17)%a ->

    (pc_a ^+ 10 +
       asm_label_offset switcher_asm ".Lswitch_trusted_stack_exhausted_return"
         ".Lswitch_callee_dead_zeros")%a =
      Some (pc_a ^+ off_dead_zeros)%a ->

    (b_stk <= a_stk)%a ->
    (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    world_interp W C ∗
    codefrag_pers pc_a switcher_instrs_17 ∗
    ▷ (∀ rcgp rcra rcs0 rcs1,
        ⌜load_heap_in_world W wcgp rcgp ∧
          load_heap_in_world W wcra rcra ∧
          load_heap_in_world W wcs0 rcs0 ∧
          load_heap_in_world W wcs1 rcs1⌝ -∗
        ( world_interp W C ∗
             PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ off_dead_zeros)%a ∗
             cs0 ↦ᵣ rcs0 ∗
             cs1 ↦ᵣ rcs1 ∗
             cgp ↦ᵣ rcgp ∗
             cra ↦ᵣ rcra ∗
             ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
             ca1 ↦ᵣ WInt 0 ∗
             csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
             a_stk ↦ₐ wcs0 ∗
             (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
             (a_stk ^+ 2)%a ↦ₐ wcra ∗
             (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag_pers pc_a switcher_instrs_17 ∗
             £ 1 -∗
             WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
           )
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_17 len_switcher_17 off_dead_zeros;
      subst switcher_instrs_17 len_switcher_17 off_dead_zeros.
    iIntros (Hstk_shadow Hsub_reg Hpca_next Hbstk Hbstk')
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0] & [%wca1 Hca1]
      & Hcsp & Hastk0 & Hastk1 & Hastk2 & Hastk3 & Hworld & #Hcode & Hpost)".
    (* Compute the distance to the block that clears the registers. *)
    offsets_compute.
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 3)%a ) ; solve_addr. }
    iEval (rewrite open_world_interp_empty) in "Hworld".
    (* CLoad cgp csp; *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ (pc_a ^+ 2)%a cgp csp
      _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Hastk3 $Hworld]"
      as (rcgp) "(%Hrcgp & HPC & Hcgp & Hcsp & Hastk3 & Hworld)".
    { reflexivity. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 2)%a ) ; solve_addr. }
    (* CLoad cra csp; *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ (pc_a ^+ 4)%a cra csp
      _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Hastk2 $Hworld]"
      as (rcra) "(%Hrcra & HPC & Hcra & Hcsp & Hastk2 & Hworld)".
    { reflexivity. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 1)%a ) ; solve_addr. }
    (* CLoad cs1 csp; *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ (pc_a ^+ 6)%a cs1 csp
      _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Hastk1 $Hworld]"
      as (rcs1) "(%Hrcs1 & HPC & Hcs1 & Hcsp & Hastk1 & Hworld)".
    { reflexivity. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some a_stk ) ; solve_addr. }
    (* CLoad cs0 csp; *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ (pc_a ^+ 8)%a cs0 csp
      _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Hastk0 $Hworld]"
      as (rcs0) "(%Hrcs0 & HPC & Hcs0 & Hcsp & Hastk0 & Hworld)".
    { reflexivity. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Mov ca0 (inl (-141)%Z); *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull))as [|_]; first done.
    (* Mov ca1 (inl 0%Z); *)
    iInstr "Hcode" with "Hlc".
    (* Jmp (inl (-20)%Z) *)
    iInstr "Hcode".

    iEval (rewrite -open_world_interp_empty) in "Hworld".
    iSpecialize ("Hpost" $! rcgp rcra rcs0 rcs1 with "[%]"); first done.
    iApply "Hpost". iFrame "∗ Hcode".
  Qed.

  (** Block 17, then blocks 15-16: the trusted stack is exhausted. Restore
      the callee-save registers, clear the registers and jump back to the
      caller with the error code [ENOTENOUGHTRUSTEDSTACK]. Each restored
      register is the result of a load, which may clear the tag of a saved
      heap capability. *)
  Lemma switcher_call_blocks_5_spec
    (b e a : Addr) (wcs0 wcs1 wcra wcgp : LWord) (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap true RWL Local b e (a ^+ 4)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs0 rcs1,
        ⌜ load_heap wcgp rcgp ∧ load_heap wcra rcra ∧
          load_heap wcs0 rcs0 ∧ load_heap wcs1 rcs1 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cs0 ↦ᵣ rcs0 ∗
        cs1 ↦ᵣ rcs1 ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ WInt 0 ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 1 -∗
        ( PC ↦ₚ lupdatePcPerm rcra ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hrmap & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 17: restore the callee-save registers *)
    switcher_focus_block (switcher_block ".Lswitch_trusted_stack_exhausted") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_17_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hcode]");
      [done|done|offsets_compute; solve_addr|done|done|].
    iNext.
    iIntros (rcgp rcra rcs0 rcs1 Hrestored)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & _ & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Blocks 15-16: clear the registers and jump to the caller *)
    switcher_change_pc (switcher_label_offset ".Lswitch_callee_dead_zeros").
    iApply (switcher_blocks_15_16_spec with "[- $HPC $Hcra $Hrmap]"); first done.
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap & _)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1); iFrame "∗ % Hswitcher".
  Qed.

  (** Variant of [switcher_call_blocks_5_spec] in a world [W]: each
      restored register retains its authority in [W]. *)
  Lemma switcher_call_blocks_5_world_spec
    (W : WORLD) (C : CmptName)
    (b e a : Addr) (wcs0 wcs1 wcra wcgp : LWord) (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap true RWL Local b e (a ^+ 4)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    world_interp W C ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs0 rcs1,
        ⌜ load_heap_in_world W wcgp rcgp ∧ load_heap_in_world W wcra rcra ∧
          load_heap_in_world W wcs0 rcs0 ∧ load_heap_in_world W wcs1 rcs1 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        world_interp W C ∗
        cs0 ↦ᵣ rcs0 ∗
        cs1 ↦ᵣ rcs1 ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ WInt 0 ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 1 -∗
        ( PC ↦ₚ lupdatePcPerm rcra ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hworld & Hrmap & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 17: restore the callee-save registers *)
    switcher_focus_block (switcher_block ".Lswitch_trusted_stack_exhausted") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_17_world_spec W C with
      "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hworld $Hcode]");
      [done|done|offsets_compute; solve_addr|done|done|].
    iNext.
    iIntros (rcgp rcra rcs0 rcs1 Hrestored)
      "(Hworld & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & _ & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Blocks 15-16: clear the registers and jump to the caller *)
    switcher_change_pc (switcher_label_offset ".Lswitch_callee_dead_zeros").
    iApply (switcher_blocks_15_16_spec with "[- $HPC $Hcra $Hrmap]"); first done.
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap & _)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1); iFrame "∗ % Hswitcher".
  Qed.

End Switcher_Call_Blocks_5.
