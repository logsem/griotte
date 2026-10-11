From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics logrel switcher_load_spec.
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
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Exhausting the trusted stack restores the saved registers before
      returning the error code. As on a regular return, each load may
      clear the tag of a saved heap capability. *)
  Lemma switcher_call_block_16_spec
    pc_b pc_e pc_a
    wcgp wcra wcs0 wcs1 b_stk e_stk a_stk :
    let switcher_instrs_16 := (switcher_instrs_n 16) in
    let len_switcher_16 := length switcher_instrs_16 in
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_16)%a ->

    (pc_a ^+ 10 + -36)%a = Some (pc_a ^+ -26)%a ->

    (b_stk <= a_stk)%a ->
    (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ->

    PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e pc_a ∗
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
    codefrag pc_a switcher_instrs_16 ∗
    ▷ (∀ rcgp rcra rcs0 rcs1,
        ⌜load_heap wcgp rcgp ∧ load_heap wcra rcra ∧
          load_heap wcs0 rcs0 ∧ load_heap wcs1 rcs1⌝ -∗
        ( PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ -26)%a ∗
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
    codefrag pc_a switcher_instrs_16 ∗
             £ 1 -∗
             WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
           )
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_16 len_switcher_16; subst switcher_instrs_16 len_switcher_16.
    iIntros (Hstk_shadow Hsub_reg Hpca_next Hbstk Hbstk')
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0] & [%wca1 Hca1]
      & Hcsp & Hastk0 & Hastk1 & Hastk2 & Hastk3 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 3)%a ) ; solve_addr. }
    (* Load cgp csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 2)%a cgp csp
      _ _ _ _ _ _
      with "[$HPC $Hi $Hcgp $Hcsp $Hastk3]");
      [ |solve_pure|solve_pure|rewrite /withinBounds; solve_addr|solve_addr|discriminate|discriminate|].
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    iNext. iIntros (rcgp) "(%Hrcgp & HPC & Hi & Hcgp & Hcsp & Hastk3 )".
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 2)%a ) ; solve_addr. }
    (* Load cra csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 4)%a cra csp
      _ _ _ _ _ _
      with "[$HPC $Hi $Hcra $Hcsp $Hastk2]");
      [ |solve_pure|solve_pure|rewrite /withinBounds; solve_addr|solve_addr|discriminate|discriminate|].
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    iNext. iIntros (rcra) "(%Hrcra & HPC & Hi & Hcra & Hcsp & Hastk2 )".
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 1)%a ) ; solve_addr. }
    (* Load cs1 csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 6)%a cs1 csp
      _ _ _ _ _ _
      with "[$HPC $Hi $Hcs1 $Hcsp $Hastk1]");
      [ |solve_pure|solve_pure|rewrite /withinBounds; solve_addr|solve_addr|discriminate|discriminate|].
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    iNext. iIntros (rcs1) "(%Hrcs1 & HPC & Hi & Hcs1 & Hcsp & Hastk1 )".
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some a_stk ) ; solve_addr. }
    (* Load cs0 csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 8)%a cs0 csp
      _ _ _ _ _ _
      with "[$HPC $Hi $Hcs0 $Hcsp $Hastk0]");
      [ |solve_pure|solve_pure|rewrite /withinBounds; solve_addr|solve_addr|discriminate|discriminate|].
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    iNext. iIntros (rcs0) "(%Hrcs0 & HPC & Hi & Hcs0 & Hcsp & Hastk0 )".
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Mov ca0 (inl (-141)%Z); *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull))as [|_]; first done.
    (* Mov ca1 (inl 0%Z); *)
    iInstr "Hcode" with "Hlc".
    (* Jmp (inl (-36)%Z) *)
    iInstr "Hcode".

    iApply ("Hpost" $! rcgp rcra rcs0 rcs1 with "[%]"); first done. iFrame.
  Qed.

  (** Saved words may become stale if their heap addresses are freed during a
      callback. Each restored register records its actual load result and
      whether that result retains authority in the current world. *)
  Lemma switcher_call_block_16_world_spec
    W C
    pc_b pc_e pc_a
    wcgp wcra wcs0 wcs1 b_stk e_stk a_stk :
    let switcher_instrs_16 := (switcher_instrs_n 16) in
    let len_switcher_16 := length switcher_instrs_16 in
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_16)%a ->

    (pc_a ^+ 10 + -36)%a = Some (pc_a ^+ -26)%a ->

    (b_stk <= a_stk)%a ->
    (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ->

    PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e pc_a ∗
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
    codefrag pc_a switcher_instrs_16 ∗
    ▷ (∀ rcgp rcra rcs0 rcs1,
        ⌜load_heap_in_world W wcgp rcgp ∧
          load_heap_in_world W wcra rcra ∧
          load_heap_in_world W wcs0 rcs0 ∧
          load_heap_in_world W wcs1 rcs1⌝ -∗
        ( world_interp W C ∗
             PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ -26)%a ∗
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
    codefrag pc_a switcher_instrs_16 ∗
             £ 1 -∗
             WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
           )
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_16 len_switcher_16; subst switcher_instrs_16 len_switcher_16.
    iIntros (Hstk_shadow Hsub_reg Hpca_next Hbstk Hbstk')
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0] & [%wca1 Hca1]
      & Hcsp & Hastk0 & Hastk1 & Hastk2 & Hastk3 & Hworld & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 3)%a ) ; solve_addr. }
    (* Load cgp csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iEval (rewrite open_world_interp_empty) in "Hworld".
    iApply (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ (pc_a ^+ 2)%a cgp csp
      _ _ _ _ _ _
      with "[$HPC $Hi $Hcgp $Hcsp $Hastk3 $Hworld]");
      [reflexivity| |solve_pure|solve_pure|rewrite /withinBounds; solve_addr|solve_addr|discriminate|discriminate|].
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    iNext. iIntros (rcgp) "(%Hrcgp & HPC & Hi & Hcgp & Hcsp & Hastk3 & Hworld)".
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 2)%a ) ; solve_addr. }
    (* Load cra csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ (pc_a ^+ 4)%a cra csp
      _ _ _ _ _ _
      with "[$HPC $Hi $Hcra $Hcsp $Hastk2 $Hworld]");
      [reflexivity| |solve_pure|solve_pure|rewrite /withinBounds; solve_addr|solve_addr|discriminate|discriminate|].
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    iNext. iIntros (rcra) "(%Hrcra & HPC & Hi & Hcra & Hcsp & Hastk2 & Hworld)".
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 1)%a ) ; solve_addr. }
    (* Load cs1 csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ (pc_a ^+ 6)%a cs1 csp
      _ _ _ _ _ _
      with "[$HPC $Hi $Hcs1 $Hcsp $Hastk1 $Hworld]");
      [reflexivity| |solve_pure|solve_pure|rewrite /withinBounds; solve_addr|solve_addr|discriminate|discriminate|].
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    iNext. iIntros (rcs1) "(%Hrcs1 & HPC & Hi & Hcs1 & Hcsp & Hastk1 & Hworld)".
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some a_stk ) ; solve_addr. }
    (* Load cs0 csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ (pc_a ^+ 8)%a cs0 csp
      _ _ _ _ _ _
      with "[$HPC $Hi $Hcs0 $Hcsp $Hastk0 $Hworld]");
      [reflexivity| |solve_pure|solve_pure|rewrite /withinBounds; solve_addr|solve_addr|discriminate|discriminate|].
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    iNext. iIntros (rcs0) "(%Hrcs0 & HPC & Hi & Hcs0 & Hcsp & Hastk0 & Hworld)".
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Mov ca0 (inl (-141)%Z); *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull))as [|_]; first done.
    (* Mov ca1 (inl 0%Z); *)
    iInstr "Hcode" with "Hlc".
    (* Jmp (inl (-36)%Z) *)
    iInstr "Hcode".

    iEval (rewrite -open_world_interp_empty) in "Hworld".
    iSpecialize ("Hpost" $! rcgp rcra rcs0 rcs1 with "[%]"); first done.
    iApply "Hpost". iFrame.
  Qed.

  (** Block 16, then blocks 14-15: the trusted stack is exhausted. Restore
      the callee-save registers, clear the registers and jump back to the
      caller with the error code [ENOTENOUGHTRUSTEDSTACK]. Each restored
      register is the result of a load, which may clear the tag of a saved
      heap capability. *)
  Lemma switcher_call_blocks_5_spec
    (b e a : Addr) (wcs0 wcs1 wcra wcgp : LWord) (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ᵣ switcher_block_pc 16 ∗
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
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        PC ↦ᵣ lupdatePcPerm rcra ∗
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
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
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
      [done|done|offsets_compute; solve_addr|done|done|].
    iNext.
    iIntros (rcgp rcra rcs0 rcs1 Hrestored)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Blocks 14-15: clear the registers and jump to the caller *)
    switcher_change_pc (switcher_block_offset 14).
    iApply (switcher_blocks_14_15_spec with "[- $HPC $Hcra $Hrmap]"); first done.
    iSplitL "Hcode"; first iFrame "Hcode".
    iNext; iIntros (rmap') "(%Hrmap' & HPC & Hcra & Hrmap & Hcode & Hlc')".
    iCombine "Hlc Hlc'" as "Hlc".
    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1); iFrame "∗ %".
  Qed.

  (** Variant of [switcher_call_blocks_5_spec] in a world [W]: each
      restored register retains its authority in [W]. *)
  Lemma switcher_call_blocks_5_world_spec
    (W : WORLD) (C : CmptName)
    (b e a : Addr) (wcs0 wcs1 wcra wcgp : LWord) (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ᵣ switcher_block_pc 16 ∗
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
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        world_interp W C ∗
        PC ↦ᵣ lupdatePcPerm rcra ∗
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
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hworld & Hrmap & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".

    (* Block 16: restore the callee-save registers *)
    switcher_focus_block 16 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_16_world_spec W C with
      "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hworld $Hcode]");
      [done|done|offsets_compute; solve_addr|done|done|].
    iNext.
    iIntros (rcgp rcra rcs0 rcs1 Hrestored)
      "(Hworld & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Blocks 14-15: clear the registers and jump to the caller *)
    switcher_change_pc (switcher_block_offset 14).
    iApply (switcher_blocks_14_15_spec with "[- $HPC $Hcra $Hrmap]"); first done.
    iSplitL "Hcode"; first iFrame "Hcode".
    iNext; iIntros (rmap') "(%Hrmap' & HPC & Hcra & Hrmap & Hcode & Hlc')".
    iCombine "Hlc Hlc'" as "Hlc".
    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1); iFrame "∗ %".
  Qed.

End Switcher_Call_Blocks_5.
