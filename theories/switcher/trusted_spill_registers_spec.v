From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher.

(** * Spill and reload of registers to the register save area

    The specifications of the macros [trusted_spill_registers_asm] and
    [trusted_reload_registers_asm] (CHERIoT's [trustedSpillRegisters] and
    [trustedReloadRegisters]), for any trusted stack: [csp] holds a
    capability to it, and the cells of the registers, at their offsets
    [TrustedStack_offset_reg], are in its bounds. *)

Section TrustedSpillRegisters.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (** The cells of the registers [regs] in the register save area at [a],
      in its bounds [b, e) and outside the shadow table. *)
  Definition trusted_save_cells_ok (b e a : Addr) (regs : list RegName) : Prop :=
    ∀ r, r ∈ regs →
         (a + TrustedStack_offset_reg r)%a = Some (a ^+ TrustedStack_offset_reg r)%a ∧
         withinBounds b e (a ^+ TrustedStack_offset_reg r)%a = true ∧
         is_shadow_address (a ^+ TrustedStack_offset_reg r)%a = false.

  Lemma trusted_spill_registers_instrs_length regs :
    length (trusted_spill_registers_instrs regs) = length regs.
  Proof.
    by rewrite /trusted_spill_registers_instrs /encodeInstrsW length_map
      /trusted_spill_registers length_fmap.
  Qed.

  Lemma trusted_reload_registers_instrs_length regs :
    length (trusted_reload_registers_instrs regs) = length regs.
  Proof.
    by rewrite /trusted_reload_registers_instrs /encodeInstrsW length_map
      /trusted_reload_registers length_fmap.
  Qed.

  Lemma trusted_spill_registers_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (g : Locality) (b e a : Addr)
    (regs : list RegName) (wregs wold : list LWord) φ :
    regs ≠ [] ->
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (trusted_spill_registers_instrs regs))%a ->
    trusted_save_cells_ok b e a regs ->
    csp ∉ regs ->
    cnull ∉ regs ->

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    csp ↦ᵣ WCap true RWL g b e a ∗
    ([∗ list] r;w ∈ regs;wregs, r ↦ᵣ w) ∗
    ([∗ list] r;w ∈ regs;wold, (a ^+ TrustedStack_offset_reg r)%a ↦ₐ w) ∗
    codefrag_pers pc_a (trusted_spill_registers_instrs regs) ∗
    ▷ ( PC ↦ₚ WCap true pc_p pc_g pc_b pc_e
            (pc_a ^+ length (trusted_spill_registers_instrs regs))%a ∗
        csp ↦ᵣ WCap true RWL g b e a ∗
        ([∗ list] r;w ∈ regs;wregs, r ↦ᵣ w) ∗
        ([∗ list] r;w ∈ regs;wregs, (a ^+ TrustedStack_offset_reg r)%a ↦ₐ w) ∗
        codefrag_pers pc_a (trusted_spill_registers_instrs regs) -∗
        WP Seq (Instr Executable) {{ φ }} )
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hne Hx Hbounds Hcells Hcsp Hcnull)
      "(HPC & Hcsp & Hregs & Hcells & #Hcode & Hpost)".
    iInduction regs as [|r regs] "IH" forall (pc_a wregs wold Hne Hbounds Hcells Hcsp Hcnull).
    { done. }
    iDestruct (big_sepL2_cons_inv_l with "Hregs") as (wr wregs' ->) "[Hr Hregs]".
    iDestruct (big_sepL2_cons_inv_l with "Hcells") as (wc wold' ->) "[Hc Hcells]".
    destruct (Hcells r ltac:(set_solver)) as (Hr_addr & Hr_bounds & Hr_shadow).
    assert (r ≠ csp) as Hr_csp by set_solver.
    assert (r ≠ cnull) as Hr_cnull by set_solver.
    iDestruct (codefrag_contiguous_region_pers with "Hcode") as %[pc_end Hpc_end].
    rewrite trusted_spill_registers_instrs_length /= in Hpc_end.
    assert ((pc_a + 1)%a = Some (pc_a ^+ 1)%a) as Hpc_a1 by solve_addr.
    codefrag_facts "Hcode".
    iAssert (codefrag_pers (pc_a ^+ 1)%a (trusted_spill_registers_instrs regs))%I as "#Hcode'".
    { iDestruct (codefrag_app_pers _ [_] with "Hcode") as "[_ $]". }
    iEval (rewrite /trusted_spill_registers_instrs /trusted_spill_registers) in "Hcode".
    (* Store csp r (TrustedStack_offset_reg r) *)
    iInstr "Hcode".
    rewrite lstore_word_isWL //.
    destruct (decide (regs = [])) as [-> | Hne'].
    { iDestruct (big_sepL2_nil_inv_l with "Hregs") as %->.
      iDestruct (big_sepL2_nil_inv_l with "Hcells") as %->.
      iApply "Hpost".
      rewrite (_ : (pc_a ^+ length (trusted_spill_registers_instrs [r]))%a = (pc_a ^+ 1)%a); last by rewrite trusted_spill_registers_instrs_length.
      iFrame "∗ #". }
    iApply ("IH" with "[] [] [] [] [] Hcode' HPC Hcsp Hregs Hcells [Hr Hc Hpost]").
    { done. }
    { iPureIntro. revert Hbounds.
      rewrite /trusted_spill_registers_instrs
        /trusted_spill_registers /encodeInstrsW
        !length_map !length_fmap /=.
      solve_addr. }
    { iPureIntro. intros r' Hr'. apply Hcells. set_solver. }
    { iPureIntro. set_solver. }
    { iPureIntro. set_solver. }
    iNext; iIntros "(HPC & Hcsp & Hregs & Hcells & _)".
    iApply "Hpost". iFrame "∗ #".
    rewrite (_ : ((pc_a ^+ 1) ^+ length (trusted_spill_registers_instrs regs))%a = (pc_a ^+ length (trusted_spill_registers_instrs (r :: regs)))%a);
      first iFrame.
    rewrite !trusted_spill_registers_instrs_length. cbn [length]. solve_addr.
  Qed.

  Lemma trusted_reload_registers_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (g : Locality) (b e a : Addr)
    (regs : list RegName) (wregs wsaved : list LWord) φ :
    regs ≠ [] ->
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (trusted_reload_registers_instrs regs))%a ->
    trusted_save_cells_ok b e a regs ->
    csp ∉ regs ->
    cnull ∉ regs ->

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    csp ↦ᵣ WCap true RWL g b e a ∗
    ([∗ list] r;w ∈ regs;wregs, r ↦ᵣ w) ∗
    ([∗ list] r;w ∈ regs;wsaved, (a ^+ TrustedStack_offset_reg r)%a ↦ₐ w) ∗
    codefrag_pers pc_a (trusted_reload_registers_instrs regs) ∗
    ▷ ( PC ↦ₚ WCap true pc_p pc_g pc_b pc_e
            (pc_a ^+ length (trusted_reload_registers_instrs regs))%a ∗
        csp ↦ᵣ WCap true RWL g b e a ∗
        ([∗ list] r;w ∈ regs;wsaved, r ↦ᵣ w) ∗
        ([∗ list] r;w ∈ regs;wsaved, (a ^+ TrustedStack_offset_reg r)%a ↦ₐ w) ∗
        codefrag_pers pc_a (trusted_reload_registers_instrs regs) -∗
        WP Seq (Instr Executable) {{ φ }} )
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hne Hx Hbounds Hcells Hcsp Hcnull)
      "(HPC & Hcsp & Hregs & Hcells & #Hcode & Hpost)".
    iInduction regs as [|r regs] "IH" forall (pc_a wregs wsaved Hne Hbounds Hcells Hcsp Hcnull).
    { done. }
    iDestruct (big_sepL2_cons_inv_l with "Hregs") as (wr wregs' ->) "[Hr Hregs]".
    iDestruct (big_sepL2_cons_inv_l with "Hcells") as (wc wsaved' ->) "[Hc Hcells]".
    destruct (Hcells r ltac:(set_solver)) as (Hr_addr & Hr_bounds & Hr_shadow).
    assert (r ≠ csp) as Hr_csp by set_solver.
    assert (r ≠ cnull) as Hr_cnull by set_solver.
    iDestruct (codefrag_contiguous_region_pers with "Hcode") as %[pc_end Hpc_end].
    rewrite trusted_reload_registers_instrs_length /= in Hpc_end.
    assert ((pc_a + 1)%a = Some (pc_a ^+ 1)%a) as Hpc_a1 by solve_addr.
    codefrag_facts "Hcode".
    iAssert (codefrag_pers (pc_a ^+ 1)%a (trusted_reload_registers_instrs regs))%I as "#Hcode'".
    { iDestruct (codefrag_app_pers _ [_] with "Hcode") as "[_ $]". }
    iEval (rewrite /trusted_reload_registers_instrs /trusted_reload_registers) in "Hcode".
    (* The saved words may be heap capabilities: they are loaded exactly *)
    iAssert (load_witness_res LoadPlain) as "Hwit"; first done.
    (* CLoad r csp (TrustedStack_offset_reg r) *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ r csp (TrustedStack_offset_reg r))
      with "[$HPC $Hr $Hcsp $Hc $Hwit]" as (wload) "(%Hload & HPC & Hr & Hcsp & Hc & _)".
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst wload.
    destruct (decide (regs = [])) as [-> | Hne'].
    { iDestruct (big_sepL2_nil_inv_l with "Hregs") as %->.
      iDestruct (big_sepL2_nil_inv_l with "Hcells") as %->.
      iApply "Hpost".
      rewrite (_ : (pc_a ^+ length (trusted_reload_registers_instrs [r]))%a = (pc_a ^+ 1)%a); last by rewrite trusted_reload_registers_instrs_length.
      iFrame "∗ #". }
    iApply ("IH" with "[] [] [] [] [] Hcode' HPC Hcsp Hregs Hcells [Hr Hc Hpost]").
    { done. }
    { iPureIntro. revert Hbounds.
      rewrite /trusted_spill_registers_instrs /trusted_reload_registers_instrs
        /trusted_spill_registers /trusted_reload_registers /encodeInstrsW
        !length_map !length_fmap /=.
      solve_addr. }
    { iPureIntro. intros r' Hr'. apply Hcells. set_solver. }
    { iPureIntro. set_solver. }
    { iPureIntro. set_solver. }
    iNext; iIntros "(HPC & Hcsp & Hregs & Hcells & _)".
    iApply "Hpost". iFrame "∗ #".
    rewrite (_ : ((pc_a ^+ 1) ^+ length (trusted_reload_registers_instrs regs))%a = (pc_a ^+ length (trusted_reload_registers_instrs (r :: regs)))%a);
      first iFrame.
    rewrite !trusted_reload_registers_instrs_length. cbn [length]. solve_addr.
  Qed.

End TrustedSpillRegisters.
