From griotte Require Import rules.
From iris.proofmode Require Import proofmode.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (* A failed instruction rolls back every tentative write. The premise is
     about all extensions of the owned registers, so no absent register or
     memory cell can be mistaken for evidence of runtime failure. *)
  Lemma wp_instr_failed E pc_p pc_g pc_b pc_e pc_a w i (regs : Reg) :
    decodeInstrW w = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m, regs ⊆ r →
       exec i pc_p (r, sr, m) = (Failed, (r, sr, m))) →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hfailed φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[Hr Hsr] Hm] /=".
    destruct σ1 as [ [r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite (Hfailed r sr m Hregs) in Hstep.
    simplify_eq. cbn; iFrame. iApply "Hφ"; iFrame. done.
  Qed.


  Lemma wp_lea_invalidated_cap E pc_p pc_g pc_b pc_e pc_a
      w dst src regs regs' (t : bool) p g b e a n :
    decodeInstrW w = Lea dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Lea dst src) ⊆ dom regs →
    regs !!ᵣ dst = Some (WCap t p g b e a) →
    z_of_argument regs src = Some n →
    (a + n)%a = None →
    incrementPC (<[ dst := WCap false p g b e a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc Hover Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_lea with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq; try congruence.
    - iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; cbn in *; congruence.
  Qed.

  Lemma wp_lea_invalidated_sr E pc_p pc_g pc_b pc_e pc_a
      w dst src regs regs' (t : bool) p g b e a n :
    decodeInstrW w = Lea dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Lea dst src) ⊆ dom regs →
    regs !!ᵣ dst = Some (WSealRange t p g b e a) →
    z_of_argument regs src = Some n →
    (a + n)%ot = None →
    incrementPC (<[ dst := WSealRange false p g b e a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc Hover Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_lea with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq; try congruence.
    - iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; cbn in *; congruence.
  Qed.

  Lemma wp_subseg_invalidated_cap E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 a1 a2 :
    decodeInstrW w = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ᵣ dst = Some (WCap t p g b e a) →
    z_of_argument regs src1 = Some n1 →
    z_of_argument regs src2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = false →
    incrementPC (<[ dst := WCap false p g a1 a2 a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hn1 Hn2 Hwithin Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: repeat match goal with
    | H : context [_ && isWithin _ _ _ _] |- _ =>
      rewrite Hwithin andb_false_r in H
    end.
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_cap E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 :
    decodeInstrW w = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ᵣ dst = Some (WCap t p g b e a) →
    z_of_argument regs src1 = Some n1 →
    z_of_argument regs src2 = Some n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    incrementPC (<[ dst := WCap false p g b e a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hover Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try (destruct Hover; congruence).
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_sr E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 a1 a2 :
    decodeInstrW w = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ᵣ dst = Some (WSealRange t p g b e a) →
    z_of_argument regs src1 = Some n1 →
    z_of_argument regs src2 = Some n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    incrementPC (<[ dst := WSealRange false p g a1 a2 a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hn1 Hn2 Hwithin Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: repeat match goal with
    | H : context [_ && isWithin _ _ _ _] |- _ =>
      rewrite Hwithin andb_false_r in H
    end.
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_sr E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 :
    decodeInstrW w = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ᵣ dst = Some (WSealRange t p g b e a) →
    z_of_argument regs src1 = Some n1 →
    z_of_argument regs src2 = Some n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    incrementPC (<[ dst := WSealRange false p g b e a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hover Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try (destruct Hover; congruence).
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.
End instruction_outcomes.
