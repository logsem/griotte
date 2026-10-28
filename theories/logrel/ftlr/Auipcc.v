From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_Auipcc.
From griotte Require Import map_simpl register_tactics.
Import CoreWPNotations.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
    `{MP: MachineParameters}
    (trusted_fault : CSTK → LWord → LReg → iProp Σ)
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  (** The result of [auipcc] is the PC with another address (or its untagged
      version), so it is safe because the PC is. *)
  Lemma auipcc_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
    (ρ : region_type) (dst : RegName) (imm : Z) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr trusted_fault W C regs p p' g b e a w (Auipcc dst imm) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Auipcc (CL := link_core) with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [HincrPC Hregs' | HincrPC]; cycle 1.
    { subst regs'.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto. }

    apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
    injection HPC as <- <- <- <- <- <- <-.
    iNext.
    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp").
    - subst regs'. by apply full_map_linsert.
    - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (Hdst_null).
      rewrite /auipcc_word.
      destruct (a + imm)%a as [a'|]; last by iApply interp_untagged.
      iApply (interp_weakening with "IH Hinv_interp"); eauto; try solve_addr;
      try apply subseg_heap_base_same.
      + eapply PermFlowsToReflexive.
      + apply LocalityFlowsToReflexive.
    - iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
