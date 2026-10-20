From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel.
From griotte Require Import ftlr_base.
Import uPred.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The [Fail] and [Halt] cases of the FTLR. *)
  Lemma fail_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P:V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w Fail ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".
    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".
    iApply (wp_fail with "[$HPC $Ha]"); eauto.
    iNext. iIntros "[HPC Ha] /=".
    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ; auto; contradiction. }
    iApply (ftlr_trap with "Htrap HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.
  Qed.

  Lemma halt_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P:V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w Halt ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".
    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".
    iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
    iNext. iIntros "[HPC Ha] /=".
    assert ( ∀ Wv : WORLD * CmptName * LWord, Persistent (safeC P Wv) ) as Hperscond_safeP.
    { rewrite /persistent_cond in Hpers; apply _. }
    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }
    iApply wp_pure_step_later; auto; iNext ; iIntros "_".
    iApply wp_value; auto.
  Qed.

End fundamental.
