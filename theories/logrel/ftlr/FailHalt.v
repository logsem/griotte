From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel.
From griotte Require Import ftlr_base.
Import CoreWPNotations.
Import uPred.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The [Fail] and [Halt] cases of the FTLR. *)
  Lemma fail_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P:V) :
    ftlr_instr W C regs p p' g b e a w Fail ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".
    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".
    iApply (wp_fail (CL := link_core) with "[$HPC $Ha]"); eauto.
    iNext. iIntros "[HPC Ha] /=".
    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ; auto; contradiction. }
    iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto.
  Qed.

  Lemma halt_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P:V) :
    ftlr_instr W C regs p p' g b e a w Halt ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".
    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".
    iApply (wp_halt (CL := link_core) with "[HPC Ha]"); eauto; iFrame.
    iNext. iIntros "[HPC Ha] /=".
    assert ( ∀ Wv : WORLD * CmptName * LWord, Persistent (safeC P Wv) ) as Hperscond_safeP.
    { rewrite /persistent_cond in Hpers; apply _. }
    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }
    iNext. iApply (ftlr_post_halt with "Hworld_interp").
  Qed.

End fundamental.
