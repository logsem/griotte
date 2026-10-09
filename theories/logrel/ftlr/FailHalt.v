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
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  (** The [Fail] and [Halt] cases of the FTLR. *)
  Lemma fail_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P:V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w Fail ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".
    iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
    iNext. iIntros "[HPC Ha] /=".
    iApply wp_pure_step_later; auto; iNext ; iIntros "_".
    iApply wp_value.
    iIntros (Hcontr); inversion Hcontr.
  Qed.

  Lemma halt_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P:V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w Halt ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".
    iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
    iNext. iIntros "[HPC Ha] /=".
    assert ( ∀ Wv : WORLD * CmptName * Word, Persistent (safeC P Wv) ) as Hperscond_safeP.
    { rewrite /persistent_cond in Hpers; apply _. }
    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }
    iApply wp_pure_step_later; auto; iNext ; iIntros "_".
    iApply wp_value; auto.
  Qed.

End fundamental.
