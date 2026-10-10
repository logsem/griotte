From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary.
Import uPred.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types interp : (V).

  (** The [Fail] and [Halt] cases of the FTLR. *)
  Lemma fail_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w Fail ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & _ & _) _ ]".
    iDestruct (big_sepM_insert_delete with "Hmap") as "[HPC _]".
    iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
    iNext. iIntros "[HPC Ha] /=".
    ftlr_impl_fail.
  Qed.

  Lemma halt_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w Halt ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & >Hsa & Hinterp) WorldRes ]".
    iDestruct (big_sepM_insert_delete with "Hmap") as "[HPC _]".
    iDestruct (big_sepM_insert_delete with "Hsmap") as "[HsPC _]".
    iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
    iNext. iIntros "[HPC Ha] /=".
    iMod (step_halt with "[$Hspec $Hj $HsPC $Hsa]") as "(Hj & HsPC & Hsa)"; eauto.
    assert ( ∀ Wv : WORLD * CmptName * (Word * Word), Persistent (safeC P Wv) ) as Hperscond_safeP.
    { rewrite /persistent_cond in Hpers; apply _. }
    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }
    iApply wp_pure_step_later; auto; iNext ; iIntros "_".
    iApply wp_value; iIntros "_"; iFrame.
  Qed.

End fundamental.
