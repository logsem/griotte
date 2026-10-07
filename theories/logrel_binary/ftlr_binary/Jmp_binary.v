From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Jmp rules_Jmp_binary.
From griotte Require Import map_simpl register_tactics.

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

  Lemma jmp_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (rimm : Z + RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Jmp rimm) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_Jmp with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_Jmp with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ regs' imm Himm Hincr| ]; cycle 1.
    { ftlr_impl_fail. }

    (* The specification run takes the same jump *)
    iDestruct (interp_z_of_argument _ _ _ _ _ rimm with "Hinv_interp Hreg") as %Hz.
    rewrite Hz in Himm.
    destruct HSpec2 as [ regs2' imm2 Himm2 Hincr2 | Hfail ].
    2: { exfalso.
         destruct Hfail as [Hnone | imm2 Himm2 Hincr2]; simplify_eq.
         rewrite /incrementPC_gen !lookup_insert_eq in Hincr Hincr2.
         by case_match. }
    simplify_eq.

    incrementPC_inv as (p0&g0&b0&e0&a0&a0'&?&Ha0'&?); simplify_map_eq.
    incrementPC_inv as (p1&g1&b1&e1&a1&a1'&?&Ha1'&?); simplify_map_eq.
    rewrite !insert_insert_eq.
    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    iApply wp_pure_step_later; auto. iNext; iIntros "_".

    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply ("IH" $! _ _ _ _ _ regs1 regs2
             with "Hspec Hreg Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec") ; eauto.
    iApply (interp_weakening with "IH Hinv_interp"); eauto; try solve_addr; try reflexivity.
  Qed.

End fundamental.
