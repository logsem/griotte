From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Jnz rules_Jnz_binary.
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

  Lemma jnz_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (rimm : Z + RegName) (rcond : RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Jnz rimm rcond) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_Jnz with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ regs' wcond Hrcond Hnz Hincr | regs' imm wcond Hrcond Hnz Hrimm HincrPC | ]
    ; cycle 2.
    { ftlr_impl_fail. }

    (* The condition and the offset are the same in both runs *)
    all: iDestruct (interp_reg_lookup_Some _ _ _ _ (WCap p g b e a) rcond with "Hreg") as %[wcond2 Hrcond2].
    all: iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "Hcond"; [exact Hrcond|exact Hrcond2|].
    all: iDestruct (interp_nonZero with "Hcond") as %Hnz2.
    all: iDestruct (interp_z_of_argument _ _ _ _ _ rimm with "Hinv_interp Hreg") as %Hz.
    all: rewrite Hnz in Hnz2.
    - destruct HSpec2 as [ regs2' wcond2' Hrcond2' Hnz2' Hincr2
                         | regs2' imm2 wcond2' Hrcond2' Hnz2' Hrimm2 HincrPC2
                         | Hfail ].
      2: { rewrite Hrcond2 in Hrcond2'; simplify_eq; congruence. }
      2: { exfalso.
           destruct Hfail as [ wcond2' Hrcond2' Hnz2' Hincr2
                             | imm2 wcond2' Hrcond2' Hnz2' Hrimm2 HincrPC2
                             | wcond2' Hrcond2' Hnz2' Hrimm2 ]
           ; rewrite Hrcond2 in Hrcond2'; simplify_eq; try congruence.
           rewrite /incrementPC /incrementPC_gen !lookup_insert_eq in Hincr Hincr2.
           by case_match. }
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
      iApply (interp_next_PC with "Hinv_interp"); eauto.
    - rewrite Hz in Hrimm.
      destruct HSpec2 as [ regs2' wcond2' Hrcond2' Hnz2' Hincr2
                         | regs2' imm2 wcond2' Hrcond2' Hnz2' Hrimm2 HincrPC2
                         | Hfail ].
      1: { rewrite Hrcond2 in Hrcond2'; simplify_eq; congruence. }
      2: { exfalso.
           destruct Hfail as [ wcond2' Hrcond2' Hnz2' Hincr2
                             | imm2 wcond2' Hrcond2' Hnz2' Hrimm2 HincrPC2
                             | wcond2' Hrcond2' Hnz2' Hrimm2 ]
           ; rewrite Hrcond2 in Hrcond2'; simplify_eq; try congruence.
           rewrite /incrementPC_gen !lookup_insert_eq in HincrPC HincrPC2.
           by case_match. }
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
