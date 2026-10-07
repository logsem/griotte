From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Lea rules_Lea_binary.
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

  Lemma lea_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
    (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Lea dst src) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_lea with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ p0 g0 b0 e0 a0 z a0' Hdst Hz Hoffset HincrPC
                      | p0 g0 b0 e0 a0 z a0' Hdst Hz Hoffset HincrPC | ]
    ; cycle 2.
    { ftlr_impl_fail. }

    (* The specification run performs the same update *)
    all: iDestruct (interp_reg_lookup_same with "Hinv_interp Hreg") as %Hdst2; [exact Hdst|done|].
    all: iDestruct (interp_z_of_argument _ _ _ _ _ src with "Hinv_interp Hreg") as %Hz2.
    all: rewrite Hz2 in Hz.
    all: apply incrementPC_Some_inv in HincrPC as (p2&g2&b2&e2&a2&a3&HPC&Ha2&->).
    1: eapply Lea_spec_determ in HSpec2 as [Hv2 Hregs2];
       last (eapply Lea_spec_success_cap; eauto; transfer_incrementPC HPC Ha2).
    2: eapply Lea_spec_determ in HSpec2 as [Hv2 Hregs2];
       last (eapply Lea_spec_success_sr; eauto; transfer_incrementPC HPC Ha2).
    all: specialize (Hregs2 eq_refl); subst retv2 regs2'.
    all: iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    all: iApply wp_pure_step_later; auto; iNext; iIntros "_".
    all: iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    all: iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    all: try (destruct ρ;auto;contradiction).

    (* The new PC is the old one, with another address *)
    all: assert (p2 = p ∧ g2 = g ∧ b2 = b ∧ e2 = e) as (-> & -> & -> & ->)
      by (rewrite /insert_reg in HPC; destruct (decide (PC = dst)); simplify_map_eq; auto).
    all: iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
             with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
    all: try (iApply (interp_next_PC with "Hinv_interp"); eauto).
    all: iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
    all: iIntros (HdstPC Hdstnull).
    all: iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "Hw"; [exact Hdst|exact Hdst2|].
    - iApply (interp_weakening with "IH Hw"); eauto; try solve_addr; try reflexivity.
    - iApply (interp_weakening_ot with "Hw"); eauto; try solve_addr; try reflexivity.
  Qed.

End fundamental.
