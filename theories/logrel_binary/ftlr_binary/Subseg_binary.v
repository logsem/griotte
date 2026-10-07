From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Subseg rules_Subseg_binary.
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

  Lemma subseg_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
    (ρ : region_type) (dst : RegName) (r1 r2 : Z + RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Subseg dst r1 r2) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_Subseg with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ p0 g0 b0 e0 a0 a1 a2 Hdst Hao1 Hao2 Hwi HincrPC
                      | p0 g0 b0 e0 a0 a1 a2 Hdst Hao1 Hao2 Hwi HincrPC
                      | ]
    ; cycle 2.
    { ftlr_impl_fail. }

    (* The specification run performs the same update *)
    all: iDestruct (interp_reg_lookup_same with "Hinv_interp Hreg") as %Hdst2; [exact Hdst|done|].
    all: iDestruct (interp_z_of_argument _ _ _ _ _ r1 with "Hinv_interp Hreg") as %Hz1.
    all: iDestruct (interp_z_of_argument _ _ _ _ _ r2 with "Hinv_interp Hreg") as %Hz2.
    all: rewrite /addr_of_argument /otype_of_argument Hz1 Hz2 in Hao1 Hao2.
    all: apply incrementPC_Some_inv in HincrPC as (p2&g2&b2&e2&a3&a4&HPC&Ha3&->).
    1: eapply Subseg_spec_determ in HSpec2 as [Hv2 Hregs2];
       last (eapply Subseg_spec_success_cap; eauto; transfer_incrementPC HPC Ha3).
    2: eapply Subseg_spec_determ in HSpec2 as [Hv2 Hregs2];
       last (eapply Subseg_spec_success_sr; eauto; transfer_incrementPC HPC Ha3).
    all: specialize (Hregs2 eq_refl); subst retv2 regs2'.
    all: iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    all: iApply wp_pure_step_later; auto; iNext; iIntros "_".
    all: iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    all: iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    all: try (destruct ρ;auto;contradiction).
    all: iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "#Hw"; [exact Hdst|exact Hdst2|].
    all: apply isWithin_implies in Hwi; destruct Hwi as [Hwi_b Hwi_e].

    - iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
               with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
      + iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
        iIntros (HdstPC Hdstnull).
        iApply (interp_weakening with "IH Hw"); eauto; try solve_addr; try reflexivity.
      + iModIntro.
        destruct (decide (dst = PC)) as [->|HdstPC].
        * rewrite /insert_reg in HPC; simplify_map_eq.
          iApply (interp_weakening with "IH Hinv_interp"); eauto; try solve_addr; try reflexivity.
        * rewrite insert_reg_lookup_PC // in HPC; simplify_map_eq.
          iApply (interp_next_PC with "Hinv_interp"); eauto.
    - assert (dst ≠ PC) as HdstPC.
      { intros ->; rewrite /insert_reg in HPC; simplify_map_eq. }
      rewrite insert_reg_lookup_PC // in HPC; simplify_map_eq.
      iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
               with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
      + iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
        iIntros (_ Hdstnull).
        iApply (interp_weakening_ot with "Hw"); eauto; try solve_addr; try reflexivity.
      + iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
