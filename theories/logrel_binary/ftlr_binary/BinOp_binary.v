From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_BinOp rules_BinOp_binary.
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

  Lemma binop_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg) (p p' : Perm)
    (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName)
    (r1 r2: Z + RegName) (P:V) (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr_base W C regs1 regs2 p p' g b e a w ρ P
      (decodeInstrW w = Add dst r1 r2 \/
       decodeInstrW w = Sub dst r1 r2 \/
       decodeInstrW w = Mul dst r1 r2 \/
       decodeInstrW w = LAnd dst r1 r2 \/
       decodeInstrW w = LOr dst r1 r2 \/
       decodeInstrW w = LShiftL dst r1 r2 \/
       decodeInstrW w = LShiftR dst r1 r2 \/
       decodeInstrW w = Lt dst r1 r2
      ) stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_BinOp with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_BinOp with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [n1 n2 Hn1 Hn2 Hincr | ]; cycle 1.
    { ftlr_impl_fail. }

    (* The operands are the same in both runs *)
    iDestruct (interp_z_of_argument _ _ _ _ _ r1 with "Hinv_interp Hreg") as %Hz1.
    iDestruct (interp_z_of_argument _ _ _ _ _ r2 with "Hinv_interp Hreg") as %Hz2.
    rewrite Hz1 in Hn1; rewrite Hz2 in Hn2.
    cbn [fst snd] in *.
    assert (dst <> PC) as HdstPC.
    { intros ->. rewrite /incrementPC /incrementPC_gen /insert_reg in Hincr; by simplify_map_eq. }
    destruct HSpec2 as [n1' n2' Hn1' Hn2' Hincr2 | Hfail].
    2: { exfalso.
         destruct Hfail as [Hn1' | Hn2' | n1' n2' Hn1' Hn2' Hincr2]; simplify_eq.
         eapply incrementPC_gen_PC_eq; [| exact Hincr | exact Hincr2].
         by rewrite !insert_reg_lookup_PC // !lookup_insert_eq. }
    simplify_eq.
    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    iApply wp_pure_step_later; auto; iNext; iIntros "_".
    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    incrementPC_inv; simplify_map_eq.
    incrementPC_inv; simplify_map_eq.
    iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
             with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec") ; eauto.
    - iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
      iIntros; iApply interp_int.
    - iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
