From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Get rules_Get_binary.
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

  (** Related words have the same observable properties. *)
  Lemma interp_denote W C (i : instr) (w1 w2 : Word) :
    interp W C (w1, w2) -∗ ⌜rules_Get.denote i w1 = rules_Get.denote i w2⌝.
  Proof.
    iIntros "Hw".
    iDestruct (interp_eq_unless_sealed with "Hw") as %[->|(o & sb1 & sb2 & -> & ->)]; first done.
    iPureIntro.
    destruct i; cbn; try done.
    f_equal.
    by pose proof (encodeWordType_correct (WSealed o sb1) (WSealed o sb2)).
  Qed.

  Lemma get_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst r : RegName) (ins: instr)
        (P:V) (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    is_Get ins dst r →
    ftlr_instr W C regs1 regs2 p p' g b e a w ins ρ P stk Ws Cs.
  Proof.
    intros Hinstr.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi;
    rewrite <- Hi in Hinstr; clear Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_Get with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_Get with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [w1 z Hw1 Hz Hincr | ]; cycle 1.
    { ftlr_impl_fail. }

    (* The specification run reads a related word, with the same denotation *)
    iDestruct (interp_reg_lookup_Some _ _ _ _ (WCap p g b e a) r with "Hreg") as %[w2 Hw2].
    iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "Hw"; [exact Hw1|exact Hw2|].
    iDestruct (interp_denote _ _ (decodeInstrW w) with "Hw") as %Hdenote.
    assert (dst <> PC) as HdstPC.
    { intros ->. rewrite /incrementPC /incrementPC_gen /insert_reg in Hincr; by simplify_map_eq. }
    destruct HSpec2 as [w2' z2 Hw2' Hz2 Hincr2 | Hfail].
    all: cbn [fst snd] in *.
    2: { exfalso.
         destruct Hfail as [w2' Hw2' Hz2 | w2' z2 Hw2' Hz2 Hincr2]
         ; rewrite Hw2 in Hw2'; simplify_eq; rewrite Hdenote in Hz; simplify_eq.
         eapply incrementPC_gen_PC_eq; [| exact Hincr | exact Hincr2].
         by rewrite !insert_reg_lookup_PC // !lookup_insert_eq. }
    rewrite Hw2 in Hw2'; simplify_eq.
    rewrite Hdenote in Hz; simplify_eq.
    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    iApply wp_pure_step_later; auto; iNext; iIntros "_".
    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    incrementPC_inv; simplify_map_eq.
    incrementPC_inv; simplify_map_eq.
    iApply ("IH" $! _ _ _ _ _ (<[dst:=WInt z2]ᵣ> _) (<[dst:=WInt z2]ᵣ> _)
             with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec") ; eauto.
    - iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
      iIntros; iApply interp_int.
    - iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
