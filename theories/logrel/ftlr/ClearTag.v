From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Export rules_ClearTag rules_base.
From griotte Require Import BinOp.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma cleartag_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
        (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
        (ρ : region_type) (dst src : RegName) (P:D)
        (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (ClearTag dst src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#Halloc #IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.
    iDestruct (WorldRes_acc with "WorldRes") as "[(Ha & Hinterp) WorldRes]".
    iApply (wp_ClearTag with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    - incrementPC_inv as (t0 & p0 & g0 & b0 & e0 & a0 & a0' & HPC0 & Ha0 & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /insert_reg /= lookup_insert in HPC0.
        injection HPC0 as Hclear.
        assert (t0 = false) as ->.
        { pose proof (get_tag_clear_tag w0) as Htag.
          rewrite Hclear in Htag. exact Htag. }
        map_simpl "Hmap".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        iApply wp_value; auto.
      + rewrite /insert_reg lookup_insert_ne in HPC0; last congruence.
        rewrite lookup_insert_eq in HPC0.
        injection HPC0 as <- <- <- <- <- <-.
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=clear_tag w0]ᵣ> (<[PC:=WCap true p g b e a]> regs)) p g b e a0'
          with "[Halloc] [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr. rewrite /insert_reg !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite /insert_reg lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull));
              [iApply interp_int | iApply interp_clear_tag]. }
          rewrite /insert_reg !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
