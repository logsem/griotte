From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Mov rules_Mov_binary.
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

  Lemma mov_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Mov dst src) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_Mov with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [w1 Hw1 Hincr | ]; cycle 1.
    { ftlr_impl_fail. }

    (* The moved words are related *)
    destruct HSpec2 as [w2 Hw2 Hincr2 | w2 Hw2 Hincr2].
    2: { iDestruct (interp_word_of_argument with "Hinv_interp Hreg") as "Hw"; [exact Hw1|exact Hw2|].
         iDestruct (interp_eq_unless_sealed with "Hw") as %Hweq.
         exfalso.
         destruct (decide (dst = PC)) as [->|HdstPC].
         - destruct Hweq as [<-|(?&?&?&->&->)].
           + eapply incrementPC_gen_PC_eq; [| exact Hincr | exact Hincr2].
             by rewrite /insert_reg; simplify_map_eq.
           + by rewrite /incrementPC /incrementPC_gen /insert_reg in Hincr; simplify_map_eq.
         - eapply incrementPC_gen_PC_eq; [| exact Hincr | exact Hincr2].
           by rewrite !insert_reg_lookup_PC // !lookup_insert_eq. }
    iDestruct (interp_word_of_argument with "Hinv_interp Hreg") as "#Hw"; [exact Hw1|exact Hw2|].
    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    iApply wp_pure_step_later; auto; iNext; iIntros "_".
    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    destruct (decide (dst = PC)) as [->|HdstPC].
    { (* The PC is overwritten: the new PC is the same capability on both sides *)
      iDestruct (interp_eq_unless_sealed with "Hw") as %[<-|(?&?&?&->&->)]; cycle 1.
      { by rewrite /incrementPC /incrementPC_gen /insert_reg in Hincr; simplify_map_eq. }
      rewrite /insert_reg in Hincr Hincr2.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      incrementPC_inv as (p0&g0&b0&e0&a0&a0'&?&Ha0'&?); simplify_map_eq.
      rewrite !insert_insert_eq.
      destruct (executeAllowed p0) eqn:Hpft; cycle 1.
      { iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
        iNext; iIntros "HPC /=".
        ftlr_impl_fail.
      }
      iApply ("IH" $! _ _ _ _ _ regs1 regs2
               with "Hspec Hreg Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec") ; eauto.
      iApply (interp_weakening with "IH Hw"); eauto; try reflexivity; try solve_addr.
    }
    incrementPC_inv; simplify_map_eq.
    incrementPC_inv; simplify_map_eq.
    iApply ("IH" $! _ _ _ _ _ (<[dst:=w1]ᵣ> _) (<[dst:=w2]ᵣ> _)
             with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec") ; eauto.
    - iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
      by iIntros.
    - iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
