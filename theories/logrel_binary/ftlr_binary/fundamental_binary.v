From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Export
  ftlr_base_binary
  Jmp_binary Jnz_binary Jalr_binary Mov_binary Load_binary Store_binary BinOp_binary Restrict_binary
  Subseg_binary Get_binary Lea_binary Seal_binary UnSeal_binary ReadSR_binary WriteSR_binary.
From griotte Require Import rules_binary.
From griotte Require Import register_tactics.

(** * Fundamental theorem of the binary logical relation

    Related words are safe to execute: if the implementation run starts from
    [w1] and the specification run from [w2], with related register files,
    then whenever the implementation halts, the specification can halt too. *)
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

  (** The implementation run fails on an incorrect PC: the postcondition holds trivially. *)
  Lemma interp_conf_notCorrectPC W C (regs : Reg) (wpc : Word) :
    ¬ isCorrectPC wpc →
    registers_pointsto (<[PC:=wpc]> regs) -∗
    interp_conf W C.
  Proof.
    iIntros (Hnpc) "Hmreg".
    rewrite /interp_conf /registers_pointsto.
    iApply (wp_bind (fill [SeqCtx])).
    iDestruct (big_sepM_insert_delete with "Hmreg") as "[HPC _]".
    iApply (wp_notCorrectPC with "HPC"); first done.
    iNext. iIntros "HPC /=".
    iApply wp_pure_step_later; auto.
    iNext ; iIntros "_".
    iApply wp_value.
    iIntros (Hcontr); inversion Hcontr.
  Qed.

  Theorem fundamental_cap
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality)
    (b e a : Addr) :
    ⊢ interp W C (WCap p g b e a, WCap p g b e a) →
      interp_expression W C (WCap p g b e a, WCap p g b e a).
  Proof.
    iIntros "#Hinv_interp".
    iIntros (stk Ws Cs regs1 regs2)
      "(#Hspec & Hreg & Hmreg & Hsmreg & Hj & Hworld_interp & Hcont & Hown & Hframe & Hframe_spec & %Hframe)".
    cbn [fst snd].
    assert ( readAllowed p = true \/ readAllowed p = false )
      as [Hread_p|Hread_p] by (destruct_perm p ; naive_solver)
    ; cycle 1.
    { (* if p not readable, then execution will fail *)
      apply notreadAllowed_is_notexecuteAllowed in Hread_p.
      iApply (interp_conf_notCorrectPC with "Hmreg").
      intro Hcontra ; destruct p ; inv Hcontra; congruence.
    }
    clear Hread_p.

    iRevert "Hinv_interp".
    iLöb as "IH'" forall (W C regs1 regs2 p g b e a stk Ws Cs Hframe).
    iAssert ftlr_IH as "IH" ; [|iClear "IH'"].
    { iModIntro; iNext.
      iIntros (W_ih C_ih stk_ih Ws_ih Cs_ih r1_ih r2_ih p_ih g_ih b_ih e_ih a_ih)
        "#Hspec' #Hreg' Hmreg Hsmreg Hj Hworld_interp Hcont %Hframe' Hown Htframe Htframe_spec #Hinterp".
      iApply ("IH'" with "[%] Hreg' Hmreg Hsmreg Hj Hworld_interp Hcont Hown Htframe Htframe_spec Hinterp"); eauto.
    }
    iIntros "#Hinv_interp".
    iDestruct "Hreg" as "#Hreg".
    rewrite /interp_conf.
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (WCap p g b e a))) as [HcorrectPC|] ; cycle 1.
    { (* Not correct PC *)
      rewrite /registers_pointsto.
      iExtract "Hmreg" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); eauto.
      iNext. iIntros "HPC /=".
      iApply wp_pure_step_later; auto.
      iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    }

    (* Correct PC *)
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }

    iAssert (⌜ validPCperm p g ⌝)%I as "%Hp".
    { (* if not, contradiction by correctPC or validity *)
      inv HcorrectPC; subst; auto.
      iSplit; first done.
      iIntros (Hpwl).
      destruct p ; cbn in Hpwl ; try congruence.
      destruct w ; cbn in Hpwl ; try congruence.
      destruct g; last done.
      (* Contradiction -- WL and Global are not safe *)
      rewrite fixpoint_interp1_eq interp1_eq.
      replace (isO (BPerm rx WL _ _)) with false by (cbn; destruct rx; done).
      cbn.
      destruct rx; auto.
      iDestruct "Hinv_interp" as "[_ Hcontra]"; done.
    }

    iPoseProof "Hinv_interp" as "#Hinv".
    iEval (rewrite !fixpoint_interp1_eq interp1_eq) in "Hinv".
    destruct (isO p) eqn: HnO.
    { destruct Hp as [Hexec _].
      eapply executeAllowed_nonO in Hexec; congruence.
    }
    destruct (has_sreg_access p) eqn:HpXRS; first done.

    iDestruct "Hinv" as "[#Hinv %Hpwl_cond]".

    iDestruct (extract_from_region_inv _ _ a with "Hinv") as "H";auto.

    assert (readAllowed p = true) as Hra.
    {
      destruct Hp as [Hexec _]
      ; by eapply executeAllowed_is_readAllowed.
    }
    iDestruct (interp_in_registers with "[Hreg] [H]")
      as (p'' P'' Hflp'' Hperscond_P'') "(Hrela & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a)"
    ;eauto ; iClear "Hinv".
    assert (∃ (ρ : region_type), (std W) !! a = Some ρ ∧ ρ ≠ Revoked)
      as [ρ [Hρ Hne ] ].
    { destruct (isWL p),g; simplify_eq ; eauto.
      destruct Hstate_a as [Htemp | Hperm];eauto. }

    iDestruct (open_world_interp with "[$Hrela] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].
    destruct w as [w1 w2].

    (* The instruction is the same in both runs, unless the implementation fails *)
    iAssert (▷ rcond P'' C p'' interp)%I as "#HrcondP".
    { rewrite decide_True; first done.
      exists PC, (WCap p g b e a); split; first by simplify_map_eq.
      split; first done.
      cbn; split; [solve_addr | done]. }
    iDestruct "WorldRes" as "(HpO & Ha & Hsa & HP & HmonoV)".
    assert (Persistent (P'' W C (w1, w2))) as HpersP by apply (Hperscond_P'' (W,C,(w1,w2))).
    iDestruct "HP" as "#HP".
    iAssert (▷ ⌜decodeInstrW w1 ≠ Fail → w1 = w2⌝)%I as ">%Hdec".
    { iNext.
      iDestruct ("HrcondP" $! W (w1,w2) with "HP") as "Hl".
      iDestruct (interp_eq_unless_sealed with "Hl") as %Hl.
      iPureIntro; intros; by eapply load_word_decode_eq. }
    iAssert (▷ WorldRes W C a p'' (safeC P'') (w1, w2) ρ)%I
      with "[HpO Ha Hsa HmonoV]" as "WorldRes".
    { iNext; iFrame "∗#". }
    iClear "HrcondP".

    rewrite /registers_pointsto /spec_registers_pointsto.
    destruct (decide (decodeInstrW w1 = Fail)) as [Hfail|Hnfail].
    { (* Fail *)
      iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & _ & _) _ ]".
      iExtract "Hmreg" PC as "HPC".
      iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto; iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    }
    specialize (Hdec Hnfail); subst w2.

    destruct (decodeInstrW w1) eqn:Hi. (* proof by cases on each instruction *)
    + (* Jmp *)
      iApply (jmp_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Jnz *)
      iApply (jnz_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Jalr *)
      iApply (jalr_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Mov *)
      iApply (mov_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Load *)
      iApply (load_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Store *)
      iApply (store_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Lt *)
      iApply (binop_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto; naive_solver.
    + (* Add *)
      iApply (binop_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto; naive_solver.
    + (* Sub *)
      iApply (binop_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto; naive_solver.
    + (* Mul *)
      iApply (binop_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto; naive_solver.
    + (* LAnd *)
      iApply (binop_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto; naive_solver.
    + (* LOr *)
      iApply (binop_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto; naive_solver.
    + (* LShiftL *)
      iApply (binop_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto; naive_solver.
    + (* LShiftR *)
      iApply (binop_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto; naive_solver.
    + (* Lea *)
      iApply (lea_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Restrict *)
      iApply (restrict_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Subseg *)
      iApply (subseg_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* GetB *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GetB _ _) with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* GetE *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GetE _ _) with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* GetA *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GetA _ _) with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* GetP *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GetP _ _) with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* GetL *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GetL _ _) with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* GetWType *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GetWType _ _) with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* GetOType *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GetOType _ _) with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Seal *)
      iApply (seal_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* UnSeal *)
      iApply (unseal_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* ReadSR *)
      iApply (readsr_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* WriteSR *)
      iApply (writesr_case with
               "[$IH] [$Hspec] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe] [$Hframe_spec]
               [$Hstate] [$Hj] [$Hmreg] [$Hsmreg]")
      ;eauto.
    + (* Fail *)
      done.
    + (* Halt *)
      iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & >Hsa & Hinterp) WorldRes ]".
      iExtract "Hmreg" PC as "HPC".
      iDestruct (big_sepM_insert_delete with "Hsmreg") as "[HsPC Hsmreg]".
      iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iMod (step_halt with "[$Hspec $Hj $HsPC $Hsa]") as "(Hj & HsPC & Hsa)"; eauto.
      assert ( ∀ Wv : WORLD * CmptName * (Word * Word), Persistent (safeC P'' Wv) ) as Hperscond_safeP''.
      { rewrite /persistent_cond in Hperscond_P''; apply _. }
      iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hrela WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }
      iApply wp_pure_step_later; auto; iNext ; iIntros "_".
      iApply wp_value; iIntros "_"; iFrame.
  Qed.

  Theorem fundamental W C (ww : Word * Word) :
    ⊢ interp W C ww -∗ interp_expression W C ww.
  Proof.
    iIntros "#Hw"; destruct ww as [w1 w2].
    iDestruct (interp_eq_unless_sealed with "Hw") as %[<-|(o & sb1 & sb2 & -> & ->)].
    - destruct w1 as [| [c | ] | | ].
      2: { destruct c; iApply fundamental_cap; done. }
      all: iIntros (?????) "(_ & _ & Hmreg & _)".
      all: iApply (interp_conf_notCorrectPC with "Hmreg"); by inversion 1.
    - iIntros (?????) "(_ & _ & Hmreg & _)".
      iApply (interp_conf_notCorrectPC with "Hmreg"); by inversion 1.
  Qed.

  (* The fundamental theorem implies the exec_cond *)
  Lemma interp_exec_cond W C p g b e a:
    executeAllowed p = true ->
    ⊢ interp W C (WCap p g b e a, WCap p g b e a) -∗ exec_cond W C p g b e interp.
  Proof.
    iIntros (Hp) "#Hw".
    iIntros (a0 W' Hin) "#Hfuture". iModIntro.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    destruct g.
    - iDestruct (interp_monotone_nl with "Hfuture [] Hw") as "Hw'";[auto|].
      iApply (fundamental W');eauto.
      iApply interp_weakeningEO; eauto; try done.
    - iDestruct (interp_monotone with "Hfuture Hw") as "Hw'".
      iApply (fundamental W');eauto.
      iApply interp_weakeningEO; eauto; try done.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)
  Lemma exec_wp W C p g b e a :
    isCorrectPC (WCap p g b e a) ->
    ⊢ exec_cond W C p g b e interp -∗
    ∀ W', future_world g W W' →
          ▷ (interp_expr interp (interp_cont interp) W' C (WCap p g b e a, WCap p g b e a)).
  Proof.
    iIntros (Hvpc) "Hexec".
    rewrite /exec_cond /enter_cond.
    iIntros (W'). rewrite /future_world.
    assert (a ∈ₐ[[b,e]])%I as Hin.
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    destruct g.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a W' Hin Hrelated).
      iFrame.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a W' Hin Hrelated).
      iFrame.
  Qed.

  Lemma fundamental_ih :
    ⊢ ftlr_IH.
  Proof.
    iModIntro; iNext.
    iIntros (????????????) "???????????#Hv".
    iDestruct (fundamental with "Hv") as "Hcont".
    iApply "Hcont"; iFrame.
  Qed.

  (* updatePcPerm adds a later because of the case of E-capabilities, which
     unfold to ▷ interp_expr *)
  Lemma interp_updatePcPerm W C (w1 w2 : Word) :
    ⊢ interp W C (w1, w2) -∗ ▷ (interp_expression W C (updatePcPerm w1, updatePcPerm w2)).
  Proof.
    iIntros "#Hw".
    iDestruct (interp_eq_unless_sealed with "Hw") as %[<-|(o & sb1 & sb2 & -> & ->)]; cycle 1.
    { iNext; by iApply fundamental. }
    assert ( ( (∃ p g b e a, w1 = WSentry p g b e a))
            ∨ updatePcPerm w1 = w1)
      as [ Hw | ->].
    {
      destruct w1 as [ | [ | ] | | ]; eauto. unfold updatePcPerm.
      eauto; try naive_solver.
    }
    { destruct Hw as (p & g & b & e & a & ->).
      rewrite interp_diag_eq // /interp1_diag /=.
      iIntros (stk Ws Cs regs1 regs2).
      iSpecialize ("Hw" $! W (futureworld_refl g W) g (LocalityFlowsToReflexive g)).
      iNext.
      iIntros "H".
      iApply "Hw"; eauto.
    }
    { iNext; iApply fundamental; eauto. }
  Qed.

  Lemma jmp_or_fail_spec W C (w1 w2 : Word) φ :
    ⊢
    (interp W C (w1, w2)
     -∗ (if decide (isCorrectPC (updatePcPerm w1))
         then
           (∃ p g b e a,
               (⌜w1 = w2⌝
                ∗ ⌜w1 = WCap p g b e a ∨ w1 = WSentry p g b e a ⌝
                ∗ □ ∀ W', future_world g W W'
                          → ▷ (interp_expr interp (interp_cont interp) W' C)
                                (updatePcPerm w1, updatePcPerm w1)))
         else φ FailedV ∗ PC ↦ᵣ updatePcPerm w1
                          -∗ WP Seq (Instr Executable) {{ φ }} )).
  Proof.
    iIntros "#Hw".
    destruct (decide (isCorrectPC (updatePcPerm w1))).
    - iDestruct (interp_eq_unless_sealed with "Hw") as %[<-|(o & sb1 & sb2 & -> & ->)]
      ; last by inversion i.
      inversion i.
      destruct w1;inv H.
      + destruct p; cbn in * ; simplify_eq.
        iExists _,_,_,_,_.
        iSplit;[eauto|]. iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "[$Hw]") as "Hexec";[auto|].
        iApply exec_wp;auto.
      + destruct p0; cbn in * ; simplify_eq.
        iExists _,_,_,_,_.
        rewrite interp_diag_eq // /interp1_diag /=.
        iSplit;[eauto|]. iSplit;[eauto|]. iModIntro.
        iIntros (W') "Hfuture".
        iSpecialize ("Hw" with "Hfuture").
        iSpecialize ("Hw" $! g0 (LocalityFlowsToReflexive g0)).
        iExact "Hw".
    - iIntros "[Hfailed HPC]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC");eauto.
      iNext. iIntros "_". iApply wp_pure_step_later;auto.
      iNext; iIntros "_". iApply wp_value. iFrame.
  Qed.

End fundamental.
