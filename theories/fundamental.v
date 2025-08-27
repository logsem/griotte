From cap_machine.ftlr Require Export Jmp. (* Jmp Jnz Jalr Mov Load Store BinOp Restrict *)
(*   Subseg Get Lea Seal UnSeal ReadSR WriteSR. *)
(* From cap_machine.ftlr Require Export JmpCap. *)
From cap_machine.ftlr Require Export ftlr_base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {tframeg : TFRAMEG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation STK := (leibnizO (list (Word * Word))).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Theorem fundamental_cap (W : WORLD) (C : CmptName) p g b e (a : Addr) (stk : STK) cstk :
    ⊢ interp W C (WCap p g b e a) →
      interp_expression stk W C (WCap p g b e a) cstk.
  Proof.
    iIntros "#Hinv_interp".
    iIntros (regs) "[[Hfull Hreg] [Hmreg [Hr [Hsts [Hcont [Hown Hframe]]]]]]".
    assert ( readAllowed p = true \/ readAllowed p = false )
      as [Hread_p|Hread_p] by (destruct_perm p ; naive_solver)
    ; cycle 1.
    { (* if p not readable, then execution will fail *)
      apply notreadAllowed_is_notexecuteAllowed in Hread_p.
      iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
      iApply (wp_bind (fill [SeqCtx])).
      rewrite /registers_pointsto.
      iExtract "Hmreg" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); eauto.
      intro Hcontra ; destruct p ; inv Hcontra; congruence.
      iNext. iIntros "HPC /=".
      iApply wp_pure_step_later; auto.
      iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    }
    clear Hread_p.

    iRevert "Hinv_interp".
    iLöb as "IH'" forall (W C regs p g b e a stk cstk).
    iAssert ftlr_IH as "IH" ; [|iClear "IH'"].
    { iModIntro; iNext.
      iIntros (W_ih C_ih stk_ih r_ih p_ig g_ih b_ih e_ih a_ih cstk_ih)
        "%Hfull #Hregs Hmreg Hr Hsts Htframe Hown Hinterp".
      iApply ("IH'" with "[%] [] [Hmreg] [$Hr] [$Hsts] [$] [$]");eauto.
    }
    iIntros "#Hinv_interp".
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
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
      replace (isO (BPerm _ WL _ _)) with false by (cbn; destruct rx; done).
      cbn.
      destruct rx; auto.
      iDestruct "Hinv_interp" as "[_ Hcontra]"; done.
    }

    iPoseProof "Hinv_interp" as "#Hinv".
    iEval (rewrite !fixpoint_interp1_eq interp1_eq) in "Hinv".
    destruct (isO p) eqn: HnO.
    { inv HcorrectPC; simplify_eq
      ; eapply executeAllowed_nonO in H6
      ; congruence.
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

    iDestruct (region_open W C a p'' with "[$Hrela $Hr $Hsts]")
      as (w) "(Hr & Hsts & Hstate & Ha & % & #HmonoV & Hw) /="; [ |apply Hρ|].
    { destruct ρ;auto;done. }
    pose proof (Hperscond_P'' (W,C,w)) as HpersP''
    ; iDestruct "Hw" as "#Hw".

    rewrite /registers_pointsto ; iExtract "Hmreg" PC as "HPC".
    destruct (decodeInstrW w) eqn:Hi. (* proof by cases on each instruction *)
    + (* Jmp *)
      iApply (jmp_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hcont] [$Hsts] [$Hown] [$Hframe]
               [$Hr] [$Hstate] [$Ha] [$HPC] [Hmreg]")
      ;eauto.
    + (* Jnz *)
      iApply (jnz_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Jalr *)
      iApply (jalr_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* JmpCap *)
      iApply (jmpcap_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Mov *)
      iApply (mov_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Load *)
      iApply (load_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Store *)
      iApply (store_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Lt *)
      iApply (binop_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto; naive_solver.
    + (* Add *)
      iApply (binop_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto; naive_solver.
    + (* Sub *)
      iApply (binop_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto; naive_solver.
    + (* Mul *)
      iApply (binop_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto; naive_solver.
    + (* LAnd *)
      iApply (binop_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto; naive_solver.
    + (* LOr *)
      iApply (binop_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto; naive_solver.
    + (* LShiftL *)
      iApply (binop_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto; naive_solver.
    + (* LShiftR *)
      iApply (binop_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto; naive_solver.
    + (* Lea *)
      iApply (lea_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Restrict *)
      iApply (restrict_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Subseg *)
      iApply (subseg_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* GetB *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetB _ _) with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* GetE *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetE _ _) with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* GetA *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetA _ _) with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* GetP *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetP _ _) with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* GetL *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetL _ _) with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* GetWType *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetWType _ _) with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* GetOType *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetOType _ _) with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Seal *)
      iApply (seal_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* UnSeal *)
      iApply (unseal_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* ReadSR *)
      iApply (readsr_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* WriteSR *)
      iApply (writesr_case with
               "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond]  [$HmonoR] [$HmonoV]
               [$Hw] [$Hsts] [$Htframe] [$Hown] [$Hr] [$Hstate]
               [$Ha] [$HPC] [$Hmreg]")
      ;eauto.
    + (* Fail *)
      iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto; iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    + (* Halt *)
      iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iDestruct (region_close _ _ _ _ _ _ ρ with "[$Hr $Ha $Hstate $HmonoV Hw]") as "Hr";[auto|iFrame "#"; auto|].
      { destruct ρ;auto; contradiction. }
      iApply wp_pure_step_later; auto; iNext ; iIntros "_".
      iApply wp_value; auto.
      Unshelve. rewrite /persistent_cond in Hperscond_P''; apply _.
  Qed.

  Theorem fundamental W C w regs :
    ⊢ interp W C w -∗ interp_expression regs W C w.
  Proof.
    iIntros "Hw". destruct w as [| [c | ] | | ].
    2: { iApply fundamental_cap. done. }
    all: iClear "Hw"; iIntros "(? & Hreg & ?)"; unfold interp_conf.
    all: iApply (wp_wand with "[-]"); [ | iIntros (?) "H"; iApply "H"].
    all: iApply (wp_bind (fill [SeqCtx])); cbn.
    all: unfold registers_pointsto; rewrite -insert_delete_insert.
    all: iDestruct (big_sepM_insert with "Hreg") as "[HPC ?]"; first by rewrite lookup_delete.
    all: iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
    all: iNext; iIntros; cbn; iApply wp_pure_step_later; auto.
    all: iNext; iIntros "_"; iApply wp_value; iIntros (?); congruence.
  Qed.

  (* The fundamental theorem implies the exec_cond *)
  Lemma interp_exec_cond W C p g b e a :
    executeAllowed p = true ->
    interp W C (WCap p g b e a) -∗ exec_cond W C p g b e interp.
  Proof.
    iIntros (Hp) "#Hw".
    iIntros (a0 r W' Hin) "#Hfuture". iModIntro.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    destruct g.
    - iDestruct (interp_monotone_nl with "Hfuture [] Hw") as "Hw'";[auto|].
      iApply fundamental;eauto.
      iApply interp_weakening.interp_weakeningEO; eauto; try done.
    - iDestruct (interp_monotone with "Hfuture Hw") as "Hw'".
      iApply fundamental;eauto.
      iApply interp_weakening.interp_weakeningEO; eauto; try done.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)

  Lemma exec_wp W C p g b e a :
    isCorrectPC (WCap p g b e a) ->
    exec_cond W C p g b e interp -∗
    ∀ r W', future_world g W W' → ▷ (interp_expr interp r W' C (WCap p g b e a)).
  Proof.
    iIntros (Hvpc) "Hexec".
    rewrite /exec_cond /enter_cond.
    iIntros (r W'). rewrite /future_world.
    assert (a ∈ₐ[[b,e]])%I as Hin.
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    destruct g.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a r W' Hin Hrelated).
      iFrame.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a r W' Hin Hrelated).
      iFrame.
  Qed.

  (* updatePcPerm adds a later because of the case of E-capabilities, which
     unfold to ▷ interp_expr *)
  Lemma interp_updatePcPerm W C w :
    ⊢ interp W C w -∗ ▷ (∀ regs, interp_expression regs W C (updatePcPerm w)).
  Proof.
    iIntros "#Hw".
    assert ( ( (∃ p g b e a, w = WSentry p g b e a))
            ∨ updatePcPerm w = w)
      as [ Hw | ->].
    {
      destruct w as [ | [ | ] | | ]; eauto. unfold updatePcPerm.
      eauto; try naive_solver.
    }
    { destruct Hw as (p & g & b & e & a & ->).
      rewrite fixpoint_interp1_eq /=.
      iIntros (rmap). iSpecialize ("Hw" $! rmap). iDestruct "Hw" as "#Hw".
      iPoseProof (futureworld_refl g W) as "Hfuture".
      iSpecialize ("Hw" $! W (futureworld_refl g W)).
      iNext. iIntros "(HPC & Hr & ?)".
      iDestruct "Hw" as "[Hw _]".
      iApply "Hw"; eauto. iFrame.
    }
    { iNext. iIntros (rmap). iApply fundamental; eauto. }
  Qed.

  Lemma jmp_or_fail_spec W C w φ :
    (interp W C w
     -∗ (if decide (isCorrectPC (updatePcPerm w))
         then (∃ p g b e a,
                  ⌜w = WCap p g b e a ∨ w = WSentry p g b e a ⌝
                  ∗ □ ∀ regs W',
                 future_world g W W'
                 → ▷ (interp_expr interp regs W' C) (updatePcPerm w))
         else φ FailedV ∗ PC ↦ᵣ updatePcPerm w
                          -∗ WP Seq (Instr Executable) {{ φ }} )).
  Proof.
    iIntros "#Hw".
    destruct (decide (isCorrectPC (updatePcPerm w))).
    - inversion i.
      destruct w;inv H.
      + destruct p; cbn in * ; simplify_eq.
        iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|].
        iApply exec_wp;auto.
      + destruct p0; cbn in * ; simplify_eq.
        * iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
          rewrite /= fixpoint_interp1_eq /=.
          iDestruct "Hw" as "#Hw".
          iIntros (regs W') "Hfuture".
          iSpecialize ("Hw" with "Hfuture").
          iDestruct "Hw" as "[Hw _]".
          iExact "Hw".
    - iIntros "[Hfailed HPC]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC");eauto.
      iNext. iIntros "_". iApply wp_pure_step_later;auto.
      iNext; iIntros "_". iApply wp_value. iFrame.
  Qed.

End fundamental.
