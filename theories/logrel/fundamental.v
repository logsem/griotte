From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel interp_weakening monotone.
From griotte Require Export
  ftlr_base
  Jmp Jnz Jalr Mov Load Store BinOp Restrict
  Subseg Get Lea Seal UnSeal ReadSR WriteSR FailHalt.
From griotte Require Import register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  (** Weakening of the instruction premise of a case lemma. *)
  Lemma ftlr_instr_base_mono (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P : V) (Pinstr Q : Prop)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    (Q → Pinstr) →
    ftlr_instr_base W C regs p p' g b e a w ρ P Pinstr cstk Ws Cs →
    ftlr_instr_base W C regs p p' g b e a w ρ P Q cstk Ws Cs.
  Proof.
    intros HQP H Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked HQ.
    exact (H Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked (HQP HQ)).
  Qed.

  (** The case lemmas of all the instructions give the FTLR step. *)
  Lemma ftlr_instr_dispatch (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P : V)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    (∀ i, ftlr_instr W C regs p p' g b e a w i ρ P cstk Ws Cs) →
    ftlr_instr_base W C regs p p' g b e a w ρ P True cstk Ws Cs.
  Proof.
    intros Hcases.
    apply (ftlr_instr_base_mono _ _ _ _ _ _ _ _ _ _ _ _ (decodeInstrW w = decodeInstrW w));
      [done | apply Hcases].
  Qed.

  Local Ltac by_binop_case :=
    eapply ftlr_instr_base_mono; [| eapply binop_case]; intros ->; eauto 10.
  Local Ltac by_get_case :=
    eapply get_case; rewrite /is_Get; eauto 10.

  (** Execution fails when the PC is not a correct PC. *)
  Lemma wp_notCorrectPC_halted (w : Word) (φ : iProp Σ) :
    ¬ isCorrectPC w →
    PC ↦ᵣ w -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → φ }}.
  Proof.
    iIntros (HnPC) "HPC".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_notCorrectPC with "HPC"); first done.
    iNext. iIntros "HPC /=".
    iApply wp_pure_step_later; auto.
    iNext ; iIntros "_".
    iApply wp_value.
    iIntros (Hcontr); inversion Hcontr.
  Qed.

  (** A safe, correct PC has a valid PC permission. *)
  Lemma interp_validPCperm W C p g b e a :
    isCorrectPC (WCap p g b e a) →
    interp W C (WCap p g b e a) -∗
    ⌜ validPCperm p g ⌝.
  Proof.
    iIntros (HcorrectPC) "Hinv_interp".
    (* if not, contradiction by correctPC or validity *)
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
  Qed.

  (** The region resources of the address pointed to by a safe, correct PC. *)
  Lemma interp_pc_in_registers W C (regs : leibnizO Reg) p g b e a :
    isCorrectPC (WCap p g b e a) →
    validPCperm p g →
    interp W C (WCap p g b e a) -∗
    (∀ (r : RegName) (v : Word), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v) -∗
    ∃ (p' : Perm) (P : V),
      ⌜PermFlowsTo p p'⌝ ∗
      ⌜persistent_cond P⌝ ∗
      rel C a p' (safeC P) ∗
      ▷ zcond P C ∗
      (if decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a)
       then ▷ (rcond P C p' interp)
       else emp) ∗
      (if decide (writeAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a)
       then ▷ wcond P C interp
       else emp) ∗
      monoReq W C a p' P ∗
      ⌜if isWL p then region_state_pwl W a else region_state_nwl W a g⌝.
  Proof.
    iIntros (HcorrectPC Hp) "#Hinv #Hreg".
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }
    iEval (rewrite !fixpoint_interp1_eq interp1_eq) in "Hinv".
    destruct (isO p) eqn: HnO.
    { destruct Hp as [Hexec _]; eapply executeAllowed_nonO in Hexec; congruence. }
    destruct (has_sreg_access p) eqn:HpXRS; first done.
    iDestruct "Hinv" as "[#Hinv %Hpwl_cond]".
    iDestruct (extract_from_region_inv _ _ a with "Hinv") as "H";auto.
    assert (readAllowed p = true) as Hra.
    { destruct Hp as [Hexec _]; by eapply executeAllowed_is_readAllowed. }
    iApply (interp_in_registers with "[Hreg] [H]"); eauto.
  Qed.

  Theorem fundamental_cap
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality)
    (b e a : Addr) :
    ⊢ interp W C (WCap p g b e a) →
      interp_expression W C (WCap p g b e a).
  Proof.
    iIntros "#Hinv_interp".
    iIntros (cstk Ws Cs regs) "[[Hfull Hreg] [Hmreg [Hworld_interp [Hcont [Hown [Hframe %Hframe]]]]]]".
    destruct (readAllowed p) eqn:Hread_p; cycle 1.
    { (* if p not readable, then execution will fail *)
      apply notreadAllowed_is_notexecuteAllowed in Hread_p.
      rewrite /registers_pointsto; iExtract "Hmreg" PC as "HPC".
      iApply (wp_notCorrectPC_halted with "HPC").
      intro Hcontra ; destruct p ; inv Hcontra; congruence.
    }
    clear Hread_p.

    iRevert "Hinv_interp".
    iLöb as "IH'" forall (W C regs p g b e a cstk Ws Cs Hframe).
    iAssert ftlr_IH as "IH" ; [|iClear "IH'"].
    { iModIntro; iNext.
      iIntros (W_ih C_ih cstk_ih Ws_ih Cs_ih r_ih p_ig g_ih b_ih e_ih a_ih)
        "%Hfull #Hregs Hmreg Hworld_interp Hcont %Hframe' Hown Htframe Hinterp".
      iApply ("IH'" with "[%] [] [] [Hmreg] [$] [$] [$] [$]");eauto.
      done.
    }
    iIntros "#Hinv_interp".
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    rewrite /registers_pointsto; iExtract "Hmreg" PC as "HPC".
    destruct (decide (isCorrectPC (WCap p g b e a))) as [HcorrectPC|] ; cycle 1.
    { (* Not correct PC *)
      by iApply (wp_notCorrectPC_halted with "HPC").
    }

    (* Correct PC *)
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }
    iDestruct (interp_validPCperm with "Hinv_interp") as "%Hp"; first done.
    iDestruct (interp_pc_in_registers with "Hinv_interp Hreg")
      as (p'' P'' Hflp'' Hperscond_P'') "(Hrela & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a)"
    ; eauto.
    assert (∃ (ρ : region_type), (std W) !! a = Some ρ ∧ ρ ≠ Revoked)
      as [ρ [Hρ Hne ] ].
    { destruct (isWL p),g; simplify_eq ; eauto.
      destruct Hstate_a as [Htemp | Hperm];eauto. }

    iDestruct (open_world_interp with "[$Hrela] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [|eauto|]; [ destruct ρ;auto;done|].

    iApply (wp_bind (fill [SeqCtx])).
    iApply (ftlr_instr_dispatch with
             "[$IH] [$Hinv_interp] [$Hreg] [$Hrela]
             [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
             [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
             [$Hstate] [$HPC] [Hmreg]")
    ; [| eauto..].
    (* proof by cases on each instruction *)
    intros i; destruct i.
    - (* Jmp *) apply jmp_case.
    - (* Jnz *) apply jnz_case.
    - (* Jalr *) apply jalr_case.
    - (* Mov *) apply mov_case.
    - (* Load *) apply load_case.
    - (* Store *) apply store_case.
    - (* Lt *) by_binop_case.
    - (* Add *) by_binop_case.
    - (* Sub *) by_binop_case.
    - (* Mul *) by_binop_case.
    - (* LAnd *) by_binop_case.
    - (* LOr *) by_binop_case.
    - (* LShiftL *) by_binop_case.
    - (* LShiftR *) by_binop_case.
    - (* Lea *) apply lea_case.
    - (* Restrict *) apply restrict_case.
    - (* Subseg *) apply subseg_case.
    - (* GetB *) by_get_case.
    - (* GetE *) by_get_case.
    - (* GetA *) by_get_case.
    - (* GetP *) by_get_case.
    - (* GetL *) by_get_case.
    - (* GetWType *) by_get_case.
    - (* GetOType *) by_get_case.
    - (* Seal *) apply seal_case.
    - (* UnSeal *) apply unseal_case.
    - (* ReadSR *) apply readsr_case.
    - (* WriteSR *) apply writesr_case.
    - (* Fail *) apply fail_case.
    - (* Halt *) apply halt_case.
  Qed.

  Theorem fundamental W C w :
    ⊢ interp W C w -∗ interp_expression W C w.
  Proof.
    iIntros "Hw"; destruct w as [| [c | ] | | ].
    2: { iApply fundamental_cap; done. }
    all: iIntros (????) "(? & Hreg & ?)"; unfold interp_conf.
    all: iApply (wp_wand with "[-]"); [ | iIntros (?) "H"; iApply "H"].
    all: iApply (wp_bind (fill [SeqCtx])); cbn.
    all: unfold registers_pointsto; rewrite -insert_delete_eq.
    all: iDestruct (big_sepM_insert with "Hreg") as "[HPC ?]"; first by rewrite lookup_delete_eq.
    all: iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
    all: iNext; iIntros; cbn; iApply wp_pure_step_later; auto.
    all: iNext; iIntros "_"; iApply wp_value; iIntros (?); congruence.
  Qed.

  (* The fundamental theorem implies the exec_cond *)
  Lemma interp_exec_cond W C p g b e a:
    executeAllowed p = true ->
    ⊢ interp W C (WCap p g b e a) -∗ exec_cond W C p g b e interp.
  Proof.
    iIntros (Hp) "#Hw".
    iIntros (a0 W' Hin) "#Hfuture". iModIntro.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    destruct g.
    - iDestruct (interp_monotone_nl with "Hfuture [] Hw") as "Hw'";[auto|].
      iApply (fundamental W');eauto.
      iApply interp_weakening.interp_weakeningEO; eauto; try done.
    - iDestruct (interp_monotone with "Hfuture Hw") as "Hw'".
      iApply (fundamental W');eauto.
      iApply interp_weakening.interp_weakeningEO; eauto; try done.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)
  Lemma exec_wp W C p g b e a :
    isCorrectPC (WCap p g b e a) ->
    ⊢ exec_cond W C p g b e interp -∗
    ∀ W', future_world g W W' → ▷ (interp_expr interp (interp_cont interp) W' C (WCap p g b e a)).
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
    iIntros (???????????) "????????#Hv".
    iDestruct (fundamental with "Hv") as "Hcont".
    iApply "Hcont"; iFrame.
  Qed.

  Lemma jmp_or_fail_spec W C w φ :
    ⊢
    (interp W C w
     -∗ (if decide (isCorrectPC (updatePcPerm w))
         then
           (∃ p g b e a,
               (⌜w = WCap p g b e a ∨ w = WSentry p g b e a ⌝
                ∗ □ ∀ W', future_world g W W'
                          → ▷ (interp_expr interp (interp_cont interp) W' C) (updatePcPerm w)))
         else φ FailedV ∗ PC ↦ᵣ updatePcPerm w
                          -∗ WP Seq (Instr Executable) {{ φ }} )).
  Proof.
    iIntros "#Hw".
    destruct (decide (isCorrectPC (updatePcPerm w))).
    - inversion i.
      destruct w;inv H.
      + destruct p; cbn in * ; simplify_eq.
        iExists _,_,_,_,_.
        iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "[$Hw]") as "Hexec";[auto|].
        iApply exec_wp;auto.
      + destruct p0; cbn in * ; simplify_eq.
        iExists _,_,_,_,_.
        rewrite /= fixpoint_interp1_eq /=.
        iSplit;[eauto|]. iModIntro.
        iDestruct "Hw" as "#Hw".
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
