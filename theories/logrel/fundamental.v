From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel interp_weakening monotone.
From griotte Require Export
  ftlr_base
  Jmp Jnz Jalr Mov CLoad Store BinOp Restrict
  Subseg Get ClearTag Lea Seal UnSeal SpecialRW SetMIE Mret FailHalt Auipcc.
From griotte Require Import register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    (trusted_fault : CSTK → LWord → LReg → iProp Σ)
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** Weakening of the instruction premise of a case lemma. *)
  Lemma ftlr_instr_base_mono (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P : V) (Pinstr Q : Prop)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    (Q → Pinstr) →
    ftlr_instr_base trusted_fault W C regs p p' g b e a w ρ P Pinstr cstk Ws Cs →
    ftlr_instr_base trusted_fault W C regs p p' g b e a w ρ P Q cstk Ws Cs.
  Proof.
    intros HQP H Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked HQ.
    exact (H Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked (HQP HQ)).
  Qed.

  (** The case lemmas of all the instructions give the FTLR step. *)
  Lemma ftlr_instr_dispatch (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P : V)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    (∀ i, ftlr_instr trusted_fault W C regs p p' g b e a w i ρ P cstk Ws Cs) →
    ftlr_instr_base trusted_fault W C regs p p' g b e a w ρ P True cstk Ws Cs.
  Proof.
    intros Hcases.
    apply (ftlr_instr_base_mono _ _ _ _ _ _ _ _ _ _ _ _ (decodeInstrW w.(lw) = decodeInstrW w.(lw)));
      [done | apply Hcases].
  Qed.

  #[local] Ltac by_binop_case :=
    eapply ftlr_instr_base_mono; [| eapply binop_case]; intros ->; eauto 10.
  #[local] Ltac by_get_case :=
    eapply get_case; rewrite /is_Get; eauto 10.

  (** A safe, correct PC has a valid PC permission. *)
  Lemma interp_validPCperm W C p g b e a :
    isCorrectPC (WCap true p g b e a) →
    interp W C (WCap true p g b e a) -∗
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
    rewrite interp_unfold interp1_eq.
    replace (isO (BPerm _ WL _ _)) with false by (cbn; destruct rx; done).
    cbn.
    destruct rx; auto.
    iDestruct "Hinv_interp" as "[_ %Hcontra]". naive_solver.
  Qed.

  (** The region resources of the address pointed to by a safe, correct PC. *)
  Lemma interp_pc_in_registers W C (regs : leibnizO LReg) p g b e a :
    isCorrectPC (WCap true p g b e a) →
    validPCperm p g →
    interp W C (WCap true p g b e a) -∗
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    ∃ (p' : Perm) (P : V),
      ⌜PermFlowsTo p p'⌝ ∗
      ⌜persistent_cond P⌝ ∗
      rel C (LNonHeap a) p' (safeC P) ∗
      ▷ zcond P C ∗
      (if decide (readAllowed_a_in_lregs regs a)
       then ▷ (rcond P C p' interp)
       else emp) ∗
      (if decide (writeAllowed_a_in_lregs regs a)
       then ▷ wcond P C interp
       else emp) ∗
      monoReq W C (LNonHeap a) p' P ∗
      ⌜if isWL p then region_state_pwl W (LNonHeap a) else region_state_nwl W (LNonHeap a) g⌝.
  Proof.
    iIntros (HcorrectPC Hp) "#Hinv #Hreg".
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }
    iEval (rewrite !interp_unfold interp1_eq) in "Hinv".
    destruct (isO p) eqn: HnO.
    { destruct Hp as [Hexec _]; eapply executeAllowed_nonO in Hexec; congruence. }
    destruct (has_sreg_access p) eqn:HpXRS; first done.
    iDestruct "Hinv" as "[#Hinv %Hpwl_cond]".
    iDestruct (extract_from_region_inv _ _ a with "Hinv") as "H";auto.
    assert (readAllowed p = true) as Hra.
    { destruct Hp as [Hexec _]; by eapply executeAllowed_is_readAllowed. }
    iApply (interp_in_registers with "[Hreg] [H]"); eauto.
  Qed.

  (* The premise [trap_vector_safe trusted_fault (lword_of_word mtcc_vec)] is discharged in
     the switcher by [switcher_mtcc_vec_safe]
     (switcher/switcher_exception.v). *)
  Theorem fundamental_cap
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality)
    (b e a : Addr) (π : option AId) :
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      interp W C (WCap true p g b e a @@? π) →
      interp_expression W C (WCap true p g b e a @@? π).
  Proof.
    iIntros "#Htrap #Hinv_interp".
    iIntros (cstk Ws Cs regs0) "[Hregs [#Htop [HPC [Hmreg [Hworld_interp [Hcont [Hown [Hframe %Hframe]]]]]]]]".
    (* The registers are replaced by their filtered words, which are safe. *)
    iApply (interp_reg_refilter with "Hregs Hmreg Hworld_interp").
    iIntros (regs) "Hfull Hreg Hmreg Hworld_interp".
    clear regs0.
    destruct (readAllowed p) eqn:Hread_p; cycle 1.
    { (* if p not readable, then execution will fail *)
      apply notreadAllowed_is_notexecuteAllowed in Hread_p.
      iApply (wp_notCorrectPC_trap with "HPC").
      { intro Hcontra ; destruct p ; inv Hcontra; congruence. }
      iDestruct "Hfull" as %Hfull.
      iApply (interp_trap_safe_untrusted with
               "Htrap [Hreg] Htop [$Hmreg $Hworld_interp $Hcont $Hown $Hframe]");
        [done | done | by iApply (interp_reg_intro with "Hreg") | done].
    }
    clear Hread_p.

    iRevert "Hinv_interp Htop".
    iLöb as "IH'" forall (W C regs p g b e a π cstk Ws Cs Hframe).
    iAssert ftlr_IH as "IH" ; [|iClear "IH'"].
    { iModIntro; iNext.
      iIntros (W_ih C_ih cstk_ih Ws_ih Cs_ih r_ih p_ig g_ih b_ih e_ih a_ih π_ih)
        "%Hfull #Hregs HPC Hmreg Hworld_interp Hcont %Hframe' #Htop Hown Htframe Hinterp".
      iApply ("IH'" with "[%] HPC Hcont Hown Htframe [%] Hregs Hmreg Hworld_interp Hinterp Htop"); eauto.
    }
    iIntros "#Hinv_interp #Htop".
    iDestruct "Hfull" as %Hfull. iDestruct "Hreg" as "#Hreg".
    rewrite /registers_pointsto.
    destruct (decide (isCorrectPC (WCap true p g b e a))) as [HcorrectPC|] ; cycle 1.
    { (* Not correct PC *)
      iApply (wp_notCorrectPC_trap with "HPC"); first done.
      iApply (interp_trap_safe_untrusted with
               "Htrap [] Htop [$Hmreg $Hworld_interp $Hcont $Hown $Hframe]");
        [done | done | by iApply (interp_reg_intro with "Hreg") | done].
    }

    (* Correct PC *)
    (* A valid PC carries no identifier: its region key is [LNonHeap a]. *)
    iDestruct (interp_pc_noid with "Hinv_interp") as %->; first exact HcorrectPC.
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }
    iDestruct (interp_validPCperm with "Hinv_interp") as "%Hp"; first done.
    iDestruct (interp_pc_in_registers with "Hinv_interp Hreg")
      as (p'' P'' Hflp'' Hperscond_P'') "(Hrela & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a)"
    ; eauto.
    assert (∃ (ρ : region_type), (std W) !! LNonHeap a = Some ρ ∧ ρ ≠ Revoked)
      as [ρ [Hρ Hne ] ].
    { destruct (isWL p),g; simplify_eq ; eauto.
      destruct Hstate_a as [Htemp | Hperm];eauto. }

    iDestruct (open_world_interp W C (LNonHeap a) p'' _ ρ with "[$Hrela] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [apply heap_key_live_nonheap | destruct ρ; auto; contradiction | exact Hρ |].

    iApply (wp_bind (fill [SeqCtx])).
    iApply (ftlr_instr_dispatch W C regs p p'' g b e a w ρ P'' cstk Ws Cs with
             "[$IH $Htrap $Hinv_interp $Hreg $Hrela $Hrcond $Hwcond $HmonoR $WorldRes
               $Hcont $Hworld_interp $Hown $Hframe $Htop $Hstate $HPC $Hmreg //]")
    ; [| eauto..].
    (* proof by cases on each instruction *)
    intros i; destruct i.
    - (* Jmp *) apply jmp_case.
    - (* Jnz *) apply jnz_case.
    - (* Jalr *) apply jalr_case.
    - (* Mov *) apply mov_case.
    - (* CLoad *) apply load_case.
    - (* Store *) apply store_case.
    - (* Lt *) by_binop_case.
    - (* Le *) by_binop_case.
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
    - (* SpecialRW *) apply specialrw_case.
    - (* SetMIE *) apply setmie_case.
    - (* Mret *) apply mret_case.
    - (* Fail *) apply fail_case.
    - (* Halt *) apply halt_case.
    - (* GetTag *) by_get_case.
    - (* ClearTag *) apply cleartag_case.
    - (* Auipcc *) apply auipcc_case.
  Qed.

  Theorem fundamental W C w :
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      interp W C w -∗
      interp_expression W C w.
  Proof.
    iIntros "#Htrap Hw"; destruct w as [ [| [ [] p g b e a | ] | | ] π].
    2: { iApply (fundamental_cap with "Htrap"); done. }
    all: iIntros (cstk Ws Cs regs)
           "(#Hinterp_regs & #Htop & HPC & Hregs & Hworld_interp & Hcont & Hown & Hframe & %Hframe)".
    all: iPoseProof "Hinterp_regs" as "[%Hfull _]".
    all: iApply (wp_notCorrectPC_trap with "HPC"); first by inversion 1.
    all: iApply (interp_trap_safe_untrusted with
                   "Htrap Hinterp_regs Htop [$Hregs $Hworld_interp $Hcont $Hown $Hframe]");
      done.
  Qed.

  (* The fundamental theorem implies the exec_cond *)
  Lemma interp_exec_cond W C p g b e a π :
    executeAllowed p = true ->
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      interp W C (WCap true p g b e a @@? π) -∗
      exec_cond W C p g b e π interp.
  Proof.
    iIntros (Hp) "#Htrap #Hw".
    destruct (decide (b < e)%a) as [Hbe|Hbe]; cycle 1.
    { iIntros (a0 W' Hin). exfalso. rewrite /in_range in Hin. solve_addr. }
    iDestruct (interp_exec_noid with "Hw") as %->; [done|done|].
    iIntros (a0 W' Hin) "#Hfuture". iModIntro.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    iDestruct (interp_cap_disjoint with "Hw") as %[_ Hdisjoint]; first done.
    destruct g.
    - iDestruct "Hfuture" as %Hrelated.
      iDestruct (interp_monotone_nl_cap_nonheap with "Hw") as "Hw'";
        [exact Hdisjoint|exact Hrelated|done|].
      iApply (fundamental W' with "Htrap"); eauto.
      iApply interp_lea; eauto.
    - iDestruct "Hfuture" as %Hrelated.
      iDestruct (interp_monotone_cap_nonheap with "Hw") as "Hw'";
        [exact Hdisjoint|exact Hrelated|].
      iApply (fundamental W' with "Htrap"); eauto.
      iApply interp_lea; eauto.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)
  Lemma exec_wp W C p g b e a π :
    isCorrectPC (WCap true p g b e a) ->
    ⊢ exec_cond W C p g b e π interp -∗
    ∀ W', future_world g W W' →
          ▷ (interp_expr interp (interp_cont interp) W' C (WCap true p g b e a @@? π)).
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
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      ftlr_IH.
  Proof.
    iIntros "#Htrap".
    iModIntro; iNext.
    iIntros (W C cstk Ws Cs regs p g b e a π)
      "Hfull #Hregs HPC Hmap Hworld Hinterp_cont Hframe #Htop Hown Hcstk #Hv".
    iDestruct (fundamental with "Htrap Hv") as "Hcont".
    iApply "Hcont"; iFrame "∗#".
    iIntros (r v Hv). iApply interp_filter_heap. by iApply "Hregs".
  Qed.

  Lemma jmp_or_fail_spec W C (w : LWord) φ :
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    (interp W C w
     -∗ (if decide (isCorrectPC (updatePcPerm w.(lw)))
         then
           (∃ p g b e a π,
               (⌜w = WCap true p g b e a @@? π ∨ (∃ k, w = WSentry k true p g b e a @@? π)⌝
                ∗ □ ∀ W', future_world g W W'
                          → ▷ (interp_expr interp (interp_cont interp) W' C) (lupdatePcPerm w)))
         else trap_safe (lupdatePcPerm w) ⊤ φ ∗ PC ↦ₚ lupdatePcPerm w
                          -∗ WP Seq (Instr Executable) {{ φ }} )).
  Proof.
    iIntros "#Htrap #Hw".
    destruct (decide (isCorrectPC (updatePcPerm w.(lw)))).
    - inversion i.
      destruct w as [w π]; cbn in H.
      destruct w;inv H.
      + destruct p; cbn in * ; simplify_eq.
        iExists _,_,_,_,_,_.
        iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "Htrap Hw") as "Hexec";[auto|].
        iApply exec_wp;auto.
      + destruct p0; cbn in * ; simplify_eq.
        iExists _,_,_,_,_,_.
        rewrite /= interp_unfold /=.
        iSplit;[iPureIntro; right; eauto|]. iModIntro.
        iDestruct "Hw" as "[%Hnonheap #Hw]".
        rewrite /enter_cond.
        iIntros (W') "Hfuture".
        iSpecialize ("Hw" with "Hfuture").
        iSpecialize ("Hw" $! g0 (LocalityFlowsToReflexive g0)).
        iExact "Hw".
    - iIntros "[Hfailed HPC]".
      by iApply (wp_notCorrectPC_trap with "HPC Hfailed").
  Qed.

End fundamental.
