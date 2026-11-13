From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel ftlr_base.
From griotte Require Import monotone wp_core_full ftlr_contract Ecall.
Import CoreWPNotations.

(** * One step of the fundamental theorem

    The step lemma [ftlr_step] runs one instruction of a thread from a safe
    PC: the head (the not-correct-PC branch, the opening of the region of
    the PC), the case of the instruction, and the handling of its value
    (the next instruction, a fault, a halt, a yield). The case of the
    instruction, Ecall included, comes from the premise. The world is
    reached through a world accessor around the core step of the
    instruction; the cases never see it. *)

Section ftlr_step_generic.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The world accessor around the core step of an instruction: from the
      world resources of [W] under the regime of [C], what the thread holds
      at its posture [m] ([held]), its MIE fragment at [m], where it may
      run, and the carried credit, the core step of the instruction runs on
      the owned world interpretation of a public future world [W'] of [W].
      The core step receives the lent volatile part and gives it back at a
      post-step InterruptEnabled. The post-state, at the post-world [W'']
      and the post-step MIE value [m'], goes back to the regime; the thread
      gets the token and the part of its posture at InterruptDisabled
      ([part_at]). *)
  Definition world_accessor : iProp Σ :=
    ∀ W C (m : InterruptStatus) (Ψ : WORLD → InterruptStatus → tval (kind_of th) → iProp Σ),
      world_resources W C -∗
      held (th := th) m -∗
      (MIE ↦ₜ[th] m ∗ ⌜route_pre th m⌝) -∗
      shared_credit C -∗
      (∀ W', ⌜related_sts_pub_world W W'⌝ -∗
         world_interp W' C -∗
         vol_lent_any -∗
         (MIE ↦ₜ[th] m ∗ ⌜route_pre th m⌝) -∗
         WP Instr Executable @core[th]
         {{ v, ▷ ∃ W'' m', ⌜related_sts_pub_world W' W''⌝ ∗
                           world_interp W'' C ∗
                           (MIE ↦ₜ[th] m' ∗ ⌜route_pre th m'⌝) ∗
                           (if m' is InterruptEnabled then vol_lent_any else True) ∗
                           Ψ W'' m' v }}) -∗
      WP Instr Executable @[th]
      {{ v, ▷ ∃ W'' m', world_resources W'' C ∗
                        part_at (th := th) m' ∗
                        (MIE ↦ₜ[th] m' ∗ ⌜route_pre th m'⌝) ∗
                        Ψ W'' m' v }}.

  (** A safe, correct PC has a valid PC permission. *)
  Lemma interp_validPCperm W C p g b e a :
    isCorrectPC (Cap p g b e a) →
    interp W C (Cap p g b e a) -∗
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
    iDestruct "Hinv_interp" as "[ [_ [%Hcontra _] ] | %Hexp]"; first naive_solver.
    (* An exposed-device capability is not write-local. *)
    destruct Hexp as (_ & _ & Hwl & _). discriminate.
  Qed.

  (** The region resources of the address pointed to by a safe, correct PC. *)
  Lemma interp_pc_in_registers W C (regs : leibnizO LReg) p g b e a :
    isCorrectPC (Cap p g b e a) →
    validPCperm p g →
    thread_in th C -∗
    world_interp W C -∗
    interp W C (Cap p g b e a) -∗
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    world_interp W C ∗
    ∃ (p' : Perm) (P : V),
      ⌜PermFlowsTo p p'⌝ ∗
      ⌜persistent_cond P⌝ ∗
      region_rel W C (LNonHeap a) p' P p g ∗
      ▷ zcond P C ∗
      (if decide (readAllowed_a_in_lregs regs a)
       then ▷ (rcond_l P C p' interp)
       else emp) ∗
      (if decide (writeAllowed_a_in_lregs regs a)
       then ▷ (if isWL p then wcond_wl P C interp else wcond_nwl P C interp)
       else emp).
  Proof.
    iIntros (HcorrectPC Hp) "#Hth Hw #Hinv #Hreg".
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }
    iEval (rewrite !interp_unfold interp1_eq) in "Hinv".
    destruct (isO p) eqn: HnO.
    { destruct Hp as [Hexec _]; eapply executeAllowed_nonO in Hexec; congruence. }
    destruct (has_sreg_access p) eqn:HpXRS; first done.
    iDestruct "Hinv" as "[ [#Hinv [%Hpwl_cond _] ] | %Hexp]"; cycle 1.
    { (* An exposed-device capability is not executable. *)
      destruct Hp as [Hexec _]. destruct Hexp as (_ & Hnexec & _). congruence. }
    iDestruct (extract_from_region_inv _ _ a with "Hinv") as "H";auto.
    assert (readAllowed p = true) as Hra.
    { destruct Hp as [Hexec _]; by eapply executeAllowed_is_readAllowed. }
    iApply (interp_in_registers with "Hth Hw [Hreg] [H]"); eauto.
    apply not_mmio_not_exposed_mmio, (disjoint_from_mmio_not_in b e); first naive_solver.
    apply withinBounds_true_iff. solve_addr.
  Qed.

End ftlr_step_generic.

(** The step lemma, at the threads' links: the core step runs through the
    full-link adapter, with the posture of the thread. *)
Section ftlr_step.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads}
    {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The world accessor at the thread's link, in either regime. The thread
      holds its posture ([held]) and its MIE fragment, at a posture where it
      may run. The full-link adapter routes the posture around the core step
      and lends it [handover_res]: the critical-section token stays with
      the accessor, the volatile part goes to the core step. The world
      resources are opened with the token and the carried credit, the step
      runs on the owned world interpretation at [W' := W], and the world
      resources are closed in the step's post, under its later. In
      exclusive mode the token and the credit are not used. *)
  Lemma world_accessor_full : ⊢ world_accessor.
  Proof.
    iIntros (W C m Ψ) "Hwres Hheld [Hmie %Hpre] Hcred Hstep".
    iApply (wp_wand with "[Hwres Hheld Hmie Hstep Hcred]").
    { iApply (wp_core_full_ho (th := th) ⊤ m
                (λ m' v, ∃ W'', ⌜route_pre th m'⌝ ∗ world_resources W'' C ∗
                   (if m' is InterruptDisabled then na_own crit ⊤ else True) ∗
                   Ψ W'' m' v)%I
               with "Hheld Hmie"); first done.
      iIntros "Hho Hmie".
      iDestruct (handover_res_vol with "Hho") as "[Htok Hvol]".
      iMod (world_resources_acc_credit ⊤ ⊤ with "Hwres Hcred Htok")
        as "(Hworld & Htok & [_ Hclose])"; [solve_ndisj | solve_ndisj |].
      iSpecialize ("Hstep" $! W with "[] Hworld Hvol [$Hmie //]").
      { iPureIntro. apply related_sts_pub_refl_world. }
      iApply (wp_strong_mono with "Hstep"); [done | done |].
      iIntros (v) "Hpost".
      iDestruct "Hpost" as (W'' m') "(_ & Hworld & [Hmie Hpre'] & Hvol & HΨ)".
      iMod ("Hclose" $! W'' with "Hworld Htok") as "[Hwres Htok]".
      iModIntro. iNext. iDestruct "Hpre'" as %Hpre'.
      iExists m'. iFrame "Hmie".
      destruct m'.
      - iSplitL "Htok Hvol"; first (iApply handover_res_vol; iFrame).
        iExists W''. by iFrame.
      - iSplitR; first done. iExists W''. by iFrame. }
    iIntros (v) "Hpost". iNext.
    iDestruct "Hpost" as (m') "(Hmie & Hpart & %W'' & %Hpre' & Hwres & Htok & HΨ)".
    iExists W'', m'. iFrame "Hwres Hmie HΨ". iSplit; last done.
    destruct m'; [done | iFrame].
  Qed.

  (** A fault whose safe-register facts, world and posture come a later
      after the fault: the trap step strips the later. The trap vector is
      safe for a fault in an untrusted compartment at the running thread,
      and receives the whole posture. *)
  Lemma ftlr_trap_later
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (w : LWord) (m : InterruptStatus) :
    (∀ x : RegName, is_Some (regs !! x)) →
    untrusted_trap_safe interp interp_continuation -∗
    PC ↦ₚ[th] w -∗
    regs[th] regs -∗
    interp_continuation cstk Ws Cs -∗
    na_own (tpool th) ⊤ -∗
    ◯(CSTK)[th] cstk -∗
    ▷ (⌜frame_match Ws Cs cstk W C⌝ ∗
       thread_in th C ∗
       interp_reg interp W C regs ∗
       top_cmpt_untrusted interp W C cstk ∗
       world_resources W C ∗
       ⌜route_pre th m⌝ ∗
       MIE ↦ₜ[th] m ∗
       held (th := th) m) -∗
    WP Seq (Instr Faulted) @[th] {{ HO th }}.
  Proof.
    iIntros (Hfull) "#Htrap HPC Hregs Hcont Hown Hcstk Hlater".
    iApply (wp_trap with "HPC").
    iApply trap_safe_entry_intro.
    iDestruct "Hlater" as "(Hframe & Hth & Hreg & Htop & Hworld & >%Hpre & >Hmie & Hheld)".
    rewrite /held /held_of.
    iAssert (◇ ((if m is InterruptDisabled then handover_res else True) ∗
                ▷ (if m is InterruptDisabled then posture_part (th := th) else True)))%I
      with "[Hheld]" as ">[Hho Hpart]".
    { destruct m; first by iModIntro. iDestruct "Hheld" as "[>Hho Hpart]". by iFrame. }
    iModIntro. iExists m.
    iSplitL "Hmie Hho".
    { iApply trap_entry_res_unfold. by iFrame. }
    iIntros "!> Hout HPC".
    iDestruct (trap_entry_out_posture with "Hout Hpart") as "[Hmie Hpost]"; first done.
    iDestruct "Hframe" as %Hframe.
    iApply ("Htrap" $! cstk regs with "[//] [Hth Hreg Htop Hworld Hcont] HPC Hmie Hpost
              Hregs Hown Hcstk").
    iLeft. iExists W, C, Ws, Cs. by iFrame.
  Qed.

  (** The post-state [Q] of a case is the post-state of the accessor's
      body, for the hand-off [λ W'' m' v, ⌜related_sts_pub_world W0 W''⌝ ∗
      Q m' W'' v], once the world [W] of the case is a public future world
      of the world [W0] of the step. *)
  Lemma ftlr_case_handoff (W0 W : WORLD) (C : CmptName)
      (Q : InterruptStatus → WORLD → tval (kind_of th) → iProp Σ) :
    related_sts_pub_world W0 W →
    WP Instr Executable @core[th] {{ ftlr_contract_post W C Q }} -∗
    WP Instr Executable @core[th]
      {{ ftlr_contract_post W C (λ m' W' v, ⌜related_sts_pub_world W0 W'⌝ ∗ Q m' W' v) }}.
  Proof.
    iIntros (Hrel0) "Hwp".
    iApply (wp_wand with "Hwp").
    iIntros (v) "Hpost !>".
    iDestruct "Hpost" as (W' m' Hrel) "(Hworld & Hmie & Hvol & Hpost)".
    iExists W', m'. iFrame.
    iSplit; first done.
    iPureIntro. by eapply related_sts_pub_trans_world.
  Qed.

  (** The value of an instruction: the next instruction runs from the
      next-PC witness at the post-step posture, a fault traps, a halt gives
      back the thread's non-atomic token, a yield hands the thread over
      ([HO YieldV]); the context-switch thread's environment call enters
      the trap vector. *)
  Lemma ftlr_value
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (v : tval (kind_of th)) :
    frame_match Ws Cs cstk W C →
    thread_in th C -∗
    untrusted_trap_safe interp interp_continuation -∗
    top_cmpt_untrusted interp W C cstk -∗
    interp_continuation cstk Ws Cs -∗
    na_own (tpool th) ⊤ -∗
    ◯(CSTK)[th] cstk -∗
    (▷ ∃ W' m', ⌜related_sts_pub_world W W'⌝ ∗ world_resources W' C ∗
                part_at (th := th) m' ∗ MIE ↦ₜ[th] m' ∗ ⌜route_pre th m'⌝ ∗
                ftlr_post_sw m' W' C v) -∗
    WP Seq (of_val v) @[th] {{ HO th }}.
  Proof.
    iIntros (Hframe) "#Hth #Htrap #Htop Hcont Hown Hcstk Hpost".
    destruct v as [| | |[ | | ] ]; cbn [of_val].
    - (* HaltedV *)
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value. rewrite HO_halted. iFrame.
    - (* FaultedV *)
      iDestruct "Hpost" as (W' m') "(>%Hrel & Hwres & Hpart & Hmie & Hpre & [Hec | [Hlent Hpost] ])".
      { iDestruct "Hec" as (b pc regs) "(_ & >%Hv & _)".
        apply tval_sw_ecall_cases in Hv as [ [_ Hv] | [_ Hv] ]; discriminate. }
      iEval (rewrite ftlr_post_at_eq // /ftlr_post) in "Hpost".
      iDestruct "Hpost" as (regs pc) "(>HPC & >Hregs & Hreg)".
      iDestruct "Hreg" as "[>%Hfull Hreg]".
      iApply (ftlr_trap_later _ _ _ _ _ _ _ m' with "Htrap HPC Hregs Hcont Hown Hcstk");
        first done.
      iNext. iDestruct (held_refold with "Hpart Hlent") as "Hheld".
      iFrame "Hreg Hwres Hth Hheld Hmie Hpre".
      iSplit; first (iPureIntro; by eapply frame_match_mono).
      iSplit; first (iPureIntro; done).
      by iApply (top_cmpt_untrusted_mono_pub with "Htop").
    - (* NextIV *)
      iApply wp_pure_step_later; auto. iNext; iIntros "Hlc".
      (* The credit of the collapse is the next carried credit. *)
      iDestruct (shared_credit_refill C with "Hlc") as "Hcred".
      iDestruct "Hpost" as (W' m' Hrel) "(Hwres & Hpart & Hmie & %Hpre & [Hec | [Hlent Hpost] ])".
      + (* The environment call of the context-switch thread enters the
           trap vector, with the posture pinned by the step. *)
        iDestruct "Hec" as (b pc regs -> Hv Hpreb Hfull) "(Hvol & HPC & Hregs & #Hreg & _)".
        apply tval_sw_ecall_cases in Hv as [ [_ Hv] | [Hctx _] ]; first discriminate.
        iDestruct "Hpart" as "[Htok Hpart]".
        iApply ("Htrap" $! cstk regs pc
                 with "[//] [Hwres Hcont] HPC Hmie [Htok Hvol Hpart] Hregs Hown Hcstk").
        * iLeft. iExists W', C, Ws, Cs. iFrame "Hwres Hth Hcont".
          iSplit; first (iPureIntro; by eapply frame_match_mono).
          iSplit; first by iApply (interp_reg_intro with "Hreg").
          by iApply (top_cmpt_untrusted_mono_pub with "Htop").
        * iExists b, MCAUSE_ECALL_MACHINE, MTVAL_NONE.
          iSplit; first done. iSplit; first (iPureIntro; by right).
          rewrite posture_res_gen_unfold. iFrame "Hpart".
          iExists (lmepcc_of_pc pc), _, MTVAL_NONE, b. rewrite handover_at_vol. by iFrame.
      + iDestruct (held_refold with "Hpart Hlent") as "Hheld".
        iEval (rewrite /ftlr_post_at) in "Hpost".
        iDestruct "Hpost" as (regs pc Hfull) "(HPC & Hregs & #Hreg & Hpc)".
        iApply ("Hpc" $! cstk Ws Cs regs
                 with "[$Hth $Htrap $HPC $Hregs $Hwres $Hcred $Hcont $Hown $Hcstk $Hmie $Hheld]").
        iSplit; first by iApply (interp_reg_intro with "Hreg").
        iSplit; first by iApply (top_cmpt_untrusted_mono_pub with "Htop").
        iPureIntro. split; [by eapply frame_match_mono | done].
    - (* YieldV *)
      iApply wp_pure_step_later; auto. iNext; iIntros "Hlc".
      (* The credit of the collapse is the next carried credit. *)
      iDestruct (shared_credit_refill C with "Hlc") as "Hcred".
      iDestruct "Hpost" as (W' m' Hrel) "(Hwres & Hpart & Hmie & %Hpre & [Hec | [_ Hpost] ])";
        last (iEval (rewrite ftlr_post_at_eq // /ftlr_post) in "Hpost"; done).
      iDestruct "Hec" as (b pc regs -> Hv Hpreb Hfull) "(Hvol & HPC & Hregs & #Hreg & Hk)".
      apply tval_sw_ecall_cases in Hv as [ [Hnctx _] | [_ Hv] ]; last discriminate.
      iDestruct "Hpart" as "[Htok Hpart]".
      iApply wp_value. rewrite HO_yield. iSplit; first done.
      rewrite /yield_body. iExists b, (lmepcc_of_pc pc).
      iSplitL "Htok Hvol Hpart".
      { rewrite posture_res_gen_unfold. iFrame "Hpart".
        iExists (lmepcc_of_pc pc), _, MTVAL_NONE, b. rewrite handover_at_vol. by iFrame. }
      iFrame "Hmie HPC".
      iApply bi.later_intro. iIntros "Hmie HPC Hheld". rewrite safe_unfold.
      iApply ("Hk" $! cstk Ws Cs regs
               with "[$Hth $Htrap $HPC $Hregs $Hwres $Hcred $Hcont $Hown $Hcstk $Hmie $Hheld]").
      iSplit; first by iApply (interp_reg_intro with "Hreg").
      iSplit; first by iApply (top_cmpt_untrusted_mono_pub with "Htop").
      iPureIntro. split; [by eapply frame_match_mono | done].
    - (* ExitV: neither post-state holds *)
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct "Hpost" as (W' m' _) "(_ & _ & _ & _ & [Hec | [_ Hpost] ])".
      + iDestruct "Hec" as (b pc regs _ Hv) "_".
        apply tval_sw_ecall_cases in Hv as [ [_ Hv] | [_ Hv] ]; discriminate.
      + iEval (rewrite ftlr_post_at_eq // /ftlr_post) in "Hpost". done.
    - (* ResumedV: neither post-state holds *)
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct "Hpost" as (W' m' _) "(_ & _ & _ & _ & [Hec | [_ Hpost] ])".
      + iDestruct "Hec" as (b pc regs _ Hv) "_".
        apply tval_sw_ecall_cases in Hv as [ [_ Hv] | [_ Hv] ]; discriminate.
      + iEval (rewrite ftlr_post_at_eq // /ftlr_post) in "Hpost". done.
  Qed.

  (** The step lemma: the head, the case of the instruction, and the value,
      around the world accessor, at the posture [m] of the thread. The
      case of the instruction, Ecall included, comes from the premise. *)
  Lemma ftlr_step
    (W : WORLD) (C : CmptName) (m : InterruptStatus) (w : LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (regs : LReg) :
    (∀ W C regs p p' g b e a w i ρ P m,
        ftlr_contract m W C regs p p' g b e a w i ρ P) →
    frame_match Ws Cs cstk W C →
    route_pre th m →
    world_accessor -∗
    thread_in th C -∗
    untrusted_trap_safe interp interp_continuation -∗
    ftlr_IH -∗
    □ interp W C w -∗
    interp_reg interp W C regs -∗
    top_cmpt_untrusted interp W C cstk -∗
    PC ↦ₚ[th] w -∗
    registers_pointsto regs -∗
    world_resources W C ∗ shared_credit C -∗
    interp_continuation cstk Ws Cs -∗
    na_own (tpool th) ⊤ -∗
    ◯(CSTK)[th] cstk -∗
    held (th := th) m -∗
    MIE ↦ₜ[th] m -∗
    safe[th].
  Proof.
    iIntros (Hcases Hframe Hpre) "Hacc #Hthread #Htrap #IH #Hw #Hreg #Htop HPC Hregs
      [Hwres Hcred] Hcont Hown Hcstk Hthr Hmie".
    iApply (wp_bind (@fill (tlang_ectx _) [SeqCtx])).
    iApply (wp_wand _ _ _
              (λ v, ▷ ∃ W'' m', world_resources W'' C ∗ part_at (th := th) m' ∗
                       (MIE ↦ₜ[th] m' ∗ ⌜route_pre th m'⌝) ∗
                       ⌜related_sts_pub_world W W''⌝ ∗ ftlr_post_sw m' W'' C v)%I
             with "[- Hcont Hown Hcstk] [Hcont Hown Hcstk]").
    2: { (* 7. The value, after the accessor closes. *)
      iIntros (v) "Hpost".
      iApply (ftlr_value with "Hthread Htrap Htop Hcont Hown Hcstk"); first done.
      iNext. iDestruct "Hpost" as (W'' m') "(Hwres & Hpart & [Hmie %Hpre'] & Hrel & Hpost)".
      iExists W'', m'. by iFrame. }
    (* 1. The accessor opens. *)
    iApply ("Hacc" $! W C m (λ W'' m' v, ⌜related_sts_pub_world W W''⌝ ∗ ftlr_post_sw m' W'' C v)%I
             with "Hwres Hthr [$Hmie //] Hcred").
    iIntros (W' Hrel) "Hworld Hvol [Hmie _]".
    iDestruct (interp_reg_monotone with "Hreg") as "#Hreg'"; first done.
    iClear "Hreg".
    (* 2. The not-correct-PC branch. *)
    destruct (decide (isCorrectPC w.(lw))) as [HcorrectPC | Hnpc]; cycle 1.
    { iApply (wp_notCorrectPC with "HPC"); first done.
      iIntros "!> HPC !>".
      iDestruct (vol_lent_frame m with "Hvol") as "[Hvol Hlent]".
      iExists W', m. iFrame "Hworld Hmie Hvol".
      iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
      iSplit; first done.
      iSplit; first done.
      iRight. iFrame "Hlent".
      rewrite ftlr_post_at_eq //.
      iExists regs, w. by iFrame "HPC Hregs Hreg'". }
    destruct w as [ [ | [ [] p g b e a | ] | | ] π]; try by inversion HcorrectPC.
    (* 3. The registers. *)
    iDestruct "Hreg'" as "[%Hfull #Hsafe]".
    iRename "Hregs" into "Hmap".
    iRename "Hsafe" into "Hregs".
    assert (∀ x : RegName, is_Some (regs !! x)) as Hfull'.
    { intros x. by destruct (Hfull x) as [? ->]. }
    (* 4. The PC and the region of its address. *)
    iDestruct (interp_pc_noid with "Hw") as %->; first exact HcorrectPC.
    iDestruct (interp_monotone_noid with "Hw") as "#Hinv_interp"; [done | done |].
    iClear "Hw".
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }
    iDestruct (interp_validPCperm with "Hinv_interp") as "%Hp"; first done.
    iDestruct (interp_pc_in_registers with "Hthread Hworld Hinv_interp Hregs")
      as "[Hworld (%p' & %P & %Hflp & %Hpers & #Hrela & #Hzcond & #Hrcond & #Hwcond)]"; eauto.
    iDestruct (region_rel_parts with "Hrela") as (ρ) "#Hinva".
    (* A Permanent region of the PC is not a Temporary key of the local world. *)
    iAssert (world_interp W' C ∗ ⌜ρ = InPerm → std W' !! LNonHeap a ≠ Some Temporary⌝)%I
      with "[Hworld]" as "[Hworld %HnT]".
    { destruct ρ; [|by iFrame].
      iDestruct (world_interp_rel_perm_not_temporary_nonheap with "Hworld Hinva") as "[$ %HnT]".
      done. }
    rewrite open_world_interp_empty.
    iAssert (world_interp_open W' C [LNonHeap a] ∗ ▷ ∃ wa, pc_open W' C (LNonHeap a) p' P wa ρ)%I
      with "[Hworld]" as "[Hworld (%wa & WorldRes)]".
    { destruct ρ; cbn.
      - iDestruct (open_world_interp_permanent with "Hworld Hinva") as "[$ Hres]";
          [set_solver|by apply HnT|].
        iDestruct "Hres" as (wa) "(%HpO & Hc & HP)".
        iNext. iExists wa. iApply (pc_open_intro with "[Hc HP]"); [done|by iFrame "∗%"].
      - iDestruct "Hinva" as "(Hrel & %HT & _)".
        iDestruct (open_world_interp_temporary with "Hworld Hrel") as "[$ Hres]";
          [set_solver|done|].
        iDestruct "Hres" as (wa) "(%HpO & Hc & HP & Hmono)".
        iNext. iExists wa. iApply (pc_open_intro with "[Hc HP Hmono]"); [done|by iFrame "∗%"]. }
    (* 5. The case of the instruction; its post-state goes back to the
       accessor. *)
    iApply (ftlr_case_handoff W W' C); first done.
    iApply (Hcases W' C regs p p' g b e a wa (decodeInstrW wa.(lw)) ρ P m
            with "[$IH $Hthread $Hinv_interp $Hregs $Hinva $Hrcond $Hwcond $WorldRes
                  $Hworld $HPC $Hmap $Hmie $Hvol //]"); eauto.
  Qed.

End ftlr_step.
