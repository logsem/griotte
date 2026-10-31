From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel ftlr_base.
From griotte Require Import monotone.
Import CoreWPNotations.

(** * One step of the fundamental theorem

    The step lemma [ftlr_step] runs one instruction of a thread from a safe
    PC: the head (the not-correct-PC branch, the opening of the region of
    the PC), the case of the instruction, and the handling of its value
    (the next instruction, a fault, a halt). The
    world is reached through a world accessor around the core step of the
    instruction; the cases never see it. *)

#[local] Instance InterruptStatus_inhabited : Inhabited InterruptStatus :=
  populate InterruptDisabled.

Section ftlr_step_generic.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The world accessor around the core step of an instruction: from the
      world resources of [W] under the regime of [C], the regime's thread
      resources [thr m] and the MIE fragment [mie m] of the thread, and the
      carried credit, the core step of the instruction runs on the owned
      world interpretation of a public future world [W'] of [W]. The
      post-state, at the post-world [W''] and the post-step MIE value [m'],
      goes back to the regime. *)
  Definition world_accessor (thr mie : InterruptStatus → iProp Σ) : iProp Σ :=
    ∀ W C (m : InterruptStatus) (Ψ : WORLD → InterruptStatus → griotte_lang.val → iProp Σ),
      world_resources W C -∗
      thr m -∗
      mie m -∗
      shared_credit C -∗
      (∀ W', ⌜related_sts_pub_world W W'⌝ -∗
         world_interp W' C -∗
         mie m -∗
         WP Instr Executable @core[th]
         {{ v, ▷ ∃ W'' m', ⌜related_sts_pub_world W' W''⌝ ∗
                           world_interp W'' C ∗
                           mie m' ∗
                           Ψ W'' m' v }}) -∗
      WP Instr Executable @[th]
      {{ v, ▷ ∃ W'' m', world_resources W'' C ∗
                        thr m' ∗
                        mie m' ∗
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
    iDestruct "Hinv_interp" as "[_ [%Hcontra _] ]". naive_solver.
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
    iDestruct "Hinv" as "[#Hinv [%Hpwl_cond _] ]".
    iDestruct (extract_from_region_inv _ _ a with "Hinv") as "H";auto.
    assert (readAllowed p = true) as Hra.
    { destruct Hp as [Hexec _]; by eapply executeAllowed_is_readAllowed. }
    iApply (interp_in_registers with "Hth Hw [Hreg] [H]"); eauto.
  Qed.

End ftlr_step_generic.

(** The step lemma, at the core link. *)
Section ftlr_step.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The exclusive world accessor: the world resources are the owned world
      interpretation, which the step uses at [W' := W]; the credit is
      dropped. *)
  Lemma world_accessor_exclusive (mie : InterruptStatus → iProp Σ) :
    ⊢ world_accessor (λ _, True)%I mie.
  Proof.
    iIntros (W C m Ψ) "Hwres _ Hmie _ Hstep".
    rewrite world_resources_exclusive.
    iApply (wp_wand with "(Hstep [] Hwres Hmie)").
    { iPureIntro. apply related_sts_pub_refl_world. }
    iIntros (v) "Hpost !>".
    iDestruct "Hpost" as (W'' m') "(_ & Hworld & Hmie & HΨ)".
    iExists W'', m'. rewrite world_resources_exclusive. by iFrame.
  Qed.

  (** A fault whose safe-register facts and world come a later after the
      fault: the trap step strips the later. The trap vector is safe for a
      fault in an untrusted compartment at the running thread. *)
  Lemma ftlr_trap_later
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (w : LWord) :
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
       world_resources W C ∗ shared_credit C) -∗
    WP Seq (Instr Faulted) @[th] {{ HO th }}.
  Proof.
    iIntros (Hfull) "#Htrap HPC Hregs Hcont Hown Hcstk Hlater".
    iApply (wp_trap with "HPC").
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iDestruct (trap_entry_res_split ⊤ with "Hown") as "[Htok Hown]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    iDestruct "Hlater" as "(%Hframe & Hth & Hreg & Htop & Hworld & Hcred)".
    iApply ("Htrap" $! cstk regs with "[//] [Hth Hreg Htop Hworld Hcred Hcont] HPC Hout Hregs Hown Hcstk").
    iLeft. iExists W, C, Ws, Cs. by iFrame.
  Qed.

  (** The value of an instruction: the next instruction runs from the
      next-PC witness, a fault traps, a halt gives back the thread's
      non-atomic token. *)
  Lemma ftlr_value
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (v : griotte_lang.val) :
    frame_match Ws Cs cstk W C →
    thread_in th C -∗
    untrusted_trap_safe interp interp_continuation -∗
    top_cmpt_untrusted interp W C cstk -∗
    interp_continuation cstk Ws Cs -∗
    na_own (tpool th) ⊤ -∗
    ◯(CSTK)[th] cstk -∗
    (▷ ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_resources W' C ∗ ftlr_post W' C v) -∗
    WP Seq (of_val v) @[th] {{ HO th }}.
  Proof.
    iIntros (Hframe) "#Hth #Htrap #Htop Hcont Hown Hcstk Hpost".
    destruct v; rewrite /ftlr_post; cbn [of_val].
    - (* HaltedV *)
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value. iIntros (_). iFrame.
    - (* FaultedV *)
      iDestruct "Hpost" as (W') "(>%Hrel & Hwres & Hpost)".
      iDestruct "Hpost" as (regs pc) "(>HPC & >Hregs & Hreg)".
      iDestruct "Hreg" as "[>%Hfull Hreg]".
      iApply (ftlr_trap_later with "Htrap HPC Hregs Hcont Hown Hcstk"); first done.
      iNext. iFrame "Hreg Hwres Hth".
      iSplit; first (iPureIntro; by eapply frame_match_mono).
      iSplit; first (iPureIntro; done).
      iSplit; first by iApply (top_cmpt_untrusted_mono_pub with "Htop").
      (* The trap step gives no credit: the exclusive regime needs none, the
         shared regime supplies it later. *)
      iApply shared_credit_exclusive.
    - (* NextIV *)
      iApply wp_pure_step_later; auto. iNext; iIntros "Hlc".
      (* The credit of the collapse is the next carried credit. *)
      iDestruct (shared_credit_refill C with "Hlc") as "Hcred".
      iDestruct "Hpost" as (W' Hrel) "(Hwres & %regs & %pc & %Hfull & HPC & Hregs & #Hreg & Hpc)".
      iApply ("Hpc" $! cstk Ws Cs regs
               with "[$Hth $Htrap $HPC $Hregs $Hwres $Hcred $Hcont $Hown $Hcstk]").
      iSplit; first by iApply (interp_reg_intro with "Hreg").
      iSplit; first by iApply (top_cmpt_untrusted_mono_pub with "Htop").
      iPureIntro. by eapply frame_match_mono.
  Qed.

  (** The step lemma: the head, the case of the instruction, and the value,
      around the world accessor. *)
  Lemma ftlr_step (thr mie : InterruptStatus → iProp Σ)
    (W : WORLD) (C : CmptName) (m : InterruptStatus) (w : LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (regs : LReg) :
    (∀ W C regs p p' g b e a w i ρ P,
        ftlr_instr W C regs p p' g b e a w i ρ P) →
    frame_match Ws Cs cstk W C →
    world_accessor thr mie -∗
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
    thr m -∗
    mie m -∗
    safe[th].
  Proof.
    iIntros (Hcases Hframe) "Hacc #Hthread #Htrap #IH #Hw #Hreg #Htop HPC Hregs [Hwres Hcred]
      Hcont Hown Hcstk Hthr Hmie".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_wand _ _ _
              (λ v, ▷ ∃ W'' m', world_resources W'' C ∗ thr m' ∗ mie m' ∗
                       ⌜related_sts_pub_world W W''⌝ ∗ ftlr_post W'' C v)%I
             with "[- Hcont Hown Hcstk] [Hcont Hown Hcstk]").
    2: { (* 7. The value, after the accessor closes. *)
      iIntros (v) "Hpost".
      iApply (ftlr_value with "Hthread Htrap Htop Hcont Hown Hcstk"); first done.
      iNext. iDestruct "Hpost" as (W'' m') "(Hwres & _ & _ & Hrel & Hpost)".
      iExists W''. iFrame. }
    (* 1. The accessor opens. *)
    iApply ("Hacc" $! W C m (λ W'' _ v, ⌜related_sts_pub_world W W''⌝ ∗ ftlr_post W'' C v)%I
             with "Hwres Hthr Hmie Hcred").
    iIntros (W' Hrel) "Hworld Hmie".
    iDestruct (interp_reg_monotone with "Hreg") as "#Hreg'"; first done.
    iClear "Hreg".
    (* 2. The not-correct-PC branch. *)
    destruct (decide (isCorrectPC w.(lw))) as [HcorrectPC | Hnpc]; cycle 1.
    { iApply (wp_notCorrectPC with "HPC"); first done.
      iIntros "!> HPC !>". iExists W', m. iFrame "Hworld Hmie".
      iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
      iSplit; first done.
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
    (* 5. The case of the instruction. *)
    iApply (wp_wand with "[- Hmie]").
    { iApply (Hcases W' C regs p p' g b e a wa (decodeInstrW wa.(lw)) ρ P
              with "[$IH $Hthread $Hinv_interp $Hregs $Hinva $Hrcond $Hwcond $WorldRes
                    $Hworld $HPC $Hmap]"); eauto. }
    (* 6. The hand-off goes back to the accessor. *)
    iIntros (v) "Hpost !>".
    iDestruct "Hpost" as (W'' Hrel') "[Hworld Hpost]".
    iExists W'', m. iFrame. iPureIntro.
    split; first done. by eapply related_sts_pub_trans_world.
  Qed.

End ftlr_step.
