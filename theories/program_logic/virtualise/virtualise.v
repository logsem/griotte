From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Import named_props_extra hw_lang.
From griotte Require Export hw_switches.

(** * Virtualisation

    The hardware runs safely from the running thread's safe run: each
    thread's WP over its thread language, the pool of the user threads and
    the entry specs of the context-switch thread give one WP over the
    hardware language. An ordinary hardware step is a step of the running
    thread; an interrupt, a yield or an exit of a user thread parks it and
    switches to the context-switch thread; the context-switch thread's
    [ResumedV] switches to the resumed thread. *)

(** * Facts on the hardware image of a thread expression *)

(* TODO: move to program_logic/thread_langs.v *)
Lemma hw_of_reducible `{MachineParameters} {k} (e : thread_langs.expr k) σ :
  wellshaped e →
  thread_langs.to_val e = None →
  reducible (Λ := griotte_hw_lang) (hw_of e) σ.
Proof.
  intros [ [f ->]|[v Hv] ] Hn; last congruence.
  destruct f as [c|s]; [apply hw_seq_reducible|apply (hw_seq_reducible σ NextI)].
Qed.

(* TODO: move to program_logic/thread_langs.v *)
Lemma hw_of_not_val `{MachineParameters} {k} (e : thread_langs.expr k) :
  wellshaped e →
  thread_langs.to_val e = None →
  language.to_val (l := griotte_hw_lang) (hw_of e) = None.
Proof. intros [ [f ->]|[v Hv] ] Hn; last congruence. by destruct f. Qed.

(* TODO: move to program_logic/thread_langs.v *)
Lemma hw_exec_thread `{MachineParameters} {k} (e : thread_langs.expr k) :
  wellshaped e →
  thread_langs.to_val e = None →
  hw_of e = griotte_lang.Exec →
  e = Exec.
Proof.
  intros Hws Hn Hh. destruct (async_at_thread e Hws Hh) as [->|[s ->] ]; done.
Qed.

(** * The context-switch thread's entry *)

Section ctx_switch_entry.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}.

  #[local] Notation posture_of x :=
    (posture_res_gen (ceriseg := ceriseG_of x) (th := x) (CL := CL x) (CR := CR x)).

  (** The resources of user thread [t], parked with kind [k] and values
      [v], that the context-switch thread receives. At an interrupt: its
      posture, pinned at the values the interrupt entry wrote (MPIE
      enabled, MEPCC its PC, mcause an interrupt cause, mtval none); a
      tagged interrupted PC has no identifier. At a yield: its posture as
      [HO] pins it, and its MIE and PC fragments. At an exit: its MIE
      fragment, its posture with mcause 24, its registers and its exit
      part. *)
  Definition parked_thread_res (t : nat) (k : park_kind) (v : resume_vals) : iProp Σ :=
    match k with
    | ParkIrq =>
        ∃ c : Z,
          "%Hmie" ∷ ⌜v.(rv_mie) = InterruptEnabled⌝ ∗
          "%Hc" ∷ ⌜c ∈ irq_causes⌝ ∗
          "%Hpc" ∷ ⌜get_tag v.(rv_pc).(lw) = true → v.(rv_pc).(lprov) = None⌝ ∗
          "Hposture" ∷ posture_of (UserThread t) (Some InterruptEnabled)
            (Some (lword_of_word v.(rv_pc).(lw))) (Some (lword_of_word (WInt c)))
            (Some MTVAL_NONE)
    | ParkYield b p =>
        "%Hv" ∷ ⌜v.(rv_pc) = lword_of_word mtcc_vec ∧ v.(rv_mie) = InterruptDisabled⌝ ∗
        "Hposture" ∷ posture_of (UserThread t) (Some b) (Some p)
          (Some (lword_of_word (WInt MCAUSE_ECALL_MACHINE))) None ∗
        "HMIE_t" ∷ MIE ↦ₜ[u t] InterruptDisabled ∗
        "HPC_t" ∷ PC ↦ₚ[u t] lword_of_word mtcc_vec
    | ParkExit =>
        "%Hmie" ∷ ⌜v.(rv_mie) = InterruptDisabled⌝ ∗
        "HMIE_t" ∷ MIE ↦ₜ[u t] InterruptDisabled ∗
        "Hposture" ∷ posture_of (UserThread t) None None
          (Some (lword_of_word (WInt MCAUSE_THREAD_EXIT))) None ∗
        "Hregs_t" ∷ regs[u t] v.(rv_regs) ∗
        "Hexit" ∷ exit_part (UserThread t)
    end.

  (** The precondition of the context-switch thread's entry after user
      thread [t] is parked with kind [k] and values [v]: its fragments (the
      PC at the trap vector, or at the exit PC; MIE disabled; mtdc at [t]'s
      home; [t]'s registers, copied), the Saving token, the scheduler's
      state, its open pool token with the closer, and [t]'s parked
      resources. *)
  Definition ctx_switch_entry_pre (t : nat) (k : park_kind) (v : resume_vals) : iProp Σ :=
    "HPC" ∷ PC ↦ₚ[CtxSwitch] (if k is ParkExit then v.(rv_pc) else lword_of_word mtcc_vec) ∗
    "HMIE" ∷ MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread t)) ∗
    "%Hdom" ∷ ⌜dom v.(rv_regs) = all_registers_s⌝ ∗
    "Hregs" ∷ regs[CtxSwitch] v.(rv_regs) ∗
    "Hcur" ∷ cur_frag (Some (UserThread t, Saving k v)) ∗
    "Hsched" ∷ sched_state ∗
    "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
    "Hclose" ∷ close_Nact ∗
    "Hparked" ∷ parked_thread_res t k v.

  (** The entry specs of the context-switch thread: from its entry
      precondition, after any park, it runs safely. *)
  Definition ctx_switch_entry_specs : iProp Σ :=
    ∀ (t : nat) (k : park_kind) (v : resume_vals),
      ctx_switch_entry_pre t k v -∗
      safe[CtxSwitch].
End ctx_switch_entry.

Section virtualise.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}
    {CSL : ContextSwitchLayout Σ CL CR}.

  (** * A thread's WP at the base's invariants *)

  (** One step of thread [th]'s WP from a non-value, its updates and credit
      at the base's [cb_invG]. *)
  Lemma thread_wp_step th (e : thread_langs.expr (kind_of th)) Φ σ :
    thread_langs.to_val e = None →
    WP e @[th] {{ Φ }} -∗
    thread_si th σ
    ={⊤,∅}=∗
    ⌜reducible (Λ := tlang (kind_of th)) e σ⌝ ∗
    ∀ e2 σ2,
      ⌜prim_step (l := tlang (kind_of th)) e σ [] e2 σ2 []⌝ -∗
      £ 1 -∗
      |={∅}▷=> |={∅,⊤}=> thread_si th σ2 ∗ WP e2 @[th] {{ Φ }}.
  Proof.
    iIntros (Hv) "Hwp Hsi". rewrite wp_unfold /wp_pre /= Hv.
    iMod ("Hwp" $! σ 0%nat [] [] 0%nat with "Hsi") as "[$ Hwp]". iModIntro.
    iIntros (e2 σ2 Hs) "Hc". iMod ("Hwp" $! e2 σ2 [] Hs with "Hc") as "Hwp".
    iModIntro. iNext. iMod "Hwp". iModIntro. iMod "Hwp" as "($ & $ & _)". done.
  Qed.

  (** A switch value of thread [th]'s WP: its postcondition, at the
      base's [cb_invG]. *)
  Lemma thread_wp_switch th s :
    WP (Instr (TSw s) : thread_langs.expr (kind_of th)) @[th] {{ HO th }}
    ={⊤}=∗
    HO th (TSwV s).
  Proof. iIntros "Hwp". rewrite wp_unfold /wp_pre /=. done. Qed.

  (** * The induction *)

  (** The premise of [hw_goal_wp] at the state [σ]. *)
  #[local] Definition hw_goal (h : griotte_lang.expr) (σ : ExecConf) : iProp Σ :=
    |={⊤,∅}=>
    ⌜reducible (Λ := griotte_hw_lang) h σ⌝ ∗
    ∀ e2 σ2,
      ⌜prim_step (l := griotte_hw_lang) h σ [] e2 σ2 []⌝ -∗
      £ 2 -∗
      |={∅}▷=>^2 |={∅,⊤}=> SI_hw σ2 ∗ WP_hw e2 {{ _, True }}.

  (** The induction predicate: [virtualise] for any running thread. *)
  #[local] Definition virt_pre (ts : list nat) : iProp Σ :=
    ∀ th (e : thread_langs.expr (kind_of th)) (k : nat),
      ⌜k ≤ 2⌝ -∗
      ⌜wellshaped e⌝ -∗
      ⌜k = 0 ∨ thread_langs.to_val e = None⌝ -∗
      inv Npool (Pool ts) -∗
      □ ctx_switch_entry_specs -∗
      thread_res th e -∗
      ▷^k WP e @[th] {{ HO th }} -∗
      WP_hw (hw_of e) {{ _, True }}.

  (** One hardware step from a non-value of the running thread [th]: an
      ordinary step is a step of [th]; an interrupt parks [th] and switches
      to the context-switch thread; a tick changes nothing. *)
  Lemma virt_step ts th (e : thread_langs.expr (kind_of th)) k σ :
    NoDup ts →
    (∀ B, mtdc_home_at (th := UserThread B) ≠ mtdc_home_at (th := CtxSwitch)) →
    k ≤ 2 →
    wellshaped e →
    thread_langs.to_val e = None →
    ▷ virt_pre ts -∗
    inv Npool (Pool ts) -∗
    □ ctx_switch_entry_specs -∗
    thread_res th e -∗
    ▷^k WP e @[th] {{ HO th }} -∗
    SI_hw σ -∗
    hw_goal (hw_of e) σ.
  Proof.
    iIntros (Hnd Hhomes Hk Hws Hv) "IH #Hinv #Hspec [Hrf Htr] Hwp Hσ".
    iDestruct (bi.laterN_le k 2 with "Hwp") as "Hwp"; first lia.
    rewrite /hw_goal.
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit; first (iPureIntro; by apply hw_of_reducible).
    iIntros (e2 σ2 Hst) "Hc".
    (* The two laters of the step: the induction's and the WP's. *)
    iModIntro. iNext. iModIntro. iModIntro. iNext. iModIntro.
    iMod "Hclose" as "_".
    destruct (hw_prim_step_inv _ _ _ _ _ _ Hst) as (_ & _ & [Hcore|(Hh & -> & Hasync)]).
    - (* An ordinary step: a step of the running thread, one credit for its
         step, one to strip its later. *)
      iDestruct (SI_hw_running th σ with "Hσ Hrf") as "(Hrun & Hwin & Hsi & Hidle & Hrf)".
      iMod (thread_wp_step th e _ σ Hv with "Hwp Hsi") as "[%Hred Hwp]".
      destruct (sim_b _ e σ e2 σ2 Hws Hred Hcore) as (e'' & Hs'' & <-).
      iDestruct (lc_split 1 1 with "Hc") as "[Hc1 Hc2]".
      iMod ("Hwp" $! e'' σ2 Hs'' with "Hc1") as "Hwp".
      iMod (lc_fupd_elim_later with "Hc2 Hwp") as "Hwp".
      iMod "Hwp". iMod "Hwp" as "[Hsi Hwp]".
      iAssert (|==> resume_window_si th σ2 ∗ thread_res th e'')%I
        with "[Hwin Hrf Htr]" as ">[Hwin Htr]".
      { iDestruct "Htr" as (w) "[Hwf Htr]". destruct th as [t|].
        - iDestruct "Hwin" as (w0) "[Hwa _]". iModIntro. iSplitL "Hwa".
          + iExists w0. iFrame "Hwa". iPureIntro. discriminate.
          + iFrame "Hrf". iExists w. iFrame "Hwf Htr".
        - iMod (resume_window_ctx_step e e'' σ [] σ2 [] w Hws Hs'' with "Hwin Hwf Htr")
            as (w') "(Hwin & Hwf & Htr)".
          iModIntro. iFrame "Hwin Hrf". iExists w'. iFrame "Hwf Htr". }
      iModIntro. iSplitR "IH Htr Hwp".
      { iExists th. iFrame "Hrun Hwin Hsi Hidle". }
      iApply ("IH" $! th e'' 0%nat with "[%] [%] [%] Hinv Hspec Htr Hwp").
      + lia.
      + by eapply wellshaped_step.
      + by left.
    - pose proof (hw_exec_thread e Hws Hv Hh) as ->.
      inversion Hasync as [σ0 c Hc Hen|σ0]; subst σ0 σ2.
      + (* An interrupt: the thread's WP is parked, not unfolded. *)
        iDestruct "Htr" as (w) "[Hwf Htr]".
        destruct th as [t|]; last first.
        { (* The context-switch thread is not interrupted: outside its
             switch window, its interrupts are disabled. *)
          iDestruct "Hσ" as (th_r) "Hσ". iNamed "Hσ".
          iDestruct (running_agree th_r CtxSwitch with "Hrun Hrf") as %->.
          iDestruct "Hwin" as (w0) "[Hwa %Hw0]".
          iDestruct (resume_window_agree with "Hwa Hwf") as %<-.
          iDestruct "Htr" as %Htr. exfalso. destruct w0.
          - by destruct (Htr eq_refl).
          - apply irq_enabled_mie_st' in Hen. by rewrite (Hw0 eq_refl eq_refl) in Hen. }
        iDestruct (SI_hw_running (UserThread t) σ with "Hσ Hrf")
          as "(Hrun & Hwin & Hsi & Hidle & Hrf)".
        apply irq_enabled_mie_st' in Hen.
        iMod (irq_hand_in t σ c Hen with "Hsi Hidle") as (lpc lreg) "H". iNamed "H".
        iDestruct (thread_si_mie_st CtxSwitch _ InterruptDisabled with "Hsi HMIE") as %Hdis.
        iMod (pool_save ts t ParkIrq (ResumeVals lreg lpc InterruptEnabled) ⊤ Hnd
                with "Hinv Htr [Hauths Hwp]") as "Hcur"; first solve_ndisj.
        { rewrite /slot /park_cont. iFrame "Hauths". iApply bi.later_intro. iExact "Hwp". }
        iMod (switch_ghosts (UserThread t) CtxSwitch σ (enter_irq c σ) w (λ _, Hdis)
                with "Hrun Hrf Hwin Hwf") as "(Hrun & Hrf & Hwin & Hwf)".
        iDestruct ("Hspec" $! t ParkIrq (ResumeVals lreg lpc InterruptEnabled)
          with "[HPC Hregs HMIE Hmtdc Hposture Hsched Hna Hclose Hcur]") as "Hctx".
        { rewrite /ctx_switch_entry_pre /parked_thread_res. cbn [rv_pc rv_regs rv_mie].
          iFrame "HPC HMIE Hmtdc Hregs Hcur Hsched Hna Hclose". iSplit; first done.
          iExists c. iFrame "Hposture". done. }
        iModIntro. iSplitR "IH Hrf Hwf Hctx".
        { iExists CtxSwitch. iFrame "Hrun Hwin Hsi". }
        iApply ("IH" $! CtxSwitch Exec 0%nat with "[%] [%] [%] Hinv Hspec [Hrf Hwf] Hctx").
        * lia.
        * left. by eexists.
        * by left.
        * iFrame "Hrf". iExists false. iFrame "Hwf". done.
      + (* A tick: the thread's WP is not unfolded. *)
        iModIntro. iSplitL "Hσ"; first by iApply SI_hw_tick.
        iApply ("IH" $! th Exec 0%nat with "[%] [%] [%] Hinv Hspec [Hrf Htr] Hwp").
        * lia.
        * done.
        * by left.
        * iFrame "Hrf Htr".
  Qed.

  (** The induction: a thread at a switch value hands over to the next
      thread before the next hardware step, by ghost updates at mask [⊤]. *)
  Lemma virt_all ts :
    NoDup ts →
    (∀ B, mtdc_home_at (th := UserThread B) ≠ mtdc_home_at (th := CtxSwitch)) →
    ⊢ virt_pre ts.
  Proof.
    intros Hnd Hhomes. iLöb as "IH".
    iIntros (th e k Hk Hws Hkv) "#Hinv #Hspec Htr Hwp".
    destruct (thread_langs.to_val e) as [v|] eqn:Hv; last first.
    { iApply hw_goal_wp; first by apply hw_of_not_val.
      iIntros (σ) "Hσ".
      iApply (virt_step ts th e k σ Hnd Hhomes Hk Hws Hv with "IH Hinv Hspec Htr Hwp Hσ"). }
    destruct Hkv as [->|Hn]; last congruence.
    apply tof_to_val in Hv as <-.
    destruct v as [| | |s].
    (* Halted, faulted, or at the next instruction: the hardware is at a
       value; [HO] is dropped. *)
    1-3: iClear "Hwp"; rewrite wp_unfold /wp_pre /=; by iModIntro.
    (* A switch: ghost updates at [⊤], before the next hardware step. *)
    iApply hw_goal_wp; first done.
    iIntros (σ) "Hσ". iMod (thread_wp_switch th s with "Hwp") as "HO".
    iDestruct "Htr" as "[Hrf Htr]". iDestruct "Htr" as (w) "[Hwf Htr]".
    iDestruct (SI_hw_running th σ with "Hσ Hrf") as "(Hrun & Hwin & Hsi & Hidle & Hrf)".
    destruct th as [t|]; destruct s.
    - (* YieldV: t is parked as Saving (ParkYield b p). *)
      rewrite HO_yield. iDestruct "HO" as "[_ Hyield]".
      iMod (yield_hand_in t σ with "Hsi Hyield Hidle") as (b p lreg) "H". iNamed "H".
      iDestruct (thread_si_mie_st CtxSwitch _ InterruptDisabled with "Hsi HMIE") as %Hdis.
      iMod (pool_save ts t (ParkYield b p)
              (ResumeVals lreg (lword_of_word mtcc_vec) InterruptDisabled) ⊤ Hnd
              with "Hinv Htr [Hauths Hcont]") as "Hcur"; first solve_ndisj.
      { rewrite /slot. iFrame "Hauths Hcont". }
      iMod (switch_ghosts (UserThread t) CtxSwitch σ σ w (λ _, Hdis)
              with "Hrun Hrf Hwin Hwf") as "(Hrun & Hrf & Hwin & Hwf)".
      iDestruct ("Hspec" $! t (ParkYield b p)
                   (ResumeVals lreg (lword_of_word mtcc_vec) InterruptDisabled)
        with "[HPC Hregs HMIE Hmtdc Hposture HMIE_t HPC_t Hsched Hna Hclose Hcur]") as "Hctx".
      { rewrite /ctx_switch_entry_pre /parked_thread_res. cbn [rv_pc rv_regs rv_mie].
        iFrame "HPC HMIE Hmtdc Hregs Hcur Hsched Hna Hclose Hposture HMIE_t HPC_t".
        iSplit; done. }
      iApply (virt_step ts CtxSwitch Exec 0%nat σ Hnd Hhomes with
                "IH Hinv Hspec [Hrf Hwf] Hctx [Hrun Hwin Hsi]").
      + lia.
      + left. by eexists.
      + done.
      + iFrame "Hrf". iExists false. iFrame "Hwf". done.
      + iExists CtxSwitch. iFrame "Hrun Hwin Hsi".
    - (* ExitV: t is parked as Saving ParkExit; its WP is over, and no pool
         token of t is needed. *)
      rewrite HO_exit. iDestruct "HO" as "[_ Hexit_b]".
      iMod (exit_hand_in t σ with "Hsi Hexit_b Hidle") as (lpc lreg) "H". iNamed "H".
      iDestruct (thread_si_mie_st CtxSwitch _ InterruptDisabled with "Hsi HMIE") as %Hdis.
      iMod (pool_save ts t ParkExit (ResumeVals lreg lpc InterruptDisabled) ⊤ Hnd
              with "Hinv Htr [Hauths]") as "Hcur"; first solve_ndisj.
      { rewrite /slot /park_cont. iFrame "Hauths". }
      iMod (switch_ghosts (UserThread t) CtxSwitch σ σ w (λ _, Hdis)
              with "Hrun Hrf Hwin Hwf") as "(Hrun & Hrf & Hwin & Hwf)".
      iDestruct ("Hspec" $! t ParkExit (ResumeVals lreg lpc InterruptDisabled)
        with "[HPC Hregs HMIE Hmtdc Hposture HMIE_t Hregs_t Hexit Hsched Hna Hclose Hcur]")
        as "Hctx".
      { rewrite /ctx_switch_entry_pre /parked_thread_res. cbn [rv_pc rv_regs rv_mie].
        iFrame "HPC HMIE Hmtdc Hregs Hcur Hsched Hna Hclose Hposture HMIE_t Hregs_t Hexit".
        iSplit; done. }
      iApply (virt_step ts CtxSwitch Exec 0%nat σ Hnd Hhomes with
                "IH Hinv Hspec [Hrf Hwf] Hctx [Hrun Hwin Hsi]").
      + lia.
      + left. by eexists.
      + done.
      + iFrame "Hrf". iExists false. iFrame "Hwf". done.
      + iExists CtxSwitch. iFrame "Hrun Hwin Hsi".
    - (* A user thread does not resume another. *)
      by iDestruct (HO_user_resumed with "HO") as "[]".
    - (* The context-switch thread neither yields nor exits. *)
      by iDestruct (HO_ctx_yield with "HO") as "[]".
    - by iDestruct (HO_ctx_exit with "HO") as "[]".
    - (* ResumedV: B is resumed, and runs after its stored later. *)
      rewrite HO_resumed. iDestruct "HO" as "[_ Hres]".
      iDestruct "Hres" as (B v) "Hres". iNamed "Hres".
      iMod (pool_run ts B v ⊤ Hnd with "Hinv Hcur") as "[Hcur Hauths]"; first solve_ndisj.
      iClear "Hidle Htr".
      iMod (resumed_hand_back B v σ (Hhomes B) with
              "Hsi [//] Hregs HPC HMIE Hmtdc Hpart Hsched Hna Hclose Hauths") as "[Hsi Hidle]".
      iMod (switch_ghosts CtxSwitch (UserThread B) σ σ w (λ H, ltac:(discriminate H))
              with "Hrun Hrf Hwin Hwf") as "(Hrun & Hrf & Hwin & Hwf)".
      iEval (rewrite safe_unfold) in "Hsafe".
      iApply (virt_step ts (UserThread B) Exec 1%nat σ Hnd Hhomes with
                "IH Hinv Hspec [Hrf Hwf Hcur] Hsafe [Hrun Hwin Hsi Hidle]").
      + lia.
      + left. by eexists.
      + done.
      + iFrame "Hrf". iExists false. iFrame "Hwf Hcur".
      + iExists (UserThread B). iFrame "Hrun Hwin Hsi Hidle".
  Qed.

  (** The hardware runs safely from the running thread's safe run: each
      thread's WP over its thread language, the pool of the user threads,
      and the entry specs of the context-switch thread give one WP over the
      hardware language. *)
  Theorem virtualise (ts : list nat) (th : Thread)
      (e : thread_langs.expr (kind_of th)) (k : nat) :
    NoDup ts →
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    (∀ t, ∃ p b e' a, mtdc_home_at (th := UserThread t) = TStack p b e' a) →
    k ≤ 2 →
    wellshaped e →
    k = 0 ∨ thread_langs.to_val e = None →
    inv Npool (Pool ts) -∗
    □ ctx_switch_entry_specs -∗
    thread_res th e -∗
    ▷^k WP e @[th] {{ HO th }} -∗
    WP_hw (hw_of e) {{ _, True }}.
  Proof.
    iIntros (Hnd Hs Hus Hk Hws Hkv) "#Hinv #Hspec Htr Hwp".
    iApply (virt_all ts Hnd (λ B, homes_differ B Hs (Hus B)) $! th e k
              with "[%] [%] [%] Hinv Hspec Htr Hwp"); done.
  Qed.

End virtualise.
