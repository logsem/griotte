From iris.proofmode Require Import proofmode.
From griotte Require Import logrel switcher_preamble handoff pool.
From griotte Require Import context_switch_layout_instance ctx_support.

(** * The hypotheses of the context-switch thread's paths

    The scheduler's words in the switcher's data, the validity of its
    entry and globals, the safety of the trap vector for a fault of the
    context-switch thread, the scheduler's state between two activations,
    the safety of the return from the scheduler, and the premises that the
    paths of the context-switch thread share. *)

Section ctx_switch.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    (C_sched : CmptName) (w_pcc w_cgp w_csp : LWord).

  (** The scheduler's words of the switcher: its entry, globals and stack,
      none of them a heap capability (a load of one may clear its tag). *)
  Definition scheduler_words : iProp Σ :=
    (b_switcher ^+ 2)%a ↦ₐ□ w_pcc ∗
    (b_switcher ^+ 3)%a ↦ₐ□ w_cgp ∗
    (b_switcher ^+ 4)%a ↦ₐ□ w_csp ∗
    ⌜is_heap_cap w_pcc.(lw) = false ∧ is_heap_cap w_cgp.(lw) = false ∧
     is_heap_cap w_csp.(lw) = false⌝.

  (** The scheduler: its entry capability, and its globals, are valid at
      the context-switch thread in its compartment, in every world. *)
  Definition scheduler_entry_valid : iProp Σ :=
    □ ∀ W : WORLD, interp (th := CtxSwitch) W C_sched w_pcc ∗ interp (th := CtxSwitch) W C_sched w_cgp.

  (** The trap vector is safe for any fault of the context-switch thread. *)
  Definition ctx_trap_vector_safe : iProp Σ :=
    trap_vector_safe (th := CtxSwitch) (λ _ _ _, True%I) (lword_of_word mtcc_vec).

  (** The scheduler's state between two activations: its world, its call
      stack, its continuation, and its stack valid in that world. *)
  Definition scheduler_concrete : iProp Σ :=
    ∃ (W : WORLD) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName),
      "Hworld" ∷ world_resources (th := CtxSwitch) W C_sched ∗
      "Hcred" ∷ shared_credit C_sched ∗
      "Hcstk" ∷ ◯(CSTK)[CtxSwitch] cstk ∗
      "Hcont" ∷ interp_continuation (th := CtxSwitch) cstk Ws Cs ∗
      "%Hframe" ∷ ⌜frame_match Ws Cs cstk W C_sched⌝ ∗
      "#Htop" ∷ top_cmpt_untrusted (th := CtxSwitch) (interp (th := CtxSwitch)) W C_sched cstk ∗
      "#Hcsp" ∷ interp (th := CtxSwitch) W C_sched w_csp.

  (** The PC of the return from the scheduler, and its sentry. *)
  Definition ctx_resume_pc : LWord :=
    lword_of_word (Cap XSRW_ Local b_switcher e_switcher a_sched_return).
  Definition ctx_resume_sentry : LWord :=
    lword_of_word (Sentry RetDisable XSRW_ Local b_switcher e_switcher a_sched_return).

  (** The return from the scheduler is safe in the public futures of the
      world [W0] of the call. *)
  Definition ctx_resume_spec (W0 : WORLD) : iProp Σ :=
    ∀ W : WORLD, ⌜related_sts_pub_world W0 W⌝ →
      interp_expr_at (th := CtxSwitch) InterruptDisabled (interp (th := CtxSwitch))
        (interp_continuation (th := CtxSwitch)) W C_sched ctx_resume_pc.

  (** In every call's world [W0] where the scheduler's stack is valid. *)
  Definition ctx_resume_specs : iProp Σ :=
    □ ∀ W0 : WORLD, interp (th := CtxSwitch) W0 C_sched w_csp -∗ ctx_resume_spec W0.

  (** The open pool token of the context-switch thread. *)
  Definition inv_CtxSwitch : iProp Σ := na_inv (tpool CtxSwitch) Nact (cur_frag None).

  (** What the context-switch thread's paths use besides its entry. *)
  Definition ctx_switch_env (ts : list nat) : iProp Σ :=
    "%Hnd" ∷ ⌜NoDup ts⌝ ∗
    "%Hts" ∷ ⌜∀ B, B ∈ ts ↔ B < swl_nthreads⌝ ∗
    "%Hhome_ctx" ∷ ⌜mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0))⌝ ∗
    "%Hhomes" ∷ ⌜∀ B, B ∈ ts → mtdc_home_at (th := UserThread B) = tstack_home B⌝ ∗
    "%Hsched_in" ∷ ⌜CtxSwitch ∈ cmpt_threads C_sched⌝ ∗
    "#Hpool" ∷ inv Npool (Pool ts) ∗
    "#Hact" ∷ inv_CtxSwitch ∗
    "#Hstatic" ∷ ([∗ list] B ∈ ts, switcher_static (th := UserThread B)) ∗
    "#Hwords" ∷ scheduler_words ∗
    "#Hsched" ∷ saved_prop_own γ_sched DfracDiscarded scheduler_concrete ∗
    "#Hentry" ∷ scheduler_entry_valid ∗
    "#Htrap" ∷ ctx_trap_vector_safe.

  (** A trusted stack sealed with the trusted-stack otype is valid at the
      context-switch thread in any compartment and world. *)
  Lemma tstack_handle_sealed_valid (W : WORLD) (C : CmptName) (g : Locality) (B : nat) :
    B < swl_nthreads →
    switcher_static (th := UserThread B) -∗
    interp (th := CtxSwitch) W C
      (lword_of_word (Sealed ot_trusted_stacks RWL g
         (@b_trusted_stack (tlayout_of (UserThread B))) (@e_trusted_stack (tlayout_of (UserThread B)))
         (@b_trusted_stack (tlayout_of (UserThread B))))).
  Proof.
    iIntros (HB) "#Hstatic".
    iEval (rewrite /switcher_static) in "Hstatic". iNamed "Hstatic".
    iEval (rewrite /switcher_sealing_inv) in "Hswitcher_sealing". iNamed "Hswitcher_sealing".
    iApply (interp_sb_intro_global (th := CtxSwitch) W C ot_trusted_stacks tstack_handle_propC
             with "[] Hp_ot_tstacks").
    { iApply tstack_handle_kind_ok. }
    - iNext. iPureIntro. exists B. split; first done. reflexivity.
    - rewrite /sealed_payload_ok /heap_cap_ok /=. iIntros "_". iPureIntro.
      apply (trusted_stack_disjoint_from_heap (tlayout := tlayout_of (UserThread B))).
  Qed.

  (** The return sentry of the scheduler is valid in the world [W0] of the
      call, where the scheduler's stack is valid. *)
  Lemma ctx_resume_sentry_valid (W0 : WORLD) :
    interp (th := CtxSwitch) W0 C_sched w_csp -∗
    □ ctx_resume_spec W0 -∗
    interp (th := CtxSwitch) W0 C_sched ctx_resume_sentry.
  Proof.
    iIntros "_ #Hspec".
    rewrite /ctx_resume_sentry interp_unfold /=.
    iSplit; first (iPureIntro; apply switcher_not_heap_range).
    iSplit.
    - iIntros "!> %W %Hfut %g' %Hflow %m".
      destruct g'; first done.
      iNext. iApply ("Hspec" $! W with "[//]").
    - iPureIntro. intros Hk. discriminate Hk.
  Qed.

  (** The scheduler's entry leaves interrupts disabled: a tagged sentry that
      enables them is not valid in a compartment of the context-switch
      thread. *)
  Lemma sched_entry_disabled :
    CtxSwitch ∈ cmpt_threads C_sched →
    get_tag w_pcc.(lw) = true →
    scheduler_entry_valid -∗
    ⌜default InterruptDisabled (jalr_target_mie w_pcc.(lw)) = InterruptDisabled⌝.
  Proof.
    iIntros (Hin Htag) "#Hentry".
    iDestruct ("Hentry" $! ∅) as "[Hpcc _]".
    destruct w_pcc as [w π]; cbn in Htag |- *.
    destruct_word w; cbn; try done.
    cbn in Htag. subst t.
    iEval (rewrite interp_unfold /=) in "Hpcc".
    iDestruct "Hpcc" as "(_ & _ & %Hclause)".
    iPureIntro. destruct (sentry_kind_mie k) as [ [|] |] eqn:Hk; cbn; try done.
    exfalso. by apply Hclause.
  Qed.

End ctx_switch.
