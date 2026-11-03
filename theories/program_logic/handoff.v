From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra instr_operands.
From griotte Require Export posture.

(** * The handoff of a thread's turn

    [cur], the postcondition [HO] of a thread's run, a guarded fixpoint
    with the safe run [safe], and the context-switch thread's resources
    while another thread runs ([idle_CtxSwitch]). The switcher's parts of
    [HO] (the exit part of a user thread, the scheduler's state) are saved
    propositions, named in the base. *)

Definition Npool : namespace := nroot .@ "pool".
Definition Nact : namespace := nroot .@ "act".

(** The share of the PC fragment that a resumed context-switch thread
    holds: a half at InterruptEnabled, the other half in its interrupt
    clause. *)
Definition pc_dq (b : InterruptStatus) : dfrac :=
  if b is InterruptEnabled then DfracOwn (1/2) else DfracOwn 1.

(** The PC that a yielded thread resumes at: the instruction after its
    [ecall]. *)
Definition yield_resume_pc (p : LWord) : LWord := default p (incrementPC p).

(** The PC after an environment call at a capability is a capability with
    the same permission, locality and bounds. *)
Lemma yield_resume_pc_cap p g b e a :
  ∃ a', yield_resume_pc (Cap p g b e a) = Cap p g b e a'.
Proof.
  rewrite /yield_resume_pc /incrementPC /incrementPC_gen /=.
  destruct (a + 1)%a as [a'|]; eauto.
Qed.

Section cur.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}.

  Definition cur_auth (c : option (Thread * TState)) : iProp Σ :=
    own cb_cur_name (●E (c : leibnizO _)).
  Definition cur_frag (c : option (Thread * TState)) : iProp Σ :=
    own cb_cur_name (◯E (c : leibnizO _)).

  #[global] Instance cur_auth_timeless c : Timeless (cur_auth c).
  Proof. apply _. Qed.
  #[global] Instance cur_frag_timeless c : Timeless (cur_frag c).
  Proof. apply _. Qed.

  Lemma cur_agree c c' : cur_auth c -∗ cur_frag c' -∗ ⌜c = c'⌝.
  Proof. iIntros "Ha Hf". iCombine "Ha Hf" gives %Hv. by apply excl_auth_agree_L in Hv. Qed.

  Lemma cur_update c c' c'' : cur_auth c -∗ cur_frag c' ==∗ cur_auth c'' ∗ cur_frag c''.
  Proof.
    iIntros "Ha Hf". iMod (own_update_2 with "Ha Hf") as "[$ $]"; last done.
    apply excl_auth_update.
  Qed.

  (** The exit part of a user thread: a saved proposition, made concrete by
      the switcher's exit path. *)
  Definition exit_part (th : Thread) : iProp Σ :=
    ∃ P : iProp Σ, saved_prop_own (γ_exit th) DfracDiscarded P ∗ ▷ P.

  (** The scheduler's state between two activations: a saved proposition,
      made concrete by the switcher. *)
  Definition sched_state : iProp Σ :=
    ∃ P : iProp Σ, saved_prop_own γ_sched DfracDiscarded P ∗ ▷ P.

  (** The closer of the context-switch thread's open pool token. *)
  Definition close_Nact : iProp Σ :=
    ▷ cur_frag None ∗ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact)
    ={⊤}=∗
    na_own (tpool CtxSwitch) ⊤.
End cur.

(** One thread's authorities, home value and mtdc token, at the instance of
    the thread: take them at another thread with [(th := …)]. *)
Section thread_parts.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread}.

  Definition thread_auths (lpc : LWord) (lreg : LReg) (m : mtdc_val) (mie : InterruptStatus)
    : iProp Σ :=
    PC_auth lpc ∗ gen_heap_interp lreg ∗ mtdc_auth m ∗ MIE_auth mie.
  Definition mtdc_home_at : mtdc_val := mtdc_home.
  Definition mtdc_lent_at : iProp Σ := mtdc_lent.
End thread_parts.

Section handoff.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}.
  Notation TV := (Thread -d> iPropO Σ).

  (* The thread [x] below is bound, not a section variable: every instance
     is given. The notation variable is not [th], which is also an argument
     name. *)
  #[local] Notation posture_of x :=
    (posture_res_gen (ceriseg := ceriseG_of x) (th := x) (CL := CL x) (CR := CR x)).
  #[local] Notation held_th x :=
    (held (ceriseg := ceriseG_of x) (th := x) (CL := CL x) (CR := CR x)).

  (** [YieldV]: the whole posture with mcause 11, MIE disabled, the PC at
      the trap vector; the continuation resumes after the [ecall]. *)
  Definition yield_body (S : TV) (th : Thread) : iProp Σ :=
    ∃ (b : InterruptStatus) (p : LWord),
      posture_of th (Some b) (Some p) (Some (lword_of_word (WInt MCAUSE_ECALL_MACHINE))) None ∗
      MIE ↦ₜ[th] InterruptDisabled ∗
      PC ↦ₚ[th] lword_of_word mtcc_vec ∗
      ▷ (MIE ↦ₜ[th] b -∗
         PC ↦ₚ[th] yield_resume_pc p -∗
         held_th th b -∗
         S th).

  (** [ExitV]: MIE disabled, the posture with mcause 24, a total register
      map, and the exit part. *)
  Definition exit_body (th : Thread) : iProp Σ :=
    MIE ↦ₜ[th] InterruptDisabled ∗
    posture_of th None None (Some (lword_of_word (WInt MCAUSE_THREAD_EXIT))) None ∗
    (∃ lreg : LReg, ⌜dom lreg = all_registers_s⌝ ∗ regs[th] lreg) ∗
    exit_part th.

  (** [ResumedV] of the context-switch thread: [B] is Resuming with [v];
      the thread's fragments at [v] (its mtdc at B's home), B's posture
      part at InterruptEnabled, the scheduler's state, the open pool token
      with its closer, and B's run. *)
  Definition resumed_body (S : TV) : iProp Σ :=
    ∃ (B : nat) (v : resume_vals),
      "Hcur" ∷ cur_frag (Some (UserThread B, Resuming v)) ∗
      "%Hdom" ∷ ⌜dom v.(rv_regs) = all_registers_s⌝ ∗
      "Hregs" ∷ regs[CtxSwitch] v.(rv_regs) ∗
      "HPC" ∷ @PC_fragq Σ (@cerise_pcG Σ (ceriseG_of CtxSwitch)) (pc_dq v.(rv_mie)) v.(rv_pc) ∗
      "HMIE" ∷ MIE ↦ₜ[CtxSwitch] v.(rv_mie) ∗
      "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread B)) ∗
      "Hpart" ∷ (if v.(rv_mie) is InterruptEnabled
                 then @posture_part Σ MP (ceriseG_of (UserThread B)) (UserThread B)
                        (CL (UserThread B)) (CR (UserThread B))
                 else True) ∗
      "Hsched" ∷ sched_state ∗
      "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
      "Hclose" ∷ close_Nact ∗
      "Hsafe" ∷ ▷ S (UserThread B).

  Definition HO_pre (S : TV) (th : Thread) (v : tval (kind_of th)) : iProp Σ :=
    match v with
    | HaltedV => na_own (tpool th) ⊤
    | FaultedV | NextIV => True
    | YieldV => ⌜th ≠ CtxSwitch⌝ ∗ yield_body S th
    | ExitV => ⌜th ≠ CtxSwitch⌝ ∗ exit_body th
    | ResumedV => ⌜th = CtxSwitch⌝ ∗ resumed_body S
    end%I.

  Definition safe_pre (S : TV) : TV := λ th, (WP Exec @[th] {{ HO_pre S th }})%I.

  (** [solve_contractive] alone fails on the match over the value: the
      value is destructed first. *)
  #[global] Instance safe_pre_contractive : Contractive safe_pre.
  Proof.
    intros n S1 S2 HS th. rewrite /safe_pre. f_equiv. intros v.
    destruct v as [| | |[ | | ] ]; cbn [HO_pre]; try reflexivity.
    - (* YieldV *) f_equiv. rewrite /yield_body. solve_contractive.
    - (* ResumedV *) f_equiv. rewrite /resumed_body. solve_contractive.
  Qed.

  Definition safe : TV := fixpoint safe_pre.

  Definition HO (th : Thread) : tval (kind_of th) → iProp Σ := HO_pre safe th.

  (** The context-switch thread while another thread runs: its authorities
      and fragments with a total register map, its mtdc token, the
      scheduler's state, and its open pool token with the closer. *)
  Definition idle_CtxSwitch : iProp Σ :=
    ∃ (lpc : LWord) (lreg : LReg) (m : mtdc_val) (mie : InterruptStatus),
      "%Hdom" ∷ ⌜dom lreg = all_registers_s⌝ ∗
      "Hauths" ∷ thread_auths (th := CtxSwitch) lpc lreg m mie ∗
      "HPC" ∷ PC ↦ₚ[CtxSwitch] lpc ∗
      "Hregs" ∷ regs[CtxSwitch] lreg ∗
      "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] m ∗
      "HMIE" ∷ MIE ↦ₜ[CtxSwitch] mie ∗
      "Hlent" ∷ mtdc_lent_at (th := CtxSwitch) ∗
      "Hsched" ∷ sched_state ∗
      "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
      "Hclose" ∷ close_Nact.
End handoff.

(* A WP with postcondition [HO th] prints as [{{ HO th }}], not η-expanded
   by the notations with a binder. *)
Notation "'WP' e '@[' th ] E {{ 'HO' th' } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th)))
     NotStuck E e%E (HO th'))
  (at level 20, th custom thread, th' at level 0, e at level 200, only printing,
   format "'[hv' 'WP'  e  '/' '@[' th ]  E  '/' {{  HO  th'  } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] {{ 'HO' th' } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th)))
     NotStuck ⊤ e%E (HO th'))
  (at level 20, th custom thread, th' at level 0, e at level 200, only printing,
   format "'[hv' 'WP'  e  '/' '@[' th ]  '/' {{  HO  th'  } } ']'") : bi_scope.

(** A safe run of thread [th]: its WP with postcondition [HO th]. *)
Notation "'safe[' th ]" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th)))
     NotStuck ⊤
     Exec (HO th))
  (at level 20, th custom thread, format "'safe[' th ]") : bi_scope.

Section handoff_lemmas.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}.

  Lemma safe_unfold th : safe th ⊣⊢ safe[th].
  Proof. exact: (fixpoint_unfold safe_pre th). Qed.

  Lemma HO_halted th : HO th HaltedV ⊣⊢ na_own (tpool th) ⊤.
  Proof. done. Qed.
  Lemma HO_faulted th : HO th FaultedV ⊣⊢ True.
  Proof. done. Qed.
  Lemma HO_next th : HO th NextIV ⊣⊢ True.
  Proof. done. Qed.
  Lemma HO_yield th : HO th YieldV ⊣⊢ ⌜th ≠ CtxSwitch⌝ ∗ yield_body safe th.
  Proof. done. Qed.
  Lemma HO_exit th : HO th ExitV ⊣⊢ ⌜th ≠ CtxSwitch⌝ ∗ exit_body th.
  Proof. done. Qed.
  Lemma HO_resumed th : HO th ResumedV ⊣⊢ ⌜th = CtxSwitch⌝ ∗ resumed_body safe.
  Proof. done. Qed.

  (** The unreachable pairs. *)
  Lemma HO_ctx_yield : HO CtxSwitch YieldV ⊢ False.
  Proof. rewrite HO_yield. by iIntros "[% _]". Qed.
  Lemma HO_ctx_exit : HO CtxSwitch ExitV ⊢ False.
  Proof. rewrite HO_exit. by iIntros "[% _]". Qed.
  Lemma HO_user_resumed t : HO (UserThread t) ResumedV ⊢ False.
  Proof. rewrite HO_resumed. by iIntros "[% _]". Qed.
End handoff_lemmas.
