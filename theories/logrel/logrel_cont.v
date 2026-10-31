From iris.proofmode Require Import proofmode.
From griotte Require Export logrel_conditions.
Import uPred.

(** interp : is a unary logical relation.

    The definitions that take the thread are in sections with a thread
    [th]; they are taken at another thread with [(th := t)]. The fixpoint
    [interp1] is over the family of the threads' relations, in a section
    without thread. The definitions about the trap vector are at the core
    link, the others at the section's link. *)
Section logrel_pre.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    `{MP: MachineParameters}
  .
  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Program Definition safeUC (P : WORLD * CmptName * leibnizO LWord → iPropO Σ) : V :=
    λne a b c, P (a, b, c).
  Solve All Obligations with solve_proper.

  (* -------------------------------------------------------------------------------- *)

  (** Future world relation: a Global word is valid in every world. *)
  Definition future_world (g : Locality) (W W' : WORLD) : iProp Σ :=
    (match g with
     | Local => ⌜related_sts_pub_world W W'⌝
     | Global => True
     end)%I.

  Lemma futureworld_refl (g : Locality) (W : WORLD) :
    ⊢ @future_world g W W.
  Proof.
    rewrite /future_world.
    destruct g; [done|]. iPureIntro. apply related_sts_pub_refl_world.
  Qed.

  #[global] Instance future_world_persistent (g : Locality) (W W' : WORLD) :
    Persistent (future_world g W W').
  Proof.
    unfold future_world. destruct g; apply bi.pure_persistent.
  Qed.

  (* interp expression definitions *)
  Definition registers_pointsto (r : LReg) : iProp Σ :=
    (regs[th] r)%I.

  Definition full_map (reg : LReg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  (** Each register is safe. *)
  Program Definition interp_reg (interp : V) : R :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO LReg),
      (full_map reg ∧
       ∀ (r : RegName) (v : LWord), (⌜reg !! r = Some v⌝ → interp W C v))%I.
  Solve All Obligations with solve_proper.
  #[global] Instance interp_reg_ne n : Proper (dist n ==> dist n) interp_reg.
  Proof. intros I1 I2 HI W C regs. cbn. repeat f_equiv. apply HI. Qed.

  (** [frame_match] expresses that the call stack [cstk], the stack of worlds [Ws] and compartments [Cs],
      match with the current world [W] and compartment [C].

      When the switcher pushes/pops a stack frame, it also pushes/pops
      the current world and compartment together.

      It is necessary because the continuation relation is monotonic with public
      transitions only.
      Without this feature, when a user receives a world [W]
      (and it's corresponding continuation relation) from a caller,
      calling the switcher requires to give a world [W'] together with the
      corresponding continuation relation.
      But because the continuation relation is monotonic with public transition only,
      it would forbid the user to take private transitions
      (which usually happen, because the user revokes the world for taking control
      of its own stack frame).

      With the [frame_match] criteria, the user can take private transition during
      the duration of their call, and calling the switcher pushed the world
      into the stack of world [Ws] (done by the switcher).
      When the user return, they have to show that they end up in a
      public future world [W'] of the caller's world [W].
      It has to be public transition (and not equality), because the world
      can evolve publicly during an adversary's call.

      Finally, this matching only happens within a "chain of untrusted calls",
      because as soon as we hit a trusted caller, the chain of public world
      can be broken by a private transition taken by the user
      (which they'll have to prove public when returning).

      The compartment's name is an equality, because untrusted (physical) compartments
      that can call each others are considered as a unique logical compartment.
   *)
  Fixpoint frame_match_l
    (Ws : list WORLD) (Cs : list CmptName) (frms : list cframe) (W : WORLD) (C : CmptName)
    : Prop :=
    match Ws,Cs,frms with
    | W' :: Ws', C' :: Cs', frm :: frms' =>
        related_sts_pub_world W' W
        ∧ C = C'
        ∧ is_known_to_known_frm frm = false
        ∧ (if (is_untrusted_caller_frm frm) then frame_match_l Ws' Cs' frms' W C else True)
    | [], [] , []=> True
    | _,_,_ => False
    end.

  (** The worlds [Ws] and compartments [Cs] match the frames pushed by the
      calls; the entry frame has none. *)
  Definition frame_match
    (Ws : list WORLD) (Cs : list CmptName) (cstk : CSTK) (W : WORLD) (C : CmptName)
    : Prop :=
    frame_match_l Ws Cs cstk.(cstk_frames) W C.
  #[global] Arguments frame_match _ _ _ _ _ /.

  Lemma frame_match_mono
    (Ws : list WORLD) (Cs : list CmptName) (cstk : CSTK) (W W' : WORLD) ( C : CmptName ) :
    related_sts_pub_world W W' ->
    frame_match Ws Cs cstk W C ->
    frame_match Ws Cs cstk W' C.
  Proof.
    rewrite /frame_match.
    generalize (cstk_frames cstk) as frms; clear cstk.
    intros frms; revert Ws Cs.
    induction frms as [|frm frms IHcstk]; intros Ws Cs Hrelated Hfrm.
    - destruct Ws,Cs; cbn in *; try done.
    - destruct Ws,Cs; cbn in *; try done.
      destruct Hfrm as (Hrelated' & <- & is_not_known_to_known & IHframe).
      split;[|split;[|split] ]; auto.
      + eapply related_sts_pub_trans_world; eauto.
      + destruct (is_untrusted_caller_frm frm); last done.
        by apply IHcstk.
  Qed.

  (** [entry_stack_interp interp W C ef]: the stack pointer that the entry
      frame [ef] holds, the thread's initial stack, is a capability without
      identifier, outside the heap, and safe in [W]. *)
  Definition entry_stack_interp (interp : V) (W : WORLD) (C : CmptName) (ef : trusted_frame)
    : iProp Σ :=
    ∃ (p : Perm) (g : Locality) (b e a : Addr),
      ⌜ef.(tf_csp) = lword_of_word (Cap p g b e a)⌝ ∗
      ⌜disjoint_from_heap b e⌝ ∗
      □ interp W C ef.(tf_csp).

  (** [top_cmpt_untrusted interp W C cstk] states that the compartment of the
      callee of the topmost frame of [cstk] (a pushed frame, or the entry
      frame when no frame is pushed) is untrusted: the PCC and the CGP of
      its export table are safe in every private future world of [W]. It
      also records the handler offsets of the header of that table, and that
      the frame's export table word is set (not [WInt 0]). When no frame is
      pushed, the thread started in that compartment, which holds the
      thread's stack: a stackless handler receives it at depth 0. *)
  Definition top_cmpt_untrusted (interp : V) (W : WORLD) (C : CmptName) (cstk : CSTK)
    : iProp Σ :=
    let tf := top_tframe cstk in
    let b_tbl := tf_export_tbl_b tf in
    let a_tbl_cgp := (b_tbl ^+ ExportTable_offset_cgp) in
    (∃ (pcc cgp : LWord) (eh ehs : Z),
       b_tbl ↦ₐ□ pcc ∗
       a_tbl_cgp ↦ₐ□ cgp ∗
       b_tbl ↦ₑ□{stackful} eh ∗
       b_tbl ↦ₑ□{stackless} ehs ∗
       (□ ∀ W', ⌜related_sts_priv_world W W'⌝ → interp W' C pcc ∗ interp W' C cgp) ∗
       ⌜tf.(tf_export_tbl) ≠ lword_of_word (WInt 0)⌝) ∗
    match cstk.(cstk_frames) with
    | [] => entry_stack_interp interp W C cstk.(cstk_entry)
    | _ :: _ => True
    end.

  #[global] Instance top_cmpt_untrusted_persistent interp W C cstk :
    Persistent (top_cmpt_untrusted interp W C cstk).
  Proof.
    rewrite /top_cmpt_untrusted /entry_stack_interp.
    destruct cstk as [ef [|frm frms] ]; apply _.
  Qed.

  #[global] Instance top_cmpt_untrusted_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) top_cmpt_untrusted.
  Proof.
    intros interp interp' Heq W ? <- C ? <- cstk ? <-.
    rewrite /top_cmpt_untrusted /entry_stack_interp.
    destruct cstk as [ef [|frm frms] ]; solve_proper.
  Qed.

  (** [top_cmpt_untrusted] does not read the count of the topmost frame. *)
  Lemma top_cmpt_untrusted_set_top_count interp (W : WORLD) (C : CmptName) (cstk : CSTK) (n : Z) :
    top_cmpt_untrusted interp W C (cstack_set_top_count cstk n) ⊣⊢
    top_cmpt_untrusted interp W C cstk.
  Proof. by destruct cstk as [ef [|frm frms] ]. Qed.

  (** A fault in an untrusted compartment, for the relation [interp] and
      the continuation [interp_cont]: the topmost frame's compartment is
      untrusted, the faulting registers are safe, and the logical
      relation's resources go to the trap vector. *)
  Definition untrusted_fault_pre (interp : V) (interp_cont : K)
      (cstk : CSTK) (regs : LReg) : iProp Σ :=
    ∃ (W : WORLD) (C : CmptName) (Ws : list WORLD) (Cs : list CmptName),
      ⌜frame_match Ws Cs cstk W C⌝ ∗
      interp_reg interp W C regs ∗
      top_cmpt_untrusted interp W C cstk ∗
      world_resources W C ∗
      shared_credit C ∗
      thread_in th C ∗
      interp_cont cstk Ws Cs.

  #[global] Instance untrusted_fault_pre_ne n :
    Proper (dist n ==> dist n ==> (=) ==> (=) ==> dist n) untrusted_fault_pre.
  Proof.
    intros interp interp' Heq K K' HK cstk ? <- regs ? <-.
    rewrite /untrusted_fault_pre. repeat f_equiv.
    all: try apply interp_reg_ne; try apply top_cmpt_untrusted_ne; try apply HK; done.
  Qed.

  (** The trap vector [wvec] is safe, at the core link: after trap entry
      from any PC [w], with any call stack [cstk] and registers [regs],
      execution from [wvec] is safe, for a fault in an untrusted compartment
      ([untrusted_fault_pre]) or a fault that [trusted_fault] accepts. Trap
      entry lends MEPCC, mcause and mtval to the trap vector
      ([trap_entry_out w]) and holds the trap-entry part [Ntrap] of the
      non-atomic token. *)
  Definition trap_vector_safe_pre (interp : V) (interp_cont : K)
      (trusted_fault : CSTK → LWord → LReg → iProp Σ) (wvec : LWord) : iProp Σ :=
    □ ∀ (cstk : CSTK) (regs : LReg) (w : LWord),
      ⌜∀ r, is_Some (regs !! r)⌝ -∗
      (untrusted_fault_pre interp interp_cont cstk regs ∨ trusted_fault cstk w regs) -∗
      PC ↦ₚ[th] wvec -∗
      trap_entry_out w -∗
      registers_pointsto regs -∗
      na_own (tpool th) (⊤ ∖ ↑Ntrap) -∗
      ◯(CSTK)[th] cstk -∗
      safe[th].

  #[global] Instance trap_vector_safe_pre_persistent interp interp_cont trusted_fault wvec :
    Persistent (trap_vector_safe_pre interp interp_cont trusted_fault wvec).
  Proof. rewrite /trap_vector_safe_pre. apply _. Qed.

  #[global] Instance trap_vector_safe_pre_ne n trusted_fault wvec :
    Proper (dist n ==> dist n ==> dist n)
      (λ interp interp_cont, trap_vector_safe_pre interp interp_cont trusted_fault wvec).
  Proof.
    intros interp interp' Heq K K' HK. rewrite /trap_vector_safe_pre.
    repeat f_equiv; done.
  Qed.

  (** The safety of the trap vector [mtcc_vec] for a fault in an untrusted
      compartment: a premise of the safe execution of the running thread. *)
  Definition untrusted_trap_safe (interp : V) (interp_cont : K) : iProp Σ :=
    trap_vector_safe_pre interp interp_cont (λ _ _ _, False%I) (lword_of_word mtcc_vec).

  #[global] Instance untrusted_trap_safe_persistent interp interp_cont :
    Persistent (untrusted_trap_safe interp interp_cont).
  Proof. apply _. Qed.

  #[global] Instance untrusted_trap_safe_ne n :
    Proper (dist n ==> dist n ==> dist n) untrusted_trap_safe.
  Proof.
    intros I1 I2 HI K1 K2 HK. exact (trap_vector_safe_pre_ne n _ _ I1 I2 HI K1 K2 HK).
  Qed.

  (** A safe trap vector is safe for a fault in an untrusted compartment. *)
  Lemma trap_vector_safe_pre_untrusted interp interp_cont trusted_fault :
    trap_vector_safe_pre interp interp_cont trusted_fault (lword_of_word mtcc_vec) -∗
    untrusted_trap_safe interp interp_cont.
  Proof.
    iIntros "#Hsafe !>" (cstk regs w Hfull) "[Hfault|[] ]".
    iApply ("Hsafe" with "[//]"). by iLeft.
  Qed.

End logrel_pre.

Section logrel_expr.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    {CL : CritLink Σ}
    `{MP: MachineParameters}
  .
  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** Safe execution from [wpc] by the thread [th] in the compartment [C]:
      with the thread in [C], a trap vector safe for its faults, safe
      registers, in an untrusted topmost compartment
      ([top_cmpt_untrusted]), and the continuation of [cstk]. *)
  Program Definition interp_expr (interp : V) (interp_cont : K) : E :=
    (λne (W : WORLD) (C : CmptName) (wpc : LWord),
       ∀ cstk Ws Cs regs,
       ( thread_in th C
        ∗ untrusted_trap_safe interp interp_cont
        ∗ interp_reg interp W C regs
        ∗ top_cmpt_untrusted interp W C cstk
        ∗ PC ↦ₚ[th] wpc
        ∗ registers_pointsto regs
        ∗ world_resources W C
        ∗ shared_credit C
        ∗ interp_cont cstk Ws Cs
        ∗ na_own (tpool th) ⊤
        ∗ ◯(CSTK)[th] cstk
        ∗ ⌜frame_match Ws Cs cstk W C⌝
          -∗ safe[th])
    )%I.
  Solve All Obligations with solve_proper.

  #[global] Instance interp_expr_ne n :
    Proper (dist n ==> dist n ==> dist n) (interp_expr).
  Proof.
    intros interp interp0 Heq K K0 HK.
    rewrite /interp_expr. intros ???. simpl.
    by repeat f_equiv.
  Qed.

  (** A safe execution that needs the thread in its compartment: the
      thread is in it, or the execution has a false premise. *)
  Lemma later_interp_expr_thread_in (interp : V) (interp_cont : K) W C w :
    (thread_in th C -∗ ▷ interp_expr interp interp_cont W C w) ⊢
    ▷ interp_expr interp interp_cont W C w.
  Proof.
    iIntros "H".
    destruct (decide (th ∈ cmpt_threads C)) as [Hin|Hnin].
    { iApply "H". by iApply thread_in_intro. }
    iClear "H". rewrite /interp_expr /=. iNext.
    iIntros (cstk Ws Cs regs) "(Hth & _)".
    iDestruct (thread_in_elim with "Hth") as %Hin. done.
  Qed.

  (** [valid_stk_interp] is a predicate stating that the safety predicate [φ]
      is a safety predicate for the stack (RWL capability). *)
  Definition valid_stk_interp (interp : V) (C : CmptName) (φ : V) (p : Perm) : iProp Σ :=
    mono_pub C (safeC φ) ∗
    zcond φ C ∗
    rcond_l φ C p interp ∗
    wcond_wl φ C interp ∗
    ⌜ persistent_cond φ ⌝.
  #[global] Instance valid_interp_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) valid_stk_interp.
  Proof. rewrite /valid_stk_interp; solve_proper. Qed.

  (** [StackWorldResource] keeps track of the safety resources of a stack address [a] containing word [w].
      Note that it does not own the points-to predicate (a ↦ₐ w). *)
  Definition StackWorldResource (interp : V) (W : WORLD) (C : CmptName) (a : Addr) (w : LWord) : iProp Σ :=
    ∃ (φ : V) (p : Perm),
      φ W C w ∗
      future_pub_mono C (safeC φ) w ∗
      (LNonHeap a) ↪ˡ[th, C]{p} (safeC φ) ∗
      valid_stk_interp interp C φ p ∗
      ⌜ PermFlowsTo RWL p ⌝.
  #[global] Instance StackWorldResource_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackWorldResource.
  Proof. rewrite /StackWorldResource; solve_proper. Qed.
  #[global] Instance StackWorldResource_Persistent
    (interp : V) (W : WORLD) (C : CmptName) (a : Addr) (v : LWord) :
    Persistent (StackWorldResource interp W C a v).
  Proof.
    assert ( forall interp W C a v,
               StackWorldResource interp W C a v ⊣⊢
                 (
                   (∃ (φ : V) (p : Perm) (_ : Persistent (φ W C v)),
                       ((φ W C v)
                        ∗ (future_pub_mono C (safeC φ) v)
                        ∗ (LNonHeap a) ↪ˡ[th, C]{p} (safeC φ)
                        ∗ valid_stk_interp interp C φ p
                        ∗ ⌜ PermFlowsTo RWL p ⌝
                       )%I
                   )
                 )) as Heq; last (rewrite Heq; apply _).
    rewrite /StackWorldResource.
    intros.
    iSplit; [iIntros "(%&%&?&?&?&(?&?&?&?&%Hpers)&?)" | iIntros "(%&%&%&?&?&?&(?&?&?&?&?)&?)"]; iFrame.
    pose proof (Hpers (W0,C0,v0)) as H'; iExists H'; done.
  Qed.

  (** [StackWorldResources] keeps track of the safety resources of the stack region [la] containing words [lw].

      This resources comes hand-to-hand with revoking/reinstating or opening/closing the world.
      This is mostly bookkeeping resources, and the user would usually only passes it around.
   *)
  Definition StackWorldResources (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lws : list LWord) : iProp Σ :=
    ([∗ list] a ; v ∈ la ; lws, StackWorldResource interp W C a v).
  #[global] Instance StackWorldResources_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackWorldResources.
  Proof. rewrite /StackWorldResources; solve_proper. Qed.
  #[global] Instance StackWorldResources_Persistent
    (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lv : list LWord) :
    Persistent (StackWorldResources interp W C la lv).
  Proof. apply _. Qed.

  (** [StackOpenWorldResources] keeps track of the safety resources of the stack region [la] containing words [lw].
      This resource is obtained by opening shared stack region, and is used to reinstate it later.

      This is mostly bookkeeping resources, and the user would usually only passes it around.
   *)
  Definition StackOpenWorldResources (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lws : list LWord) : iProp Σ :=
    StackWorldResources interp W C la lws ∗ ([∗ list] a ∈ la, ⌜std W !! LNonHeap a = Some Temporary⌝).
  #[global] Instance StackOpenWorldResources_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackOpenWorldResources.
  Proof. rewrite /StackOpenWorldResources; solve_proper. Qed.

  (** [interp_cont_exec] provides a WP rule for the continuation relation.
      It matches the states of the machine at the point where the switcher returns to the caller.

      [interp_cont_exec] is somewhat the dual of [execute_entry_point]:
      - [interp_cont_exec] matches the state of the machine after the execution of return-to-switcher
      - [execute_entry_point] matches the state of the machine after the execution of call-switcher

      The state of the machine should:
      - [PC] points-to the caller's site
      - the callee-saved registers of the topmost call-frame [frm] are restored in their
        original registers, each satisfying [load_heap] for its saved word
      - [ca0] and [ca1] contain some return values, [interp] in the current world
      - all the other registers have been clear and point to zero
      - the stack is given back, with some universally content (1) [stk_mem_l]
        and [stk_mem_h].
      - [stk_mem_h] corresponds to the callee's stack frame.
        It is shared with the caller, and therefore part of the standard world.
      - [stk_mem_l] corresponds the part of the stack used by the switcher to save the callee-save registers.
        When the caller is untrusted, the points-to have been shared with the callee,
        and therefore stored in the region invariant.
        When the caller is trusted, they are not shared with the callee,
        and therefore _not_ stored in the region invariant.
      - The region invariant is returned, but open to have the points-to of the stack region out.
      - Because the region invariant is open, we need to give the user a way to close the region invariant.
        That's the role of the resources [closing_resources interp W C a v].
      - Finally, we have the [interp_cont] of the (depoped) stack frame (we don't see it in this def,
        but we see it in the definition of [interp_cont] later),
        and the fragmental view of the call-stack [cstk].

    (1) Although we know it should contain zeroes due to the clearing during the return routine,
        it is logically hard to prove in the functional specification because the world
        given by the (known) user is revoked. Which means that we need to
        re-instate the world, together with keeping it open to keep track of its content.
        I think it should work, but the infrastructure for this case doesn't exist,
        and we don't lose anything to have the content universally quantified.
   *)
  Program Definition interp_cont_exec (interp : V) (interp_cont : iProp Σ)
    :
    (CSTK -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO cframe) -n> iPropO Σ)
    :=
    (λne (cstk : CSTK) (W : WORLD) (C : CmptName) (frm : cframe)
     ,
       ∀ (rcgp rcra rcs0 rcs1 wca0 wca1 : LWord) (regs : LReg) (stk_mem_l stk_mem_h : list LWord),
       let b_stk := cf_stk_b frm in
       let a_stk := cf_caller_a frm in
       let e_stk := cf_stk_e frm in
       let shared_stk_region :=
         if (is_untrusted_caller_frm frm)
         then stk_free b_stk e_stk a_stk
         else callee_stk_region b_stk e_stk a_stk in
       let callee_stk_mem :=
         if (is_untrusted_caller_frm frm)
         then stk_mem_join stk_mem_l stk_mem_h
         else stk_mem_h in
       ⌜load_heap frm.(cf_saved).(cs_cgp) rcgp⌝ -∗
       ⌜load_heap frm.(cf_saved).(cs_cra) rcra⌝ -∗
       ⌜load_heap frm.(cf_saved).(cs_cs0) rcs0⌝ -∗
       ⌜load_heap frm.(cf_saved).(cs_cs1) rcs1⌝ -∗
       ( PC ↦ₚ[th] lupdatePcPerm rcra
         ∗ cra ↦ᵣ[th] rcra
         ∗ csp ↦ᵣ[th] (Cap RWL Local b_stk e_stk a_stk)
         (* cgp, cs0 and cs1 are callee-saved registers *)
         ∗ cgp ↦ᵣ[th] rcgp
         ∗ cs0 ↦ᵣ[th] rcs0
         ∗ cs1 ↦ᵣ[th] rcs1
         (* ca0 and ca1 are the return value *)
         ∗ ca0 ↦ᵣ[th] wca0 ∗ interp W C wca0
         ∗ ca1 ↦ᵣ[th] wca1 ∗ interp W C wca1
         (* all other register contain 0 *)
         ∗ ⌜dom regs = all_registers_s ∖ {[cra ; cgp; csp; cs0; cs1 ; ca0; ca1]}⌝
         ∗ regs₀[th] regs
         (* points-to predicate of the stack region *)
         ∗ [[ stk_spill_a a_stk , stk_spill_a a_stk ^+ SpillSlot_size ]] ↦ₐ [[ stk_mem_l ]]
         ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_h ]]
         (* World interpretation *)
         ∗ world_interp_open W C (LNonHeap <$> shared_stk_region)
         (* Bookkeeping resources for the opened world *)
         ∗ StackOpenWorldResources interp W C shared_stk_region callee_stk_mem
         (* Continuation *)
         ∗ interp_cont
         ∗ ◯(CSTK)[th] cstk
         ∗ na_own (tpool th) ⊤
         ∗ thread_in th C
           -∗ safe[th])
    )%I.
  Solve All Obligations with solve_proper.
  #[global] Instance interp_cont_exec_ne n :
    Proper (dist n ==> dist n ==> dist n) (fun interp cont => interp_cont_exec interp cont).
  Proof. solve_proper. Qed.

  (** [interp_callee_part_of_the_stack] interprets the stack pointer of the caller [wstk].
      When a caller calls the switcher-call routine with a capability [Cap p g b e a] in the [csp]
      register, the switcher is using the spill area at [stk_spill_a a] as callee-saved registers area,
      and giving the region $[stk_callee_b b a, stk_callee_e e a)$ as callee-stack frame.

      If the caller is trusted, the callee-saved registers area is expected to be solely accessed by the switcher,
      sharing in fact only the callee's region with the caller.

      If the caller is untrusted, there are no guarantees that the caller won't share its entire stack frame
      with the callee, through one of the arguments.
      In that case, we need to capture the worst possible case, i.e., the caller is sharing all its stack frame,
      making in fact the entire caller's stack pointer [interp].
      This is specifically important in the [ftlr_switcher_call],
      where we don't have any information about the registers,
      and so the points-to predicate of the callee-saved registers are in the region invariant.
   *)
  Definition interp_callee_part_of_the_stack
    (interp : V) (W : WORLD) ( C : CmptName ) (wstk : Word)
    (is_untrusted_caller : bool)
    : iProp Σ :=
    match wstk with
    | WCap t p g b e a =>
        let b_callee := if is_untrusted_caller then b else stk_callee_b b a in
        let e_callee := if is_untrusted_caller then e else stk_callee_e e a in
        ⌜disjoint_from_heap b_callee e_callee⌝ ∗
        interp W C (WCap t p g b_callee e_callee a)
    | _ => True
    end.

  (** [interp_cont] is the continuation relation.
      It takes a call-stack [cstk], a list of world [Ws] and a list of compartments [Cs], all of same size.
      All together, they keep track of the stack of continuations.
      [interp_cont] contains 3 components:
      - the recursive part of the definition, stating that the rest of the stack is also part of the continuation
      - safety of the stack callee stack pointer
      - for a trusted caller, [interp_cont_exec], which provides a WP rule for
        the continuation, matching the machine state after the return-to-caller

      Each known caller records only its pure machine frame. The continuation
      accepts the four words restored by the switcher, each related to its
      saved word by [load_heap]. Neither shadow bits nor restoration
      resources are stored here.

      Unknown callers use the logical relation on the actual words loaded
      from their shared stack. Their frame's placeholder words do not classify
      those saved words. Untrusted callers instead record
      [top_cmpt_untrusted] of their own call stack at their world, for the
      return to them.

      The "body" of continuation relation is only enforced if the caller-callee relation
      involves an unknown compartment.
   *)
  Program Fixpoint interp_cont_aux (interp : V) (ef : trusted_frame) (frms : list cframe)
    (Ws : list WORLD) (Cs : list CmptName)
    : iProp Σ :=
    match frms, Ws, Cs with
    | [],[],[] => True%I
    | frm :: frms', Wt :: Ws', Ct :: Cs' =>
        let cstk' := {| cstk_entry := ef; cstk_frames := frms' |} in
        (* Continuation for the rest of the call-stack *)
        interp_cont_aux interp ef frms' Ws' Cs' ∗
        (if is_known_to_known_frm frm
         then True%I
         else
           ((* The callee stack frame must be safe, because we use the old copy of the stack to clear the stack *)
             interp_callee_part_of_the_stack interp Wt Ct
               (Cap RWL Local (cf_stk_b frm) (cf_stk_e frm) (cf_caller_a frm))
               (is_untrusted_caller_frm frm)
             (* An untrusted caller records that its topmost compartment is
                untrusted, for the return to it; a trusted caller, the
                continuation matching the switcher's state at return-to-caller *)
             ∗ (if is_untrusted_caller_frm frm then top_cmpt_untrusted interp Wt Ct cstk' else
                    (∀ W', ⌜related_sts_pub_world Wt W'⌝
                      -∗ interp_cont_exec interp (interp_cont_aux interp ef frms' Ws' Cs')
                           cstk' W' Ct frm))))%I
    | _,_,_ =>  False%I
    end.
  Solve All Obligations with ( solve_proper; split; intros ; (intros [?  [] ]; done) ).
  #[global] Instance interp_cont_aux_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (interp_cont_aux).
  Proof.
    intros interp interp0 Heq ef ? <- x y -> W W0 -> C C0 ->.
    generalize dependent W0.
    generalize dependent C0.
    induction y as [|frm y IH]; intros C0 W0;[simpl;f_equiv|].
    destruct W0 as [|Wt Ws], C0 as [|Ct Cs]; [reflexivity|reflexivity|reflexivity|].
    cbn [interp_cont_aux].
    apply bi.sep_ne; first apply IH.
    destruct (is_known_to_known_frm frm); first done.
    apply bi.sep_ne.
    { unfold interp_callee_part_of_the_stack. apply bi.sep_ne; first reflexivity. apply Heq. }
    destruct (is_untrusted_caller_frm frm).
    { by apply top_cmpt_untrusted_ne. }
    apply bi.forall_ne; intros W'.
    apply bi.wand_ne; first reflexivity.
    exact (interp_cont_exec_ne n interp interp0 Heq _ _ (IH Cs Ws)
      _ W' Ct frm).
  Qed.

  Program Definition interp_cont (interp : V) : K :=
    (λne (cstk : CSTK) (Ws : list WORLD) (Cs : leibnizO (list CmptName)),
       interp_cont_aux interp cstk.(cstk_entry) cstk.(cstk_frames) Ws Cs
    ).
  Solve All Obligations with solve_proper.
  #[global] Instance interp_cont_ne n :
    Proper (dist n ==> dist n) (interp_cont).
  Proof. solve_proper. Qed.

  (** Execute condition of the logical relation. The capability keeps the
      identifier [π] of the word it comes from. *)
  Definition exec_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e : Addr) (π : option AId)
    (interp : V) : iProp Σ :=
    (∀ (a : Addr) (W' : WORLD),
       ⌜a ∈ₐ [b, e)⌝
       → future_world g W W'
       → ▷ interp_expr interp (interp_cont interp) W' C (Cap p g b e a @@? π))%I.
  #[global] Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof.
    solve_proper_prepare.
    solve_proper.
  Qed.
  #[global] Instance exec_cond_contractive W C b e g p π :
    Contractive (λ interp, exec_cond W C b e g p π interp).
  Proof.
    intros ????. rewrite /exec_cond.
    do 6 f_equiv.
    apply later_contractive.
    { inversion H. constructor. intros.
      apply dist_later_lt in H0.
      apply interp_expr_ne;auto.
      apply interp_cont_ne;auto. }
    Qed.

  (** Enter condition of the logical relation
      Describes that, for a sentry capability to be safe to share,
      its unsealed version must be safe to execute.

      The world must be any future world of [W], public for local and private for global,
      because the world can evolve before invoking the capability.

      The locality must be any lower locality,
      because the locality of a sentry capability can be weakened.

      The unsealed capability keeps the sentry's identifier [π].
 *)
  Definition enter_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (interp : V) : iProp Σ :=
    (∀ W',
       future_world g W W'
       → (∀ g', ⌜ LocalityFlowsTo g' g ⌝ → (▷ interp_expr interp (interp_cont interp) W' C (Cap p g' b e a @@? π)))
    )%I.
  #[global] Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof.
    solve_proper_prepare.
    solve_proper.
  Qed.
  #[global] Instance enter_cond_contractive W C p g b e a π :
    Contractive (λ interp, enter_cond W C p g b e a π interp).
  Proof.
    intros ????. rewrite /enter_cond.
    do 6 f_equiv.
    apply later_contractive.
    inversion H. constructor. intros.
    apply dist_later_lt in H0.
    apply interp_expr_ne;auto.
    apply interp_cont_ne;auto.
  Qed.

End logrel_expr.
