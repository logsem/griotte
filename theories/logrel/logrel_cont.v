From iris.proofmode Require Import proofmode.
From griotte Require Export logrel_conditions.
Import uPred.

(** interp : is a unary logical relation.

    The definitions that take the thread are in sections with a thread
    [th]; they are taken at another thread with [(th := t)]. The fixpoint
    [interp1] is over the family of the threads' relations, in a section
    without thread. The definitions are at the links of the threads'
    family [CL], with their routing laws [CR]. *)

(** The causes with which the trap vector is entered: a fault's cause, or,
    at the context-switch thread, the environment call's. *)
Definition mcause_ok_at (th : Thread) (c : Z) : Prop :=
  mcause_ok c ∨ (th = CtxSwitch ∧ c = MCAUSE_ECALL_MACHINE).

Lemma mcause_ok_at_fault th c : mcause_ok c → mcause_ok_at th c.
Proof. by left. Qed.

Section logrel_pre.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
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

  (** The two high-water-mark registers, MSHWMB at [mshwmb_v] and MSHWM at [mshwm_v],
      with [mshwmb_v ≤ mshwm_v]. *)
  Definition hwm_res_at (mshwmb_v : Addr) (mshwm_v : Z) : iProp Σ :=
    mshwmb ↦ₜ[th] mshwmb_v ∗
    mshwm ↦ₜ[th] mshwm_v ∗
    ⌜(mshwmb_v <= mshwm_v)%Z⌝.

  (** The registers of the thread of [cstk], with MSHWMB at the base of the
      thread's initial stack, and the bounds of its stack. *)
  Definition hwm_res (cstk : CSTK) (mshwm_v : Z) : iProp Σ :=
    hwm_res_at (cstk_hwm_base cstk) mshwm_v ∗
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk).

  (** The stack addresses in [b, mshwm_v) are Temporary in [W]. *)
  Definition zone_temporary (W : WORLD) (b : Addr) (mshwm_v : Z) : Prop :=
    ∀ a : Addr, (b <= a)%a → (a < mshwm_v)%Z → std W !! LNonHeap a = Some Temporary.

  (** What untrusted code holds: the registers, with the stack addresses
      between MSHWMB and MSHWM Temporary in [W]. *)
  Definition hwm_res_untrusted (W : WORLD) (cstk : CSTK) : iProp Σ :=
    ∃ mshwm_v : Z, hwm_res cstk mshwm_v ∗ ⌜zone_temporary W (cstk_hwm_base cstk) mshwm_v⌝.

  (** The high-water-mark resources of the context-switch thread: its MSHWMB
      and MSHWM at the pair it runs with, its window closed, and its last
      owner with the halves it lends. *)
  Definition hwm_res_ctx : iProp Σ :=
    ∃ (mshwmb_v mshwm_v : Z) (o : option (nat * gset Addr)),
      mshwmb ↦ₜ[th] mshwmb_v ∗
      mshwm ↦ₜ[th] mshwm_v ∗
      pend_frag[th] None ∗
      lent_frag[th] (last_owner_zone o) ∗
      ctx_last_owner_frag o.

  (** The high-water-mark resources of the thread, by its kind, with MSHWM
      at [mshwm_v] at a user thread. *)
  Definition hwm_res_trap (cstk : CSTK) (mshwm_v : Z) : iProp Σ :=
    match kind_of th with
    | UserK => hwm_res cstk mshwm_v
    | CtxK => hwm_res_ctx
    end.

  (** What the logical relation holds of the high-water mark: at a user
      thread, the stack addresses between MSHWMB and MSHWM are Temporary in
      [W]. *)
  Definition hwm_res_kind (W : WORLD) (cstk : CSTK) : iProp Σ :=
    ∃ mshwm_v : Z,
      hwm_res_trap cstk mshwm_v ∗
      ⌜kind_of th = UserK → zone_temporary W (cstk_hwm_base cstk) mshwm_v⌝.

  (** The registers as the FTLR sees them: the order [mshwmb_v ≤ mshwm_v] only at a user
      thread. *)
  Definition hwm_res_ftlr (mshwmb_v mshwm_v : Z) : iProp Σ :=
    hwm_regs (ceriseg := ceriseG_of th) mshwmb_v mshwm_v ∗
    ⌜kind_of th = CtxK ∨ (mshwmb_v <= mshwm_v)%Z⌝.

  (** What the FTLR frames around [hwm_res_ftlr]: at a user thread, the
      base is its stack's and its stack token; at the context-switch
      thread, the window closed and the lent halves with their owner. *)
  Definition hwm_frame (cstk : CSTK) (mshwmb_v : Z) : iProp Σ :=
    match kind_of th with
    | UserK =>
        ⌜mshwmb_v = cstk_hwm_base cstk⌝ ∗
        thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk)
    | CtxK =>
        pend_frag[th] None ∗
        ∃ o : option (nat * gset Addr), lent_frag[th] (last_owner_zone o) ∗ ctx_last_owner_frag o
    end.

  #[global] Instance hwm_res_at_timeless mshwmb_v mshwm_v : Timeless (hwm_res_at mshwmb_v mshwm_v).
  Proof. apply _. Qed.

  #[global] Instance hwm_res_timeless cstk mshwm_v : Timeless (hwm_res cstk mshwm_v).
  Proof. apply _. Qed.

  #[global] Instance hwm_res_untrusted_timeless W cstk : Timeless (hwm_res_untrusted W cstk).
  Proof. apply _. Qed.

  #[global] Instance hwm_res_ctx_timeless : Timeless hwm_res_ctx.
  Proof. apply _. Qed.

  #[global] Instance hwm_res_trap_timeless cstk mshwm_v : Timeless (hwm_res_trap cstk mshwm_v).
  Proof. rewrite /hwm_res_trap. destruct (kind_of th); apply _. Qed.

  #[global] Instance hwm_res_kind_timeless W cstk : Timeless (hwm_res_kind W cstk).
  Proof. apply _. Qed.

  #[global] Instance hwm_res_ftlr_timeless mshwmb_v mshwm_v : Timeless (hwm_res_ftlr mshwmb_v mshwm_v).
  Proof. rewrite /hwm_res_ftlr /hwm_regs. apply _. Qed.

  Lemma hwm_res_trap_user cstk mshwm_v :
    th ≠ CtxSwitch → hwm_res_trap cstk mshwm_v ⊣⊢ hwm_res cstk mshwm_v.
  Proof. intros Hth. by rewrite /hwm_res_trap (kind_of_user th). Qed.

  Lemma hwm_res_kind_user W cstk :
    th ≠ CtxSwitch → hwm_res_kind W cstk ⊣⊢ hwm_res_untrusted W cstk.
  Proof.
    intros Hth. rewrite /hwm_res_kind /hwm_res_untrusted.
    setoid_rewrite hwm_res_trap_user; last done.
    iSplit; iIntros "(%mshwm_v & Hres & %Hzone)"; iExists mshwm_v; iFrame; iPureIntro;
      [by apply Hzone, (kind_of_user th) | done].
  Qed.

  Lemma hwm_res_ftlr_user (mshwmb_v : Addr) (mshwm_v : Z) :
    th ≠ CtxSwitch → hwm_res_ftlr mshwmb_v mshwm_v ⊣⊢ hwm_res_at mshwmb_v mshwm_v.
  Proof.
    intros Hth. rewrite /hwm_res_ftlr /hwm_res_at /hwm_regs (kind_of_user th) //.
    iSplit.
    - iIntros "[ [$ $] [%Hk | %Hle] ]"; done.
    - iIntros "($ & $ & %Hle)". by iRight.
  Qed.

  Lemma hwm_res_kind_split W cstk :
    hwm_res_kind W cstk ⊣⊢
    ∃ (mshwmb_v mshwm_v : Z),
      hwm_res_ftlr mshwmb_v mshwm_v ∗
      hwm_frame cstk mshwmb_v ∗
      ⌜kind_of th = UserK → zone_temporary W (cstk_hwm_base cstk) mshwm_v⌝.
  Proof.
    iSplit.
    - iIntros "(%mshwm_v & Hres & %Hzone)".
      rewrite /hwm_res_trap /hwm_res_ftlr /hwm_frame /hwm_regs.
      destruct (kind_of th) eqn:Hk.
      + iDestruct "Hres" as "[ (Hb & Hh & %Hle) Hts]".
        iExists (cstk_hwm_base cstk), mshwm_v. iFrame. iPureIntro. split_and!; [by right | done | done].
      + iDestruct "Hres" as "(%mshwmb_v & %mshwm_v' & %o & Hb & Hh & Hpend & Hlent & Hlast_owner)".
        iExists mshwmb_v, mshwm_v'. iFrame. iPureIntro. split; [by left | done].
    - iIntros "(%mshwmb_v & %mshwm_v & Hres & Hframe & %Hzone)". iExists mshwm_v. iSplitL; last done.
      rewrite /hwm_res_ftlr /hwm_frame /hwm_res_trap /hwm_regs.
      destruct (kind_of th) eqn:Hk.
      + iDestruct "Hres" as "[ [Hb Hh] [%Hctx | %Hle] ]"; first congruence.
        iDestruct "Hframe" as "[-> Hts]". iFrame. by iPureIntro.
      + iDestruct "Hres" as "[ [Hb Hh] _]". iDestruct "Hframe" as "(Hpend & %o & Hlent & Hlast_owner)".
        iExists mshwmb_v, mshwm_v, o. iFrame.
  Qed.

  (** The count of the topmost frame does not change the registers. *)
  Lemma hwm_res_set_top_count (cstk : CSTK) (n : Z) (mshwm_v : Z) :
    hwm_res (cstack_set_top_count cstk n) mshwm_v ⊣⊢ hwm_res cstk mshwm_v.
  Proof.
    by rewrite /hwm_res cstk_hwm_base_set_top_count cstk_hwm_top_set_top_count.
  Qed.

  (** The stack addresses between [b] and MSHWM stay Temporary in a public
      future world, and below a lower MSHWM. *)
  Lemma zone_temporary_mono_pub W W' b mshwm_v :
    related_sts_pub_world W W' → zone_temporary W b mshwm_v → zone_temporary W' b mshwm_v.
  Proof. intros Hrel Hzone a Hb Ha. eapply related_pub_Temporary; eauto. Qed.

  Lemma zone_temporary_lower W b mshwm_v mshwm_v' :
    (mshwm_v' <= mshwm_v)%Z → zone_temporary W b mshwm_v → zone_temporary W b mshwm_v'.
  Proof. intros Hh Hzone a Hb Ha. apply Hzone; [done|lia]. Qed.

  (** Pushing a frame does not change the registers. *)
  Lemma hwm_res_push frm cstk mshwm_v :
    hwm_res (cstack_push frm cstk) mshwm_v ⊣⊢ hwm_res cstk mshwm_v.
  Proof. by rewrite /hwm_res cstk_hwm_base_push cstk_hwm_top_push. Qed.

  (** MSHWM at [mshwm_v], for the call stack [cstk], from the high-water-mark
      registers that the exception path gives back. *)
  Lemma hwm_res_of_regs (cstk : CSTK) (mshwm_v : Z) :
    (cstk_hwm_base cstk <= mshwm_v)%Z →
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk) -∗
    hwm_regs (cstk_hwm_base cstk) mshwm_v -∗
    hwm_res cstk mshwm_v.
  Proof.
    iIntros (Hbh) "#Hts [Hmshwmb Hmshwm]".
    rewrite /hwm_res /hwm_res_at. by iFrame "Hts Hmshwmb Hmshwm".
  Qed.

  (** A cell of a stack is the cell of a Temporary key of the thread. *)
  Lemma stack_cell_temp_cell (a : Addr) (v : LWord) :
    stack_cell a v ⊣⊢ temp_cell th (LNonHeap a) v.
  Proof. by rewrite temp_cell_nonheap. Qed.

  (** The cells of a stack region are the cells of Temporary keys. *)
  Lemma stack_region_temp_cells (b e : Addr) (ws : list LWord) :
    stack_region b e ws ⊣⊢
    [∗ list] a;v ∈ finz.seq_between b e; ws, temp_cell th (LNonHeap a) v.
  Proof.
    rewrite /stack_region. apply big_sepL2_proper. intros. apply stack_cell_temp_cell.
  Qed.

  (** The cell of a Temporary non-heap key is outside a stack region. *)
  Lemma stack_region_temp_cell_notin (b e a : Addr) (ws : list LWord) (w : LWord) :
    stack_region b e ws -∗ temp_cell th (LNonHeap a) w -∗ ⌜a ∉ finz.seq_between b e⌝.
  Proof.
    iIntros "Hstk Ha %Hin".
    iDestruct (big_sepL2_length with "Hstk") as %Hlen.
    apply list_elem_of_lookup in Hin as [i Hi].
    destruct (lookup_lt_is_Some_2 ws i) as [wx Hwx].
    { rewrite -Hlen. by eapply lookup_lt_Some. }
    iDestruct (big_sepL2_lookup with "Hstk") as "Hx"; [exact Hi | exact Hwx |].
    iDestruct (temp_cell_nonheap with "Ha") as "[Ha | (%z & Ha & _) ]".
    - iDestruct (stack_cell_half with "Hx") as "[Hx _]".
      iDestruct (pointsto_ne with "Ha Hx") as %Hne. done.
    - iDestruct (stack_cell_temp_cell with "Hx") as "Hx".
      iApply (temp_cell_zone_cell_false with "Hx [Ha]"). by iExists z.
  Qed.

  (** The cell of a Temporary key of an object: a stack cell of its
      address, and the share of its key. *)
  Lemma temp_cell_addr_key π a v :
    temp_cell th (addr_key π a) v -∗ stack_cell a v ∗ key_share (addr_key π a).
  Proof.
    destruct π as [ι|]; cbn [addr_key].
    - rewrite temp_cell_heap. iIntros "Hk".
      iDestruct (addr_key_pointsto (Some ι) with "Hk") as "[Ha $]".
      by iApply stack_cell_of_pointsto.
    - rewrite -stack_cell_temp_cell. iIntros "$".
  Qed.

  (** The cell of a non-heap Temporary key of the thread, outside
      [MSHWMB, MSHWM), is a points-to. *)
  Lemma wp_temp_cell_release_nosr E e Φ (lpc : LWord) (cstk : CSTK) (mshwm_v : Z) (a : Addr) (w : LWord) :
    to_val e = None →
    pc_nosr lpc.(lw) = true →
    ¬ (cstk_hwm_base cstk ≤ a < mshwm_v)%Z →
    PC ↦ₚ lpc -∗
    temp_cell th (LNonHeap a) w -∗
    hwm_res cstk mshwm_v -∗
    (PC ↦ₚ lpc -∗
     a ↦ₐ w -∗
     hwm_res cstk mshwm_v -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hnsr Hout) "HPC Hcell Hhwm HΦ".
    iDestruct (temp_cell_nonheap with "Hcell") as "[Ha | (%z & Hcell & ->) ]".
    { iApply ("HΦ" with "HPC Ha Hhwm"). }
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hord) Htstk]".
    iApply (wp_zone_release_nosr with "HPC Hcell Hmshwmb Hmshwm"); [done | done | done |].
    iIntros "HPC Ha Hmshwmb Hmshwm".
    iApply ("HΦ" with "HPC Ha [$Hmshwmb $Hmshwm $Htstk //]").
  Qed.

  (** The cells of a stack outside [MSHWMB, MSHWM) are points-to. *)
  Lemma wp_stack_cells_release_nosr E e Φ (lpc : LWord) (cstk : CSTK) (mshwm_v : Z)
      (la : list Addr) (lv : list LWord) :
    to_val e = None →
    pc_nosr lpc.(lw) = true →
    Forall (λ a : Addr, ¬ (cstk_hwm_base cstk <= a < mshwm_v)%Z) la →
    PC ↦ₚ lpc -∗
    ([∗ list] a;v ∈ la;lv, stack_cell a v) -∗
    hwm_res cstk mshwm_v -∗
    (PC ↦ₚ lpc -∗
     ([∗ list] a;v ∈ la;lv, a ↦ₐ v) -∗
     hwm_res cstk mshwm_v -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hnsr).
    iInduction la as [|a la] "IH" forall (lv); iIntros (Hla) "HPC Hl Hhwm HΦ".
    { iDestruct (big_sepL2_nil_inv_l with "Hl") as %->.
      iApply ("HΦ" with "HPC [//] Hhwm"). }
    iDestruct (big_sepL2_cons_inv_l with "Hl") as (v lv' ->) "[Ha Hl]".
    apply Forall_cons_1 in Hla as [Ha Hla].
    iApply ("IH" $! lv' with "[//] HPC Hl Hhwm").
    iIntros "HPC Hl Hhwm".
    iDestruct (stack_cell_temp_cell with "Ha") as "Ha".
    iApply (wp_temp_cell_release_nosr with "HPC Ha Hhwm"); [done | done | done |].
    iIntros "HPC Ha Hhwm".
    iApply ("HΦ" with "HPC [$Ha $Hl] Hhwm").
  Qed.

  (** A write-local capability on [b, e) lies in the stack of the
      thread. *)
  Definition wl_in_stack (p : Perm) (b e : Addr) : iProp Σ :=
    (if isWL p
     then ∃ bs es : Addr, thread_stack_bounds bs es ∗ ⌜(bs <= b)%a ∧ (e <= es)%a⌝
     else True)%I.

  #[global] Instance wl_in_stack_persistent p b e : Persistent (wl_in_stack p b e).
  Proof. rewrite /wl_in_stack. destruct (isWL p); apply _. Qed.

  Lemma wl_in_stack_nonWL p b e : isWL p = false → wl_in_stack p b e ⊣⊢ True.
  Proof. intros Hp. by rewrite /wl_in_stack Hp. Qed.

  Lemma wl_in_stack_weaken p p' (b e b' e' : Addr) :
    PermFlowsTo p' p → (b <= b')%a → (e' <= e)%a →
    wl_in_stack p b e -∗ wl_in_stack p' b' e'.
  Proof.
    iIntros (Hfl Hb He) "Hwl". rewrite /wl_in_stack.
    destruct (isWL p') eqn:Hp'; last done.
    rewrite (isWL_flowsto _ _ Hfl Hp').
    iDestruct "Hwl" as (bs es) "[Hts %Hbs]". iExists bs, es. iFrame "Hts".
    iPureIntro. solve_addr.
  Qed.

  Lemma wl_in_stack_base p (b e mshwmb_v es : Addr) :
    isWL p = true →
    thread_stack_bounds mshwmb_v es -∗ wl_in_stack p b e -∗ ⌜(mshwmb_v <= b)%a ∧ (e <= es)%a⌝.
  Proof.
    iIntros (Hp) "Hts Hwl". rewrite /wl_in_stack Hp.
    iDestruct "Hwl" as (bs es') "[Hts' %Hbs]".
    iDestruct (thread_stack_bounds_agree with "Hts Hts'") as %[-> ->]. done.
  Qed.

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
      (cstk : CSTK) (regs : LReg) (mshwm_v : Z) : iProp Σ :=
    ∃ (W : WORLD) (C : CmptName) (Ws : list WORLD) (Cs : list CmptName),
      ⌜frame_match Ws Cs cstk W C⌝ ∗
      ⌜kind_of th = UserK → zone_temporary W (cstk_hwm_base cstk) mshwm_v⌝ ∗
      interp_reg interp W C regs ∗
      top_cmpt_untrusted interp W C cstk ∗
      world_resources W C ∗
      thread_in th C ∗
      interp_cont cstk Ws Cs.

  #[global] Instance untrusted_fault_pre_ne n :
    Proper (dist n ==> dist n ==> (=) ==> (=) ==> (=) ==> dist n) untrusted_fault_pre.
  Proof.
    intros interp interp' Heq K K' HK cstk ? <- regs ? <- mshwm_v ? <-.
    rewrite /untrusted_fault_pre. repeat f_equiv.
    all: try apply interp_reg_ne; try apply top_cmpt_untrusted_ne; try apply HK; done.
  Qed.

  (** The trap vector [wvec] is safe: after trap entry from any PC [w],
      with any call stack [cstk], registers [regs] and MSHWM [mshwm_v], execution
      from [wvec] is safe, for a fault in an untrusted compartment
      ([untrusted_fault_pre]) or a fault that [trusted_fault] accepts. The
      trap vector runs with MIE disabled and receives the whole posture of
      the thread, with MPIE (the posture of the fault), MEPCC, mcause and
      mtval pinned at the values of trap entry. *)
  Definition trap_vector_safe_pre (interp : V) (interp_cont : K)
      (trusted_fault : CSTK → LWord → LReg → Z → iProp Σ) (wvec : LWord) : iProp Σ :=
    □ ∀ (cstk : CSTK) (regs : LReg) (w : LWord) (mshwm_v : Z),
      ⌜∀ r, is_Some (regs !! r)⌝ -∗
      (untrusted_fault_pre interp interp_cont cstk regs mshwm_v ∨ trusted_fault cstk w regs mshwm_v) -∗
      PC ↦ₚ[th] wvec -∗
      MIE ↦ₜ[th] InterruptDisabled -∗
      (∃ (b : InterruptStatus) (c v : Z),
         ⌜route_pre th b⌝ ∗
         ⌜mcause_ok_at th c⌝ ∗
         posture_res_gen (th := th) (Some b) (Some (lmepcc_of_pc w))
           (Some (lword_of_word (WInt c))) (Some v)) -∗
      registers_pointsto regs -∗
      hwm_res_trap cstk mshwm_v -∗
      na_own (tpool th) ⊤ -∗
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
    trap_vector_safe_pre interp interp_cont (λ _ _ _ _, False%I) (lword_of_word mtcc_vec).

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
    iIntros "#Hsafe !>" (cstk regs w mshwm_v Hfull) "[Hfault|[] ]".
    iApply ("Hsafe" with "[//]"). by iLeft.
  Qed.

  (** What trap entry gives back, with the part of the posture that the
      faulting code keeps at InterruptDisabled, is what the trap vector
      receives. *)
  Lemma trap_entry_out_posture w b :
    route_pre th b →
    trap_entry_out w b -∗
    (if b is InterruptDisabled then posture_part (th := th) else True) -∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    ∃ (b' : InterruptStatus) (c v : Z),
      ⌜route_pre th b'⌝ ∗
      ⌜mcause_ok_at th c⌝ ∗
      posture_res_gen (th := th) (Some b') (Some (lmepcc_of_pc w))
        (Some (lword_of_word (WInt c))) (Some v).
  Proof.
    iIntros (Hpre) "Hout Hpart".
    iDestruct (trap_entry_out_handover with "Hout") as "($ & (%c & %v & %Hc & _ & Hh) & Hpart')".
    iExists b, c, v. iSplit; first done.
    iSplit; first (iPureIntro; by apply mcause_ok_at_fault).
    iApply (posture_res_gen_intro with "Hh"). destruct b; [iExact "Hpart'" | iExact "Hpart"].
  Qed.

End logrel_pre.

(** The high-water-mark resources of the logical relation at the
    context-switch thread. *)
Section hwm_res_ctx_conv.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t} `{MP : MachineParameters}.

  Lemma hwm_res_trap_ctx cstk (mshwm_v : Z) :
    hwm_res_trap (th := CtxSwitch) cstk mshwm_v ⊣⊢ hwm_res_ctx (th := CtxSwitch).
  Proof. done. Qed.

  Lemma hwm_res_kind_ctx (W : WORLD) cstk :
    hwm_res_kind (th := CtxSwitch) W cstk ⊣⊢ hwm_res_ctx (th := CtxSwitch).
  Proof.
    rewrite /hwm_res_kind. setoid_rewrite hwm_res_trap_ctx.
    iSplit.
    - iIntros "(%mshwm_v & $ & _)".
    - iIntros "Hres". iExists 0%Z. iFrame. iPureIntro. discriminate.
  Qed.
End hwm_res_ctx_conv.

Section logrel_expr.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .
  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** Safe execution from [wpc] by the thread [th] in the compartment [C],
      at the posture [b]: with the thread in [C], a trap vector safe for its
      faults, safe registers, in an untrusted topmost compartment
      ([top_cmpt_untrusted]), the continuation of [cstk], and the MIE
      fragment and what the thread holds at [b], where the thread may run at
      [b] ([route_pre]). *)
  Program Definition interp_expr_at (b : InterruptStatus) (interp : V) (interp_cont : K) : E :=
    (λne (W : WORLD) (C : CmptName) (wpc : LWord),
       ∀ cstk Ws Cs regs,
       ( thread_in th C
        ∗ untrusted_trap_safe interp interp_cont
        ∗ interp_reg interp W C regs
        ∗ top_cmpt_untrusted interp W C cstk
        ∗ PC ↦ₚ[th] wpc
        ∗ registers_pointsto regs
        ∗ hwm_res_kind W cstk
        ∗ world_resources W C
        ∗ shared_credit C
        ∗ interp_cont cstk Ws Cs
        ∗ na_own (tpool th) ⊤
        ∗ ◯(CSTK)[th] cstk
        ∗ ⌜frame_match Ws Cs cstk W C⌝
        ∗ ⌜route_pre th b⌝
        ∗ MIE ↦ₜ[th] b
        ∗ held (th := th) b
          -∗ safe[th])
    )%I.
  Solve All Obligations with solve_proper.

  #[global] Instance interp_expr_at_ne b n :
    Proper (dist n ==> dist n ==> dist n) (interp_expr_at b).
  Proof.
    intros interp interp0 Heq K K0 HK.
    rewrite /interp_expr_at. intros ???. simpl.
    by repeat f_equiv.
  Qed.

  (** Safe execution at every posture. *)
  Program Definition interp_expr (interp : V) (interp_cont : K) : E :=
    (λne (W : WORLD) (C : CmptName) (wpc : LWord),
       ∀ b, interp_expr_at b interp interp_cont W C wpc)%I.
  Solve All Obligations with solve_proper.

  #[global] Instance interp_expr_ne n :
    Proper (dist n ==> dist n ==> dist n) (interp_expr).
  Proof.
    intros interp interp0 Heq K K0 HK.
    rewrite /interp_expr. intros ???. simpl.
    f_equiv. intros b. by apply interp_expr_at_ne.
  Qed.

  (** A safe execution that needs the thread in its compartment: the
      thread is in it, or the execution has a false premise. *)
  Lemma later_interp_expr_at_thread_in b (interp : V) (interp_cont : K) W C w :
    (thread_in th C -∗ ▷ interp_expr_at b interp interp_cont W C w) ⊢
    ▷ interp_expr_at b interp interp_cont W C w.
  Proof.
    iIntros "H".
    destruct (decide (th ∈ cmpt_threads C)) as [Hin|Hnin].
    { iApply "H". by iApply thread_in_intro. }
    iClear "H". rewrite /interp_expr_at /=. iNext.
    iIntros (cstk Ws Cs regs) "(Hth & _)".
    iDestruct (thread_in_elim with "Hth") as %Hin. done.
  Qed.

  Lemma later_interp_expr_thread_in (interp : V) (interp_cont : K) W C w :
    (thread_in th C -∗ ▷ interp_expr interp interp_cont W C w) ⊢
    ▷ interp_expr interp interp_cont W C w.
  Proof.
    iIntros "H". rewrite /interp_expr /=. iIntros (b).
    iApply later_interp_expr_at_thread_in.
    iIntros "Hth". iSpecialize ("H" with "Hth"). iNext. iApply "H".
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
      - The local map is returned, but open to have the points-to of the stack region out,
        together with the part of the world premise that holds the map of
        Permanent regions, [perm_resources C].
      - Because the local map is open on the stack region,
        [StackOpenWorldResources] gives the user what it needs to close it.
      - Finally, we have the [interp_cont] of the (depoped) stack frame (we don't see it in this def,
        but we see it in the definition of [interp_cont] later),
        and the fragmental view of the call-stack [cstk].
      - The caller resumes with its MIE fragment and what the thread holds at
        the posture that its return sentry [rcra] restores; [m] is the
        posture of the return routine, kept by an inheriting target.

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
       ∀ (rcgp rcra rcs0 rcs1 wca0 wca1 : LWord) (regs : LReg) (stk_mem_l stk_mem_h : list LWord)
         (m : InterruptStatus),
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
         (* the high-water mark is the caller's stack pointer *)
         ∗ hwm_res cstk a_stk
         (* cells of the stack region *)
         ∗ stack_region (stk_spill_a a_stk) (stk_spill_a a_stk ^+ SpillSlot_size) stk_mem_l
         ∗ stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) stk_mem_h
         (* The local map, open on the shared stack region, and the part of
            the world premise that holds the map of Permanent regions *)
         ∗ local_region_map th W C (open_l W (LNonHeap <$> shared_stk_region))
         ∗ perm_resources C
         (* Bookkeeping resources for the opened world *)
         ∗ StackOpenWorldResources interp W C shared_stk_region callee_stk_mem
         (* Continuation *)
         ∗ interp_cont
         ∗ ◯(CSTK)[th] cstk
         ∗ na_own (tpool th) ⊤
         ∗ thread_in th C
         (* The caller resumes at the posture its return sentry restores *)
         ∗ ⌜route_pre th (default m (jalr_target_mie rcra.(lw)))⌝
         ∗ MIE ↦ₜ[th] (default m (jalr_target_mie rcra.(lw)))
         ∗ held (th := th) (default m (jalr_target_mie rcra.(lw)))
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
         then
           (* the caller's stack starts at the base of the thread's stack *)
           ⌜cf_stk_b frm = tf_stk_b ef⌝
         else
           ((* The callee stack frame must be safe, because we use the old copy of the stack to clear the stack *)
             interp_callee_part_of_the_stack interp Wt Ct
               (Cap RWL Local (cf_stk_b frm) (cf_stk_e frm) (cf_caller_a frm))
               (is_untrusted_caller_frm frm)
             (* An untrusted caller records that its topmost compartment is
                untrusted, for the return to it; a trusted caller, the
                continuation matching the switcher's state at return-to-caller *)
             ∗ (if is_untrusted_caller_frm frm
                then
                  top_cmpt_untrusted interp Wt Ct cstk' ∗
                  (* the stack addresses between the base of the thread's
                     stack and the caller's cursor are Temporary in the
                     caller's world *)
                  ⌜zone_temporary Wt (tf_stk_b ef) (cf_caller_a frm)⌝ ∗
                  (* the caller's stack starts at the base of the thread's
                     stack *)
                  ⌜cf_stk_b frm = tf_stk_b ef⌝
                else
                  ⌜cf_stk_b frm = tf_stk_b ef⌝ ∗
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
    { apply bi.sep_ne; [by apply top_cmpt_untrusted_ne|done]. }
    apply bi.sep_ne; first done.
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
  Definition enter_cond (k : SentryKind)
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (interp : V) : iProp Σ :=
    (∀ W',
       future_world g W W'
       → (∀ g', ⌜ LocalityFlowsTo g' g ⌝ →
          ∀ m, ▷ interp_expr_at (default m (sentry_kind_mie k)) interp (interp_cont interp)
                   W' C (Cap p g' b e a @@? π))
    )%I.
  #[global] Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==>
            dist n ==> dist n) enter_cond.
  Proof.
    intros k ? <- W ? <- C ? <- p ? <- g ? <- b ? <- e ? <- a ? <- π ? <- interp interp' Heq.
    rewrite /enter_cond. do 9 f_equiv. apply interp_expr_at_ne; [done | by apply interp_cont_ne].
  Qed.
  #[global] Instance enter_cond_contractive k W C p g b e a π :
    Contractive (λ interp, enter_cond k W C p g b e a π interp).
  Proof.
    intros n interp interp' Heq. rewrite /enter_cond.
    do 8 f_equiv.
    apply later_contractive.
    inversion Heq as [Heq']. constructor. intros n' Hn'.
    apply interp_expr_at_ne; [by apply Heq' | by apply interp_cont_ne, Heq'].
  Qed.

End logrel_expr.
