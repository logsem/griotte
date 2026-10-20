From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Import bitblast.
From griotte Require Import map_simpl register_tactics.
From griotte Require Export code_blocks.
From griotte Require Export switcher.
From griotte Require Export clear_stack_spec clear_registers_spec.

Lemma switcher_disjoint_subseg `{MP : MachineParameters} b e b' e' :
  (b <= b')%a -> (e' <= e)%a ->
  disjoint_from_mmio b e ∧ disjoint_from_heap b e ->
  disjoint_from_mmio b' e' ∧ disjoint_from_heap b' e'.
Proof.
  intros Hb He [Hs Hh]. split.
  - by eapply disjoint_from_mmio_weaken.
  - rewrite /disjoint_from_heap elem_of_disjoint in Hh |- *.
    intros x Hx Hregion; eapply Hh; try exact Hregion.
    apply elem_of_finz_seq_between; apply elem_of_finz_seq_between in Hx.
    solve_addr.
Qed.

Section Switcher_preamble.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma encode_entry_point_eq_nargs mie nargs minstk off_entry :
    (0 ≤ nargs ≤ 7)%Z ->
    Z.land (encode_entry_point mie nargs minstk off_entry) 7 = nargs.
  Proof.
    intros Hnargs.
    transitivity (Z.land nargs 7).
    { rewrite /encode_entry_point /entry_point_posture /entry_point_irq_disabled_mask.
      destruct mie; bitblast. }
    change 7%Z with (Z.ones 3).
    rewrite Z.land_ones; last lia.
    apply Z.mod_small; lia.
  Qed.

  Lemma encode_entry_point_eq_posture mie nargs minstk off_entry :
    Z.land (encode_entry_point mie nargs minstk off_entry) entry_point_irq_disabled_mask =
    entry_point_posture mie.
  Proof.
    rewrite /encode_entry_point /entry_point_posture /entry_point_irq_disabled_mask.
    destruct mie; bitblast.
  Qed.

  Lemma encode_entry_point_eq_minstk mie nargs minstk off_entry :
    (0 ≤ minstk ≤ 255)%Z ->
    Z.land (encode_entry_point mie nargs minstk off_entry ≫ 8) 255 = minstk.
  Proof.
    intros Hminstk.
    transitivity (Z.land minstk 255).
    { rewrite /encode_entry_point /entry_point_posture /entry_point_irq_disabled_mask.
      destruct mie; bitblast. }
    change 255%Z with (Z.ones 8).
    rewrite Z.land_ones; last lia.
    apply Z.mod_small; lia.
  Qed.

  (** Only the low byte of the minimum stack size is encoded. *)
  Lemma encode_entry_point_minstk_land mie nargs minstk off_entry :
    encode_entry_point mie nargs minstk off_entry =
    encode_entry_point mie nargs (Z.land minstk 255) off_entry.
  Proof.
    rewrite /encode_entry_point -Z.land_assoc Z.land_diag //.
  Qed.

  Lemma encode_entry_point_eq_off mie nargs minstk off_entry :
    (encode_entry_point mie nargs minstk off_entry ≫ 16)%Z = off_entry.
  Proof.
    rewrite /encode_entry_point /entry_point_posture /entry_point_irq_disabled_mask.
    destruct mie; bitblast.
  Qed.

  (** Property of capability sealed by the switcher's otype *)
  Definition export_tableN (Cname : namespace) : namespace := nroot .@ "export_tableN" .@ Cname.
  Definition export_table_PCCN (Cname : namespace) : namespace := (export_tableN Cname) .@ "PCC".
  Definition export_table_CGPN (Cname : namespace) : namespace := (export_tableN Cname) .@ "CGP".
  Definition export_table_entryN (Cname : namespace) (a : Addr) : namespace :=
    (export_tableN Cname) .@ "entry" .@ a.

  (** [execute_entry_point_register] describes the register state of the machine
      after jumping to the callee, at the end of the switcher-call.
      [cgp] contains the callee compartment's data capability
      (the PC, which holds its code capability, is not a register).
      They don't have to be [interp], and are _not_ [interp]
      when the compartment is one of the trusted ones.

      [cps] contains the callee's stack frame. It has to be [interp] because it always comes from the caller,
      which is usually untrusted.

      Finally, all the register contain some (1) safe values.

      (1) Although we know that they contain zeroes due to the caller's clearing,
          it makes the proofs more annoying, and we never rely on this information anyway.
   *)
  Program Definition execute_entry_point_register (wcgp wstk : LWord) (nargs : nat) :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO LReg),
      (full_map reg
       ∧ ⌜ reg !! cgp = Some wcgp ⌝
       ∧ ⌜ ∃ mie, reg !! cra = Some (lword_of_word (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return)) ⌝
       ∧ ⌜ reg !! csp = Some wstk ⌝
       ∗ interp W C wstk
       ∗ (∀ (r : RegName) (v : LWord), (⌜r ∈ (dom_arg_rmap nargs)⌝ → ⌜reg !! r = Some v⌝ → interp W C v))
       ∗ (∀ (r : RegName) (v : LWord), (⌜r ∉ ({[cra; cgp; csp]} ∪ (dom_arg_rmap nargs) : gset RegName)⌝ → ⌜reg !! r = Some v⌝ → ⌜ v = WInt 0 ⌝))
      )%I.
  Solve All Obligations with solve_proper.

  (** [csp_sync] is a small pure side-condition that relates the stack pointer of the caller,
      with the stack pointer of the callee.
      See [execute_entry_point] to understand how they are related.
   *)
  Definition csp_sync (cstk : CSTK) (a_stk' e_stk' : Addr) :=
    match cstk with
    | frm::_ =>
        frm.(a_stk) = a_stk'
        ∧ frm.(e_stk) = e_stk'
    | _ => True
    end
  .

  (** [execute_entry_point] provides a WP rule matching the state of the machine
      after the execution of call-switcher.

      [execute_entry_point] is somewhat the dual of [interp_cont_exec]:
      - [execute_entry_point] matches the state of the machine after the execution of call-switcher
      - [interp_cont_exec] matches the state of the machine after the execution of return-to-switcher

      It is the WP rule to prove to show that the execution of an entry point is valid.
      In case of known code entry point, it contains all the information available when invoked.
      In case of unknown code entry point, we can show this by validity of
      the code and data capability (see the use of [fundamental] in [ot_switcher_interp]).

      An important point is the use of [csp_sync] and the stack capability [WCap true RWL Local a_stk4 e_stk a_stk4].
      If the call stack is not empty, we know that the caller's stack looks like
      [WCap true RWL Local b_stk e_stk a_stk] (it is tested by the switcher's call routine).
      The switcher reserves the area `[a_stk, a_stk+4)` for the callee-saved area,
      and passes the rest, i.e. `[a_stk+4, e_stk)`  to the callee.

      [csp_sync] synchronises the caller's stack pointer with the callee stack pointer.
      It's important when proving the functional specification of the return-to-switcher routine,
      because the switcher uses the caller stack pointer to clear (and therefore re-instate) the stack.
      But the caller gives the `revoked_resources` of its own stack pointer.
      Synchronising the caller and callee is important for using the caller's `revoked_resources`
      to re-instate validity of the caller's stack.
      This will become clearer in the proof of [switcher_ret_specification].
   *)
  Program Definition execute_entry_point (wpcc wcgp : LWord) (nargs minstk : nat) :
    (WORLD -n> (leibnizO CmptName) -n> iPropO Σ) :=
    (λne (W : WORLD) (C : CmptName),
      ∀ (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) regs a_stk e_stk,
       let a_stk4 := (a_stk ^+4)%a in
       ( interp_continuation cstk Ws Cs
         ∗ ⌜frame_match Ws Cs cstk W C⌝
         ∗ PC ↦ₚ wpcc
         ∗ (execute_entry_point_register wcgp (WCap true RWL Local a_stk4 e_stk a_stk4) nargs W C regs)
         ∗ registers_pointsto regs
         ∗ world_interp W C
         (* The 2nd condition [a_stk = (a_stk4 ^+ -4)%a] is necessary,
            because ((a_stk ^+4)%a ^+ -4)%a is not necessarily [a_stk] due to finite integers. *)
         ∗ ⌜csp_sync cstk a_stk e_stk ∧ a_stk = (a_stk4 ^+ -4)%a⌝
         (* The switcher checked that the callee's stack is at least the
            minimum stack size of the entry point. *)
         ∗ ⌜(Z.of_nat minstk <= e_stk - a_stk4)%Z⌝
         ∗ cstack_frag cstk
         ∗ na_own cerise_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  (** [ot_switcher_prop] is the sealing predicate for the switcher's otype, used for sealing entry points.
      Any (regular) compartment's are sealed with this otype, and must therefore respect this predicate.
      Only the switcher can unseal this otype.

      Operationally, a compartment entry point is a RO-capability pointing to
      an entry in the compartment's export table.
      The compartment's export table always starts with the compartment's PCC and CGP,
      and then a list of entries of the form [(posture,nargs,minstk,offset)],
      where [posture] is the interrupt posture the callee runs with,
      [nargs] is the number of argument (up-to 7),
      [minstk] is the minimum size of the callee's stack, in words (up-to 255),
      and [offset] is the offset of the function in the code,
      from the first address of the PCC (i.e., we must take account for the RO global data, like the imports).

      For the most of the definition, [ot_switcher_prop] describes the logical state of the physical state described above.
      In addition, it contains the resources [(seal_capability w ot_switcher) ↦□ₑ nargs],
      which states that entry point uses [nargs] (the others are cleared by the switcher).
      It's a [Persistent] knowledge, and is used by the functional spec of the switcher's call
      for requiring the caller to only show [interp] of the actual arguments.

      Finally, [execute_entry_point] is called, with [PCC+off] in the [PC],
      and the callee knows that its stack has at least [minstk] words.
      It is guarded by a □-modality, because the entry point can be invoked at any time.
      Similarly, [related_sts_priv_world].
   *)
  Program Definition ot_switcher_prop :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ):=
    λne (W : WORLD) (C : CmptName) (w : LWord),
       (∃ (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr)
          (bpcc epcc : Addr)
          (bcgp ecgp : Addr)
          (nargs minstk : nat) (off : Z) (posture : InterruptStatus)
         ,
           ⌜ w = WCap true RO g_tbl b_tbl e_tbl a_tbl ⌝
           ∗ ⌜ (b_tbl <= a_tbl < e_tbl)%a ⌝
           ∗ ⌜ (b_tbl < (b_tbl ^+1))%a ⌝
           ∗ ⌜ ((b_tbl ^+1) < a_tbl)%a ⌝
           ∗ ⌜ (0 <= nargs <= 7 )%nat ⌝
           ∗ ⌜ (minstk <= 255)%nat ⌝
           ∗ ⌜ is_Some (bpcc + off)%a ⌝
           ∗ ⌜ is_shadow_address a_tbl = false ⌝
           ∗ ⌜ is_shadow_address b_tbl = false ⌝
           ∗ ⌜ is_shadow_address (b_tbl ^+ 1)%a = false ⌝
           ∗ ⌜ is_heap_address bpcc = false ⌝
           ∗ ⌜ is_heap_address bcgp = false ⌝
           ∗ b_tbl ↦ₐ□ WCap true RX Global bpcc epcc bpcc
           ∗ (b_tbl ^+ 1)%a ↦ₐ□ WCap true RW Global bcgp ecgp bcgp
           ∗ a_tbl ↦ₐ□ WInt (encode_entry_point posture (Z.of_nat nargs) (Z.of_nat minstk) off)
           ∗ (seal_capability w.(lw) ot_switcher) ↦□ₑ nargs
           ∗ (seal_capability (borrow w.(lw)) ot_switcher) ↦□ₑ nargs
           ∗ □ ( ∀ W', ⌜related_sts_priv_world W W'⌝ →
                   ▷ (execute_entry_point
                            (WCap true RX Global bpcc epcc (bpcc ^+ off)%a)
                            (WCap true RW Global bcgp ecgp bcgp)
                            nargs minstk
                            W' C))
      )%I.
  Solve All Obligations with solve_proper.

  Definition ot_switcher_propC : (WORLD * CmptName * LWord) -> iPropI Σ :=
    safeC ot_switcher_prop.


  Lemma mono_priv_ot_switcher (C : CmptName) (w : LWord) :
    ⊢ future_priv_mono C ot_switcher_propC w.
  Proof.
    iIntros (W W' Hrelated_W_W').
    iModIntro.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iDestruct "Hot_switcher" as
      (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs minstk off posture ->
       Hatbl Hbtbl Hbtbl1 Hnargs Hminstk Hentry_some Hatbl_shadow Hbtbl_shadow Hbtbl1_shadow Hbpcc_heap Hbcgp_heap)
      "(Hinvpcc & Hinvcgp & Hinventry & #Hentry &#Hentry_borrow & #Hcont)".
    iFrame "Hinvpcc Hinvcgp Hinventry Hentry".
    iExists _,_.
    repeat (iSplit ; first done).
    iModIntro.
    iIntros (W'' Hrelated_W'_W'').
    iSpecialize ("Hcont" $! W'').
    iApply "Hcont".
    iPureIntro.
    by eapply related_sts_priv_trans_world.
  Qed.


  Lemma ot_switcher_prop_borrow (W : WORLD) (C : CmptName) (w : LWord) :
    ot_switcher_prop W C w -∗ ot_switcher_prop W C (lborrow w).
  Proof.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iDestruct "Hot_switcher" as
      (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs minstk off posture ->
       Hatbl Hbtbl Hbtbl1 Hnargs Hminstk Hentry_some Hatbl_shadow Hbtbl_shadow Hbtbl1_shadow Hbpcc_heap Hbcgp_heap)
      "(Hinvpcc & Hinvcgp & Hinventry & #Hentry & #Hentry_borrow & #Hcont)".
    iFrame "#∗%".
    iExists Local; iPureIntro; done.
  Qed.

  (** [cframe_interp] interprets a call-frame, i.e.,
      describes how the physical call-frame is linked to the logical call-frame [frm : cframe].
      We have 2 situations to take into account:
      - If the caller is untrusted, the points-to predicate of the callee-save region
        are stored in the region invariant, which means that their content is controlled by adversary,
        and does not have to match with the call-frame.
      - If the caller is trusted, the switcher controls the callee-save region,
        and the content should match the words of the call-frame.
   *)
  Definition cframe_stk_own (frm : cframe) : iProp Σ :=
    let a_stk := frm.(a_stk) in
    (if (is_untrusted_caller_frm frm)
    then True
    else
      a_stk ↦ₐ frm.(wcs0)
      ∗ (a_stk ^+ 1)%a ↦ₐ frm.(wcs1)
      ∗ (a_stk ^+ 2)%a ↦ₐ frm.(wret)
      ∗ (a_stk ^+ 3)%a ↦ₐ frm.(wcgp))%I.

  Definition cframe_interp (frm : cframe) (a_tstk : Addr) : iProp Σ :=
    let b_stk := frm.(b_stk) in
    let a_stk := frm.(a_stk) in
    let e_stk := frm.(e_stk) in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    a_csp ↦ₐ WCap true RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    (∃ w, a_export_table ↦ₐ w) ∗
    (∃ w, a_error_count ↦ₐ w) ∗
    ⌜ (b_stk <= a_stk)%a ∧ (a_stk ^+ 3 < e_stk)%a ∧ is_Some (a_stk + 4)%a ∧
      disjoint_from_mmio b_stk e_stk ∧ disjoint_from_heap b_stk e_stk ∧
      (* a trusted caller returns to a valid target, outside the heap *)
      (is_untrusted_caller_frm frm = false →
       jalr_target_ok cnull cra frm.(wret).(lw) = true ∧ is_heap_cap frm.(wret).(lw) = false) ⌝ ∗
    cframe_stk_own frm%I.

  (** [cstack_interp] interprets a call-stack, whose topmost frame is at
      [a_tstk] in the trusted stack. It interprets the topmost stack frame,
      as well as the rest of the call-stack, in the frames below. The empty
      call-stack is the entry frame of the thread, [frames[0]], whose cells
      are not constrained.
   *)
  Fixpoint cstack_interp (cstk : cstack) (a_tstk : Addr) : iProp Σ :=
    (match cstk with
    | [] =>
        let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
        let a_export_table := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
        let a_error_count := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
        ∃ w0 w1 w2,
          a_csp ↦ₐ w0 ∗
          a_export_table ↦ₐ w1 ∗
          a_error_count ↦ₐ w2
    | frm::cstk' =>
        let a_prev := (a_tstk ^+ - TrustedStackFrame_size)%a in
        cstack_interp cstk' a_prev ∗ cframe_interp frm a_tstk
    end)%I.

  (** [switcher_inv] describes the invariant of the switcher,
      and describe the private state of the switcher.

      [mtdc] is the a privileged register, than only the switcher can access.
      It contains a capability to the base of the _trusted stack_
      (also called _physical call stack_ or _switcher's private state_),
      which never changes. The trusted stack starts with the register save
      area, followed by [frameoffset] (the offset of the next free frame) and
      the frames. Each frame stores the stack pointer of a caller, the
      export table of the callee and the number of error handlers invoked.

      The _trusted stack_ must be in sync with the logical call stack [cstk],
      for which the switcher's invariant holds the authoritative view [cstack_full].
      As a reminder, the fragmental view [cstack_frag] is given by the expression relation
      (or any of its variants).

      The code of the switcher and the unsealing capability of the switcher's
      otype are read-only: they are not in the invariant, but in the persistent
      resource [switcher_static].

      Finally, the invariant holds the points-to predicates of the trusted stack.
      The topmost frame is at [a_tstk]; the unused part, from the next frame
      to [e_trusted_stack], and the save area contain some unknown values.
      The used part is contained in the definition of [cstack_interp].
   *)
  Definition switcher_inv : iProp Σ :=
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    ∃ (a_tstk : Addr) (cstk' : CSTK) (save_area tstk_next : list LWord),
      let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
      "Hmtdc" ∷ mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
      "%Hot_bounds" ∷ ⌜(ot_switcher < (ot_switcher ^+1))%ot⌝ ∗
      "Hsave_area" ∷ [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
      "Hframeoffset" ∷ a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk')) ∗
      "HthreadID" ∷ (∃ w, a_threadID ↦ₐ w) ∗
      "Htstk" ∷ [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
      "Hcstk_full" ∷ cstack_full cstk' ∗
      "%Hlen_cstk" ∷ ⌜(b_trusted_stack + tstack_frame_offset (length cstk'))%a = Some a_tstk
                      ∧ (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z⌝ ∗
      (* link the topmost frame of cstk' to the state *)
      "Hstk_interp" ∷ cstack_interp cstk' a_tstk ∗
      "#Hp_ot_switcher" ∷ seal_pred ot_switcher ot_switcher_propC.

  (** Opens [switcher_inv] under the later of [na_inv_acc]: the timeless
      conjuncts lose their later, so that [iNamed] can name them. *)
  Lemma switcher_inv_open :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    ▷ switcher_inv -∗
    ◇ ∃ (a_tstk : Addr) (cstk' : CSTK) (save_area tstk_next : list LWord),
      let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
      "Hmtdc" ∷ mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
      "%Hot_bounds" ∷ ⌜(ot_switcher < (ot_switcher ^+1))%ot⌝ ∗
      "Hsave_area" ∷ [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
      "Hframeoffset" ∷ a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk')) ∗
      "HthreadID" ∷ (∃ w, a_threadID ↦ₐ w) ∗
      "Htstk" ∷ [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
      "Hcstk_full" ∷ cstack_full cstk' ∗
      "%Hlen_cstk" ∷ ⌜(b_trusted_stack + tstack_frame_offset (length cstk'))%a = Some a_tstk
                      ∧ (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z⌝ ∗
      "Hstk_interp" ∷ ▷ cstack_interp cstk' a_tstk ∗
      "#Hp_ot_switcher" ∷ ▷ seal_pred ot_switcher ot_switcher_propC.
  Proof.
    intros a_frameoffset a_save_end a_threadID; subst a_frameoffset a_save_end a_threadID.
    iIntros "Hinv". rewrite /switcher_inv /=.
    iDestruct "Hinv" as (a_tstk cstk' save_area tstk_next)
      "(>Hmtdc & >% & >Hsave_area & >Hframeoffset & >HthreadID & >Htstk & >Hcstk_full & >% & Hstk_interp
       & #Hp_ot_switcher)".
    iModIntro. iExists a_tstk, cstk', save_area, tstk_next. by iFrame "∗ # %".
  Qed.

  (** Close [switcher_inv] after popping the topmost frame, at [a_tstk],
      of the trusted stack: its cells go back to the unused part. *)
  Lemma switcher_inv_pop_frame
    (a_tstk : Addr) (cstk : CSTK) (save_area tstk_next : list LWord) (w0 w1 w2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_prev := (a_tstk ^+ - TrustedStackFrame_size)%a in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    (b_trusted_stack + tstack_frame_offset (S (length cstk)))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack -∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk)) -∗
    (∃ w, a_threadID ↦ₐ w) -∗
    a_csp ↦ₐ w0 -∗
    a_export_table ↦ₐ w1 -∗
    a_error_count ↦ₐ w2 -∗
    [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    cstack_full cstk -∗
    cstack_interp cstk a_prev -∗
    seal_pred ot_switcher ot_switcher_propC -∗
    switcher_inv.
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next a_prev a_csp a_export_table a_error_count.
    subst a_frameoffset a_save_end a_threadID a_next a_prev a_csp a_export_table a_error_count.
    iIntros (Hlen_cstk Ha_tstk_e Hot)
      "Hmtdc Hsave_area Hframeoffset HthreadID Hw0 Hw1 Hw2 Htstk Hcstk_full Hstk_interp #Hp_ot_switcher".
    iExists (a_tstk ^+ - TrustedStackFrame_size)%a, cstk, save_area, (w0 :: w1 :: w2 :: tstk_next).
    iFrame "Hmtdc Hsave_area Hframeoffset HthreadID Hcstk_full Hstk_interp Hp_ot_switcher".
    replace ((a_tstk ^+ - TrustedStackFrame_size) ^+ TrustedStackFrame_size)%a with a_tstk
      by (tstack_unfold; solve_addr).
    iSplit; first done.
    iSplitL "Hw0 Hw1 Hw2 Htstk".
    { iDestruct (region_pointsto_cons _ (a_tstk ^+ TrustedStackFrame_size)%a
                   with "[$Hw2 $Htstk]") as "Htstk"; [tstack_unfold; solve_addr..|].
      iDestruct (region_pointsto_cons _ (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a
                   with "[$Hw1 $Htstk]") as "Htstk"; [tstack_unfold; solve_addr..|].
      iEval (rewrite /TrustedStackFrame_offset_csp finz_add_0_default) in "Hw0".
      iDestruct (region_pointsto_cons _ (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a
                   with "[$Hw0 $Htstk]") as "Htstk"; [tstack_unfold; solve_addr..|].
      iFrame "Htstk". }
    iPureIntro; tstack_unfold; split; solve_addr.
  Qed.

  (** [switcher_static] holds the read-only memory of the switcher: its code,
      and the unsealing capability of the switcher's otype; and the fact that
      the trap vector is the exception entry of the switcher. *)
  Definition switcher_static : iProp Σ :=
    codefrag_pers a_switcher_call switcher_instrs ∗
    b_switcher ↦ₐ□ WSealRange true (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher ∗
    ⌜mtcc_vec =
       WCap true XSRW_ Local b_switcher e_switcher
         (a_switcher_call ^+
            asm_label_offset switcher_asm ".Lswitcher_csp_check_perm" "exception_entry_asm")%a⌝.

  #[global] Instance switcher_static_persistent : Persistent switcher_static.
  Proof. apply _. Qed.

End Switcher_preamble.

(** * Code of the switcher

    Shared definitions about the code of the switcher, used by the
    block-group lemmas of the call and return routines. *)

(** The offset of the first instruction of block [n] of the switcher, from
    [a_switcher_call]. *)
Notation switcher_block_offset := (code_block_offset assembled_switcher).

(** The offset of the label [s] of the switcher from [a_switcher_call], its
    first instruction (the label [.Lswitcher_csp_check_perm]). *)
Notation switcher_label_offset s :=
  (asm_label_offset switcher_asm ".Lswitcher_csp_check_perm" s).

(** The index of the block of the switcher that defines the label [s]. *)
Notation switcher_block s := (asm_block switcher_asm s).

(** The PC capability of the switcher at offset [off] of the code. *)
Notation switcher_pc off :=
  (WCap true XSRW_ Local b_switcher e_switcher (a_switcher_call ^+ off)%a) (only parsing).

(** The PC capability of the switcher at its label [s]. *)
Notation switcher_label_pc s := (switcher_pc (switcher_label_offset s)) (only parsing).

(** The code of the switcher. *)
Notation switcher_code := (codefrag_pers a_switcher_call switcher_instrs) (only parsing).

(** Unfold the code of the switcher in [h], in order to focus on its blocks. *)
Ltac switcher_unfold_code h :=
  iEval (rewrite /switcher_instrs /assembled_switcher) in h;
  repeat (iEval (cbn [fmap list_fmap]) in h);
  repeat (iEval (cbn [concat]) in h).

(** A trusted-stack address is not a shadow-table address, when [H] states
    that the trusted stack is disjoint from the shadow table. *)
Ltac tstk_not_shadow H :=
  eapply disjoint_from_shadow_not_in; [exact H | rewrite /withinBounds; tstack_unfold; solve_addr].

(** Change the PC to [a_switcher_call ^+ off]. *)
Ltac switcher_change_pc off := change_pc_to (a_switcher_call ^+ off)%a.

(** Focus on block [n] of the switcher, whose first address is
    [a_switcher_call ^+ switcher_block_offset n]. The PC is moved to this
    address, when possible. *)
Tactic Notation "switcher_focus_block" constr(n) constr(h)
    "as" constr(hi) constr(hcont) :=
  let n := eval vm_compute in n in
  let a := fresh "a_block" in
  let Ha := fresh "Ha_block" in
  focus_block_nochangePC n h as a Ha hi hcont;
  let Ha' := fresh in
  pose proof Ha as Ha'; cbn in Ha';
  assert (a = (a_switcher_call ^+ switcher_block_offset n)%a) as ->
    by (offsets_compute; solve_addr);
  clear Ha';
  try switcher_change_pc (switcher_block_offset n).

Section Switcher_Code.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_SubBounds :
    SubBounds b_switcher e_switcher a_switcher_call
      (a_switcher_call ^+ length switcher_instrs)%a.
  Proof.
    pose proof switcher_size.
    pose proof switcher_call_entry_point.
    solve_addr.
  Qed.

  Lemma switcher_return_offset :
    a_switcher_return =
      (a_switcher_call ^+ switcher_label_offset ".Lswitcher_after_compartment_call")%a.
  Proof.
    pose proof switcher_return_entry_point as Hret.
    pose proof switcher_call_entry_point as Hcall.
    pose proof switcher_size as Hsize.
    cbn in Hret, Hcall, Hsize.
    offsets_compute.
    solve_addr.
  Qed.

  (** A return through the switcher's return sentry passes the checks of
      [Jalr cnull cra]. *)
  Lemma jalr_target_ok_switcher_return_sentry mie :
    jalr_target_ok cnull cra
      (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return) = true.
  Proof. by destruct mie. Qed.

  (** The callee-save area of the caller's stack frame. *)
  Definition switcher_stk_cells (a : Addr) (w0 w1 w2 w3 : LWord) : iProp Σ :=
    a ↦ₐ w0 ∗
    (a ^+ 1)%a ↦ₐ w1 ∗
    (a ^+ 2)%a ↦ₐ w2 ∗
    (a ^+ 3)%a ↦ₐ w3.

  (** The bounds of the caller's stack frame, once the callee-save registers
      have been spilled. *)
  Definition switcher_stk_bounds (b e a : Addr) : Prop :=
    (b <= a)%a ∧ (b <= (a ^+ 3)%a < e)%a ∧ (a + 4)%a = Some (a ^+ 4)%a.

  Lemma switcher_stk_cells_region a w0 w1 w2 w3 e ws :
    (a + 4)%a = Some (a ^+ 4)%a ->
    (a ^+ 4 <= e)%a ->
    switcher_stk_cells a w0 w1 w2 w3 -∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ ws ]] -∗
    [[ a , e ]] ↦ₐ [[ w0 :: w1 :: w2 :: w3 :: ws ]].
  Proof.
    iIntros (Ha4 He) "Hcells Hstk".
    iApply (region_pointsto_region_cells_app a (a ^+ 4)%a e [w0; w1; w2; w3] ws);
      [done|done|].
    region_cells_simpl; iFrame.
  Qed.

  Lemma switcher_stk_cells_region_4 a w0 w1 w2 w3 :
    (a + 4)%a = Some (a ^+ 4)%a ->
    switcher_stk_cells a w0 w1 w2 w3 ⊣⊢
    [[ a , (a ^+ 4)%a ]] ↦ₐ [[ [w0; w1; w2; w3] ]].
  Proof.
    iIntros (Ha4); iSplit; iIntros "H".
    - iRegionMerge; iFrame.
    - iRegionSplit "H" as "H"; iFrame.
  Qed.

End Switcher_Code.
