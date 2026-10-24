From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Import switcher clear_registers_spec.

(** * The switcher's sealing predicate

    The register state and the WP rule of an entry point after the switcher's
    call routine, and the sealing predicate of the switcher's otype. *)

Section Switcher_sealing.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

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

  (** [csp_sync cstk b_stk' e_stk'] is a small pure side-condition that
      relates the stack pointer of the caller, saved in the topmost frame of
      [cstk], with the stack [[b_stk', e_stk')] of the callee: the callee's
      stack is the one that the switcher carved out of the caller's.
      See [execute_entry_point] to understand how they are related.
   *)
  Definition csp_sync (cstk : CSTK) (b_stk' e_stk' : Addr) :=
    match cstk.(cstk_frames) with
    | frm::_ =>
        stk_callee_b (cf_stk_b frm) (cf_caller_a frm) = b_stk'
        ∧ stk_callee_e (cf_stk_e frm) (cf_caller_a frm) = e_stk'
    | _ => True
    end
  .

  (** [tf_export_tbl_ok tf]: the word [tf_export_tbl] of the frame [tf] is a
      capability to an export table, at [tf_export_tbl_b tf], without
      identifier: the switcher loads the table's header through it. *)
  Definition tf_export_tbl_ok (tf : trusted_frame) : Prop :=
    exp_tbl_cap (tf_export_tbl_b tf) tf.(tf_export_tbl).(lw) ∧
    tf.(tf_export_tbl).(lprov) = None.

  (** [execute_entry_point] provides a WP rule matching the state of the machine
      after the execution of call-switcher.

      [execute_entry_point] is somewhat the dual of [interp_cont_exec]:
      - [execute_entry_point] matches the state of the machine after the execution of call-switcher
      - [interp_cont_exec] matches the state of the machine after the execution of return-to-switcher

      It is the WP rule to prove to show that the execution of an entry point is valid.
      In case of known code entry point, it contains all the information available when invoked.
      In case of unknown code entry point, we can show this by validity of
      the code and data capability (see [fundamental_execute_entry_point]).

      [b_tbl] is the base of the callee's export table: the switcher has pushed a
      frame for this call, so the call stack has a frame above the entry
      frame, and its topmost frame records the table word, whose base is
      [b_tbl] ([top_export_tbl]). For unknown code, this is what builds
      [top_cmpt_untrusted].

      An important point is the use of [csp_sync] and the stack capability
      [WCap true RWL Local b_stk e_stk (stk_start_a b_stk e_stk)] of the callee.
      We know that the caller's stack looks like
      [WCap true RWL Local b e a] (it is tested by the switcher's call routine).
      The switcher reserves the spill area, from [stk_spill_a a], for the
      callee-saved registers, and passes the callee's part
      [[stk_callee_b b a, stk_callee_e e a)] of the stack to the callee,
      with the cursor of a fresh stack: [b_stk] and [e_stk] are its bounds.

      [csp_sync] synchronises the caller's stack pointer with the callee stack pointer.
      It's important when proving the functional specification of the return-to-switcher routine,
      because the switcher uses the caller stack pointer to clear (and therefore re-instate) the stack.
      But the caller gives the `revoked_resources` of its own stack pointer.
      Synchronising the caller and callee is important for using the caller's `revoked_resources`
      to re-instate validity of the caller's stack.
      This will become clearer in the proof of [switcher_ret_specification].
   *)
  Program Definition execute_entry_point (b_tbl : Addr) (wpcc wcgp : LWord) (nargs minstk : nat) :
    (WORLD -n> (leibnizO CmptName) -n> iPropO Σ) :=
    (λne (W : WORLD) (C : CmptName),
      ∀ (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) regs b_stk e_stk,
       ( interp_continuation cstk Ws Cs
         ∗ ⌜frame_match Ws Cs cstk W C⌝
         (* The switcher pushed a frame for the call of the compartment of the
            export table at [b_tbl], with no fault yet and the unsealed entry
            in its table cell. *)
         ∗ ⌜cstk.(cstk_frames) ≠ [] ∧ top_export_tbl cstk = b_tbl ∧
            top_error_count cstk = 0 ∧ tf_export_tbl_ok (top_tframe cstk)⌝
         ∗ PC ↦ₚ wpcc
         ∗ (execute_entry_point_register wcgp
              (WCap true RWL Local b_stk e_stk (stk_start_a b_stk e_stk)) nargs W C regs)
         ∗ registers_pointsto regs
         ∗ world_interp W C
         ∗ ⌜csp_sync cstk b_stk e_stk⌝
         (* The switcher checked that the callee's stack holds the minimum
            stack size of the entry point plus the space reserved at its
            top. *)
         ∗ ⌜(Z.of_nat minstk + StackEntry_reserved_space <= e_stk - b_stk)%Z⌝
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
      the offsets of its stackful and stackless error handlers,
      and then a list of entries of the form [(posture,nargs,minstk,offset)],
      where [posture] is the interrupt posture the callee runs with,
      [nargs] is the number of argument (up-to 7),
      [minstk] is the minimum size of the callee's stack, in words (up-to 255),
      and [offset] is the offset of the function in the code,
      from the first address of the PCC (i.e., we must take account for the RO global data, like the imports).

      [ot_switcher_prop] describes the logical state of the physical state described above:
      the export table's PCC and CGP, and the entry itself, as persistent points-to,
      and the handler offsets of the header, as projections ([↦ₕ□{stackful}],
      [↦ₕ□{stackless}]) of any value.
      The entry word determines the number of arguments [nargs] the callee uses
      (the switcher clears the other argument registers); callers of a known entry
      read it through [↦ₑ□{nargs}] on the entry's address or its sealable.

      Finally, [execute_entry_point] is called with the table base [b_tbl],
      [PCC+off] in the [PC],
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
          (eh ehs : Z),
           let a_tbl_cgp := (b_tbl ^+ ExportTable_offset_cgp)%a in
           let a_tbl_ehs := (b_tbl ^+ ExportTable_offset_errorHandlerStackless)%a in
           "%Hw" ∷ ⌜ w = WCap true RO g_tbl b_tbl e_tbl a_tbl ⌝ ∗
           "%Htbl_shadow" ∷ ⌜ disjoint_from_shadow b_tbl e_tbl ⌝ ∗
           "%Hatbl" ∷ ⌜ (b_tbl <= a_tbl < e_tbl)%a ⌝ ∗
           "%Hbtbl" ∷ ⌜ (b_tbl < a_tbl_cgp)%a ⌝ ∗
           "%Hbtbl_header" ∷ ⌜ (a_tbl_ehs < a_tbl)%a ⌝ ∗
           "%Hnargs" ∷ ⌜ (0 <= nargs <= 7 )%nat ⌝ ∗
           "%Hminstk" ∷ ⌜ (minstk <= 255)%nat ⌝ ∗
           "%Hentry_some" ∷ ⌜ is_Some (bpcc + off)%a ⌝ ∗
           "%Hatbl_shadow" ∷ ⌜ is_shadow_address a_tbl = false ⌝ ∗
           "%Hbtbl_shadow" ∷ ⌜ is_shadow_address b_tbl = false ⌝ ∗
           "%Hbtbl_cgp_shadow" ∷ ⌜ is_shadow_address a_tbl_cgp = false ⌝ ∗
           "%Hbpcc_heap" ∷ ⌜ is_heap_address bpcc = false ⌝ ∗
           "%Hbcgp_heap" ∷ ⌜ is_heap_address bcgp = false ⌝ ∗
           "#Htbl_pcc" ∷ b_tbl ↦ₐ□ WCap true RX Global bpcc epcc bpcc ∗
           "#Htbl_cgp" ∷ a_tbl_cgp ↦ₐ□ WCap true RW Global bcgp ecgp bcgp ∗
           "#Htbl_eh" ∷ b_tbl ↦ₕ□{stackful} eh ∗
           "#Htbl_ehs" ∷ b_tbl ↦ₕ□{stackless} ehs ∗
           "#Htbl_entry" ∷
             a_tbl ↦ₐ□ WInt (encode_entry_point posture (Z.of_nat nargs) (Z.of_nat minstk) off) ∗
           "#Hentry_cont" ∷
             □ ( ∀ W', ⌜related_sts_priv_world W W'⌝ →
                   ▷ (execute_entry_point b_tbl
                            (WCap true RX Global bpcc epcc (bpcc ^+ off)%a)
                            (WCap true RW Global bcgp ecgp bcgp)
                            nargs minstk
                            W' C))
      )%I.
  Solve All Obligations with solve_proper.

  Definition ot_switcher_propC : (WORLD * CmptName * LWord) -> iPropI Σ :=
    safeC ot_switcher_prop.

  (** Monotonicity of [ot_switcher_prop] in the world, and its stability
      under [lborrow]. *)
  Lemma mono_priv_ot_switcher (C : CmptName) (w : LWord) :
    ⊢ future_priv_mono C ot_switcher_propC w.
  Proof.
    iIntros (W W' Hrelated_W_W').
    iModIntro.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iNamed "Hot_switcher".
    iExists g_tbl, b_tbl, e_tbl, a_tbl, bpcc, epcc, bcgp, ecgp, nargs, minstk, off, posture,
      eh, ehs.
    repeat (iSplitR; [iPureIntro; assumption|]).
    iFrame "Htbl_pcc Htbl_cgp Htbl_eh Htbl_ehs Htbl_entry".
    iIntros "!>" (W'' Hrelated_W'_W'').
    iApply "Hentry_cont".
    iPureIntro.
    by eapply related_sts_priv_trans_world.
  Qed.

  Lemma ot_switcher_prop_borrow (W : WORLD) (C : CmptName) (w : LWord) :
    ot_switcher_prop W C w -∗ ot_switcher_prop W C (lborrow w).
  Proof.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iNamed "Hot_switcher". subst w.
    iExists Local, b_tbl, e_tbl, a_tbl, bpcc, epcc, bcgp, ecgp, nargs, minstk, off, posture,
      eh, ehs.
    iSplitR; [done|].
    repeat (iSplitR; [iPureIntro; assumption|]).
    iFrame "Htbl_pcc Htbl_cgp Htbl_eh Htbl_ehs Htbl_entry Hentry_cont".
  Qed.

End Switcher_sealing.
