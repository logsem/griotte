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

(** The number of arguments of an export entry, given by its address in the
    export table or by the sealable that points to it. *)
Class EntryNargs (Σ : gFunctors) (K : Type) := entry_nargs_at : K → nat → iProp Σ.
#[global] Arguments entry_nargs_at {Σ K _} _ _.
#[export] Hint Mode EntryNargs - ! : typeclass_instances.

Notation "a ↦ₑ□{nargs} n" := (entry_nargs_at a n)
  (at level 20, format "a  ↦ₑ□{nargs}  n") : bi_scope.

Section Entry_projections.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

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

  (** Projections of an export-table entry: the entry at [a] encodes
      [n] arguments ([entry_nargs]), a minimum stack of [m] words
      ([entry_min_stack]), or the interrupt posture [ie] ([entry_irq]).
      Each is persistent, and the bound of its field is part of it. *)
  Definition entry_nargs (a : Addr) (n : nat) : iProp Σ :=
    ⌜n ≤ 7⌝ ∗ ∃ ie (m : nat) (off : Z), a ↦ₐ□ WInt (encode_entry_point ie n m off).
  Definition entry_min_stack (a : Addr) (m : nat) : iProp Σ :=
    ⌜m ≤ 255⌝ ∗ ∃ ie (n : nat) (off : Z), a ↦ₐ□ WInt (encode_entry_point ie n m off).
  Definition entry_irq (a : Addr) (ie : InterruptStatus) : iProp Σ :=
    ∃ (n m : nat) (off : Z), a ↦ₐ□ WInt (encode_entry_point ie n m off).

  #[global] Instance entry_nargs_addr : EntryNargs Σ Addr := entry_nargs.

  (** The entry of a sealable that is a read-only capability to an export
      table entry. *)
  Definition entry_nargs_sb (sb : Sealable) (n : nat) : iProp Σ :=
    ∃ g b e a, ⌜sb = SCap true RO g b e a⌝ ∗ a ↦ₑ□{nargs} n.
  #[global] Instance entry_nargs_sealable : EntryNargs Σ Sealable := entry_nargs_sb.

  #[global] Instance entry_nargs_persistent (a : Addr) n : Persistent (a ↦ₑ□{nargs} n).
  Proof. apply _. Qed.
  #[global] Instance entry_nargs_sb_persistent (sb : Sealable) n :
    Persistent (sb ↦ₑ□{nargs} n).
  Proof. apply _. Qed.
  #[global] Instance entry_min_stack_persistent a m : Persistent (entry_min_stack a m).
  Proof. apply _. Qed.
  #[global] Instance entry_irq_persistent a ie : Persistent (entry_irq a ie).
  Proof. apply _. Qed.

  Lemma entry_nargs_intro (a : Addr) ie (n m : nat) off :
    n ≤ 7 →
    a ↦ₐ□ WInt (encode_entry_point ie n m off) ⊢ a ↦ₑ□{nargs} n.
  Proof. iIntros (Hn) "Ha". iSplit; [done|]. iExists _, _, _; iFrame. Qed.

  Lemma entry_nargs_sb_intro g b e (a : Addr) n :
    a ↦ₑ□{nargs} n ⊢ (SCap true RO g b e a) ↦ₑ□{nargs} n.
  Proof. iIntros "Ha". iExists _, _, _, _. by iFrame "Ha". Qed.

  Lemma entry_min_stack_intro a ie (n m : nat) off :
    m ≤ 255 →
    a ↦ₐ□ WInt (encode_entry_point ie n m off) ⊢ entry_min_stack a m.
  Proof. iIntros (Hm) "Ha". iSplit; [done|]. iExists _, _, _; iFrame. Qed.

  Lemma entry_irq_intro a ie (n m : nat) off :
    a ↦ₐ□ WInt (encode_entry_point ie n m off) ⊢ entry_irq a ie.
  Proof. iIntros "Ha". iExists _, _, _; iFrame. Qed.

  Lemma entry_nargs_agree_raw (a : Addr) (n n' m : nat) ie off :
    n' ≤ 7 →
    a ↦ₑ□{nargs} n -∗
    a ↦ₐ□ WInt (encode_entry_point ie n' m off) -∗
    ⌜n = n'⌝.
  Proof.
    iIntros (Hn') "[%Hn (%ie0 & %m0 & %off0 & Ha0)] Ha".
    iDestruct (pointsto_agree with "Ha0 Ha") as %Heq.
    simplify_eq.
    apply (f_equal (λ z, Z.land z 7)) in Heq.
    rewrite !encode_entry_point_eq_nargs in Heq; [|lia|lia].
    iPureIntro; lia.
  Qed.

  Lemma entry_nargs_agree (a : Addr) n n' :
    a ↦ₑ□{nargs} n -∗ a ↦ₑ□{nargs} n' -∗ ⌜n = n'⌝.
  Proof.
    iIntros "Hn [%Hn' (%ie & %m & %off & Ha)]".
    iApply (entry_nargs_agree_raw with "Hn Ha"); done.
  Qed.

  Lemma entry_min_stack_agree a m m' :
    entry_min_stack a m -∗ entry_min_stack a m' -∗ ⌜m = m'⌝.
  Proof.
    iIntros "[%Hm (%ie & %n & %off & Ha)] [%Hm' (%ie' & %n' & %off' & Ha')]".
    iDestruct (pointsto_agree with "Ha Ha'") as %Heq.
    simplify_eq.
    apply (f_equal (λ z, Z.land (z ≫ 8) 255)) in Heq.
    rewrite !encode_entry_point_eq_minstk in Heq; [|lia|lia].
    iPureIntro; lia.
  Qed.

  Lemma entry_irq_agree a ie ie' :
    entry_irq a ie -∗ entry_irq a ie' -∗ ⌜ie = ie'⌝.
  Proof.
    iIntros "(%n & %m & %off & Ha) (%n' & %m' & %off' & Ha')".
    iDestruct (pointsto_agree with "Ha Ha'") as %Heq.
    simplify_eq.
    apply (f_equal (λ z, Z.land z entry_point_irq_disabled_mask)) in Heq.
    rewrite !encode_entry_point_eq_posture in Heq.
    iPureIntro.
    destruct ie, ie'; done.
  Qed.

End Entry_projections.

Notation "a ↦ₑ□{stack} m" := (entry_min_stack a m)
  (at level 20, format "a  ↦ₑ□{stack}  m") : bi_scope.
Notation "a ↦ₑ□{irq} ie" := (entry_irq a ie)
  (at level 20, format "a  ↦ₑ□{irq}  ie") : bi_scope.

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
         (* The switcher checked that the callee's stack is at least the
            minimum stack size of the entry point. *)
         ∗ ⌜(Z.of_nat minstk <= e_stk - b_stk)%Z⌝
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
    iFrame "#%".
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
    iFrame "#∗%".
    iExists Local; iPureIntro; done.
  Qed.

  (** The export table cell of a pushed frame, as the call path writes it:
      cleared, before the entry unseals... *)
  Lemma tf_export_tbl_cell_cleared (tf : trusted_frame) :
    tf.(tf_export_tbl) = lword_of_word (WInt 0) →
    tf.(tf_export_tbl) = lword_of_word (WInt 0) ∨ tf_export_tbl_ok tf.
  Proof. by left. Qed.

  (** ... or holding the unsealed entry, a capability to the export table. *)
  Lemma tf_export_tbl_cell_entry (tf : trusted_frame) g b e a :
    tf.(tf_export_tbl) = lword_of_word (WCap true RO g b e a) →
    (b ^+ ExportTable_offset_errorHandlerStackless < a)%a →
    (a < e)%a →
    disjoint_from_shadow b e →
    tf_export_tbl_ok tf.
  Proof.
    intros Htbl Hb Ha Hshadow.
    rewrite /tf_export_tbl_ok /tf_export_tbl_b Htbl /=. split; last done.
    by apply exp_tbl_cap_entry.
  Qed.

  (** [trusted_frame_interp entry tf a_tstk] interprets the frame [tf] of the
      trusted stack at [a_tstk]: its three cells hold the stack pointer
      [tf_csp], the capability [tf_export_tbl] to the export table of the
      callee, and the error handler count [tf_error_count].
      The export table cell of the entry frame ([entry = true]) is written
      once, by the loader: it holds the capability for good. The export
      table cell of a pushed frame holds the frame's word: the unsealed
      entry, or [WInt 0] for a frame unwound because its entry does not
      unseal (the call path clears the cell before it unseals).
   *)
  Definition trusted_frame_interp (entry : bool) (tf : trusted_frame) (a_tstk : Addr) : iProp Σ :=
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    ("Htf_csp" ∷ a_csp ↦ₐ tf.(tf_csp) ∗
     "Htf_tbl" ∷ (if entry
                  then a_export_table ↦ₐ□ tf.(tf_export_tbl) ∗ ⌜tf_export_tbl_ok tf⌝
                  else a_export_table ↦ₐ tf.(tf_export_tbl) ∗
                         ⌜tf.(tf_export_tbl) = lword_of_word (WInt 0) ∨
                          tf_export_tbl_ok tf⌝) ∗
     "Htf_cnt" ∷ a_error_count ↦ₐ WInt tf.(tf_error_count))%I.

  (** The four cells of the spill area from [a], in address order: the
      slots [SpillSlot_cs0], [SpillSlot_cs1], [SpillSlot_cgp] and
      [SpillSlot_pcc]. *)
  Definition switcher_stk_cells (a : Addr) (w0 w1 w2 w3 : LWord) : iProp Σ :=
    a ↦ₐ w0 ∗
    (a ^+ SpillSlot_cs1)%a ↦ₐ w1 ∗
    (a ^+ SpillSlot_cgp)%a ↦ₐ w2 ∗
    (a ^+ SpillSlot_pcc)%a ↦ₐ w3.

  (** [cframe_stk_own s saved ccrel] holds the spill area
      [[s, s + SpillSlot_size)] where the switcher spilled the callee-saved
      registers [saved] of the caller. We have 2 situations to take into account:
      - If the caller is untrusted, the points-to predicate of the callee-save region
        are stored in the region invariant, which means that their content is controlled by adversary,
        and does not have to match with the call-frame.
      - If the caller is trusted, the switcher controls the callee-save region,
        and the content should match the words of the call-frame.
   *)
  Definition cframe_stk_own (a_stk : Addr) (saved : callee_saved_registers)
    (ccrel : caller_callee_relation) : iProp Σ :=
    (if (is_untrusted_caller ccrel)
    then True
    else
      switcher_stk_cells a_stk saved.(cs_cs0) saved.(cs_cs1) saved.(cs_cgp) saved.(cs_cra))%I.

  (** The spill area of a caller whose cursor is [a] lies in its stack
      [[b, e)], and does not wrap around. *)
  Definition switcher_stk_bounds (b e a : Addr) : Prop :=
    (b <= stk_spill_a a)%a ∧
    (b <= (stk_spill_a a ^+ (SpillSlot_size - 1))%a < e)%a ∧
    stk_spill_ok a.

  (** [cframe_interp] interprets a call-frame, i.e.,
      describes how the physical call-frame is linked to the logical call-frame [frm : cframe]:
      its frame of the trusted stack, whose stack pointer is the stack of
      the caller [[b_stk, e_stk)] with the cursor saved after the spill at
      the caller's cursor [a_stk]; and the spill area.
   *)
  Definition cframe_interp (frm : cframe) (a_tstk : Addr) : iProp Σ :=
    "Hcf_tframe" ∷ trusted_frame_interp false frm.(cf_tframe) a_tstk ∗
    ∃ b_stk e_stk a_stk : Addr,
    "%Hcf_csp" ∷
      ⌜ frm.(cf_tframe).(tf_csp) = WCap true RWL Local b_stk e_stk (stk_saved_a a_stk) ∧
        switcher_stk_bounds b_stk e_stk a_stk ∧
        disjoint_from_mmio b_stk e_stk ∧ disjoint_from_heap b_stk e_stk ∧
        (* a trusted caller returns to a valid target, outside the heap *)
        (is_untrusted_caller_frm frm = false →
         jalr_target_ok cnull cra frm.(cf_saved).(cs_cra).(lw) = true ∧
         is_heap_cap frm.(cf_saved).(cs_cra).(lw) = false) ⌝ ∗
    "Hcf_spill" ∷ cframe_stk_own (stk_spill_a a_stk) frm.(cf_saved) frm.(ccrel).

  (** [frames_interp ef frms a_tstk] interprets the frames [frms], the
      topmost at [a_tstk] in the trusted stack, above the entry frame [ef]. *)
  Fixpoint frames_interp (ef : trusted_frame) (frms : list cframe) (a_tstk : Addr) : iProp Σ :=
    (match frms with
    | [] => trusted_frame_interp true ef a_tstk
    | frm::frms' =>
        let a_prev := (a_tstk ^+ - TrustedStackFrame_size)%a in
        frames_interp ef frms' a_prev ∗ cframe_interp frm a_tstk
    end)%I.

  (** [cstack_interp] interprets a call-stack, whose topmost frame is at
      [a_tstk] in the trusted stack: the frames pushed by the calls, and,
      below them, the entry frame of the thread, [frames[0]]. *)
  Definition cstack_interp (cstk : cstack) (a_tstk : Addr) : iProp Σ :=
    frames_interp cstk.(cstk_entry) cstk.(cstk_frames) a_tstk.

  (** Open the three cells of the topmost frame, whether it is the entry
      frame or a pushed frame; close them with any error handler count. *)
  Lemma cstack_interp_open_top (cstk : CSTK) (a_tstk : Addr) :
    cstack_interp cstk a_tstk ⊢
    trusted_frame_interp (top_is_entry cstk) (top_tframe cstk) a_tstk ∗
    (∀ n, trusted_frame_interp (top_is_entry cstk) (tf_set_count (top_tframe cstk) n) a_tstk -∗
          cstack_interp (cstack_set_top_count cstk n) a_tstk).
  Proof.
    destruct cstk as [ef [|frm frms] ]; rewrite /cstack_interp /=.
    - iIntros "Htf". iFrame "Htf". by iIntros (n) "Htf".
    - iIntros "[Hrest [Htf Hspill]]". iFrame "Htf". iIntros (n) "Htf". iFrame.
  Qed.

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
      "Hframeoffset" ∷ a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      "HthreadID" ∷ (∃ w, a_threadID ↦ₐ w) ∗
      "Htstk" ∷ [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
      "Hcstk_full" ∷ cstack_full cstk' ∗
      "%Hlen_cstk" ∷
        ⌜(b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk
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
      "Hframeoffset" ∷ a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      "HthreadID" ∷ (∃ w, a_threadID ↦ₐ w) ∗
      "Htstk" ∷ [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
      "Hcstk_full" ∷ cstack_full cstk' ∗
      "%Hlen_cstk" ∷
        ⌜(b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk
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
    (b_trusted_stack + tstack_frame_offset (S (length cstk.(cstk_frames))))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack -∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk.(cstk_frames))) -∗
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
            asm_label_offset switcher_asm ".Lswitch_csp_check" "exception_entry_asm")%a⌝.

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
    first instruction (the label [.Lswitch_csp_check]). *)
Notation switcher_label_offset s :=
  (asm_label_offset switcher_asm ".Lswitch_csp_check" s).

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
      (a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call")%a.
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


  Lemma switcher_stk_cells_region_4 a w0 w1 w2 w3 :
    (a + SpillSlot_size)%a = Some (a ^+ SpillSlot_size)%a ->
    switcher_stk_cells a w0 w1 w2 w3 ⊣⊢
    [[ a , (a ^+ SpillSlot_size)%a ]] ↦ₐ [[ [w0; w1; w2; w3] ]].
  Proof.
    rewrite /SpillSlot_size.
    iIntros (Ha4); iSplit; iIntros "H".
    - iRegionMerge; iFrame.
    - iRegionSplit "H" as "H"; iFrame.
  Qed.

  (** The spill area ends at the cursor. *)
  Lemma stk_spill_a_end a : stk_spill_ok a → (stk_spill_a a ^+ SpillSlot_size)%a = a.
  Proof. stk_unfold; solve_addr. Qed.

  (** The free part of a caller's stack splits into its spill area and the
      callee's stack. *)
  Lemma stk_free_split_addrs b e a :
    switcher_stk_bounds b e a →
    stk_free b e a =
      stk_mem_join (finz.seq_between (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)%a)
        (callee_stk_region b e a).
  Proof.
    rewrite /switcher_stk_bounds; intros (Hb & Hb3 & Ha4).
    rewrite stk_spill_a_end //. stk_unfold.
    apply finz_seq_between_split; solve_addr.
  Qed.

  Lemma stk_free_split_zeroes b e a :
    switcher_stk_bounds b e a →
    region_addrs_zeroes (stk_free_b b a) (stk_free_e e a) =
      stk_mem_join (region_addrs_zeroes (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)%a)
        (region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a)).
  Proof.
    rewrite /switcher_stk_bounds; intros (Hb & Hb3 & Ha4).
    rewrite stk_spill_a_end //. stk_unfold.
    apply region_addrs_zeroes_split; solve_addr.
  Qed.

  Lemma stk_free_split_join b e a (ls lc : list LWord) :
    switcher_stk_bounds b e a →
    length ls = Z.to_nat SpillSlot_size →
    [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ stk_mem_join ls lc ]] ⊣⊢
    [[ stk_spill_a a , (stk_spill_a a ^+ SpillSlot_size)%a ]] ↦ₐ [[ ls ]] ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ lc ]].
  Proof.
    rewrite /switcher_stk_bounds.
    intros (Hb & Hb3 & Ha4) Hls.
    rewrite stk_spill_a_end //. stk_unfold.
    rewrite region_pointsto_split_r; [by rewrite bi.sep_comm|solve_addr|].
    rewrite Hls /finz.dist. solve_addr.
  Qed.

  Lemma stk_free_split b e a (l : list LWord) :
    switcher_stk_bounds b e a →
    length l = length (stk_free b e a) →
    [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ l ]] ⊣⊢
    [[ stk_spill_a a , (stk_spill_a a ^+ SpillSlot_size)%a ]] ↦ₐ [[ stk_mem_spill l ]] ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem_callee l ]].
  Proof.
    intros Hbounds Hl.
    rewrite -stk_free_split_join //.
    - by rewrite /stk_mem_join /stk_mem_spill /stk_mem_callee take_drop.
    - rewrite /stk_mem_spill length_drop Hl /stk_free finz_seq_between_length.
      revert Hbounds; rewrite /switcher_stk_bounds; stk_unfold; intros (Hb & Hb3 & Ha4).
      rewrite /finz.dist. solve_addr.
  Qed.

  (** The spill area and the callee's stack make the free part. *)
  Lemma switcher_stk_cells_region b e a w0 w1 w2 w3 lc :
    switcher_stk_bounds b e a →
    switcher_stk_cells (stk_spill_a a) w0 w1 w2 w3 -∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ lc ]] -∗
    [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ stk_mem_join [w0; w1; w2; w3] lc ]].
  Proof.
    iIntros (Hbounds) "Hcells Hstk".
    rewrite stk_free_split_join //.
    iFrame "Hstk".
    iApply switcher_stk_cells_region_4; last done.
    destruct Hbounds as (_ & _ & Ha). revert Ha; stk_unfold. solve_addr.
  Qed.

  (** The callee's stack is in the caller's. *)
  Lemma callee_stk_region_incl b e a x :
    callee_stk_bounds b e a →
    x ∈ callee_stk_region b e a →
    (b <= x < e)%a.
  Proof.
    stk_unfold; intros (Hb & He & Hbe & Ha) Hx.
    apply elem_of_finz_seq_between in Hx. solve_addr.
  Qed.

  (** A fresh stack: its free part is the whole stack. *)
  Lemma stk_start_free_b (b e : Addr) : stk_free_b b (stk_start_a b e) = b.
  Proof. done. Qed.
  Lemma stk_start_free_e (b e : Addr) : stk_free_e e (stk_start_a b e) = e.
  Proof. done. Qed.
  Lemma stk_start_cursor_ok (b e : Addr) : (b <= e)%a → stk_cursor_ok b e (stk_start_a b e).
  Proof. stk_unfold; solve_addr. Qed.
  Lemma stk_start_callee_fits (b e : Addr) n :
    (b + SpillSlot_size + n <= e)%Z → stk_callee_fits b e (stk_start_a b e) n.
  Proof. stk_unfold; lia. Qed.
  Lemma stk_start_spill_fits (b e : Addr) :
    (b + SpillSlot_size <= e)%Z → stk_spill_fits b e (stk_start_a b e).
  Proof. stk_unfold; lia. Qed.

  (** A callee that fits leaves room for the spill. *)
  Lemma stk_callee_fits_spill_fits (b e a : Addr) n :
    (0 <= n)%Z → stk_callee_fits b e a n → stk_spill_fits b e a.
  Proof. stk_unfold; lia. Qed.

  (** The spill of a caller whose callee fits does not wrap around. *)
  Lemma stk_callee_fits_spill_ok (b e a : Addr) n :
    (0 <= n)%Z → stk_callee_fits b e a n → stk_spill_ok a.
  Proof. stk_unfold; intros Hn Hfits. solve_addr. Qed.

  (** A callee that fits has its [n] words in its stack. *)
  Lemma stk_callee_fits_callee (b e a : Addr) n :
    stk_spill_ok a →
    stk_callee_fits b e a n →
    (n <= stk_callee_e e a - stk_callee_b b a)%Z.
  Proof. stk_unfold; intros Ha Hn. solve_addr. Qed.

  (** The faults whose context the exception path of the switcher does not
      resume: every fault but one of the first spill of the call path
      ([.Lswitch_entry_first_spill]), which the exception path resumes as
      a return of [-ENOTENOUGHSTACK]. The exception path tests the base and
      the address of the faulting PC, as MEPCC holds it. *)
  Definition trap_no_resume (w : LWord) : Prop :=
    get_b (lmepcc_of_pc w).(lw) ≠ (b_switcher : Z) ∨
    get_a (lmepcc_of_pc w).(lw) ≠
      ((a_switcher_call ^+ switcher_label_offset ".Lswitch_entry_first_spill")%a : Z).

  Lemma get_b_mepcc_of_pc w : get_b (mepcc_of_pc w) = get_b w.
  Proof.
    rewrite /mepcc_of_pc. case_match; last done.
    destruct w as [z|sb|k t p g b e a|ot sb]; try destruct sb; reflexivity.
  Qed.

  Lemma get_a_mepcc_of_pc w : get_a (mepcc_of_pc w) = get_a w.
  Proof.
    rewrite /mepcc_of_pc. case_match; last done.
    destruct w as [z|sb|k t p g b e a|ot sb]; try destruct sb; reflexivity.
  Qed.

  (** A fault outside the switcher's code is not resumed. *)
  Lemma trap_no_resume_base w :
    get_b w.(lw) ≠ (b_switcher : Z) → trap_no_resume w.
  Proof. intros Hb. left. by rewrite /lmepcc_of_pc /= get_b_mepcc_of_pc. Qed.

  (** A fault of code outside the switcher's PC is not resumed. *)
  Lemma trap_no_resume_cap (t : bool) (p : Perm) (g : Locality) (b e a : Addr) :
    b ≠ b_switcher → trap_no_resume (WCap t p g b e a).
  Proof. intros Hb. apply trap_no_resume_base. cbn. intros Heq. apply Hb. solve_addr. Qed.

  (** A fault at another address than the first spill is not resumed. *)
  Lemma trap_no_resume_addr w :
    get_a w.(lw) ≠ ((a_switcher_call ^+ switcher_label_offset ".Lswitch_entry_first_spill")%a : Z) →
    trap_no_resume w.
  Proof. intros Ha. right. by rewrite /lmepcc_of_pc /= get_a_mepcc_of_pc. Qed.

  (** A fault at any other instruction of the switcher is not resumed. The
      premise computes. *)
  Lemma trap_no_resume_switcher_pc (off : Z) :
    ((0 <=? off) && (off <? length switcher_instrs) &&
       negb (off =? switcher_label_offset ".Lswitch_entry_first_spill"))%Z = true →
    trap_no_resume (switcher_pc off).
  Proof.
    intros Hoff.
    apply andb_true_iff in Hoff as [Hoff Hne]. apply andb_true_iff in Hoff as [H0 Hlt].
    apply Z.leb_le in H0. apply Z.ltb_lt in Hlt. apply negb_true_iff, Z.eqb_neq in Hne.
    apply trap_no_resume_addr. cbn.
    pose proof switcher_size as Hsize. pose proof switcher_call_entry_point as Hcall.
    assert (switcher_label_offset ".Lswitch_entry_first_spill" = 8%Z) as Hfirst
      by reflexivity.
    rewrite Hfirst in Hne |- *.
    remember (length switcher_instrs) as len.
    solve_addr.
  Qed.

  (** A fault at the first spill is resumed. *)
  Lemma trap_no_resume_first_spill :
    ¬ trap_no_resume (switcher_label_pc ".Lswitch_entry_first_spill").
  Proof.
    rewrite /trap_no_resume /lmepcc_of_pc /= get_b_mepcc_of_pc get_a_mepcc_of_pc.
    by intros [Hb | Ha].
  Qed.

End Switcher_Code.
