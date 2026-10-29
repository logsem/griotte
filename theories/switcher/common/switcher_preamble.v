From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Import bitblast.
From griotte Require Import map_simpl register_tactics.
From griotte Require Export code_blocks.
From griotte Require Export switcher switcher_tactics.
From griotte Require Export clear_stack_spec clear_registers_spec.
From griotte Require Export switcher_sealing.
From griotte Require Export switcher_namespace.

(** The user-thread number of a thread. The context-switch thread has no
    trusted stack: it gets thread 0's layout, which it never uses. *)
Definition thread_index (th : Thread) : nat :=
  match th with UserThread i => i | CtxSwitch => 0 end.

(** The layout of the section's thread: [b_trusted_stack] in a thread section
    is that thread's. *)
#[global] Instance tlayout_of {swlayout : switcherLayout} (th : Thread) : threadLayout :=
  swl_thread (thread_index th).
#[global] Instance tlayout_wf_of `{MP : MachineParameters}
  {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  (th : Thread) : threadLayoutWf (tlayout := tlayout_of th) := swl_thread_wf _.
#[global] Arguments tlayout_of : simpl never.
#[global] Arguments tlayout_wf_of : simpl never.

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

(** A read of mtdc, which holds the trusted stack up to the Global bit,
    gives the capability with some locality. *)
Lemma mtdc_match_TStack_cap p b e a (vm : LWord) :
  mtdc_match (Capₗ p _ b e a) vm →
  ∃ g', vm = Cap p g' b e a.
Proof. done. Qed.

(** A write of the trusted stack to mtdc, with any locality. *)
Lemma mtdc_match_TStack_cap_any p g' b e a :
  mtdc_match (Capₗ p _ b e a) (Cap p g' b e a).
Proof. by eexists. Qed.

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
    { rewrite /encode_entry_point /entry_point_posture /ExportEntryInterruptStatusSwitcherMask.
      destruct mie; bitblast. }
    change 7%Z with (Z.ones 3).
    rewrite Z.land_ones; last lia.
    apply Z.mod_small; lia.
  Qed.

  Lemma encode_entry_point_eq_posture mie nargs minstk off_entry :
    Z.land (encode_entry_point mie nargs minstk off_entry) ExportEntryInterruptStatusSwitcherMask =
    entry_point_posture mie.
  Proof.
    rewrite /encode_entry_point /entry_point_posture /ExportEntryInterruptStatusSwitcherMask.
    destruct mie; bitblast.
  Qed.

  Lemma encode_entry_point_eq_minstk mie nargs minstk off_entry :
    (0 ≤ minstk ≤ 255)%Z ->
    Z.land (encode_entry_point mie nargs minstk off_entry ≫ 8) 255 = minstk.
  Proof.
    intros Hminstk.
    transitivity (Z.land minstk 255).
    { rewrite /encode_entry_point /entry_point_posture /ExportEntryInterruptStatusSwitcherMask.
      destruct mie; bitblast. }
    change 255%Z with (Z.ones 8).
    rewrite Z.land_ones; last lia.
    apply Z.mod_small; lia.
  Qed.

  Lemma encode_entry_point_eq_flags mie nargs minstk off_entry :
    Z.land (encode_entry_point mie nargs minstk off_entry) 255 =
    entry_point_flags mie nargs.
  Proof.
    rewrite /encode_entry_point /entry_point_flags /entry_point_posture
      /ExportEntryInterruptStatusSwitcherMask.
    destruct mie; bitblast.
  Qed.

  Lemma entry_point_flags_nargs mie nargs :
    (0 ≤ nargs ≤ 7)%Z ->
    Z.land (entry_point_flags mie nargs) 7 = nargs.
  Proof.
    intros Hnargs.
    rewrite -(encode_entry_point_eq_flags mie nargs 0 0) -Z.land_assoc.
    change (Z.land 255 7) with 7%Z.
    by apply encode_entry_point_eq_nargs.
  Qed.

  Lemma entry_point_flags_posture mie nargs :
    Z.land (entry_point_flags mie nargs) ExportEntryInterruptStatusSwitcherMask =
    entry_point_posture mie.
  Proof.
    rewrite -(encode_entry_point_eq_flags mie nargs 0 0) -Z.land_assoc.
    change (Z.land 255 ExportEntryInterruptStatusSwitcherMask)
      with ExportEntryInterruptStatusSwitcherMask.
    apply encode_entry_point_eq_posture.
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
    rewrite /encode_entry_point /entry_point_posture /ExportEntryInterruptStatusSwitcherMask.
    destruct mie; bitblast.
  Qed.

  (** The decoders of the fields of an export entry word invert
      [encode_entry_point], within the bounds of each field. *)
  Lemma export_entry_offset_encode mie nargs minstk off_entry :
    export_entry_offset (encode_entry_point mie nargs minstk off_entry) = off_entry.
  Proof. apply encode_entry_point_eq_off. Qed.

  Lemma export_entry_min_stack_encode mie nargs minstk off_entry :
    (0 ≤ minstk ≤ 255)%Z ->
    export_entry_min_stack (encode_entry_point mie nargs minstk off_entry) = minstk.
  Proof. apply encode_entry_point_eq_minstk. Qed.

  Lemma export_entry_nargs_encode mie nargs minstk off_entry :
    (0 ≤ nargs ≤ 7)%Z ->
    export_entry_nargs (encode_entry_point mie nargs minstk off_entry) = nargs.
  Proof. apply encode_entry_point_eq_nargs. Qed.

  Lemma export_entry_flags_encode mie nargs minstk off_entry :
    export_entry_flags (encode_entry_point mie nargs minstk off_entry) =
    entry_point_flags mie nargs.
  Proof. apply encode_entry_point_eq_flags. Qed.

  Lemma export_entry_posture_encode mie nargs minstk off_entry :
    export_entry_posture (encode_entry_point mie nargs minstk off_entry) = mie.
  Proof.
    rewrite /export_entry_posture encode_entry_point_eq_posture.
    by destruct mie.
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
    apply (f_equal export_entry_nargs) in Heq.
    rewrite !export_entry_nargs_encode in Heq; [|lia|lia].
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
    apply (f_equal export_entry_min_stack) in Heq.
    rewrite !export_entry_min_stack_encode in Heq; [|lia|lia].
    iPureIntro; lia.
  Qed.

  Lemma entry_irq_agree a ie ie' :
    entry_irq a ie -∗ entry_irq a ie' -∗ ⌜ie = ie'⌝.
  Proof.
    iIntros "(%n & %m & %off & Ha) (%n' & %m' & %off' & Ha')".
    iDestruct (pointsto_agree with "Ha Ha'") as %Heq.
    simplify_eq.
    apply (f_equal export_entry_posture) in Heq.
    rewrite !export_entry_posture_encode in Heq.
    by iPureIntro.
  Qed.

End Entry_projections.

Notation "a ↦ₑ□{stack} m" := (entry_min_stack a m)
  (at level 20, format "a  ↦ₑ□{stack}  m") : bi_scope.
Notation "a ↦ₑ□{irq} ie" := (entry_irq a ie)
  (at level 20, format "a  ↦ₑ□{irq}  ie") : bi_scope.

Section Switcher_preamble.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The export table cell of a pushed frame holding the unsealed entry,
      a capability to the export table. *)
  Lemma tf_export_tbl_cell_entry (tf : trusted_frame) g b e a :
    tf.(tf_export_tbl) = lword_of_word (Cap RO g b e a) →
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
      once, by the loader: it holds the capability for good. A pushed
      frame whose word is [WInt 0] (pending, or unwound because its entry
      does not unseal) leaves its cell's content free; otherwise the cell
      holds the frame's word, the unsealed entry.
   *)
  Definition trusted_frame_interp (entry : bool) (tf : trusted_frame) (a_tstk : Addr) : iProp Σ :=
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp) in
    let a_export_table := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_error_count := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount) in
    ("Htf_csp" ∷ a_csp ↦ₐ tf.(tf_csp) ∗
     "Htf_tbl" ∷ (if entry
                  then a_export_table ↦ₐ□ tf.(tf_export_tbl) ∗ ⌜tf_export_tbl_ok tf⌝
                  else ∃ w, a_export_table ↦ₐ w ∗
                         ⌜tf.(tf_export_tbl) = lword_of_word (WInt 0) ∨
                          (w = tf.(tf_export_tbl) ∧ tf_export_tbl_ok tf)⌝) ∗
     "Htf_cnt" ∷ a_error_count ↦ₐ WInt tf.(tf_error_count))%I.

  (** The four cells of the spill area from [a], in address order: the
      slots [SpillSlot_cs0], [SpillSlot_cs1], [SpillSlot_cgp] and
      [SpillSlot_pcc]. *)
  Definition switcher_stk_cells (a : Addr) (w0 w1 w2 w3 : LWord) : iProp Σ :=
    a ↦ₐ w0 ∗
    (a ^+ SpillSlot_cs1) ↦ₐ w1 ∗
    (a ^+ SpillSlot_cgp) ↦ₐ w2 ∗
    (a ^+ SpillSlot_pcc) ↦ₐ w3.

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
    (stk_spill_a a ^+ (SpillSlot_size - 1)) ∈ₐ [b, e) ∧
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
      ⌜ frm.(cf_tframe).(tf_csp) = Cap RWL Local b_stk e_stk (stk_saved_a a_stk) ∧
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
        let a_prev := (a_tstk ^+ - TrustedStackFrame_size) in
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

  (** The store-only capability to the two hazard slots of the thread, in
      the word [hazardPointers] of the register save area. *)
  Definition hazard_slots_cap : Word :=
    Cap WO Global b_hazard_slots e_hazard_slots b_hazard_slots.

  (** The word [hazardPointers] of the register save area. *)
  Definition tstack_hazard_cell : Addr :=
    (b_trusted_stack ^+ TrustedStack_offset_hazardPointers).

  (** What the switcher uses to clear the hazard slots: the word
      [hazardPointers] of the register save area, and the two slots. *)
  Definition switcher_hazard : iProp Σ :=
    tstack_hazard_cell ↦ₐ hazard_slots_cap ∗
    (∃ ws, [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ [[ ws ]]).

  (** [trusted_stack_inv] is the part of the switcher's invariant for the
      thread [th]: the private state of the switcher for that thread.

      [mtdc] is the a privileged register, than only the switcher can access.
      It contains a capability to the base of the _trusted stack_
      (also called _physical call stack_ or _switcher's private state_),
      which never changes. The trusted stack starts with the register save
      area, followed by [frameoffset] (the offset of the next free frame) and
      the frames. Each frame stores the stack pointer of a caller, the
      export table of the callee and the number of error handlers invoked.

      The _trusted stack_ must be in sync with the logical call stack [cstk],
      for which [trusted_stack_inv] holds the authoritative view [cstack_full].
      As a reminder, the fragmental view [cstack_frag] is given by the expression relation
      (or any of its variants).

      The code of the switcher and the unsealing capability of the switcher's
      otype are read-only: they are not in the invariant, but in the persistent
      resource [switcher_static], with the global part [switcher_sealing_inv].
      [trusted_stack_inv] is the part of the section's thread.

      Finally, the invariant holds the points-to predicates of the trusted stack.
      The topmost frame is at [a_tstk]; the unused part, from the next frame
      to [e_trusted_stack], and the save area contain some unknown values,
      but for the word [hazardPointers] of the save area, which holds the
      capability to the hazard slots of the thread. The invariant owns the
      two hazard slots, which hold unknown values: no compartment reaches
      them. The used part is contained in the definition of [cstack_interp].
   *)
  Definition trusted_stack_inv : iProp Σ :=
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ) in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID) in
    ∃ (a_tstk : Addr) (cstk' : CSTK) (save_area tstk_next : list LWord),
      let a_next := (a_tstk ^+ TrustedStackFrame_size) in
      "Hmtdc" ∷ mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
      "Hsave_area" ∷ [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
      "%Hsave_hazard" ∷
        ⌜save_area !! Z.to_nat TrustedStack_offset_hazardPointers
         = Some (lword_of_word hazard_slots_cap)⌝ ∗
      "Hhazard_slots" ∷ (∃ ws, [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ [[ ws ]]) ∗
      "Hframeoffset" ∷ a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      "HthreadID" ∷ (∃ w, a_threadID ↦ₐ w) ∗
      "Htstk" ∷ [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
      "Hcstk_full" ∷ ●(CSTK)[th] cstk' ∗
      "%Hlen_cstk" ∷
        ⌜(b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk
         ∧ (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z⌝ ∗
      (* link the topmost frame of cstk' to the state *)
      "Hstk_interp" ∷ cstack_interp cstk' a_tstk.

  (** Opens [trusted_stack_inv] under the later of [na_inv_acc]: the timeless
      conjuncts lose their later, so that [iNamed] can name them. *)
  Lemma trusted_stack_inv_open :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ) in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID) in
    ▷ trusted_stack_inv -∗
    ◇ ∃ (a_tstk : Addr) (cstk' : CSTK) (save_area tstk_next : list LWord),
      let a_next := (a_tstk ^+ TrustedStackFrame_size) in
      "Hmtdc" ∷ mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
      "Hsave_area" ∷ [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
      "%Hsave_hazard" ∷
        ⌜save_area !! Z.to_nat TrustedStack_offset_hazardPointers
         = Some (lword_of_word hazard_slots_cap)⌝ ∗
      "Hhazard_slots" ∷ (∃ ws, [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ [[ ws ]]) ∗
      "Hframeoffset" ∷ a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      "HthreadID" ∷ (∃ w, a_threadID ↦ₐ w) ∗
      "Htstk" ∷ [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
      "Hcstk_full" ∷ ●(CSTK)[th] cstk' ∗
      "%Hlen_cstk" ∷
        ⌜(b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk
         ∧ (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z⌝ ∗
      "Hstk_interp" ∷ ▷ cstack_interp cstk' a_tstk.
  Proof.
    intros a_frameoffset a_save_end a_threadID; subst a_frameoffset a_save_end a_threadID.
    iIntros "Hinv". rewrite /trusted_stack_inv /=.
    iDestruct "Hinv" as (a_tstk cstk' save_area tstk_next)
      "(>Hmtdc & >Hsave_area & >% & >Hhazard_slots & >Hframeoffset & >HthreadID & >Htstk
       & >Hcstk_full & >% & Hstk_interp)".
    iModIntro. iExists a_tstk, cstk', save_area, tstk_next. by iFrame "∗ %".
  Qed.

  (** Close [trusted_stack_inv] after popping the topmost frame, at [a_tstk],
      of the trusted stack: its cells go back to the unused part. *)
  Lemma trusted_stack_inv_pop_frame
    (a_tstk : Addr) (cstk : CSTK) (save_area tstk_next : list LWord) (w0 w1 w2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ) in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    let a_prev := (a_tstk ^+ - TrustedStackFrame_size) in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp) in
    let a_export_table := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_error_count := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount) in
    (b_trusted_stack + tstack_frame_offset (S (length cstk.(cstk_frames))))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    save_area !! Z.to_nat TrustedStack_offset_hazardPointers = Some (lword_of_word hazard_slots_cap) ->

    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack -∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] -∗
    (∃ ws, [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ [[ ws ]]) -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk.(cstk_frames))) -∗
    (∃ w, a_threadID ↦ₐ w) -∗
    a_csp ↦ₐ w0 -∗
    a_export_table ↦ₐ w1 -∗
    a_error_count ↦ₐ w2 -∗
    [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    ●(CSTK)[th] cstk -∗
    cstack_interp cstk a_prev -∗
    trusted_stack_inv.
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next a_prev a_csp a_export_table a_error_count.
    subst a_frameoffset a_save_end a_threadID a_next a_prev a_csp a_export_table a_error_count.
    iIntros (Hlen_cstk Ha_tstk_e Hsave_hazard)
      "Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Hw0 Hw1 Hw2 Htstk Hcstk_full
       Hstk_interp".
    iExists (a_tstk ^+ - TrustedStackFrame_size), cstk, save_area, (w0 :: w1 :: w2 :: tstk_next).
    iFrame "Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Hcstk_full Hstk_interp".
    replace ((a_tstk ^+ - TrustedStackFrame_size) ^+ TrustedStackFrame_size) with a_tstk
      by (tstack_unfold; solve_addr).
    iSplit; first done.
    iSplitL "Hw0 Hw1 Hw2 Htstk".
    { iDestruct (region_pointsto_cons _ (a_tstk ^+ TrustedStackFrame_size)
                   with "[$Hw2 $Htstk]") as "Htstk"; [tstack_unfold; solve_addr..|].
      iDestruct (region_pointsto_cons _ (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)
                   with "[$Hw1 $Htstk]") as "Htstk"; [tstack_unfold; solve_addr..|].
      iEval (rewrite /TrustedStackFrame_offset_csp finz_add_0_default) in "Hw0".
      iDestruct (region_pointsto_cons _ (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)
                   with "[$Hw0 $Htstk]") as "Htstk"; [tstack_unfold; solve_addr..|].
      iFrame "Htstk". }
    iPureIntro; tstack_unfold; split; solve_addr.
  Qed.

  (** The part of the switcher's invariant shared by the threads: the bounds
      of the switcher's otype, and the predicate of the sealed export
      entries, at the section's thread. *)
  Definition switcher_sealing_inv : iProp Σ :=
    "%Hot_bounds" ∷ ⌜(ot_switcher < (ot_switcher ^+1))%ot⌝ ∗
    "#Hp_ot_switcher" ∷ seal_pred ot_switcher ot_switcher_propC.

  #[global] Instance switcher_sealing_inv_persistent : Persistent switcher_sealing_inv.
  Proof. apply _. Qed.

  (** [switcher_static] holds the read-only memory of the switcher: its code,
      and the unsealing capability of the switcher's otype; the fact that
      the trap vector is the exception entry of the switcher; and the global
      part of the switcher's invariant. *)
  Definition switcher_static : iProp Σ :=
    codefrag_pers a_switcher_call switcher_instrs ∗
    (b_switcher ^+ 1) ↦ₐ□ SealRange (true,true) Global ot_switcher (ot_switcher^+1) ot_switcher ∗
    ⌜mtcc_vec =
       Cap XSRW_ Local b_switcher e_switcher
         (a_switcher_call ^+
            asm_label_offset switcher_asm ".Lswitch_csp_check" "exception_entry_asm")%a⌝ ∗
    switcher_sealing_inv.

  #[global] Instance switcher_static_persistent : Persistent switcher_static.
  Proof. apply _. Qed.

  (** The predicate of the sealed export entries, from [switcher_static]. *)
  Lemma switcher_static_seal_pred :
    switcher_static ⊢ seal_pred ot_switcher ot_switcher_propC.
  Proof. iIntros "(_ & _ & _ & Hsealing)". iNamed "Hsealing". iExact "Hp_ot_switcher". Qed.

End Switcher_preamble.

(** A trusted-stack address is not a shadow-table address, when [H] states
    that the trusted stack is disjoint from the shadow table. *)
Ltac tstk_not_shadow H :=
  eapply disjoint_from_shadow_not_in; [exact H | rewrite /withinBounds; tstack_unfold; solve_addr].

Section Switcher_Hazard.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Take the word [hazardPointers] out of the register save area
      [save_area], with the hazard slots. *)
  Lemma switcher_hazard_open (save_area : list LWord) :
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ) in
    save_area !! Z.to_nat TrustedStack_offset_hazardPointers = Some (lword_of_word hazard_slots_cap) ->
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] -∗
    (∃ ws, [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ [[ ws ]]) -∗
    switcher_hazard ∗
    (tstack_hazard_cell ↦ₐ hazard_slots_cap -∗
     [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]]).
  Proof.
    intros a_save_end; subst a_save_end.
    iIntros (Hk) "Hsave Hslots".
    pose proof trusted_stack_frames_fit as [n Hfit].
    rewrite /region_pointsto.
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    iDestruct (big_sepL2_lookup_acc _ _ _ (Z.to_nat TrustedStack_offset_hazardPointers)
                 with "Hsave") as "[Hw Hcont]"; [|exact Hk|].
    { eapply finz_seq_between_lookup with (n := 21%nat);
        rewrite /TrustedStack_offset_hazardPointers; tstack_unfold; [lia | solve_addr]. }
    iFrame "Hslots".
    iSplitL "Hw"; [iExact "Hw" | iExact "Hcont"].
  Qed.

End Switcher_Hazard.

Section Switcher_Stack_Traps.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_stk_cells_region_4 a w0 w1 w2 w3 :
    (a + SpillSlot_size)%a = Some (a ^+ SpillSlot_size) ->
    switcher_stk_cells a w0 w1 w2 w3 ⊣⊢
    [[ a , a ^+ SpillSlot_size ]] ↦ₐ [[ [w0; w1; w2; w3] ]].
  Proof.
    rewrite /SpillSlot_size.
    iIntros (Ha4); iSplit; iIntros "H".
    - iRegionMerge; iFrame.
    - iRegionSplit "H" as "H"; iFrame.
  Qed.

  (** The spill area ends at the cursor. *)
  Lemma stk_spill_a_end a : stk_spill_ok a → (stk_spill_a a ^+ SpillSlot_size) = a.
  Proof. stk_unfold; solve_addr. Qed.

  (** The free part of a caller's stack splits into its spill area and the
      callee's stack. *)
  Lemma stk_free_split_addrs b e a :
    switcher_stk_bounds b e a →
    stk_free b e a =
      stk_mem_join (finz.seq_between (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size))
        (callee_stk_region b e a).
  Proof.
    rewrite /switcher_stk_bounds; intros (Hb & Hb3 & Ha4).
    rewrite stk_spill_a_end //. stk_unfold.
    apply finz_seq_between_split; solve_addr.
  Qed.

  Lemma stk_free_split_zeroes b e a :
    switcher_stk_bounds b e a →
    region_addrs_zeroes (stk_free_b b a) (stk_free_e e a) =
      stk_mem_join (region_addrs_zeroes (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size))
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
    [[ stk_spill_a a , stk_spill_a a ^+ SpillSlot_size ]] ↦ₐ [[ ls ]] ∗
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
    [[ stk_spill_a a , stk_spill_a a ^+ SpillSlot_size ]] ↦ₐ [[ stk_mem_spill l ]] ∗
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
    x ∈ₐ [b, e).
  Proof.
    stk_unfold; intros (Hb & He & Hbe & Ha) Hx.
    apply elem_of_finz_seq_between in Hx. solve_addr.
  Qed.

  (** A fresh stack: its free part is the whole stack. *)
  Lemma stk_start_free_b (b e : Addr) : stk_free_b b (stk_start_a b e) = b.
  Proof. done. Qed.
  Lemma stk_start_free_e (b e : Addr) : stk_free_e e (stk_start_a b e) = stk_start_a b e.
  Proof. done. Qed.
  Lemma stk_start_cursor_ok (b e : Addr) :
    (b + StackEntry_reserved_space <= e)%Z → stk_cursor_ok b e (stk_start_a b e).
  Proof. stk_unfold; solve_addr. Qed.
  Lemma stk_start_callee_fits (b e : Addr) n :
    (b + SpillSlot_size + n + 2 * StackEntry_reserved_space <= e)%Z →
    stk_callee_fits b e (stk_start_a b e) n.
  Proof. stk_unfold; solve_addr. Qed.
  Lemma stk_start_spill_fits (b e : Addr) :
    (b + SpillSlot_size + StackEntry_reserved_space <= e)%Z →
    stk_spill_fits b e (stk_start_a b e).
  Proof. stk_unfold; solve_addr. Qed.

  (** A callee that fits leaves room for the spill. *)
  Lemma stk_callee_fits_spill_fits (b e a : Addr) n :
    (0 <= n)%Z → stk_callee_fits b e a n → stk_spill_fits b e a.
  Proof. stk_unfold; lia. Qed.

  (** The spill of a caller whose callee fits does not wrap around. *)
  Lemma stk_callee_fits_spill_ok (b e a : Addr) n :
    (0 <= n)%Z → stk_callee_fits b e a n → stk_spill_ok a.
  Proof. stk_unfold; intros Hn Hfits. solve_addr. Qed.

  (** A callee that fits has its [n] words, plus the reserved space, in its
      stack. *)
  Lemma stk_callee_fits_callee (b e a : Addr) n :
    stk_spill_ok a →
    stk_callee_fits b e a n →
    (n + StackEntry_reserved_space <= stk_callee_e e a - stk_callee_b b a)%Z.
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
    assert (switcher_label_offset ".Lswitch_entry_first_spill" = 6%Z) as Hfirst
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

End Switcher_Stack_Traps.
