From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From iris.base_logic Require Import own.
From griotte Require Import griotte_lang.
From griotte Require Export resources machine_parameters machine_word machine_base addresses.
From griotte Require Export logical_words export_table_layout.


(** The relationship between the caller and the callee determines
    the guarantees that the continuation K provides when popping a frame;
    and conversely, the obligations that we need to prove when pushing a frame.
 *)

Inductive caller_callee_relation : Type :=
| Unknown_to_Unknown
| Unknown_to_Known
| Known_to_Unknown
| Known_to_Known.

Definition is_untrusted_caller (r : caller_callee_relation) :=
  match r with
  | Unknown_to_Unknown | Unknown_to_Known => true
  | Known_to_Unknown | Known_to_Known => false
  end.

Definition is_known_to_known (r : caller_callee_relation) :=
  match r with
  | Known_to_Known => true
  | Unknown_to_Unknown | Unknown_to_Known | Known_to_Unknown => false
  end.


(** The callee-saved registers of a caller, spilled by the switcher on the
    caller's own stack at the call, and restored at the return.

    - [cs_cra] records the value of [cra], the return pointer of the caller
    - [cs_cgp] records the value of [cgp], the global data (compartment's memory) of the caller
    - [cs_cs0] records the value of [cs0], general purpose register
    - [cs_cs1] records the value of [cs1], general purpose register

    They are logical words, with their identifiers, not their mutable shadow
    bits. Each restored word satisfies [load_heap]: a heap capability may lose
    its tag when loaded, and keeps its identifier. The shadow state is not
    recorded on the call stack.
 **)
Record callee_saved_registers := MkCalleeSaved {
      cs_cra : LWord;
      cs_cgp : LWord;
      cs_cs0 : LWord;
      cs_cs1 : LWord;
  }.

(** A frame of the trusted stack ([TrustedStackFrame] in CHERIoT):

    - [tf_csp] is the word of its [csp] cell: the stack pointer of the
      caller, after the spill of the callee-saved registers; for the entry
      frame of the thread, the initial stack pointer of the thread
    - [tf_export_tbl] is the word of its [calleeExportTable] cell, stored
      when the frame is pushed: the unsealed export entry of the callee, a
      capability to its export table (its base is [tf_export_tbl_b]); for the
      entry frame, the capability to the export table of the compartment the
      thread starts in. When the unseal of the entry fails, the frame is
      unwound with the cell still 0: the field may then be any word, and it
      is never read
    - [tf_error_count] is the number of error handlers invoked
      ([errorHandlerCount])
 **)
Record trusted_frame := MkTFrame {
      tf_csp : LWord;
      tf_export_tbl : LWord;
      tf_error_count : Z;
  }.

(** The stack of the caller of a frame, read from [tf_csp]: its bounds
    [tf_stk_b] and [tf_stk_e], and the cursor [tf_caller_a] of the caller at
    the call (see [stk_saved_a]). *)
Definition tf_stk_b (tf : trusted_frame) : Addr :=
  match tf.(tf_csp).(lw) with
  | WCap _ _ _ b _ _ => b
  | _ => 0%a
  end.
Definition tf_stk_e (tf : trusted_frame) : Addr :=
  match tf.(tf_csp).(lw) with
  | WCap _ _ _ _ e _ => e
  | _ => 0%a
  end.

(** The base of the export table of the callee of a frame. *)
Definition tf_export_tbl_b (tf : trusted_frame) : Addr :=
  match tf.(tf_export_tbl).(lw) with
  | WCap _ _ _ b _ _ => b
  | _ => 0%a
  end.

Arguments tf_export_tbl_b !tf /.
Arguments tf_stk_b !tf /.
Arguments tf_stk_e !tf /.

(** * The layout of a compartment stack

    The switcher's call path takes the caller's stack [[b, e)] with its
    cursor at [a]. It spills the callee-saved registers of the caller in the
    [SpillSlot_size] words of the spill area, at [stk_spill_a a], moves the
    cursor to [stk_saved_a a], saved in the frame, and gives the callee the
    stack [[stk_callee_b b a, stk_callee_e e a)]. The part of the caller's
    stack that the call hands to the switcher, the spill area and the
    callee's stack, is [[stk_free_b b a, stk_free_e e a)]. Stacks grow
    down, as in CHERIoT: the free part is below the cursor, the spill area
    is its top [SpillSlot_size] words, and the callee's stack the rest. *)

(** The base of the spill area. *)
Definition stk_spill_a (a : Addr) : Addr := (a ^+ (- SpillSlot_size))%a.
(** The cursor after the spill, which the frame saves. *)
Definition stk_saved_a (a : Addr) : Addr := (a ^+ (- SpillSlot_size))%a.
(** The bounds of the callee's stack. *)
Definition stk_callee_b (b a : Addr) : Addr := b.
Definition stk_callee_e (e a : Addr) : Addr := (a ^+ (- SpillSlot_size))%a.
(** The bounds of the free part of the caller's stack. *)
Definition stk_free_b (b a : Addr) : Addr := b.
Definition stk_free_e (e a : Addr) : Addr := a.
(** Where the cursor of a fresh stack [[b, e)] starts: below the
    [StackEntry_reserved_space] words reserved at its top. *)
Definition stk_start_a (b e : Addr) : Addr := (e ^+ (- StackEntry_reserved_space))%a.
(** The spill area does not wrap around the address space. *)
Definition stk_spill_ok (a : Addr) : Prop :=
  (a + (- SpillSlot_size))%a = Some (a ^+ (- SpillSlot_size))%a.
(** The cursor is not outside the stack on the side of its used part (the
    caller's frames): a trusted caller's spill can only fault at its first
    store. *)
Definition stk_cursor_ok (b e a : Addr) : Prop := (a <= e)%a.
(** The spill fits in the stack: its first store does not fault. *)
Definition stk_spill_fits (b e a : Addr) : Prop := (b + SpillSlot_size <= a)%Z.
(** A callee that needs [n] words, plus the space reserved at the top of
    its stack, fits in the stack, once the spill is done. *)
Definition stk_callee_fits (b e a : Addr) (n : Z) : Prop :=
  (b + n + StackEntry_reserved_space + SpillSlot_size <= a)%Z.

(** The cursor of the caller at the call, read from the stack pointer that
    a frame saves. *)
Definition tf_caller_a (tf : trusted_frame) : Addr :=
  match tf.(tf_csp).(lw) with
  | WCap _ _ _ _ _ c => (c ^+ SpillSlot_size)%a
  | _ => 0%a
  end.

(* Kept folded by [simpl] and [cbn] on a concrete frame, so that
   [tf_caller_a_saved] can rewrite it. *)
Arguments tf_caller_a : simpl never.

Lemma tf_caller_a_saved (tf : trusted_frame) t p g b e (a : Addr) :
  stk_spill_ok a →
  tf.(tf_csp).(lw) = WCap t p g b e (stk_saved_a a) →
  tf_caller_a tf = a.
Proof.
  rewrite /stk_spill_ok /stk_saved_a /tf_caller_a /SpillSlot_size.
  intros Ha ->. solve_addr.
Qed.

(** The stack pointer of the call path once the stack is restricted to the
    callee's, with its cursor at the top, before the switcher reserves the
    space at the top of the callee's stack. *)
Definition chopped_csp (b e a : Addr) : Word :=
  WCap true RWL Local (stk_callee_b b a) (stk_callee_e e a) (stk_callee_e e a).
(** The stack pointer that the switcher gives to the callee. *)
Definition callee_csp (b e a : Addr) : Word :=
  WCap true RWL Local (stk_callee_b b a) (stk_callee_e e a)
    (stk_start_a (stk_callee_b b a) (stk_callee_e e a)).
(** The callee's stack pointer is that of a fresh stack on the callee's
    bounds. *)
Lemma callee_csp_start b e a :
  callee_csp b e a =
  WCap true RWL Local (stk_callee_b b a) (stk_callee_e e a)
    (stk_start_a (stk_callee_b b a) (stk_callee_e e a)).
Proof. done. Qed.
(** The addresses of the callee's stack. *)
Definition callee_stk_region (b e a : Addr) : list Addr :=
  finz.seq_between (stk_callee_b b a) (stk_callee_e e a).
(** The addresses of the free part of the caller's stack. *)
Definition stk_free (b e a : Addr) : list Addr :=
  finz.seq_between (stk_free_b b a) (stk_free_e e a).
(** The words of the free part, in address order: those of the spill area,
    those of the callee's stack, and the free part from both. *)
Definition stk_mem_spill {A} (l : list A) : list A :=
  drop (length l - Z.to_nat SpillSlot_size) l.
Definition stk_mem_callee {A} (l : list A) : list A :=
  take (length l - Z.to_nat SpillSlot_size) l.
Definition stk_mem_join {A} (ls lc : list A) : list A := lc ++ ls.
(** The bounds of the callee's stack are within the caller's, and the spill
    area does not wrap around. *)
Definition callee_stk_bounds (b e a : Addr) : Prop :=
  (b <= stk_callee_b b a)%a ∧ (stk_callee_e e a <= e)%a ∧
  (stk_callee_b b a <= stk_callee_e e a)%a ∧ stk_spill_ok a.

(** Unfold the stack layout and the spill slots, for [solve_addr]. *)
Ltac stk_unfold :=
  unfold chopped_csp, callee_csp, callee_stk_region, stk_free, stk_mem_spill, stk_mem_callee,
    stk_mem_join, callee_stk_bounds, stk_spill_a, stk_saved_a, stk_callee_b,
    stk_callee_e, stk_free_b, stk_free_e, stk_start_a, stk_spill_ok, stk_cursor_ok,
    stk_spill_fits, stk_callee_fits,
    SpillSlot_size, SpillSlot_cs0, SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc,
    StackEntry_reserved_space in *;
  try change (Z.to_nat 4) with 4%nat in *.

(** A call-frame [cframe]: the frame [cf_tframe] of the trusted stack, the
    callee-saved registers [cf_saved] of the caller, and the caller-callee
    relationship [ccrel].
    In case of know-to-known, we trust the caller and the callee to properly
    keep track of the continuation themselves, and therefore the continuation is trivial.

    In addition, if the caller topmost frame is unknown,
    the callee-saved registers values are stored in the compartment's stack,
    and the way to handle the points-to predicates
    depend on whether the region is shared.
    More explanation in the switcher's invariant.
 **)
Record cframe := MkCFrame {
      cf_tframe : trusted_frame;
      cf_saved : callee_saved_registers;
      ccrel : caller_callee_relation;
  }.

(** The stack of the caller of a frame, and its cursor at the call. *)
Notation cf_stk_b frm := (tf_stk_b (cf_tframe frm)).
Notation cf_stk_e frm := (tf_stk_e (cf_tframe frm)).
Notation cf_caller_a frm := (tf_caller_a (cf_tframe frm)).

(** [load_heap saved actual] describes a saved register after its load.
    A heap capability may retain its tag or have it cleared, depending on
    the shadow entry at that instruction. No allocation state is retained
    by this relation: later instructions may change that state again.
    All other words, including untagged capabilities, are unchanged.
 **)
Notation load_heap := lload_heap (only parsing).

Lemma load_heap_nonheap `{HeapRegion} (saved actual : LWord) :
  is_heap_cap saved.(lw) = false -> load_heap saved actual -> actual = saved.
Proof. intros Hheap [-> | [Hheap' ->]]; congruence. Qed.


Definition is_untrusted_caller_frm (frm : cframe) :=
  is_untrusted_caller frm.(ccrel).
Definition is_known_to_known_frm (frm : cframe) :=
  is_known_to_known frm.(ccrel).


(** A call stack [cstack]: the entry frame of the thread [cstk_entry]
    ([frames[0]] of the trusted stack), and the frames [cstk_frames] pushed
    above it by the calls, the topmost first. *)
Record cstack := MkCStack {
      cstk_entry : trusted_frame;
      cstk_frames : list cframe;
  }.
Notation CSTK := (leibnizO cstack).

#[global] Instance trusted_frame_inhabited : Inhabited trusted_frame :=
  populate (MkTFrame (lword_of_word (WInt 0)) (lword_of_word (WInt 0)) 0).
#[global] Instance cstack_inhabited : Inhabited cstack :=
  populate (MkCStack inhabitant []).

(** The call stack of a thread with no call: its entry frame only. *)
Notation entry_cstack ef := {| cstk_entry := ef; cstk_frames := [] |}.

(** The call stack [cstk] with the frame [frm] pushed on top. *)
Notation cstack_push frm cstk :=
  {| cstk_entry := cstk.(cstk_entry); cstk_frames := frm :: cstk.(cstk_frames) |}.

Lemma cstack_eta (cstk : cstack) :
  {| cstk_entry := cstk.(cstk_entry); cstk_frames := cstk.(cstk_frames) |} = cstk.
Proof. by destruct cstk. Qed.

(** The topmost frame of the trusted stack: the topmost pushed frame, or the
    entry frame. *)
Definition top_tframe (cstk : cstack) : trusted_frame :=
  match cstk.(cstk_frames) with
  | frm :: _ => frm.(cf_tframe)
  | [] => cstk.(cstk_entry)
  end.

(** The base of the export table of the callee of the topmost frame. *)
Definition top_export_tbl (cstk : cstack) : Addr := tf_export_tbl_b (top_tframe cstk).

(** The error handler count of the topmost frame. *)
Definition top_error_count (cstk : cstack) : Z := (top_tframe cstk).(tf_error_count).

Lemma top_tframe_push (frm : cframe) (cstk : cstack) :
  top_tframe (cstack_push frm cstk) = frm.(cf_tframe).
Proof. done. Qed.
Lemma top_tframe_entry (ef : trusted_frame) :
  top_tframe (entry_cstack ef) = ef.
Proof. done. Qed.

(** The frame [tf] with its error handler count set to [n]. *)
Definition tf_set_count (tf : trusted_frame) (n : Z) : trusted_frame :=
  {| tf_csp := tf.(tf_csp); tf_export_tbl := tf.(tf_export_tbl); tf_error_count := n |}.

(** The call stack [cstk] with the error handler count of its topmost frame
    set to [n]; the rest is unchanged. *)
Definition cstack_set_top_count (cstk : cstack) (n : Z) : cstack :=
  match cstk.(cstk_frames) with
  | frm :: frms =>
      {| cstk_entry := cstk.(cstk_entry);
         cstk_frames :=
           {| cf_tframe := tf_set_count frm.(cf_tframe) n;
              cf_saved := frm.(cf_saved);
              ccrel := frm.(ccrel) |} :: frms |}
  | [] => {| cstk_entry := tf_set_count cstk.(cstk_entry) n; cstk_frames := [] |}
  end.

(** Whether the topmost frame is the entry frame. *)
Definition top_is_entry (cstk : cstack) : bool :=
  match cstk.(cstk_frames) with [] => true | _ :: _ => false end.

Lemma top_tframe_set_count cstk n :
  top_tframe (cstack_set_top_count cstk n) = tf_set_count (top_tframe cstk) n.
Proof. by destruct cstk as [ef [|frm frms] ]. Qed.
Lemma top_error_count_set_count cstk n :
  top_error_count (cstack_set_top_count cstk n) = n.
Proof. by destruct cstk as [ef [|frm frms] ]. Qed.
Lemma top_export_tbl_set_count cstk n :
  top_export_tbl (cstack_set_top_count cstk n) = top_export_tbl cstk.
Proof. by destruct cstk as [ef [|frm frms] ]. Qed.
Lemma top_is_entry_set_count cstk n :
  top_is_entry (cstack_set_top_count cstk n) = top_is_entry cstk.
Proof. by destruct cstk as [ef [|frm frms] ]. Qed.
Lemma cstack_set_top_count_frames_length cstk n :
  length (cstack_set_top_count cstk n).(cstk_frames) = length cstk.(cstk_frames).
Proof. by destruct cstk as [ef [|frm frms] ]. Qed.
Lemma cstack_set_top_count_id cstk :
  cstack_set_top_count cstk (top_error_count cstk) = cstk.
Proof. by destruct cstk as [ [csp tbl n] [|[ [csp' tbl' n'] saved rel] frms] ]. Qed.
Lemma cstack_set_top_count_twice cstk n m :
  cstack_set_top_count (cstack_set_top_count cstk n) m = cstack_set_top_count cstk m.
Proof. by destruct cstk as [ef [|frm frms] ]. Qed.

(** The two kinds of error handler an export table may declare. *)
Inductive handler_kind := Stackful | Stackless.

Definition cstackUR := excl_authUR CSTK.

Class CSTACK_preG Σ :=
  { cstack_preG :: inG Σ cstackUR; }.
#[export] Hint Mode CSTACK_preG - : typeclass_instances.

Class CSTACKG Σ :=
  { cstack_inG :: inG Σ cstackUR;
    γcstack : gname;
  }.
#[export] Hint Mode CSTACKG - : typeclass_instances.

Definition CSTACK_preΣ :=
  #[ GFunctor cstackUR ].

#[export] Instance subG_CSTACK_preΣ {Σ} :
  subG CSTACK_preΣ Σ → CSTACK_preG Σ.
Proof. solve_inG. Qed.

Section CStack.
  Context {Σ : gFunctors} {cstackg : CSTACKG Σ}.

  Definition cstack_full (cstk : cstack) : iProp Σ
    := own γcstack (●E (cstk : leibnizO cstack) : cstackUR).

  Definition cstack_frag (cstk : cstack) : iProp Σ
    := own γcstack (◯E (cstk : leibnizO cstack) : cstackUR).

  Lemma cstack_agree (cstk cstk' : cstack) :
   cstack_full cstk -∗
   cstack_frag cstk' -∗
   ⌜ cstk = cstk' ⌝.
  Proof.
    iIntros "Hfull Hfrag".
    rewrite /cstack_full /cstack_frag.
    iCombine "Hfull Hfrag" as "H".
    iDestruct (own_valid with "H") as "%H".
    by apply excl_auth_agree_L in H.
  Qed.

  Lemma cstack_update (cstk cstk' cstk'' : cstack) :
   cstack_full cstk -∗
   cstack_frag cstk' ==∗
   cstack_full cstk'' ∗ cstack_frag cstk''.
  Proof.
    iIntros "Hfull Hfrag".
    rewrite /cstack_full /cstack_frag.
    iCombine "Hfull Hfrag" as "H".
    iMod ( own_update _ _ _  with "H" ) as "H".
    { apply excl_auth_update. }
    iDestruct "H" as "[? ?]".
    by iFrame.
  Qed.

End CStack.

Section pre_CSTACK.
  Context {Σ : gFunctors} {cstackg : CSTACK_preG Σ}.

  Lemma gen_cstack_init (cstk : cstack) :
    ⊢ |==> (∃ (cstackg : CSTACKG Σ), cstack_full cstk ∗ cstack_frag cstk).
  Proof.
    iMod (own_alloc (A:=cstackUR) (●E (cstk : leibnizO _) ⋅ ◯E (cstk : leibnizO _) )) as (γcstack) "Hcstack"
    ; first by apply excl_auth_valid.
    iModIntro. iExists (Build_CSTACKG _ _ γcstack).
    by rewrite own_op.
  Qed.

End pre_CSTACK.

Section Handler_projections.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  (** Projections of the header of the export table at [b]: the offset [z]
      of its stackful error handler ([handler_stackful]) and of its
      stackless one ([handler_stackless]), [ExportTable_no_handler] for none. Each is
      persistent. *)
  Definition handler_stackful_def (b : Addr) (z : Z) : iProp Σ :=
    let a_eh := (b ^+ ExportTable_offset_errorHandler)%a in
    a_eh ↦ₐ□ WInt z.
  #[local] Definition handler_stackful_aux : seal (@handler_stackful_def). Proof. by eexists. Qed.
  Definition handler_stackful := handler_stackful_aux.(unseal).
  #[local] Definition handler_stackful_unseal :
    @handler_stackful = @handler_stackful_def := handler_stackful_aux.(seal_eq).

  Definition handler_stackless_def (b : Addr) (z : Z) : iProp Σ :=
    let a_ehs := (b ^+ ExportTable_offset_errorHandlerStackless)%a in
    a_ehs ↦ₐ□ WInt z.
  #[local] Definition handler_stackless_aux : seal (@handler_stackless_def). Proof. by eexists. Qed.
  Definition handler_stackless := handler_stackless_aux.(unseal).
  #[local] Definition handler_stackless_unseal :
    @handler_stackless = @handler_stackless_def := handler_stackless_aux.(seal_eq).

  #[global] Instance handler_stackful_persistent b z : Persistent (handler_stackful b z).
  Proof. rewrite handler_stackful_unseal. apply _. Qed.
  #[global] Instance handler_stackless_persistent b z : Persistent (handler_stackless b z).
  Proof. rewrite handler_stackless_unseal. apply _. Qed.

  Lemma handler_stackful_intro b z :
    let a_eh := (b ^+ ExportTable_offset_errorHandler)%a in
    a_eh ↦ₐ□ WInt z ⊢ handler_stackful b z.
  Proof. by rewrite handler_stackful_unseal. Qed.
  Lemma handler_stackless_intro b z :
    let a_ehs := (b ^+ ExportTable_offset_errorHandlerStackless)%a in
    a_ehs ↦ₐ□ WInt z ⊢ handler_stackless b z.
  Proof. by rewrite handler_stackless_unseal. Qed.

  Lemma handler_stackful_elim b z :
    let a_eh := (b ^+ ExportTable_offset_errorHandler)%a in
    handler_stackful b z ⊢ a_eh ↦ₐ□ WInt z.
  Proof. by rewrite handler_stackful_unseal. Qed.
  Lemma handler_stackless_elim b z :
    let a_ehs := (b ^+ ExportTable_offset_errorHandlerStackless)%a in
    handler_stackless b z ⊢ a_ehs ↦ₐ□ WInt z.
  Proof. by rewrite handler_stackless_unseal. Qed.

  Lemma handler_stackful_agree b z z' :
    handler_stackful b z -∗ handler_stackful b z' -∗ ⌜z = z'⌝.
  Proof.
    rewrite handler_stackful_unseal. iIntros "Ha Ha'".
    iDestruct (pointsto_agree with "Ha Ha'") as %Heq. by simplify_eq.
  Qed.
  Lemma handler_stackless_agree b z z' :
    handler_stackless b z -∗ handler_stackless b z' -∗ ⌜z = z'⌝.
  Proof.
    rewrite handler_stackless_unseal. iIntros "Ha Ha'".
    iDestruct (pointsto_agree with "Ha Ha'") as %Heq. by simplify_eq.
  Qed.

  (** The compartment of the export table at [b] declares no error
      handler. *)
  Definition no_handler (b : Addr) : iProp Σ :=
    handler_stackful b ExportTable_no_handler ∗ handler_stackless b ExportTable_no_handler.

  #[global] Instance no_handler_persistent b : Persistent (no_handler b).
  Proof. apply _. Qed.
End Handler_projections.

Notation "b ↦ₕ□{stackful} z" := (handler_stackful b z)
  (at level 20, format "b  ↦ₕ□{stackful}  z") : bi_scope.
Notation "b ↦ₕ□{stackless} z" := (handler_stackless b z)
  (at level 20, format "b  ↦ₕ□{stackless}  z") : bi_scope.
