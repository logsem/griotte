From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From iris.base_logic Require Import own.
From griotte Require Import griotte_lang.
From griotte Require Export cerise_instance machine_parameters machine_word machine_base addresses.
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
    [tf_stk_b] and [tf_stk_e], and the base [tf_spill_a] of the area where the
    switcher spilled the callee-saved registers, the four words below the
    cursor of [tf_csp]. *)
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
Definition tf_spill_a (tf : trusted_frame) : Addr :=
  match tf.(tf_csp).(lw) with
  | WCap _ _ _ _ _ a => (a ^+ -4)%a
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
Arguments tf_spill_a !tf /.

Lemma spill_cursor (a : Addr) : is_Some (a + 4)%a → ((a ^+ 4) ^+ -4)%a = a.
Proof. intros [a4 Ha4]. solve_addr. Qed.

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

(** The stack of the caller of a frame, and the base of its spill area. *)
Notation cf_stk_b frm := (tf_stk_b (cf_tframe frm)).
Notation cf_stk_e frm := (tf_stk_e (cf_tframe frm)).
Notation cf_spill_a frm := (tf_spill_a (cf_tframe frm)).

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
