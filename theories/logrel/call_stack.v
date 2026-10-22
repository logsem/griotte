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


(** A calls stack [cstack] is a list of call-frames [cframe],
    and they contain the content of the callee-saved registers,
    kept track by the switcher.

    - [wret] records the value of [cra], the return pointer of the caller
    - [wcgp] records the value of [cgp], the global data (compartment's memory) of the caller
    - [wcs0] records the value of [cs0], general purpose register
    - [wcs1] records the value of [cs1], general purpose register
    - [b_stk], [a_stk] and  [e_stk] records the bounds of the stack capability [csp],
    the (compartment) stack frame of the caller
    - [b_callee_exp_tbl] records the base of the export table of the callee
      ([calleeExportTable] in CHERIoT)

    The frame records the saved logical words, with their identifiers, not
    their mutable shadow bits. Each restored word satisfies [load_heap]: a
    heap capability may lose its tag when loaded, and keeps its identifier.
    The shadow state is not recorded on the call stack.

    Finally, [ccrel] tracks the caller-callee relationship.
    In case of know-to-known, we trust the caller and the callee to properly
    keep track of the continuation themselves, and therefore the continuation is trivial.

    In addition, if the caller topmost frame is unknown,
    the callee-saved registers values are stored in the compartment's stack,
    and the way to handle the points-to predicates
    depend on whether the region is shared.
    More explanation in the switcher's invariant.
 **)
Record cframe := MkCFrame {
      wret : LWord;
      wcgp : LWord;
      wcs0 : LWord;
      wcs1 : LWord;
      b_stk : Addr;
      a_stk : Addr;
      e_stk : Addr;
      b_callee_exp_tbl : Addr;
      ccrel : caller_callee_relation;
  }.

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


Notation cstack := (list cframe).
Notation CSTK := (leibnizO cstack).

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

(** The callee of the topmost frame of [cstk], if any, has its export table
    at [b]. *)
Definition top_callee_tbl (cstk : cstack) (b : Addr) : Prop :=
  match cstk with
  | frm :: _ => frm.(b_callee_exp_tbl) = b
  | [] => True
  end.
