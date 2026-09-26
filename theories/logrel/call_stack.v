From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From iris.base_logic Require Import own.
From griotte Require Import griotte_lang.
From griotte Require Export cerise_instance machine_parameters machine_word machine_base addresses.
From griotte.program_logic Require Import allocator_resources.


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

    The frame records the saved words, not their mutable shadow bits.
    Each restored word satisfies [load_heap]: a heap capability may lose its
    tag when loaded. The allocator owns the shadow entries, and their state
    is not recorded on the call stack.

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
      wret : Word;
      wcgp : Word;
      wcs0 : Word;
      wcs1 : Word;
      b_stk : Addr;
      a_stk : Addr;
      e_stk : Addr;
      ccrel : caller_callee_relation;
  }.

(** [load_heap saved actual] describes a saved register after its load.
    A heap capability may retain its tag or have it cleared, depending on
    the shadow entry at that instruction. No allocation state is retained
    by this relation: later instructions may change that state again.
    All other words, including untagged capabilities, are unchanged.
 **)
Definition load_heap `{HeapRegion} (saved actual : Word) : Prop :=
  actual = saved ∨ (is_heap_cap saved = true ∧ actual = clear_tag saved).

Lemma load_heap_nonheap `{HeapRegion} saved actual :
  is_heap_cap saved = false -> load_heap saved actual -> actual = saved.
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

Class CSTACKG Σ :=
  { cstack_inG :: inG Σ cstackUR;
    γcstack : gname;
  }.

Definition CSTACK_preΣ :=
  #[ GFunctor cstackUR ].

Instance subG_CSTACK_preΣ {Σ} :
  subG CSTACK_preΣ Σ → CSTACK_preG Σ.
Proof. solve_inG. Qed.

Section CStack.
  Context {Σ : gFunctors} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} .

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
