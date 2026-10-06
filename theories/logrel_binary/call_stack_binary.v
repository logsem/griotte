From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From iris.base_logic Require Import own.
From griotte Require Import griotte_lang.
From griotte Require Export call_stack.

(** * Call stacks of the binary model

    Each run has its own logical call stack: the implementation run uses the
    [cstack] ghost of [call_stack.v] (class [CSTACKG]), the specification run
    uses a second copy of the same ghost (class [CSTACK_specG]).

    The relation-level definitions work with a stack of pairs of frames
    [list (cframe * cframe)]: the first components form the implementation
    call stack, the second components the specification call stack. Frames at
    the same position are related by [cframe_pair_cond]. *)

(** The spec ghost stack is a [CSTACKG] that is deliberately *not* an
    instance: otherwise [inG Σ cstackUR] would be found twice and the
    implementation definitions [cstack_full]/[cstack_frag] could pick up the
    wrong ghost name. *)
Class CSTACK_specG Σ :=
  { cstack_spec_G : CSTACKG Σ; }.

Notation cstack_pair := (list (cframe * cframe)).
Notation CSTKP := (leibnizO cstack_pair).

Section CStack_spec.
  Context {Σ : gFunctors} {cstackg_spec : CSTACK_specG Σ}.

  Definition cstack_full_spec (cstk : cstack) : iProp Σ :=
    @cstack_full Σ cstack_spec_G cstk.

  Definition cstack_frag_spec (cstk : cstack) : iProp Σ :=
    @cstack_frag Σ cstack_spec_G cstk.

  Lemma cstack_agree_spec (cstk cstk' : cstack) :
    cstack_full_spec cstk -∗
    cstack_frag_spec cstk' -∗
    ⌜ cstk = cstk' ⌝.
  Proof. apply (@cstack_agree Σ cstack_spec_G). Qed.

  Lemma cstack_update_spec (cstk cstk' cstk'' : cstack) :
    cstack_full_spec cstk -∗
    cstack_frag_spec cstk' ==∗
    cstack_full_spec cstk'' ∗ cstack_frag_spec cstk''.
  Proof. apply (@cstack_update Σ cstack_spec_G). Qed.

End CStack_spec.

Section pre_CSTACK_spec.
  Context {Σ : gFunctors} {cstackg : CSTACK_preG Σ}.

  Lemma gen_cstack_spec_init (cstk : cstack) :
    ⊢ |==> (∃ (cstackg_spec : CSTACK_specG Σ),
               cstack_full_spec cstk ∗ cstack_frag_spec cstk).
  Proof.
    iMod (gen_cstack_init cstk) as (cstackg') "[Hfull Hfrag]".
    iModIntro. iExists {| cstack_spec_G := cstackg' |}.
    iFrame.
  Qed.

End pre_CSTACK_spec.

(** ** Pairs of frames *)

(** Two frames at the same position of the two call stacks are related when
    an untrusted compartment is involved (as caller or as callee) on either
    side: then both frames have the same caller-callee relationship and the
    same stack bounds. Frames between two trusted compartments are
    unconstrained: the trusted code may use its stack differently in the two
    runs. The saved registers are not constrained here: for a trusted caller
    they may hold different (secret) values, and for an untrusted caller the
    switcher reloads them from the shared stack frame on return. *)
Definition cframe_pair_cond (frm : cframe * cframe) : Prop :=
  (is_known_to_known_frm frm.1 = false ∨ is_known_to_known_frm frm.2 = false) →
  frm.1.(ccrel) = frm.2.(ccrel)
  ∧ frm.1.(b_stk) = frm.2.(b_stk)
  ∧ frm.1.(a_stk) = frm.2.(a_stk)
  ∧ frm.1.(e_stk) = frm.2.(e_stk).

Lemma cframe_pair_cond_known_to_known (frm : cframe * cframe) :
  cframe_pair_cond frm →
  is_known_to_known_frm frm.1 = is_known_to_known_frm frm.2.
Proof.
  rewrite /cframe_pair_cond /is_known_to_known_frm.
  destruct frm as [frm1 frm2]; cbn.
  destruct (is_known_to_known (ccrel frm1)) eqn:H1,
    (is_known_to_known (ccrel frm2)) eqn:H2; auto
  ; intros Hcond.
  - destruct Hcond as (Heq & _); auto; rewrite Heq in H1; congruence.
  - destruct Hcond as (Heq & _); auto; rewrite Heq in H1; congruence.
Qed.

Lemma cframe_pair_cond_untrusted_caller (frm : cframe * cframe) :
  cframe_pair_cond frm →
  is_known_to_known_frm frm.1 = false →
  is_untrusted_caller_frm frm.1 = is_untrusted_caller_frm frm.2.
Proof.
  intros Hcond Hk.
  destruct Hcond as (Heq & _); auto.
  by rewrite /is_untrusted_caller_frm Heq.
Qed.

Lemma cframe_pair_cond_diag (frm : cframe) :
  cframe_pair_cond (frm, frm).
Proof. done. Qed.
