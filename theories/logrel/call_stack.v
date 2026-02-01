From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From iris.base_logic Require Import own.
From cap_machine Require Import cap_lang.

(** A calls stack [cstack] is a list of call-frames [cframe],
    and they contain the content of the callee-saved registers,
    kept track by the switcher.

    - [wret] records the value of [cra], the return pointer of the caller
    - [wcgp] records the value of [cgp], the global data (compartment's memory) of the caller
    - [wcs0] records the value of [cs0], general purpose register
    - [wcs1] records the value of [cs1], general purpose register
    - [b_stk], [a_stk] and  [e_stk] records the bounds of the stack capability [csp],
    the (compartment) stack frame of the caller

    TODO: reformulate the following.
    In addition, it records whether the caller of the topmost frame
    is trusted or not.
    It is necessary, because the callee-saved registers values are stored
    in the compartment's stack, and the way to handle the points-to predicates
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
      is_untrusted_caller : bool;
  }.

Notation cstack := (list cframe).
Notation CSTK := (leibnizO cstack).

Definition cstackR := excl_authR CSTK.
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
  Context {Σ : gFunctors} {cstackg : CSTACKG Σ} .

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
