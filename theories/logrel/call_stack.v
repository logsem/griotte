From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl_auth.
From iris.base_logic Require Import own.
From griotte Require Import griotte_lang.
From griotte Require Export cerise_instance machine_parameters machine_word machine_base addresses.


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

Lemma is_untrusted_caller_is_not_known_to_known (r : caller_callee_relation) :
  is_untrusted_caller r = true -> is_known_to_known r = false.
Proof. intros Huntrusted; destruct r; cbn in *; auto. Qed.

(** A calls stack [cstack] is a list of call-frames [cframe],
    and they contain the content of the callee-saved registers,
    kept track by the switcher.

    - [wret] records the value of [cra], the return pointer of the caller
    - [wcgp] records the value of [cgp], the global data (compartment's memory) of the caller
    - [wcs0] records the value of [cs0], general purpose register
    - [wcs1] records the value of [cs1], general purpose register
    - [b_stk], [a_stk] and  [e_stk] records the bounds of the stack capability [csp],
    the (compartment) stack frame of the caller

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

(** The saved words of a frame, in the order used by the switcher's
    specifications: [cgp], [cra], [cs0], and [cs1].
    These are the original values; restoring a heap capability may clear
    its tag if its allocation has since been quarantined.
 **)
Definition frame_saved_words (frm : cframe) : list Word :=
  [frm.(wcgp); frm.(wret); frm.(wcs0); frm.(wcs1)].

(** [heap_cap_base w] identifies the shadow entry needed when restoring [w].
    An ordinary capability whose base lies in the heap uses that base to
    identify its shadow entry. Other words do not require a shadow entry.

    This follows the classification [is_heap_cap] used by [Load], which
    includes untagged heap capabilities. In particular, being safe to share
    does not by itself imply that a word has no heap base.
 **)
Definition heap_cap_base `{HeapRegion} (w : Word) : option Addr :=
  match w with
  | WCap _ _ _ b _ _ => if is_heap_address b then Some b else None
  | _ => None
  end.

(** The set of heap bases mentioned by the saved words. Several registers
    may contain capabilities with the same base; they share one shadow entry,
    so the set records that base only once.
 **)
Definition saved_heap_bases `{HeapRegion} (ws : list Word) : gset Addr :=
  list_to_set (omap heap_cap_base ws).

(** The word obtained when restoring [w] using the recorded shadow bits.
    A [true] bit means QUARANTINED: the capability's tag is cleared, while
    its other fields are preserved. Otherwise the word is unchanged.

    A missing entry also leaves the word unchanged, making this function
    total. When used with [saved_shadow], every heap base in the saved words
    has an entry, so restoration does not rely on this default.
 **)
Definition restore_word `{HeapRegion} (shadow : gmap Addr bool) (w : Word) : Word :=
  match heap_cap_base w with
  | Some b => if default false (shadow !! b) then clear_tag w else w
  | None => w
  end.

Lemma restore_word_nonheap `{HeapRegion} shadow w :
  is_heap_cap w = false -> restore_word shadow w = w.
Proof.
  destruct w as [|[t p g b e a|]| |]; simpl; auto.
  rewrite /is_heap_cap /restore_word /heap_cap_base.
  by intros ->.
Qed.

Lemma restore_word_empty `{HeapRegion} w : restore_word ∅ w = w.
Proof. unfold restore_word. destruct (heap_cap_base w); done. Qed.

Section Saved_Shadow.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  (** [saved_shadow ws shadow] owns the shadow entries needed to restore [ws].

      - The domain is exactly [saved_heap_bases ws]: every saved heap
        capability has an entry, and no unrelated entries are transferred.
      - Each entry carries full points-to ownership. Aliases among saved
        registers share a single entry, rather than splitting its ownership.

      The map records the bits at the point where the words are restored.
      In a known-to-known call, the call and return specifications may use
      different maps, allowing the callee to change the shadow bits.
   **)
  Definition saved_shadow (ws : list Word)
    (shadow : gmap Addr bool) : iProp Σ :=
    ⌜dom shadow = saved_heap_bases ws⌝ ∗
    ([∗ map] b ↦ bit ∈ shadow, b ↦ₛ bit).

  (** Saved words without heap capabilities require no shadow ownership. *)
  Lemma saved_shadow_empty ws :
    Forall (fun w => is_heap_cap w = false) ws ->
    ⊢ saved_shadow ws ∅.
  Proof.
    intros Hws. rewrite /saved_shadow big_sepM_empty dom_empty_L.
    iSplit; last done. iPureIntro.
    induction Hws as [|w ws Hw Hws IH]; first done.
    rewrite /saved_heap_bases /= in IH |- *.
    assert (heap_cap_base w = None) as ->.
    { destruct w as [|[t p g b e a|]| |]; try done.
      by rewrite /heap_cap_base /is_heap_cap in Hw |- *; rewrite Hw. }
    done.
  Qed.

  (** Temporarily extract the shadow entry for one saved heap capability.
      Returning the same points-to restores the whole [saved_shadow]
      assertion, so the entry can also be used to restore aliased registers.
   **)
  Lemma saved_shadow_lookup ws shadow w b :
    w ∈ ws -> heap_cap_base w = Some b ->
    saved_shadow ws shadow -∗
    ∃ bit, ⌜shadow !! b = Some bit⌝ ∗ b ↦ₛ bit ∗
      (b ↦ₛ bit -∗ saved_shadow ws shadow).
  Proof.
    iIntros (Hw Hb) "[%Hdom Hshadow]".
    assert (is_Some (shadow !! b)) as [bit Hbit].
    { apply elem_of_dom. rewrite Hdom /saved_heap_bases elem_of_list_to_set.
      apply list_elem_of_omap. eauto. }
    iDestruct (big_sepM_lookup_acc with "Hshadow") as "[Hb Hclose]"; first exact Hbit.
    iExists bit. iFrame. iSplit; first done.
    iIntros "Hb". iSplit; first done. by iApply "Hclose".
  Qed.
End Saved_Shadow.

Definition is_untrusted_caller_frm (frm : cframe) :=
  is_untrusted_caller frm.(ccrel).
Definition is_known_to_known_frm (frm : cframe) :=
  is_known_to_known frm.(ccrel).

Lemma is_untrusted_caller_is_not_known_to_known_frm (frm : cframe) :
  is_untrusted_caller_frm frm = true -> is_known_to_known_frm frm = false.
Proof.
  rewrite /is_untrusted_caller_frm /is_known_to_known_frm.
  apply is_untrusted_caller_is_not_known_to_known.
Qed.

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
