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

    The fields [shadow_cgp], [shadow_cra], [shadow_cs0], and [shadow_cs1]
    record the call-time shadow bits of the corresponding saved words.
    For a known caller, [None] means nonheap, [Some false] means not
    quarantined, and [Some true] means quarantined. Unknown callers use
    [None] for all four fields: their actual saved words are tracked by
    the world, and these fields do not classify those words.

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
      shadow_cgp : option bool;
      shadow_cra : option bool;
      shadow_cs0 : option bool;
      shadow_cs1 : option bool;
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

(** The optional shadow bit associated with one word in an internal map.
    Maps are used only to share ownership between registers with the same
    heap base; public specifications give the four bits separately.
 **)
Definition saved_word_shadow `{HeapRegion} (shadow : gmap Addr bool) (w : Word)
  : option bool := heap_cap_base w ≫= fun b => shadow !! b.

(** Restoring a quarantined saved word clears its tag, preserving its other
    fields. [None] is used for nonheap words, or for untracked unknown frames.
 **)
Definition restore_saved_word (bit : option bool) (w : Word) : Word :=
  match bit with
  | Some true => clear_tag w
  | _ => w
  end.

Lemma restore_saved_word_map `{HeapRegion} shadow w :
  restore_saved_word (saved_word_shadow shadow w) w = restore_word shadow w.
Proof.
  unfold restore_saved_word, saved_word_shadow, restore_word.
  destruct (heap_cap_base w) as [b|]; last done.
  cbn. destruct (shadow !! b) as [[]|]; done.
Qed.

Lemma saved_word_shadow_nonheap `{HeapRegion} shadow w :
  is_heap_cap w = false -> saved_word_shadow shadow w = None.
Proof.
  destruct w as [|[t p g b e a|]| |]; simpl; auto.
  rewrite /is_heap_cap /saved_word_shadow /heap_cap_base. by intros ->.
Qed.

Lemma saved_word_shadow_empty `{HeapRegion} w :
  saved_word_shadow ∅ w = None.
Proof. unfold saved_word_shadow. destruct (heap_cap_base w); done. Qed.

Lemma restore_word_nonheap `{HeapRegion} shadow w :
  is_heap_cap w = false -> restore_word shadow w = w.
Proof.
  destruct w as [|[t p g b e a|]| |]; simpl; auto.
  rewrite /is_heap_cap /restore_word /heap_cap_base.
  by intros ->.
Qed.

Lemma restore_word_empty `{HeapRegion} w : restore_word ∅ w = w.
Proof. unfold restore_word. destruct (heap_cap_base w); done. Qed.

(** Exact domains and equal per-word bits determine the internal map.
    This lets specifications expose individual bits without losing ownership.
 **)
Lemma saved_shadow_map_unique `{HeapRegion} ws (shadow shadow' : gmap Addr bool) :
  dom shadow = saved_heap_bases ws ->
  dom shadow' = saved_heap_bases ws ->
  Forall2 (fun w bit => bit = saved_word_shadow shadow' w)
    ws (map (saved_word_shadow shadow) ws) ->
  shadow = shadow'.
Proof.
  intros Hdom Hdom' Hbits.
  assert (∀ w, w ∈ ws -> saved_word_shadow shadow w = saved_word_shadow shadow' w)
    as Hlookup.
  { clear Hdom Hdom'. revert Hbits. induction ws as [|w ws IH]; intros Hbits v Hv; first set_solver.
    inversion Hbits; subst. apply elem_of_cons in Hv as [->|Hv]; first done.
    apply IH; done. }
  apply map_eq. intros b.
  destruct (decide (b ∈ saved_heap_bases ws)) as [Hb|Hb].
  - rewrite /saved_heap_bases elem_of_list_to_set list_elem_of_omap in Hb.
    destruct Hb as (w & Hw & Hwbase).
    specialize (Hlookup w Hw).
    by rewrite /saved_word_shadow Hwbase /= in Hlookup.
  - assert (shadow !! b = None) as ->.
    { apply not_elem_of_dom. by rewrite Hdom. }
    symmetry. apply not_elem_of_dom. by rewrite Hdom'.
Qed.

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
  (** Explicit shadow metadata for a list of saved words. The internal map
      deduplicates full ownership; [Forall2] associates each word with its bit.
      Its exact domain ensures that [None] occurs precisely for nonheap words.
      Aliased heap capabilities must have the same bit, and own only one entry.
   **)
  Definition saved_words_shadow (ws : list Word) (bits : list (option bool))
    : iProp Σ :=
    ∃ shadow, saved_shadow ws shadow ∗
      ⌜Forall2 (fun w bit => bit = saved_word_shadow shadow w) ws bits⌝.

  (** The public saved-register resources, in [cgp], [cra], [cs0], [cs1]
      order. The bits are explicit, but ownership is shared between aliases.
   **)
  Definition saved_registers_shadow (wcgp wcra wcs0 wcs1 : Word)
    (scgp scra scs0 scs1 : option bool) : iProp Σ :=
    saved_words_shadow [wcgp; wcra; wcs0; wcs1] [scgp; scra; scs0; scs1].

  Definition frame_saved_shadow (frm : cframe) : iProp Σ :=
    saved_registers_shadow frm.(wcgp) frm.(wret) frm.(wcs0) frm.(wcs1)
      frm.(shadow_cgp) frm.(shadow_cra) frm.(shadow_cs0) frm.(shadow_cs1).

  (** Unknown callers carry no shadow resources. Their saved words may be
      recovered from shared memory, so [None] here means untracked, rather
      than asserting anything about those actual words.
   **)
  Definition frame_shadow_resources (frm : cframe) : iProp Σ :=
    (if is_untrusted_caller frm.(ccrel)
    then ⌜frm.(shadow_cgp) = None ∧ frm.(shadow_cra) = None ∧
           frm.(shadow_cs0) = None ∧ frm.(shadow_cs1) = None⌝
    else frame_saved_shadow frm)%I.

  Lemma saved_words_shadow_map ws shadow :
    saved_shadow ws shadow -∗
    saved_words_shadow ws (map (saved_word_shadow shadow) ws).
  Proof.
    iIntros "Hshadow". iExists shadow. iFrame. iPureIntro.
    induction ws; constructor; auto.
  Qed.

  Lemma saved_words_shadow_empty ws :
    Forall (fun w => is_heap_cap w = false) ws ->
    ⊢ saved_words_shadow ws (replicate (length ws) None).
  Proof.
    intros Hws. iExists ∅. iSplit.
    - by iApply saved_shadow_empty.
    - iPureIntro. clear Hws. induction ws; constructor; auto using saved_word_shadow_empty.
  Qed.

  Lemma saved_registers_shadow_map wcgp wcra wcs0 wcs1 shadow :
    saved_shadow [wcgp; wcra; wcs0; wcs1] shadow -∗
    saved_registers_shadow wcgp wcra wcs0 wcs1
      (saved_word_shadow shadow wcgp) (saved_word_shadow shadow wcra)
      (saved_word_shadow shadow wcs0) (saved_word_shadow shadow wcs1).
  Proof. apply saved_words_shadow_map. Qed.

  Lemma saved_words_shadow_map_equiv ws shadow :
    dom shadow = saved_heap_bases ws ->
    saved_words_shadow ws (map (saved_word_shadow shadow) ws) ⊣⊢ saved_shadow ws shadow.
  Proof.
    intros Hdom. iSplit; last iApply saved_words_shadow_map.
    iIntros "(%shadow' & [%Hdom' Hshadow] & %Hbits)".
    pose proof (saved_shadow_map_unique _ _ _ Hdom Hdom' Hbits) as ->.
    by iFrame.
  Qed.

  Lemma saved_registers_shadow_map_equiv wcgp wcra wcs0 wcs1 shadow :
    dom shadow = saved_heap_bases [wcgp; wcra; wcs0; wcs1] ->
    saved_registers_shadow wcgp wcra wcs0 wcs1
      (saved_word_shadow shadow wcgp) (saved_word_shadow shadow wcra)
      (saved_word_shadow shadow wcs0) (saved_word_shadow shadow wcs1) ⊣⊢
    saved_shadow [wcgp; wcra; wcs0; wcs1] shadow.
  Proof. apply saved_words_shadow_map_equiv. Qed.

  Lemma saved_registers_shadow_empty wcgp wcra wcs0 wcs1 :
    Forall (fun w => is_heap_cap w = false) [wcgp; wcra; wcs0; wcs1] ->
    ⊢ saved_registers_shadow wcgp wcra wcs0 wcs1 None None None None.
  Proof. apply saved_words_shadow_empty. Qed.

  (** Opening the explicit resources recovers a map and the four lookup
      equalities. They allow low-level load rules to keep using maps without
      exposing a map parameter in the caller's specification.
   **)
  Lemma saved_registers_shadow_open wcgp wcra wcs0 wcs1 scgp scra scs0 scs1 :
    saved_registers_shadow wcgp wcra wcs0 wcs1 scgp scra scs0 scs1 -∗
    ∃ shadow, saved_shadow [wcgp; wcra; wcs0; wcs1] shadow ∗
      ⌜scgp = saved_word_shadow shadow wcgp ∧
       scra = saved_word_shadow shadow wcra ∧
       scs0 = saved_word_shadow shadow wcs0 ∧
       scs1 = saved_word_shadow shadow wcs1⌝.
  Proof.
    iIntros "(%shadow & Hshadow & %Hbits)". iExists shadow. iFrame.
    iPureIntro. inversion Hbits; subst.
    repeat match goal with
    | H : Forall2 _ (_ :: _) _ |- _ => inversion H; subst; clear H
    end. auto.
  Qed.

  Lemma saved_registers_shadow_nonheap wcgp wcra wcs0 wcs1 scgp scra scs0 scs1 :
    is_heap_cap wcgp = false -> is_heap_cap wcra = false ->
    is_heap_cap wcs0 = false -> is_heap_cap wcs1 = false ->
    saved_registers_shadow wcgp wcra wcs0 wcs1 scgp scra scs0 scs1 -∗
    ⌜scgp = None ∧ scra = None ∧ scs0 = None ∧ scs1 = None⌝.
  Proof.
    iIntros (Hcgp Hcra Hcs0 Hcs1) "Hshadow".
    iDestruct (saved_registers_shadow_open with "Hshadow")
      as (shadow) "[_ %Hbits]".
    iPureIntro. by rewrite !saved_word_shadow_nonheap in Hbits.
  Qed.

  (** The unknown-caller branch needs no map entries, regardless of the
      actual words in its shared stack. Its four [None] fields agree with the
      empty map. Known callers expose precisely their saved-register map.
   **)
  Lemma saved_registers_shadow_resources_open
    wcgp wcra wcs0 wcs1 scgp scra scs0 scs1 (unknown : bool) :
    (if unknown then ⌜scgp = None ∧ scra = None ∧ scs0 = None ∧ scs1 = None⌝
     else saved_registers_shadow wcgp wcra wcs0 wcs1 scgp scra scs0 scs1) -∗
    ∃ shadow,
      (if unknown then ⌜shadow = ∅⌝
       else saved_shadow [wcgp; wcra; wcs0; wcs1] shadow) ∗
      ⌜scgp = saved_word_shadow shadow wcgp ∧
       scra = saved_word_shadow shadow wcra ∧
       scs0 = saved_word_shadow shadow wcs0 ∧
       scs1 = saved_word_shadow shadow wcs1⌝.
  Proof.
    destruct unknown.
    - iIntros "%Hbits". iExists ∅. rewrite !saved_word_shadow_empty. iSplit; done.
    - apply saved_registers_shadow_open.
  Qed.

  (** Equal heap bases must refer to the same entry, even when the words
      differ in permissions, bounds, or tags.
   **)
  Lemma saved_words_shadow_alias ws bits i j wi wj si sj b :
    ws !! i = Some wi -> ws !! j = Some wj ->
    bits !! i = Some si -> bits !! j = Some sj ->
    heap_cap_base wi = Some b -> heap_cap_base wj = Some b ->
    saved_words_shadow ws bits -∗ ⌜si = sj⌝.
  Proof.
    iIntros (Hwi Hwj Hsi Hsj Hbi Hbj) "(%shadow & _ & %Hbits)".
    iPureIntro.
    pose proof (Forall2_lookup_lr _ _ _ _ _ _ Hbits Hwi Hsi) as Hi.
    pose proof (Forall2_lookup_lr _ _ _ _ _ _ Hbits Hwj Hsj) as Hj.
    rewrite /saved_word_shadow Hbi in Hi. rewrite /saved_word_shadow Hbj in Hj.
    congruence.
  Qed.

  (** Extract one entry and return it unchanged to recover the whole bundle.
      The same entry can then be used for another register that aliases it.
   **)
  Lemma saved_words_shadow_lookup ws bits w b :
    w ∈ ws -> heap_cap_base w = Some b ->
    saved_words_shadow ws bits -∗
    ∃ bit, b ↦ₛ bit ∗ (b ↦ₛ bit -∗ saved_words_shadow ws bits).
  Proof.
    iIntros (Hw Hb) "(%shadow & Hshadow & %Hbits)".
    iDestruct (saved_shadow_lookup with "Hshadow") as (bit Hbit) "[Hb Hclose]";
      [exact Hw|exact Hb|].
    iExists bit. iFrame "Hb". iIntros "Hb".
    iExists shadow. iSplit; last done. by iApply "Hclose".
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
