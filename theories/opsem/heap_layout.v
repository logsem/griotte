From griotte Require Import machine_base.

(** The heap region, and the predicates on words and ranges that refer to
    it. *)
Class HeapRegion := {
    heap_b : Addr;
    heap_e : Addr;
    heap_valid : (heap_b < heap_e)%a;
  }.

Definition is_heap_address `{HeapRegion} (a : Addr) : bool :=
  withinBounds heap_b heap_e a.

(* Memory capabilities, including sealed ones and sentries, use their base. *)
Definition heap_cap_base `{HeapRegion} (w : Word) : option Addr :=
  match memory_cap_base w with
  | Some b => if is_heap_address b then Some b else None
  | None => None
  end.

(** Empty bounds carry no authority, even when their base is in the heap. *)
Definition heap_authority_base `{HeapRegion} (w : Word) : option Addr :=
  match w with
  | WCap _ _ _ b e _ | WSentry _ _ _ _ b e _
  | WSealed _ (SCap _ _ _ b e _) =>
      if decide (b < e)%a then heap_cap_base w else None
  | _ => None
  end.

Lemma heap_authority_base_heap_cap_base `{HeapRegion} (raw : Word) base :
  heap_authority_base raw = Some base → heap_cap_base raw = Some base.
Proof.
  destruct raw; unfold heap_authority_base; simpl; try discriminate.
  - destruct sb; simpl; try discriminate. case_decide; auto; discriminate.
  - case_decide; auto; discriminate.
  - destruct sb; simpl; try discriminate. case_decide; auto; discriminate.
Qed.

(* Bounds of memory capabilities, including sealed ones and sentries. *)
Definition memory_cap_bounds (w : Word) : option (Addr * Addr) :=
  match w with
  | WCap _ _ _ b e _ | WSentry _ _ _ _ b e _
  | WSealed _ (SCap _ _ _ b e _) => Some (b, e)
  | _ => None
  end.

Lemma heap_authority_base_memory_cap_bounds `{HeapRegion} (w : Word) base :
  heap_authority_base w = Some base <->
  ∃ e, memory_cap_bounds w = Some (base, e) ∧ (base < e)%a ∧ is_heap_address base = true.
Proof.
  rewrite /heap_authority_base /heap_cap_base /memory_cap_base.
  destruct_word w; cbn; try (split; [discriminate | intros (? & ? & _); discriminate]).
  all: try (destruct sb; cbn; try (split; [discriminate | intros (? & ? & _); discriminate])).
  all: case_decide; destruct (is_heap_address _) eqn:Hheap; split;
    try (intros; simplify_eq; eauto; fail).
  all: intros (? & ? & ? & ?); simplify_eq; solve [done | congruence].
Qed.

(* A word with authority over heap memory: tagged, non-empty, heap base. *)
Definition has_authority `{HeapRegion} (w : Word) : Prop :=
  get_tag w = true ∧ ∃ b, heap_authority_base w = Some b.

Definition is_heap_cap `{HeapRegion} (w : Word) : bool :=
  match heap_cap_base w with Some _ => true | None => false end.

Lemma sealed_cap_nonheap `{HeapRegion} o t p g b e a :
  is_heap_address b = false ->
  is_heap_cap (WSealed o (SCap t p g b e a)) = false.
Proof.
  intros Hb. rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hb /=.
  reflexivity.
Qed.

Definition disjoint_from_heap `{HeapRegion} (b e : Addr) : Prop :=
  finz.seq_between b e ## finz.seq_between heap_b heap_e.

(* An empty range is disjoint from the heap regardless of its base.  Keep the
   base check as well so that even an empty range cannot start in the heap. *)
Definition not_heap_range `{HeapRegion} (b e : Addr) : Prop :=
  is_heap_address b = false ∧ disjoint_from_heap b e.

Lemma disjoint_from_heap_not_in `{HeapRegion} (b e a : Addr) :
  disjoint_from_heap b e →
  withinBounds b e a = true →
  is_heap_address a = false.
Proof.
  intros Hdisjoint Hbounds. apply not_true_is_false. intros Hheap.
  apply withinBounds_true_iff in Hbounds, Hheap.
  rewrite /disjoint_from_heap elem_of_disjoint in Hdisjoint.
  eapply Hdisjoint; apply elem_of_finz_seq_between; eauto.
Qed.
