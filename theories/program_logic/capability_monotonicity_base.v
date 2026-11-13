From griotte Require Import erasure.

(** * Capability monotonicity: the physical part

    The words that an instruction may write are below a word of the
    pre-state: [word_le], no more authority than a given word, and what
    the erasure needs from it ([word_shrinks]): a word below a
    well-formed logical word is well-formed with its provenance, given
    the heap-root clause ([lift_root_ok]). The logical counterparts and
    the lifting are in [capability_monotonicity.v]. *)

Declare Scope capability_scope.
Delimit Scope capability_scope with cap.

(** ** The relation *)

Section capability_monotonicity_base.
  Context `{MP : MachineParameters}.

  (** A capability whose bounds [b, e] became [b', e'] keeps them, or has
      its new base within its new bounds: the base is not above the end. An
      executable capability needs it, as its base must avoid the heap like
      its bounds ([lword_exec]). Only [Subseg] changes the bounds of a
      capability; its result is tagged only if [a1 <=? a2], which gives
      this. Kept bounds, rather than a kept base only, make [word_le]
      transitive. *)
  Definition rebased_bounds_ok (b e b' e' : Addr) : Prop :=
    (b' = b ∧ e' = e) ∨ (b' <= e')%a.

  (** [w'] carries no more authority than [w]: capability monotonicity, the
      preorder of capabilities in the spirit of T-CHERI's [≤]
      ([word_le_preorder]). A tagged result needs a tagged source;
      permission and locality only decrease (Restrict); bounds only shrink
      (Subseg), with the Griotte-specific [rebased_bounds_ok]; the address
      is free (Lea, SetA). Any untagged word is below any word (ClearTag,
      Get, the integer results). *)
  Inductive word_le : Word → Word → Prop :=
  | wle_untagged w' w : get_tag w' = false → word_le w' w
  | wle_refl w : word_le w w
  | wle_cap t t' p p' g g' b b' e e' a a' :
      (t' = true → t = true) →
      PermFlowsTo p' p → LocalityFlowsTo g' g → (b <= b')%a → (e' <= e)%a →
      rebased_bounds_ok b e b' e' →
      word_le (WCap t' p' g' b' e' a') (WCap t p g b e a)
  | wle_sr t t' p p' g g' b b' e e' a a' :
      (t' = true → t = true) →
      SealPermFlowsTo p' p → LocalityFlowsTo g' g → (b <= b')%ot → (e' <= e)%ot →
      word_le (WSealRange t' p' g' b' e' a') (WSealRange t p g b e a).

  #[global] Instance word_le_preorder : PreOrder word_le.
  Proof.
    split; first (intros w; apply wle_refl).
    intros w1 w2 w3 H12 H23.
    destruct H12 as [w1 w2 Ht| w2 | t2 t1 p2 p1 g2 g1 b2 b1 e2 e1 a2 a1 Ht12 Hp12 Hg12 ? ? Hr12
                    | t2 t1 p2 p1 g2 g1 b2 b1 e2 e1 a2 a1 Ht12 Hp12 Hg12 ? ?]; [by apply wle_untagged | done | |].
    - inversion H23 as [? ? Ht| | t3 ? p3 ? g3 ? b3 ? e3 ? a3 ? Ht23 Hp23 Hg23 ? ? Hr23 |]; subst.
      + destruct t1; last by apply wle_untagged.
        cbn in Ht. by rewrite (Ht12 eq_refl) in Ht.
      + by apply wle_cap.
      + apply wle_cap; [auto | by etrans | by etrans | solve_addr | solve_addr |].
        rewrite /rebased_bounds_ok in Hr12 Hr23 |- *.
        destruct Hr12 as [ [-> ->] | ?]; [done | right; solve_addr].
    - inversion H23 as [? ? Ht| | | t3 ? p3 ? g3 ? b3 ? e3 ? a3 ? Ht23 Hp23 Hg23 ? ?]; subst.
      + destruct t1; last by apply wle_untagged.
        cbn in Ht. by rewrite (Ht12 eq_refl) in Ht.
      + by apply wle_sr.
      + apply wle_sr; [auto | by etrans | by etrans | solve_addr | solve_addr].
  Qed.

End capability_monotonicity_base.

(** [w' ⊑ w]: [w'] carries no more authority than [w]. *)
Notation "w' ⊑ w" := (word_le w' w) (at level 70) : capability_scope.
#[local] Open Scope capability_scope.

(** ** What the erasure needs from [⊑] *)

Section capability_shrink.
  Context `{MP : MachineParameters}.
  Implicit Types (R : RegState) (C : gmap Addr AddrClaim) (vs : LWord) (w : Word).

  (** What the erasure needs from [w ≤ ws], for a tagged [w]. *)
  Definition word_shrinks w ws : Prop :=
    get_tag w = true →
    get_tag ws = true ∧
    (executable_word w = true → executable_word ws = true) ∧
    match memory_cap_bounds w with
    | None => True
    | Some (b', e') => ∃ b e, memory_cap_bounds ws = Some (b, e) ∧
        (b <= b')%a ∧ (e' <= e)%a ∧ rebased_bounds_ok b e b' e'
    end.

  (** The heap-root clause, for an identifier-less result. *)
  Definition lift_root_ok C (π : option AId) w : Prop :=
    π = None → get_tag w = true →
    ∀ b', heap_authority_base w = Some b' → C !! b' = Some HeapRoot.

  (** Below a tagged word is only a tagged source. *)
  Lemma word_le_tagged w w' : w' ⊑ w → get_tag w' = true → get_tag w = true.
  Proof. destruct 1 as [? ? Ht| | ? ? * Ht | ? ? * Ht]; cbn; auto; congruence. Qed.

  (** A word below [w] keeps what the erasure needs from it. *)
  Lemma word_le_shrinks w w' : w' ⊑ w → word_shrinks w' w.
  Proof.
    intros Hle Ht. destruct Hle as [w' w Ht'| w | t t' p p' g g' b b' e e' a a' Htt Hp
                                   | t t' p p' g g' b b' e e' a a' Htt]; cbn in *.
    - congruence.
    - split_and!; [done | done |]. destruct (memory_cap_bounds w) as [ [b e]|]; last done.
      exists b, e. split_and!; [done | solve_addr | solve_addr | by left].
    - split_and!; [by apply Htt | by apply executeAllowed_flowsto | by exists b, e].
    - split_and!; [by apply Htt | done | done].
  Qed.

  (** A tagged word [w] that shrinks [vs], with the heap-root clause, is
      well-formed for the erasure with the provenance of [vs]. *)
  Lemma reg_word_ok_shrink R C vs w :
    reg_word_ok R C vs →
    word_shrinks w vs.(lw) → get_tag w = true →
    lift_root_ok C vs.(lprov) w →
    reg_word_ok R C (MkLWord w vs.(lprov)).
  Proof.
    intros (Hp & Hauth & Hexec) Hsh Ht Hroot. destruct (Hsh Ht) as (Hts & Hx & Hb).
    split_and!.
    - intros ι b' e' _ Hb' Hlt Hι; cbn in *. rewrite Hb' in Hb.
      destruct Hb as (b & e & Hbe & ? & ? & _).
      destruct (Hp ι b e Hts Hbe ltac:(solve_addr) Hι) as (x & Hx' & ? & ?).
      exists x. simpl in *. split_and!; [done | solve_addr | solve_addr].
    - intros b' _ Hab; cbn. destruct (lprov vs) as [ι|] eqn:Hι; last by apply Hroot.
      apply heap_authority_base_memory_cap_bounds in Hab as (e' & Hb' & Hlt & _).
      rewrite Hb' in Hb. destruct Hb as (b & e & Hbe & ? & ? & _).
      destruct (Hp ι b e Hts Hbe ltac:(solve_addr) Hι) as (x & Hx' & _). by exists x.
    - intros _ Hxw; cbn. destruct (Hexec Hts (Hx Hxw)) as [Hπ Havoid]. split; first done.
      intros b' e' Hb'. rewrite Hb' in Hb. destruct Hb as (b & e & Hbe & ? & ? & Hrebased).
      destruct (Havoid b e Hbe) as [Hbh Hy]. split.
      + destruct Hrebased as [ [-> _] | ?]; first done. apply Hy; solve_addr.
      + intros y ?. apply Hy; solve_addr.
  Qed.

  (** Such a word is its own physical copy: its heap authority, inside the
      one of [vs], is not quarantined. *)
  Lemma reg_phys_shrink R C st vs w :
    registry_ok R C st →
    reg_word_ok R C vs →
    reg_phys R vs vs.(lw) →
    word_shrinks w vs.(lw) → get_tag w = true →
    reg_phys R (MkLWord w vs.(lprov)) w.
  Proof.
    intros Hreg (Hp & _ & _) [_ Hq] Hsh Ht. split; first by left.
    intros ι x [_ [b' Hab] ] Hι Hx Hqd; cbn in *. exfalso.
    destruct (Hsh Ht) as (Hts & _ & Hb).
    apply heap_authority_base_memory_cap_bounds in Hab as (e' & Hb' & Hlt & _).
    rewrite Hb' in Hb. destruct Hb as (b & e & Hbe & ? & ? & _).
    destruct (Hp ι b e Hts Hbe ltac:(solve_addr) Hι) as (x' & Hx' & ? & ?).
    rewrite Hx in Hx'; simplify_eq.
    assert (has_authority vs.(lw)) as Has.
    { split; first done. exists b. apply heap_authority_base_memory_cap_bounds.
      exists e. split_and!; [done | solve_addr |].
      eapply reg_ok_heap; [done | done | rewrite /re_covers; solve_addr]. }
    pose proof (Hq ι x' Has Hι Hx Hqd) as Heq.
    by rewrite Heq get_tag_clear_tag in Hts.
  Qed.

End capability_shrink.
