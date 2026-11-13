From griotte Require Import interp_weakening.

(** The projections of the erasure, and [erasure_pc_exact], take the
    erasure only. *)
#[local] Arguments er_registry {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments er_regs {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments er_pc {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments er_pc_word {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments er_pc_ok {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments erasure_pc_exact {MP R C σ lpc lreg lsreg lmem}.

(** * Capability monotonicity

    The words that an instruction may write: [word_le], no more authority
    than a given word, and [derivable], no more authority than a register
    or the PC of the pre-state, or a sealing by a register's authority.
    Their counterparts on logical words, [lword_le] and [lderivable], and
    the lifting: a derivable physical word has a derivable logical word,
    well-formed for the erasure. *)

Declare Scope capability_scope.
Delimit Scope capability_scope with cap.

(** ** The relations *)

Section capability_monotonicity.
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

  (** A word that an instruction may write: no more authority than a
      register or the PC of the pre-state, or a sealing by the authority of
      a register. *)
  Inductive derivable (φ : ExecConf) : Word → Prop :=
  | derivable_reg r w w' : reg φ !!ᵣ r = Some w → word_le w' w → derivable φ w'
  (* The PC as a source: Auipcc. *)
  | derivable_pc w' : word_le w' (pcc φ) → derivable φ w'
  (* A sealable sealed by a tagged range that permits sealing at [a]: Seal. *)
  | derivable_seal r1 r2 t p g b e a sb :
      reg φ !!ᵣ r1 = Some (WSealRange t p g b e a) → reg φ !!ᵣ r2 = Some (WSealable sb) →
      t = true → permit_seal p = true → withinBounds b e a = true →
      derivable φ (WSealed a sb)
  (* A sealed word unsealed by a tagged range that permits unsealing at
     [o]: UnSeal. *)
  | derivable_unseal r1 r2 t p g b e a o sb :
      reg φ !!ᵣ r1 = Some (WSealRange t p g b e a) → reg φ !!ᵣ r2 = Some (WSealed o sb) →
      t = true → permit_unseal p = true → withinBounds b e o = true →
      derivable φ (WSealable (unseal_sb g sb)).

  Lemma derivable_untagged φ w : get_tag w = false → derivable φ w.
  Proof. intros Ht. eapply (derivable_reg _ cnull (WInt 0)); [done | by apply wle_untagged]. Qed.

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

  (** *** The logical counterpart of [derivable]

      The same relations on logical words: [lword_le] keeps the provenance,
      and the erasure needs one more premise, [subseg_heap_base]: a moved
      base of an identified capability stays in the heap. *)

  Inductive lword_le : LWord → LWord → Prop :=
  | lwle_untagged v' v : get_tag v'.(lw) = false → lword_le v' v
  | lwle_refl v : lword_le v v
  | lwle_cap t t' p p' g g' b b' e e' a a' π :
      (t' = true → t = true) →
      PermFlowsTo p' p → LocalityFlowsTo g' g → (b <= b')%a → (e' <= e)%a →
      subseg_heap_base π b b' e' →
      lword_le (WCap t' p' g' b' e' a' @@? π) (WCap t p g b e a @@? π)
  | lwle_sr t t' p p' g g' b b' e e' a a' π :
      (t' = true → t = true) →
      SealPermFlowsTo p' p → LocalityFlowsTo g' g → (b <= b')%ot → (e' <= e)%ot →
      lword_le (WSealRange t' p' g' b' e' a' @@? π) (WSealRange t p g b e a @@? π).

  (** A logical word derivable from the logical registers [lregs] and PC
      [lpc]: [derivable] on logical words, the provenance kept by
      [lword_le], and a sealing or unsealing keeping the sealee's. *)
  Inductive lderivable (lregs : LReg) (lpc : LWord) : LWord → Prop :=
  | lderivable_reg r v v' : lregs !! r = Some v → lword_le v' v → lderivable lregs lpc v'
  | lderivable_pc v' : lword_le v' lpc → lderivable lregs lpc v'
  | lderivable_seal r1 r2 p g b e a πr sb π :
      lregs !! r1 = Some (SealRange p g b e a @@? πr) → lregs !! r2 = Some (WSealable sb @@? π) →
      permit_seal p = true → withinBounds b e a = true →
      lderivable lregs lpc (WSealed a sb @@? π)
  | lderivable_unseal r1 r2 p g b e a πr o sb π :
      lregs !! r1 = Some (SealRange p g b e a @@? πr) → lregs !! r2 = Some (WSealed o sb @@? π) →
      permit_unseal p = true → withinBounds b e o = true →
      lderivable lregs lpc (WSealable (unseal_sb g sb) @@? π).

  (** An identifier-less capability is off the heap: what [interp] gives
      ([heap_cap_ok p b e None]). *)
  Definition no_prov_disjoint_from_heap (v : LWord) : Prop :=
    ∀ p g b e a x, v = Cap p g b e a @@? None → (b <= x)%a → (x < e)%a →
      is_heap_address x = false.

End capability_monotonicity.

(** [w' ⊑ w]: [w'] carries no more authority than [w]; [v' ⊑ₗ v], the same
    on logical words. *)
Notation "w' ⊑ w" := (word_le w' w) (at level 70) : capability_scope.
Notation "v' ⊑ₗ v" := (lword_le v' v) (at level 70) : capability_scope.
#[local] Open Scope capability_scope.


(** ** Lifting: a derivable physical word has a derivable logical word *)

Section capability_lift.
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

  (** The lift of the physical word [w'] that a step writes: a logical word,
      well-formed for the erasure, whose physical copy is [w'], and
      derivable from the logical registers or PC. *)
  Definition has_lift R C (lreg : LReg) (lpc : LWord) w' : Prop :=
    ∃ v, reg_word_ok R C v ∧ reg_phys R v w' ∧ lderivable lreg lpc v.

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

  (** The heap-base premise of [lwle_cap], from the provenance. *)
  Lemma subseg_heap_base_reg R C st vs b e b' e' :
    registry_ok R C st → lword_prov R vs →
    get_tag vs.(lw) = true → memory_cap_bounds vs.(lw) = Some (b, e) →
    (b <= b')%a → (e' <= e)%a →
    subseg_heap_base vs.(lprov) b b' e'.
  Proof.
    intros Hreg Hp Ht Hbe ? ? ι Hι _ Hlt.
    destruct (Hp ι b e Ht Hbe ltac:(solve_addr) Hι) as (x & Hx & ? & ?).
    eapply reg_ok_heap; [done | done | rewrite /re_covers; solve_addr].
  Qed.

  (** An identifier-less source off the heap gives the heap-root clause:
      only the source itself can have a heap authority base. *)
  Lemma lift_root_ok_word_le R C vs w :
    reg_word_ok R C vs → no_prov_disjoint_from_heap vs →
    w ⊑ vs.(lw) →
    lift_root_ok C vs.(lprov) w.
  Proof.
    destruct vs as [ws π]; cbn.
    intros (_ & Hauth & _) Hnoid Hle Hπ Ht base Hab.
    destruct Hle as [w ws Ht'| ws | t t' p p' g g' b b' e e' a a' Htt _ _ ? ? _
                    | t t' p p' g g' b b' e e' a a'].
    - congruence.
    - by pose proof (Hauth base Ht Hab) as Hb; rewrite Hπ in Hb.
    - apply heap_authority_base_memory_cap_bounds in Hab as (? & Hbe & Hlt & Hh).
      cbn in Ht, Hbe; simplify_eq. rewrite (Htt eq_refl) in Hnoid.
      by rewrite (Hnoid p g b e a base eq_refl ltac:(solve_addr) ltac:(solve_addr)) in Hh.
    - done.
  Qed.

  (** [word_le] on the physical words is [lword_le] with the provenance of
      the source. *)
  Lemma lword_le_of_word_le R C st vs w :
    registry_ok R C st → reg_word_ok R C vs →
    w ⊑ vs.(lw) →
    MkLWord w vs.(lprov) ⊑ₗ vs.
  Proof.
    destruct vs as [ws π]; cbn. intros Hreg (Hp & _ & _) Hle.
    destruct Hle as [w ws Ht'| ws | t t' p p' g g' b b' e e' a a' Htt ? ? Hb He _
                    | t t' p p' g g' b b' e e' a a' Htt ? ? ? ?].
    - by apply lwle_untagged.
    - apply lwle_refl.
    - destruct t'; last by apply lwle_untagged.
      apply lwle_cap; try done.
      apply (subseg_heap_base_reg R C st (WCap t p g b e a @@? π) b e);
        [done | done | by apply Htt | done | done | done].
    - by apply lwle_sr.
  Qed.

  (** A tagged [word_le] of a well-formed logical word lifts with the same
      provenance. *)
  Lemma word_le_lift R C st vs w' :
    registry_ok R C st → reg_word_ok R C vs → reg_phys R vs vs.(lw) → no_prov_disjoint_from_heap vs →
    w' ⊑ vs.(lw) → get_tag w' = true →
    reg_word_ok R C (MkLWord w' vs.(lprov)) ∧ reg_phys R (MkLWord w' vs.(lprov)) w' ∧
    MkLWord w' vs.(lprov) ⊑ₗ vs.
  Proof.
    intros Hreg Hok Hphys Hnoid Hle Ht. split_and!.
    - apply reg_word_ok_shrink; [done | by apply word_le_shrinks | done |].
      by eapply lift_root_ok_word_le.
    - by eapply reg_phys_shrink; [| | | apply word_le_shrinks |].
    - by eapply lword_le_of_word_le.
  Qed.

  (** The PC is off the heap when it has no identifier: the erasure makes
      an executable word avoid the heap. *)
  Lemma erasure_pc_no_prov_disjoint_from_heap {R C σ lpc lreg lsreg lmem} :
    erasure R C σ lpc lreg lsreg lmem → no_prov_disjoint_from_heap lpc.
  Proof.
    intros Her p g b e a x -> ? ?.
    destruct (er_pc_word Her) as (_ & _ & Hexec).
    destruct ((er_pc_ok Her) eq_refl) as [_ Hx].
    destruct (Hexec eq_refl Hx) as [_ Havoid].
    apply (Havoid b e eq_refl). solve_addr.
  Qed.

  (** A tagged physical register is the copy of its logical register. *)
  Lemma erasure_reg_tagged {R C φ lpc lreg lsreg lmem r w} :
    erasure R C φ lpc lreg lsreg lmem →
    reg φ !!ᵣ r = Some w → get_tag w = true →
    ∃ vs, lreg !! r = Some vs ∧ vs.(lw) = w ∧ reg_word_ok R C vs ∧ reg_phys R vs w.
  Proof.
    intros Her Hr Ht.
    rewrite /lookup_reg in Hr. case_decide; first by simplify_eq.
    destruct (er_regs Her) as [Hdom Hphys].
    assert (is_Some (lreg !! r)) as [vs Hvs].
    { apply elem_of_dom. rewrite -Hdom. by apply elem_of_dom. }
    destruct (Hphys r vs Hvs) as (ws & Hws & Hp). rewrite Hr in Hws; simplify_eq.
    exists vs. split_and!; [done | | by eapply er_reg_words | done].
    symmetry. by eapply reg_phys_tagged.
  Qed.

  Section lifts.
    Context {R C φ lpc lreg lsreg lmem}
      (Her : erasure R C φ lpc lreg lsreg lmem)
      (Hnoid : ∀ r v, lreg !! r = Some v → no_prov_disjoint_from_heap v).

    Lemma lift_untagged w' : get_tag w' = false → has_lift R C lreg lpc w'.
    Proof.
      intros Ht. exists (MkLWord w' None). split_and!;
        [by apply reg_word_ok_untagged | by apply reg_phys_untagged | by apply lderivable_pc, lwle_untagged].
    Qed.

    (** Below a register: the register's logical word, narrowed. *)
    Lemma lift_reg r w w' :
      reg φ !!ᵣ r = Some w → w' ⊑ w → get_tag w' = true → has_lift R C lreg lpc w'.
    Proof.
      intros Hr Hle Ht.
      destruct (erasure_reg_tagged Her Hr (word_le_tagged _ _ Hle Ht)) as (vs & Hvs & <- & Hok & Hp).
      destruct (word_le_lift R C _ vs w' (er_registry Her) Hok Hp (Hnoid r vs Hvs) Hle Ht)
        as (Hok' & Hp' & Hle').
      eexists. split_and!; [exact Hok' | exact Hp' | by eapply lderivable_reg].
    Qed.

    (** Below the PC: the logical PC, narrowed. *)
    Lemma lift_pc w' : w' ⊑ pcc φ → get_tag w' = true → has_lift R C lreg lpc w'.
    Proof.
      intros Hle Ht. rewrite (erasure_pc_exact Her) in Hle.
      pose proof (er_pc Her) as Hp. rewrite (erasure_pc_exact Her) in Hp.
      destruct (word_le_lift R C _ lpc w' (er_registry Her) (er_pc_word Her) Hp
                  (erasure_pc_no_prov_disjoint_from_heap Her) Hle Ht) as (Hok' & Hp' & Hle').
      eexists. split_and!; [exact Hok' | exact Hp' | by apply lderivable_pc].
    Qed.

    (** A sealing: the sealee keeps its provenance; the range is exact. *)
    Lemma lift_seal r1 r2 p g b e a sb :
      reg φ !!ᵣ r1 = Some (WSealRange true p g b e a) → reg φ !!ᵣ r2 = Some (WSealable sb) →
      permit_seal p = true → withinBounds b e a = true →
      get_tag (WSealed a sb) = true →
      has_lift R C lreg lpc (WSealed a sb).
    Proof.
      intros Hr1 Hr2 Hps Hwb Ht.
      destruct (erasure_reg_tagged Her Hr1 eq_refl) as ([w1 π1] & Hv1 & Hw1 & _ & _).
      cbn in Hw1; subst w1.
      destruct (erasure_reg_tagged Her Hr2 Ht) as ([w2 π2] & Hv2 & Hw2 & Hok & Hp).
      cbn in Hw2; subst w2.
      exists (WSealed a sb @@? π2). split_and!.
      - apply (reg_word_ok_seal _ _ sb); [by left | done].
      - eapply (reg_phys_derive_eq _ (WSealable sb @@? π2) true);
          [by rewrite and_tag_true | by destruct sb | done | by rewrite and_tag_true].
      - by eapply lderivable_seal.
    Qed.

    (** An unsealing: the sealed word keeps its provenance; the range is
        exact. *)
    Lemma lift_unseal r1 r2 p g b e a o sb :
      reg φ !!ᵣ r1 = Some (WSealRange true p g b e a) → reg φ !!ᵣ r2 = Some (WSealed o sb) →
      permit_unseal p = true → withinBounds b e o = true →
      get_tag (WSealable (unseal_sb g sb)) = true →
      has_lift R C lreg lpc (WSealable (unseal_sb g sb)).
    Proof.
      intros Hr1 Hr2 Hps Hwb Ht. cbn in Ht. rewrite get_tag_unseal in Ht.
      destruct (erasure_reg_tagged Her Hr1 eq_refl) as ([w1 π1] & Hv1 & Hw1 & _ & _).
      cbn in Hw1; subst w1.
      destruct (erasure_reg_tagged Her Hr2 Ht) as ([w2 π2] & Hv2 & Hw2 & Hok & Hp).
      cbn in Hw2; subst w2.
      exists (WSealable (unseal_sb g sb) @@? π2). split_and!.
      - apply (reg_word_ok_unseal _ _ sb _ _ o); [by destruct sb | | by destruct sb | done].
        by rewrite /= get_tag_unseal.
      - eapply (reg_phys_derive_eq _ (WSealed o sb @@? π2) true);
          [by rewrite and_tag_true | by destruct sb | by rewrite /= get_tag_unseal
          | by rewrite and_tag_true].
      - by eapply lderivable_unseal.
    Qed.

    (** Every derivable word lifts: one lemma per rule of [derivable]. *)
    Lemma derivable_lift w' : derivable φ w' → has_lift R C lreg lpc w'.
    Proof.
      intros Hder. destruct (get_tag w') eqn:Ht; last by apply lift_untagged.
      destruct Hder as [r w w' Hr Hle | w' Hle
                       | r1 r2 t p g b e a sb Hr1 Hr2 -> Hps Hwb
                       | r1 r2 t p g b e a o sb Hr1 Hr2 -> Hps Hwb].
      - by eapply lift_reg.
      - by apply lift_pc.
      - by eapply lift_seal.
      - by eapply lift_unseal.
    Qed.
  End lifts.

End capability_lift.
