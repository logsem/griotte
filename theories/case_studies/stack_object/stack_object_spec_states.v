From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec checkra checkints check_no_overlap_spec.
From griotte Require Export switcher_preamble stack_object.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proofs of [so_init_spec] and [stack_object_f_spec]

    The proofs of [so_init_spec] (see [stack_object_spec]) and of
    [stack_object_f_spec] (see [stack_object_spec_closure]) are split along
    the control flow of [so_main_code]. The block-group lemmas only depend
    on this file:
    - [stack_object_spec_run_blocks_1]: blocks 0-2, fetch the imports and
      jump to the switcher, for the call to [C.adv],
    - [stack_object_spec_run_blocks_2]: block 2, from the return of the call
      to [C.adv], halt,
    - [stack_object_spec_check_blocks_1]: blocks 3-5, save the callback
      and check that the stack object [in] is readable and does not overlap
      with the stack frame,
    - [stack_object_spec_checkints_blocks_2]: block 6, check that [in]
      only contains integers,
    - [stack_object_spec_call_blocks_3]: blocks 7-9, push the secret,
      allocate the stack object [z], fetch the switcher and jump to it, for
      the call to [g],
    - [stack_object_spec_return_blocks_4]: blocks 10-12, from the return of
      the call to [g], assert that the secret is unchanged and return.

    The logical steps between the block groups, which do not execute code,
    are in [stack_object_spec_world_object] (opening and closing the world
    around [checkints]), [stack_object_spec_world_call] (preparation of the
    calls to the switcher) and [stack_object_spec_world_return] (repair of
    the world before the return of [f]).

    The block-group lemmas start and end at addresses of the code
    [so_main_code], given by [so_block_offset] and [so_instr_offset]. *)

Section SO_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [so_main_code], as focused by [focus_block]. *)
  Definition so_main_blocks : list (list Word) :=
    ltac:(code_blocks_of SO_main_code_run) ++ ltac:(code_blocks_of SO_main_code_f).

  Lemma so_main_code_blocks : so_main_code = concat so_main_blocks.
  Proof. reflexivity. Qed.

  (** [so_main_code], as the chain of its blocks. *)
  Lemma so_main_code_flat :
    so_main_code =
      fetch_instrs 0 ct0 cs0 cs1
      ++ fetch_instrs 2 ct1 cs0 cs1
      ++ encodeInstrsW [Jalr cra ct0; Halt]
      ++ encodeInstrsW [Mov ct1 ca1]
      ++ checkra_instrs ca0 cs0 cs1
      ++ check_no_overlap_instrs ca0 csp cs0 cs1
      ++ checkints_instrs ca0 cs0 cs1
      ++ so_f_alloc_instrs
      ++ fetch_instrs 0 ct0 cs0 cs1
      ++ so_f_call_instrs
      ++ so_f_assert_prep_instrs
      ++ assert_instrs 1 ct2 ct3 ct4
      ++ so_f_return_instrs.
  Proof. rewrite /so_main_code /SO_main_code_run /SO_main_code_f -!app_assoc //. Qed.

End SO_Code.

(** Offset of the first instruction of the block [n] in [so_main_code]. *)
Notation so_block_offset := (code_block_offset so_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [so_main_code]. *)
Notation so_instr_offset := (code_instr_offset so_main_blocks).

(** Unfold [so_main_code] into the chain of its blocks, in the goal (both in
    the code and in the continuation). *)
Ltac so_unfold_code := rewrite so_main_code_flat.

(** ** Addresses of the stack object [in]

    The addresses of the stack object [(p, g, b, e, _)] passed to [f] are
    either permanent or temporary in the world [W] of the call. The
    temporary ones are revoked, together with the stack frame, by [f]. *)
Section SO_Object.

  Definition so_object_addresses (b e : Addr) :=
    finz.seq_between b e.

  Definition so_object_temporaries (W : WORLD) (b e : Addr) :=
    filter
      (fun a => std W !! a = Some Temporary)
      (so_object_addresses b e).

  Definition so_object_permanents (W : WORLD) (b e : Addr) :=
    filter
      (fun a => std W !! a = Some Permanent)
      (so_object_addresses b e).

  (** The revoked addresses [l] that are not temporary addresses of the
      stack object. *)
  Definition so_revoked_without_object
      (W : WORLD) (b e : Addr) (l : list Addr) :=
    filter
      (fun a => a ∉ so_object_temporaries W b e)
      l.

  Lemma NoDup_subset_filter_membership
      {A} `{EqDecision0 : EqDecision A} (xs ys : list A) :
    NoDup xs ->
    NoDup ys ->
    xs ⊆ ys ->
    xs ≡ₚ filter (fun y => y ∈ xs) ys.
  Proof.
    intros Hnodup_xs Hnodup_ys Hsubset.
    generalize dependent xs.
    induction ys as [|y ys]; intros xs Hnodup_xs Hsubset.
    - destruct xs; last set_solver.
      done.
    - cbn.
      apply NoDup_cons in Hnodup_ys as [Hy_ys Hnodup_ys].
      destruct (decide (y ∈ xs)) as [Hy_xs | Hy_xs].
      + apply elem_of_Permutation in Hy_xs as [xs' Hxs].
        setoid_rewrite Hxs in Hnodup_xs.
        apply NoDup_cons in Hnodup_xs as [Hy_xs' Hnodup_xs'].
        setoid_rewrite Hxs in Hsubset.
        setoid_rewrite Hxs at 1.
        assert (xs' ⊆ ys) as Hsubset'.
        { intros x Hx.
          assert (x ≠ y) by (intro; simplify_eq; done).
          apply (list_elem_of_further _ y) in Hx.
          apply Hsubset in Hx.
          apply elem_of_cons in Hx as [Hx|Hx]; auto.
          done.
        }
        eapply IHys in Hsubset'; eauto.
        apply Permutation_cons; first done.
        rewrite Hsubset'.
        clear -Hnodup_ys Hxs Hy_ys.
        induction ys; cbn; first done.
        apply not_elem_of_cons in Hy_ys as [Hy_a Hy_ys].
        apply NoDup_cons in Hnodup_ys as [_ Hnodup_ys].
        destruct (decide (a ∈ xs')) as [Ha|Ha].
        * apply (list_elem_of_further _ y) in Ha.
          setoid_rewrite <- Hxs in Ha.
          rewrite decide_True; last done.
          rewrite IHys; auto.
        * rewrite decide_False; first (rewrite IHys; auto).
          intros Ha'.
          setoid_rewrite Hxs in Ha'.
          apply elem_of_cons in Ha' as [Ha'|?]; auto.
      + eapply IHys; auto.
        intros x Hx.
        assert (x ≠ y) by (intro; simplify_eq; done).
        apply Hsubset in Hx.
        apply elem_of_cons in Hx as [Hx|Hx]; auto.
        done.
  Qed.

  Lemma so_object_addresses_partition W b e :
    Forall
      (fun a =>
         std W !! a = Some Permanent \/
         std W !! a = Some Temporary)
      (so_object_addresses b e) ->
    so_object_addresses b e
      ≡ₚ so_object_permanents W b e ++
          so_object_temporaries W b e.
  Proof.
    intros Hstates.
    rewrite /so_object_permanents /so_object_temporaries
      /so_object_addresses in Hstates |- *.
    generalize (finz.seq_between b e), Hstates.
    clear Hstates.
    induction l; intros Hl; cbn; first done.
    apply Forall_cons in Hl as [Ha Hl].
    apply IHl in Hl.
    destruct Ha as [Ha | Ha].
    - assert (std W !! a <> Some Temporary) as Ha'
        by (intro; simplify_map_eq).
      rewrite (decide_True _ _ Ha); auto.
      rewrite (decide_False _ _ Ha'); auto.
      cbn. rewrite -Hl. done.
    - assert (std W !! a <> Some Permanent) as Ha'
        by (intro; simplify_map_eq).
      rewrite (decide_True _ _ Ha); auto.
      rewrite (decide_False _ _ Ha'); auto.
      cbn. rewrite -Permutation_middle -Hl. done.
  Qed.

  Lemma so_object_temporaries_NoDup W b e :
    NoDup (so_object_temporaries W b e).
  Proof.
    apply NoDup_filter, finz_seq_between_NoDup.
  Qed.

  Lemma so_object_permanents_NoDup W b e :
    NoDup (so_object_permanents W b e).
  Proof.
    apply NoDup_filter, finz_seq_between_NoDup.
  Qed.

End SO_Object.

Section SO_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The bounds of the code and of the imports, as given to [so_init_spec]
      and [stack_object_f_spec]. *)
  Definition so_code_bounds (pc_b pc_e pc_a : Addr) (C_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ∧
    (pc_b + length (so_main_imports C_f))%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition so_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

  (** The capability of the entry point of the assert routine. *)
  Definition so_assert_entry : Word :=
    WSentry RX Global b_assert e_assert b_assert.

End SO_States.
