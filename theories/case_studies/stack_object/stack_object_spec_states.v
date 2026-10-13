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
    [so_main_code], given by the labels of [so_main_asm]
    ([so_label_offset]). *)

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
      so_main_instrs_n 0 ++ so_main_instrs_n 1 ++ so_main_instrs_n 2
      ++ so_main_instrs_n 3 ++ so_main_instrs_n 4 ++ so_main_instrs_n 5
      ++ so_main_instrs_n 6 ++ so_main_instrs_n 7 ++ so_main_instrs_n 8
      ++ so_main_instrs_n 9 ++ so_main_instrs_n 10 ++ so_main_instrs_n 11
      ++ so_main_instrs_n 12.
  Proof. rewrite /so_main_code /SO_main_code_run /SO_main_code_f -!app_assoc //. Qed.

End SO_Code.

(** Offset of the first instruction of the block [n] in [so_main_code]. *)
Notation so_block_offset := (code_block_offset so_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [so_main_code]. *)
Notation so_instr_offset := (code_instr_offset so_main_blocks).

(** Offset of the label [s] of [so_main_asm] from the start of the PCC,
    the imports. *)
Notation so_label s := (asm_label so_main_asm s).

(** Offset of the label [s] in [so_main_code], which starts at the label
    [.Lso_run]. *)
Notation so_label_offset s := (asm_label_offset so_main_asm ".Lso_run" s).

(** Index of the block of [so_main_code] that defines the label [s]. *)
Notation so_block s := (asm_block so_main_asm s).

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

  Definition so_object_temporaries (W : WORLD) (π : option AId) (b e : Addr) :=
    filter
      (fun a => std W !! addr_key π a = Some Temporary)
      (so_object_addresses b e).

  Definition so_object_permanents (W : WORLD) (π : option AId) (b e : Addr) :=
    filter
      (fun a => std W !! addr_key π a = Some Permanent)
      (so_object_addresses b e).

  (** The revoked addresses [l] that are not temporary addresses of the
      stack object. *)
  Definition so_revoked_without_object
      (W : WORLD) (π : option AId) (b e : Addr) (l : list LAddr) :=
    filter
      (fun a => a ∉ addr_key π <$> so_object_temporaries W π b e)
      l.

  (** The object may be a heap object: its addresses are keyed by [addr_key π]. *)
  Global Instance addr_key_inj π : Inj eq eq (addr_key π).
  Proof.
    intros a a' Heq.
    rewrite -(addr_key_addr π a) -(addr_key_addr π a'). by rewrite Heq.
  Qed.

  Lemma NoDup_addr_key_fmap π (l : list Addr) : NoDup l -> NoDup (addr_key π <$> l).
  Proof. intros Hl. apply NoDup_fmap_2; [apply _|done]. Qed.

  Lemma elem_of_addr_key_fmap π a (l : list Addr) :
    addr_key π a ∈ addr_key π <$> l <-> a ∈ l.
  Proof. apply (list_elem_of_fmap_inj (addr_key π)). Qed.

  Lemma addr_key_LNonHeap_eq π a b : addr_key π a = LNonHeap b -> a = b.
  Proof. intros Heq. rewrite -(addr_key_addr π a). by rewrite Heq. Qed.

  Lemma addr_key_elem_of_LNonHeap_fmap π a (l : list Addr) :
    addr_key π a ∈ LNonHeap <$> l -> a ∈ l.
  Proof.
    intros (b & Heq & Hb)%list_elem_of_fmap.
    by apply addr_key_LNonHeap_eq in Heq as ->.
  Qed.

  Lemma LNonHeap_elem_of_addr_key_fmap π b (l : list Addr) :
    LNonHeap b ∈ addr_key π <$> l -> b ∈ l.
  Proof.
    intros (a & Heq & Ha)%list_elem_of_fmap. symmetry in Heq.
    by apply addr_key_LNonHeap_eq in Heq as ->.
  Qed.

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

  Lemma so_object_addresses_partition W π b e :
    Forall
      (fun a =>
         std W !! addr_key π a = Some Permanent \/
         std W !! addr_key π a = Some Temporary)
      (so_object_addresses b e) ->
    so_object_addresses b e
      ≡ₚ so_object_permanents W π b e ++
          so_object_temporaries W π b e.
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
    - assert (std W !! addr_key π a <> Some Temporary) as Ha'
        by (intro; simplify_map_eq).
      rewrite (decide_True _ _ Ha); auto.
      rewrite (decide_False _ _ Ha'); auto.
      cbn. rewrite -Hl. done.
    - assert (std W !! addr_key π a <> Some Permanent) as Ha'
        by (intro; simplify_map_eq).
      rewrite (decide_True _ _ Ha); auto.
      rewrite (decide_False _ _ Ha'); auto.
      cbn. rewrite -Permutation_middle -Hl. done.
  Qed.

  Lemma so_object_temporaries_NoDup W π b e :
    NoDup (so_object_temporaries W π b e).
  Proof.
    apply NoDup_filter, finz_seq_between_NoDup.
  Qed.

  Lemma so_object_permanents_NoDup W π b e :
    NoDup (so_object_permanents W π b e).
  Proof.
    apply NoDup_filter, finz_seq_between_NoDup.
  Qed.

End SO_Object.

Section SO_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The bounds of the code and of the imports, as given to [so_init_spec]
      and [stack_object_f_spec]. *)
  Definition so_code_bounds (pc_b pc_e pc_a : Addr) (C_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ∧
    (pc_b + so_label ".Lso_run")%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false.

  (** The capability of the entry point of the switcher. *)
  Definition so_switcher_entry : Word :=
    WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call.

  (** The capability of the entry point of the assert routine. *)
  Definition so_assert_entry : Word :=
    WSentry true RX Global b_assert e_assert b_assert.

End SO_States.
