From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode stack_world_resources.
From griotte Require Export assert_compiled_spec switcher_preamble cmdc_compiled.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proof of [cmdc_compiled_spec]

    The proof of [cmdc_compiled_spec] is split along the control flow of
    [cmdc_compiled_main_code], the function [run]. The block-group lemmas
    only depend on this file:
    - [cmdc_compiled_spec_prologue_blocks_1]: block 0, the prologue: spill
      [cra], [cs0] and [cs1] in the frame of [run], set [b := 0] and
      [c := 0] through 1-word capabilities in [cs0] and [cs1], and prepare
      the argument of the call to [B.f],
    - [cmdc_compiled_spec_call_blocks_2]: block 1 (resp. 5), fetch the
      callee and the switcher and jump to the switcher, for the call to
      [B.f] (resp. [C.g]),
    - [cmdc_compiled_spec_check_blocks_3]: blocks 2-3 (resp. 6-7), from the
      return of the call, load [c] (resp. [b]) and call the assert library,
    - [cmdc_compiled_spec_prep_blocks_4]: block 4, overwrite [b] and prepare
      the argument of the call to [C.g],
    - [cmdc_compiled_spec_epilogue_blocks_5]: blocks 8-9, restore the
      spilled registers and return: the thread exits.

    The logical steps between the block groups, which do not execute code,
    are in [cmdc_compiled_spec_world]. *)

Section CMDC_Compiled_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [cmdc_compiled_main_code], as focused by [focus_block]. *)
  Definition cmdc_compiled_main_blocks : list (list Word) :=
    ltac:(code_blocks_of cmdc_compiled_main_code).

  Lemma cmdc_compiled_main_code_blocks :
    cmdc_compiled_main_code = concat cmdc_compiled_main_blocks.
  Proof. reflexivity. Qed.

  (** The words of the imports of [main], in the order of
      [cmdc_compiled_main_asm]: the switcher, the entry of the compiled
      assert library, the exports [B.f] and [C.g]. *)
  Definition cmdc_compiled_main_imports `{!switcherLayout}
    (b_lib e_lib : Addr) (B_f C_g : Sealable) : list Word :=
    [ switcher_entry_call;
      assert_compiled_entry_of Global b_lib e_lib;
      WSealed ot_switcher B_f;
      WSealed ot_switcher C_g ].

End CMDC_Compiled_Code.

(** The number of arguments of the exports [B.f] and [C.g]. *)
Definition cmdc_B_f_args : nat := 1.
Definition cmdc_C_g_args : nat := 1.

(** Offset of the first instruction of the block [n] in
    [cmdc_compiled_main_code]. *)
Notation cmdc_compiled_block_offset := (code_block_offset cmdc_compiled_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in
    [cmdc_compiled_main_code]. *)
Notation cmdc_compiled_instr_offset := (code_instr_offset cmdc_compiled_main_blocks).

(** Offset of the label [s] of [cmdc_compiled_main_asm] from the start of
    the PCC, the imports. *)
Notation cmdc_compiled_label s := (asm_label cmdc_compiled_main_asm s).

(** Offset of the label [s] in [cmdc_compiled_main_code], which starts at
    the label [.Lcmdc_run]. *)
Notation cmdc_compiled_label_offset s :=
  (asm_label_offset cmdc_compiled_main_asm ".Lcmdc_run" s).

(** Index of the block of [cmdc_compiled_main_code] that defines the label
    [s]. *)
Notation cmdc_compiled_block s := (asm_block cmdc_compiled_main_asm s).

(** ** The two calls of [run]

    The call to [B.f] (blocks 1-3) and the call to [C.g] (blocks 5-7) have
    the same code, up to the import of the callee, the global loaded after
    the return, and the value asserted. *)
Inductive cmdc_compiled_call := cmdc_compiled_call_B | cmdc_compiled_call_C.

(** The start of the call: fetch the callee and the switcher. *)
Definition cmdc_compiled_call_label (c : cmdc_compiled_call) : string :=
  match c with
  | cmdc_compiled_call_B => ".Lcmdc_run_call_B_f"%string
  | cmdc_compiled_call_C => ".Lcmdc_run_call_C_g"%string
  end.

(** The return point of the call. *)
Definition cmdc_compiled_return_label (c : cmdc_compiled_call) : string :=
  match c with
  | cmdc_compiled_call_B => ".Lcmdc_run_return_B_f"%string
  | cmdc_compiled_call_C => ".Lcmdc_run_return_C_g"%string
  end.

(** The call to the assert library that follows the call. *)
Definition cmdc_compiled_assert_label (c : cmdc_compiled_call) : string :=
  match c with
  | cmdc_compiled_call_B => ".Lcmdc_run_assert_1"%string
  | cmdc_compiled_call_C => ".Lcmdc_run_assert_2"%string
  end.

(** The code after the assertion. *)
Definition cmdc_compiled_next_label (c : cmdc_compiled_call) : string :=
  match c with
  | cmdc_compiled_call_B => ".Lcmdc_run_return_assert_1"%string
  | cmdc_compiled_call_C => ".Lcmdc_run_return_assert_2"%string
  end.

(** The index of the import of the callee. *)
Definition cmdc_compiled_call_import (c : cmdc_compiled_call) : Z :=
  match c with cmdc_compiled_call_B => 2 | cmdc_compiled_call_C => 3 end.

(** The callee. *)
Definition cmdc_compiled_call_target (c : cmdc_compiled_call) (B_f C_g : Sealable)
  : Sealable :=
  match c with cmdc_compiled_call_B => B_f | cmdc_compiled_call_C => C_g end.

(** The value asserted after the return of the call. *)
Definition cmdc_compiled_call_expected (c : cmdc_compiled_call) : Z :=
  match c with cmdc_compiled_call_B => 0 | cmdc_compiled_call_C => 42 end.

(** The register that points to the global checked after the call, the one
    not shared with the callee: [c] in [cs1], resp. [b] in [cs0]. *)
Definition cmdc_compiled_call_checked (c : cmdc_compiled_call) : RegName :=
  match c with cmdc_compiled_call_B => cs1 | cmdc_compiled_call_C => cs0 end.

(** The cursor of the stack in [run], below its frame: the frame of [run]
    is the [cmdc_compiled_main_run_frame_size] words below the cursor of a
    fresh stack $[b, e)$. *)
Definition cmdc_compiled_frame_a (b e : Addr) : Addr :=
  stk_start_a b e ^+ (- Z.of_nat cmdc_compiled_main_run_frame_size).

Section CMDC_Compiled_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  (** The bounds of the code and of the imports, as given to
      [cmdc_compiled_spec]. *)
  Definition cmdc_compiled_code_bounds (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_compiled_main_code) ∧
    (pc_b + cmdc_compiled_main_run_offset)%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false ∧
    is_heap_cap (WSealed ot_switcher B_f) = false ∧
    is_heap_cap (WSealed ot_switcher C_g) = false.

End CMDC_Compiled_States.

(** ** The free part of a stack at any cursor

    The cursor-generic forms of [stk_start_region_split],
    [stk_start_seq_split], [stk_start_revoked_split] and
    [stk_start_revoked_addresses]. *)
Section Cursor_stack.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  (* TODO: move to case_studies/case_study_spec_helpers.v *)
  Lemma stk_cursor_region_split (b e a : Addr) (stk_mem : list LWord) :
    (b <= a)%a -> (a <= e)%a ->
    [[b, e]] ↦ₐ [[stk_mem]] -∗
    ∃ stk_mem' stk_rest,
      [[stk_free_b b a, stk_free_e e a]] ↦ₐ [[stk_mem']] ∗
      [[a, e]] ↦ₐ [[stk_rest]].
  Proof.
    iIntros (Hba Hae) "Hstk".
    iDestruct (big_sepL2_length with "Hstk") as %Hlen.
    rewrite -(take_drop (finz.dist b a) stk_mem).
    iDestruct (region_pointsto_split b e a with "Hstk") as "[Hstk Hrest]".
    { solve_addr+Hba Hae. }
    { rewrite length_take finz_seq_between_length in Hlen |- *.
      rewrite /finz.dist in Hlen |- *; solve_addr+Hba Hae Hlen. }
    iExists _, _. iFrame "Hstk Hrest".
  Qed.

  (* TODO: move to case_studies/case_study_spec_helpers.v *)
  Lemma stk_cursor_seq_split (b e a : Addr) :
    (b <= a)%a -> (a <= e)%a ->
    finz.seq_between b e = stk_free b e a ++ finz.seq_between a e.
  Proof.
    intros Hba Hae. rewrite /stk_free. apply finz_seq_between_split.
    stk_unfold; solve_addr+Hba Hae.
  Qed.

  (* TODO: move to case_studies/case_study_spec_helpers.v *)
  Lemma stk_cursor_revoked_split (W : WORLD) (C : CmptName) (b e a : Addr) :
    (b <= a)%a -> (a <= e)%a ->
    StackRevokedResources W C (finz.seq_between b e) ⊣⊢
    StackRevokedResources W C (stk_free b e a) ∗
    StackRevokedResources W C (finz.seq_between a e).
  Proof.
    intros Hba Hae. by rewrite {1}(stk_cursor_seq_split b e a Hba Hae) StackRevokedResources_app.
  Qed.

  (* TODO: move to case_studies/case_study_spec_helpers.v *)
  Lemma stk_cursor_revoked_addresses (W : WORLD) (b e a : Addr) :
    (b <= a)%a -> (a <= e)%a ->
    revoked_addresses W (finz.seq_between b e) ->
    revoked_addresses W (stk_free b e a).
  Proof.
    intros Hba Hae Hrevoked.
    rewrite (stk_cursor_seq_split b e a Hba Hae) in Hrevoked.
    by apply revoked_addresses_app in Hrevoked as [? _].
  Qed.
End Cursor_stack.
