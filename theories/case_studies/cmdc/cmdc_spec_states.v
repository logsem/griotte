From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec switcher_preamble cmdc.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proof of [cmdc_spec]

    The proof of [cmdc_spec] is split along the control flow of
    [cmdc_main_code]. The block-group lemmas only depend on this
    file:
    - [cmdc_spec_init_blocks_1]: block 0, initialisation of the data and of
      the argument of the call to [B.f],
    - [cmdc_spec_call_blocks_2]: blocks 1-3 (resp. 6-8), fetch the imports
      and jump to the switcher, for the call to [B.f] (resp. [C.g]),
    - [cmdc_spec_check_blocks_3]: blocks 3-4 (resp. 8-9), from the return
      of the call to [B.f] (resp. [C.g]), assert the value of [c] (resp.
      [b]),
    - [cmdc_spec_prep_blocks_4]: block 5, overwrite [b] and prepare the
      argument of the call to [C.g],
    - [cmdc_spec_halt_blocks_5]: block 10, halt.

    The two calls have the same shape, so that [cmdc_spec_call_blocks_2] and
    [cmdc_spec_check_blocks_3] are parametrised by the call ([cmdc_call]).

    The logical steps between the block groups, which do not execute code,
    are in [cmdc_spec_world].

    The block-group lemmas start and end at addresses of the code
    [cmdc_main_code], given by the labels of [cmdc_main_asm]
    ([cmdc_label_offset]). *)

Section CMDC_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [cmdc_main_code], as focused by [focus_block]. *)
  Definition cmdc_main_blocks : list (list Word) := ltac:(code_blocks_of cmdc_main_code).

  Lemma cmdc_main_code_blocks : cmdc_main_code = concat cmdc_main_blocks.
  Proof. reflexivity. Qed.

End CMDC_Code.

(** Offset of the first instruction of the block [n] in [cmdc_main_code]. *)
Notation cmdc_block_offset := (code_block_offset cmdc_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [cmdc_main_code]. *)
Notation cmdc_instr_offset := (code_instr_offset cmdc_main_blocks).

(** Offset of the label [s] of [cmdc_main_asm] from the start of the PCC,
    the imports. *)
Notation cmdc_label s := (asm_label cmdc_main_asm s).

(** Offset of the label [s] in [cmdc_main_code], which starts at the label
    [.Lcmdc_init]. *)
Notation cmdc_label_offset s := (asm_label_offset cmdc_main_asm ".Lcmdc_init" s).

(** Index of the block of [cmdc_main_code] that defines the label [s]. *)
Notation cmdc_block s := (asm_block cmdc_main_asm s).

(** ** The two calls of [cmdc_main_code]

    The call to [B.f] (blocks 1-4) and the call to [C.g] (blocks 6-9) have
    the same code, up to the import of the callee and the value asserted
    after the return. *)
Inductive cmdc_call := cmdc_call_B | cmdc_call_C.

(** The start of the call: fetch the entry point of the switcher. *)
Definition cmdc_call_label (c : cmdc_call) : string :=
  match c with cmdc_call_B => ".Lcmdc_call_B"%string | cmdc_call_C => ".Lcmdc_call_C"%string end.

(** The return point of the call. *)
Definition cmdc_return_label (c : cmdc_call) : string :=
  match c with cmdc_call_B => ".Lcmdc_return_B"%string | cmdc_call_C => ".Lcmdc_return_C"%string end.

(** The code after the assertion that follows the call. *)
Definition cmdc_next_label (c : cmdc_call) : string :=
  match c with cmdc_call_B => ".Lcmdc_prep_C"%string | cmdc_call_C => ".Lcmdc_halt"%string end.

(** The index of the import of the callee. *)
Definition cmdc_call_import (c : cmdc_call) : Z :=
  match c with cmdc_call_B => 2 | cmdc_call_C => 3 end.

(** The callee. *)
Definition cmdc_call_target (c : cmdc_call) (B_f C_g : Sealable) : Sealable :=
  match c with cmdc_call_B => B_f | cmdc_call_C => C_g end.

(** The value asserted after the return of the call. *)
Definition cmdc_call_expected (c : cmdc_call) : Z :=
  match c with cmdc_call_B => 0 | cmdc_call_C => 42 end.

Section CMDC_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The bounds of the code and of the imports, as given to [cmdc_spec]. *)
  Definition cmdc_code_bounds (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ∧
    (pc_b + cmdc_label ".Lcmdc_init")%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false ∧
    is_heap_cap (WSealed ot_switcher B_f) = false ∧
    is_heap_cap (WSealed ot_switcher C_g) = false.

  (** The capability of the entry point of the switcher. *)
  Definition cmdc_switcher_entry : Word :=
    WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call.

End CMDC_States.
