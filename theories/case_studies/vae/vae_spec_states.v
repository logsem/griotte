From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec.
From griotte Require Export switcher_preamble vae vae_helper.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proofs of [vae_init_spec] and [vae_awkward_spec]

    The proofs of [vae_init_spec] (see [vae_spec]) and of [vae_awkward_spec]
    (see [vae_spec_closure]) are split along the control flow of
    [vae_main_code]. The block-group lemmas only depend on this file:
    - [vae_spec_init_blocks_1]: blocks 0-3, set the flag to [0], fetch the
      imports and jump to the switcher, for the call to [B.adv],
    - [vae_spec_init_blocks_2]: block 3, from the return of the call to
      [B.adv], halt,
    - [vae_spec_awkward_blocks_1]: blocks 4-6, set the flag to [0], fetch
      the switcher and jump to it, for the first call to [g],
    - [vae_spec_awkward_blocks_2]: blocks 7-9, from the return of the first
      call to [g], set the flag to [1], fetch the switcher and jump to it,
      for the second call to [g],
    - [vae_spec_awkward_blocks_3]: blocks 9-11, from the return of the second
      call to [g], assert that the flag is [1] and return.

    The logical steps between the block groups, which do not execute code,
    are in [vae_spec_world] (evolution of the world and of the custom
    location of the flag, preparation of the calls to the switcher, repair
    of the world before the return of [awkward]).

    The block-group lemmas start and end at addresses of the code
    [vae_main_code], given by [vae_block_offset] and [vae_instr_offset]. *)

Section VAE_Code.
  Context `{MP: MachineParameters} {swlayout : switcherLayout}.

  (** The blocks of [vae_main_code], as focused by [focus_block]. *)
  Definition vae_main_blocks : list (list Word) :=
    ltac:(code_blocks_of VAE_main_code_init)
    ++ ltac:(code_blocks_of (VAE_main_code_f ot_switcher)).

  Lemma vae_main_code_blocks : vae_main_code = concat vae_main_blocks.
  Proof. reflexivity. Qed.

End VAE_Code.

(** Offset of the first instruction of the block [n] in [vae_main_code]. *)
Notation vae_block_offset := (code_block_offset vae_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [vae_main_code]. *)
Notation vae_instr_offset := (code_instr_offset vae_main_blocks).

(** Unfold [vae_main_code] into the chain of its blocks, in the goal (both in
    the code and in the continuation). *)
Ltac vae_unfold_code :=
  rewrite /vae_main_code /VAE_main_code_init -!app_assoc /VAE_main_code_f.

Section VAE_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The bounds of the code, of the imports and of the data, as given to
      [vae_init_spec] and [vae_awkward_spec]. *)
  Definition vae_code_bounds (pc_b pc_e pc_a : Addr) (C_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length vae_main_code)%a ∧
    (pc_b + length (vae_main_imports C_f))%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition vae_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

  (** The capability of the entry point of the assert routine. *)
  Definition vae_assert_entry : Word :=
    WSentry RX Global b_assert e_assert b_assert.

  (** The arguments of both calls to the adversary: all the argument
      registers are cleared, and [ct0] is the entry point of the switcher. *)
  Definition vae_call_adv_arg_rmap : Reg :=
    {[ ca0 := WInt 0;
       ca1 := WInt 0;
       ca2 := WInt 0;
       ca3 := WInt 0;
       ca4 := WInt 0;
       ca5 := WInt 0;
       ct0 := vae_switcher_entry ]}.

  Lemma vae_call_adv_arg_rmap_is_arg :
    is_arg_rmap vae_call_adv_arg_rmap 8.
  Proof. by rewrite /is_arg_rmap /vae_call_adv_arg_rmap. Qed.

End VAE_States.
