From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.

(** * Offsets of the blocks of a code

    A code [l1 ++ l2 ++ ... ++ ln] is split into the list of its blocks
    [[l1; l2; ...; ln]], as focused by [focus_block]. The offsets of the
    blocks and of their instructions are given by [code_block_offset] and
    [code_instr_offset], and computed by [offsets_compute]. *)

(** The list of the sub-blocks of a code [l1 ++ l2 ++ ... ++ ln]. *)
Ltac app_chain_to_list c :=
  lazymatch c with
  | ?l1 ++ ?l2 => let r := app_chain_to_list l2 in constr:(l1 :: r)
  | ?l => constr:([l])
  end.

(** Build the list of the blocks of the code [c], a constant (possibly
    applied to its implicit arguments) whose body is a chain of [++].
    To be used as [Definition blocks := ltac:(code_blocks_of c)]. *)
Ltac code_blocks_of c :=
  let c := eval red in c in
  let c := eval cbv beta zeta in c in
  let r := app_chain_to_list c in
  exact r.

(** Offset of the first instruction of the block [n] in [concat blocks]. *)
Definition code_block_offset {A} (blocks : list (list A)) (n : nat) : Z :=
  Z.of_nat (sum_list (length <$> take n blocks)).

(** Offset of the [i]-th instruction of the block [n] in [concat blocks]. *)
Definition code_instr_offset {A} (blocks : list (list A)) (n i : nat) : Z :=
  (code_block_offset blocks n + Z.of_nat i)%Z.

(** Compute the offsets of the blocks in the goal and the hypotheses. *)
Ltac offsets_compute :=
  repeat match goal with
    | |- context [code_instr_offset ?bs ?n ?i] =>
        let v := eval vm_compute in (code_instr_offset bs n i) in
        change (code_instr_offset bs n i) with v
    | H : context [code_instr_offset ?bs ?n ?i] |- _ =>
        let v := eval vm_compute in (code_instr_offset bs n i) in
        change (code_instr_offset bs n i) with v in H
    | |- context [code_block_offset ?bs ?n] =>
        let v := eval vm_compute in (code_block_offset bs n) in
        change (code_block_offset bs n) with v
    | H : context [code_block_offset ?bs ?n] |- _ =>
        let v := eval vm_compute in (code_block_offset bs n) in
        change (code_block_offset bs n) with v in H
    end.

(** Change the address of the PC to [a']. *)
Ltac change_pc_to a' :=
  match goal with |- context [ environments.Esnoc _ _ (PC ↦ᵣ WCap _ _ _ _ ?a)%I ] =>
    rewrite (_ : a = a');
    [| offsets_compute; solve_addr]
  end.

(** Unfold the code [c], a constant, in [h], in order to focus on its
    blocks. *)
Tactic Notation "unfold_code" reference(c) constr(h) :=
  iEval (cbv beta delta [c] zeta) in h.

(** Focus on block [n] of the code [concat blocks] (at address [pc_a]),
    whose first address [a] is [pc_a + code_block_offset blocks n]. The PC
    is moved to [a], when possible. *)
Tactic Notation "focus_block" constr(n) constr(h) "of" constr(blocks) "at" constr(pc_a)
    "as" ident(a) ident(Ha) constr(hi) constr(hcont) :=
  focus_block_nochangePC n h as a Ha hi hcont;
  let Ha' := fresh in
  assert ((pc_a + code_block_offset blocks n)%a = Some a) as Ha'
      by (cbn in Ha; offsets_compute; solve_addr);
  clear Ha; rename Ha' into Ha;
  try change_pc_to a.
