From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require assembler.

(** * Offsets of the blocks of a code

    A code [l1 ++ l2 ++ ... ++ ln] is split into the list of its blocks
    [[l1; l2; ...; ln]], as focused by [focus_block]. The offsets of the
    blocks and of their instructions are given by [code_block_offset] and
    [code_instr_offset], and computed by [offsets_compute]. The offsets of
    the labels of an assembled program are related to them by
    [label_offset_code_block] and [label_offset_code_instr]. *)

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

(** The offset of a label of a program by blocks [P] counts the words of
    the code, its instructions and its symbols, while the offsets of the
    blocks of the assembled code count its instructions only. *)
Lemma label_offset_code_instr P n b1 s b2 :
  assembler.Asm_Griotte.asm_ok (assembler.Asm_Griotte.assemble_block_check P) →
  P !! n = Some (b1 ++ assembler.Asm_Griotte.ASM_Label s :: b2) →
  Z.of_nat (assembler.Asm_Griotte.label_offset (concat P) s) =
    (Z.of_nat (assembler.Asm_Griotte.asm_symbols (concat (take n P) ++ b1)) +
     code_instr_offset (assembler.Asm_Griotte.assemble_block P) n (assembler.Asm_Griotte.asm_instrs b1))%Z.
Proof.
  intros Hok HP.
  destruct (assembler.Asm_Griotte.assemble_block_check_ok P Hok) as (Henv & benv & Hbs).
  assert (concat P =
            (concat (take n P) ++ b1) ++ assembler.Asm_Griotte.ASM_Label s :: b2 ++ concat (drop (S n) P))
    as Hconcat.
  { rewrite -{1}(take_drop_middle P n _ HP) concat_app /=. by rewrite -!app_assoc. }
  rewrite Hconcat in Henv |- *. rewrite assembler.Asm_Griotte.label_offset_app //.
  rewrite /code_instr_offset /code_block_offset fmap_take
    (assembler.Asm_Griotte.assemble_blocks_length _ _ _ _ Hbs) -fmap_take.
  assert (∀ L, sum_list (assembler.Asm_Griotte.asm_instrs <$> L) = assembler.Asm_Griotte.asm_instrs (concat L))
    as Hsum.
  { induction L as [|b L IH]; [done|]. by rewrite /= assembler.Asm_Griotte.asm_instrs_app IH. }
  rewrite Hsum !assembler.Asm_Griotte.asm_words_split !assembler.Asm_Griotte.asm_symbols_app
    !assembler.Asm_Griotte.asm_instrs_app.
  lia.
Qed.

(** A label at the start of the block [n] is at the offset of the block,
    after the symbols of the previous blocks. *)
Lemma label_offset_code_block P n s b :
  assembler.Asm_Griotte.asm_ok (assembler.Asm_Griotte.assemble_block_check P) →
  P !! n = Some (assembler.Asm_Griotte.ASM_Label s :: b) →
  Z.of_nat (assembler.Asm_Griotte.label_offset (concat P) s) =
    (Z.of_nat (assembler.Asm_Griotte.asm_symbols (concat (take n P))) +
     code_block_offset (assembler.Asm_Griotte.assemble_block P) n)%Z.
Proof.
  intros Hok HP. rewrite (label_offset_code_instr P n [] s b) //.
  rewrite /code_instr_offset app_nil_r /=. lia.
Qed.

(** Compute the offsets of the blocks and the offsets of the labels
    ([label_offset], [label_offset_from]) in the goal and the hypotheses.
    The code must be closed. *)
Ltac offsets_compute :=
  repeat match goal with
    | |- context [assembler.Asm_Griotte.label_offset_from ?l ?f ?s] =>
        let v := eval vm_compute in (assembler.Asm_Griotte.label_offset_from l f s) in
        change (assembler.Asm_Griotte.label_offset_from l f s) with v
    | H : context [assembler.Asm_Griotte.label_offset_from ?l ?f ?s] |- _ =>
        let v := eval vm_compute in (assembler.Asm_Griotte.label_offset_from l f s) in
        change (assembler.Asm_Griotte.label_offset_from l f s) with v in H
    | |- context [Z.of_nat (assembler.Asm_Griotte.label_offset ?l ?s)] =>
        let v := eval vm_compute in (Z.of_nat (assembler.Asm_Griotte.label_offset l s)) in
        change (Z.of_nat (assembler.Asm_Griotte.label_offset l s)) with v
    | H : context [Z.of_nat (assembler.Asm_Griotte.label_offset ?l ?s)] |- _ =>
        let v := eval vm_compute in (Z.of_nat (assembler.Asm_Griotte.label_offset l s)) in
        change (Z.of_nat (assembler.Asm_Griotte.label_offset l s)) with v in H
    | |- context [assembler.Asm_Griotte.label_offset ?l ?s] =>
        let v := eval vm_compute in (assembler.Asm_Griotte.label_offset l s) in
        change (assembler.Asm_Griotte.label_offset l s) with v
    | H : context [assembler.Asm_Griotte.label_offset ?l ?s] |- _ =>
        let v := eval vm_compute in (assembler.Asm_Griotte.label_offset l s) in
        change (assembler.Asm_Griotte.label_offset l s) with v in H
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
  try (unfold lword_of_word);
  match goal with |- context [ environments.Esnoc _ _ (PC ↦ₚ (WCap _ _ _ _ _ ?a) @@? _)%I ] =>
    rewrite (_ : a = a');
    [| offsets_compute; solve_addr]
  end.

(** Unfold the code [c], a constant, in [h], in order to focus on its
    blocks. *)
Tactic Notation "unfold_code" reference(c) constr(h) :=
  iEval (cbv beta delta [c] zeta) in h.

(** Positions by label in an assembled program by blocks [P]: the offset
    of the label [s] from the start of the program, the offset of [s] from
    the label [from], and the index of the block that defines [s]. *)
Notation asm_label P s :=
  (Z.of_nat (assembler.Asm_Griotte.label_offset (concat P) s%string)).
Notation asm_label_offset P from s :=
  (assembler.Asm_Griotte.label_offset_from (concat P) from%string s%string).
Notation asm_block P s := (assembler.Asm_Griotte.label_block P s%string).

(** Focus on block [n] of the code [concat blocks] (at address [pc_a]),
    whose first address [a] is [pc_a + code_block_offset blocks n]. The PC
    is moved to [a], when possible. The index [n] can be given by a label,
    as [asm_block P s]: it is computed first. *)
Tactic Notation "focus_block" constr(n) constr(h) "of" constr(blocks) "at" constr(pc_a)
    "as" ident(a) ident(Ha) constr(hi) constr(hcont) :=
  let n := eval vm_compute in n in
  focus_block_nochangePC n h as a Ha hi hcont;
  let Ha' := fresh in
  assert ((pc_a + code_block_offset blocks n)%a = Some a) as Ha'
      by (cbn in Ha; offsets_compute; solve_addr);
  clear Ha; rename Ha' into Ha;
  try change_pc_to a.
