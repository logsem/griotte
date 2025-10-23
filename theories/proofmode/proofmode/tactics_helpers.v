From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From Stdlib Require Import Eqdep_dec List.
From cap_machine Require Import cap_lang memory_region contiguous.

Section helpers.

  (* ---------------------------- Helper Lemmas --------------------------------------- *)
  Definition isCorrectPC_range p g b e a0 an :=
    ∀ ai, (a0 <= ai)%a ∧ (ai < an)%a → isCorrectPC (WCap p g b e ai).

  Lemma isCorrectPC_inrange p g b (e a0 an a: Addr) :
    isCorrectPC_range p g b e a0 an →
    (a0 <= a < an)%Z →
    isCorrectPC (WCap p g b e a).
  Proof.
    unfold isCorrectPC_range. move=> /(_ a) HH ?. apply HH. eauto.
  Qed.

  Lemma isCorrectPC_contiguous_range p g b e a0 an a l :
    isCorrectPC_range p g b e a0 an →
    contiguous_between l a0 an →
    a ∈ l →
    isCorrectPC (WCap p g b e a).
  Proof.
    intros Hr Hc Hin.
    eapply isCorrectPC_inrange; eauto.
    eapply contiguous_between_middle_bounds'; eauto.
  Qed.

  Lemma isCorrectPC_range_perm p g b e a0 an :
    isCorrectPC_range p g b e a0 an →
    (a0 < an)%a →
    executeAllowed p = true.
  Proof.
    intros Hr H0n.
    assert (isCorrectPC (WCap p g b e a0)) as HH by (apply Hr; solve_addr).
    inversion HH; auto.
  Qed.

  Lemma isCorrectPC_range_restrict p g b e a0 an a0' an' :
    isCorrectPC_range p g b e a0 an →
    (a0 <= a0')%a ∧ (an' <= an)%a →
    isCorrectPC_range p g b e a0' an'.
  Proof.
    intros HR [? ?] a' [? ?]. apply HR. solve_addr.
  Qed.


End helpers.

(* Ltacs *)

(* Tactic for destructing a list into elements *)
Ltac destruct_list l :=
  match goal with
  | H : length l = _ |- _ =>
    let a := fresh "a" in
    let l' := fresh "l" in
    destruct l as [|a l']; [inversion H|];
    repeat (let a' := fresh "a" in
            destruct l' as [|a' l'];[by inversion H|]);
    destruct l'; [|by inversion H]
  end.

Ltac iPrologue_pre :=
  match goal with
  | Hlen : length ?a = ?n |- _ =>
    let a' := fresh "a" in
    destruct a as [| a' a]; inversion Hlen; simpl
  end.

Ltac iPrologue prog :=
  (try iPrologue_pre);
  iDestruct prog as "[Hi Hprog]";
  iApply (wp_bind (fill [SeqCtx])).

Ltac iEpilogue prog :=
  iNext; iIntros prog; iSimpl;
  iApply wp_pure_step_later;auto;iNext;iIntros "_".

Ltac iCombinePtrn :=
  iCombine "Hi" "Hprog_done" as "Hprog_done";
  iCombine "Hsi" "Hsprog_done" as "Hsprog_done".

(* Inline version *)
Ltac iCorrectPC i j :=
  eapply isCorrectPC_contiguous_range with (a0 := i) (an := j); eauto; [];
  cbn; solve [ repeat constructor ].

Ltac iContiguous_next Ha index :=
  generalize (contiguous_between_spec _ _ _ Ha index); auto.

Ltac disjoint_from_rmap rmap :=
  match goal with
  | Hsub : _ ⊆ dom rmap |- _ !! ?r = _ =>
    assert (is_Some (rmap !! r)) as [x Hx];[apply elem_of_dom;apply Hsub;constructor|];
    apply map_disjoint_Some_l with rmap x;auto;apply map_disjoint_union_r_2;auto
  end.

Ltac iContiguous_le Ha index :=
  eapply contiguous_between_middle_bounds with (i:=index) in Ha;eauto;clear -Ha;solve_addr.

Ltac consider_next_reg r1 r2 :=
  destruct (decide (r1 = r2));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
