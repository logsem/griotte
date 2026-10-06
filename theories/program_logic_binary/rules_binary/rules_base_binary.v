From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language ectx_language.
From griotte Require Export spec_instance_binary.
(* Re-imported after [language], which shadows the operational [step]. *)
From griotte Require Import griotte_opsem.

(** * Common definitions for the spec instruction rules

    The generic spec rules [step_X] have the shape
      [spec_ctx ∗ ⤇ Seq (Instr Executable) ∗ P ={E}=∗
       ∃ retv regs', ⤇ Seq (of_val retv) ∗ ⌜X_spec … regs' retv⌝ ∗ Q].
    They are proved by replaying the bodies of the unary [wp_X] rules. To make
    this replay literal, the lemmas below hand to the continuation a
    hypothesis that plays the role of the unary postcondition ["Hφ"]
    ([∀ regs' retv, Ψ retv regs' -∗ Φ retv], for an abstract [Φ]), so that [iApply "Hφ"] and
    [iFailWP "Hφ" …] work unchanged. *)

(** ** Determinism of the instruction specifications

    The generic rules [wp_X] (implementation) and [step_X] (spec) both produce
    an [X_spec] outcome. Each [rules_X_binary.v] proves [X_spec_determ]: two
    outcomes from the same inputs agree on the return value, and on the
    outputs when the instruction succeeds (failure cases leave the output map
    unconstrained). The tactic below proves them all: [F] is the failure
    inductive of the instruction (or the spec inductive when there is none),
    [pre] unfolds instruction-specific definitions. *)
Ltac solve_spec_determ_gen F pre :=
  let H1 := fresh "H1" in let H2 := fresh "H2" in
  intros H1 H2; destruct H1; destruct H2;
  repeat match goal with H : ?T |- _ => lazymatch T with context [F] => destruct H end end;
  pre;
  repeat match goal with H : _ ∨ _ |- _ => destruct H end;
  repeat match goal with H : _ ∧ _ |- _ => destruct H end;
  simplify_eq;
  repeat split; try done; try congruence;
  intros; simplify_eq; try done; try congruence.

Ltac solve_spec_determ F := solve_spec_determ_gen F idtac.

Section rules_base_binary.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.

  (** One existentially quantified output (usually the new register map). *)
  Lemma spec_step_exec_1 {A : Type} E (Ψ : griotte_lang.val → A → iProp Σ) :
    ↑specN ⊆ E →
    spec_ctx -∗
    ⤇ Seq (Instr Executable) -∗
    (∀ Φ, (∀ (x : A) v, Ψ v x -∗ Φ v) -∗
       ∀ σ c σ', ⌜step (Executable, σ) (c, σ')⌝ -∗
       spec_state_interp σ ==∗
       spec_state_interp σ' ∗ from_option Φ False (to_val (Instr c)))
    ={E}=∗
    ∃ v x, ⤇ Seq (of_val v) ∗ Ψ v x.
  Proof.
    iIntros (HE) "#Hctx Hj Hcont".
    iMod (spec_step_exec_gen _ (λ v, ∃ x, Ψ v x)%I with "Hctx Hj [Hcont]")
      as (v) "[Hj [%x HΨ]]"; first done.
    - iApply "Hcont". iIntros (x v) "H". by iExists x.
    - iModIntro. iExists v, x. iFrame.
  Qed.

  (** Two existentially quantified outputs (new registers and memory, or new
      registers and system registers). *)
  Lemma spec_step_exec_2 {A B : Type} E (Ψ : griotte_lang.val → A → B → iProp Σ) :
    ↑specN ⊆ E →
    spec_ctx -∗
    ⤇ Seq (Instr Executable) -∗
    (∀ Φ, (∀ (x : A) (y : B) v, Ψ v x y -∗ Φ v) -∗
       ∀ σ c σ', ⌜step (Executable, σ) (c, σ')⌝ -∗
       spec_state_interp σ ==∗
       spec_state_interp σ' ∗ from_option Φ False (to_val (Instr c)))
    ={E}=∗
    ∃ v x y, ⤇ Seq (of_val v) ∗ Ψ v x y.
  Proof.
    iIntros (HE) "#Hctx Hj Hcont".
    iMod (spec_step_exec_gen _ (λ v, ∃ x y, Ψ v x y)%I with "Hctx Hj [Hcont]")
      as (v) "[Hj (%x & %y & HΨ)]"; first done.
    - iApply "Hcont". iIntros (x y v) "H". by iExists x, y.
    - iModIntro. iExists v, x, y. iFrame.
  Qed.

End rules_base_binary.

(** Spec copies of the memory-map lemmas of [rules_base.v]. The lemmas of
    [rules_base.v] that are generic in the points-to predicate
    ([memMap_resource_2gen_d(_dq)], [memMap_resource_2gen_clater(_dq)]) are
    reused directly. *)
Section spec_memMap.
  Context `{specg : specG Σ}.

  Lemma spec_memMap_resource_0 :
    True ⊣⊢ ([∗ map] a↦w ∈ ∅, a ↣ₐ w).
  Proof. by rewrite big_sepM_empty. Qed.

  Lemma spec_memMap_resource_2ne_apply (a1 a2 : Addr) (w1 w2 : Word) :
    a1 ↣ₐ w1 -∗
    a2 ↣ₐ w2 -∗
    ([∗ map] a↦w ∈ <[a1:=w1]> (<[a2:=w2]> ∅), a ↣ₐ w) ∗ ⌜a1 ≠ a2⌝.
  Proof.
    iIntros "Hi Hr2a".
    iDestruct (spec_address_neq with "Hi Hr2a") as %Hne; auto.
    iSplitL; last by auto.
    iApply spec_memMap_resource_2ne; auto. iSplitL "Hi"; auto.
  Qed.

  Lemma spec_memMap_resource_2gen (a1 a2 : Addr) (w1 w2 : Word) :
    (∃ mem, ([∗ map] a↦w ∈ mem, a ↣ₐ w) ∧
       ⌜if (a2 =? a1)%a
        then mem = (<[a1:=w1]> ∅)
        else mem = <[a1:=w1]> (<[a2:=w2]> ∅)⌝)%I
    ⊣⊢ (a1 ↣ₐ w1 ∗ if (a2 =? a1)%a then emp else a2 ↣ₐ w2).
  Proof.
    destruct (a2 =? a1)%a eqn:Heq.
    - apply Z.eqb_eq, finz_to_z_eq in Heq. rewrite spec_memMap_resource_1.
      iSplit.
      * iDestruct 1 as (mem) "[HH ->]". by iSplit.
      * iDestruct 1 as "[Hmap _]". iExists (<[a1:=w1]> ∅); iSplitL; auto.
    - apply Z.eqb_neq in Heq.
      rewrite -spec_memMap_resource_2ne; auto. 2: congruence.
      iSplit.
      * iDestruct 1 as (mem) "[HH ->]". done.
      * iDestruct 1 as "Hmap". iExists (<[a1:=w1]> (<[a2:=w2]> ∅)); iSplitL; auto.
  Qed.

  Lemma spec_memMap_delete (a : Addr) (w : Word) mem0 :
    mem0 !! a = Some w →
    ([∗ map] a↦w ∈ mem0, a ↣ₐ w) ⊣⊢ (a ↣ₐ w ∗ ([∗ map] k↦y ∈ delete a mem0, k ↣ₐ y)).
  Proof. intros Hmem0a. rewrite -(big_sepM_delete _ _ a); auto. Qed.

  Lemma spec_mem_remove_dq mem dq :
    ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ⊣⊢
    ([∗ map] a↦dw ∈ (prod_merge (create_gmap_default (elements (dom mem)) dq) mem), a ↣ₐ{dw.1} dw.2).
  Proof.
    iInduction (mem) as [|a k mem] "IH" using map_ind.
    - rewrite big_sepM_empty dom_empty_L elements_empty
              /= /prod_merge merge_empty big_sepM_empty. done.
    - rewrite dom_insert_L.
      assert (elements ({[a]} ∪ dom mem) ≡ₚ a :: elements (dom mem)) as Hperm.
      { apply elements_union_singleton. apply not_elem_of_dom. auto. }
      apply (create_gmap_default_permutation _ _ dq) in Hperm. rewrite Hperm /=.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq,k)) //.
      iSplit.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"; auto.
        iApply big_sepM_insert.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom mem)) dq !! a); auto; rewrite H; auto. }
        iFrame. iApply "IH". iFrame.
      + iIntros "Hmem". iDestruct (big_sepM_insert with "Hmem") as "[Ha Hmem]"; auto.
        { rewrite lookup_merge /prod_op /=.
          destruct (create_gmap_default (elements (dom mem)) dq !! a); auto; rewrite H; auto. }
        iApply big_sepM_insert; auto.
        iFrame. iApply "IH". iFrame.
  Qed.

End spec_memMap.

(* TODO: move to rules_base.v. Later-free variant of
   [memMap_resource_2gen_clater_dq], for the spec rules (no laters there). *)
Lemma memMap_resource_2gen_dq {Σ} (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : Word)
  (Φ : Addr → dfrac → Word → iProp Σ) :
  Φ a1 dq1 w1 -∗
  (if (a2 =? a1)%a then emp else Φ a2 dq2 w2) -∗
  (∃ mem dfracs, ([∗ map] a↦wq ∈ prod_merge dfracs mem, Φ a wq.1 wq.2) ∗
     ⌜(if (a2 =? a1)%a
       then mem = (<[a1:=w1]> ∅)
       else mem = <[a1:=w1]> (<[a2:=w2]> ∅)) ∧
      (if (a2 =? a1)%a
       then dfracs = (<[a1:=dq1]> ∅)
       else dfracs = <[a1:=dq1]> (<[a2:=dq2]> ∅))⌝).
Proof.
  iIntros "Hc1 Hc2".
  destruct (a2 =? a1)%a eqn:Heq.
  - iExists (<[a1:= w1]> ∅), (<[a1:= dq1]> ∅); iSplitL; auto.
    rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1)); auto. rewrite merge_empty.
    iApply big_sepM_insert; [|by iFrame]. auto.
  - iExists (<[a1:=w1]> (<[a2:=w2]> ∅)), (<[a1:=dq1]> (<[a2:=dq2]> ∅)); iSplitL; auto.
    rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1)); auto.
    rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,w2)); auto.
    rewrite merge_empty.
    iApply big_sepM_insert; [|iFrame].
    { apply Z.eqb_neq in Heq. rewrite lookup_insert_ne//. congruence. }
    iApply big_sepM_insert; [|by iFrame]. auto.
Qed.
