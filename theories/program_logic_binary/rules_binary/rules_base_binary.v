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
  intros; simplify_eq; try done; try congruence;
  (* Validity-tag cases: equal decoded permissions and contradictory flows. *)
  repeat match goal with
    H1 : (?x, ?y) = ?d, H2 : (?x', ?y') = ?d |- _ =>
      rewrite <- H1 in H2; inversion H2; clear H2; subst
  end;
  repeat match goal with
    H : _ && _ = false |- _ => apply andb_false_iff in H; destruct H
  end;
  simplify_eq; try done; try congruence.

Ltac solve_spec_determ F := solve_spec_determ_gen F idtac.

(** ** Physical register files

    The spec run is a physical machine: its registers hold words without
    identifiers. These are the physical counterparts of the logical
    [read_reg_inr] and [incrementPC] of [rules_base.v]. *)

(* Conditionally unify on the read register value *)
Definition spec_read_reg_inr (regs : Reg) (r : RegName) (t : bool) p g b e a :=
  match regs !! r with
  | Some (WCap t' p' g' b' e' a') => WCap t' p' g' b' e' a' = WCap t p g b e a
  | Some _ => True
  | None => False end.

Definition spec_incrementPC_gen (regs: Reg) (n : Z) : option Reg :=
  match regs !! PC with
  | Some (WCap t p g b e a) =>
    match (a + n)%a with
    | Some a' => Some (<[ PC := WCap t p g b e a' ]> regs)
    | None => None
    end
  | _ => None
  end.

Definition spec_incrementPC (regs: Reg) : option Reg := spec_incrementPC_gen regs 1.

Lemma spec_incrementPC_gen_Some_inv regs regs' n :
  spec_incrementPC_gen regs n = Some regs' ->
  exists t p g b e a a',
    regs !! PC = Some (WCap t p g b e a) ∧
    (a + n)%a = Some a' ∧
    regs' = <[ PC := WCap t p g b e a' ]> regs.
Proof.
  unfold spec_incrementPC_gen.
  destruct (regs !! PC) ; try congruence.
  destruct_word w;try congruence.
  case_eq (a+n)%a; try congruence. intros ? ?. inversion 1.
  do 7 eexists. split; eauto.
Qed.
Lemma spec_incrementPC_Some_inv regs regs' :
  spec_incrementPC regs = Some regs' ->
  exists t p g b e a a',
    regs !! PC = Some (WCap t p g b e a) ∧
    (a + 1)%a = Some a' ∧
    regs' = <[ PC := WCap t p g  b e a' ]> regs.
Proof. apply spec_incrementPC_gen_Some_inv. Qed.

Lemma spec_incrementPC_gen_None_inv regs (t : bool) p g b e a n :
  spec_incrementPC_gen regs n = None ->
  regs !! PC = Some (WCap t p g b e a) ->
  (a + n)%a = None.
Proof.
  unfold spec_incrementPC_gen.
  destruct (regs !! PC) ; try congruence.
  destruct_word w;try congruence.
  case_eq (a0+n)%a; try congruence.
Qed.
Lemma spec_incrementPC_None_inv regs (t : bool) p g b e a :
  spec_incrementPC regs = None ->
  regs !! PC = Some (WCap t p g b e a) ->
  (a + 1)%a = None.
Proof. apply spec_incrementPC_gen_None_inv. Qed.

Lemma spec_incrementPC_gen_overflow_mono regs regs' n :
  spec_incrementPC_gen regs n = None →
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  spec_incrementPC_gen regs' n = None.
Proof.
  intros Hi HPC Hincl. unfold spec_incrementPC_gen in *. destruct HPC as [c HPC].
  pose proof (lookup_weaken _ _ _ _ HPC Hincl) as HPC'.
  rewrite HPC HPC' in Hi |- *. destruct c as [| [? ? ? ? ? aa | ] | | ]; auto.
  destruct (aa+n)%a; last by auto. congruence.
Qed.
Lemma spec_incrementPC_overflow_mono regs regs' :
  spec_incrementPC regs = None →
  is_Some (regs !! PC) →
  regs ⊆ regs' →
  spec_incrementPC regs' = None.
Proof. apply spec_incrementPC_gen_overflow_mono. Qed.

Lemma spec_incrementPC_gen_fail_updatePC_gen regs sregs m shadow n :
   spec_incrementPC_gen regs n = None ->
   updatePC_gen (regs, sregs, m, shadow) n = None.
Proof.
   rewrite /spec_incrementPC_gen /updatePC_gen /=; cbn.
   destruct (regs !! PC) as [X|]; auto.
   destruct X as [| [? ? ? ? ? a' | ] | |]; auto.
   destruct (a' + n)%a; auto. congruence.
Qed.
Lemma spec_incrementPC_fail_updatePC regs sregs m shadow :
   spec_incrementPC regs = None ->
   updatePC (regs, sregs, m, shadow) = None.
Proof. apply spec_incrementPC_gen_fail_updatePC_gen. Qed.

Lemma spec_incrementPC_gen_success_updatePC_gen regs sregs m shadow regs' n :
  spec_incrementPC_gen regs n = Some regs' ->
  ∃ t p g b e a a',
    regs !! PC = Some (WCap t p g b e a) ∧
    (a + n)%a = Some a' ∧
    updatePC_gen (regs, sregs, m, shadow) n =
      Some (NextI, (<[ PC := WCap t p g b e a' ]> regs, sregs, m, shadow)) ∧
    regs' = <[ PC := WCap t p g b e a' ]> regs.
Proof.
  rewrite /spec_incrementPC_gen /updatePC_gen /update_reg /=; cbn.
  destruct (regs !! PC) as [X|] eqn:?; auto; try congruence; [].
  destruct X as [| [? ? ? ? ? a'|]| |] eqn:?; try congruence; [].
  destruct (a' + n)%a eqn:?; [| congruence]. inversion 1; subst regs'.
  do 7 eexists. repeat split; auto.
Qed.
Lemma spec_incrementPC_success_updatePC regs sregs m shadow regs' :
  spec_incrementPC regs = Some regs' ->
  ∃ t p g b e a a',
    regs !! PC = Some (WCap t p g b e a) ∧
    (a + 1)%a = Some a' ∧
    updatePC (regs, sregs, m, shadow) =
      Some (NextI, (<[ PC := WCap t p g b e a' ]> regs, sregs, m, shadow)) ∧
    regs' = <[ PC := WCap t p g b e a' ]> regs.
Proof. apply spec_incrementPC_gen_success_updatePC_gen. Qed.

Ltac spec_incrementPC_inv :=
  match goal with
  | H : spec_incrementPC _ = Some _ |- _ =>
    apply spec_incrementPC_Some_inv in H as (?&?&?&?&?&?&?&?&?&?)
  | H : spec_incrementPC _ = None |- _ =>
    eapply spec_incrementPC_None_inv in H
  end; simplify_eq.

Tactic Notation "spec_incrementPC_inv" "as" simple_intropattern(pat):=
  match goal with
  | H : spec_incrementPC _ = Some _ |- _ =>
    apply spec_incrementPC_Some_inv in H as pat
  | H : spec_incrementPC _ = None |- _ =>
    eapply spec_incrementPC_None_inv in H
  | H : spec_incrementPC_gen _ _ = Some _ |- _ =>
    apply spec_incrementPC_gen_Some_inv in H as pat
  | H : spec_incrementPC_gen _ _ = None |- _ =>
    eapply spec_incrementPC_gen_None_inv in H
  end; simplify_eq.

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


  (** ** Runtime failure of an instruction

      Spec counterparts of [wp_instr_failed_N] ([rules_base.v]): a failed
      instruction leaves the state unchanged. *)
  Lemma step_instr_failed_map E pc_p pc_g pc_b pc_e pc_a w i (regs : Reg) :
    ↑specN ⊆ E →
    decodeInstrW w = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, regs ⊆ r →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y).
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hfailed) "(#Hctx & Hj & Hpc_a & Hmap)".
    iMod (spec_step_exec _
            (λ v, ⌜v = FailedV⌝ ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y))%I
           with "Hctx Hj Hmap Hpc_a [] ")
      as (v) "(Hj & -> & Hpc_a & Hmap)"; [done..| |by iFrame].
    iIntros ([[[r sr] m] st] c σ' Hincl _ Hexec) "Hσ Hmap Hpc_a".
    rewrite Hinstr (Hfailed r sr m st Hincl) in Hexec. simplify_eq.
    by iFrame.
  Qed.

  Lemma step_instr_failed_0 E pc_p pc_g pc_b pc_e pc_a w i :
    ↑specN ⊆ E →
    decodeInstrW w = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w.
  Proof.
    iIntros (HE Hinstr Hvpc Hfailed) "(#Hctx & Hj & HPC & Hmem)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iMod (step_instr_failed_map with "[$Hctx $Hj $Hmap $Hmem]") as "($ & $ & Hmap)".
    1-3: done.
    - by simplify_map_eq.
    - intros r sr m st Hincl. apply Hfailed.
      all: eapply lookup_weaken; last exact Hincl.
      all: by simplify_map_eq.
    - by iDestruct (spec_regs_of_map_1 with "Hmap") as "$".
  Qed.

  Lemma step_instr_failed_1 E pc_p pc_g pc_b pc_e pc_a w i r1 w1 :
    ↑specN ⊆ E →
    decodeInstrW w = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
       r !! r1 = Some w1 →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    r1 ↣ᵣ w1 ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    r1 ↣ᵣ w1 ∗
    pc_a ↣ₐ w.
  Proof.
    iIntros (HE Hinstr Hvpc Hfailed) "(#Hctx & Hj & HPC & Hr1 & Hmem)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iMod (step_instr_failed_map with "[$Hctx $Hj $Hmap $Hmem]") as "($ & $ & Hmap)".
    1-3: done.
    - by simplify_map_eq.
    - intros r sr m st Hincl. apply Hfailed.
      all: eapply lookup_weaken; last exact Hincl.
      all: by simplify_map_eq.
    - by iDestruct (spec_regs_of_map_2 with "Hmap") as "[$ $]".
  Qed.

  Lemma step_instr_failed_2 E pc_p pc_g pc_b pc_e pc_a w i r1 w1 r2 w2 :
    ↑specN ⊆ E →
    decodeInstrW w = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
       r !! r1 = Some w1 →
       r !! r2 = Some w2 →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    r1 ↣ᵣ w1 ∗
    r2 ↣ᵣ w2 ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    r1 ↣ᵣ w1 ∗
    r2 ↣ᵣ w2 ∗
    pc_a ↣ₐ w.
  Proof.
    iIntros (HE Hinstr Hvpc Hfailed) "(#Hctx & Hj & HPC & Hr1 & Hr2 & Hmem)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (Hne0 & Hne1 & Hne2).
    iMod (step_instr_failed_map with "[$Hctx $Hj $Hmap $Hmem]") as "($ & $ & Hmap)".
    1-3: done.
    - by simplify_map_eq.
    - intros r sr m st Hincl. apply Hfailed.
      all: eapply lookup_weaken; last exact Hincl.
      all: by simplify_map_eq.
    - by iDestruct (spec_regs_of_map_3 with "Hmap") as "($ & $ & $)".
  Qed.

  Lemma step_instr_failed_3 E pc_p pc_g pc_b pc_e pc_a w i r1 w1 r2 w2 r3 w3 :
    ↑specN ⊆ E →
    decodeInstrW w = i →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st, r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
       r !! r1 = Some w1 →
       r !! r2 = Some w2 →
       r !! r3 = Some w3 →
       exec i pc_p (r, sr, m, st) = (Failed, (r, sr, m, st))) →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    r1 ↣ᵣ w1 ∗
    r2 ↣ᵣ w2 ∗
    r3 ↣ᵣ w3 ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    r1 ↣ᵣ w1 ∗
    r2 ↣ᵣ w2 ∗
    r3 ↣ᵣ w3 ∗
    pc_a ↣ₐ w.
  Proof.
    iIntros (HE Hinstr Hvpc Hfailed) "(#Hctx & Hj & HPC & Hr1 & Hr2 & Hr3 & Hmem)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (Hne0 & Hne1 & Hne2 & Hne3 & Hne4 & Hne5).
    iMod (step_instr_failed_map with "[$Hctx $Hj $Hmap $Hmem]") as "($ & $ & Hmap)".
    1-3: done.
    - by simplify_map_eq.
    - intros r sr m st Hincl. apply Hfailed.
      all: eapply lookup_weaken; last exact Hincl.
      all: by simplify_map_eq.
    - by iDestruct (spec_regs_of_map_4 with "Hmap") as "($ & $ & $ & $)".
  Qed.

End rules_base_binary.

(** Spec copies of the memory-map lemmas of [rules_base.v], over physical
    words. *)
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

  Lemma spec_memMap_resource_2gen_d_dq (Φ : Addr → dfrac → Word → iProp Σ)
    (a1 a2 : Addr) (dq1 dq2 : dfrac) (w1 w2 : Word) :
    (∃ mem dfracs, ([∗ map] a↦wq ∈ prod_merge dfracs mem, Φ a wq.1 wq.2) ∧
       ⌜(if (a2 =? a1)%a
         then mem = (<[a1:=w1]> ∅)
         else mem = <[a1:=w1]> (<[a2:=w2]> ∅)) ∧
        (if (a2 =? a1)%a
         then dfracs = (<[a1:=dq1]> ∅)
         else dfracs = <[a1:=dq1]> (<[a2:=dq2]> ∅))⌝) -∗
    (Φ a1 dq1 w1 ∗ if (a2 =? a1)%a then emp else Φ a2 dq2 w2).
  Proof.
    iIntros "Hmem". iDestruct "Hmem" as (mem dfracs) "[Hmem [Hif Hif'] ]".
    destruct ((a2 =? a1)%a) eqn:Heq.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1)); auto. rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
    - iDestruct "Hif" as %->. iDestruct "Hif'" as %->.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq1,w1)); auto.
      rewrite /prod_merge -(insert_merge _ _ _ _ (dq2,w2)); auto.
      rewrite merge_empty.
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]".
      { rewrite lookup_insert_ne; auto. apply Z.eqb_neq in Heq. solve_addr. }
      iDestruct (big_sepM_insert with "Hmem") as "[$ Hmem]". auto.
  Qed.

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

(** ** Physical register files as logical ones

    The binary model relates physical words. The implementation run is
    reasoned about with the unary rules, over logical register files: the
    physical ones, without identifiers. The lemmas below relate the logical
    operations on such register files with their physical counterparts. *)
Notation lift_regs regs := (lword_of_word <$> (regs : Reg) : LReg).

Section lift_regs.
  Context `{MP: MachineParameters}.
  Implicit Types regs : Reg.

  Lemma lift_regs_lookup regs r :
    lift_regs regs !! r = lword_of_word <$> regs !! r.
  Proof. by rewrite lookup_fmap. Qed.

  Lemma lift_regs_llookup regs r :
    lift_regs regs !!ₗ r = lword_of_word <$> regs !!ᵣ r.
  Proof.
    rewrite /llookup_reg /lookup_reg lookup_fmap.
    destruct (regs !! r) eqn:Hr; rewrite ?Hr /=; [by destruct (decide (r = cnull))|done].
  Qed.

  Lemma lift_regs_lw_llookup regs r :
    lw <$> (lift_regs regs !!ₗ r) = regs !!ᵣ r.
  Proof.
    rewrite lift_regs_llookup -option_fmap_compose.
    by destruct (regs !!ᵣ r).
  Qed.

  Lemma lift_regs_insert regs r (w : Word) :
    <[r := lword_of_word w]> (lift_regs regs) = lift_regs (<[r := w]> regs).
  Proof. by rewrite fmap_insert. Qed.

  Lemma lift_regs_linsert regs r (w : Word) :
    <[r := lword_of_word w]ₗ> (lift_regs regs) = lift_regs (<[r := w]ᵣ> regs).
  Proof. rewrite /linsert_reg /insert_reg fmap_insert. by destruct (decide (r = cnull)). Qed.

  Lemma lift_regs_inj regs1 regs2 :
    lift_regs regs1 = lift_regs regs2 → regs1 = regs2.
  Proof. intros H. apply (map_fmap_inj lword_of_word); [intros ?? [=]; done|exact H]. Qed.

  Lemma lregs_erase_lift regs : lregs_erase (lift_regs regs) = regs.
  Proof.
    rewrite /lregs_erase -map_fmap_compose. by apply map_fmap_id.
  Qed.

  Lemma lift_regs_incrementPC_gen regs n :
    incrementPC_gen (lift_regs regs) n = (λ r, lift_regs r) <$> spec_incrementPC_gen regs n.
  Proof.
    rewrite /incrementPC_gen /spec_incrementPC_gen lookup_fmap.
    destruct (regs !! PC) as [w|] eqn:HPC; rewrite ?HPC /=; last done.
    destruct_word w; cbn; try done.
    destruct (a + n)%a; cbn; last done.
    by rewrite fmap_insert.
  Qed.

  Lemma lift_regs_incrementPC regs :
    incrementPC (lift_regs regs) = (λ r, lift_regs r) <$> spec_incrementPC regs.
  Proof. apply lift_regs_incrementPC_gen. Qed.

  Lemma lift_regs_incrementPC_Some regs lregs' :
    incrementPC (lift_regs regs) = Some lregs' →
    ∃ regs', lregs' = lift_regs regs' ∧ spec_incrementPC regs = Some regs'.
  Proof.
    rewrite lift_regs_incrementPC.
    destruct (spec_incrementPC regs) as [regs'|]; cbn; intros Heq; simplify_eq; eauto.
  Qed.

  Lemma lift_regs_incrementPC_None regs :
    incrementPC (lift_regs regs) = None → spec_incrementPC regs = None.
  Proof. rewrite lift_regs_incrementPC. by destruct (spec_incrementPC regs). Qed.

  Lemma lift_regs_lword_of_argument regs src :
    lword_of_argument (lift_regs regs) src = lword_of_word <$> word_of_argument regs src.
  Proof. destruct src; cbn; [done|apply lift_regs_llookup]. Qed.

  Lemma lift_regs_lz_of_argument regs src :
    lz_of_argument (lift_regs regs) src = z_of_argument regs src.
  Proof.
    destruct src as [z|r]; cbn; first done.
    rewrite lift_regs_llookup. by destruct (regs !!ᵣ r) as [[]|] eqn:Hr; rewrite ?Hr.
  Qed.

  Lemma lift_regs_laddr_of_argument regs src :
    laddr_of_argument (lift_regs regs) src = addr_of_argument regs src.
  Proof. by rewrite /laddr_of_argument /addr_of_argument lift_regs_lz_of_argument. Qed.

  Lemma lift_regs_lotype_of_argument regs src :
    lotype_of_argument (lift_regs regs) src = otype_of_argument regs src.
  Proof. by rewrite /lotype_of_argument /otype_of_argument lift_regs_lz_of_argument. Qed.

End lift_regs.

Lemma lupdatePcPerm_lword_of_word (w : Word) :
  lupdatePcPerm (lword_of_word w) = lword_of_word (updatePcPerm w).
Proof. done. Qed.

Lemma lseal_capability_lword_of_word (w : Word) o :
  lseal_capability (lword_of_word w) o = lword_of_word (seal_capability w o).
Proof. done. Qed.

(** Rewrites the logical register-file operations of lifted physical
    register files, in the hypotheses, into physical ones. *)
Ltac lift_regs_simpl :=
  repeat match goal with
  | H : context [lword_of_argument (lword_of_word <$> _) _] |- _ =>
      rewrite lift_regs_lword_of_argument in H
  | H : context [lz_of_argument (lword_of_word <$> _) _] |- _ =>
      rewrite lift_regs_lz_of_argument in H
  | H : context [laddr_of_argument (lword_of_word <$> _) _] |- _ =>
      rewrite lift_regs_laddr_of_argument in H
  | H : context [lotype_of_argument (lword_of_word <$> _) _] |- _ =>
      rewrite lift_regs_lotype_of_argument in H
  | H : context [lw <$> ((lword_of_word <$> _) !!ₗ _)] |- _ =>
      rewrite lift_regs_lw_llookup in H
  | H : context [(lword_of_word <$> _) !!ₗ _] |- _ =>
      rewrite lift_regs_llookup in H
  | H : context [(lword_of_word <$> _) !! _] |- _ =>
      rewrite lookup_fmap in H
  | H : lword_of_word <$> _ = Some _ |- _ =>
      let x := fresh "w" in
      let Hx := fresh "Hx" in
      apply fmap_Some in H as (x & H & Hx); simplify_eq
  | H : MkLWord _ _ = lword_of_word _ |- _ => unfold lword_of_word in H; simplify_eq
  | H : lword_of_word _ = MkLWord _ _ |- _ => unfold lword_of_word in H; simplify_eq
  | H : context [lw (lword_of_word _)] |- _ => cbn [lw lword_of_word] in H
  | H : context [lw (MkLWord _ _)] |- _ => cbn [lw] in H
  | H : context [lupdatePcPerm (lword_of_word _)] |- _ =>
      rewrite lupdatePcPerm_lword_of_word in H
  | |- context [lupdatePcPerm (lword_of_word _)] =>
      rewrite lupdatePcPerm_lword_of_word
  | H : context [lseal_capability (lword_of_word _) _] |- _ =>
      rewrite lseal_capability_lword_of_word in H
  | |- context [<[ _ := _ ]ₗ> (lword_of_word <$> _)] =>
      rewrite lift_regs_linsert
  | H : context [<[ ?r := MkLWord ?x None ]ₗ> (lword_of_word <$> ?R)] |- _ =>
      rewrite (lift_regs_linsert R r x) in H
  | H : context [<[ ?r := MkLWord ?x None ]> (lword_of_word <$> ?R)] |- _ =>
      rewrite (lift_regs_insert R r x) in H
  | H : incrementPC_gen (lword_of_word <$> _) _ = Some _ |- _ =>
      let r := fresh "regs'" in
      rewrite lift_regs_incrementPC_gen in H;
      apply fmap_Some in H as (r & H & ?); subst
  | H : incrementPC_gen (lword_of_word <$> _) _ = None |- _ =>
      rewrite lift_regs_incrementPC_gen in H; apply fmap_None in H
  | H : context [lclear_tag (lword_of_word _)] |- _ =>
      rewrite lclear_tag_lword_of_word in H
  | H : context [lload_word _ (lword_of_word _)] |- _ =>
      rewrite lload_word_lword_of_word in H
  | H : context [lstore_word _ (lword_of_word _)] |- _ =>
      rewrite lstore_word_lword_of_word in H
  | H : context [<[ _ := lword_of_word _ ]ₗ> (lword_of_word <$> _)] |- _ =>
      rewrite lift_regs_linsert in H
  | H : context [<[ _ := lword_of_word _ ]> (lword_of_word <$> _)] |- _ =>
      rewrite lift_regs_insert in H
  | H : incrementPC (lword_of_word <$> _) = Some _ |- _ =>
      let r := fresh "regs'" in
      apply lift_regs_incrementPC_Some in H as (r & ? & H); subst
  | H : incrementPC (lword_of_word <$> _) = None |- _ =>
      apply lift_regs_incrementPC_None in H
  end.

(** Builds a physical outcome from its premises, trying the constructors in
    order, and the constructors of a failure inductive under the failure
    constructor. *)
Ltac spec_try_constructors :=
  first [ solve [econstructor 1; eauto] | solve [econstructor 2; eauto]
        | solve [econstructor 3; eauto] | solve [econstructor 4; eauto]
        | solve [econstructor 5; eauto] | solve [econstructor 6; eauto]
        | solve [econstructor 7; eauto] | solve [econstructor 8; eauto]
        | solve [econstructor 9; eauto] | solve [econstructor 10; eauto] ].

Ltac spec_build :=
  first [ spec_try_constructors
        | solve [econstructor 1; spec_try_constructors] | solve [econstructor 2; spec_try_constructors]
        | solve [econstructor 3; spec_try_constructors] | solve [econstructor 4; spec_try_constructors]
        | solve [econstructor 5; spec_try_constructors] | solve [econstructor 6; spec_try_constructors]
        | solve [econstructor 7; spec_try_constructors] | solve [econstructor 8; spec_try_constructors] ].

(** Concludes a lifting lemma [X_spec_lift], after [lift_regs_simpl]. *)
Ltac spec_lift_finish regs :=
  first [ eexists; split; [intros _; reflexivity|]; spec_build
        | exists regs; split; [intros ?; discriminate|]; spec_build ].

(** Proves a lifting lemma [X_spec_lift]: [F] is the failure inductive of the
    instruction (or the spec inductive when there is none). *)
Ltac spec_lift F regs :=
  let Hs := fresh "Hspec" in
  intros Hs; destruct Hs;
  repeat match goal with H : ?T |- _ => lazymatch T with context [F] => destruct H end end;
  lift_regs_simpl; try subst; spec_lift_finish regs.
