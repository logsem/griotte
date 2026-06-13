From iris.prelude Require Import prelude.
From iris.program_logic Require Import language ectx_language ectxi_language.
From griotte Require Export griotte_opsem griotte_opsem_prop machine_instructions.
Set Warnings "-redundant-canonical-projection".

Section griotte_lang.
  Context `{MachineParameters}.
  Inductive val: Type :=
  | HaltedV: val
  | FailedV: val
  | NextIV: val.

  Inductive expr: Type :=
  | Instr (c : ConfFlag)
  | Seq (e : expr).
  Definition state : Type := ExecConf.

  Definition of_val (v: val): expr :=
    match v with
    | HaltedV => Instr Halted
    | FailedV => Instr Failed
    | NextIV => Instr NextI
    end.

  Definition to_val (e: expr): option val :=
    match e with
    | Instr c =>
      match c with
      | Executable => None
      | Halted => Some HaltedV
      | Failed => Some FailedV
      | NextI => Some NextIV
      end
    | Seq _ => None
    end.

  Lemma of_to_val:
    forall e v, to_val e = Some v →
           of_val v = e.
  Proof.
    intros * HH. destruct e; try destruct c; simpl in HH; inv HH; auto.
  Qed.

  Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
  Proof. destruct v; reflexivity. Qed.

  (** Evaluation context *)
  Inductive ectx_item :=
  | SeqCtx.

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | SeqCtx => Seq e
    end.

  Inductive prim_step: expr → state → list Empty_set → expr → state → list expr → Prop :=
  | PS_no_fork_instr σ e' σ' :
      step (Executable, σ) (e', σ') → prim_step (Instr Executable) σ [] (Instr e') σ' []
  | PS_no_fork_seq σ : prim_step (Seq (Instr NextI)) σ [] (Seq (Instr Executable)) σ []
  | PS_no_fork_halt σ : prim_step (Seq (Instr Halted)) σ [] (Instr Halted) σ []
  | PS_no_fork_fail σ : prim_step (Seq (Instr Failed)) σ [] (Instr Failed) σ [].

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs →
      to_val e = None.
  Proof. intros * HH. by inversion HH. Qed.

  Lemma prim_step_exec_inv σ1 l1 e2 σ2 efs :
    prim_step (Instr Executable) σ1 l1 e2 σ2 efs →
    l1 = [] ∧ efs = [] ∧
    exists (c: ConfFlag),
      e2 = Instr c ∧
      step (Executable, σ1) (c, σ2).
  Proof. inversion 1; subst; split; eauto. Qed.

  Lemma prim_step_and_step_exec σ1 e2 σ2 l1 e2' σ2' efs :
    step (Executable, σ1) (e2, σ2) →
    prim_step (Instr Executable) σ1 l1 e2' σ2' efs →
    l1 = [] ∧ e2' = (Instr e2) ∧ σ2' = σ2 ∧ efs = [].
  Proof.
    intros* Hstep Hpstep. inversion Hpstep as [? ? ? Hstep' | | |]; subst.
    generalize (step_deterministic _ _ _ _ _ _ Hstep Hstep'). intros [-> ->].
    auto.
  Qed.

  Lemma griotte_lang_determ e1 σ1 κ κ' e2 e2' σ2 σ2' efs efs' :
    prim_step e1 σ1 κ e2 σ2 efs →
    prim_step e1 σ1 κ' e2' σ2' efs' →
    κ = κ' ∧ e2 = e2' ∧ σ2 = σ2' ∧ efs = efs'.
  Proof.
    intros Hs1 Hs2. inv Hs1; inv Hs2.
    all: repeat match goal with HH : step _ _ |- _ => inv HH end; try congruence.
    all: auto.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma base_ctx_step_val Ki e σ1 κ e2 σ2 ef :
    prim_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | HH : to_val (of_val _) = None |- _ => by rewrite to_of_val in HH
           end; auto.
  Qed.

  Lemma griotte_lang_mixin : EctxiLanguageMixin of_val to_val fill_item prim_step.
  Proof.
    constructor;
    apply _ || eauto using to_of_val, of_to_val, val_stuck,
           fill_item_val, fill_item_no_val_inj, base_ctx_step_val.
  Qed.

  Definition is_atomic (e : expr) : Prop :=
    match e with
    | Instr _ => True
    | _ => False
    end.


End griotte_lang.

Canonical Structure cap_ectxi_lang `{MachineParameters} := EctxiLanguage griotte_lang_mixin.
Canonical Structure cap_ectx_lang `{MachineParameters} := EctxLanguageOfEctxi cap_ectxi_lang.
Canonical Structure griotte_lang `{MachineParameters} := LanguageOfEctx cap_ectx_lang.

#[export] Hint Extern 20 (PureExec _ _ _) => progress simpl : typeclass_instances.

#[export] Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
#[export] Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

#[export] Hint Extern 5 (AsVal _) => eexists; eapply of_to_val; fast_done : typeclass_instances.
#[export] Hint Extern 10 (AsVal _) =>
eexists; rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

Local Hint Resolve language.val_irreducible : core.
Local Hint Resolve to_of_val : core.
Local Hint Unfold language.irreducible : core.

Global Instance dec_pc c : Decision (isCorrectPC c).
Proof. apply isCorrectPC_dec. Qed.

(* There is probably a more general instance to be stated there...*)
Instance Reflexive_ofe_equiv_Word : (Reflexive (ofe_equiv (leibnizO Word))).
Proof. intro; reflexivity. Qed.

(****)

Global Instance is_atomic_correct `{MachineParameters} s (e : expr) : is_atomic e → Atomic s e.
Proof.
  intros Ha; apply strongly_atomic_atomic, ectx_language_atomic.
  - destruct e.
    + destruct c; rewrite /Atomic; intros ????? Hstep;
        inversion Hstep.
      match goal with HH : step _ _ |- _ => inversion HH end; eauto.
      destruct (instr_atomic i p σ) as [σstepped [Hst | [Hst | Hst]]];
          simplify_eq; rewrite Hst; simpl; eauto.
    + inversion Ha.
  - intros K e' -> Hval%eq_None_not_Some.
    induction K using rev_ind; first done.
    simpl in Ha; rewrite fill_app in Ha; simpl in Ha.
    destruct Hval. apply (fill_val K e'); simpl in *.
    destruct x; naive_solver.
Qed.

Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

#[export] Hint Extern 0 (Atomic _ _) => solve_atomic : core.
#[export] Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.

Lemma base_reducible_from_step `{MachineParameters} σ1 e2 σ2 :
  step (Executable, σ1) (e2, σ2) →
  base_reducible (Instr Executable) σ1.
Proof. intros * HH. rewrite /base_reducible /base_step //=.
       eexists [], (Instr _), σ2, []. by constructor.
Qed.

Lemma normal_always_base_reducible `{MachineParameters} σ :
  base_reducible (Instr Executable) σ.
Proof.
  generalize (normal_always_step σ); intros (?&?&?).
  eapply base_reducible_from_step. eauto.
Qed.
