From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode machine_parameters switcher.
From griotte Require Import adequacy_helpers_binary compartment_layout.

(** * Contextual equivalence

    The end-to-end theorems of the binary case studies are contextual
    equivalences: for every context [C], the linked programs [C⟦P1⟧] and
    [C⟦P2⟧] either both halt, or both do not halt.

    - A program [P] is the trusted part of the system (e.g., the main
      compartment holding a secret). The switcher is the runtime, shared by
      every program.
    - A context [C] is the set of adversary compartments: arbitrary
      instructions as code, integers or capabilities into their own data
      region as data. They are linked with the program through their import
      table (the switcher's entry point and the entry points exported by the
      program) and their export table (the entry points imported by the
      program).
    - Linking [C ⟦ P ⟧ ↝ σ] states that [σ] is the initial configuration of
      the machine running [P] together with [C]: the compartments are
      disjoint, the imports of [P] are the entry points exported by [C], and
      the memory is the union of the switcher, [P] and [C]. *)

(** ** Halting equivalence *)

Notation "σ ⇓" := (halts σ) (at level 10, format "σ ⇓").

(** Two full programs are halting-equivalent when either both halt,
    or both do not halt. *)
Definition halt_equiv `{MP: MachineParameters} (σ1 σ2 : ExecConf) : Prop :=
  σ1 ⇓ ↔ σ2 ⇓.
Notation "σ1 ≃⇓ σ2" := (halt_equiv σ1 σ2) (at level 70).

Lemma halt_equiv_intro `{MP: MachineParameters} (σ1 σ2 : ExecConf) :
  (σ1 ⇓ → σ2 ⇓) →
  (σ2 ⇓ → σ1 ⇓) →
  σ1 ≃⇓ σ2.
Proof. apply halts_equiv. Qed.

(** ** Contexts *)

Section Contexts.
  Context `{MP: MachineParameters}.

  (** An adversary compartment: its code contains only integers (i.e.,
      arbitrary instructions), its data contains only integers or
      capabilities into its own data region, its import table is [imports],
      and its export table contains one entry point per element of
      [arities], with the given number of arguments, at any offset. *)
  Definition is_adv_cmpt (imports : list Word) (arities : list nat) (C : cmpt) : Prop :=
    cmpt_imports C = imports ∧
    Forall is_z (cmpt_code C) ∧
    Forall (is_initial_data_word C) (cmpt_data C) ∧
    Forall2 (λ (n : nat) w, ∃ (off : nat), w = WInt (encode_entry_point n off))
      arities (cmpt_exp_tbl_entries C).

End Contexts.

(** ** Contextual equivalence *)

(** A linking of contexts of type [Ctx] with programs of type [Prog].
    [is_context C] describes the valid contexts. [link C P σ] states that [σ]
    is the initial configuration of the program [P] linked with [C]. *)
Class Linking `{MP: MachineParameters} (Ctx Prog : Type) := {
  is_context : Ctx → Prop;
  link : Ctx → Prog → ExecConf → Prop;
}.
Global Arguments is_context {_ _ _ _} _.
Global Arguments link {_ _ _ _} _ _ _.

Notation "C ⟦ P ⟧ ↝ σ" := (link C P σ) (at level 70, P at level 200).

(** The programs [P1] and [P2] are contextually equivalent when, for every
    context [C], the linked programs [C⟦P1⟧] and [C⟦P2⟧] are
    halting-equivalent. *)
Definition ctx_equiv `{MP: MachineParameters} {Ctx Prog} `{!Linking Ctx Prog}
  (P1 P2 : Prog) : Prop :=
  ∀ (C : Ctx) (σ1 σ2 : ExecConf),
    is_context C →
    C ⟦ P1 ⟧ ↝ σ1 →
    C ⟦ P2 ⟧ ↝ σ2 →
    σ1 ≃⇓ σ2.

Lemma ctx_equiv_intro `{MP: MachineParameters} {Ctx Prog} `{!Linking Ctx Prog}
  (P1 P2 : Prog) :
  (∀ C σ1 σ2, is_context C → C ⟦ P1 ⟧ ↝ σ1 → C ⟦ P2 ⟧ ↝ σ2 → σ1 ⇓ → σ2 ⇓) →
  (∀ C σ1 σ2, is_context C → C ⟦ P2 ⟧ ↝ σ1 → C ⟦ P1 ⟧ ↝ σ2 → σ1 ⇓ → σ2 ⇓) →
  ctx_equiv P1 P2.
Proof.
  intros H12 H21 C σ1 σ2 HC Hl1 Hl2.
  apply halt_equiv_intro; eauto.
Qed.
