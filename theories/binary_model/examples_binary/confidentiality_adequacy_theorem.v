From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.

From cap_machine Require Import
     stdpp_extra iris_extra
     logrel_binary fundamental_binary linking.
From cap_machine.binary_model Require Import
     macros_binary confidentiality region_invariants_binary_allocation.
From cap_machine.examples Require Import
     disjoint_regions_tactics.

From cap_machine.binary_model Require Import
     confidentiality_adequacy.

Definition is_initial_configuration_left `{memory_layout} c_adv prog :=
  ∃ stack_init p1, is_machine_context c_adv comp1 p1
                   ∧ (b_stk + length stack_init)%a = Some e_stk
                   ∧ prog = initial_state_stk b_stk e_stk stack_init p1.

Definition is_initial_configuration_right `{memory_layout} c_adv prog :=
  ∃ stack_init p2, is_machine_context c_adv comp2 p2
                   ∧ (b_stk + length stack_init)%a = Some e_stk
                   ∧ prog = initial_state_stk b_stk e_stk stack_init p2.

Definition soundness_binaryΣ : gFunctors :=
  #[GFunctor (authR cfgUR); invΣ; gen_heapΣ Addr Word;
   gen_heapΣ RegName Word;
   na_invΣ;
   STS_preΣ Addr region_invariants_binary.region_type; region_invariants_binary.heapPreΣ;
   savedPredΣ (((STS_std_states Addr region_invariants_binary.region_type)
                * (STS_states * STS_rels)) * (Word * Word))].

Global Instance inG_soundness_binaryΣ Σ : subG soundness_binaryΣ Σ → inG Σ (authR cfgUR).
Proof. solve_inG. Qed.


Theorem confidentiality_adequacy_l `{MachineParameters} `{memory_layout}
        prog1 prog2 c_adv reg' m' (es: list cap_lang.expr):
  is_initial_configuration_left c_adv prog1 →
  is_initial_configuration_right c_adv prog2 →
  is_initial_context c_adv →
  rtc erased_step prog1 (of_val HaltedV :: es, (reg', m')) →
  (∃ es' conf', rtc erased_step prog2 (of_val HaltedV :: es', conf')).
Proof.
  set (Σ := soundness_binaryΣ).
  intros [stack_init [p1 [? [? ->] ] ] ] [stack_init' [p2 [? [? ->] ] ] ] ? ?.
  eapply (@confidentiality_adequacy_l' Σ);last eauto;eauto. all: try typeclasses eauto.
Qed.

Theorem confidentiality_adequacy_r `{MachineParameters} `{memory_layout}
        prog1 prog2 c_adv reg' m' (es: list cap_lang.expr):
  is_initial_configuration_left c_adv prog1 →
  is_initial_configuration_right c_adv prog2 →
  is_initial_context c_adv →
  rtc erased_step prog2 (of_val HaltedV :: es, (reg', m')) →
  (∃ es' conf', rtc erased_step prog1 (of_val HaltedV :: es', conf')).
Proof.
  set (Σ := soundness_binaryΣ).
  intros [stack_init [p1 [? [? ->] ] ] ] [stack_init' [p2 [? [? ->] ] ] ] ? ?.
  eapply (@confidentiality_adequacy_r' Σ);last eauto;eauto. all: try typeclasses eauto.
Qed.

Theorem confidentiality_ctx_equivalent `{MachineParameters} `{memory_layout}
        prog1 prog2 c_adv :
  is_initial_configuration_left c_adv prog1 →
  is_initial_configuration_right c_adv prog2 →
  is_initial_context c_adv →
  (∃ es conf, rtc erased_step prog1 (of_val HaltedV :: es, conf)) ↔
  (∃ es conf, rtc erased_step prog2 (of_val HaltedV :: es, conf)).
Proof.
  intros. split.
  - intros (?&[? ?]&?). eapply confidentiality_adequacy_l;eauto.
  - intros (?&[? ?]&?). eapply confidentiality_adequacy_r;eauto.
Qed.
