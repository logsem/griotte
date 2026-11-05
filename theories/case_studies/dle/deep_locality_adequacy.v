From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  firmware_thread_obligations dle_firmware.
From griotte Require Import hw_lang.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import deep_locality deep_locality_spec.
From griotte Require Import assert_spec logrel.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.
From griotte Require Import allocator_resources heap_region.
From griotte Require Export deep_locality_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_dle := | C | Sched.
#[local] Instance CmptNames_dle_eq_dec : EqDecision CmptNames_dle.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_dle_finite : finite.Finite CmptNames_dle.
Proof.
  refine {| finite.enum := [C; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_dle_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_dle; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition dle_adv_C : @CmptName CmptNames_dle_CmptNameG := C.
Definition dle_sched : @CmptName CmptNames_dle_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem dle_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  dle_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (dle_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & idle & boot & main & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_dle_CmptNameG) #[]
            dle_firmware (dle_img sw asrt t0 idle boot main C sched));
    [| exact Hfw | exact Hstep].
  apply (dle_fw_obligations (C := dle_adv_C) (Sched := dle_sched)); done.
Qed.
