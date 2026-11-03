From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  error_handling_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import
  error_handling error_handling_spec_handler error_handling_spec_read
  error_handling_spec_read_safe error_handling_main_spec.
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
From griotte Require Export error_handling_adequacy_obligations.

(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_error_handling := | Adv.
#[local] Instance CmptNames_error_handling_eq_dec : EqDecision CmptNames_error_handling.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_error_handling_finite : finite.Finite CmptNames_error_handling.
Proof.
  refine {| finite.enum := [Adv] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_error_handling_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_error_handling; |}.

(** The logical compartment of the adversary. *)
Definition error_handling_adv_name : @CmptName CmptNames_error_handling_CmptNameG := Adv.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem error_handling_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  error_handling_initial_state_ok flag σ →
  rtc erased_step ([Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (error_handling_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & stats & adv & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_error_handling_CmptNameG) #[]
            error_handling_firmware (error_handling_img sw asrt t0 main stats adv));
    [| exact Hfw | exact Hstep].
  apply (error_handling_fw_obligations (C := error_handling_adv_name)).
Qed.
