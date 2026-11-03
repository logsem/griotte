From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  so_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import stack_object stack_object_spec_closure stack_object_spec.
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
From griotte Require Export stack_object_adequacy_obligations.

(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_so := | C.
#[local] Instance CmptNames_so_eq_dec : EqDecision CmptNames_so.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_so_finite : finite.Finite CmptNames_so.
Proof.
  refine {| finite.enum := [C] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_so_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_so; |}.

(** The logical compartment of the adversary. *)
Definition so_adv_C : @CmptName CmptNames_so_CmptNameG := C.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem so_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  so_initial_state_ok flag σ →
  rtc erased_step ([Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (so_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & C & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_so_CmptNameG) #[]
            so_firmware (so_img sw asrt t0 main C));
    [| exact Hfw | exact Hstep].
  apply (so_fw_obligations (C := so_adv_C)).
Qed.
