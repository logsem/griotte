From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  firmware_thread_obligations.
From griotte.case_studies.hts_ownership Require Import hts_firmware.
From griotte Require Import hw_lang.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import assert_spec.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.
From griotte Require Import allocator_resources heap_region.
From griotte.case_studies.hts_ownership Require Import
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec.
From griotte.allocators.ownership Require Import
  allocator allocator_preamble allocator_resource_spec allocator_malloc_safe allocator_free_safe
  allocator_adequacy.
From griotte Require Export heap_temporal_safety_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_hts := | B | Sched.
#[local] Instance CmptNames_hts_eq_dec : EqDecision CmptNames_hts.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_hts_finite : finite.Finite CmptNames_hts.
Proof.
  refine {| finite.enum := [B; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_hts_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_hts; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition hts_adv_B : @CmptName CmptNames_hts_CmptNameG := B.
Definition hts_sched : @CmptName CmptNames_hts_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem hts_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  hts_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (hts_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & idle & boot & main & allocator & B & sched & ot_alloc & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_hts_CmptNameG)
            #[allocator_ownerΣ; @seal_registryΣ CmptNames_hts_CmptNameG LAddr _ _]
            (hts_firmware ot_alloc)
            (hts_img sw asrt t0 idle boot main allocator B sched));
    [| exact Hfw | exact Hstep].
  apply (hts_fw_obligations (B := hts_adv_B) (Sched := hts_sched)); done.
Qed.
