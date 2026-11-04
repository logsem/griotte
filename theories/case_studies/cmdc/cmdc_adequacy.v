From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  firmware_thread_obligations cmdc_firmware.
From griotte Require Import hw_lang.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import cmdc cmdc_spec.
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
From griotte Require Export cmdc_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the two
    adversaries and the scheduler. *)

Inductive CmptNames_CMDC := | B | C | Sched.
#[local] Instance CmptNames_CMDC_eq_dec : EqDecision CmptNames_CMDC.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
#[local] Instance CmptNames_CMDC_finite : finite.Finite CmptNames_CMDC.
Proof.
  refine {| finite.enum := [B; C; Sched] |}.
  + constructor; [set_solver | constructor; [set_solver | apply NoDup_singleton] ].
  + intros [| |]; [ left | right; left | right; right; left ].
Defined.

#[local] Program Instance CmptNames_CMDC_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_CMDC; |}.

(** The logical compartments of the adversaries and of the scheduler. *)
Definition cmdc_adv_B : @CmptName CmptNames_CMDC_CmptNameG := B.
Definition cmdc_adv_C : @CmptName CmptNames_CMDC_CmptNameG := C.
Definition cmdc_sched : @CmptName CmptNames_CMDC_CmptNameG := Sched.

(** The logical compartment of each compartment of the firmware, as the
    proof of [cmdc_fw_obligations] uses it: the adversaries ["B"] and ["C"]
    are [B] and [C], the scheduler ["sched"] is [Sched]. [fw_reach] reads
    [main], which is trusted and not imported, nowhere; it is mapped to
    [B]. *)
Definition cmdc_own (s : string) : @CmptName CmptNames_CMDC_CmptNameG :=
  if String.eqb s "C"%string then C
  else if String.eqb s "sched"%string then Sched
  else B.

(** The threads of a compartment can run in every compartment whose entries
    its untrusted code can obtain, for the assignment of threads that
    [cmdc_fw_obligations] uses through [fw_obligations_pt_of_pinned]: no
    untrusted compartment of the firmware imports an export. *)
Lemma cmdc_T_closed `{MP : MachineParameters} :
  T_closed (cthreads := fw_cthreads_pinned cmdc_sched) cmdc_firmware cmdc_own.
Proof.
  intros Ch Ct (fc & ub & c & e & Hfc & Hbody & _ & Himp & _).
  cbv [cmdc_firmware fw_cmpts] in Hfc.
  repeat (apply elem_of_cons in Hfc as [-> | Hfc]);
    try discriminate Hbody;
    try (apply list_elem_of_singleton in Himp; discriminate Himp).
  all: by apply not_elem_of_nil in Hfc.
Qed.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem cmdc_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  cmdc_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (cmdc_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & idle & boot & main & B & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_CMDC_CmptNameG) #[]
            cmdc_firmware (cmdc_img sw asrt t0 idle boot main B C sched));
    [| exact Hfw | exact Hstep].
  apply (cmdc_fw_obligations (B := cmdc_adv_B) (C := cmdc_adv_C) (Sched := cmdc_sched));
    done.
Qed.
