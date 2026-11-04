From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  firmware_thread_obligations droe_firmware.
From griotte Require Import hw_lang.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import deep_immutability deep_immutability_spec.
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
From griotte Require Export deep_immutability_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_droe := | C | Sched.
#[local] Instance CmptNames_droe_eq_dec : EqDecision CmptNames_droe.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_droe_finite : finite.Finite CmptNames_droe.
Proof.
  refine {| finite.enum := [C; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_droe_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_droe; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition droe_adv_C : @CmptName CmptNames_droe_CmptNameG := C.
Definition droe_sched : @CmptName CmptNames_droe_CmptNameG := Sched.

(** The logical compartment of each compartment of the firmware, as the
    proof of [droe_fw_obligations] uses it: the scheduler ["sched"] is
    [Sched]; every other compartment, trusted ones included, is the
    adversary's [C], whose world runs the calls into them. *)
Definition droe_own (s : string) : @CmptName CmptNames_droe_CmptNameG :=
  if String.eqb s "sched"%string then Sched else C.

(** The threads of a compartment can run in every compartment whose entries
    its untrusted code can obtain, for the assignment of threads that
    [droe_fw_obligations] uses through [fw_obligations_of_pinned]: no
    untrusted compartment of the firmware imports an export. *)
Lemma droe_T_closed `{MP : MachineParameters} :
  T_closed (cthreads := fw_cthreads_pinned droe_sched) droe_firmware droe_own.
Proof.
  intros Ch Ct (fc & ub & c & e & Hfc & Hbody & _ & Himp & _).
  cbv [droe_firmware fw_cmpts] in Hfc.
  repeat (apply elem_of_cons in Hfc as [-> | Hfc]);
    try discriminate Hbody;
    try (apply list_elem_of_singleton in Himp; discriminate Himp).
  all: by apply not_elem_of_nil in Hfc.
Qed.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem droe_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  droe_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (droe_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & idle & boot & main & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_droe_CmptNameG) #[]
            droe_firmware (droe_img sw asrt t0 idle boot main C sched));
    [| exact Hfw | exact Hstep].
  apply (droe_fw_obligations (C := droe_adv_C) (Sched := droe_sched)); done.
Qed.
