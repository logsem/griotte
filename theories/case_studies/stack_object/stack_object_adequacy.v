From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  firmware_thread_obligations so_firmware.
From griotte Require Import hw_lang.
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

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_so := | C | Sched.
#[local] Instance CmptNames_so_eq_dec : EqDecision CmptNames_so.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_so_finite : finite.Finite CmptNames_so.
Proof.
  refine {| finite.enum := [C; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_so_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_so; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition so_adv_C : @CmptName CmptNames_so_CmptNameG := C.
Definition so_sched : @CmptName CmptNames_so_CmptNameG := Sched.

(** The logical compartment of each compartment of the firmware, as the
    proof of [so_fw_obligations] uses it: the scheduler ["sched"] is
    [Sched]; every other compartment, trusted ones included, is the
    adversary's [C], whose world runs the calls into them. *)
Definition so_own (s : string) : @CmptName CmptNames_so_CmptNameG :=
  if String.eqb s "sched"%string then Sched else C.

(** The threads of a compartment can run in every compartment whose entries
    its untrusted code can obtain, for the assignment of threads that
    [so_fw_obligations] uses through [fw_obligations_pt_of_pinned]: the
    untrusted ["C"] imports exports of ["main"] and of itself, both owned
    by [C]. *)
Lemma so_T_closed `{MP : MachineParameters} :
  T_closed (cthreads := fw_cthreads_pinned so_sched) so_firmware so_own.
Proof.
  intros Ch Ct (fc & ub & c & e & Hfc & Hbody & <- & Himp & <-).
  cbv [so_firmware fw_cmpts] in Hfc.
  repeat (apply elem_of_cons in Hfc as [-> | Hfc]);
    try discriminate Hbody;
    try by apply not_elem_of_nil in Hfc.
  cbn [fc_imports] in Himp.
  repeat (apply elem_of_cons in Himp as [Himp | Himp]);
    try discriminate Himp;
    try by apply not_elem_of_nil in Himp.
  all: injection Himp as -> _; done.
Qed.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem so_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  so_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (so_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & idle & boot & main & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_so_CmptNameG) #[]
            so_firmware (so_img sw asrt t0 idle boot main C sched));
    [| exact Hfw | exact Hstep].
  apply (so_fw_obligations (C := so_adv_C) (Sched := so_sched)); done.
Qed.
