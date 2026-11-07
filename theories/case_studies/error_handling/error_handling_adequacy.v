From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy error_handling_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export error_handling_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_error_handling := | Adv | Sched.
#[local] Instance CmptNames_error_handling_eq_dec : EqDecision CmptNames_error_handling.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_error_handling_finite : finite.Finite CmptNames_error_handling.
Proof.
  refine {| finite.enum := [Adv; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_error_handling_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_error_handling; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition error_handling_adv_name : @CmptName CmptNames_error_handling_CmptNameG := Adv.
Definition error_handling_sched_name : @CmptName CmptNames_error_handling_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem error_handling_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  error_handling_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (error_handling_initial_state_ok_start _ _ Hok)
    as (sw & la & fo & t0 & idle & boot & main & stats & adv & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_error_handling_CmptNameG) #[]
            error_handling_firmware
            (error_handling_img sw la fo t0 idle boot main stats adv sched));
    [| exact Hfw | exact Hstep].
  apply (error_handling_fw_obligations (C := error_handling_adv_name)
           (Sched := error_handling_sched_name)); done.
Qed.
