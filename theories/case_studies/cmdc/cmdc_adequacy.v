From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy cmdc_firmware.
From griotte Require Import hw_lang logrel.
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
    as (sw & assert & assert_flag & t0 & idle & boot & main & B & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_CMDC_CmptNameG) #[]
            cmdc_firmware (cmdc_img sw assert assert_flag t0 idle boot main B C sched));
    [| exact Hfw | exact Hstep].
  apply (cmdc_fw_obligations (B := cmdc_adv_B) (C := cmdc_adv_C) (Sched := cmdc_sched));
    done.
Qed.
