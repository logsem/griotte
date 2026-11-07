From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy cmdc_shared_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export cmdc_shared_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the two
    adversaries and the scheduler. *)

Inductive CmptNames_CMDC_shared := | B | C | Sched.
#[local] Instance CmptNames_CMDC_shared_eq_dec : EqDecision CmptNames_CMDC_shared.
Proof. intros X Y; destruct X, Y; solve_decision. Qed.
#[local] Instance CmptNames_CMDC_shared_finite : finite.Finite CmptNames_CMDC_shared.
Proof.
  refine {| finite.enum := [B; C; Sched] |}.
  + constructor; [set_solver | constructor; [set_solver | apply NoDup_singleton] ].
  + intros [| |]; [left | right; left | right; right; left].
Defined.

#[local] Program Instance CmptNames_CMDC_shared_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_CMDC_shared; |}.

(** The logical compartments of the adversaries and of the scheduler. *)
Definition cmdc_shared_adv_B : @CmptName CmptNames_CMDC_shared_CmptNameG := B.
Definition cmdc_shared_adv_C : @CmptName CmptNames_CMDC_shared_CmptNameG := C.
Definition cmdc_shared_sched : @CmptName CmptNames_CMDC_shared_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The CMDC firmware with a second thread in [C]: the
    thread 0 enters [main], which calls the adversary [B] with a capability
    to its global [b] and the adversary [C] with a capability to its global
    [c]; the thread 1 enters [C] at [adv], so [C] is shared by the threads
    0 and 1 (the world of [C] in its invariant); [B] runs only on the
    thread 0. Whatever the code of [B] and [C], the flag of the assert
    library stays zero. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem cmdc_shared_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  cmdc_shared_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (cmdc_shared_initial_state_ok_start _ _ Hok)
    as (sw & la & fo & t0 & t1 & idle & boot & main & B & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_CMDC_shared_CmptNameG) #[]
            cmdc_shared_firmware (cmdc_shared_img sw la fo t0 t1 idle boot main B C sched));
    [| exact Hfw | exact Hstep].
  apply (cmdc_shared_fw_obligations (B := cmdc_shared_adv_B) (C := cmdc_shared_adv_C)
           (Sched := cmdc_shared_sched));
    done.
Qed.
