From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy cmdc_isolated_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export cmdc_isolated_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the three
    adversaries and the scheduler. *)

Inductive CmptNames_CMDC_isolated := | B | C | D | Sched.
#[local] Instance CmptNames_CMDC_isolated_eq_dec : EqDecision CmptNames_CMDC_isolated.
Proof. intros X Y; destruct X, Y; solve_decision. Qed.
#[local] Instance CmptNames_CMDC_isolated_finite : finite.Finite CmptNames_CMDC_isolated.
Proof.
  refine {| finite.enum := [B; C; D; Sched] |}.
  + constructor; [set_solver | constructor; [set_solver | constructor;
      [set_solver | apply NoDup_singleton] ] ].
  + intros [| | |]; [left | right; left | right; right; left | right; right; right; left].
Defined.

#[local] Program Instance CmptNames_CMDC_isolated_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_CMDC_isolated; |}.

(** The logical compartments of the adversaries and of the scheduler. *)
Definition cmdc_isolated_adv_B : @CmptName CmptNames_CMDC_isolated_CmptNameG := B.
Definition cmdc_isolated_adv_C : @CmptName CmptNames_CMDC_isolated_CmptNameG := C.
Definition cmdc_isolated_adv_D : @CmptName CmptNames_CMDC_isolated_CmptNameG := D.
Definition cmdc_isolated_sched : @CmptName CmptNames_CMDC_isolated_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The firmware runs two threads: the CMDC case
    study's, and a thread alone in the adversary [D]. Whatever the code of
    [B], [C] and [D], the flag of the assert library stays zero: the
    isolated thread cannot make [main]'s checks fail. The scheduler starts
    with no interrupt-enabling sentry: [firmware_ok_sched_no_enabling]. *)
Theorem cmdc_isolated_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  cmdc_isolated_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (cmdc_isolated_initial_state_ok_start _ _ Hok)
    as (sw & la & fo & t0 & t1 & idle & boot & main & B & C & D & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_CMDC_isolated_CmptNameG) #[]
            cmdc_isolated_firmware (cmdc_isolated_img sw la fo t0 t1 idle boot main B C D sched));
    [| exact Hfw | exact Hstep].
  apply (cmdc_isolated_fw_obligations (B := cmdc_isolated_adv_B) (C := cmdc_isolated_adv_C)
           (D := cmdc_isolated_adv_D) (Sched := cmdc_isolated_sched));
    done.
Qed.
