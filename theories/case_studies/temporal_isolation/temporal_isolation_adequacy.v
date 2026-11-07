From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy ti_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export temporal_isolation_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_ti := | B | Sched.
#[local] Instance CmptNames_ti_eq_dec : EqDecision CmptNames_ti.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_ti_finite : finite.Finite CmptNames_ti.
Proof.
  refine {| finite.enum := [B; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_ti_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_ti; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition ti_adv_B : @CmptName CmptNames_ti_CmptNameG := B.
Definition ti_sched : @CmptName CmptNames_ti_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The firmware runs two threads that share the
    adversary [B]: the thread 0 lends [B] a local capability to the global
    [b] of [K]; the thread 1 runs in [B] concurrently. Whatever the code of
    [B], the flag of the assert library stays zero: the local capability
    never reaches the thread 1, which could otherwise overwrite [b] between
    [K]'s write and its assert: [K.run] runs with interrupts enabled, so
    the thread 1 may run there. The scheduler starts with no
    interrupt-enabling sentry: [firmware_ok_sched_no_enabling]. *)
Theorem ti_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  ti_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (ti_initial_state_ok_start _ _ Hok)
    as (sw & la & fo & t0 & t1 & idle & boot & K & B & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_ti_CmptNameG) #[]
            ti_firmware (ti_img sw la fo t0 t1 idle boot K B sched));
    [| exact Hfw | exact Hstep].
  apply (ti_fw_obligations (B := ti_adv_B) (Sched := ti_sched)); done.
Qed.
