From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy ist_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export interrupt_status_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_ist := | B | Sched.
#[local] Instance CmptNames_ist_eq_dec : EqDecision CmptNames_ist.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_ist_finite : finite.Finite CmptNames_ist.
Proof.
  refine {| finite.enum := [B; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_ist_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_ist; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition ist_adv_B : @CmptName CmptNames_ist_CmptNameG := B.
Definition ist_sched : @CmptName CmptNames_ist_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The firmware runs two threads that share the
    adversary [B]: the thread 0 enters [K.run] with interrupts disabled and
    gives [B] a capability to the global [b] of [K], which [B] may keep in
    its globals; the thread 1 runs in [B] concurrently and may write [b]
    whenever it runs. Whatever the code of [B], the flag of the assert
    library stays zero: the return from [B] restores the posture of [K], so
    no thread runs between [K]'s write of [b] and its assert. The scheduler
    starts with no interrupt-enabling sentry: [firmware_ok_sched_no_enabling]. *)
Theorem ist_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  ist_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (ist_initial_state_ok_start _ _ Hok)
    as (sw & la & fo & t0 & t1 & idle & boot & K & B & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_ist_CmptNameG) #[]
            ist_firmware (ist_img sw la fo t0 t1 idle boot K B sched));
    [| exact Hfw | exact Hstep].
  apply (ist_fw_obligations (B := ist_adv_B) (Sched := ist_sched)); done.
Qed.
