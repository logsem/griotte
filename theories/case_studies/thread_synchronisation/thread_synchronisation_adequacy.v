From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy tsy_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export thread_synchronisation_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_tsy := | B | Sched.
#[local] Instance CmptNames_tsy_eq_dec : EqDecision CmptNames_tsy.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_tsy_finite : finite.Finite CmptNames_tsy.
Proof.
  refine {| finite.enum := [B; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_tsy_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_tsy; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition tsy_adv_B : @CmptName CmptNames_tsy_CmptNameG := B.
Definition tsy_sched : @CmptName CmptNames_tsy_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The firmware runs two threads in the trusted [K]:
    the thread 0 enters [K.run1], gives the adversary [B] a capability to
    the global [b] of [K], which [B] may keep in its globals, then sets the
    global [flag] of [K]; the thread 1 enters [K.run2], waits for [flag],
    yielding, then writes [b] and asserts it. Only the thread 0 runs in
    [B] ([B] is exclusive), and the world of [B] passes to the thread 1
    with [flag]. Whatever the code of [B], the flag of the assert library
    stays zero. The scheduler starts with no interrupt-enabling sentry:
    [firmware_ok_sched_no_enabling]. *)
Theorem tsy_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  tsy_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (tsy_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & t1 & idle & boot & K & B & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_tsy_CmptNameG) #[]
            tsy_firmware (tsy_img sw asrt t0 t1 idle boot K B sched));
    [| exact Hfw | exact Hstep].
  apply (tsy_fw_obligations (B := tsy_adv_B) (Sched := tsy_sched)); done.
Qed.
