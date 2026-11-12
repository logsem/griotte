From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy so_firmware.
From griotte Require Import hw_lang logrel.
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
    as (sw & assert & assert_flag & t0 & idle & boot & main & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_so_CmptNameG) #[]
            so_firmware (so_img sw assert assert_flag t0 idle boot main C sched));
    [| exact Hfw | exact Hstep].
  apply (so_fw_obligations (C := so_adv_C) (Sched := so_sched)); done.
Qed.
