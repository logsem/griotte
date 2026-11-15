From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy lse_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export lse_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_lse := | C | Sched.
#[local] Instance CmptNames_lse_eq_dec : EqDecision CmptNames_lse.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_lse_finite : finite.Finite CmptNames_lse.
Proof.
  refine {| finite.enum := [C; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_lse_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_lse; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition lse_adv_C : @CmptName CmptNames_lse_CmptNameG := C.
Definition lse_sched : @CmptName CmptNames_lse_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem lse_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  lse_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (lse_initial_state_ok_start _ _ Hok)
    as (sw & assert & assert_flag & t0 & idle & boot & main & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_lse_CmptNameG) #[]
            lse_firmware (lse_img sw assert assert_flag t0 idle boot main C sched));
    [| exact Hfw | exact Hstep].
  apply (lse_fw_obligations (C := lse_adv_C) (Sched := lse_sched)); done.
Qed.
