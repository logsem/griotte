From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy droe_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export deep_immutability_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_droe := | C | Sched.
#[local] Instance CmptNames_droe_eq_dec : EqDecision CmptNames_droe.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_droe_finite : finite.Finite CmptNames_droe.
Proof.
  refine {| finite.enum := [C; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_droe_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_droe; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition droe_adv_C : @CmptName CmptNames_droe_CmptNameG := C.
Definition droe_sched : @CmptName CmptNames_droe_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem droe_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  droe_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (droe_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & idle & boot & main & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_droe_CmptNameG) #[]
            droe_firmware (droe_img sw asrt t0 idle boot main C sched));
    [| exact Hfw | exact Hstep].
  apply (droe_fw_obligations (C := droe_adv_C) (Sched := droe_sched)); done.
Qed.
