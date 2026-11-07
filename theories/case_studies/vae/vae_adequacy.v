From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy vae_firmware.
From griotte Require Import hw_lang logrel.
From griotte Require Export vae_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_vae := | C | Sched.
#[local] Instance CmptNames_vae_eq_dec : EqDecision CmptNames_vae.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_vae_finite : finite.Finite CmptNames_vae.
Proof.
  refine {| finite.enum := [C; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_vae_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_vae; |}.

(** The logical compartments of the adversary and of the scheduler. *)
Definition vae_adv_C : @CmptName CmptNames_vae_CmptNameG := C.
Definition vae_sched : @CmptName CmptNames_vae_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem vae_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  vae_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (vae_initial_state_ok_start _ _ Hok)
    as (sw & la & fo & t0 & idle & boot & main & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_vae_CmptNameG) #[]
            vae_firmware (vae_img sw la fo t0 idle boot main C sched));
    [| exact Hfw | exact Hstep].
  apply (vae_fw_obligations (C := vae_adv_C) (Sched := vae_sched)); done.
Qed.
