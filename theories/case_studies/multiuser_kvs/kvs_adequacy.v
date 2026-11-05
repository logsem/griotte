From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy kvs_firmware.
From griotte Require Import hw_lang logrel seal_registry kvs_preamble.
From griotte Require Export kvs_adequacy_obligations.

(** We initialise concretely the compartments name typeclass: the
    adversary and the scheduler. *)

Inductive CmptNames_kvs := | B | Sched.
#[local] Instance CmptNames_kvs_eq_dec : EqDecision CmptNames_kvs.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
#[local] Instance CmptNames_kvs_finite : finite.Finite CmptNames_kvs.
Proof.
  refine {| finite.enum := [B; Sched] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_kvs_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_kvs; |}.


(** The logical compartments of the adversary and of the scheduler. *)
Definition kvs_adv_name : @CmptName CmptNames_kvs_CmptNameG := B.
Definition kvs_sched_name : @CmptName CmptNames_kvs_CmptNameG := Sched.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem kvs_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  kvs_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (kvs_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & idle & boot & main & kvs & B & sched & ot_kvs & key_main & key_B
        & <- & Hkeys & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_kvs_CmptNameG)
            #[gen_heapΣ user_key_t kvs_user_map; ghost_mapΣ user_key_t (option LWord);
              ghost_varΣ kvs_physical_map; @seal_registryΣ CmptNames_kvs_CmptNameG LAddr _ _]
            (kvs_firmware ot_kvs key_main key_B)
            (kvs_img sw asrt t0 idle boot main kvs B sched));
    [| exact Hfw | exact Hstep].
  apply (kvs_fw_obligations (B := kvs_adv_name) (Sched := kvs_sched_name));
    [exact Hkeys | done].
Qed.
