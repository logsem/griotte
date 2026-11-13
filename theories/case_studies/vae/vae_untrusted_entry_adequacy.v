From iris.proofmode Require Import proofmode.
From griotte Require Import image firmware firmware_ok firmware_adequacy
  vae_untrusted_entry_firmware.
From griotte Require Import hw_lang logrel vae_adequacy.
From griotte Require Export vae_untrusted_entry_adequacy_obligations.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM. The scheduler starts with no interrupt-enabling
    sentry: [firmware_ok_sched_no_enabling]. *)
Theorem vae_untrusted_entry_adequacy `{MP : MachineParameters}
    (flag : Addr) (σ σ' : ExecConf) (es : list (language.expr griotte_hw_lang)) :
  vae_untrusted_entry_initial_state_ok flag σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (vae_untrusted_entry_initial_state_ok_start _ _ Hok)
    as (sw & assert & assert_flag & t0 & idle & boot & main & C & sched & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_vae_CmptNameG) #[]
            vae_untrusted_entry_firmware
            (vae_untrusted_entry_img sw assert assert_flag t0 idle boot main C sched));
    [| exact Hfw | exact Hstep].
  apply (vae_untrusted_entry_fw_obligations (C := vae_adv_C) (Sched := vae_sched)); done.
Qed.
