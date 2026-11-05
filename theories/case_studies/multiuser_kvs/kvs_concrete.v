From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  kvs kvs_main kvs_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link kvs_firmware
  round_robin_scheduler_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the KVS case study

    The KVS firmware with concrete sealing types and user keys, a concrete
    adversary [B] and the round-robin scheduler, laid out by the linker.
    Its initial state satisfies [kvs_initial_state_ok] by computation; from
    it the thread runs, through the scheduler, to its exit, where the
    scheduler halts the machine; [kvs_adequacy] applies to the run. *)

Definition kvs_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.
Definition kvs_service_sealing_type : OType := @finz.FinZ ONum 11 eq_refl eq_refl.

(** The firmware, with the user keys [1] (main) and [2] (B). *)
Definition kvs_demo_firmware : firmware := kvs_firmware kvs_service_sealing_type 1 2.

(** The adversary [B]: the code of [kvs_B_asm], one zeroed global, and its
    entry point. *)
Definition kvs_B_code : list Word := encodeInstrsW kvs_B_instrs.
Definition kvs_B_data : list Word := [WInt 0].

Definition kvs_demo_link_cfg : link_cfg :=
  rr_link_cfg 16 kvs_switcher_sealing_type [
    ("B", {| la_code    := kvs_B_code;
             la_data    := kvs_B_data;
             la_exports := [
               kvs_B_adv_entry
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ] 16 kvs_demo_firmware.

(** ** The linked image and its initial state *)

Definition kvs_demo_image : fw_image :=
  Eval vm_compute in
    default (place kvs_demo_link_cfg kvs_demo_firmware).1
      (link kvs_demo_link_cfg kvs_demo_firmware).

Lemma kvs_demo_linked :
  link kvs_demo_link_cfg kvs_demo_firmware = Some kvs_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition kvs_demo_state : ExecConf := img_state kvs_demo_firmware kvs_demo_image.

Lemma kvs_demo_ok :
  kvs_initial_state_ok (flag_assert (img_asrt kvs_demo_image)) kvs_demo_state.
Proof.
  rewrite /kvs_initial_state_ok.
  exists (img_sw kvs_demo_image), (img_asrt kvs_demo_image), (thread_of kvs_demo_image 0),
    (img_idle kvs_demo_image), (img_boot kvs_demo_image),
    (cmpt_of kvs_demo_image "main"), (cmpt_of kvs_demo_image "kvs"), (cmpt_of kvs_demo_image "B"),
    (cmpt_of kvs_demo_image "sched"), kvs_service_sealing_type, 1%Z, 2%Z.
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers kvs_demo_link_cfg.
  all: try (exists kvs_B_adv_entry, 0%nat; split_and!).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /kvs_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [kvs_demo_state] starts at the switcher's call of the scheduler, which
    resumes the thread; the thread runs to its exit, and the scheduler then
    halts the machine. [kvs_adequacy] applies to the run: the flag of the
    assert library is still zero. *)
Theorem kvs_runs_and_gracefully_halts :
  ∃ σ',
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state) ([Instr Halted], σ')
    ∧ mem σ' !! flag_assert (img_asrt kvs_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_hw_correct (N.to_nat 16500%N) kvs_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (kvs_adequacy _ _ _ _ kvs_demo_ok Hrun).
Qed.
