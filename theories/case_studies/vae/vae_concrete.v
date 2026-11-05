From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  vae vae_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link vae_firmware
  round_robin_scheduler_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the very awkward example

    The very awkward example's firmware with a concrete adversary [C] and
    the round-robin scheduler, laid out by the linker. Its initial state
    satisfies [vae_initial_state_ok] by computation; from it the thread
    runs, through the scheduler, to its exit, where the scheduler halts the
    machine; [vae_adequacy] applies to the run. *)

Definition vae_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary's first entry calls [awkward] with its second entry
    [g]. The callback [g] uses the adversary data address as a one-shot flag: on
    its first invocation it sets the flag and makes one nested call to
    [awkward], while later invocations return immediately. Both entries save
    and restore their outer return capabilities around nested calls. *)
Definition vae_C_code : list Word := encodeInstrsW vae_C_instrs.

Definition vae_C_data : list Word := [WInt 0].

Definition vae_demo_adv : list (string * link_adv) := [
  ("C", {| la_code    := vae_C_code;
           la_data    := vae_C_data;
           la_exports := [
             vae_C_adv_entry;
             vae_C_g_entry
           ];
           la_handler := ExportTable_no_handler;
           la_handler_stackless := ExportTable_no_handler |})
].

Definition vae_demo_link_cfg : link_cfg :=
  rr_link_cfg 16 vae_switcher_sealing_type vae_demo_adv 16 vae_firmware.

(** ** The linked image and its initial state *)

Definition vae_demo_image : fw_image :=
  Eval vm_compute in
    default (place vae_demo_link_cfg vae_firmware).1
      (link vae_demo_link_cfg vae_firmware).

Lemma vae_demo_linked :
  link vae_demo_link_cfg vae_firmware = Some vae_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition vae_demo_state : ExecConf := img_state vae_firmware vae_demo_image.

Lemma vae_demo_ok :
  vae_initial_state_ok (flag_assert (img_asrt vae_demo_image)) vae_demo_state.
Proof.
  rewrite /vae_initial_state_ok.
  exists (img_sw vae_demo_image), (img_asrt vae_demo_image), (thread_of vae_demo_image 0),
    (img_idle vae_demo_image), (img_boot vae_demo_image),
    (cmpt_of vae_demo_image "main"), (cmpt_of vae_demo_image "C"),
    (cmpt_of vae_demo_image "sched").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers vae_demo_link_cfg.
  all: try (exists vae_C_adv_entry, 0%nat; split; [|exists vae_C_g_entry, 0%nat; split_and!]).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /vae_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [vae_demo_state] starts at the switcher's call of the scheduler, which
    resumes the thread; the thread runs to its exit, and the scheduler then
    halts the machine. [vae_adequacy] applies to the run: the flag of the
    assert library is still zero. *)
Theorem vae_runs_and_gracefully_halts :
  ∃ σ',
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], vae_demo_state) ([Instr Halted], σ')
    ∧ mem σ' !! flag_assert (img_asrt vae_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_hw_correct (N.to_nat 16500%N) vae_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (vae_adequacy _ _ _ _ vae_demo_ok Hrun).
Qed.
