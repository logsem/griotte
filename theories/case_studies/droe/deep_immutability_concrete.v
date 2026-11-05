From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  deep_immutability deep_immutability_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link droe_firmware
  round_robin_scheduler_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the deep-immutability case study

    The deep-immutability firmware with a concrete adversary [C] and the
    round-robin scheduler, laid out by the linker. Its initial state
    satisfies [droe_initial_state_ok] by computation; from it the thread
    runs, through the scheduler, to its exit, where the scheduler halts the
    machine; [droe_adequacy] applies to the run. *)

Definition droe_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary follows the outer read-only capability in [ca0],
    reads through the nested capability, and stores the observed word in its
    own data address before returning. It therefore directly tests whether the
    supposedly deeply immutable value can be observed through the nesting.
    It has one zeroed global, and its entry point right after its import. *)
Definition droe_C_code : list Word :=
  encodeInstrsW [
    CLoad ct0 ca0 0;
    CLoad ct0 ct0 0;
    Store cgp ct0 0;
    Jalr cnull cra
  ].

Definition droe_C_data : list Word := [WInt 0].

Definition droe_demo_link_cfg : link_cfg :=
  rr_link_cfg 16 droe_switcher_sealing_type [
    ("C", {| la_code    := droe_C_code;
             la_data    := droe_C_data;
             la_exports := [
               1  (* after the import *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ] 16 droe_firmware.

(** ** The linked image and its initial state *)

Definition droe_demo_image : fw_image :=
  Eval vm_compute in
    default (place droe_demo_link_cfg droe_firmware).1
      (link droe_demo_link_cfg droe_firmware).

Lemma droe_demo_linked :
  link droe_demo_link_cfg droe_firmware = Some droe_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition droe_demo_state : ExecConf := img_state droe_firmware droe_demo_image.

Lemma droe_demo_ok :
  droe_initial_state_ok (flag_assert (img_asrt droe_demo_image)) droe_demo_state.
Proof.
  rewrite /droe_initial_state_ok.
  exists (img_sw droe_demo_image), (img_asrt droe_demo_image), (thread_of droe_demo_image 0),
    (img_idle droe_demo_image), (img_boot droe_demo_image),
    (cmpt_of droe_demo_image "main"), (cmpt_of droe_demo_image "C"),
    (cmpt_of droe_demo_image "sched").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers droe_demo_link_cfg.
  all: try (exists 1%nat, 0%nat; split_and!).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /droe_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [droe_demo_state] starts at the switcher's call of the scheduler, which
    resumes the thread; the thread runs to its exit, and the scheduler then
    halts the machine. [droe_adequacy] applies to the run: the flag of the
    assert library is still zero. Fuel 1600 does not suffice; 1700 reaches
    [Halted]. *)
Theorem droe_runs_and_gracefully_halts :
  ∃ σ',
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], droe_demo_state) ([Instr Halted], σ')
    ∧ mem σ' !! flag_assert (img_asrt droe_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_hw_correct (N.to_nat 4500%N) droe_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (droe_adequacy _ _ _ _ droe_demo_ok Hrun).
Qed.
