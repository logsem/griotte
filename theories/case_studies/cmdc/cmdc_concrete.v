From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  switcher assert allocator_resources compartment_layout
  cmdc cmdc_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link cmdc_firmware.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the CMDC case study

    The CMDC firmware with two concrete adversaries [B] and [C], laid out
    by the linker. Its initial state satisfies [cmdc_initial_state_ok] by
    computation, runs to [Halted], and [cmdc_adequacy] applies to it. *)

Definition cmdc_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary consists of two unknown compartments. Compartment
    [B] writes [7] through the capability it receives and also saves that
    capability on its stack; compartment [C] writes [9] through its received
    capability. Together they exercise the main program's cross-compartment
    capability discipline. Each has one zeroed global, and its entry point
    right after its import. *)
Definition cmdc_B_code : list Word :=
  encodeInstrsW [
    Store ca0 7%Z 0;
    Store csp ca0 0;
    Jalr cnull cra
  ].
Definition cmdc_C_code : list Word :=
  encodeInstrsW [
    Store ca0 9%Z 0;
    Jalr cnull cra
  ].
Definition cmdc_B_data : list Word := [WInt 0].
Definition cmdc_C_data : list Word := [WInt 0].

Definition cmdc_demo_link_cfg : link_cfg := {|
  lk_base        := 16;
  lk_ot_switcher := cmdc_switcher_sealing_type;
  lk_adv         := [
    ("B", {| la_code    := cmdc_B_code;
             la_data    := cmdc_B_data;
             la_exports := [
               1  (* after the import *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |});
    ("C", {| la_code    := cmdc_C_code;
             la_data    := cmdc_C_data;
             la_exports := [
               1  (* after the import *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ]
|}.

(** ** The linked image and its initial state *)

Definition cmdc_demo_image : fw_image :=
  Eval vm_compute in
    default (place cmdc_demo_link_cfg cmdc_firmware).1
      (link cmdc_demo_link_cfg cmdc_firmware).

Lemma cmdc_demo_linked :
  link cmdc_demo_link_cfg cmdc_firmware = Some cmdc_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition cmdc_demo_state : ExecConf := img_state cmdc_firmware cmdc_demo_image.

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma cmdc_demo_ok :
  cmdc_initial_state_ok (flag_assert (img_asrt cmdc_demo_image)) cmdc_demo_state.
Proof.
  rewrite /cmdc_initial_state_ok.
  exists (img_sw cmdc_demo_image), (img_asrt cmdc_demo_image), (thread_of cmdc_demo_image 0),
    (cmpt_of cmdc_demo_image "main"), (cmpt_of cmdc_demo_image "B"), (cmpt_of cmdc_demo_image "C").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers cmdc_demo_link_cfg.
  all: try (exists 1%nat, 0%nat; split_and!).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /cmdc_demo_state /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [cmdc_demo_state] runs to [Halted], and [cmdc_adequacy] applies to it:
    the flag of the assert library is still zero. *)
Theorem cmdc_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Seq (Instr Executable)], cmdc_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt cmdc_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct (N.to_nat 10000%N) Executable cmdc_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[[[pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (cmdc_adequacy _ _ _ _ cmdc_demo_ok Hrun).
Qed.
