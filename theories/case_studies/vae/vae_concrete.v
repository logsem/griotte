From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  switcher assert allocator_resources compartment_layout
  vae vae_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link vae_firmware.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the very awkward example

    The very awkward example's firmware with a concrete adversary [C], laid
    out by the linker. Its initial state satisfies [vae_initial_state_ok] by
    computation, runs to [Halted], and [vae_adequacy] applies to it. *)

Definition vae_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary's first entry calls [awkward] with its second entry
    [g]. The callback [g] uses the adversary data address as a one-shot flag: on
    its first invocation it sets the flag and makes one nested call to
    [awkward], while later invocations return immediately. Both entries save
    and restore their outer return capabilities around nested calls. *)
Definition vae_C_code : list Word := encodeInstrsW vae_C_instrs.

Definition vae_C_data : list Word := [WInt 0].

Definition vae_demo_link_cfg : link_cfg := {|
  lk_base        := 16;
  lk_ot_switcher := vae_switcher_sealing_type;
  lk_adv         := [
    ("C", {| la_code    := vae_C_code;
             la_data    := vae_C_data;
             la_exports := [
               vae_C_adv_entry;
               vae_C_g_entry
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ]
|}.

(** ** The linked image and its initial state *)

Definition vae_demo_image : fw_image :=
  Eval vm_compute in
    default (place vae_demo_link_cfg vae_firmware).1
      (link vae_demo_link_cfg vae_firmware).

Lemma vae_demo_linked :
  link vae_demo_link_cfg vae_firmware = Some vae_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition vae_demo_state : ExecConf := img_state vae_firmware vae_demo_image.

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma vae_demo_ok :
  vae_initial_state_ok (flag_assert (img_asrt vae_demo_image)) vae_demo_state.
Proof.
  rewrite /vae_initial_state_ok.
  exists (img_sw vae_demo_image), (img_asrt vae_demo_image), (thread_of vae_demo_image 0),
    (cmpt_of vae_demo_image "main"), (cmpt_of vae_demo_image "C").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers vae_demo_link_cfg.
  all: try (exists vae_C_adv_entry, 0%nat; split; [|exists vae_C_g_entry, 0%nat; split_and!]).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /vae_demo_state /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [vae_demo_state] runs to [Halted], and [vae_adequacy] applies to it:
    the flag of the assert library is still zero. *)
Theorem vae_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Exec], vae_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt vae_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct (N.to_nat 15000%N) Executable vae_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [ [ [ [ [pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (vae_adequacy _ _ _ _ vae_demo_ok Hrun).
Qed.
