From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  switcher assert allocator_resources compartment_layout
  stack_object stack_object_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link so_firmware.
Set Mangle Names.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the stack object case study

    The stack object firmware with a concrete adversary [C], laid out by
    the linker. Its initial state satisfies [so_initial_state_ok] by
    computation, runs to [Halted], and [so_adequacy] applies to it. *)

Definition so_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary allocates and initializes a one-word public object
    on its stack, then calls the main function with that object and callback
    [g]. The main function allocates a second public stack object and passes
    both capabilities to [g], which attempts to overwrite them with [7] and
    [9]. After the call, the adversary restores its stack and return capability
    before returning to the main program. It has one zeroed global, and its
    entry points [adv_entry] and [g_entry]. *)
Definition so_C_code : list Word := encodeInstrsW so_C_instrs.

Definition so_C_data : list Word := [WInt 0].

Definition so_demo_link_cfg : link_cfg := {|
  lk_base        := 16;
  lk_ot_switcher := so_switcher_sealing_type;
  lk_adv         := [
    ("C", {| la_code    := so_C_code;
             la_data    := so_C_data;
             la_exports := [
               so_C_adv_entry;
               so_C_g_entry
             ] |})
  ]
|}.

(** ** The linked image and its initial state *)

Definition so_demo_image : fw_image :=
  Eval vm_compute in
    default (place so_demo_link_cfg so_firmware).1
      (link so_demo_link_cfg so_firmware).

Lemma so_demo_linked :
  link so_demo_link_cfg so_firmware = Some so_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition so_demo_state : ExecConf := img_state so_firmware so_demo_image.

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma so_demo_ok :
  so_initial_state_ok (flag_assert (img_asrt so_demo_image)) so_demo_state.
Proof.
  rewrite /so_initial_state_ok.
  exists (img_sw so_demo_image), (img_asrt so_demo_image), (thread_of so_demo_image 0),
    (cmpt_of so_demo_image "main"), (cmpt_of so_demo_image "C").
  split; first done.
  split_and!.
  all: try (exists so_C_adv_entry, 0%nat; split; [|exists so_C_g_entry, 0%nat; split_and!]).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /so_demo_state /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [so_demo_state] runs to [Halted], and [so_adequacy] applies to it:
    the flag of the assert library is still zero. *)
Theorem so_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Seq (Instr Executable)], so_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt so_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct 7000 Executable so_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[[[pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (so_adequacy _ _ _ _ so_demo_ok Hrun).
Qed.
