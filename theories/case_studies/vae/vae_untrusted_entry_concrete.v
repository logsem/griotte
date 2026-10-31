From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  switcher assert allocator_resources compartment_layout
  vae vae_concrete vae_untrusted_entry_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link
  vae_untrusted_entry_firmware.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the very awkward example, thread starting in the adversary

    The firmware [vae_untrusted_entry_firmware] with [vae_concrete]'s
    adversary, laid out by the linker. The thread starts at the adversary's
    [adv]. [adv] calls [awkward] with its callback [g], then returns, and
    the switcher exits the thread. The initial state satisfies
    [vae_untrusted_entry_initial_state_ok] by computation, runs to [Halted],
    and [vae_untrusted_entry_adequacy] applies to it. *)

(** ** The linked image and its initial state *)

Definition vae_untrusted_entry_demo_image : fw_image :=
  Eval vm_compute in
    default (place vae_demo_link_cfg vae_untrusted_entry_firmware).1
      (link vae_demo_link_cfg vae_untrusted_entry_firmware).

Lemma vae_untrusted_entry_demo_linked :
  link vae_demo_link_cfg vae_untrusted_entry_firmware = Some vae_untrusted_entry_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition vae_untrusted_entry_demo_state : ExecConf :=
  img_state vae_untrusted_entry_firmware vae_untrusted_entry_demo_image.

(** The entry word of [adv], as the linker writes it: no argument, no
    minimum stack, at [adv]'s offset. *)
Definition vae_untrusted_entry_adv_word : Z :=
  encode_entry_point InterruptEnabled 0 0 (Z.of_nat vae_C_adv_entry).

Lemma vae_untrusted_entry_demo_ok :
  vae_untrusted_entry_initial_state_ok
    (flag_assert (img_asrt vae_untrusted_entry_demo_image)) vae_untrusted_entry_demo_state.
Proof.
  rewrite /vae_untrusted_entry_initial_state_ok.
  exists (img_sw vae_untrusted_entry_demo_image), (img_asrt vae_untrusted_entry_demo_image),
    (thread_of vae_untrusted_entry_demo_image 0),
    (cmpt_of vae_untrusted_entry_demo_image "main"), (cmpt_of vae_untrusted_entry_demo_image "C").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers vae_demo_link_cfg.
  all: try (exists vae_C_adv_entry, 0%nat; split; [|exists vae_C_g_entry, 0%nat; split_and!]).
  (* The entry word of [adv]: the PC and the minimum stack *)
  all: try (lazymatch goal with
            | |- ∃ z : Z, cmpt_exp_tbl_entries _ !! _ = Some (WInt z) ∧ _ =>
                exists vae_untrusted_entry_adv_word; split
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ =>
                rewrite /vae_untrusted_entry_demo_state /img_state /img_regs;
                solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [vae_untrusted_entry_demo_state] runs to [Halted], and
    [vae_untrusted_entry_adequacy] applies to it: the flag of the assert
    library is still zero. *)
Theorem vae_untrusted_entry_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Exec], vae_untrusted_entry_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt vae_untrusted_entry_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct (N.to_nat 15000%N) Executable vae_untrusted_entry_demo_state
                Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [ [ [ [ [pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (vae_untrusted_entry_adequacy _ _ _ _ vae_untrusted_entry_demo_ok Hrun).
Qed.
