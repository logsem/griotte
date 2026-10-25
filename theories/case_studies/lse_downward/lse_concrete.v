From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  switcher assert allocator_resources compartment_layout
  lse lse_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link lse_firmware.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the LSE downward case study

    The LSE downward firmware with a concrete adversary [C], laid out by
    the linker. Its initial state satisfies [lse_initial_state_ok] by
    computation, runs to [Halted], and [lse_adequacy] applies to it. *)

Definition lse_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary saves its outer return capability, fetches the
    switcher and the exported main function, and calls the function twice. It
    deliberately fetches both imports again before the second call, then
    restores its return capability and returns to the caller. It has one
    zeroed global, and its entry point right after its two imports. *)
Definition lse_C_code : list Word := encodeInstrsW lse_C_instrs.

Definition lse_C_data : list Word := [WInt 0].

Definition lse_demo_link_cfg : link_cfg := {|
  lk_base        := 16;
  lk_ot_switcher := lse_switcher_sealing_type;
  lk_adv         := [
    ("C", {| la_code    := lse_C_code;
             la_data    := lse_C_data;
             la_exports := [
               2  (* after the 2 imports *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ]
|}.

(** ** The linked image and its initial state *)

Definition lse_demo_image : fw_image :=
  Eval vm_compute in
    default (place lse_demo_link_cfg lse_firmware).1
      (link lse_demo_link_cfg lse_firmware).

Lemma lse_demo_linked :
  link lse_demo_link_cfg lse_firmware = Some lse_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition lse_demo_state : ExecConf := img_state lse_firmware lse_demo_image.

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma lse_demo_ok :
  lse_initial_state_ok (flag_assert (img_asrt lse_demo_image)) lse_demo_state.
Proof.
  rewrite /lse_initial_state_ok.
  exists (img_sw lse_demo_image), (img_asrt lse_demo_image), (thread_of lse_demo_image 0),
    (cmpt_of lse_demo_image "main"), (cmpt_of lse_demo_image "C").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers lse_demo_link_cfg.
  all: try (exists 2%nat, 0%nat; split_and!).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /lse_demo_state /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [lse_demo_state] runs to [Halted], and [lse_adequacy] applies to it:
    the flag of the assert library is still zero. *)
Theorem lse_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Seq (Instr Executable)], lse_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt lse_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct (N.to_nat 7500%N) Executable lse_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[[[pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (lse_adequacy _ _ _ _ lse_demo_ok Hrun).
Qed.
