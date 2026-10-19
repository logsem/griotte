From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  switcher assert allocator_resources compartment_layout
  kvs kvs_main kvs_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link kvs_firmware.
Set Mangle Names.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the KVS case study

    The KVS firmware with concrete sealing types and user keys, and a
    concrete adversary [B], laid out by the linker. Its initial state
    satisfies [kvs_initial_state_ok] by computation, runs to [Halted], and
    [kvs_adequacy] applies to it. *)

Definition kvs_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.
Definition kvs_service_sealing_type : OType := @finz.FinZ ONum 10 eq_refl eq_refl.

(** The firmware, with the user keys [1] (main) and [2] (B). *)
Definition kvs_demo_firmware : firmware := kvs_firmware kvs_service_sealing_type 1 2.

(** The adversary [B]: the code of [kvs_B_asm], one zeroed global, and its
    entry point. *)
Definition kvs_B_code : list Word := encodeInstrsW kvs_B_instrs.
Definition kvs_B_data : list Word := [WInt 0].

Definition kvs_demo_link_cfg : link_cfg :=
  MkLinkCfg 16 kvs_switcher_sealing_type
    [("B", MkLinkAdv kvs_B_code kvs_B_data [kvs_B_adv_entry])].

(** ** The linked image and its initial state *)

Definition kvs_demo_image : fw_image :=
  Eval vm_compute in
    default (place kvs_demo_link_cfg kvs_demo_firmware).1
      (link kvs_demo_link_cfg kvs_demo_firmware).

Lemma kvs_demo_linked :
  link kvs_demo_link_cfg kvs_demo_firmware = Some kvs_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition kvs_demo_state : ExecConf := img_state kvs_demo_firmware kvs_demo_image.

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma kvs_demo_ok :
  kvs_initial_state_ok (flag_assert (img_asrt kvs_demo_image)) kvs_demo_state.
Proof.
  rewrite /kvs_initial_state_ok.
  exists (img_sw kvs_demo_image), (img_asrt kvs_demo_image), (thread_of kvs_demo_image 0),
    (cmpt_of kvs_demo_image "main"), (cmpt_of kvs_demo_image "kvs"), (cmpt_of kvs_demo_image "B"),
    kvs_service_sealing_type, 1%Z, 2%Z.
  split; first done.
  split_and!.
  all: try (exists kvs_B_adv_entry; split_and!).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /kvs_demo_state /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [kvs_demo_state] runs to [Halted], and [kvs_adequacy] applies to it:
    the flag of the assert library is still zero. *)
Theorem kvs_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Seq (Instr Executable)], kvs_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt kvs_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct (N.to_nat 15000%N) Executable kvs_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[[[pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (kvs_adequacy _ _ _ _ kvs_demo_ok Hrun).
Qed.
