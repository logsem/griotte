From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  switcher assert allocator_resources compartment_layout
  deep_locality deep_locality_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link dle_firmware.
Set Mangle Names.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the deep-locality case study

    The deep-locality firmware with a concrete adversary [C], laid out by
    the linker. Its initial state satisfies [dle_initial_state_ok] by
    computation, runs to [Halted], and [dle_adequacy] applies to it. *)

Definition dle_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary examines the argument passed in [ca0]. If it is a
    capability, the adversary follows it to the nested capability and attempts
    to overwrite the nested address with [7]; otherwise it simply returns. This
    instantiates the unknown compartment with a direct attack on deep locality.
    It has one zeroed global, and its entry point right after its import. *)
Definition dle_C_code : list Word :=
  encodeInstrsW [
    GetWType ct0 ca0;
    Sub ct0 ct0 (encodeWordType wt_cap);
    Jnz 3%Z ct0;
    CLoad ct0 ca0 0;
    Store ct0 7%Z 0;
    Jalr cnull cra
  ].

Definition dle_C_data : list Word := [WInt 0].

Definition dle_demo_link_cfg : link_cfg :=
  MkLinkCfg 16 dle_switcher_sealing_type
    [("C", MkLinkAdv dle_C_code dle_C_data [1])].

(** ** The linked image and its initial state *)

Definition dle_demo_image : fw_image :=
  Eval vm_compute in
    default (place dle_demo_link_cfg dle_firmware).1
      (link dle_demo_link_cfg dle_firmware).

Lemma dle_demo_linked :
  link dle_demo_link_cfg dle_firmware = Some dle_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition dle_demo_state : ExecConf := img_state dle_firmware dle_demo_image.

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma dle_demo_ok :
  dle_initial_state_ok (img_sw dle_demo_image) (img_asrt dle_demo_image)
    (thread_of dle_demo_image 0) (cmpt_of dle_demo_image "main")
    (cmpt_of dle_demo_image "C") dle_demo_state.
Proof.
  rewrite /dle_initial_state_ok.
  split_and!.
  all: try (exists 1%nat; split_and!).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /dle_demo_state /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [dle_demo_state] runs to [Halted], and [dle_adequacy] applies to it:
    the flag of the assert library is still zero. Fuel 3000 does not
    suffice; 5000 reaches [Halted]. *)
Theorem dle_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Seq (Instr Executable)], dle_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt dle_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct 5000 Executable dle_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[[[pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (dle_adequacy _ _ _ _ _ _ _ _ dle_demo_ok Hrun).
Qed.
