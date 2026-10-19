From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  switcher assert allocator_resources compartment_layout
  kvs kvs_main kvs_adequacy kvs_concrete.
From griotte Require Import image firmware firmware_ok image_state link print kvs_firmware.
Set Mangle Names.

#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * Checks of the KVS predicate on concrete images

    The images of the concrete KVS instance satisfy [kvs_initial_state_ok]
    with their initial states, by computation. *)

#[local] Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).

(** ** The layout of the concrete KVS instance

    The addresses of [kvs_concrete], except for the export table of [main],
    which now holds the entry of the thread: it moves to [[109, 112)], which
    is free, since its old place [[113, 115)] has no room for an entry. *)

Definition kvs_head_sw : img_switcher :=
  MkImgSwitcher kvs_switcher_b kvs_switcher_e kvs_switcher_call kvs_switcher_return
    kvs_switcher_sealing_type.

Definition kvs_head_asrt : img_assert :=
  MkImgAssert kvs_assert_b kvs_assert_e kvs_assert_cap kvs_assert_flag.

Definition kvs_head_t0 : img_thread :=
  MkImgThread kvs_stack_b kvs_stack_e kvs_trusted_stack_b kvs_trusted_stack_e.

Definition kvs_head_main_entry : Word :=
  WInt (encode_entry_point InterruptEnabled 0 7).

Definition kvs_head_main : img_cmpt :=
  MkImgCmpt kvs_main_pcc_b kvs_main_code_start kvs_main_pcc_e
    kvs_main_data_b kvs_main_data_e
    kvs_main_static_sealed_b kvs_main_static_sealed_e
    (A 109) (A 110) (A 111) (A 112)
    kvs_main_imports_concrete kvs_main_code kvs_main_data
    kvs_main_static_sealed_concrete [kvs_head_main_entry].

Definition kvs_head_kvs : img_cmpt :=
  MkImgCmpt kvs_KVS_pcc_b kvs_KVS_code_start kvs_KVS_pcc_e
    kvs_KVS_data_b kvs_KVS_data_e kvs_KVS_data_e kvs_KVS_data_e
    kvs_KVS_exports_pcc kvs_KVS_exports_cgp
    kvs_KVS_exports_entries_b kvs_KVS_exports_entries_e
    kvs_KVS_imports kvs_service_instrs kvs_data [] kvs_export_table_entries.

Definition kvs_head_B : img_cmpt :=
  MkImgCmpt kvs_B_pcc_b kvs_B_code_start kvs_B_pcc_e
    kvs_B_data_b kvs_B_data_e
    kvs_B_static_sealed_b kvs_B_static_sealed_e
    kvs_B_exports_pcc kvs_B_exports_cgp
    kvs_B_exports_entries_b kvs_B_exports_entries_e
    kvs_B_imports kvs_B_code kvs_B_data kvs_B_static_sealed kvs_B_exports.

(** The initial state of [kvs_concrete], with the export table of [main]
    moved and holding the entry, and the entry frame of the trusted stack
    ([[4119, 4122)]) holding the stack and the export table of [main]. *)
Definition kvs_head_memory : Mem :=
  <[A 4119 := WCap true RWL Local kvs_stack_b kvs_stack_e kvs_stack_b]>
    (<[A 4120 := WCap true RW Global (A 109) (A 112) (A 109)]>
       (<[A 109 := WCap true RX Global kvs_main_pcc_b kvs_main_pcc_e kvs_main_pcc_b]>
          (<[A 110 := WCap true RW Global kvs_main_data_b kvs_main_data_e kvs_main_data_b]>
             (<[A 111 := kvs_head_main_entry]>
                (delete (A 113) (delete (A 114) kvs_initial_memory)))))).

Definition kvs_head_state : ExecConf :=
  (kvs_initial_pc, kvs_initial_registers, kvs_initial_sregisters, kvs_head_memory,
   initial_heap_shadow).

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma kvs_head_state_ok :
  kvs_initial_state_ok kvs_head_sw kvs_head_asrt kvs_head_t0
    kvs_head_main kvs_head_kvs kvs_head_B kvs_service_sealing_type 1 2 kvs_head_state.
Proof.
  rewrite /kvs_initial_state_ok.
  split_and!.
  all: try (exists kvs_B_adv_entry; split_and!).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /kvs_head_state /kvs_initial_registers; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** [kvs_head_state] runs to [Halted], and [kvs_adequacy] applies to it:
    the flag of the assert library is still zero. *)
Theorem kvs_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Seq (Instr Executable)], kvs_head_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! kvs_assert_flag = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct (N.to_nat 15000%N) Executable kvs_head_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[[[pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (kvs_adequacy _ _ _ _ _ _ _ _ _ _ _ _ kvs_head_state_ok Hrun).
Qed.

(** The state of the image, as the loader builds it, is the same. *)
Lemma kvs_head_img_state_ok :
  kvs_initial_state_ok kvs_head_sw kvs_head_asrt kvs_head_t0
    kvs_head_main kvs_head_kvs kvs_head_B kvs_service_sealing_type 1 2
    (img_state (kvs_firmware kvs_service_sealing_type 1 2)
       (kvs_img kvs_head_sw kvs_head_asrt kvs_head_t0 kvs_head_main kvs_head_kvs kvs_head_B)).
Proof.
  rewrite /kvs_initial_state_ok.
  split_and!.
  all: try (exists kvs_B_adv_entry; split_and!).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** A linked image *)

Definition kvs_link_cfg : link_cfg :=
  MkLinkCfg 16 kvs_switcher_sealing_type
    [("B", MkLinkAdv kvs_B_code kvs_B_data [kvs_B_adv_entry])].

Definition kvs_linked : fw_image :=
  Eval vm_compute in
    default (MkFwImage kvs_head_sw kvs_head_asrt [] [])
      (link kvs_link_cfg (kvs_firmware kvs_service_sealing_type 1 2)).

Definition kvs_linked_state : ExecConf :=
  img_state (kvs_firmware kvs_service_sealing_type 1 2) kvs_linked.

Lemma kvs_linked_ok :
  kvs_initial_state_ok (img_sw kvs_linked) (img_asrt kvs_linked) (thread_of kvs_linked 0)
    (cmpt_of kvs_linked "main") (cmpt_of kvs_linked "kvs") (cmpt_of kvs_linked "B")
    kvs_service_sealing_type 1 2 kvs_linked_state.
Proof.
  rewrite /kvs_initial_state_ok.
  split_and!.
  all: try (exists kvs_B_adv_entry; split_and!).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /kvs_linked_state /img_state /img_regs; solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** Printing the linked image *)

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Import FwMapNotations.
#[local] Open Scope Z_scope.

Ltac2 Eval print_memory_map constr:(kvs_linked).
