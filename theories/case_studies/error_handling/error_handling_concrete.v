From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  assembler fetch switcher assert allocator_resources compartment_layout
  error_handling error_handling_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link error_handling_firmware.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the error-handling case study

    The error-handling firmware with a concrete adversary [adv], laid out
    by the linker. Its initial state satisfies
    [error_handling_initial_state_ok] by computation, and runs to [Halted];
    [error_handling_adequacy] gives that the flag of the assert library is
    still zero. *)

Definition error_handling_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** ** The concrete adversary

    [adv] saves its outer return capability and keeps an integer object
    ([ADV_OBJ]) in its frame, then calls [stats_read] four times through
    the switcher:
    - with an untagged copy of its [cgp]: the load of [stats_read] faults,
      and the error handler of [stats] releases the lock and unwinds the
      call;
    - with its [cgp];
    - with a Local capability to its object, one past its end: the handler
      moves it back to its base, outside its [ErrorState], and the retried
      load returns [ADV_OBJ], which [adv] stores in its second global;
    - with a capability whose base is the first word of the [ErrorState]
      slot of [stats_read], one past its end: the handler does not repair
      it (the retried load would read the saved context) and unwinds the
      call; [adv] stores the result, [ECOMPARTMENTFAIL], in its third
      global.
    It then restores its return capability and returns to the caller. Its
    stackful error handler, which follows, asks for the unwind (it returns
    1, ForceUnwind); it does not run in the demo, where [adv] does not
    fault. The code is assembled here, away from the program logic's
    coercions. *)
Section error_handling_adv_code.
  Context `{MP: MachineParameters}.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.

  (** The integer object of [adv], in its frame at [csp + 1]. *)
  Definition ADV_OBJ : Z := 7.

  (** How far below [adv]'s [csp] cursor the [ErrorState] slot of its
      callee [stats_read] starts: the switcher's spill, the reserved space
      of the entry, and the [ErrorState] itself. *)
  Definition adv_slot_depth : Z :=
    SpillSlot_size + StackEntry_reserved_space + ErrorState_size.

  Definition error_handling_adv_asm : list asm_code :=
    [ #@".Limport_switcher";
      #@".Limport_stats_read";
      #".Ladv";
      lea csp csp (-2);
      store csp cra;
      store_imm csp ADV_OBJ 1;
      cleartag ca0 cgp ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_stats_read" ct1 ++
    [ jalr cra ct0;
      mov ca0 cgp ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_stats_read" ct1 ++
    [ jalr cra ct0;
      (* the object $[csp + 1, csp + 2)$, one past its end *)
      geta ct2 csp;
      add ct2 ct2 1;
      add ctp ct2 1;
      subseg ca0 csp ct2 ctp;
      seta ca0 ca0 ctp ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_stats_read" ct1 ++
    [ jalr cra ct0;
      store_imm cgp ca0 1;
      (* the first word of the callee's [ErrorState] slot, one past it *)
      geta ct2 csp;
      add ct2 ct2 (- adv_slot_depth);
      add ctp ct2 1;
      subseg ca0 csp ct2 ctp;
      seta ca0 ca0 ctp ] ++
    fetch_asm ".Limport_switcher" ct0 ++
    fetch_asm ".Limport_stats_read" ct1 ++
    [ jalr cra ct0;
      store_imm cgp ca0 2;
      load cra csp;
      lea csp csp 2;
      mov ca0 0;
      mov ca1 0;
      ret;
      #".Ladv_handler";
      mov ca0 1;
      ret ].

  Definition error_handling_adv_instrs : list instr :=
    Eval compute in assemble error_handling_adv_asm.
  Lemma error_handling_adv_assembles : asm_ok (assemble_check error_handling_adv_asm).
  Proof. asm_check. Qed.

  (** The offsets of the entry [.Ladv] and of the handler [.Ladv_handler]
      from the start of the PCC, after the two imports. *)
  Definition error_handling_adv_entry_off : nat :=
    Eval vm_compute in label_offset error_handling_adv_asm ".Ladv".
  Definition error_handling_adv_handler_off : nat :=
    Eval vm_compute in label_offset error_handling_adv_asm ".Ladv_handler".
End error_handling_adv_code.

Definition error_handling_adv_code : list Word := encodeInstrsW error_handling_adv_instrs.

(** The globals of [adv]: the word that its second call reads, and the
    results of its last two calls. *)
Definition error_handling_adv_data : list Word := [WInt 0; WInt 0; WInt 0].

Definition error_handling_demo_link_cfg : link_cfg := {|
  lk_base        := 16;
  lk_ot_switcher := error_handling_switcher_sealing_type;
  lk_adv         := [
    ("adv", {| la_code    := error_handling_adv_code;
               la_data    := error_handling_adv_data;
               la_exports := [
                 error_handling_adv_entry_off
               ];
               la_handler := Z.of_nat error_handling_adv_handler_off;
               la_handler_stackless := ExportTable_no_handler |})
  ]
|}.

(** ** The linked image and its initial state *)

Definition error_handling_demo_image : fw_image :=
  Eval vm_compute in
    default (place error_handling_demo_link_cfg error_handling_firmware).1
      (link error_handling_demo_link_cfg error_handling_firmware).

Lemma error_handling_demo_linked :
  link error_handling_demo_link_cfg error_handling_firmware = Some error_handling_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition error_handling_demo_state : ExecConf :=
  img_state error_handling_firmware error_handling_demo_image.

Ltac solve_other_registers :=
  intros r Hr; cbn [pcc reg sreg mem shadowtbl fst snd];
  rewrite !lookup_insert_ne; try set_solver;
  apply lookup_gset_to_gmap_Some; split; [apply all_registers_s_correct | done].

Lemma error_handling_demo_ok :
  error_handling_initial_state_ok (flag_assert (img_asrt error_handling_demo_image))
    error_handling_demo_state.
Proof.
  rewrite /error_handling_initial_state_ok.
  exists (img_sw error_handling_demo_image), (img_asrt error_handling_demo_image),
    (thread_of error_handling_demo_image 0),
    (cmpt_of error_handling_demo_image "main"), (cmpt_of error_handling_demo_image "stats"),
    (cmpt_of error_handling_demo_image "adv").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers error_handling_demo_link_cfg.
  all: try (exists error_handling_adv_entry_off, 0%nat; split_and!).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /error_handling_demo_state /img_state /img_regs;
                           solve_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [error_handling_demo_state] runs to [Halted], at the switcher's thread
    exit after [main] returns, and [error_handling_adequacy] applies to it: the flag of the
    assert library is still zero. [error_handling_demo_adv_results] shows
    the results of [adv]'s last two calls. *)
Theorem error_handling_runs_and_gracefully_halts :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Exec], error_handling_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt error_handling_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct (N.to_nat 15000%N) Executable error_handling_demo_state Halted)
    as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [ [ [ [ [pc' reg'] sreg'] mem'] sh'] Hrun].
  exists pc', reg', sreg', mem', sh'. split; first exact Hrun.
  exact (error_handling_adequacy _ _ _ _ error_handling_demo_ok Hrun).
Qed.

(** The globals of [adv] in the demo. *)
Definition error_handling_demo_adv_cgp : Addr :=
  cmpt_b_cgp (cmpt_of error_handling_demo_image "adv").

(** The two calls of [adv] that showcase the slot check: the repaired
    Local pointer returned [ADV_OBJ], stored in [adv]'s second global, and
    the pointer into the [ErrorState] slot was unwound, [ECOMPARTMENTFAIL]
    stored in its third. *)
Remark error_handling_demo_adv_results :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Exec], error_handling_demo_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! (error_handling_demo_adv_cgp ^+ 1) = Some (WInt ADV_OBJ)
    ∧ mem' !! (error_handling_demo_adv_cgp ^+ 2) = Some (WInt ECOMPARTMENTFAIL).
Proof.
  pose proof (machine_run_conf_correct (N.to_nat 15000%N) Executable
                error_handling_demo_state) as Hrun.
  assert (match machine_run_conf (N.to_nat 15000%N) (Executable, error_handling_demo_state)
          with
          | Some (Halted, (_, _, _, mem', _)) =>
              mem' !! (error_handling_demo_adv_cgp ^+ 1) = Some (WInt ADV_OBJ) ∧
              mem' !! (error_handling_demo_adv_cgp ^+ 2) = Some (WInt ECOMPARTMENTFAIL)
          | _ => False
          end) as Hres by (vm_compute; split; reflexivity).
  destruct (machine_run_conf _ _) as [ [ [] [ [ [ [pc' reg'] sreg'] mem'] sh'] ] | ];
    try done.
  exists pc', reg', sreg', mem', sh'. split; [by apply Hrun | exact Hres].
Qed.

(** ** Without the error handler

    The same firmware and adversary, where [stats] declares no error
    handler. The fault of [stats_read], in the first call of [adv], then
    unwinds [stats] with its lock held: the first call of [main] returns
    [EBUSY], its first assert fails, and the machine halts with the flag
    set.

    [machine_run_conf], rather than [machine_run], returns the final
    configuration, so that the final memory computes. *)

(** [stats] without its error handler. *)
Definition error_handling_drop_stats_handler (fc : fw_cmpt) : fw_cmpt :=
  match fc_body fc with
  | TrustedBody b =>
      if String.eqb (fc_name fc) "stats" then
        MkFwCmpt (fc_name fc) (fc_imports fc) (fc_static_sealed fc)
          (TrustedBody (MkFwTrusted (tb_code b) (tb_data b) (tb_exports b) None
                          (tb_error_handler_stackless b)))
      else fc
  | UntrustedBody _ => fc
  end.

Definition error_handling_no_handler_firmware : firmware :=
  MkFirmware (map error_handling_drop_stats_handler (fw_cmpts error_handling_firmware))
    (fw_threads error_handling_firmware) (fw_otypes error_handling_firmware)
    (fw_heap_roots error_handling_firmware).

Definition error_handling_no_handler_image : fw_image :=
  Eval vm_compute in
    default (place error_handling_demo_link_cfg error_handling_no_handler_firmware).1
      (link error_handling_demo_link_cfg error_handling_no_handler_firmware).

Definition error_handling_no_handler_state : ExecConf :=
  img_state error_handling_no_handler_firmware error_handling_no_handler_image.

Remark error_handling_no_handler_assert_fails :
  ∃ pc' reg' sreg' mem' sh',
    rtc erased_step ([Exec], error_handling_no_handler_state)
      ([Instr Halted], (pc', reg', sreg', mem', sh'))
    ∧ mem' !! flag_assert (img_asrt error_handling_no_handler_image) = Some (WInt 1%Z).
Proof.
  pose proof (machine_run_conf_correct (N.to_nat 15000%N) Executable
                error_handling_no_handler_state) as Hrun.
  assert (match machine_run_conf (N.to_nat 15000%N) (Executable, error_handling_no_handler_state)
          with
          | Some (Halted, (_, _, _, mem', _)) =>
              mem' !! flag_assert (img_asrt error_handling_no_handler_image) = Some (WInt 1%Z)
          | _ => False
          end) as Hflag by (vm_compute; reflexivity).
  destruct (machine_run_conf _ _) as [ [ [] [ [ [ [pc' reg'] sreg'] mem'] sh'] ] | ];
    try done.
  exists pc', reg', sreg', mem', sh'. split; [by apply Hrun | exact Hflag].
Qed.
