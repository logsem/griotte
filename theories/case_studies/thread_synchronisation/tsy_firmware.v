From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (tools/prints/). *)
From griotte Require Export thread_synchronisation.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The firmware of the thread-synchronisation case study and its initial-state predicate *)

(** Two threads run the trusted [K]. The thread 0 starts at the export
    [run1]: it calls [B.f] with a capability to the global [b] of [K], then
    sets the global [flag] of [K] to [1] and exits. The thread 1 starts at
    the export [run2]: it waits until [flag] is [1], yielding, then writes
    [42] to [b] and checks that [b] still holds [42]. [B] exports [f],
    taking one argument, and imports the switcher only; it may keep the
    capability to [b] in its globals, but only the thread 0 runs in [B],
    and never after [flag] is set. Both exports of [K] run with interrupts
    enabled. *)
Definition tsy_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "K";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "B" "f"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := tsy_K_code;
         tb_data    := [
           FWs tsy_K_data
         ];
         tb_exports := [
           (* after the 3 imports; the stack holds the spill of the switcher call *)
           {| fe_name := "run1"; fe_offset := 3;  fe_nargs := 0; fe_min_stack := 4; fe_posture := InterruptEnabled |};
           (* no call: no stack *)
           {| fe_name := "run2"; fe_offset := 19; fe_nargs := 0; fe_min_stack := 0; fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "B";
       fc_imports       := [
         ISwitcherCall
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "B";
         ub_exports := [
           {| ue_name := "f"; ue_nargs := 1 |}
         ] |} |};
    {| fc_name          := "sched";
       fc_imports       := [
         ISwitcherCall;
         IMtime;
         IMtimecmp
       ];
       fc_static_sealed := [];
       fc_body          := SchedulerBody {|
         (* the exception entry after the 3 imports; the code is arbitrary *)
         sb_entry      := 3;
         sb_boot_stack := 16 |} |}
  ];
  fw_threads    := [
    {| ft_cmpt := "K"; ft_entry := "run1"; ft_stack_size := 100; ft_tstack_frames := 24 |};
    {| ft_cmpt := "K"; ft_entry := "run2"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the thread-synchronisation firmware, from the records of
    its sections. *)
Definition tsy_img (sw : img_switcher) (asrt : img_assert) (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (K B sched : img_cmpt) : fw_image :=
  MkFwImage sw asrt default_img_locks [("K", K); ("B", B); ("sched", sched)] [t0; t1] idle boot.

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition tsy_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (K B sched : img_cmpt),
    fw_start [] tsy_firmware (tsy_img sw asrt t0 t1 idle boot K B sched) flag σ.

(** The predicate, computed from [tsy_start], with its comments. *)
Definition tsy_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@tsy_start MP) [tsy_firmware; tsy_img]).

(** The initial-state predicate of the thread-synchronisation case study:
    the annotated one without its comments. *)
Definition tsy_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@tsy_initial_state_ok_annot MP)).

Lemma tsy_initial_state_ok_start `{MP : MachineParameters} flag σ :
  tsy_initial_state_ok flag σ → tsy_start flag σ.
Proof. initial_state_conv. Qed.
