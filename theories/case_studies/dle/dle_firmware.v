From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (tools/prints/). *)
From griotte Require Export deep_locality.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The firmware of the deep-locality case study and its initial-state predicate *)

(** The main compartment calls the adversary [C] twice: first passing it a
    local capability with the deeply local permission [RW_DL] to one of its
    globals, which holds a capability to the other global, then, after
    writing [42] to the other global, passing it nothing; it then checks
    that the other global still holds [42]. [C] exports
    one entry [f], taking one argument, and imports the switcher only. The
    thread starts at the export [entry] of [main], after its three
    imports. *)
Definition dle_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "C" "f"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := dle_main_code;
         tb_data    := [
           FWs dle_main_data
         ];
         tb_exports := [
           (* after the 3 imports; the stack holds the spill of the switcher calls *)
           {| fe_name := "entry"; fe_offset := 3; fe_nargs := 0; fe_min_stack := 4; fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "C";
       fc_imports       := [
         ISwitcherCall
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "C";
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
    {| ft_cmpt := "main"; ft_entry := "entry"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the deep-locality firmware, from the records of its
    sections. *)
Definition dle_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main C sched : img_cmpt) : fw_image :=
  MkFwImage sw asrt default_img_locks [("main", main); ("C", C); ("sched", sched)] [t0] idle boot.

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition dle_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main C sched : img_cmpt),
    fw_start [] dle_firmware (dle_img sw asrt t0 idle boot main C sched) flag σ.

(** The predicate, computed from [dle_start], with its comments. *)
Definition dle_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@dle_start MP) [dle_firmware; dle_img]).

(** The initial-state predicate of the deep-locality case study: the
    annotated one without its comments. *)
Definition dle_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@dle_initial_state_ok_annot MP)).

Lemma dle_initial_state_ok_start `{MP : MachineParameters} flag σ :
  dle_initial_state_ok flag σ → dle_start flag σ.
Proof. initial_state_conv. Qed.
