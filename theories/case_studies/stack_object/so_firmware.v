From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (tools/prints/). *)
From griotte Require Export stack_object.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The firmware of the stack object case study and its initial-state predicate *)

(** The main compartment calls the adversary [C], which imports the
    export [f] of [main] and its own export [g]. The function [f] takes a
    stack object [in] of its caller and a callback [g]; it checks that [in]
    is readable, does not overlap its own stack frame and holds integers
    only, pushes a secret on its stack frame, allocates a public stack
    object, and calls [g] with both objects; it then asserts that the
    secret is intact. [C] exports two entries: [adv], taking no argument,
    and [g], taking two. [main] has two exports: [f], called by [C], and
    [entry], where the thread starts, after its three imports. *)
Definition so_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "C" "adv"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := so_main_code;
         tb_data    := [
           FWs so_main_data
         ];
         tb_exports := [
           (* after the 3 imports and the 8 words of [run]; the stack holds the
              secret, [z] and the spill of the call to [g] *)
           {| fe_name := "f";     fe_offset := 11; fe_nargs := 2; fe_min_stack := 6; fe_posture := InterruptEnabled |};
           (* after the 3 imports; the stack holds the spill of the switcher call *)
           {| fe_name := "entry"; fe_offset := 3; fe_nargs := 0; fe_min_stack := 4; fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "C";
       fc_imports       := [
         ISwitcherCall;
         IExport "main" "f";
         IExport "C" "g"
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "C";
         ub_exports := [
           {| ue_name := "adv"; ue_nargs := 0 |};
           {| ue_name := "g";   ue_nargs := 2 |}
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

(** The image of the stack object firmware, from the records of its
    sections. *)
Definition so_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main C sched : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("C", C); ("sched", sched)] [t0] idle boot.

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition so_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main C sched : img_cmpt),
    fw_start [] so_firmware (so_img sw asrt t0 idle boot main C sched) flag σ.

(** The predicate, computed from [so_start], with its comments. *)
Definition so_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@so_start MP) [so_firmware; so_img]).

(** The initial-state predicate of the stack object case study: the
    annotated one without its comments. *)
Definition so_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@so_initial_state_ok_annot MP)).

Lemma so_initial_state_ok_start `{MP : MachineParameters} flag σ :
  so_initial_state_ok flag σ → so_start flag σ.
Proof. initial_state_conv. Qed.
