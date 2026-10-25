From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (prints/). *)
From griotte Require Export error_handling.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The firmware of the error-handling case study and its initial-state predicate *)

(** The main compartment calls the adversary [adv], then [stats_read] of
    [stats] with an untagged capability to its global [x], then with the
    capability of [x]. [adv] imports [stats_read]. [stats] has no import;
    its stackful error handler follows the code of [stats_read]. The thread
    starts at the export [entry] of [main], after its four imports. *)
Definition error_handling_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "adv" "adv";
         IExport "stats" "stats_read"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := error_handling_main_code;
         tb_data    := [
           FWs error_handling_main_data
         ];
         tb_exports := [
           {| fe_name := "entry"; fe_offset := error_handling_main_entry_pcc_off; fe_nargs := error_handling_main_entry_nargs; fe_min_stack := error_handling_main_entry_min_stack; fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "stats";
       fc_imports       := [];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := stats_code;
         tb_data    := [
           FWs stats_data
         ];
         tb_exports := [
           {| fe_name := "stats_read"; fe_offset := stats_read_pcc_off; fe_nargs := stats_read_nargs; fe_min_stack := stats_read_min_stack; fe_posture := InterruptDisabled |}
         ];
         tb_error_handler := Some stats_handler_pcc_off;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "adv";
       fc_imports       := [
         ISwitcherCall;
         IExport "stats" "stats_read"
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "adv";
         ub_exports := [
           {| ue_name := "adv"; ue_nargs := 0 |}
         ] |} |}
  ];
  fw_threads    := [
    {| ft_cmpt := "main"; ft_entry := "entry"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the error-handling firmware, from the records of its
    sections. *)
Definition error_handling_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main stats adv : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("stats", stats); ("adv", adv)] [t0].

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition error_handling_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main stats adv : img_cmpt),
    fw_start [] error_handling_firmware (error_handling_img sw asrt t0 main stats adv) flag σ.

(** The predicate, computed from [error_handling_start], with its comments.
    The offset of the entry of the thread is unfolded, so that the initial
    PC computes. *)
Definition error_handling_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@error_handling_start MP)
          [error_handling_firmware; error_handling_img; error_handling_main_entry_pcc_off]).

(** The initial-state predicate of the error-handling case study: the
    annotated one without its comments. *)
Definition error_handling_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@error_handling_initial_state_ok_annot MP)).

Lemma error_handling_initial_state_ok_start `{MP : MachineParameters} flag σ :
  error_handling_initial_state_ok flag σ → error_handling_start flag σ.
Proof. initial_state_conv. Qed.
