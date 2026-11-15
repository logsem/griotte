From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (tools/prints/). *)
From griotte Require Export cmdc.
From griotte Require Import image firmware libraries firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The CMDC firmware with a second thread in [C], and its initial-state predicate *)

(** The CMDC firmware with a second thread in [C]. The thread 0 is the
    CMDC case study's: the main compartment calls the adversary [B], then
    the adversary [C], passing each a capability to one of its globals, and
    checks after each call that the other global was not modified. The
    thread 1 starts at the export [adv] of [C], so that [C] runs on two
    threads; [C] imports the switcher only and never gets a capability to
    the global of [main] given to [B]. *)
Definition cmdc_shared_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         ILibCall "assert" "assert";
         IExport "B" "f";
         IExport "C" "g"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := cmdc_main_code;
         tb_data    := [
           FWs cmdc_main_data
         ];
         tb_exports := [
           (* after the 4 imports; the stack holds the spill of the switcher calls *)
           {| fe_name := "entry"; fe_offset := 4; fe_nargs := 0; fe_min_stack := 4; fe_posture := InterruptEnabled |}
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
           {| ue_name := "f"; ue_nargs := cmdc_B_f_args |}
         ] |} |};
    {| fc_name          := "C";
       fc_imports       := [
         ISwitcherCall
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "C";
         ub_exports := [
           {| ue_name := "g"; ue_nargs := cmdc_C_g_args |};
           {| ue_name := "adv"; ue_nargs := 0 |}
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
  fw_libs       := [
    assert_lib
  ];
  fw_shared     := [
    assert_flag_object
  ];
  fw_threads    := [
    {| ft_cmpt := "main"; ft_entry := "entry"; ft_stack_size := 100; ft_tstack_frames := 24 |};
    {| ft_cmpt := "C"; ft_entry := "adv"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the firmware, from the records of its sections. *)
Definition cmdc_shared_img (sw : img_switcher) (assert : img_lib) (assert_flag : img_shared_object)
    (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main B C sched : img_cmpt) : fw_image :=
  MkFwImage sw [("assert", assert)] [("assert_flag", assert_flag)]
    [("main", main); ("B", B); ("C", C); ("sched", sched)]
    [t0; t1] idle boot.

(** The start of the firmware: some layout, with the assert flag at
    [flag], such that [σ] is the state the loader builds. *)
Definition cmdc_shared_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (assert : img_lib) (assert_flag : img_shared_object) (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main B C sched : img_cmpt),
    fw_start [] cmdc_shared_firmware
      (cmdc_shared_img sw assert assert_flag t0 t1 idle boot main B C sched) flag σ.

(** The predicate, computed from [cmdc_shared_start], with its comments. *)
Definition cmdc_shared_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@cmdc_shared_start MP) [cmdc_shared_firmware; cmdc_shared_img]).

(** The initial-state predicate of the CMDC firmware with a second thread
    in [C]: the annotated one without its comments. *)
Definition cmdc_shared_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@cmdc_shared_initial_state_ok_annot MP)).

Lemma cmdc_shared_initial_state_ok_start `{MP : MachineParameters} flag σ :
  cmdc_shared_initial_state_ok flag σ → cmdc_shared_start flag σ.
Proof. initial_state_conv. Qed.
