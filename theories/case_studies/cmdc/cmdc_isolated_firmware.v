From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (tools/prints/). *)
From griotte Require Export cmdc.
From griotte Require Import image firmware libraries firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The CMDC firmware with an isolated thread, and its initial-state predicate *)

(** The CMDC firmware with a second thread. The thread 0 is the CMDC case
    study's: the main compartment calls the adversary [B], then the
    adversary [C], passing each a capability to one of its globals, and
    checks after each call that the other global was not modified. The
    thread 1 starts at the export [adv] of a third adversary [D], which
    imports the switcher only and which no compartment imports: it runs
    alone in [D]. [B], [C] and [D] each export one entry ([f], [g] and
    [adv]). *)
Definition cmdc_isolated_firmware `{MP : MachineParameters} : firmware := {|
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
           {| ue_name := "g"; ue_nargs := cmdc_C_g_args |}
         ] |} |};
    {| fc_name          := "D";
       fc_imports       := [
         ISwitcherCall
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "D";
         ub_exports := [
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
    {| ft_cmpt := "D"; ft_entry := "adv"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the firmware, from the records of its sections. *)
Definition cmdc_isolated_img (sw : img_switcher) (la : img_lib) (fo : img_shared_object)
    (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main B C D sched : img_cmpt) : fw_image :=
  MkFwImage sw [("assert", la)] [("assert_flag", fo)]
    [("main", main); ("B", B); ("C", C); ("D", D); ("sched", sched)]
    [t0; t1]
    idle boot.

(** The start of the firmware: some layout, with the assert flag at
    [flag], such that [σ] is the state the loader builds. *)
Definition cmdc_isolated_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (la : img_lib) (fo : img_shared_object) (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main B C D sched : img_cmpt),
    fw_start [] cmdc_isolated_firmware (cmdc_isolated_img sw la fo t0 t1 idle boot main B C D sched)
      flag σ.

(** The predicate, computed from [cmdc_isolated_start], with its comments. *)
Definition cmdc_isolated_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@cmdc_isolated_start MP) [cmdc_isolated_firmware; cmdc_isolated_img]).

(** The initial-state predicate of the CMDC firmware with an isolated
    thread: the annotated one without its comments. *)
Definition cmdc_isolated_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@cmdc_isolated_initial_state_ok_annot MP)).

Lemma cmdc_isolated_initial_state_ok_start `{MP : MachineParameters} flag σ :
  cmdc_isolated_initial_state_ok flag σ → cmdc_isolated_start flag σ.
Proof. initial_state_conv. Qed.
