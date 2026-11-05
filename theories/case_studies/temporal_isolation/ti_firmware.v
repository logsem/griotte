From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (tools/prints/). *)
From griotte Require Export temporal_isolation.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The firmware of the temporal-isolation case study and its initial-state predicate *)

(** Two threads share the adversary [B]. The thread 0 starts at the export
    [run] of the trusted [K]: it writes [0] to its global [b], calls
    [B.f] with a local capability to [b], then writes [42] to [b] and checks
    that [b] still holds [42]. The thread 1 starts at the export [adv] of
    [B], concurrently. [B] exports [f], taking one argument, and [adv],
    taking none, and imports the switcher only. A local capability can only
    be stored through a capability that may store local capabilities, so
    [B] can keep the capability to [b] only on the stack of the thread 0,
    which the thread 1 never sees. *)
Definition ti_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "K";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "B" "f"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := ti_K_code;
         tb_data    := [
           FWs ti_K_data
         ];
         tb_exports := [
           (* after the 3 imports; the stack holds the spill of the switcher call *)
           {| fe_name := "run"; fe_offset := 3; fe_nargs := 0; fe_min_stack := 4; fe_posture := InterruptEnabled |}
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
           {| ue_name := "f";   ue_nargs := 1 |};
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
  fw_threads    := [
    {| ft_cmpt := "K"; ft_entry := "run"; ft_stack_size := 100; ft_tstack_frames := 24 |};
    {| ft_cmpt := "B"; ft_entry := "adv"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the temporal-isolation firmware, from the records of its
    sections. *)
Definition ti_img (sw : img_switcher) (asrt : img_assert) (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (K B sched : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("K", K); ("B", B); ("sched", sched)] [t0; t1] idle boot.

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition ti_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (K B sched : img_cmpt),
    fw_start [] ti_firmware (ti_img sw asrt t0 t1 idle boot K B sched) flag σ.

(** The predicate, computed from [ti_start], with its comments. *)
Definition ti_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@ti_start MP) [ti_firmware; ti_img]).

(** The initial-state predicate of the temporal-isolation case study: the
    annotated one without its comments. *)
Definition ti_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@ti_initial_state_ok_annot MP)).

Lemma ti_initial_state_ok_start `{MP : MachineParameters} flag σ :
  ti_initial_state_ok flag σ → ti_start flag σ.
Proof. initial_state_conv. Qed.
