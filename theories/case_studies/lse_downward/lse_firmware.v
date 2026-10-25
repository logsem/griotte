From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (prints/). *)
From griotte Require Export lse.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The firmware of the LSE downward case study and its initial-state predicate *)

(** The main compartment sets its global [a] to [2] and calls the adversary
    [C], which imports the export [f] of [main]. The function [f] pushes a
    global capability to [a] on its stack frame and asserts that [a] still
    holds [2]: when [f] returns, the switcher clears its stack frame, so
    that [C] cannot reach the capability. [C] exports one entry [adv],
    taking no argument. [main] has two exports: [f], called by [C], and
    [entry], where the thread starts, after its three imports. *)
Definition lse_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "C" "adv"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := lse_main_code;
         tb_data    := [
           FWs lse_main_data
         ];
         tb_exports := [
           (* after the 3 imports and the 7 words of [run]; the stack holds the
              pushed capability *)
           {| fe_name := "f";     fe_offset := 10; fe_nargs := 0; fe_min_stack := 1; fe_posture := InterruptEnabled |};
           (* after the 3 imports; the stack holds the spill of the switcher call *)
           {| fe_name := "entry"; fe_offset := 3;  fe_nargs := 0; fe_min_stack := 4; fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "C";
       fc_imports       := [
         ISwitcherCall;
         IExport "main" "f"
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "C";
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

(** The image of the LSE downward firmware, from the records of its
    sections. *)
Definition lse_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("C", C)] [t0].

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition lse_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt),
    fw_start [] lse_firmware (lse_img sw asrt t0 main C) flag σ.

(** The predicate, computed from [lse_start], with its comments. *)
Definition lse_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@lse_start MP) [lse_firmware; lse_img]).

(** The initial-state predicate of the LSE downward case study: the
    annotated one without its comments. *)
Definition lse_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@lse_initial_state_ok_annot MP)).

Lemma lse_initial_state_ok_start `{MP : MachineParameters} flag σ :
  lse_initial_state_ok flag σ → lse_start flag σ.
Proof. initial_state_conv. Qed.
