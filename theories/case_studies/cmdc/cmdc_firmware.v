From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout cmdc.
From griotte Require Import image firmware firmware_ok initial_state.
Set Mangle Names.

#[local] Open Scope string_scope.

(** * The firmware of the CMDC case study and its initial-state predicate *)

(** The main compartment calls the adversary [B], then the adversary [C],
    passing each a capability to one of its globals, and checks after each
    call that the other global was not modified. [B] and [C] each export
    one entry ([f] and [g]), taking one argument, and import the switcher
    only. The thread starts at the export [entry] of [main], after its four
    imports. *)
Definition cmdc_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
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
           {| fe_name := "entry"; fe_offset := 4; fe_nargs := 0; fe_posture := InterruptEnabled |}  (* after the 4 imports *)
         ] |} |};
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
         ] |} |}
  ];
  fw_threads    := [
    {| ft_cmpt := "main"; ft_entry := "entry"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the CMDC firmware, from the records of its sections. *)
Definition cmdc_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main B C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("B", B); ("C", C)] [t0].

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition cmdc_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main B C : img_cmpt),
    fw_start cmdc_firmware (cmdc_img sw asrt t0 main B C) flag σ.

(** The predicate, computed from [cmdc_start], with its comments. *)
Definition cmdc_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@cmdc_start MP) [cmdc_firmware; cmdc_img]).

(** The initial-state predicate of the CMDC case study: the annotated one
    without its comments. *)
Definition cmdc_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@cmdc_initial_state_ok_annot MP)).

Lemma cmdc_initial_state_ok_start `{MP : MachineParameters} flag σ :
  cmdc_initial_state_ok flag σ → cmdc_start flag σ.
Proof. initial_state_conv. Qed.
