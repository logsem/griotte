From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout deep_immutability.
From griotte Require Import image firmware firmware_ok initial_state.
Set Mangle Names.

#[local] Open Scope string_scope.

(** * The firmware of the deep-immutability case study and its initial-state predicate *)

(** The main compartment writes [42] to its first global and a capability
    to it into its second global, then calls the adversary [C], passing it a
    capability with the deeply read-only permission [RO_DRO] to the second
    global; it then checks that the first global still holds [42]. [C]
    exports one entry [f], taking one argument, and imports the switcher
    only. The thread starts at the export [entry] of [main], after its three
    imports. *)
Definition droe_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "C" "f"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := droe_main_code;
         tb_data    := [
           FWs droe_main_data
         ];
         tb_exports := [
           {| fe_name := "entry"; fe_offset := 3; fe_nargs := 0; fe_posture := InterruptEnabled |}  (* after the 3 imports *)
         ] |} |};
    {| fc_name          := "C";
       fc_imports       := [
         ISwitcherCall
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "C";
         ub_exports := [
           {| ue_name := "f"; ue_nargs := 1 |}
         ] |} |}
  ];
  fw_threads    := [
    {| ft_cmpt := "main"; ft_entry := "entry"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the deep-immutability firmware, from the records of its
    sections. *)
Definition droe_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("C", C)] [t0].

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition droe_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt),
    fw_start [] droe_firmware (droe_img sw asrt t0 main C) flag σ.

(** The predicate, computed from [droe_start], with its comments. *)
Definition droe_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@droe_start MP) [droe_firmware; droe_img]).

(** The initial-state predicate of the deep-immutability case study: the
    annotated one without its comments. *)
Definition droe_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@droe_initial_state_ok_annot MP)).

Lemma droe_initial_state_ok_start `{MP : MachineParameters} flag σ :
  droe_initial_state_ok flag σ → droe_start flag σ.
Proof. initial_state_conv. Qed.
