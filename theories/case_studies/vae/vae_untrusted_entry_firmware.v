From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (prints/). *)
From griotte Require Export vae.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The very awkward example, with its thread starting in the adversary *)

(** The very awkward example's firmware whose thread starts at the export
    [adv] of the adversary [C] instead of the export [entry] of [main]: the
    compartments, their code and their exports are those of the very
    awkward example. The main compartment's function [awkward] takes a
    callback [g]; it sets its global [a] to [0], calls [g], sets [a] to [1],
    calls [g] again, and asserts that [a] still holds [1]. The adversary
    imports the export [awkward] of [main] and its own export [g].
    [main]'s [entry] export and its [init] code are not reached. *)
Definition vae_untrusted_entry_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "C" "adv"
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := vae_main_code;
         tb_data    := [
           FWs vae_main_data
         ];
         tb_exports := [
           (* after the 3 imports and the 9 words of [init]; the stack holds the
              spill of the switcher calls *)
           {| fe_name := "awkward"; fe_offset := 12; fe_nargs := 1; fe_min_stack := 4;
              fe_posture := InterruptEnabled |};
           (* after the 3 imports; the stack holds the spill of the switcher call *)
           {| fe_name := "entry";   fe_offset := 3;  fe_nargs := 0; fe_min_stack := 4;
              fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "C";
       fc_imports       := [
         ISwitcherCall;
         IExport "main" "awkward";
         IExport "C" "g"
       ];
       fc_static_sealed := [];
       fc_body          := UntrustedBody {|
         ub_owner   := "C";
         ub_exports := [
           {| ue_name := "adv"; ue_nargs := 0 |};
           {| ue_name := "g";   ue_nargs := 0 |}
         ] |} |}
  ];
  fw_threads    := [
    {| ft_cmpt := "C"; ft_entry := "adv"; ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the firmware, from the records of its sections. *)
Definition vae_untrusted_entry_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("C", C)] [t0].

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition vae_untrusted_entry_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf)
  : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt),
    fw_start [] vae_untrusted_entry_firmware (vae_untrusted_entry_img sw asrt t0 main C) flag σ.

(** The predicate, computed from [vae_untrusted_entry_start], with its
    comments. *)
Definition vae_untrusted_entry_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@vae_untrusted_entry_start MP)
          [vae_untrusted_entry_firmware; vae_untrusted_entry_img]).

(** The initial-state predicate of the very awkward example whose thread
    starts in the adversary: the annotated one without its comments. *)
Definition vae_untrusted_entry_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@vae_untrusted_entry_initial_state_ok_annot MP)).

Lemma vae_untrusted_entry_initial_state_ok_start `{MP : MachineParameters} flag σ :
  vae_untrusted_entry_initial_state_ok flag σ → vae_untrusted_entry_start flag σ.
Proof. initial_state_conv. Qed.
