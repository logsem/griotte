From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout vae.
From griotte Require Import image firmware firmware_ok initial_state.
Set Mangle Names.

#[local] Open Scope string_scope.

(** * The firmware of the very awkward example and its initial-state predicate *)

(** The main compartment sets its global [a] to [0] and calls the adversary
    [C], which imports the export [awkward] of [main] and its own export
    [g]. The function [awkward] takes a callback [g]; it sets [a] to [0],
    calls [g], sets [a] to [1], calls [g] again, and asserts that [a] still
    holds [1]. [C] exports two entries, [adv] and [g], taking no argument.
    [main] has two exports: [awkward], called by [C], taking one argument,
    and [entry], where the thread starts, after its three imports. *)
Definition vae_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [ISwitcherCall; IAssert; IExport "C" "adv"];
       fc_static_sealed := [];
       fc_body          :=
         TrustedBody {|
           tb_code    := vae_main_code;
           tb_data    := [FWs vae_main_data];
           tb_exports := [ {| fe_name    := "awkward";
                              fe_offset  := 10;
                              fe_nargs   := 1;
                              fe_posture := InterruptEnabled |};
                           {| fe_name    := "entry";
                              fe_offset  := 3;
                              fe_nargs   := 0;
                              fe_posture := InterruptEnabled |} ] |} |};
    {| fc_name          := "C";
       fc_imports       := [ISwitcherCall; IExport "main" "awkward"; IExport "C" "g"];
       fc_static_sealed := [];
       fc_body          :=
         UntrustedBody {|
           ub_owner   := "C";
           ub_exports := [ {| ue_name  := "adv";
                              ue_nargs := 0 |};
                           {| ue_name  := "g";
                              ue_nargs := 0 |} ] |} |}
  ];
  fw_threads    := [ {| ft_cmpt          := "main";
                        ft_entry         := "entry";
                        ft_stack_size    := 100;
                        ft_tstack_frames := 24 |} ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the very awkward example's firmware, from the records of
    its sections. *)
Definition vae_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("C", C)] [t0].

(** The start of the firmware: some layout, with the flag of the assert
    library at [flag], such that [σ] is the state the loader builds. *)
Definition vae_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt),
    fw_start vae_firmware (vae_img sw asrt t0 main C) flag σ.

(** The predicate, computed from [vae_start], with its comments. *)
Definition vae_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@vae_start MP) [vae_firmware; vae_img]).

(** The initial-state predicate of the very awkward example: the annotated
    one without its comments. *)
Definition vae_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@vae_initial_state_ok_annot MP)).

Lemma vae_initial_state_ok_start `{MP : MachineParameters} flag σ :
  vae_initial_state_ok flag σ → vae_start flag σ.
Proof. initial_state_conv. Qed.
