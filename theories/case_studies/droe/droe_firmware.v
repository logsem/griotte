From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout deep_immutability.
From griotte Require Import image firmware firmware_ok.
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
       fc_imports       := [ISwitcherCall; IAssert; IExport "C" "f"];
       fc_static_sealed := [];
       fc_body          :=
         TrustedBody {|
           tb_code    := droe_main_code;
           tb_data    := [FWs droe_main_data];
           tb_exports := [ {| fe_name    := "entry";
                              fe_offset  := 3;
                              fe_nargs   := 0;
                              fe_posture := InterruptEnabled |} ] |} |};
    {| fc_name          := "C";
       fc_imports       := [ISwitcherCall];
       fc_static_sealed := [];
       fc_body          :=
         UntrustedBody {|
           ub_owner   := "C";
           ub_exports := [ {| ue_name  := "f";
                              ue_nargs := 1 |} ] |} |}
  ];
  fw_threads    := [ {| ft_cmpt          := "main";
                        ft_entry         := "entry";
                        ft_stack_size    := 100;
                        ft_tstack_frames := 24 |} ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the deep-immutability firmware, from the records of its
    sections. *)
Definition droe_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("C", C)] [t0].

(** The predicate, computed from the firmware, with its comments: some
    layout, with the flag of the assert library at [flag], satisfies the
    translation of the firmware. *)
Definition droe_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(let t := eval cbv beta delta [droe_firmware droe_img] in
          (λ (flag : Addr) (σ : ExecConf),
             ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
               (main C : img_cmpt),
               note "the flag of the assert library" (flag_assert asrt = flag) ∧
               firmware_ok droe_firmware (droe_img sw asrt t0 main C) σ)
        in
        let t := reduce_firmware_ok t in
        exact t).

(** The initial-state predicate of the deep-immutability case study: the
    annotated one without its comments. *)
Definition droe_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  Eval cbv beta delta [section note droe_initial_state_ok_annot] in
    @droe_initial_state_ok_annot MP.

Lemma droe_initial_state_ok_erase `{MP : MachineParameters} flag σ :
  droe_initial_state_ok_annot flag σ ↔ droe_initial_state_ok flag σ.
Proof. reflexivity. Qed.

(** The predicate is the generic translation on the deep-immutability
    firmware. *)
Lemma droe_initial_state_ok_firmware_ok `{MP : MachineParameters} flag σ :
  droe_initial_state_ok flag σ →
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread) (main C : img_cmpt),
    flag_assert asrt = flag ∧
    firmware_ok droe_firmware (droe_img sw asrt t0 main C) σ.
Proof. intros Hok. exact Hok. Qed.
