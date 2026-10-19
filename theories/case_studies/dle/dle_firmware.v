From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout deep_locality.
From griotte Require Import image firmware firmware_ok.
Set Mangle Names.

#[local] Open Scope string_scope.

(** * The firmware of the deep-locality case study and its initial-state predicate *)

(** The main compartment calls the adversary [C] twice: first passing it a
    local capability with the deeply local permission [RW_DL] to one of its
    globals, which holds a capability to the other global, then, after
    writing [42] to the other global, passing it nothing; it then checks
    that the other global still holds [42]. [C] exports
    one entry, taking one argument, and imports the switcher only. The
    thread starts at the export of [main], after its three imports. *)
Definition dle_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts := [
    {| fc_name := "main";
       fc_imports := [ISwitcherCall; IAssert; IExport "C" 0];
       fc_static_sealed := [];
       fc_body := TrustedBody dle_main_code [FWs dle_main_data]
                    [MkFwExport 3 0 InterruptEnabled] |};
    {| fc_name := "C";
       fc_imports := [ISwitcherCall];
       fc_static_sealed := [];
       fc_body := UntrustedBody "C" [1] |}
  ];
  fw_threads := [MkFwThread "main" 0 100 24];
  fw_otypes := [];
  fw_heap_roots := []
|}.

(** The image of the deep-locality firmware, from the records of its
    sections. *)
Definition dle_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("C", C)] [t0].

(** The predicate, computed from the firmware, with its comments: some
    layout, with the flag of the assert library at [flag], satisfies the
    translation of the firmware. *)
Definition dle_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(let t := eval cbv beta delta [dle_firmware dle_img] in
          (λ (flag : Addr) (σ : ExecConf),
             ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
               (main C : img_cmpt),
               note "the flag of the assert library" (flag_assert asrt = flag) ∧
               firmware_ok dle_firmware (dle_img sw asrt t0 main C) σ)
        in
        let t := reduce_firmware_ok t in
        exact t).

(** The initial-state predicate of the deep-locality case study: the
    annotated one without its comments. *)
Definition dle_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  Eval cbv beta delta [section note dle_initial_state_ok_annot] in
    @dle_initial_state_ok_annot MP.

Lemma dle_initial_state_ok_erase `{MP : MachineParameters} flag σ :
  dle_initial_state_ok_annot flag σ ↔ dle_initial_state_ok flag σ.
Proof. reflexivity. Qed.

(** The predicate is the generic translation on the deep-locality
    firmware. *)
Lemma dle_initial_state_ok_firmware_ok `{MP : MachineParameters} flag σ :
  dle_initial_state_ok flag σ →
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread) (main C : img_cmpt),
    flag_assert asrt = flag ∧
    firmware_ok dle_firmware (dle_img sw asrt t0 main C) σ.
Proof. intros Hok. exact Hok. Qed.
