From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout cmdc.
From griotte Require Import image firmware firmware_ok.
Set Mangle Names.

#[local] Open Scope string_scope.

(** * The firmware of the CMDC case study and its initial-state predicate *)

(** The main compartment calls the adversary [B], then the adversary [C],
    passing each a capability to one of its globals, and checks after each
    call that the other global was not modified. [B] and [C] each export
    one entry, taking one argument, and import the switcher only. The
    thread starts at the export of [main], after its four imports. *)
Definition cmdc_firmware `{MP : MachineParameters} : firmware := {|
  fw_cmpts := [
    {| fc_name := "main";
       fc_imports := [ISwitcherCall; IAssert; IExport "B" 0; IExport "C" 0];
       fc_static_sealed := [];
       fc_body := TrustedBody cmdc_main_code [FWs cmdc_main_data]
                    [MkFwExport 4 0 InterruptEnabled] |};
    {| fc_name := "B";
       fc_imports := [ISwitcherCall];
       fc_static_sealed := [];
       fc_body := UntrustedBody "B" [cmdc_B_f_args] |};
    {| fc_name := "C";
       fc_imports := [ISwitcherCall];
       fc_static_sealed := [];
       fc_body := UntrustedBody "C" [cmdc_C_g_args] |}
  ];
  fw_threads := [MkFwThread "main" 0 100 24];
  fw_otypes := [];
  fw_heap_roots := []
|}.

(** The image of the CMDC firmware, from the records of its sections. *)
Definition cmdc_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main B C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("B", B); ("C", C)] [t0].

(** The predicate, computed from the firmware, with its comments. *)
Definition cmdc_initial_state_ok_annot `{MP : MachineParameters} :
    img_switcher → img_assert → img_thread → img_cmpt → img_cmpt → img_cmpt →
    ExecConf → Prop :=
  ltac:(let t := eval cbv beta delta [cmdc_firmware cmdc_img] in
          (λ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
             (main B C : img_cmpt) (σ : ExecConf),
             firmware_ok cmdc_firmware (cmdc_img sw asrt t0 main B C) σ)
        in
        let t := reduce_firmware_ok t in
        exact t).

(** The initial-state predicate of the CMDC case study: the annotated one
    without its comments. *)
Definition cmdc_initial_state_ok `{MP : MachineParameters} :
    img_switcher → img_assert → img_thread → img_cmpt → img_cmpt → img_cmpt →
    ExecConf → Prop :=
  Eval cbv beta delta [section note cmdc_initial_state_ok_annot] in
    @cmdc_initial_state_ok_annot MP.

Lemma cmdc_initial_state_ok_erase `{MP : MachineParameters} sw asrt t0 main B C σ :
  cmdc_initial_state_ok_annot sw asrt t0 main B C σ ↔
  cmdc_initial_state_ok sw asrt t0 main B C σ.
Proof. reflexivity. Qed.

(** The predicate is the generic translation on the CMDC firmware. *)
Lemma cmdc_initial_state_ok_firmware_ok `{MP : MachineParameters} sw asrt t0 main B C σ :
  cmdc_initial_state_ok sw asrt t0 main B C σ →
  firmware_ok cmdc_firmware (cmdc_img sw asrt t0 main B C) σ.
Proof. intros Hok. exact Hok. Qed.
