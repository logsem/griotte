From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout cmdc.
From griotte Require Import image firmware firmware_ok.
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
       fc_imports       := [ISwitcherCall; IAssert; IExport "B" "f"; IExport "C" "g"];
       fc_static_sealed := [];
       fc_body          :=
         TrustedBody {|
           tb_code    := cmdc_main_code;
           tb_data    := [FWs cmdc_main_data];
           tb_exports := [ {| fe_name    := "entry";
                              fe_offset  := 4;
                              fe_nargs   := 0;
                              fe_posture := InterruptEnabled |} ] |} |};
    {| fc_name          := "B";
       fc_imports       := [ISwitcherCall];
       fc_static_sealed := [];
       fc_body          :=
         UntrustedBody {|
           ub_owner   := "B";
           ub_exports := [ {| ue_name  := "f";
                              ue_nargs := cmdc_B_f_args |} ] |} |};
    {| fc_name          := "C";
       fc_imports       := [ISwitcherCall];
       fc_static_sealed := [];
       fc_body          :=
         UntrustedBody {|
           ub_owner   := "C";
           ub_exports := [ {| ue_name  := "g";
                              ue_nargs := cmdc_C_g_args |} ] |} |}
  ];
  fw_threads    := [ {| ft_cmpt          := "main";
                        ft_entry         := "entry";
                        ft_stack_size    := 100;
                        ft_tstack_frames := 24 |} ];
  fw_otypes     := [];
  fw_heap_roots := []
|}.

(** The image of the CMDC firmware, from the records of its sections. *)
Definition cmdc_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main B C : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("B", B); ("C", C)] [t0].

(** The predicate, computed from the firmware, with its comments: some
    layout, with the flag of the assert library at [flag], satisfies the
    translation of the firmware. *)
Definition cmdc_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(let t := eval cbv beta delta [cmdc_firmware cmdc_img] in
          (λ (flag : Addr) (σ : ExecConf),
             ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
               (main B C : img_cmpt),
               note "the flag of the assert library" (flag_assert asrt = flag) ∧
               firmware_ok cmdc_firmware (cmdc_img sw asrt t0 main B C) σ)
        in
        let t := reduce_firmware_ok t in
        exact t).

(** The initial-state predicate of the CMDC case study: the annotated one
    without its comments. *)
Definition cmdc_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  Eval cbv beta delta [section note cmdc_initial_state_ok_annot] in
    @cmdc_initial_state_ok_annot MP.

Lemma cmdc_initial_state_ok_erase `{MP : MachineParameters} flag σ :
  cmdc_initial_state_ok_annot flag σ ↔ cmdc_initial_state_ok flag σ.
Proof. reflexivity. Qed.

(** The predicate is the generic translation on the CMDC firmware. *)
Lemma cmdc_initial_state_ok_firmware_ok `{MP : MachineParameters} flag σ :
  cmdc_initial_state_ok flag σ →
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread) (main B C : img_cmpt),
    flag_assert asrt = flag ∧
    firmware_ok cmdc_firmware (cmdc_img sw asrt t0 main B C) σ.
Proof. intros Hok. exact Hok. Qed.
