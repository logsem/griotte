From stdpp Require Import gmap strings.
From griotte Require Import machine_base griotte_opsem switcher assert allocator_resources compartment_layout kvs kvs_main.
From griotte Require Import image firmware firmware_ok.
Set Mangle Names.

#[local] Open Scope string_scope.

(** * The firmware of the KVS case study and its initial-state predicate *)

(** The main compartment calls the KVS service, then the adversary [B],
    then reads back its value; [B] can use the service with its own key.
    The sealing type [ot_kvs] of the user keys and the two user keys are
    parameters. The thread starts at the export [entry] of [main], after
    its seven imports. *)
Definition kvs_firmware `{MP : MachineParameters}
    (ot_kvs : OType) (key_main key_B : Z) : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [ISwitcherCall; IAssert; IExport "B" "f";
                            IExport "kvs" "addOrUpdate"; IExport "kvs" "read";
                            IExport "kvs" "erase"; ISealedStatic ot_kvs 0];
       fc_static_sealed := kvs_main_static_sealed key_main;
       fc_body          :=
         TrustedBody {|
           tb_code    := kvs_main_code;
           tb_data    := [FWs kvs_main_data];
           tb_exports := [ {| fe_name    := "entry";
                              fe_offset  := 7;
                              fe_nargs   := 0;
                              fe_posture := InterruptEnabled |} ] |} |};
    {| fc_name          := "kvs";
       fc_imports       := [ISwitcherCall;
                            FW (WSealRange true (false, true) Global ot_kvs (ot_kvs ^+ 1)%ot ot_kvs)];
       fc_static_sealed := [];
       fc_body          :=
         TrustedBody {|
           tb_code    := kvs_service_instrs;
           tb_data    := [FWs kvs_data];
           tb_exports := [ {| fe_name    := "addOrUpdate";
                              fe_offset  := kvs_addOrUpdate_pcc_off;
                              fe_nargs   := kvs_addOrUpdate_nargs;
                              fe_posture := InterruptEnabled |};
                           {| fe_name    := "read";
                              fe_offset  := kvs_read_pcc_off;
                              fe_nargs   := kvs_read_nargs;
                              fe_posture := InterruptEnabled |};
                           {| fe_name    := "erase";
                              fe_offset  := kvs_erase_pcc_off;
                              fe_nargs   := kvs_erase_nargs;
                              fe_posture := InterruptEnabled |} ] |} |};
    {| fc_name          := "B";
       fc_imports       := [ISwitcherCall; IExport "kvs" "addOrUpdate"; IExport "kvs" "read";
                            IExport "kvs" "erase"; ISealedStatic ot_kvs 0];
       fc_static_sealed := [WInt key_B];
       fc_body          :=
         UntrustedBody {|
           ub_owner   := "B";
           ub_exports := [ {| ue_name  := "f";
                              ue_nargs := 0 |} ] |} |}
  ];
  fw_threads    := [ {| ft_cmpt          := "main";
                        ft_entry         := "entry";
                        ft_stack_size    := 100;
                        ft_tstack_frames := 24 |} ];
  fw_otypes     := [ot_kvs];
  fw_heap_roots := []
|}.

(** The image of the KVS firmware, from the records of its sections. *)
Definition kvs_img (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main kvs B : img_cmpt) : fw_image :=
  MkFwImage sw asrt [("main", main); ("kvs", kvs); ("B", B)] [t0].

(** The predicate, computed from the firmware, with its comments: some
    layout and parameters, with the flag of the assert library at [flag],
    satisfy the translation of the firmware. *)
Definition kvs_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(let t := eval cbv beta delta [kvs_firmware kvs_img] in
          (λ (flag : Addr) (σ : ExecConf),
             ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
               (main kvs B : img_cmpt) (ot_kvs : OType) (key_main key_B : Z),
               note "the flag of the assert library" (flag_assert asrt = flag) ∧
               section "Parameters" (key_main ≠ key_B) ∧
               firmware_ok (kvs_firmware ot_kvs key_main key_B) (kvs_img sw asrt t0 main kvs B) σ)
        in
        let t := reduce_firmware_ok t in
        exact t).

(** The initial-state predicate of the KVS case study: the annotated one
    without its comments. *)
Definition kvs_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  Eval cbv beta delta [section note kvs_initial_state_ok_annot] in
    @kvs_initial_state_ok_annot MP.

Lemma kvs_initial_state_ok_erase `{MP : MachineParameters} flag σ :
  kvs_initial_state_ok_annot flag σ ↔ kvs_initial_state_ok flag σ.
Proof. reflexivity. Qed.

(** The predicate is the generic translation on the KVS firmware. *)
Lemma kvs_initial_state_ok_firmware_ok `{MP : MachineParameters} flag σ :
  kvs_initial_state_ok flag σ →
  ∃ (sw : img_switcher) (asrt : img_assert) (t0 : img_thread)
    (main kvs B : img_cmpt) (ot_kvs : OType) (key_main key_B : Z),
    flag_assert asrt = flag ∧
    key_main ≠ key_B ∧
    firmware_ok (kvs_firmware ot_kvs key_main key_B) (kvs_img sw asrt t0 main kvs B) σ.
Proof. intros Hok. exact Hok. Qed.
