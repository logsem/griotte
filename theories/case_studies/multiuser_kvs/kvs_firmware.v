From stdpp Require Import gmap strings.
From griotte Require Import
  machine_base griotte_opsem switcher assert allocator_resources compartment_layout.
(* Exported, so that the code of the case study prints unqualified (tools/prints/). *)
From griotte Require Export kvs kvs_main.
From griotte Require Import image firmware firmware_ok initial_state.

#[local] Open Scope string_scope.

(** * The firmware of the KVS case study and its initial-state predicate *)

(** The main compartment calls the KVS service, then the adversary [B],
    then reads back its value; [B] can use the service with its own key.
    The KVS takes the lock of the lock library around its accesses to the
    table. The sealing type [ot_kvs] of the user keys and the two user keys
    are parameters. The thread 0 starts at the export [entry] of [main],
    after its seven imports; the thread 1 at the export [adv] of [B]. [B]
    is shared by the two threads. *)
Definition kvs_firmware `{MP : MachineParameters}
    (ot_kvs : OType) (key_main key_B : Z) : firmware := {|
  fw_cmpts      := [
    {| fc_name          := "main";
       fc_imports       := [
         ISwitcherCall;
         IAssert;
         IExport "B" "f";
         IExport "kvs" "addOrUpdate";
         IExport "kvs" "read";
         IExport "kvs" "erase";
         ISealedStatic ot_kvs "user_key"
       ];
       fc_static_sealed := [
         {| ss_name := "user_key"; ss_word := WInt key_main |}
       ];
       fc_body          := TrustedBody {|
         tb_code    := kvs_main_code;
         tb_data    := [
           FWs kvs_main_data
         ];
         tb_exports := [
           (* after the 7 imports; the stack holds the spill of the switcher calls *)
           {| fe_name := "entry"; fe_offset := 7; fe_nargs := 0; fe_min_stack := 6; fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "kvs";
       fc_imports       := [
         ISwitcherCall;
         FW (SealRange (false, true) Global ot_kvs (ot_kvs ^+ 1) ot_kvs);  (* unseal-only key of [ot_kvs] *)
         ITryLock
       ];
       fc_static_sealed := [];
       fc_body          := TrustedBody {|
         tb_code    := kvs_service_instrs;
         tb_data    := [
           FWs kvs_data
         ];
         tb_exports := [
           {| fe_name := "addOrUpdate"; fe_offset := kvs_addOrUpdate_pcc_off; fe_nargs := kvs_addOrUpdate_nargs; fe_min_stack := kvs_addOrUpdate_min_stack; fe_posture := InterruptEnabled |};
           {| fe_name := "read";        fe_offset := kvs_read_pcc_off;        fe_nargs := kvs_read_nargs;        fe_min_stack := kvs_read_min_stack;        fe_posture := InterruptEnabled |};
           {| fe_name := "erase";       fe_offset := kvs_erase_pcc_off;       fe_nargs := kvs_erase_nargs;       fe_min_stack := kvs_erase_min_stack;       fe_posture := InterruptEnabled |}
         ];
         tb_error_handler := None;
         tb_error_handler_stackless := None |} |};
    {| fc_name          := "B";
       fc_imports       := [
         ISwitcherCall;
         IExport "kvs" "addOrUpdate";
         IExport "kvs" "read";
         IExport "kvs" "erase";
         ISealedStatic ot_kvs "user_key"
       ];
       fc_static_sealed := [
         {| ss_name := "user_key"; ss_word := WInt key_B |}
       ];
       fc_body          := UntrustedBody {|
         ub_owner   := "B";
         ub_exports := [
           {| ue_name := "f"; ue_nargs := 0 |};
           {| ue_name := "adv"; ue_nargs := 0 |}
         ] |} |};
    {| fc_name          := "sched";
       fc_imports       := [
         ISwitcherCall;
         IMtime;
         IMtimecmp
       ];
       fc_static_sealed := [];
       fc_body          := SchedulerBody {|
         (* the exception entry after the 3 imports; the code is arbitrary *)
         sb_entry      := 3;
         sb_boot_stack := 16 |} |}
  ];
  fw_threads    := [
    {| ft_cmpt := "main"; ft_entry := "entry"; ft_stack_size := 100; ft_tstack_frames := 24 |};
    {| ft_cmpt := "B";    ft_entry := "adv";   ft_stack_size := 100; ft_tstack_frames := 24 |}
  ];
  fw_otypes     := [
    ot_kvs
  ];
  fw_heap_roots := []
|}.

(** The image of the KVS firmware, from the records of its sections. *)
Definition kvs_img (sw : img_switcher) (asrt : img_assert) (lck : img_locks) (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack) (main kvs B sched : img_cmpt) : fw_image :=
  MkFwImage sw asrt lck [("main", main); ("kvs", kvs); ("B", B); ("sched", sched)]
    [t0; t1] idle boot.

(** The start of the firmware: some layout and parameters, with the flag of the
    assert library at [flag] and the lock library at [lck], such that [σ] is
    the state the loader builds. Two threads: the thread 0 starts in [main],
    the thread 1 in [B], which both threads may run. *)
Definition kvs_start `{MP : MachineParameters} (flag : Addr) (σ : ExecConf) : Prop :=
  ∃ (sw : img_switcher) (asrt : img_assert) (lck : img_locks) (t0 t1 : img_thread)
    (idle : img_idle_thread) (boot : img_boot_stack)
    (main kvs B sched : img_cmpt) (ot_kvs : OType) (key_main key_B : Z),
    fw_start [key_main ≠ key_B]
      (kvs_firmware ot_kvs key_main key_B)
      (kvs_img sw asrt lck t0 t1 idle boot main kvs B sched) flag σ.

(** The predicate, computed from [kvs_start], with its comments. *)
Definition kvs_initial_state_ok_annot `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(compute_initial_state (@kvs_start MP) [kvs_firmware; kvs_img]).

(** The initial-state predicate of the KVS case study: the annotated one
    without its comments. *)
Definition kvs_initial_state_ok `{MP : MachineParameters} :
    Addr → ExecConf → Prop :=
  ltac:(erase_annot (@kvs_initial_state_ok_annot MP)).

Lemma kvs_initial_state_ok_start `{MP : MachineParameters} flag σ :
  kvs_initial_state_ok flag σ → kvs_start flag σ.
Proof. initial_state_conv. Qed.
