From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher assert compartment_layout
  kvs kvs_main kvs_adequacy disjoint_regions_tactics.

Existing Instance machine_parameters_instance.
Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).
Local Notation "'OT' z" :=
  (@finz.FinZ ONum z%Z eq_refl eq_refl) (at level 10).

Definition kvs_main_pcc_b : Addr := A 9.
Definition kvs_main_code_start : Addr := A 16.
Definition kvs_main_pcc_e : Addr := A 112.
Definition kvs_B_pcc_b : Addr := A 115.
Definition kvs_B_code_start : Addr := A 120.
Definition kvs_B_pcc_e : Addr := A 178.
Definition kvs_KVS_pcc_b : Addr := A 183.
Definition kvs_KVS_code_start : Addr := A 185.
Definition kvs_KVS_pcc_e : Addr := A 367.
Definition kvs_main_static_sealed_b : Addr := A 112.
Definition kvs_main_static_sealed_e : Addr := A 113.
Definition kvs_main_data_b : Addr := A 113.
Definition kvs_main_data_e : Addr := A 113.
Definition kvs_B_static_sealed_b : Addr := A 178.
Definition kvs_B_static_sealed_e : Addr := A 179.
Definition kvs_B_data_b : Addr := A 179.
Definition kvs_B_data_e : Addr := A 180.
Definition kvs_KVS_data_b : Addr := A 367.
Definition kvs_KVS_data_e : Addr := A 415.
Definition kvs_main_exports_pcc : Addr := A 113.
Definition kvs_main_exports_cgp : Addr := A 114.
Definition kvs_main_exports_entries_b : Addr := A 115.
Definition kvs_main_exports_entries_e : Addr := A 115.
Definition kvs_B_exports_pcc : Addr := A 180.
Definition kvs_B_exports_cgp : Addr := A 181.
Definition kvs_B_exports_entries_b : Addr := A 182.
Definition kvs_B_exports_entries_e : Addr := A 183.
Definition kvs_KVS_exports_pcc : Addr := A 415.
Definition kvs_KVS_exports_cgp : Addr := A 416.
Definition kvs_KVS_exports_entries_b : Addr := A 417.
Definition kvs_KVS_exports_entries_e : Addr := A 420.
Definition kvs_assert_b : Addr := A 420.
Definition kvs_assert_cap : Addr := A 432.
Definition kvs_assert_e : Addr := A 433.
Definition kvs_assert_flag : Addr := A 433.
Definition kvs_switcher_b : Addr := A 434.
Definition kvs_switcher_call : Addr := A 435.
Definition kvs_switcher_return : Addr := A 523.
Definition kvs_switcher_e : Addr := A 585.
Definition kvs_switcher_sealing_type : OType := OT 9.
Definition kvs_service_sealing_type : OType := OT 10.
Definition kvs_trusted_stack_b : Addr := A 4096.
Definition kvs_trusted_stack_e : Addr := A 4196.
Definition kvs_stack_b : Addr := A 1024.
Definition kvs_stack_e : Addr := A 1124.

Ltac unfold_kvs_addresses :=
  unfold kvs_main_pcc_b, kvs_main_code_start, kvs_main_pcc_e,
    kvs_B_pcc_b, kvs_B_code_start, kvs_B_pcc_e,
    kvs_KVS_pcc_b, kvs_KVS_code_start, kvs_KVS_pcc_e,
    kvs_main_static_sealed_b, kvs_main_static_sealed_e,
    kvs_main_data_b, kvs_main_data_e,
    kvs_B_static_sealed_b, kvs_B_static_sealed_e,
    kvs_B_data_b, kvs_B_data_e, kvs_KVS_data_b, kvs_KVS_data_e,
    kvs_main_exports_pcc, kvs_main_exports_cgp,
    kvs_main_exports_entries_b, kvs_main_exports_entries_e,
    kvs_B_exports_pcc, kvs_B_exports_cgp,
    kvs_B_exports_entries_b, kvs_B_exports_entries_e,
    kvs_KVS_exports_pcc, kvs_KVS_exports_cgp,
    kvs_KVS_exports_entries_b, kvs_KVS_exports_entries_e,
    kvs_assert_b, kvs_assert_cap, kvs_assert_e, kvs_assert_flag,
    kvs_switcher_b, kvs_switcher_call, kvs_switcher_return,
    kvs_switcher_e, kvs_switcher_sealing_type,
    kvs_service_sealing_type,
    kvs_trusted_stack_b, kvs_trusted_stack_e,
    kvs_stack_b, kvs_stack_e.

Ltac unfold_kvs_addresses_in H :=
  unfold kvs_main_pcc_b, kvs_main_code_start, kvs_main_pcc_e,
    kvs_B_pcc_b, kvs_B_code_start, kvs_B_pcc_e,
    kvs_KVS_pcc_b, kvs_KVS_code_start, kvs_KVS_pcc_e,
    kvs_main_static_sealed_b, kvs_main_static_sealed_e,
    kvs_main_data_b, kvs_main_data_e,
    kvs_B_static_sealed_b, kvs_B_static_sealed_e,
    kvs_B_data_b, kvs_B_data_e, kvs_KVS_data_b, kvs_KVS_data_e,
    kvs_main_exports_pcc, kvs_main_exports_cgp,
    kvs_main_exports_entries_b, kvs_main_exports_entries_e,
    kvs_B_exports_pcc, kvs_B_exports_cgp,
    kvs_B_exports_entries_b, kvs_B_exports_entries_e,
    kvs_KVS_exports_pcc, kvs_KVS_exports_cgp,
    kvs_KVS_exports_entries_b, kvs_KVS_exports_entries_e,
    kvs_assert_b, kvs_assert_cap, kvs_assert_e, kvs_assert_flag,
    kvs_switcher_b, kvs_switcher_call, kvs_switcher_return,
    kvs_switcher_e, kvs_switcher_sealing_type,
    kvs_service_sealing_type,
    kvs_trusted_stack_b, kvs_trusted_stack_e,
    kvs_stack_b, kvs_stack_e in H.

Local Instance kvs_concrete_kvsLayout : kvsLayout :=
  @mkKvsLayout kvs_service_sealing_type
    kvs_KVS_pcc_b kvs_KVS_code_start kvs_KVS_pcc_e
    kvs_KVS_data_b kvs_KVS_data_e
    kvs_KVS_exports_pcc kvs_KVS_exports_entries_e.

(** The concrete adversary inserts key [1] with value [42] in its own KVS
    namespace, then erases that key. It restores its return capability and
    clears its argument registers before returning to the main program. *)
Definition kvs_B_code : list Word :=
  encodeInstrsW [
    (* Fetch the adversary's sealed KVS user key. *)
    Mov cs1 PC;
    GetB ct0 cs1;
    GetA ct1 cs1;
    Sub ct0 ct0 ct1;
    Lea cs1 ct0;
    Lea cs1 4%Z;
    Load cs1 cs1;
    Mov ct0 0%Z;
    Mov ct1 0%Z;

    (* Preserve the return capability and prepare
       addOrUpdate(sealed key, 1, 42). *)
    Mov cs0 cra;
    Mov ca0 cs1;
    Mov ca1 1%Z;
    Mov ca2 42%Z;

    (* Fetch the switcher entry point. *)
    Mov ctp PC;
    GetB ct0 ctp;
    GetA ct1 ctp;
    Sub ct0 ct0 ct1;
    Lea ctp ct0;
    Lea ctp 0%Z;
    Load ctp ctp;
    Mov ct0 0%Z;
    Mov ct1 0%Z;

    (* Fetch the sealed KVS.addOrUpdate entry point. *)
    Mov ct1 PC;
    GetB ct0 ct1;
    GetA ct2 ct1;
    Sub ct0 ct0 ct2;
    Lea ct1 ct0;
    Lea ct1 1%Z;
    Load ct1 ct1;
    Mov ct0 0%Z;
    Mov ct2 0%Z;

    (* Invoke KVS.addOrUpdate through the switcher. *)
    Jalr cra ctp;

    (* Prepare erase(sealed key, 1). *)
    Mov ca0 cs1;
    Mov ca1 1%Z;

    (* Fetch the switcher entry point. *)
    Mov ctp PC;
    GetB ct0 ctp;
    GetA ct1 ctp;
    Sub ct0 ct0 ct1;
    Lea ctp ct0;
    Lea ctp 0%Z;
    Load ctp ctp;
    Mov ct0 0%Z;
    Mov ct1 0%Z;

    (* Fetch the sealed KVS.erase entry point. *)
    Mov ct1 PC;
    GetB ct0 ct1;
    GetA ct2 ct1;
    Sub ct0 ct0 ct2;
    Lea ct1 ct0;
    Lea ct1 3%Z;
    Load ct1 ct1;
    Mov ct0 0%Z;
    Mov ct2 0%Z;

    (* Invoke KVS.erase through the switcher. *)
    Jalr cra ctp;

    (* Restore the return capability, clear arguments, and return via the
       switcher. *)
    Mov cra cs0;
    Mov ca0 0%Z;
    Mov ca1 0%Z;
    Mov ca2 0%Z;
    Jalr cnull cra
  ].

Definition kvs_B_data : list Word := [WInt 0].
Definition kvs_main_static_sealed_concrete : list Word := [WInt 1].
Definition kvs_B_static_sealed : list Word := [WInt 2].

Program Definition kvs_concrete_cmptSwitcher : cmptSwitcher.
Proof.
  refine (@mkCmptSwitcher machine_parameters_instance
    kvs_switcher_b kvs_switcher_e kvs_switcher_call
    kvs_switcher_return kvs_switcher_sealing_type
    kvs_trusted_stack_b kvs_trusted_stack_e _ _ _ _
    (replicate 100 (WInt 0)) _ eq_refl kvs_stack_b kvs_stack_e
    (replicate 100 (WInt 0)) _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_kvs_addresses.
    repeat split; unfold disjoint, set_disjoint_instance;
      intros x Hx Hx'; rewrite !elem_of_finz_seq_between in Hx, Hx';
      solve_addr.
Defined.

Program Definition kvs_concrete_cmptAssert : cmptAssert.
Proof.
  refine (@mkCmptAssert machine_parameters_instance kvs_assert_b
    kvs_assert_e kvs_assert_cap kvs_assert_flag _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_kvs_addresses.
    unfold disjoint, set_disjoint_instance.
    intros x Hx Hx'.
    rewrite !elem_of_finz_seq_between in Hx, Hx'.
    solve_addr.
Defined.

Local Instance kvs_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout kvs_concrete_cmptSwitcher).
Defined.

Local Instance kvs_concrete_assertLayout : assertLayout.
Proof.
  exact (cmptAssert_assertLayout kvs_concrete_cmptAssert).
Defined.

Definition kvs_B_f : Sealable :=
  SCap RO Global kvs_B_exports_pcc kvs_B_exports_entries_e
    kvs_B_exports_entries_b.
Definition kvs_main_imports_concrete : list Word :=
  kvs_main_imports kvs_main_static_sealed_b
    kvs_switcher_b kvs_switcher_e kvs_switcher_call
    kvs_switcher_sealing_type kvs_assert_b kvs_assert_e kvs_B_f.
Definition kvs_B_imports : list Word :=
  [ WSentry XSRW_ Local kvs_switcher_b kvs_switcher_e kvs_switcher_call
  ; WSealed kvs_switcher_sealing_type (KVS_addOrUpdate Global)
  ; WSealed kvs_switcher_sealing_type (KVS_read Global)
  ; WSealed kvs_switcher_sealing_type (KVS_erase Global)
  ; kvs_user_seal_key Global kvs_B_static_sealed_b
  ].
Definition kvs_B_exports : list Word :=
  [WInt (encode_entry_point 0 5)].
Definition kvs_KVS_imports : list Word :=
  kvs_imports kvs_switcher_b kvs_switcher_e kvs_switcher_call
    kvs_switcher_sealing_type.

Program Definition kvs_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt kvs_main_pcc_b kvs_main_code_start kvs_main_pcc_e
    kvs_main_data_b kvs_main_data_e
    kvs_main_static_sealed_b kvs_main_static_sealed_e
    kvs_main_exports_pcc kvs_main_exports_cgp
    kvs_main_exports_entries_b kvs_main_exports_entries_e
    kvs_main_imports_concrete kvs_main_code kvs_main_data
    kvs_main_static_sealed_concrete [] _ _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_kvs_addresses.
    rewrite (finz_seq_between_empty (A 113) (A 113)); last solve_addr.
    rewrite !disjoint_list_cons.
    repeat split.
    + unfold disjoint, set_disjoint_instance.
      intros x Hx Hx'.
      rewrite elem_of_finz_seq_between in Hx.
      repeat (rewrite elem_of_app in Hx' ||
              rewrite elem_of_finz_seq_between in Hx').
      cbn in Hx'.
      destruct Hx' as [Hx' | [Hx' | [Hx' | Hx']]];
        [set_solver | solve_addr | solve_addr | set_solver].
    + set_solver.
    + disj_regions.
    + disj_regions.
    + constructor.
Defined.

Program Definition kvs_concrete_B_cmpt : cmpt.
Proof.
  refine (@mkCmpt kvs_B_pcc_b kvs_B_code_start kvs_B_pcc_e
    kvs_B_data_b kvs_B_data_e
    kvs_B_static_sealed_b kvs_B_static_sealed_e
    kvs_B_exports_pcc kvs_B_exports_cgp
    kvs_B_exports_entries_b kvs_B_exports_entries_e
    kvs_B_imports kvs_B_code kvs_B_data
    kvs_B_static_sealed kvs_B_exports _ _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_kvs_addresses.
    rewrite !disjoint_list_cons.
    repeat split.
    + disj_regions.
    + unfold disjoint, set_disjoint_instance.
      intros x Hx Hx'.
      rewrite elem_of_finz_seq_between in Hx.
      repeat (rewrite elem_of_app in Hx' ||
              rewrite elem_of_finz_seq_between in Hx').
      cbn in Hx'.
      destruct Hx' as [Hx' | [Hx' | Hx']].
      * solve_addr.
      * solve_addr.
      * set_solver.
    + disj_regions.
    + disj_regions.
    + constructor.
Defined.

Program Definition kvs_concrete_KVS_cmpt : cmpt.
Proof.
  refine (@mkCmpt kvs_KVS_pcc_b kvs_KVS_code_start kvs_KVS_pcc_e
    kvs_KVS_data_b kvs_KVS_data_e kvs_KVS_data_e kvs_KVS_data_e
    kvs_KVS_exports_pcc kvs_KVS_exports_cgp
    kvs_KVS_exports_entries_b kvs_KVS_exports_entries_e
    kvs_KVS_imports kvs_service_instrs kvs_data []
    kvs_export_table_entries _ _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_kvs_addresses.
    rewrite (finz_seq_between_empty (A 415) (A 415)); last solve_addr.
    rewrite !disjoint_list_cons.
    repeat split.
    + unfold disjoint, set_disjoint_instance.
      intros x Hx Hx'.
      rewrite elem_of_finz_seq_between in Hx.
      repeat (rewrite elem_of_app in Hx' ||
              rewrite elem_of_finz_seq_between in Hx').
      cbn in Hx'.
      destruct Hx' as [Hx' | [Hx' | [Hx' | Hx']]];
        [solve_addr | set_solver | solve_addr | set_solver].
    + unfold disjoint, set_disjoint_instance.
      intros x Hx Hx'.
      rewrite elem_of_finz_seq_between in Hx.
      repeat (rewrite elem_of_app in Hx' ||
              rewrite elem_of_finz_seq_between in Hx').
      cbn in Hx'.
      destruct Hx' as [Hx' | [Hx' | Hx']];
        [set_solver | solve_addr | set_solver].
    + set_solver.
    + disj_regions.
    + constructor.
Defined.

Ltac solve_kvs_cmpt_disjoint :=
  unfold disjoint, Cmpt_Disjoint, disjoint_cmpt,
    cmpt_region, cmpt_pcc_region, cmpt_cgp_region,
    cmpt_static_sealed_region, cmpt_exp_tbl_region;
  unfold kvs_concrete_main_cmpt, kvs_concrete_B_cmpt,
    kvs_concrete_KVS_cmpt;
  cbn;
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_kvs_addresses_in Hx;
  unfold_kvs_addresses_in Hx';
  destruct Hx as [[[Hx | Hx] | Hx] | Hx];
  destruct Hx' as [[[Hx' | Hx'] | Hx'] | Hx'];
  try set_solver; solve_addr.

Ltac solve_kvs_switcher_disjoint :=
  unfold switcher_cmpt_disjoint, cmpt_switcher_region,
    cmpt_switcher_code_region, cmpt_switcher_trusted_stack_region,
    cmpt_switcher_stack_region, cmpt_region, cmpt_pcc_region,
    cmpt_cgp_region, cmpt_static_sealed_region, cmpt_exp_tbl_region;
  unfold kvs_concrete_cmptSwitcher, kvs_concrete_main_cmpt,
    kvs_concrete_B_cmpt, kvs_concrete_KVS_cmpt;
  cbn;
  unfold disjoint, set_disjoint_instance;
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_kvs_addresses_in Hx;
  unfold_kvs_addresses_in Hx';
  destruct Hx as [[Hx | Hx] | Hx];
  destruct Hx' as [[[Hx' | Hx'] | Hx'] | Hx'];
  try set_solver; solve_addr.

Ltac solve_kvs_assert_disjoint :=
  unfold assert_cmpt_disjoint, cmpt_assert_region,
    cmpt_assert_code_region, cmpt_assert_cap_region,
    cmpt_assert_flag_region, cmpt_region, cmpt_pcc_region,
    cmpt_cgp_region, cmpt_static_sealed_region, cmpt_exp_tbl_region;
  unfold kvs_concrete_cmptAssert, kvs_concrete_main_cmpt,
    kvs_concrete_B_cmpt, kvs_concrete_KVS_cmpt;
  cbn;
  unfold disjoint, set_disjoint_instance;
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_kvs_addresses_in Hx;
  unfold_kvs_addresses_in Hx';
  destruct Hx as [[Hx | Hx] | Hx];
  destruct Hx' as [[[Hx' | Hx'] | Hx'] | Hx'];
  try set_solver; solve_addr.

Ltac solve_kvs_assert_switcher_disjoint :=
  unfold assert_switcher_disjoint, cmpt_assert_region,
    cmpt_assert_code_region, cmpt_assert_cap_region,
    cmpt_assert_flag_region, cmpt_switcher_region,
    cmpt_switcher_code_region, cmpt_switcher_trusted_stack_region,
    cmpt_switcher_stack_region;
  unfold kvs_concrete_cmptAssert, kvs_concrete_cmptSwitcher;
  cbn;
  unfold disjoint, set_disjoint_instance;
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_kvs_addresses_in Hx;
  unfold_kvs_addresses_in Hx';
  destruct Hx as [[Hx | Hx] | Hx];
  destruct Hx' as [[Hx' | Hx'] | Hx'];
  solve_addr.

Global Instance kvs_concrete_layout : memory_layout.
Proof.
  refine (@Build_memory_layout machine_parameters_instance
    kvs_concrete_cmptSwitcher kvs_concrete_cmptAssert
    kvs_concrete_main_cmpt kvs_concrete_KVS_cmpt
    kvs_service_sealing_type _ _ 1 2 _ kvs_concrete_B_cmpt 5
    _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - lia.
  - repeat split; solve_kvs_cmpt_disjoint.
  - repeat split; solve_kvs_switcher_disjoint.
  - repeat split; solve_kvs_assert_disjoint.
  - solve_kvs_assert_switcher_disjoint.
Defined.

Definition kvs_initial_registers : Reg :=
  <[PC := WCap RX Global kvs_main_pcc_b kvs_main_pcc_e
      kvs_main_code_start]>
  (<[cgp := WCap RW Global kvs_main_data_b kvs_main_data_e
      kvs_main_data_b]>
  (<[csp := WCap RWL Local kvs_stack_b kvs_stack_e kvs_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).

Definition kvs_initial_sregisters : SReg :=
  <[MTDC := WCap RWL Local kvs_trusted_stack_b kvs_trusted_stack_e
      kvs_trusted_stack_b]> ∅.

Definition kvs_initial_memory : Mem := mk_initial_memory.

Lemma kvs_initial_registers_correct :
  is_initial_registers kvs_initial_registers.
Proof.
  rewrite /is_initial_registers /kvs_initial_registers.
  cbn [kvs_concrete_layout kvs_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma kvs_initial_sregisters_correct :
  is_initial_sregisters kvs_initial_sregisters.
Proof.
  rewrite /is_initial_sregisters /kvs_initial_sregisters.
  cbn [kvs_concrete_layout kvs_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma kvs_initial_memory_correct :
  is_initial_memory kvs_initial_memory.
Proof.
  rewrite /is_initial_memory /kvs_initial_memory.
  cbn [kvs_concrete_layout kvs_concrete_main_cmpt
       kvs_concrete_KVS_cmpt kvs_concrete_B_cmpt
       kvs_concrete_cmptSwitcher kvs_concrete_cmptAssert
       kvs_concrete_kvsLayout].
  repeat split; try reflexivity.
  - rewrite /kvs_B_code /encodeInstrsW; repeat constructor; done.
  - rewrite /kvs_B_data; repeat constructor; done.
  - apply Forall_replicate; done.
Qed.

Lemma kvs_concrete_adequacy reg' sreg' mem' es :
  rtc erased_step
    ([Seq (Instr Executable)],
      (kvs_initial_registers, kvs_initial_sregisters, kvs_initial_memory))
    (es, (reg', sreg', mem')) ->
  mem' !! kvs_assert_flag = Some (WInt 0%Z).
Proof.
  intro Hrun.
  pose proof
    (@kvs_adequacy machine_parameters_instance kvs_concrete_layout
      kvs_initial_registers reg' kvs_initial_sregisters sreg'
      kvs_initial_memory mem' es kvs_initial_registers_correct
      kvs_initial_sregisters_correct kvs_initial_memory_correct Hrun)
    as Hadequacy.
  cbn [kvs_concrete_layout kvs_concrete_cmptAssert] in Hadequacy.
  exact Hadequacy.
Qed.

(** Combining the computed execution with [kvs_concrete_adequacy] shows that
    there is a final machine state such that the exact initial configuration:
    - executes to [Halted], rather than failing or exhausting the chosen fuel;
    - finishes with the assertion flag still set to zero.
    Thus this particular adversarial execution terminates normally without
    violating the case study's assertion. *)
Theorem kvs_runs_and_gracefully_halts :
  ∃ reg' sreg' mem',
    rtc erased_step
      ([Seq (Instr Executable)],
        (kvs_initial_registers, kvs_initial_sregisters,
         kvs_initial_memory))
      ([Instr Halted], (reg', sreg', mem'))
    ∧ mem' !! kvs_assert_flag = Some (WInt 0%Z).
Proof.
  pose proof
    (machine_run_correct 15000 Executable
      (kvs_initial_registers, kvs_initial_sregisters, kvs_initial_memory)
      Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[reg' sreg'] mem'] Hrun].
  exists reg', sreg', mem'. split.
  - exact Hrun.
  - eapply kvs_concrete_adequacy; exact Hrun.
Qed.
