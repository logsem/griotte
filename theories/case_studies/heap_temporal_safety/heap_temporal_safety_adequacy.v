From iris.program_logic Require Import adequacy.
From griotte Require Import griotte_lang.
From griotte Require Import compartment_layout adequacy_helpers switcher assert heap_temporal_safety.
From griotte.allocator Require Import allocator allocator_preamble allocator_resource_spec.

(** The allocator is an ordinary switcher compartment. Its special authority
    is in its imports (shadow) and data (heap root), not a new calling ABI. *)
Definition hts_cmpt_allocator_layout `{MP : MachineParameters} (C : cmpt)
    : allocatorLayout :=
  {| allocator_pcc_b := cmpt_b_pcc C;
     allocator_code_b := cmpt_a_code C;
     allocator_pcc_e := cmpt_e_pcc C;
     allocator_cgp_b := cmpt_b_cgp C;
     allocator_cgp_e := cmpt_e_cgp C;
     allocator_exp_tbl_b := cmpt_exp_tbl_pcc C;
     allocator_exp_tbl_e := cmpt_exp_tbl_entries_end C |}.

Class hts_memory_layout `{MP : MachineParameters} := {
    hts_switcher_cmpt : cmptSwitcher;
    hts_assert_cmpt : cmptAssert;
    hts_main_cmpt : cmpt;
    hts_adv_cmpt : cmpt;
    hts_allocator_cmpt : cmpt;
    hts_adv_entry_offset : nat;
    hts_adv_entry_valid :
      is_Some (cmpt_b_pcc hts_adv_cmpt + hts_adv_entry_offset)%a;
    hts_allocator_wf :
      @allocatorLayoutWf MP (hts_cmpt_allocator_layout hts_allocator_cmpt);
    hts_regions_disjoint :
      ## [cmpt_region hts_main_cmpt; cmpt_region hts_adv_cmpt;
          cmpt_region hts_allocator_cmpt; cmpt_switcher_region hts_switcher_cmpt;
          cmpt_assert_region hts_assert_cmpt;
          finz.seq_between heap_b heap_e; finz.seq_between shadow_b shadow_e]
  }.

#[local] Instance hts_memory_switcher_layout `{hts_memory_layout} : switcherLayout :=
  cmptSwitcher_switcherLayout hts_switcher_cmpt.
#[local] Instance hts_memory_assert_layout `{hts_memory_layout} : assertLayout :=
  cmptAssert_assertLayout hts_assert_cmpt.
#[local] Instance hts_memory_allocator_layout `{hts_memory_layout} : allocatorLayout :=
  hts_cmpt_allocator_layout hts_allocator_cmpt.

#[local] Instance hts_memory_allocator_wf `{hts_memory_layout} : allocatorLayoutWf :=
  hts_allocator_wf.

#[local] Instance hts_memory_switcher_wf `{hts_memory_layout} : switcherLayoutWf.
Proof.
  pose proof (compartment_layout.ot_switcher_size hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_size hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_call_entry_point hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_return_entry_point hts_switcher_cmpt).
  pose proof (compartment_layout.trusted_stack_disjoint_from_shadow hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_base_not_shadow hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_base_not_heap hts_switcher_cmpt).
  pose proof (compartment_layout.switcher_disjoint_from_heap hts_switcher_cmpt).
  refine (mkSwitcherLayoutWf _ _ _ _ _ _ _ _ _); cbn in *; auto.
Defined.

Definition hts_initial_program_memory `{hts_memory_layout} : Mem :=
  mk_initial_switcher hts_switcher_cmpt ∪
  mk_initial_assert hts_assert_cmpt ∪
  mk_initial_cmpt hts_main_cmpt ∪
  mk_initial_cmpt hts_allocator_cmpt ∪
  mk_initial_cmpt hts_adv_cmpt.

Definition hts_initial_memory `{hts_memory_layout} : Mem :=
  initial_heap_memory ∪ hts_initial_program_memory.

Definition hts_is_initial_registers `{hts_memory_layout} (reg : Reg) :=
  reg !! PC = Some (WCap true RX Global
    (cmpt_b_pcc hts_main_cmpt) (cmpt_e_pcc hts_main_cmpt) (cmpt_a_code hts_main_cmpt)) ∧
  reg !! cgp = Some (WCap true RW Global
    (cmpt_b_cgp hts_main_cmpt) (cmpt_e_cgp hts_main_cmpt) (cmpt_b_cgp hts_main_cmpt)) ∧
  reg !! csp = Some (WCap true RWL Local
    (b_stack hts_switcher_cmpt) (e_stack hts_switcher_cmpt) (b_stack hts_switcher_cmpt)) ∧
  (∀ r, r ∉ ({[PC; cgp; csp]} : gset RegName) -> reg !! r = Some (WInt 0)).

Definition hts_is_initial_sregisters `{hts_memory_layout} (sreg : SReg) :=
  sreg !! MTDC = Some (WCap true RWL Local
    (compartment_layout.b_trusted_stack hts_switcher_cmpt)
    (compartment_layout.e_trusted_stack hts_switcher_cmpt)
    (compartment_layout.b_trusted_stack hts_switcher_cmpt)).

Definition hts_is_initial_memory `{hts_memory_layout} (mem : Mem) :=
  let adv_f := SCap true RO Global
    (cmpt_exp_tbl_pcc hts_adv_cmpt) (cmpt_exp_tbl_entries_end hts_adv_cmpt)
    (cmpt_exp_tbl_entries_start hts_adv_cmpt) in
  mem = hts_initial_memory ∧
  cmpt_imports hts_main_cmpt = hts_main_imports adv_f ∧
  cmpt_code hts_main_cmpt = hts_main_code ∧
  cmpt_data hts_main_cmpt = hts_main_data ∧
  cmpt_static_sealed hts_main_cmpt = [] ∧
  cmpt_exp_tbl_entries hts_main_cmpt = [] ∧
  cmpt_imports hts_allocator_cmpt = allocator_imports ∧
  cmpt_code hts_allocator_cmpt = allocator_code ∧
  cmpt_data hts_allocator_cmpt = allocator_data ∧
  cmpt_static_sealed hts_allocator_cmpt = [] ∧
  cmpt_exp_tbl_entries hts_allocator_cmpt = allocator_export_table_entries ∧
  (* The adversary is arbitrary and may call malloc and free. In particular,
     it may quarantine the buffer during the first call. *)
  cmpt_imports hts_adv_cmpt =
    [WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
     WSealed ot_switcher (allocator_malloc Global);
     WSealed ot_switcher (allocator_free Global)] ∧
  Forall is_z (cmpt_code hts_adv_cmpt) ∧
  Forall (is_initial_data_word hts_adv_cmpt) (cmpt_data hts_adv_cmpt) ∧
  cmpt_static_sealed hts_adv_cmpt = [] ∧
  cmpt_exp_tbl_entries hts_adv_cmpt =
    [WInt (encode_entry_point 1 hts_adv_entry_offset)] ∧
  Forall is_z (stack_content hts_switcher_cmpt).

(** Initialization must use [allocator_service_init_correct] once to obtain
    both [allocator_ctx] and [allocator_service_ctx]. The allocator export
    table stays outside that initialization for the usual switcher entry
    invariants. No second allocation of the heap ghost state is needed. *)

(** Intended end-to-end safety statement. This permits early halt, failure,
    and adversarial divergence. It does not assume that the first call
    preserves the buffer or that either adversary call returns.

    BLOCKED: safe heap sharing, allocator entry interpretations, and the
    live-to-quarantined world transition described in the specification files.
    The definitions above and the concrete execution do not depend on this
    aborted theorem. *)
Theorem hts_adequacy `{hts_memory_layout}
    (reg reg' : Reg) (sreg sreg' : SReg) (mem mem' : Mem)
    (sh sh' : ShadowTbl) (es : list griotte_lang.expr) :
  hts_is_initial_registers reg ->
  hts_is_initial_sregisters sreg ->
  hts_is_initial_memory mem ->
  sh = initial_heap_shadow ->
  initial_heap_memory ##ₘ hts_initial_program_memory ->
  rtc erased_step ([Seq (Instr Executable)], (reg, sreg, mem, sh))
    (es, (reg', sreg', mem', sh')) ->
  mem' !! flag_assert hts_assert_cmpt = Some (WInt 0).
Proof.
Abort.
