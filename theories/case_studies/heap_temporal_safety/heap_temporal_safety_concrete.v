From iris.program_logic Require Import adequacy.
From griotte Require Import machine_parameters machine_parameters_instance
  machine_run assembler rules proofmode switcher assert compartment_layout
  heap_temporal_safety heap_temporal_safety_adequacy disjoint_regions_tactics.
From griotte.allocator Require Import allocator allocator_preamble.

Local Transparent MemNum ONum.
Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).
Local Notation "'OT' z" :=
  (@finz.FinZ ONum z%Z eq_refl eq_refl) (at level 10).

(** The default machine instance has only the allocator's reserved heap cell.
    This example adds two header cells and one payload cell, with a matching
    shadow region. All instruction and permission encodings are reused. *)
Definition hts_heap_region : HeapRegion :=
  {| heap_b := A 8192; heap_e := A 8196; heap_valid := ltac:(solve_addr) |}.
Definition hts_shadow_region : ShadowRegion :=
  {| shadow_b := A 12288; shadow_e := A 12292; shadow_valid := ltac:(solve_addr) |}.

#[local] Instance hts_machine_parameters : MachineParameters :=
  {| instruction_encoding_mixin := @instruction_encoding_mixin machine_parameters_instance;
     permission_encoding_mixin := @permission_encoding_mixin machine_parameters_instance;
     word_encoding_mixin := @word_encoding_mixin machine_parameters_instance;
     encodeAllocStatus := @encodeAllocStatus machine_parameters_instance;
     decodeAllocStatus := @decodeAllocStatus machine_parameters_instance;
     decode_encode_alloc_status_inv := @decode_encode_alloc_status_inv machine_parameters_instance;
     heap_mixin := hts_heap_region;
     shadow_mixin := hts_shadow_region;
     heap_shadow_translation_mixin :=
       @affine_heap_shadow_translation hts_heap_region hts_shadow_region eq_refl;
     heap_shadow_disjoint := ltac:(
       intros x Hheap Hshadow;
       rewrite !elem_of_finz_seq_between in Hheap, Hshadow;
       unfold finz.le_lt in Hheap, Hshadow;
       cbn in Hheap, Hshadow; lia) |}.

(** The concrete adversary counts calls. Its imports remain exactly those
    allowed by general adequacy; it does not need an assert entry point. *)
Import Asm_Griotte.
Definition hts_adv_asm : list (list Asm_Griotte.asm_code) :=
  let first := ".hts_first" in
  let second := ".hts_second" in
  let return_ := ".hts_return" in
  let bad := ".hts_bad" in
  let count := 0%Z in
  let saved := 1%Z in
  let observed := 2%Z in
  [ [load_imm ct0 cgp count; add ct0 (asmr ct0) (asmz 1);
     store_imm cgp (asmr ct0) count;
     sub ct1 (asmr ct0) (asmz 1); jnz (asms second) ct1;
     #first; store_imm cgp (asmr ca0) saved; jmp (asms return_)];
    [ #second; sub ct1 (asmr ct0) (asmz 2); jnz (asms bad) ct1;
     load_imm ct0 cgp saved; gettag ct1 ct0;
     store_imm cgp (asmr ct1) observed; jnz (asms bad) ct1];
    [ #return_; mov ca0 (asmz 0); mov ca1 (asmz 0); ret];
    [ #bad; fail] ].

Import machine_instructions.

Definition hts_adv_code : list Word :=
  concat (encodeInstrsW <$> Asm_Griotte.assemble_block hts_adv_asm).
Definition hts_adv_data : list Word := [WInt 0; WInt 0; WInt (-1)].

(** Regions are adjacent, with boundaries derived from the actual code.
    The ordinary and trusted stacks are kept away from code, heap and shadow. *)
Definition hts_main_pcc_b : Addr := A 9.
Definition hts_main_code_a : Addr := (hts_main_pcc_b ^+ 5)%a.
Definition hts_main_pcc_e : Addr := (hts_main_code_a ^+ length hts_main_code)%a.
Definition hts_adv_pcc_b : Addr := hts_main_pcc_e.
Definition hts_adv_code_a : Addr := (hts_adv_pcc_b ^+ 3)%a.
Definition hts_adv_pcc_e : Addr := (hts_adv_code_a ^+ length hts_adv_code)%a.
Definition hts_alloc_pcc_b : Addr := hts_adv_pcc_e.
Definition hts_alloc_code_a : Addr := (hts_alloc_pcc_b ^+ length allocator_imports)%a.
Definition hts_alloc_pcc_e : Addr := (hts_alloc_code_a ^+ length allocator_code)%a.
Definition hts_main_cgp_b : Addr := hts_alloc_pcc_e.
Definition hts_main_cgp_e : Addr := (hts_main_cgp_b ^+ 2)%a.
Definition hts_adv_cgp_b : Addr := hts_main_cgp_e.
Definition hts_adv_cgp_e : Addr := (hts_adv_cgp_b ^+ 3)%a.
Definition hts_alloc_cgp_b : Addr := hts_adv_cgp_e.
Definition hts_alloc_cgp_e : Addr := (hts_alloc_cgp_b ^+ 1)%a.
Definition hts_main_exports_b : Addr := hts_alloc_cgp_e.
Definition hts_main_exports_e : Addr := (hts_main_exports_b ^+ 2)%a.
Definition hts_adv_exports_b : Addr := hts_main_exports_e.
Definition hts_adv_exports_e : Addr := (hts_adv_exports_b ^+ 3)%a.
Definition hts_alloc_exports_b : Addr := hts_adv_exports_e.
Definition hts_alloc_exports_e : Addr := (hts_alloc_exports_b ^+ 4)%a.
Definition hts_assert_b : Addr := hts_alloc_exports_e.
Definition hts_assert_cap : Addr := (hts_assert_b ^+ length assert_subroutine_instrs)%a.
Definition hts_assert_e : Addr := (hts_assert_cap ^+ 1)%a.
Definition hts_assert_flag : Addr := hts_assert_e.
Definition hts_switcher_b : Addr := (hts_assert_flag ^+ 1)%a.
Definition hts_switcher_call : Addr := (hts_switcher_b ^+ 1)%a.
Definition hts_switcher_return : Addr :=
  (hts_switcher_call ^+ length switcher_call_instrs)%a.
Definition hts_switcher_e : Addr := (hts_switcher_call ^+ length switcher_instrs)%a.
Definition hts_stack_b : Addr := A 1024.
Definition hts_stack_e : Addr := A 1124.
Definition hts_trusted_stack_b : Addr := A 4096.
Definition hts_trusted_stack_e : Addr := A 4196.
Definition hts_switcher_otype : OType := OT 9.

(** These are finite, closed layout obligations; the decision procedures
    produce ordinary kernel-checked proofs. *)
Ltac hts_compute_layout :=
  first [reflexivity | apply (bool_decide_unpack _); vm_compute; reflexivity |
    unfold disjoint_from_shadow, disjoint_from_heap;
    repeat match goal with
    | |- context [finz.seq_between ?b ?e] =>
        let b' := eval vm_compute in b in
        let e' := eval vm_compute in e in
        progress (change b with b'; change e with e')
    end;
    rewrite ?disjoint_list_cons;
    cbn [union_list foldr];
    repeat split;
    try apply disjoint_nil_l; try apply disjoint_nil_r;
    try apply addr_disjoint_list_empty;
    intros x Hx Hy;
    rewrite ?elem_of_union ?elem_of_finz_seq_between ?elem_of_nil in Hx, Hy;
    unfold finz.le_lt in Hx, Hy; cbn in Hx, Hy; lia].

Program Definition hts_concrete_switcher : cmptSwitcher.
Proof.
  refine (@mkCmptSwitcher hts_machine_parameters
    hts_switcher_b hts_switcher_e hts_switcher_call hts_switcher_return
    hts_switcher_otype hts_trusted_stack_b hts_trusted_stack_e
    _ _ _ _ (replicate 100 (WInt 0)) _ eq_refl
    hts_stack_b hts_stack_e (replicate 100 (WInt 0)) _ _ _ _ _ _ _ _).
  all: hts_compute_layout.
Defined.

Program Definition hts_concrete_assert : cmptAssert.
Proof.
  refine (@mkCmptAssert hts_machine_parameters
    hts_assert_b hts_assert_e hts_assert_cap hts_assert_flag _ _ _ _ _).
  all: hts_compute_layout.
Defined.

#[local] Instance hts_concrete_switcher_layout : switcherLayout :=
  cmptSwitcher_switcherLayout hts_concrete_switcher.
#[local] Instance hts_concrete_assert_layout : assertLayout :=
  cmptAssert_assertLayout hts_concrete_assert.
#[local] Instance hts_concrete_allocator_layout : allocatorLayout :=
  {| allocator_pcc_b := hts_alloc_pcc_b;
     allocator_code_b := hts_alloc_code_a;
     allocator_pcc_e := hts_alloc_pcc_e;
     allocator_cgp_b := hts_alloc_cgp_b;
     allocator_cgp_e := hts_alloc_cgp_e;
     allocator_exp_tbl_b := hts_alloc_exports_b;
     allocator_exp_tbl_e := hts_alloc_exports_e |}.

Definition hts_adv_f : Sealable :=
  SCap true RO Global hts_adv_exports_b hts_adv_exports_e (hts_adv_exports_b ^+ 2)%a.
Definition hts_adv_imports : list Word :=
  [WSentry true XSRW_ Local hts_switcher_b hts_switcher_e hts_switcher_call;
   WSealed hts_switcher_otype (allocator_malloc Global);
   WSealed hts_switcher_otype (allocator_free Global)].
Definition hts_adv_exports : list Word := [WInt (encode_entry_point 1 3)].

Program Definition hts_concrete_main : cmpt.
Proof.
  refine (@mkCmpt hts_machine_parameters
    hts_main_pcc_b hts_main_code_a hts_main_pcc_e
    hts_main_cgp_b hts_main_cgp_e hts_main_cgp_e hts_main_cgp_e
    hts_main_exports_b (hts_main_exports_b ^+ 1)%a
    (hts_main_exports_b ^+ 2)%a hts_main_exports_e
    (hts_main_imports hts_adv_f) hts_main_code hts_main_data [] []
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: hts_compute_layout.
Defined.

Program Definition hts_concrete_adv : cmpt.
Proof.
  refine (@mkCmpt hts_machine_parameters
    hts_adv_pcc_b hts_adv_code_a hts_adv_pcc_e
    hts_adv_cgp_b hts_adv_cgp_e hts_adv_cgp_e hts_adv_cgp_e
    hts_adv_exports_b (hts_adv_exports_b ^+ 1)%a
    (hts_adv_exports_b ^+ 2)%a hts_adv_exports_e
    hts_adv_imports hts_adv_code hts_adv_data [] hts_adv_exports
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: hts_compute_layout.
Defined.

Program Definition hts_concrete_alloc : cmpt.
Proof.
  refine (@mkCmpt hts_machine_parameters
    hts_alloc_pcc_b hts_alloc_code_a hts_alloc_pcc_e
    hts_alloc_cgp_b hts_alloc_cgp_e hts_alloc_cgp_e hts_alloc_cgp_e
    hts_alloc_exports_b (hts_alloc_exports_b ^+ 1)%a
    (hts_alloc_exports_b ^+ 2)%a hts_alloc_exports_e
    allocator_imports allocator_code allocator_data [] allocator_export_table_entries
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  all: hts_compute_layout.
Defined.

#[local] Instance hts_concrete_allocator_wf : allocatorLayoutWf.
Proof.
  constructor.
  all: try (intros a; reflexivity).
  all: hts_compute_layout.
Defined.

(** Split unions structurally, then decide only the endpoint inequalities.
    Keeping the interval lemma opaque avoids reducing large address lists. *)
Local Lemma hts_interval_disjoint (b e b' e' : Addr) :
  (e <= b' \/ e' <= b \/ e <= b \/ e' <= b')%a ->
  finz.seq_between b e ## finz.seq_between b' e'.
Proof.
  intros H x Hx Hy. apply elem_of_finz_seq_between in Hx, Hy. solve_addr.
Qed.

Ltac hts_disjoint_regions :=
  lazymatch goal with
  | |- _ /\ _ => split; hts_disjoint_regions
  | |- ?l ∪ ?k ## ?m =>
      apply (proj2 (disjoint_union_l l k m)); split; hts_disjoint_regions
  | |- ?l ## ?k ∪ ?m =>
      apply (proj2 (disjoint_union_r l k m)); split; hts_disjoint_regions
  | |- finz.seq_between _ _ ## finz.seq_between _ _ =>
      apply hts_interval_disjoint;
      apply (bool_decide_unpack _); vm_compute; reflexivity
  | |- _ ## ∅ => apply disjoint_empty_r
  | |- ## [] => apply addr_disjoint_list_empty
  end.

#[local] Instance hts_concrete_layout : hts_memory_layout.
Proof.
  refine {| hts_switcher_cmpt := hts_concrete_switcher;
            hts_assert_cmpt := hts_concrete_assert;
            hts_main_cmpt := hts_concrete_main;
            hts_adv_cmpt := hts_concrete_adv;
            hts_allocator_cmpt := hts_concrete_alloc;
            hts_adv_entry_offset := 3 |}.
  - eexists. reflexivity.
  - unfold cmpt_region, cmpt_pcc_region, cmpt_cgp_region,
      cmpt_static_sealed_region, cmpt_exp_tbl_region, cmpt_switcher_region,
      cmpt_switcher_code_region, cmpt_switcher_trusted_stack_region,
      cmpt_switcher_stack_region, cmpt_assert_region,
      cmpt_assert_code_region, cmpt_assert_cap_region, cmpt_assert_flag_region.
    rewrite ?disjoint_list_cons. cbn [union_list foldr].
    hts_disjoint_regions.
Defined.


Definition hts_concrete_registers : Reg :=
  <[PC := WCap true RX Global hts_main_pcc_b hts_main_pcc_e hts_main_code_a]>
  (<[cgp := WCap true RW Global hts_main_cgp_b hts_main_cgp_e hts_main_cgp_b]>
  (<[csp := WCap true RWL Local hts_stack_b hts_stack_e hts_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).
Definition hts_concrete_sregisters : SReg :=
  <[MTDC := WCap true RWL Local hts_trusted_stack_b hts_trusted_stack_e
    hts_trusted_stack_b]> ∅.
Definition hts_concrete_memory : Mem := hts_initial_memory.
Definition hts_concrete_initial_state : ExecConf :=
  (hts_concrete_registers, hts_concrete_sregisters, hts_concrete_memory, initial_heap_shadow).

Lemma hts_concrete_registers_correct : hts_is_initial_registers hts_concrete_registers.
Proof.
  rewrite /hts_is_initial_registers /hts_concrete_registers.
  split; [rewrite lookup_insert; reflexivity|]. split.
  - rewrite lookup_insert_ne; last done. rewrite lookup_insert.
    case_decide; last done.
    cbn [hts_main_cmpt hts_concrete_layout cmpt_b_cgp cmpt_e_cgp hts_concrete_main].
    reflexivity.
  - split.
    + rewrite lookup_insert_ne; last done.
      rewrite lookup_insert_ne; last done. rewrite lookup_insert.
      cbn [hts_switcher_cmpt hts_concrete_layout b_stack e_stack hts_concrete_switcher].
      reflexivity.
    + intros r Hr. rewrite !lookup_insert_ne; try set_solver.
      apply lookup_gset_to_gmap_Some. split; [apply all_registers_s_correct|done].
Qed.

Lemma hts_concrete_sregisters_correct : hts_is_initial_sregisters hts_concrete_sregisters.
Proof. reflexivity. Qed.

Lemma hts_concrete_memory_correct : hts_is_initial_memory hts_concrete_memory.
Proof.
  unfold hts_is_initial_memory.
  cbn [hts_main_cmpt hts_allocator_cmpt hts_adv_cmpt hts_switcher_cmpt
    hts_concrete_layout cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end
    cmpt_exp_tbl_entries_start cmpt_imports cmpt_code cmpt_data
    cmpt_static_sealed cmpt_exp_tbl_entries stack_content
    hts_concrete_main hts_concrete_alloc hts_concrete_adv hts_concrete_switcher].
  repeat match goal with |- _ /\ _ => split end.
  { reflexivity. }
  { unfold hts_adv_f.
    cbv beta iota zeta delta [hts_memory_switcher_layout hts_memory_assert_layout
      hts_memory_allocator_layout hts_switcher_cmpt hts_assert_cmpt
      hts_allocator_cmpt hts_concrete_layout hts_cmpt_allocator_layout
      hts_concrete_alloc cmpt_b_pcc cmpt_a_code cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
      cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end hts_concrete_switcher_layout
      hts_concrete_assert_layout hts_concrete_allocator_layout].
    reflexivity. }
  1-9: reflexivity.
  - unfold hts_adv_imports.
    cbv beta iota zeta delta [hts_memory_switcher_layout hts_memory_allocator_layout
      hts_switcher_cmpt hts_allocator_cmpt hts_concrete_layout
      hts_cmpt_allocator_layout hts_concrete_alloc cmpt_b_pcc cmpt_a_code cmpt_e_pcc
      cmpt_b_cgp cmpt_e_cgp cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end
      hts_concrete_allocator_layout cmptSwitcher_switcherLayout
      switcher.b_switcher switcher.e_switcher switcher.a_switcher_call
      switcher.ot_switcher hts_concrete_switcher
      b_switcher e_switcher a_switcher_call ot_switcher].
    reflexivity.
  - vm_compute. repeat constructor.
  - rewrite /hts_adv_data. repeat constructor; done.
  - reflexivity.
  - reflexivity.
  - apply Forall_replicate. done.
Qed.

Lemma hts_concrete_heap_disjoint : initial_heap_memory ##ₘ hts_initial_program_memory.
Proof. hts_compute_layout. Qed.

(** [machine_run] reports only a flag. This local counterpart also retains the
    final state, allowing us to check the counter, observed tag and private p.
    Its simulation proof is the state-preserving version of machine_run_correct. *)
Fixpoint hts_run (fuel: nat) (c: Conf): option Conf :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | (Failed, φ) => Some (Failed, φ)
    | (Halted, φ) => Some (Halted, φ)
    | (NextI, φ) => hts_run fuel (Executable, φ)
    | (Executable, (r, sr, m, st)) =>
      match r !! PC with
      | None => Some (Failed, (r, sr, m, st))
      | Some pc =>
        if isCorrectPCb pc
        then (
            let a := match pc with
                     | WCap _ _ _ _ _ a => a
                     | _ => addresses.top (* dummy *)
                     end
            in
            let p := match pc with
                     | WCap _ p _ _ _ _ => p
                     | _ => RWX (* dummy *)
                     end
            in
            match m !! a with
            | None => Some (Failed, (r, sr, m, st))
            | Some wa =>
                let i := decodeInstrW wa in
                let c' := exec i p (r, sr, m, st) in
                hts_run fuel (c'.1,  c'.2)
            end
          ) else (
          Some (Failed, (r, sr, m, st))
        )
      end
    end
  end.

Lemma hts_run_correct fuel cf (φ : ExecConf) cf' (φ' : ExecConf) :
  hts_run fuel (cf, φ) = Some (cf', φ') ->
  rtc erased_step ([Seq (Instr cf)], φ) ([Instr cf'], φ').
Proof.
  revert cf cf' φ φ'. induction fuel; first (cbn; done).
  cbn. intros ? ? [ [ [r sr] m] st] φ' Hc.
  destruct cf; simplify_eq.
  - destruct (r !! PC) as [wpc | ] eqn:HePC; cycle 1.
    + simplify_eq. eapply rtc_l.
      * unfold erased_step. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
        constructor. constructor; auto.
      * eapply rtc_once. exists []. simplify_eq.
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
        constructor.
    + destruct (isCorrectPCb wpc) eqn:HPC.
      * apply isCorrectPCb_isCorrectPC in HPC.
        destruct wpc eqn:Hr; [by inversion HPC| | by inversion HPC | by inversion HPC]. destruct sb as [t p g b e a | ]; last by inversion HPC.
        destruct t; last by inversion HPC.
        destruct (m !! a) as [wa | ] eqn:HeMem.
        ** eapply IHfuel in Hc.
           eapply rtc_l; last eapply Hc.
           unfold erased_step. exists [].
           eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
           eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity.
           constructor. eapply step_exec_instr; eauto.
        ** simplify_eq. eapply rtc_l.
           *** unfold erased_step. exists [].
               eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
               eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
               constructor. eapply step_exec_memfail; eauto.
           *** eapply rtc_once. exists []. simplify_eq.
               eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
               eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
               constructor.
      * simplify_eq. apply isCorrectPCb_nisCorrectPC in HPC.
        eapply rtc_l.
        ** unfold erased_step. exists [].
           eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
           eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
           constructor. eapply step_exec_corrfail; eauto.
        ** eapply rtc_once. exists [].
           eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
           eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
           constructor.
  - eapply rtc_once. exists [].
    eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
    eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
    econstructor.
  - eapply rtc_once. exists [].
    eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
    eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
    econstructor.
  - apply IHfuel in Hc.
    eapply rtc_l.
    + exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
      econstructor.
    + cbn. apply Hc.
Qed.

Local Notation hts_execution :=
  (hts_run 10000 (Executable, hts_concrete_initial_state)).
Definition hts_final_state : ExecConf :=
  default hts_concrete_initial_state (snd <$> hts_execution).

(** Compute only observations; materializing the entire final memory as a
    normalized definition would produce a needlessly large proof term. *)
Lemma hts_execution_flag : fst <$> hts_execution = Some Halted.
Proof. vm_compute. reflexivity. Qed.

Lemma hts_execution_memory :
  hts_final_state.1.2 !! hts_adv_cgp_b = Some (WInt 2) /\
  hts_final_state.1.2 !! (hts_adv_cgp_b ^+ 2)%a = Some (WInt 0) /\
  hts_final_state.1.2 !! hts_main_cgp_b = Some (WInt 0) /\
  hts_final_state.1.2 !! hts_assert_flag = Some (WInt 0).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Computing these observations also rules out allocation failure, an early
    halt at the trusted tag check, and a failed concrete adversary tag check. *)
Lemma hts_execution_observations :
  ∃ reg sr mem sh,
    hts_execution = Some (Halted, (reg, sr, mem, sh)) ∧
    mem !! hts_adv_cgp_b = Some (WInt 2) ∧
    mem !! (hts_adv_cgp_b ^+ 2)%a = Some (WInt 0) ∧
    mem !! hts_main_cgp_b = Some (WInt 0) ∧
    mem !! hts_assert_flag = Some (WInt 0).
Proof.
  generalize hts_execution_flag hts_execution_memory.
  unfold hts_final_state. generalize hts_execution.
  intros result Hflag Hmem.
  destruct result as [ [cf φ] | ]; last discriminate.
  destruct φ as [ [ [reg sr] mem] sh].
  cbn in Hflag, Hmem. injection Hflag as ->.
  exists reg, sr, mem, sh. split; [reflexivity|exact Hmem].
Qed.

Theorem hts_runs_and_gracefully_halts :
  ∃ reg sr mem sh,
    rtc erased_step ([Seq (Instr Executable)], hts_concrete_initial_state)
      ([Instr Halted], (reg, sr, mem, sh)) ∧
    mem !! hts_adv_cgp_b = Some (WInt 2) ∧
    mem !! (hts_adv_cgp_b ^+ 2)%a = Some (WInt 0) ∧
    mem !! hts_main_cgp_b = Some (WInt 0) ∧
    mem !! hts_assert_flag = Some (WInt 0).
Proof.
  destruct hts_execution_observations as (reg & sr & mem & sh & Hrun & Hobs).
  exists reg, sr, mem, sh. split; last exact Hobs.
  apply (hts_run_correct 10000). exact Hrun.
Qed.
