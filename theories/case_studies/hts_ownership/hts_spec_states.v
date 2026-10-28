From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_base switcher_base_ktk.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost region_keys.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte Require Export code_blocks.

(** * Interfaces of the control-flow segments of [hts_main_asm]

    The proof of [hts_main_spec] is split along the control flow: each
    segment ends at a switcher call (or at the return), and its lemma hands the
    state right after the call returns to a continuation.  This file defines
    the shared persistent context, the memory threaded unchanged, and one
    state predicate per call-return edge:
    - [hts_malloc_ret]: after [malloc] (block 5),
    - [hts_adv1_ret]: after [adv(buf)] (block 10),
    - [hts_free_ret]: after [free] (block 16),
    - [hts_adv2_ret]: after [adv(0)] (block 21).

    The return addresses of the calls are addresses of the code
    [hts_main_code], given by the labels of [hts_main_asm]
    ([hts_label_offset]). *)

Section HTS_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [hts_main_code], as focused by [focus_block]. *)
  Definition hts_main_blocks : list (list Word) := ltac:(code_blocks_of hts_main_code).

  Lemma hts_main_code_blocks : hts_main_code = concat hts_main_blocks.
  Proof. reflexivity. Qed.

End HTS_Code.

(** Offset of the first instruction of the block [n] in [hts_main_code]. *)
Notation hts_block_offset := (code_block_offset hts_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [hts_main_code]. *)
Notation hts_instr_offset := (code_instr_offset hts_main_blocks).

(** Offset of the label [s] of [hts_main_asm] from the start of the PCC,
    the imports. *)
Notation hts_label s := (asm_label hts_main_asm s).

(** Offset of the label [s] in [hts_main_code], which starts at the label
    [.Lhts_main]. *)
Notation hts_label_offset s := (asm_label_offset hts_main_asm ".Lhts_main" s).

(** Index of the block of [hts_main_code] that defines the label [s]. *)
Notation hts_block s := (asm_block hts_main_asm s).

(** Pure facts about the allocator layout, shared by the known calls. *)
Section HTS_Layout.
  Context `{MP: MachineParameters} {alloclayout : allocatorLayout}
    {allocwf : allocatorLayoutWf}.

  Lemma hts_export_tbl_not_shadow a :
    (allocator_exp_tbl_b <= a < allocator_exp_tbl_e)%a ->
    is_shadow_address a = false.
  Proof.
    intros Ha. apply not_true_is_false; intros Hshadow.
    pose proof allocator_regions_disjoint as Hregions.
    rewrite !disjoint_list_cons in Hregions.
    cbn [union_list] in Hregions.
    apply withinBounds_true_iff in Hshadow.
    clear - Hregions Ha Hshadow.
    assert (a ∈ finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e)
      as Htbl by (apply elem_of_finz_seq_between; solve_addr).
    assert (a ∈ finz.seq_between shadow_b shadow_e)
      as Hsh by (apply elem_of_finz_seq_between; solve_addr).
    set_solver.
  Qed.

  Lemma hts_export_tbl_disjoint_from_shadow :
    disjoint_from_shadow allocator_exp_tbl_b allocator_exp_tbl_e.
  Proof.
    pose proof allocator_regions_disjoint as Hregions.
    rewrite !disjoint_list_cons in Hregions. cbn [union_list] in Hregions.
    rewrite /disjoint_from_shadow. set_solver+Hregions.
  Qed.

  Lemma hts_export_tbl_not_heap :
    is_heap_address allocator_exp_tbl_b = false.
  Proof.
    apply not_true_is_false; intros Hheap.
    pose proof allocator_regions_disjoint as Hregions.
    rewrite !disjoint_list_cons in Hregions.
    cbn [union_list] in Hregions.
    apply withinBounds_true_iff in Hheap.
    pose proof allocator_size_exports as Hsize.
    rewrite /allocator_export_table_entries in Hsize.
    clear - Hregions Hheap Hsize.
    assert (allocator_exp_tbl_b ∈
      finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e) as Htbl
      by (apply elem_of_finz_seq_between; solve_addr).
    assert (allocator_exp_tbl_b ∈ finz.seq_between heap_b heap_e) as Hhelem
      by (apply elem_of_finz_seq_between; solve_addr).
    set_solver.
  Qed.

  Lemma hts_allocator_pcc_not_heap :
    is_heap_address allocator_pcc_b = false.
  Proof.
    apply not_true_is_false; intros Hheap.
    pose proof allocator_regions_disjoint as Hregions.
    rewrite !disjoint_list_cons in Hregions.
    cbn [union_list] in Hregions.
    apply withinBounds_true_iff in Hheap.
    pose proof allocator_size_imports as Himports_size.
    pose proof allocator_size_code as Hcode_size.
    clear - Hregions Hheap Himports_size Hcode_size.
    assert (allocator_pcc_b ∈
      finz.seq_between allocator_pcc_b allocator_pcc_e)
      as Hpcc by (apply elem_of_finz_seq_between; solve_addr).
    assert (allocator_pcc_b ∈ finz.seq_between heap_b heap_e)
      as Hhelem by (apply elem_of_finz_seq_between; solve_addr).
    set_solver.
  Qed.

  Lemma hts_allocator_cgp_not_heap :
    is_heap_address allocator_cgp_b = false.
  Proof.
    apply not_true_is_false; intros Hheap.
    pose proof allocator_regions_disjoint as Hregions.
    rewrite !disjoint_list_cons in Hregions.
    cbn [union_list] in Hregions.
    apply withinBounds_true_iff in Hheap.
    pose proof allocator_size_data as Hdata_size.
    clear - Hregions Hheap Hdata_size.
    assert (allocator_cgp_b ∈
      finz.seq_between allocator_cgp_b allocator_cgp_e)
      as Hcgp by (apply elem_of_finz_seq_between; solve_addr).
    assert (allocator_cgp_b ∈ finz.seq_between heap_b heap_e)
      as Hhelem by (apply elem_of_finz_seq_between; solve_addr).
    set_solver.
  Qed.

  (** Heap addresses are not shadow addresses. *)
  Lemma hts_heap_not_shadow b :
    (heap_b <= b < heap_e)%a ->
    is_shadow_address b = false.
  Proof.
    intros Hb. apply not_true_is_false; intros Hshadow.
    pose proof allocator_regions_disjoint as Hregions.
    rewrite !disjoint_list_cons in Hregions.
    cbn [union_list] in Hregions.
    apply withinBounds_true_iff in Hshadow.
    clear - Hregions Hshadow Hb.
    assert (b ∈ finz.seq_between heap_b heap_e) as Hheap
      by (apply elem_of_finz_seq_between; solve_addr).
    assert (b ∈ finz.seq_between shadow_b shadow_e) as Hsh
      by (apply elem_of_finz_seq_between; solve_addr).
    set_solver.
  Qed.
End HTS_Layout.

Section HTS_States.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  #[local] Instance free_auth_owner_inst : FreeAuth Σ := free_auth_owner.

  (** The parameters of [hts_main_spec]. Each definition below only takes
      the ones it uses, in this order. *)
  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (owner_a : Addr) (W_init_C : WORLD).
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (cstk : CSTK).

  (** The persistent invariants and facts used by every segment. *)
  Definition hts_main_ctx : iProp Σ :=
    let a_alloc_exp_tbl_cgp := (allocator_exp_tbl_b ^+ ExportTable_offset_cgp)%a in
    let a_alloc_entry_malloc := (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a in
    let a_alloc_entry_free := (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a in
    assert_static b_assert e_assert a_flag ∗
    allocator_service_ctx ∗
    allocator_service_static ∗
    na_inv (tpool th) Nswitcher switcher_inv ∗
    switcher_static ∗
    allocator_exp_tbl_b ↦ₐ□ WCap true RX Global
      allocator_pcc_b allocator_pcc_e allocator_pcc_b ∗
    a_alloc_exp_tbl_cgp ↦ₐ□ WCap true RW Global
      allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    a_alloc_entry_malloc ↦ₐ□
      WInt (encode_entry_point InterruptEnabled allocator_malloc_nargs allocator_malloc_min_stack
        allocator_malloc_pcc_off) ∗
    a_alloc_entry_free ↦ₐ□
      WInt (encode_entry_point InterruptEnabled allocator_free_nargs allocator_free_min_stack
        allocator_free_pcc_off) ∗
    interp W_init_C C (WSealed ot_switcher C_f) ∗
    C_f ↦ₑ□{nargs} 1.

  #[global] Instance hts_main_ctx_persistent : Persistent hts_main_ctx.
  Proof. rewrite /hts_main_ctx. tc_solve. Qed.

  (** The imported words, in the order of [hts_main_imports]. *)
  Definition hts_imports : iProp Σ :=
    pc_b ↦ₐ□ WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    (pc_b ^+ 1)%a ↦ₐ□ WSentry Inherit true RX Global b_assert e_assert b_assert ∗
    (pc_b ^+ 2)%a ↦ₐ□ WSealed ot_switcher C_f ∗
    (pc_b ^+ 3)%a ↦ₐ□ WSealed ot_switcher (allocator_malloc Global) ∗
    (pc_b ^+ 4)%a ↦ₐ□ WSealed ot_switcher (allocator_free Global) ∗
    (pc_b ^+ 5)%a ↦ₐ□ allocator_capability Global owner_a.

  (** The memory that every segment returns unchanged: the imports, the
      code, [p] and the owner word of the allocator capability. *)
  Definition hts_static_mem : iProp Σ :=
    hts_imports ∗
    codefrag_pers pc_a hts_main_code ∗
    cgp_b ↦ₐ WInt 0 ∗
    owner_a ↦ₐ WInt hts_main_owner_id.

  Definition hts_buffer_bounds (b : Addr) : Prop :=
    (heap_b < b)%a ∧ (b < b ^+ 1)%a ∧ (b ^+ 1 <= heap_e)%a.

  (** The registers restored by the switcher on return to [a_ret], and the
      resources that are threaded through every call. *)
  Definition hts_frame (a_ret a_stk : Addr) : iProp Σ :=
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] WCap true RX Global pc_b pc_e a_ret ∗
    (∃ mie, cra ↦ᵣ[th] WSentry (ret_kind mie) true RX Global pc_b pc_e a_ret) ∗
    cgp ↦ᵣ[th] WCap true RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ[th] WCap true RWL Local csp_b csp_e a_stk ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    (∃ w, cs1 ↦ᵣ[th] w) ∗
    cstack_frag cstk ∗
    hts_static_mem.

  (** The registers cleared by the switcher. *)
  Definition hts_zero_regs : iProp Σ :=
    ∃ rmap : LReg,
      ⌜dom rmap = all_registers_s ∖ {[ csp; cgp; cra; cs0; cs1; ca0; ca1]}⌝ ∗
      ([∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w ∗ ⌜w = WInt 0⌝).

  (** Enough to run a failing result check at [a], and to return through the
      switcher's return sentry saved in [cs0], at the thread's entry call
      stack: [ca0] holds the integer error code [z]. *)
  Definition hts_halt_ready (a : Addr) (z : Z) : iProp Σ :=
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] WCap true RX Global pc_b pc_e a ∗
    ca0 ↦ᵣ[th] WInt z ∗
    (∃ w, ct0 ↦ᵣ[th] w) ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    (∃ w, cra ↦ᵣ[th] w) ∗
    (∃ w, ctp ↦ᵣ[th] w) ∗
    (∃ w, ct2 ↦ᵣ[th] w) ∗
    cstack_frag cstk ∗
    ⌜cstk.(cstk_frames) = []⌝ ∗
    codefrag_pers pc_a hts_main_code.

  (** The world shared with the first adversary call: the stack is revoked
      and the buffer [b] of [ι] is allocated and [Permanent]. *)
  Definition hts_Wshare (ι : AId) (b : Addr) : WORLD :=
    <s[LHeap b ι := Permanent]s>
      (heap_std_update (revoke W_init_C) (heap_allocate ∅ ι b (b ^+ 1)%a)).

  (** The world after freeing [ι] in the revoked world [Wret]. *)
  Definition hts_Wfree (Wret : WORLD) (ι : AId) : WORLD :=
    heap_std_update (revoke Wret) (heap_quarantine (heap_std (revoke Wret)) ι).

  (** Successful malloc: [ca0] holds the fresh buffer [b] of [ι]. *)
  Definition hts_malloc_ok (a_ret : Addr) : iProp Σ :=
    ∃ (ι : AId) (b : Addr),
      ⌜hts_buffer_bounds b⌝ ∗
      hts_frame a_ret (stk_start_a csp_b csp_e) ∗
      ca0 ↦ᵣ[th] hts_buffer b @@ ι ∗
      ca1 ↦ᵣ[th] WInt 0 ∗
      hts_zero_regs ∗
      [[csp_b, stk_start_a csp_b csp_e]] ↦ₐ
        [[region_addrs_zeroes csp_b (stk_start_a csp_b csp_e)]] ∗
      world_interp (revoke W_init_C) C ∗
      StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e) ∗
      ⌜revoked_addresses (revoke W_init_C) (finz.seq_between csp_b csp_e)⌝ ∗
      interp_continuation cstk Ws Cs ∗
      allocator_owner_id hts_main_owner_id {[ι]} ∗
      alloc_obj ι b (b ^+ 1)%a ∗
      free_right ι ∗
      b ↦ₕ[ι] WInt 0.

  (** Return from the call to malloc. Allocator failure and trusted-stack
      exhaustion both return an integer in [ca0]. *)
  Definition hts_malloc_ret : iProp Σ :=
    (∃ z, hts_halt_ready (pc_a ^+ hts_label_offset ".Lhts_malloc_result")%a z) ∨
    hts_malloc_ok (pc_a ^+ hts_label_offset ".Lhts_malloc_result")%a.

  (** Return from the first adversary call: [b] was shared in [hts_Wshare b],
      and the switcher returns a public future [Wret] of it. [p] and the
      saved buffer (in the cell [stk_start_a csp_b csp_e ^+ -1], below the
      space reserved at the top of the stack) stayed outside the
      callee's frame. Only main holds [free_right ι], so [ι] is still
      live. *)
  Definition hts_adv1_ret : iProp Σ :=
    ∃ (ι : AId) (b : Addr) (Wret : WORLD),
      ⌜hts_buffer_bounds b⌝ ∗
      ⌜(csp_b < csp_e)%a⌝ ∗
      ⌜related_sts_pub_world
        (std_update_multiple (hts_Wshare ι b)
          (callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)%a) Temporary) Wret⌝ ∗
      rel C (LHeap b ι) RW interp_in_memC ∗
      hts_frame (pc_a ^+ hts_label_offset ".Lhts_reload")%a (stk_start_a csp_b csp_e ^+ -1)%a ∗
      (∃ w, ca0 ↦ᵣ[th] w) ∗
      (∃ w, ca1 ↦ᵣ[th] w) ∗
      hts_zero_regs ∗
      (stk_start_a csp_b csp_e ^+ -1)%a ↦ₐ hts_buffer b @@ ι ∗
      (∃ stk, [[stk_free_b csp_b (stk_start_a csp_b csp_e ^+ -1)%a,
                stk_free_e csp_e (stk_start_a csp_b csp_e ^+ -1)%a]] ↦ₐ [[stk]]) ∗
      world_interp (revoke Wret) C ∗
      StackRevokedResources Wret C (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)%a) ∗
      ⌜revoked_addresses (revoke Wret) (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)%a)⌝ ∗
      interp_continuation cstk Ws Cs ∗
      allocator_owner_id hts_main_owner_id {[ι]} ∗
      alloc_obj ι b (b ^+ 1)%a ∗
      free_right ι.

  (** Successful free: [ι] is quarantined, its world entry is still open. *)
  Definition hts_free_ok (a_ret : Addr) : iProp Σ :=
    ∃ (ι : AId) (b : Addr) (Wret : WORLD),
      ⌜hts_buffer_bounds b⌝ ∗
      ⌜(csp_b < csp_e)%a⌝ ∗
      ⌜heap_std (revoke Wret) !! ι = Some (MkAllocObject b (b ^+ 1)%a AllocObjectLive)⌝ ∗
      ⌜std (revoke Wret) !! LHeap b ι = Some Permanent⌝ ∗
      rel C (LHeap b ι) RW interp_in_memC ∗
      hts_frame a_ret (stk_start_a csp_b csp_e ^+ -1)%a ∗
      ca0 ↦ᵣ[th] WInt 0 ∗
      ca1 ↦ᵣ[th] WInt 0 ∗
      hts_zero_regs ∗
      (∃ stk, [[stk_free_b csp_b (stk_start_a csp_b csp_e ^+ -1)%a,
                stk_free_e csp_e (stk_start_a csp_b csp_e ^+ -1)%a]] ↦ₐ [[stk]]) ∗
      world_interp_open (revoke Wret) C [LHeap b ι] ∗
      sts_state_std C (LHeap b ι) Permanent ∗
      StackRevokedResources Wret C (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)%a) ∗
      ⌜revoked_addresses (revoke Wret) (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)%a)⌝ ∗
      interp_continuation cstk Ws Cs ∗
      ι ⊒ AQuar.

  (** Return from the call to free. The allocator cannot fail: only
      trusted-stack exhaustion returns a nonzero code. *)
  Definition hts_free_ret : iProp Σ :=
    (∃ z, ⌜z ≠ 0%Z⌝ ∗ hts_halt_ready (pc_a ^+ hts_label_offset ".Lhts_free_result")%a z) ∨
    hts_free_ok (pc_a ^+ hts_label_offset ".Lhts_free_result")%a.

  (** Return from the second adversary call: only [p] and the code are
      needed for the assertion. *)
  Definition hts_adv2_ret : iProp Σ :=
    hts_frame (pc_a ^+ hts_label_offset ".Lhts_prep_assert")%a (stk_start_a csp_b csp_e ^+ -1)%a ∗
    hts_zero_regs.

End HTS_States.
