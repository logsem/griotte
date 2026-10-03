From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost region_keys.
From griotte Require Import proofmode register_tactics map_simpl.

(** * Interfaces of the control-flow segments of [hts_main_asm]

    The proof of [hts_main_spec] is split along the control flow: each
    segment ends at a switcher call (or at [halt]), and its lemma hands the
    state right after the call returns to a continuation.  This file defines
    the shared persistent context, the memory threaded unchanged, and one
    state predicate per call-return edge:
    - [hts_malloc_ret]: after [malloc] (block 4),
    - [hts_adv1_ret]: after [adv(buf)] (block 9),
    - [hts_free_ret]: after [free] (block 15),
    - [hts_adv2_ret]: after [adv(0)] (block 20). *)

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
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {FA : FreeAuth Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The parameters of [hts_main_spec]. Each definition below only takes
      the ones it uses, in this order. *)
  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (W_init_C : WORLD).
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (Nassert Nswitcher : namespace) (cstk : CSTK).

  (** The persistent invariants and facts used by every segment. *)
  Definition hts_main_ctx : iProp Σ :=
    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
    allocator_service_ctx ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    inv (export_table_PCCN allocator_exp_tblN)
      (allocator_exp_tbl_b ↦ₐ WCap true RX Global
        allocator_pcc_b allocator_pcc_e allocator_pcc_b) ∗
    inv (export_table_CGPN allocator_exp_tblN)
      ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b) ∗
    inv (export_table_entryN allocator_exp_tblN
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a)
      ((allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a ↦ₐ
        WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off)) ∗
    inv (export_table_entryN allocator_exp_tblN
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a)
      ((allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ
        WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)) ∗
    interp W_init_C C (WSealed ot_switcher C_f) ∗
    (WSealed ot_switcher C_f) ↦□ₑ 1.

  Global Instance hts_main_ctx_persistent : Persistent hts_main_ctx.
  Proof. rewrite /hts_main_ctx. tc_solve. Qed.

  (** The imported words, in the order of [hts_main_imports]. *)
  Definition hts_imports : iProp Σ :=
    pc_b ↦ₐ WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    (pc_b ^+ 1)%a ↦ₐ WSentry true RX Global b_assert e_assert b_assert ∗
    (pc_b ^+ 2)%a ↦ₐ WSealed ot_switcher C_f ∗
    (pc_b ^+ 3)%a ↦ₐ WSealed ot_switcher (allocator_malloc Global) ∗
    (pc_b ^+ 4)%a ↦ₐ WSealed ot_switcher (allocator_free Global).

  (** The memory that every segment returns unchanged: the imports, the
      code and [p]. *)
  Definition hts_static_mem : iProp Σ :=
    hts_imports ∗
    codefrag pc_a hts_main_code ∗
    cgp_b ↦ₐ WInt 0.

  (** [a] is the first address of block [n] of [hts_main_asm]. *)
  Definition hts_block_addr (n : nat) (a : Addr) : Prop :=
    (pc_a + length (concat (take n (encodeInstrsW <$> assembled_hts_main))))%a = Some a.

  Definition hts_buffer_bounds (b : Addr) : Prop :=
    (heap_b < b)%a ∧ (b < b ^+ 1)%a ∧ (b ^+ 1 <= heap_e)%a.

  (** The registers restored by the switcher on return to [a_ret], and the
      resources that are threaded through every call. *)
  Definition hts_frame (a_ret a_stk : Addr) : iProp Σ :=
    na_own cerise_nais ⊤ ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e a_ret ∗
    cra ↦ᵣ WSentry true RX Global pc_b pc_e a_ret ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ WCap true RWL Local csp_b csp_e a_stk ∗
    (∃ w, cs0 ↦ᵣ w) ∗
    (∃ w, cs1 ↦ᵣ w) ∗
    cstack_frag cstk ∗
    hts_static_mem.

  (** The registers cleared by the switcher. *)
  Definition hts_zero_regs : iProp Σ :=
    ∃ rmap : LReg,
      ⌜dom rmap = all_registers_s ∖ {[PC; csp; cgp; cra; cs0; cs1; ca0; ca1]}⌝ ∗
      ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜w = WInt 0⌝).

  (** Enough to run a failing result check at [a]: [ca0] holds the integer
      error code [z]. *)
  Definition hts_halt_ready (a : Addr) (z : Z) : iProp Σ :=
    na_own cerise_nais ⊤ ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e a ∗
    ca0 ↦ᵣ WInt z ∗
    (∃ w, ct0 ↦ᵣ w) ∗
    codefrag pc_a hts_main_code.

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
      hts_frame a_ret csp_b ∗
      ca0 ↦ᵣ hts_buffer b @@ ι ∗
      ca1 ↦ᵣ WInt 0 ∗
      hts_zero_regs ∗
      [[csp_b, csp_e]] ↦ₐ [[region_addrs_zeroes csp_b csp_e]] ∗
      world_interp (revoke W_init_C) C ∗
      StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e) ∗
      ⌜revoked_addresses (revoke W_init_C) (finz.seq_between csp_b csp_e)⌝ ∗
      interp_continuation cstk Ws Cs ∗
      alloc_obj ι b (b ^+ 1)%a ∗
      free_auth_held ι ∗
      b ↦ₕ[ι] WInt 0.

  (** Return from the call to malloc. Allocator failure and trusted-stack
      exhaustion both return an integer in [ca0]. *)
  Definition hts_malloc_ret : iProp Σ :=
    ∃ a_ret : Addr,
      ⌜hts_block_addr 4 a_ret⌝ ∗
      ((∃ z, hts_halt_ready a_ret z) ∨ hts_malloc_ok a_ret).

  (** Return from the first adversary call: [b] was shared in [hts_Wshare b],
      and the switcher returns a public future [Wret] of it. [p] and the
      saved buffer (in [csp_b]) stayed outside the callee's frame. The
      adversary may have freed [b]: its liveness is only known after the
      reload of the saved buffer. *)
  Definition hts_adv1_ret : iProp Σ :=
    ∃ (ι : AId) (b a_ret : Addr) (Wret : WORLD),
      ⌜hts_block_addr 9 a_ret⌝ ∗
      ⌜hts_buffer_bounds b⌝ ∗
      ⌜(csp_b < csp_e)%a⌝ ∗
      ⌜related_sts_pub_world
        (std_update_multiple (hts_Wshare ι b)
          (finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) Temporary) Wret⌝ ∗
      rel C (LHeap b ι) RW interp_in_memC ∗
      hts_frame a_ret (csp_b ^+ 1)%a ∗
      (∃ w, ca0 ↦ᵣ w) ∗
      (∃ w, ca1 ↦ᵣ w) ∗
      hts_zero_regs ∗
      csp_b ↦ₐ hts_buffer b @@ ι ∗
      (∃ stk, [[(csp_b ^+ 1)%a, csp_e]] ↦ₐ [[stk]]) ∗
      world_interp (revoke Wret) C ∗
      StackRevokedResources Wret C (finz.seq_between (csp_b ^+ 1)%a csp_e) ∗
      ⌜revoked_addresses (revoke Wret) (finz.seq_between (csp_b ^+ 1)%a csp_e)⌝ ∗
      interp_continuation cstk Ws Cs ∗
      alloc_obj ι b (b ^+ 1)%a ∗
      free_auth_held ι.

  (** Successful free: [ι] is quarantined, its world entry is still open. *)
  Definition hts_free_ok (a_ret : Addr) : iProp Σ :=
    ∃ (ι : AId) (b : Addr) (Wret : WORLD),
      ⌜hts_buffer_bounds b⌝ ∗
      ⌜(csp_b < csp_e)%a⌝ ∗
      ⌜heap_std (revoke Wret) !! ι = Some (MkAllocObject b (b ^+ 1)%a AllocObjectLive)⌝ ∗
      ⌜std (revoke Wret) !! LHeap b ι = Some Permanent⌝ ∗
      rel C (LHeap b ι) RW interp_in_memC ∗
      hts_frame a_ret (csp_b ^+ 1)%a ∗
      ca0 ↦ᵣ WInt 0 ∗
      ca1 ↦ᵣ WInt 0 ∗
      hts_zero_regs ∗
      (∃ stk, [[(csp_b ^+ 1)%a, csp_e]] ↦ₐ [[stk]]) ∗
      world_interp_open (revoke Wret) C [LHeap b ι] ∗
      sts_state_std C (LHeap b ι) Permanent ∗
      StackRevokedResources Wret C (finz.seq_between (csp_b ^+ 1)%a csp_e) ∗
      ⌜revoked_addresses (revoke Wret) (finz.seq_between (csp_b ^+ 1)%a csp_e)⌝ ∗
      interp_continuation cstk Ws Cs ∗
      ι ⊒ AQuar.

  (** Return from the call to free. The allocator cannot fail: only
      trusted-stack exhaustion returns a nonzero code. *)
  Definition hts_free_ret : iProp Σ :=
    ∃ a_ret : Addr,
      ⌜hts_block_addr 15 a_ret⌝ ∗
      ((∃ z, ⌜z ≠ 0%Z⌝ ∗ hts_halt_ready a_ret z) ∨ hts_free_ok a_ret).

  (** Return from the second adversary call: only [p] and the code are
      needed for the assertion. *)
  Definition hts_adv2_ret : iProp Σ :=
    ∃ a_ret : Addr,
      ⌜hts_block_addr 20 a_ret⌝ ∗
      hts_frame a_ret (csp_b ^+ 1)%a ∗
      hts_zero_regs.

End HTS_States.

(** Focus on the first block of a segment, whose start address [a_ret] is
    given by [Hret : hts_block_addr pc_a n a_ret]. *)
Tactic Notation "hts_focus_entry_block" constr(n) constr(h) "as"
    ident(a) ident(Ha) constr(hi) constr(hcont) "from" hyp(Hret) :=
  rewrite /hts_block_addr /assembled_hts_main /assembled_hts_main' in Hret;
  cbn in Hret;
  focus_block_nochangePC n h as a Ha hi hcont;
  let Ha' := fresh "Ha" in
  pose proof Ha as Ha'; cbn in Ha'; changePCto a; clear Ha' Hret.
