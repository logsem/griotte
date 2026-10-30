From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import switcher_macros_spec.
From griotte Require Import switcher_call_states switcher_call_world.
From griotte.switcher.call Require Import call_path.
From griotte Require Import map_simpl register_tactics proofmode.

(** * Call routine of the switcher, known-to-known calls

    The proof composes the block and path lemmas of [call/],
    shared with [switcher_cc_specification_gen]. The caller and the callee
    are both known: the entry point is the sealed capability of a known
    export table, and the arguments are not required to be valid. *)

Section Switcher_KtK_Call.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  (* TODO: move to switcher/code/clear_stack_spec.v *)
  (** Zeroing twice from the same address is zeroing once. *)
  #[local] Lemma stack_zeroed_from_idemp (b : Addr) (v : Z) (ws : list LWord) :
    stack_zeroed_from b v (stack_zeroed_from b v ws) = stack_zeroed_from b v ws.
  Proof.
    rewrite /stack_zeroed_from length_app length_take length_replicate.
    destruct (decide (Z.to_nat (v - b) <= length ws)%nat) as [Hle | Hgt].
    - rewrite take_app_le; last (rewrite length_take; lia).
      rewrite take_take Nat.min_id.
      f_equal. f_equal. lia.
    - rewrite take_ge; last (rewrite length_app length_take length_replicate; lia).
      rewrite (_ : Nat.min (Z.to_nat (v - b)) (length ws) + (length ws - Z.to_nat (v - b))
                   - Z.to_nat (v - b) = 0)%nat; last lia.
      by rewrite app_nil_r.
  Qed.

  (* TODO: move to switcher/code/clear_stack_spec.v (a copy of the lemma of
     switcher_spec_KtK_return.v) *)
  (** Everything is zeroed from an address below the cells. *)
  #[local] Lemma stack_zeroed_from_below (b : Addr) (v : Z) (ws : list LWord) :
    (v <= b)%Z →
    stack_zeroed_from b v ws = replicate (length ws) (lword_of_word (WInt 0)).
  Proof.
    intros Hv. rewrite /stack_zeroed_from Z2Nat.nonpos; last lia.
    by rewrite take_0 Nat.sub_0_r.
  Qed.

  (* TODO: move to switcher/code/clear_stack_spec.v (a copy of the lemma of
     switcher_spec_KtK_return.v) *)
  (** The cells of a stack region above MSHWMB and below MSHWM are cells of
      the zone, which hold 0: zeroing them from MSHWM zeroes them all. *)
  #[local] Lemma stack_region_below_hwm E (b e : Addr) (ws : list LWord) (hb h : Z) :
    (hb <= b)%Z →
    stack_region b e ws -∗
    hwm_regs hb h -∗
    |~{E}~>
    ⌜stack_zeroed_from b h ws = replicate (length ws) (lword_of_word (WInt 0))⌝ ∗
    stack_region b e ws ∗
    hwm_regs hb h.
  Proof.
    iInduction ws as [|w ws] "IH" forall (b); iIntros (Hhb) "Hstk Hhwm".
    { iModIntro. iFrame. iPureIntro. by rewrite /stack_zeroed_from take_nil. }
    destruct (decide (h <= b)%Z) as [Hh | Hh].
    { iModIntro. iFrame. iPureIntro. by apply stack_zeroed_from_below. }
    iDestruct (stack_region_length with "Hstk") as %Hlen.
    rewrite finz_seq_between_length /= in Hlen.
    assert (b < e)%a as Hbe by (rewrite /finz.dist in Hlen; solve_addr).
    destruct (b + 1)%a as [b'|] eqn:Hb'; last solve_addr.
    iDestruct (stack_region_cons b b' e with "Hstk") as "[[Hb | [Hb ->]] Hstk]"; [done|done|..].
    - (* A full points-to is outside the zone *)
      iDestruct "Hhwm" as "[Hhb Hh]".
      iMod (hwm_pointsto_outside with "Hb Hhb Hh") as "(%Hout & _)".
      exfalso; lia.
    - iMod ("IH" $! b' with "[%] Hstk Hhwm") as "(%Hz & Hstk & Hhwm)"; first solve_addr.
      iModIntro. iFrame "Hhwm".
      iSplit.
      + iPureIntro. revert Hz. rewrite /stack_zeroed_from.
        rewrite (_ : Z.to_nat (h - b) = S (Z.to_nat (h - b'))); last solve_addr.
        cbn. by intros ->.
      + iApply (stack_region_cons b b' e); [done|done|]. iFrame.
        by iApply stack_cell_of_zone.
  Qed.

  (* TODO: move to switcher/code/clear_stack_spec.v *)
  (** A stack region zeroed from MSHWM, above MSHWMB, holds only zeros. *)
  #[local] Lemma stack_region_zeroed_from_hwm E (b e : Addr) (ws : list LWord) (hb h : Z) :
    (hb <= b)%Z →
    stack_region b e (stack_zeroed_from b h ws) -∗
    hwm_regs hb h -∗
    |~{E}~>
    stack_region b e (region_addrs_zeroes b e) ∗
    hwm_regs hb h.
  Proof.
    iIntros (Hhb) "Hstk Hhwm".
    iDestruct (stack_region_length with "Hstk") as %Hlen.
    iMod (stack_region_below_hwm with "Hstk Hhwm") as "(%Hz & Hstk & Hhwm)"; first done.
    rewrite stack_zeroed_from_idemp in Hz.
    rewrite Hz /region_addrs_zeroes -Hlen finz_seq_between_length.
    iModIntro. iFrame.
  Qed.

  (* TODO: move to switcher/code/clear_stack_spec.v *)
  (** Cells of the zone are zeroed stack cells. *)
  #[local] Lemma stack_region_of_zone (b e : Addr) :
    ([∗ list] a ∈ finz.seq_between b e, zone_cell a) ⊢
    stack_region b e (region_addrs_zeroes b e).
  Proof.
    rewrite /stack_region /region_addrs_zeroes -finz_seq_between_length big_sepL2_replicate_r //.
    iIntros "H". iApply (big_sepL_mono with "H"). iIntros (k a _) "Ha".
    by iApply stack_cell_of_zone.
  Qed.

  (* TODO: move to switcher/code/clear_stack_spec.v *)
  (** The zeroed cells of [[lo, s)], inside a zeroed stack region, join the
      zone, and come back. *)
  #[local] Lemma stack_region_zeroes_zone_acc E (b lo s e : Addr) :
    (b <= lo)%a → (b <= s)%a → (s <= e)%a →
    stack_region b e (region_addrs_zeroes b e) ⊢
    |~{E}~> ([∗ list] a ∈ finz.seq_between lo s, zone_cell a) ∗
            (([∗ list] a ∈ finz.seq_between lo s, zone_cell a) -∗
             stack_region b e (region_addrs_zeroes b e)).
  Proof.
    iIntros (Hblo Hbs Hse) "Hstk".
    destruct (decide (lo <= s)%a) as [Hlos | Hslo]; cycle 1.
    { rewrite finz_seq_between_empty; last solve_addr.
      iModIntro. iSplitR; first done. iIntros "_". iExact "Hstk". }
    rewrite (region_addrs_zeroes_split b lo e); last solve_addr.
    rewrite (region_addrs_zeroes_split lo s e); last solve_addr.
    iDestruct (stack_region_split b lo e with "Hstk") as "[Hlo Hhi]"; [solve_addr|solve_addr|].
    rewrite take_app_length'; last (by rewrite /region_addrs_zeroes length_replicate).
    rewrite drop_app_length'; last (by rewrite /region_addrs_zeroes length_replicate).
    iDestruct (stack_region_split lo s e with "Hhi") as "[Hmid Hhi]"; [solve_addr|solve_addr|].
    rewrite take_app_length'; last (by rewrite /region_addrs_zeroes length_replicate).
    rewrite drop_app_length'; last (by rewrite /region_addrs_zeroes length_replicate).
    iMod (stack_region_zeroes_zone with "Hmid") as "Hmid".
    iModIntro. iFrame "Hmid". iIntros "Hmid".
    iDestruct (stack_region_of_zone with "Hmid") as "Hmid".
    iApply (stack_region_join with "[$Hlo Hmid Hhi]"); [solve_addr|solve_addr|].
    iApply (stack_region_join with "[$Hmid $Hhi]"); solve_addr.
  Qed.

  (** Failure path of [switcher_cc_specification_known_to_known]: the
      trusted stack is exhausted. *)
  Lemma switcher_cc_spec_tstack_exhausted_known_to_known
    (F : coPset)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller wct2 wctp : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk cstk' : CSTK)
    (a_tstk : Addr) (save_area tstk_next : list LWord) (h : Z) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ) in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    disjoint_from_mmio b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    (b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    save_area !! Z.to_nat TrustedStack_offset_hazardPointers = Some (lword_of_word hazard_slots_cap) ->
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (▷ trusted_stack_inv ∗ na_own (tpool th) (F ∖ ↑Ntstack) ={⊤}=∗ na_own (tpool th) F) ∗
    na_own (tpool th) (F ∖ ↑Ntstack) ∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
    (∃ ws, [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ [[ ws ]]) ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
    (∃ w, a_threadID ↦ₐ w) ∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_static ∗
    ●(CSTK)[th] cstk' ∗
    cstack_interp cstk' a_tstk ∗
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0, cs0 ↦ᵣ[th] wcs0) ∗
    (∃ wcs1, cs1 ↦ᵣ[th] wcs1) ∗
    cgp ↦ᵣ[th] wcgp_caller ∗
    cra ↦ᵣ[th] wcra_caller ∗
    ctp ↦ᵣ[th] wctp ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ct1 ↦ᵣ[th] wct1_caller ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (stk_saved_a a_stk) ∗
    switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller ∗
    stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) (stk_mem_callee stk_mem) ∗
    hwm_res cstk h ∗
    regs[th] arg_rmap ∗
    regs[th] delete ctp (delete ct2 rmap) ∗
    ◯(CSTK)[th] cstk ∗
    ▷ ( ( ∃ rmap' stk_mem' rcgp rcra rcs0 rcs1,
            ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
            na_own (tpool th) F ∗
            PC ↦ₚ[th] lupdatePcPerm rcra ∗
            cgp ↦ᵣ[th] rcgp ∗
            cra ↦ᵣ[th] rcra ∗
            csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
            cs0 ↦ᵣ[th] rcs0 ∗
            cs1 ↦ᵣ[th] rcs1 ∗
            ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK ∗
            ca1 ↦ᵣ[th] WInt 0 ∗
            regs₀[th] rmap' ∗
            stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem' ∗
            (∃ h', hwm_res cstk h') ∗
            ◯(CSTK)[th] cstk ∗
            ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
              load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝ )
        -∗ safe[th] )
    ⊢ safe[th].
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next.
    subst a_frameoffset a_save_end a_threadID a_next.
    (* Outline of the proof: [switcher_cc_exhausted_regs] collects the
       registers, [switch_trusted_stack_exhausted_path_spec] restores the
       registers, clears the others and returns, then close the trusted-stack
       invariant. The return address is a valid
       target, so the jump back does not fault. *)
    iIntros (Hstk_mmio Hdom Hrdom Hstk_bounds Hlen_cstk Ha_tstk_e Hsave_hazard Hret_jalr Hret_heap)
      "(Hclose_switcher_inv & Hna & Hmtdc & Hsave_area & Hhazard_slots & Hframeoffset & HthreadID
      & Htstk & #Hstatic & Hcstk_full & Hstk_interp
      & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hctp & Hct2 & Hct1 & Hcsp & Hcells & Hstk & Hhwm
      & Hargs & Hregs & Hcstk & Hpost)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    stk_unfold. change (4 - 1)%Z with 3%Z in Hastk_bounds.
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iApply (switch_trusted_stack_exhausted_path_spec with
      "[- $HPC $Hcsp $Hcells $Hrmap0 $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1]");
      [done|done|done|].
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "(%Hrestored & %Hrmap' & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp & Hcells & Hrmap & _)".
    iSplit; cycle 1.
    { (* The return address of the caller is a valid target *)
      iIntros "%Hjalr".
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_nonheap in Hra; last done.
      subst rcra; congruence. }
    iIntros "[HPC _]".
    iMod ("Hclose_switcher_inv" with
      "[$Hna $Hcstk_full Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Htstk Hstk_interp]")
      as "Hna".
    { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }
    iDestruct (switcher_stk_cells_region_4 with "Hcells") as "Hcells";
      first (stk_unfold; solve_addr).
    iDestruct (stack_region_of_pointsto with "Hcells") as "Hcells".
    iEval (rewrite /stk_spill_a /SpillSlot_size (_ : (a_stk ^+ - (4)) ^+ 4 = a_stk);
           last solve_addr) in "Hcells".
    iDestruct (stack_region_join b_stk (a_stk ^+ - (4)) a_stk with "[$Hstk $Hcells]") as "Hstk";
      [solve_addr|solve_addr|].
    iApply "Hpost"; iFrame.
    iPureIntro; split; last done. rewrite Hrmap'; set_solver.
  Qed.

  Lemma switcher_cc_specification_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK)
    (nargs minstk_tgt : nat)
    (F : coPset)

    (btbl_tgt atbl_tgt etbl_tgt : Addr)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z) (posture_tgt : InterruptStatus)
    (h : Z)
    :
    let a_tbl_cgp := (btbl_tgt ^+ ExportTable_offset_cgp) in
    let a_tbl_ehs := (btbl_tgt ^+ ExportTable_offset_errorHandlerStackless) in
    let wct1_caller := Sealed ot_switcher RO Global btbl_tgt etbl_tgt atbl_tgt in
    let frame :=
           {| cf_tframe :=
                {| tf_csp := Cap RWL Local b_stk e_stk (stk_saved_a a_stk);
                   tf_export_tbl := Cap RO Global btbl_tgt etbl_tgt atbl_tgt;
                   tf_error_count := 0 |};
              cf_saved :=
                {| cs_cra := wcra_caller;
                   cs_cgp := wcgp_caller;
                   cs_cs0 := wcs0_caller;
                   cs_cs1 := wcs1_caller |};
              ccrel := Known_to_Known
           |}
    in

    disjoint_from_mmio b_stk e_stk ->
    is_shadow_address atbl_tgt = false ->
    is_shadow_address btbl_tgt = false ->
    is_shadow_address a_tbl_cgp = false ->
    disjoint_from_shadow btbl_tgt etbl_tgt ->
    is_heap_address bpcc_tgt = false ->
    is_heap_address bcgp_tgt = false ->

    (* (* NA mask *) *)
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    (* The caller's stack starts at the floor *)
    b_stk = cstk_hwm_floor cstk ->
    ↑Ntstack ⊆ F ->

    (* Well formed entry point *)
    (atbl_tgt ∈ₐ [btbl_tgt, etbl_tgt)) →
    (btbl_tgt < a_tbl_cgp)%a →
    (a_tbl_ehs < atbl_tgt)%a  →
    (0 <= nargs <= 7 )%nat →
    is_Some (bpcc_tgt + off_tgt)%a →
    (* The callee's stack is at least its minimum stack size plus the
       reserved space *)
    stk_callee_fits b_stk e_stk a_stk minstk_tgt →

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (* Trusted-stack invariant *)
    na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static

    (* Export table of the target compartment *)
    ∗ btbl_tgt ↦ₐ□ Cap RX Global bpcc_tgt epcc_tgt bpcc_tgt
    ∗ a_tbl_cgp ↦ₐ□ Cap RW Global bcgp_tgt ecgp_tgt bcgp_tgt
    ∗ atbl_tgt ↦ₐ□ WInt (encode_entry_point posture_tgt (Z.of_nat nargs) (Z.of_nat minstk_tgt) off_tgt)


    (* PRE-CONDITION *)
    ∗ na_own (tpool th) F
    (* Registers *)
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ[th] wcgp_caller
    ∗ cra ↦ᵣ[th] wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ[th] wct1_caller
    ∗ cs0 ↦ᵣ[th] wcs0_caller
    ∗ cs1 ↦ᵣ[th] wcs1_caller
    (* All the other registers *)
    ∗ regs[th] arg_rmap
    ∗ regs[th] rmap

    (* Stack frame *)
    ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
    (* The high-water-mark registers *)
    ∗ hwm_res cstk h

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ ◯(CSTK)[th] cstk


    ∗ ▷ ( (∃ mie arg_rmap' rmap',
            ⌜ is_arg_rmap arg_rmap' 8 ⌝
            ∗ ⌜ dom rmap' = dom rmap ∪ {[ ct1 ; cs0 ; cs1 ]} ⌝
            ∗ na_own (tpool th) F
            (* Registers *)
            ∗ PC ↦ₚ[th] Cap RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)
            ∗ cgp ↦ᵣ[th] Cap RW Global bcgp_tgt ecgp_tgt bcgp_tgt
            ∗ cra ↦ᵣ[th] (Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return)
            (* Stack register *)
            ∗ csp ↦ᵣ[th] callee_csp b_stk e_stk a_stk
            (* All the other registers *)
            (* Entry point of the target compartment *)
            ∗ ( [∗ map] rarg↦warg ∈ arg_rmap', rarg ↦ᵣ[th] warg
                                               ∗ (if decide (rarg ∈ dom_arg_rmap nargs)
                                                  then ⌜ arg_rmap !! rarg = Some warg ⌝
                                                  else ⌜warg = WInt 0⌝)
              )
            ∗ regs₀[th] rmap'

            (* Stack frame *)
            ∗ stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)
                (region_addrs_zeroes (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk))
            (* MSHWM is the callee's stack pointer *)
            ∗ hwm_res (cstack_push frame cstk)
                (stk_start_a (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk))

            (* Interpretation of the world and stack, at the moment of the switcher_call *)
            ∗ ◯(CSTK)[th] (cstack_push frame cstk)
          )
          ∨
          (
            ∃ rmap' stk_mem' rcgp rcra rcs0 rcs1,
              ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ na_own (tpool th) F
              (* Registers *)
              ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ[th] rcgp
              ∗ cra ↦ᵣ[th] rcra
              ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
              ∗ cs0 ↦ᵣ[th] rcs0
              ∗ cs1 ↦ᵣ[th] rcs1
              ∗ ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ[th] WInt 0
              (* All the other registers *)
              ∗ regs₀[th] rmap'

              (* Stack frame *)
              ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem'
              ∗ (∃ h', hwm_res cstk h')

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ ◯(CSTK)[th] cstk
              ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                  load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
          )
         -∗ safe[th]
        )
    ⊢ safe[th].
  Proof.
    (* Outline of the proof:
       - open the trusted-stack invariant;
       - [switcher_call_path_spec]: check the stack pointer, spill the
         callee-save registers, push the frame, clear the callee's stack and
         unseal the entry point; the spill fits on the caller's stack, which
         is at least the callee's minimum stack size plus the reserved space,
         and the entry point is sealed by the switcher; when the trusted
         stack is exhausted, [switcher_cc_spec_tstack_exhausted_known_to_known];
       - [switcher_decode_entry_path_known_spec]: load the callee and jump to it;
         its stack is at least its minimum stack size plus the reserved space,
         so the check passes;
       - [trusted_stack_inv_push_frame]: push the frame and close the trusted-stack
         invariant. *)
    intros a_tbl_cgp a_tbl_ehs wct1_caller frame.
    subst a_tbl_cgp a_tbl_ehs.
    iIntros (Hstk_mmio Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow Htbl_shadow Hbpcc_heap Hbcgp_heap Hstk_heap
             Hb_a Hfloor HE atbl_tgt_inbounds Hbtbl_cgp Hbtbl_ehs Hnargs Hentry Hminstk Hdom Harg_rmap
             Hret_jalr Hret_heap)
      "(#Hswitcher & #Hstatic & #Hinv_exp_tbl_pcc & #Hinv_exp_tbl_cgp & #Hinv_exp_tbl_entry
        & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hhwm
        & Hcstk & Hpost)".
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hhwm_ord & Hlocked) #Hts]".
    iAssert (hwm_regs (cstk_hwm_base cstk) h) with "[$Hmshwmb $Hmshwm]" as "Hhwm_regs".
    rewrite -Hfloor in Hhwm_ord.
    stk_unfold.

    assert ( exists wr0, rmap !! ct2 = Some wr0) as [wr0 Hwr0].
    { rewrite -/(is_Some (rmap !! ct2)).
      apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hregs") as "[Hct2 Hregs]"; first by simplify_map_eq.
    assert ( exists wr1, rmap !! ctp = Some wr1) as [wr1 Hwr1].
    { rewrite -/(is_Some (rmap !! ctp)).
      apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ctp with "Hregs") as "[Hctp Hregs]"; first by simplify_map_eq.

    (* Open the trusted-stack invariant *)
    iPoseProof "Hstatic" as "(#Hcode & #Hb_switcher & _ & Hswitcher_global)".
    iNamed "Hswitcher_global".
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed trusted_stack_inv_open "Hswitcher_inv".
    iDestruct (switcher_hazard_open with "Hsave_area Hhazard_slots") as "[Hhazard Hsave_area]";
      first done.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].

    (* [.Lswitch_csp_check] to [.Lswitcher_decode_entry] *)
    iEval (rewrite -switcher_call_entry_label) in "HPC".
    iApply (switcher_call_path_spec with
      "[- $HPC $Hcsp $Hct2 $Hctp $Hcs0 $Hcs1 $Hcra $Hcgp $Hct1 $Hstk $Hhwm_regs $Hmtdc
          $Hframeoffset $Hhazard $Htstk $Hb_switcher $Hcode]"); [done..| solve_addr |].
    iNext.
    iSplit; [ |iSplit; [ |iSplit; [ |iSplit] ] ]; cycle 1.
    { (* The entry point is sealed by the switcher: the unsealing does not
         fault *)
      iIntros (g_tstk h') "(%Hnot_entry & _)"; exfalso.
      apply Hnot_entry; subst wct1_caller.
      by eexists _, None. }
    { (* The trusted stack is exhausted *)
      iIntros (g_tstk h') "(%Hstk_bounds & %Hh' & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hcra
        & Hcgp & Hct1 & Hcells & Hstk & [Hmshwmb Hmshwm] & Hmtdc & Hframeoffset & Hhazard & Htstk)".
      iDestruct "Hhazard" as "[Hhazard_cell Hhazard_slots]".
      iSpecialize ("Hsave_area" with "Hhazard_cell").
      iApply (switcher_cc_spec_tstack_exhausted_known_to_known with
        "[$Hclose_switcher_inv $Hna $Hmtdc $Hsave_area $Hhazard_slots $Hframeoffset $HthreadID $Htstk
          $Hstatic
          $Hcstk_full $Hstk_interp
          $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hctp $Hct2 $Hct1 $Hcsp $Hcells $Hstk
          $Hargs $Hregs $Hcstk Hpost Hmshwmb Hmshwm Hlocked]"); [done..|].
      iSplitL "Hmshwmb Hmshwm Hlocked".
      { (* MSHWM is unchanged by the spill, or lowered to a spilled cell *)
        iFrame "Hmshwmb Hmshwm Hts". rewrite -Hfloor. iFrame "Hlocked".
        iPureIntro. pose proof Hstk_bounds as (Hb4 & _ & _). revert Hb4. stk_unfold.
        intros. solve_addr. }
      iNext; iIntros "H"; iApply "Hpost"; iRight; iExact "H". }
    { (* The caller's stack starts at the floor, at or below MSHWM: the
         zeroing of the callee's stack does not fault *)
      iIntros (g_tstk h' off) "(%Hstk_bounds & _ & _ & %Hh' & %Hlt & _)"; exfalso.
      pose proof Hstk_bounds as (Hb4 & _ & _). revert Hb4 Hlt. stk_unfold. intros. solve_addr. }
    { (* The callee-save registers fit on the caller's stack: the spill does
         not fault *)
      iIntros "(%Hnfits & _)". exfalso. apply Hnfits.
      by apply (stk_callee_fits_spill_fits _ _ _ minstk_tgt); [lia|]. }
    iNext; iIntros (g_tstk wsb π h')
      "(%Hwsb & _ & %Hstk_bounds & %Ha_frame & %Ha_frame_e & %Hh' & %Hcallee_h' & HPC & Hcs0
      & [%wcs1' Hcs1] & [%wct2' Hct2] & Hctp & Hcsp & Hcra & Hcgp & Hct1 & Hcells & Hstk
      & Hhwm_regs & Hmtdc & Hframeoffset & Hhazard & Hframe_csp & [%wtbl Hframe_tbl] & Hframe_cnt
      & [%tstk_next' Htstk] & _)".
    subst wct1_caller; rewrite /lword_of_word in Hwsb; simplify_eq.

    (* The cells of the callee's stack below MSHWM are cells of the zone,
       which hold 0 *)
    iMod (stack_region_zeroed_from_hwm with "Hstk Hhwm_regs") as "[Hstk [Hmshwmb Hmshwm]]".
    { rewrite /stk_callee_b. solve_addr. }
    (* MSHWM is at or below the spill area, which is full points-to *)
    iDestruct "Hcells" as "(Hc0 & Hc1 & Hc2 & Hc3)".
    iMod (hwm_pointsto_outside with "Hc0 Hmshwmb Hmshwm") as "(%Hout & Hc0 & Hmshwmb & Hmshwm)".
    iAssert (switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller)
      with "[$Hc0 $Hc1 $Hc2 $Hc3]" as "Hcells".
    pose proof Hstk_bounds as (Hb4 & Hb4' & Ha4).
    revert Hb4 Hb4' Ha4 Hcallee_h' Hout. stk_unfold. intros Hb4 Hb4' Ha4 Hcallee_h' Hout.
    assert (h' <= a_stk ^- 4)%Z as Hh'_spill by solve_addr.
    (* The cells between MSHWM and the callee's stack pointer join the zone,
       for the raise of MSHWM *)
    set (lo := (cstk_hwm_floor cstk ^+ (h' - cstk_hwm_floor cstk))%a).
    assert (lo = h' :> Z) as Hlo by (subst lo; clear -Hcallee_h' Hh'_spill Hb4; solve_addr).
    iMod (stack_region_zeroes_zone_acc _ _ lo ((a_stk ^- 4) ^+ (- StackEntry_reserved_space))
           with "Hstk") as "[Hzone Hzone_close]";
      [ clear -Hlo Hcallee_h' Hh'_spill Hb4; solve_addr
      | rewrite /StackEntry_reserved_space; clear -Hminstk Ha4 Hb4; solve_addr
      | rewrite /StackEntry_reserved_space; clear -Hminstk Ha4 Hb4; solve_addr |].

    (* [.Lswitcher_decode_entry]: load the callee and jump to it; only the low byte of the
       minimum stack size is encoded *)
    assert (Z.land (Z.of_nat minstk_tgt) 255 = Z.of_nat minstk_tgt `mod` 256)%Z as Hland.
    { change 255%Z with (Z.ones 8). rewrite Z.land_ones //. }
    set (minstk8 := Z.to_nat (Z.of_nat minstk_tgt `mod` 256)).
    assert (Z.land (Z.of_nat minstk_tgt) 255 = Z.of_nat minstk8) as Hminstk8.
    { subst minstk8. rewrite Hland Z2Nat.id //. apply Z.mod_pos_bound; lia. }
    assert (Z.of_nat minstk8 <= Z.of_nat minstk_tgt)%Z as Hminstk8_le.
    { rewrite -Hminstk8 Hland. apply Z.mod_le; lia. }
    assert (Z.of_nat minstk8 < 256)%Z as Hminstk8_lt.
    { rewrite -Hminstk8 Hland. apply Z.mod_pos_bound; lia. }
    iEval (rewrite encode_entry_point_minstk_land Hminstk8) in "Hinv_exp_tbl_entry".
    iApply (switcher_decode_entry_path_known_spec with
      "[- $Hinv_exp_tbl_pcc $Hinv_exp_tbl_cgp $Hinv_exp_tbl_entry $HPC $Hcs0 $Hcs1 $Hct1
        $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra $Hcsp $Hmshwmb $Hmshwm $Hzone $Hargs $Hregs $Hcode]");
      [done|solve_addr|done|lia|lia|done|done|done|done| | | |done|done| | |].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { tstack_unfold; solve_addr. }
    { tstack_unfold; solve_addr. }
    { rewrite !dom_delete_L Hdom. set_solver. }
    { rewrite Hlo. clear -Hhwm_ord Hcallee_h'; solve_addr. }
    iNext; iSplit; cycle 1.
    { (* The callee's stack is at least its minimum stack size plus the
         reserved space *)
      iIntros "(%Hsmall & _)"; exfalso.
      clear -Hsmall Hminstk Hminstk8_le Ha4.
      rewrite /StackEntry_reserved_space in Hsmall. clearbody minstk8. solve_addr. }
    iIntros (mie arg_rmap' rmap')
      "(_ & %Harg_rmap' & %Hrmap' & HPC & Hcgp & Hcra & Hcsp & [Hmshwmb Hmshwm] & Hzone
      & Hframe_tbl & Hargs & Hregs)".
    iDestruct ("Hzone_close" with "Hzone") as "Hstk".

    (* Push the frame and close the trusted-stack invariant *)
    (* The table cell holds the unsealed entry *)
    pose proof (tf_export_tbl_cell_entry (cf_tframe frame) Global btbl_tgt etbl_tgt atbl_tgt
               eq_refl Hbtbl_ehs ltac:(solve_addr) Htbl_shadow) as Htbl_cell.
    iDestruct "Hhazard" as "[Hhazard_cell Hhazard_slots]".
    iSpecialize ("Hsave_area" with "Hhazard_cell").
    iMod (trusted_stack_inv_push_frame frame cstk with
           "Hcstk_full Hcstk Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Hframe_csp
            Hframe_tbl Hframe_cnt Htstk Hstk_interp [Hcells]")
      as "[Hinv Hcstk]";
      [done|done|done|done|exact Hstk_bounds|done|done|by intros _
      |right; split; [done | exact Htbl_cell]|done| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".
    (* MSHWM is the callee's stack pointer; the floor is the caller's stack
       base *)
    iAssert (hwm_res (cstack_push frame cstk) ((a_stk ^- 4) ^+ (- StackEntry_reserved_space)))
      with "[Hmshwmb Hmshwm Hlocked]" as "Hhwm".
    { rewrite hwm_res_push_ktk //. iFrame "Hmshwmb Hmshwm Hlocked Hts".
      iPureIntro. rewrite /StackEntry_reserved_space. clear -Hhwm_ord Hminstk Ha4. solve_addr. }
    iApply "Hpost"; iLeft; iFrame "∗ %".
    iPureIntro; rewrite Hrmap' Hdom; set_solver.
  Qed.

End Switcher_KtK_Call.
