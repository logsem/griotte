From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel world_interp bitblast.
From griotte Require Import interp_weakening.
From griotte Require Import wp_rules_interp switcher_macros_spec.
From griotte Require Import rules proofmode monotone.
From griotte Require Import fundamental.
From griotte Require Import switcher_preamble.
From griotte Require Import interp_switcher_return switcher_trap_safety switcher_unwind switcher_helpers.
From griotte Require Import switcher_call_states switcher_call_world switcher_registers.
From griotte.switcher.call Require Import call_path.
From griotte Require Import map_simpl register_tactics proofmode.


Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** ** Stack cells and high-water mark *)

  (** What untrusted code holds, from the high-water-mark registers, the
      bounds of the thread's stack, and the stack addresses between MSHWMB
      and MSHWM Temporary. *)
  #[local] Lemma hwm_res_untrusted_of_regs W (cstk : CSTK) (mshwm_v : Z) :
    (cstk_hwm_base cstk <= mshwm_v)%Z →
    zone_temporary W (cstk_hwm_base cstk) mshwm_v →
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk) -∗
    hwm_regs (cstk_hwm_base cstk) mshwm_v -∗
    hwm_res_untrusted W cstk.
  Proof.
    iIntros (Hh Hzone) "#Hts Hhwm_regs".
    iExists mshwm_v. iSplitL; last (iPureIntro; exact Hzone).
    iApply (hwm_res_of_regs with "Hts Hhwm_regs"); done.
  Qed.

  (** The addresses of a valid stack capability, from its base up to [x],
      are Temporary. *)
  #[local] Lemma interp_stack_zone_temporary W C (b e a : Addr) (x : Z) :
    (x <= e)%Z →
    interp W C (Cap RWL Local b e a) -∗ ⌜zone_temporary W b x⌝.
  Proof.
    iIntros (Hx) "#Hspv".
    iDestruct (writeLocalAllowed_valid_cap_implies_full_cap_nonheap with "Hspv") as "Htemp";
      first done.
    iDestruct (big_sepL_pure_1 with "Htemp") as %Htemp.
    iPureIntro. intros a' Hba' Ha'x.
    assert (a' ∈ finz.seq_between b e) as Hin by (apply elem_of_finz_seq_between; solve_addr).
    apply list_elem_of_lookup in Hin as [k Hk].
    exact (Htemp k a' Hk).
  Qed.

  (** Close the free part of the caller's stack in the local map, with safe
      spilled words and callee's words that are unchanged or safe. *)
  #[local] Lemma interp_call_stk_close W C (b e a : Addr) (lv lc : list LWord)
    (wcs0 wcs1 wcgp wcra : LWord) :
    switcher_stk_bounds b e a →
    length (stk_free b e a) = length lv →
    interp W C wcs0 -∗
    interp W C wcs1 -∗
    interp W C wcgp -∗
    interp W C wcra -∗
    ([∗ list] k ↦ w ∈ lc, ⌜lv !! k = Some w⌝ ∨ interp W C w) -∗
    local_stk_opened W C (stk_free_b b a) (stk_free_e e a) lv -∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra -∗
    stack_region (stk_callee_b b a) (stk_callee_e e a) lc -∗
    local_region_map th W C ∅.
  Proof.
    iIntros (Hbounds Hlen_lv) "#Hcs0v #Hcs1v #Hcgpv #Hcrav Hlc Hstk_opened Hcells Hstk".
    iDestruct (switcher_stk_cells_stack_region with "Hcells Hstk") as "Hstk"; first done.
    iDestruct (stack_region_length with "Hstk") as %Hlen_stk.
    iApply (local_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk [Hlc]").
    { rewrite -Hlen_stk. exact Hlen_lv. }
    rewrite /stk_mem_join big_sepL_app.
    iFrame "Hlc". cbn.
    iSplitL; first (iRight; iExact "Hcs0v").
    iSplitL; first (iRight; iExact "Hcs1v").
    iSplitL; first (iRight; iExact "Hcgpv").
    iSplitL; first (iRight; iExact "Hcrav").
    done.
  Qed.

  (** The words of the callee's stack after the call path: unchanged below
      MSHWM, 0 above. *)
  #[local] Lemma interp_call_zeroed_words W C (b : Addr) (mshwm_v' : Z) (lv : list LWord) :
    ⊢ [∗ list] k ↦ w ∈ stack_zeroed_from b mshwm_v' (stk_mem_callee lv),
        ⌜lv !! k = Some w⌝ ∨ interp W C w.
  Proof.
    rewrite /stack_zeroed_from big_sepL_app. iSplit.
    - iApply big_sepL_forall. iIntros (k w Hk). iLeft. iPureIntro.
      apply lookup_take_Some in Hk as [Hk _].
      rewrite /stk_mem_callee in Hk. by apply lookup_take_Some in Hk as [Hk _].
    - iApply big_sepL_forall. iIntros (k w Hk). iRight.
      apply lookup_replicate in Hk as [-> _]. iApply interp_int.
  Qed.

  (** Integer words are safe. *)
  #[local] Lemma interp_call_ints_words W C (lc lv : list LWord) :
    Forall lword_int lc →
    ⊢ [∗ list] k ↦ w ∈ lc, ⌜lv !! k = Some w⌝ ∨ interp W C w.
  Proof.
    intros Hlc. iApply big_sepL_forall. iIntros (k w Hk). iRight.
    destruct (Forall_lookup_1 _ _ _ _ Hlc Hk) as [z ->]. iApply interp_int.
  Qed.

  (** ** Register files *)

  (** The register file of the caller, after the checks on the stack
      pointer wrote integers in [ct2] and [ctp], is safe. *)
  #[local] Lemma interp_call_regs_scratch W C (regs : LReg) (z2 zp : Z) :
    (∀ r, is_Some (regs !! r)) ->
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    interp_reg interp W C (<[ctp := (WInt zp : LWord)]> (<[ct2 := (WInt z2 : LWord)]> regs)).
  Proof.
    iIntros (Hfull) "#Hreg".
    iApply interp_reg_intro.
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iIntros (r v Hv).
    destruct (decide (r = ctp)) as [-> | Hctp].
    { rewrite lookup_insert_eq in Hv; simplify_eq. iApply interp_int. }
    rewrite lookup_insert_ne // in Hv.
    destruct (decide (r = ct2)) as [-> | Hct2].
    { rewrite lookup_insert_eq in Hv; simplify_eq. iApply interp_int. }
    rewrite lookup_insert_ne // in Hv.
    by iApply "Hreg".
  Qed.

  (** The registers of the exhausted path: [ca0] and [ca1] out of the
      registers that the call path does not use, and [ct1], [ct2] and
      [ctp] back in. *)
  #[local] Lemma interp_call_regs_exhausted (regs : LReg) (wct1 wct2 wctp : LWord) :
    (∀ r, is_Some (regs !! r)) ->
    regs[th] call_regs_without regs -∗
    ct1 ↦ᵣ[th] wct1 -∗
    ct2 ↦ᵣ[th] wct2 -∗
    ctp ↦ᵣ[th] wctp -∗
    ∃ (wca0 wca1 : LWord) (rmap0 : LReg),
      ca0 ↦ᵣ[th] wca0 ∗
      ca1 ↦ᵣ[th] wca1 ∗
      ⌜ dom rmap0 = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
      regs[th] rmap0.
  Proof.
    iIntros (Hfull) "Hregs Hct1 Hct2 Hctp".
    destruct (Hfull ca0) as [wca0 Hwca0].
    destruct (Hfull ca1) as [wca1 Hwca1].
    iDestruct (big_sepM_delete _ _ ca0 wca0 with "Hregs") as "[Hca0 Hregs]".
    { rewrite /call_regs_without !lookup_delete_ne //. }
    iDestruct (big_sepM_delete _ _ ca1 wca1 with "Hregs") as "[Hca1 Hregs]".
    { rewrite /call_regs_without !lookup_delete_ne //. }
    iDestruct (big_sepM_insert_2 _ _ ct1 wct1 with "[Hct1] Hregs") as "Hregs"; first iExact "Hct1".
    iDestruct (big_sepM_insert_2 _ _ ct2 wct2 with "[Hct2] Hregs") as "Hregs"; first iExact "Hct2".
    iDestruct (big_sepM_insert_2 _ _ ctp wctp with "[Hctp] Hregs") as "Hregs"; first iExact "Hctp".
    iExists wca0, wca1, _; iFrame "Hca0 Hca1 Hregs".
    iPureIntro.
    rewrite /call_regs_without !dom_insert_L !dom_delete_L (lregmap_full_dom _ Hfull).
    apply set_eq; intros r. pose proof (all_registers_s_correct r). set_solver.
  Qed.

  (** A full register file out of the argument registers, the other
      registers and the registers of the call path. *)
  #[local] Lemma interp_call_regs_full (arg_rmap rmap : LReg)
    (wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 : LWord) :
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->
    regs[th] arg_rmap -∗
    regs[th] rmap -∗
    csp ↦ᵣ[th] wcsp -∗
    ct2 ↦ᵣ[th] wct2 -∗
    ctp ↦ᵣ[th] wctp -∗
    cs0 ↦ᵣ[th] wcs0 -∗
    cs1 ↦ᵣ[th] wcs1 -∗
    cra ↦ᵣ[th] wcra -∗
    cgp ↦ᵣ[th] wcgp -∗
    ct1 ↦ᵣ[th] wct1 -∗
    ∃ regs, ⌜ ∀ r, is_Some (regs !! r) ⌝ ∗ registers_pointsto regs.
  Proof.
    iIntros (Hargs Hdom) "Hargs Hregs Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1".
    iDestruct (big_sepM_union with "[$Hargs $Hregs]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hargs Hdom. set_solver. }
    iDestruct (call_regs_insert (arg_rmap ∪ rmap) with "[Hregs] Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
      as "Hregs".
    { iApply (big_sepM_subseteq with "Hregs"). apply map_subseteq_spec.
      intros r w. rewrite /call_regs_without. intros Hr.
      by repeat (apply lookup_delete_Some in Hr as [_ Hr]). }
    iExists _; iFrame "Hregs"; iPureIntro.
    intros r. rewrite /call_regs_with. rewrite !lookup_insert_is_Some'.
    destruct (decide (r ∈ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} : gset RegName)))
      as [Hr|Hr]; first (rewrite !elem_of_union !elem_of_singleton in Hr; naive_solver).
    do 8 right. apply elem_of_dom. rewrite dom_union_L Hargs Hdom.
    pose proof (all_registers_s_correct r).
    rewrite elem_of_union elem_of_difference elem_of_union.
    destruct (decide (r ∈ dom_arg_rmap 8)); tauto.
  Qed.

  (** The frame of an untrusted caller, whose stack pointer is
      [Cap RWL Local b e a], with the word [wtbl] in its table cell.
      The saved registers are not read: the caller's spill area belongs to
      its world. *)
  Definition interp_call_frame (b e a : Addr) (wtbl : LWord) : cframe :=
    {| cf_tframe :=
         {| tf_csp := Cap RWL Local b e (stk_saved_a a);
            tf_export_tbl := wtbl;
            tf_error_count := 0 |};
       cf_saved :=
         {| cs_cra := WInt 0;
            cs_cgp := WInt 0;
            cs_cs0 := WInt 0;
            cs_cs1 := WInt 0 |};
       ccrel := Unknown_to_Unknown
    |}.

  (** The continuation of the caller, once its frame is pushed. The caller's
      stack starts at the base of the thread's stack, and its addresses
      between that base and its cursor are Temporary. *)
  #[local] Lemma interp_call_cont_frame W C (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (b e a : Addr) (wtbl : LWord) :
    disjoint_from_heap b e ->
    switcher_stk_bounds b e a ->
    b = cstk_hwm_base cstk ->
    interp W C (Cap RWL Local b e a) -∗
    top_cmpt_untrusted interp W C cstk -∗
    interp_cont interp cstk Ws Cs -∗
    interp_cont interp (cstack_push (interp_call_frame b e a wtbl) cstk) (W :: Ws) (C :: Cs).
  Proof.
    iIntros (Hstk_heap Hstk_bounds Hbase) "#Hspv #Htop Hcont".
    destruct Hstk_bounds as (Hba & Hba3 & Ha4).
    iDestruct (interp_stack_zone_temporary _ _ _ _ _ a with "Hspv") as %Hzone.
    { revert Hba3; stk_unfold; intros Hba3; solve_addr. }
    simpl.
    iFrame "Hcont".
    rewrite (tf_caller_a_saved _ true RWL Local b e a); [| done | done].
    rewrite ?cstack_eta.
    iSplit.
    { iSplit; first (iPureIntro; exact Hstk_heap).
      iApply (interp_weakeningEO_gen with "[] Hspv"); last (iIntros "!>" (Hg _); discriminate Hg).
      all: auto; revert Hba Hba3 Ha4; stk_unfold; solve_addr. }
    iFrame "Htop". iPureIntro. split; last exact Hbase.
    change (zone_temporary W (cstk_hwm_base cstk) a).
    rewrite -Hbase. exact Hzone.
  Qed.

  (** ** Failure and fault paths *)

  (** Failure path of [interp_expr_switcher_call]: the checks on the stack
      pointer fail, and the call is unwound by the return routine.
      [.Lcommon_force_unwind] sets the return values, so no register needs
      to be safe. MSHWM is [mshwm_v]. *)
  Lemma interp_switcher_call_force_unwind
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (a_tstk : Addr) (tstk_next : list LWord) (mshwm_v : Z) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    (∀ r, is_Some (regs !! r)) ->
    frame_match Ws Cs cstk W C ->

    thread_in th C -∗
    switcher_trap_safety -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) -∗
    switcher_hazard -∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" -∗
    registers_pointsto regs -∗
    world_resources W C -∗
    interp_cont interp cstk Ws Cs -∗
    hwm_res cstk mshwm_v -∗
    ◯(CSTK)[th] cstk -∗
    MIE ↦ₜ[th] InterruptDisabled -∗
    held (th := th) InterruptDisabled -∗
    safe[th].
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    (* Outline of the proof: [common_force_unwind_spec] sets the return
       values, then close the trusted-stack invariant and run the return routine
       ([switcher_return_unwind]) with the integer return values. *)
    iIntros (Hfull_rmap Hframe)
      "#Hthread #Hsafety Hopened Hmtdc Hframeoffset Hhazard Htstk HPC Hrmap Hworld_res Hcont
        Hhwm Hcstk Hmie Hheld".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[#Hinv_switcher #Hstatic]".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    destruct (Hfull_rmap ca0) as [wca0 Hwca0].
    destruct (Hfull_rmap ca1) as [wca1 Hwca1].
    rewrite /registers_pointsto.
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first exact Hwca0.
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]";
      first by rewrite lookup_delete_ne.
    iApply (common_force_unwind_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1)".
    iEval (rewrite -switcher_return_offset) in "HPC".
    iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
    iDestruct (big_sepM_insert_2 _ _ ca1 with "[Hca1] Hrmap") as "Hrmap"; first iExact "Hca1".
    iDestruct (big_sepM_insert_2 _ _ ca0 with "[Hca0] Hrmap") as "Hrmap"; first iExact "Hca0".
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hthread $Hinv_switcher $Hstatic $Htrap $Hworld_res $Hcont $Hhwm $Hna
               $Hcstk $Hmie $Hheld]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'.
      destruct (decide (r = ca0)); first naive_solver.
      destruct (decide (r = ca1)); first naive_solver.
      do 2 right. rewrite !lookup_delete_ne //. }
    iSplit; iApply interp_int.
  Qed.

  (** Failure path of [interp_expr_switcher_call]: the trusted stack is
      exhausted. MSHWM is unchanged by the spill, or lowered to a spilled
      cell. *)
  Lemma interp_switcher_call_tstack_exhausted
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (b e a : Addr) (lv : list LWord)
    (wcs0 wcs1 wcra wcgp wct1 : LWord) (g_tstk : Locality)
    (a_tstk : Addr) (tstk_next : list LWord) (mshwm_v mshwm_v' : Z) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    (∀ r, is_Some (regs !! r)) ->
    frame_match Ws Cs cstk W C ->
    disjoint_from_mmio b e ->
    length (stk_free b e a) = length lv ->
    (cstk_hwm_base cstk <= mshwm_v)%Z ->
    zone_temporary W (cstk_hwm_base cstk) mshwm_v ->

    thread_in th C -∗
    switcher_trap_safety -∗
    interp W C wcs0 -∗
    interp W C wcs1 -∗
    interp W C wcra -∗
    interp W C wcgp -∗
    interp W C (Cap RWL Local b e a) -∗
    top_cmpt_untrusted interp W C cstk -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    local_stk_opened W C (stk_free_b b a) (stk_free_e e a) lv -∗
    perm_resources C -∗
    regs[th] call_regs_without regs -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    MIE ↦ₜ[th] InterruptDisabled -∗
    held (th := th) InterruptDisabled -∗
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk) -∗
    ( ⌜ switcher_stk_bounds b e a ⌝ ∗
      ⌜ (mshwm_v' = mshwm_v ∨ (cstk_hwm_base cstk <= mshwm_v' < mshwm_v ∧ stk_spill_a a <= mshwm_v' < a))%Z ⌝ ∗
      PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
      cs0 ↦ᵣ[th] WInt (e_trusted_stack - b_trusted_stack) ∗
      cs1 ↦ᵣ[th] wcs1 ∗
      ctp ↦ᵣ[th] WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      ct2 ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
      csp ↦ᵣ[th] Cap RWL Local b e (stk_saved_a a) ∗
      cra ↦ᵣ[th] wcra ∗
      cgp ↦ᵣ[th] wcgp ∗
      ct1 ↦ᵣ[th] wct1 ∗
      switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
      stack_region (stk_callee_b b a) (stk_callee_e e a) (stk_mem_callee lv) ∗
      hwm_regs (cstk_hwm_base cstk) mshwm_v' ∗
      mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      switcher_hazard ∗
      [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
      safe[th] ).
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    (* Outline of the proof: [switch_trusted_stack_exhausted_path_spec]
       restores the registers, clears the others and returns,
       [local_call_stk_close] closes the caller's stack frame,
       then close the trusted-stack invariant and
       [switcher_jump_to_caller_cases_spec]. *)
    iIntros (Hfull Hframe Hstk_mmio Hlen_lv Hhb_h Hzone)
      "#Hthread #Hsafety #Hcs0v #Hcs1v #Hcrav #Hcgpv #Hspv #Htop Hopened Hstk_opened Hperm Hrmap
      Hcont Hcstk Hmie Hheld #Hts
      (%Hstk_bounds & %Hh' & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hcra & Hcgp & Hct1 &
        Hcells & Hstk & Hhwm_regs
      & Hmtdc & Hframeoffset & Hhazard & Htstk)".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[_ #Hstatic]".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    (* The untrusted caller's stack addresses up to MSHWM stay Temporary *)
    iDestruct (hwm_res_untrusted_of_regs W cstk mshwm_v' with "Hts Hhwm_regs") as "Hhwm".
    { destruct Hh' as [-> | Hh'']; lia. }
    { eapply zone_temporary_lower; [|exact Hzone]. destruct Hh' as [-> | Hh'']; lia. }
    iDestruct (interp_call_regs_exhausted with "Hrmap Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; first done.
    iAssert (⌜th ≠ CtxSwitch⌝)%I as %Huser; first (iNamed "Hopened"; done).
    iApply (switch_trusted_stack_exhausted_path_spec with
      "[- $HPC $Hcsp $Hcells $Hrmap0 $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hmie $Hheld]");
      [done|done|done|done|].
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "((%Hrcgp & %Hrcra & %Hrcs0 & %Hrcs1) & %Hrmap' & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1
      & Hcsp & Hcells & Hrmap & Hlc)".
    iDestruct (interp_load_heap with "Hcs0v") as "#Hrcs0v"; first done.
    iDestruct (interp_load_heap with "Hcs1v") as "#Hrcs1v"; first done.
    iDestruct (interp_load_heap with "Hcrav") as "#Hrcrav"; first done.
    iDestruct (interp_load_heap with "Hcgpv") as "#Hrcgpv"; first done.

    (* Close the caller's stack frame *)
    iDestruct (interp_call_stk_close _ _ b e a lv (stk_mem_callee lv) with
                "Hcs0v Hcs1v Hcgpv Hcrav [] Hstk_opened Hcells Hstk") as "Hlocal";
      [done|done| |].
    { iApply big_sepL_forall. iIntros (k w Hk). iLeft. iPureIntro.
      rewrite /stk_mem_callee in Hk. by apply lookup_take_Some in Hk as [Hk _]. }

    (* Jump back to the caller, or unwind the call when the jump faults;
       close the trusted-stack invariant first *)
    iApply (switcher_jump_to_caller_cases_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ InterruptDisabled with
             "Htrap Hthread Hrcrav Hrcgpv Hrcs0v Hrcs1v Hspv [] [] Htop Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
              Hrmap Hhwm Hcont Hlc [-]");
      [done|done|done|by intros|intros Hcs; by destruct Huser|iApply interp_int|iApply interp_int|].
    iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
    iModIntro.
    rewrite world_resources_split.
    iFrame "Hlocal Hperm Hna Hcstk".
  Qed.

  (** Fault of the first spill: the checks leave the value of MSHWMB in
      [ct2] and [ctp], and the other registers hold the caller's safe words.
      Close the caller's stack and the trusted-stack invariant, and give the
      fault to the untrusted caller. MSHWM is unchanged. *)
  Lemma interp_switcher_call_spill_fault
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (b e a : Addr) (lv : list LWord)
    (wcs0 wcs1 wcra wcgp wct1 : LWord)
    (a_tstk : Addr) (tstk_next : list LWord) (mshwm_v : Z) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    (∀ r, is_Some (regs !! r)) ->
    regs !! csp = Some (Cap RWL Local b e a : LWord) -> regs !! cs0 = Some wcs0 ->
    regs !! cs1 = Some wcs1 -> regs !! cra = Some wcra -> regs !! cgp = Some wcgp ->
    regs !! ct1 = Some wct1 ->
    frame_match Ws Cs cstk W C ->
    (cstk_hwm_base cstk <= mshwm_v)%Z ->
    zone_temporary W (cstk_hwm_base cstk) mshwm_v ->

    thread_in th C -∗
    switcher_trap_safety -∗
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    top_cmpt_untrusted interp W C cstk -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    local_stk_opened W C (stk_free_b b a) (stk_free_e e a) lv -∗
    perm_resources C -∗
    regs[th] call_regs_without regs -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    MIE ↦ₜ[th] InterruptDisabled -∗
    held (th := th) InterruptDisabled -∗
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk) -∗
    ( ⌜ ¬ stk_spill_fits b e a ⌝ ∗
      csp ↦ᵣ[th] Cap RWL Local b e a ∗
      ct2 ↦ᵣ[th] WInt (cstk_hwm_base cstk) ∗
      ctp ↦ᵣ[th] WInt (cstk_hwm_base cstk) ∗
      cs0 ↦ᵣ[th] wcs0 ∗
      cs1 ↦ᵣ[th] wcs1 ∗
      cra ↦ᵣ[th] wcra ∗
      cgp ↦ᵣ[th] wcgp ∗
      ct1 ↦ᵣ[th] wct1 ∗
      stack_region (stk_free_b b a) (stk_free_e e a) lv ∗
      hwm_regs (cstk_hwm_base cstk) mshwm_v ∗
      mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      switcher_hazard ∗
      [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
      trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
        (HO th) ).
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    iIntros (Hfull Hcsp Hcs0 Hcs1 Hcra Hcgp Hct1 Hframe Hhb_h Hzone)
      "#Hthread #Hsafety #Hreg #Htop Hopened Hstk_opened Hperm Hrmap Hcont Hcstk Hmie Hheld #Hts
      (_ & Hcsp & Hct2 & Hctp & Hcs0 & Hcs1 & Hcra & Hcgp & Hct1 & Hstk & Hhwm_regs
      & Hmtdc & Hframeoffset & Hhazard & Htstk)".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    iAssert (⌜th ≠ CtxSwitch⌝)%I as %Huser; first (iNamed "Hopened"; done).
    iDestruct (hwm_res_untrusted_of_regs W cstk mshwm_v with "Hts Hhwm_regs") as "Hhwm";
      [done|done|].
    iEval (rewrite -(hwm_res_kind_user _ _ Huser)) in "Hhwm".
    iDestruct (local_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
      as "Hlocal"; first done.
    { iApply big_sepL_intro; iIntros "!>" (k w Hk); by iLeft. }
    iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1") as "Hrmap".
    iEval (rewrite (call_regs_with_id regs) //) in "Hrmap".
    iApply (interp_trap_safe_untrusted _ W C cstk Ws Cs
              (<[ctp := (WInt (cstk_hwm_base cstk) : LWord)]>
                (<[ct2 := (WInt (cstk_hwm_base cstk) : LWord)]> regs))
             with "Htrap Hthread [] Htop [-]"); [ |done| |].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    { by iApply interp_call_regs_scratch. }
    iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
    iModIntro.
    rewrite world_resources_split.
    iFrame "Hrmap Hhwm Hlocal Hperm Hcont Hna Hcstk".
    iExists InterruptDisabled; iFrame "Hmie Hheld"; iPureIntro; by intros.
  Qed.

  (** Fault of the unsealing: close the caller's stack, push the frame,
      with the table word [WInt 0] and any word in its table cell, close the
      trusted-stack invariant, and unwind the call. *)
  Lemma interp_switcher_call_unseal_fault
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (b e a : Addr) (lv : list LWord)
    (wcs0 wcs1 wcra wcgp wct1 : LWord) (g_tstk : Locality) (a_tstk : Addr) (mshwm_v mshwm_v' : Z) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    let a_free := (a_next ^+ TrustedStackFrame_size) in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp) in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount) in
    (∀ r, is_Some (regs !! r)) ->
    frame_match Ws Cs cstk W C ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->
    length (stk_free b e a) = length lv ->
    b = cstk_hwm_base cstk ->
    (cstk_hwm_base cstk <= mshwm_v)%Z ->

    thread_in th C -∗
    switcher_trap_safety -∗
    interp W C wcs0 -∗
    interp W C wcs1 -∗
    interp W C wcra -∗
    interp W C wcgp -∗
    interp W C (Cap RWL Local b e a) -∗
    top_cmpt_untrusted interp W C cstk -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    local_stk_opened W C (stk_free_b b a) (stk_free_e e a) lv -∗
    perm_resources C -∗
    regs[th] call_regs_without regs -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    MIE ↦ₜ[th] InterruptDisabled -∗
    held (th := th) InterruptDisabled -∗
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk) -∗
    ( ⌜ ¬ ∃ wsb π, wct1 = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ ∗
      ⌜ switcher_stk_bounds b e a ⌝ ∗
      ⌜ (b_trusted_stack + tstack_frame_offset (S (length cstk'.(cstk_frames))))%a = Some a_next ⌝ ∗
      ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
      ⌜ (mshwm_v' = mshwm_v ∨ (cstk_hwm_base cstk <= mshwm_v' < mshwm_v ∧ stk_spill_a a <= mshwm_v' < a))%Z ⌝ ∗
      ⌜ (stk_callee_b b a <= mshwm_v')%Z ⌝ ∗
      cs0 ↦ᵣ[th] SealRange (true,true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
      (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
      (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
      ctp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack a_next ∗
      csp ↦ᵣ[th] chopped_csp b e a ∗
      cra ↦ᵣ[th] wcra ∗
      cgp ↦ᵣ[th] WInt mshwm_v' ∗
      ct1 ↦ᵣ[th] - ∗
      switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
      stack_region (stk_callee_b b a) (stk_callee_e e a)
        (stack_zeroed_from (stk_callee_b b a) mshwm_v' (stk_mem_callee lv)) ∗
      hwm_regs (cstk_hwm_base cstk) mshwm_v' ∗
      mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (S (length cstk'.(cstk_frames)))) ∗
      switcher_hazard ∗
      a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
      a_export_table ↦ₐ - ∗
      a_error_count ↦ₐ WInt 0 ∗
      (∃ tstk_next', [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]]) ∗
      £ 2 -∗
      trap_safe (switcher_label_pc ".Lswitcher_decode_entry") ⊤
        (HO th) ).
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hfull Hframe Hstk_mmio Hstk_heap Hlen_lv Hbase Hhb_h)
      "#Hthread #Hsafety #Hcs0v #Hcs1v #Hcrav #Hcgpv #Hspv #Htop Hopened Hstk_opened Hperm Hrmap
       Hcont Hcstk Hmie Hheld #Hts
       (_ & %Hstk_bounds & %Ha_next & %Ha_next_e & %Hh' & %Hcallee_h' & Hcs0 & [%wcs1' Hcs1]
         & [%wct2' Hct2] & Hctp
       & Hcsp & Hcra & Hcgp & [%wct1' Hct1] & Hcells & Hstk & Hhwm_regs & Hmtdc & Hframeoffset
       & Hhazard & Hframe_csp & [%wtbl Hframe_tbl] & Hframe_cnt & [%tstk_next' Htstk] & _)".
    set (frame := interp_call_frame b e a (lword_of_word (WInt 0))).
    (* Close the caller's stack frame: the words of the callee's stack below
       MSHWM are unchanged, and those above are 0 *)
    iDestruct (interp_call_stk_close _ _ b e a lv with
                "Hcs0v Hcs1v Hcgpv Hcrav [] Hstk_opened Hcells Hstk") as "Hlocal";
      [done|done| |].
    { iApply interp_call_zeroed_words. }
    (* MSHWM is unchanged by the push of an untrusted caller's frame *)
    iDestruct (hwm_res_of_regs with "Hts Hhwm_regs") as "Hhwm".
    { destruct Hh' as [-> | Hh'']; solve_addr. }
    iEval (rewrite -(hwm_res_push frame cstk mshwm_v')) in "Hhwm".
    iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1") as "Hrmap".
    iApply (trap_safe_unwind_logrel_of_safety _ _ (cstack_push frame cstk) (W :: Ws) (C :: Cs)
             with "Hthread Hsafety [] [-]").
    { by apply call_regs_with_full. }
    { simpl. split; auto; first apply related_sts_pub_refl_world.
      split; [reflexivity|]; split; done. }
    { (* The unsealing is not the first spill *)
      apply trap_no_resume_switcher_pc. by vm_compute. }
    { (* The fault is in the switcher *)
      iLeft; iPureIntro. apply switcher_fault_pc_cap. }
    (* The frame's table word is [WInt 0] *)
    iMod (trusted_stack_inv_opened_push frame cstk with
           "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk []")
      as "[Hna Hcstk]"; [done..|by left| |].
    { by rewrite /cframe_stk_own /=. }
    iModIntro.
    rewrite world_resources_split.
    iFrame "Hrmap Hhwm Hlocal Hperm Hcstk Hna".
    iSplitL "Hcont"; first (iApply (interp_call_cont_frame with "Hspv Htop Hcont"); done).
    iExists InterruptDisabled; iFrame "Hmie Hheld"; iPureIntro; by intros.
  Qed.

  (** The callee's stack is too small: push the frame, whose table cell
      holds the unsealed entry, close the trusted-stack invariant, and return to
      the caller through the return routine. MSHWM is [mshwm_v]. *)
  Lemma interp_switcher_call_stack_too_small
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (b e a : Addr) (a_tstk : Addr) (tstk_next : list LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr) (nargs : nat)
    (arg_rmap rmap : LReg) (mshwm_v : Z) :
    let frame := interp_call_frame b e a (Cap RO g_tbl b_tbl e_tbl a_tbl) in
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    let a_free := (a_next ^+ TrustedStackFrame_size) in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp) in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount) in
    frame_match Ws Cs cstk W C ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->
    switcher_stk_bounds b e a ->
    b = cstk_hwm_base cstk ->
    (b_trusted_stack + tstack_frame_offset (S (length cstk'.(cstk_frames))))%a = Some a_next ->
    (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    tf_export_tbl_ok (cf_tframe frame) ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    thread_in th C -∗
    switcher_trap_safety -∗
    interp W C (Cap RWL Local b e a) -∗
    top_cmpt_untrusted interp W C cstk -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    world_resources W C -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    hwm_res (cstack_push frame cstk) mshwm_v -∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S (length cstk'.(cstk_frames)))) -∗
    switcher_hazard -∗
    a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) -∗
    a_error_count ↦ₐ WInt 0 -∗
    [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    ( PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_too_small" ∗
      cs0 ↦ᵣ[th] - ∗
      cs1 ↦ᵣ[th] - ∗
      ct1 ↦ᵣ[th] - ∗
      ct2 ↦ᵣ[th] - ∗
      ctp ↦ᵣ[th] - ∗
      cgp ↦ᵣ[th] - ∗
      cra ↦ᵣ[th] - ∗
      csp ↦ᵣ[th] Cap RWL Local (stk_callee_b b a) (stk_callee_e e a) (stk_saved_a a) ∗
      a_export_table ↦ₐ Cap RO g_tbl b_tbl e_tbl a_tbl ∗
      ( [∗ map] r↦w ∈ arg_rmap,
          r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
      regs[th] rmap ∗
      MIE ↦ₜ[th] InterruptDisabled ∗
      held (th := th) InterruptDisabled -∗
      safe[th] ).
  Proof.
    intros frame a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hframe Hstk_mmio Hstk_heap Hstk_bounds Hbase Ha_next Ha_next_e Htbl_cell Hargs Hdom)
      "#Hthread #Hsafety #Hspv #Htop Hopened Hworld_res Hcont Hcstk Hhwm Hmtdc Hframeoffset Hhazard
       Hframe_csp Hframe_cnt Htstk
       (HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wct1' Hct1] & [%wct2' Hct2] & [%wctp' Hctp]
       & [%wcgp' Hcgp] & [%wcra' Hcra] & Hcsp & Hframe_tbl & Hparams & Hrest & Hmie & Hheld)".
    iMod (trusted_stack_inv_opened_push frame cstk with
           "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk []")
      as "[Hna Hcstk]"; [done|done|done|done|done|done|done|right; split; [done | exact Htbl_cell]| |].
    { by rewrite /cframe_stk_own /=. }
    iDestruct (big_sepM_sep with "Hparams") as "[Hparams _]".
    iDestruct (interp_call_regs_full with "Hparams Hrest Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
      as (regs) "[%Hfull Hregs]"; [done|done|].
    iDestruct (interp_call_cont_frame _ _ _ _ _ _ _ _ (Cap RO g_tbl b_tbl e_tbl a_tbl)
                with "Hspv Htop Hcont") as "Hcont"; [done|done|done|].
    iApply (switcher_call_stack_too_small_unwind_of_safety _ _ (cstack_push frame cstk)
             (W :: Ws) (C :: Cs) regs mshwm_v
             with "[$HPC $Hregs $Hthread $Hsafety $Hworld_res $Hhwm $Hna $Hcstk $Hcont $Hmie
                    $Hheld]");
      first done.
    simpl. split; [apply related_sts_pub_refl_world|done].
  Qed.

  (** ** The call routine *)

  Lemma interp_expr_switcher_call_gen (W : WORLD) (C : CmptName) :
    switcher_trap_safety
    ⊢ interp_expr_at InterruptDisabled interp (interp_cont interp) W C
        (Cap XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    (* Outline of the proof:
       - open the trusted-stack invariant;
       - when the stack pointer is not a valid stack capability, its checks
         fail ([interp_switcher_call_force_unwind]) or the first spill
         faults ([switch_entry_first_spill_fail_spec], or
         [switch_entry_first_spill_above_spec] when its cursor is above the
         top and the furthest cell of the spill within bounds);
       - when the base of the stack pointer is not MSHWMB, the checks fail
         ([switch_csp_check_spec], [interp_switcher_call_force_unwind]);
       - [world_resources_split], [local_call_stk_open]: open the free part
         of the caller's stack in the local map; its cells below MSHWM hold
         0;
       - [switcher_call_path_spec]: check the stack pointer, spill the
         callee-save registers, push the frame, clear the callee's stack and
         unseal the entry point; its fault and failure exits close through
         [interp_switcher_call_unseal_fault],
         [interp_switcher_call_tstack_exhausted] and
         [interp_switcher_call_spill_fault]; the zeroing does not fault;
       - [ot_switcher_entry_prop]: the entry point satisfies the sealing
         predicate of the switcher;
       - the cells between MSHWM and the callee's stack pointer join the
         zone; [switcher_decode_entry_path_spec]: check the size of the
         callee's stack, raise MSHWM, load the callee and jump to it; when
         the stack is too small, [interp_switcher_call_stack_too_small];
       - [interp_call_stk_close]: close the caller's stack frame, and rejoin
         the world premise;
       - [trusted_stack_inv_opened_push]: push the frame and close the trusted-stack
         invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros "#Hsafety %cstk %Ws %Cs %regs
      (#Hthread & #Htv & Hregs & #Htop & HPC & Hrmap & Hhwm & Hworld_res & Hcred & Hcont & Hna
       & Hcstk & %Hframe & _ & Hmie & Hheld)".
    iDestruct "Hregs" as "[%Hfull_rmap #Hreg]".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[#Hinv_switcher #Hstatic]".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    iPoseProof "Hstatic" as "(#Hcode & #Hb_switcher & _)".

    (* Open the trusted-stack invariant *)
    iMod (trusted_stack_inv_open_call with "Hinv_switcher Hna")
      as (a_tstk cstk' tstk_next)
         "(%Huser & %Hlen_cstk & %Ha_tstk_e & Hopened & Hmtdc & Hframeoffset & Hhazard & Htstk)".

    (* The high-water mark, at a user thread: the stack addresses between
       MSHWMB and MSHWM are Temporary *)
    iEval (rewrite (hwm_res_kind_user _ _ Huser)) in "Hhwm".
    iDestruct "Hhwm" as (mshwm_v) "[ [(Hmshwmb & Hmshwm & %Hhb_h) #Hts] %Hzone]".

    (* The registers of the call path *)
    destruct (Hfull_rmap csp) as [wcsp Hwcsp].
    destruct (Hfull_rmap ct2) as [wct2 Hwct2].
    destruct (Hfull_rmap ctp) as [wctp Hwctp].
    destruct (Hfull_rmap cs0) as [wcs0 Hwcs0].
    destruct (Hfull_rmap cs1) as [wcs1 Hwcs1].
    destruct (Hfull_rmap cra) as [wcra Hwcra].
    destruct (Hfull_rmap cgp) as [wcgp Hwcgp].
    destruct (Hfull_rmap ct1) as [wct1 Hwct1].
    iDestruct (call_regs_extract with "Hrmap")
      as "(Hcsp & Hct2 & Hctp & Hcs0 & Hcs1 & Hcra & Hcgp & Hct1 & Hrmap)"; [done..|].
    iDestruct ("Hreg" $! csp with "[//]") as "#Hspv".
    iDestruct ("Hreg" $! cs0 with "[//]") as "#Hcs0v".
    iDestruct ("Hreg" $! cs1 with "[//]") as "#Hcs1v".
    iDestruct ("Hreg" $! cra with "[//]") as "#Hcrav".
    iDestruct ("Hreg" $! cgp with "[//]") as "#Hcgpv".
    iDestruct ("Hreg" $! ct1 with "[//]") as "#Hct1v".

    (* Is the stack pointer a valid stack capability, whose cursor is not
       above its top? *)
    iAssert (⌜(∃ b e a, wcsp = Cap RWL Local b e a ∧ (b < e)%a ∧ (a <= e)%a)
            ∨ (∀ b e a, wcsp.(lw) = Cap RWL Local b e a → (e <= b)%a ∨ (e < a)%a)⌝)%I
      as %[(b & e & a & -> & Hbe & Hae) | Hnot_stk].
    { destruct wcsp as [ [| [t p g b e a|] | |] π]; try (iPureIntro; right; intros; discriminate).
      destruct t; [|iPureIntro; right; intros; discriminate].
      destruct (decide (p = RWL ∧ g = Local)) as [ [-> ->] | Hpg].
      - destruct (decide (b < e ∧ a <= e)%a) as [ [Hbe Hae] | Hbae].
        + iDestruct (interp_wl_noid with "Hspv") as %->; [done|solve_addr|].
          iPureIntro; left; by eexists _, _, _.
        + iPureIntro; right; intros ??? Heq; inversion Heq; subst; solve_addr.
      - iPureIntro; right; intros ??? Heq; inversion Heq; subst; tauto. }
    2: { (* The stack pointer is not a valid stack capability: the spill
            faults. Is the furthest cell of the spill within its bounds? *)
         iAssert (⌜(∃ b e a, wcsp = Cap RWL Local b e a ∧
                              stk_spill_ok a ∧ stk_spill_a a ∈ₐ [b, e))
                 ∨ (∀ b e a a4, wcsp.(lw) = Cap RWL Local b e a →
                                (a + (SpillSlot_cs0 - SpillSlot_size))%a = Some a4 →
                                (a4 < b)%a ∨ (e <= a4)%a)⌝)%I
           as %[(b & e & a & -> & Ha4 & Ha4_in) | Hfirst].
         { destruct wcsp as [ [| [t p g b e a|] | |] π]; try (iPureIntro; right; intros; discriminate).
           destruct t; [|iPureIntro; right; intros; discriminate].
           destruct (decide (p = RWL ∧ g = Local)) as [ [-> ->] | Hpg]; cycle 1.
           { iPureIntro; right; intros ???? Heq; inversion Heq; subst; tauto. }
           destruct (a + -4)%a as [a4|] eqn:Ha4; cycle 1.
           { iPureIntro; right; intros ???? Heq Ha4'; inversion Heq; subst.
             change (SpillSlot_cs0 - SpillSlot_size)%Z with (-4)%Z in Ha4'. congruence. }
           destruct (decide (a4 ∈ₐ [b, e))) as [Ha4_in|Ha4_out]; cycle 1.
           { iPureIntro; right; intros ???? Heq Ha4'; inversion Heq; subst.
             change (SpillSlot_cs0 - SpillSlot_size)%Z with (-4)%Z in Ha4'.
             rewrite Ha4 in Ha4'; simplify_eq; solve_addr. }
           iDestruct (interp_wl_noid with "Hspv") as %->; [done|solve_addr|].
           iPureIntro; left; exists b, e, a; split; first done.
           stk_unfold. split; solve_addr. }
         2: {
           (* [.Lswitch_csp_check]: checks on the stack pointer *)
           iEval (rewrite -switcher_call_entry_label) in "HPC".
           iApply (switch_csp_check_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hmshwmb $Hcode]").
           iNext; iIntros "[(%Hchecked & _ & HPC & Hcsp & Hct2 & Hctp & Hmshwmb)
                           | (_ & %zct2 & %zctp & HPC & Hcsp & Hct2 & Hctp & Hmshwmb)]";
             cycle 1.
           { (* The checks fail: force the unwinding of the call *)
             iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
               as "Hrmap".
             iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm"; first done.
             iApply (interp_switcher_call_force_unwind with
               "Hthread Hsafety Hopened Hmtdc Hframeoffset Hhazard Htstk HPC Hrmap Hworld_res
                 Hcont Hhwm Hcstk Hmie Hheld");
               [by apply call_regs_with_full|done]. }
           (* The first store faults, and nothing is written: close the
              trusted-stack invariant, and unwind the call *)
           iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
           iPoseProof (hwm_closed_user th Huser) as "Hcl".
           iApply (switch_entry_first_spill_fail_spec with "[- $HPC $Hcsp $Hcs0 $Hcl $Hcode]");
             [done | done |].
           iIntros "[Hcsp Hcs0] _".
           iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
             as "Hrmap".
           iEval (rewrite (call_regs_with_id regs) //) in "Hrmap".
           iDestruct (hwm_res_untrusted_of_regs W cstk mshwm_v with "Hts [$Hmshwmb $Hmshwm]")
             as "Hhwm"; [done|done|].
           iEval (rewrite -(hwm_res_kind_user _ _ Huser)) in "Hhwm".
           iApply (interp_trap_safe_untrusted _ W C cstk Ws Cs
                     (<[ctp := (WInt (cstk_hwm_base cstk) : LWord)]>
                (<[ct2 := (WInt (cstk_hwm_base cstk) : LWord)]> regs))
                    with "Htrap Hthread [] Htop [-]");
             [ |done| |iModIntro;
                        iFrame "Hrmap Hhwm Hworld_res Hcont Hna Hcstk";
                        iExists InterruptDisabled; iFrame "Hmie Hheld"; iPureIntro; by intros].
           { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
           (* A fault of the first spill: the registers are safe *)
           by iApply interp_call_regs_scratch. }
         (* The cursor is above the top, and the furthest cell within
            bounds: open the caller's stack from that cell to the top *)
         destruct (Hnot_stk b e a eq_refl) as [Heb|Hea]; first (revert Ha4_in; stk_unfold; solve_addr).
         iDestruct (interp_cap_disjoint_wl with "Hspv") as %[Hstk_mmio _]; first done.
         iDestruct (world_resources_split with "Hworld_res") as "[Hlocal Hperm]".
         iDestruct (local_call_stk_open _ _ b e a (stk_spill_a a) e with "Hspv Hlocal")
           as (lv) "(Hstk & Hstk_opened)"; [solve_addr | solve_addr |].
         iDestruct (stack_region_length with "Hstk") as %Hlen_lv.

         (* [.Lswitch_csp_check]: checks on the stack pointer *)
         iEval (rewrite -switcher_call_entry_label) in "HPC".
         iApply (switch_csp_check_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hmshwmb $Hcode]").
         iNext; iIntros "[(_ & _ & HPC & Hcsp & Hct2 & Hctp & Hmshwmb)
                         | (_ & %zct2 & %zctp & HPC & Hcsp & Hct2 & Hctp & Hmshwmb)]"; cycle 1.
         { (* The base of the stack pointer is not MSHWMB: force the
              unwinding of the call *)
           iDestruct (local_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
             as "Hlocal"; first done.
           { iApply big_sepL_intro; iIntros "!>" (k w Hk); by iLeft. }
           iAssert (world_resources W C) with "[Hlocal Hperm]" as "Hworld_res".
           { rewrite world_resources_split. iFrame "Hlocal Hperm". }
           iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
             as "Hrmap".
           iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm"; first done.
           iApply (interp_switcher_call_force_unwind with
             "Hthread Hsafety Hopened Hmtdc Hframeoffset Hhazard Htstk HPC Hrmap Hworld_res Hcont
              Hhwm Hcstk Hmie Hheld");
             [by apply call_regs_with_full|done]. }
         (* The first stores write the cells of the spill area below the
            top, and the store at the top faults: close the trusted-stack
            invariant and the caller's stack, and unwind the call *)
         iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
         iPoseProof (hwm_closed_user th Huser) as "Hcl".
         iApply (switch_entry_first_spill_above_spec with
                  "[- $HPC $Hcsp $Hcs0 $Hcs1 $Hcgp $Hcra $Hstk $Hmshwmb $Hmshwm $Hcl $Hcode]");
           [done..|].
         iIntros (k off mshwm_v' [Hk Hk_bounds] Hoff Hh')
           "(Hcsp & Hcs0 & Hcs1 & Hcgp & Hcra & Hstk & Hhwm_regs) _".
         iDestruct (stack_region_of_pointsto with "Hstk") as "Hstk".
         iDestruct (local_call_stk_close _ _ _ _ lv (take k [wcs0; wcs1; wcgp])
                     with "Hstk_opened Hstk []") as "Hlocal".
         { rewrite length_take Nat.min_l; last (simpl; lia).
           rewrite -Hlen_lv finz_seq_between_length /finz.dist. solve_addr. }
         { iApply big_sepL_forall. iIntros (j w Hj). iRight.
           apply lookup_take_Some in Hj as [Hj _].
           destruct j as [|[|[|j] ] ]; cbn in Hj; simplify_eq; done. }
         (* MSHWM is unchanged, or lowered to a spilled cell *)
         iDestruct (hwm_res_of_regs with "Hts Hhwm_regs") as "Hhwm".
         { destruct Hh' as [-> | Hh'']; solve_addr. }
         iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
           as "Hrmap".
         iApply (trap_safe_unwind_logrel_of_safety with "Hthread Hsafety [] [-]");
           [by apply call_regs_with_full|done| |
            |iModIntro; rewrite world_resources_split;
             iFrame "Hrmap Hlocal Hperm Hcont Hhwm Hna Hcstk";
             iExists InterruptDisabled; iFrame "Hmie Hheld"; iPureIntro; by intros].
         { (* A fault of a later store of the spill is not resumed *)
           exact Hoff. }
         (* The fault is in the switcher *)
         iLeft; iPureIntro. apply switcher_fault_pc_cap. }
    iDestruct (interp_cap_disjoint_wl with "Hspv") as %[Hstk_mmio Hstk_heap]; first done.

    (* Is the base of the stack pointer MSHWMB? *)
    destruct (decide (b = cstk_hwm_base cstk)) as [Hbase | Hbase]; cycle 1.
    { (* [.Lswitch_csp_check]: the check of the base fails, force the
         unwinding of the call *)
      iEval (rewrite -switcher_call_entry_label) in "HPC".
      iApply (switch_csp_check_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hmshwmb $Hcode]").
      iNext; iIntros "[(_ & %Hb & _) | (_ & %zct2 & %zctp & HPC & Hcsp & Hct2 & Hctp & Hmshwmb)]".
      { exfalso. apply Hbase. cbn in Hb. solve_addr. }
      iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
        as "Hrmap".
      iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm"; first done.
      iApply (interp_switcher_call_force_unwind with
        "Hthread Hsafety Hopened Hmtdc Hframeoffset Hhazard Htstk HPC Hrmap Hworld_res Hcont
         Hhwm Hcstk Hmie Hheld");
        [by apply call_regs_with_full|done]. }

    (* Open the free part of the caller's stack, before the checks: the
       opened resources are then available at a fault of the spill *)
    iDestruct (world_resources_split with "Hworld_res") as "[Hlocal Hperm]".
    iDestruct (local_call_stk_open _ _ b e a (stk_free_b b a) (stk_free_e e a)
                with "Hspv Hlocal")
      as (lv) "(Hstk & Hstk_opened)"; [rewrite /stk_free_b; solve_addr | exact Hae |].
    iDestruct (stack_region_length with "Hstk") as %Hlen_lv.
    (* Its cells below MSHWM are cells of the zone, which hold integers *)
    iPoseProof (hwm_closed_user th Huser) as "Hcl".
    iApply (wp_stack_region_below_hwm with "Hcl Hstk [$Hmshwmb $Hmshwm]");
      [done | rewrite /stk_free_b; solve_addr |].
    iIntros (Hints_free) "_ Hstk Hhwm_regs".

    (* [.Lswitch_csp_check] to [.Lswitcher_decode_entry] *)
    iEval (rewrite -switcher_call_entry_label) in "HPC".
    iApply (switcher_call_path_spec with
      "[- $HPC $Hcsp $Hct2 $Hctp $Hcs0 $Hcs1 $Hcra $Hcgp $Hct1 $Hstk $Hhwm_regs $Hcl $Hmtdc
          $Hframeoffset $Hhazard $Htstk $Hb_switcher $Hcode]"); [done..| solve_addr | by rewrite Hbase |].
    iNext.
    iPoseProof "Hstatic" as "(_ & _ & _ & Hswitcher_global & _)".
    iNamed "Hswitcher_global". iNamed "Hswitcher_sealing".
    iSplit; [ |iSplit; [ |iSplit; [ |iSplit] ] ]; cycle 1.
    { (* The entry point is not sealed by the switcher *)
      iIntros (g_tstk mshwm_v') "Hfault _".
      iApply (interp_switcher_call_unseal_fault with
               "Hthread Hsafety Hcs0v Hcs1v Hcrav Hcgpv Hspv Htop Hopened Hstk_opened Hperm Hrmap
                 Hcont Hcstk Hmie Hheld Hts Hfault");
        done. }
    { (* The trusted stack is exhausted *)
      iIntros (g_tstk mshwm_v').
      iApply (interp_switcher_call_tstack_exhausted with
               "Hthread Hsafety Hcs0v Hcs1v Hcrav Hcgpv Hspv Htop Hopened Hstk_opened Hperm Hrmap
                 Hcont Hcstk Hmie Hheld Hts");
        done. }
    { (* The caller's stack starts at MSHWMB, at or below MSHWM: the zeroing
         of the callee's stack does not fault *)
      iIntros (g_tstk mshwm_v' off) "(%Hstk_bounds & _ & _ & %Hh' & %Hlt & _)"; exfalso.
      pose proof Hstk_bounds as (Hb4 & _ & _). revert Hb4 Hlt. stk_unfold. intros. solve_addr. }
    { (* The callee-save registers do not fit on the caller's stack *)
      iIntros "Hfault _".
      iApply (interp_switcher_call_spill_fault with
               "Hthread Hsafety Hreg Htop Hopened Hstk_opened Hperm Hrmap Hcont Hcstk Hmie Hheld
                Hts Hfault"); done. }
    iNext; iIntros (g_tstk wsb π mshwm_v')
      "(-> & %Htag & %Hstk_bounds & %Ha_next & %Ha_next_e & %Hh' & %Hcallee_h' & HPC & Hcs0
      & [%wcs1' Hcs1] & [%wct2' Hct2] & Hctp & Hcsp & Hcra & Hcgp & Hct1 & Hcells & Hstk
      & Hhwm_regs & Hmtdc & Hframeoffset & Hhazard & Hframe_csp & [%wtbl Hframe_tbl] & Hframe_cnt
      & [%tstk_next' Htstk] & Hlc)".
    pose proof Hstk_bounds as (Hba & Hba3 & Ha4).

    (* The callee's stack holds integers *)
    assert (Forall lword_int (stack_zeroed_from (stk_callee_b b a) mshwm_v' (stk_mem_callee lv)))
      as Hints_callee.
    { apply (callee_stk_ints b e a mshwm_v mshwm_v'); [done|done|done|].
      destruct Hh' as [-> | Hh'']; [by left | right; lia]. }
    iDestruct (stack_ints_of_region _ _ _ Hints_callee with "Hstk") as "Hstk".

    (* The entry point satisfies the sealing predicate of the switcher *)
    iDestruct (ot_switcher_entry_prop with "Hp_ot_switcher []") as "Hentry_prop".
    { case_match; [iExact "Hct1v"|done]. }
    iDestruct "Hlc" as "[Hlc _]".
    iMod (lc_fupd_elim_later with "Hlc Hentry_prop") as "Hentry_prop_now".
    iDestruct ("Hentry_prop_now" with "[//] [//]") as "Hentry_ot".
    iNamed "Hentry_ot".
    (* [simplify_eq] would substitute [b] with [Hbase] *)
    revert Hbase. rewrite /lword_of_word in Hw; simplify_eq. intros Hbase.
    iSpecialize ("Hentry_cont" $! th with "Hthread").
    iSpecialize ("Hentry_cont" $! W).

    (* The argument registers *)
    set (rmap' := call_regs_without regs).
    set (Pf := ((λ '(r,_), r ∈ dom_arg_rmap 8) : RegName * LWord → Prop)).
    rewrite -(map_filter_union_complement Pf rmap').
    iDestruct (big_sepM_union with "Hrmap") as "[Hparams Hrest]".
    { apply map_disjoint_filter_complement. }
    iAssert ([∗ map] r↦w ∈ filter Pf rmap',
               r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True)%I
      with "[Hparams]" as "Hparams".
    { iApply big_sepM_sep. iFrame "Hparams". iApply big_sepM_forall.
      { intros k v.
        destruct (decide ( (k ∈ dom_arg_rmap nargs) )); tc_solve. }
      iIntros (k v [Hin Hspec]%map_lookup_filter_Some).
      destruct ( decide (k ∈ dom_arg_rmap nargs) ); last done.
      iApply ("Hreg" $! k); iPureIntro.
      rewrite /rmap' /call_regs_without in Hin.
      repeat (apply lookup_delete_Some in Hin as [_ Hin]); auto. }
    assert (is_arg_rmap (filter Pf rmap') 8) as Hparams_dom.
    { rewrite /is_arg_rmap.
      apply dom_filter_L. clear -Hfull_rmap.
      rewrite /rmap' /call_regs_without. split.
      - intros Hi.
        repeat (rewrite lookup_delete_ne;[|set_solver]).
        specialize (Hfull_rmap i) as [x Hx].
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    assert (dom (filter (λ v, ¬ Pf v) rmap') =
              all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8))
      as Hrest_dom.
    { clear -Hfull_rmap. apply lregmap_full_dom in Hfull_rmap as Hw'.
      rewrite /rmap' /call_regs_without !map_filter_delete !dom_delete_L.
      cut (dom (filter (λ v, ¬ Pf v) regs) = all_registers_s ∖ dom_arg_rmap 8).
      { intros Heq. clear -Heq. rewrite Heq. generalize (dom_arg_rmap 8); intros S. set_solver. }
      apply (dom_filter_L _ (regs : gmap RegName LWord)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_rmap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }
    set (frame := interp_call_frame b e a (Cap RO g_tbl b_tbl e_tbl a_tbl)).
    (* The table cell holds the unsealed entry *)
    assert (tf_export_tbl_ok (cf_tframe frame)) as Htbl_ok.
    { apply (tf_export_tbl_cell_entry (cf_tframe frame) g_tbl b_tbl e_tbl a_tbl eq_refl
               Hbtbl_header); [clear -Hatbl; solve_addr | exact Htbl_shadow]. }

    (* MSHWM is at or below the spill area, which is full points-to *)
    iDestruct "Hcells" as "(Hc0 & Hc1 & Hc2 & Hc3)".
    iDestruct "Hhwm_regs" as "[Hmshwmb Hmshwm]".
    iApply (wp_hwm_pointsto_outside with "Hcl Hc0 Hmshwmb Hmshwm"); first done.
    iIntros (Hout) "_ Hc0 Hmshwmb Hmshwm".
    iAssert (switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra)
      with "[$Hc0 $Hc1 $Hc2 $Hc3]" as "Hcells".
    assert (mshwm_v' <= stk_spill_a a)%Z as Hh'_spill.
    { clear -Hout Hba Hbase. solve_addr. }
    (* The cells between MSHWM and the callee's stack pointer join the zone,
       for the raise of MSHWM *)
    set (lo := (cstk_hwm_base cstk ^+ (mshwm_v' - cstk_hwm_base cstk))%a).
    assert (lo = mshwm_v' :> Z) as Hlo.
    { subst lo. clear -Hcallee_h' Hh'_spill Hba. stk_unfold. solve_addr. }

    destruct (decide (StackEntry_reserved_space <= stk_callee_e e a)%Z)
      as [Hnowrap | Hwrap]; cycle 1.
    { (* The callee's stack ends below the space reserved at its top: it is
         too small, and the decoding takes no cell of the zone *)
      iApply (switcher_decode_entry_path_spec W C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo
        with "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra
            $Hcsp $Hmshwmb $Hmshwm $Hparams $Hrest $Hcode $Hmie $Hheld]");
        [done|clear -Hbtbl_header; solve_addr|done|clear -Hnargs; lia|clear -Hminstk; lia|done|done|done|done| | | |done|done|done
        |intros Hcs; by destruct Huser| |].
      { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
        reflexivity. }
      { clear -Ha_next; tstack_unfold; solve_addr. }
      { clear -Ha_next Ha_next_e; tstack_unfold; solve_addr. }
      { rewrite -Hlo Z.max_r; first reflexivity.
        clear -Hlo Hbase Hcallee_h'. stk_unfold. solve_addr. }
      iSplitR.
      { iLeft. iPureIntro. clear -Hwrap. stk_unfold. solve_addr. }
      iNext; iSplit.
      { iIntros (arg_rmap_s rmap_s) "(%Hbig & _)". exfalso. clear -Hbig Hwrap. stk_unfold.
        rewrite /StackEntry_reserved_space in Hbig Hwrap. solve_addr. }
      iIntros "(_ & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcgp & Hcra & Hcsp
               & [Hmshwmb Hmshwm] & _ & Hframe_tbl & Hparams & Hrest & Hmie & Hheld)".
      iDestruct "Hstk" as (lc) "[%Hlc Hstk]".
      iDestruct (interp_call_stk_close _ _ b e a lv lc with
                  "Hcs0v Hcs1v Hcgpv Hcrav [] Hstk_opened Hcells Hstk") as "Hlocal";
        [done|done| |].
      { by iApply interp_call_ints_words. }
      iAssert (world_resources W C) with "[Hlocal Hperm]" as "Hworld_res".
      { rewrite world_resources_split. iFrame "Hlocal Hperm". }
      iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm".
      { destruct Hh' as [-> | Hh'']; solve_addr. }
      iEval (rewrite -(hwm_res_push frame cstk mshwm_v')) in "Hhwm".
      iApply (interp_switcher_call_stack_too_small with
               "Hthread Hsafety Hspv Htop Hopened Hworld_res Hcont Hcstk Hhwm Hmtdc Hframeoffset
                Hhazard Hframe_csp Hframe_cnt Htstk
                [$HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcgp $Hcra $Hcsp $Hframe_tbl $Hparams $Hrest
                 $Hmie $Hheld]");
        done. }

    iMod (stack_region_zeroes_zone_acc _ _ lo
            (stk_callee_e e a ^+ (- StackEntry_reserved_space))%a with "Hstk")
      as "[Hzone Hzone_close]".
    { clear -Hlo Hcallee_h'. stk_unfold. solve_addr. }
    { intros _. clear -Hnowrap. stk_unfold. solve_addr. }

    (* [.Lswitcher_decode_entry]: load the callee and jump to it *)
    iApply (switcher_decode_entry_path_spec W C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra $Hcsp
          $Hmshwmb $Hmshwm $Hparams $Hrest $Hcode $Hmie $Hheld]");
      [done|clear -Hbtbl_header; solve_addr|done|clear -Hnargs; lia|clear -Hminstk; lia|done|done|done|done| | | |done|done|done
      |intros Hcs; by destruct Huser| |].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { clear -Ha_next; tstack_unfold; solve_addr. }
    { clear -Ha_next Ha_next_e; tstack_unfold; solve_addr. }
    { rewrite Hlo. clear -Hbase Hcallee_h'. stk_unfold. solve_addr. }
    iSplitL "Hzone".
    { iRight. iExact "Hzone". }
    iNext; iSplit; cycle 1.
    { (* The callee's stack is too small *)
      iIntros "(_ & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcgp & Hcra & Hcsp
               & [Hmshwmb Hmshwm] & Hzone & Hframe_tbl & Hparams & Hrest & Hmie & Hheld)".
      iDestruct "Hzone" as "[%Hsmall_e | Hzone]".
      { exfalso. clear -Hsmall_e Hnowrap. lia. }
      iDestruct ("Hzone_close" with "Hzone") as "Hstk".
      iDestruct "Hstk" as (lc) "[%Hlc Hstk]".
      iDestruct (interp_call_stk_close _ _ b e a lv lc with
                  "Hcs0v Hcs1v Hcgpv Hcrav [] Hstk_opened Hcells Hstk") as "Hlocal";
        [done|done| |].
      { by iApply interp_call_ints_words. }
      iAssert (world_resources W C) with "[Hlocal Hperm]" as "Hworld_res".
      { rewrite world_resources_split. iFrame "Hlocal Hperm". }
      iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm".
      { destruct Hh' as [-> | Hh'']; solve_addr. }
      iEval (rewrite -(hwm_res_push frame cstk mshwm_v')) in "Hhwm".
      iApply (interp_switcher_call_stack_too_small with
               "Hthread Hsafety Hspv Htop Hopened Hworld_res Hcont Hcstk Hhwm Hmtdc Hframeoffset
                Hhazard Hframe_csp Hframe_cnt Htstk
                [$HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcgp $Hcra $Hcsp $Hframe_tbl $Hparams $Hrest
                 $Hmie $Hheld]");
        done. }
    iIntros (arg_rmap' rmap'')
      "(%Hbig & %Harg_rmap' & %Hrmap'' & HPC & Hcgp & Hcra & Hcsp & [Hmshwmb Hmshwm] & Hzone
      & Hframe_tbl & Hargs & Hregs & Hmie & Hheld & _)".
    iDestruct ("Hzone_close" with "Hzone") as "Hstk".

    (* Close the caller's stack frame, and rejoin the world premise *)
    iDestruct "Hstk" as (lc) "[%Hlc Hstk]".
    iDestruct (interp_call_stk_close _ _ b e a lv lc with
                "Hcs0v Hcs1v Hcgpv Hcrav [] Hstk_opened Hcells Hstk") as "Hlocal";
      [done|done| |].
    { by iApply interp_call_ints_words. }
    iAssert (world_resources W C) with "[Hlocal Hperm]" as "Hworld_res".
    { rewrite world_resources_split. iFrame "Hlocal Hperm". }

    (* Push the frame and close the trusted-stack invariant *)
    iMod (trusted_stack_inv_opened_push frame cstk with
           "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk []")
      as "[Hna Hcstk]"; [done|done|done|done|done|done|done|right; split; [done | exact Htbl_ok]| |].
    { by rewrite /cframe_stk_own /=. }
    iDestruct (interp_call_cont_frame _ _ _ _ _ _ _ _ (Cap RO g_tbl b_tbl e_tbl a_tbl)
                with "Hspv Htop Hcont") as "Hcont"; [done|done|done|].

    (* MSHWM is the callee's stack pointer; the stack addresses between
       MSHWMB and it are Temporary *)
    iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm".
    { clear -Hbase Hbig. stk_unfold. solve_addr. }
    iEval (rewrite -(hwm_res_push frame cstk)) in "Hhwm".
    iDestruct (interp_stack_zone_temporary _ _ _ _ _
                 (stk_callee_e e a ^+ (- StackEntry_reserved_space))%a with "Hspv")
      as %Hzone_callee.
    { clear -Hnowrap Hba3 Ha4 Hae. stk_unfold. solve_addr. }

    (* Execute the entry point of the callee *)
    iAssert (interp W C (callee_csp b e a)) as "#Hstk4v".
    { stk_unfold. iApply (interp_weakeningEO_gen with "[] Hspv");
        last (iIntros "!>" (Hg _); discriminate Hg).
      all: auto; revert Hba Hba3 Ha4; stk_unfold; solve_addr. }
    iDestruct (switcher_call_entry_registers W W C nargs arg_rmap' rmap'' with
                "[$Hcgp $Hcra $Hcsp $Hstk4v $Hargs $Hregs]")
      as (regs') "[Hregs Hregs_interp]"; [apply related_sts_pub_refl_world|done|done|].
    iApply ("Hentry_cont" $! (cstack_push frame cstk) (W :: Ws) (C :: Cs) regs'
             (stk_callee_b b a) (stk_callee_e e a)).
    iSplitR; first iExact "Hthread".
    iSplitR; first iExact "Htv".
    iSplitL "Hcont"; first iExact "Hcont".
    iSplit.
    { iPureIntro. simpl. split;auto. apply related_sts_pub_refl_world. }
    iSplit; first (iPureIntro; split_and!; [done | reflexivity | reflexivity | exact Htbl_ok]).
    iFrame "HPC Hregs Hregs_interp Hhwm Hworld_res Hcred Hcstk Hna Hmie Hheld".
    (* The remaining pure conjuncts of [execute_entry_point]: zone, [csp_sync],
       base, size, posture *)
    iSplit.
    { iPureIntro. rewrite cstk_hwm_base_push -Hbase. exact Hzone_callee. }
    iSplit.
    { iPureIntro.
      cbn. pose proof Hstk_bounds as (_ & _ & Ha4').
      rewrite (tf_caller_a_saved _ true RWL Local b e a); [by split | done | done]. }
    iSplit; first (iPureIntro; exact Hbase).
    iSplit; [iPureIntro; exact Hbig | iPureIntro; intros Hcs; by destruct Huser].
  Qed.

End fundamental.
