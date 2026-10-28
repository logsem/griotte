From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants bitblast.
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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

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
    ( [∗ map] r↦w ∈ call_regs_without regs, r ↦ᵣ[th] w ) -∗
    ct1 ↦ᵣ[th] wct1 -∗
    ct2 ↦ᵣ[th] wct2 -∗
    ctp ↦ᵣ[th] wctp -∗
    ∃ (wca0 wca1 : LWord) (rmap0 : LReg),
      ca0 ↦ᵣ[th] wca0 ∗
      ca1 ↦ᵣ[th] wca1 ∗
      ⌜ dom rmap0 = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
      ( [∗ map] r↦w ∈ rmap0, r ↦ᵣ[th] w ).
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
    ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ[th] w ) -∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w ) -∗
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
      [WCap true RWL Local b e a], with the word [wtbl] in its table cell.
      The saved registers are not read: the caller's spill area belongs to
      its world. *)
  Definition interp_call_frame (b e a : Addr) (wtbl : LWord) : cframe :=
    {| cf_tframe :=
         {| tf_csp := WCap true RWL Local b e (stk_saved_a a);
            tf_export_tbl := wtbl;
            tf_error_count := 0 |};
       cf_saved :=
         {| cs_cra := WInt 0;
            cs_cgp := WInt 0;
            cs_cs0 := WInt 0;
            cs_cs1 := WInt 0 |};
       ccrel := Unknown_to_Unknown
    |}.

  (** The continuation of the caller, once its frame is pushed. *)
  #[local] Lemma interp_call_cont_frame W C (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (b e a : Addr) (wtbl : LWord) :
    disjoint_from_heap b e ->
    switcher_stk_bounds b e a ->
    switcher_trap_safety -∗
    interp W C (WCap true RWL Local b e a) -∗
    top_cmpt_untrusted interp W C cstk -∗
    interp_cont interp cstk Ws Cs -∗
    interp_cont interp (cstack_push (interp_call_frame b e a wtbl) cstk) (W :: Ws) (C :: Cs).
  Proof.
    iIntros (Hstk_heap Hstk_bounds) "#Hsafety #Hspv #Htop Hcont".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    iPoseProof (fundamental_ih with "Htrap") as "IH".
    simpl.
    iFrame "Hcont".
    destruct Hstk_bounds as (Hba & Hba3 & Ha4).
    rewrite (tf_caller_a_saved _ true RWL Local b e a); [| done | done].
    rewrite ?cstack_eta.
    iSplit; last iExact "Htop".
    iSplit; first (iPureIntro; exact Hstk_heap).
    iApply (interp_weakening with "IH Hspv"); auto; revert Hba Hba3 Ha4; stk_unfold; solve_addr.
  Qed.

  (** ** Failure and fault paths *)

  (** Failure path of [interp_expr_switcher_call]: the checks on the stack
      pointer fail, and the call is unwound by the return routine.
      [.Lcommon_force_unwind] sets the return values, so no register needs
      to be safe. *)
  Lemma interp_switcher_call_force_unwind
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (a_tstk : Addr) (tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    (∀ r, is_Some (regs !! r)) ->
    frame_match Ws Cs cstk W C ->

    switcher_trap_safety -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    mtdc ↦ₜ[th] TStack (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) -∗
    switcher_hazard -∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" -∗
    registers_pointsto regs -∗
    world_interp W C -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    (* Outline of the proof: [common_force_unwind_spec] sets the return
       values, then close the trusted-stack invariant and run the return routine
       ([switcher_return_unwind]) with the integer return values. *)
    iIntros (Hfull_rmap Hframe)
      "#Hsafety Hopened Hmtdc Hframeoffset Hhazard Htstk HPC Hrmap Hworld_interp Hcont Hcstk".
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
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'.
      destruct (decide (r = ca0)); first naive_solver.
      destruct (decide (r = ca1)); first naive_solver.
      do 2 right. rewrite !lookup_delete_ne //. }
    iSplit; iApply interp_int.
  Qed.

  (** Failure path of [interp_expr_switcher_call]: the trusted stack is
      exhausted. *)
  Lemma interp_switcher_call_tstack_exhausted
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (b e a : Addr) (lv : list LWord)
    (wcs0 wcs1 wcra wcgp wct1 : LWord) (g_tstk : Locality)
    (a_tstk : Addr) (tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    (∀ r, is_Some (regs !! r)) ->
    frame_match Ws Cs cstk W C ->
    disjoint_from_mmio b e ->
    length (stk_free b e a) = length lv ->

    switcher_trap_safety -∗
    interp W C wcs0 -∗
    interp W C wcs1 -∗
    interp W C wcra -∗
    interp W C wcgp -∗
    interp W C (WCap true RWL Local b e a) -∗
    top_cmpt_untrusted interp W C cstk -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    switcher_stk_opened W C (stk_free_b b a) (stk_free_e e a) lv -∗
    ( [∗ map] r↦w ∈ call_regs_without regs, r ↦ᵣ[th] w ) -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    ( ⌜ switcher_stk_bounds b e a ⌝ ∗
      PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
      cs0 ↦ᵣ[th] WInt (e_trusted_stack - b_trusted_stack) ∗
      cs1 ↦ᵣ[th] wcs1 ∗
      ctp ↦ᵣ[th] WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      ct2 ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
      csp ↦ᵣ[th] WCap true RWL Local b e (stk_saved_a a) ∗
      cra ↦ᵣ[th] wcra ∗
      cgp ↦ᵣ[th] wcgp ∗
      ct1 ↦ᵣ[th] wct1 ∗
      switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
      [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem_callee lv ]] ∗
      mtdc ↦ₜ[th] TStack (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      switcher_hazard ∗
      [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
      WP Seq (Instr Executable) @[th] {{ HO th }} ).
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    (* Outline of the proof: [switch_trusted_stack_exhausted_path_spec]
       restores the registers, clears the others and returns,
       [switcher_call_stk_close] closes the caller's stack frame,
       then close the trusted-stack invariant and
       [switcher_jump_to_caller_cases_spec]. *)
    iIntros (Hfull Hframe Hstk_mmio Hlen_lv)
      "#Hsafety #Hcs0v #Hcs1v #Hcrav #Hcgpv #Hspv #Htop Hopened Hstk_opened Hrmap Hcont Hcstk
      (%Hstk_bounds & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hcra & Hcgp & Hct1 & Hcells & Hstk
      & Hmtdc & Hframeoffset & Hhazard & Htstk)".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[_ #Hstatic]".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    pose proof Hstk_bounds as (Hba & Hba3 & Ha4).
    assert (4 <= length lv)%nat as Hlen_lv4.
    { rewrite -Hlen_lv /stk_free finz_seq_between_length /finz.dist.
      revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4. solve_addr. }
    iDestruct (interp_call_regs_exhausted with "Hrmap Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; first done.
    iApply (switch_trusted_stack_exhausted_path_spec with
      "[- $HPC $Hcsp $Hcells $Hrmap0 $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1]");
      [done|done|done|].
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "((%Hrcgp & %Hrcra & %Hrcs0 & %Hrcs1) & %Hrmap' & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1
      & Hcsp & Hcells & Hrmap & _)".
    iDestruct (interp_load_heap with "Hcs0v") as "#Hrcs0v"; first done.
    iDestruct (interp_load_heap with "Hcs1v") as "#Hrcs1v"; first done.
    iDestruct (interp_load_heap with "Hcrav") as "#Hrcrav"; first done.
    iDestruct (interp_load_heap with "Hcgpv") as "#Hrcgpv"; first done.

    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; first done.
    iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
      as "Hworld_interp".
    { rewrite /stk_mem_join /stk_mem_callee /SpillSlot_size length_app length_take /=. lia. }
    { rewrite /stk_mem_join /stk_mem_callee big_sepL_app.
      iSplitL.
      - iApply big_sepL_forall. iIntros (k w Hk). iLeft. iPureIntro.
        by apply lookup_take_Some in Hk as [Hk _].
      - iSplitL; first (iRight; iExact "Hcs0v").
        iSplitL; first (iRight; iExact "Hcs1v").
        iSplitL; first (iRight; iExact "Hcgpv").
        iSplitL; first (iRight; iExact "Hcrav").
        done. }

    (* Jump back to the caller, or unwind the call when the jump faults;
       close the trusted-stack invariant first *)
    iApply (switcher_jump_to_caller_cases_spec with
             "Htrap Hrcrav Hrcgpv Hrcs0v Hrcs1v Hspv [] [] Htop Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
              Hrmap Hcont [-]"); [done|done|iApply interp_int|iApply interp_int|].
    iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
    iModIntro.
    iFrame "Hworld_interp Hna Hcstk".
  Qed.

  (** Fault of the first spill: the checks leave integers in [ct2] and
      [ctp], and the other registers hold the caller's safe words. Close
      the caller's stack and the trusted-stack invariant, and give the fault to
      the untrusted caller. *)
  Lemma interp_switcher_call_spill_fault
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (b e a : Addr) (lv : list LWord)
    (wcs0 wcs1 wcra wcgp wct1 : LWord)
    (a_tstk : Addr) (tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    (∀ r, is_Some (regs !! r)) ->
    regs !! csp = Some (WCap true RWL Local b e a : LWord) -> regs !! cs0 = Some wcs0 ->
    regs !! cs1 = Some wcs1 -> regs !! cra = Some wcra -> regs !! cgp = Some wcgp ->
    regs !! ct1 = Some wct1 ->
    frame_match Ws Cs cstk W C ->

    switcher_trap_safety -∗
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    top_cmpt_untrusted interp W C cstk -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    switcher_stk_opened W C (stk_free_b b a) (stk_free_e e a) lv -∗
    ( [∗ map] r↦w ∈ call_regs_without regs, r ↦ᵣ[th] w ) -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    ( ⌜ ¬ stk_spill_fits b e a ⌝ ∗
      csp ↦ᵣ[th] WCap true RWL Local b e a ∗
      ct2 ↦ᵣ[th] WInt COMPARTMENT_STACK_LOCALITY ∗
      ctp ↦ᵣ[th] WInt COMPARTMENT_STACK_LOCALITY ∗
      cs0 ↦ᵣ[th] wcs0 ∗
      cs1 ↦ᵣ[th] wcs1 ∗
      cra ↦ᵣ[th] wcra ∗
      cgp ↦ᵣ[th] wcgp ∗
      ct1 ↦ᵣ[th] wct1 ∗
      [[ stk_free_b b a , stk_free_e e a ]] ↦ₐ [[ lv ]] ∗
      mtdc ↦ₜ[th] TStack (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      switcher_hazard ∗
      [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
      trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
        (HO th) ).
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    iIntros (Hfull Hcsp Hcs0 Hcs1 Hcra Hcgp Hct1 Hframe)
      "#Hsafety #Hreg #Htop Hopened Hstk_opened Hrmap Hcont Hcstk
      (_ & Hcsp & Hct2 & Hctp & Hcs0 & Hcs1 & Hcra & Hcgp & Hct1 & Hstk
      & Hmtdc & Hframeoffset & Hhazard & Htstk)".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
      as "Hworld_interp"; first done.
    { iApply big_sepL_intro; iIntros "!>" (k w Hk); by iLeft. }
    iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1") as "Hrmap".
    iEval (rewrite (call_regs_with_id regs) //) in "Hrmap".
    iApply (interp_trap_safe_untrusted _ W C cstk Ws Cs
              (<[ctp := (WInt COMPARTMENT_STACK_LOCALITY : LWord)]>
                (<[ct2 := (WInt COMPARTMENT_STACK_LOCALITY : LWord)]> regs))
             with "Htrap [] Htop [-]"); [ |done| |].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    { by iApply interp_call_regs_scratch. }
    iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
    iModIntro.
    iFrame "Hrmap Hworld_interp Hcont Hna Hcstk".
  Qed.

  (** Fault of the unsealing: close the caller's stack, push the frame,
      with the table word [WInt 0] and any word in its table cell, close the
      trusted-stack invariant, and unwind the call. *)
  Lemma interp_switcher_call_unseal_fault
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (b e a : Addr) (lv : list LWord)
    (wcs0 wcs1 wcra wcgp wct1 : LWord) (g_tstk : Locality) (a_tstk : Addr) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_free := (a_next ^+ TrustedStackFrame_size)%a in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    (∀ r, is_Some (regs !! r)) ->
    frame_match Ws Cs cstk W C ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->
    length (stk_free b e a) = length lv ->

    switcher_trap_safety -∗
    interp W C wcs0 -∗
    interp W C wcs1 -∗
    interp W C wcra -∗
    interp W C wcgp -∗
    interp W C (WCap true RWL Local b e a) -∗
    top_cmpt_untrusted interp W C cstk -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    switcher_stk_opened W C (stk_free_b b a) (stk_free_e e a) lv -∗
    ( [∗ map] r↦w ∈ call_regs_without regs, r ↦ᵣ[th] w ) -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    ( ⌜ ¬ ∃ wsb π, wct1 = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ ∗
      ⌜ switcher_stk_bounds b e a ⌝ ∗
      ⌜ (b_trusted_stack + tstack_frame_offset (S (length cstk'.(cstk_frames))))%a = Some a_next ⌝ ∗
      ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
      cs0 ↦ᵣ[th] WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
      (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
      (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
      ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_next ∗
      csp ↦ᵣ[th] chopped_csp b e a ∗
      cra ↦ᵣ[th] wcra ∗
      cgp ↦ᵣ[th] wcgp ∗
      ct1 ↦ᵣ[th] - ∗
      switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
      [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
        [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
      mtdc ↦ₜ[th] TStack (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (S (length cstk'.(cstk_frames)))) ∗
      switcher_hazard ∗
      a_csp ↦ₐ WCap true RWL Local b e (stk_saved_a a) ∗
      a_export_table ↦ₐ - ∗
      a_error_count ↦ₐ WInt 0 ∗
      (∃ tstk_next', [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]]) ∗
      £ 2 -∗
      trap_safe (switcher_label_pc ".Lswitcher_decode_entry") ⊤
        (HO th) ).
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hfull Hframe Hstk_mmio Hstk_heap Hlen_lv)
      "#Hsafety #Hcs0v #Hcs1v #Hcrav #Hcgpv #Hspv #Htop Hopened Hstk_opened Hrmap Hcont Hcstk
       (_ & %Hstk_bounds & %Ha_next & %Ha_next_e & Hcs0 & [%wcs1' Hcs1] & [%wct2' Hct2] & Hctp
       & Hcsp & Hcra & Hcgp & [%wct1' Hct1] & Hcells & Hstk & Hmtdc & Hframeoffset & Hhazard & Hframe_csp
       & [%wtbl Hframe_tbl] & Hframe_cnt & [%tstk_next' Htstk] & _)".
    set (frame := interp_call_frame b e a (lword_of_word (WInt 0))).
    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; first done.
    iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
      as "Hworld_interp".
    { rewrite /stk_mem_join length_app /region_addrs_zeroes length_replicate -Hlen_lv
        !finz_seq_between_length /finz.dist /=.
      destruct Hstk_bounds as (Hba & Hba3 & Ha4).
      revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4. solve_addr. }
    { rewrite /stk_mem_join big_sepL_app.
      iSplitL.
      - iApply big_sepL_forall. iIntros (k w Hk). iRight.
        apply lookup_replicate in Hk as [-> _]. iApply interp_int.
      - iSplitL; first (iRight; iExact "Hcs0v").
        iSplitL; first (iRight; iExact "Hcs1v").
        iSplitL; first (iRight; iExact "Hcgpv").
        iSplitL; first (iRight; iExact "Hcrav").
        done. }
    iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1") as "Hrmap".
    iApply (trap_safe_unwind_logrel_of_safety _ _ (cstack_push frame cstk) (W :: Ws) (C :: Cs)
             with "Hsafety [] [-]").
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
    iFrame "Hrmap Hworld_interp Hcstk Hna".
    iApply (interp_call_cont_frame with "Hsafety Hspv Htop Hcont"); done.
  Qed.

  (** The callee's stack is too small: push the frame, whose table cell
      holds the unsealed entry, close the trusted-stack invariant, and return to
      the caller through the return routine. *)
  Lemma interp_switcher_call_stack_too_small
    (W : WORLD) (C : CmptName)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (b e a : Addr) (a_tstk : Addr) (tstk_next : list LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr) (nargs minstk : nat)
    (arg_rmap rmap : LReg) :
    let frame := interp_call_frame b e a (WCap true RO g_tbl b_tbl e_tbl a_tbl) in
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_free := (a_next ^+ TrustedStackFrame_size)%a in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    frame_match Ws Cs cstk W C ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->
    switcher_stk_bounds b e a ->
    (b_trusted_stack + tstack_frame_offset (S (length cstk'.(cstk_frames))))%a = Some a_next ->
    (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    tf_export_tbl_ok (cf_tframe frame) ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    switcher_trap_safety -∗
    interp W C (WCap true RWL Local b e a) -∗
    top_cmpt_untrusted interp W C cstk -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    world_interp W C -∗
    interp_cont interp cstk Ws Cs -∗
    ◯(CSTK)[th] cstk -∗
    mtdc ↦ₜ[th] TStack (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S (length cstk'.(cstk_frames)))) -∗
    switcher_hazard -∗
    a_csp ↦ₐ WCap true RWL Local b e (stk_saved_a a) -∗
    a_error_count ↦ₐ WInt 0 -∗
    [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    ( ⌜ (stk_callee_e e a - stk_callee_b b a < Z.of_nat minstk + StackEntry_reserved_space)%Z ⌝ ∗
      PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_too_small" ∗
      cs0 ↦ᵣ[th] - ∗
      cs1 ↦ᵣ[th] - ∗
      ct1 ↦ᵣ[th] - ∗
      ct2 ↦ᵣ[th] - ∗
      ctp ↦ᵣ[th] - ∗
      cgp ↦ᵣ[th] - ∗
      cra ↦ᵣ[th] - ∗
      csp ↦ᵣ[th] WCap true RWL Local (stk_callee_b b a) (stk_callee_e e a) (stk_saved_a a) ∗
      a_export_table ↦ₐ WCap true RO g_tbl b_tbl e_tbl a_tbl ∗
      ( [∗ map] r↦w ∈ arg_rmap,
          r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
      ( [∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w ) -∗
      WP Seq (Instr Executable) @[th] {{ HO th }} ).
  Proof.
    intros frame a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hframe Hstk_mmio Hstk_heap Hstk_bounds Ha_next Ha_next_e Htbl_cell Hargs Hdom)
      "#Hsafety #Hspv #Htop Hopened Hworld_interp Hcont Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp
       Hframe_cnt Htstk
       (_ & HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wct1' Hct1] & [%wct2' Hct2] & [%wctp' Hctp]
       & [%wcgp' Hcgp] & [%wcra' Hcra] & Hcsp & Hframe_tbl & Hparams & Hrest)".
    iMod (trusted_stack_inv_opened_push frame cstk with
           "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk []")
      as "[Hna Hcstk]"; [done|done|done|done|done|done|done|right; split; [done | exact Htbl_cell]| |].
    { by rewrite /cframe_stk_own /=. }
    iDestruct (big_sepM_sep with "Hparams") as "[Hparams _]".
    iDestruct (interp_call_regs_full with "Hparams Hrest Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
      as (regs) "[%Hfull Hregs]"; [done|done|].
    iDestruct (interp_call_cont_frame _ _ _ _ _ _ _ _ (WCap true RO g_tbl b_tbl e_tbl a_tbl)
                with "Hsafety Hspv Htop Hcont") as "Hcont"; [done|done|].
    iApply (switcher_call_stack_too_small_unwind_of_safety _ _ (cstack_push frame cstk)
             (W :: Ws) (C :: Cs)
             with "[$HPC $Hregs $Hsafety $Hworld_interp $Hna $Hcstk $Hcont]"); first done.
    simpl. split; [apply related_sts_pub_refl_world|done].
  Qed.

  (** ** The call routine *)

  Lemma interp_expr_switcher_call_gen (W : WORLD) (C : CmptName) :
    switcher_trap_safety
    ⊢ interp_expr interp (interp_cont interp) W C (WCap true XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    (* Outline of the proof:
       - open the trusted-stack invariant;
       - when the stack pointer is not a valid stack capability, its checks
         fail ([interp_switcher_call_force_unwind]) or the first spill
         faults ([switch_entry_first_spill_fail_spec], or
         [switch_entry_first_spill_above_spec] when its cursor is above the
         top and the furthest cell of the spill within bounds);
       - [switcher_call_stk_open]: open the free part of the caller's stack
         in the world;
       - [switcher_call_path_spec]: check the stack pointer, spill the
         callee-save registers, push the frame, clear the callee's stack and
         unseal the entry point; its fault and failure exits close through
         [interp_switcher_call_unseal_fault],
         [interp_switcher_call_tstack_exhausted] and
         [interp_switcher_call_spill_fault];
       - [switcher_call_stk_close]: close the caller's stack frame;
       - [switcher_entry_point_prop]: the entry point satisfies the sealing
         predicate of the switcher;
       - [switcher_decode_entry_path_spec]: check the size of the callee's
         stack, load the callee and jump to it; when the stack is too small,
         [interp_switcher_call_stack_too_small];
       - [trusted_stack_inv_opened_push]: push the frame and close the trusted-stack
         invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros "#Hsafety %cstk %Ws %Cs %regs0 (Hregs & #Htop & HPC & Hrmap & Hworld_interp & Hcont & Hna & Hcstk & %Hframe)".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (regs) "%Hfull_rmap #Hreg Hrmap Hworld_interp". clear regs0.
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[#Hinv_switcher #Hstatic]".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    iPoseProof (fundamental_ih with "Htrap") as "IH". (* used for weakening lemma later *)
    iPoseProof "Hstatic" as "(#Hcode & #Hb_switcher & _)".

    (* Open the trusted-stack invariant *)
    iMod (trusted_stack_inv_open_call with "Hinv_switcher Hna")
      as (a_tstk cstk' tstk_next)
         "(%Hlen_cstk & %Ha_tstk_e & Hopened & Hmtdc & Hframeoffset & Hhazard & Htstk)".

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
    iAssert (⌜(∃ b e a, wcsp = WCap true RWL Local b e a ∧ (b < e)%a ∧ (a <= e)%a)
            ∨ (∀ b e a, wcsp.(lw) = WCap true RWL Local b e a → (e <= b)%a ∨ (e < a)%a)⌝)%I
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
         iAssert (⌜(∃ b e a, wcsp = WCap true RWL Local b e a ∧
                              stk_spill_ok a ∧ (b <= stk_spill_a a < e)%a)
                 ∨ (∀ b e a a4, wcsp.(lw) = WCap true RWL Local b e a →
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
           destruct (decide (b <= a4 < e)%a) as [Ha4_in|Ha4_out]; cycle 1.
           { iPureIntro; right; intros ???? Heq Ha4'; inversion Heq; subst.
             change (SpillSlot_cs0 - SpillSlot_size)%Z with (-4)%Z in Ha4'.
             rewrite Ha4 in Ha4'; simplify_eq; solve_addr. }
           iDestruct (interp_wl_noid with "Hspv") as %->; [done|solve_addr|].
           iPureIntro; left; exists b, e, a; split; first done.
           stk_unfold. split; solve_addr. }
         2: {
           (* [.Lswitch_csp_check]: checks on the stack pointer *)
           iEval (rewrite -switcher_call_entry_label) in "HPC".
           iApply (switch_csp_check_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
           iNext; iIntros "[(%Hchecked & HPC & Hcsp & Hct2 & Hctp)
                           | (_ & % & % & HPC & Hcsp & Hct2 & Hctp)]";
             cycle 1.
           { (* The checks fail: force the unwinding of the call *)
             iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
               as "Hrmap".
             iApply (interp_switcher_call_force_unwind with
               "Hsafety Hopened Hmtdc Hframeoffset Hhazard Htstk HPC Hrmap Hworld_interp Hcont Hcstk");
               [by apply call_regs_with_full|done]. }
           (* The first store faults, and nothing is written: close the
              trusted-stack invariant, and unwind the call *)
           iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
           iApply (switch_entry_first_spill_fail_spec with "[- $HPC $Hcsp $Hcs0 $Hcode]");
             [done | done |].
           iIntros "[Hcsp Hcs0]".
           iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
             as "Hrmap".
           iEval (rewrite (call_regs_with_id regs) //) in "Hrmap".
           iApply (interp_trap_safe_untrusted _ W C cstk Ws Cs
                     (<[ctp := (WInt COMPARTMENT_STACK_LOCALITY : LWord)]>
                (<[ct2 := (WInt COMPARTMENT_STACK_LOCALITY : LWord)]> regs))
                    with "Htrap [] Htop [-]");
             [ |done| |iModIntro; iFrame "Hrmap Hworld_interp Hcont Hna Hcstk"].
           { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
           (* A fault of the first spill: the registers are safe *)
           by iApply interp_call_regs_scratch. }
         (* The cursor is above the top, and the furthest cell within
            bounds: open the caller's stack from that cell to the top *)
         destruct (Hnot_stk b e a eq_refl) as [Heb|Hea]; first (revert Ha4_in; stk_unfold; solve_addr).
         iDestruct (interp_cap_disjoint_wl with "Hspv") as %[Hstk_mmio _]; first done.
         iDestruct (switcher_call_stk_open _ _ b e a (stk_spill_a a) e with "Hspv Hworld_interp")
           as (lv) "(Hstk & Hstk_opened)"; [solve_addr | solve_addr |].
         iDestruct (big_sepL2_length with "Hstk") as %Hlen_lv.

         (* [.Lswitch_csp_check]: checks on the stack pointer *)
         iEval (rewrite -switcher_call_entry_label) in "HPC".
         iApply (switch_csp_check_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
         iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp)
                         | (%Hcontra & _)]";
           last (exfalso; apply Hcontra, switcher_csp_checked_stk).
         (* The first stores write the cells of the spill area below the
            top, and the store at the top faults: close the trusted-stack
            invariant and the caller's stack, and unwind the call *)
         iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
         iApply (switch_entry_first_spill_above_spec with
                  "[- $HPC $Hcsp $Hcs0 $Hcs1 $Hcgp $Hcra $Hstk $Hcode]"); [done..|].
         iIntros (k off [Hk Hk_bounds] Hoff) "(Hcsp & Hcs0 & Hcs1 & Hcgp & Hcra & Hstk)".
         iDestruct (switcher_call_stk_close _ _ _ _ lv (take k [wcs0; wcs1; wcgp])
                     with "Hstk_opened Hstk []") as "Hworld_interp".
         { rewrite length_take Nat.min_l; last (simpl; lia).
           rewrite -Hlen_lv finz_seq_between_length /finz.dist. solve_addr. }
         { iApply big_sepL_forall. iIntros (j w Hj). iRight.
           apply lookup_take_Some in Hj as [Hj _].
           destruct j as [|[|[|j] ] ]; cbn in Hj; simplify_eq; done. }
         iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
           as "Hrmap".
         iApply (trap_safe_unwind_logrel_of_safety with "Hsafety [] [-]");
           [by apply call_regs_with_full|done| |
            |iModIntro; iFrame "Hrmap Hworld_interp Hcont Hna Hcstk"].
         { (* A fault of a later store of the spill is not resumed *)
           exact Hoff. }
         (* The fault is in the switcher *)
         iLeft; iPureIntro. apply switcher_fault_pc_cap. }
    iDestruct (interp_cap_disjoint_wl with "Hspv") as %[Hstk_mmio Hstk_heap]; first done.

    (* Open the free part of the caller's stack, before the checks: the
       opened resources are then available at a fault of the spill *)
    iDestruct (switcher_call_stk_open _ _ b e a (stk_free_b b a) (stk_free_e e a)
                with "Hspv Hworld_interp")
      as (lv) "(Hstk & Hstk_opened)"; [rewrite /stk_free_b; solve_addr | exact Hae |].
    iDestruct (big_sepL2_length with "Hstk") as %Hlen_lv.

    (* [.Lswitch_csp_check] to [.Lswitcher_decode_entry] *)
    iEval (rewrite -switcher_call_entry_label) in "HPC".
    iApply (switcher_call_path_spec with
      "[- $HPC $Hcsp $Hct2 $Hctp $Hcs0 $Hcs1 $Hcra $Hcgp $Hct1 $Hstk $Hmtdc $Hframeoffset $Hhazard $Htstk
          $Hb_switcher $Hcode]"); [done..|].
    iNext.
    iPoseProof "Hstatic" as "(_ & _ & _ & Hswitcher_global)".
    iNamed "Hswitcher_global".
    iSplit; [ |iSplit; [ |iSplit] ]; cycle 1.
    { (* The entry point is not sealed by the switcher *)
      iIntros (g_tstk).
      iApply (interp_switcher_call_unseal_fault with
               "Hsafety Hcs0v Hcs1v Hcrav Hcgpv Hspv Htop Hopened Hstk_opened Hrmap Hcont Hcstk");
        done. }
    { (* The trusted stack is exhausted *)
      iIntros (g_tstk).
      iApply (interp_switcher_call_tstack_exhausted with
               "Hsafety Hcs0v Hcs1v Hcrav Hcgpv Hspv Htop Hopened Hstk_opened Hrmap Hcont Hcstk");
        done. }
    { (* The callee-save registers do not fit on the caller's stack *)
      iApply (interp_switcher_call_spill_fault with
               "Hsafety Hreg Htop Hopened Hstk_opened Hrmap Hcont Hcstk"); done. }
    iNext; iIntros (g_tstk wsb π)
      "(-> & %Htag & %Hstk_bounds & %Ha_next & %Ha_next_e & HPC & Hcs0 & [%wcs1' Hcs1]
      & [%wct2' Hct2] & Hctp & Hcsp & Hcra & Hcgp & Hct1 & Hcells & Hstk & Hmtdc & Hframeoffset
      & Hhazard & Hframe_csp & [%wtbl Hframe_tbl] & Hframe_cnt & [%tstk_next' Htstk] & Hlc)".

    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; first done.
    iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
      as "Hworld_interp".
    { rewrite /stk_mem_join length_app /region_addrs_zeroes length_replicate -Hlen_lv
        !finz_seq_between_length /finz.dist /=.
      destruct Hstk_bounds as (Hba & Hba3 & Ha4).
      revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4. solve_addr. }
    { rewrite /stk_mem_join big_sepL_app.
      iSplitL.
      - iApply big_sepL_forall. iIntros (k w Hk). iRight.
        apply lookup_replicate in Hk as [-> _]. iApply interp_int.
      - iSplitL; first (iRight; iExact "Hcs0v").
        iSplitL; first (iRight; iExact "Hcs1v").
        iSplitL; first (iRight; iExact "Hcgpv").
        iSplitL; first (iRight; iExact "Hcrav").
        done. }

    (* The entry point satisfies the sealing predicate of the switcher *)
    iDestruct (switcher_entry_point_prop with "Hp_ot_switcher [] Hworld_interp")
      as "[Hworld_interp Hentry_prop]".
    { case_match; [iExact "Hct1v"|done]. }
    iDestruct "Hlc" as "[Hlc _]".
    iMod (lc_fupd_elim_later with "Hlc Hentry_prop") as "Hentry_prop".
    iDestruct ("Hentry_prop" with "[//] [//]") as "Hentry_ot".
    iNamed "Hentry_ot".
    rewrite /lword_of_word in Hw; simplify_eq.
    iSpecialize ("Hentry_cont" $! W with "[]").
    { iPureIntro. apply related_sts_priv_refl_world. }

    (* [.Lswitcher_decode_entry]: load the callee and jump to it *)
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
      { intros ->. clear. generalize (dom_arg_rmap 8); intros S. set_solver. }
      apply (dom_filter_L _ (regs : gmap RegName LWord)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_rmap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }
    iApply (switcher_decode_entry_path_spec W C with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra $Hcsp
          $Hparams $Hrest $Hcode]");
      [done|solve_addr|done|lia|lia|done|done|done|done| | | |done|done|done|].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { clear -Ha_next; tstack_unfold; solve_addr. }
    { clear -Ha_next Ha_next_e; tstack_unfold; solve_addr. }
    set (frame := interp_call_frame b e a (WCap true RO g_tbl b_tbl e_tbl a_tbl)).
    (* The table cell holds the unsealed entry *)
    assert (tf_export_tbl_ok (cf_tframe frame)) as Htbl_ok.
    { apply (tf_export_tbl_cell_entry (cf_tframe frame) g_tbl b_tbl e_tbl a_tbl eq_refl
               Hbtbl_header); [clear -Hatbl; solve_addr | exact Htbl_shadow]. }
    iNext; iSplit; cycle 1.
    { (* The callee's stack is too small *)
      iApply (interp_switcher_call_stack_too_small with
               "Hsafety Hspv Htop Hopened Hworld_interp Hcont Hcstk Hmtdc Hframeoffset
                Hhazard Hframe_csp Hframe_cnt Htstk"); done. }
    iIntros (mie arg_rmap' rmap'')
      "(%Hbig & %Harg_rmap' & %Hrmap'' & HPC & Hcgp & Hcra & Hcsp & Hframe_tbl & Hargs & Hregs)".

    (* Push the frame and close the trusted-stack invariant *)
    iMod (trusted_stack_inv_opened_push frame cstk with
           "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk []")
      as "[Hna Hcstk]"; [done|done|done|done|done|done|done|right; split; [done | exact Htbl_ok]| |].
    { by rewrite /cframe_stk_own /=. }
    iDestruct (interp_call_cont_frame _ _ _ _ _ _ _ _ (WCap true RO g_tbl b_tbl e_tbl a_tbl)
                with "Hsafety Hspv Htop Hcont") as "Hcont"; [done|done|].

    (* Execute the entry point of the callee *)
    iAssert (interp W C (callee_csp b e a)) as "#Hstk4v".
    { destruct Hstk_bounds as (Hba & Hba3 & Ha4).
      stk_unfold. iApply (interp_weakening with "IH Hspv"); auto;
        revert Hba Hba3 Ha4; stk_unfold; solve_addr. }
    iDestruct (switcher_call_entry_registers W W C nargs arg_rmap' rmap'' with
                "[$Hcgp $Hcra $Hcsp $Hstk4v $Hargs $Hregs]")
      as (regs') "[Hregs Hregs_interp]"; [apply related_sts_pub_refl_world|done|done|done|].
    iApply ("Hentry_cont" $! (cstack_push frame cstk) (W :: Ws) (C :: Cs) regs'
             (stk_callee_b b a) (stk_callee_e e a)).
    iSplitL "Hcont"; first iExact "Hcont".
    iSplit.
    { iPureIntro. simpl. split;auto. apply related_sts_pub_refl_world. }
    iSplit; first (iPureIntro; split_and!; [done | reflexivity | reflexivity | exact Htbl_ok]).
    iFrame "HPC Hregs Hregs_interp Hworld_interp Hcstk Hna".
    iPureIntro; split; last exact Hbig.
    cbn. pose proof Hstk_bounds as (_ & _ & Ha4).
    rewrite (tf_caller_a_saved _ true RWL Local b e a); [by split | done | done].
  Qed.

End fundamental.
