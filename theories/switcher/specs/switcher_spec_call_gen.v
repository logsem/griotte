From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import ftlr_base interp_weakening interp_switcher_return.
From griotte Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Export switcher switcher_preamble switcher_macros_spec switcher_helpers.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import switcher_call_states switcher_call_world.
From griotte.switcher.call Require Import call_path.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Import switcher_load_spec switcher_trap_safety switcher_unwind.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  (** The post-condition of [switcher_cc_specification_gen], once the
      caller's stack pointer [WCap true RWL Local b_stk e_stk a_stk] is known. *)
  Definition switcher_cc_post
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) : iProp Σ :=
    ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem_l stk_mem_h : list LWord) rcgp rcra rcs0 rcs1,
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world
                  (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais ⊤
              ∗ interp W2 C (callee_csp b_stk e_stk a_stk)
              ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
              ∗ ⌜ disjoint_from_heap (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) ⌝
              (* Interpretation of the world *)
              ∗ world_interp_open W2 C (LNonHeap <$> (callee_stk_region b_stk e_stk a_stk))
              ∗ StackOpenWorldResources interp W2 C (callee_stk_region b_stk e_stk a_stk) stk_mem_h
              ∗ cstack_frag cstk
              ∗ ([∗ list] a ∈ (callee_stk_region b_stk e_stk a_stk), ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ rcgp ∗ cra ↦ᵣ rcra ∗ cs0 ↦ᵣ rcs0 ∗ cs1 ↦ᵣ rcs1
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ stk_spill_a a_stk , (stk_spill_a a_stk ^+ SpillSlot_size)%a ]] ↦ₐ [[ stk_mem_l ]]
              ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_h ]]
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W2 wcgp_caller rcgp ∧
                load_heap_in_world W2 wcra_caller rcra ∧
                load_heap_in_world W2 wcs0_caller rcs0 ∧
                load_heap_in_world W2 wcs1_caller rcs1⌝
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't went through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
              ∗ na_own cerise_nais ⊤
              (* Registers are preserved *)
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ rcgp
              ∗ cra ↦ᵣ rcra
              ∗ cs0 ↦ᵣ rcs0
              ∗ cs1 ↦ᵣ rcs1
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ WInt 0
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              (* Stack frame *)
              ∗ [[ stk_spill_a a_stk , (stk_spill_a a_stk ^+ SpillSlot_size)%a ]] ↦ₐ
                  [[ [wcs0_caller; wcs1_caller; wcgp_caller; wcra_caller] ]]
              ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_callee stk_mem ]]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_interp W C
              ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
              ∗ cstack_frag cstk
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W wcgp_caller rcgp ∧
                load_heap_in_world W wcra_caller rcra ∧
                load_heap_in_world W wcs0_caller rcs0 ∧
                load_heap_in_world W wcs1_caller rcs1⌝
              ∗ £ 2
            )
          )
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  (** The spill of the callee-save registers at the cursor [a_stk] does not
      fit in the caller's stack [[b_stk, e_stk)]. *)
  Definition switcher_spill_overflows (b_stk e_stk a_stk : Addr) : Prop :=
    ¬ stk_spill_fits b_stk e_stk a_stk.

  (** The fault case of [switcher_cc_specification_gen]: the first store of
      the spill faults, because the callee-save registers do not fit on the
      caller's stack. The exception path of the switcher resumes the caller
      as if the call had returned [-ENOTENOUGHSTACK] and 0: the caller must
      be safe from there, with the PC and the registers of a successful
      return (the other registers hold any words; no interrupt status is
      promised), the switcher invariant closed, and its unchanged stack and
      world. *)
  Definition switcher_cc_fault
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) : iProp Σ :=
    ⌜ switcher_spill_overflows b_stk e_stk a_stk ⌝ -∗
    ∀ (rmap' : LReg),
      ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝ ∗
      na_own cerise_nais ⊤ ∗
      PC ↦ₚ lupdatePcPerm wcra_caller ∗
      cgp ↦ᵣ wcgp_caller ∗
      cra ↦ᵣ wcra_caller ∗
      cs0 ↦ᵣ wcs0_caller ∗
      cs1 ↦ᵣ wcs1_caller ∗
      csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
      ca0 ↦ᵣ WInt ENOTENOUGHSTACK ∗
      ca1 ↦ᵣ WInt 0 ∗
      ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ) ∗
      [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]] ∗
      world_interp W C ∗
      StackRevokedResources W C (stk_free b_stk e_stk a_stk) ∗
      cstack_frag cstk ∗
      interp_continuation cstk Ws Cs -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  (** The fault of the first spill of a trusted caller: the exception path
      of the switcher resumes the caller at [.Lswitch_just_return], whose
      return to [cra] goes to the continuation of the fault case. The
      resources come under an update at the time of the fault, with the
      switcher invariant closed: the caller's registers, of which [ct2] and
      [ctp] hold the scratch words of the checks, and its stack. *)
  Lemma switcher_cc_fault_resume
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (arg_rmap rmap rmap0 : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    switcher_spill_overflows b_stk e_stk a_stk ->
    dom rmap0 = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    switcher_trap_safety -∗
    (|={⊤}=>
       na_own cerise_nais ⊤ ∗
       cgp ↦ᵣ wcgp_caller ∗
       cra ↦ᵣ wcra_caller ∗
       cs0 ↦ᵣ wcs0_caller ∗
       cs1 ↦ᵣ wcs1_caller ∗
       csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
       (∃ wca0, ca0 ↦ᵣ wca0) ∗
       (∃ wca1, ca1 ↦ᵣ wca1) ∗
       ( [∗ map] r↦w ∈ rmap0, r ↦ᵣ w ) ∗
       [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]] ∗
       world_interp W C ∗
       StackRevokedResources W C (stk_free b_stk e_stk a_stk) ∗
       cstack_frag cstk ∗
       interp_continuation cstk Ws Cs) -∗
    switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs -∗
    trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
      (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hjalr Hspill Hdom) "#Hsafety Hres Hfault".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[_ #Hstatic]".
    iApply (trap_safe_resume_of_safety ⊤ with "Hsafety");
      [set_solver | set_solver | apply trap_no_resume_first_spill |].
    iMod "Hres" as "(Hna & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & [%wca0 Hca0] & [%wca1 Hca1]
                     & Hrmap0 & Hstk & Hworld_interp & Hstk_val & Hcstk & Hcont)".
    iModIntro.
    iDestruct (big_sepM_insert_2 _ _ cra wcra_caller with "[Hcra] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cgp wcgp_caller with "[Hcgp] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ csp with "[Hcsp] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cs0 wcs0_caller with "[Hcs0] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cs1 wcs1_caller with "[Hcs1] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ ca0 wca0 with "[Hca0] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ ca1 wca1 with "[Hca1] Hrmap0") as "Hrmap0"; [iFrame|].
    iExists _; iFrame "Hna Hrmap0".
    iSplit.
    { iPureIntro. intros r; apply elem_of_dom.
      rewrite !dom_insert_L Hdom.
      pose proof (all_registers_s_correct r).
      set_solver. }
    iIntros (rmap' Hfull_rmap' Hsame Hca0' Hca1') "HPC Hrmap' Hna".
    assert (rmap' !! cra = Some wcra_caller) as Hcra'
      by (rewrite Hsame //; by simplify_map_eq).
    assert (rmap' !! cgp = Some wcgp_caller) as Hcgp'
      by (rewrite Hsame //; by simplify_map_eq).
    assert (rmap' !! csp = Some (WCap true RWL Local b_stk e_stk a_stk : LWord)) as Hcsp'
      by (rewrite Hsame //; by simplify_map_eq).
    assert (rmap' !! cs0 = Some wcs0_caller) as Hcs0'
      by (rewrite Hsame //; by simplify_map_eq).
    assert (rmap' !! cs1 = Some wcs1_caller) as Hcs1'
      by (rewrite Hsame //; by simplify_map_eq).
    rewrite /registers_pointsto.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap'") as "[Hcra Hrmap']"; first done.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap'") as "[Hcgp Hrmap']";
      first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap'") as "[Hcsp Hrmap']";
      first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap'") as "[Hcs0 Hrmap']";
      first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap'") as "[Hcs1 Hrmap']";
      first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap'") as "[Hca0 Hrmap']";
      first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap'") as "[Hca1 Hrmap']";
      first by simplify_map_eq.
    (* [.Lswitch_just_return]: the return to the caller *)
    iPoseProof "Hstatic" as "[#Hswitcher _]".
    iApply (switcher_just_return_spec with "[- $HPC $Hcra $Hswitcher]").
    iSplit; last (iIntros "(%Hjalr' & _)"; congruence).
    iNext; iIntros "(HPC & Hcra & _)".
    iApply ("Hfault" $! Hspill with "[-]").
    iFrame.
    iPureIntro.
    rewrite !dom_delete_L (lregmap_full_dom _ Hfull_rmap').
    set_solver.
  Qed.

  (** The spill of a caller whose stack holds it does not fault. *)
  Lemma switcher_cc_fault_stack_fits
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    stk_spill_fits b_stk e_stk a_stk ->
    ⊢ switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
        b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs.
  Proof.
    iIntros (Hfits Hspill).
    rewrite /switcher_spill_overflows in Hspill.
    by exfalso.
  Qed.

  (** The full register file, from the registers left by
      [switcher_cc_exhausted_regs]. *)
  #[local] Lemma switcher_cc_full_regs (rmap0 : LReg)
    (wcra wcgp wcsp wcs0 wcs1 wca0 wca1 : LWord) :
    dom rmap0 = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    ( [∗ map] r↦w ∈ rmap0, r ↦ᵣ w ) -∗
    cra ↦ᵣ wcra -∗
    cgp ↦ᵣ wcgp -∗
    csp ↦ᵣ wcsp -∗
    cs0 ↦ᵣ wcs0 -∗
    cs1 ↦ᵣ wcs1 -∗
    ca0 ↦ᵣ wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    ∃ regs, ⌜ ∀ r, is_Some (regs !! r) ⌝ ∗ registers_pointsto regs.
  Proof.
    iIntros (Hdom) "Hrmap Hcra Hcgp Hcsp Hcs0 Hcs1 Hca0 Hca1".
    iDestruct (big_sepM_insert_2 _ _ cra wcra with "[Hcra] Hrmap") as "Hrmap"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cgp wcgp with "[Hcgp] Hrmap") as "Hrmap"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ csp wcsp with "[Hcsp] Hrmap") as "Hrmap"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cs0 wcs0 with "[Hcs0] Hrmap") as "Hrmap"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cs1 wcs1 with "[Hcs1] Hrmap") as "Hrmap"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ ca0 wca0 with "[Hca0] Hrmap") as "Hrmap"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ ca1 wca1 with "[Hca1] Hrmap") as "Hrmap"; [iFrame|].
    iExists _; iFrame "Hrmap"; iPureIntro.
    intros r; apply elem_of_dom.
    rewrite !dom_insert_L Hdom.
    pose proof (all_registers_s_correct r).
    set_solver.
  Qed.

  (** Failure path of [switcher_cc_specification_gen]: the trusted stack is
      exhausted. *)
  Lemma switcher_cc_spec_tstack_exhausted
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller wct2 wctp : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    (a_tstk : Addr) (save_area tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    disjoint_from_mmio b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    (b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (▷ switcher_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) ∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
    (∃ w, a_threadID ↦ₐ w) ∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_static ∗
    cstack_full cstk' ∗
    cstack_interp cstk' a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0, cs0 ↦ᵣ wcs0) ∗
    (∃ wcs1, cs1 ↦ᵣ wcs1) ∗
    cgp ↦ᵣ wcgp_caller ∗
    cra ↦ᵣ wcra_caller ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    ct1 ↦ᵣ wct1_caller ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (stk_saved_a a_stk) ∗
    switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller ∗
    [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_callee stk_mem ]] ∗
    (if is_entry_point_known
     then ∃ sb nargs,
            ⌜wct1_caller.(lw) = WSealed ot_switcher sb⌝ ∗
            sb ↦ₑ□{nargs} nargs ∗
            ( [∗ map] rarg↦warg ∈ arg_rmap,
                rarg ↦ᵣ warg
                ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                  then interp W C warg
                  else True )
     else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
    ) ∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), r ↦ᵣ w ) ∗
    world_interp W C ∗
    StackRevokedResources W C (stk_free b_stk e_stk a_stk) ∗
    cstack_frag cstk ∗
    interp_continuation cstk Ws Cs ∗
    switcher_cc_post W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk stk_mem cstk Ws Cs
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next.
    subst a_frameoffset a_save_end a_threadID a_next.
    (* Outline of the proof: [switcher_cc_exhausted_regs] collects the
       registers, [switch_trusted_stack_exhausted_path_spec] restores the
       registers, clears the others and returns, then close the switcher
       invariant and use the second post-condition.
       The return address is a valid target, so the jump back does not
       fault. *)
    iIntros (Hstk_mmio Hdom Hrdom Hstk_bounds Hlen_cstk Ha_tstk_e Hot_bounds Hret_jalr Hret_heap)
      "(Hclose_switcher_inv & Hna & Hmtdc & Hsave_area & Hframeoffset & HthreadID & Htstk & #Hstatic & Hcstk_full & Hstk_interp
      & #Hp_ot_switcher & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hctp & Hct2 & Hct1 & Hcsp & Hcells & Hstk
      & Hargs & Hregs & Hworld_interp & Hstk_val & Hcstk & Hcont & Hpost)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    stk_unfold. change (4 - 1)%Z with 3%Z in Hastk_bounds.
    iAssert ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg)%I
      with "[Hargs]" as "Hargs".
    { destruct is_entry_point_known.
      + iDestruct "Hargs" as "(% & % & _ & _ & Hargs)".
        iApply (big_sepM_impl with "Hargs"); eauto.
        iIntros (r w Hr) "!> [$ _]".
      + iApply (big_sepM_impl with "Hargs"); eauto.
        iIntros (r w Hr) "!> [$ _]".
    }
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iApply (switch_trusted_stack_exhausted_path_world_spec W C with
      "[- $HPC $Hcsp $Hcells $Hworld_interp $Hrmap0 $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1]");
      [done|done|done|].
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "(%Hrestored & %Hrmap' & Hworld_interp & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Hcells & Hrmap & _ & Hlc)".
    iSplit; cycle 1.
    { (* The return address of the caller is a valid target *)
      iIntros "%Hjalr".
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_in_world_nonheap in Hra; last done.
      subst rcra; congruence. }
    iIntros "[HPC Hlc']".
    iCombine "Hlc Hlc'" as "Hlc".
    iMod ("Hclose_switcher_inv" with
      "[$Hna $Hcstk_full Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hstk_interp]") as "HH".
    { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }
    iApply ("Hpost" $! W rmap' [] [] rcgp rcra rcs0 rcs1); iRight; iFrame "∗ %".
    iDestruct (switcher_stk_cells_region_4 with "Hcells") as "$";
      first (stk_unfold; solve_addr+Hastk).
    iPureIntro. stk_unfold.
    split_and!; solve_addr+Hastk Hastk_bounds Hastk_bstk.
  Qed.

  Lemma switcher_cc_specification_gen
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (* Trap safety of the switcher, with its invariant *)
    switcher_trap_safety

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller.(lw) ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ sb nargs,
              ⌜wct1_caller.(lw) = WSealed ot_switcher sb⌝ ∗
              sb ↦ₑ□{nargs} nargs ∗
              (* Argument registers, need to be safe-to-share *)
              ( [∗ map] rarg↦warg ∈ arg_rmap,
                  rarg ↦ᵣ warg
                  ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                    then interp W C warg
                    else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
    ∗ ⌜ revoked_addresses W (stk_free b_stk e_stk a_stk) ⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs


    ∗ ( ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem_l stk_mem_h : list LWord) rcgp rcra rcs0 rcs1,
        ( ( (* POST-CONDITION --- the call went through *)
              (* Also the return of ECOMPARTMENTFAIL when [ct1] is not a sealed export entry: the callee's frame is already pushed, so the exception entry pops it *)
              (* Also the return of ENOTENOUGHSTACK when the callee's stack is smaller than its minimum stack size: the return routine pops the frame *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world
                  (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais ⊤
              ∗ interp W2 C (callee_csp b_stk e_stk a_stk)
              ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
              ∗ ⌜ disjoint_from_heap (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) ⌝
              (* Interpretation of the world *)
              ∗ world_interp_open W2 C (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)
              ∗ StackOpenWorldResources interp W2 C (callee_stk_region b_stk e_stk a_stk) stk_mem_h
              ∗ cstack_frag cstk
              ∗ ([∗ list] a ∈ callee_stk_region b_stk e_stk a_stk,
                   ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ rcgp ∗ cra ↦ᵣ rcra ∗ cs0 ↦ᵣ rcs0 ∗ cs1 ↦ᵣ rcs1
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ stk_spill_a a_stk , (stk_spill_a a_stk ^+ SpillSlot_size)%a ]] ↦ₐ [[ stk_mem_l ]]
              ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_h ]]
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W2 wcgp_caller rcgp ∧
                load_heap_in_world W2 wcra_caller rcra ∧
                load_heap_in_world W2 wcs0_caller rcs0 ∧
                load_heap_in_world W2 wcs1_caller rcs1⌝
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't went through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
              ∗ na_own cerise_nais ⊤
              (* Registers are preserved *)
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ rcgp
              ∗ cra ↦ᵣ rcra
              ∗ cs0 ↦ᵣ rcs0
              ∗ cs1 ↦ᵣ rcs1
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ WInt 0
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              (* Stack frame *)
              ∗ [[ stk_spill_a a_stk , (stk_spill_a a_stk ^+ SpillSlot_size)%a ]] ↦ₐ
                  [[ [wcs0_caller; wcs1_caller; wcgp_caller; wcra_caller] ]]
              ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_callee stk_mem ]]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_interp W C
              ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
              ∗ cstack_frag cstk
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W wcgp_caller rcgp ∧
                load_heap_in_world W wcra_caller rcra ∧
                load_heap_in_world W wcs0_caller rcs0 ∧
                load_heap_in_world W wcs1_caller rcs1⌝
              ∗ £ 2
            )
          )
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
        ∧
        (* FAULT --- the callee-save registers do not fit on the caller's stack *)
        switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
          b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs )

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - [switch_csp_check_spec]: checks on the stack pointer;
       - [switch_entry_first_spill_path_spec]: spill the callee-save registers and
         push the stack pointer on the trusted stack; when the spill faults,
         close the switcher invariant and use the fault case;
       - when the trusted stack is exhausted:
         [switcher_cc_spec_tstack_exhausted];
       - [switcher_entry_point_prop]: the entry point satisfies the sealing
         predicate of the switcher;
       - [switch_stack_chop_path_spec]: clear the callee's stack frame and
         unseal the entry point; when the unsealing faults, push the frame and
         unwind to the caller's continuation ([trap_safe_unwind_logrel]);
       - [switcher_cc_world_reinstate]: reinstate the callee's stack frame;
       - [switcher_decode_entry_path_spec]: check the size of the callee's
         stack, load the callee and jump to it; when the stack is too small,
         push the frame and return to the caller's continuation
         ([switcher_call_stack_too_small_unwind]);
       - [switcher_inv_push_frame]: close the switcher invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros (Hstk_mmio Hstk_heap Hb_a Hdom Hrdom Hret_jalr Hret_heap)
      "(#Hsafety & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hworld_interp & Hstk_val & %Hstk_revoked & Hcstk & Hcont & Hpost)".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[#Hswitcher #Hstatic]".
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

    (* Open the switcher invariant *)
    iPoseProof "Hstatic" as "(#Hcode & #Hb_switcher & _)".
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].

    (* [.Lswitch_csp_check]: checks on the stack pointer *)
    iEval (rewrite -switcher_call_entry_label) in "HPC".
    iApply (switch_csp_check_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
    iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp) | (%Hcontra & _)]";
      last (exfalso; apply Hcontra, switcher_csp_checked_stk).

    (* [.Lswitch_entry_first_spill]: spill and push on the trusted stack *)
    iApply (switch_entry_first_spill_path_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hctp $Hct2 $Hcsp $Hstk $Hmtdc $Hframeoffset $Htstk $Hcode]");
      [done|done|done|done|].
    iSplit; cycle 1.
    { (* The callee-save registers do not fit on the caller's stack: close
         the switcher invariant, and return the fault resources *)
      iIntros (Hspill) "(Hcs0 & Hcs1 & Hcra & Hcgp & Hctp & Hct2 & Hcsp & Hstk
        & Hmtdc & Hframeoffset & Htstk)".
      iDestruct "Hpost" as "[_ Hfault]".
      iAssert ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg)%I with "[Hargs]" as "Hargs".
      { destruct is_entry_point_known.
        + iDestruct "Hargs" as "(% & % & _ & _ & Hargs)".
          iApply (big_sepM_impl with "Hargs"); eauto.
          iIntros (r w Hr) "!> [$ _]".
        + iApply (big_sepM_impl with "Hargs"); eauto.
          iIntros (r w Hr) "!> [$ _]". }
      iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
        as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
      subst hclose_switcher_inv hinv_switcher.
      iApply (switcher_cc_fault_resume with "Hsafety [-Hfault] Hfault");
        [done | exact Hspill | done |].
      iMod ("Hclose_switcher_inv" with
        "[$Hna $Hcstk_full Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hstk_interp]") as "Hna".
      { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }
      iModIntro.
      iFrame. }
    iDestruct "Hpost" as "[Hpost _]".
    iNext; iIntros "(%Hstk_bounds & Hcra & Hcgp & Hcsp & Hcells & Hstk & Hmtdc & _ & Hbranch)".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    stk_unfold. change (4 - 1)%Z with 3%Z in Hastk_bounds.
    iDestruct "Hbranch" as
      "[(%Ha_frame & %Ha_frame_e & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hframeoffset
         & Hframe_csp & Hframe_tbl & Hframe_cnt & [%tstk_next' Htstk] & Hlc)
       | (HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hframeoffset & Htstk)]"; cycle 1.
    { (* The trusted stack is exhausted *)
      iApply (switcher_cc_spec_tstack_exhausted with
        "[$Hclose_switcher_inv $Hna $Hmtdc $Hsave_area $Hframeoffset $HthreadID $Htstk $Hstatic
          $Hcstk_full $Hstk_interp
          $Hp_ot_switcher $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hctp $Hct2 $Hct1 $Hcsp $Hcells $Hstk
          $Hargs $Hregs $Hworld_interp $Hstk_val $Hcstk $Hcont $Hpost]"); done.
    }

    (* [.Lswitch_stack_chop]: clear the callee's stack frame and unseal the entry point *)
    iDestruct (switcher_entry_point_prop with "Hp_ot_switcher Htarget_v Hworld_interp")
      as "[Hworld_interp Hentry_prop]".
    set (W' := std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary).
    set (frame_tbl := λ wtbl : LWord,
           {| cf_tframe :=
                {| tf_csp := WCap true RWL Local b_stk e_stk (stk_saved_a a_stk);
                   tf_export_tbl := wtbl;
                   tf_error_count := 0 |};
              cf_saved :=
                {| cs_cra := wcra_caller;
                   cs_cgp := wcgp_caller;
                   cs_cs0 := wcs0_caller;
                   cs_cs1 := wcs1_caller |};
              ccrel := Known_to_Unknown
           |}).
    (* The frame holds the entry point, unsealed, if it is sealed *)
    set (frame := frame_tbl (lunseal Global wct1_caller)).
    (* The continuation of the caller, once the frame is pushed, whatever
       the word of its export table *)
    iAssert (∀ wtbl : LWord,
               interp W' C (callee_csp b_stk e_stk a_stk) -∗
               interp_continuation (cstack_push (frame_tbl wtbl) cstk) (W' :: Ws) (C :: Cs))%I
      with "[Hpost Hlc Hcont]" as "Hcont_frame".
    { iIntros (wtbl) "#Hstk4v".
      simpl.
      iFrame.
      iEval (cbn).
      rewrite (tf_caller_a_saved _ true RWL Local b_stk e_stk a_stk); [| done | done].
      rewrite ?cstack_eta.
      stk_unfold.
      iDestruct (interp_cap_disjoint_wl with "Hstk4v") as %[_ Hstk4_heap]; first done.
      iSplitR.
      { iSplit; first (iPureIntro; exact Hstk4_heap).
        iApply (interp_lea with "Hstk4v"); done. }
      iIntros (W'' HW' rcgp rcra rcs0 rcs1 ?????)
        "%Hrcgp %Hrcra %Hrcs0 %Hrcs1 (HPC & Hcra & Hcsp & Hgp & Hcs0 & Hcs1 & Ha0 & #Hv
      & Hca1 & #Hv' & % & Hregs & Hstk & Hstk' & Hworld_interp & Hcls & Hcont & Hcstk & Own)".
      iApply "Hpost";iLeft. simplify_eq.
      iFrame "∗#%".
      iSplit.
      {
        iApply interp_monotone_cap_nonheap;
          [exact Hstk4_heap|exact HW'|].
        done.
      }
      iSplit.
      { iPureIntro; repeat split; solve_addr+Hastk_bstk Hastk_bounds Hastk. }
      iSplit.
      { iPureIntro.
        assert ((b_stk <= b_stk)%a) as Hb by solve_addr.
        assert ((a_stk <= e_stk)%a) as He by solve_addr+Hastk Hastk_bounds.
        destruct (switcher_disjoint_subseg b_stk e_stk b_stk a_stk
                    Hb He (conj Hstk_mmio Hstk_heap)) as [_ Hstack_heap].
        exact Hstack_heap. }

      iSplit; last (iPureIntro; exact (conj Hrcgp (conj Hrcra (conj Hrcs0 Hrcs1)))).
      clear -HW'.
      iPureIntro; intros k a Ha; cbn.
      eapply region_state_pub_temp;[apply HW'|].
      apply std_sta_update_multiple_lookup_in_i.
      apply list_elem_of_lookup; eauto.
    }
    iApply (switch_stack_chop_path_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct2 $Hcsp $Hstk $Hb_switcher $Hct1 $Hcode]"); [done|done|done|].
    iSplit; cycle 1.
    { (* The entry point is not sealed by the switcher: the frame is already
         pushed on the trusted stack, so the exception entry returns to the
         caller, through its continuation *)
      iIntros "_ (Hcs0 & [%wcs1' Hcs1] & [%wct2_3 Hct2] & Hcsp & Hstk & [%wct1' Hct1])".
      subst hclose_switcher_inv hinv_switcher.
      iAssert ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg)%I with "[Hargs]" as "Hargs".
      { destruct is_entry_point_known.
        + iDestruct "Hargs" as "(% & % & _ & _ & Hargs)".
          iApply (big_sepM_impl with "Hargs"); eauto.
          iIntros (r w Hr) "!> [$ _]".
        + iApply (big_sepM_impl with "Hargs"); eauto.
          iIntros (r w Hr) "!> [$ _]". }
      iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
        as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
      iDestruct (switcher_cc_full_regs with "Hrmap0 Hcra Hcgp Hcsp Hcs0 Hcs1 Hca0 Hca1")
        as (regs) "[%Hfull_regs Hregs]"; first done.
      (* The frame of a failed unsealing: its table cell is still cleared *)
      set (frame_failed := frame_tbl (lword_of_word (WInt 0))).
      iApply (trap_safe_unwind_logrel_of_safety _ _ (cstack_push frame_failed cstk) (W' :: Ws) (C :: Cs)
                regs with "Hsafety [] [-]"); [done | | | |].
      { simpl. split; first apply related_sts_pub_refl_world. done. }
      { (* The unsealing is not the first spill *)
        apply trap_no_resume_switcher_pc. by vm_compute. }
      { (* The fault is in the switcher *)
        iLeft; iPureIntro. apply switcher_fault_pc_cap. }
      iMod (switcher_cc_world_reinstate with "Hworld_interp Hstk_val Hstk")
        as "(Hworld_interp & #Hstk4v & _ & _)"; [done| | | |].
      { stk_unfold; split_and!; solve_addr+Hastk Hastk_bounds Hastk_bstk. }
      { eapply switcher_disjoint_subseg; [reflexivity| |split; eassumption].
        stk_unfold; solve_addr+Hastk Hastk_bounds. }
      { eapply switcher_disjoint_subseg; [reflexivity| |split; eassumption].
        stk_unfold; solve_addr+Hastk Hastk_bounds. }
      pose proof (tf_export_tbl_cell_cleared (cf_tframe frame_failed) eq_refl) as Htbl_cell.
      iMod (switcher_inv_push_frame frame_failed cstk with
             "Hcstk_full Hcstk Hmtdc Hsave_area Hframeoffset HthreadID Hframe_csp Hframe_tbl Hframe_cnt
              Htstk Hstk_interp [Hcells] Hp_ot_switcher")
        as "[Hinv Hcstk]";
        [done|done|done|done|done|done|done|done|by intros _|done|exact Htbl_cell| |].
      { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
      iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".
      iDestruct ("Hcont_frame" $! (lword_of_word (WInt 0)) with "Hstk4v") as "Hcont_frame".
      by iFrame. }
    iNext; iIntros (wsb π)
      "(-> & %Htag & HPC & Hcs0 & [%wcs1' Hcs1] & [%wct2_3 Hct2] & Hcsp & Hstk & _ & Hct1 & _)".
    iDestruct ("Hentry_prop" with "[//] [//]") as "Hentry_ot".
    iNamed "Hentry_ot".
    rewrite /lword_of_word in Hw; simplify_eq.
    iAssert ([∗ map] r↦w ∈ arg_rmap,
               r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True)%I
      with "[Hargs]" as "Hargs".
    { destruct is_entry_point_known.
      + iDestruct "Hargs" as "(%sb & %nargs0 & %Hwct1 & (%g & %b & %e & %a & -> & Hentry) & Hargs)".
        cbn in Hwct1; simplify_eq.
        iDestruct (entry_nargs_agree_raw with "Hentry Htbl_entry") as %->; first lia.
        iFrame.
      + iApply (big_sepM_impl with "Hargs").
        iIntros "!> %k %w' _ [$ Hinterp]".
        destruct ( decide (k ∈ dom_arg_rmap nargs) ) ; auto.
    }

    (* Reinstate the callee's stack frame in the world *)
    iMod (switcher_cc_world_reinstate with "Hworld_interp Hstk_val Hstk")
      as "(Hworld_interp & #Hstk4v & %Hrelated & %Hrev)"; [done| | | |].
    { stk_unfold; split_and!; solve_addr+Hastk Hastk_bounds Hastk_bstk. }
    { eapply switcher_disjoint_subseg; [reflexivity| |split; eassumption].
      stk_unfold; solve_addr+Hastk Hastk_bounds. }
    { eapply switcher_disjoint_subseg; [reflexivity| |split; eassumption].
      stk_unfold; solve_addr+Hastk Hastk_bounds. }
    iSpecialize ("Hentry_cont" $! W' with "[]").
    { iPureIntro. by apply related_sts_pub_priv_world. }

    (* [.Lswitcher_decode_entry]: load the callee and jump to it *)
    iApply (switcher_decode_entry_path_spec W C with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra $Hcsp
          $Hargs $Hregs $Hcode]");
      [done|solve_addr|done|lia|lia|done|done|done|done| | | |done| |].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { tstack_unfold; solve_addr. }
    { tstack_unfold; solve_addr. }
    { rewrite !dom_delete_L Hdom. set_solver. }
    iNext; iSplit; cycle 1.
    { (* The callee's stack is too small: push the frame, close the switcher
         invariant, and return to the caller, through its continuation *)
      iIntros "(_ & HPC & [%wcs0' Hcs0] & [%wcs1'' Hcs1] & [%wct1' Hct1] & [%wct2' Hct2]
        & [%wctp' Hctp] & [%wcgp' Hcgp] & [%wcra' Hcra] & Hcsp & Hframe_tbl & Hargs & Hregs & _)".
      subst hclose_switcher_inv hinv_switcher.
      (* The table cell holds the unsealed entry *)
      pose proof (tf_export_tbl_cell_entry (cf_tframe frame) g_tbl b_tbl e_tbl a_tbl
               eq_refl Hbtbl_header ltac:(solve_addr) Htbl_shadow) as Htbl_cell.
      iMod (switcher_inv_push_frame frame cstk with
             "Hcstk_full Hcstk Hmtdc Hsave_area Hframeoffset HthreadID Hframe_csp Hframe_tbl Hframe_cnt
              Htstk Hstk_interp [Hcells] Hp_ot_switcher")
        as "[Hinv Hcstk]";
        [done|done|done|done|done|done|done|done|by intros _|done|right; exact Htbl_cell| |].
      { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
      iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".
      iDestruct (big_sepM_sep with "Hargs") as "[Hargs _]".
      iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
        as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
      iDestruct (switcher_cc_full_regs with "Hrmap0 Hcra Hcgp Hcsp Hcs0 Hcs1 Hca0 Hca1")
        as (regs) "[%Hfull_regs Hregs]"; first done.
      iDestruct ("Hcont_frame" with "Hstk4v") as "Hcont_frame".
      iApply (switcher_call_stack_too_small_unwind_of_safety W' C (cstack_push frame cstk)
                (W' :: Ws) (C :: Cs) regs);
        [done|simpl; split; [apply related_sts_pub_refl_world|done]|].
      iFrame "Hsafety".
      iFrame. }
    iIntros (mie arg_rmap' rmap')
      "(%Hbig & %Harg_rmap' & %Hrmap' & HPC & Hcgp & Hcra & Hcsp & Hframe_tbl & Hargs & Hregs & _)".

    (* Push the frame and close the switcher invariant *)
    (* The table cell holds the unsealed entry *)
    pose proof (tf_export_tbl_cell_entry (cf_tframe frame) g_tbl b_tbl e_tbl a_tbl
               eq_refl Hbtbl_header ltac:(solve_addr) Htbl_shadow) as Htbl_cell.
    iMod (switcher_inv_push_frame frame cstk with
           "Hcstk_full Hcstk Hmtdc Hsave_area Hframeoffset HthreadID Hframe_csp Hframe_tbl Hframe_cnt Htstk
            Hstk_interp [Hcells] Hp_ot_switcher")
      as "[Hinv Hcstk]";
      [done|done|done|done|done|done|done|done|by intros _|done|right; exact Htbl_cell| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".

    (* Execute the entry point of the callee *)
    iDestruct (switcher_call_entry_registers W W' C nargs arg_rmap' rmap' with
                "[$Hcgp $Hcra $Hcsp $Hstk4v $Hargs $Hregs]")
      as (regs) "[Hregs Hregs_interp]"; [done| |done|done|].
    { symmetry. apply std_update_multiple_heap. }
    iApply ("Hentry_cont" $! (cstack_push frame cstk) (W' :: Ws) (C :: Cs) regs
              (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)).
    iSplitL "Hcont_frame"; first by iApply "Hcont_frame".
    iSplit.
    { iPureIntro; simpl; split; [|split]; auto.
      apply related_sts_pub_refl_world.
    }
    iSplit; first (iPureIntro; split_and!; [done | reflexivity | reflexivity | exact Htbl_cell]).
    iFrame "HPC Hregs Hregs_interp Hworld_interp Hcstk Hna".
    iPureIntro; split; last exact Hbig.
    cbn. rewrite (tf_caller_a_saved _ true RWL Local b_stk e_stk a_stk); [by split | done | done].
  Qed.

  (* This specification unifies the two possible outcomes of the switcher call.
     It closes the world, and then revokes it.
   *)
  Lemma switcher_cc_specification_gen_revoked
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (* Trap safety of the switcher, with its invariant *)
    switcher_trap_safety

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller.(lw) ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ sb nargs,
              ⌜wct1_caller.(lw) = WSealed ot_switcher sb⌝ ∗
              sb ↦ₑ□{nargs} nargs ∗
              (* Argument registers, need to be safe-to-share *)
              ( [∗ map] rarg↦warg ∈ arg_rmap,
                  rarg ↦ᵣ warg
                  ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                    then interp W C warg
                    else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
    ∗ ⌜ revoked_addresses W (stk_free b_stk e_stk a_stk) ⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs


    (* POST-CONDITION *)
    ∗ ( ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem : list LWord) l' rcgp rcra rcs0 rcs1,
              (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2
                (l' ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_keys (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world
                  (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region b_stk e_stk a_stk,
                 ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (stk_free b_stk e_stk a_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (stk_free b_stk e_stk a_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ₚ lupdatePcPerm (rcra)
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ rcgp
            ∗ cra ↦ᵣ rcra
            ∗ cs0 ↦ᵣ rcs0
            ∗ cs1 ↦ᵣ rcs1
            ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W2 wcgp_caller rcgp ∧
                load_heap_in_world W2 wcra_caller rcra ∧
                load_heap_in_world W2 wcs0_caller rcs0 ∧
                load_heap_in_world W2 wcs1_caller rcs1⌝
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
        ∧
        (* FAULT --- the callee-save registers do not fit on the caller's stack *)
        switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
          b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs )


    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: apply [switcher_cc_specification_gen], then
       revoke the world in the post-condition, with
       [switcher_cc_revoke_returned] when the callee returned, and with
       [switcher_cc_revoke_exhausted] when the trusted stack was exhausted. *)
    iIntros (Hstk_mmio Hstk_heap Hb_a Hdom Hrdom Hret_jalr Hret_heap)
      "(#Hsafety & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hworld_interp & #Hstk_val & %Hrevoked_stk & Hcstk & Hcont & Hpost)".
    stk_unfold.
    iApply switcher_cc_specification_gen; eauto; iFrame "∗#%".
    iSplit; last by iDestruct "Hpost" as "[_ $]".
    iDestruct "Hpost" as "[Hpost _]".
    iIntros (W' rmap' stk_mem_l stk_mem_h rcgp rcra rcs0 rcs1).
    stk_unfold.
    iNext; iIntros "[H|H]".
    + clear stk_mem.
      iDestruct "H" as
        "(%Hrelated_pub_Wext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds & %Hstack_heap
      & Hworld_interp_C & Hstack_revoked_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & Hca0 & Hca1 & Hrmap & Hstk_l & Hstk_h & HK & %Hrestored & Hlc)".
      iMod (switcher_cc_revoke_returned with
             "Hinterp_W2_csp Hstk_val Hworld_interp_C Hstack_revoked_W2 Hstk_l Hstk_h Hlc")
        as (stk_mem l') "(% & Hrevoked_l' & % & Hstk_revoked & % & Hworld_interp & Hstk)";
        [done|done|naive_solver|].
      iApply "Hpost"; iFrame "∗ %".
    + clear W' stk_mem_l stk_mem_h.
      iDestruct "H" as
        "( %Hdom_rmap & %Hcsp_bounds
           & Hna
           & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
           & Hrmap & Hstk_l & Hstk_h
           & Hworld_interp_C & _
           & Hcstk_frag & HK & %Hrestored & Hlc)".
      iMod (switcher_cc_revoke_exhausted with "Hworld_interp_C Hstk_val Hstk_l Hstk_h Hlc")
        as (l') "(% & Hrevoked_l & % & % & Htemp & Hstk_revoked & % & Hworld_interp & Hstk)";
        [done|naive_solver|done|].
      iApply "Hpost"; iFrame "∗ %".
      iSplit; first iApply interp_int.
      iSplit; first iApply interp_int.
      iPureIntro.
      destruct Hrestored as ([Hgp Hgpf] & [Hra Hraf] & [Hs0 Hs0f] & [Hs1 Hs1f]).
      rewrite /load_heap_in_world /filter_heap std_update_multiple_heap.
      by repeat split.
  Qed.

End Switcher.
