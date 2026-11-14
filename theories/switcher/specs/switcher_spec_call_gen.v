From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From griotte Require Import sts_multiple_updates world_interp_revocation.
From griotte Require Export switcher switcher_preamble switcher_macros_spec switcher_helpers.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import switcher_call_states switcher_call_world.
From griotte.switcher.call Require Import call_path.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Import switcher_load_spec switcher_trap_safety switcher_unwind.


Section Switcher.
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
  #[local] Notation V := (interpO Σ).

  (** ** Stack cells and high-water mark *)

  (** ** Post-conditions *)

  (** The post-condition of [switcher_cc_specification_gen], once the
      caller's stack pointer [Cap RWL Local b_stk e_stk a_stk] is known, with
      MSHWM at [mshwm_v] at the call. *)
  Definition switcher_cc_post
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (mshwm_v : Z) : iProp Σ :=
    ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem_l stk_mem_h : list LWord) rcgp rcra rcs0 rcs1
        (m : InterruptStatus),
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world
                  (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own (tpool th) ⊤
              ∗ interp W2 C (callee_csp b_stk e_stk a_stk)
              ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
              ∗ ⌜ disjoint_from_heap (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) ⌝
              (* The local map, open on the callee's stack region, and the
                 map of Permanent regions *)
              ∗ local_region_map th W2 C
                  (open_l W2 (LNonHeap <$> (callee_stk_region b_stk e_stk a_stk)))
              ∗ perm_resources C
              ∗ StackOpenWorldResources interp W2 C (callee_stk_region b_stk e_stk a_stk) stk_mem_h
              ∗ ◯(CSTK)[th] cstk
              ∗ ([∗ list] a ∈ (callee_stk_region b_stk e_stk a_stk), ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
              ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ[th] rcgp ∗ cra ↦ᵣ[th] rcra ∗ cs0 ↦ᵣ[th] rcs0 ∗ cs1 ↦ᵣ[th] rcs1
              ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ[th] warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ[th] warg1 ∗ interp W2 C warg1)
              ∗ regs₀[th] rmap'
              ∗ stack_region (stk_spill_a a_stk) (stk_spill_a a_stk ^+ SpillSlot_size) stk_mem_l
              ∗ stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) stk_mem_h
              (* MSHWM is the caller's stack pointer *)
              ∗ hwm_res cstk a_stk
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧
                load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧
                load_heap wcs1_caller rcs1⌝
              (* The caller resumes at the posture of its return sentry *)
              ∗ ⌜route_pre th (default m (jalr_target_mie rcra.(lw)))⌝
              ∗ MIE ↦ₜ[th] default m (jalr_target_mie rcra.(lw))
              ∗ held (th := th) (default m (jalr_target_mie rcra.(lw)))
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't went through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
              ∗ na_own (tpool th) ⊤
              (* Registers are preserved *)
              ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ[th] rcgp
              ∗ cra ↦ᵣ[th] rcra
              ∗ cs0 ↦ᵣ[th] rcs0
              ∗ cs1 ↦ᵣ[th] rcs1
              ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ[th] WInt 0
              ∗ regs₀[th] rmap'
              (* Stack frame *)
              ∗ [[ stk_spill_a a_stk , stk_spill_a a_stk ^+ SpillSlot_size ]] ↦ₐ
                  [[ [wcs0_caller; wcs1_caller; wcgp_caller; wcra_caller] ]]
              ∗ stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)
                  (stk_mem_callee stk_mem)
              (* MSHWM is unchanged by the spill, or lowered to a spilled cell *)
              ∗ (∃ mshwm_v' : Z, ⌜ (mshwm_v' <= mshwm_v)%Z ⌝ ∗ hwm_res cstk mshwm_v')

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_resources W C
              ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
              ∗ ◯(CSTK)[th] cstk
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧
                load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧
                load_heap wcs1_caller rcs1⌝
              (* The caller resumes at the posture of its return sentry,
                 from the switcher's *)
              ∗ ⌜route_pre th (default InterruptDisabled (jalr_target_mie rcra.(lw)))⌝
              ∗ MIE ↦ₜ[th] default InterruptDisabled (jalr_target_mie rcra.(lw))
              ∗ held (th := th) (default InterruptDisabled (jalr_target_mie rcra.(lw)))
              ∗ £ 2
            )
          )
            -∗ safe[th].

  (** The spill of the callee-save registers at the cursor [a_stk] does not
      fit in the caller's stack $[b_stk, e_stk)$. *)
  Definition switcher_spill_overflows (b_stk e_stk a_stk : Addr) : Prop :=
    ¬ stk_spill_fits b_stk e_stk a_stk.

  (** The fault case of [switcher_cc_specification_gen]: the first store of
      the spill faults, because the callee-save registers do not fit on the
      caller's stack. The exception path of the switcher resumes the caller
      as if the call had returned [-ENOTENOUGHSTACK] and 0: the caller must
      be safe from there, with the PC and the registers of a successful
      return (the other registers hold any words), the posture that its
      return sentry restores from the switcher's, the trusted-stack invariant
      closed, its unchanged stack and world, and MSHWM at its value [mshwm_v] at
      the call. *)
  Definition switcher_cc_fault
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (mshwm_v : Z) : iProp Σ :=
    ⌜ switcher_spill_overflows b_stk e_stk a_stk ⌝ -∗
    ∀ (rmap' : LReg),
      ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝ ∗
      na_own (tpool th) ⊤ ∗
      PC ↦ₚ[th] lupdatePcPerm wcra_caller ∗
      cgp ↦ᵣ[th] wcgp_caller ∗
      cra ↦ᵣ[th] wcra_caller ∗
      cs0 ↦ᵣ[th] wcs0_caller ∗
      cs1 ↦ᵣ[th] wcs1_caller ∗
      csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
      ca0 ↦ᵣ[th] WInt ENOTENOUGHSTACK ∗
      ca1 ↦ᵣ[th] WInt 0 ∗
      regs[th] rmap' ∗
      stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem ∗
      hwm_res cstk mshwm_v ∗
      world_resources W C ∗
      StackRevokedResources W C (stk_free b_stk e_stk a_stk) ∗
      ◯(CSTK)[th] cstk ∗
      interp_continuation cstk Ws Cs ∗
      MIE ↦ₜ[th] default InterruptDisabled (jalr_target_mie wcra_caller.(lw)) ∗
      held (th := th) (default InterruptDisabled (jalr_target_mie wcra_caller.(lw))) -∗
      safe[th].

  (** The fault of the first spill of a trusted caller: the exception path
      of the switcher resumes the caller at [.Lswitch_just_return], whose
      return to [cra] goes to the continuation of the fault case. The
      resources come under an update at the time of the fault, with the
      trusted-stack invariant closed: the caller's registers, of which [ct2] and
      [ctp] hold the scratch words of the checks, its stack, and the
      high-water-mark registers. *)
  Lemma switcher_cc_fault_resume
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (rmap0 : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (mshwm_v : Z) :
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    switcher_spill_overflows b_stk e_stk a_stk ->
    dom rmap0 = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    th ≠ CtxSwitch ->

    switcher_trap_safety -∗
    (|={⊤}=>
       na_own (tpool th) ⊤ ∗
       cgp ↦ᵣ[th] wcgp_caller ∗
       cra ↦ᵣ[th] wcra_caller ∗
       cs0 ↦ᵣ[th] wcs0_caller ∗
       cs1 ↦ᵣ[th] wcs1_caller ∗
       csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
       (∃ wca0, ca0 ↦ᵣ[th] wca0) ∗
       (∃ wca1, ca1 ↦ᵣ[th] wca1) ∗
       regs[th] rmap0 ∗
       stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem ∗
       hwm_res cstk mshwm_v ∗
       world_resources W C ∗
       StackRevokedResources W C (stk_free b_stk e_stk a_stk) ∗
       ◯(CSTK)[th] cstk ∗
       interp_continuation cstk Ws Cs ∗
       MIE ↦ₜ[th] InterruptDisabled ∗
       held (th := th) InterruptDisabled) -∗
    switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v -∗
    trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
      (HO th).
  Proof.
    iIntros (Hjalr Hspill Hdom Hth) "#Hsafety Hres Hfault".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[_ #Hstatic]".
    iApply (trap_safe_resume_of_safety ⊤ with "Hsafety");
      [set_solver | apply trap_no_resume_first_spill |].
    iMod "Hres" as "(Hna & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & [%wca0 Hca0] & [%wca1 Hca1]
                     & Hrmap0 & Hstk & Hhwm & Hworld_res & Hstk_val & Hcstk & Hcont & Hmie
                     & Hheld)".
    iModIntro.
    iDestruct (big_sepM_insert_2 _ _ cra wcra_caller with "[Hcra] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cgp wcgp_caller with "[Hcgp] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ csp with "[Hcsp] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cs0 wcs0_caller with "[Hcs0] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ cs1 wcs1_caller with "[Hcs1] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ ca0 wca0 with "[Hca0] Hrmap0") as "Hrmap0"; [iFrame|].
    iDestruct (big_sepM_insert_2 _ _ ca1 wca1 with "[Hca1] Hrmap0") as "Hrmap0"; [iFrame|].
    iExists _, InterruptDisabled; iFrame "Hna Hrmap0 Hmie Hheld".
    iSplit.
    { iPureIntro. intros r; apply elem_of_dom.
      rewrite !dom_insert_L Hdom.
      pose proof (all_registers_s_correct r).
      set_solver. }
    iSplit; first done.
    (* MSHWM is unchanged by the fault and the resume *)
    iExists cstk, mshwm_v. iFrame "Hhwm".
    iIntros (rmap' Hfull_rmap' Hsame Hca0' Hca1') "HPC Hrmap' Hhwm Hna Hmie Hheld".
    assert (rmap' !! cra = Some wcra_caller) as Hcra'
      by (rewrite Hsame //; by simplify_map_eq).
    assert (rmap' !! cgp = Some wcgp_caller) as Hcgp'
      by (rewrite Hsame //; by simplify_map_eq).
    assert (rmap' !! csp = Some (Cap RWL Local b_stk e_stk a_stk : LWord)) as Hcsp'
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
    iApply (switcher_just_return_spec _ InterruptDisabled with
              "[- $HPC $Hcra $Hswitcher $Hmie $Hheld]"); [done | done |].
    iSplit; last (iIntros "(%Hjalr' & _)"; congruence).
    iNext; iIntros "(HPC & Hcra & Hmie & Hheld & _)".
    iApply ("Hfault" $! Hspill with "[-]").
    iFrame.
    iPureIntro.
    rewrite !dom_delete_L (lregmap_full_dom _ Hfull_rmap').
    set_solver.
  Qed.

  (** The spill of a caller whose stack holds it does not fault. *)
  Lemma switcher_cc_fault_stack_fits
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (mshwm_v : Z) :
    stk_spill_fits b_stk e_stk a_stk ->
    ⊢ switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
        b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v.
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
    regs[th] rmap0 -∗
    cra ↦ᵣ[th] wcra -∗
    cgp ↦ᵣ[th] wcgp -∗
    csp ↦ᵣ[th] wcsp -∗
    cs0 ↦ᵣ[th] wcs0 -∗
    cs1 ↦ᵣ[th] wcs1 -∗
    ca0 ↦ᵣ[th] wca0 -∗
    ca1 ↦ᵣ[th] wca1 -∗
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

  (** The argument registers of [switcher_cc_specification_gen], with the
      validity of the arguments. *)
  Definition switcher_cc_args (W : WORLD) (C : CmptName) (wct1 : LWord) (arg_rmap : LReg)
    (is_entry_point_known : bool) : iProp Σ :=
    (if is_entry_point_known
    then ∃ sb nargs,
           ⌜wct1.(lw) = WSealed ot_switcher sb⌝ ∗
           sb ↦ₑ□{nargs} nargs ∗
           ( [∗ map] rarg↦warg ∈ arg_rmap,
               rarg ↦ᵣ[th] warg
               ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                 then interp W C warg
                 else True )
    else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗ interp W C warg ))%I.

  #[local] Lemma switcher_cc_args_regs W C wct1 arg_rmap is_entry_point_known :
    switcher_cc_args W C wct1 arg_rmap is_entry_point_known ⊢
    regs[th] arg_rmap.
  Proof.
    iIntros "Hargs".
    destruct is_entry_point_known.
    - iDestruct "Hargs" as (sb nargs) "(_ & _ & Hargs)".
      iApply (big_sepM_impl with "Hargs").
      iIntros "!>" (r w Hr) "[$ _]".
    - iApply (big_sepM_impl with "Hargs").
      iIntros "!>" (r w Hr) "[$ _]".
  Qed.

  (** The arguments of an entry point that takes [nargs] arguments. *)
  #[local] Lemma switcher_cc_args_entry W C π g_tbl b_tbl e_tbl a_tbl arg_rmap
    is_entry_point_known (posture : InterruptStatus) (nargs minstk : nat) (off : Z) :
    nargs <= 7 ->
    switcher_cc_args W C (Sealed ot_switcher RO g_tbl b_tbl e_tbl a_tbl @@? π) arg_rmap
      is_entry_point_known -∗
    a_tbl ↦ₐ□ WInt (encode_entry_point posture (Z.of_nat nargs) (Z.of_nat minstk) off) -∗
    [∗ map] r↦w ∈ arg_rmap,
      r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True.
  Proof.
    iIntros (Hnargs) "Hargs #Htbl_entry".
    destruct is_entry_point_known.
    - iDestruct "Hargs" as (sb nargs0) "(%Hwct1 & (%g & %b & %e & %a & -> & Hentry) & Hargs)".
      cbn in Hwct1; simplify_eq.
      iDestruct (entry_nargs_agree_raw with "Hentry Htbl_entry") as %->; first lia.
      iExact "Hargs".
    - iApply (big_sepM_impl with "Hargs").
      iIntros "!>" (k w' _) "[$ Hinterp]".
      by destruct (decide (k ∈ dom_arg_rmap nargs)).
  Qed.

  (** The frame of the caller, pushed on the trusted stack, with the word
      [wtbl] in its table cell. *)
  Definition switcher_cc_frame (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (wtbl : LWord) : cframe :=
    {| cf_tframe :=
         {| tf_csp := Cap RWL Local b_stk e_stk (stk_saved_a a_stk);
            tf_export_tbl := wtbl;
            tf_error_count := 0 |};
       cf_saved :=
         {| cs_cra := wcra_caller;
            cs_cgp := wcgp_caller;
            cs_cs0 := wcs0_caller;
            cs_cs1 := wcs1_caller |};
       ccrel := Known_to_Unknown
    |}.

  (** The continuation of the caller, once its frame is pushed, whatever
      the word of its table cell. The caller's stack starts at the base of
      the thread's stack. *)
  #[local] Lemma switcher_cc_cont_frame
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (mshwm_v : Z) (wtbl : LWord) :
    let W' := std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    b_stk = cstk_hwm_base cstk ->

    switcher_cc_post W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v -∗
    £ 2 -∗
    interp_continuation cstk Ws Cs -∗
    interp W' C (callee_csp b_stk e_stk a_stk) -∗
    interp_continuation
      (cstack_push (switcher_cc_frame wcgp_caller wcra_caller wcs0_caller wcs1_caller
                      b_stk e_stk a_stk wtbl) cstk)
      (W' :: Ws) (C :: Cs).
  Proof.
    intros W'.
    iIntros (Hstk_mmio Hstk_heap (Hastk_bstk & Hastk_bounds & Hastk) Hbase)
      "Hpost Hlc Hcont #Hstk4v".
    cbn.
    iFrame "Hcont".
    rewrite (tf_caller_a_saved _ true RWL Local b_stk e_stk a_stk); [| done | done].
    rewrite ?cstack_eta.
    stk_unfold.
    iDestruct (interp_cap_disjoint_wl with "Hstk4v") as %[_ Hstk4_heap]; first done.
    iSplitR.
    { iSplit; first (iPureIntro; exact Hstk4_heap).
      iApply (interp_lea with "Hstk4v"); done. }
    (* The caller's stack starts at the base of the thread's stack *)
    iSplitR; first (iPureIntro; exact Hbase).
    iIntros (W'' HW' rcgp rcra rcs0 rcs1 warg0 warg1 rmap' stk_mem_l stk_mem_h m)
      "%Hrcgp %Hrcra %Hrcs0 %Hrcs1 (HPC & Hcra & Hcsp & Hgp & Hcs0 & Hcs1 & Ha0 & #Hv
    & Hca1 & #Hv' & %Hdom' & Hregs & Hhwm & Hstk & Hstk' & Hlocal & Hperm & Hcls & Hcont & Hcstk
    & Own & _ & %Hpre_ret & Hmie & Hheld)".
    iApply ("Hpost" $! W'' rmap' stk_mem_l stk_mem_h rcgp rcra rcs0 rcs1 m); iLeft.
    iFrame "Hcls Hlocal Hperm HPC Hgp Hcra Hcs0 Hcs1 Hcsp Hregs Hstk Hstk' Hhwm Hcont Hcstk Own
      Hlc Hmie Hheld".
    iSplit; first (iPureIntro; exact HW').
    iSplit; first (iPureIntro; rewrite Hdom'; set_solver).
    iSplit.
    { iApply interp_monotone_cap_nonheap; [exact Hstk4_heap|exact HW'|done]. }
    iSplit.
    { iPureIntro; stk_unfold; repeat split; solve_addr+Hastk_bstk Hastk_bounds Hastk. }
    iSplit.
    { iPureIntro.
      assert ((b_stk <= b_stk)%a) as Hb by solve_addr.
      assert ((a_stk <= e_stk)%a) as He by solve_addr+Hastk Hastk_bounds.
      destruct (switcher_disjoint_subseg b_stk e_stk b_stk a_stk
                  Hb He (conj Hstk_mmio Hstk_heap)) as [_ Hstack_heap].
      exact Hstack_heap. }
    iSplit.
    { clear -HW'.
      iPureIntro; intros k a Ha; cbn.
      eapply region_state_pub_temp; [apply HW'|].
      apply std_sta_update_multiple_lookup_in_i.
      apply list_elem_of_lookup; eauto. }
    iSplitL "Ha0"; first (iExists warg0; iFrame "Ha0 Hv").
    iSplitL "Hca1"; first (iExists warg1; iFrame "Hca1 Hv'").
    iPureIntro; exact (conj (conj Hrcgp (conj Hrcra (conj Hrcs0 Hrcs1))) Hpre_ret).
  Qed.

  (** Fault of the first spill: close the trusted-stack invariant and resume the
      caller through [switcher_cc_fault_resume]. *)
  #[local] Lemma switcher_cc_spill_fault
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    (cstk' : CSTK) (a_tstk : Addr) (tstk_next : list LWord) (wct2 wctp : LWord) (mshwm_v : Z) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    (cstk_hwm_base cstk <= mshwm_v)%Z ->

    switcher_trap_safety -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    switcher_cc_args W C wct1_caller arg_rmap is_entry_point_known -∗
    regs[th] delete ctp (delete ct2 rmap) -∗
    world_resources W C -∗
    StackRevokedResources W C (stk_free b_stk e_stk a_stk) -∗
    ◯(CSTK)[th] cstk -∗
    interp_continuation cstk Ws Cs -∗
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk) -∗
    switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v -∗
    MIE ↦ₜ[th] InterruptDisabled -∗
    held (th := th) InterruptDisabled -∗
    ( ⌜ ¬ stk_spill_fits b_stk e_stk a_stk ⌝ ∗
      csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
      ct2 ↦ᵣ[th] wct2 ∗
      ctp ↦ᵣ[th] wctp ∗
      cs0 ↦ᵣ[th] wcs0_caller ∗
      cs1 ↦ᵣ[th] wcs1_caller ∗
      cra ↦ᵣ[th] wcra_caller ∗
      cgp ↦ᵣ[th] wcgp_caller ∗
      ct1 ↦ᵣ[th] wct1_caller ∗
      stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem ∗
      hwm_regs (cstk_hwm_base cstk) mshwm_v ∗
      mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      switcher_hazard ∗
      [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
      trap_safe (switcher_label_pc ".Lswitch_entry_first_spill") ⊤
        (HO th) ).
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    iIntros (Hdom Hrdom Hret_jalr Hhb_h)
      "#Hsafety Hopened Hargs Hregs Hworld_interp Hstk_val Hcstk Hcont #Hts Hfault Hmie Hheld
       (%Hspill & Hcsp & Hct2 & Hctp & Hcs0 & Hcs1 & Hcra & Hcgp & Hct1 & Hstk & Hhwm_regs
       & Hmtdc & Hframeoffset & Hhazard & Htstk)".
    iDestruct (hwm_res_of_regs with "Hts Hhwm_regs") as "Hhwm"; first done.
    iDestruct (switcher_cc_args_regs with "Hargs") as "Hargs".
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iAssert (⌜th ≠ CtxSwitch⌝)%I as %Huser; first (iNamed "Hopened"; done).
    iApply (switcher_cc_fault_resume with "Hsafety [-Hfault] Hfault");
      [done | exact Hspill | done | exact Huser |].
    iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
    iModIntro.
    iFrame "Hna Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap0 Hstk Hhwm Hworld_interp Hstk_val Hcstk
      Hcont Hmie Hheld".
  Qed.

  (** Failure path of [switcher_cc_specification_gen]: the trusted stack is
      exhausted. *)
  #[local] Lemma switcher_cc_spec_tstack_exhausted
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    (cstk' : CSTK) (g_tstk : Locality) (a_tstk : Addr) (tstk_next : list LWord) (mshwm_v mshwm_v' : Z) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    disjoint_from_mmio b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->
    (cstk_hwm_base cstk <= mshwm_v)%Z ->

    switcher_trap_safety -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    switcher_cc_args W C wct1_caller arg_rmap is_entry_point_known -∗
    regs[th] delete ctp (delete ct2 rmap) -∗
    world_resources W C -∗
    StackRevokedResources W C (stk_free b_stk e_stk a_stk) -∗
    ◯(CSTK)[th] cstk -∗
    interp_continuation cstk Ws Cs -∗
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk) -∗
    switcher_cc_post W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v -∗
    MIE ↦ₜ[th] InterruptDisabled -∗
    held (th := th) InterruptDisabled -∗
    ( ⌜ switcher_stk_bounds b_stk e_stk a_stk ⌝ ∗
      ⌜ (mshwm_v' = mshwm_v ∨ (cstk_hwm_base cstk <= mshwm_v' < mshwm_v ∧ stk_spill_a a_stk <= mshwm_v' < a_stk))%Z ⌝ ∗
      PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
      cs0 ↦ᵣ[th] WInt (e_trusted_stack - b_trusted_stack) ∗
      cs1 ↦ᵣ[th] wcs1_caller ∗
      ctp ↦ᵣ[th] WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      ct2 ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
      csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (stk_saved_a a_stk) ∗
      cra ↦ᵣ[th] wcra_caller ∗
      cgp ↦ᵣ[th] wcgp_caller ∗
      ct1 ↦ᵣ[th] wct1_caller ∗
      switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller ∗
      stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) (stk_mem_callee stk_mem) ∗
      hwm_regs (cstk_hwm_base cstk) mshwm_v' ∗
      mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
      switcher_hazard ∗
      [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
      safe[th] ).
  Proof.
    intros a_frameoffset a_next; subst a_frameoffset a_next.
    (* Outline of the proof: [switcher_cc_exhausted_regs] collects the
       registers, [switch_trusted_stack_exhausted_path_spec] restores
       the registers, clears the others and returns, then close the trusted-stack
       invariant and use the second post-condition. The return address is a
       valid target, so the jump back does not fault. *)
    iIntros (Hstk_mmio Hdom Hrdom Hret_jalr Hret_heap Hhb_h)
      "#Hsafety Hopened Hargs Hregs Hworld_interp Hstk_val Hcstk Hcont #Hts Hpost Hmie Hheld
       (%Hstk_bounds & %Hh' & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hcra & Hcgp & Hct1 & Hcells
       & Hstk & Hhwm_regs & Hmtdc & Hframeoffset & Hhazard & Htstk)".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[_ #Hstatic]".
    iPoseProof "Hstatic" as "[#Hcode _]".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    (* MSHWM is unchanged by the spill, or lowered to a spilled cell *)
    iDestruct (hwm_res_of_regs with "Hts Hhwm_regs") as "Hhwm".
    { destruct Hh' as [-> | Hh'']; solve_addr. }
    iDestruct (switcher_cc_args_regs with "Hargs") as "Hargs".
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iAssert (⌜th ≠ CtxSwitch⌝)%I as %Huser; first (iNamed "Hopened"; done).
    iApply (switch_trusted_stack_exhausted_path_spec with
      "[- $HPC $Hcsp $Hcells $Hrmap0 $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1
        $Hcode $Hmie $Hheld]");
      [done|done|done|done|].
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "(%Hrestored & %Hrmap' & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Hcells & Hrmap & Hlc)".
    iSplit; cycle 1.
    { (* The return address of the caller is a valid target *)
      iIntros "%Hjalr".
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_nonheap in Hra; last done.
      subst rcra; congruence. }
    iIntros "(HPC & Hmie & Hheld & Hlc')".
    iCombine "Hlc Hlc'" as "Hlc".
    iMod (trusted_stack_inv_opened_close with "Hopened Hmtdc Hframeoffset Hhazard Htstk") as "Hna".
    iApply ("Hpost" $! W rmap' [] [] rcgp rcra rcs0 rcs1 InterruptDisabled); iRight.
    iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hstk Hworld_interp Hstk_val Hcstk
      Hcont Hlc Hmie Hheld".
    iSplit; first (iPureIntro; rewrite Hrmap'; set_solver).
    iSplit; first (iPureIntro; rewrite /callee_stk_bounds; stk_unfold;
                   split_and!; solve_addr+Hastk Hastk_bounds Hastk_bstk).
    iSplitL "Hcells".
    { iApply (switcher_stk_cells_region_4 with "Hcells"); stk_unfold; solve_addr+Hastk. }
    iSplitL "Hhwm".
    { iExists mshwm_v'. iFrame "Hhwm". iPureIntro. destruct Hh' as [-> | Hh'']; lia. }
    iPureIntro; split; first exact Hrestored.
    intros Hcs; by destruct Huser.
  Qed.

  (** Fault of the unsealing: the frame is pushed, with the table word
      [WInt 0] and any word in its table cell, and the exception entry unwinds the call to the caller's
      continuation. The cells of the caller's stack below MSHWM held
      integers at the call, so the call path leaves integers in the callee's
      stack. *)
  #[local] Lemma switcher_cc_unseal_fault
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    (cstk' : CSTK) (g_tstk : Locality) (a_tstk : Addr) (mshwm_v mshwm_v' : Z) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    let a_free := (a_next ^+ TrustedStackFrame_size) in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp) in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount) in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    b_stk = cstk_hwm_base cstk ->
    (e_stk <= cstk_hwm_top cstk)%a ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    revoked_addresses W (stk_free b_stk e_stk a_stk) ->
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->
    (cstk_hwm_base cstk <= mshwm_v)%Z ->
    length (stk_free b_stk e_stk a_stk) = length stk_mem ->
    Forall lword_int (take (Z.to_nat (mshwm_v - stk_free_b b_stk a_stk)) stk_mem) ->

    thread_in th C -∗
    switcher_trap_safety -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    switcher_cc_args W C wct1_caller arg_rmap is_entry_point_known -∗
    regs[th] delete ctp (delete ct2 rmap) -∗
    world_resources W C -∗
    StackRevokedResources W C (stk_free b_stk e_stk a_stk) -∗
    ◯(CSTK)[th] cstk -∗
    interp_continuation cstk Ws Cs -∗
    thread_stack_bounds (cstk_hwm_base cstk) (cstk_hwm_top cstk) -∗
    switcher_cc_post W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v -∗
    MIE ↦ₜ[th] InterruptDisabled -∗
    held (th := th) InterruptDisabled -∗
    ( ⌜ ¬ ∃ wsb π, wct1_caller = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ ∗
      ⌜ switcher_stk_bounds b_stk e_stk a_stk ⌝ ∗
      ⌜ (b_trusted_stack + tstack_frame_offset (S (length cstk'.(cstk_frames))))%a = Some a_next ⌝ ∗
      ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
      ⌜ (mshwm_v' = mshwm_v ∨ (cstk_hwm_base cstk <= mshwm_v' < mshwm_v ∧ stk_spill_a a_stk <= mshwm_v' < a_stk))%Z ⌝ ∗
      ⌜ (stk_callee_b b_stk a_stk <= mshwm_v')%Z ⌝ ∗
      cs0 ↦ᵣ[th] SealRange (true,true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
      (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
      (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
      ctp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack a_next ∗
      csp ↦ᵣ[th] chopped_csp b_stk e_stk a_stk ∗
      cra ↦ᵣ[th] wcra_caller ∗
      cgp ↦ᵣ[th] WInt mshwm_v' ∗
      ct1 ↦ᵣ[th] - ∗
      switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller ∗
      stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)
        (stack_zeroed_from (stk_callee_b b_stk a_stk) mshwm_v' (stk_mem_callee stk_mem)) ∗
      hwm_regs (cstk_hwm_base cstk) mshwm_v' ∗
      mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
      a_frameoffset ↦ₐ WInt (tstack_frameoffset (S (length cstk'.(cstk_frames)))) ∗
      switcher_hazard ∗
      a_csp ↦ₐ Cap RWL Local b_stk e_stk (stk_saved_a a_stk) ∗
      a_export_table ↦ₐ - ∗
      a_error_count ↦ₐ WInt 0 ∗
      (∃ tstk_next', [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]]) ∗
      £ 2 -∗
      trap_safe (switcher_label_pc ".Lswitcher_decode_entry") ⊤
        (HO th) ).
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hstk_mmio Hstk_heap Hbase Htop Hdom Hrdom Hstk_revoked Hret_jalr Hret_heap Hhb_h
             Hlen Hints_free)
      "#Hthread #Hsafety Hopened Hargs Hregs Hworld_interp Hstk_val Hcstk Hcont #Hts Hpost Hmie
       Hheld
       (_ & %Hstk_bounds & %Ha_next & %Ha_next_e & %Hh' & %Hcallee_h' & Hcs0 & [%wcs1' Hcs1]
       & [%wct2' Hct2] & Hctp & Hcsp & Hcra & Hcgp & [%wct1' Hct1] & Hcells & Hstk & Hhwm_regs
       & Hmtdc & Hframeoffset & Hhazard & Hframe_csp & [%wtbl Hframe_tbl] & Hframe_cnt
       & [%tstk_next' Htstk] & Hlc)".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    set (W' := std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary).
    (* The frame of a failed unsealing: its table word is [WInt 0] *)
    set (frame := switcher_cc_frame wcgp_caller wcra_caller wcs0_caller wcs1_caller
                    b_stk e_stk a_stk (lword_of_word (WInt 0))).
    (* The callee's stack holds integers *)
    assert (Forall lword_int
              (stack_zeroed_from (stk_callee_b b_stk a_stk) mshwm_v' (stk_mem_callee stk_mem)))
      as Hints_callee.
    { apply (callee_stk_ints b_stk e_stk a_stk mshwm_v mshwm_v'); [done|done|done|].
      destruct Hh' as [-> | Hh'']; [by left | right; lia]. }
    iDestruct (stack_ints_of_region _ _ _ Hints_callee with "Hstk") as "Hstk".
    (* MSHWM is in the pushed frame's registers *)
    iDestruct (hwm_res_of_regs with "Hts Hhwm_regs") as "Hhwm".
    { destruct Hh' as [-> | Hh'']; solve_addr. }
    iEval (rewrite -(hwm_res_push frame cstk mshwm_v')) in "Hhwm".
    iDestruct (switcher_cc_args_regs with "Hargs") as "Hargs".
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iDestruct (switcher_cc_full_regs with "Hrmap0 Hcra Hcgp Hcsp Hcs0 Hcs1 Hca0 Hca1")
      as (regs) "[%Hfull_regs Hregs]"; first done.
    iApply (trap_safe_unwind_logrel_of_safety W' C (cstack_push frame cstk) (W' :: Ws) (C :: Cs)
              regs with "Hthread Hsafety [] [-]"); [done | | | |].
    { simpl. split; first apply related_sts_pub_refl_world. done. }
    { (* The unsealing is not the first spill *)
      apply trap_no_resume_switcher_pc. by vm_compute. }
    { (* The fault is in the switcher *)
      iLeft; iPureIntro. apply switcher_fault_pc_cap. }
    iDestruct (world_resources_split with "Hworld_interp") as "[Hlocal Hperm]".
    iMod (local_cc_world_reinstate _ W C b_stk e_stk a_stk
            (cstk_hwm_base cstk) (cstk_hwm_top cstk) with "Hlocal Hstk_val Hstk Hts")
      as "(Hlocal & #Hstk4v & _ & _)"; [done| | | | |].
    { rewrite /callee_stk_bounds; stk_unfold;
        split_and!; solve_addr+Hastk Hastk_bounds Hastk_bstk. }
    { (* The callee's stack is in the thread's stack *)
      split; [rewrite -Hbase; solve_addr | stk_unfold; solve_addr]. }
    { eapply switcher_disjoint_subseg; [reflexivity| |split; eassumption].
      stk_unfold; solve_addr+Hastk Hastk_bounds. }
    { eapply switcher_disjoint_subseg; [reflexivity| |split; eassumption].
      stk_unfold; solve_addr+Hastk Hastk_bounds. }
    iAssert (world_resources W' C) with "[Hlocal Hperm]" as "Hworld_interp".
    { rewrite world_resources_split. iFrame "Hlocal Hperm". }
    iMod (trusted_stack_inv_opened_push frame cstk with
           "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk [Hcells]")
      as "[Hna Hcstk]";
      [done|done|done|done|done|done|by intros _|by left| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
    iDestruct (switcher_cc_cont_frame W C with "Hpost Hlc Hcont Hstk4v") as "Hcont_frame";
      [done|done|done|done|].
    iModIntro.
    iFrame "Hregs Hworld_interp Hcont_frame Hhwm Hna Hcstk".
    iExists InterruptDisabled; iFrame "Hmie Hheld"; done.
  Qed.

  (** The callee's stack is smaller than the minimum stack size of the
      entry plus the reserved space: the frame is pushed, and the switcher
      returns to the caller's continuation. MSHWM is [mshwm_v]. *)
  #[local] Lemma switcher_cc_stack_too_small
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (cstk' : CSTK) (a_tstk : Addr) (tstk_next : list LWord)
    (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr) (nargs : nat) (mshwm_v : Z) :
    let W' := std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary in
    let frame := switcher_cc_frame wcgp_caller wcra_caller wcs0_caller wcs1_caller
                   b_stk e_stk a_stk (Cap RO g_tbl b_tbl e_tbl a_tbl) in
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_next := (a_tstk ^+ TrustedStackFrame_size) in
    let a_free := (a_next ^+ TrustedStackFrame_size) in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp) in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable) in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount) in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->
    (b_trusted_stack + tstack_frame_offset (S (length cstk'.(cstk_frames))))%a = Some a_next ->
    (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    tf_export_tbl_ok (cf_tframe frame) ->

    thread_in th C -∗
    switcher_trap_safety -∗
    trusted_stack_inv_opened cstk' a_tstk -∗
    world_resources W' C -∗
    ◯(CSTK)[th] cstk -∗
    hwm_res (cstack_push frame cstk) mshwm_v -∗
    interp_continuation (cstack_push frame cstk) (W' :: Ws) (C :: Cs) -∗
    switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller -∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack -∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S (length cstk'.(cstk_frames)))) -∗
    switcher_hazard -∗
    a_csp ↦ₐ Cap RWL Local b_stk e_stk (stk_saved_a a_stk) -∗
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
      csp ↦ᵣ[th] Cap RWL Local (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)
               (stk_saved_a a_stk) ∗
      a_export_table ↦ₐ Cap RO g_tbl b_tbl e_tbl a_tbl ∗
      ( [∗ map] r↦w ∈ arg_rmap,
          r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
      regs[th] delete ctp (delete ct2 rmap) ∗
      MIE ↦ₜ[th] InterruptDisabled ∗
      held (th := th) InterruptDisabled -∗
      safe[th] ).
  Proof.
    intros W' frame a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hstk_mmio Hstk_heap Hstk_bounds Hdom Hrdom Hret_jalr Hret_heap Ha_next Ha_next_e
               Htbl_cell)
      "#Hthread #Hsafety Hopened Hworld_interp Hcstk Hhwm Hcont_frame Hcells Hmtdc Hframeoffset
       Hhazard Hframe_csp Hframe_cnt Htstk
       (HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wct1' Hct1] & [%wct2' Hct2] & [%wctp' Hctp]
       & [%wcgp' Hcgp] & [%wcra' Hcra] & Hcsp & Hframe_tbl & Hargs & Hregs & Hmie & Hheld)".
    iMod (trusted_stack_inv_opened_push frame cstk with
           "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk [Hcells]")
      as "[Hna Hcstk]";
      [done|done|done|done|done|done|by intros _|right; split; [done | exact Htbl_cell]| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
    iDestruct (big_sepM_sep with "Hargs") as "[Hargs _]".
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iDestruct (switcher_cc_full_regs with "Hrmap0 Hcra Hcgp Hcsp Hcs0 Hcs1 Hca0 Hca1")
      as (regs) "[%Hfull_regs Hregs]"; first done.
    iApply (switcher_call_stack_too_small_unwind_of_safety W' C (cstack_push frame cstk)
              (W' :: Ws) (C :: Cs) regs mshwm_v);
      [done|simpl; split; [apply related_sts_pub_refl_world|done]|].
    iFrame "HPC Hregs Hthread Hsafety Hworld_interp Hcont_frame Hhwm Hna Hcstk Hmie Hheld".
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
    (mshwm_v : Z)
    :
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    (* The caller's stack starts at the base of the thread's stack, and ends
       in it *)
    b_stk = cstk_hwm_base cstk ->
    (e_stk <= cstk_hwm_top cstk)%a ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (* The thread runs in the caller's compartment *)
    thread_in th C
    (* Trap safety of the switcher, with its invariant *)
    ∗ switcher_trap_safety

    (* PRE-CONDITION *)
    ∗ na_own (tpool th) ⊤
    (* Registers *)
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ[th] wcgp_caller
    ∗ cra ↦ᵣ[th] wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ[th] wct1_caller
    ∗ (if is_sealed_with_o wct1_caller.(lw) ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ sb nargs,
              ⌜wct1_caller.(lw) = WSealed ot_switcher sb⌝ ∗
              sb ↦ₑ□{nargs} nargs ∗
              (* Argument registers, need to be safe-to-share *)
              ( [∗ map] rarg↦warg ∈ arg_rmap,
                  rarg ↦ᵣ[th] warg
                  ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                    then interp W C warg
                    else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ[th] wcs0_caller
    ∗ cs1 ↦ᵣ[th] wcs1_caller
    (* All the other registers *)
    ∗ regs[th] rmap

    (* Stack frame *)
    ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
    (* The high-water-mark registers *)
    ∗ hwm_res cstk mshwm_v

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_resources W C
    ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
    ∗ ⌜ revoked_addresses W (stk_free b_stk e_stk a_stk) ⌝
    ∗ ◯(CSTK)[th] cstk
    ∗ interp_continuation cstk Ws Cs
    (* The switcher's entry disables interrupts *)
    ∗ MIE ↦ₜ[th] InterruptDisabled
    ∗ held (th := th) InterruptDisabled


    ∗ ( ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem_l stk_mem_h : list LWord) rcgp rcra rcs0 rcs1
        (m : InterruptStatus),
        ( ( (* POST-CONDITION --- the call went through *)
              (* Also the return of ECOMPARTMENTFAIL when [ct1] is not a sealed export entry: the callee's frame is already pushed, so the exception entry pops it *)
              (* Also the return of ENOTENOUGHSTACK when the callee's stack is smaller than its minimum stack size: the return routine pops the frame *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world
                  (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own (tpool th) ⊤
              ∗ interp W2 C (callee_csp b_stk e_stk a_stk)
              ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
              ∗ ⌜ disjoint_from_heap (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) ⌝
              (* The local map, open on the callee's stack region, and the
                 map of Permanent regions *)
              ∗ local_region_map th W2 C
                  (open_l W2 (LNonHeap <$> callee_stk_region b_stk e_stk a_stk))
              ∗ perm_resources C
              ∗ StackOpenWorldResources interp W2 C (callee_stk_region b_stk e_stk a_stk) stk_mem_h
              ∗ ◯(CSTK)[th] cstk
              ∗ ([∗ list] a ∈ callee_stk_region b_stk e_stk a_stk,
                   ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
              ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ[th] rcgp ∗ cra ↦ᵣ[th] rcra ∗ cs0 ↦ᵣ[th] rcs0 ∗ cs1 ↦ᵣ[th] rcs1
              ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ[th] warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ[th] warg1 ∗ interp W2 C warg1)
              ∗ regs₀[th] rmap'
              ∗ stack_region (stk_spill_a a_stk) (stk_spill_a a_stk ^+ SpillSlot_size) stk_mem_l
              ∗ stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) stk_mem_h
              (* MSHWM is the caller's stack pointer *)
              ∗ hwm_res cstk a_stk
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧
                load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧
                load_heap wcs1_caller rcs1⌝
              (* The caller resumes at the posture of its return sentry *)
              ∗ ⌜route_pre th (default m (jalr_target_mie rcra.(lw)))⌝
              ∗ MIE ↦ₜ[th] default m (jalr_target_mie rcra.(lw))
              ∗ held (th := th) (default m (jalr_target_mie rcra.(lw)))
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't went through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
              ∗ na_own (tpool th) ⊤
              (* Registers are preserved *)
              ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ[th] rcgp
              ∗ cra ↦ᵣ[th] rcra
              ∗ cs0 ↦ᵣ[th] rcs0
              ∗ cs1 ↦ᵣ[th] rcs1
              ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ[th] WInt 0
              ∗ regs₀[th] rmap'
              (* Stack frame *)
              ∗ [[ stk_spill_a a_stk , stk_spill_a a_stk ^+ SpillSlot_size ]] ↦ₐ
                  [[ [wcs0_caller; wcs1_caller; wcgp_caller; wcra_caller] ]]
              ∗ stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)
                  (stk_mem_callee stk_mem)
              (* MSHWM is unchanged by the spill, or lowered to a spilled cell *)
              ∗ (∃ mshwm_v' : Z, ⌜ (mshwm_v' <= mshwm_v)%Z ⌝ ∗ hwm_res cstk mshwm_v')

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_resources W C
              ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
              ∗ ◯(CSTK)[th] cstk
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧
                load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧
                load_heap wcs1_caller rcs1⌝
              (* The caller resumes at the posture of its return sentry,
                 from the switcher's *)
              ∗ ⌜route_pre th (default InterruptDisabled (jalr_target_mie rcra.(lw)))⌝
              ∗ MIE ↦ₜ[th] default InterruptDisabled (jalr_target_mie rcra.(lw))
              ∗ held (th := th) (default InterruptDisabled (jalr_target_mie rcra.(lw)))
              ∗ £ 2
            )
          )
            -∗ safe[th] )
        ∧
        (* FAULT --- the callee-save registers do not fit on the caller's stack *)
        switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
          b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v )

    ⊢ safe[th].
  Proof.
    (* Outline of the proof:
       - open the trusted-stack invariant ([trusted_stack_inv_open_call]);
       - the cells of the caller's free stack below MSHWM hold integers
         ([wp_stack_region_below_hwm]);
       - [switcher_call_path_spec]: check the stack pointer, whose base is
         MSHWMB, spill the callee-save registers, push the frame, clear the
         callee's stack from MSHWM and unseal the entry point; its fault and
         failure exits close through [switcher_cc_unseal_fault],
         [switcher_cc_spec_tstack_exhausted] and [switcher_cc_spill_fault];
         the zeroing does not fault, since MSHWM is at or above the base of
         the caller's stack;
       - [ot_switcher_entry_prop]: the entry point satisfies the sealing
         predicate of the switcher;
       - the callee's stack holds integers; the cells between MSHWM and the
         callee's stack pointer join the zone, for the raise of MSHWM;
       - [switcher_decode_entry_path_spec]: check the size of the callee's
         stack, raise MSHWM to the callee's stack pointer, load the callee
         and jump to it; when the stack is too small,
         [switcher_cc_stack_too_small], also when the callee's stack ends
         below the reserved space (then no cell of the zone is given);
       - [local_cc_world_reinstate]: reinstate the callee's stack frame;
       - [trusted_stack_inv_opened_push]: push the frame and close the trusted-stack
         invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros (Hstk_mmio Hstk_heap Hb_a Hbase Htop Hdom Hrdom Hret_jalr Hret_heap)
      "(#Hthread & #Hsafety & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hhwm & Hworld_interp & Hstk_val & %Hstk_revoked
    & Hcstk & Hcont & Hmie & Hheld & Hpost)".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[#Hswitcher #Hstatic]".
    iPoseProof "Hstatic" as "(#Hcode & #Hb_switcher & _)".
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hhb_h) #Hts]".
    iDestruct (stack_region_length with "Hstk") as %Hlen.
    assert (is_Some (rmap !! ct2)) as [wct2 Hwct2].
    { apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver]. }
    iDestruct (big_sepM_delete _ _ ct2 with "Hregs") as "[Hct2 Hregs]"; first exact Hwct2.
    assert (is_Some (delete ct2 rmap !! ctp)) as [wctp Hwctp].
    { rewrite lookup_delete_ne //. apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver]. }
    iDestruct (big_sepM_delete _ _ ctp with "Hregs") as "[Hctp Hregs]"; first exact Hwctp.

    (* Open the trusted-stack invariant *)
    iMod (trusted_stack_inv_open_call with "Hswitcher Hna")
      as (a_tstk cstk' tstk_next)
         "(%Huser & %Hlen_cstk & %Ha_tstk_e & Hopened & Hmtdc & Hframeoffset & Hhazard & Htstk)".

    (* The cells of the caller's free stack below MSHWM are cells of the
       zone, which hold integers *)
    iPoseProof (hwm_closed_user th Huser) as "Hcl".
    iApply (wp_stack_region_below_hwm with "Hcl Hstk [$Hmshwmb $Hmshwm]");
      [done | rewrite /stk_free_b -Hbase; solve_addr |].
    iIntros (Hints_free) "_ Hstk Hhwm_regs".

    (* [.Lswitch_csp_check] to [.Lswitcher_decode_entry] *)
    iEval (rewrite -switcher_call_entry_label) in "HPC".
    iApply (switcher_call_path_spec with
      "[- $HPC $Hcsp $Hct2 $Hctp $Hcs0 $Hcs1 $Hcra $Hcgp $Hct1 $Hstk $Hhwm_regs $Hcl $Hmtdc
          $Hframeoffset $Hhazard $Htstk $Hb_switcher $Hcode]");
      [done..| solve_addr | by rewrite Hbase |].
    iNext.
    iPoseProof "Hstatic" as "(_ & _ & _ & Hswitcher_global & _)".
    iNamed "Hswitcher_global". iNamed "Hswitcher_sealing".
    iSplit; [ |iSplit; [ |iSplit; [ |iSplit] ] ]; cycle 1.
    { (* The entry point is not sealed by the switcher: the frame is pushed,
         and the exception entry returns to the caller's continuation *)
      iIntros (g_tstk mshwm_v') "Hfault _".
      iDestruct "Hpost" as "[Hpost _]".
      iApply (switcher_cc_unseal_fault with
               "Hthread Hsafety Hopened Hargs Hregs Hworld_interp Hstk_val Hcstk Hcont Hts Hpost
                Hmie Hheld Hfault"); done. }
    { (* The trusted stack is exhausted *)
      iIntros (g_tstk mshwm_v').
      iDestruct "Hpost" as "[Hpost _]".
      iApply (switcher_cc_spec_tstack_exhausted with
               "Hsafety Hopened Hargs Hregs Hworld_interp Hstk_val Hcstk Hcont Hts Hpost Hmie
                Hheld");
        done. }
    { (* The caller's stack starts at the base of the thread's stack, at or
         below MSHWM: the zeroing of the callee's stack does not fault *)
      iIntros (g_tstk mshwm_v' off) "(%Hstk_bounds & _ & _ & %Hh' & %Hlt & _)"; exfalso.
      pose proof Hstk_bounds as (Hb4 & _ & _). revert Hb4 Hlt. stk_unfold. intros. solve_addr. }
    { (* The callee-save registers do not fit on the caller's stack *)
      iIntros "Hfault_pre _".
      iDestruct "Hpost" as "[_ Hfault]".
      iApply (switcher_cc_spill_fault with
               "Hsafety Hopened Hargs Hregs Hworld_interp Hstk_val Hcstk Hcont Hts Hfault Hmie
                Hheld Hfault_pre");
        done. }
    iDestruct "Hpost" as "[Hpost _]".

    (* The entry point satisfies the sealing predicate of the switcher *)
    iDestruct (ot_switcher_entry_prop with "Hp_ot_switcher Htarget_v") as "Hentry_prop".
    iNext; iIntros (g_tstk wsb π mshwm_v')
      "(-> & %Htag & %Hstk_bounds & %Ha_next & %Ha_next_e & %Hh' & %Hcallee_h' & HPC & Hcs0
      & [%wcs1' Hcs1] & [%wct2' Hct2] & Hctp & Hcsp & Hcra & Hcgp & Hct1 & Hcells & Hstk
      & Hhwm_regs & Hmtdc & Hframeoffset & Hhazard & Hframe_csp & [%wtbl Hframe_tbl] & Hframe_cnt
      & [%tstk_next' Htstk] & Hlc)".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    iDestruct ("Hentry_prop" with "[//] [//]") as "Hentry_ot".
    iNamed "Hentry_ot".
    (* [simplify_eq] would substitute [b_stk] with [Hbase] *)
    revert Hbase. rewrite /lword_of_word in Hw; simplify_eq. intros Hbase.
    iDestruct (switcher_cc_args_entry with "Hargs Htbl_entry") as "Hargs"; first lia.

    (* The callee's stack holds integers *)
    assert (Forall lword_int
              (stack_zeroed_from (stk_callee_b b_stk a_stk) mshwm_v' (stk_mem_callee stk_mem)))
      as Hints_callee.
    { apply (callee_stk_ints b_stk e_stk a_stk mshwm_v mshwm_v'); [done|done|done|].
      destruct Hh' as [-> | Hh'']; [by left | right; lia]. }
    iDestruct (stack_ints_of_region _ _ _ Hints_callee with "Hstk") as "Hstk".

    (* The callee's world, its frame, and its continuation *)
    set (W' := std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary).
    iDestruct (world_resources_split with "Hworld_interp") as "[Hlocal Hperm]".
    iSpecialize ("Hentry_cont" $! th with "Hthread").
    iSpecialize ("Hentry_cont" $! W').
    set (frame := switcher_cc_frame wcgp_caller wcra_caller wcs0_caller wcs1_caller
                    b_stk e_stk a_stk (Cap RO g_tbl b_tbl e_tbl a_tbl)).
    (* The table cell holds the unsealed entry *)
    assert (tf_export_tbl_ok (cf_tframe frame)) as Htbl_cell.
    { apply (tf_export_tbl_cell_entry (cf_tframe frame) g_tbl b_tbl e_tbl a_tbl eq_refl
               Hbtbl_header); [clear -Hatbl; solve_addr | exact Htbl_shadow]. }
    assert (callee_stk_bounds b_stk e_stk a_stk) as Hcallee_bounds.
    { rewrite /callee_stk_bounds; stk_unfold;
        split_and!; solve_addr+Hastk Hastk_bounds Hastk_bstk. }
    assert ((cstk_hwm_base cstk <= b_stk)%a ∧
            (stk_callee_e e_stk a_stk <= cstk_hwm_top cstk)%a) as Hcallee_ts.
    { split; [rewrite -Hbase; solve_addr | stk_unfold; solve_addr]. }
    assert (disjoint_from_mmio (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) ∧
            disjoint_from_heap (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk))
      as [Hfree_mmio Hfree_heap].
    { eapply switcher_disjoint_subseg; [reflexivity| |split; eassumption].
      stk_unfold; solve_addr+Hastk Hastk_bounds. }

    (* MSHWM is at or below the spill area, which is full points-to *)
    iDestruct "Hcells" as "(Hc0 & Hc1 & Hc2 & Hc3)".
    iDestruct "Hhwm_regs" as "[Hmshwmb Hmshwm]".
    iApply (wp_hwm_pointsto_outside with "Hcl Hc0 Hmshwmb Hmshwm"); first done.
    iIntros (Hout) "_ Hc0 Hmshwmb Hmshwm".
    iAssert (switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller)
      with "[$Hc0 $Hc1 $Hc2 $Hc3]" as "Hcells".
    assert (mshwm_v' <= stk_spill_a a_stk)%Z as Hh'_spill.
    { clear -Hout Hastk_bstk Hbase. solve_addr. }
    (* The cells between MSHWM and the callee's stack pointer join the zone,
       for the raise of MSHWM *)
    set (lo := (cstk_hwm_base cstk ^+ (mshwm_v' - cstk_hwm_base cstk))%a).
    assert (lo = mshwm_v' :> Z) as Hlo.
    { subst lo. clear -Hcallee_h' Hh'_spill Hastk_bstk Hbase. stk_unfold. solve_addr. }

    destruct (decide (StackEntry_reserved_space <= stk_callee_e e_stk a_stk)%Z)
      as [Hnowrap | Hwrap]; cycle 1.
    { (* The callee's stack ends below the space reserved at its top: it is
         too small, and the decoding takes no cell of the zone *)
      iApply (switcher_decode_entry_path_spec W C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo
        with "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra
            $Hcsp $Hmshwmb $Hmshwm $Hargs $Hregs $Hcode $Hmie $Hheld]");
        [done|clear -Hbtbl_header; solve_addr|done|clear -Hnargs; lia|clear -Hminstk; lia
        |done|done|done|done| | | |done|done| |intros ?; congruence| |].
      { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
        reflexivity. }
      { clear -Ha_next; tstack_unfold; solve_addr. }
      { clear -Ha_next Ha_next_e; tstack_unfold; solve_addr. }
      { rewrite !dom_delete_L Hdom. set_solver. }
      { rewrite -Hlo Z.max_r; first reflexivity.
        clear -Hlo Hbase Hcallee_h'. stk_unfold. solve_addr. }
      iSplitR.
      { iLeft. iPureIntro. clear -Hwrap. stk_unfold. solve_addr. }
      iNext; iSplit.
      { iIntros (arg_rmap_s rmap_s) "(%Hbig & _)". exfalso. clear -Hbig Hwrap. stk_unfold.
        rewrite /StackEntry_reserved_space in Hbig Hwrap. solve_addr. }
      iIntros "(_ & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcgp & Hcra & Hcsp
               & [Hmshwmb Hmshwm] & _ & Hframe_tbl & Hargs & Hregs & Hmie & Hheld)".
      iMod (local_cc_world_reinstate _ W C b_stk e_stk a_stk
              (cstk_hwm_base cstk) (cstk_hwm_top cstk) with "Hlocal Hstk_val Hstk Hts")
        as "(Hlocal & #Hstk4v & _ & _)"; [done|done|done|done|done|].
      iAssert (world_resources W' C) with "[Hlocal Hperm]" as "Hworld_interp".
      { rewrite world_resources_split. iFrame "Hlocal Hperm". }
      iDestruct (switcher_cc_cont_frame W C _ _ _ _ _ _ _ _ _ _ _ _
                   (Cap RO g_tbl b_tbl e_tbl a_tbl) with "Hpost Hlc Hcont Hstk4v")
        as "Hcont_frame"; [done|done|done|done|].
      fold frame.
      iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm".
      { destruct Hh' as [-> | Hh'']; solve_addr. }
      iEval (rewrite -(hwm_res_push frame cstk mshwm_v')) in "Hhwm".
      iApply (switcher_cc_stack_too_small with
               "Hthread Hsafety Hopened Hworld_interp Hcstk Hhwm Hcont_frame Hcells Hmtdc
                Hframeoffset Hhazard Hframe_csp Hframe_cnt Htstk
                [$HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcgp $Hcra $Hcsp $Hframe_tbl $Hargs $Hregs
                 $Hmie $Hheld]");
        done. }

    iMod (stack_region_zeroes_zone_acc _ _ lo
            (stk_callee_e e_stk a_stk ^+ (- StackEntry_reserved_space))%a with "Hstk")
      as "[Hzone Hzone_close]".
    { clear -Hlo Hcallee_h'. stk_unfold. solve_addr. }
    { intros _. clear -Hnowrap. stk_unfold. solve_addr. }

    (* [.Lswitcher_decode_entry]: load the callee and jump to it *)
    iApply (switcher_decode_entry_path_spec W C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra $Hcsp
          $Hmshwmb $Hmshwm $Hargs $Hregs $Hcode $Hmie $Hheld]");
      [done|clear -Hbtbl_header; solve_addr|done|clear -Hnargs; lia|clear -Hminstk; lia
      |done|done|done|done| | | |done|done| |intros ?; congruence| |].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { clear -Ha_next; tstack_unfold; solve_addr. }
    { clear -Ha_next Ha_next_e; tstack_unfold; solve_addr. }
    { rewrite !dom_delete_L Hdom. set_solver. }
    { rewrite Hlo Z.max_r; first done. clear -Hbase Hcallee_h'. stk_unfold. solve_addr. }
    iSplitL "Hzone".
    { iRight. iExact "Hzone". }
    iNext; iSplit; cycle 1.
    { (* The callee's stack is too small *)
      iIntros "(_ & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcgp & Hcra & Hcsp
               & [Hmshwmb Hmshwm] & Hzone & Hframe_tbl & Hargs & Hregs & Hmie & Hheld)".
      iDestruct "Hzone" as "[%Hsmall_e | Hzone]".
      { exfalso. clear -Hsmall_e Hnowrap. lia. }
      iDestruct ("Hzone_close" with "Hzone") as "Hstk".
      iMod (local_cc_world_reinstate _ W C b_stk e_stk a_stk
              (cstk_hwm_base cstk) (cstk_hwm_top cstk) with "Hlocal Hstk_val Hstk Hts")
        as "(Hlocal & #Hstk4v & _ & _)"; [done|done|done|done|done|].
      iAssert (world_resources W' C) with "[Hlocal Hperm]" as "Hworld_interp".
      { rewrite world_resources_split. iFrame "Hlocal Hperm". }
      iDestruct (switcher_cc_cont_frame W C _ _ _ _ _ _ _ _ _ _ _ _
                   (Cap RO g_tbl b_tbl e_tbl a_tbl) with "Hpost Hlc Hcont Hstk4v")
        as "Hcont_frame"; [done|done|done|done|].
      fold frame.
      iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm".
      { destruct Hh' as [-> | Hh'']; solve_addr. }
      iEval (rewrite -(hwm_res_push frame cstk mshwm_v')) in "Hhwm".
      iApply (switcher_cc_stack_too_small with
               "Hthread Hsafety Hopened Hworld_interp Hcstk Hhwm Hcont_frame Hcells Hmtdc
                Hframeoffset Hhazard Hframe_csp Hframe_cnt Htstk
                [$HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcgp $Hcra $Hcsp $Hframe_tbl $Hargs $Hregs
                 $Hmie $Hheld]");
        done. }
    iIntros (arg_rmap' rmap')
      "(%Hbig & %Harg_rmap' & %Hrmap' & HPC & Hcgp & Hcra & Hcsp & [Hmshwmb Hmshwm] & Hzone
      & Hframe_tbl & Hargs & Hregs & Hmie & Hheld & Hlc_cred)".
    iDestruct ("Hzone_close" with "Hzone") as "Hstk".

    (* Reinstate the callee's stack frame in the world *)
    iMod (local_cc_world_reinstate _ W C b_stk e_stk a_stk
            (cstk_hwm_base cstk) (cstk_hwm_top cstk) with "Hlocal Hstk_val Hstk Hts")
      as "(Hlocal & #Hstk4v & %Hrelated & %Hrev)"; [done|done|done|done|done|].
    iAssert (world_resources W' C) with "[Hlocal Hperm]" as "Hworld_interp".
    { rewrite world_resources_split. iFrame "Hlocal Hperm". }
    iDestruct (switcher_cc_cont_frame W C _ _ _ _ _ _ _ _ _ _ _ _
                 (Cap RO g_tbl b_tbl e_tbl a_tbl) with "Hpost Hlc Hcont Hstk4v")
      as "Hcont_frame"; [done|done|done|done|].
    fold frame.

    (* Push the frame and close the trusted-stack invariant *)
    iMod (trusted_stack_inv_opened_push frame cstk with
           "Hopened Hcstk Hmtdc Hframeoffset Hhazard Hframe_csp Hframe_tbl Hframe_cnt Htstk [Hcells]")
      as "[Hna Hcstk]";
      [done|done|done|done|done|done|by intros _|right; split; [done | exact Htbl_cell]| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }

    (* MSHWM is the callee's stack pointer *)
    iDestruct (hwm_res_of_regs with "Hts [$Hmshwmb $Hmshwm]") as "Hhwm".
    { clear -Hbase Hbig. stk_unfold. solve_addr. }
    iEval (rewrite -(hwm_res_push frame cstk)) in "Hhwm".
    (* The stack addresses between the base of the thread's stack and the
       callee's stack pointer are Temporary in the callee's world *)
    assert (zone_temporary W' (cstk_hwm_base (cstack_push frame cstk))
              (stk_callee_e e_stk a_stk ^+ (- StackEntry_reserved_space))%a) as Hzone_callee.
    { rewrite cstk_hwm_base_push -Hbase.
      intros a' Ha'1 Ha'2.
      apply std_sta_update_multiple_lookup_in_i, elem_of_finz_seq_between.
      clear -Ha'1 Ha'2 Hnowrap. stk_unfold. solve_addr. }

    (* Execute the entry point of the callee *)
    iDestruct (switcher_call_entry_registers W W' C nargs arg_rmap' rmap' with
                "[$Hcgp $Hcra $Hcsp $Hstk4v $Hargs $Hregs]")
      as (regs) "[Hregs Hregs_interp]"; [done|done|done|].
    iPoseProof (switcher_untrusted_vec_safe_of_safety with "Hsafety") as "#Htv".
    iDestruct (shared_credit_refill C with "Hlc_cred") as "Hcred".
    iApply ("Hentry_cont" $! (cstack_push frame cstk) (W' :: Ws) (C :: Cs) regs
              (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)).
    iSplitR; first iExact "Hthread".
    iSplitR; first iExact "Htv".
    iSplitL "Hcont_frame"; first iExact "Hcont_frame".
    iSplit.
    { iPureIntro; simpl; split; [|split]; auto.
      apply related_sts_pub_refl_world. }
    iSplit; first (iPureIntro; split_and!; [done | reflexivity | reflexivity | exact Htbl_cell]).
    iFrame "HPC Hregs Hregs_interp Hhwm Hworld_interp Hcred Hcstk Hna Hmie Hheld".
    iSplit; first (iPureIntro; exact Hzone_callee).
    iSplit.
    { iPureIntro.
      cbn. rewrite (tf_caller_a_saved _ true RWL Local b_stk e_stk a_stk); [by split | done | done]. }
    iSplit; first (iPureIntro; exact Hbase).
    iSplit; [iPureIntro; exact Hbig | iPureIntro; intros ?; congruence].
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
    (mshwm_v : Z)
    :
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    (* The caller's stack starts at the base of the thread's stack, and ends
       in it *)
    b_stk = cstk_hwm_base cstk ->
    (e_stk <= cstk_hwm_top cstk)%a ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (* The thread runs in the caller's compartment *)
    thread_in th C
    (* Trap safety of the switcher, with its invariant *)
    ∗ switcher_trap_safety

    (* PRE-CONDITION *)
    ∗ na_own (tpool th) ⊤
    (* Registers *)
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ[th] wcgp_caller
    ∗ cra ↦ᵣ[th] wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ[th] wct1_caller
    ∗ (if is_sealed_with_o wct1_caller.(lw) ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ sb nargs,
              ⌜wct1_caller.(lw) = WSealed ot_switcher sb⌝ ∗
              sb ↦ₑ□{nargs} nargs ∗
              (* Argument registers, need to be safe-to-share *)
              ( [∗ map] rarg↦warg ∈ arg_rmap,
                  rarg ↦ᵣ[th] warg
                  ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                    then interp W C warg
                    else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ[th] wcs0_caller
    ∗ cs1 ↦ᵣ[th] wcs1_caller
    (* All the other registers *)
    ∗ regs[th] rmap

    (* Stack frame *)
    ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
    (* The high-water-mark registers *)
    ∗ hwm_res cstk mshwm_v

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_resources W C
    ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
    ∗ ⌜ revoked_addresses W (stk_free b_stk e_stk a_stk) ⌝
    ∗ ◯(CSTK)[th] cstk
    ∗ interp_continuation cstk Ws Cs
    (* The switcher's entry disables interrupts *)
    ∗ MIE ↦ₜ[th] InterruptDisabled
    ∗ held (th := th) InterruptDisabled


    (* POST-CONDITION *)
    ∗ ( ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem : list LWord) l' rcgp rcra rcs0 rcs1
              (m : InterruptStatus),
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
            ∗ na_own (tpool th) ⊤
            ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
            (* Interpretation of the world *)
            ∗ world_resources (revoke W2) C
            ∗ ◯(CSTK)[th] cstk
            ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ[th] rcgp
            ∗ cra ↦ᵣ[th] rcra
            ∗ cs0 ↦ᵣ[th] rcs0
            ∗ cs1 ↦ᵣ[th] rcs1
            ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ[th] warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ[th] warg1 ∗ interp W2 C warg1)
            ∗ regs₀[th] rmap'
            ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
            (* MSHWM is the caller's stack pointer when the call went
               through, and at most its value at the call otherwise *)
            ∗ (∃ mshwm_v' : Z, ⌜ (mshwm_v' <= Z.max mshwm_v a_stk)%Z ⌝ ∗ hwm_res cstk mshwm_v')
            ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧
                load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧
                load_heap wcs1_caller rcs1⌝
            (* The caller resumes at the posture of its return sentry *)
            ∗ ⌜route_pre th (default m (jalr_target_mie rcra.(lw)))⌝
            ∗ MIE ↦ₜ[th] default m (jalr_target_mie rcra.(lw))
            ∗ held (th := th) (default m (jalr_target_mie rcra.(lw)))
              -∗ safe[th])
        ∧
        (* FAULT --- the callee-save registers do not fit on the caller's stack *)
        switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
          b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v )


    ⊢ safe[th].
  Proof.
    (* Outline of the proof: apply [switcher_cc_specification_gen], then
       revoke the world in the post-condition, with
       [local_cc_revoke_returned] when the callee returned, and with
       [local_cc_revoke_exhausted] when the trusted stack was exhausted. *)
    iIntros (Hstk_mmio Hstk_heap Hb_a Hbase Htop Hdom Hrdom Hret_jalr Hret_heap)
      "(#Hthread & #Hsafety & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hhwm & Hworld_interp & #Hstk_val & %Hrevoked_stk
    & Hcstk & Hcont & Hmie & Hheld & Hpost)".
    iApply (switcher_cc_specification_gen with
             "[$Hthread $Hsafety $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Htarget_v $Hargs $Hcs0 $Hcs1 $Hregs $Hstk
               $Hhwm $Hworld_interp $Hstk_val $Hcstk $Hcont $Hmie $Hheld Hpost]"); [done..|].
    iSplit; first done.
    iSplit; last by iDestruct "Hpost" as "[_ $]".
    iDestruct "Hpost" as "[Hpost _]".
    iIntros (W' rmap' stk_mem_l stk_mem_h rcgp rcra rcs0 rcs1 m).
    iNext; iIntros "[H|H]".
    + iDestruct "H" as
        "(%Hrelated_pub_Wext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds & %Hstack_heap
      & Hlocal_C & Hperm_C & Hstack_revoked_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & Hca0 & Hca1 & Hrmap & Hstk_l & Hstk_h & Hhwm & HK & %Hrestored & %Hpre_ret & Hmie & Hheld
      & Hlc)".
      iMod (local_cc_revoke_returned with
             "Hinterp_W2_csp Hstk_val Hlocal_C Hstack_revoked_W2 Hstk_l Hstk_h Hlc")
        as (stk_mem' l') "(%Htemp & Hrevoked_l' & %Hrev_l' & Hstk_revoked & %Hrev_stk
                           & Hlocal_C & Hstk)";
        [done|done|naive_solver|].
      iAssert (world_resources (revoke W') C) with "[Hlocal_C Hperm_C]" as "Hworld_interp".
      { rewrite world_resources_split. iFrame "Hlocal_C Hperm_C". }
      iAssert (∃ mshwm_v' : Z, ⌜ (mshwm_v' <= Z.max mshwm_v a_stk)%Z ⌝ ∗ hwm_res cstk mshwm_v')%I
        with "[Hhwm]" as "Hhwm".
      { iExists a_stk. iFrame "Hhwm". iPureIntro; lia. }
      iApply ("Hpost" $! W' rmap' stk_mem' l' rcgp rcra rcs0 rcs1 m).
      iFrame "Hrevoked_l' Hrel_stk_C Hstk_revoked Hna Hworld_interp Hcstk_frag HPC Hcgp Hcra
        Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hstk Hhwm HK Hmie Hheld".
      iPureIntro.
      exact (conj Htemp (conj Hrev_l' (conj Hrelated_pub_Wext_W2 (conj Hdom_rmap
               (conj Hrev_stk (conj Hcsp_bounds (conj Hrestored Hpre_ret))))))).
    + iDestruct "H" as
        "( %Hdom_rmap & %Hcsp_bounds
           & Hna
           & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
           & Hrmap & Hstk_l & Hstk_h & (%mshwm_v' & %Hh' & Hhwm)
           & Hworld_interp_C & _
           & Hcstk_frag & HK & %Hrestored & %Hpre_ret & Hmie & Hheld & Hlc)".
      iDestruct (stack_region_of_pointsto with "Hstk_l") as "Hstk_l".
      iDestruct (world_resources_split with "Hworld_interp_C") as "[Hlocal_C Hperm_C]".
      iMod (local_cc_revoke_exhausted with "Hlocal_C Hstk_val Hstk_l Hstk_h Hlc")
        as (l') "(%Htemp & Hrevoked_l & %Hrev_l & %Hstd & Htemp_W & Hstk_revoked & %Hrev_stk
                  & Hlocal_C & Hstk)";
        [done|naive_solver|done|].
      iAssert (world_resources
                 (revoke (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary)) C)
        with "[Hlocal_C Hperm_C]" as "Hworld_interp".
      { rewrite world_resources_split. iFrame "Hlocal_C Hperm_C". }
      iAssert (∃ mshwm_v'' : Z, ⌜ (mshwm_v'' <= Z.max mshwm_v a_stk)%Z ⌝ ∗ hwm_res cstk mshwm_v'')%I
        with "[Hhwm]" as "Hhwm".
      { iExists mshwm_v'. iFrame "Hhwm". iPureIntro; lia. }
      iApply ("Hpost" $! _ rmap' _ l' rcgp rcra rcs0 rcs1 InterruptDisabled).
      iFrame "Hrevoked_l Htemp_W Hstk_revoked Hna Hworld_interp Hcstk_frag HPC Hcgp Hcra Hcs0
        Hcs1 Hcsp Hrmap Hstk Hhwm HK Hmie Hheld".
      do 6 (iSplit; first done).
      iSplitL "Hca0"; first (iExists _; iFrame "Hca0"; iApply interp_int).
      iSplitL "Hca1"; first (iExists _; iFrame "Hca1"; iApply interp_int).
      iPureIntro.
      destruct Hrestored as (Hgp & Hra & Hs0 & Hs1).
      by repeat split.
  Qed.

End Switcher.
