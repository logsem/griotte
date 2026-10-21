From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import switcher_spec_call switcher_spec_return switcher_exception_stub.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import stack_object_spec_states
  stack_object_spec_world_object stack_object_spec_world_call
  stack_object_spec_world_return
  stack_object_spec_check_blocks_1 stack_object_spec_checkints_blocks_2
  stack_object_spec_call_blocks_3 stack_object_spec_return_blocks_4.

Section SO.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  (** Steps of the proofs:
      - 1) Revoke the world, obtain [l] the unknown addresses being revoked.
      - 2) Check that the passed stack object [wca0] has read permission,
         and that it does not overlap with our stack frame.
      - 3) Knowing that [wca0] is a safe capability with read permission,
         we know that all addresses must be in the world,
         either Temporary or Permanent.
      - 4) Filter [l] to separate the addresses of [wca0]'s region
         that are Temporary, and the others.
         We know that they are in [l] because if Temporary
         they must either be in [l] or in our stack frame.
         That way, we can get the points-to predicates for
         the Temporary addresses of [wca0].
      - 5) Open the world and get the points-to predicates
         of the Permanent addresses of [wca0].
      - 6) We know have all the points-to predicate of [wca0]'s region,
         we can apply [checkints_spec].
      - 7) We can close the world with the Permanent addresses,
         and we can re-introduce the Temporary ones (via [close_list]).
         They respect their associated validity predicate because [wca0] is interp,
         so their associated predicate must be [zcond],
         and they contain integers.
      - 8) Allocate a new stack object [a_stk1] from our stack frame,
         update the world with its address.
      - 9) Show the arguments to be safe.
         The passed SO is safe because it was safe in the initial world,
         and we re-introduced the Temporary addresses
         (which had been revoked in the initial revocation)
         manually.
         The allocated SO [a_stk1] is safe because we updated the world accordingly.
      - 10) Call the adversary. We obtain a new public future world that is revoked.
          The unknown addresses are [l''].
      - 11) We know that [a_stk1] is in [l'']
          and that the Temporary addresses of `wca0` also are in [l''].
      - 12) We fix the world by closing the world with [l] and [l''],
          but some addresses are redundant.
          It's mostly a game of filtering the addresses.
      - 13) Note that the addresses of [l] are revoked in the initial world,
          but the ones of [l''] are revoked in the final world.
          That's why we need the generalised version of the switcher's return specification.
   *)

  Lemma stack_object_f_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_so_exp_tbl e_so_exp_tbl : Addr)
    (g_so_exp_tbl : Locality)

    (C_f : Sealable)

    (W : WORLD)

    (Nswitcher : namespace)

    :

    let imports := so_main_imports C_f in
    let a_so_exp_tbl_cgp := (b_so_exp_tbl ^+ ExportTable_offset_cgp)%a in
    let a_so_entry_f := (b_so_exp_tbl ^+ ExportTable_offset_entry so_entry_f)%a in

    disjoint_from_shadow pc_b pc_e ->
    disjoint_from_shadow b_so_exp_tbl e_so_exp_tbl ->
    is_heap_address pc_b = false ->
    is_heap_address cgp_b = false ->
    (b_so_exp_tbl <= a_so_entry_f < e_so_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ->
    (pc_b + so_label ".Lso_run")%a = Some pc_a ->
    (cgp_b + length so_main_data)%a = Some cgp_e ->
    is_Some (pc_b + length (imports ++ SO_main_code_run))%a ->

    assert_static b_assert e_assert a_flag
    ∗ na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static
    ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
    ∗ codefrag_pers pc_a so_main_code
    ∗ b_so_exp_tbl ↦ₐ□ WCap true RX Global pc_b pc_e pc_b
    ∗ a_so_exp_tbl_cgp ↦ₐ□ WCap true RW Global cgp_b cgp_e cgp_b
    ∗ no_handler b_so_exp_tbl
    ∗ a_so_entry_f ↦ₐ□ WInt (encode_entry_point InterruptEnabled 2 6 (length (imports ++ SO_main_code_run)))
    ∗ seal_pred ot_switcher ot_switcher_propC
      -∗
    ot_switcher_prop W C (WCap true RO g_so_exp_tbl b_so_exp_tbl e_so_exp_tbl a_so_entry_f).
  Proof.
    (* Outline of the proof:
       - unfold [ot_switcher_prop] and introduce the state of the machine at
         the entry point of [f];
       - [so_check_blocks_1_spec]: blocks 3-5, save the callback [g], check
         that [in] is readable and does not overlap with the stack frame;
       - [so_world_open_object]: revoke the world and open the region of
         [in];
       - [so_checkints_blocks_2_spec]: block 6, [in] only contains integers;
       - close the region of [in], with the closing part of
         [so_world_open_object];
       - [so_world_quarantine]: close the quarantined revoked keys;
       - [so_call_blocks_3_spec]: blocks 7-9, push the secret, allocate the
         stack object [z], and jump to the switcher;
       - [so_world_call]: reinstate [z] in the world of the call;
       - [so_call_args] and [switcher_cc_specification_alt]: call to [g];
       - [so_return_blocks_4_spec]: blocks 10-12, assert that the secret is
         unchanged, and return;
       - [so_world_return]: repair the world;
       - [switcher_ret_specification]: return to the caller of [f].
       A fault before the revocation unwinds [f] ([trap_safe_unwind]). A
       fault after it returns to the caller of [f] through the switcher:
       [checkints] puts [in] back unchanged (second closing of
       [so_world_open_object]). The stack of [f] holds its minimum stack
       size, so neither block 7 nor the spill of the call to [g] faults. *)
    intros imports a_so_exp_tbl_cgp a_so_entry_f.
    subst imports a_so_exp_tbl_cgp a_so_entry_f.
    iIntros (Hpc_shadow Hexports_shadow Hpc_nonheap Hcgp_nonheap
               Hso_exp_tbl_size Hso_size_code Hso_imports Hcgp_size Hentry_some)
      "(#Hassert & #Hswitcher & #Hswitcher_static
      & #Himports_main & #Hcode_main
      & #Hso_exp_PCC
      & #Hso_exp_CGP
      & [#Hso_exp_eh #Hso_exp_ehs]
      & #Hso_exp_awkward
      & #Hot_switcher)".
    iExists g_so_exp_tbl, b_so_exp_tbl, e_so_exp_tbl,
      (b_so_exp_tbl ^+ ExportTable_offset_entry so_entry_f)%a,
    pc_b, pc_e, cgp_b, cgp_e, 2, 6, _.
    iFrame "#".
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iSplit; first (iPureIntro; lia).
    iSplit; first done.
    iSplit; first (iPureIntro; eapply disjoint_from_shadow_not_in;
      [exact Hexports_shadow | apply withinBounds_true_iff; solve_addr]).
    iSplit; first (iPureIntro; eapply disjoint_from_shadow_not_in;
      [exact Hexports_shadow | apply withinBounds_true_iff; solve_addr]).
    iSplit; first (iPureIntro; eapply disjoint_from_shadow_not_in;
      [exact Hexports_shadow | apply withinBounds_true_iff; solve_addr]).
    iSplit; first done.
    iSplit; first done.
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & HPC & Hregister_state & Hrmap & Hworld_interp_C & %Hsync_csp & %Hstk_min & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %Hcgp & [%mie_ret %Hcra] & %Hcsp & #Hinterp_W0_csp & #Hinterp_rmap & #Hzeroed_rmap)".
    rewrite /interp_conf /registers_pointsto.
    assert (so_code_bounds pc_b pc_e pc_a C_f) as Hbounds
      by (rewrite /so_code_bounds; eauto 10).
    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_mmio Hstk_heap]; first done.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    iDestruct (so_args_zero with "Hzeroed_rmap") as %Hzero; first done.
    pose proof (lregmap_full_dom _ Hrmap_init) as Hrmap_dom.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    destruct (Hrmap_init ca0) as [wca0 Hwca0].
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    destruct (Hrmap_init ca1) as [wca1 Hwca1].
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    iExtractList "Hrmap" [ct0;ct1;cs0;cs1] as ["Hct0";"Hct1";"Hcs0";"Hcs1"].
    iAssert (interp W0 C wca0) as "#Hinterp_wca0".
    { iApply "Hinterp_rmap"; eauto. cbn; set_solver+. }
    iAssert (interp W0 C wca1) as "#Hinterp_wca1".
    { iApply "Hinterp_rmap"; eauto. cbn; set_solver+. }
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".

    (* Blocks 3-5: save the callback, check [in] *)
    iEval (rewrite (_ : (pc_b ^+ length (so_main_imports C_f ++ SO_main_code_run))%a =
                        (pc_a ^+ so_label_offset ".Lso_f")%a);
           [|rewrite length_app; offsets_compute; cbn in Hso_imports |- *; solve_addr]) in "HPC".
    iApply (so_check_blocks_1_spec with
             "[- $HPC $Hca0 $Hca1 $Hct1 $Hcs0 $Hcs1 $Hcsp $Hcode_main]"); first done.
    iSplit; cycle 1.
    { (* The checks of [in] fail: [f] is unwound *)
      iIntros (a_f Ha_f) "(Hca0 & Hca1 & Hct1 & [%wcs0' Hcs0] & [%wcs1' Hcs1] & Hcsp)".
      iInsertRegs "Hrmap" ["Hcs1";"Hcs0";"Hct1";"Hct0";"Hca1";"Hca0";"Hcra";"Hcsp";"Hcgp"].
      iApply (trap_safe_unwind W0 C Nswitcher cstk Ws Cs with "Hswitcher Hswitcher_static [-]");
        last (iModIntro; iFrame).
      { intros r; apply elem_of_dom.
        rewrite !dom_insert_L !dom_delete_L Hrmap_dom.
        pose proof (all_registers_s_correct r) as Hall.
        set_solver+ Hall. }
      { exact Hframe_match. } }
    iNext; iIntros (t p g b e a π)
      "(%Hp & -> & %Hno_overlap & HPC & Hca0 & Hca1 & Hct1 & Hcs0 & Hcs1 & Hcsp
      & _ & Hlc)".
    destruct (decide (t = true ∨ (e <= b)%a)) as [Htag_or_empty | Hbad]; cycle 1.
    { (* Block 6 fails on an untagged, non-empty object *)
      destruct t; first (exfalso; apply Hbad; auto).
      iApply (so_checkints_blocks_2_untagged_spec with
               "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode_main]"); [done|solve_addr|].
      iIntros "(Hca0 & [%wcs0' Hcs0] & [%wcs1' Hcs1])".
      iInsertRegs "Hrmap" ["Hcs1";"Hcs0";"Hct1";"Hct0";"Hca1";"Hca0";"Hcra";"Hcsp";"Hcgp"].
      iApply (trap_safe_unwind W0 C Nswitcher cstk Ws Cs with "Hswitcher Hswitcher_static [-]");
        last (iModIntro; iFrame).
      { intros r; apply elem_of_dom.
        rewrite !dom_insert_L !dom_delete_L Hrmap_dom.
        pose proof (all_registers_s_correct r) as Hall.
        set_solver+ Hall. }
      { exact Hframe_match. } }

    iAssert (⌜disjoint_from_shadow b e⌝)%I as "%Hobject_shadow".
    { destruct Htag_or_empty as [-> | Hempty].
      - iDestruct (interp_cap_regions with "Hinterp_wca0") as %[Hshadow _].
        { eapply readAllowed_nonO; exact Hp. }
        iPureIntro. by apply disjoint_from_mmio_shadow.
      - iPureIntro. rewrite /disjoint_from_shadow finz_seq_between_empty;
          [apply disjoint_nil_l | solve_addr].
    }

    (* Revoke the world and open the region of [in] *)
    iMod (so_world_open_object with "Hinterp_W0_csp Hinterp_wca0 Hworld_interp_C Hlc")
      as (l_revoked stk_mem la object_mem)
           "(%Hextract & Hstack_revoked & %Hla & Hobject & Hclose_object)";
      [done|done|done|].

    (* The world fixed by the return path, if [f] faults before it
       reinstates [in] *)
    assert (related_sts_pub_world W0
              (close_list (l_revoked ++ (LNonHeap <$> finz.seq_between (csp_b' ^+ 4)%a csp_e))
                 (revoke W0))) as Hpub_W0_Wrevoked.
    { apply related_pub_revoke_close_list. destruct Hextract as [_ Htemps]; exact Htemps. }

    (* Block 6: [in] only contains integers *)
    iApply (so_checkints_blocks_2_spec with
             "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hobject $Hcode_main]"); [done..|].
    iSplit; cycle 1.
    { (* [checkints] faults: [in] is put back unchanged, and [f] returns to
         its caller through the switcher *)
      iNext; iIntros (a_f Ha_f) "([%a_r Hca0] & [%wcs0' Hcs0] & [%wcs1' Hcs1] & Hobject)".
      iDestruct "Hclose_object" as "[_ Hclose_object]".
      iInsertRegs "Hrmap" ["Hcs1";"Hcs0";"Hct1";"Hct0";"Hcra";"Hcgp"].
      iApply (trap_safe_return _ W0 (revoke W0) C _ csp_e (csp_b' ^+ 4)%a l_revoked stk_mem
                cstk Ws Cs with "Hswitcher Hswitcher_static [-]").
      7: { iMod ("Hclose_object" with "Hobject") as "(Hworld_interp_C & Hrevoked & Hstk)".
           iDestruct (RevokedResources_mono_pub W0 _ C l_revoked [] Hpub_W0_Wrevoked
                       with "Hrevoked") as "Hrevoked".
           iModIntro; iFrame. }
      { exact Hpub_W0_Wrevoked. }
      { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
      { exact Hframe_match. }
      { destruct Hsync_csp as [Hcsp_sync Hcsp_base].
        rewrite -Hcsp_base; exact Hcsp_sync. }
      { destruct Hextract as [Hnodup _]; exact Hnodup. }
      { intros a' Ha'; destruct Hextract as [_ Htemp].
        destruct (Htemp a') as [Hin _]; exact (Hin Ha'). } }
    iNext; iIntros "(%Hints & HPC & Hca0 & Hcs0 & Hcs1 & Hobject & _ & [_ Hlc'])".

    (* Close the region of [in] *)
    iDestruct "Hclose_object" as "[Hclose_object _]".
    iMod ("Hclose_object" with "[$Hobject]")
      as "(Hworld_interp_C & Hrevoked_l_rest & Hstk & #Hinterp_wca0_W2)"; first done.

    (* Close the quarantined revoked keys *)
    iMod (so_world_quarantine W0 _ C with "Hworld_interp_C Hrevoked_l_rest")
      as (l0_live l0_quarantined) "(%Hl0_partition & %Hl0_live & %Hl0_quarantined
                                    & Hworld_interp_C & Hl0_live)".
    { reflexivity. }
    assert (l0_quarantined ## (LNonHeap <$> finz.seq_between (csp_b' ^+ 4)%a csp_e))
      as Hq_stack.
    { rewrite elem_of_disjoint. intros x Hx Hx_stack.
      apply list_elem_of_fmap in Hx_stack as [x' [-> _] ].
      rewrite Forall_forall in Hl0_quarantined.
      specialize (Hl0_quarantined _ Hx). discriminate. }

    (* Blocks 7-9: push the secret, allocate [z], jump to the switcher *)
    iApply (so_call_blocks_3_spec with
             "[- $HPC $Hcsp $Hca1 $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcra $Hstk $Himport_switcher
              $Hcode_main]"); [done|done|done|solve_addr+Hstk_min|].
    iNext; iIntros (mie a_stk1 a_stk2 stk_tail)
      "(%Hastk1 & %Hastk2 & %Hastk2_csp_e & HPC & Hcsp & Hca1 & Hct0 & Hct1 & Hcs0 & Hcs1
      & Hcra & Hsecret & Hastk1 & Hstk & _ & _)".

    (* Reinstate [z] in the world of the call *)
    iMod (so_world_call with
           "Hinterp_W0_csp Hinterp_wca1 Hworld_interp_C Hinterp_wca0_W2 Hstack_revoked
            Hastk1 Hlc'")
      as "(Hworld_interp_C & #Hinterp_wca0_W3 & #Hinterp_z & #Hinterp_wct1
           & Hstack_revoked & %Hrevoked_W3 & %Hpriv_W0_W3 & %Ha_stk1_W3)";
      [done..|].
    iDestruct (so_call_args with "Hswitcher Hswitcher_static Hca0 Hinterp_wca0_W3 Hca1 Hinterp_z Hct0 Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_delete_L Hrmap_dom; set_solver+. }
    { intros r Hr.
      rewrite !lookup_delete_ne; [by apply Hzero|set_solver+Hr..]. }

    (* Call to [g] *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked $Hcstk
              $Hinterp_wct1 $HK]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { solve_addr+ Hastk1 Hastk2. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    iSplit; first done.
    iSplit; cycle 1.
    { (* The spill of the call to [g] cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits; solve_addr+Hstk_min Hastk1 Hastk2. }
    iNext.
    clear dependent arg_rmap rmap' stk_mem.
    iIntros (W4 rmap'' stk_mem l4 rcgp rcra rcs0 callback)
      "(%Hextract4 & Hl4 & %Hl4_W5 & %Hpub_ext & _ & %Hrmap''_dom & _ & %Hstack_W5
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & _).
    apply load_heap_in_world_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=; reflexivity].
    apply load_heap_in_world_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_in_world_nonheap in Hrcs0;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= switcher_base_not_heap /=; reflexivity].
    subst rcgp rcra rcs0.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ca2;cnull]
      as ["Hct0";"Hct1";"Hct2";"Hca2";"Hcnull"].

    (* Blocks 10-12: assert that the secret is unchanged, return *)
    iApply (so_return_blocks_4_spec with
             "[- $Hassert $HPC $Hcsp $Hct0 $Hct1 $Hct2 $Hca2 $Hcra
              $Hcs0 $Hca0 $Hca1 $Hsecret $Himport_assert $Hcode_main]");
      [done|done|solve_addr|solve_addr|exact (jalr_target_ok_switcher_return_sentry mie_ret)|].
    iNext; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hct2 & Hca2 & Hcra
                    & Hcs0 & Hca0 & Hca1 & Hsecret & _ & _)".
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iInsertRegs "Hrmap" ["Hcnull";"Hca2";"Hct2";"Hct1";"Hct0";"Hcs0";"Hcs1";"Hcgp";"Hcra"].

    (* Repair the world *)
    iMod (so_world_return W0 W4 C b e (csp_b' ^+ 4)%a csp_e a_stk1 a_stk2 π
           l_revoked l0_live l0_quarantined l4 with
           "[$Hworld_interp_C $Hl0_live $Hl4 $Hsecret $Hstk]")
      as (w_stk1)
           "(Hworld_interp_C & %Hpub_W0_Wfixed & %Hclosing_nodup & %Hclosing_temps
            & Hclosing & Hstk)";
      [done..|].

    (* Return to the caller of [f] *)
    iApply (switcher_ret_specification _ W0 (revoke W4) with
             "[$Hswitcher $Hswitcher_static $Hstk $Hcstk $HK $Hworld_interp_C $Hna $HPC
              $Hrmap $Hca0 $Hca1 $Hcsp $Hclosing]"); eauto.
    { rewrite !dom_insert_L !dom_delete_L Hrmap''_dom; set_solver+. }
    { destruct Hsync_csp as [Hcsp_sync Hcsp_base].
      rewrite -Hcsp_base; exact Hcsp_sync. }
    { iSplit; iApply interp_int. }
  Qed.

End SO.
