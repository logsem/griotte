From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_base.
From griotte Require Import lse.
From griotte Require Import world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import lse_spec_states lse_spec_world
  lse_spec_f_blocks_1 lse_spec_f_blocks_2.

Section LSE.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
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

  Lemma lse_f_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_lse_exp_tbl e_lse_exp_tbl : Addr)
    (g_lse_exp_tbl : Locality)

    (C_f : Sealable)

    (W : WORLD)

    :

    let imports := lse_main_imports C_f in
    let a_lse_exp_tbl_cgp := (b_lse_exp_tbl ^+ ExportTable_offset_cgp)%a in
    let a_lse_entry_f := (b_lse_exp_tbl ^+ ExportTable_offset_entry lse_entry_f)%a in

    disjoint_from_shadow pc_b pc_e ->
    is_shadow_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    disjoint_from_shadow b_lse_exp_tbl e_lse_exp_tbl ->
    is_heap_address pc_b = false ->
    (b_lse_exp_tbl <= a_lse_entry_f < e_lse_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length lse_main_code)%a ->
    (pc_b + lse_label ".Llse_run")%a = Some pc_a ->
    (cgp_b + length lse_main_data)%a = Some cgp_e ->
    is_Some (pc_b + (length_lse_main_imports + length LSE_main_code_run))%a ->

    assert_static b_assert e_assert a_flag
    ∗ na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static
    ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
    ∗ codefrag_pers pc_a lse_main_code
    ∗ na_inv (tpool th) Nlse (cgp_b ↦ₐ WInt 2)
    ∗ b_lse_exp_tbl ↦ₐ□ WCap true RX Global pc_b pc_e pc_b
    ∗ a_lse_exp_tbl_cgp ↦ₐ□ WCap true RW Global cgp_b cgp_e cgp_b
    ∗ no_handler b_lse_exp_tbl
    ∗ a_lse_entry_f ↦ₐ□ lse_exp_tbl_entry_f
      -∗
    ot_switcher_prop W C (WCap true RO g_lse_exp_tbl b_lse_exp_tbl e_lse_exp_tbl a_lse_entry_f).
  Proof.
    (* Outline of the proof:
       - unfold [ot_switcher_prop] and introduce the state of the machine at
         the entry point of [f];
       - [lse_world_f]: revoke the world, to get the stack frame;
       - [lse_f_blocks_1_spec]: block 4, push the capability of [a] on the
         stack and load [a];
       - [lse_f_blocks_2_spec]: blocks 5-6, assert that [a] contains [2],
         and jump to the switcher;
       - [switcher_ret_specification]: return to the caller of [f]. *)
    intros imports a_lse_exp_tbl_cgp a_lse_entry_f.
    subst imports a_lse_exp_tbl_cgp a_lse_entry_f.
    iIntros (Hpc_shadow Hcgp_shadow Hcgp_nonheap Hexports_shadow Hpc_nonheap
               Hlse_exp_tbl_size Hlse_size_code Hlse_imports Hcgp_size Hentry_some)
      "(#Hassert & #Hswitcher & #Hswitcher_static
      & #Himports_main & #Hcode_main
      & #Hlse_code
      & #Hlse_exp_PCC
      & #Hlse_exp_CGP
      & [#Hlse_exp_eh #Hlse_exp_ehs]
      & #Hlse_exp_f)".
    iExists g_lse_exp_tbl, b_lse_exp_tbl, e_lse_exp_tbl,
      (b_lse_exp_tbl ^+ ExportTable_offset_entry lse_entry_f)%a,
    pc_b, pc_e, cgp_b, cgp_e, 0, 1, _.
    iFrame "#".
    iSplit; first done.
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
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b %csp_e".
    iIntros "(HK & %Hframe_match & _ & HPC & Hregister_state & Hrmap & Hworld_interp_C & %Hsync_csp & %Hstk_min & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %Hcgp & [%mie_ret %Hcra] & %Hcsp & #Hinterp_W0_csp & _ & _)".
    rewrite /interp_conf /registers_pointsto.
    assert (lse_code_bounds pc_b pc_e pc_a C_f) as Hbounds by (rewrite /lse_code_bounds; eauto 10).
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by (cbn in Hcgp_size; solve_addr).
    pose proof (lregmap_full_dom _ Hrmap_init) as Hrmap_dom.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    iExtractList "Hrmap" [ct0;ct1;cs0;cs1;ca0;ca1]
      as ["Hct0";"Hct1";"Hcs0";"Hcs1";"Hca0";"Hca1"].

    (* Revoke the world, to get the stack frame *)
    iMod (lse_world_f with "Hinterp_W0_csp Hworld_interp_C")
      as (l stk_mem) "(%Hextract & %Hpub_W0_Wfixed & Hworld_interp_C & Hrevoked_l & Hstk)".
    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_mmio Hstk_heap]; first done.

    (* Block 4: push the capability of [a] on the stack, load [a] *)
    iMod (na_inv_acc with "Hlse_code Hna")
      as "(>Hcgp_b & Hna & Hlse_code_close)"; auto.
    iEval (cbn [fmap list_fmap lse_main_imports]) in "Himports_main".
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    rewrite /length_lse_main_imports.
    change_pc_to (pc_a ^+ lse_label_offset ".Llse_f")%a.
    iApply (lse_f_blocks_1_spec with
             "[- $HPC $Hcgp $Hcsp $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcgp_b $Hstk $Hcode_main]");
      [done|done|done|done| |solve_addr+Hstk_min|].
    { by eapply switcher_disjoint_subseg; [| |split; eassumption]; solve_addr. }
    iNext; iIntros (stk_mem' wcs0' wcs1')
      "(HPC & Hcgp & Hcsp & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcgp_b & Hstk & _)".

    (* Blocks 5-6: assert that [a] contains [2], and return *)
    iApply (lse_f_blocks_2_spec with
             "[- $Hassert $HPC $Hcgp $Hcs0 $Hct0 $Hct1 $Hcra $Hca0 $Hca1
              $Himport_assert $Hcode_main]"); [done|exact (jalr_target_ok_switcher_return_sentry mie_ret)|].
    iNext; iIntros "(HPC & Hcgp & Hcs0 & Hct0 & Hct1 & Hcra & Hca0 & Hca1
                    & _ & _)".
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iMod ("Hlse_code_close" with "[$Hna $Hcgp_b]") as "Hna".
    iInsertRegs "Hrmap" ["Hct1";"Hct0";"Hcs1";"Hcs0";"Hcgp";"Hcra"].

    (* Return to the caller of [f] *)
    iDestruct (RevokedResources_mono_pub W0 _ C l l Hpub_W0_Wfixed with "Hrevoked_l") as "Hrevoked_l".
    iApply (switcher_ret_specification W0 (revoke W0) with
             "[$Hswitcher $Hswitcher_static $Hstk $Hcstk $HK $Hworld_interp_C $Hna $HPC $Hrevoked_l
              $Hrmap $Hca0 $Hca1 $Hcsp]"); auto.
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { destruct Hextract; auto. }
    { intros a; destruct Hextract as [_ Htemp]; destruct (Htemp a); auto. }
    { iSplit; iApply interp_int. }
  Qed.

End LSE.
