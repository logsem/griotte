From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher switcher_spec_return.
From griotte Require Import lse.
From griotte Require Import world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import lse_spec_states lse_spec_world
  lse_spec_f_blocks_1 lse_spec_f_blocks_2.

Section LSE.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma lse_f_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_lse_exp_tbl e_lse_exp_tbl : Addr)
    (g_lse_exp_tbl : Locality)

    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nlse LSEN : namespace)

    :

    let imports := lse_main_imports C_f in

    Nswitcher ## Nassert ->
    Nswitcher ## Nlse ->
    Nassert ## Nlse ->
    (b_lse_exp_tbl <= b_lse_exp_tbl ^+ 2 < e_lse_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length lse_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length lse_main_data)%a = Some cgp_e ->

    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_inv cerise_nais Nlse
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
         ∗ codefrag pc_a lse_main_code
         ∗ cgp_b ↦ₐ WInt 2
        )
    ∗ inv (export_table_PCCN LSEN) (b_lse_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN LSEN) ((b_lse_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN LSEN (b_lse_exp_tbl ^+ 2)%a)
        ((b_lse_exp_tbl ^+ 2)%a ↦ₐ lse_exp_tbl_entry_f)
    ∗ WSealed ot_switcher (SCap RO g_lse_exp_tbl b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+ 2)%a)
        ↦□ₑ 0
    ∗ seal_pred ot_switcher ot_switcher_propC
      -∗
    ot_switcher_prop W C (WCap RO g_lse_exp_tbl b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+ 2)%a).
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
    intros imports; subst imports.
    iIntros (Hswitcher_assert HNswitcher_lse HNassert_lse
               Hlse_exp_tbl_size Hlse_size_code Hlse_imports Hcgp_size)
      "(#Hassert & #Hswitcher
      & #Hlse_code
      & #Hlse_exp_PCC
      & #Hlse_exp_CGP
      & #Hlse_exp_f
      & #Hentry_LSE & #Hot_switcher)".
    iExists g_lse_exp_tbl, b_lse_exp_tbl, e_lse_exp_tbl, (b_lse_exp_tbl ^+ 2)%a,
    pc_b, pc_e, cgp_b, cgp_e, 0, _, LSEN.
    iFrame "#".
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hworld_interp_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & _ & _)".
    rewrite /interp_conf /registers_pointsto.
    assert (lse_code_bounds pc_b pc_e pc_a C_f) as Hbounds by done.
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by (cbn in Hcgp_size; solve_addr).
    pose proof (regmap_full_dom _ Hrmap_init) as Hrmap_dom.
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    iExtractList "Hrmap" [ct0;ct1;cs0;cs1;ca0;ca1;cnull]
      as ["Hct0";"Hct1";"Hcs0";"Hcs1";"Hca0";"Hca1";"Hcnull"].

    (* Revoke the world, to get the stack frame *)
    set (csp_b := (csp_b' ^+ 4)%a).
    iMod (lse_world_f with "Hinterp_W0_csp Hworld_interp_C")
      as (l stk_mem) "(%Hextract & %Hpub_W0_Wfixed & Hworld_interp_C & Hrevoked_l & Hstk)".

    (* Block 4: push the capability of [a] on the stack, load [a] *)
    iMod (na_inv_acc with "Hlse_code Hna")
      as "(( >Himports_main & >Hcode_main & >Hcgp_b) & Hna & Hlse_code_close)"; auto.
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    rewrite /length_lse_main_imports.
    change_pc_to (pc_a ^+ lse_block_offset 4)%a.
    iApply (lse_f_blocks_1_spec with
             "[- $HPC $Hcgp $Hcsp $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcgp_b $Hstk $Hcode_main]");
      [done|done|].
    iNext; iIntros (stk_mem' wcs0' wcs1')
      "(HPC & Hcgp & Hcsp & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcgp_b & Hstk & Hcode_main)".

    (* Blocks 5-6: assert that [a] contains [2], and return *)
    iApply (lse_f_blocks_2_spec with
             "[- $Hassert $Hna $HPC $Hcgp $Hcs0 $Hcs1 $Hct0 $Hct1 $Hcra $Hca0 $Hca1 $Hcnull
              $Himport_assert $Hcode_main]"); [done|solve_ndisj|].
    iNext; iIntros "(Hna & HPC & Hcgp & Hcs0 & Hcs1 & Hct0 & Hct1 & Hcra & Hca0 & Hca1
                    & Hcnull & Himport_assert & Hcode_main)".
    iEval (cbn [updatePcPerm]) in "HPC".
    iMod ("Hlse_code_close" with
           "[$Hna Himport_switcher Himport_assert Himport_C_f $Hcode_main $Hcgp_b]")
      as "Hna".
    { iNext. iRegionMerge. iFrame. }
    iInsertRegs "Hrmap" ["Hcnull";"Hct1";"Hct0";"Hcs1";"Hcs0";"Hcgp";"Hcra"].

    (* Return to the caller of [f] *)
    iApply (switcher_ret_specification _ W0 (revoke W0) with
             "[$Hswitcher $Hstk $Hcstk $HK $Hworld_interp_C $Hna $HPC $Hrevoked_l
              $Hrmap $Hca0 $Hca1 $Hcsp]"); auto.
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { subst csp_b.
      destruct Hsync_csp as [Hcsp_sync Hcsp_base].
      rewrite -Hcsp_base; auto. }
    { destruct Hextract; auto. }
    { intros a; destruct Hextract as [_ Htemp]; destruct (Htemp a); auto. }
    { iSplit; iApply interp_int. }
  Qed.

  Lemma lse_awkward_safe

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_lse_exp_tbl e_lse_exp_tbl : Addr)

    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nlse LSEN : namespace)

    :

    let imports := lse_main_imports C_f in

    Nswitcher ## Nassert ->
    Nswitcher ## Nlse ->
    Nassert ## Nlse ->
    (b_lse_exp_tbl <= b_lse_exp_tbl ^+ 2 < e_lse_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length lse_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length lse_main_data)%a = Some cgp_e ->

    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_inv cerise_nais Nlse
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
         ∗ codefrag pc_a lse_main_code
         ∗ cgp_b ↦ₐ WInt 2
        )
    ∗ inv (export_table_PCCN LSEN) (b_lse_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN LSEN) ((b_lse_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN LSEN (b_lse_exp_tbl ^+ 2)%a)
        ((b_lse_exp_tbl ^+ 2)%a ↦ₐ lse_exp_tbl_entry_f)
    ∗ WSealed ot_switcher (SCap RO Global b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+ 2)%a)
        ↦□ₑ 0
    ∗ WSealed ot_switcher (SCap RO Local b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+ 2)%a)
        ↦□ₑ 0
    ∗ seal_pred ot_switcher ot_switcher_propC
      -∗
    interp W C
      (WSealed ot_switcher (SCap RO Global b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+ 2)%a)).
  Proof.
    intros imports; subst imports.
    iIntros (Hswitcher_assert HNswitcher_lse HNassert_lse
               Hlse_exp_tbl_size Hlse_size_code Hlse_imports Hcgp_size)
      "(#Hassert & #Hswitcher
      & #Hlse_code
      & #Hlse_exp_PCC
      & #Hlse_exp_CGP
      & #Hlse_exp_awkward
      & #Hentry_LSE & #Hentry_LSE' & #Hot_switcher
      )".
    iEval (rewrite fixpoint_interp1_eq /=).
    rewrite /interp_sb.
    iFrame "Hot_switcher".
    iSplit; [iPureIntro; apply persistent_cond_ot_switcher |].
    iSplit; [iIntros (w); iApply mono_priv_ot_switcher|].
    iSplit; iNext ; iApply lse_f_spec; try iFrame "#"; eauto.
  Qed.


End LSE.
