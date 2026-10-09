From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel interp_weakening monotone.
From griotte Require Import fetch_spec assert_spec switcher interp_switcher_call switcher_spec_call switcher_spec_return.
From griotte Require Import vae vae_helper.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import vae_spec_states vae_spec_world_call vae_spec_world_return
  vae_spec_awkward_blocks_1 vae_spec_awkward_blocks_2 vae_spec_awkward_blocks_3.

Section VAE.
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

  Lemma vae_awkward_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)
    (g_vae_exp_tbl : Locality)

    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nvae VAEN : namespace)
    i

    :

    let imports := vae_main_imports C_f in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae ->
    Nassert ## Nvae ->
    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length vae_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    (exists b : bool, loc W !! i = Some (encode b)) ->
    wrel W !! i =
    Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->

    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_inv cerise_nais Nvae
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a vae_main_code)
    ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 1 (length (imports ++ VAE_main_code_init))))
    ∗ WSealed ot_switcher (SCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ seal_pred ot_switcher ot_switcher_propC
    (* invariant for d *)
    ∗ (∃ ι, inv ι (awk_inv C i cgp_b))
    ∗ sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_priv
      -∗
    ot_switcher_prop W C (WCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a).
  Proof.
    (* Outline of the proof:
       - unfold [ot_switcher_prop] and introduce the state of the machine at
         the entry point of [awkward];
       - [world_interp_revoke_stack]: revoke the world, to get the stack
         frame;
       - [vae_world_flag_false]: the flag can be set to [false];
       - [vae_awkward_blocks_1_spec]: blocks 4-6, set the flag to [0], and
         jump to the switcher;
       - [vae_world_stack], [vae_world_callback] and [vae_call_args]:
         prepare the first call to [g];
       - [switcher_cc_specification_alt]: first call to [g];
       - [vae_world_pub_call] and [vae_world_flag_true]: the flag can be set
         to [true];
       - [vae_awkward_blocks_2_spec]: blocks 7-9, set the flag to [1], and
         jump to the switcher;
       - [vae_world_stack], [vae_world_callback] and [vae_call_args]:
         prepare the second call to [g];
       - [switcher_cc_specification_alt]: second call to [g];
       - [vae_world_pub_call] and [vae_world_return]: the flag is still
         [true], and the world can be repaired;
       - [vae_awkward_blocks_3_spec]: blocks 9-11, assert that the flag is
         [1], and return;
       - [switcher_ret_specification]: return to the caller of [awkward]. *)
    intros imports.
    iIntros (Hswitcher_assert HNswitcher_vae HNassert_vae
               Hvae_exp_tbl_size Hvae_size_code Hvae_imports Hcgp_size Hloc_i_W Hrel_i_W)
      "(#Hassert & #Hswitcher
      & #Hvae_code
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & #Hvae_exp_awkward
      & #Hentry_VAE & #Hot_switcher
      & [%awkN #HawkN] & #Hsts_rel)".
    iExists g_vae_exp_tbl, b_vae_exp_tbl, e_vae_exp_tbl, (b_vae_exp_tbl ^+ 2)%a,
    pc_b, pc_e, cgp_b, cgp_e, 1, _, VAEN.
    iFrame "#".
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hworld_interp_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & #Hinterp_rmap & #Hzeroed_rmap)".
    rewrite /interp_conf /registers_pointsto.
    assert (vae_code_bounds pc_b pc_e pc_a C_f) as Hbounds by done.
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by (cbn in Hcgp_size; solve_addr).
    iDestruct (vae_args_zero with "Hzeroed_rmap") as %Hzero; first done.
    pose proof (regmap_full_dom _ Hrmap_init) as Hrmap_dom.
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    destruct (Hrmap_init ca0) as [wca0 Hwca0].
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]".
    { rewrite !lookup_delete_ne //; apply Hzero; set_solver+. }
    iExtractList "Hrmap" [ct0;ct1;cs0;cs1] as ["Hct0";"Hct1";"Hcs0";"Hcs1"].
    iAssert (interp W0 C wca0) as "#Hinterp_wca0".
    { iApply "Hinterp_rmap"; eauto. cbn; set_solver+. }
    iDestruct (world_interp_rel_loc_valid with "Hworld_interp_C Hsts_rel") as %Hrel_i_W0.

    (* Revoke the world, to get the stack frame *)
    set (csp_b := (csp_b' ^+ 4)%a).
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_interp_C]")
      as (l) "(%Hextract & Hworld_interp_C & #Hstack_revoked_W0 & >%Hstack_revoked_W0
               & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".

    (* The flag can be set to [false] *)
    set (W2 := <l[i:=false]l>(revoke W0)).
    destruct (vae_world_flag_false W W0 i Hpriv_W_W0 Hloc_i_W Hrel_i_W Hrel_i_W0)
      as ([b Hloc_i_W1] & Hrevoke_W1 & Hpriv_W1_W2 & Hpriv_W0_W2 & Hloc_i_W2 & Hrel_i_W2).

    (* Blocks 4-6: set the flag to [0], and jump to the switcher *)
    iMod (na_inv_acc with "Hvae_code Hna")
      as "((>Himports_main & >Hcode_main) & Hna & Hvae_code_close)"; auto.
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    change_pc_to (pc_a ^+ vae_block_offset 4)%a.
    iApply (vae_awkward_blocks_1_spec with
             "[- $HawkN $Hworld_interp_C $HPC $Hcgp $Hcra $Hca0 $Hct0 $Hct1 $Hcs0 $Hcs1
              $Himport_switcher $Hcode_main]"); [done|done|done|done|].
    iNext; iIntros "(Hworld_interp_C & HPC & Hcgp & Hcra & Hca0 & Hct0 & Hct1 & Hcs0 & Hcs1
                    & Himport_switcher & Hcode_main)".
    iMod ("Hvae_code_close" with "[$Hna Himport_switcher Himport_assert Himport_C_f $Hcode_main]")
      as "Hna".
    { iNext. iRegionMerge. iFrame. }

    (* Prepare the first call to [g] *)
    iDestruct (vae_world_stack W0 C i false with "Hstack_revoked_W0")
      as "[Hstack_revoked_W2 %Hstack_revoked_W2]"; [done|done|].
    iDestruct (vae_world_callback W0 W2 C wca0 with "[]") as "#Hinterp_W2_wca0";
      first done.
    { by case_match. }
    iDestruct (vae_call_args W2 C Nswitcher with "Hswitcher Hca0 Hca1 Hct0 Hrmap")
      as (rmap1) "(%Hrmap1_dom & Hrmap_arg & Hrmap)".
    { rewrite !dom_delete_L Hrmap_dom; set_solver+. }
    { intros r Hr.
      rewrite !lookup_delete_ne; [apply Hzero; set_solver+Hr|set_solver+Hr..]. }

    (* First call to [g] *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W2 $Hcstk
              $Hinterp_W2_wca0 $HK]"); [done|apply vae_call_adv_arg_rmap_is_arg|].
    iSplit; first done.
    iNext.
    clear dependent rmap1 stk_mem.
    iIntros (W3 rmap3 stk_mem l3)
      "(_ & _ & _ & %Hpub_ext_W3 & _ & %Hrmap3_dom & Hstack_revoked_W3 & %Hstack_revoked_W3
      & Hna & _
      & Hworld_interp_C
      & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn [updatePcPerm]) in "HPC".

    (* The flag can be set to [true] *)
    pose proof (vae_world_pub_call W2 W3 csp_b csp_e Hstack_revoked_W2 Hpub_ext_W3)
      as Hpub_W2_W3.
    iDestruct (world_interp_rel_loc_valid with "Hworld_interp_C Hsts_rel") as %Hrel_i_W3.
    set (W5 := <l[i:=true]l>(revoke W3)).
    destruct (vae_world_flag_true W2 W3 i false Hloc_i_W2 Hrel_i_W2 Hrel_i_W3 Hpub_W2_W3)
      as (Hrevoke_W4 & Hpriv_W4_W5 & Hpriv_W3_W5 & Hpriv_W2_W5 & Hloc_i_W5).

    (* Blocks 7-9: set the flag to [1], and jump to the switcher *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hzero3]".
    iDestruct (big_sepM_pure with "Hzero3") as %Hzero3.
    iExtractList "Hrmap" [ct0;ct1] as ["Hct0";"Hct1"].
    iMod (na_inv_acc with "Hvae_code Hna")
      as "((>Himports_main & >Hcode_main) & Hna & Hvae_code_close)"; auto.
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    iApply (vae_awkward_blocks_2_spec with
             "[- $HawkN $Hworld_interp_C $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct0 $Hct1 $Hcs0 $Hcs1
              $Himport_switcher $Hcode_main]"); [done|done|done|done|].
    iNext; iIntros "(Hworld_interp_C & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct0 & Hct1 & Hcs0
                    & Hcs1 & Himport_switcher & Hcode_main)".
    iMod ("Hvae_code_close" with "[$Hna Himport_switcher Himport_assert Himport_C_f $Hcode_main]")
      as "Hna".
    { iNext. iRegionMerge. iFrame. }

    (* Prepare the second call to [g] *)
    iDestruct (vae_world_stack W3 C i true with "Hstack_revoked_W3")
      as "[Hstack_revoked_W5 %Hstack_revoked_W5]"; [done|done|].
    iDestruct (vae_world_callback W2 W5 C wca0 with "Hinterp_W2_wca0")
      as "#Hinterp_W5_wca0"; first done.
    iDestruct (vae_call_args W5 C Nswitcher with "Hswitcher Hca0 Hca1 Hct0 Hrmap")
      as (rmap5) "(%Hrmap5_dom & Hrmap_arg & Hrmap)".
    { rewrite !dom_delete_L Hrmap3_dom; set_solver+. }
    { by apply vae_rmap_zero. }

    (* Second call to [g] *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W5 $Hcstk
              $Hinterp_W5_wca0 $HK]"); [done|apply vae_call_adv_arg_rmap_is_arg|].
    iSplit; first done.
    iNext.
    iIntros (W6 rmap6 stk_mem6 l6)
      "(_ & _ & _ & %Hpub_ext_W6 & _ & %Hrmap6_dom & _ & %Hstack_revoked_W6
      & Hna & _
      & Hworld_interp_C
      & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0' [Hca0 _] ] & [%warg1' [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn [updatePcPerm]) in "HPC".

    (* The flag is still [true], and the world can be repaired *)
    pose proof (vae_world_pub_call W5 W6 csp_b csp_e Hstack_revoked_W5 Hpub_ext_W6)
      as Hpub_W5_W6.
    iMod (vae_world_return W0 W3 W6 C i b l csp_b csp_e
           with "Hsts_rel Hworld_interp_C Hrevoked_l")
      as "(Hworld_interp_C & Hrevoked_l & %Hloc_i_W7 & %Hpub_W0_Wfixed)";
      [done..|].

    (* Blocks 9-11: assert that the flag is [1], and return *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;cnull]
      as ["Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hcnull"].
    iMod (na_inv_acc with "Hvae_code Hna")
      as "((>Himports_main & >Hcode_main) & Hna & Hvae_code_close)"; auto.
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    iApply (vae_awkward_blocks_3_spec with
             "[- $HawkN $Hworld_interp_C $Hassert $Hna $HPC $Hcgp $Hcra $Hcs0 $Hca0 $Hca1
              $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hcnull $Himport_assert $Hcode_main]");
      [done|done|exact Hloc_i_W7|solve_ndisj|].
    iNext; iIntros "(Hworld_interp_C & Hna & HPC & Hcgp & Hcra & Hcs0 & Hca0 & Hca1
                    & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hcnull & Himport_assert & Hcode_main)".
    iEval (cbn [updatePcPerm]) in "HPC".
    iMod ("Hvae_code_close" with "[$Hna Himport_switcher Himport_assert Himport_C_f $Hcode_main]")
      as "Hna".
    { iNext. iRegionMerge. iFrame. }
    iInsertRegs "Hrmap" ["Hcnull";"Hct4";"Hct3";"Hct2";"Hct1";"Hct0";"Hcs0";"Hcs1";"Hcgp";"Hcra"].

    (* Return to the caller of [awkward] *)
    iApply (switcher_ret_specification _ W0 (revoke W6) with
             "[$Hswitcher $Hstk $Hcstk $HK $Hworld_interp_C $Hna $HPC $Hrevoked_l
              $Hrmap $Hca0 $Hca1 $Hcsp]"); auto.
    { rewrite !dom_insert_L !dom_delete_L Hrmap6_dom; set_solver+. }
    { subst csp_b.
      destruct Hsync_csp as [Hcsp_sync Hcsp_base].
      rewrite -Hcsp_base; auto. }
    { destruct Hextract; auto. }
    { intros a; destruct Hextract as [_ Htemp]; destruct (Htemp a); auto. }
    { iSplit; iApply interp_int. }
  Qed.

  Lemma vae_awkward_safe

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)

    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nvae VAEN : namespace)
    i

    :

    let imports := vae_main_imports C_f in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae ->
    Nassert ## Nvae ->
    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length vae_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    (exists b : bool, loc W !! i = Some (encode b)) ->
    wrel W !! i =
    Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->

    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_inv cerise_nais Nvae
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a vae_main_code)
    ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 1 (length (imports ++ VAE_main_code_init))))
    ∗ WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO Local b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ seal_pred ot_switcher ot_switcher_propC
    ∗ (∃ ι, inv ι (awk_inv C i cgp_b))
    ∗ sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_priv
      -∗
    interp W C
      (WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)).
  Proof.
    intros imports; subst imports.
    iIntros (Hswitcher_assert HNswitcher_vae HNassert_vae
               Hvae_exp_tbl_size Hvae_size_code Hvae_imports Hcgp_size Hloc_i_W Hrel_i_W)
      "(#Hassert & #Hswitcher
      & #Hvae_code
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & #Hvae_exp_awkward
      & #Hentry_VAE & #Hentry_VAE' & #Hot_switcher
      & [%ι #Hι] & #Hsts_rel)".
    iEval (rewrite fixpoint_interp1_eq /=).
    rewrite /interp_sb.
    iFrame "Hot_switcher".
    iSplit; [iPureIntro; apply persistent_cond_ot_switcher |].
    iSplit; [iIntros (w); iApply mono_priv_ot_switcher|].
    iSplit; iNext ; iApply vae_awkward_spec; try iFrame "#"; eauto.
  Qed.


End VAE.
