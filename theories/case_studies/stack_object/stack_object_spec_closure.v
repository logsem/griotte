From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import switcher_spec_call switcher_spec_return.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
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
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

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

    (Nassert Nswitcher Nso SON : namespace)

    :

    let imports := so_main_imports C_f in

    Nswitcher ## Nassert ->
    Nswitcher ## Nso ->
    Nassert ## Nso ->
    (b_so_exp_tbl <= b_so_exp_tbl ^+ 2 < e_so_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length so_main_data)%a = Some cgp_e ->

    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_inv cerise_nais Nso
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a so_main_code)
    ∗ inv (export_table_PCCN SON) (b_so_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN SON) ((b_so_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN SON (b_so_exp_tbl ^+ 2)%a)
        ((b_so_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 2 (length (imports ++ SO_main_code_run))))
    ∗ WSealed ot_switcher (SCap RO g_so_exp_tbl b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)
        ↦□ₑ 2
    ∗ seal_pred ot_switcher ot_switcher_propC
      -∗
    ot_switcher_prop W C (WCap RO g_so_exp_tbl b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a).
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
       - [so_call_blocks_3_spec]: blocks 7-9, push the secret, allocate the
         stack object [z], and jump to the switcher;
       - [so_world_call]: reinstate [z] in the world of the call;
       - [so_call_args] and [switcher_cc_specification_alt]: call to [g];
       - [so_return_blocks_4_spec]: blocks 10-12, assert that the secret is
         unchanged, and return;
       - [so_world_return]: repair the world;
       - [switcher_ret_specification_gen]: return to the caller of [f]. *)
    intros imports; subst imports.
    iIntros (Hswitcher_assert HNswitcher_so HNassert_so
               Hso_exp_tbl_size Hso_size_code Hso_imports Hcgp_size)
      "(#Hassert & #Hswitcher
      & #Hso_code
      & #Hso_exp_PCC
      & #Hso_exp_CGP
      & #Hso_exp_awkward
      & #Hentry_SO & #Hot_switcher)".
    iExists g_so_exp_tbl, b_so_exp_tbl, e_so_exp_tbl, (b_so_exp_tbl ^+ 2)%a,
    pc_b, pc_e, cgp_b, cgp_e, 2, _, SON.
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
    assert (so_code_bounds pc_b pc_e pc_a C_f) as Hbounds by done.
    iDestruct (so_args_zero with "Hzeroed_rmap") as %Hzero; first done.
    pose proof (regmap_full_dom _ Hrmap_init) as Hrmap_dom.
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
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
    iMod (na_inv_acc with "Hso_code Hna")
      as "((>Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".

    (* Blocks 3-5: save the callback, check [in] *)
    iEval (rewrite (_ : (pc_b ^+ 23%nat)%a = (pc_a ^+ so_block_offset 3)%a);
           [|offsets_compute; cbn in Hso_imports; solve_addr]) in "HPC".
    iApply (so_check_blocks_1_spec with
             "[- $HPC $Hca0 $Hca1 $Hct1 $Hcs0 $Hcs1 $Hcsp $Hcode_main]"); first done.
    iNext; iIntros (p g b e a)
      "(%Hp & -> & %Hno_overlap & HPC & Hca0 & Hca1 & Hct1 & Hcs0 & Hcs1 & Hcsp
      & Hcode_main & Hlc)".

    (* Revoke the world and open the region of [in] *)
    iMod (so_world_open_object with "Hinterp_W0_csp Hinterp_wca0 Hworld_interp_C Hlc")
      as (l_revoked stk_mem la object_mem)
           "(%Hextract & Hstack_revoked & %Hla & Hobject & Hclose_object)";
      [done|done|].

    (* Block 6: [in] only contains integers *)
    iApply (so_checkints_blocks_2_spec with
             "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hobject $Hcode_main]"); [done|done|done|].
    iNext; iIntros "(%Hints & HPC & Hca0 & Hcs0 & Hcs1 & Hobject & Hcode_main & [Hlc Hlc'])".

    (* Close the region of [in] *)
    iMod ("Hclose_object" with "[$Hobject $Hlc]")
      as "(Hworld_interp_C & Hrevoked_l_rest & Hstk & #Hinterp_wca0_W2)"; first done.

    (* Blocks 7-9: push the secret, allocate [z], jump to the switcher *)
    iApply (so_call_blocks_3_spec with
             "[- $HPC $Hcsp $Hca1 $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcra $Hstk $Himport_switcher
              $Hcode_main]"); first done.
    iNext; iIntros (a_stk1 a_stk2 stk_tail)
      "(%Hastk1 & %Hastk2 & %Hastk2_csp_e & HPC & Hcsp & Hca1 & Hct0 & Hct1 & Hcs0 & Hcs1
      & Hcra & Hsecret & Hastk1 & Hstk & Himport_switcher & Hcode_main)".

    (* Reinstate [z] in the world of the call *)
    iMod (so_world_call with
           "Hinterp_W0_csp Hinterp_wca1 Hworld_interp_C Hinterp_wca0_W2 Hstack_revoked
            Hastk1 Hlc'")
      as "(Hworld_interp_C & #Hinterp_wca0_W3 & #Hinterp_z & #Hinterp_wct1
           & Hstack_revoked & %Hrevoked_W3 & %Hpriv_W0_W3 & %Ha_stk1_W3)";
      [done..|].
    iMod ("Hso_code_close" with "[$Hna Himport_switcher Himport_assert Himport_C_f $Hcode_main]")
      as "Hna".
    { iNext. iRegionMerge. iFrame. }
    iDestruct (so_call_args with "Hswitcher Hca0 Hinterp_wca0_W3 Hca1 Hinterp_z Hct0 Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_delete_L Hrmap_dom; set_solver+. }
    { intros r Hr.
      rewrite !lookup_delete_ne; [by apply Hzero|set_solver+Hr..]. }

    (* Call to [g] *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked $Hcstk
              $Hinterp_wct1 $HK]"); [done|done|].
    iSplit; first done.
    iNext.
    clear dependent arg_rmap rmap' stk_mem.
    iIntros (W4 rmap'' stk_mem l4)
      "(%Hextract4 & Hl4 & %Hl4_W5 & %Hpub_ext & _ & %Hrmap''_dom & _ & %Hstack_W5
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn [updatePcPerm]) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;cnull]
      as ["Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hcnull"].
    iMod (na_inv_acc with "Hso_code Hna")
      as "((>Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".

    (* Blocks 10-12: assert that the secret is unchanged, return *)
    iApply (so_return_blocks_4_spec with
             "[- $Hassert $Hna $HPC $Hcsp $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hcnull $Hcra
              $Hcs0 $Hca0 $Hca1 $Hsecret $Himport_assert $Hcode_main]");
      [done|solve_addr|solve_addr|solve_ndisj|].
    iNext; iIntros "(Hna & HPC & Hcsp & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hcnull & Hcra
                    & Hcs0 & Hca0 & Hca1 & Hsecret & Himport_assert & Hcode_main)".
    iEval (cbn [updatePcPerm]) in "HPC".
    iMod ("Hso_code_close" with "[$Hna Himport_switcher Himport_assert Himport_C_f $Hcode_main]")
      as "Hna".
    { iNext. iRegionMerge. iFrame. }
    iInsertRegs "Hrmap" ["Hcnull";"Hct4";"Hct3";"Hct2";"Hct1";"Hct0";"Hcs0";"Hcs1";"Hcgp";"Hcra"].

    (* Repair the world *)
    iMod (so_world_return W0 W4 C b e (csp_b' ^+ 4)%a csp_e a_stk1 a_stk2 l_revoked l4 with
           "[$Hworld_interp_C $Hrevoked_l_rest $Hl4 $Hsecret $Hstk]")
      as (w_stk1)
           "(Hworld_interp_C & %Hpub_W0_Wfixed & %Hclosing_nodup & %Hclosing_temps
            & Hclosing & Hstk)";
      [done..|].

    (* Return to the caller of [f] *)
    iApply (switcher_ret_specification_gen _ W0 (revoke W4) with
             "[$Hswitcher $Hstk $Hcstk $HK $Hworld_interp_C $Hna $HPC
              $Hrmap $Hca0 $Hca1 $Hcsp $Hclosing]"); eauto.
    { rewrite !dom_insert_L !dom_delete_L Hrmap''_dom; set_solver+. }
    { clear -Hsync_csp.
      destruct Hsync_csp as [].
      rewrite -H0; auto. }
    { iSplit; iApply interp_int. }
  Qed.


  Lemma stack_object_f_spec_safe

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_so_exp_tbl e_so_exp_tbl : Addr)

    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nso SON : namespace)

    :

    let imports := so_main_imports C_f in

    Nswitcher ## Nassert ->
    Nswitcher ## Nso ->
    Nassert ## Nso ->
    (b_so_exp_tbl <= b_so_exp_tbl ^+ 2 < e_so_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length so_main_data)%a = Some cgp_e ->

    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_inv cerise_nais Nso
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a so_main_code)
    ∗ inv (export_table_PCCN SON) (b_so_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN SON) ((b_so_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN SON (b_so_exp_tbl ^+ 2)%a)
        ((b_so_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 2 (length (imports ++ SO_main_code_run))))
    ∗ WSealed ot_switcher (SCap RO Global b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)
        ↦□ₑ 2
    ∗ WSealed ot_switcher (SCap RO Local b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)
        ↦□ₑ 2
    ∗ seal_pred ot_switcher ot_switcher_propC
      -∗
    interp W C
      (WSealed ot_switcher (SCap RO Global b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)).
  Proof.
    intros imports.
    iIntros (Hswitcher_assert HNswitcher_so HNassert_so
               Hso_exp_tbl_size Hso_size_code Hso_imports Hcgp_size)
      "(#Hassert & #Hswitcher
      & #Hso_code
      & #Hso_exp_PCC
      & #Hso_exp_CGP
      & #Hso_exp_awkward
      & #Hentry_SO & #Hentry_SO' & #Hot_switcher)".
    iEval (rewrite fixpoint_interp1_eq /=).
    rewrite /interp_sb.
    iFrame "Hot_switcher".
    iSplit; [iPureIntro; apply persistent_cond_ot_switcher |].
    iSplit; [iIntros (w); iApply mono_priv_ot_switcher|].
    iSplit; iNext ; iApply stack_object_f_spec; try iFrame "#"; eauto.
  Qed.

End SO.
