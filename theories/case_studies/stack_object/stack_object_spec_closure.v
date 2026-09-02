From iris.proofmode Require Import proofmode.
From griotte Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From griotte Require Import rules logrel world_interp_stack monotone proofmode register_tactics.
From griotte Require Import fetch_spec assert_spec checkints checkra check_no_overlap_spec.
From griotte Require Import
  switcher interp_switcher_call switcher_spec_call switcher_spec_return.
From griotte Require Import world_ghost_theory stack_object_helpers world_std_revocation.
From griotte Require Import stack_object.
From griotte Require Import stack_object_spec_blocks.
From griotte Require Import stack_object_spec_resources.
From griotte Require Import stack_object_spec_repair.
From griotte Require Import proofmode.

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
    intros imports.
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
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

    iMod (na_inv_acc with "Hso_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* --- Extract registers ca0  --- *)
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs0) ) as [wcs0 Hwcs0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs1) ) as [wcs1 Hwcs1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.

    (* Extract the imports *)
    iDestruct (so_main_imports_pointsto with "Himports_main") as
      "(Himport_switcher & Himport_assert & Himport_C_f & Himports_main)"; eauto.

    iAssert (interp W0 C wca0) as "#Hinterp_wca0_W0".
    { iApply "Hinterp_rmap"; eauto.
      cbn; set_solver+.
    }

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    rewrite /so_main_code /SO_main_code_run.
    rewrite -!app_assoc.
    rewrite /SO_main_code_f.
    assert (SubBounds pc_b pc_e (pc_a ^+ length SO_main_code_run)%a
              (pc_a ^+ length so_main_code)%a).
    { solve_addr. }
    focus_block_nochangePC 3 "Hcode_main" as a_f Ha_f "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace (pc_b ^+ 23%nat)%a with a_f by solve_addr.

    (* Mov ct1 ca1 *)
    iInstr "Hcode" with "Hlc".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ----------------------------------------------- *)
    (* ------------- BLOCK 4 : CHECKRA --------------- *)
    (* ----------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_checkra Ha_checkra "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_f.
    iApply (checkra_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iSplitL; last ( iModIntro; iNext ; iIntros (?); done).
    iNext ; iIntros "H"; iDestruct "H" as (p g b e a) "([%Hp ->] & HPC & Hca0 & Hcs0 & Hcs1 & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ------------------------------------------------------ *)
    (* ------------- BLOCK 5:  CHECK_NO_OVERLAP ------------- *)
    (* ------------------------------------------------------ *)
    focus_block 5 "Hcode_main" as a_check_overlap Ha_check_overlap "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_checkra.
    iApply (check_no_overlap_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcsp $Hcode]"); eauto.
    iSplitL; last ( iNext ; iIntros (?); done).
    iNext ; iIntros "(HPC & Hca0 & Hcsp & Hcs1 & Hcs0 & %Hno_overlap & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ------------------------------------------------------- *)
    (* ----------------- BLOCK 6:  CHECKINTS ----------------- *)
    (* ------------------------------------------------------- *)
    focus_block 6 "Hcode_main" as a_checkints Ha_checkints "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_overlap.

    (* Revoke the world to get the stack frame *)
    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_interp_C]")
        as (l_revoked_W0) "([%Hl_revoked_W0_nodup %Hl_revoked_W0_temporaries]
                 & Hworld_interp_C
                 & #Hstack_revoked_W0 & >%Hstack_revoked_W0 & >[%stk_mem Hstk]
                 & [Hl_revoked_W0 %Hl_revoked_W0])".

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as
      Hrelated_priv_W0_W1 by eapply revoke_related_sts_priv_world.

    set (la_be_temporaries := so_object_temporaries W0 b e).
    set (la_be_permanents := so_object_permanents W0 b e).
    (* Filter the addresses that are in Temporary state in [la_be_temporaries]. *)
    set (l_revoked_W0_no_be :=
      so_revoked_without_object W0 b e l_revoked_W0).

    assert (la_be_temporaries ⊆ l_revoked_W0) as Htemps_subset.
    { intros x Hx.
      subst la_be_temporaries.
      apply list_elem_of_filter in Hx as [Hx Hx_be].
      apply (Hl_revoked_W0_temporaries x) in Hx.
      apply elem_of_app in Hx as [Hx|Hx]; first done.
      rewrite elem_of_disjoint in Hno_overlap.
      exfalso; eapply Hno_overlap; eauto.
    }
    assert (
      la_be_temporaries
        ≡ₚ filter (fun a => a ∈ la_be_temporaries) l_revoked_W0
    ) as Hla_be_temporaries_l.
    { apply NoDup_subset_filter_membership.
      - apply so_object_temporaries_NoDup.
      - apply NoDup_app in Hl_revoked_W0_nodup as [? _]. done.
      - exact Htemps_subset.
    }
    assert (
      l_revoked_W0 ≡ₚ la_be_temporaries ++ l_revoked_W0_no_be
    ) as Hl_wca0_l'.
    { subst l_revoked_W0_no_be.
      rewrite {1}Hla_be_temporaries_l.
      apply filter_complement_list.
    }
    assert (
      Forall
        (fun a => std (revoke W0) !! a = Some Revoked)
        la_be_temporaries
    ) as Hrevoked_la_be_temporaries.
    { apply Forall_forall. intros x Hx.
      apply revoke_lookup_Monotemp.
      apply Hl_revoked_W0_temporaries.
      apply elem_of_app; left.
      by apply Htemps_subset.
    }
    assert (
      finz.seq_between csp_b csp_e ## la_be_temporaries
    ) as Hstack_temps_disjoint.
    { rewrite elem_of_disjoint in Hno_overlap |- *.
      intros x Hx_stk Hx_temp.
      eapply Hno_overlap.
      - subst la_be_temporaries.
        apply list_elem_of_filter in Hx_temp as [_ Hx_object].
        exact Hx_object.
      - exact Hx_stk.
    }

    (* Get the list of permissions, predicates and words for the [la_be_temporaries]. *)
    iMod (stack_object_open_region_for_checkints
      W0 C p g b e a csp_b csp_e l_revoked_W0 stk_mem
      with "[$Hinterp_wca0_W0 $Hworld_interp_C $Hl_revoked_W0 $Hstk $Hlc]")
      as (wca0_lvs)
        "(%Hwca0_lvs_length & %Hwca0_range & Hwca0_lvs & Hrestore_wca0)".
    { split; eauto. }
    { exact Hno_overlap. }
    { exact Hp. }

    (* Apply the checkint specification*)
    iApply (checkints_spec
      with "[- $HPC $Hca0 $Hcs1 $Hcs0 $Hwca0_lvs $Hcode]"); eauto.
    { symmetry; exact Hwca0_range. }
    iSplitL; last (iModIntro; iNext; iIntros (?); done).
    iNext.
    iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hwca0_lvs
              & %Hwca0_lvs_ints & Hcode & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    set (W2 := close_list la_be_temporaries W1).
    iDestruct "Hlc" as "[Hlc_restore Hlc]".
    (* Close the world from the opened addresses [la_be_permanents]. *)
    iMod ("Hrestore_wca0" with "[$Hwca0_lvs $Hlc_restore]")
      as "(Hworld_interp_C & Hrevoked_l_revoked_W0_no_be
           & Hstk & #Hinterp_wca0_W2)".
    { iPureIntro. exact Hwca0_lvs_ints. }

    (* ------------------------------------------------------- *)
    (* ------------------ BLOCK 7: ALLOC_SO ------------------ *)
    (* ------------------------------------------------------- *)
    focus_block 7 "Hcode_main" as a_alloc_so Ha_alloc_so "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_checkints.

    iApply (stack_object_alloc_block_spec
              with "[- $HPC $Hcsp $Hca1 $Hcs0 $Hcs1 $Hstk $Hcode]"); eauto.
    iNext.
    iIntros (a_stk1 a_stk2 w0 w1 stk_mem')
      "(%Hastk1 & %Hastk2 & %Hastk_bounds & %Hstk_mem
       & HPC & Hcsp & Hca1 & Hcs0 & Hcs1
       & Hastk0 & Hastk1 & Hstk & Hcode)".
    destruct Hastk_bounds as (Hcsp_astk1 & Hastk1_astk2 & Hastk2_csp_e).
    assert (csp_b < csp_e)%a as Hcsp_size by solve_addr.
    assert (a_stk1 < csp_e)%a as Hcsp_size' by solve_addr.
    subst stk_mem; rename stk_mem' into stk_mem.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 8 : FETCH ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 8 "Hcode_main" as a_fetch Ha_fetch "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_alloc_so.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 9 : CALL ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 9 "Hcode_main" as a_call Ha_call "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_fetch.
    iApply (stack_object_call_block_spec
              with "[- $HPC $Hcra $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iNext.
    iIntros "(HPC & Hcra & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcode)".


    (* and the hard part should be mostly done at that point *)

    (* -- separate argument registers -- *)
    assert ( is_Some (rmap !! ca2) ) as [wca2 Hwca2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca3) ) as [wca3 Hwca3].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca4) ) as [wca4 Hwca4].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca5) ) as [wca5 Hwca5].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    set ( rmap_arg :=
           {[ ca0 := WCap p g b e (finz.max b e);
              ca1 := WCap RWL Local a_stk1 a_stk2 a_stk1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).

    assert (related_sts_pub_world W1 W2) as Hrelated_pub_W1_W2.
    { apply close_list_related_sts_pub. }

    assert (related_sts_priv_world W0 W2) as Hrelated_priv_W0_W2.
    { eapply related_sts_priv_pub_trans_world; eauto. }
    assert (related_sts_priv_world W W2) as
      Hrelated_priv_W_W2 by (by eapply related_sts_priv_trans_world; eauto).

    (* Show that the arguments are safe, when necessary *)
    iAssert ( ⌜ wca2 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca3 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca4 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca5 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    assert (std W0 !! a_stk1 = Some Temporary) as Ha_stk1_W0.
    { apply Hl_revoked_W0_temporaries.
      apply elem_of_app; right.
      apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
    }
    assert (std W2 !! a_stk1 = Some Revoked) as Ha_stk1_W2.
    { subst W2.
      rewrite close_list_lookup_not_in.
      * subst W1; cbn. apply revoke_lookup_Monotemp. exact Ha_stk1_W0.
      * subst la_be_temporaries.
        intro Ha'.
        rewrite elem_of_disjoint in Hstack_temps_disjoint.
        eapply Hstack_temps_disjoint; eauto.
        apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
    }
    (* Update the world and insert [la_be_temporaries]. *)
    set (W3 := reinstate W2 [a_stk1]).
    (* Insert the allocated SO [a_stk1] in the world. *)
    iMod (stack_object_reinstate_fresh_object
      W0 W2 C csp_b csp_e csp_b a_stk1 a_stk2
      with "[$Hinterp_W0_csp $Hworld_interp_C $Hastk1 $Hlc]")
      as "(Hworld_interp_C & %Hrelated_pub_W2_W3
           & %Ha_stk1_W3 & #Hinterp_W2_wca1)"; eauto.
    { split; first solve_addr+Hastk1.
      split; solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'. }
    assert (related_sts_priv_world W0 W3) as Hrelated_priv_W0_W3.
    { eapply related_sts_priv_pub_trans_world; eauto. }
    iDestruct (interp_monotone with "[] Hinterp_wca0_W2") as "Hinterp_wca0_W3"; eauto.

    (* The passed object is safe to share in the world [W2]. *)
    iAssert (if is_sealed_with_o wca1 ot_switcher
             then (interp W3 C wca1)
             else True)%I as "#Hinterp_W3_wct1".
    { destruct (is_sealed_with_o wca1 ot_switcher) eqn:His_sealed_wct1; last done.
      destruct wca1 as [| [|] | |]; try discriminate.
      iApply (interp_monotone_sd W0 W3); eauto.
      iApply "Hinterp_rmap"; eauto.
      iPureIntro ; set_solver.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg , rarg ↦ᵣ warg ∗ interp W3 C warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W3 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      iAssert (interp W3 C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call)) as
        "Hinterp_sw_call"; first iApply interp_switcher_call; auto.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    rewrite (finz_seq_between_cons csp_b csp_e); last solve_addr+Hcsp_size.
    iEval (cbn) in "Hstack_revoked_W0".
    iDestruct "Hstack_revoked_W0" as "[Hstack_revoked_W0_a_stk1 Hstack_revoked_W0]".
    rewrite (finz_seq_between_cons ((csp_b ^+ 1)%a) csp_e)
    ; last solve_addr+Hcsp_size Hcsp_size' Hastk1.
    iEval (cbn) in "Hstack_revoked_W0".
    iDestruct "Hstack_revoked_W0" as "[Hstack_revoked_W0_a_stk2 Hstack_revoked_W0]".
    (* Prepare the closing resources for the switcher call spec *)
    assert (
        Forall (λ k : finz MemNum, W3.1 !! k = Some Revoked) (finz.seq_between a_stk2 csp_e)
      ) as HW3_revoked_callee_frm.
    {
      apply Forall_forall; intros x Hx.
      subst W3 W2 W1.
      rewrite close_list_lookup_not_in.
      2: { intros Hx'; apply list_elem_of_singleton in Hx'; simplify_eq.
           apply elem_of_finz_seq_between in Hx.
           solve_addr+Hx Hastk2 Hcsp_size'.
      }
      rewrite close_list_lookup_not_in.
      2: { intro Hx'.
           apply Hstack_temps_disjoint in Hx'; first done.
           apply elem_of_finz_seq_between in Hx.
           apply elem_of_finz_seq_between.
           solve_addr+Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
      }
      apply revoke_lookup_Monotemp.
      clear -Hl_revoked_W0_nodup Hl_revoked_W0_temporaries Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
      specialize (Hl_revoked_W0_temporaries x) ; apply Hl_revoked_W0_temporaries.
      apply elem_of_app; right.
      apply elem_of_finz_seq_between in Hx.
      apply elem_of_finz_seq_between.
      solve_addr+Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
    }
    iDestruct (StackRevokedResources_mono_priv _ W3 with "Hstack_revoked_W0") as "Hstack_revoked_W3"; eauto.
    replace ((csp_b ^+ 1) ^+ 1)%a with a_stk2 by solve_addr.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hso_code_close" with "[$Hna Himport_assert Himport_switcher Himport_C_f Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iApply so_main_imports_pointsto; first exact Hso_imports.
      iFrame.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W3 $Hcstk
              $Hinterp_W3_wct1 $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hrmap_init.
      rewrite /dom_arg_rmap Hrmap_init.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    iClear "Hinterp_rmap Hzeroed_rmap".
    clear dependent wct1 wct0 wcs0 wcs1 rmap stk_mem.
    iNext.
    iIntros (W4 rmap stk_mem l_revoked_W4)
      "( [%Hl_revoked_W4_nodup %Hl_revoked_W4_temporaries] & Hl_revoked_W4 & %Hl_revoked_W4
      & %Hrelated_pub_2ext_W4 & Hrel_stk_C' & %Hdom_rmap & Hstack_revoked_W4 & %Hstack_revoked_W4
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn) in "HPC".

    assert (related_sts_pub_world W3 W4) as Hrelated_pub_W3_W4.
    {
      eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros x Hx.
      rewrite Forall_forall in HW3_revoked_callee_frm.
      apply HW3_revoked_callee_frm.
      rewrite !elem_of_finz_seq_between in Hx |- *; solve_addr+Hx.
    }
    (* Derive a bunch of disjointness properties that will be necessary later. *)
    set (W5 := revoke W4).
    (* Revoke the returned world resources by separation.  The repair helper
       later uses these state facts to reconcile the two revocation sets. *)
    iMod (world_interp_revoked_by_separation_many_with_RevokedResources
           with "[$Hrevoked_l_revoked_W0_no_be $Hworld_interp_C]")
      as "(Hworld_interp_C & Hrevoked_l_revoked_W0_no_be & %Hrevoked_l_revoked_W0_no_be_W5)".
    { apply Forall_forall.
      intros x Hx.
      subst l_revoked_W0_no_be.
      apply list_elem_of_filter in Hx as [_ Hl].
      rewrite -revoke_dom_eq.
      eapply elem_of_mono_pub; eauto.
      rewrite -!close_list_dom_eq.
      rewrite -revoke_dom_eq.
      assert ( std W0 !! x = Some Temporary).
      { apply Hl_revoked_W0_temporaries; apply elem_of_app ; by left. }
      rewrite elem_of_dom; done.
    }
    iMod (world_interp_revoked_by_separation_many_with_RevokedResources with "[$Hl_revoked_W4 $Hworld_interp_C]")
      as "(Hworld_interp_C & Hl_revoked_W4 & %Hrevoked_l_revoked_W4_W5)".
    { apply Forall_forall.
      intros x Hx.
      rewrite -revoke_dom_eq.
      assert ( std W4 !! x = Some Temporary).
      { apply Hl_revoked_W4_temporaries; apply elem_of_app ; by left. }
      rewrite elem_of_dom; done.
    }
    iMod (world_interp_revoked_by_separation_many with "[$Hstk $Hworld_interp_C]")
      as "(Hworld_interp_C & Hstk & %Hstk_W5)".
    { eapply Forall_impl; eauto; cbn.
      intros x Hx.
      rewrite elem_of_dom; done.
    }

    iMod (world_interp_revoked_by_separation with "[$Hastk0 $Hworld_interp_C]")
      as "(Hworld_interp_C & Hastk0 & %Hastk0_W5)".
    {
      rewrite -revoke_dom_eq.
      eapply elem_of_mono_pub; eauto.
      rewrite -!close_list_dom_eq.
      rewrite -revoke_dom_eq.
      assert ( std W0 !! csp_b = Some Temporary).
      { apply Hl_revoked_W0_temporaries; apply elem_of_app ; right.
        apply elem_of_finz_seq_between; done.
      }
      rewrite elem_of_dom; done.
    }

    (* simplify the knowledge about the new rmap *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero".
    assert (∀ r : RegName, r ∈ dom rmap → rmap !! r = Some (WInt 0)) as Hrmap_init.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    iExtractList "Hrmap" [ct0;ct1] as ["Hct0"; "Hct1"].

    iMod (na_inv_acc with "Hso_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    clear Hpc_contiguous.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* Extract the imports *)
    iDestruct (so_main_imports_pointsto with "Himports_main") as
      "(Himport_switcher & Himport_assert & Himport_C_f & Himports_main)"; eauto.

    focus_block 10 "Hcode_main" as a_assert_prep Ha_assert_prep "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_call.

    iApply (stack_object_assert_prep_block_spec
              with "[- $HPC $Hcsp $Hct0 $Hct1 $Hastk0 $Hcode]").
    { solve_addr+Hastk1 Hastk2. }
    { eauto. }
    iNext.
    iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hastk0 & Hcode)".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 11: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 11 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_assert_prep.
    iExtractList "Hrmap" [ct2;ct3;ct4;cnull] as ["Hct2"; "Hct3";"Hct4";"Hcnull"].
    iApply (assert_success_spec
             with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra $Hcnull
              $Hcode $Himport_assert]") ; auto.
    { apply withinBounds_true_iff; solve_addr. }
    { solve_ndisj. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 12: RETURN ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 12 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_assert_c.
    iApply (stack_object_return_block_spec
              with "[- $HPC $Hcra $Hcs0 $Hca0 $Hca1 $Hcnull $Hcode]"); eauto.
    iNext.
    iIntros "(HPC & Hcra & Hcs0 & Hca0 & Hca1 & Hcnull & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hso_code_close" with "[$Hna Himport_switcher Himport_assert Himport_C_f Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iApply so_main_imports_pointsto; first exact Hso_imports.
      iFrame.
    }

    (* Put all the registers under the same map *)
    iInsertList "Hrmap" [cnull;ct4;ct3;ct2;ct1;ct0].
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap ; set_solver+. }

    (* Repair the initial and returned revocation sets together.  The helper
       removes the fresh cell and the incoming object overlap, closes the
       repaired world, and reconstructs the complete stack region. *)
    set (l_revoked_W4_no_astk1 :=
      filter (fun a => a <> a_stk1) l_revoked_W4).
    set (l_revoked_W4_no_astk1_wca0 :=
      filter (fun a => a ∈ la_be_temporaries)
        l_revoked_W4_no_astk1).
    set (l_revoked_W4_no_astk1_no_wca0 :=
      filter (fun a => a ∉ la_be_temporaries)
        l_revoked_W4_no_astk1).
    set (closing_list_revoked_addresses :=
      l_revoked_W0 ++ l_revoked_W4_no_astk1_no_wca0).
    set (closing_list :=
      closing_list_revoked_addresses ++ finz.seq_between csp_b csp_e).

    iMod (stack_object_repair_world_for_return
      W0 W3 W4 C b e csp_b csp_e a_stk1 a_stk2
      l_revoked_W0 l_revoked_W4 (WInt so_secret) stk_mem
      with "[$Hworld_interp_C $Hrevoked_l_revoked_W0_no_be
             $Hl_revoked_W4 $Hastk0 $Hstk]")
      as (w_stk1_return)
        "(Hworld_interp_C & %Hrelated_pub_W0_Wfixed & %Hclosing_list_nodup
          & %Hclosing_list_covers_W0 & Hrevoked & Hstk)".
    { split; eauto. }
    { split; eauto. }
    { subst W3 W2 W1 la_be_temporaries. reflexivity. }
    { exact Ha_stk1_W3. }
    { exact Hrelated_priv_W0_W3. }
    { exact Hrelated_pub_W3_W4. }
    { exact Hno_overlap. }
    { exact Hastk1. }
    { exact Hastk2. }
    { exact Hastk2_csp_e. }
    { exact Hcsp_bounds. }
    { exact Hl_revoked_W4. }
    { exact Hrevoked_l_revoked_W0_no_be_W5. }
    { exact Hstk_W5. }
    { exact Hastk0_W5. }

    (* The repair helper's postcondition is exactly the generalized switcher
       return protocol: no filtering or resource surgery remains here. *)
    iApply (switcher_ret_specification_gen _ W0 W5
             with
             "[ $Hswitcher $Hstk $Hcstk_frag $HK $Hworld_interp_C $Hna $HPC
                $Hrmap $Hca0 $Hca1 $Hcsp $Hrevoked]"); eauto.
    { repeat (rewrite dom_insert_L); rewrite Hdom_rmap; set_solver+. }
    { subst csp_b.
      clear -Hsync_csp.
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
