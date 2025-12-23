From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import rules logrel logrel_extra monotone proofmode register_tactics.
From cap_machine Require Import fetch_spec assert_spec checkints checkra check_no_overlap_spec.
From cap_machine Require Import
  switcher interp_switcher_call switcher_spec_call switcher_spec_return.
From cap_machine Require Import stack_object.
From cap_machine Require Import proofmode.

Section SO.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma stack_object_f_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_so_exp_tbl e_so_exp_tbl : Addr)
    (g_so_exp_tbl : Locality)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nso SON : namespace)

    :

    let imports :=
     so_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nso ->
    Nassert ## Nso ->
    (b_so_exp_tbl <= b_so_exp_tbl ^+ 2 < e_so_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length so_main_data)%a = Some cgp_e ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nso
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a so_main_code)
    ∗ inv (export_table_PCCN SON) (b_so_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN SON) ((b_so_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN SON (b_so_exp_tbl ^+ 2)%a)
        ((b_so_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 1 (length (imports ++ SO_main_code_run))))
    ∗ WSealed ot_switcher (SCap RO g_so_exp_tbl b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
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
    pc_b, pc_e, cgp_b, cgp_e, 1, _, SON.
    iFrame "#".
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hr_C & Hsts_C & %Hsync_csp & Hcstk & Hna)".
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
    assert ( is_Some (rmap !! ct2) ) as [wct2 Hwct2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct3) ) as [wct3 Hwct3].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f Himports_main]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }

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
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ----------------------------------------------- *)
    (* ------------- BLOCK 4 : CHECKRA --------------- *)
    (* ----------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_checkra Ha_checkra "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_f.
    iApply (checkra_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iSplitL; last ( iNext ; iIntros (?); done).
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

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l) "(%Hl_unk & Hsts_C & Hr_C & #Hfrm_close_W0 & >[%stk_mem Hstk] & Hrevoked_l)".

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as
      Hrelated_priv_W0_W1 by eapply revoke_related_sts_priv_world.
    iAssert ( ⌜ Forall (fun a => std W !! a = Some Permanent ∨ std W !! a = Some Temporary)
                (finz.seq_between b e) ⌝)%I
    as "%Harg_std_states".
    { admit. (* easy, consequence of RO interp capability *) }
    set (wca0_temp := filter (fun a => std W !! a = Some Temporary) (finz.seq_between b e)).
    set (wca0_perma := filter (fun a => std W !! a = Some Permanent) (finz.seq_between b e)).
    assert ( (finz.seq_between b e) ≡ₚ wca0_perma ++ wca0_temp ) as Hwca0_range.
    { clear - Harg_std_states.
      admit. (* should be easy -ish *)
    }
    set (l' := filter (fun a => a ∉ wca0_temp) l).
    assert ( l ≡ₚ wca0_temp ∪ l') as Hl_wca0_l'.
    { admit. (* should be easy -ish *) }
    setoid_rewrite Hl_wca0_l'.
    iDestruct (big_sepL_app with "Hrevoked_l") as "[Hrevoked_wca0_temp Hrevoked_l']".

    rewrite region_open_nil.
    iDestruct (read_allowed_inv_full_cap with "Hinterp_wca0_W0") as "Hinterp_wca0_invs"; auto.
    iAssert (
        ∃ (wca0_invs : list (finz MemNum * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type)),
          ⌜ (λ '(a, _, _, _), a) <$> wca0_invs = wca0_perma ⌝ ∗
          ⌜ Forall (λ '(a, _, _, ρ), W !! a = Some ρ) wca0_invs ⌝ ∗
          ([∗ list] '(a, p, φ, _) ∈ wca0_invs, rel C a p φ)
      )%I as "(%wca0_invs & %Hwca0_invs_perma & %Hwca0_invs_std_perma & Hrels_wca0)".
    { admit. (* should be doable *)
    }

    iDestruct (region_open_list with "[$Hrels_wca0 $Hr_C $Hsts_C]") as
      "(%wca0_lv_perma & Hr_C & Hsts_C & Hsts_std_wca0 & Hwca0_perma_lv & Hwca0_mono & Hwca0_φs
     & %Hlength_wca0_lv & Hwca0_pO)".
    { rewrite Hwca0_invs_perma.
      admit.
    }
    { rewrite Hwca0_invs_perma; set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [  ] ] ] Hx; cbn in *; simplify_eq.
      admit.
    }
    { admit. }
    iAssert ( [∗ list] a;v ∈ wca0_perma ; wca0_lv_perma, a ↦ₐ v )%I with "[Hwca0_perma_lv]"
      as "Hwca0_perma_lv".
    { admit. (* easy, just impl *)
    }
    iDestruct (big_sepL_sep with "Hrevoked_wca0_temp") as "[Hrevoked_wca0_temp %Hrevoked_wca0_temp]"
    .
    iAssert (
        ∃ (lp : list Perm)
          (lφ : list (WORLD * CmptName * Word → iPropI Σ) )
          (lv : list Word),
          ([∗ list] φ ∈ lφ, ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝)
          ∗ ([∗ list] a;pφ ∈ wca0_temp;(zip lp lφ), rel C a pφ.1 pφ.2)
          ∗ ([∗ list] p ∈ lp, ⌜isO p = false⌝)
          ∗ ([∗ list] a;v ∈ wca0_temp;lv, a ↦ₐ v)
          ∗ ([∗ list] lpφ;v ∈ (zip lp lφ);lv,
               (if isWL lpφ.1
                then future_pub_mono C lpφ.2 v
                else (if isDL lpφ.1 then future_pub_mono C lpφ.2 v else future_priv_mono C lpφ.2 v))
            )
          ∗ ([∗ list] φ;v ∈ lφ;lv, φ (W,C,v)))%I
      with "[Hrevoked_wca0_temp]"
      as (lp lφ wca0_lv_temps) "(Hlφ_pers & #Hlpφ_rels & HlpO & Hwca0_temp_lv & Hlpφ_mono & Hlφ_lv)".
    { admit. (* very annoying, but should be okay *) }
    iDestruct (big_sepL2_app with "Hwca0_perma_lv Hwca0_temp_lv") as "Hwca0_lvs".
    iAssert (∃ wca0_lvs,
                ⌜ wca0_lvs ≡ₚ wca0_lv_perma ∪ wca0_lv_temps ⌝
                ∗ [[b,e]] ↦ₐ [[ wca0_lvs ]]
            )%I with "[Hwca0_lvs]" as (wca0_lvs) "[%Hwca0_lvs_eq Hwca0_lvs]".
    { admit. (* TODO might be pretty hard to prove... but maybe if generalised + induction *)
    }

    iApply (checkints_spec with "[- $HPC $Hca0 $Hcs1 $Hcs0 $Hwca0_lvs $Hcode]"); eauto.
    iSplitL; last ( iNext ; iIntros (?); done).
    iNext ; iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hwca0_lvs & %Hwca0_lvs_ints & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    (* close the world *)
    (* update the world with wca0_temp to temporary *)
    (* and the hard part should be mostly done at that point *)

    iApply (checkints_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.

    (* -- separate argument registers -- *)
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
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

    focus_block 6 "Hcode_main" as a_call_g1 Ha_call_g1 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_fetch1.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov cs1 ca0 *)
    iInstr "Hcode".
    (* Mov ct1 ca0 *)
    iInstr "Hcode".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".

    set ( rmap_arg :=
           {[ ca0 := WInt 0;
              ca1 := wca1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    iInsertList "Hrmap" [ct2;ct3].
    repeat (iEval (rewrite -delete_insert_ne //) in "Hrmap").
    set (rmap' := (delete ca5 _)).
    iDestruct (sts_full_rel_loc  with "Hsts_C Hsts_rel") as "%Hwrel_i".

    set (W2 := (<l[i:=false]l>W1)).
    assert (related_sts_priv_world W1 W2) as Hrelated_priv_W1_W2.
    { subst W2.
     rewrite /related_sts_priv_world /=.
     split; first apply related_sts_std_priv_refl.
     split;[set_solver|split;[set_solver|] ].
     intros d rpub rpriv rpub' rpriv' Hr Hr'; simplify_eq.
     repeat (split; first done).
     intros x y Hd Hd'.
     destruct (decide (d = i)); simplify_map_eq; last apply rtc_refl.
     destruct b; simplify_map_eq; last apply rtc_refl.
     apply rtc_once.
     right;apply convert_rel_of_rel.
     done.
    }

    assert (related_sts_priv_world W0 W2) as Hrelated_priv_W0_W2 by (by eapply related_sts_priv_trans_world; eauto).
    assert (related_sts_priv_world W W2) as
      Hrelated_priv_W_W2 by (by eapply related_sts_priv_trans_world; eauto).

    iMod (update_region_revoked_update_loc with "Hsts_C Hr_C") as "[Hr_C Hsts_C]"; auto.
    { apply revoke_conditions_sat. }

    (* Show that the arguments are safe, when necessary *)
    iAssert (if is_sealed_with_o wca0 ot_switcher
             then (interp W2 C wca0)
             else True)%I as "#Hinterp_W2_wct1".
    { destruct (is_sealed_with_o wca0 ot_switcher) eqn:His_sealed_wct1; last done.
      destruct wca0 as [| [|] | |]; try discriminate.
      iApply (interp_monotone_sd W0 W2); eauto.
      iApply "Hinterp_rmap"; eauto.
      iPureIntro ; set_solver.
    }
    iAssert ( ⌜ wca1 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
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

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg , rarg ↦ᵣ warg ∗ interp W2 C warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W2 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      iAssert (interp W2 C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call)) as
        "Hinterp_sw_call"; first iApply interp_switcher_call; auto.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    (* Prepare the closing resources for the switcher call spec *)
    iAssert (
        ([∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W2 C a ∗
                                                    ⌜W2.1 !! a = Some Revoked⌝)
      )%I with "[Hfrm_close_W0]" as "Hfrm_close_W2".
    {
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a Ha) "[Hclose %Hrev]".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hvae_code_close" with "[$Hna Himport_assert Himport_switcher Himport_C_f Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_C_f $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W2 $Hcstk
              $Hinterp_W2_wct1 $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hrmap_init.
      rewrite /dom_arg_rmap Hrmap_init.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    iClear "Hinterp_rmap Hzeroed_rmap".
    clear dependent wct1 wct0 wct2 wct3 wcs0 wcs1 rmap stk_mem.
    iNext.
    iIntros (W3 rmap stk_mem l')
      "( _ & _ & %Hrelated_pub_2ext_W3 & Hrel_stk_C' & %Hdom_rmap & Hfrm_close_W3
      & Hna & %Hcsp_bounds
      & Hsts_C & Hr_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)"; clear l'.
    iEval (cbn) in "HPC".

    assert (related_sts_pub_world W2 W3) as Hrelated_pub_W2_W3.
    {
      eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros a Ha.
      cbn.
      eapply revoke_lookup_Monotemp.
      destruct Hl_unk as [_ Htemp]; apply Htemp.
      apply elem_of_app; right.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
    }
    set (W4 := revoke W3).

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

    iMod (na_inv_acc with "Hvae_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hvae_code_close)"; auto.
    clear Hpc_contiguous.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

    clear a_awkward.
    focus_block_nochangePC 7 "Hcode_main" as a_awkward Ha_awkward "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace (a_call_g1 ^+ 5)%a with a_awkward by solve_addr.

    (* Store cgp 1%Z; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "HawkN") as "(>(%b' & Hst_i & Hcgp_b) & Hclose_awk)"; auto.
    iAssert ( cgp_b ↦ₐ (if b' then WInt 1 else WInt 0) )%I with "[Hcgp_b]" as "Hcgp_b".
    { destruct b' ; iFrame. }
    iApply (wp_store_success_z with "[$HPC $Hi $Hcgp $Hcgp_b]"); try solve_pure.
    { apply withinBounds_true_iff; solve_addr. }
    iIntros "!> (HPC & Hi & Hcgp & Hcgp_b)".
    iDestruct (sts_full_state_loc  with "Hsts_C Hst_i") as "%Hwst_i'".
    iMod (sts_update_loc _ _ _ _ true with "Hsts_C Hst_i") as "[Hsts_C Hst_i]".
    iMod ("Hclose_awk" with "[$Hst_i $Hcgp_b]") as "_".
    iModIntro.
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Mov ct1 cs1 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 9 : FETCH ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 8 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_awkward.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 9 "Hcode_main" as a_call_g2 Ha_call_g2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_fetch2.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".

    (* -- separate argument registers -- *)
    assert ( rmap !! ca2 = Some (WInt 0)) as Hwca2.
    { apply Hrmap_init; rewrite Hdom_rmap; set_solver+. }
    assert ( rmap !! ca3 = Some (WInt 0)) as Hwca3.
    { apply Hrmap_init; rewrite Hdom_rmap; set_solver+. }
    assert ( rmap !! ca4 = Some (WInt 0)) as Hwca4.
    { apply Hrmap_init; rewrite Hdom_rmap; set_solver+. }
    assert ( rmap !! ca5 = Some (WInt 0)) as Hwca5.
    { apply Hrmap_init; rewrite Hdom_rmap; set_solver+. }
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as ["Hca2"; "Hca3"; "Hca4"; "Hca5"].

    clear rmap_arg.
    set ( rmap_arg :=
           {[ ca0 := WInt 0;
              ca1 := WInt 0;
              ca2 := WInt 0;
              ca3 := WInt 0;
              ca4 := WInt 0;
              ca5 := WInt 0;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).
    set (rmap' := (delete ca5 _)).


    iDestruct (sts_full_rel_loc  with "Hsts_C Hsts_rel") as "%Hwrel_i'".
    set (W5 := (<l[i:=true]l>W4)).
    assert (related_sts_pub_world W4 W5) as Hpriv_W4_W5.
    { subst W5.
     rewrite /related_sts_pub_world /=.
     split; first apply related_sts_std_pub_refl.
     split;[set_solver|split;[set_solver|] ].
     intros d rpub rpriv rpub' rpriv' Hr Hr'; simplify_eq.
     repeat (split; first done).
     intros x y Hd Hd'.
     destruct (decide (d = i)); simplify_map_eq; last apply rtc_refl.
     destruct b'; simplify_map_eq; first apply rtc_refl.
     apply rtc_once.
     rewrite /convert_rel.
     exists false, true.
     repeat (split; first done).
     by rewrite /awk_rel_pub; left.
    }

    assert (related_sts_priv_world W3 W5) as Hrelated_priv_W3_W5.
    { eapply (related_sts_priv_pub_trans_world W3 W4); eauto.
      apply revoke_related_sts_priv_world.
    }
    assert (related_sts_priv_world W2 W5) as Hrelated_priv_W2_W5.
    { eapply related_sts_pub_priv_trans_world; eauto. }

    iMod (update_region_revoked_update_loc with "Hsts_C Hr_C") as "[Hr_C Hsts_C]"; auto.
    { apply revoke_conditions_sat. }
    { by apply related_sts_pub_priv_world. }

    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg , rarg ↦ᵣ warg ∗ interp W5 C warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W5 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      iAssert (interp W5 C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call)) as
        "Hinterp_sw_call"; first iApply interp_switcher_call; auto.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    (* Show that the arguments are safe, when necessary *)
    iAssert (if is_sealed_with_o wca0 ot_switcher
             then (interp W5 C wca0)
             else True)%I as "#Hinterp_W5_wca0".
    { destruct (is_sealed_with_o wca0 ot_switcher) eqn:His_sealed_wca0; last done.
      destruct wca0 as [| [|] | |]; try discriminate.
      iApply (interp_monotone_sd W2 W5); eauto.
    }

    (* Prepare the closing resources for the switcher call spec *)
    iAssert (
        ([∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W5 C a ∗
                                                    ⌜W5.1 !! a = Some Revoked⌝)
      )%I with "[Hfrm_close_W3]" as "#Hfrm_close_W5".
    { rewrite !big_sepL_sep.
      iDestruct "Hfrm_close_W3" as "[Hclose_W3 %Hrev_W3]".
      iSplitL "Hclose_W3".
      - iApply (big_sepL_impl with "Hclose_W3").
        iModIntro; iIntros (k a Ha) "Hclose'".
        iApply mono_priv_closing_revoked_resources; last done.
        eauto.
      - iApply big_sepL_pure; iPureIntro.
        intros k x Hk.
        cbn.
        eapply Hrev_W3; eauto.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hvae_code_close" with "[$Hna Himport_switcher Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    iDestruct (sts_full_rel_loc  with "Hsts_C Hsts_rel") as "%Hwrel_i_W5".
    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W5 $Hcstk_frag
              $Hinterp_W5_wca0 $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hdom_rmap.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    clear dependent wct1 wct0 warg0 warg1 rmap stk_mem Hcsp_bounds.
    iNext.
    iIntros (W6 rmap stk_mem l')
      "(_ & _ & %Hrelated_pub_5ext_W6 & Hrel_stk_C'' & %Hdom_rmap & Hfrm_close_W6
      & Hna & %Hcsp_bounds
      & Hsts_C & Hr_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)"; clear l'.
    iEval (cbn) in "HPC".

    (* Derive some information necessary later *)
    iAssert ( ⌜ Forall (λ k : finz MemNum, W5.1 !! k = Some Revoked) (finz.seq_between (csp_b ^+ 4)%a csp_e) ⌝)%I
      as "%Hrevoked_stk_W5".
    { iClear "∗".
      iDestruct (big_sepL_sep with "Hfrm_close_W5") as "[_ %]".
      iPureIntro.
      apply Forall_forall.
      intros x Hx.
      assert (x ∈ finz.seq_between csp_b csp_e) as Hx'.
      {
        rewrite (finz_seq_between_split csp_b (csp_b ^+ 4)%a csp_e); last solve_addr.
        rewrite elem_of_app; by right.
      }
      apply elem_of_list_lookup in Hx' as [k Hk].
      eapply H; eauto.
    }
    assert (related_sts_pub_world W5 W6) as Hrelated_pub_W5_W6.
    { clear -Hrelated_pub_5ext_W6 Hrevoked_stk_W5.
      eapply related_sts_pub_trans_world; eauto.
      eapply related_sts_pub_update_multiple_temp; eauto.
    }
    clear Hrevoked_stk_W5.

    iAssert (⌜ Forall (λ a : finz MemNum, a ∈ dom W6.1) l ⌝)%I as "%Hl_revoked_W6".
    {
      iDestruct (big_sepL_sep with "Hrevoked_l") as "[_ %Hrevoked_l]".
      iPureIntro; apply Forall_forall; intros a Ha.
      apply elem_of_list_lookup in Ha as [k Hk].
      apply Hrevoked_l in Hk.
      cbn.
      assert (a ∈ dom (std W2)) as Ha2.
      { rewrite elem_of_dom; done. }
      destruct Hrelated_pub_W5_W6 as [ [Hdom_5_6 _] _ ].
      apply Hdom_5_6.
      cbn.
      rewrite -revoke_dom_eq.
      destruct Hrelated_pub_W2_W3 as [ [Hdom_2_3 _] _ ].
      by apply Hdom_2_3.
    }

    set (W7 := revoke W6).
    iMod (
       revoked_by_separation_many_with_temp_resources with "[$Hsts_C $Hr_C $Hrevoked_l]"
      ) as "(Hrevoked_l & Hsts_C & Hr_C & %Hl_revoked_W7)".
    { apply Forall_forall; intros a Ha.
      rewrite Forall_forall in Hl_revoked_W6.
      apply Hl_revoked_W6 in Ha.
      rewrite -revoke_dom_eq.
      done.
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

    iMod (na_inv_acc with "Hvae_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hvae_code_close)"; auto.
    clear Hpc_contiguous.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    clear a_awkward.
    focus_block_nochangePC 9 "Hcode_main" as a_ret Ha_ret "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace a_call_g2 with a_ret by solve_addr.

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "HawkN") as "(>(%b'' & Hst_i & Hcgp_b) & Hclose_awk)"; auto.
    iDestruct (sts_full_state_loc  with "Hsts_C Hst_i") as "%Hwst_i''".
    iDestruct (sts_full_rel_loc  with "Hsts_C Hsts_rel") as "%Hwrel_i''".
    assert (loc W7 !! i = Some (encode true)); last simplify_eq.
    {
      destruct Hrelated_pub_W5_W6 as [_ [Hdom1 [Hdom2 Htrans] ] ].
      specialize (Htrans i _ _ _ _ Hwrel_i_W5 Hwrel_i'') as [Heq1 [Heq2 Htrans] ]; eauto .
      assert (loc W5 !! i = Some (encode true)) by (by simplify_map_eq).
      specialize (Htrans _ _ H2 Hwst_i'').
      apply rtc_rel_pub' in Htrans ; auto.
      simplify_eq; auto.
    }

    iApply (wp_load_success_alt with "[$HPC $Hi $Hct0 $Hcgp $Hcgp_b]"); try solve_pure.
    { split; last apply withinBounds_true_iff; solve_addr. }
    iIntros "!> (HPC & Hct0 & Hi & Hcgp & Hcgp_b)".
    iMod ("Hclose_awk" with "[$Hst_i $Hcgp_b]") as "_".
    iModIntro.
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    iEval (cbn) in "Hct0".

    (* Mov ct1 1%Z; *)
    iInstr "Hcode".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 10 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct2;ct3;ct4] as ["Hct2"; "Hct3";"Hct4"].
    iApply (assert_success_spec
             with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]") ; auto.
    { apply withinBounds_true_iff; solve_addr. }
    { solve_ndisj. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 5: RETURN ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 11 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cra cs0; *)
    iInstr "Hcode".
    (* Mov ca0 0%Z; *)
    iInstr "Hcode".
    (* Mov ca1 0%Z; *)
    iInstr "Hcode".
    (* JmpCap cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hvae_code_close" with "[$Hna Himport_switcher Himport_assert Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Put all the registers under the same map *)
    iInsertList "Hrmap" [ct4;ct3;ct2;ct1;ct0].
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }

    iDestruct (big_sepL_sep with "Hfrm_close_W6") as "[_ %Hrevoked_stk_W7]".
    iApply (switcher_ret_specification _ W0 W7
             with
             "[ $Hswitcher $Hstk $Hcstk_frag $HK $Hsts_C $Hna $HPC $Hr_C $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ); auto.
    { destruct Hl_unk as [_ ?].
      eapply (related_pub_W0_Wfixed W0 W3 W6 l); eauto.
      apply Forall_app; split; auto.
      apply Forall_forall; intros a Ha.
      apply elem_of_list_lookup in Ha ; destruct Ha as [??]; eapply Hrevoked_stk_W7; eauto.
    }
    { repeat (rewrite dom_insert_L); rewrite Hdom_rmap; set_solver+. }
    { subst csp_b.
      destruct Hsync_csp as [].
      rewrite -H0; auto.
    }
    { destruct Hl_unk; auto. }
    { destruct Hl_unk; auto. }
    { iSplit; iApply interp_int. }
  Qed.

  Lemma vae_awkward_safe

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nvae VAEN : namespace)
    i

    :

    let imports :=
     vae_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae ->
    Nassert ## Nvae ->
    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (vae_main_code ot_switcher))%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    (exists b : bool, loc W !! i = Some (encode b)) ->
    wrel W !! i =
    Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nvae
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a (vae_main_code ot_switcher))
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
