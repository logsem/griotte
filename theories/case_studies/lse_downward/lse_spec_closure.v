From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import rules logrel logrel_extra monotone proofmode register_tactics.
From cap_machine Require Import fetch assert switcher switcher_spec_return.
From cap_machine Require Import lse.
From cap_machine Require Import proofmode.

Section LSE.
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

  Lemma lse_f_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_lse_exp_tbl e_lse_exp_tbl : Addr)
    (g_lse_exp_tbl : Locality)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nlse LSEN : namespace)

    :

    let imports :=
     lse_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nlse ->
    Nassert ## Nlse ->
    (b_lse_exp_tbl <= b_lse_exp_tbl ^+ 2 < e_lse_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length lse_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length lse_main_data)%a = Some cgp_e ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nlse
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
    intros imports.
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
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hr_C & Hsts_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

    iMod (na_inv_acc with "Hlse_code Hna")
      as "(( >Himports_main & >Hcode_main & >Hcgp_b) & Hna & Hlse_code_close)"; auto.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* --- Extract registers ca0  --- *)
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs0) ) as [wcs0 Hwcs0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs1) ) as [wcs1 Hwcs1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
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

    (* Revoke the world to get the stack frame *)
    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l) "(%Hl_unk & Hsts_C & Hr_C & #Hfrm_close_W0 & >[%stk_mem Hstk] & Hrevoked_l)".

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    rewrite /lse_main_code /LSE_main_code_run.
    rewrite -!app_assoc.
    rewrite /LSE_main_code_f.
    assert (SubBounds pc_b pc_e (pc_a ^+ length LSE_main_code_run)%a
              (pc_a ^+ length lse_main_code)%a).
    { solve_addr. }
    focus_block_nochangePC 4 "Hcode_main" as a_f Ha_f "Hcode" "Hcont"; iHide "Hcont" as hcont.
    rewrite /length_lse_main_imports.
    iEval (cbn) in "HPC".
    replace (pc_b ^+ (3%nat + 21%nat))%a with a_f by solve_addr.

    (* GetB cs0 cgp; *)
    iInstr "Hcode".
    (* Add cs1 cs0; *)
    iInstr "Hcode".
    (* Subseg cgp cs0 cs1; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1%nat)%a); [solve_addr+Hcgp_size|reflexivity]. }
    { solve_addr+Hcgp_size. }
    (* Store csp cgp; *)
    destruct ( decide ((csp_b < csp_e)%a) ) as [Hcsp_size|Hcsp_size]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcgp $Hcsp]"); try solve_pure.
      { rewrite /withinBounds; solve_addr+Hcsp_size. }
      iIntros "!> _".
      wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.
    rewrite finz_dist_S in Hstklen; last solve_addr+Hcsp_size.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    assert (is_Some (csp_b + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hcsp_size|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1. }
    iInstr "Hcode".
    { rewrite /withinBounds; solve_addr+Hcsp_size. }
    (* Load ct0 cgp; *)
    iInstr "Hcode".
    { split; [solve_pure| solve_addr+Hcgp_size]. }
    (* Mov ct1 2; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 2: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 5 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_f.
    iApply (assert_success_spec
             with
             "[- $Hassert $Hna $HPC $Hcgp $Hcs0 $Hcs1 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]") ; auto.
    { apply withinBounds_true_iff; solve_addr. }
    { solve_ndisj. }
    iNext; iIntros "(Hna & HPC & Hcgp & Hcs0 & Hcs1 & Hcra & Hct0 & Hct1
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: RETURN ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 6 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_assert_c.
    (* Mov ca0 0%Z; *)
    iInstr "Hcode".
    (* Mov ca1 0%Z; *)
    iInstr "Hcode".
    (* JmpCap cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hlse_code_close" with "[$Hna Himport_C_f Himport_switcher Himport_assert Himports_main $Hcode_main $Hcgp_b]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_C_f $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Put all the registers under the same map *)
    iInsertList "Hrmap" [cra;cgp;cs1;cs0;ct1;ct0].
    iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk".
    { solve_addr+Hastk1. }
    { solve_addr+Hastk1 Hcsp_size. }

    iApply (switcher_ret_specification _ W0 W1
             with
             "[ $Hswitcher $Hstk $Hcstk $HK $Hsts_C $Hna $HPC $Hr_C $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ); auto.
    { apply related_pub_revoke_close_list.
      destruct Hl_unk; auto.
    }
    { apply regmap_full_dom in Hrmap_init.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_init; set_solver+.
    }
    { subst csp_b.
      destruct Hsync_csp as [Hsync_csp <-].
      auto.
    }
    { destruct Hl_unk; auto. }
    { destruct Hl_unk; auto. }
    { iSplit; iApply interp_int. }
  Qed.

  Lemma lse_awkward_safe

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_lse_exp_tbl e_lse_exp_tbl : Addr)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nlse LSEN : namespace)

    :

    let imports :=
     lse_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nlse ->
    Nassert ## Nlse ->
    (b_lse_exp_tbl <= b_lse_exp_tbl ^+ 2 < e_lse_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length lse_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length lse_main_data)%a = Some cgp_e ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nlse
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
