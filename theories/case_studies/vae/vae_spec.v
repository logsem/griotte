From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import rules logrel logrel_extra monotone proofmode register_tactics.
From cap_machine Require Import fetch assert interp_switcher_call switcher_spec_call switcher_spec_call_alt vae.

Section VAE.
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

  Definition awkN : namespace := nroot .@ "awkN".
  Definition awk_inv C i a :=
    (∃ x:bool, sts_state_loc (A:=Addr) C i x
            ∗ if x
              then a ↦ₐ WInt 1%Z
              else a ↦ₐ WInt 0%Z)%I.

  Definition awk_rel_pub := λ a b, a = false ∨ b = true.
  Definition awk_rel_priv := λ (a b : bool), True.

  Lemma vae_awkward_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)
    (g_vae_exp_tbl : Locality)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nvae VAEN : namespace)
    i

    :

    let imports :=
     vae_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
       b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+2)%a
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae ->
    Nassert ## Nvae ->
    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (vae_main_code ot_switcher))%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length vae_main_data)%a = Some cgp_e ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nvae
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a (vae_main_code ot_switcher))
    ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (switcher.encode_entry_point 1 (length (imports ++ VAE_main_code_init))))
    ∗ interp W C (WSealed ot_switcher C_f)
    ∗ WSealed ot_switcher C_f ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ seal_pred ot_switcher ot_switcher_propC
    (* invariant for d *)
    ∗ (∃ ι, inv ι (awk_inv C i cgp_b))
    ∗ sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_pub awk_rel_priv
      -∗
    ot_switcher_prop W C (WCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a).
  Proof.
    intros imports.
    iIntros (Hswitcher_assert HNswitcher_vae HNassert_vae
               Hvae_exp_tbl_size Hvae_size_code Hvae_imports Hcgp_size)
      "(#Hassert & #Hswitcher
      & #Hvae_code
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & #Hvae_exp_awkward
      & #Hinterp_W0_C_f
      & #HentryC_f & #Hentry_VAE & #Hot_switcher
      & [%awkN #HawkN] & #Hsts_rel)".
    iExists g_vae_exp_tbl, b_vae_exp_tbl, e_vae_exp_tbl, (b_vae_exp_tbl ^+ 2)%a,
    pc_b, pc_e, cgp_b, cgp_e, 1, _, VAEN.
    iFrame "#".
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iIntros "!> %rmap %cstk %Ws %Cs %W0 %Hpriv_W_W0 !> %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hr_C & Hsts_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

    iMod (na_inv_acc with "Hvae_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hvae_code_close)"; auto.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* --- Extract registers ca0  --- *)
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
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
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_VAE_awkward Himports_main]".
    { transitivity (Some (pc_b ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }

    (* Revoke the world to get the stack frame *)
    generalize (csp_b' ^+4)%a as csp_b; intros csp_b.
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

    rewrite /vae_main_code /VAE_main_code_init /VAE_main_code_f.
    rewrite -!app_assoc.
    assert (SubBounds pc_b pc_e (pc_a ^+ length VAE_main_code_init)%a
              (pc_a ^+ length (vae_main_code ot_switcher))%a).
    { solve_addr. }
    focus_block_nochangePC 5 "Hcode_main" as a_awkward Ha_awkward "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace (pc_b ^+ 34%nat)%a with a_awkward by solve_addr.

    (* Store cgp 0%Z; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "HawkN") as "(>(%b & Hst_i & Hcgp_b) & Hclose_awk)"; auto.
    iAssert ( cgp_b ↦ₐ (if b then WInt 1 else WInt 0) )%I with "[Hcgp_b]" as "Hcgp_b".
    { destruct b ; iFrame. }
    iApply (wp_store_success_z with "[$HPC $Hi $Hcgp $Hcgp_b]"); try solve_pure.
    { apply withinBounds_true_iff; solve_addr. }
    iIntros "!> (HPC & Hi & Hcgp & Hcgp_b)".
    iDestruct (sts_full_state_loc  with "Hsts_C Hst_i") as "%Hwst_i".
    iMod (sts_update_loc _ _ _ _ false with "Hsts_C Hst_i") as "[Hsts_C Hst_i]".
    iMod ("Hclose_awk" with "[$Hst_i $Hcgp_b]") as "_".
    iModIntro.
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 2 : FETCH ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 6 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_awkward.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL g ----------------- *)
    (* --------------------------------------------------- *)

    (* -- separate argument registers -- *)
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

    focus_block 7 "Hcode_main" as a_call_g1 Ha_call_g1 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_fetch1.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov cs1 ca0 *)
    iInstr "Hcode".
    (* Mov ct1 ca0 *)
    iInstr "Hcode".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Mov ca2 0 *)
    iInstr "Hcode".
    (* Mov ca3 0 *)
    iInstr "Hcode".
    (* Mov ca4 0 *)
    iInstr "Hcode".
    (* Mov ca5 0 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".

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

    iInsertList "Hrmap" [ct2;ct3].
    repeat (iEval (rewrite -delete_insert_ne //) in "Hrmap").
    set (rmap' := (delete ca5 _)).
    iDestruct (sts_full_rel_loc  with "Hsts_C Hsts_rel") as "%Hwrel_i".

    set (W2 := (<l[i:=false]l>W1)).
    assert (related_sts_priv_world W1 W2) as Hpriv_W1_W2.
    { subst W2.
     rewrite /related_sts_priv_world /=.
     split; first apply related_sts_std_priv_refl.
     split;[set_solver|split;[set_solver|] ].
     intros d r1 r2 r1' r2' r3 r3' Hr Hr'; simplify_eq.
     repeat (split; first done).
     intros x y Hd Hd'.
     destruct (decide (d = i)); simplify_map_eq; last apply rtc_refl.
     destruct b; simplify_map_eq; last apply rtc_refl.
     apply rtc_once.
     right;right; apply convert_rel_of_rel.
     done.
    }

    assert (related_sts_priv_world W0 W2) as Hpriv_W0_W2 by (by eapply related_sts_priv_trans_world; eauto).
    assert (related_sts_priv_world W W2) as
      Hpriv_W_W2 by (by eapply related_sts_priv_trans_world; eauto).

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
      )%I with "[Hfrm_close_W0]" as "#Hfrm_close_W2".
    {
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a Ha) "[Hclose %Hrev]".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hvae_code_close" with "[$Hna Himport_assert Himport_switcher Himport_C_f Himport_VAE_awkward Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_VAE_awkward $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
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

    iClear "Hinterp_rmap".
    clear dependent wca1 wca2 wca3 wca4 wca5.
    clear dependent wct1 wct0 wct2 wct3 wcs0 wcs1 rmap.
    iNext.
    (* subst rmap'; clear stk_mem. *)
    iIntros (W3 rmap stk_mem_l stk_mem_h)
      "(%Hrelated_pub_2ext_W3 & %Hdom_rmap
      & Hna & #Hinterp_W3_csp & %Hcsp_bounds
      & Hsts_C & Hr_C & Hfrm_close_W3
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk_l & Hstk_h & HK)".
    iEval (cbn) in "HPC".

    (* ----- Revoke the world to get borrowed addresses back -----*)
    (* 1. Close the world *)
    iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
    iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
    iEval (rewrite <- (app_nil_r (finz.seq_between (csp_b ^+ 4)%a csp_e))) in "Hr_C".
    iAssert (
       [∗ list] a ; v ∈ finz.seq_between (csp_b ^+ 4)%a csp_e ; stk_mem_h, a ↦ₐ v ∗ closing_resources interp W3 C a v
      )%I with "[Hfrm_close_W3 Hstk_h]" as "Hfrm_close_W3".
    { rewrite /region_pointsto.
      iDestruct (big_sepL2_sep  with "[$Hstk_h $Hfrm_close_W3]") as "$".
    }
    iDestruct (region_close_list_interp_gen with "[$Hr_C $Hfrm_close_W3]"
      ) as "Hr_C".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { done. }
    rewrite -region_open_nil.

    (* 1.5. Derive some properties on the world required later *)
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

    iMod (revoked_by_separation_many with "[$Hr_C $Hsts_C $Hstk_l]")
      as "(Hr_C & Hsts_C & Hstk_l & %Hstk_l_revoked)".
    {
      apply Forall_forall; intros a Ha.
      eapply elem_of_mono_pub;eauto.
      rewrite elem_of_dom.
      rewrite revoke_lookup_Monotemp; first done.
      destruct Hl_unk as [_ H_lunk].
      pose proof (H_lunk a) as [_ Ha']; apply Ha'.
      apply elem_of_app; right.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha Hcsp_bounds.
    }
    rewrite Forall_forall in Hstk_l_revoked.

    (* 2. Revoke the world again *)
    clear dependent stk_mem stk_mem_h.
    iMod (monotone_revoke_stack_alt with "[$Hinterp_W3_csp $Hsts_C $Hr_C]")
        as (l') "(%Hl_unk' & Hsts_C & Hr_C & #Hfrm_close_W3 & >[%stk_mem_h Hstk_h] & Hrevoked_l')".
    iDestruct (region_pointsto_split with "[$Hstk_l $Hstk_h]") as "Hstk"; auto.
    { solve_addr+ Hcsp_bounds. }
    { by rewrite finz_seq_between_length in Hlen_stk_l. }
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
    focus_block_nochangePC 8 "Hcode_main" as a_awkward Ha_awkward "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace (a_call_g1 ^+ 10)%a with a_awkward by solve_addr.

    (* Store cgp 0%Z;8*)
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

    iInstr "Hcode".
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 9 : FETCH ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 9 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_awkward.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 10 "Hcode_main" as a_call_g2 Ha_call_g2 "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_fetch2.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov cs1 ca0 *)
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
     intros d r1 r2 r1' r2' r3 r3' Hr Hr'; simplify_eq.
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

    assert (related_sts_priv_world W2 W5) as Hpriv_W2_W5.
    { admit. }

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
    { admit.
      (* iApply (big_sepL_impl with "Hfrm_close_W3"). *)
      (* iModIntro; iIntros (k a Ha) "[Hclose %Hrev]". *)
      (* iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto. *)
      (* + admit. *)
      (* + admit. *)
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
      (* apply regmap_full_dom in Hrmap_init. *)
      (* rewrite /dom_arg_rmap Hrmap_init. *)
      admit.
      (* set_solver+. *)
    }
    { by rewrite /is_arg_rmap. }

    clear dependent wct1 wct0 warg0 warg1 rmap stk_mem_l stk_mem_h Hcsp_bounds.
    iNext.
    (* subst rmap'; clear stk_mem. *)
    iIntros (W6 rmap stk_mem_l stk_mem_h)
      "(%Hrelated_pub_5ext_W6 & %Hdom_rmap
      & Hna & #Hinterp_W6_csp & %Hcsp_bounds
      & Hsts_C & Hr_C & Hfrm_close_W6
      & Hcstk_frag & Hrel_stk_C'
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk_l & Hstk_h & HK)".
    iEval (cbn) in "HPC".

    (* ----- Revoke the world to get borrowed addresses back -----*)
    (* 1. Close the world *)
    iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
    iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
    iEval (rewrite <- (app_nil_r (finz.seq_between (csp_b ^+ 4)%a csp_e))) in "Hr_C".
    iAssert (
       [∗ list] a ; v ∈ finz.seq_between (csp_b ^+ 4)%a csp_e ; stk_mem_h, a ↦ₐ v ∗ closing_resources interp W6 C a v
      )%I with "[Hfrm_close_W6 Hstk_h]" as "Hfrm_close_W6".
    { rewrite /region_pointsto.
      iDestruct (big_sepL2_sep  with "[$Hstk_h $Hfrm_close_W6]") as "$".
    }
    iDestruct (region_close_list_interp_gen with "[$Hr_C $Hfrm_close_W6]"
      ) as "Hr_C".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { done. }
    rewrite -region_open_nil.

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
    focus_block_nochangePC 10 "Hcode_main" as a_ret Ha_ret "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace a_call_g2 with a_ret by solve_addr.

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iMod (inv_acc with "HawkN") as "(>(%b'' & Hst_i & Hcgp_b) & Hclose_awk)"; auto.
    iDestruct (sts_full_state_loc  with "Hsts_C Hst_i") as "%Hwst_i''".
    iDestruct (sts_full_rel_loc  with "Hsts_C Hsts_rel") as "%Hwrel_i''".
    iAssert ( ⌜ Forall (λ k : finz MemNum, W5.1 !! k = Some Revoked) (finz.seq_between (csp_b ^+ 4)%a csp_e) ⌝)%I
      as "%Hrevoked_stk_W5".
    { admit. (* derive from Hfrm_close_W5 *)
    }
    assert (related_sts_pub_world W5 W6) as Hrelated_pub_W5_W6.
    { clear -Hrelated_pub_5ext_W6 Hrevoked_stk_W5.
      eapply related_sts_pub_trans_world; eauto.
      eapply related_sts_pub_update_multiple_temp; eauto.
    }
    assert (loc W6 !! i = Some (encode true)); last simplify_eq.
    {
      clear - Hwrel_i_W5 Hwst_i' Hwst_i'' Hwrel_i'' Hrelated_pub_W5_W6.
      (* destruct W6 as [W6_loc W6_cus]. *)
      destruct Hrelated_pub_W5_W6 as [_ [Hdom1 [Hdom2 Htrans] ] ].
      specialize (Htrans i _ _ _ _ _ _ Hwrel_i_W5 Hwrel_i'') as [Heq1 [Heq2 [Heq3 Htrans] ] ]; eauto .
      assert (loc W5 !! i = Some (encode true)) by (by simplify_map_eq).
      specialize (Htrans _ _ H Hwst_i'').
      Set Nested Proofs Allowed.
     Lemma rtc_rel_pub y x :
     y = (encode true) ->
     rtc (convert_rel awk_rel_pub) y x ->
     x = (encode true).
   Proof.
     intros Heq Hrtc.
     induction Hrtc; auto.
     rewrite Heq in H.
     inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ].
     inversion Hy; subst; auto.
     apply encode_inj in Heq1. inversion Heq1.
   Qed.
   Lemma rtc_rel_pub' x :
     rtc (convert_rel awk_rel_pub) (encode true) (encode x) ->
     x = true.
   Proof.
     intros Hrtc.
     apply encode_inj.
     apply rtc_rel_pub with (encode true); auto.
   Qed.
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

    focus_block 11 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct2;ct3] as ["Hct2"; "Hct3"].
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ------------------ BLOCK 5: HALT ------------------ *)
    (* --------------------------------------------------- *)
    focus_block 5 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* JmpCap cra *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.


  Admitted.

  Lemma vae_awkward_safe

    (pc_b pc'_e pc'_a : Addr)
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
       b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+2)%a
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae ->
    Nassert ## Nvae ->
    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nvae
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a (vae_main_code ot_switcher))
    ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (switcher.encode_entry_point 1 (length VAE_main_code_init)))
    ∗ interp W C (WSealed ot_switcher C_f)
    ∗ WSealed ot_switcher C_f ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO Local b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ seal_pred ot_switcher ot_switcher_propC
    ∗ (∃ ι, inv ι (awk_inv C i cgp_b))
    ∗ sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_pub awk_rel_priv
      -∗
    interp W C
      (WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)).
  Proof.
    intros imports; subst imports.
    iIntros (Hswitcher_assert HNswitcher_vae HNassert_vae Hvae_size)
      "(#Hassert & #Hswitcher
      & #Hvae_code
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & #Hvae_exp_awkward
      & #Hinterp_W0_C_f
      & #HentryC_f & #Hentry_VAE & #Hentry_VAE' & #Hot_switcher
      & [%ι #Hι] & #Hsts_rel)".
    iEval (rewrite fixpoint_interp1_eq /=).
    rewrite /interp_sb.
    iFrame "Hot_switcher".
    iSplit; [iPureIntro; apply persistent_cond_ot_switcher |].
    iSplit; [iIntros (w); iApply mono_priv_ot_switcher|].
    iSplit; iNext ; iApply vae_awkward_spec; try iFrame "HentryC_f #"; eauto.
  Qed.

  Lemma vae_init_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher Nvae_code VAEN : namespace)

    (cstk : CSTK)
    :

    let imports :=
     vae_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
       b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+2)%a
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae_code ->
    Nassert ## Nvae_code ->

    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (vae_main_code ot_switcher))%a ->

    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W0) ->

    frame_match Ws Cs cstk W0 C ->
    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher switcher_inv
      ∗ na_inv logrel_nais Nvae_code
          ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a (vae_main_code ot_switcher))
      ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
      ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
      ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
          ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (switcher.encode_entry_point 1 (length VAE_main_code_init)))
      ∗ na_own logrel_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ vae_main_data ]]

      ∗ region W0 C ∗ sts_full_world W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W0 C (WCap RWL Local csp_b csp_e csp_b)

      ∗ WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a) ↦□ₑ 1
      ∗ WSealed ot_switcher (SCap RO Local b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a) ↦□ₑ 1
      ∗ seal_pred ot_switcher ot_switcher_propC

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert HNswitcher_vae HNassert_vae Hsize_vae_exp_tbl Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hframe_match
            )
      "(#Hassert & #Hswitcher
      & #Hvae
      & #Hvae_exp_tbl_PCC
      & #Hvae_exp_tbl_CGP
      & #Hvae_exp_tbl_awkward
      & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Hcgp_main
      & Hr_C & Hsts_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      & #Hentry_awkward & #Hentry_awkward'
      & #Hot_switcher
      )".
    iMod (na_inv_acc with "Hvae Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hvae_close)"; auto.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.
    (* --- Extract registers ca0 ct0 ct1 ct2 ct3 cs0 cs1 --- *)
    iExtractList "Hrmap" [cra;ca0;ct0;ct1;ct2;ct3;cs0;cs1]
      as ["Hcra"; "Hca0"; "Hct0"; "Hct1"; "Hct2"; "Hct3"; "Hcs0"; "Hcs1"].

    (* Extract the addresses of a *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

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
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_VAE_awkward Himports_main]".
    { transitivity (Some (pc_b ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }

    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l) "(%Hl_unk & Hsts_C & Hr_C & Hfrm_close_W0 & >[%stk_mem Hstk] & Hrevoked_l)".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_b]") as "%Hcgp_b_stk".
    set (W1 := revoke W0).

    (* --------------------------------------------------------------- *)
    (* ----------------- Start the proof of the code ----------------- *)
    (* --------------------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)
    rewrite /vae_main_code /VAE_main_code_init.
    replace
     ((encodeInstrsW [Store cgp 0] ++
                     fetch_instrs 3 ca0 cs0 cs1 ++
                     fetch_instrs 0 ct0 cs0 cs1 ++
                     fetch_instrs 2 ct1 cs0 cs1 ++ encodeInstrsW [Jalr cra ct0; Halt]) ++
                    VAE_main_code_f ot_switcher)
       with
      (encodeInstrsW [Store cgp 0] ++
                     fetch_instrs 3 ca0 cs0 cs1 ++
                     fetch_instrs 0 ct0 cs0 cs1 ++
                     fetch_instrs 2 ct1 cs0 cs1 ++ encodeInstrsW [Jalr cra ct0; Halt] ++
                    VAE_main_code_f ot_switcher) by auto.
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.

    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { solve_addr. }

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 to 3 : FETCH --------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode $Himport_VAE_awkward]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hcode & Himport_VAE_awkward)".
    iEval (cbn) in "Hca0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 3 "Hcode_main" as a_fetch3 Ha_fetch3 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch2.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcs0 $Hcs1 $Hcode $Himport_C_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hcs0 & Hcs1 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch3.
    (* Jalr cra ct0; *)
    iInstr "Hcode".


    (*  -- prove that the VAE_awkward entry point is safe-to-share -- *)

    (* -- separate argument registers -- *)
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5]
      as ["Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"].

    set ( rmap_arg :=
           {[ ca0 :=
                WSealed ot_switcher
                (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a);
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

    pose proof (revoke_related_sts_priv_world W0) as Hpriv_W0_W1.
    (* Show that the entry point to C_f is still safe in W1 *)
    iAssert (interp W1 C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply interp_monotone_sd; eauto. }
    iClear "Hinterp_W0_C_f".

    (* TODO alloc the invariant in the custom world *)
     iDestruct (sts_alloc_loc _ C false awk_rel_pub awk_rel_pub awk_rel_priv with "Hsts_C")
       as ">(Hsts & %Hloc_fresh & %Hcus_fresh & Hst_i & #Hrel_i)".
     set (i := (fresh_cus_name W1)).
    iDestruct (inv_alloc awkN _ (awk_inv C i cgp_b) with "[Hcgp_b Hst_i]") as ">#Hawk_inv".
    { iExists false; iFrame. }
    (* Show that the arguments are safe, when necessary *)
    iAssert (
        interp W1 C
          (WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a))
      )%I as "#Hinterp_VAE".
    { iApply (vae_awkward_safe pc_b pc_e pc_a cgp_b cgp_e b_vae_exp_tbl e_vae_exp_tbl b_assert
                e_assert a_flag C_f W1); try iFrame "#"; eauto.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W1 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W1 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    (* Prepare the closing resources for the switcher call spec *)
    iAssert (
        ([∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W1 C a ∗
                                                    ⌜W1.1 !! a = Some Revoked⌝)
      )%I with "[Hfrm_close_W0]" as "#Hfrm_close_W1".
    {
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a Ha) "[Hclose %Hrev]".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hvae_close" with "[$Hna Himport_assert Himport_switcher Himport_C_f Himport_VAE_awkward Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_VAE_awkward $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_C_f $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W1 $Hcstk_frag
              $Hinterp_W1_C_f $HentryC_f $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    clear dependent wca0 wct0 wct1 wct2 wct3 wcs0 wcs1.
    clear dependent wca1 wca2 wca3 wca4 wca5 rmap.
    iNext.
    iIntros (W2 rmap stk_mem_l stk_mem_h)
      "(%Hrelated_pub_W3ext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds
      & Hsts_C & Hr_C & Hfrm_close_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk_l & Hstk_h & HK)".
    iEval (cbn) in "HPC".

    (* Halt *)
    iMod (na_inv_acc with "Hvae Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hvae_close)"; auto.
    rewrite /vae_main_code /VAE_main_code_init.
    replace
     (encodeInstrsW [Store cgp 0] ++
                     fetch_instrs 3 ca0 cs0 cs1 ++
                     fetch_instrs 0 ct0 cs0 cs1 ++
                     fetch_instrs 2 ct1 cs0 cs1 ++ encodeInstrsW [Jalr cra ct0; Halt] ++
                    VAE_main_code_f ot_switcher)
       with
      (encodeInstrsW [Store cgp 0] ++
                     fetch_instrs 3 ca0 cs0 cs1 ++
                     fetch_instrs 0 ct0 cs0 cs1 ++
                     fetch_instrs 2 ct1 cs0 cs1
                     ++ encodeInstrsW [Jalr cra ct0 ]
                     ++ encodeInstrsW [Halt]
                     ++ VAE_main_code_f ot_switcher) by auto.
    focus_block 5 "Hcode_main" as a_callB' Ha_callB' "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iMod ("Hvae_close" with "[$Hna $Himports_main $Hcode_main]") as "Hna".
    wp_end; iIntros "_"; iFrame.
  Qed.

End VAE.
