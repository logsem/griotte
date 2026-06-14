From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel interp_weakening monotone.
From griotte Require Import fetch_spec assert_spec switcher interp_switcher_call switcher_spec_call switcher_spec_return.
From griotte Require Import vae vae_helper.
From griotte Require Import vae_spec_closure_blocks.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.

Section VAE.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma related_pub_W0_Wfixed (W0 W3 W6 : WORLD) (l : list Addr) (csp_b csp_e : Addr)
    (b : bool) (i : positive) :
    let W1 := revoke W0 in
    let W2 := <l[i:=false]l>W1 in
    let W4 := revoke W3 in
    let W5 := <l[i:=true]l>W4 in
    let W7 := revoke W6 in
    (* initial revocation W0 *)
    (∀ a : finz MemNum, std W0 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e) ->
    (* final revocation W7 *)
    Forall (λ a : finz MemNum, std W7 !! a = Some Revoked) (l ++ finz.seq_between csp_b csp_e)->
    (* world transition of the first call *)
    related_sts_pub_world W2 W3 ->
    (* world transition of the second call *)
    related_sts_pub_world W5 W6 ->
    (* custom invariant `i` in initial world W0 *)
    loc W1 !! i = Some (encode b) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (* custom invariant `i` in final world W7 *)
    loc W7 !! i = Some (encode true) ->
    wrel W7 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (* public transition between initial and fixed *)
    related_sts_pub_world W0 (close_list (l ++ finz.seq_between csp_b csp_e) W7).
  Proof.
    eapply awk_two_call_world_repair
      with (closing := l ++ finz.seq_between csp_b csp_e); eauto.
  Qed.

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
    ∗ WSealed ot_switcher (SCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a) ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO Local b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a) ↦□ₑ 1
    ∗ seal_pred ot_switcher ot_switcher_propC
    (* invariant for d *)
    ∗ (∃ ι, inv ι (awk_inv C i cgp_b))
    ∗ sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_priv
      -∗
    ot_switcher_prop W C (WCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a).
  Proof.
    intros imports.
    iIntros (Hswitcher_assert HNswitcher_vae HNassert_vae
               Hvae_exp_tbl_size Hvae_size_code Hvae_imports Hcgp_size Hloc_i_W Hrel_i_W)
      "(#Hassert & #Hswitcher
      & #Hvae_code
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & #Hvae_exp_awkward
      & #Hentry_VAE & #Hentry_VAE_borrow
      & #Hot_switcher
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
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.
    iDestruct (world_interp_rel_loc_valid  with "Hworld_interp_C Hsts_rel") as "%Hwrel_i_W0".
    assert (∃ b : bool, loc W0 !! i = Some (encode b)) as Hloc_i_W0.
    { destruct Hpriv_W_W0 as (_ & (?&_&Hpriv) & _).
      destruct Hloc_i_W.
      assert (is_Some (loc W0 !! i)) as [d Hloc_0] by (by apply elem_of_dom, H, elem_of_dom).
      specialize (Hpriv _ _ _ _ _ Hrel_i_W Hwrel_i_W0) as (_&_&Hpriv).
      specialize (Hpriv _ _ H0 Hloc_0).
      eapply awk_rel_inv in Hpriv; last done.
      destruct Hpriv as [? ->]. eexists; done.
    }

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

    (* Revoke the world to get the stack frame *)
    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜std W0 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_interp_C]")
        as (l
           ) "(%Hl_unk & Hworld_interp_C & #Hstack_revoked_W0 & >%Hstack_revoked_W0 & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelated_priv_W0_W1 by eapply revoke_related_sts_priv_world.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    rewrite /vae_main_code /VAE_main_code_init.
    rewrite -!app_assoc.
    rewrite /VAE_main_code_f.
    assert (SubBounds pc_b pc_e (pc_a ^+ length VAE_main_code_init)%a
              (pc_a ^+ length vae_main_code)%a).
    { solve_addr. }
    focus_block_nochangePC 4 "Hcode_main" as a_awkward Ha_awkward "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace (pc_b ^+ 24%nat)%a with a_awkward by solve_addr.

    (* Store false and update the matching custom-world location. *)
    iDestruct (world_interp_rel_loc_valid
      with "Hworld_interp_C Hsts_rel") as "%Hwrel_i".
    destruct Hloc_i_W0 as [b Hwst_i].
    change (loc W1 !! i = Some (encode b)) in Hwst_i.
    set (W2 := <l[i:=false]l>W1).
    assert (related_sts_priv_world W1 W2) as Hrelated_priv_W1_W2.
    { subst W2. eapply awk_loc_update_false_related_priv; eauto. }
    assert (related_sts_priv_world W0 W2) as Hrelated_priv_W0_W2
      by (eapply related_sts_priv_trans_world; eauto).
    assert (related_sts_priv_world W W2) as Hrelated_priv_W_W2
      by (eapply related_sts_priv_trans_world; eauto).
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by solve_addr.
    assert (revoke_condition W1) as Hrevoke_W1
      by apply revoke_conditions_sat.

    iApply (vae_awkward_store_flag_spec W1 C i false awkN
      pc_b pc_e a_awkward cgp_b cgp_e []
      with "[- $Hworld_interp_C $HPC $Hcgp $Hcode]"); eauto.
    iFrame "#∗".
    iNext; iIntros "(Hworld_interp_C & HPC & Hcgp & Hcode)".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 2 : FETCH ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 5 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_awkward.
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
    assert ((a_call_g1 + 5)%a = Some (a_call_g1 ^+ 5)%a)
      as Hcall_g1_end by solve_addr.
    iApply (vae_awkward_call1_prep_spec
      with "[- $HPC $Hcra $Hca0 $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iNext; iIntros
      "(HPC & Hcra & Hca0 & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcode)".

    set (rmap_arg := vae_call_adv_arg_rmap).

    iInsertList "Hrmap" [ct2;ct3].
    repeat (iEval (rewrite -delete_insert_ne //) in "Hrmap").
    set (rmap' := (delete ca5 _)).

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
      iApply (vae_call_adv_arg_rmap_resources W2 C Nswitcher
        with "[$Hswitcher $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hct0]").
    }

    (* Prepare the closing resources for the switcher call spec *)
    iDestruct (StackRevokedResources_mono_priv _ W2 with "Hstack_revoked_W0") as "Hstack_revoked_W2"; auto.
    assert ( revoked_addresses W2 (finz.seq_between csp_b csp_e) ) as Hstack_revoked_W2.
    { rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      subst W2 W1.
      cbn.
      by rewrite /revoked_addresses Forall_forall in Hstack_revoked_W0; eapply Hstack_revoked_W0.
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
              $Hstk $Hworld_interp_C $Hstack_revoked_W2 $Hcstk
              $Hinterp_W2_wct1 $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hrmap_init.
      rewrite /dom_arg_rmap Hrmap_init.
      set_solver+.
    }
    { apply vae_call_adv_arg_rmap_is_arg. }

    iClear "Hinterp_rmap Hzeroed_rmap".
    clear dependent wct1 wct0 wct2 wct3 wcs0 wcs1 rmap stk_mem.
    iNext.
    iIntros (W3 rmap stk_mem l')
      "( _ & _ & _ & %Hrelated_pub_2ext_W3 & Hrel_stk_C' & %Hdom_rmap & Hstack_revoked_W3 & %Hstack_revoked_W3
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
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
    rewrite !length_app /= in Ha_call_g1, Ha_awkward.
    assert ((a_call_g1 ^+ 5)%a = a_awkward) as Hcall_g1_addr.
    { pose proof (incr_addr_trans _ _ _ _ _ Ha_call_g1 Hcall_g1_end)
        as Hend.
      cbn in Hend. rewrite Ha_awkward in Hend.
      apply Some_inj in Hend. symmetry; exact Hend.
    }
    assert (AsWeakFinZIncr (a_call_g1 ^+ 5)%a a_awkward 0)
      as Hcall_g1_weak.
    { rewrite /AsWeakFinZIncr. solve_addr+Hcall_g1_addr. }
    replace (a_call_g1 ^+ 5)%a with a_awkward by
      exact (eq_sym Hcall_g1_addr).

    (* Store true; retain its public transition for the second call. *)
    iDestruct (world_interp_rel_loc_valid
      with "Hworld_interp_C Hsts_rel") as "%Hwrel_i'".
    (* The first callback may change [false] privately, but the relation
       invariant guarantees that the flag remains Boolean. *)
    assert (related_sts_priv_world W1 W4) as Hrelated_priv_W1_W4.
    { eapply related_sts_priv_trans_world; first exact Hrelated_priv_W1_W2.
      eapply related_sts_priv_trans_world.
      - by apply related_sts_pub_priv_world.
      - apply revoke_related_sts_priv_world. }
    destruct (awk_loc_is_bool_mono_priv W1 W4 i b
      Hrelated_priv_W1_W4 Hwst_i Hwrel_i) as [b' Hwst_i'].
    set (W5 := <l[i:=true]l>W4).
    assert (related_sts_pub_world W4 W5) as Hrelated_pub_W4_W5.
    { subst W5. eapply awk_loc_update_true_related_pub; eauto. }
    assert (related_sts_priv_world W3 W5) as Hrelated_priv_W3_W5.
    { eapply (related_sts_priv_pub_trans_world W3 W4); eauto.
      apply revoke_related_sts_priv_world. }
    assert (related_sts_priv_world W2 W5) as Hrelated_priv_W2_W5.
    { eapply related_sts_pub_priv_trans_world; eauto. }
    assert (ContiguousRegion a_awkward 1) as Hstore_true_contiguous
      by solve_addr.
    assert (SubBounds pc_b pc_e a_awkward (a_awkward ^+ 1)%a)
      as Hstore_true_subbounds by solve_addr.
    assert (related_sts_priv_world W4 W5) as Hrelated_priv_W4_W5
      by (apply related_sts_pub_priv_world; exact Hrelated_pub_W4_W5).
    assert (revoke_condition W4) as Hrevoke_W4
      by apply revoke_conditions_sat.
    iEval (rewrite Hcall_g1_addr) in "HPC".
    iApply (vae_awkward_store_flag_spec W4 C i true awkN
      pc_b pc_e a_awkward cgp_b cgp_e
      [Mov cra cs0; Mov ct1 cs1]
      with "[- $Hworld_interp_C $HPC $Hcgp $Hcode]"); eauto.
    iFrame "#∗".
    iNext; iIntros "(Hworld_interp_C & HPC & Hcgp & Hcode)".

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
    assert (ContiguousRegion a_call_g2 4) as Hcall2_contiguous by solve_addr.
    assert (SubBounds pc_b pc_e a_call_g2 (a_call_g2 ^+ 4)%a)
      as Hcall2_subbounds by solve_addr.
    iApply (vae_awkward_call2_prep_spec pc_b pc_e a_call_g2 _ _ _ _
      [Load ct0 cgp; Mov ct1 1]
      with "[- $HPC $Hcra $Hca0 $Hca1 $Hct0 $Hcs0 $Hcode]"); eauto.
    iNext; iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct0 & Hcs0 & Hcode)".

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
    set (rmap_arg := vae_call_adv_arg_rmap).
    set (rmap' := (delete ca5 _)).


    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg , rarg ↦ᵣ warg ∗ interp W5 C warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iApply (vae_call_adv_arg_rmap_resources W5 C Nswitcher
        with "[$Hswitcher $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hct0]").
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
    iDestruct (StackRevokedResources_mono_priv _ W5 with "Hstack_revoked_W3") as "Hstack_revoked_W5"; auto.
    assert ( revoked_addresses W5 (finz.seq_between csp_b csp_e) ) as Hstack_revoked_W5.
    { rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      subst W5 W4.
      cbn.
      by rewrite /revoked_addresses Forall_forall in Hstack_revoked_W3; eapply Hstack_revoked_W3.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hvae_code_close" with "[$Hna Himport_switcher Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    iDestruct (world_interp_rel_loc_valid  with "Hworld_interp_C Hsts_rel") as "%Hwrel_i_W5".
    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W5 $Hcstk_frag
              $Hinterp_W5_wca0 $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hdom_rmap.
      set_solver+.
    }
    { apply vae_call_adv_arg_rmap_is_arg. }

    clear dependent wct1 wct0 warg0 warg1 rmap stk_mem Hcsp_bounds.
    iNext.
    iIntros (W6 rmap stk_mem l')
      "(_ & _ & _ & %Hrelated_pub_5ext_W6 & Hrel_stk_C'' & %Hdom_rmap & Hstack_revoked_W6 & %Hstack_revoked_W6
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)"; clear l'.
    iEval (cbn) in "HPC".

    (* Derive some information necessary later *)
    iAssert ( ⌜ revoked_addresses W5 (finz.seq_between (csp_b ^+ 4)%a csp_e)⌝)%I
      as "%Hrevoked_stk_W5".
    { iPureIntro.
      rewrite /revoked_addresses Forall_forall.
      intros x Hx.
      assert (x ∈ finz.seq_between csp_b csp_e) as Hx'.
      {
        rewrite (finz_seq_between_split csp_b (csp_b ^+ 4)%a csp_e); last solve_addr.
        rewrite elem_of_app; by right.
      }
      by rewrite /revoked_addresses Forall_forall in Hstack_revoked_W5 ; apply Hstack_revoked_W5.
    }
    assert (related_sts_pub_world W5 W6) as Hrelated_pub_W5_W6.
    { clear -Hrelated_pub_5ext_W6 Hrevoked_stk_W5.
      eapply related_sts_pub_trans_world; eauto.
      eapply related_sts_pub_update_multiple_temp; eauto.
    }
    clear Hrevoked_stk_W5.

    iAssert (⌜ Forall (λ a : finz MemNum, a ∈ dom (std W6)) l ⌝)%I as "%Hl_revoked_W6".
    {
      iPureIntro; apply Forall_forall; intros a Ha.
      rewrite /revoked_addresses Forall_forall in Hrevoked_l.
      apply Hrevoked_l in Ha.
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
       world_interp_revoked_by_separation_many_with_RevokedResources with "[$Hworld_interp_C $Hrevoked_l]"
      ) as "(Hworld_interp_C & Hrevoked_l & %Hl_revoked_W7)".
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

    focus_block_nochangePC 9 "Hcode_main" as a_ret Ha_ret "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_call_g2 = a_ret) as Hcall2_ret by solve_addr.
    iEval (rewrite Hcall2_ret) in "HPC".
    assert (loc W5 !! i = Some (encode true)) as Hwst_i_W5.
    { subst W5. by simplify_map_eq. }
    assert (SubBounds pc_b pc_e a_ret (a_ret ^+ 6)%a)
      as Hload_subbounds by solve_addr.
    iApply (vae_awkward_flag_load_spec W5 W6 C i awkN
      pc_b pc_e a_ret cgp_b cgp_e _ _
      with "[- $Hworld_interp_C $HPC $Hcgp $Hct0 $Hct1 $Hcode]"); eauto.
    iFrame "#∗".
    iNext; iIntros
      "(Hworld_interp_C & HPC & Hcgp & Hct0 & Hct1 & Hcode)".
    pose proof (awk_loc_true_mono_pub W5 W6 i Hrelated_pub_W5_W6
      Hwst_i_W5 Hwrel_i_W5) as Hwst_i_W6.
    assert (loc W7 !! i = Some (encode true)) as Hwst_i_W7.
    { subst W7. exact Hwst_i_W6. }
    iDestruct (world_interp_rel_loc_valid
      with "Hworld_interp_C Hsts_rel") as "%Hwrel_i_W7".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 10 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct2;ct3;ct4;cnull] as ["Hct2"; "Hct3";"Hct4";"Hcnull"].
    iApply (assert_success_spec
             with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]") ; auto.
    { apply withinBounds_true_iff; solve_addr. }
    { solve_ndisj. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 5: RETURN ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 11 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (vae_awkward_return_prep_spec pc_b pc_e a_halt _ _ _ _
      with "[- $HPC $Hcra $Hcs0 $Hca0 $Hca1 $Hcnull $Hcode]"); eauto.
    iNext; iIntros
      "(HPC & Hcra & Hcs0 & Hca0 & Hca1 & Hcnull & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hvae_code_close" with "[$Hna Himport_switcher Himport_assert Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
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
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }

    iApply (switcher_ret_specification _ W0 W7
             with
             "[ $Hswitcher $Hstk $Hcstk_frag $HK $Hworld_interp_C $Hna $HPC $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ); auto.
    { destruct Hl_unk as [_ ?].
      eapply (related_pub_W0_Wfixed W0 W3 W6 l); eauto.
      apply Forall_app; split; auto.
    }
    { repeat (rewrite dom_insert_L); rewrite Hdom_rmap; set_solver+. }
    { subst csp_b.
      destruct Hsync_csp as [Hcsp_sync Hcsp_base].
      rewrite -Hcsp_base; auto.
    }
    { destruct Hl_unk; auto. }
    { intros a; destruct Hl_unk as [_ Hl_unk]; destruct (Hl_unk a); auto. }
    { iSplit; iApply interp_int. }
  Qed.


End VAE.
