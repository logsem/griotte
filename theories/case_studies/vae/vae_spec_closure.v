From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import rules logrel logrel_extra monotone proofmode register_tactics.
From cap_machine Require Import fetch assert interp_switcher_call switcher_spec_call switcher_spec_call_alt switcher_spec_return.
From cap_machine Require Import vae vae_helper.

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

  Lemma related_pub_W0_Wfixed (W0 W3 W6 : WORLD) (csp_b csp_e : Addr) (l : list Addr) ( i : positive) :
    let W1 := revoke W0 in
    let W2 := <l[i:=false]l>W1 in
    let W4 := revoke W3 in
    let W5 := <l[i:=true]l>W4 in
    let W7 := (revoke W6) in
    (∀ a : finz MemNum, W0.1 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e) ->
    related_sts_pub_world W2 W3 ->
    related_sts_pub_world
      (std_update_multiple W2 (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) W3 ->
    related_sts_pub_world W5 W6 ->
    related_sts_pub_world
      (std_update_multiple W5 (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) W6 ->
    Forall (λ a : finz MemNum, W6.1 !! a = Some Revoked) l ->
    Forall (λ a : finz MemNum, W6.1 !! a = Some Revoked) (finz.seq_between csp_b (csp_b ^+ 4)%a) ->
    finz.seq_between csp_b csp_e = finz.seq_between csp_b (csp_b ^+ 4)%a ++ finz.seq_between (csp_b ^+ 4)%a csp_e ->
    wrel W6 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    loc W6 !! i = Some (encode true) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (exists b : bool, loc W0 !! i = Some (encode b)) ->

    related_sts_pub_world W0
      (close_list (l ++ finz.seq_between csp_b csp_e) W7).
  Proof.
    intros W1 W2 W4 W5 W7.
    intros Htemporaries_W0 Hrelated_pub_W2_W3 Hrelated_pub_W2ext_W3 Hrelated_pub_W5_W6 Hrelated_pub_W5ext_W6
      HW6_revoked_l Hrevoked_stk_l Hsplit_csp Hwrel_i Hwloc_i Hwrel_i_0 Hwloc_i_0.

    assert ( related_sts_priv_world W0 W6 ) as Hrelated_priv_W0_W6.
    { eapply (related_sts_priv_trans_world _ W3); eauto.
      + eapply (related_sts_priv_pub_trans_world _ W2); eauto.
        subst W2 W1.
        eapply (related_sts_priv_trans_world _ (revoke W0)).
        * apply revoke_related_sts_priv_world.
        * destruct Hwloc_i_0 as [b Hwloc_i_0].
          eapply related_sts_priv_world_loc_update; eauto.
          right; apply convert_rel_of_rel; done.
      + eapply (related_sts_priv_pub_trans_world _ W5); eauto.
        subst W4 W5.
        eapply (related_sts_priv_trans_world _ (revoke W3)).
        * apply revoke_related_sts_priv_world.
        *
          destruct Hrelated_pub_W2_W3 as [HW2_W3_std (Hdom_loc_2_3 & Hdom_rel_2_3 & Hrtc_loc_2_3)].
          assert (∃ d_W3, loc W3 !! i = Some d_W3) as [d_W3 Hd_W3].
          { apply elem_of_dom.
            apply Hdom_loc_2_3.
            rewrite dom_insert.
            rewrite elem_of_union; right.
            apply elem_of_dom.
            set_solver+Hwloc_i_0.
          }
          assert (∃ r1 r2 , wrel W3 !! i = Some (r1, r2)) as (rpub & rpriv  & HW3_rel).
          { assert (is_Some (wrel W0 !! i)) as HW0_rel_some by set_solver+Hwrel_i_0.
            apply elem_of_dom in HW0_rel_some.
            apply Hdom_rel_2_3 in HW0_rel_some.
            apply elem_of_dom in HW0_rel_some as [ [] ].
            eexists _,_; eauto.
          }
          destruct Hwloc_i_0 as [b Hwloc_i_0].
          specialize (Hrtc_loc_2_3 i  _ _ _ _ Hwrel_i_0 HW3_rel) as (<- & <- & Hrtc_loc_0_3).
          ospecialize (Hrtc_loc_0_3 _ _ _ Hd_W3); first by simplify_map_eq.
          eapply awk_rel_pub_inv in Hrtc_loc_0_3 as [b' ->]; last done.
          eapply related_sts_priv_world_loc_update; eauto.
          right; apply convert_rel_of_rel; done.
    }
    split; cbn; cycle 1.
    - destruct W0 as [W0_std [W0_loc W0_rel] ],
                 W3 as [W3_std [W3_loc W3_rel] ],
                   W6 as [W6_std [W6_loc W6_rel] ]
                   ; cbn.
      destruct Hrelated_pub_W2_W3 as [HW2_W3_std HW2_W3_cus].
      destruct Hrelated_pub_W5_W6 as [HW5_W6_std HW5_W6_cus].
      destruct Hrelated_priv_W0_W6 as [HW0_W6_std HW0_W6_cus].
      destruct HW0_W6_cus as (Hdom_loc_0_6 & Hdom_rel_0_6 & Hrtc_loc_0_6); cbn in *.
      split;[|split];auto.
      intros d rpub rpriv rpub' rpriv' HW0_rel HW6_rel.
      specialize (Hrtc_loc_0_6 d _ _ _ _ HW0_rel HW6_rel) as (-> & -> &  Hrtc_loc_0_6).
      repeat (split;first done).
      intros d_W0 d_W6 Hd_W0 Hd_W6.
      destruct HW2_W3_cus as (Hdom_loc_2_3 & Hdom_rel_2_3 & Hrtc_loc_2_3); cbn in *.
      assert (∃ d_W3, W3_loc !! d = Some d_W3) as [d_W3 Hd_W3].
      { apply elem_of_dom.
        apply Hdom_loc_2_3.
        rewrite dom_insert.
        rewrite elem_of_union; right.
        apply elem_of_dom.
        set_solver+Hd_W0.
      }
      assert (∃ r1 r2 , W3_rel !! d = Some (r1, r2)) as (rpub & rpriv & HW3_rel).
      { assert (is_Some (W0_rel !! d)) as HW0_rel_some by set_solver+HW0_rel.
        apply elem_of_dom in HW0_rel_some.
        apply Hdom_rel_2_3 in HW0_rel_some.
        apply elem_of_dom in HW0_rel_some as [ [] HW3_rel].
        eexists _,_; eauto.
      }

      destruct (decide (d = i)); simplify_eq.
      + destruct Hwloc_i_0 as [b Hwloc_i_0]; simplify_eq.
        apply rtc_once.
        destruct HW5_W6_cus as (Hdom_loc_5_6 & Hdom_rel_5_6 & Hrtc_loc_5_6); cbn in *.
        apply convert_rel_of_rel.
        by right.
      + eapply (rtc_transitive d_W0 d_W3 d_W6).
        * specialize (Hrtc_loc_2_3 d _ _ _ _ HW0_rel HW3_rel) as (-> & -> & Hrtc_loc_0_3).
          ospecialize (Hrtc_loc_0_3 d_W0 d_W3 _ Hd_W3).
          { by simplify_map_eq. }
          done.
        * destruct HW5_W6_cus as (Hdom_loc_5_6 & Hdom_rel_5_6 & Hrtc_loc_5_6); cbn in *.
          specialize (Hrtc_loc_5_6 d _ _ _ _ HW3_rel HW6_rel) as (-> & -> & Hrtc_loc_5_6).
          ospecialize (Hrtc_loc_5_6 d_W3 d_W6 _ Hd_W6).
          { by simplify_map_eq. }
          done.
    - cbn in *.
      split.
      {
        intros a Ha.
        rewrite elem_of_dom -close_list_std_sta_is_Some -revoke_std_sta_lookup_Some -elem_of_dom.
        destruct Hrelated_pub_W5_W6 as [ [Hdom_W5_W6 _] _].
        apply Hdom_W5_W6.
        rewrite -revoke_dom_eq.
        destruct Hrelated_pub_W2_W3 as [ [Hdom_W2_W3 _] _].
        apply Hdom_W2_W3.
        by rewrite -revoke_dom_eq.
      }
      intros a ρ0 ρ2 Ha0 Ha2.
      destruct ρ0; cycle 1.
      + (* the initial a was in the Permanent state *)
        assert (a ∉ l ++ finz.seq_between csp_b csp_e) as Ha_notin.
        { destruct (Htemporaries_W0 a) as [_ ?].
          intro Hcontra; apply H in Hcontra. by rewrite Ha0 in Hcontra.
        }
        apply revoke_lookup_Perm in Ha0.
        assert (std W3 !! a = Some Permanent) as Ha0_W3.
        { rewrite (region_state_pub_perm W2); eauto. }
        assert (std W6 !! a = Some Permanent) as Ha0_W6.
        { rewrite (region_state_pub_perm W5); eauto.
          subst W5. cbn.
          rewrite revoke_lookup_Perm; eauto.
        }
        rewrite -close_list_std_sta_same in Ha2; eauto.
        apply revoke_lookup_Perm in Ha0_W6.
        simplify_map_eq.
        apply rtc_refl.
      + (* the initial a was in the Revoked state *)
        destruct ρ2; last apply rtc_refl; apply rtc_once; constructor.
      + (* the initial a was in the Temporary state *)
        assert (a ∈ l ++ finz.seq_between csp_b csp_e) as Ha_in.
        { destruct (Htemporaries_W0 a) as [? _]; by apply Htemporaries_W0. }
        apply revoke_lookup_Monotemp in Ha0.
        assert (std W1 !! a = Some Revoked) as Ha0_W1.
        { done. }
        assert (std W2 !! a = Some Revoked) as Ha0_W2.
        { done. }
        assert (
            std ((std_update_multiple W2 (finz.seq_between (csp_b ^+ 4)%a csp_e)
                    Temporary)) !! a =
            Some (if (decide (a ∈ (finz.seq_between (csp_b ^+ 4)%a csp_e)))
                  then Temporary
                  else Revoked
          )).
        {
          destruct (decide (a ∈ (finz.seq_between (csp_b ^+ 4)%a csp_e))) as [Ha_in_stk | Ha_in_stk].
          + apply std_sta_update_multiple_lookup_in_i; eauto.
          + rewrite std_sta_update_multiple_lookup_same_i; eauto.
        }

        destruct (decide (a ∈ finz.seq_between (csp_b ^+ 4)%a csp_e)) as [Ha_in''|Ha_in''].
        * assert (std W3 !! a = Some Temporary) as Ha0_W3.
          { eapply region_state_pub_temp; eauto. }
          assert (std W4 !! a = Some Revoked) as Ha0_W4.
          { by apply revoke_lookup_Monotemp. }
          assert (std W5 !! a = Some Revoked) as Ha0_W5 by done.
          assert (
              std (std_update_multiple W5 (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) !! a = Some Temporary
            ) as Ha0_W5ext.
          { apply std_sta_update_multiple_lookup_in_i; eauto. }
          assert (std W6 !! a = Some Temporary) as Ha0_W6.
          { eapply region_state_pub_temp; eauto. }
          assert (std W7 !! a = Some Revoked) as Ha0_W7.
          { by apply revoke_lookup_Monotemp. }
          eapply (close_list_std_sta_revoked _ _ _  Ha_in) in Ha0_W7; eauto.
          rewrite Ha2 in Ha0_W7; simplify_eq.
          apply rtc_refl.
        * destruct (decide (a ∈ finz.seq_between csp_b (csp_b ^+ 4)%a)) as [Ha_in_save|Ha_in_save].
          ** rewrite Forall_forall in Hrevoked_stk_l.
             apply Hrevoked_stk_l in Ha_in_save.
             apply revoke_lookup_Revoked in Ha_in_save.
             eapply (close_list_std_sta_revoked _ _ _  Ha_in) in Ha_in_save; eauto.
             rewrite Ha2 in Ha_in_save; simplify_eq.
             apply rtc_refl.
          ** assert (a ∈ l) as Ha_in_l.
             { rewrite Hsplit_csp in Ha_in.
               rewrite elem_of_app in Ha_in.
               destruct Ha_in; first done.
               rewrite elem_of_app in H0.
               destruct H0; contradiction.
             }
             rewrite Forall_forall in HW6_revoked_l.
             apply HW6_revoked_l in Ha_in_l.
             apply revoke_lookup_Revoked in Ha_in_l.
             eapply (close_list_std_sta_revoked _ _ _  Ha_in) in Ha_in_l; eauto.
             rewrite Ha2 in Ha_in_l; simplify_eq.
             apply rtc_refl.
  Qed.

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
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (switcher.encode_entry_point 1 (length (imports ++ VAE_main_code_init))))
    ∗ WSealed ot_switcher (SCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
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
    iIntros "!> %rmap %cstk %Ws %Cs %W0 %Hpriv_W_W0 !> %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hr_C & Hsts_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.
    iDestruct (sts_full_rel_loc  with "Hsts_C Hsts_rel") as "%Hwrel_i_W0".
    assert (∃ b : bool, loc W0 !! i = Some (encode b)) as Hloc_i_W0.
    { destruct Hpriv_W_W0 as [_ (?&_&Hpriv) ].
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
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l) "(%Hl_unk & Hsts_C & Hr_C & #Hfrm_close_W0 & >[%stk_mem Hstk] & Hrevoked_l)".

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    rewrite /vae_main_code /VAE_main_code_init.
    rewrite -!app_assoc.
    rewrite /VAE_main_code_f.
    assert (SubBounds pc_b pc_e (pc_a ^+ length VAE_main_code_init)%a
              (pc_a ^+ length (vae_main_code ot_switcher))%a).
    { solve_addr. }
    focus_block_nochangePC 4 "Hcode_main" as a_awkward Ha_awkward "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace (pc_b ^+ 24%nat)%a with a_awkward by solve_addr.

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
    assert (related_sts_priv_world W1 W2) as Hpriv_W1_W2.
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
      )%I with "[Hfrm_close_W0]" as "#Hfrm_close_W2".
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

    assert (related_sts_priv_world W2 W5) as Hpriv_W2_W5.
    { eapply related_sts_pub_priv_trans_world; eauto.
      eapply (related_sts_priv_pub_trans_world W3 W4); eauto.
      apply revoke_related_sts_priv_world.
    }

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
      )%I with "[Hfrm_close_W2 Hfrm_close_W3]" as "#Hfrm_close_W5".
    { rewrite !big_sepL_sep.
      rewrite (finz_seq_between_split csp_b (csp_b ^+ 4)%a csp_e); last solve_addr.
      iDestruct "Hfrm_close_W2" as "[Hclose_W2 Hrev_W2]".
      iEval (rewrite big_sepL_app) in "Hclose_W2".
      iEval (rewrite big_sepL_app) in "Hrev_W2".
      iDestruct "Hclose_W2" as "[Hclose_W2 _]".
      iDestruct "Hrev_W2" as "[Hrev_W2 _]".
      iDestruct "Hfrm_close_W3" as "[Hclose_W3 Hrev_W3]".
      iSplitL "Hclose_W2 Hclose_W3".
      - rewrite big_sepL_app.
        iSplitL "Hclose_W2".
        + iApply (big_sepL_impl with "Hclose_W2").
          iModIntro; iIntros (k a Ha) "Hclose'".
          iApply mono_priv_closing_revoked_resources; eauto.
        + iApply (big_sepL_impl with "Hclose_W3").
          iModIntro; iIntros (k a Ha) "Hclose_".
          iApply mono_priv_closing_revoked_resources.
          { apply related_sts_pub_priv_world; eapply Hpriv_W4_W5. }
          iApply mono_priv_closing_revoked_resources; eauto.
          by apply revoke_related_sts_priv_world.
      - iApply big_sepL_app.
        iFrame "#".
        iApply big_sepL_pure; iPureIntro.
        intros k x Hk.
        cbn.
        apply revoke_lookup_Revoked.
        apply Hstk_l_revoked .
        apply elem_of_list_lookup.
        set_solver+Hk.
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

    iAssert (⌜ Forall (λ a : finz MemNum, a ∈ dom W5.1) l ⌝)%I as "%Hrevoked_l_W".
    {
      iDestruct (big_sepL_sep with "Hrevoked_l") as "[_ %Hrevoked_l]".
      iPureIntro; apply Forall_forall; intros a Ha.
      apply elem_of_list_lookup in Ha as [k Hk].
      apply Hrevoked_l in Hk.
      cbn.
      rewrite -revoke_dom_eq.
      assert (a ∈ dom (std W2)) as Ha2.
      { rewrite elem_of_dom; done. }
      destruct Hrelated_pub_W2_W3 as [ [Hdom_2_3 _] _ ].
      by apply Hdom_2_3.
    }
    iMod (
       revoked_by_separation_many_with_temp_resources with "[$Hsts_C $Hr_C $Hrevoked_l]"
      ) as "(Hrevoked_l & Hsts_C & Hr_C & %HW2_revoked_l)".
    { apply Forall_forall; intros a Ha.
      rewrite Forall_forall in Hrevoked_l_W.
      apply Hrevoked_l_W in Ha.
      destruct Hrelated_pub_W5_W6 as [ [Hdom _ ] _].
      by apply Hdom.
    }

    iDestruct (big_sepL_sep with "Hfrm_close_W5") as "[_ %Hrevoked_stk]".
    iMod (
       revoked_by_separation_many with "[$Hsts_C $Hr_C $Hstk_l]"
      ) as "(Hsts_C & Hr_C & Hstk_l & %Hrevoked_stk_l)".
    { apply Forall_forall; intros x Hx.
      destruct Hrelated_pub_W5_W6 as [ [Hdom _ ] _].
      apply Hdom.
      subst W1.
      rewrite elem_of_dom.
      assert (x ∈ finz.seq_between csp_b csp_e) as Hx'.
      { rewrite !elem_of_finz_seq_between in Hx |- *.
        solve_addr+Hcsp_bounds Hx.
      }
      apply elem_of_list_lookup in Hx' as [? Hx'].
      eexists; eapply Hrevoked_stk; eauto.
    }

    (* Revoke the world again to get the points-to of the stack *)
    iMod (monotone_revoke_stack_alt with "[$Hinterp_W6_csp $Hsts_C $Hr_C]")
        as (l'') "(%Hl_unk'' & Hsts_C & Hr_C & Hfrm_close_W6 & >[%stk_mem Hstk] & Hrevoked_l'')".
    iDestruct (region_pointsto_split with "[$Hstk_l $Hstk]") as "Hstk"; auto.
    { solve_addr+Hcsp_bounds. }
    { by rewrite finz_seq_between_length in Hlen_stk_l. }
    set (W7 := revoke W6).

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

    iApply (switcher_ret_specification _ W0 W7
             with
             "[ $Hswitcher $Hstk $Hcstk_frag $HK $Hsts_C $Hna $HPC $Hr_C $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ); auto.
    { eapply (related_pub_W0_Wfixed W0 W3 W6); eauto.
      + destruct Hl_unk; auto.
      + apply finz_seq_between_split; solve_addr+Hcsp_bounds.
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
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (switcher.encode_entry_point 1 (length (imports ++ VAE_main_code_init))))
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
