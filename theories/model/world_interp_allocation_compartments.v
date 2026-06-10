From iris.proofmode Require Import proofmode.
From cap_machine Require Export region_invariants sts_multiple_updates.
From cap_machine Require Import logrel interp_weakening.
From cap_machine Require Import switcher.
From cap_machine Require Import compartment_layout mkregion_helpers disjoint_regions_tactics.
From cap_machine Require Import world_ghost_theory.
From cap_machine Require Import stdpp_extra.

Section region_alloc_cmpt.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Definition std_update_compartment (W : WORLD) (C_cmpt : cmpt) :=
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let Wcode := std_update_multiple W code_addrs Permanent in
    let Wdata := std_update_multiple Wcode data_addrs Permanent in
    std_update_multiple Wdata imports_addrs Permanent.

  Lemma std_update_compartment_pub (W : WORLD) (C_cmpt : cmpt) :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    Forall (λ k, std W !! k = None) imports_addrs →
    Forall (λ k, std W !! k = None) code_addrs →
    Forall (λ k, std W !! k = None) data_addrs →
    related_sts_pub_world W (std_update_compartment W C_cmpt).
  Proof.
    intros * Himports Hcode Hdata.
    rewrite !Forall_forall in Himports, Hcode, Hdata.
    set (W2 := std_update_multiple W (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt)) Permanent).
    assert (related_sts_pub_world W W2) as Hrelated_pub_W_W2.
    { apply related_sts_pub_update_multiple.
      apply Forall_forall.
      intros a Ha.
      by apply Hcode in Ha; rewrite -not_elem_of_dom in Ha.
    }
    set (W3 := std_update_multiple W2 (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)) Permanent).
    assert (related_sts_pub_world W2 W3) as Hrelated_pub_W2_W3.
    { apply related_sts_pub_update_multiple.
      apply Forall_forall.
      intros a Ha.
      assert (a ∉ dom W.1)
        as Hadom by (by apply Hdata in Ha; rewrite -not_elem_of_dom in Ha).
      subst W2.
      intro Ha'.
      apply elem_of_dom_std_multiple_update in Ha' as [Ha' | Ha']; last done.
      pose proof (cmpt_cgp_disjoint C_cmpt) as Hdisjoint.
      apply map_disjoint_dom_1 in Hdisjoint.
      rewrite /cmpt_pcc_mregion dom_union_L in Hdisjoint.
      rewrite disjoint_union_l in Hdisjoint.
      destruct Hdisjoint as [_ Hdisjoint].
      pose proof (cmpt_data_size C_cmpt) as Hsize_data.
      pose proof (cmpt_code_size C_cmpt) as Hsize_code.
      rewrite !dom_mkregion_eq in Hdisjoint; auto.
      apply list_to_set_disj_2 in Hdisjoint.
      rewrite /disjoint /set_disjoint_instance in Hdisjoint.
      apply (Hdisjoint a); auto.
    }
    set (W4 := std_update_multiple W3 (finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt))
                 Permanent).
    assert (Forall (fun a => a ∉ dom (std W3))
              (finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt))) as Himports_W3.
    { apply Forall_forall; intros a Ha; cbn.
      assert (a ∉ dom W.1)
        as Hadom by (by apply Himports in Ha; rewrite -not_elem_of_dom in Ha).
      rewrite not_elem_of_dom.
      pose proof (cmpt_import_size C_cmpt) as H.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      2: {
        pose proof (cmpt_cgp_disjoint C_cmpt) as Hdisjoint.
        apply map_disjoint_dom_1 in Hdisjoint.
        rewrite /cmpt_pcc_mregion dom_union_L in Hdisjoint.
        rewrite disjoint_union_l in Hdisjoint.
        destruct Hdisjoint as [H1 _].
        pose proof (cmpt_data_size C_cmpt) as Hsize_data.
        pose proof (cmpt_import_size C_cmpt) as Hsize_imports.
        pose proof (cmpt_code_size C_cmpt) as Hsize_code.
        rewrite !dom_mkregion_eq in H1; auto.
        apply list_to_set_disj_2 in H1.
        apply H1 in Ha; eauto.
      }
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      {  pose proof (cmpt_code_disjoint C_cmpt) as Hdis.
         apply map_disjoint_dom_1 in Hdis.
        pose proof (cmpt_import_size C_cmpt) as Hsize_imports.
        pose proof (cmpt_code_size C_cmpt) as Hsize_code.
        rewrite !dom_mkregion_eq in Hdis; auto.
        apply list_to_set_disj_2 in Hdis.
        apply Hdis in Ha; eauto.
      }
    }
    assert (related_sts_pub_world W3 W4) as Hrelated_pub_W3_W4.
    { apply related_sts_pub_update_multiple; auto. }
    eapply related_sts_pub_trans_world; eauto.
    eapply related_sts_pub_trans_world; eauto.
  Qed.

  Lemma switcher_cmpt_disjoint_std_update_compartment
    (W : WORLD) (C_cmpt : cmpt) (switcher_cmpt : cmptSwitcher) (a : Addr) :
    a ∈ finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt) ->
    switcher_cmpt_disjoint C_cmpt switcher_cmpt ->
    std W !! a = None ->
    std (std_update_compartment W C_cmpt) !! a = None.
  Proof.
    intros Ha Hc Ha_W.
    pose proof (cmpt_import_size C_cmpt) as H.
    pose proof (cmpt_code_size C_cmpt) as H'.
    rewrite std_sta_update_multiple_lookup_same_i.
    2: {
      intro Hcontra.
      assert (a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)).
      {
        apply elem_of_finz_seq_between.
        apply elem_of_finz_seq_between in Hcontra.
        solve_addr+H H' Hcontra.
      }
      apply (Hc a).
      + rewrite /cmpt_switcher_region.
        eapply elem_of_union;eauto.
      + eapply elem_of_union;eauto.
        left; eapply elem_of_union;eauto.
    }
    rewrite std_sta_update_multiple_lookup_same_i.
    2: { intro Hcontra.
         (* admit. *)
         apply (Hc a); eauto.
         + rewrite /cmpt_switcher_region.
           eapply elem_of_union;eauto.
         + eapply elem_of_union;eauto.
           left;eapply elem_of_union;eauto.
    }
    rewrite std_sta_update_multiple_lookup_same_i; first done.
    intro Hcontra.
    apply (Hc a); eauto.
    + rewrite /cmpt_switcher_region. eapply elem_of_union;eauto.
    + eapply elem_of_union;eauto.
      left;eapply elem_of_union;eauto.
      left.
      rewrite !elem_of_finz_seq_between in Hcontra |- *.
      solve_addr+H H' Hcontra.
  Qed.

  Lemma alloc_compartment_interp_rel {E : coPset} (W : WORLD) ( C_cmpt : cmpt ) (C : CmptName)  :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in
    let Wfinal := std_update_compartment W C_cmpt in

    Forall (λ k, std W !! k = None) imports_addrs →
    Forall (λ k, std W !! k = None) code_addrs →
    Forall (λ k, std W !! k = None) data_addrs →

    Forall (λ w : Word, is_z w) (cmpt_code C_cmpt) ->
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) ->

    ([∗ list] k;v ∈ imports_addrs ; cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; cmpt_data C_cmpt, k ↦ₐ v) -∗

    (
      (
        ([∗ list] k ∈ (imports_addrs++code_addrs), rel C k RX interpC)
        ∗ ([∗ list] k ∈ (data_addrs), rel C k RW interpC)
      )
      -∗
      ([∗ list] v ∈ cmpt_imports C_cmpt, interpC (Wfinal, C, v) ∗ future_priv_mono C interpC v)
    ) -∗

    world_interp W C

    ={E}=∗

    world_interp Wfinal C
    ∗ interp Wfinal C pcc_cap
    ∗ interp Wfinal C cgp_cap
    ∗ ([∗ list] v ∈ cmpt_imports C_cmpt, interp Wfinal C v)
  .
  Proof.
    intros * Himports Hcode Hdata C_code C_data.

    iIntros "HC_imports HC_code HC_data Himport_interp Hworld_interp_C".

    iMod (world_interp_extend_perm_sepL2 W C
            code_addrs (cmpt_code C_cmpt)
            RX interpC
           with "Hworld_interp_C [HC_code]") as "(Hworld_interp_C & #HC_code)".
    { done. }
    { auto. }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HC_code]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ C_code Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite fixpoint_interp1_eq /=.
        iSplit; eauto.
        iSplit; eauto.
        rewrite /mono_permanent.
        iApply future_priv_mono_interp_z.
      - iFrame.
    }

    iMod (world_interp_extend_perm_sepL2_open _ C
            data_addrs
            (cmpt_data C_cmpt)
            RW interpC
           with "Hworld_interp_C [HC_data] []") as "(Hworld_interp_C & #HC_data & _)".
    { apply finz_seq_between_NoDup. }
    { done. }
    { apply Forall_forall. intros a Ha.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      { by rewrite Forall_forall in Hdata; apply Hdata in Ha. }
      pose proof (cmpt_cgp_disjoint C_cmpt) as Hdisjoint.
      apply map_disjoint_dom_1 in Hdisjoint.
      rewrite /cmpt_pcc_mregion dom_union_L in Hdisjoint.
      rewrite disjoint_union_l in Hdisjoint.
      destruct Hdisjoint as [_ Hdisjoint].
      pose proof (cmpt_data_size C_cmpt) as Hsize_data.
      pose proof (cmpt_code_size C_cmpt) as Hsize_code.
      rewrite !dom_mkregion_eq in Hdisjoint; auto.
      apply list_to_set_disj_2 in Hdisjoint.
      rewrite /disjoint /set_disjoint_instance in Hdisjoint.
      intro Ha'.
      apply (Hdisjoint a); auto.
    }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "HC_data").
      intros k v1 v2 Hv1 Hv2. iIntros; iFrame.
    }
    {
      iClear "#".
      clear -C_data.
      generalize dependent (cmpt_data C_cmpt); iIntros (l Hl).
      iIntros "#Hrels".
      iInduction (l) as [| w l] "IH"; first done.
      cbn.
      apply Forall_cons in Hl; destruct Hl as [Hw Hl].
      iSplitL; last (iApply "IH"; eauto).
      destruct w as [| [|] | |] ; cbn in Hw; destruct Hw as [Hw|Hw]; cbn in Hw; try done
      ; [|destruct g ; last done].
      - iSplit; last iApply future_priv_mono_interp_z.
        by rewrite fixpoint_interp1_eq /=.
      - iSplit; last iApply future_priv_mono_interp_global.
        rewrite fixpoint_interp1_eq interp1_eq.
        destruct Hw as (Hp & Hb & He).
        destruct (isO p) eqn:HpO; first done.
        destruct (has_sreg_access p) eqn:HpXSR.
        { destruct p as [ [] w dl dro ]; cbn in *; done. }
        replace (isWL p) with false; cycle 1.
        { destruct p as [ rx [] dl dro ]; cbn in *; auto.
          rewrite !andb_True in Hp.
          destruct Hp as [ [ [] ] ]; done.
        }
        iSplit; last done.
        iApply big_sepL_forall; cbn.
        iIntros (k a' Ha').
        apply list_elem_of_lookup_2, elem_of_finz_seq_between in Ha'.
        assert ((cmpt_b_cgp C_cmpt) <= a' < (cmpt_e_cgp C_cmpt))%a as Ha'' by solve_addr.
        apply elem_of_finz_seq_between in Ha''.
        iDestruct (big_sepL_elem_of with "Hrels") as "Hrel_a'"; eauto.
        assert (
            (std_update_multiple (std_update_multiple W code_addrs Permanent) data_addrs Permanent).1
              !! a' = Some Permanent
          ) as Ha'_W.
        { by apply std_sta_update_multiple_lookup_in_i. }
        iExists RW, interp; cbn.
        iSplit; first done.
        iSplit; first (iPureIntro; apply persistent_cond_interp).
        iSplit; first iFrame "#".
        iSplit; first iApply zcond_interp.
        iSplit; first iApply rcond_interp.
        iSplit; first iApply wcond_interp.
        iSplit; first iApply monoReq_interp; eauto.
    }

    iMod (world_interp_extend_perm_sepL2_open _ C
            imports_addrs
            (cmpt_imports C_cmpt)
            RX interpC
           with "Hworld_interp_C HC_imports [Himport_interp]") as "(Hworld_interp_C & #HC_imports & Hinterp_imports)".
    { apply finz_seq_between_NoDup. }
    { done. }
    { apply Forall_forall.
      intros a Ha.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      + rewrite std_sta_update_multiple_lookup_same_i; auto.
        { by rewrite Forall_forall in Himports; apply Himports in Ha. }
        pose proof (cmpt_import_size C_cmpt) as HC.
        apply not_elem_of_finz_seq_between.
        subst imports_addrs.
        rewrite elem_of_finz_seq_between in Ha.
        solve_addr+HC Ha.
      + pose proof (cmpt_disjointness C_cmpt) as HC.
        apply disjoint_list_cons in HC
        ; destruct HC as [HC _].
        rewrite union_list_cons in HC.
        cbn in HC.
        assert (
            finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
              ## finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)
          ) as HC' by set_solver+HC
        ; clear HC.
        intro Hcontra ; eapply HC'; eauto.
        pose proof (cmpt_import_size C_cmpt) as H.
        pose proof (cmpt_code_size C_cmpt) as H'.
        rewrite elem_of_finz_seq_between in Ha.
        apply elem_of_finz_seq_between; solve_addr+H H' Ha.
    }
    { iIntros "#HC_imports".
      iApply "Himport_interp"; iFrame "#".
    }
    iDestruct (big_sepL_sep with "Hinterp_imports") as "[$ _]".
    iFrame.
    iModIntro.
    iDestruct (big_sepL_app _ imports_addrs code_addrs with "[$HC_imports $HC_code]") as "HC_PCC".
    rewrite -finz_seq_between_split.
    2: {
      pose proof (cmpt_import_size C_cmpt) as HC.
      pose proof (cmpt_code_size C_cmpt) as HC'.
      solve_addr.
    }

    iSplit.
    - iEval (rewrite fixpoint_interp1_eq /=).
      iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      iExists RX, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit.
      { apply list_elem_of_lookup_2 in Ha.
        iApply (big_sepL_elem_of with "HC_PCC"); eauto.
      }
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first done.
      assert ((std Wfinal) !! a = Some Permanent).
      {
        subst Wfinal.
        apply list_elem_of_lookup_2 in Ha.
        rewrite (finz_seq_between_split _ (cmpt_a_code C_cmpt)) in Ha.
        2: {
          pose proof (cmpt_import_size C_cmpt) as HC.
          pose proof (cmpt_code_size C_cmpt) as HC'.
          solve_addr.
        }
        rewrite elem_of_app in Ha.
        destruct Ha as [ Ha | Ha ]; simplify_eq.
        + rewrite std_sta_update_multiple_lookup_in_i; auto; set_solver+.
        + rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
          { pose proof (cmpt_import_size C_cmpt) as HC.
            pose proof (cmpt_code_size C_cmpt) as HC'.
            apply elem_of_finz_seq_between in Ha.
            apply not_elem_of_finz_seq_between.
            solve_addr.
          }
          rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
          { intro Hcontra.
            assert (
                (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt))
                  ##
                  (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt))
              ) as Hdis; last set_solver+Ha Hcontra Hdis.
            clear.
            pose proof (cmpt_cgp_disjoint C_cmpt) as Hdis.
            rewrite /cmpt_pcc_mregion /cmpt_cgp_mregion in Hdis.
            rewrite -/(cmpt_pcc_mregion C_cmpt) -/(cmpt_cgp_mregion C_cmpt) in Hdis.
            rewrite map_disjoint_dom in Hdis.
            rewrite dom_cmpt_pcc_mregion dom_cmpt_cgp_mregion /cmpt_pcc_region /cmpt_cgp_region in Hdis.
            rewrite -list_to_set_disj in Hdis.
            assert (
                finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) ⊆ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
              ); last set_solver.
            intros a Ha.
            rewrite !elem_of_finz_seq_between in Ha |- *.
            pose proof (cmpt_import_size C_cmpt).
            solve_addr.
          }
          rewrite std_sta_update_multiple_lookup_in_i; auto; set_solver+.
      }
      iSplit; last done.
      iApply (monoReq_interp _ _ _ _ Permanent); done.
    - iEval (rewrite fixpoint_interp1_eq /=).
      iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      rewrite (big_sepL_lookup _ (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt))
                 k a); eauto.
      iFrame "HC_data".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      assert ((std Wfinal) !! a = Some Permanent).
      { subst Wfinal.
        apply list_elem_of_lookup_2 in Ha.
        assert (a ∉ imports_addrs).
        { clear -Ha.
          pose proof (cmpt_disjointness C_cmpt) as Hdis.
          apply disjoint_list_cons in Hdis as [Hdis _].
          rewrite union_list_cons disjoint_union_r in Hdis.
          destruct Hdis as [Hdis _].
          intro Hcontra.
          assert ( a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt))
          ; last set_solver.
          pose proof (cmpt_import_size C_cmpt) as Hsize.
          pose proof (cmpt_code_size C_cmpt).
          apply elem_of_finz_seq_between in Hcontra.
          apply elem_of_finz_seq_between.
          solve_addr.
        }
        repeat (rewrite std_sta_update_multiple_lookup_same_i; last done).
        rewrite std_sta_update_multiple_lookup_in_i; auto.
      }
      iSplit; last done.
      iApply (monoReq_interp _ _ _ _ Permanent); done.
  Qed.

  Lemma alloc_compartment_interp {E : coPset} (W : WORLD) ( C_cmpt : cmpt ) (C : CmptName)  :
    let imports_addrs := finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) in
    let pcc_cap := (WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a) in
    let cgp_cap := (WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a) in
    let Wfinal := std_update_compartment W C_cmpt in

    Forall (λ k, std W !! k = None) imports_addrs →
    Forall (λ k, std W !! k = None) code_addrs →
    Forall (λ k, std W !! k = None) data_addrs →

    Forall (λ w : Word, is_z w) (cmpt_code C_cmpt) ->
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) ->

    ([∗ list] k;v ∈ imports_addrs ; cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; cmpt_data C_cmpt, k ↦ₐ v) -∗
    (
      (interp Wfinal C pcc_cap ∗ interp Wfinal C cgp_cap)
      -∗
      ([∗ list] v ∈ cmpt_imports C_cmpt, interpC (Wfinal, C, v) ∗ future_priv_mono C interpC v)
    )
    -∗

    world_interp W C

    ={E}=∗

    world_interp Wfinal C
    ∗ interp Wfinal C pcc_cap
    ∗ interp Wfinal C cgp_cap
    ∗ ([∗ list] v ∈ cmpt_imports C_cmpt, interp Wfinal C v)
  .
  Proof.
    intros * Himports Hcode Hdata C_code C_data.
    iIntros "HC_imports HC_code HC_data Himport_interp Hworld_interp_C".
    iApply (alloc_compartment_interp_rel with "[$] [$] [$] [Himport_interp] [$]"); eauto.
    iIntros "[#Hrel_pcc #Hrel_data]".
    iApply "Himport_interp".
    iSplit.
    - iEval (rewrite fixpoint_interp1_eq /=).
      iApply big_sepL_intro; iModIntro.
      iIntros (ka a Ha).
      iExists RX, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit.
      { apply list_elem_of_lookup_2 in Ha.
        iApply (big_sepL_elem_of with "Hrel_pcc"); eauto.
        rewrite -finz_seq_between_split;auto.
        pose proof (cmpt_import_size C_cmpt) as HC.
        pose proof (cmpt_code_size C_cmpt) as HC'.
        solve_addr.
      }
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first done.
      assert ((std Wfinal) !! a = Some Permanent).
      {
        subst Wfinal.
        apply list_elem_of_lookup_2 in Ha.
        rewrite (finz_seq_between_split _ (cmpt_a_code C_cmpt)) in Ha.
        2: {
          pose proof (cmpt_import_size C_cmpt) as HC.
          pose proof (cmpt_code_size C_cmpt) as HC'.
          solve_addr.
        }
        rewrite elem_of_app in Ha.
        destruct Ha as [ Ha | Ha ]; simplify_eq.
        + rewrite std_sta_update_multiple_lookup_in_i; auto; set_solver+.
        + rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
          { pose proof (cmpt_import_size C_cmpt) as HC.
            pose proof (cmpt_code_size C_cmpt) as HC'.
            apply elem_of_finz_seq_between in Ha.
            apply not_elem_of_finz_seq_between.
            solve_addr.
          }
          rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
          { intro Hcontra.
            assert (
                (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt))
                  ##
                  (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt))
              ) as Hdis; last set_solver+Ha Hcontra Hdis.
            clear.
            pose proof (cmpt_cgp_disjoint C_cmpt) as Hdis.
            rewrite /cmpt_pcc_mregion /cmpt_cgp_mregion in Hdis.
            rewrite -/(cmpt_pcc_mregion C_cmpt) -/(cmpt_cgp_mregion C_cmpt) in Hdis.
            rewrite map_disjoint_dom in Hdis.
            rewrite dom_cmpt_pcc_mregion dom_cmpt_cgp_mregion /cmpt_pcc_region /cmpt_cgp_region in Hdis.
            rewrite -list_to_set_disj in Hdis.
            assert (
                finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) ⊆ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
              ); last set_solver.
            intros a Ha.
            rewrite !elem_of_finz_seq_between in Ha |- *.
            pose proof (cmpt_import_size C_cmpt).
            solve_addr.
          }
          rewrite std_sta_update_multiple_lookup_in_i; auto; set_solver+.
      }
      iSplit; last done.
      iApply (monoReq_interp _ _ _ _ Permanent); done.
    - iEval (rewrite fixpoint_interp1_eq /=).
      iApply big_sepL_intro; iModIntro.
      iIntros (ka a Ha).
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      rewrite (big_sepL_lookup _ (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt))
                 ka a); eauto.
      iFrame "Hrel_data".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      assert ((std Wfinal) !! a = Some Permanent).
      { subst Wfinal.
        apply list_elem_of_lookup_2 in Ha.
        assert (a ∉ imports_addrs).
        { clear -Ha.
          pose proof (cmpt_disjointness C_cmpt) as Hdis.
          apply disjoint_list_cons in Hdis as [Hdis _].
          rewrite union_list_cons disjoint_union_r in Hdis.
          destruct Hdis as [Hdis _].
          intro Hcontra.
          assert ( a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt))
          ; last set_solver.
          pose proof (cmpt_import_size C_cmpt) as Hsize.
          pose proof (cmpt_code_size C_cmpt).
          apply elem_of_finz_seq_between in Hcontra.
          apply elem_of_finz_seq_between.
          solve_addr.
        }
        repeat (rewrite std_sta_update_multiple_lookup_same_i; last done).
        rewrite std_sta_update_multiple_lookup_in_i; auto.
      }
      iSplit; last done.
      iApply (monoReq_interp _ _ _ _ Permanent); done.
  Qed.


End region_alloc_cmpt.
