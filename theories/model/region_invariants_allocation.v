From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import proofmode.
From stdpp Require Import list_relations.
From cap_machine Require Export region_invariants multiple_updates.
From cap_machine Require Import seal_store logrel interp_weakening.
Import uPred.

Section region_alloc.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {heapg : heapGS Σ}
    `{MP: MachineParameters}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* Lemmas for extending the region map *)
  Lemma extend_region_temp_pwl E W C a v p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
     a ∉ dom (std W) →
     (isWL p) = true →
     future_pub_mono C φ v -∗
     sts_full_world W C -∗
     region W C -∗
     a ↦ₐ v -∗
     φ (W,C,v)

     ={E}=∗

     region (<s[ a:= Temporary ]s>W) C
     ∗ rel C a p φ
     ∗ sts_full_world (<s[ a := Temporary ]s>W) C.
  Proof.
    iIntros (HnpO Hnone1 Hpwl) "#HmonoV Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %HMW & %HMρ & Hpreds)".
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom (std W) a) in Hnone1.
      rewrite Hcontr in Hnone1; done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'"; first apply dfrac_valid_discarded.
    iMod (update_RELS _ _ _ a γpred p with "Hγrel") as "[HR Hγrel]"; auto.
    iMod (sts_alloc_std_i W C a Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W a Temporary) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    iFrame "HR ∗ #".
    iExists (<[a:=_]> Mρ);iSplitR;[|iSplitR].
    - iPureIntro. rewrite /std_update in HMW |- *.
      repeat rewrite dom_insert_L; rewrite HMW; auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Temporary. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,p,φ. rewrite Hpwl.
        iFrame "∗ #".
        repeat(iSplitR;auto).
        iApply "HmonoV"; eauto.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a';rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
  Qed.

  Lemma extend_region_temp_nwl E W C a v p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
     a ∉ dom (std W) →
     (isWL p) = false →
     (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v) -∗
     sts_full_world W C -∗
     region W C -∗
     a ↦ₐ v -∗
     φ (W,C,v)

     ={E}=∗

     region (<s[a := Temporary ]s>W) C
     ∗ rel C a p φ
     ∗ sts_full_world (<s[a := Temporary ]s>W) C.
  Proof.
    iIntros (HnpO Hnone1 Hpwl) "#HmonoV Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %HMW & %HMρ & Hpreds)".
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom (std W) a) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, *)
  (*      and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'"; first apply dfrac_valid_discarded.
    iMod (update_RELS _ _ _ a γpred p with "Hγrel") as "[HR Hγrel]"; auto.
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W C a Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W a Temporary) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    iFrame "HR ∗ #".
    iExists (<[a:=_]> Mρ);iSplitR;[|iSplitR].
    - iPureIntro. rewrite /std_update in HMW |- *.
      repeat rewrite dom_insert_L; rewrite HMW; auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Temporary. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,p,φ. rewrite Hpwl.
        iFrame "∗ #".
        repeat(iSplitR;[auto|]).
        destruct (isDL p); iApply "HmonoV"; eauto.
        by iPureIntro; apply related_sts_pub_priv_world.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a';rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
  Qed.

  Lemma extend_region_temp E W C a v p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    a ∉ dom (std W) →
    (if isWL p then future_pub_mono C φ v else
       (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)) -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W,C,v)

    ={E}=∗

    region (<s[a := Temporary ]s>W) C
    ∗ rel C a p φ
    ∗ sts_full_world (<s[a := Temporary ]s>W) C.
  Proof.
    iIntros (HnpO Hnone1) "#HmonoV Hfull Hreg Hl #Hφ".
    destruct (isWL p) eqn:Hpwl.
    + iApply (extend_region_temp_pwl with "[$] [$] [$] [$]"); eauto.
    + iApply (extend_region_temp_nwl with "[$] [$] [$] [$]"); eauto.
  Qed.

  Lemma extend_region_perm E W C a v p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
     a ∉ dom (std W) →
     future_priv_mono C φ v -∗
     sts_full_world W C -∗
     region W C -∗
     a ↦ₐ v -∗
     φ (W,C,v)

     ={E}=∗

     region (<s[a := Permanent ]s>W) C
     ∗ rel C a p φ
     ∗ sts_full_world (<s[a := Permanent ]s>W) C.
  Proof.
    iIntros (HnpO Hnone1) "#HmonoV Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %HMW & %HMρ & Hpreds)".
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom (std W) a) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, *)
  (*      and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'"; first apply dfrac_valid_discarded.
    iMod (update_RELS _ _ _ a γpred p with "Hγrel") as "[HR Hγrel]"; auto.
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W C a Permanent
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W a Permanent) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    iFrame "HR ∗ #".
    iExists (<[a:=_]> Mρ);iSplitR;[|iSplitR].
    - iPureIntro. rewrite /std_update in HMW |- *.
      repeat rewrite dom_insert_L; rewrite HMW; auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Permanent. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,p,φ. iFrame "∗ #".
        repeat (iSplitR;[done|]).
        iNext. iApply "HmonoV"; eauto.
        iPureIntro; by apply related_sts_pub_priv_world.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a';rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
  Qed.

  (* The following allocates a Revoked region. This allocates the saved predicate and the region state, *)
  (* but since a revoked region is empty, there is no need to assume any resources for that region *)

  Lemma extend_region_revoked E W C a p φ `{∀ Wv, Persistent (φ Wv)} :
     a ∉ dom (std W) →
     sts_full_world W C
     -∗ region W C

     ={E}=∗

     region (<s[a := Revoked ]s>W) C
     ∗ rel C a p φ
     ∗ sts_full_world (<s[a := Revoked ]s>W) C.
  Proof.
    iIntros (Hnone1) "Hfull Hreg".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %HMW & %HMρ & Hpreds)".
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom (std W) a) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ, *)
  (*      and extend R with a := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'"; first apply dfrac_valid_discarded.
    iMod (update_RELS _ _ _ a γpred p with "Hγrel") as "[HR Hγrel]"; auto.
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W C a Revoked
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W a Revoked) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    iFrame "HR ∗ #".
    iExists (<[a:=_]> Mρ);iSplitR;[|iSplitR].
    - iPureIntro. rewrite /std_update in HMW |- *.
      repeat rewrite dom_insert_L; rewrite HMW; auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Revoked. iFrame. iSplitR.
        + iPureIntro;apply lookup_insert.
        + iExists _. iFrame "#". auto.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha') "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha'; inversion Ha'|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
  Qed.

  Lemma extend_region_revoked_sepL2 E W C l1 p φ `{∀ Wv, Persistent (φ Wv)}:
    Forall (λ k, std W !! k = None) l1 →
    sts_full_world W C
    -∗ region W C

     ={E}=∗

     region (std_update_multiple W l1 Revoked) C
     ∗ ([∗ list] k ∈ l1, rel C k p φ)
     ∗ sts_full_world (std_update_multiple W l1 Revoked) C.
  Proof.
    induction l1.
    - cbn. intros. iIntros "? ?". iFrame. eauto.
    - intros [? ?]%Forall_cons_1. iIntros "Hsts Hr".
      simpl. iMod (IHl1 with "Hsts Hr") as "(Hr & #Hrels & Hsts)"; auto.
      destruct (decide (a ∈ l1)).
      + (* if a is already in l1, we are done *)
        assert (e':=e). apply elem_of_list_lookup in e as [k Hk].
        iDestruct (big_sepL_lookup _ _ k with "Hrels") as "Ha";[eauto|].
        (* rewrite /std_multiple_update HWC; cbn. *)
        assert (<s[a:=Revoked]s>(std_update_multiple W l1 Revoked)
                = std_update_multiple W l1 Revoked) as ->.
        { rewrite /std_update.
          destruct (std_update_multiple W l1 Revoked) as [] eqn:Heq.
          f_equiv; last done.
          simpl. rewrite insert_id//.
          assert (o = std (std_update_multiple W l1 Revoked)) as ->;[rewrite Heq//|].
          apply std_sta_update_multiple_lookup_in_i;auto.
        }
        destruct (std_update_multiple W l1 Revoked) as [Wstd_sta Wloc] eqn:Heq.
        destruct l1; first by rewrite lookup_nil in Hk.
        by iFrame "#∗".
      + iMod (extend_region_revoked _ _ _ a with "Hsts Hr") as "(Hr & Hrel & Hsts)"; auto.
        { destruct l1.
          { rewrite not_elem_of_dom //. }
          rewrite -std_update_multiple_not_in_sta; auto.
          rewrite not_elem_of_dom //.
        }
        by iFrame "#∗".
  Qed.

  Lemma extend_region_temp_sepL2 E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    Forall (λ k, std W !! k = None) l1 →
    sts_full_world W C
    -∗ region W C
    -∗ ([∗ list] k;v ∈ l1;l2,
          k ↦ₐ v
          ∗ φ (W, C, v)
          ∗ (if isWL p then future_pub_mono C φ v else
               (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)) )

    ={E}=∗

    region (std_update_multiple W l1 Temporary) C
    ∗ ([∗ list] k ∈ l1, rel C k p φ)
    ∗ sts_full_world (std_update_multiple W l1 Temporary) C.
  Proof.
    revert l2. induction l1.
    - cbn. intros. iIntros "? ?". iFrame. eauto.
    - intros l2 HneqO [HWa Hnone_l1]%Forall_cons_1. iIntros "Hsts Hr Hl".
      simpl.
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hal1 ND]%NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ?) (H2 & ? & ?)".
        iApply (addr_dupl_false with "H1 H2"). }
      destruct l2; [ by inversion Hlen |].
      iDestruct (big_sepL2_cons with "Hl") as "[(Ha & Hφ & #Hf) Hl]".

      iMod (IHl1 with "Hsts Hr Hl") as "(Hr & ? & Hsts)"; auto.
      iDestruct (extend_region_temp with "Hf Hsts Hr Ha [Hφ]") as ">(? & ? & ?)"; eauto.
      {
        intro Hcontra.
        apply elem_of_dom_std_multiple_update in Hcontra.
        destruct Hcontra as [?|Hcontra]; first set_solver.
        rewrite elem_of_dom in Hcontra.
        destruct Hcontra as [? Hcontra].
        by rewrite Hcontra in HWa.
      }
      { destruct (isWL p).
        + iApply ("Hf" with "[] Hφ"). iPureIntro.
          apply related_sts_pub_update_multiple.
          eapply Forall_impl; eauto.
          intros. by rewrite not_elem_of_dom.
        + destruct (isDL p).
          ++ iApply ("Hf" with "[] Hφ"). iPureIntro.
             apply related_sts_pub_update_multiple.
             eapply Forall_impl; eauto.
             intros. by rewrite not_elem_of_dom.
          ++ iApply ("Hf" with "[] Hφ"). iPureIntro.
             apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
             eapply Forall_impl; eauto.
             intros. by rewrite not_elem_of_dom.
      }
      iModIntro. cbn. iFrame.
  Qed.


  Lemma extend_region_perm_sepL2 E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    Forall (λ k, std W !! k = None) l1 →
    sts_full_world W C
    -∗ region W C
    -∗ ([∗ list] k;v ∈ l1;l2,
          k ↦ₐ v
          ∗ φ (W, C, v)
          ∗ future_priv_mono C φ v)

    ={E}=∗

    region (std_update_multiple W l1 Permanent) C
    ∗ ([∗ list] k ∈ l1, rel C k p φ)
    ∗ sts_full_world (std_update_multiple W l1 Permanent) C.
  Proof.
    revert l2. induction l1.
    { cbn. intros. iIntros "? ? ?". iFrame. eauto. }
    { intros ? ? [? ?]%Forall_cons_1. iIntros "Hsts Hr Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hal1 ND]%NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ?) (H2 & ? & ?)".
        iApply (addr_dupl_false with "H1 H2"). }
      destruct l2; [ by inversion Hlen |].
      iDestruct (big_sepL2_cons with "Hl") as "[(Ha & Hφ & #Hf) Hl]".
      iMod (IHl1 with "Hsts Hr Hl") as "(Hr & ? & Hsts)"; auto.
      iDestruct (extend_region_perm with "Hf Hsts Hr Ha [Hφ]") as ">(? & ? & ?)"; eauto.
      { rewrite -std_update_multiple_not_in_sta; auto.
        rewrite not_elem_of_dom //. }
      { iApply ("Hf" with "[] Hφ"). iPureIntro.
        apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
        eapply Forall_impl; eauto.
        intros. by rewrite not_elem_of_dom. }
      iModIntro. cbn. iFrame. }
  Qed.

End region_alloc.
