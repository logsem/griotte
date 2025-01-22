From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Export region_invariants region_invariants_frozen (* region_invariants_batch_uninitialized *).
Import uPred.

Section region_alloc.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ}
          {stsg : STSG Addr region_type Σ}
          {heapg : heapGS Σ}
          `{MP:MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.


  (* Lemmas for extending the region map *)

  Lemma frozen_extend_preserve W (M : relT) (Mρ : gmap Addr region_type) (a : Addr) g ρ :
    a ∉ dom (std W) ->
    dom (std W) = dom M ->
    dom Mρ = dom M ->
    (∀ a' : Addr, a' ∈ dom g → Mρ !! a' = Some (Frozen g)) ->
    ∀ a' : Addr, a' ∈ dom g → <[a:=ρ]> Mρ !! a' = Some (Frozen g).
  Proof.
    intros Hl Hdom1 Hdom2 Hall.
    intros a' Hin. pose proof (Hall _ Hin) as Hcontr.
    assert (a' ∈ dom Mρ) as Hincontr;[apply elem_of_dom;eauto|].
    rewrite Hdom2 in Hincontr. apply elem_of_dom in Hincontr. clear Hcontr.
    assert (is_Some (std W !! a')) as Hcontr.
    { rewrite -elem_of_dom. rewrite Hdom1. rewrite elem_of_dom. eauto. }
    rewrite -elem_of_dom in Hcontr.
    assert (a' ≠ a) as Hne';[intros Heq;subst;contradiction|].
    rewrite lookup_insert_ne;auto.
  Qed.

  Lemma extend_region_temp_pwl E W a v p φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     a ∉ dom (std W) →
     (pwl p) = true →
     future_pub_mono φ v -∗
     sts_full_world W -∗
     region W -∗
     a ↦ₐ v -∗
     φ (W,v)

     ={E}=∗

     region (<s[a := Temporary ]s>W)
     ∗ rel a p φ
     ∗ sts_full_world (<s[a := Temporary ]s>W).
  Proof.
    iIntros (HnpO Hnone1 Hpwl) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 a) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'". apply dfrac_valid_discarded.
    iMod (own_update _ _ (● (<[a:=to_agree (γpred,p)]> (to_agree <$> M : relUR))
                          ⋅ ◯ ({[a:=to_agree (γpred,p)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W a Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W a Temporary) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame "∗ #".
    iSplitL;[iExists (<[a:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Temporary. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,p,φ. rewrite Hpwl.
        iFrame "∗ #".
        repeat(iSplitR;[auto|]).
        iApply "Hmono"; eauto.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a';rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Hγ Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hnp0O Hg) "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _. repeat iSplit;eauto. iExists p0,φ0. iFrame.
      repeat (iSplit;auto). iPureIntro.
      eapply frozen_extend_preserve; eauto.
    - rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma extend_region_temp_nwl E W a v p φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     a ∉ dom (std W) →
     (pwl p) = false →
     future_priv_mono φ v -∗
     sts_full_world W -∗
     region W -∗
     a ↦ₐ v -∗
     φ (W,v)

     ={E}=∗

     region (<s[a := Temporary ]s>W)
     ∗ rel a p φ
     ∗ sts_full_world (<s[a := Temporary ]s>W).
  Proof.
    iIntros (HnpO Hnone1 Hpwl) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 a) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'". apply dfrac_valid_discarded.
    iMod (own_update _ _ (● (<[a:=to_agree (γpred,p)]> (to_agree <$> M : relUR))
                          ⋅ ◯ ({[a:=to_agree (γpred,p)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W a Temporary
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W a Temporary) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame "∗ #".
    iSplitL;[iExists (<[a:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Temporary. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,p,φ. rewrite Hpwl.
        iFrame "∗ #".
        repeat(iSplitR;[auto|]).
        iApply "Hmono"; eauto.
        by iPureIntro; apply related_sts_pub_priv_world.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a';rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Hγ Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hnp0O Hg) "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _. repeat iSplit;eauto. iExists p0,φ0. iFrame.
      repeat (iSplit;auto). iPureIntro.
      eapply frozen_extend_preserve; eauto.
    - rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma extend_region_perm E W a v p φ `{∀ Wv, Persistent (φ Wv)}:
     p ≠ O →
     a ∉ dom (std W) →
     future_priv_mono φ v -∗
     sts_full_world W -∗
     region W -∗
     a ↦ₐ v -∗
     φ (W,v)

     ={E}=∗

     region (<s[a := Permanent ]s>W)
     ∗ rel a p φ
     ∗ sts_full_world (<s[a := Permanent ]s>W).
  Proof.
    iIntros (HnpO Hnone1) "#Hmono Hfull Hreg Hl #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! a *)
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 a) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'". apply dfrac_valid_discarded.
    iMod (own_update _ _ (● (<[a:=to_agree (γpred,p)]> (to_agree <$> M : relUR))
                          ⋅ ◯ ({[a:=to_agree (γpred,p)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W a Permanent
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W a Permanent) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
    iSplitL;[iExists (<[a:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Permanent. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists γpred,p,φ. iFrame "∗ #".
        repeat (iSplitR;[done|]).
        iNext. iApply "Hmono"; eauto.
        iPureIntro. by apply related_sts_pub_priv_world.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a';rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Hγ Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hnp0O Hg) "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _,_,_. repeat iSplit;eauto.
      iExists v0; iFrame.
      repeat (iSplit;auto).
      iPureIntro; eapply frozen_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  (* The following allocates a Revoked region. This allocates the saved predicate and the region state, *)
  (* but since a revoked region is empty, there is no need to assume any resources for that region *)

  Lemma extend_region_revoked E W a p φ `{∀ Wv, Persistent (φ Wv)} :
     a ∉ dom (std W) →
     sts_full_world W
     -∗ region W

     ={E}=∗

     region (<s[a := Revoked ]s>W)
     ∗ rel a p φ
     ∗ sts_full_world (<s[a := Revoked ]s>W).
  Proof.
    iIntros (Hnone1) "Hfull Hreg".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! a *)
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 a) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with a := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'". apply dfrac_valid_discarded.
    iMod (own_update _ _ (● (<[a:=to_agree (γpred,p)]> (to_agree <$> M : relUR))
                          ⋅ ◯ ({[a:=to_agree (γpred,p)]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W a Revoked
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W a Revoked) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
    iSplitL;[iExists (<[a:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Revoked. iFrame. iSplitR.
        iPureIntro;apply lookup_insert.
        iExists _. iFrame "#". auto.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha') "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha'; inversion Ha'|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (γpred0 p0 φ0 Hγ Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 Hnp0O Hg) "[Ha #Hall]". iDestruct "Hall" as %Hall.
      iExists _,_,_. repeat iSplit;eauto.
      iExists v0; iFrame.
      repeat (iSplit;auto).
      iPureIntro; eapply frozen_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma extend_region_revoked_sepL2 E W l1 p φ `{∀ Wv, Persistent (φ Wv)}:
    Forall (λ k, std W !! k = None) l1 →
    sts_full_world W
    -∗ region W

     ={E}=∗

     region (std_update_multiple W l1 Revoked)
     ∗ ([∗ list] k ∈ l1, rel k p φ)
     ∗ sts_full_world (std_update_multiple W l1 Revoked).
  Proof.
    induction l1.
    { cbn. intros. iIntros "? ?". iFrame. eauto. }
    { intros [? ?]%Forall_cons_1. iIntros "Hsts Hr".
      simpl. iMod (IHl1 with "Hsts Hr") as "(Hr & #Hrels & Hsts)"; auto.
      destruct (decide (a ∈ l1)).
      { (* if a is already in l1, we are done *)
        assert (e':=e). apply elem_of_list_lookup in e as [k Hk].
        iDestruct (big_sepL_lookup _ _ k with "Hrels") as "Ha";[eauto|].
        assert (<s[a:=Revoked]s>(std_update_multiple W l1 Revoked) = std_update_multiple W l1 Revoked) as ->;[|by iFrame "∗ #"].
        rewrite /std_update. destruct (std_update_multiple W l1 Revoked) eqn:Heq. f_equiv. simpl. rewrite insert_id//.
        assert (o = (std_update_multiple W l1 Revoked).1) as ->;[rewrite Heq//|].
        apply std_sta_update_multiple_lookup_in_i;auto. done. }
      iMod (extend_region_revoked _ _ a with "Hsts Hr") as "(Hr & Hrel & Hsts)".
      { auto. }
      { rewrite -std_update_multiple_not_in_sta; auto.
        rewrite not_elem_of_dom //. }
      iFrame. done. }
  Qed.

  Lemma extend_region_perm_sepL2 E W l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    p ≠ O ->
    Forall (λ k, std W !! k = None) l1 →
    sts_full_world W
    -∗ region W
    -∗ ([∗ list] k;v ∈ l1;l2, k ↦ₐ v ∗ φ (W, v) ∗ future_priv_mono φ v)

    ={E}=∗

    region (std_update_multiple W l1 Permanent)
    ∗ ([∗ list] k ∈ l1, rel k p φ)
    ∗ sts_full_world (std_update_multiple W l1 Permanent).
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

  (* Lemma extend_region_uninitialized_single E W l v φ `{∀ Wv, Persistent (φ Wv)}: *)
  (*    l ∉ dom (std W) → *)
  (*    sts_full_world W -∗ region W -∗ l ↦ₐ v *)
  (*    ={E}=∗ *)
  (*    region (<s[l := Uninitialized v]s>W) *)
  (*    ∗ rel l φ *)
  (*    ∗ sts_full_world (<s[l := Uninitialized v ]s>W). *)
  (* Proof. *)
  (*   iIntros (Hnone1) "Hfull Hreg Hl". *)
  (*   rewrite region_eq rel_eq /region_def /rel_def. *)
  (*   iDestruct "Hreg" as (M Mρ) "(Hγrel & HdomM & HdomMρ & Hpreds)". *)
  (*   iDestruct "HdomM" as %HdomM. iDestruct "HdomMρ" as %HdomMρ. *)
  (*   rewrite RELS_eq /RELS_def. *)
  (*   (* destruct on M !! l *) *)
  (*   destruct (M !! l) eqn:HRl. *)
  (*   { (* The location is not in the map *) *)
  (*     iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]". *)
  (*     iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']". *)
  (*     iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr. *)
  (*     apply (not_elem_of_dom W.1 l) in Hnone1. *)
  (*     rewrite Hcontr in Hnone1. done. *)
  (*   } *)
  (*   (* if not, we need to allocate a new saved pred using φ, *)
  (*      and extend R with l := pred *) *)
  (*   iMod (saved_pred_alloc φ) as (γpred) "#Hφ'". apply dfrac_valid_discarded. *)
  (*   iMod (own_update _ _ (● (<[l:=to_agree γpred]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree γpred]})) *)
  (*           with "Hγrel") as "[HR #Hγrel]". *)
  (*   { apply auth_update_alloc. *)
  (*     apply (alloc_singleton_local_update (to_agree <$> M)); last done. *)
  (*     rewrite lookup_fmap. rewrite HRl. done. *)
  (*   } *)
  (*   (* we also need to extend the World with a new temporary region *) *)
  (*   iMod (sts_alloc_std_i W l (Uninitialized v) *)
  (*           with "[] Hfull") as "(Hfull & Hstate)"; auto. *)
  (*   eapply (related_sts_pub_world_fresh W l (Uninitialized v)) in Hnone1 as Hrelated; auto. *)
  (*   iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|]. *)
  (*   iModIntro. rewrite bi.sep_exist_r. iExists _. *)
  (*   rewrite -fmap_insert. *)
  (*   iFrame "HR". iFrame. *)
  (*   iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|]. *)
  (*   - iPureIntro. repeat rewrite dom_insert_L. rewrite HdomM. auto. *)
  (*   - iPureIntro. repeat rewrite dom_insert_L. rewrite HdomMρ. auto. *)
  (*   - iApply big_sepM_insert; auto. *)
  (*     iSplitR "Hpreds'". *)
  (*     { iExists (Uninitialized v). iFrame. *)
  (*       iSplitR;[iPureIntro;apply lookup_insert|]. *)
  (*       iExists φ. iSplitR;[auto|]. iFrame "∗ #". } *)
  (*     iApply (big_sepM_mono with "Hpreds'"). *)
  (*     iIntros (a x Ha) "Hρ". *)
  (*     iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]". *)
  (*     iExists ρ. *)
  (*     assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|]. *)
  (*     rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame. *)
  (*     destruct ρ; iFrame. *)
  (*     iDestruct "Hρ" as (φ0 Hpers) "[Hsaved Hl]". *)
  (*     iDestruct "Hl" as (v0 Hg) "[Ha #Hall]". iDestruct "Hall" as %Hall. *)
  (*     iExists _. repeat iSplit;eauto. iExists v0. iFrame. iSplit;auto. iPureIntro. *)
  (*     eapply frozen_extend_preserve; eauto. *)
  (*   - iExists γpred. iFrame "#". *)
  (*     rewrite REL_eq /REL_def. *)
  (*     done. *)
  (* Qed. *)

  (* Lemma override_uninitialize_std_sta_dom' W (m: gmap Addr Word) : *)
  (*    dom (override_uninitialize_std_sta m W.1) = *)
  (*    dom m ∪ dom W.1. *)
  (* Proof. *)
  (*   rewrite set_eq. intro x. *)
  (*   rewrite !elem_of_union. split. *)
  (*   - intros HH. rewrite elem_of_dom in HH. *)
  (*     destruct (decide (x ∈ dom m));auto. right. *)
  (*     rewrite override_uninitialize_std_sta_lookup_none in HH. *)
  (*     2: rewrite -not_elem_of_dom//. rewrite elem_of_dom;eauto. *)
  (*   - intros [ HH | HH ]; rewrite elem_of_dom in HH; destruct HH as [? HH]. *)
  (*     rewrite elem_of_dom. erewrite override_uninitialize_std_sta_lookup_some;eauto. *)
  (*     destruct (m !! x) eqn:Hsome;auto. 1,2: rewrite elem_of_dom. *)
  (*     erewrite override_uninitialize_std_sta_lookup_some;eauto. *)
  (*     rewrite override_uninitialize_std_sta_lookup_none;eauto. *)
  (* Qed. *)

  (* Lemma extend_region_frozen_single_sepM E W (m: gmap Addr Word) φ `{∀ Wv, Persistent (φ Wv)}: *)
  (*    (∀ k, is_Some (m !! k) → std W !! k = None) → *)
  (*    sts_full_world W -∗ region W -∗ *)
  (*    ([∗ map] k↦v ∈ m, k ↦ₐ v) *)

  (*    ={E}=∗ *)

  (*    region (override_uninitialize m W) *)
  (*    ∗ ([∗ map] k↦_ ∈ m, rel k φ) *)
  (*    ∗ sts_full_world (override_uninitialize m W). *)
  (* Proof. *)
  (*   induction m using map_ind. *)
  (*   { intros. rewrite !override_uninitialize_empty !big_sepM_empty. *)
  (*     iIntros. by iFrame. } *)
  (*   { iIntros (HnW) "Hsts Hr H". rewrite big_sepM_insert //. *)
  (*     iDestruct "H" as "(Hk & Hm)". *)
  (*     rewrite /override_uninitialize. *)
  (*     rewrite !override_uninitialize_std_sta_insert. *)
  (*     iMod (IHm with "Hsts Hr Hm") as "(Hr & Hm & Hsts)"; auto. *)
  (*     { intros. apply HnW. rewrite lookup_insert_is_Some. *)
  (*       destruct (decide (i = k)); auto. } *)
  (*     iDestruct (extend_region_uninitialized_single with "Hsts Hr Hk") *)
  (*       as ">(Hr & Hrel & Hsts)"; auto. *)
  (*     { rewrite override_uninitialize_std_sta_dom'. *)
  (*       rewrite not_elem_of_union !not_elem_of_dom. split; auto. *)
  (*       apply HnW. rewrite lookup_insert //. } *)
  (*     iFrame. iModIntro. iApply big_sepM_insert; eauto. } *)
  (* Qed. *)

  Lemma extend_region_perm_sepL2_from_rev φ E W l1 l2 p `{∀ Wv, Persistent (φ Wv)}:
    p ≠ O →
    Forall (λ k, std W !! k = Some Revoked) l1 →
    sts_full_world W -∗
    region W -∗
    ([∗ list] k;v ∈ l1;l2, k ↦ₐ v ∗ φ (W, v) ∗ future_priv_mono φ v ∗ rel k p φ)

    ={E}=∗

    region (std_update_multiple W l1 Permanent)
    ∗ ([∗ list] k ∈ l1, rel k p φ)
    ∗ sts_full_world (std_update_multiple W l1 Permanent).
  Proof.
    revert l2. induction l1.
    { cbn. intros. iIntros "? ? ?". iFrame. eauto. }
    { intros ? ? [? ?]%Forall_cons_1. iIntros "Hsts Hr Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hal1 ND]%list.NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ?) (H2 & ? & ?)".
        iApply (addr_dupl_false with "H1 H2"). }
      destruct l2; [ by inversion Hlen |].
      iDestruct (big_sepL2_cons with "Hl") as "[(Ha & Hφ & #Hf & #Hrel) Hl]".
      iMod (IHl1 with "Hsts Hr Hl") as "(Hr & ? & Hsts)"; auto.
      iMod (update_region_revoked_perm with "Hf Hsts Hr Ha [Hφ] Hrel") as "(? & ?)"; auto.
      { erewrite std_sta_update_multiple_lookup_same_i;auto. }
      { iApply ("Hf" with "[] Hφ"). iPureIntro.
        apply related_sts_pub_priv_world,related_sts_pub_update_multiple_perm. auto. }
      iFrame "∗ #". done.
    }
  Qed.

End region_alloc.
