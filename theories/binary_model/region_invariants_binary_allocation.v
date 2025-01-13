From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export region_invariants_binary
     region_invariants_batch_uninitialized_binary multiple_updates_binary.
Import uPred.

Lemma big_sepM_to_big_sepL2 (PROP : bi) (A B : Type) `{EqDecision A} `{Countable A}
        (φ: A -> B -> PROP) (l1: list A) (l2: list B):
  length l1 = length l2 ->
  NoDup l1 →
    ⊢ ([∗ map] y1↦y2 ∈ list_to_map (zip l1 l2), φ y1 y2) -∗
      ([∗ list] y1;y2 ∈ l1;l2, φ y1 y2).
  Proof.
    revert l2. iInduction (l1) as [|x l1] "IH"; iIntros (l2 Hnd Hdup) "H".
    - iSimpl. destruct l2;inversion Hnd. auto.
    - destruct l2;inversion Hnd.
      simpl.
      apply NoDup_cons in Hdup as [Hnin Hdup].
      iDestruct (big_sepM_insert with "H") as "[A H]".
      { eapply not_elem_of_list_to_map.
        rewrite fst_zip; auto. lia. }
      iFrame. iApply ("IH" $! l2 H1 Hdup with "H"); auto.
  Qed.

Section region_alloc.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {cfgg : cfgSG Σ} `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Definition u_merge_op (wo : option (Word * Word)) (ro : option region_type) : option region_type :=
    match wo,ro with
    | Some w, _ => Some (Uninitialized w)
    | None, Some r => Some r
    | None, None => None
    end.

  Definition override_uninitialize_std_sta (m : gmap Addr (Word * Word)) : STS_STD → STS_STD :=
    merge u_merge_op m.

  Definition override_uninitialize (m : gmap Addr (Word * Word)) : WORLD → WORLD :=
    λ W, (override_uninitialize_std_sta m W.1,W.2).

  Global Instance diag_none_u_merge_op : DiagNone u_merge_op.
  Proof. by rewrite /u_merge_op /DiagNone /=. Qed.

  Lemma override_uninitialize_std_sta_empty fs :
    override_uninitialize_std_sta ∅ fs = fs.
  Proof.
    rewrite map_eq_iff. intros a.
    rewrite /override_uninitialize_std_sta.
    rewrite lookup_merge lookup_empty /=.
    destruct (fs !! a) eqn:Hsome;rewrite Hsome;auto.
  Qed.

  Lemma override_uninitialize_empty W :
    override_uninitialize ∅ W = W.
  Proof.
    destruct W. rewrite /override_uninitialize /=. f_equiv.
    apply override_uninitialize_std_sta_empty.
  Qed.

  Lemma override_uninitialize_std_sta_insert fs m i w:
    override_uninitialize_std_sta (<[i:=w]> m) fs = <[i:=Uninitialized w]> (override_uninitialize_std_sta m fs).
  Proof.
    rewrite map_eq_iff. intros a.
    rewrite /override_uninitialize_std_sta.
    rewrite lookup_merge.
    destruct (decide (i = a)).
    - simplify_map_eq. rewrite lookup_insert. auto.
    - simplify_map_eq. rewrite lookup_insert_ne//.
      rewrite lookup_merge. auto.
  Qed.

  Lemma override_uninitialize_std_sta_lookup_none fs m i:
    m !! i = None ->
    override_uninitialize_std_sta m fs !! i = fs !! i.
  Proof.
    intros Hnone.
    rewrite lookup_merge Hnone /=.
    destruct (fs !! i) eqn:Hsome;rewrite Hsome;auto.
  Qed.

  Lemma override_uninitialize_std_sta_lookup_some fs m i x:
    m !! i = Some x ->
    override_uninitialize_std_sta m fs !! i = Some (Uninitialized x).
  Proof.
    intros Hsome.
    rewrite lookup_merge Hsome /=. auto.
  Qed.

  Lemma override_uninitialize_std_sta_dom fs m :
    dom (gset Addr) m ⊆ dom (gset Addr) fs →
    dom (gset Addr) (override_uninitialize_std_sta m fs) = dom (gset Addr) fs.
  Proof.
    intros Hsub.
    apply set_equiv_spec_L. split.
    - apply elem_of_subseteq.
      intros x [y Hin]%elem_of_gmap_dom.
      destruct (m !! x) eqn:Hsome.
      + apply Hsub. apply elem_of_gmap_dom;eauto.
      + rewrite override_uninitialize_std_sta_lookup_none// in Hin.
        apply elem_of_gmap_dom. eauto.
    - apply elem_of_subseteq. intros x Hx.
      destruct (m !! x) eqn:Hsome.
      + apply elem_of_gmap_dom. erewrite override_uninitialize_std_sta_lookup_some;eauto.
      + apply elem_of_gmap_dom. rewrite override_uninitialize_std_sta_lookup_none//.
        apply elem_of_gmap_dom;auto.
  Qed.

  Lemma static_extend_preserve W (M : relT) (Mρ : gmap Addr region_type) (l : Addr) g ρ :
    l ∉ dom (gset Addr) (std W) ->
    dom (gset Addr) (std W) = dom (gset Addr) M ->
    dom (gset Addr) Mρ = dom (gset Addr) M ->
    (∀ a' : Addr, a' ∈ dom (gset Addr) g → Mρ !! a' = Some (Monostatic g)) ->
    ∀ a' : Addr, a' ∈ dom (gset Addr) g → <[l:=ρ]> Mρ !! a' = Some (Monostatic g).
  Proof.
    intros Hl Hdom1 Hdom2 Hall.
    intros a' Hin. pose proof (Hall _ Hin) as Hcontr.
    assert (a' ∈ dom (gset Addr) Mρ) as Hincontr;[apply elem_of_gmap_dom;eauto|].
    rewrite Hdom2 in Hincontr. apply elem_of_gmap_dom in Hincontr. clear Hcontr.
    assert (is_Some (std W !! a')) as Hcontr.
    { apply elem_of_gmap_dom. rewrite Hdom1. apply elem_of_gmap_dom. eauto. }
    apply elem_of_gmap_dom in Hcontr.
    assert (a' ≠ l) as Hne';[intros Heq;subst;contradiction|].
    rewrite lookup_insert_ne;auto.
  Qed.

  Lemma extend_region_uninitialized_single E W l v φ `{∀ Wv, Persistent (φ Wv)}:
     l ∉ dom (gset Addr) (std W) →
     sts_full_world W -∗ region W -∗ l ↦ₐ v.1 -∗ l ↣ₐ v.2
     ={E}=∗
     region (<s[l := Uninitialized  v]s>W)
     ∗ rel l φ
     ∗ sts_full_world (<s[l := Uninitialized v ]s>W).
  Proof.
    iIntros (Hnone1) "Hfull Hreg Hl Hl'".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HdomM & HdomMρ & Hpreds)".
    iDestruct "HdomM" as %HdomM. iDestruct "HdomMρ" as %HdomMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl2 _]".
      iDestruct "Hl2" as (ρ' Hl) "[Hstate Hl2]".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 l) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree γpred]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree γpred]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W l (Uninitialized v)
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    eapply (related_sts_pub_world_fresh W l (Uninitialized v)) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
    iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HdomM. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HdomMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists (Uninitialized v). iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists φ. iSplitR;[auto|]. iFrame "∗ #".
        destruct v as [v1 v2]. iFrame. }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (φ0 Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v1 v2 Hg) "[Ha [Ha' #Hall] ]". iDestruct "Hall" as %Hall.
      iExists _. repeat iSplit;eauto. iExists v1, v2. iFrame. iSplit;auto. iPureIntro.
      eapply static_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma uninitialized_region_alloc  E m W φ `{∀ Wv, Persistent (φ Wv)} :
    (∀ k, is_Some (m !! k) → std W !! k = None) →
    sts_full_world W -∗ region W -∗
    ([∗ map] k↦v ∈ m, k ↦ₐ v.1 ∗ k ↣ₐ v.2)

     ={E}=∗

     region (override_uninitialize m W)
     ∗ ([∗ map] k↦_ ∈ m, rel k φ)
     ∗ sts_full_world (override_uninitialize m W).
  Proof.
    induction m using map_ind.
    { iIntros (Hdisj) "Hsts Hr Hm".
      rewrite override_uninitialize_empty. iFrame.
      rewrite !big_sepM_empty. done. }
    { iIntros (HnW) "Hsts Hr H". rewrite big_sepM_insert //.
      iDestruct "H" as "(Hk & Hm)".
      iDestruct "Hk" as "[Hk1 Hk2]".
      rewrite /override_uninitialize.
      rewrite !override_uninitialize_std_sta_insert.
      iMod (IHm with "Hsts Hr Hm") as "(Hr & Hm & Hsts)"; auto.
      { intros. apply HnW. rewrite lookup_insert_is_Some.
        destruct (decide (i = k)); auto. }
      iMod (extend_region_uninitialized_single with "Hsts Hr Hk1 Hk2")
        as "(Hr & Hrel & Hsts)"; auto.
      { rewrite not_elem_of_dom.
        rewrite override_uninitialize_std_sta_lookup_none;auto.
        apply HnW. rewrite lookup_insert //. eauto. }
      iFrame. iModIntro. iApply big_sepM_insert; eauto. }
  Qed.

  Lemma extend_region_perm E W l v φ `{∀ Wv, Persistent (φ Wv)}:
    l ∉ dom (gset Addr) (std W) →
    future_priv_mono φ v.1 v.2 -∗
    sts_full_world W -∗ region W -∗ l ↦ₐ v.1 -∗ l ↣ₐ v.2 -∗ φ (W,v) ={E}=∗ region (<s[l := Permanent ]s>W)
                                                          ∗ rel l φ
                                                          ∗ sts_full_world (<s[l := Permanent ]s>W).
  Proof.
    iIntros (Hnone1) "#Hmono Hfull Hreg Hl Hl2 #Hφ".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    rewrite RELS_eq /RELS_def.
    (* destruct on M !! l *)
    destruct (M !! l) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom W.1 l) in Hnone1.
      rewrite Hcontr in Hnone1. done.
    }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'".
    iMod (own_update _ _ (● (<[l:=to_agree γpred]> (to_agree <$> M : relUR)) ⋅ ◯ ({[l:=to_agree γpred]}))
            with "Hγrel") as "[HR #Hγrel]".
    { apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap. rewrite HRl. done.
    }
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W l Permanent
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W l Permanent) in Hnone1 as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    rewrite -fmap_insert.
    iFrame "HR". iFrame.
    iSplitL;[iExists (<[l:=_]> Mρ);iSplitR;[|iSplitR]|].
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMW. auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists Permanent. iFrame.
        iSplitR;[iPureIntro;apply lookup_insert|].
        iExists φ. iSplitR;[auto|]. iFrame "∗ #".
        iExists _,_. iFrame. repeat iSplit;auto.
        iNext. iApply "Hmono"; eauto.
        iPureIntro. by apply related_sts_pub_priv_world. destruct v as [v1 v2]. auto.
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a ≠ l) as Hne;[intros Hcontr;subst a;rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
      destruct ρ; iFrame.
      iDestruct "Hρ" as (φ0 Hpers) "[Hsaved Hl]".
      iDestruct "Hl" as (v0 v2 Hg) "[Ha [Ha' #Hall]]". iDestruct "Hall" as %Hall.
      iExists _. repeat iSplit;eauto. iExists v0,v2. iFrame. iSplit;auto. iPureIntro.
      eapply static_extend_preserve; eauto.
    - iExists γpred. iFrame "#".
      rewrite REL_eq /REL_def.
      done.
  Qed.

  Lemma extend_region_perm_sepL2 E W l1 l2 φ `{∀ Wv, Persistent (φ Wv)}:
     Forall (λ k, std W !! k = None) l1 →
     sts_full_world W -∗ region W -∗
     ([∗ list] k;v ∈ l1;l2, k ↦ₐ v ∗ k ↣ₐ v ∗ φ (W, (v,v)) ∗ future_priv_mono φ v v)

     ={E}=∗

     region (std_update_multiple W l1 Permanent)
     ∗ ([∗ list] k ∈ l1, rel k φ)
     ∗ sts_full_world (std_update_multiple W l1 Permanent).
  Proof.
    revert l2. induction l1.
    { cbn. intros. iIntros "? ? ?". iFrame. eauto. }
    { intros * [? ?]%Forall_cons_1. iIntros "Hsts Hr Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hal1 ND]%NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ? & ?) (H2 & ? & ? & ?)".
        iApply (addr_dupl_false with "H1 H2"). }
      destruct l2; [ by inversion Hlen |].
      iDestruct (big_sepL2_cons with "Hl") as "[(Ha & Ha' & Hφ & #Hf) Hl]".
      iMod (IHl1 with "Hsts Hr Hl") as "(Hr & ? & Hsts)"; auto.
      iDestruct (extend_region_perm _ _ _ (w,w) with "Hf Hsts Hr Ha Ha' [Hφ]") as ">(? & ? & ?)"; auto.
      { rewrite -std_update_multiple_not_in_sta; auto.
        rewrite not_elem_of_dom //. }
      { iApply ("Hf" with "[] Hφ"). iPureIntro.
        apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
        eapply Forall_impl; eauto.
        intros. by rewrite not_elem_of_dom. }
      iModIntro. cbn. iFrame. }
  Qed.

  Lemma extend_region_perm_sepM E W m φ `{∀ Wv, Persistent (φ Wv)}:
    (∀ k, is_Some (m !! k) → std W !! k = None) →
    sts_full_world W -∗ region W -∗
    ([∗ map] k↦v ∈ m, k ↦ₐ v ∗ k ↣ₐ v ∗ φ (W, (v,v)) ∗ future_priv_mono φ v v)

    ={E}=∗

        region (std_update_multiple W (elements (dom (gset Addr) m)) Permanent)
        ∗ ([∗ list] k ∈ elements (dom (gset Addr) m), rel k φ)
        ∗ sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Permanent).
  Proof.
    induction m using map_ind.
    { cbn. intros. iIntros "? ? ?". iFrame. eauto. }
    { intros * ?. iIntros "Hsts Hr Hl".
      iDestruct (big_sepM_insert with "Hl") as "[(Ha & Ha' & Hφ & #Hf) Hl]";auto.
      iMod (IHm with "Hsts Hr Hl") as "(Hr & #Hrels & Hsts)"; auto.
      { intros. apply H2. destruct (decide (i = k));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//]. }
      iDestruct (extend_region_perm _ _ _ (x,x) with "Hf Hsts Hr Ha Ha' [Hφ]") as ">(? & #Hrel & ?)"; auto.
      { rewrite -std_update_multiple_not_in_sta; auto.
        rewrite not_elem_of_dom //. apply H2. rewrite lookup_insert. eauto. rewrite elem_of_elements.
        apply not_elem_of_dom. auto. }
      { iApply ("Hf" with "[] Hφ"). iPureIntro.
        apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
        apply Forall_forall. intros. rewrite not_elem_of_dom.
        apply H2. destruct (decide (i = x0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        apply elem_of_gmap_dom,elem_of_elements;auto. }
      iModIntro. rewrite !dom_insert_L.
      assert (i ∉ dom (gset Addr) m) as Hnin.
      { apply not_elem_of_dom. auto. }
      pose proof (elements_union_singleton (dom (gset Addr) m) i Hnin) as Hperm.
      apply std_update_multiple_permutation with (W:=W) (ρ:=Permanent) in Hperm.
      rewrite !Hperm /=. iFrame.
      rewrite (big_sepL_forall _ (elements ({[i]} ∪ dom (gset Addr) m))).
      iIntros (k x0 Hin). destruct (decide (x0 = i));[subst;iFrame "#"|].
      iDestruct (big_sepL_elem_of _ _ x0 with "Hrels") as "$".
      assert (x0 ∈ (elements ({[i]} ∪ dom (gset Addr) m))) as Hin'.
      { apply elem_of_list_lookup. eauto. }
      revert Hin'. rewrite elements_union_singleton =>Hin'.
      apply elem_of_cons in Hin' as [Hcontr | Hin'];auto. done.
      apply elem_of_gmap_dom in Hin'. rewrite H1 in Hin'. by inv Hin'.
    }
  Qed.

End region_alloc.
