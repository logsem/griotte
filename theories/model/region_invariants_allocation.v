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

  Lemma extend_region_perm' E W C a v p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
     a ∉ dom (std W) →
     future_priv_mono C φ v -∗
     sts_full_world W C -∗
     region W C -∗
     a ↦ₐ v -∗
     φ ((<s[a := Permanent ]s>W),C,v)

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
        repeat (iSplitR;done).
      }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      assert (a' ≠ a) as Hne;[intros Hcontr;subst a';rewrite HRl in Ha; inversion Ha|].
      rewrite lookup_insert_ne;auto. iSplitR;[auto|]. iFrame.
  Qed.

  Lemma extend_region_perm'' E W W' C a v p φ `{∀ Wv, Persistent (φ Wv)}:
    related_sts_priv_world W W' ->
    isO p = false ->
     a ∉ dom (std W) →
     a ∉ dom (std W') →
     future_priv_mono C φ v -∗
     sts_full_world W C -∗
     region W C -∗
     a ↦ₐ v -∗
     φ ((<s[a := Permanent ]s>W'),C,v) -∗
     (
     (sts_full_world (W) C ∗ region (W) C)
     ={E}=∗
     (sts_full_world W' C ∗ region W' C)
     )

     ={E}=∗

     region (<s[a := Permanent ]s>W') C
     ∗ rel C a p φ
     ∗ sts_full_world (<s[a := Permanent ]s>W') C.
  Proof.
    iIntros (Hrelated_W_W' HnpO Hnone_W Hnone_W') "#HmonoV Hfull Hreg Hl #Hφ Htransition".
    iMod ("Htransition" with "[$Hfull $Hreg]") as "[Hfull Hreg]".
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %HMW & %HMρ & Hpreds)".
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      iDestruct (big_sepM_delete _ _ _ _ HRl with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      apply (not_elem_of_dom (std W') a) in Hnone_W'.
      rewrite Hcontr in Hnone_W'. done.
    }
    rewrite /region_map_def.
    (* if not, we need to allocate a new saved pred using φ, *)
  (*      and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'"; first apply dfrac_valid_discarded.
    iMod (update_RELS _ _ _ a γpred p with "Hγrel") as "[HR Hγrel]"; auto.
    (* we also need to extend the World with a new temporary region *)
    iMod (sts_alloc_std_i W' C a Permanent
            with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh W' a Permanent) in Hnone_W' as Hrelated; auto.
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
        repeat (iSplitR;done).
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


  Lemma extend_region_perm_open E W C a w p la1 φ `{∀ Wv, Persistent (φ Wv)} :
    a ∉ dom (std W) →
    a ∉ la1 ->
    sts_full_world (std_update_multiple W la1 Permanent) C -∗
    open_region_many (std_update_multiple W la1 Permanent) C la1 -∗
    a ↦ₐ w
    ={E}=∗
    open_region_many (std_update_multiple W (a::la1) Permanent) C (a::la1)
    ∗ rel C a p φ
    ∗ a ↦ₐ w
    ∗ sts_state_std C a Permanent
    ∗ sts_full_world (std_update_multiple W (a::la1) Permanent) C.
  Proof.
    iIntros (Hnone ?) "Hfull Hreg Ha".
    assert (a ∉ dom (std (std_update_multiple W la1 Permanent))) as Hnone'.
    {
      rewrite not_elem_of_dom.
      rewrite std_sta_update_multiple_lookup_same_i; eauto.
      by rewrite -not_elem_of_dom.
    }
    rewrite open_region_many_eq /open_region_many_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %HMW & %HMρ & Hpreds)".
    destruct (M !! a) eqn:HRl.
    { (* The location is not in the map *)
      assert ((delete_list la1) M !! a = Some o) as HRl'.
      { rewrite lookup_delete_list_notin; auto. }
      iDestruct (big_sepM_delete _ _ _ _ HRl' with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      rewrite (not_elem_of_dom _ a) in Hnone'.
      by rewrite Hcontr in Hnone'.
    }
    rewrite /region_map_def.
    (* if not, we need to allocate a new saved pred using φ, *)
    (*      and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'"; first apply dfrac_valid_discarded.
    iMod (update_RELS _ _ _ a γpred p with "Hγrel") as "[HR #Hγrel]"; auto.
    iAssert (rel C a p φ) as "Ha_rel".
    { rewrite rel_eq /rel_def; iFrame "#". }
    iMod (sts_alloc_std_i _ C a Permanent
           with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh (std_update_multiple W la1 Permanent) a Permanent)
      in Hnone' as Hrelated; auto.
    iDestruct (region_map_monotone with "Hpreds") as "Hpreds'";[apply Hrelated|].
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    iFrame "HR ∗ #".
    iExists (<[a:=Permanent]> Mρ);iSplitR;[|iSplitR].
    - iPureIntro. rewrite /std_update in HMW |- *.
      repeat rewrite dom_insert_L; rewrite HMW; auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - cbn.
      rewrite -(delete_list_delete _ (<[a:=(γpred, p)]> M)); last done.
      rewrite delete_insert; last done.
      rewrite -(delete_list_delete _ (<[a:=_]> Mρ)); last done.
      rewrite delete_insert; last (rewrite -not_elem_of_dom HMρ not_elem_of_dom; done).
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      iFrame.
      done.
  Qed.

  Lemma extend_region_perm_sepL2_open_ind E W C la1 la2 lw2 p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    Forall (λ k, std W !! k = None) la2 →
    NoDup la1 ->
    NoDup la2 ->
    la2 ## la1 ->
    sts_full_world (std_update_multiple W la1 Permanent) C -∗
    open_region_many (std_update_multiple W la1 Permanent) C la1 -∗
    ([∗ list] k;v ∈ la2;lw2, k ↦ₐ v)

    ={E}=∗

    open_region_many (std_update_multiple W (la1++la2) Permanent) C (la1++la2)
    ∗ ([∗ list] k;v ∈ la2;lw2,
          k ↦ₐ v
          ∗ sts_state_std C k Permanent)
    ∗ ([∗ list] k ∈ la2, rel C k p φ)
    ∗ sts_full_world (std_update_multiple W (la1++la2) Permanent) C.
  Proof.
    revert la1 lw2.
    induction la2.
    { cbn. intros. iIntros "? ? ?".
      rewrite app_nil_r. iFrame. iModIntro. done. }
    iIntros (la1 lw2 Hp HW Hnodup_l1 Hnodup_l2 Hdisj) "Hsts Hreg Hl2".
    apply NoDup_cons in Hnodup_l2 as [Hna Hnodup_l2].
    apply disjoint_cons in Hdisj as Hni'.
    apply disjoint_swap in Hdisj;auto.
    apply Forall_cons in HW as [HWa HW].
    iDestruct (big_sepL2_length with "Hl2") as "%Hlen_l2".
    destruct lw2 as [|w lw2]; simplify_eq.
    iDestruct "Hl2" as "[ Ha Hl2]".
    replace (std_update_multiple W (la1 ++ a :: la2) Permanent)
              with (std_update_multiple W ( a::(la1 ++ la2)) Permanent).
    2: { apply std_update_multiple_permutation.
         apply Permutation_middle.
    }
    iMod (extend_region_perm_open with "Hsts Hreg Ha") as "(Hreg & Hrel & Ha & Hsts_std & Hsts)"; auto.
    { by rewrite not_elem_of_dom. }
    iMod (IHla2 (a::la1) lw2 with "[Hsts] [Hreg] [Hl2]") as "(Hreg&?&?&?)"; auto.
    { apply NoDup_cons;auto. }
    iDestruct (open_region_many_permutation _ _ _ (la1 ++ a :: la2) with "Hreg") as "Hreg".
    { apply Permutation_middle. }
    iFrame "∗#".
    done.
  Qed.

  Lemma region_close_many E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)} :
    NoDup l1 ->
    isO p = false ->
    ([∗ list] k ∈ l1, rel C k p φ) -∗
    open_region_many W C l1 -∗
    ([∗ list] k;v ∈ l1;l2, k ↦ₐ v ∗ sts_state_std C k Permanent) -∗
    ([∗ list] v ∈ l2, φ (W, C, v)) -∗
    ([∗ list] v ∈ l2, future_priv_mono C φ v)
    ={E}=∗ region W C.
  Proof.
    revert l2.
    induction l1; iIntros (l2 HNoDup Hp) "#Hrel Hreg Hl Hφ Hmono".
    {by rewrite region_open_nil. }
    iDestruct (big_sepL2_length with "Hl") as %Hlen.
    destruct l2; [ by inversion Hlen |]; simplify_eq.
    cbn.
    iDestruct "Hrel" as "[Ha_rel Hrel]".
    iDestruct "Hl" as "[(Ha & Ha_std) Hl]".
    iDestruct "Hφ" as "[Ha_φ Hφ]".
    iDestruct "Hmono" as "[Ha_mono Hmono]".
    apply NoDup_cons in HNoDup as [Ha_l1 HNoDup].
    iDestruct (region_close_next_perm with "[$Ha_std $Hreg $Ha $Ha_mono $Ha_φ $Ha_rel]")
      as "Hreg"; eauto.
    iMod (IHl1 with "Hrel Hreg Hl Hφ Hmono"); auto.
  Qed.

  Lemma extend_region_perm_sepL2_open E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    NoDup l1 ->
    isO p = false ->
    Forall (λ k, std W !! k = None) l1 →
    sts_full_world W C
    -∗ region W C
    -∗ ([∗ list] k;v ∈ l1;l2, k ↦ₐ v)
    -∗ ([∗ list] v ∈ l2,
          (([∗ list] k ∈ l1, rel C k p φ) -∗ φ ((std_update_multiple W l1 Permanent), C, v))
          ∗ future_priv_mono C φ v)

    ={E}=∗

    region (std_update_multiple W l1 Permanent) C
    ∗ ([∗ list] k ∈ l1, rel C k p φ)
    ∗ sts_full_world (std_update_multiple W l1 Permanent) C.
  Proof.
    iIntros (HNoDup Hp Hl1) "Hsts Hreg Hl".
    iMod (extend_region_perm_sepL2_open_ind E W C [] l1 l2 p φ with "[Hsts] [Hreg] [Hl]") as
    "(Hreg & Hl & #Hrel & Hsts)"; auto.
    { apply NoDup_nil. auto. }
    { eapply disjoint_nil_r. }
    { by rewrite -region_open_nil. }
    { cbn; iFrame "Hrel Hsts".
      iIntros "Hφ".
      iDestruct (big_sepL_sep with "Hφ") as "[Hφ Hmono]".
      iAssert ([∗ list] y2 ∈ l2, φ (std_update_multiple W l1 Permanent, C, y2))%I as "#Hφ'".
      { iClear "Hreg Hl Hmono".
        iInduction (l2) as [|x l2]; first done.
        iDestruct "Hφ" as "[H1 H2]".
        iDestruct ("H1" with "Hrel") as "$".
        iApply ("IHl2" with "H2"); auto.
      }
      iMod (region_close_many with "Hrel Hreg Hl Hφ' Hmono"); eauto.
    }
  Qed.

End region_alloc.
