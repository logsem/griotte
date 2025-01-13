From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export stdpp_extra iris_extra region_invariants
     multiple_updates region_invariants_revocation region_invariants_batch_uninitialized sts.
Require Import stdpp.countable.
Import uPred.

Section heap.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* This file provides three main lemmas:
     - one that opens all of a static region at once
     - one that closes what was a static region and turns it into a temporary one
     - one that turns a revoked region into a static region
   *)

  (* this change is for the local stack frame that we freeze when calling an adv       *)
  (* we can only do this change if there are no monotemporary states above our frame   *)

  Definition u_merge_op (wo : option Word) (ro : option region_type) : option region_type :=
    match wo,ro with
    | Some w, _ => Some (Uninitialized w)
    | None, Some r => Some r
    | None, None => None
    end.

  Definition override_uninitialize_std_sta (m : gmap Addr Word) : STS_STD → STS_STD :=
    merge u_merge_op m.

  Definition override_uninitialize (m : gmap Addr Word) : WORLD → WORLD :=
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

  (* --------------------------------------------------------------------------------- *)
  (* Auxiliary definitions around opened regions *)

  (* A collection of sts_state_std *)
  Definition sts_state_std_many {V} (m: gmap Addr V) (Mρ: V → region_type) :=
    ([∗ map] a↦v ∈ m, sts_state_std a (Mρ v))%I.

  Definition sts_state_std_many_uninit (m: gmap Addr Word) := sts_state_std_many m (λ v, Uninitialized v).

  (* Bulk update of the state of a [sts_state_std_many] *)
  Lemma region_update_multiple_states W (m : gmap Addr Word) st st' :
    sts_full_world W ∗ sts_state_std_many m (λ _, st)
    ==∗ sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) st')
    ∗ sts_state_std_many m (λ _, st').
  Proof.
    iIntros "[Hfull Hstate]".
    iInduction (m) as [|x l] "IH" using map_ind.
    - rewrite /sts_state_std_many dom_empty_L elements_empty big_sepM_empty big_sepM_empty /=.
      iModIntro. iFrame.
    - iDestruct (big_sepM_insert with "Hstate") as "[Hx Hstate]";auto.
      iDestruct (sts_full_state_std with "Hfull Hx") as %Hstate.
      iMod ("IH" with "Hfull Hstate") as "[Hfull Hstate]". iClear "IH".
      iMod (sts_update_std _ _ _ st' with "Hfull Hx") as "[Hfull Hx]".
      rewrite dom_insert_L.
      erewrite (std_update_multiple_permutation _ (elements (_ ∪ _))).
      2: { rewrite elements_union_singleton // not_elem_of_dom //. }
      iAssert (⌜is_Some ((std_update_multiple W (elements (dom (gset Addr) m)) st').1 !! x)⌝%I)
        as %Hsome.
      { rewrite /sts_full_world /sts_full_std /=.
        iPureIntro. apply std_sta_update_multiple_is_Some.
        eauto. }
      iFrame.
      iModIntro. iApply big_sepM_insert;auto. iFrame.
  Qed.

  Lemma region_update_multiple_states_uninit W (m : gmap Addr Word) st :
    sts_full_world W ∗ sts_state_std_many m (λ _, st)
    ==∗ sts_full_world (override_uninitialize m W)
    ∗ sts_state_std_many_uninit m.
  Proof.
    iIntros "[Hfull Hstate]".
    iInduction (m) as [|x w] "IH" using map_ind.
    - rewrite /sts_state_std_many_uninit /sts_state_std_many override_uninitialize_empty !big_sepM_empty /=.
      iModIntro. iFrame.
    - iDestruct (big_sepM_insert with "Hstate") as "[Hx Hstate]";auto.
      iDestruct (sts_full_state_std with "Hfull Hx") as %Hstate.
      iMod ("IH" with "Hfull Hstate") as "[Hfull Hstate]". iClear "IH".
      rewrite /override_uninitialize override_uninitialize_std_sta_insert.
      iMod (sts_update_std _ _ _ (Uninitialized w) with "Hfull Hx") as "[Hfull Hx]".
      iFrame.
      iModIntro. iApply big_sepM_insert;auto. iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- Opening a static region ------------------------------- *)

  Lemma region_map_delete_monostatic (M: gmap Addr _) (Mρ: gmap Addr _) W m l γ v:
    dom (gset Addr) M ⊆ dom (gset Addr) Mρ →
    M !! l = Some γ →
    Mρ !! l = Some (Monostatic m) →
    m !! l = Some v →
    region_map_def M Mρ W -∗
    region_map_def (delete l M) Mρ W ∗
    l ↦ₐ v ∗ sts_state_std l (Monostatic m).
  Proof.
    intros Hdom HMl HMρ Hm.
    iIntros "Hr".
    iDestruct (big_sepM_delete _ _ l with "Hr") as "(Hl & Hr)"; eauto; [].
    iFrame. iDestruct "Hl" as (ρ' Hρ') "(? & Hst)".
    assert (ρ' = Monostatic m) as -> by congruence.
    iDestruct "Hst" as (?) "(? & ? & H)".
    iDestruct "H" as (v') "(% & ? & _)".
    assert (v' = v) as -> by (congruence). simplify_eq. iFrame.
  Qed.

  Definition static_resources (m: gmap Addr Word) :=
    ([∗ map] a↦v ∈ m, ∃ φ, rel a φ ∗ a ↦ₐ v)%I.

  Lemma region_map_open_some_monostatic (M: gmap Addr _) Mρ W (m m_all: gmap Addr Word) :
    m ⊆ m_all →
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Monostatic m_all)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W
    ∗ RELS M
    ∗ sts_full_world W
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, rel a φ)
    -∗
    region_map_def (M ∖∖ m) Mρ W
    ∗ RELS M
    ∗ sts_full_world W
    ∗ static_resources m
    ∗ sts_state_std_many m (λ _, Monostatic m_all).
  Proof.
    pattern m. revert m. refine (map_ind _ _ _).
    - intros **. iIntros "(?&?&?&?)".
      rewrite !difference_het_empty /static_resources /sts_state_std_many !big_sepM_empty /=.
      iFrame; eauto.
    - intros a v m Hma HI Hsub_all Hm_all Hdom.
      iIntros "(Hr & HM & Hsts & Hrels)".
      assert (a ∈ dom (gset Addr) Mρ).
      { specialize (Hm_all a).
        feed pose proof Hm_all. rewrite dom_insert; set_solver.
        rewrite -elem_of_gmap_dom. eauto. }
      assert (a ∈ dom (gset Addr) M) by (rewrite -Hdom; auto).
      rewrite difference_het_insert_r //.
      feed specialize HI; eauto.
      { transitivity (<[a:=v]> m); auto. by apply insert_subseteq. }
      { intros a' Ha'. apply Hm_all. rewrite dom_insert. set_solver. }
      iDestruct (big_sepM_insert with "Hrels") as "[Ha Hrels]";auto.
      iDestruct (HI with "[Hr HM Hsts Hrels]") as "(Hr & HM & Hfull & ? & Hmap)"; [by iFrame|..].
      rewrite rel_eq /rel_def. iDestruct "Ha" as (? ?) "[HREL ?]".
      rewrite REL_eq RELS_eq /REL_def /RELS_def.
      iDestruct (reg_in with "[$HREL $HM]") as %HMeq.
      apply elem_of_gmap_dom in H0. destruct H0.
      iDestruct (region_map_delete_monostatic _ _ _ m_all a with "Hr") as "(? & ? & ?)".
      { rewrite dom_difference_het. rewrite Hdom. set_solver. }
      { apply difference_het_lookup_Some. split;eauto. }
      { apply Hm_all. rewrite dom_insert; set_solver. }
      { eapply lookup_weaken; [| apply Hsub_all]. by rewrite lookup_insert. }
      rewrite HMeq in H0. rewrite lookup_insert in H0; inv H0.
      all: iFrame. all: rewrite /static_resources /sts_state_std_many !big_sepM_insert //.
      all: iFrame. all: iExists _. iFrame. rewrite rel_eq /rel_def REL_eq /REL_def. iExists _. iFrame.
  Qed.

  Lemma region_map_open_all_monostatic M Mρ W (m: gmap Addr Word) :
    (forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Monostatic m)) →
    dom (gset Addr) Mρ = dom (gset Addr) M →
    region_map_def M Mρ W
    ∗ sts_full_world W
    ∗ RELS M
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, rel a φ)
    -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    ∗ sts_full_world W
    ∗ sts_state_std_many m (λ _, Monostatic m)
    ∗ static_resources m
    ∗ RELS M.
  Proof.
    iIntros (HH Hdom) "(Hr & Hsts & HM & Hrels)".
    iDestruct (region_map_open_some_monostatic M Mρ W m m with "[Hr Hsts HM Hrels]")
      as "(Hr & HM & Hsts & ? & ?)"; auto; iFrame.
    iApply (big_sepM_mono with "Hr").
    iIntros (k γp HMk) "H". iDestruct "H" as (ρ HMρ) "(Hst & Hρ)". iExists ρ.
    rewrite difference_het_lookup_Some in HMk * => HMk. destruct HMk as [HMk Hmk].
    iSplitR. iPureIntro. by rewrite difference_het_lookup_Some; eauto.
    iFrame. destruct ρ as [| | | |m']; (try by iFrame).
    iDestruct "Hρ" as (φ Hpers) "[Hsaved Hρ]".
    iDestruct "Hρ" as (v) "(% & ? & Hothers)"; iDestruct "Hothers" as %Hothers.
    iExists _; iFrame; repeat iSplitR;auto; iFrame. iExists _. iFrame. iPureIntro.
    split;auto. intros a' Ha'. all: rewrite difference_het_lookup_Some. all: split; eauto.
    destruct (m !! a') eqn:?; eauto; exfalso.
    specialize (HH a'); feed specialize HH. by rewrite -elem_of_gmap_dom; eauto.
    specialize (Hothers a'). feed specialize Hothers; auto. rewrite Hothers in HH.
    inversion HH. subst. congruence.
  Qed.

  Lemma region_map_has_monostatic_addr M Mρ W (l: Addr) m :
    (std W) !! l = Some (Monostatic m) →
    dom (gset Addr) (std W) = dom (gset Addr) M →
    region_map_def M Mρ W ∗ sts_full_world W -∗
    ⌜(forall a', a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Monostatic m))⌝ ∗
    ⌜l ∈ dom (gset Addr) m⌝.
  Proof.
    iIntros (HWl Hdom) "(Hr & Hsts)".
    assert (is_Some (M !! l)) as [ρ Hρ].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    iDestruct (big_sepM_lookup _ _ l with "Hr") as "Hl"; eauto.
    iDestruct "Hl" as (ρ' Hρ') "(Hst & Hρ)".
    iDestruct (sts_full_state_std with "Hsts Hst") as %HH.
    rewrite HWl in HH. apply Some_eq_inj in HH. subst ρ'.
    iDestruct "Hρ" as (?) "(? & ? & Hρ)".
    iDestruct "Hρ" as (? ?) "(? & %)".
    intros. iPureIntro. split; eauto.
    rewrite -elem_of_gmap_dom; eauto.
  Qed.

  Lemma region_rel_get_all (W : WORLD) (a : Addr) :
    is_Some ((std W) !! a) ->
    region W ∗ sts_full_world W ==∗
    region W ∗ sts_full_world W ∗ ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ rel a φ.
  Proof.
    iIntros ([x Hlookup]) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    assert (is_Some (M !! a)) as [γp Hγp].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    rewrite RELS_eq /RELS_def.
    iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
    (* rewrite /region_map_def. iDestruct (reg_in with "[$HM $Hrel]") as %HMeq. *)
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
    iDestruct (sts_full_state_std with "Hsts Hρ") as %Hx''.
    rewrite Hlookup in Hx''. inversion Hx''. subst.
    iDestruct "Hstate" as (φ Hpers) "(#Hsaved & Ha)".
    (* iDestruct "Ha" as (v Hne) "(Ha & Hmono & #Hφ)". *)
    iDestruct (big_sepM_delete _ _ a with "[Hρ Ha $Hr]") as "Hr";[eauto| |].
    { iExists ρ. iSplit;auto. iFrame. iExists φ. iFrame "∗ #". repeat iSplit; auto. }
    iModIntro.
    iSplitL "HM Hr".
    { iExists M. iFrame. auto. }
    iFrame. iExists φ. iSplit;auto. rewrite rel_eq /rel_def REL_eq /REL_def. iExists γp.
    iFrame "Hsaved Hrel".
  Qed.

  Lemma region_map_has_monostatic_rels W m' m a :
    m' ⊆ m →
    (std W) !! a = Some (Monostatic m) ->
    region W ∗ sts_full_world W ==∗
    region W ∗ sts_full_world W ∗ ([∗ map] a↦v ∈ m', ∃ φ, rel a φ).
  Proof.
    iIntros (Hsub Hsta) "[Hr Hsts]".
    iInduction (m') as [|l x] "IH" using map_ind.
    - iFrame. iModIntro. iApply big_sepM_empty. done.
    - iDestruct (full_sts_monostatic_all with "Hsts Hr") as %Hforall;eauto.
      assert (is_Some (std W !! l)) as Hsta'.
      { assert (l ∈ dom (gset Addr) m) as Hin.
        { revert Hsub. rewrite map_subseteq_spec =>Hsub. apply elem_of_gmap_dom.
          exists x. apply Hsub. apply lookup_insert. }
        apply Hforall in Hin. rewrite /monostatic in Hin. rewrite /std.
        destruct (W.1 !! l);inversion Hin;eauto.
      }
      iMod (region_rel_get_all with "[$Hr $Hsts]") as "(Hr & Hsts & Hrel)";eauto.
      iMod ("IH" with "[] Hr Hsts") as "(Hr & Hsts & Hrels)".
      { iPureIntro. trans (<[l:=x]> m0);auto. apply insert_subseteq. auto. }
      iFrame. iModIntro. iApply big_sepM_insert;auto. iFrame.
      iDestruct "Hrel" as (φ Hpers) "Hrel".
      iExists φ. iFrame.
  Qed.

  Lemma region_map_has_monostatic_rels_all W m a :
    (std W) !! a = Some (Monostatic m) ->
    region W ∗ sts_full_world W ==∗
    region W ∗ sts_full_world W ∗ ([∗ map] a↦v ∈ m, ∃ φ, rel a φ).
  Proof.
    iIntros (Hsta) "[Hr Hsts]".
    iApply region_map_has_monostatic_rels;eauto. iFrame.
  Qed.

  Lemma region_open_monostatic W (m: gmap Addr Word) (l: Addr) :
    (std W) !! l = Some (Monostatic m) →
    region W ∗ sts_full_world W ==∗
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world W
    ∗ sts_state_std_many m (λ _, Monostatic m)
    ∗ static_resources m
    ∗ ⌜l ∈ dom (gset Addr) m⌝.
  Proof.
    iIntros (HWl) "(Hr & Hsts)".
    iMod (region_map_has_monostatic_rels_all with "[$Hr $Hsts]") as "(Hr & Hsts & Hrels)";eauto.
    iModIntro. rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & % & % & Hr)".
    iDestruct (region_map_has_monostatic_addr with "[HM Hr Hsts]")
      as %(Hstatic & ?); eauto; [by iFrame|].
    iDestruct (region_map_open_all_monostatic M Mρ W m with "[HM Hr Hsts Hrels]")
      as "(Hr & Hsts & ? & ? & ?)"; eauto; [iFrame|].
    iFrame. iSplitL; eauto. rewrite open_region_many_eq /open_region_many_def.
    iExists M,Mρ. iFrame. do 2 (iSplitR; eauto).
    rewrite !delete_elements_eq_difference_het. eauto.
  Qed.


  (* --------------------------------------------------------------------------------- *)
  (* ------------------ Turn a monostatic region into an uninitialized one ----------- *)

  Lemma related_sts_pub_world_monostatic_to_uninitialized a m m' W :
    (∀ a', is_Some(m !! a') → W.1 !! a' = Some (Monostatic m')) →
    (∀ a', is_Some(m !! a') → a <= a')%a →
    related_sts_a_world W (override_uninitialize m W) a.
  Proof.
    intros Hforall Hcond.
    induction m using map_ind.
    - rewrite override_uninitialize_empty. apply related_sts_a_refl_world.
    - assert (a <= i)%a as Hlt.
      { apply Hcond. simplify_map_eq. eauto. }
      assert (∀ a' : Addr, is_Some (m !! a') → (a <= a')%a) as Hnewcond.
      { intros. apply Hcond. destruct (decide (i = a')); simplify_map_eq;eauto. }
      assert (W.1 !! i = Some (Monostatic m')) as Hmono.
      { apply Hforall. simplify_map_eq. eauto. }
      assert (∀ a' : Addr, is_Some (m !! a') → W.1 !! a' = Some (Monostatic m')) as Hnewforall.
      { intros. apply Hforall. destruct (decide (i = a')); simplify_map_eq;eauto. }

      specialize (IHm Hnewforall Hnewcond) as IHm.
      eapply related_sts_a_trans_world;[by apply IHm|].
      split;simpl.
      2: { apply related_sts_pub_plus_refl. }
      split.
      { rewrite override_uninitialize_std_sta_insert dom_insert_L. set_solver. }
      intros a' x' y' Hx' Hy'.
      destruct (decide (i = a')).
      + subst. rewrite override_uninitialize_std_sta_insert lookup_insert in Hy'.
        inversion Hy';subst. rewrite override_uninitialize_std_sta_lookup_none in Hx';auto.
        rewrite Hx' in Hmono. inversion Hmono;subst.
        destruct (decide (le_a a a'));try solve_addr.
        right with Monotemporary. right;constructor.
        eright;[|left]. right. constructor.
      + rewrite override_uninitialize_std_sta_insert lookup_insert_ne// in Hy'.
        rewrite Hx' in Hy'. inversion Hy';left.
  Qed.

  Lemma region_close_next_uninit W φ ls l v `{forall Wv, Persistent (φ Wv)} :
    l ∉ ls ->
    ⊢ sts_state_std l (Uninitialized v) ∗
      open_region_many (l::ls) W ∗ l ↦ₐ v ∗ rel l φ
      -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonmonostatic (Uninitialized v) with "Hpreds") as "Hpreds". congruence.
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iSplitR; [by simplify_map_eq|].
      iExists _. iFrame "∗ #". repeat (iSplitR;[eauto|]). auto. }
    rewrite -(delete_list_delete _ M) // -(delete_list_insert _ (delete l M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists _, _. iFrame.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; auto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close_uninitialized_many (m: gmap Addr Word) W:
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
        a ↦ₐ v ∗ rel a φ)
    ∗ sts_state_std_many_uninit m
    ∗ sts_full_world W
    -∗
    region W ∗ sts_full_world W.
  Proof.
    pattern m. revert m. eapply map_ind.
    - iIntros "(Hor & ? & ? & Hsts)". rewrite dom_empty_L elements_empty.
      iDestruct (region_open_nil with "Hor") as "Hor". iFrame.
    - iIntros (a γp m Hma HInd) "(HR & Htmp & Hst & Hsts)".
      iDestruct (open_region_many_permutation with "HR") as "HR".
      { rewrite dom_insert elements_union_singleton // not_elem_of_dom //. }
      iDestruct (big_sepM_insert with "Hst") as "[Hsta Hst]"; eauto.
      iDestruct (sts_full_state_std with "Hsts Hsta") as %HWa.
      iDestruct (big_sepM_insert with "Htmp") as "[Ha Htmp]"; eauto.
      iDestruct "Ha" as (?) "(%&Hrel)".
      iApply HInd. iFrame.
      iApply (region_close_next_uninit with "[$HR $Hsta $Hrel]");auto.
      auto. intros [? ?]%elem_of_elements%elem_of_gmap_dom. congruence.
  Qed.

  Lemma sts_full_state_std_many {V} (m: gmap Addr V) (ρ:region_type) W:
    sts_full_world W
    ∗ sts_state_std_many m (λ _, ρ)
    -∗
    ⌜Forall (λ (a:Addr), std W !! a = Some ρ) (elements (dom (gset Addr) m))⌝.
  Proof.
    pattern m. revert m. apply map_ind.
    - iIntros. iPureIntro. rewrite dom_empty elements_empty //.
    - iIntros (a x m ? IH) "(Hsts & Hst)".
      iDestruct (big_sepM_insert with "Hst") as "[Hsta Hst]"; auto.
      iDestruct (sts_full_state_std with "Hsts Hsta") as %Hsta.
      iDestruct (IH with "[Hsts Hst]") as %?. by iFrame.
      iPureIntro. rewrite dom_insert elements_union_singleton ?not_elem_of_dom //.
      constructor; eauto.
  Qed.

  Lemma full_sts_Mρ_agree_weaker W M Mρ (ρ: region_type) :
    (* NB: only the forward direction of dom_equal (std_sta W) M is actually needed *)
    dom (gset Addr) (std W) ⊆ dom (gset Addr) M →
    (* NB: only one direction of this assumption is needed, and only for the reverse *)
  (*      direction of the lemma *)
    (* dom (gset Addr) Mρ = dom (gset Addr) M → *)
    sts_full_world W -∗
    region_map_def M Mρ W -∗
    ⌜∀ a:Addr, (std W) !! a = Some ρ → Mρ !! a = Some ρ⌝.
  Proof.
    iIntros (HWM) "Hfull Hr".
    iAssert (∀ a:Addr, ⌜ std W !! a = Some ρ ⌝ → ⌜ Mρ !! a = Some ρ ⌝)%I as %?.
    { iIntros (a Haρ).
      assert (is_Some (M !! a)) as [γp Hγp].
      { apply elem_of_gmap_dom. apply HWM. apply elem_of_gmap_dom. eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). apply encode_inj.
      rewrite Haρ in Haρ'. congruence. } auto.
  Qed.

  Lemma full_sts_Mρ_agree_weaker_delete_list W M Mρ l m :
    elements (dom (gset Addr) m) ≡ₚl →
    (* NB: only the forward direction of dom_equal (std_sta W) M is actually needed *)
    (∀ a, a ∈ dom (gset Addr) W.1 ∧ a ∉ l → a ∈ dom (gset Addr) (delete_list l M)) →
    (* NB: only one direction of this assumption is needed, and only for the reverse *)
  (*      direction of the lemma *)
    (* dom (gset Addr) Mρ = dom (gset Addr) M → *)
    sts_full_world (override_uninitialize m W) -∗
    region_map_def (delete_list l M) Mρ W -∗
    ⌜∀ (a:Addr) ρ, (std W) !! a = Some ρ ∧ a ∉ l → Mρ !! a = Some ρ⌝.
  Proof.
    iIntros (Heql HWM) "Hfull Hr".
    iAssert (∀ (a:Addr) ρ, ⌜ std W !! a = Some ρ ∧ a ∉ l⌝ → ⌜ Mρ !! a = Some ρ ⌝)%I as %?.
    { iIntros (a ρ [Haρ Hnin]).
      assert (is_Some ((delete_list l M) !! a)) as [γp Hγp].
      { apply elem_of_gmap_dom. apply HWM. split;auto. apply elem_of_gmap_dom. eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). apply encode_inj.
      rewrite override_uninitialize_std_sta_lookup_none in Haρ'.
      rewrite Haρ in Haρ'. congruence. apply not_elem_of_dom. intros Hcontr%elem_of_elements.
      revert Hcontr. rewrite Heql. auto. } auto.
  Qed.

  Lemma extract_lo {V} (m : gmap Addr V) :
    m ≠ ∅ →
    ∃ a, is_Some (m !! a) ∧ (∀ a', is_Some(m !! a') → a <= a')%a.
  Proof.
    induction m using map_ind.
    - done.
    - destruct (decide (m = ∅)).
      + subst. intros Hsingleton. exists i.
        simplify_map_eq. split;eauto.
        intros a' Hsome. destruct Hsome as [v Hsome].
        destruct (decide (i = a'));simplify_map_eq. solve_addr.
      + apply IHm in n as [a [Hsomea Ha] ].
        intros _. destruct (decide (i < a))%a.
        * exists i. simplify_map_eq. split;eauto.
          intros a' Ha'. destruct (decide (i = a')).
          ** subst. solve_addr.
          ** rewrite lookup_insert_ne// in Ha'.
             apply Ha in Ha' as Hle.
             solve_addr.
        * exists a. assert (i ≠ a) as Hne;[intros ->;rewrite H in Hsomea;by inversion Hsomea|].
          rewrite lookup_insert_ne//. split;auto.
          intros a' Hsomea'. destruct (decide (i = a'));subst.
          ** solve_addr.
          ** simplify_map_eq. apply Ha. auto.
  Qed.

  Lemma open_region_world_monostatic_to_uninitialized l m W :
    (elements (dom (gset Addr) m) ≡ₚl) →
    (∀ (a : Addr), is_Some (m !! a) → W.1 !! a = Some (Monostatic m)) →
    (∀ (a a' : Addr), is_Some (m !! a) ∧ (a <= a')%a → W.1 !! a' ≠ Some Monotemporary) →
    sts_full_world (override_uninitialize m W) -∗
    open_region_many l W
    -∗
    sts_full_world (override_uninitialize m W) ∗ open_region_many l (override_uninitialize m W).
  Proof.
    intros Heq Hmono Hntemp. iIntros "Hsts Hr".
    rewrite open_region_many_eq /open_region_many_def.
    iDestruct "Hr" as (M Mρ) "(HR & % & % & Hr)".
    iDestruct (full_sts_Mρ_agree_weaker_delete_list with "Hsts Hr") as %Hagree;auto.
    { intros a [Ha Hnin]. apply elem_of_gmap_dom. rewrite lookup_delete_list_notin;auto.
      rewrite H in Ha. apply elem_of_gmap_dom in Ha. auto. }
    iFrame. iExists M,Mρ. iFrame. repeat iSplit;auto.
    - rewrite -H. rewrite override_uninitialize_std_sta_dom;auto.
      apply elem_of_subseteq. intros x [y Hy]%elem_of_gmap_dom.
      apply elem_of_gmap_dom. rewrite Hmono;eauto.
    - destruct (decide (m = ∅));subst.
      rewrite override_uninitialize_empty. iFrame.
      apply extract_lo in n as [a [Ha Hle] ].
      iApply (region_map_uninitialized_monotone _ _ _ _ a with "Hr").
      eapply related_sts_pub_world_monostatic_to_uninitialized;eauto.
      intros a'' Hle''. destruct (m !! a'') eqn:Hsome.
      + rewrite delete_list_None;auto. rewrite -Heq. apply elem_of_elements.
        apply elem_of_gmap_dom. eauto.
      + assert (a'' ∉ l) as Hnin;[rewrite -Heq;intros [? Hcontr]%elem_of_elements%elem_of_gmap_dom;congruence|].
        rewrite lookup_delete_list_notin//. destruct (Mρ !! a'') eqn:Hsome'';[|eauto].
        assert (is_Some(W.1 !! a'')) as [y Hy];[apply elem_of_gmap_dom;rewrite H -H0;apply elem_of_gmap_dom;eauto|].
        assert (delete_list l Mρ !! a'' = Some y) as Hy';[auto|].
        rewrite lookup_delete_list_notin// in Hy'. rewrite Hsome'' in Hy';inversion Hy';subst.
        rewrite -Hy. apply Hntemp with a;eauto.
  Qed.

  Lemma region_close_monostatic_to_uninitialized (m: gmap Addr Word) W :
    (∀ a a' : Addr, is_Some (m !! a) ∧ (a <= a')%a → W.1 !! a' ≠ Some Monotemporary) →
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world W
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
         a ↦ₐ v ∗ rel a φ)
    ∗ sts_state_std_many m (λ _, Monostatic m)
    ==∗
    sts_full_world (override_uninitialize m W)
    ∗ region (override_uninitialize m W).
  Proof.
    iIntros (Hcond) "(HR & Hsts & Hres & Hst)".
    iDestruct (sts_full_state_std_many with "[Hsts Hst]") as %?. by iFrame.
    iDestruct (region_update_multiple_states_uninit with "[$Hsts $Hst]") as ">[Hsts Hst]".
    iModIntro.
    iDestruct (open_region_world_monostatic_to_uninitialized with "Hsts HR") as "(Hsts & HR)"; eauto.
    { intros a Hsome. revert H; rewrite Forall_forall =>H. apply H, elem_of_elements, elem_of_gmap_dom;auto. }
    iDestruct (region_close_uninitialized_many with "[$HR $Hres $Hst $Hsts]") as "(?&?)".
    iFrame.
  Qed.

  (* Similarly, we also want to reinstate static regions back into monotemporary. Again, this is not a public
     transition, and we have to make sure there are no new monotemporary addresses left. *)

  Lemma related_sts_pub_world_monostatic_to_monotemporary a m l W :
    Forall (λ a', W.1 !! a' = Some (Monostatic m)) l →
    Forall (λ a', a <= a')%a l →
    related_sts_a_world W (std_update_multiple W l Monotemporary) a.
  Proof.
    intros Hforall Hcond.
    induction l.
    - simpl. apply related_sts_a_refl_world.
    - apply Forall_cons in Hforall as [Ha0 Hl].
      apply Forall_cons in Hcond as [Hle Hl'].
      specialize (IHl Hl Hl') as IHl.
      eapply related_sts_a_trans_world;[by apply IHl|].
      split;simpl.
      2: { apply related_sts_pub_plus_refl. }
      split.
      { rewrite dom_insert_L. set_solver. }
      intros a' x' y' Hx' Hy'.
      destruct (decide (a0 = a')).
      + subst. rewrite lookup_insert in Hy'. simplify_eq.
        destruct (decide (a' ∈ l)).
        ++ rewrite std_sta_update_multiple_lookup_in_i// in Hx'. simplify_eq;left.
        ++ rewrite std_sta_update_multiple_lookup_same_i// in Hx'. rewrite Ha0 in Hx'.
           simplify_eq.
           destruct (decide (le_a a a'));try solve_addr.
           eright;[|left]. right. constructor.
      + rewrite lookup_insert_ne// in Hy'.
        rewrite Hx' in Hy'. inversion Hy';left.
  Qed.

  Lemma region_close_monotemporary_many (m: gmap Addr Word) W:
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
        monotemp_resources W φ a ∗ rel a φ)
    ∗ sts_state_std_many m (λ _, Monotemporary)
    ∗ sts_full_world W
    -∗
    region W ∗ sts_full_world W.
  Proof.
    pattern m. revert m. eapply map_ind.
    - iIntros "(Hor & ? & ? & Hsts)". rewrite dom_empty_L elements_empty.
      iDestruct (region_open_nil with "Hor") as "Hor". iFrame.
    - iIntros (a γp m Hma HInd) "(HR & Htmp & Hst & Hsts)".
      iDestruct (open_region_many_permutation with "HR") as "HR".
      { rewrite dom_insert elements_union_singleton // not_elem_of_dom //. }
      iDestruct (big_sepM_insert with "Hst") as "[Hsta Hst]"; eauto.
      iDestruct (sts_full_state_std with "Hsts Hsta") as %HWa.
      iDestruct (big_sepM_insert with "Htmp") as "[Ha Htmp]"; eauto.
      iDestruct "Ha" as (? ?) "(Hatmp&?)".
      iDestruct "Hatmp" as (?) "(?&?&?)".
      iApply HInd. iFrame.
      iApply (region_close_next _ _ _ a _ Monotemporary).
      + congruence.
      + intros [? ?]. congruence.
      + intros [? ?]. congruence.
      + intros [? ?]%elem_of_elements%elem_of_gmap_dom. congruence.
      + iFrame.
    Unshelve. auto.
  Qed.

  Lemma full_sts_Mρ_agree_weaker_delete_list_monotemp W M Mρ l (m : gmap Addr Word) :
    elements (dom (gset Addr) m) ≡ₚ l →
    (* NB: only the forward direction of dom_equal (std_sta W) M is actually needed *)
    (∀ a, a ∈ dom (gset Addr) W.1 ∧ a ∉ l → a ∈ dom (gset Addr) (delete_list l M)) →
    (* NB: only one direction of this assumption is needed, and only for the reverse *)
  (*      direction of the lemma *)
    (* dom (gset Addr) Mρ = dom (gset Addr) M → *)
    sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Monotemporary) -∗
    region_map_def (delete_list l M) Mρ W -∗
    ⌜∀ (a:Addr) ρ, (std W) !! a = Some ρ ∧ a ∉ l → Mρ !! a = Some ρ⌝.
  Proof.
    iIntros (Heql HWM) "Hfull Hr".
    iAssert (∀ (a:Addr) ρ, ⌜ std W !! a = Some ρ ∧ a ∉ l⌝ → ⌜ Mρ !! a = Some ρ ⌝)%I as %?.
    { iIntros (a ρ [Haρ Hnin]).
      assert (is_Some ((delete_list l M) !! a)) as [γp Hγp].
      { apply elem_of_gmap_dom. apply HWM. split;auto. apply elem_of_gmap_dom. eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). apply encode_inj.
      rewrite std_sta_update_multiple_lookup_same_i// in Haρ'.
      rewrite Haρ in Haρ'. congruence. rewrite Heql. auto. } auto.
  Qed.

  Lemma open_region_world_monostatic_to_monotemporary l m W :
    (elements (dom (gset Addr) m) ≡ₚl) →
    (∀ (a : Addr), is_Some (m !! a) → W.1 !! a = Some (Monostatic m)) →
    (∀ (a a' : Addr), is_Some (m !! a) ∧ (a <= a')%a → W.1 !! a' ≠ Some Monotemporary) →
    sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Monotemporary) -∗
    open_region_many l W
    -∗
    sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Monotemporary)
    ∗ open_region_many l (std_update_multiple W (elements (dom (gset Addr) m)) Monotemporary).
  Proof.
    intros Heq Hmono Hntemp. iIntros "Hsts Hr".
    rewrite open_region_many_eq /open_region_many_def.
    iDestruct "Hr" as (M Mρ) "(HR & % & % & Hr)".
    iDestruct (full_sts_Mρ_agree_weaker_delete_list_monotemp with "Hsts Hr") as %Hagree;auto.
    { intros a [Ha Hnin]. apply elem_of_gmap_dom. rewrite lookup_delete_list_notin;auto.
      rewrite H in Ha. apply elem_of_gmap_dom in Ha. auto. }
    iFrame. iExists M,Mρ. iFrame. repeat iSplit;auto.
    - rewrite -H. rewrite -std_update_multiple_dom_equal//.
      intros i Hi%elem_of_elements%elem_of_gmap_dom.
      apply elem_of_gmap_dom. rewrite Hmono;eauto.
    - destruct (decide (m = ∅));subst.
      rewrite dom_empty_L elements_empty /=. iFrame.
      apply extract_lo in n as [a [Ha Hle] ].
      iApply (region_map_uninitialized_monotone _ _ _ _ a with "Hr").
      eapply related_sts_pub_world_monostatic_to_monotemporary with m;eauto.
      { apply Forall_forall. intros x Hx%elem_of_elements%elem_of_gmap_dom. auto. }
      { apply Forall_forall. intros x Hx%elem_of_elements%elem_of_gmap_dom. auto. }
      intros a'' Hle''. destruct (m !! a'') eqn:Hsome.
      + rewrite delete_list_None;auto. rewrite -Heq. apply elem_of_elements.
        apply elem_of_gmap_dom. eauto.
      + assert (a'' ∉ l) as Hnin;[rewrite -Heq;intros [? Hcontr]%elem_of_elements%elem_of_gmap_dom;congruence|].
        rewrite lookup_delete_list_notin//. destruct (Mρ !! a'') eqn:Hsome'';[|eauto].
        assert (is_Some(W.1 !! a'')) as [y Hy];[apply elem_of_gmap_dom;rewrite H -H0;apply elem_of_gmap_dom;eauto|].
        assert (delete_list l Mρ !! a'' = Some y) as Hy';[auto|].
        rewrite lookup_delete_list_notin// in Hy'. rewrite Hsome'' in Hy';inversion Hy';subst.
        rewrite -Hy. apply Hntemp with a;eauto.
  Qed.

  Lemma future_a_mono_is_future_pub_mono (φ: _ → iProp Σ) v a :
    future_pub_a_mono a φ v -∗ future_pub_mono φ v.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrel). iApply "H". iPureIntro.
    eauto using related_sts_pub_a_world.
  Qed.

  Lemma future_priv_mono_is_future_pub_mono (φ: _ → iProp Σ) v :
    future_priv_mono φ v -∗ future_pub_mono φ v.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrel). iApply "H". iPureIntro.
    eauto using related_sts_pub_priv_world.
  Qed.

  Lemma future_priv_mono_is_future_a_mono (φ: _ → iProp Σ) v a :
    future_priv_mono φ v -∗ future_pub_a_mono a φ v.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrel). iApply "H". iPureIntro.
    apply related_sts_pub_plus_priv_world.
    eapply related_sts_a_pub_plus_world;eauto.
  Qed.

  Lemma future_a_mono_is_future_a_mono (φ: _ → iProp Σ) v a a' :
    (a <= a')%a →
    future_pub_a_mono a φ v -∗ future_pub_a_mono a' φ v.
  Proof.
    iIntros (Hle) "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrel). iApply "H". iPureIntro.
    eapply related_sts_a_weak_world;[|eauto]. solve_addr.
  Qed.


  (* In this version the user is only required to show that the resources are valid in the updated world *)
  (* This is indeed the only way to state this lemma! we cannot "address stratify" from static to monotemporary
     Which is why we in the above case go all the way to uninitialized first *)
  Lemma region_close_monostatic_to_monotemporary (m: gmap Addr Word) W :
    (∀ a a' : Addr, is_Some (m !! a) ∧ (a <= a')%a → W.1 !! a' ≠ Some Monotemporary) →
    open_region_many (elements (dom (gset Addr) m)) W
    ∗ sts_full_world W
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
         monotemp_resources (std_update_multiple W (elements (dom (gset Addr) m)) Monotemporary) φ a ∗ rel a φ)
    ∗ sts_state_std_many m (λ _, Monostatic m)
    ==∗
    sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) Monotemporary)
    ∗ region (std_update_multiple W (elements (dom (gset Addr) m)) Monotemporary).
  Proof.
    iIntros (Hcond) "(HR & Hsts & Hres & Hst)".
    iDestruct (sts_full_state_std_many with "[Hsts Hst]") as %?. by iFrame.
    iDestruct (region_update_multiple_states with "[$Hsts $Hst]") as ">[Hsts Hst]".
    iModIntro.
    iDestruct (open_region_world_monostatic_to_monotemporary with "Hsts HR") as "(Hsts & HR)"; eauto.
    { intros a Hsome. revert H; rewrite Forall_forall =>H. apply H, elem_of_elements, elem_of_gmap_dom;auto. }
    iDestruct (region_close_monotemporary_many with "[HR Hres Hst Hsts]") as "(?&?)";iFrame.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------ Allocate a Static region from a Revoked one ------------------ *)

  Lemma related_sts_pub_a_world_static W W' m i a :
    (std W !! i) = Some (Monostatic m) ->
    (i < a)%a →
    related_sts_a_world W W' a ->
    (std W' !! i) = Some (Monostatic m).
  Proof.
    intros Hsta Hcond [ [Hdom1 Hrelated_std] _].
    assert (is_Some (std W' !! i)) as [y Hy].
    { apply elem_of_gmap_dom. assert (i ∈ dom (gset Addr) (std W));[apply elem_of_gmap_dom;eauto|]. set_solver. }
    eapply Hrelated_std in Hsta;[|eauto].
    apply rtc_implies with _ Rpub _ _ in Hsta.
    2: { intros. rewrite decide_False in H;auto. solve_addr. }
    eapply std_rel_pub_rtc_Monostatic in Hsta;[|eauto]. subst. auto.
  Qed.

  Lemma related_sts_priv_world_static W l (m' : gmap Addr Word) :
    Forall (λ a : Addr, (std W) !! a = Some Revoked) l →
    related_sts_priv_world W (std_update_multiple W l (Monostatic m')).
  Proof.
    intros Hforall.
    induction l.
    - apply related_sts_priv_refl_world.
    - eapply related_sts_priv_trans_world;[apply IHl|].
      + apply Forall_cons_1 in Hforall as [_ Hforall]. auto.
      + split;[|rewrite std_update_multiple_loc_rel;apply related_sts_priv_refl].
        split.
        ++ rewrite /std_update dom_insert_L. set_solver.
        ++ intros j x0 y Hx0 Hy.
           destruct (decide (a = j)).
           +++ subst. rewrite lookup_insert in Hy. inversion Hy; subst.
               apply Forall_cons_1 in Hforall as [Hi _].
               destruct (decide (j ∈ l)).
               { rewrite std_sta_update_multiple_lookup_in_i in Hx0; auto. inversion Hx0. left. }
               rewrite std_sta_update_multiple_lookup_same_i in Hx0; auto.
               rewrite /revoke /std /= in Hi.
               rewrite Hi in Hx0. inversion Hx0; subst.
               right with Monotemporary.
               { left. constructor. }
               right with (Monostatic m');[|left]. right. right. constructor.
           +++ rewrite /= lookup_insert_ne in Hy;auto. rewrite Hx0 in Hy; inversion Hy; subst; left.
  Qed.

  Lemma related_sts_priv_world_static2 W l (m' : gmap Addr Word) :
    Forall (λ a : Addr, ∃ ρ, (std W) !! a = Some ρ /\ ρ <> Permanent) l →
    related_sts_priv_world W (std_update_multiple W l (Monostatic m')).
  Proof.
    intros Hforall.
    induction l.
    - apply related_sts_priv_refl_world.
    - eapply related_sts_priv_trans_world;[apply IHl|].
      + apply Forall_cons_1 in Hforall as [_ Hforall]. auto.
      + split;[|rewrite std_update_multiple_loc_rel;apply related_sts_priv_refl].
        split.
        ++ rewrite /std_update dom_insert_L. set_solver.
        ++ intros j x0 y Hx0 Hy.
           destruct (decide (a = j)).
           +++ subst. rewrite lookup_insert in Hy. inversion Hy; subst.
               apply Forall_cons_1 in Hforall as [Hi _].
               destruct (decide (j ∈ l)).
               { rewrite std_sta_update_multiple_lookup_in_i in Hx0; auto. inversion Hx0. left. }
               rewrite std_sta_update_multiple_lookup_same_i in Hx0; auto.
               rewrite /revoke /std /= in Hi.
               destruct Hi as [ρ [Hi Hi'] ].
               rewrite Hi in Hx0. inversion Hx0; subst.
               destruct x0; try congruence.
               { eright. right. right. constructor.
                 left. }
               { right with Monotemporary. left; constructor.
                 eright. right;right. constructor.
                 left. }
               { eright. right;left;econstructor.
                 eright. right;right. constructor.
                 left. }
               { eright. left;constructor.
                 eright. right;right;constructor. left. }
           +++ rewrite /= lookup_insert_ne in Hy;auto. rewrite Hx0 in Hy; inversion Hy; subst; left.
  Qed.

  Lemma std_update_multiple_dom_equal_eq W (M: gmap Addr (gname)) (m: gmap Addr Word) ρ :
    dom (gset Addr) (std W) = dom (gset Addr) M ->
    dom (gset Addr) m ⊆ dom (gset Addr) M ->
    dom (gset Addr) (std (std_update_multiple W (elements (dom (gset Addr) m)) ρ)) = dom (gset Addr) M.
  Proof.
    intros Hdom Hsub.
    induction m using map_ind.
    - rewrite dom_empty_L elements_empty /=. rewrite Hdom. auto.
    - rewrite dom_insert_L.
      assert (elements ({[i]} ∪ dom (gset Addr) m) ≡ₚ i :: elements (dom (gset Addr) m)) as Heq.
      { apply elements_union_singleton. apply not_elem_of_dom. auto. }
      apply std_update_multiple_permutation with (W:=W) (ρ:=ρ) in Heq.
      rewrite Heq /= dom_insert_L /=. rewrite IHm.
      + assert (i ∈ dom (gset Addr) M) as Hin.
        { apply Hsub. rewrite dom_insert_L. set_solver. }
        set_solver.
      + rewrite dom_insert_L in Hsub. set_solver.
  Qed.

  (* The difficulty with static regions is that if one of the addresses is in its static state, all others must be.
     We can therefore not update them one by one (since invariants will break in the middle of the state change).
     Instead, we need to:
              (1) assert that the states are all curently Revoked + delete them from the region map
              (2) update the full sts for all addresses in the static region
              (3) insert the updated states back into the region map
   *)

  (* (1) assert that the states are all curently Revoked + delete them from the region map *)
  Lemma region_revoked_to_static_preamble W M Mρ (m: gmap Addr Word) :
    region_map_def M Mρ W -∗
    ([∗ map] a↦v ∈ m, ∃ φ, a ↦ₐ v ∗ rel a φ) -∗
    RELS M -∗
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    ∗ RELS M
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗
                              a ↦ₐ v ∗ rel a φ ∗ sts_state_std a Revoked).
  Proof.
    iIntros "Hr Hmap HM".
    iInduction (m) as [|x l] "IH" using map_ind.
    - rewrite difference_het_empty difference_het_empty /= big_sepM_empty big_sepM_empty.
      iFrame.
    - rewrite difference_het_insert_r difference_het_insert_r.
      iDestruct (big_sepM_insert with "Hmap") as "[Hx Hmap]";auto.
      iDestruct ("IH" with "Hr Hmap HM") as "(Hr & HM & Hmap)". iClear "IH".
      iDestruct "Hx" as (φ) "[Hx Hrel]".
      rewrite rel_eq /rel_def REL_eq /REL_def RELS_eq /RELS_def.
      iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)".
      iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq.
      assert (M ∖∖ m = <[x:=γpred]> (delete x (M ∖∖ m))) as HMeq'.
      { rewrite HMeq. rewrite insert_delete insert_delete. rewrite difference_het_insert_l; auto.
        by rewrite insert_insert. }
      rewrite HMeq'.
      iDestruct (big_sepM_insert with "Hr") as "[Hxinv Hr]";[by rewrite lookup_delete|].
      iDestruct "Hxinv" as (ρ Hρ) "[Hstate Hinv]".
      iAssert (⌜ρ = Revoked⌝)%I as %Heqρ.
      { destruct ρ;auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as ( φ'  Hpers) "[Hsaved Hinv]"; simplify_eq.
          iDestruct "Hinv" as (v' ) "[Hinv _]".
          iDestruct (addr_dupl_false with "Hx Hinv") as "Hf"; auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as (φ'  Hpers) "[Hsaved Hinv]"; simplify_eq.
          iDestruct "Hinv" as (v' ) "[Hinv _]".
          iDestruct (addr_dupl_false with "Hx Hinv") as "Hf"; auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as ( φ'  Hpers) "[Hsaved Hinv]"; simplify_eq.
          iDestruct "Hinv" as (v Hlookup) "[Hinv _]"; simplify_eq.
          iDestruct (addr_dupl_false with "Hx Hinv") as "Hf"; auto.
        - iApply bi.False_elim.
          iDestruct "Hinv" as ( φ'  Hpers) "[Hsaved Hinv]"; simplify_eq.
          iDestruct (addr_dupl_false with "Hx Hinv") as "Hf"; auto.
      }
      subst ρ. iDestruct "Hinv" as (φ' Hpers) "[#Hsaved _]".
      iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros;by rewrite Hρ|].
      iFrame. iSplitL "Hr".
      { rewrite delete_insert;[|by rewrite lookup_delete]. iFrame. }
      iApply big_sepM_insert;auto. iFrame. iExists φ'. simplify_eq. repeat iSplit;auto.
  Qed.

  (* (2) is simply lemma [region_update_multiple_states] *)

  (* (3) insert the updated states back into the region map *)
  (* note that the following statement is a generalisation of the lemma which has fully updated the map *)
  (* m' represents the part of the map which has been closed thus far. This lemma can be applied to m' = m,
     where we would need to establish that indeed all adresses in the domain of (m \\ m) are Static (that is
     to say that none of the addresses in the beginning are Static) *)
  Lemma region_revoked_to_static_close_mid W M M' Mρ m m' :
    (forall (x : Addr) (γp : gname), M !! x = Some γp -> M' !! x = Some γp) ->
    dom (gset Addr) m ⊆ dom (gset Addr) m' ->
    (forall a ρ, m !! a = Some ρ -> m' !! a = Some ρ) ->
    (∀ a, is_Some(m !! a) -> is_Some(M !! a)) ->
    (∀ a' : Addr, a' ∈ dom (gset Addr) (m' ∖∖ m) → ((Mρ ∖∖ m) !! a' = Some (Monostatic m'))) ->
    dom (gset Addr) M ⊆ dom (gset Addr) Mρ ->
    region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    -∗ RELS M'
    -∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ a ↦ₐ v ∗ rel a φ ∗ sts_state_std a (Monostatic m'))
    -∗ ∃ Mρ', region_map_def M Mρ' W
            ∗ RELS M'
            ∗ ⌜dom (gset Addr) Mρ' = dom (gset Addr) Mρ⌝
            ∗ ⌜∀ a' : Addr, a' ∈ dom (gset Addr) m' → Mρ' !! a' = Some (Monostatic m')⌝.
  Proof.
    iIntros (HsubM Hsub Hsame HmM Hmid Hdom) "Hr HM Hmap".
    iRevert (HsubM HmM Hmid Hdom). iInduction (m) as [|x w] "IH" using map_ind forall (M Mρ) .
    - iIntros (HsubM HmM Hmid Hdom). rewrite difference_het_empty difference_het_empty /=. iExists Mρ. iFrame.
      rewrite !difference_het_empty in Hmid. auto.
    - iIntros (HsubM HmM Hmid Hdom).
      rewrite !difference_het_insert_r !difference_het_delete_assoc.
      iDestruct (big_sepM_insert with "Hmap") as "[Hx Hmap]";auto.
      iDestruct "Hx" as (φ Hpers) "(Hx & #Hrel & Hstate)".
      iAssert (region_map_def (delete x M ∖∖ m) (<[x:=Monostatic m']> Mρ ∖∖ m) W) with "[Hr]" as "Hr".
      { iApply (big_sepM_mono with "Hr").
        iIntros (a y Ha) "Hr".
        iDestruct "Hr" as (ρ Ha') "[Hstate Hρ]".
        assert (a ≠ x) as Hne'.
        { intros Hcontr; subst a. rewrite -difference_het_delete_assoc lookup_delete in Ha. done. }
        iExists ρ. iFrame. iSplitR.
        { rewrite difference_het_insert_l; auto. rewrite lookup_insert_ne;auto.
          rewrite -difference_het_delete_assoc lookup_delete_ne in Ha';auto. }
        destruct ρ; iFrame.
        { iDestruct "Hρ" as (Heq' Hpers') "[Hsaved Hρ]".
          iDestruct "Hρ" as (v' ?) "[Ha #Hforall]".
          iExists _. repeat iSplit;auto. iExists v'. repeat iSplit;auto. iDestruct "Hforall" as %Hforall.
          iPureIntro. intros a' Hag. destruct (decide (x = a')).
          - subst. apply Hforall in Hag. rewrite -difference_het_delete_assoc lookup_delete in Hag. done.
          - rewrite difference_het_insert_l; auto. rewrite lookup_insert_ne;auto.
            apply Hforall in Hag. rewrite -difference_het_delete_assoc lookup_delete_ne in Hag;auto. }
      }
      iDestruct ("IH" with "[] [] Hr HM Hmap [] [] [] []") as (Mρ') "(Hr & HM & #Hforall)".
      { rewrite dom_insert_L in Hsub. iPureIntro. set_solver. }
      { iPureIntro. intros a ρ Ha. apply Hsame. by simplify_map_eq. }
      { iPureIntro. intros x0 γp Hx0.
        assert (x ≠ x0) as Hne';[intros Hcontr;subst;rewrite lookup_delete in Hx0;done|].
        rewrite lookup_delete_ne in Hx0; auto. }
      { iPureIntro. intros a [y Ha]. destruct (decide (a = x)).
        - subst. rewrite Ha in H. done.
        - rewrite lookup_delete_ne;auto. apply HmM. rewrite lookup_insert_ne;auto. rewrite Ha. eauto.
      }
      { iPureIntro. intros a' Hin.
        destruct (decide (x = a')).
        - subst. rewrite difference_het_insert_l; auto. apply lookup_insert.
        - rewrite difference_het_insert_l; auto. rewrite lookup_insert_ne;auto.
          repeat rewrite difference_het_insert_r in Hmid.
          specialize (Hmid a'). rewrite lookup_delete_ne in Hmid;auto. apply Hmid.
          rewrite dom_delete. set_solver.
      }
      { iPureIntro. rewrite dom_delete dom_insert_L. set_solver. }
      iDestruct "Hforall" as %[Hdom' Hforall].
      assert (is_Some (M !! x)) as [γp HMx].
      { apply HmM. rewrite lookup_insert. eauto. }
      assert (M' !! x = Some γp) as HM'x;auto.
      rewrite rel_eq /rel_def RELS_eq /RELS_def REL_eq /REL_def.
      iDestruct "Hrel" as (γpred') "[HREL Hsaved']".
      iDestruct (reg_in γrel M' with "[$HM $HREL]") as %HMeq.
      rewrite HMeq in HM'x. rewrite lookup_insert in HM'x. inversion HM'x.
      iDestruct (big_sepM_insert _ _ x γp with "[$Hr Hx Hstate]") as "Hr";[by rewrite lookup_delete|..].
      { iExists (Monostatic m').
        iSplitR.
        - iPureIntro. apply Hforall. rewrite dom_insert_L in Hsub. set_solver.
        - iFrame. iExists _. repeat iSplit;auto.
          iExists w. iFrame. repeat iSplit;auto. iPureIntro. apply Hsame. subst. apply lookup_insert.
      }
      apply insert_id in HMx. rewrite insert_delete HMx.
      iExists Mρ'. iFrame. repeat iSplit;auto. iPureIntro.
      rewrite Hdom' dom_insert_L.
      assert (x ∈ dom (gset Addr) Mρ) as Hin;[|set_solver].
      apply elem_of_subseteq in Hdom. apply Hdom. apply elem_of_gmap_dom. apply HmM. rewrite lookup_insert; eauto.
  Qed.

  Lemma RELS_sub M (m : gmap Addr Word) :
    RELS M -∗ ([∗ map] a↦_ ∈ m, ∃ φ, rel a φ) -∗
    ⌜∀ (a : Addr), is_Some(m !! a) -> is_Some(M !! a)⌝.
  Proof.
    iIntros "HM Hmap".
    iIntros (a [x Hx]).
    iDestruct (big_sepM_delete _ _ a with "Hmap") as "[Ha _]";eauto.
    iDestruct "Ha" as (φ) "Hrel".
    rewrite rel_eq /rel_def REL_eq RELS_eq /REL_def /RELS_def.
    iDestruct "Hrel" as (γpred) "[Hown _]".
    iDestruct (reg_in with "[$HM $Hown]") as %HMeq.
    rewrite HMeq. rewrite lookup_insert. eauto.
  Qed.

  Lemma region_revoked_to_static_close W M Mρ m :
    dom (gset Addr) M = dom (gset Addr) Mρ ->
    RELS M
    -∗ region_map_def (M ∖∖ m) (Mρ ∖∖ m) W
    -∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗  a ↦ₐ v ∗ rel a φ ∗ sts_state_std a (Monostatic m))
    -∗ RELS M ∗ ∃ Mρ, region_map_def M Mρ W
                   ∗ ⌜∀ a' : Addr, a' ∈ dom (gset Addr) m → Mρ !! a' = Some (Monostatic m)⌝
                   ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝.
  Proof.
    iIntros (Hdom) "HM Hr Hmap".
    iDestruct (RELS_sub with "HM [Hmap]") as %Hsub.
    { iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "Ha".
      iDestruct "Ha" as (φ Hpers) "(_ & Hrel & _)". eauto.
    }
    iDestruct (region_revoked_to_static_close_mid _ _ _ _ m with "Hr HM [Hmap]") as "HH"; auto.
    { rewrite difference_het_eq_empty dom_empty_L. intros a' Hin. set_solver. }
    { rewrite Hdom. set_solver. }
    iDestruct "HH" as (Mρ') "(? & ? & % & ?)". iFrame. iExists _. iFrame. iPureIntro. congruence.
  Qed.

  Lemma region_revoked_cond_to_static W (m: gmap Addr Word) :
    revoke_condition W →
    sts_full_world W
    ∗ region W
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ a ↦ₐ v ∗ rel a φ)
    ==∗ (sts_full_world (std_update_multiple W (elements (dom (gset Addr) m)) (Monostatic m))
      ∗ region (std_update_multiple W (elements (dom (gset Addr) m)) (Monostatic m))).
  Proof.
    iIntros (Hcond) "(Hfull & Hr & Hmap)".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    iDestruct (region_revoked_to_static_preamble with "Hr [Hmap] HM") as "(Hr & HM & Hmap)".
    { iApply (big_sepM_mono with "Hmap"). iIntros (k x Hk) "Hr". iDestruct "Hr" as (? ?) "[? ?]".
      iExists _. iFrame. }
    iAssert ([∗ map] a↦v ∈ m, (∃ φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ a ↦ₐ v ∗ rel a φ)
                                 ∗ sts_state_std a Revoked)%I with "[Hmap]" as "Hmap".
    { iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "Hx".
      iDestruct "Hx" as (φ Hpers) "(Ha & Hrel & Hstate)".
      iFrame. iExists _. iFrame. auto. }
    iAssert (⌜Forall (λ a : Addr, std W !! a = Some (Revoked)) (elements (dom (gset Addr) m))⌝%I)
      as %Hforall.
    { rewrite Forall_forall. iIntros (x Hx).
      apply elem_of_elements in Hx.
      apply elem_of_gmap_dom in Hx as [pw Hpw].
      iDestruct (big_sepM_delete with "Hmap") as "[[Hx Hstate] Hmap]";[apply Hpw|].
      iDestruct "Hx" as (φ Hpers) "(Hx & #Hrel)".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hlookup. auto.
    }
    iDestruct (monotone_revoke_cond_region_def_mono with "[] [] Hfull Hr") as "[Hfull Hr]";auto.
    { iPureIntro. apply related_sts_priv_world_static with (m':=m). apply Hforall. }
    iDestruct (big_sepM_sep with "Hmap") as "[Hmap Hstates]".
    iMod (region_update_multiple_states _ _ with "[$Hfull $Hstates]") as "[Hfull Hstates]".
    iModIntro.
    iDestruct (region_revoked_to_static_close with "HM Hr [Hmap Hstates]") as "[HM Hr]";auto.
    { iDestruct (big_sepM_sep with "[$Hmap $Hstates]") as "Hmap".
      iApply (big_sepM_mono with "Hmap"). iIntros (a x Hx) "[Hx Hstate]".
      iDestruct "Hx" as (φ Hne) "(Ha & Hrel)". iExists _. iFrame. iFrame. auto.
    }
    iDestruct "Hr" as (Mρ') "[Hr #Hforall]". iDestruct "Hforall" as %[Hforall' HdomMρ'].
    iFrame.
    iExists M,Mρ'. iFrame. iSplit;auto.
    iPureIntro.
    assert (dom (gset Addr) m ⊆ dom (gset Addr) M) as Hmsub.
    { apply elem_of_subseteq. intros x Hx. rewrite -HdomMρ'.
      apply elem_of_gmap_dom. pose proof (Hforall' _ Hx) as Hx'. eauto. }
    apply std_update_multiple_dom_equal_eq;eauto.
  Qed.

  Lemma region_revoked_to_static W (m: gmap Addr Word) :
    sts_full_world (revoke W)
    ∗ region (revoke W)
    ∗ ([∗ map] a↦v ∈ m, ∃ φ, ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝ ∗ a ↦ₐ v ∗ rel a φ)
    ==∗ (sts_full_world (std_update_multiple (revoke W) (elements (dom (gset Addr) m)) (Monostatic m))
      ∗ region (std_update_multiple (revoke W) (elements (dom (gset Addr) m)) (Monostatic m))).
  Proof.
    iIntros "(Hfull & Hr & Hmap)".
    iApply region_revoked_cond_to_static;[|iFrame].
    apply revoke_conditions_sat.
  Qed.

End heap.
