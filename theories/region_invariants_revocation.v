From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export stdpp_extra iris_extra region_invariants region_invariants_transitions.
Import uPred.

Section heap.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {heapg : heapGS Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).
  Implicit Types WC : CVIEW.
  Implicit Types W : WORLD.

  (* --------------------------------------------------------------------------------------------------------- *)
  (* --------------------------------------------- REVOCATION ------------------------------------------------ *)
  (* --------------------------------------------------------------------------------------------------------- *)

  (*
     Revocation turns every temporary/temporary location state to revoked.
     Revocation is crucial to privately update state: in general,
     region states are only monotone with regards to public future
     world. To do a private update, we must thus revoke all temp
     regions, after which we only have regions that are indeed
     monotone wrt private future world.
   *)

  (* the revoke condition states that there are no Temporary states left *)
  Definition revoke_condition W C := ∀ a, (std_C W C) !! a ≠ Some Temporary.

  (* Revocation only changes the states of the standard STS collection *)
  Definition revoke_std_sta : STS_STD → STS_STD :=
    fmap (λ v, match v with
               | Temporary => Revoked
               | _ => v
               end).
  Definition revoke (WC : CVIEW) : CVIEW := (revoke_std_sta (std WC), loc WC).
  Definition revoke_C (W : WORLD) (C : CmptName) : WORLD :=
    match W !! C with
    | Some WC => <[C := revoke WC]> W
    | None => W
    end.

  (* A weaker revocation which only revokes elements from a list *)
  Fixpoint revoke_list_std_sta (l : list Addr) (fs : STS_STD) : STS_STD :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => match j with
                          | Temporary => <[i := Revoked]> (revoke_list_std_sta l' fs)
                          | _ => (revoke_list_std_sta l' fs)
                          end
               | None => (revoke_list_std_sta l' fs)
               end
    end.
  Definition revoke_list l WC : CVIEW := ((revoke_list_std_sta l (std WC)), loc WC).
  Definition revoke_list_C l (W : WORLD) (C : CmptName) : WORLD :=
    match W !! C with
    | Some WC => <[C := revoke_list l WC]> W
    | None => W
    end.

  (* TODO move *)
  Lemma dom_world_std_update W C a ρ :
    dom W ⊆ dom (<s[(C,a):=ρ]s>W).
  Proof.
    rewrite /std_update_C.
    destruct (W !! C); rewrite dom_insert_L; set_solver.
  Qed.

  Lemma related_sts_pub_cview_fresh WC a ρ :
    a ∉ dom (std WC) →
    related_sts_pub_cview WC (<s[a:=ρ]s> WC).
  Proof.
    rewrite /std_C.
    intros Hdom_sta.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (D:=gset Addr) (std WC) a) in Hdom_sta.
      intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst. rewrite Hdom_sta in Hx. inversion Hx.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma related_sts_pub_world_fresh W C a ρ :
    a ∉ dom (std_C W C) →
    related_sts_pub_world W (<s[(C,a):=ρ]s> W) C.
  Proof.
    rewrite /std_C.
    intros Hdom_sta.
    rewrite /related_sts_pub_world /=.
    split;first apply dom_world_std_update.
    intros WC WC' HWC HWC'.
    rewrite /std_update_C HWC lookup_insert in HWC'; simplify_eq.
    rewrite HWC in Hdom_sta.
    by apply related_sts_pub_cview_fresh.
  Qed.

  Lemma related_sts_pub_fresh (W : STS) a ρ i:
    i ∉ dom W.1 →
    i ∉ dom W.2 →
    related_sts_pub W.1 (<[i:=a]> W.1) W.2 (<[i:=ρ]> W.2).
  Proof.
    intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub. split;[|split;[auto|] ].
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq.
    - apply not_elem_of_dom in Hdom_sta.
       apply not_elem_of_dom in Hdom_rel.
       intros j r1 r2 r1' r2' r3 r3' Hr Hr'.
       destruct (decide (j = i)).
      + subst. rewrite Hr in Hdom_rel. done.
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy.
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

  Lemma related_sts_pub_cview_fresh_loc WC (i x : positive) r1 r2 :
    i ∉ dom (loc WC).1 →
    i ∉ dom (loc WC).2 →
    related_sts_pub_cview WC (std WC,(<[i:=x]> (loc WC).1, <[i:= (r1,r2)]> (loc WC).2)).
  Proof.
    rewrite /loc. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[apply related_sts_std_pub_refl|].
    rewrite /related_sts_pub. split;[|split].
    - rewrite dom_insert_L. set_solver.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (D:=gset positive) (loc WC).1 i) in Hdom_sta.
      apply (not_elem_of_dom (D:=gset positive) (loc WC).2 i) in Hdom_rel.
      intros j r1' r2' r1'' r2'' r3' r3''  Hr' Hr''.
      destruct (decide (j = i)).
      + subst. rewrite Hdom_rel in Hr'. inversion Hr'.
      + simplify_map_eq. repeat split;auto.
        intros x' y Hx' Hy. simplify_map_eq. left.
  Qed.

  (* TODO version with world *)
  (* Lemma related_sts_pub_world_fresh_loc W C (i x : positive) r1 r2 : *)

  Lemma related_sts_pub_cview_revoked_temp WC a :
    (std WC) !! a = Some Revoked ∨
    (std WC) !! a = Some Temporary →
    related_sts_pub_cview WC (<s[a:=Temporary]s>WC).
  Proof.
    intros Ha.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst.
        rewrite Hx in Ha.
        destruct Ha as [Ha | Ha]; inversion Ha.
        ++ rewrite lookup_insert in Hy. inversion Hy.
           right with (Temporary);[|left]. constructor.
        ++ rewrite lookup_insert in Hy. inversion Hy. left.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma related_sts_pub_world_revoked_temp W C a :
    (std_C W C) !! a = Some Revoked ∨
    (std_C W C) !! a = Some Temporary →
    related_sts_pub_world W (<s[(C,a):=Temporary]s>W) C.
    Proof.
    rewrite /std_C.
    intros Hdom_sta.
    rewrite /related_sts_pub_world /=.
    split;first apply dom_world_std_update.
    intros WC WC' HWC HWC'.
    rewrite /std_update_C HWC lookup_insert in HWC'; simplify_eq.
    rewrite HWC in Hdom_sta.
    by apply related_sts_pub_cview_revoked_temp.
    Qed.

  (* The following lemma takes a revoked region and makes it Temporary. *)

  (* In the following variant, we only require monotonicity of the updated world *)
  Lemma update_region_revoked_temp_pwl_updated E W C a p v φ `{∀ Wv, Persistent (φ Wv)} :
    let W' := (<s[ (C, a) := Temporary ]s> W) in
    (std_C W C) !! a = Some Revoked →
    isO p = false → isWL p = true →

    future_pub_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W',C, v) -∗
    rel C a p φ

    ={E}=∗

    region W' C
    ∗ sts_full_world W' C.
  Proof.
    intro.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ MC) "(Hγrel & %HMC & %Hdom & %Hdom' & Hpreds)";simplify_eq.
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct ( (reg_in C M) with "[] [$HREL $Hγrel]") as %HMeq;eauto.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %(WC & HWC & Hρ).
    rewrite /std_C HWC in Hrev.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[(C,a) := Temporary ]s> W) C) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto.
      rewrite /std_C HWC; auto.
    }
    iDestruct (region_map_monotone _ _ _ _ _ Hrelated with "Hr") as "Hr".
    assert (is_Some (MC !! a)) as [x Hsome].
    { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom.
      rewrite /std_C HWC; auto.
    }
    iDestruct (region_map_delete_nonfrozen with "Hr") as "Hr"; [intros m;congruence|].
    iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Temporary with "Hr") as "Hr";auto.
    iDestruct (big_sepM_delete _ _ a _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert|].
      iExists γ, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome.
      rewrite Hpwl.
      repeat (iSplit; auto).
    }
    subst W'.
    (* TODO insert_std and std_update_C are actually the same..... *)
    rewrite /insert_std /std_update_C HWC /=; iFrame "Hsts".
    iExists M. iFrame "∗%".
    iModIntro. iPureIntro.
    apply insert_id in Hsome. apply insert_id in Hl. rewrite -Hsome -Hl.
    rewrite /std_C lookup_insert.
    rewrite /std_C HWC in Hdom.
    split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite dom_insert_L;rewrite Hdom';set_solver.
  Qed.

  Lemma update_region_revoked_temp_nwl_updated E W C a p v φ `{∀ Wv, Persistent (φ Wv)} :
    let W' := (<s[ (C, a) := Temporary ]s> W) in
    (std_C W C) !! a = Some Revoked →
    isO p = false → isWL p = false →

    future_priv_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W',C, v) -∗
    rel C a p φ

    ={E}=∗

    region W' C
    ∗ sts_full_world W' C.
  Proof.
    intro.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ MC) "(Hγrel & %HMC & %Hdom & %Hdom' & Hpreds)";simplify_eq.
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct ( (reg_in C M) with "[] [$HREL $Hγrel]") as %HMeq;eauto.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %(WC & HWC & Hρ).
    rewrite /std_C HWC in Hrev.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[(C,a) := Temporary ]s> W) C) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto.
      rewrite /std_C HWC; auto.
    }
    iDestruct (region_map_monotone _ _ _ _ _ Hrelated with "Hr") as "Hr".
    assert (is_Some (MC !! a)) as [x Hsome].
    { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom.
      rewrite /std_C HWC; auto.
    }
    iDestruct (region_map_delete_nonfrozen with "Hr") as "Hr"; [intros m;congruence|].
    iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Temporary with "Hr") as "Hr";auto.
    iDestruct (big_sepM_delete _ _ a _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Temporary. iFrame. iSplitR;[iPureIntro;apply lookup_insert|].
      iExists γ, p, φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. rewrite Hpwl.
      repeat (iSplit; auto).
    }
    subst W'; rewrite /insert_std /std_update_C HWC /=; iFrame "Hsts".
    iExists M. iFrame "∗%".
    iModIntro. iPureIntro.
    apply insert_id in Hsome. apply insert_id in Hl. rewrite -Hsome -Hl.
    rewrite /std_C lookup_insert; rewrite /std_C HWC in Hdom.
    split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite dom_insert_L;rewrite Hdom';set_solver.
  Qed.

  Lemma update_region_revoked_temp_pwl E W C a p v φ `{∀ Wv, Persistent (φ Wv)} :
    (std_C W C) !! a = Some Revoked →
    isO p = false → isWL p = true →

    future_pub_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W,C,v) -∗
    rel C a p φ

    ={E}=∗

    region (<s[ (C, a) := Temporary ]s> W) C
    ∗ sts_full_world (<s[(C,a) := Temporary ]s>W) C.
  Proof.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    assert (related_sts_pub_world W (<s[(C,a) := Temporary ]s> W) C) as Hrelated.
    { apply related_sts_pub_world_revoked_temp; auto. }
    iDestruct ("HmonoV" $! W ((<s[ (C, a) := Temporary ]s> W)) with "[] [Hφ]") as "Hφ'"; eauto.
    iApply (update_region_revoked_temp_pwl_updated with "HmonoV Hsts Hreg Hl Hφ' Hrel");auto.
  Qed.

  Lemma update_region_revoked_temp_nwl E W C a p v φ `{∀ Wv, Persistent (φ Wv)} :
    (std_C W C) !! a = Some Revoked →
    isO p = false → isWL p = false →

    future_priv_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    a ↦ₐ v -∗
    φ (W,C,v) -∗
    rel C a p φ

    ={E}=∗

    region (<s[ (C, a) := Temporary ]s> W) C
    ∗ sts_full_world (<s[ (C, a) := Temporary ]s> W) C.
  Proof.
    iIntros (Hrev Hne Hpwl) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    assert (related_sts_priv_world W (<s[ (C, a) := Temporary ]s> W) C) as Hrelated.
    { apply related_sts_pub_priv_world,related_sts_pub_world_revoked_temp; auto. }
    iDestruct ("HmonoV" $! W ((<s[ (C, a) := Temporary ]s> W)) with "[] [Hφ]") as "Hφ'"; eauto.
    iApply (update_region_revoked_temp_nwl_updated with "HmonoV Hsts Hreg Hl Hφ' Hrel");auto.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT REVOKE ---------------------------- *)

  Definition revoke_i i :=
    match i with
    | Temporary => Revoked
    | _ => i
    end.

  Lemma revoke_list_std_sta_spec (l : list Addr) :
    forall (Wstd_sta : STS_STD) (i : Addr),
      (revoke_list_std_sta l Wstd_sta) !! i =
      match Wstd_sta !! i with
      | None => None
      | Some j => Some (if List.In_dec finz_eq_dec i l
                       then revoke_i j else j)
      end.
  Proof.
    induction l; intros.
    - simpl. destruct (Wstd_sta !! i); auto.
    - case_eq (Wstd_sta !! i); [intros j H3 | intros H3].
      { destruct (in_dec finz_eq_dec i (a :: l)).
        + destruct i0 as [A | A].
          * subst i. simpl. rewrite H3.
            destruct j;[rewrite lookup_insert;auto|rewrite IHl H3; destruct (in_dec finz_eq_dec a l);auto..].
          * simpl.
            case_eq (Wstd_sta !! a); intros.
            { destruct (decide (Temporary = r)).
              { subst. destruct (decide (i = a)).
                - subst. rewrite lookup_insert. by simplify_map_eq.
                - rewrite lookup_insert_ne//. rewrite IHl H3.
                  destruct (in_dec finz_eq_dec i l);[auto|contradiction]. }
              destruct r; try contradiction; rewrite IHl H3;
                destruct (in_dec finz_eq_dec i l); tauto. }
            { rewrite IHl H3.
              destruct (in_dec finz_eq_dec i l); tauto. }
        + simpl. case_eq (Wstd_sta !! a); intros.
          * destruct (decide (Temporary = r)).
            { subst. destruct (decide (a = i)).
              - subst. elim n. left; auto.
              - rewrite lookup_insert_ne//.
                rewrite IHl H3. destruct (in_dec finz_eq_dec i l); auto.
                elim n. right. auto. }
            destruct r; try contradiction; rewrite IHl H3;
              destruct (in_dec finz_eq_dec i l); auto;
                elim n; right; auto.
          * rewrite IHl H3.
            destruct (in_dec finz_eq_dec i l); auto.
            elim n; right; auto. }
      { simpl. case_eq (Wstd_sta !! a); intros.
        - destruct (finz_eq_dec i a); try congruence.
          destruct (decide (Temporary = r)); intros.
          + subst. rewrite lookup_insert_ne; auto.
            rewrite IHl H3; auto.
          + destruct r; try contradiction; rewrite IHl H3; auto.
        - rewrite IHl H3; auto. }
  Qed.

  Lemma revoke_list_not_elem_of_lookup i l m :
    i ∉ l →
    (revoke_list_std_sta l m) !! i = m !! i.
  Proof.
    rewrite revoke_list_std_sta_spec.
    intros; destruct (m !! i) as [x|] eqn:Hm; auto.
    destruct (in_dec finz_eq_dec i l); auto.
    eapply elem_of_list_In in i0. by simplify_map_eq.
  Qed.

  Lemma revoke_list_dom_std_sta (Wstd_sta : gmap Addr region_type) :
    revoke_std_sta Wstd_sta = revoke_list_std_sta (map_to_list Wstd_sta).*1 Wstd_sta.
  Proof.
    eapply (map_leibniz (M:=gmap Addr)). red. red. intros.
    rewrite revoke_list_std_sta_spec /revoke_std_sta lookup_fmap /revoke_i /=.
    destruct (Wstd_sta !! i) as [x|] eqn:Hwstd; rewrite Hwstd /=; auto.
    destruct (decide (Temporary = x)).
    - subst x.
      eapply elem_of_map_to_list in Hwstd as Hx.
      destruct (in_dec finz_eq_dec i (map_to_list Wstd_sta).*1); auto.
      eapply leibniz_equiv_iff. auto.
      elim n. eapply elem_of_list_In.
      eapply elem_of_list_fmap. exists (i, Temporary).
      split; auto.
    - destruct (in_dec finz_eq_dec i (map_to_list Wstd_sta).*1); auto.
      destruct x;auto; try contradiction.
      all: try eapply leibniz_equiv_iff; auto.
      destruct x;auto; try contradiction.
    - eapply leibniz_equiv_iff; auto.
      Unshelve. all: try apply _.
      all: try apply option_leibniz.
      all: try eapply Equivalence_Reflexive.
      Unshelve.
      all: apply option_equivalence; apply _.
  Qed.

  Lemma revoke_list_dom (WC : CVIEW) :
    revoke WC = revoke_list (map_to_list (std WC)).*1 WC.
  Proof.
    by rewrite /revoke_list /= -revoke_list_dom_std_sta /revoke.
  Qed.

  Lemma revoke_list_lookup_Some Wstd_sta l (a : Addr) :
    is_Some (Wstd_sta !! a) ↔ is_Some ((revoke_list_std_sta l Wstd_sta) !! a).
  Proof.
    rewrite revoke_list_std_sta_spec.
    destruct (Wstd_sta !! a); split; eauto.
  Qed.

  Lemma revoke_lookup_Some WC (i : Addr) :
    is_Some ((std WC) !! i) ↔ is_Some ((std (revoke WC)) !! i).
  Proof.
    rewrite revoke_list_dom /revoke_list /=.
    rewrite revoke_list_std_sta_spec.
    destruct (std WC !! i); eauto.
    rewrite !is_Some_alt; auto.
  Qed.

  Lemma revoke_lookup_None WC (i : Addr) :
    (std WC) !! i = None ↔ (std (revoke WC)) !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply revoke_lookup_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply revoke_lookup_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
  Qed.

  Lemma revoke_std_sta_lookup_Some Wstd_sta (i : Addr) :
    is_Some (Wstd_sta !! i) ↔ is_Some (revoke_std_sta Wstd_sta !! i).
  Proof.
    split; intros Hi.
    - assert (std (Wstd_sta, (∅,∅)) = Wstd_sta) as Heq;auto.
      rewrite -Heq in Hi.
      apply (revoke_lookup_Some ((Wstd_sta),∅) i) in Hi.
      auto.
    - assert (std (Wstd_sta, (∅,∅)) = Wstd_sta) as <-;auto.
      apply (revoke_lookup_Some ((Wstd_sta),∅) i).
      auto.
  Qed.

  Lemma revoke_lookup_Monotemp Wstd_sta i :
    (Wstd_sta !! i = Some Temporary) →
    (revoke_std_sta Wstd_sta) !! i = Some Revoked.
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec finz_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Revoked Wstd_sta i :
    (Wstd_sta !! i = Some Revoked) →
    (revoke_std_sta Wstd_sta) !! i = Some Revoked.
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec finz_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Perm Wstd_sta i :
    (Wstd_sta !! i = Some Permanent) →
    (revoke_std_sta Wstd_sta) !! i = Some Permanent.
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec finz_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_lookup_Frozen Wstd_sta i m :
    (Wstd_sta !! i = Some (Frozen m)) →
    (revoke_std_sta Wstd_sta) !! i = Some (Frozen m).
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec finz_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply elem_of_list_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_list_lookup_non_temp (Wstd_sta : STS_STD) (l : list Addr) (i : Addr) (ρ : region_type) :
    i ∈ l →
    (revoke_list_std_sta l Wstd_sta) !! i = Some ρ → ρ ≠ Temporary.
  Proof.
    intros Hin Hsome.
    rewrite revoke_list_std_sta_spec in Hsome.
    destruct (Wstd_sta !! i); try congruence.
    eapply elem_of_list_In in Hin.
    destruct (in_dec finz_eq_dec i l); try tauto.
    inv Hsome. rewrite /revoke_i.
    destruct (decide (Temporary = r)).
    - destruct r;auto;contradiction.
    - destruct r;[contradiction|auto..].
  Qed.

  Lemma revoke_std_sta_lookup_non_temp Wstd_sta (i : Addr) (ρ : region_type) :
    (revoke_std_sta Wstd_sta) !! i = Some ρ → ρ ≠ Temporary.
  Proof.
    intros Hin.
    rewrite revoke_list_dom_std_sta in Hin.
    apply revoke_list_lookup_non_temp with Wstd_sta ((map_to_list Wstd_sta).*1) i; auto.
    rewrite /std /= in Hin.
    assert (is_Some (Wstd_sta !! i)) as [x Hsome].
    { rewrite revoke_list_std_sta_spec in Hin.
      destruct (Wstd_sta !! i); eauto. }
    apply map_to_list_fst. exists x.
    apply elem_of_map_to_list. done.
  Qed.

  Lemma revoke_lookup_non_temp WC (i : Addr) (ρ : region_type) :
    (std (revoke WC)) !! i = Some ρ → ρ ≠ Temporary.
  Proof.
    intros Hin.
    rewrite revoke_list_dom in Hin.
    apply revoke_list_lookup_non_temp with (std WC) ((map_to_list (std WC)).*1) i; auto.
    rewrite /std /= in Hin.
    assert (is_Some ((std WC) !! i)) as [x Hsome].
    { rewrite revoke_list_lookup_Some. eauto. }
    apply map_to_list_fst. exists x.
    apply elem_of_map_to_list. done.
  Qed.

  Lemma revoke_monotone_dom (Wstd_sta Wstd_sta' : gmap Addr region_type) :
    dom Wstd_sta ⊆ dom Wstd_sta' →
    dom (revoke_std_sta Wstd_sta) ⊆ dom (revoke_std_sta Wstd_sta').
  Proof.
    intros Hdom.
    induction Wstd_sta using map_ind.
    - rewrite /revoke_std_sta fmap_empty dom_empty.
      apply empty_subseteq.
    - apply elem_of_subseteq in Hdom.
      assert (is_Some (Wstd_sta' !! i)) as Hsome.
      { apply elem_of_dom;apply Hdom.
        rewrite elem_of_dom. rewrite lookup_insert. eauto. }
      apply elem_of_subseteq. intros j Hj.
      rewrite elem_of_dom in Hj; rewrite elem_of_dom.
      destruct (decide (i=j));subst.
      { by apply (revoke_std_sta_lookup_Some Wstd_sta'). }
      { rewrite -revoke_std_sta_lookup_Some.
        rewrite -elem_of_dom. apply elem_of_subseteq in Hdom. apply Hdom.
        rewrite elem_of_dom. rewrite lookup_insert_ne;auto.
        apply (revoke_std_sta_lookup_Some) in Hj. rewrite lookup_insert_ne in Hj;auto.
      }
  Qed.

  Lemma revoke_monotone_lookup (Wstd_sta Wstd_sta' : gmap Addr region_type) i :
    Wstd_sta !! i = Wstd_sta' !! i →
    revoke_std_sta Wstd_sta !! i = revoke_std_sta Wstd_sta' !! i.
  Proof.
    intros Heq.
    induction Wstd_sta using map_ind.
    - rewrite lookup_empty in Heq.
      rewrite /revoke_std_sta fmap_empty lookup_empty lookup_fmap.
      destruct (Wstd_sta' !! i) eqn:Hnone; inversion Heq.
      done.
    - destruct (decide (i0 = i)).
      + subst. rewrite lookup_insert in Heq.
        rewrite /revoke_std_sta fmap_insert lookup_fmap lookup_insert -Heq /=.
        done.
      + rewrite lookup_insert_ne in Heq;auto.
        specialize (IHWstd_sta Heq).
        rewrite /revoke_std_sta fmap_insert lookup_insert_ne;auto.
  Qed.

  Lemma revoke_monotone_lookup_same (Wstd_sta : gmap Addr region_type) i :
    Wstd_sta !! i ≠ Some Temporary →
    revoke_std_sta Wstd_sta !! i = Wstd_sta !! i.
  Proof.
    intros Hneq'.
    induction Wstd_sta using map_ind.
    - done.
    - destruct (decide (i0 = i)).
      + subst. rewrite lookup_insert in Hneq'.
        rewrite /revoke_std_sta fmap_insert lookup_insert lookup_insert /=.
        f_equiv.
        destruct x eqn:Hcontr; auto.
        contradiction.
      + simplify_map_eq.
        rewrite /revoke_std_sta fmap_insert lookup_insert_ne;auto.
  Qed.

  Lemma revoke_monotone_lookup_same' (WC:CVIEW) (i: Addr) :
    std WC !! i ≠ Some Temporary ->
    std (revoke WC) !! i = std WC !! i.
  Proof. cbn. eauto using revoke_monotone_lookup_same. Qed.

  Lemma anti_revoke_lookup_Revoked Wstd_sta i :
    (revoke_std_sta Wstd_sta) !! i = Some Revoked ->
    (Wstd_sta !! i = Some Revoked) ∨ (Wstd_sta !! i = Some Temporary).
  Proof.
    intros Hrev.
    assert (is_Some (Wstd_sta !! i)) as [x Hx];[apply revoke_std_sta_lookup_Some;eauto|].
    destruct x;subst;auto;
      rewrite revoke_monotone_lookup_same in Hrev;auto;rewrite Hx;auto.
  Qed.

  Lemma revoke_dom_eq Wstd_sta :
    dom Wstd_sta = dom (revoke_std_sta Wstd_sta).
  Proof.
    apply gset_leibniz. split.
    - intros Hin.
      rewrite elem_of_dom. rewrite elem_of_dom in Hin.
      rewrite -revoke_std_sta_lookup_Some.
      eauto.
    - intros Hin.
      rewrite elem_of_dom. rewrite elem_of_dom in Hin.
      rewrite revoke_std_sta_lookup_Some.
      eauto.
  Qed.

  (* a revoked world satisfies the revoke condition *)
  Lemma revoke_conditions_sat (W : WORLD) (C : CmptName) :
    revoke_condition (revoke_C W C) C.
  Proof.
    intros a. destruct ((std_C (revoke_C W C) C) !! a) eqn:Hsome;auto.
    intros Hcontr;simplify_eq.
    rewrite /std_C /revoke_C in Hsome.
    destruct (W!!C) as [WC|] eqn:HWC; last by rewrite HWC in Hsome.
    rewrite lookup_insert in Hsome.
    apply revoke_lookup_non_temp in Hsome. done.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------- A REVOKED REGION IS MONOTONE WRT PRIVATE FUTURΕ WORLDS -------------- *)


  Lemma std_rel_priv_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (std_rel_priv) x y →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_pub x0 y0 ∨ std_rel_priv x0 y0) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - destruct j,k; inversion Hjk; try discriminate; auto.
      + apply std_rel_priv_rtc_Permanent in Hrtc; auto; subst.
        apply revoke_lookup_Monotemp in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq.
        right with Permanent; [|left]. left. constructor.
      + apply std_rel_priv_rtc_Revoked in Hrtc;auto;subst.
        apply revoke_lookup_Monotemp in Hx as Hxtemp.
        apply revoke_lookup_Revoked in Hy as Hyperm.
        simplify_eq. left.
      + subst. eapply std_rel_priv_rtc_Frozen in Hrtc;auto;subst.
        apply revoke_lookup_Monotemp in Hx as Hxtemp.
        apply revoke_lookup_Frozen in Hy as Hyperm.
        simplify_eq. right with Temporary.
        left. constructor. eright;[|left].
        right. right. constructor.
  Qed.

  Lemma std_rel_pub_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc std_rel_pub x y →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_priv x0 y0) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - destruct j,k; inversion Hjk; try discriminate; auto.
      + apply std_rel_pub_rtc_Temporary in Hrtc; auto. subst.
        apply revoke_lookup_Revoked in Hx as Hxtemp.
        apply revoke_lookup_Monotemp in Hy as Hyperm.
        simplify_eq. left.
      + apply std_rel_pub_rtc_Permanent in Hrtc; auto. subst.
        apply revoke_lookup_Revoked in Hx as Hxtemp.
        apply revoke_lookup_Perm in Hy as Hyperm.
        simplify_eq. eright;[|left]. left. constructor.
      + apply std_rel_pub_rtc_Temporary in Hrtc; auto. subst.
        apply revoke_lookup_Frozen in Hx as Hxtemp.
        apply revoke_lookup_Monotemp in Hy as Hyperm.
        rewrite Hxtemp in Hx'. rewrite Hyperm in Hy'.
        inversion Hx'; inversion Hy'; simplify_eq.
        right with Temporary.
        { left. constructor. }
        right with Revoked;[|left].
        right. constructor.
  Qed.

  Ltac revoke_i W1 W2 i :=
    (match goal with
     | H : W1 !! i = Some _
           , H' : W2 !! i = Some _ |- _ =>
       let Hxtemp := fresh "Hxtemp" in
       let Hytemp := fresh "Hytemp" in
       try (apply revoke_lookup_Monotemp in H as Hxtemp);
       try (apply revoke_lookup_Perm in H as Hxtemp);
       try (apply revoke_lookup_Revoked in H as Hxtemp);
       try (eapply revoke_lookup_Frozen in H as Hxtemp);
       try (apply revoke_lookup_Monotemp in H' as Hytemp);
       try (apply revoke_lookup_Perm in H' as Hytemp);
       try (eapply revoke_lookup_Frozen in H' as Hytemp);
       try (apply revoke_lookup_Revoked in H' as Hytemp);simplify_eq
     end).

  Lemma std_rel_monotone x y x' y' Wstd_sta Wstd_sta' i :
    Wstd_sta !! i = Some x -> Wstd_sta' !! i = Some y ->
    (revoke_std_sta Wstd_sta) !! i = Some x' → (revoke_std_sta Wstd_sta') !! i = Some y' →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_priv x0 y0) x y →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_priv x0 y0) x' y'.
  Proof.
    intros Hx Hy Hx' Hy' Hrtc.
    induction Hrtc as [Hrefl | j k h Hjk].
    - simplify_eq. rewrite -Hx in Hy.
      apply revoke_monotone_lookup in Hy.
      rewrite Hx' Hy' in Hy. inversion Hy. left.
    - destruct Hjk as [Hjk | Hjk].
      + destruct j,k; inversion Hjk; try discriminate; auto.
        * destruct h;revoke_i Wstd_sta Wstd_sta' i;try left.
          eright;[left;constructor|left].
          eright;[left;constructor|eright;[right;constructor|left]].
        * destruct h;revoke_i Wstd_sta Wstd_sta' i;try left.
          eright;[left;constructor|left].
          eright;[left;constructor|eright;[right;constructor|left]].
        * destruct h;revoke_i Wstd_sta Wstd_sta' i;try left.
          all: eright;[left;constructor|eright;[right;constructor|constructor]].
      + destruct j,k,h; inversion Hjk; try discriminate; auto;
          revoke_i Wstd_sta Wstd_sta' i; try left; try (by inversion H).
        all: try (right with Permanent; [left;constructor|eleft; constructor]).
        all: try (right with Temporary; [left;constructor|eright;[right; constructor|]; constructor]).
  Qed.

  Lemma revoke_monotone_cview (WC WC' : CVIEW) :
    related_sts_priv_cview WC WC' → related_sts_priv_cview (revoke WC) (revoke WC').
  Proof.
    destruct WC as [ Wstd_sta [Wloc_sta Wloc_rel] ].
    destruct WC' as [ Wstd_sta' [Wloc_sta' Wloc_rel'] ].
    intros [(Hdom_sta & Htransition) Hrelated_loc].
    apply revoke_monotone_dom in Hdom_sta.
    split;[split;[auto|]|auto].
    intros i x' y' Hx' Hy'.
    simpl in *.
    assert (is_Some (Wstd_sta !! i)) as [x Hx]; [apply revoke_std_sta_lookup_Some; eauto|].
    assert (is_Some (Wstd_sta' !! i)) as [y Hy]; [apply revoke_std_sta_lookup_Some; eauto|].
    apply std_rel_monotone with x y Wstd_sta Wstd_sta' i; auto. apply Htransition with i;auto.
  Qed.

  Lemma revoke_monotone (W W' : WORLD) (C : CmptName) :
    related_sts_priv_world W W' C → related_sts_priv_world (revoke_C W C) (revoke_C W' C) C.
  Proof.
    rewrite !/related_sts_priv_world !/revoke_C.
    intros (Hdom & Hrelated).
    split.
    - destruct (W!!C) as [WC|] eqn:HWC.
      + assert (exists WC', W' !! C = Some WC') as [WC' HWC'].
        { eapply (elem_of_dom_2 W C WC) in HWC.
          eapply elem_of_weaken in HWC; eauto.
          eapply (elem_of_dom W' C) in HWC.
          destruct HWC as [WC' HWC'].
          naive_solver.
        }
        rewrite HWC'.
        rewrite !dom_insert_L; set_solver.
      + destruct (W'!!C) as [WC'|] eqn:HWC'; auto.
        rewrite dom_insert_L; set_solver.
    - intros WC_rev WC_rev' HWC_rev HWC_rev'.
      destruct (W!!C) as [WC|] eqn:HWC;simplify_eq.
      assert (exists WC', W' !! C = Some WC') as [WC' HWC'].
      { eapply (elem_of_dom_2 W C WC) in HWC.
        eapply elem_of_weaken in HWC; eauto.
        eapply (elem_of_dom W' C) in HWC.
        destruct HWC as [WC' HWC'].
        naive_solver.
      }
      rewrite HWC' in HWC_rev'.
      rewrite !lookup_insert in HWC_rev,HWC_rev'; simplify_eq.
      apply revoke_monotone_cview, Hrelated; eauto.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------- REVOKED W IS A PRIVATE FUTURE WORLD TO W ---------------------- *)

  Lemma revoke_list_related_sts_priv_cons_cview WC l i :
    related_sts_priv_cview WC (revoke_list l WC) → related_sts_priv_cview WC (revoke_list (i :: l) WC).
  Proof.
    intros Hpriv.
    rewrite /revoke_list /=.
    destruct (std WC !! i) eqn:Hsome; auto.
    destruct r eqn:Htemp; auto.
    - destruct WC as [ Wstd_sta Wloc].
      destruct Hpriv as [(Hdoms & Ha) Hloc]; auto.
      split;simpl;auto.
      rewrite /related_sts_std_priv.
      simpl in *.
      split.
      + rewrite dom_insert_L. set_solver.
      + intros j x y Hx Hy.
        destruct (decide (i = j)).
        { subst.
          rewrite lookup_insert in Hy. inversion Hy.
          rewrite Hsome in Hx;inversion Hx;subst.
          right with Revoked;[|left].
          right; constructor.
        }
        rewrite lookup_insert_ne in Hy;auto.
        apply Ha with j;auto.
  Qed.

  Lemma revoke_list_related_sts_priv_cview WC l :
    related_sts_priv_cview WC (revoke_list l WC).
  Proof.
    induction l.
    - destruct WC. rewrite /revoke_list /=. apply related_sts_priv_refl_cview.
    - split;[|apply related_sts_priv_refl].
      apply revoke_list_related_sts_priv_cons_cview; auto.
  Qed.

  Lemma revoke_related_sts_priv_cview WC :
    related_sts_priv_cview WC (revoke WC).
  Proof.
    rewrite revoke_list_dom. apply revoke_list_related_sts_priv_cview.
  Qed.

  Lemma revoke_related_sts_priv_world W C :
    related_sts_priv_world W (revoke_C W C) C.
  Proof.
    rewrite /revoke_C.
    destruct (W!!C) as [WC|] eqn:HWC; last apply related_sts_priv_refl_world.
    split.
    - rewrite dom_insert_L; set_solver.
    - intros ? WC' ? HWC'; simplify_eq.
      rewrite lookup_insert in HWC'; simplify_eq.
      apply revoke_related_sts_priv_cview.
  Qed.
  (* Helper lemmas for reasoning about a revoked domain *)

  Lemma dom_equal_revoke_list (WC : CVIEW) (MC : gmap Addr (gname * Perm)) l :
    dom (std WC) = dom MC →
    dom (std (revoke_list l WC)) = dom MC.
  Proof.
    intros Hdom.
    induction l.
    - done.
    - rewrite /revoke_list /=.
      destruct (std WC !! a) eqn:Hsome; auto.
      destruct r eqn:Htemp;auto.
      all: rewrite dom_insert_L;rewrite IHl.
      all: assert (a ∈ dom MC) as Hin;[rewrite -Hdom;rewrite elem_of_dom;eauto|].
      all: try set_solver.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- IF THΕ FULL STS IS REVOKED, WΕ CAN REVOKE REGION ------------------- *)

  (* Note that Mρ by definition matches up with the full sts. Mρ starts out by being indirectly revoked *)
  Lemma monotone_revoke_region_def W C MC Mρ :
    ⌜dom (std_C W C) = dom MC⌝
    -∗ sts_full_world (revoke_C W C) C
    -∗ region_map_def W C MC Mρ
    -∗ sts_full_world (revoke_C W C) C ∗ region_map_def (revoke_C W C) C MC Mρ.
  Proof.
    iIntros (Hdom) "Hfull Hr".
    rewrite /revoke_C in Hdom |- *.
    destruct (W !! C ) as [WC|] eqn:HWC; last iFrame.
    destruct WC as [Wstd_sta Wloc].
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[HMρ Hr]".
    iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Hmonotemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_lookup_l _ _ _ a with "Hstates") as (γp) "[Hl Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hρ.
      iPureIntro.
      destruct Hρ as (WC_rev & HWC_rev & Hρ).
      rewrite /revoke_C in HWC_rev.
      rewrite lookup_insert in HWC_rev; simplify_eq.
      eapply revoke_lookup_non_temp; eauto.
    }
    iFrame.
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iDestruct (big_sepM2_sep with "[$Hstates $Hr]") as "Hr".
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hm' HM) "/= [Hstate Ha]".
    specialize (Hmonotemp a ρ Hm').
    destruct ρ;iFrame;[contradiction|].
    iDestruct "Ha" as (γpred p φ) "(%Hγp & % & Hpred & Ha)".
    iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    iFrame "∗%#".
    iNext. iApply ("HmonoV" with "[] Hφ").
    iPureIntro.
    replace (<[C:=revoke (Wstd_sta, Wloc)]> W) with (revoke_C W C).
    + apply revoke_related_sts_priv_world.
    + by rewrite /revoke_C HWC.
    Unshelve. apply _.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------- A REVOKED W IS MONOTONE WRT PRIVATE FUTURE WORLD ------------------- *)

  Lemma monotone_revoke_cond_region_def_mono
    (W W1 W2: WORLD) (C : CmptName)
    (MC : gmap Addr (gname * Perm)) (Mρ : gmap Addr region_type) :
    ⌜revoke_condition W C⌝
    -∗ ⌜related_sts_priv_world W1 W2 C⌝
    -∗ sts_full_world W C
    -∗ region_map_def W1 C MC Mρ
    -∗ sts_full_world W C ∗ region_map_def W2 C MC Mρ.
  Proof.
    iIntros (Hcond Hrelated) "Hfull Hr".
    rewrite /revoke_condition /std_C in Hcond.
    iDestruct (big_sepM_exists with "Hr") as (m') "Hr".
    iDestruct (big_sepM2_sep with "Hr") as "[HMρ Hr]".
    iAssert (∀ a ρ, ⌜m' !! a = Some ρ⌝ → ⌜ρ ≠ Temporary⌝)%I as %Hmonotemp.
    { iIntros (a ρ Hsome).
      iDestruct (big_sepM2_sep with "Hr") as "[Hstates Hr]".
      iDestruct (big_sepM2_lookup_l _ _ _ a with "Hstates") as (γp) "[_ Hstate]"; eauto.
      iDestruct (sts_full_state_std with "Hfull Hstate") as %(? & ? & Hρ); simplify_map_eq.
      iPureIntro. intros ->. specialize (Hcond a). done.
    }
    iFrame.
    iApply big_sepM_exists. iExists m'.
    iApply big_sepM2_sep. iFrame.
    iApply (big_sepM2_mono with "Hr").
    iIntros (a ρ γp Hsomeρ Hsomeγp) "[Hstate Ha] /=".
    specialize (Hmonotemp a ρ Hsomeρ).
    destruct ρ;try contradiction;iFrame.
    iDestruct "Ha" as (γpred p φ) "(%Hγp & % & Hpred & Ha)".
    iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    iFrame "∗%#".
    iNext. iApply "HmonoV";[|iFrame "#"]. auto.
    Unshelve. apply _.
  Qed.

  Lemma monotone_revoke_list_region_def_mono
    (W W1 W2: WORLD) (C : CmptName)
    (MC : gmap Addr (gname * Perm)) (Mρ : gmap Addr region_type) :
    ⌜related_sts_priv_world W1 W2 C⌝
    -∗ sts_full_world (revoke_C W C) C
    -∗ region_map_def W1 C MC Mρ
    -∗ sts_full_world (revoke_C W C) C ∗ region_map_def W2 C MC Mρ.
  Proof.
    iIntros (Hrelated) "Hfull Hr".
    pose proof (revoke_conditions_sat W).
    iApply (monotone_revoke_cond_region_def_mono with "[] [] Hfull Hr");auto.
  Qed.

  Lemma monotone_revoke_cond_region_def_mono_same
    (W W': WORLD) (C : CmptName)
    (MC : gmap Addr (gname * Perm)) (Mρ : gmap Addr region_type) :
    ⌜revoke_condition W C⌝
    -∗ ⌜related_sts_priv_world W W' C⌝
    -∗ sts_full_world W C
    -∗ region_map_def W C MC Mρ
    -∗ sts_full_world W C ∗ region_map_def W' C MC Mρ.
  Proof.
    iIntros (Hcond Hrelated) "Hfull Hr".
    iApply (monotone_revoke_cond_region_def_mono with "[] [] Hfull Hr");auto.
  Qed.

  Lemma monotone_revoke_list_region_def_mono_same
    (W W': WORLD) (C : CmptName)
    (MC : gmap Addr (gname * Perm)) (Mρ : gmap Addr region_type) :
    ⌜related_sts_priv_world W W' C⌝
    -∗ sts_full_world (revoke_C W C) C
    -∗ region_map_def (revoke_C W C) C MC Mρ
    -∗ sts_full_world (revoke_C W C) C ∗ region_map_def (revoke_C W' C) C MC Mρ.
  Proof.
    iIntros (Hrelated) "Hfull Hr".
    iApply (monotone_revoke_list_region_def_mono _ (revoke_C W C) (revoke_C W' C)
             with "[] Hfull Hr")
    ; first eauto.
    iPureIntro; apply revoke_monotone; auto.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ---------------- IF WΕ HAVE THE REGION, THEN WE CAN REVOKE THE FULL STS ---------------- *)

  (* This matches the temprary resources in the map *)
  Definition temp_resources (W : WORLD) (C : CmptName) φ (a : Addr) (p : Perm) : iProp Σ :=
    (∃ (v : Word),
           ⌜isO p = false⌝
          ∗ a ↦ₐ v
          ∗ (if isWL p
             then future_pub_mono C φ v
             else future_priv_mono C φ v)
          ∗ φ (W,C,v))%I.

  Lemma reg_get (C : CmptName) (M : relT) MC (a : Addr) (γp : leibnizO (gname * Perm)) :
    own (γrel C) (● ((λ m : gmap (finz MemNum) (leibnizO (gname * Perm)), to_agree <$> m) <$> M : relUR))
    ∧ ⌜M !! C = Some MC⌝ ∧ ⌜MC !! a = Some γp⌝
    ==∗
    (own (γrel C) (● ((λ m : gmap (finz MemNum) (leibnizO (gname * Perm)), to_agree <$> m) <$> M : relUR))
     ∗ own (γrel C) (◯ {[C := {[a := to_agree γp]}]})).
  Proof.
    iIntros "(HR & %HWC & %Hγp)".
    iApply own_op.
    iApply (own_update with "HR").
    apply auth_update_dfrac_alloc; auto.
    - apply gmap_core_id.
      intros C' MC' HMC'; eapply gmap_core_id.
      intros a' γr' Hγr'; eapply agree_core_id.
    - apply singleton_included_l.
      eexists (_ MC).
      split; eauto.
      + rewrite !lookup_fmap; apply fmap_Some_equiv.
        exists MC. split; auto.
      + apply Some_included_mono.
        apply singleton_included_l.
        exists (to_agree γp). split; auto.
        rewrite !lookup_fmap; apply fmap_Some_equiv.
        exists (γp). split; auto.
  Qed.

  Lemma region_rel_get (W : WORLD) (C : CmptName) (a : Addr) :
    (std_C W C) !! a = Some Temporary ->
    region W C ∗ sts_full_world W C
    ==∗
    region W C ∗ sts_full_world W C ∗ ∃ p φ, ⌜forall WCv, Persistent (φ WCv)⌝ ∗ rel C a p φ.
  Proof.
    iIntros (Hlookup) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ MC) "(HM & %HMC & %Hdom & %Hdom' & Hr)".
    assert (is_Some (MC !! a)) as [γp Hγp].
    { apply elem_of_dom. rewrite /std_C in Hlookup,Hdom'.
      rewrite -Hdom. rewrite elem_of_dom; eauto.
    }
    rewrite RELS_eq /RELS_def.
    iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
    iDestruct (sts_full_state_std with "Hsts Hρ") as %(WC & HWC & Hx''); simplify_eq.
    all: rewrite /std_C HWC in Hlookup .
    all: rewrite Hlookup in Hx'';inversion Hx'';subst.
    all: iDestruct "Hstate" as (γpred p φ Heq Hpers) "(#Hsaved & Ha)".
    all: iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    all: iDestruct (big_sepM_delete _ _ a with "[Hρ Ha HmonoV Hφ $Hr]") as "Hr";[eauto| |].
    { iExists Temporary. iFrame "∗#%". }
    all: iModIntro.
    all: iSplitL "HM Hr".
    { iExists M. iFrame "∗#%". }
    all: iFrame; iExists p,φ; iSplit;auto; rewrite rel_eq /rel_def REL_eq /REL_def; iExists γpred.
    all: rewrite Heq ; iFrame "Hsaved Hrel".
  Qed.


  (* TODO move earlier in the file *)
  Lemma revoke_list_C_empty C W :
    (revoke_list_C [] W C) = W.
  Proof.
    rewrite /revoke_list_C.
    destruct (W!!C)as [WC|] eqn:HWC; last done.
    rewrite /revoke_list /= insert_id ; first done.
    by rewrite HWC -surjective_pairing.
  Qed.

  Lemma monotone_revoke_list_sts_full_world_keep W C (l : list Addr) (l' : list Addr) :
    ⊢ ⌜NoDup l'⌝ → ⌜NoDup l⌝ → ⌜l' ⊆+ l⌝ →
    ([∗ list] a ∈ l', ⌜(std_C W C) !! a = Some Temporary⌝)
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke_list_C l W C) C
     ∗ region W C
     ∗ [∗ list] a ∈ l',
       ∃ p φ, ⌜forall WCv, Persistent (φ WCv)⌝
                          ∗ ▷ temp_resources W C φ a p
                          ∗ rel C a p φ).
  Proof.
    rewrite /std region_eq /region_def /=.
    iInduction (l) as [|x l] "IH" forall (l');
    iIntros (Hdup' Hdup Hsub) "(#Hrel & Hfull & Hr)".
    - iFrame. apply submseteq_nil_r in Hsub as ->. repeat rewrite big_sepL_nil.
      rewrite revoke_list_C_empty. by iFrame.
    - destruct (decide (x ∈ l')).
      + apply elem_of_list_split in e as [l1 [l2 Heq] ].
        rewrite Heq in Hsub.
        iRevert (Hsub Hdup Hdup'). rewrite Heq -Permutation_middle. iIntros (Hsub Hdup Hdup').
        apply NoDup_cons in Hdup as [Hnin Hdup].
        apply NoDup_cons in Hdup' as [Hnin' Hdup'].
        assert (x ∈ l') as Ha.
        { rewrite Heq. apply elem_of_app. right. apply elem_of_list_here. }
        apply elem_of_Permutation in Ha as [l'' Hleq].
        simpl. iDestruct "Hrel" as "[ Htemp Hrel]".
        iDestruct "Htemp" as %Htemp.
        iMod (region_rel_get with "[$Hfull Hr]") as "(Hfull & Hr & #Hx)";[apply Htemp|..].
        { rewrite region_eq /region_def. iFrame. }
        rewrite region_eq /region_def.
        iMod ("IH" with "[] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        { iPureIntro. apply submseteq_cons_l in Hsub as [k' [Hperm Hsub] ].
          apply Permutation.Permutation_cons_inv in Hperm. etrans;eauto. rewrite Hperm. done. }
        rewrite /std_C in Htemp.
        destruct (W!!C) as [WC|] eqn:HWC; last done.
        rewrite /revoke_list_C HWC /revoke_list /= /std /= Htemp.
        rewrite rel_eq /rel_def REL_eq /REL_def.
        iDestruct "Hr" as (M Mρ MC) "(HM & %HMC & % & %Hdom & Hpreds)".
        iDestruct "Hx" as (p' φ' Hpers) "Hx".
        iDestruct "Hx" as (γpred) "#(Hγpred & Hφ)".
        iDestruct ( (reg_in C M) with "[] [$HM $Hγpred]") as %HMeq; auto.
        rewrite /region_map_def.
        rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
        iDestruct "Hpreds" as "[Ha Hpreds]".
        iDestruct "Ha" as (ρ Ha) "[Hstate Ha]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %(WC' & HWC' & Hlookup); simplify_eq.
        rewrite lookup_insert in HWC'; simplify_eq.
        simpl in Hlookup. subst.
        rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
        rewrite Htemp in Hlookup. inversion Hlookup. subst ρ.
        iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        iDestruct (region_map_delete_nonfrozen with "Hpreds") as "Hpreds";[intros m; by rewrite Ha|].
        iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Revoked with "Hpreds") as "Hpreds";auto.
        iDestruct (big_sepM_insert _ _ x (γpred, p') with "[$Hpreds Hstate]") as "Hpreds"
        ; [apply lookup_delete|..]
        ; iClear "IH"
        ; iFrame "∗ #".
        iSplitR;[iPureIntro; apply lookup_insert|].
        iExists _ ;iSplit;auto.
        rewrite -HMeq.
        rewrite /insert_std lookup_insert insert_insert //=.
        iModIntro. iFrame "%∗".
        iSplit.
        {
          iPureIntro. rewrite dom_insert_L.
          assert (x ∈ dom MC) as Hin.
          { rewrite -Hdom. apply elem_of_dom. eauto. }
          revert Hin Hdom. clear; intros Hin Hdom. rewrite Hdom. set_solver.
        }
        iDestruct "Ha" as (γpred0 p0 φ0 Heq0 Hpers0) "(#Hsaved & Ha)".
        iDestruct "Ha" as (v Hne0) "(Hx & #HmonoV & #Hφ0)"; simplify_eq.
        iExists v; iFrame "%∗".
        destruct WC as [ Wstd_sta Wloc].
        iDestruct (saved_pred_agree _ _ _ _ _ (W, C, v) with "Hφ Hsaved") as "#Hφeq".
        iDestruct (internal_eq_iff with "Hφeq") as "Hφeq'".
        iSplitL "HmonoV";[|by iNext; iApply "Hφeq'"].
        destruct (isWL p0).
        ++ iApply future_pub_mono_eq_pred; auto.
        ++ iApply future_priv_mono_eq_pred; auto.
      + apply NoDup_cons in Hdup as [Hnin Hdup].
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Hcontr _] ] ].
        2: { exfalso. apply n. rewrite Hcontr. apply elem_of_list_here. }
        iMod ("IH" with "[] [] [] [$Hrel $Hfull $Hr]") as "(Hfull & Hr & Hl)"; auto.
        iDestruct "Hr" as (M Mρ MC) "(HM & %HMC & %Hdom & %Hdom' & Hr)".
        iClear "IH".
        rewrite /revoke_list_C /revoke_list /std_C /=.
        rewrite /std_C in Hdom.
        destruct (W!!C) as [WC|] eqn:HWC; auto.
        2:{ iFrame "%∗".
            rewrite dom_empty_L in Hdom.
            rewrite -Hdom in Hdom'.
            symmetry in Hdom.
            by eapply dom_empty_inv_L in Hdom',Hdom; simplify_eq.
        }
        destruct WC as [ Wstd_sta Wloc].
        destruct (Wstd_sta !! x) eqn:Hsome.
        2: { iFrame. iModIntro. rewrite Hsome. iFrame. iFrame. auto. }
        rewrite Hsome.
        destruct (decide (r = Temporary)).
        2: { destruct r; try contradiction; iFrame; iModIntro; iFrame; auto. }
        assert (is_Some (MC !! x)) as [γp Hsomea].
        { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom. eauto. }
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]"; eauto.
        iDestruct "Hx" as (ρ Ha) "[Hstate Hρ]".
        iDestruct (sts_full_state_std with "Hfull Hstate") as %(WC' & HWC' & Hlookup); simplify_eq.
        iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
        rewrite lookup_insert in HWC'; simplify_eq.
        simpl in Hlookup; subst.
        iDestruct (region_map_delete_nonfrozen with "Hr") as "Hpreds";[intros m; rewrite Ha; auto|].
        { simplify_map_eq.
          intro Hcontra. inv Hcontra.
          simpl in *.
          rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
          rewrite Hlookup in Hsome. inversion Hsome.
        }
        iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Revoked with "Hpreds") as "Hpreds";auto.
        iDestruct (big_sepM_delete _ _ x with "[Hstate $Hpreds Hρ]") as "Hr"; eauto.
        { iExists Revoked; iSplitR; first (by iPureIntro ; simplify_map_eq).
          iFrame.
          iDestruct "Hρ" as (? ? ? ? ?) "[? _]". iExists _,_,_. repeat iSplit;eauto.
        }
        iModIntro. iFrame.
        rewrite /insert_std lookup_insert insert_insert //=.
        iSplit; auto.
        iPureIntro.
        rewrite /std /= in Hdom.
        repeat (split; auto).
        rewrite dom_insert_L.
        assert (x ∈ dom MC) as Hin.
        { rewrite -Hdom'. apply elem_of_dom. eauto. }
        revert Hin Hdom'. clear; intros Hin Hdom. rewrite Hdom. set_solver.
  Qed.

  Lemma monotone_revoke_list_sts_full_world_keep_alt W C (l : list Addr) (l' : list Addr) p φ :
    ⊢ ⌜NoDup l'⌝ → ⌜NoDup l⌝ → ⌜l' ⊆+ l⌝ →
    ([∗ list] a ∈ l', ⌜(std_C W C) !! a = Some Temporary⌝ ∗ rel C a p φ)
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke_list_C l W C) C
     ∗ region W C
     ∗ [∗ list] a ∈ l', ▷ temp_resources W C φ a p ∗ rel C a p φ).
  Proof.
    iIntros (Hdupl Hdupl' Hsub) "(Htemp & Hsts & Hr)".
    iDestruct (big_sepL_sep with "Htemp") as "[Htemp Hrel]".
    iMod (monotone_revoke_list_sts_full_world_keep with "[] [] [] [$Hsts $Hr $Htemp]") as "(Hsts & Hr & Htemp)";auto.
    iFrame. iApply big_sepL_bupd.
    iDestruct (big_sepL_sep with "[$Hrel $Htemp]") as "Htemp".
    iApply (big_sepL_mono with "Htemp").
    iIntros (k y Hsome) "(#Hr & Htemp)".
    iDestruct "Htemp" as (p' φ' Hpers) "[Htemp #Hrel]".
    iModIntro. rewrite /temp_resources.
    iDestruct (rel_agree _ _ φ φ' with "[$Hrel $Hr]") as "(-> & #Hφeq')".
    iDestruct "Htemp" as (v) "(Hne & Ha & #HmonoV & Hφ)".
    iFrame "Hr".
    iExists v. iFrame "#∗%".
    repeat iSplitR.
    - destruct (isWL p');
      [iApply future_pub_mono_eq_pred_rel|iApply future_priv_mono_eq_pred_rel]; eauto.
    - iNext. iSpecialize ("Hφeq'" $! (W,C,v)). iRewrite "Hφeq'". iFrame.
  Qed.

  (* TODO move earlier in the file *)
  Lemma revoke_list_C_dom (W : WORLD) (C : CmptName) :
    revoke_C W C = revoke_list_C (map_to_list (std_C W C)).*1 W C.
  Proof.
    rewrite /revoke_C /revoke_list_C /std_C.
    destruct (W!!C) as [WC|] eqn:HWC; last done.
    by rewrite revoke_list_dom.
  Qed.

  Lemma monotone_revoke_sts_full_world_keep W C (l : list Addr) :
    ⌜NoDup l⌝ -∗
    ([∗ list] a ∈ l, ⌜(std_C W C) !! a = Some Temporary⌝)
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke_C W C) C
     ∗ region W C
     ∗ ([∗ list] a ∈ l,
          ∃ p φ, ⌜forall WCv, Persistent (φ WCv)⌝
                           ∗ ▷ temp_resources W C φ a p ∗ rel C a p φ)).
  Proof.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_C_dom.
    iAssert (⌜l ⊆+ (map_to_list (std_C W C)).*1⌝)%I as %Hsub.
    { iClear "Hfull Hr". iInduction l as [| x l] "IH".
      - iPureIntro. apply submseteq_nil_l.
      - iDestruct "Hl" as "[ Hin Hl]".
        iDestruct "Hin" as %Hin. apply NoDup_cons in Hdup as [Hnin Hdup].
        iDestruct ("IH" with "[] Hl") as %Hsub; auto.
        iPureIntro.
        assert (x ∈ (map_to_list (std_C W C)).*1) as Helem.
        { apply map_to_list_fst. exists Temporary. by apply elem_of_map_to_list. }
        apply elem_of_Permutation in Helem as [l' Hl']. rewrite Hl'.
        apply submseteq_skip. revert Hsub. rewrite Hl'; intros Hsub.
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto.
        assert (countable.encode x ∈ countable.encode <$> l) as Hcontr.
        { rewrite Heq. apply elem_of_list_here. }
        apply elem_of_list_fmap_2 in Hcontr as [y [Hxy Hy] ].
        apply encode_inj in Hxy. subst. contradiction.
    }
    iMod (monotone_revoke_list_sts_full_world_keep _ _ (map_to_list (std_C W C)).*1 l
            with "[] [] [] [$Hl $Hfull $Hr]") as "(Hfull & Hr & Hi)"; auto.
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    by iFrame.
  Qed.

  Lemma monotone_revoke_sts_full_world_keep_alt W C (l : list Addr) p φ :
    ⌜NoDup l⌝ -∗
    ([∗ list] a ∈ l, ⌜(std_C W C) !! a = Some Temporary⌝ ∗ rel C a p φ)
    ∗ sts_full_world W C ∗ region W C
    ==∗
    (sts_full_world (revoke_C W C) C
     ∗ region W C
     ∗ ([∗ list] a ∈ l, ▷ temp_resources W C φ a p ∗ rel C a p φ)).
  Proof.
    iIntros (Hdup) "(Hl & Hfull & Hr)".
    rewrite revoke_list_C_dom.
    iAssert (⌜l ⊆+ (map_to_list (std_C W C)).*1⌝)%I as %Hsub.
    { iClear "Hfull Hr". iInduction l as [| x l] "IH".
      - iPureIntro. apply submseteq_nil_l.
      - iDestruct "Hl" as "[ [Hin Hrel] Hl]".
        iDestruct "Hin" as %Hin. apply NoDup_cons in Hdup as [Hnin Hdup].
        iDestruct ("IH" with "[] Hl") as %Hsub; auto.
        iPureIntro.
        assert (x ∈ (map_to_list (std_C W C)).*1) as Helem.
        { apply map_to_list_fst. exists Temporary. by apply elem_of_map_to_list. }
        apply elem_of_Permutation in Helem as [l' Hl']. rewrite Hl'.
        apply submseteq_skip. revert Hsub. rewrite Hl'; intros Hsub.
        apply submseteq_cons_r in Hsub as [Hsub | [l'' [Heq _] ] ]; auto.
        assert (x ∈ l) as Hcontr.
        { rewrite Heq. apply elem_of_list_here. }
        subst. contradiction.
    }
    iMod (monotone_revoke_list_sts_full_world_keep_alt _ _ (map_to_list (std_C W C)).*1 l
            with "[] [] [] [$Hl $Hfull $Hr]") as "(Hfull & Hr & Hi)"; auto.
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    by iFrame.
  Qed.

  (* The following statement discards all the resources of temporary regions *)
  Lemma monotone_revoke_list_sts_full_world W C MC Mρ l :
    ⌜∀ (a : Addr), a ∈ l → is_Some (MC !! a)⌝ -∗
    ⌜dom Mρ = dom MC⌝ -∗
    ⌜NoDup l⌝ -∗
    sts_full_world W C ∗ region_map_def W C MC Mρ
    ==∗
    ∃ Mρ, ⌜dom Mρ = dom MC⌝
              ∧ (sts_full_world (revoke_list_C l W C) C ∗ region_map_def W C MC Mρ).
  Proof.
    (* rewrite /std /=. *)
    iIntros (Hin Hdom Hdup) "[Hfull Hr]".
    iInduction (l) as [|x l] "IH".
    - iExists _. rewrite revoke_list_C_empty.
      by iFrame "%∗".
    - apply NoDup_cons in Hdup as [Hnin Hdup].
      iMod ("IH" with "[] [] Hfull Hr") as (Mρ' Hdom_new) "[Hfull Hr]"; auto.
      { iPureIntro. intros a Ha. apply Hin. apply elem_of_cons. by right. }
      rewrite /revoke_list_C /revoke_list /= /std /=.
      destruct (W!!C) as [WC|] eqn:HWC; last (by iFrame).
      destruct WC as [Wstd_sta Wloc].
      destruct (Wstd_sta !! x) eqn:Hsome;[|iExists _; cbn; rewrite Hsome ; by iFrame "%∗"].
      destruct r;[|iExists _; cbn; rewrite Hsome; by iFrame..].
      destruct Hin with x as [γp Hsomea];[apply elem_of_list_here|].
      iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hρ Hr]"; eauto.
      iDestruct "Hρ" as (ρ' Hρ') "(Hstate & Ha)".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %(WC' & HWC' & Hlookup); simplify_eq.
      rewrite lookup_insert in HWC'; simplify_eq.
      simpl in Hlookup; subst.
      rewrite revoke_list_not_elem_of_lookup in Hlookup; auto.
      rewrite Hsome in Hlookup. inversion Hlookup as [Heq]. subst ρ'.
      iMod (sts_update_std _ _ _ _ (Revoked) with "Hfull Hstate") as "[Hfull Hstate]".
      iFrame.
      iDestruct (region_map_delete_nonfrozen with "Hr") as "Hr";[intros m;by rewrite Hρ'|].
      iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Revoked with "Hr") as "Hr";auto.
      iExists _.
      iDestruct "Ha" as (γpred p0 φ Heq Hpers) "[#Hsaved Ha]".
      iDestruct (big_sepM_delete _ _ x with "[$Hr Hstate]") as "$"; eauto.
      { iExists Revoked. iFrame.
        iSplitR; first (iPureIntro; apply lookup_insert).
        iExists _. iFrame "#". auto.
      }
      rewrite /insert_std lookup_insert insert_insert Hsome /=.
      iFrame "%∗".
      iPureIntro. rewrite -Hdom_new dom_insert_L.
      assert (x ∈ dom Mρ') as Hin'.
      { apply elem_of_dom;eauto. }
      set_solver.
  Qed.

  (* The following statement discards all the resources of temporary regions *)
  Lemma monotone_revoke_sts_full_world W C :
    sts_full_world W C ∗ region W C
    ==∗ (sts_full_world (revoke_C W C) C ∗ region W C).
  Proof.
    iIntros "[Hfull Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M MC Mρ) "(HM & %HMC & %Hdom & %Hdom' & Hr)".
    rewrite revoke_list_C_dom.
    iMod (monotone_revoke_list_sts_full_world _ _ _ _ (map_to_list (std_C W C)).*1
            with "[] [] [] [$Hfull $Hr]") as (Mρ' Hin) "[Hfull Hr]";auto.
    { iPureIntro. intros i Hin. apply map_to_list_fst in Hin as [x Hin].
      apply elem_of_dom. rewrite -Hdom. apply elem_of_map_to_list in Hin.
      rewrite elem_of_dom. eauto.
    }
    { iPureIntro. apply (NoDup_fst_map_to_list (M:=gmap Addr) (A:=region_type)). }
    iFrame.
    iModIntro.
    done.
  Qed.

  Lemma submseteq_dom (l : list Addr) (Wstd_sta : gmap Addr region_type) :
    Forall (λ i : Addr, Wstd_sta !! i = Some Temporary) l
    → NoDup l → l ⊆+ (map_to_list Wstd_sta).*1.
  Proof.
    generalize l.
    induction Wstd_sta using map_ind.
    + intros l' Htemps Hdup. destruct l'; auto. inversion Htemps. subst. discriminate.
    + intros l' Htemps Hdup. rewrite map_to_list_insert; auto.
      cbn.
      (* destruct on i being an element of l'! *)
      destruct (decide (i ∈ l')).
      ++ apply elem_of_list_split in e as [l1 [l2 Heq] ].
         rewrite Heq -Permutation_middle.
         apply submseteq_skip.
         rewrite Heq in Hdup.
         apply NoDup_app in Hdup as [Hdup1 [Hdisj Hdup2] ].
         apply NoDup_cons in Hdup2 as [Helem2 Hdup2].
         assert (i ∉ l1) as Helem1.
         { intros Hin. specialize (Hdisj i Hin). apply not_elem_of_cons in Hdisj as [Hcontr _]. done. }
         apply IHWstd_sta.
         +++ revert Htemps. repeat rewrite Forall_forall. intros Htemps.
             intros j Hin.
             assert (j ≠ i) as Hne.
             { intros Hcontr; subst. apply elem_of_app in Hin as [Hcontr | Hcontr]; congruence. }
             rewrite -(Htemps j);[rewrite lookup_insert_ne;auto|].
             subst. apply elem_of_app. apply elem_of_app in Hin as [Hin | Hin]; [left;auto|right].
             apply elem_of_cons;by right.
         +++ apply NoDup_app; repeat (split;auto).
             intros j Hj. specialize (Hdisj j Hj). apply not_elem_of_cons in Hdisj as [_ Hl2];auto.
      ++ apply submseteq_cons. apply IHWstd_sta; auto.
         revert Htemps. repeat rewrite Forall_forall. intros Htemps j Hin.
         specialize (Htemps j Hin).
         assert (i ≠ j) as Hneq; [intros Hcontr; subst; congruence|].
         rewrite lookup_insert_ne in Htemps;auto.
  Qed.


  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------ WE CAN REVOKΕ A REGION AND STS COLLECTION PAIR ---------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* revoke and discards temp regions *)
  Lemma monotone_revoke W C :
    sts_full_world W C ∗ region W C
    ==∗
    sts_full_world (revoke_C W C) C ∗ region (revoke_C W C) C.
  Proof.
    iIntros "[HW Hr]".
    iMod (monotone_revoke_sts_full_world with "[$HW $Hr]") as "[HW Hr]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M MC Mρ) "(HM & % & % & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame.
    iPureIntro.
    repeat (split;auto).
    rewrite /std_C in H0; rewrite /revoke_C /std_C.
    destruct (W!!C) as [WC|] eqn:HWC; simplify_map_eq; last set_solver.
    by rewrite lookup_insert -revoke_dom_eq.
  Qed.

  (* revoke and keep temp resources in list l, with unknown p and φ *)
  Lemma monotone_revoke_keep W C l :
    NoDup l ->
    ([∗ list] a ∈ l, ⌜(std_C W C) !! a = Some Temporary⌝)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    sts_full_world (revoke_C W C) C
    ∗ region (revoke_C W C) C
    ∗ [∗ list] a ∈ l,
          (∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ ▷ temp_resources W C φ a p ∗ rel C a p φ)
          ∗ ⌜(std_C (revoke_C W C) C) !! a = Some Revoked⌝.
  Proof.
    iIntros (Hdup) "(Hl & HW & Hr)".
    iAssert (⌜Forall (λ a, std_C W C !! a = Some Temporary) l⌝)%I as %Htemps.
    { iDestruct (big_sepL_forall with "Hl") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iMod (monotone_revoke_sts_full_world_keep with "[] [$HW $Hr $Hl]") as "(HW & Hr & Hl)"; eauto.
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M MC Mρ) "(HM & % & % & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iSplitR.
    - iPureIntro.
      repeat (split;auto).
      rewrite /std_C in H0; rewrite /revoke_C /std_C.
      destruct (W!!C) as [WC|] eqn:HWC; simplify_map_eq; last set_solver.
      by rewrite lookup_insert -revoke_dom_eq.
    - iApply big_sepL_sep. iFrame. iApply big_sepL_forall. iPureIntro.
      revert Htemps. rewrite (Forall_lookup _ l). intros Hl i a Ha; auto.
      specialize (Hl i a Ha).
      rewrite /std_C in H0,Hl; rewrite /revoke_C /std_C.
      destruct (W!!C) as [WC|] eqn:HWC; simplify_map_eq.
      rewrite lookup_insert.
      by apply revoke_lookup_Monotemp.
  Qed.

  (* revoke and keep temp resources in list l, with know p and φ *)
  Lemma monotone_revoke_keep_alt W C l p φ :
    NoDup l ->
    ([∗ list] a ∈ l, ⌜(std_C W C) !! a = Some Temporary⌝ ∗ rel C a p φ)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    sts_full_world (revoke_C W C) C
    ∗ region (revoke_C W C) C
    ∗ [∗ list] a ∈ l, (▷ temp_resources W C φ a p ∗ rel C a p φ)
                      ∗ ⌜(std_C (revoke_C W C) C) !! a = Some Revoked⌝.
  Proof.
    iIntros (Hdup) "(Hl & HW & Hr)".
    iAssert (⌜Forall (λ a, std_C W C !! a = Some Temporary) l⌝)%I as %Htemps.
    { iDestruct (big_sepL_sep with "Hl") as "[Htemps Hrel]".
      iDestruct (big_sepL_forall with "Htemps") as %Htemps.
      iPureIntro. apply Forall_lookup. done. }
    iMod (monotone_revoke_sts_full_world_keep_alt with "[] [$HW $Hr $Hl]") as "(HW & Hr & Hl)"; eauto.
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M MC Mρ) "(HM & % & % & % & Hpreds)".
    iDestruct (monotone_revoke_region_def with "[] [$HW] [$Hpreds]") as "[Hpreds HW]"; auto.
    iModIntro. iFrame. iSplitR.
    - iPureIntro. repeat(split;auto).
      rewrite /std_C in H0; rewrite /revoke_C /std_C.
      destruct (W!!C) as [WC|] eqn:HWC; simplify_map_eq; last set_solver.
      by rewrite lookup_insert -revoke_dom_eq.
    - iApply big_sepL_sep. iFrame. iApply big_sepL_forall. iPureIntro.
      revert Htemps. rewrite (Forall_lookup _ l). intros Hl i a Ha; auto.
      specialize (Hl i a Ha).
      rewrite /std_C in H0,Hl; rewrite /revoke_C /std_C.
      destruct (W!!C) as [WC|] eqn:HWC; simplify_map_eq.
      rewrite lookup_insert.
      by apply revoke_lookup_Monotemp.
  Qed.

  (* For practical reasons, it will be convenient to have a version of revoking where you only know what some of the
     temp regions are *)
  Lemma monotone_revoke_keep_some W C l1 l2 p φ :
    NoDup (l1 ++ l2) ->
    ([∗ list] a ∈ l1, ⌜(std_C W C) !! a = Some Temporary⌝) ∗
    ([∗ list] a ∈ l2, ⌜(std_C W C) !! a = Some Temporary⌝ ∗ rel C a p φ)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    sts_full_world (revoke_C W C) C
    ∗ region (revoke_C W C) C
    ∗ ([∗ list] a ∈ l1, (∃ p' φ, ⌜forall Wv, Persistent (φ Wv)⌝
                                             ∗ ▷ temp_resources W C φ a p'
                                             ∗ rel C a p' φ)
                        ∗ ⌜(std_C (revoke_C W C) C) !! a = Some Revoked⌝)
    ∗ [∗ list] a ∈ l2, (▷ temp_resources W C φ a p ∗ rel C a p φ)
                       ∗ ⌜(std_C (revoke_C W C) C) !! a = Some Revoked⌝.
  Proof.
    iIntros (Hdup) "(Hl1 & Hl2 & HW & Hr)".
    iDestruct (big_sepL_sep with "Hl2") as "[Hl2 #Hrels]".
    iDestruct (big_sepL_app with "[$Hl1 $Hl2]") as "Hl".
    iMod (monotone_revoke_keep with "[$HW $Hr $Hl]") as "(HW & Hr & Hl)";[auto|].
    iDestruct (big_sepL_app with "Hl") as "[Hl1 Hl2]".
    iDestruct (big_sepL_sep with "Hl2") as "[Hl2 Hrev]".
    iFrame. iApply big_sepL_sep. iFrame.
    iModIntro.
    iDestruct (big_sepL_sep with "[Hrels $Hl2]") as "Hl2";[iFrame "Hrels"|].
    iApply (big_sepL_mono with "Hl2").
    iIntros (k y Hlookup) "[Htemp #Hrel]".
    iDestruct "Htemp" as (p' φ' Hpers) "(Htemp & #Hrel')".
    rewrite /temp_resources.
    iDestruct (later_exist with "Htemp") as (v) "(Hne & Hy & #HmonoV & Hφ')".
    iDestruct (rel_agree _ _ φ φ' with "[$Hrel $Hrel']") as "[-> #Hφeq]".
    iFrame "Hrel". iApply later_exist_2. iExists (v). iFrame.
    repeat iSplitR.
    - destruct (isWL p');
      [iApply future_pub_mono_eq_pred_rel|iApply future_priv_mono_eq_pred_rel]; eauto.
    - iNext. iSpecialize ("Hφeq" $! (W,C,v)). iRewrite "Hφeq". iFrame.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------- REVOKING ALL TEMPORARY REGIONS, KNOWN AND UNKNOWN  ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* The following helper lemmas are for revoking all temporary regions in the world *)

  (* First we must assert that there exists a list of distinct addresses whose state is temporary,
     and no other address is temp*)
  Lemma extract_temps_cview WC :
    ∃ l, NoDup l ∧ (forall (a : Addr), (std WC) !! a = Some Temporary <-> a ∈ l).
  Proof.
    destruct WC as [Wstd_sta Wloc].
    induction Wstd_sta using (map_ind (M:=gmap Addr) (A:=region_type)).
    - exists []. split;[by apply NoDup_nil|]. intros a. split; intros Hcontr; inversion Hcontr.
    - destruct IHWstd_sta as [l [Hdup Hiff] ].
      assert (i ∈ dom (<[i:=x]> m)) as Hin.
      { apply elem_of_dom. rewrite lookup_insert; eauto. }
      assert (i ∉ l) as Hnin.
      { intros Hcontr. apply Hiff in Hcontr. simplify_map_eq. }
      destruct (decide (x = Temporary)); subst.
      + exists (i :: l). split;[apply NoDup_cons;split;auto|].
        intros a0. destruct (decide (i = a0)); subst.
        { rewrite lookup_insert. split; auto. intros _. apply elem_of_cons. by left. }
        rewrite lookup_insert_ne;[|intros Hcontr;congruence].
        split; intros Htemp.
        { apply elem_of_cons; right. by apply Hiff. }
        { apply elem_of_cons in Htemp as [Hcontr | Hin'];[congruence|]. apply Hiff; auto. }
      + exists l. split; auto. intros a0. split.
        { destruct (decide (i = a0));subst.
          - rewrite lookup_insert. intros Hcontr. congruence.
          - rewrite lookup_insert_ne;[apply Hiff|]. auto.
        }
        intros Hin'. destruct (decide (i = a0));[congruence|].
        rewrite lookup_insert_ne;[|intros Hcontr;congruence].
        apply Hiff; auto.
  Qed.


  Lemma extract_temps W C :
    ∃ l, NoDup l ∧ (forall (a : Addr), (std_C W C) !! a = Some Temporary <-> a ∈ l).
  Proof.
    rewrite /std_C /std /=.
    destruct (W!!C) as [WC|] eqn:HWC; cycle 1.
    { exists [].
      split;[by apply NoDup_nil|].
      intros a. split; intros Hcontr; inversion Hcontr.
    }
    apply extract_temps_cview.
  Qed.

  (* We also want to be able to split the extracted temporary regions into known and unknown *)
  Lemma extract_temps_split_cview WC l :
    NoDup l ->
    Forall (λ (a : Addr), (std WC) !! a = Some Temporary) l ->
    ∃ l', NoDup (l' ++ l) ∧ (forall (a : Addr), (std WC) !! a = Some Temporary <-> a ∈ (l' ++ l)).
  Proof.
    intros Hdup HForall.
    pose proof (extract_temps_cview WC) as [l' [Hdup' Hl'] ].
    revert HForall; rewrite Forall_forall =>HForall.
    exists (list_difference l' l). split.
    - apply NoDup_app. split;[|split].
      + apply NoDup_list_difference. auto.
      + intros a Ha. apply elem_of_list_difference in Ha as [_ Ha]; auto.
      + auto.
    - intros a. split.
      + intros Htemp.
        destruct (decide (a ∈ list_difference l' l));[by apply elem_of_app;left|].
        apply elem_of_app;right. apply Hl' in Htemp.
        assert (not (a ∈ l' ∧ a ∉ l)) as Hnot.
        { intros Hcontr. apply elem_of_list_difference in Hcontr. contradiction. }
        destruct (decide (a ∈ l)); auto.
        assert (a ∈ l' ∧ a ∉ l) as Hcontr; auto. apply Hnot in Hcontr. done.
      + intros Hin. apply elem_of_app in Hin as [Hin | Hin].
        ++ apply elem_of_list_difference in Hin as [Hinl Hninl'].
           by apply Hl'.
        ++ by apply HForall.
  Qed.

  Lemma extract_temps_split W C l :
    NoDup l ->
    Forall (λ (a : Addr), (std_C W C) !! a = Some Temporary) l ->
    ∃ l', NoDup (l' ++ l) ∧ (forall (a : Addr), (std_C W C) !! a = Some Temporary <-> a ∈ (l' ++ l)).
  Proof.
    rewrite /std_C /std /=.
    intros Hdup HForall.
    destruct (W!!C) as [WC|] eqn:HWC; cycle 1.
    - exists [].
      split.
      + apply NoDup_app. split;[by apply NoDup_nil|]; auto.
        split; auto.
        intros a. intros Hcontr; inversion Hcontr.
      + eapply Forall_iff with (P := (fun _ => False)) in HForall; last done.
        destruct l.
        ++ intros; cbn; split; intro; set_solver.
        ++ eapply Forall_cons in HForall; naive_solver.
    - eapply extract_temps_split_cview; eauto.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------ WE CAN UPDATE A REVOKED WORLD BACK TO TEMPORARY  -------------------- *)
  (* ---------------------------------------------------------------------------------------- *)


  Fixpoint conditional_close_list_std_sta (ρ : region_type) (l : list Addr) (fs : STS_STD) : STS_STD :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => if (decide (ρ = j))
                          then <[i := Temporary]> (conditional_close_list_std_sta ρ l' fs)
                          else (conditional_close_list_std_sta ρ l' fs)
               | None => (conditional_close_list_std_sta ρ l' fs)
               end
    end.
  Definition close_list_std_sta (l : list Addr) (fs : STS_STD) : STS_STD := conditional_close_list_std_sta Revoked l fs.
  Definition close_list l WC : CVIEW := (close_list_std_sta l (std WC), loc WC).
  Definition close_list_C l W C : WORLD :=
    match W !! C with
    | Some WC => <[C := close_list l WC ]> W
    | None => W
    end.

  Lemma conditional_close_list_std_sta_is_Some Wstd_sta ρ l i :
    is_Some (Wstd_sta !! i) <-> is_Some (conditional_close_list_std_sta ρ l Wstd_sta !! i).
  Proof.
    split.
    - induction l.
      + done.
      + intros [x Hx].
      simpl.
      destruct (Wstd_sta !! a);[|apply IHl;eauto].
      destruct (decide (ρ = r));eauto.
      destruct (decide (a = i)).
        * subst. rewrite lookup_insert. eauto.
        * rewrite lookup_insert_ne;eauto.
    - induction l.
      + done.
      + intros [x Hx].
        simpl in Hx.
        destruct (Wstd_sta !! a) eqn:Hsome;eauto.
        destruct (decide (ρ = r));try by (apply IHl;eauto).
        destruct (decide (a = i)).
        * subst. eauto.
        * rewrite lookup_insert_ne in Hx;eauto.
  Qed.

  Lemma close_list_std_sta_is_Some Wstd_sta l i :
    is_Some (Wstd_sta !! i) <-> is_Some (close_list_std_sta l Wstd_sta !! i).
  Proof.
    apply conditional_close_list_std_sta_is_Some.
  Qed.

  Lemma conditional_close_list_std_sta_None Wstd_sta ρ l i :
    Wstd_sta !! i = None <-> conditional_close_list_std_sta ρ l Wstd_sta !! i = None.
  Proof.
    split.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. apply conditional_close_list_std_sta_is_Some in Hcontr.
      apply eq_None_not_Some in Hcontr; auto.
    - intros Hnone. apply eq_None_not_Some.
      intros Hcontr. revert Hcontr. rewrite conditional_close_list_std_sta_is_Some =>Hcontr.
      apply eq_None_not_Some in Hcontr; eauto.
  Qed.
  Lemma close_list_std_sta_None Wstd_sta l i :
    Wstd_sta !! i = None <-> close_list_std_sta l Wstd_sta !! i = None.
  Proof.
    apply conditional_close_list_std_sta_None.
  Qed.

  Lemma conditional_close_list_dom_eq Wstd_sta l ρ :
    dom Wstd_sta = dom (conditional_close_list_std_sta ρ l Wstd_sta).
  Proof.
    apply gset_leibniz. split.
    - intros Hin.
      rewrite elem_of_dom. rewrite elem_of_dom in Hin.
      rewrite -conditional_close_list_std_sta_is_Some.
      eauto.
    - intros Hin.
      rewrite elem_of_dom. rewrite elem_of_dom in Hin.
      rewrite conditional_close_list_std_sta_is_Some.
      eauto.
  Qed.
  Lemma close_list_dom_eq Wstd_sta l :
    dom Wstd_sta = dom (close_list_std_sta l Wstd_sta).
  Proof.
    apply conditional_close_list_dom_eq.
  Qed.

  Lemma conditional_close_list_std_sta_same Wstd_sta ρ l i :
    i ∉ l → Wstd_sta !! i = conditional_close_list_std_sta ρ l Wstd_sta !! i.
  Proof.
    intros Hnin. induction l.
    - done.
    - simpl. apply not_elem_of_cons in Hnin as [Hne Hnin].
      destruct (Wstd_sta !! a); auto.
      destruct (decide (ρ = r)); auto.
      rewrite lookup_insert_ne; auto.
  Qed.
  Lemma close_list_std_sta_same Wstd_sta l i :
    i ∉ l → Wstd_sta !! i = close_list_std_sta l Wstd_sta !! i.
  Proof.
    apply conditional_close_list_std_sta_same.
  Qed.

  Lemma conditional_close_list_std_sta_same_alt Wstd_sta ρ l i :
    Wstd_sta !! i ≠ Some ρ ->
    Wstd_sta !! i = conditional_close_list_std_sta ρ l Wstd_sta !! i.
  Proof.
    intros Hnin. induction l.
    - done.
    - simpl.
      destruct (Wstd_sta !! a) eqn:some; auto.
      destruct (decide (ρ = r)); auto.
      destruct (decide (a = i)).
      + subst. contradiction.
      + rewrite lookup_insert_ne; auto.
  Qed.
  Lemma close_list_std_sta_same_alt Wstd_sta l i :
    Wstd_sta !! i ≠ Some Revoked ->
    Wstd_sta !! i = close_list_std_sta l Wstd_sta !! i.
  Proof.
    apply conditional_close_list_std_sta_same_alt.
  Qed.

  Lemma conditional_close_list_std_sta_revoked Wstd_sta ρ l i :
    i ∈ l -> Wstd_sta !! i = Some ρ →
    conditional_close_list_std_sta ρ l Wstd_sta !! i = Some Temporary.
  Proof.
    intros Hin Hrev. induction l.
    - inversion Hin.
    - apply elem_of_cons in Hin as [Heq | Hin].
      + subst. simpl. rewrite Hrev. rewrite decide_True//.
        rewrite lookup_insert. auto.
      + simpl. destruct (Wstd_sta !! a); auto.
        destruct (decide (ρ = r)); auto.
        destruct (decide (i = a)); subst.
        * rewrite lookup_insert; auto.
        * rewrite lookup_insert_ne;auto.
  Qed.
  Lemma close_list_std_sta_revoked Wstd_sta l i :
    i ∈ l -> Wstd_sta !! i = Some Revoked →
    close_list_std_sta l Wstd_sta !! i = Some Temporary.
  Proof.
    apply conditional_close_list_std_sta_revoked.
  Qed.

  Lemma close_list_related_sts_pub_cons_cview WC a l :
    related_sts_pub_cview WC (close_list l WC) →
    related_sts_pub_cview WC (close_list_std_sta (a :: l) (std WC), loc WC).
  Proof.
    rewrite /close_list /close_list_std_sta /=. intros IHl.
    destruct (std WC !! a) eqn:Hsome; eauto.
    destruct r;simpl;auto.
    apply related_sts_pub_trans_cview with (close_list l WC); auto.
    split;[|apply related_sts_pub_refl].
    split.
    + simpl. rewrite dom_insert /close_list /=.
      apply union_subseteq_r.
    + rewrite /close_list /=.
      intros i x y Hx Hy.
      destruct (decide (i = a)); subst.
      ++ rewrite lookup_insert in Hy. inversion Hy.
         subst.
         destruct (decide (a ∈ l)).
         +++ apply close_list_std_sta_revoked with _ l _ in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. left.
         +++ rewrite (close_list_std_sta_same _ l) in Hsome;auto.
             rewrite Hsome in Hx. inversion Hx. right with Temporary;[|left].
             constructor.
      ++ rewrite lookup_insert_ne in Hy; auto.
         rewrite Hx in Hy. inversion Hy. left.
  Qed.

  (* TODO version with world? *)
  (* Lemma close_list_related_sts_pub_cons W C a l : *)

  Lemma close_list_related_sts_pub_cview WC l :
    related_sts_pub_cview WC (close_list l WC).
  Proof.
    induction l.
    - rewrite /close_list /=. destruct WC. apply related_sts_pub_refl_cview.
    - apply close_list_related_sts_pub_cons_cview; auto.
  Qed.

  Lemma close_list_C_dom l W C : dom W ⊆ dom (close_list_C l W C).
  Proof.
    rewrite /close_list_C.
    destruct (W!!C) as [WC|] eqn:HWC; last done.
    rewrite dom_insert_L; set_solver.
  Qed.

  Lemma close_list_related_sts_pub W C l :
    related_sts_pub_world W (close_list_C l W C) C.
  Proof.
    split; first by apply close_list_C_dom.
    intros WC WC' HWC HWC'.
    rewrite /close_list_C HWC lookup_insert in HWC'; simplify_eq.
    eapply close_list_related_sts_pub_cview.
  Qed.

  Lemma close_list_related_sts_pub_insert'_cview Wstd_sta Wloc i l :
    i ∉ l → Wstd_sta !! i = Some Revoked ->
    related_sts_pub_cview
      (close_list_std_sta l ((std (Wstd_sta,Wloc))), Wloc)
      (<[i:=Temporary]> (close_list_std_sta l Wstd_sta), Wloc).
  Proof.
    intros Hnin Hlookup.
    split;[|apply related_sts_pub_refl]; simpl.
    split;auto.
    + apply elem_of_subseteq. intros j Hj.
      rewrite dom_insert_L. apply elem_of_union. right.
      apply elem_of_dom. rewrite elem_of_dom in Hj. done.
    + intros j x y Hx Hy.
      destruct (decide (i = j)); subst.
      * rewrite lookup_insert in Hy. rewrite -(close_list_std_sta_same _ l) in Hx; auto.
        rewrite Hlookup in Hx. inversion Hx; inversion Hy; subst.
        right with Temporary;[|left]. constructor.
      * rewrite lookup_insert_ne in Hy; auto. rewrite Hx in Hy. inversion Hy. left.
  Qed.

  Lemma close_list_related_sts_pub_insert_cview Wstd_sta Wloc i l :
    i ∉ l → Wstd_sta !! i = Some Revoked ->
    related_sts_pub_cview
      (Wstd_sta, Wloc)
      (<[i:= Temporary]> (close_list_std_sta l Wstd_sta), Wloc).
  Proof.
    intros Hnin Hlookup.
    apply related_sts_pub_trans_cview with (close_list_std_sta l ((std (Wstd_sta, Wloc))), Wloc).
    - apply close_list_related_sts_pub_cview.
    - apply close_list_related_sts_pub_insert'_cview; auto.
  Qed.

  Lemma close_revoke_iff Wstd_sta (l : list Addr) :
     (forall (i : Addr), Wstd_sta !! i = Some Temporary <-> i ∈ l) ->
     ∀ i, (close_list_std_sta l (revoke_std_sta Wstd_sta)) !! i =
          Wstd_sta !! i.
  Proof.
    intros Hiff.
    intros i. destruct (decide (i ∈ l)).
    + apply Hiff in e as Htemp. rewrite Htemp.
      apply close_list_std_sta_revoked;[auto|].
      apply revoke_lookup_Monotemp; auto.
    + apply (close_list_std_sta_same (revoke_std_sta Wstd_sta)) in n as Heq. rewrite -Heq.
      apply revoke_monotone_lookup_same.
      intros Hcontr. apply Hiff in Hcontr. contradiction.
  Qed.

  Lemma close_revoke_eq Wstd_sta (l : list Addr) :
    (forall (i : Addr), Wstd_sta !! i = Some Temporary <-> i ∈ l) ->
    (close_list_std_sta l (revoke_std_sta Wstd_sta)) = Wstd_sta.
  Proof.
    intros Hiff.
    eapply (map_leibniz (M:=gmap Addr) (A:=region_type)).
    intros i.
    eapply leibniz_equiv_iff.
    apply close_revoke_iff. auto.
    Unshelve.
    apply _.
    apply option_leibniz.
  Qed.

  Lemma close_list_std_sta_idemp Wstd_sta (l1 l2 : list Addr) :
    close_list_std_sta l1 (close_list_std_sta l2 Wstd_sta) = close_list_std_sta (l1 ++ l2) Wstd_sta.
  Proof.
    induction l1;[done|].
    rewrite /close_list_std_sta /=.
    destruct (Wstd_sta !! a) eqn:Hsome.
    - destruct (decide (Revoked = r)).
      + subst.
        destruct (decide (a ∈ l2)).
        ++ apply close_list_std_sta_revoked with (l:=l2) in Hsome as Hsome'; auto.
           rewrite Hsome'. simpl.
           rewrite insert_id;auto.
           apply close_list_std_sta_revoked;auto.
           apply elem_of_app;by right.
        ++ rewrite (close_list_std_sta_same _ l2) in Hsome;auto.
           rewrite Hsome. simpl. f_equiv. auto.
      + assert (Wstd_sta !! a ≠ Some Revoked) as Hnrev.
        { intros Hcontr. congruence. }
        rewrite (close_list_std_sta_same_alt _ l2) in Hsome;auto.
        rewrite Hsome. rewrite decide_False;auto.
    - apply (close_list_std_sta_None _ l2) in Hsome. rewrite Hsome. done.
  Qed.

  (* TODO fix from here *)

  (* The following closes resources that are valid in the current world *)
  Lemma monotone_close W C l p φ `{forall Wv, Persistent (φ Wv)} :
    ([∗ list] a ∈ l, temp_resources W C φ a p ∗ rel C a p φ ∗ ⌜(std_C W C) !! a = Some Revoked⌝)
    ∗ sts_full_world W C
    ∗ region W C
    ==∗
    sts_full_world (close_list_C l W C) C ∗ region (close_list_C l W C) C.
  Proof.
    iIntros "(Hl & Hfull & Hr)".
    (* iAssert (⌜NoDup l⌝)%I as %Hdup. *)
    (* { iClear "Hfull Hr". *)
    (*   iInduction (l) as [|x l] "IH". *)
    (*   - iPureIntro. by apply NoDup_nil. *)
    (*   - iDestruct "Hl" as "[Ha Hl]". *)
    (*     iDestruct ("IH" with "Hl") as %Hdup. *)
    (*     iAssert (⌜x ∉ l⌝)%I as %Hnin. *)
    (*     { iIntros (Hcontr). iDestruct (big_sepL_elem_of _ _ x with "Hl") as "[Ha' Hcontr]"; auto. *)
    (*       rewrite /temp_resources /=. *)
    (*       iDestruct "Ha" as "(Ha & _)". *)
    (*       iDestruct "Ha" as (v) "(% & Ha & _)". *)
    (*       iDestruct "Ha'" as (v') "(% & Ha' & _)". *)
    (*       iApply (addr_dupl_false with "Ha Ha'"); auto. *)
    (*     } iPureIntro. apply NoDup_cons. split; auto. *)
    (* } *)
    (* iInduction (l) as [|x l] "IH". *)
    (* - iFrame. destruct W as [ Wstd_sta Wloc]; done. *)
    (* - apply NoDup_cons in Hdup as [Hdup Hnin]. *)
    (*   iDestruct "Hl" as "[ [Hx #[Hrel Hrev] ] Hl]". *)
    (*   rewrite /close_list /close_list_std_sta region_eq /region_def /std /=. *)
    (*   iMod ("IH" $! Hnin with "Hl Hfull Hr") as "(Hfull & Hr)"; auto. *)
    (*   iClear "IH". *)
    (*   destruct W as [ Wstd_sta Wloc]. *)
    (*   iDestruct "Hx" as (a HO) "(Hx & #HmonoV & Hφ)". *)
    (*   iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)". iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'. *)
    (*   rewrite rel_eq /rel_def. iDestruct "Hrel" as (γpred) "[HREL Hpred]". *)
    (*   iDestruct (reg_in γrel M with "[$HM $HREL]") as %HMeq. rewrite HMeq. *)
    (*   iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hstate Hr]"; [apply lookup_insert|]. *)
    (*   iDestruct "Hstate" as (ρ Mx) "[Hρ Hstate]". *)
    (*   iDestruct (sts_full_state_std with "Hfull Hρ") as %Hx''. *)
    (*   rewrite -(close_list_std_sta_same _ l _) in Hx''; auto. *)
    (*   rewrite  Hx''. *)
    (*   iDestruct "Hrev" as %Hrev. inversion Hrev as [Heq]. subst ρ. *)
    (*   erewrite decide_True;auto. *)
    (*   iMod (sts_update_std _ _ _ Temporary with "Hfull Hρ") as "[Hfull Hρ] /=". *)
    (*   iFrame "Hfull". *)
    (*   iModIntro. iExists M,(<[x:=Temporary]> Mρ). rewrite HMeq. *)
    (*   iDestruct (region_map_delete_nonfrozen with "Hr") as "Hr";[intros m; by rewrite Mx|]. *)
    (*   iDestruct (region_map_insert_nonfrozen Temporary with "Hr") as "Hr";auto. *)
    (*   rewrite /region_map_def. *)
    (*   iDestruct (big_sepM_delete _ _ x with "[Hρ Hr Hx HmonoV Hφ]") as "$"; [apply lookup_insert|..]. *)
    (*   { do 2 (rewrite delete_insert;[|apply lookup_delete]). *)
    (*     iSplitR "Hr". *)
    (*     - iExists Temporary. iFrame "#∗%". *)
    (*       iSplit;[iPureIntro;apply lookup_insert|]. *)
    (*       repeat (iSplit; auto). *)
    (*       iAssert (future_pub_mono φ a) as "#HmonoV'". *)
    (*       { destruct (isWL p); [|iApply future_priv_mono_is_future_pub_mono]; done. } *)
    (*       iNext. iApply "HmonoV'"; iFrame. *)
    (*       iPureIntro. apply close_list_related_sts_pub_insert; auto. *)
    (*     - iApply (big_sepM_mono with "Hr"). *)
    (*       iIntros (a' γp Hsome) "Hρ /=". iDestruct "Hρ" as (ρ Ha) "[Hstate Hρ]". *)
    (*       iExists ρ. iFrame. destruct ρ; auto. *)
    (*       + iDestruct "Hρ" as (γpred' p' φ0 Heq Hpers) "(#Hpred & Hρ)". *)
    (*         iDestruct "Hρ" as (v) "(HO & Ha' & #HmonoV & Hφ0)". *)
    (*         iSplit;auto. iExists _,_,_. *)
    (*         iAssert (future_pub_mono φ0 v) as "#HmonoV'". *)
    (*         { destruct (isWL p'); [|iApply future_priv_mono_is_future_pub_mono]; done. } *)
    (*         iFrame "∗#%". *)
    (*         iNext. iApply ("HmonoV'" with "[] Hφ0"). iPureIntro. *)
    (*         apply close_list_related_sts_pub_insert'; auto. *)
    (*       + iDestruct "Hρ" as (γpred' p' φ0 Heq' Hpers) "(#Hpred & Hρ)". *)
    (*         iDestruct "Hρ" as (v) "(HO & Ha' & #HmonoV & Hφ0)". *)
    (*         iSplit;auto. iExists _,_,_. iFrame "∗%#". *)
    (*         iNext. iApply ("HmonoV" with "[] Hφ0"). *)
    (*         iPureIntro. *)
    (*         apply related_sts_pub_priv_world. *)
    (*         apply close_list_related_sts_pub_insert'; auto. *)
    (*   } *)
    (*   do 2 (rewrite -HMeq). iFrame. iPureIntro. *)
    (*   (* The domains remain equal *) *)
    (*   split. *)
    (*   { rewrite -Hdom. rewrite dom_insert_L. *)
    (*     assert (x ∈ dom M) as Hin. *)
    (*     { apply elem_of_dom. rewrite HMeq. rewrite lookup_insert. eauto. } *)
    (*     rewrite Hdom. set_solver. *)
    (*   } *)
    (*   rewrite dom_insert_L. assert (x ∈ dom Mρ) as Hin;[apply elem_of_dom;eauto|]. *)
    (*   rewrite -Hdom'. set_solver. *)
    Admitted.

  Lemma monotone_revoked_close_sub W C l p φ `{forall Wv, Persistent (φ Wv)} :
    ([∗ list] a ∈ l, temp_resources (revoke_C W C) C φ a p ∗ rel C a p φ
                                    ∗ ⌜(std_C (revoke_C W C) C) !! a = Some Revoked⌝)
    ∗ sts_full_world (revoke_C W C) C
    ∗ region (revoke_C W C) C
    ==∗
    sts_full_world (close_list_C l (revoke_C W C) C) C ∗ region (close_list_C l (revoke_C W C) C) C.
  Proof.
    iIntros "(Hl & Hfull & Hr)".
    iApply monotone_close;auto.
    iFrame.
  Qed.

  (* However, we also want to be able to close regions that were valid in some world W, and which will be valid again
     in a public future world close l W' ! This is slightly more tricky: we must first update the region monotonically,
     after which it will be possible to consolidate the full_sts and region *)

  Lemma close_list_consolidate W W' (l' l : list Addr) :
    ⊢ ⌜l' ⊆+ l⌝ →
    ⌜related_sts_pub_world W (close_list_std_sta l (std W'), loc W')⌝ →
    (region (close_list l W')
     ∗ sts_full_world W'
     ∗ ([∗ list] a ∈ l',
          ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ temp_resources W φ a p ∗ rel a p φ))
      ==∗
      (sts_full_world (close_list l' W')
       ∗ region (close_list l W')).
  Proof.
    iIntros (Hsub Hrelated) "(Hr & Hsts & Htemps)".
    iInduction l' as [|x l'] "IH".
    - simpl. iFrame. done.
    - iDestruct "Htemps" as "[Hx Htemps]".
      assert (l' ⊆+ l) as Hsub'.
      { apply submseteq_cons_l in Hsub as [k [Hperm Hsub] ]. rewrite Hperm.
        apply submseteq_cons_r. left. auto. }
      iMod ("IH" $! Hsub' with "Hr Hsts Htemps") as "[Hsts Hr]".
      iClear "IH".
      rewrite /close_list /close_list_std_sta /=.
      iDestruct "Hx" as (p φ Hpers) "(Htemp & Hrel)".
      iDestruct "Htemp" as (v) "(%Hne & Hx' & #HmonoV & Hφ)".
      destruct (std W' !! x) eqn:Hsome;[|iFrame;done].
      destruct (decide (Revoked = r)).
      + subst.
        assert (x ∈ l) as Hinl.
        { apply elem_of_submseteq with (x:=x) in Hsub;[auto|apply elem_of_cons;by left]. }
        rewrite region_eq /region_def /region_map_def.
        iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
        iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
        rewrite rel_eq /rel_def REL_eq /REL_def.
        iDestruct "Hrel" as (γpred) "#[Hrel Hsaved]".
        iDestruct (reg_in with "[$HM $Hrel]") as %HMeq. rewrite HMeq.
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]";[apply lookup_insert|].
        rewrite delete_insert;[|apply lookup_delete].
        iDestruct "Hx" as (ρ Hx) "[Hstate Hx]".
        destruct ρ.
        { iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Hx)".
          iDestruct "Hx" as (v' Hne') "(Hx & _)".
          inversion Heq; subst.
          iApply bi.False_elim. iApply (addr_dupl_false with "Hx' Hx"); auto. }
        { iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Hx)".
          iDestruct "Hx" as (v' Hne') "(Hx & _)".
          inversion Heq; subst.
          iApply bi.False_elim. iApply (addr_dupl_false with "Hx' Hx"); auto. }
        2 : {
          iDestruct "Hx" as (γpred' p' φ' Heq Hpers') "(_ & Hx)".
          iDestruct "Hx" as (v' Hge Hne') "(Hx & _)".
          iApply bi.False_elim. iApply (addr_dupl_false with "Hx' Hx"); auto. }

        iMod (sts_update_std _ _ _ Temporary with "Hsts Hstate") as "[Hsts Hstate]".
        rewrite HMeq.
        iDestruct (region_map_delete_nonfrozen with "Hr") as "Hr";[intros m;by rewrite Hx|].
        iDestruct (region_map_insert_nonfrozen Temporary with "Hr") as "Hr"; auto.
        iDestruct (big_sepM_delete _ _ x with "[ Hx' HmonoV Hφ Hstate $Hr]") as "Hr"
        ;[apply lookup_insert|..].

        { iExists Temporary. iFrame. rewrite lookup_insert. iSplit;auto. iExists γpred,p,φ. repeat (iSplit;auto).
          destruct (isWL p).
          - iFrame "∗#"; iApply ("HmonoV" with "[] Hφ"); auto.
          - iFrame "∗#"; iApply ("HmonoV" with "[] Hφ"); auto.
            iPureIntro.
            apply related_sts_pub_priv_world; auto.
        }
        iFrame. rewrite -HMeq. iFrame. rewrite -HMeq. iFrame. iModIntro. iSplit; auto.
        iPureIntro. rewrite dom_insert_L. rewrite -Hdom'.
        assert (x ∈ dom  Mρ);[apply elem_of_dom;eauto|]. set_solver.
      + iFrame; done.
  Qed.

  Lemma monotone_close_list_region W W' (l : list Addr) :
    ⊢ ⌜related_sts_pub_world W (close_list l W')⌝ -∗
     sts_full_world W'
     ∗ region W'
     ∗ ([∗ list] a ∈ l,
          ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ temp_resources W φ a p ∗ rel a p φ)
     ==∗
     (sts_full_world (close_list l W')
      ∗ region (close_list l W')
     ).
  Proof.
    iIntros (Hrelated) "(Hsts & Hr & Htemp)".
    assert (related_sts_pub_world W' (close_list l W')) as Hrelated'.
    { apply close_list_related_sts_pub; auto. }
    assert (dom (std W') = dom (std (close_list l W'))) as Heq.
    { apply close_list_dom_eq. }
    iDestruct (region_monotone with "Hr") as "Hr";[apply Heq|apply Hrelated'|].
    iMod (close_list_consolidate _ _ l with "[] [] [$Hr $Hsts $Htemp]") as "[Hsts Hr]";[auto|eauto|iFrame;done].
  Qed.

   Lemma related_sts_pub_world_revoked_permanent W a :
    (std W) !! a = Some Revoked →
    related_sts_pub_world W (<s[a:=Permanent]s>W).
  Proof.
    intros Ha.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst.
        rewrite Hx in Ha. inversion Ha.
        rewrite lookup_insert in Hy. inversion Hy.
        right with (Permanent);[|left]. constructor.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma update_region_revoked_perm E W l v φ p `{∀ Wv, Persistent (φ Wv)} :
    (std W) !! l = Some Revoked ->
    isO p = false →
    future_priv_mono φ v -∗
    sts_full_world W -∗
    region W -∗
    l ↦ₐ v -∗
    φ (W,v) -∗
    rel l p φ

    ={E}=∗

    region (<s[l := Permanent ]s>W)
    ∗ sts_full_world (<s[l := Permanent ]s>W).
  Proof.
    iIntros (Hrev HpO) "#HmonoV Hsts Hreg Hl #Hφ #Hrel".
    rewrite region_eq /region_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & #Hdom & #Hdom' & Hpreds)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    rewrite rel_eq /rel_def REL_eq /REL_def. iDestruct "Hrel" as (γ) "[HREL Hsaved]".
    iDestruct (reg_in γrel (M) with "[$Hγrel $HREL]") as %HMeq.
    rewrite /region_map_def HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl' Hr]".
    iDestruct "Hl'" as (ρ Hl) "[Hstate Hresources]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    rewrite Hrev in Hρ. inversion Hρ as [Hρrev]. subst.
    iMod (sts_update_std _ _ _ Permanent with "Hsts Hstate") as "[Hsts Hstate]".
    assert (related_sts_pub_world W (<s[l := Permanent ]s> W)) as Hrelated.
    { apply related_sts_pub_world_revoked_permanent; auto. }
    iDestruct (region_map_monotone with "Hr") as "Hr";[apply Hrelated|].
    pose proof (related_sts_pub_priv_world _ _ Hrelated) as Hrelated'.
    iDestruct ("HmonoV" $! _ _ Hrelated' with "Hφ") as "Hφ'".
    assert (is_Some (M !! l)) as [x Hsome].
    { apply elem_of_dom. rewrite -Hdom. rewrite elem_of_dom. eauto. }
    iDestruct (region_map_delete_nonfrozen with "Hr") as "Hr"; [intros m;intros Hcontr;congruence|].
    iDestruct (region_map_insert_nonfrozen Permanent with "Hr") as "Hr";auto.
    iDestruct (big_sepM_delete _ _ l _ Hsome with "[Hl Hstate $Hr]") as "Hr".
    { iExists Permanent. iFrame. iSplitR;[iPureIntro;apply lookup_insert|].
      iExists γ,p,φ. rewrite HMeq lookup_insert in Hsome.
      inversion Hsome. repeat (iSplit; auto). }
    rewrite /std_update /=. iFrame "Hsts".
    iExists M. iFrame. rewrite -HMeq. iFrame.
    iModIntro. iPureIntro.
    apply insert_id in Hsome. apply insert_id in Hl. rewrite -Hsome -Hl. split.
    - repeat rewrite dom_insert_L;rewrite Hdom;set_solver.
    - repeat rewrite dom_insert_L;rewrite Hdom';set_solver.
  Qed.

End heap.
