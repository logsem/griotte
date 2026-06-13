From griotte Require Export sts world_std_sts sts_multiple_updates.
From griotte Require Export stdpp_extra.

Section world_std_revocation.
  Context {Σ:gFunctors}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    `{MP: MachineParameters}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (*** World Revocation and Reinstate *)

  (** This file defines revocation of the standard world.

      Revocation turns every temporary/temporary location state to revoked.
      Revocation is crucial to privately update state: in general,
      region states are only monotone with regards to public future
      world. To do a private update, we must thus revoke all temp
      regions, after which we only have regions that are indeed
      monotone wrt private future world.
   *)

  (* --------------------------------------------------------------------------------------------------------- *)
  (* --------------------------------------------- REVOCATION ------------------------------------------------ *)
  (* --------------------------------------------------------------------------------------------------------- *)

  (* the revoke condition states that there are no Temporary states left *)
  Definition revoke_condition W := ∀ a, (std W) !! a ≠ Some Temporary.

  (* Revocation only changes the states of the standard STS collection *)
  Definition revoke_std_sta : STS_STD → STS_STD :=
    fmap (λ v, match v with
               | Temporary => Revoked
               | _ => v
               end).
  Definition revoke (W : WORLD) : WORLD := (revoke_std_sta (std W), cus W).

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
  Definition revoke_list (l : list Addr) (W : WORLD) : WORLD
    := ((revoke_list_std_sta l (std W)), cus W).

  Lemma revoke_list_empty W :
    (revoke_list [] W) = W.
  Proof.
    rewrite /revoke_list.
    destruct W; by rewrite -surjective_pairing.
  Qed.


  (* -------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT REVOKE ---------------------------- *)
  (* -------------------------------------------------------------------------- *)

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
            destruct j;[rewrite lookup_insert_eq;auto|rewrite IHl H3; destruct (in_dec finz_eq_dec a l);auto..].
          * simpl.
            case_eq (Wstd_sta !! a); intros.
            { destruct (decide (Temporary = r)).
              { subst. destruct (decide (i = a)).
                - subst. rewrite lookup_insert_eq. by simplify_map_eq.
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
    eapply list_elem_of_In in i0. by simplify_map_eq.
  Qed.

  Lemma revoke_list_dom_std_sta (Wstd_sta : gmap Addr region_type) :
    revoke_std_sta Wstd_sta = revoke_list_std_sta (map_to_list Wstd_sta).*1 Wstd_sta.
  Proof.
    eapply (map_leibniz (M:=gmap Addr)). red. red. intros.
    rewrite revoke_list_std_sta_spec /revoke_std_sta lookup_fmap /revoke_i /=.
    destruct (Wstd_sta !! i) as [x|] eqn:Hwstd; rewrite Hwstd /=; auto.
    2: { eapply leibniz_equiv_iff; auto. }
    destruct (decide (Temporary = x)).
    - subst x.
      eapply elem_of_map_to_list in Hwstd as Hx.
      destruct (in_dec finz_eq_dec i (map_to_list Wstd_sta).*1); auto.
      + eapply leibniz_equiv_iff; auto.
      + elim n. eapply list_elem_of_In.
        eapply list_elem_of_fmap. exists (i, Temporary).
        split; auto.
    - destruct (in_dec finz_eq_dec i (map_to_list Wstd_sta).*1); auto.
      + destruct x;auto; try contradiction.
        all: try eapply leibniz_equiv_iff; auto.
      + destruct x;auto; try contradiction.
        all: try eapply leibniz_equiv_iff; auto.
        Unshelve.
        all: try apply _.
        all: try apply option_leibniz.
        all: try eapply Equivalence_Reflexive.
        Unshelve.
        all: try (apply option_equivalence; apply _).
  Qed.

  Lemma revoke_list_dom (W : WORLD) :
    revoke W = revoke_list (map_to_list (std W)).*1 W.
  Proof.
    by rewrite /revoke_list /= -revoke_list_dom_std_sta /revoke.
  Qed.

  Lemma revoke_list_lookup_Some Wstd_sta l (a : Addr) :
    is_Some (Wstd_sta !! a) ↔ is_Some ((revoke_list_std_sta l Wstd_sta) !! a).
  Proof.
    rewrite revoke_list_std_sta_spec.
    destruct (Wstd_sta !! a); split; eauto.
  Qed.

  Lemma revoke_lookup_Some W (i : Addr) :
    is_Some ((std W) !! i) ↔ is_Some ((std (revoke W)) !! i).
  Proof.
    rewrite revoke_list_dom /revoke_list /=.
    rewrite revoke_list_std_sta_spec.
    destruct (std W !! i); eauto.
    rewrite !is_Some_alt; auto.
  Qed.

  Lemma revoke_lookup_None W (i : Addr) :
    (std W) !! i = None ↔ (std (revoke W)) !! i = None.
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
    - assert (std ((Wstd_sta, (∅,∅)) : WORLD) = Wstd_sta) as Heq;auto.
      rewrite -Heq in Hi.
      apply (revoke_lookup_Some ((Wstd_sta, (∅,∅)) : WORLD) i) in Hi.
      auto.
    - assert (std ((Wstd_sta, (∅,∅)) : WORLD) = Wstd_sta) as <-;auto.
      apply (revoke_lookup_Some ((Wstd_sta, (∅,∅)) : WORLD) i).
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
    - elim n. eapply list_elem_of_In.
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
    - elim n. eapply list_elem_of_In.
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
    - elim n. eapply list_elem_of_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_list_lookup_non_temp (Wstd_sta : STS_STD) (l : list Addr) (i : Addr) (ρ : region_type) :
    i ∈ l →
    (revoke_list_std_sta l Wstd_sta) !! i = Some ρ → ρ ≠ Temporary.
  Proof.
    intros Hin Hsome.
    rewrite revoke_list_std_sta_spec in Hsome.
    destruct (Wstd_sta !! i); try congruence.
    eapply list_elem_of_In in Hin.
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
    rewrite /= in Hin.
    assert (is_Some (Wstd_sta !! i)) as [x Hsome].
    { rewrite revoke_list_std_sta_spec in Hin.
      destruct (Wstd_sta !! i); eauto. }
    apply map_to_list_fst. exists x.
    apply elem_of_map_to_list. done.
  Qed.

  Lemma revoke_lookup_non_temp W (i : Addr) (ρ : region_type) :
    (std (revoke W)) !! i = Some ρ → ρ ≠ Temporary.
  Proof.
    intros Hin.
    rewrite revoke_list_dom in Hin.
    apply revoke_list_lookup_non_temp with (std W) ((map_to_list (std W)).*1) i; auto.
    rewrite /= in Hin.
    assert (is_Some ((std W) !! i)) as [x Hsome].
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
        rewrite elem_of_dom. rewrite lookup_insert_eq. eauto. }
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
      + subst. rewrite lookup_insert_eq in Heq.
        rewrite /revoke_std_sta fmap_insert lookup_fmap lookup_insert_eq -Heq /=.
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
      + subst. rewrite lookup_insert_eq in Hneq'.
        rewrite /revoke_std_sta fmap_insert lookup_insert_eq lookup_insert_eq /=.
        f_equiv.
        destruct x eqn:Hcontr; auto.
        contradiction.
      + simplify_map_eq.
        rewrite /revoke_std_sta fmap_insert lookup_insert_ne;auto.
  Qed.

  Lemma revoke_monotone_lookup_same' (W:WORLD) (i: Addr) :
    std W !! i ≠ Some Temporary ->
    std (revoke W) !! i = std W !! i.
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
  Lemma revoke_conditions_sat (W : WORLD) :
    revoke_condition (revoke W).
  Proof.
    intros a. destruct ((std (revoke W)) !! a) eqn:Hsome;auto.
    intros Hcontr;simplify_eq.
    rewrite /revoke in Hsome.
    apply revoke_lookup_non_temp in Hsome. done.
  Qed.


  Lemma related_sts_pub_revoked_temp W a :
    (std W) !! a = Some Revoked ∨
    (std W) !! a = Some Temporary →
    related_sts_pub_world W (<s[a:=Temporary]s>W).
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
        ++ rewrite lookup_insert_eq in Hy. inversion Hy.
           right with (Temporary);[|left]. constructor.
        ++ rewrite lookup_insert_eq in Hy. inversion Hy. left.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.


  (* --------------------------------------------------------------------------------- *)
  (* ----------- A REVOKED REGION IS MONOTONE WRT PRIVATE FUTURΕ WORLDS -------------- *)
  (* --------------------------------------------------------------------------------- *)


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
       try (apply revoke_lookup_Monotemp in H' as Hytemp);
       try (apply revoke_lookup_Perm in H' as Hytemp);
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
        * destruct h;revoke_i Wstd_sta Wstd_sta' i;try left.
          eright;[left;constructor|left].
      + destruct j,k,h; inversion Hjk; try discriminate; auto;
          revoke_i Wstd_sta Wstd_sta' i; try left; try (by inversion H).
        all: try (right with Permanent; [left;constructor|eleft; constructor]).
  Qed.

  Lemma revoke_monotone (W W' : WORLD) :
    related_sts_priv_world W W' → related_sts_priv_world (revoke W) (revoke W').
  Proof.
    destruct W as [ Wstd_sta [Wloc_sta Wloc_rel] ].
    destruct W' as [ Wstd_sta' [Wloc_sta' Wloc_rel'] ].
    intros [(Hdom_sta & Htransition) Hrelated_loc].
    (* pose proof (revoke_private_monotone_dom _ _ Hdom_sta) as Hdom_sta'. *)
    split;[split;[auto|]|auto].
    - apply revoke_monotone_dom; eauto.
    - intros i x' y' Hx' Hy'.
      simpl in *.
      assert (is_Some (Wstd_sta !! i)) as [x Hx]; [apply revoke_std_sta_lookup_Some; eauto|].
      assert (is_Some (Wstd_sta' !! i)) as [y Hy]; [apply revoke_std_sta_lookup_Some; eauto|].
      apply std_rel_monotone with x y Wstd_sta Wstd_sta' i; auto. apply Htransition with i;auto.
  Qed.


  (* --------------------------------------------------------------------------------- *)
  (* ----------------- REVOKED W IS A PRIVATE FUTURE WORLD TO W ---------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Lemma revoke_list_related_sts_priv_cons_world W l i :
    related_sts_priv_world W (revoke_list l W) → related_sts_priv_world W (revoke_list (i :: l) W).
  Proof.
    intros Hpriv.
    rewrite /revoke_list /=.
    destruct (std W !! i) eqn:Hsome; auto.
    destruct r eqn:Htemp; auto.
    - destruct W as [ Wstd_sta Wloc].
      destruct Hpriv as [(Hdoms & Ha) Hloc]; auto.
      split;simpl;auto.
      rewrite /related_sts_std_priv.
      simpl in *.
      split.
      + rewrite dom_insert_L; set_solver.
      + intros j x y Hx Hy.
        destruct (decide (i = j)).
        { subst.
          rewrite lookup_insert_eq in Hy. inversion Hy.
          rewrite Hsome in Hx;inversion Hx;subst.
          right with Revoked;[|left].
          right; constructor.
        }
        rewrite lookup_insert_ne in Hy;auto.
        apply Ha with j;auto.
  Qed.

  Lemma revoke_list_related_sts_priv_world W l :
    related_sts_priv_world W (revoke_list l W).
  Proof.
    induction l.
    - destruct W as [ [] ]. rewrite /revoke_list /=. apply related_sts_priv_refl_world.
    - split;[|apply related_sts_priv_refl].
      apply revoke_list_related_sts_priv_cons_world; auto.
  Qed.

  Lemma revoke_related_sts_priv_world W :
    related_sts_priv_world W (revoke W).
  Proof.
    rewrite revoke_list_dom. apply revoke_list_related_sts_priv_world.
  Qed.

  (* Helper lemmas for reasoning about a revoked domain *)

  Lemma dom_equal_revoke_list (W : WORLD) (MC : gmap Addr (gname * Perm)) l :
    dom (std W) = dom MC →
    dom (std (revoke_list l W)) = dom MC.
  Proof.
    intros Hdom.
    induction l.
    - done.
    - rewrite /revoke_list /=.
      destruct (std W !! a) eqn:Hsome; auto.
      destruct r eqn:Htemp;auto.
      all: rewrite dom_insert_L;rewrite IHl.
      all: assert (a ∈ dom MC) as Hin;[rewrite -Hdom;rewrite elem_of_dom;eauto|].
      all: try set_solver.
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
  Definition close_list (l : list Addr) (W : WORLD) : WORLD := (close_list_std_sta l (std W), cus W).

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
        * subst. rewrite lookup_insert_eq. eauto.
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
        rewrite lookup_insert_eq. auto.
      + simpl. destruct (Wstd_sta !! a); auto.
        destruct (decide (ρ = r)); auto.
        destruct (decide (i = a)); subst.
        * rewrite lookup_insert_eq; auto.
        * rewrite lookup_insert_ne;auto.
  Qed.
  Lemma close_list_std_sta_revoked Wstd_sta l i :
    i ∈ l -> Wstd_sta !! i = Some Revoked →
    close_list_std_sta l Wstd_sta !! i = Some Temporary.
  Proof.
    apply conditional_close_list_std_sta_revoked.
  Qed.

  Lemma close_list_related_sts_pub_cons_world W a l :
    related_sts_pub_world W (close_list l W) →
    related_sts_pub_world W (close_list_std_sta (a :: l) (std W), cus W).
  Proof.
    rewrite /close_list /close_list_std_sta /=. intros IHl.
    destruct (std W !! a) eqn:Hsome; eauto.
    destruct r;simpl;auto.
    apply related_sts_pub_trans_world with (close_list l W); auto.
    split;[|apply related_sts_pub_refl].
    split.
    + simpl. rewrite dom_insert /close_list /=.
      apply union_subseteq_r.
    + rewrite /close_list /=.
      intros i x y Hx Hy.
      destruct (decide (i = a)); subst.
      ++ rewrite lookup_insert_eq in Hy. inversion Hy.
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

  Lemma close_list_related_sts_pub W l :
    related_sts_pub_world W (close_list l W).
  Proof.
    induction l.
    - rewrite /close_list /=. destruct W as [ [] ]. apply related_sts_pub_refl_world.
    - apply close_list_related_sts_pub_cons_world; auto.
  Qed.

  Lemma close_list_related_sts_pub_insert' Wstd_sta Wloc i l :
    i ∉ l → Wstd_sta !! i = Some Revoked ->
    related_sts_pub_world
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
      * rewrite lookup_insert_eq in Hy. rewrite -(close_list_std_sta_same _ l) in Hx; auto.
        rewrite Hlookup in Hx. inversion Hx; inversion Hy; subst.
        right with Temporary;[|left]. constructor.
      * rewrite lookup_insert_ne in Hy; auto. rewrite Hx in Hy. inversion Hy. left.
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
    + apply _.
    + apply option_leibniz.
  Qed.

  Lemma related_pub_revoke_close_list (W : WORLD) (l : list Addr) :
    (∀ a : finz MemNum, std W !! a = Some Temporary ↔ a ∈ l) ->
    related_sts_pub_world W (close_list l (revoke W)).
  Proof.
    intros Htemporaries.
    rewrite /revoke /close_list.
    rewrite close_revoke_eq; auto; cbn.
    destruct W; apply related_sts_pub_refl_world.
  Qed.

  Lemma close_list_empty W : (close_list [] W) = W.
  Proof.
    rewrite /close_list.
    by destruct W as [ [] ]; rewrite -surjective_pairing.
  Qed.

   (* commuting updates and revoke *)

   Lemma revoke_std_update_multiple_eq W l :
     Forall (fun a => std W !! a = Some Revoked) l ->
     (revoke (std_update_multiple W l Temporary)) = (revoke W).
   Proof.
     induction l; intros Hl; cbn; first done.
     rewrite Forall_cons in Hl; destruct Hl as [Hla Hl].
     rewrite /revoke /revoke_std_sta.
     rewrite fmap_insert.
     destruct W as [W1 W2].
     rewrite -/revoke_std_sta -/(revoke (W1,W2)).
     rewrite -IHl; auto.
     rewrite insert_id; auto.
     destruct (decide (a ∈ l)).
     + apply revoke_lookup_Monotemp.
       by apply std_sta_update_multiple_lookup_in_i.
     + apply revoke_lookup_Revoked.
       rewrite std_sta_update_multiple_lookup_same_i; auto.
   Qed.

  Lemma close_list_lookup_not_in W l a :
    a ∉ l -> std (close_list l W) !! a = std W !! a.
  Proof.
    intros Ha.
    induction l as [|a' l]; cbn; first done.
    apply not_elem_of_cons in Ha; destruct Ha as [Haeq Ha].
    apply IHl in Ha.
    rewrite -Ha.
    destruct (W.1 !! a') eqn:Ha'; last done.
    destruct (decide (Revoked = r)); last done.
    simplify_map_eq.
    done.
  Qed.

  Lemma close_list_lookup_in W l a :
    std W !! a = Some Revoked -> a ∈ l -> std (close_list l W) !! a = Some Temporary.
  Proof.
    intros Hrevoked Ha.
    induction l as [|a' l]; cbn;first set_solver.
    destruct (decide (a = a')) as [-> | Ha'].
    + rewrite Hrevoked.
      destruct (decide (Revoked = Revoked)); last done.
      by simplify_map_eq.
    + apply elem_of_cons in Ha; destruct Ha as [-> | Ha]; first done.
      apply IHl in Ha.
      destruct (W.1 !! a') eqn:Ha''; auto.
      destruct (decide (Revoked = r)); auto.
      by simplify_map_eq.
  Qed.

  Lemma close_list_lookup_Temporary W l a :
    std W !! a = Some Temporary -> std (close_list l W) !! a = Some Temporary.
  Proof.
    intros Hrevoked.
    induction l as [|a' l]; cbn;first set_solver.
    destruct (decide (a = a')) as [-> | Ha'].
    + rewrite Hrevoked.
      destruct (decide (Revoked = Temporary)); first done.
      by rewrite IHl.
    + destruct (W.1 !! a') eqn:Ha''; auto.
      destruct (decide (Revoked = r)); auto.
      by simplify_map_eq.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------- REVOKING ALL TEMPORARY REGIONS, KNOWN AND UNKNOWN  ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* Extract all the Temporary addresses from W *)
  Lemma extract_temps W :
    ∃ l, NoDup l ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ l).
  Proof.
    destruct W as [Wstd_sta Wloc].
    induction Wstd_sta using (map_ind (M:=gmap Addr) (A:=region_type)).
    - exists []. split;[by apply NoDup_nil|]. intros a. split; intros Hcontr; inversion Hcontr.
    - destruct IHWstd_sta as [l [Hdup Hiff] ].
      assert (i ∈ dom (<[i:=x]> m)) as Hin.
      { apply elem_of_dom. rewrite lookup_insert_eq; eauto. }
      assert (i ∉ l) as Hnin.
      { intros Hcontr. apply Hiff in Hcontr. simplify_map_eq. }
      destruct (decide (x = Temporary)); subst.
      + exists (i :: l). split;[apply NoDup_cons;split;auto|].
        intros a0. destruct (decide (i = a0)); subst.
        { rewrite lookup_insert_eq. split; auto. intros _. apply elem_of_cons. by left. }
        rewrite lookup_insert_ne;[|intros Hcontr;congruence].
        split; intros Htemp.
        { apply elem_of_cons; right. by apply Hiff. }
        { apply elem_of_cons in Htemp as [Hcontr | Hin'];[congruence|]. apply Hiff; auto. }
      + exists l. split; auto. intros a0. split.
        { destruct (decide (i = a0));subst.
          - rewrite lookup_insert_eq. intros Hcontr. congruence.
          - rewrite lookup_insert_ne;[apply Hiff|]. auto.
        }
        intros Hin'. destruct (decide (i = a0));[congruence|].
        rewrite lookup_insert_ne;[|intros Hcontr;congruence].
        apply Hiff; auto.
  Qed.

  (* We also want to be able to split the extracted temporary regions into known and unknown *)
  Lemma extract_temps_split_world W l :
    NoDup l ->
    Forall (λ (a : Addr), (std W) !! a = Some Temporary) l ->
    ∃ l', NoDup (l' ++ l) ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ (l' ++ l)).
  Proof.
    intros Hdup HForall.
    pose proof (extract_temps W) as [l' [Hdup' Hl'] ].
    revert HForall; rewrite Forall_forall =>HForall.
    exists (list_difference l' l). split.
    - apply NoDup_app. split;[|split].
      + apply NoDup_list_difference. auto.
      + intros a Ha. apply list_elem_of_difference in Ha as [_ Ha]; auto.
      + auto.
    - intros a. split.
      + intros Htemp.
        destruct (decide (a ∈ list_difference l' l));[by apply elem_of_app;left|].
        apply elem_of_app;right. apply Hl' in Htemp.
        assert (not (a ∈ l' ∧ a ∉ l)) as Hnot.
        { intros Hcontr. apply list_elem_of_difference in Hcontr. contradiction. }
        destruct (decide (a ∈ l)); auto.
        assert (a ∈ l' ∧ a ∉ l) as Hcontr; auto. apply Hnot in Hcontr. done.
      + intros Hin. apply elem_of_app in Hin as [Hin | Hin].
        ++ apply list_elem_of_difference in Hin as [Hinl Hninl'].
           by apply Hl'.
        ++ by apply HForall.
  Qed.


End world_std_revocation.
