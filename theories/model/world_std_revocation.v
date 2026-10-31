From griotte Require Export sts world_std_sts sts_multiple_updates.
From griotte Require Export stdpp_extra.

Section world_std_revocation.
  Context {Σ:gFunctors}
    {Cname : CmptNameG}
    `{MP: MachineParameters}.

  #[local] Notation WORLD := (leibnizO (World LAddr region_type)).

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
  Definition revoke (W : WORLD) : WORLD := MkWorld (revoke_std_sta (std W)) (cus W).

  (* A weaker revocation which only revokes elements from a list *)
  Fixpoint revoke_list_std_sta (l : list LAddr) (fs : STS_STD) : STS_STD :=
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
  Definition revoke_list (l : list LAddr) (W : WORLD) : WORLD
    := MkWorld (revoke_list_std_sta l (std W)) (cus W).

  (* -------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT REVOKE ---------------------------- *)
  (* -------------------------------------------------------------------------- *)

  Definition revoke_i i :=
    match i with
    | Temporary => Revoked
    | _ => i
    end.

  Lemma revoke_list_std_sta_spec (l : list LAddr) :
    forall (Wstd_sta : STS_STD) (i : LAddr),
      (revoke_list_std_sta l Wstd_sta) !! i =
      match Wstd_sta !! i with
      | None => None
      | Some j => Some (if List.In_dec LAddr_eq_dec i l
                       then revoke_i j else j)
      end.
  Proof.
    induction l; intros.
    - simpl. destruct (Wstd_sta !! i); auto.
    - case_eq (Wstd_sta !! i); [intros j H3 | intros H3].
      { destruct (in_dec LAddr_eq_dec i (a :: l)).
        + destruct i0 as [A | A].
          * subst i. simpl. rewrite H3.
            destruct j;[rewrite lookup_insert_eq;auto|rewrite IHl H3; destruct (in_dec LAddr_eq_dec a l);auto..].
          * simpl.
            case_eq (Wstd_sta !! a); intros.
            { destruct (decide (Temporary = r)).
              { subst. destruct (decide (i = a)).
                - subst. rewrite lookup_insert_eq. by simplify_map_eq.
                - rewrite lookup_insert_ne//. rewrite IHl H3.
                  destruct (in_dec LAddr_eq_dec i l);[auto|contradiction]. }
              destruct r; try contradiction; rewrite IHl H3;
                destruct (in_dec LAddr_eq_dec i l); tauto. }
            { rewrite IHl H3.
              destruct (in_dec LAddr_eq_dec i l); tauto. }
        + simpl. case_eq (Wstd_sta !! a); intros.
          * destruct (decide (Temporary = r)).
            { subst. destruct (decide (a = i)).
              - subst. elim n. left; auto.
              - rewrite lookup_insert_ne//.
                rewrite IHl H3. destruct (in_dec LAddr_eq_dec i l); auto.
                elim n. right. auto. }
            destruct r; try contradiction; rewrite IHl H3;
              destruct (in_dec LAddr_eq_dec i l); auto;
                elim n; right; auto.
          * rewrite IHl H3.
            destruct (in_dec LAddr_eq_dec i l); auto.
            elim n; right; auto. }
      { simpl. case_eq (Wstd_sta !! a); intros.
        - destruct (LAddr_eq_dec i a); try congruence.
          destruct (decide (Temporary = r)); intros.
          + subst. rewrite lookup_insert_ne; auto.
            rewrite IHl H3; auto.
          + destruct r; try contradiction; rewrite IHl H3; auto.
        - rewrite IHl H3; auto. }
  Qed.

  Lemma revoke_list_dom_std_sta (Wstd_sta : gmap LAddr region_type) :
    revoke_std_sta Wstd_sta = revoke_list_std_sta (map_to_list Wstd_sta).*1 Wstd_sta.
  Proof.
    eapply (map_leibniz (M:=gmap LAddr)). red. red. intros.
    rewrite revoke_list_std_sta_spec /revoke_std_sta lookup_fmap /revoke_i /=.
    destruct (Wstd_sta !! i) as [x|] eqn:Hwstd; rewrite Hwstd /=; auto.
    2: { eapply leibniz_equiv_iff; auto. }
    destruct (decide (Temporary = x)).
    - subst x.
      eapply elem_of_map_to_list in Hwstd as Hx.
      destruct (in_dec LAddr_eq_dec i (map_to_list Wstd_sta).*1); auto.
      + eapply leibniz_equiv_iff; auto.
      + elim n. eapply list_elem_of_In.
        eapply list_elem_of_fmap. exists (i, Temporary).
        split; auto.
    - destruct (in_dec LAddr_eq_dec i (map_to_list Wstd_sta).*1); auto.
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

  Lemma revoke_list_lookup_Some Wstd_sta l (a : LAddr) :
    is_Some (Wstd_sta !! a) ↔ is_Some ((revoke_list_std_sta l Wstd_sta) !! a).
  Proof.
    rewrite revoke_list_std_sta_spec.
    destruct (Wstd_sta !! a); split; eauto.
  Qed.

  Lemma revoke_lookup_Some W (i : LAddr) :
    is_Some ((std W) !! i) ↔ is_Some ((std (revoke W)) !! i).
  Proof.
    rewrite revoke_list_dom /revoke_list /=.
    rewrite revoke_list_std_sta_spec.
    destruct (std W !! i); eauto.
    rewrite !is_Some_alt; auto.
  Qed.

  Lemma revoke_lookup_None W (i : LAddr) :
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

  Lemma revoke_std_sta_lookup_Some Wstd_sta (i : LAddr) :
    is_Some (Wstd_sta !! i) ↔ is_Some (revoke_std_sta Wstd_sta !! i).
  Proof.
    by rewrite /revoke_std_sta lookup_fmap fmap_is_Some.
  Qed.

  Lemma revoke_lookup_Monotemp Wstd_sta i :
    (Wstd_sta !! i = Some Temporary) →
    (revoke_std_sta Wstd_sta) !! i = Some Revoked.
  Proof.
    rewrite revoke_list_dom_std_sta. intros Hsome.
    rewrite revoke_list_std_sta_spec Hsome.
    destruct (in_dec LAddr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
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
    destruct (in_dec LAddr_eq_dec i (map_to_list Wstd_sta).*1) eqn:HH.
    - rewrite /revoke_i HH. auto.
    - elim n. eapply list_elem_of_In.
      eapply map_to_list_fst. eexists; by apply elem_of_map_to_list.
  Qed.

  Lemma revoke_list_lookup_non_temp (Wstd_sta : STS_STD) (l : list LAddr) (i : LAddr) (ρ : region_type) :
    i ∈ l →
    (revoke_list_std_sta l Wstd_sta) !! i = Some ρ → ρ ≠ Temporary.
  Proof.
    intros Hin Hsome.
    rewrite revoke_list_std_sta_spec in Hsome.
    destruct (Wstd_sta !! i); try congruence.
    eapply list_elem_of_In in Hin.
    destruct (in_dec LAddr_eq_dec i l); try tauto.
    inv Hsome. rewrite /revoke_i.
    destruct (decide (Temporary = r)).
    - destruct r;auto;contradiction.
    - destruct r;[contradiction|auto..].
  Qed.

  Lemma revoke_lookup_non_temp W (i : LAddr) (ρ : region_type) :
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

  Lemma revoke_monotone_lookup_same (Wstd_sta : gmap LAddr region_type) i :
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

  (* --------------------------------------------------------------------------------- *)
  (* ----------- A REVOKED REGION IS MONOTONE WRT PRIVATE FUTURΕ WORLDS -------------- *)
  (* --------------------------------------------------------------------------------- *)

  Ltac revoke_i W1 W2 i :=
    (match goal with
     | H : W1 !! i = Some _
           , H' : W2 !! i = Some _ |- _ =>
       let Hxtemp := fresh "Hxtemp" in
       let Hytemp := fresh "Hytemp" in
       try (apply revoke_lookup_Monotemp in H as Hxtemp);
       try (apply revoke_lookup_Revoked in H as Hxtemp);
       try (apply revoke_lookup_Monotemp in H' as Hytemp);
       try (apply revoke_lookup_Revoked in H' as Hytemp);simplify_eq
     end).

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
    - destruct W as [Wstd_sta Wcus].
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
    - destruct W. rewrite /revoke_list /=. apply related_sts_priv_refl_world.
    - split;[|apply related_sts_priv_refl].
      apply revoke_list_related_sts_priv_cons_world; auto.
  Qed.

  Lemma revoke_related_sts_priv_world W :
    related_sts_priv_world W (revoke W).
  Proof.
    rewrite revoke_list_dom. apply revoke_list_related_sts_priv_world.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ------------------ WE CAN UPDATE A REVOKED WORLD BACK TO TEMPORARY  -------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  Fixpoint conditional_close_list_std_sta (ρ : region_type) (l : list LAddr) (fs : STS_STD) : STS_STD :=
    match l with
    | [] => fs
    | i :: l' => match fs !! i with
               | Some j => if (decide (ρ = j))
                          then <[i := Temporary]> (conditional_close_list_std_sta ρ l' fs)
                          else (conditional_close_list_std_sta ρ l' fs)
               | None => (conditional_close_list_std_sta ρ l' fs)
               end
    end.
  Definition close_list_std_sta (l : list LAddr) (fs : STS_STD) : STS_STD := conditional_close_list_std_sta Revoked l fs.
  Definition close_list (l : list LAddr) (W : WORLD) : WORLD := MkWorld (close_list_std_sta l (std W)) (cus W).

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
    related_sts_pub_world W (MkWorld (close_list_std_sta (a :: l) (std W)) (cus W)).
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
    - rewrite /close_list /=. destruct W. apply related_sts_pub_refl_world.
    - apply close_list_related_sts_pub_cons_world; auto.
  Qed.

  Lemma close_revoke_iff Wstd_sta (l : list LAddr) :
     (forall (i : LAddr), Wstd_sta !! i = Some Temporary <-> i ∈ l) ->
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

  Lemma close_revoke_eq Wstd_sta (l : list LAddr) :
    (forall (i : LAddr), Wstd_sta !! i = Some Temporary <-> i ∈ l) ->
    (close_list_std_sta l (revoke_std_sta Wstd_sta)) = Wstd_sta.
  Proof.
    intros Hiff.
    eapply (map_leibniz (M:=gmap LAddr) (A:=region_type)).
    intros i.
    eapply leibniz_equiv_iff.
    apply close_revoke_iff. auto.
    Unshelve.
    + apply _.
    + apply option_leibniz.
  Qed.

  Lemma related_pub_revoke_close_list (W : WORLD) (l : list LAddr) :
    (∀ a : LAddr, std W !! a = Some Temporary ↔ a ∈ l) ->
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
    by destruct W.
  Qed.

   (* commuting updates and revoke *)

   Lemma revoke_std_update_multiple_eq W l :
     Forall (fun a => std W !! LNonHeap a = Some Revoked) l ->
     (revoke (std_update_multiple W l Temporary)) = (revoke W).
   Proof.
     induction l; intros Hl; cbn; first done.
     rewrite Forall_cons in Hl; destruct Hl as [Hla Hl].
     rewrite /revoke /revoke_std_sta.
     rewrite fmap_insert.
     destruct W as [W1 Wc].
     rewrite -/revoke_std_sta -/(revoke (MkWorld W1 Wc)).
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
    destruct (std W !! a') eqn:Ha'; last done.
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
      destruct (std W !! a') eqn:Ha''; auto.
      destruct (decide (Revoked = r)); auto.
      by simplify_map_eq.
  Qed.

  Lemma close_list_std_update_multiple_revoked (W : WORLD) (la : list Addr) :
    Forall (λ a, std W !! LNonHeap a = Some Revoked) la →
    close_list (LNonHeap <$> la) W = std_update_multiple W la Temporary.
  Proof.
    intros Hrev.
    assert (∀ W1 W2 : WORLD, std W1 = std W2 → cus W1 = cus W2 → W1 = W2) as Hext.
    { intros [] [] ? ?; simpl in *; by subst. }
    apply Hext; last first.
    { rewrite /close_list /=. clear. induction la as [|a la IH]; [done|]. by rewrite /= -IH. }
    apply (map_eq (M:=gmap LAddr) (A:=region_type)). intros k.
    destruct (decide (k ∈ LNonHeap <$> la)) as [Hk|Hk].
    - rewrite std_sta_update_multiple_lookup_in_k //.
      apply close_list_lookup_in; [|done].
      apply list_elem_of_fmap in Hk as (x & -> & Hx).
      by eapply Forall_forall in Hrev.
    - rewrite close_list_lookup_not_in // std_sta_update_multiple_lookup_same_k //.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------- REVOKING ALL TEMPORARY REGIONS, KNOWN AND UNKNOWN  ------------------- *)
  (* ---------------------------------------------------------------------------------------- *)

  (* Extract all the Temporary addresses from W *)
  Lemma extract_temps W :
    ∃ l, NoDup l ∧ (forall (a : LAddr), (std W) !! a = Some Temporary <-> a ∈ l).
  Proof.
    destruct W as [Wstd_sta Wcus].
    induction Wstd_sta using (map_ind (M:=gmap LAddr) (A:=region_type)).
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
    Forall (λ (a : LAddr), (std W) !! a = Some Temporary) l ->
    ∃ l', NoDup (l' ++ l) ∧ (forall (a : LAddr), (std W) !! a = Some Temporary <-> a ∈ (l' ++ l)).
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

(** ** The local world *)

(** Revocation turns every Temporary key Revoked; restoring a set of keys
    turns its Revoked keys Temporary. *)
Definition revoke_rt (ρ : region_type) : region_type :=
  match ρ with Temporary => Revoked | _ => ρ end.
Definition close_rt (ρ : region_type) : region_type :=
  match ρ with Revoked => Temporary | _ => ρ end.

(** Restoring the keys of a set; the list-based [close_list] above
    restores the keys of a list. *)
Definition close_set (S : gset LAddr) (W : WORLD) : WORLD :=
  MkWorld (map_imap (λ k ρ, Some (if decide (k ∈ S) then close_rt ρ else ρ)) (std W)) (cus W).

(** [S] is exactly the set of Temporary keys of [W] that are not open. *)
Definition extract_T (W : WORLD) (O S : gset LAddr) : Prop :=
  ∀ k, k ∈ S ↔ std W !! k = Some Temporary ∧ k ∉ O.

Section local_world.
  Implicit Types W : WORLD.

  Lemma elem_of_dom_std W k : k ∈ dom (std W) ↔ is_Some (std W !! k).
  Proof. by rewrite elem_of_dom. Qed.

  Lemma elem_of_dom_std_2 W k ρ : std W !! k = Some ρ → k ∈ dom (std W).
  Proof. intros Hk. rewrite elem_of_dom_std. eauto. Qed.

  Lemma related_pub_Temporary W W' k :
    related_sts_pub_world W W' → std W !! k = Some Temporary → std W' !! k = Some Temporary.
  Proof.
    intros [ [Hd Hr] _] Hk.
    assert (is_Some (std W' !! k)) as [ρ Hρ].
    { rewrite -elem_of_dom; apply Hd; rewrite elem_of_dom; eauto. }
    rewrite Hρ. f_equal.
    eapply (std_rel_pub_rtc_Temporary Temporary ρ); [done|exact (Hr k _ _ Hk Hρ)].
  Qed.

  Lemma revoke_lookup W k : std (revoke W) !! k = revoke_rt <$> std W !! k.
  Proof. by rewrite /revoke /= lookup_fmap. Qed.

  Lemma close_set_lookup S W k :
    std (close_set S W) !! k =
    (λ ρ, if decide (k ∈ S) then close_rt ρ else ρ) <$> std W !! k.
  Proof. rewrite /close_set /= map_lookup_imap. by destruct (_ !! k). Qed.

  Lemma dom_revoke W : dom (std (revoke W)) = dom (std W).
  Proof. by rewrite /revoke /= dom_fmap_L. Qed.

  Lemma dom_close_set S W : dom (std (close_set S W)) = dom (std W).
  Proof.
    apply set_eq. intros k. rewrite !elem_of_dom close_set_lookup fmap_is_Some. done.
  Qed.

  Lemma revoke_not_Temporary W k : std (revoke W) !! k ≠ Some Temporary.
  Proof. rewrite revoke_lookup. destruct (std W !! k) as [ [] | ]; simpl; done. Qed.

  (** A restored key of the domain is Temporary. *)
  Lemma close_set_Temporary S W k :
    k ∈ S → k ∈ dom (std W) →
    std (close_set S W) !! k = Some Temporary.
  Proof.
    intros HkS [ρ Hρ]%elem_of_dom_std. rewrite close_set_lookup Hρ /= decide_True //.
    destruct ρ; done.
  Qed.

  Lemma close_set_not_elem S W k :
    k ∉ S → std (close_set S W) !! k = std W !! k.
  Proof.
    intros HkS. rewrite close_set_lookup. destruct (std W !! k); simpl; [|done].
    by rewrite decide_False.
  Qed.

  Lemma related_pub_close_set S W : related_sts_pub_world W (close_set S W).
  Proof.
    split; [|apply related_sts_pub_refl].
    split; [by rewrite dom_close_set|].
    intros k x y Hx Hy. rewrite close_set_lookup Hx /= in Hy. injection Hy as <-.
    case_decide; [|apply rtc_refl].
    destruct x; simpl; [apply rtc_refl|].
    apply rtc_once. constructor.
  Qed.

End local_world.
