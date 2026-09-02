From iris.proofmode Require Import proofmode.
From griotte Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.

Section VAE_helper.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Definition awkN : namespace := nroot .@ "awkN".
  Definition awk_inv C i a :=
    (∃ x:bool, sts_state_loc (A:=Addr) C i x
            ∗ if x
              then a ↦ₐ WInt 1%Z
              else a ↦ₐ WInt 0%Z)%I.

  Definition awk_rel_pub := λ a b, a = false ∨ b = true.
  Definition awk_rel_priv := λ (a b : bool), True.

  Lemma rtc_rel_pub y x :
    y = (encode true) ->
    rtc (convert_rel awk_rel_pub) y x ->
    x = (encode true).
  Proof.
    intros Heq Hrtc.
    induction Hrtc; auto.
    rewrite Heq in H.
    inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ].
    inversion Hy; subst; auto.
    apply encode_inj in Heq1. inversion Heq1.
  Qed.
  Lemma rtc_rel_pub' x :
    rtc (convert_rel awk_rel_pub) (encode true) (encode x) ->
    x = true.
  Proof.
    intros Hrtc.
    apply encode_inj.
    apply rtc_rel_pub with (encode true); auto.
  Qed.

  Lemma rtc_rel_pub_inv y x :
    y = (encode true) ∨ y = (encode false) ->
    rtc (convert_rel awk_rel_pub) y x ->
    x = (encode true) ∨ x = (encode false).
  Proof.
    intros Heq Hrtc.
    induction Hrtc; auto.
    destruct Heq; subst.
    + inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      apply IHHrtc. destruct b; auto.
    + inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      apply IHHrtc. destruct b; auto.
  Qed.

  Lemma awk_rel_pub_inv (b : bool) (d d' : positive) :
    d = encode b ->
    rtc (convert_rel awk_rel_pub) d d' ->
    ∃ b : bool, d' = encode b.
  Proof.
    intros Hd Hrtc.
    assert (d' = encode true ∨ (d' = encode false)).
    { eapply rtc_rel_pub_inv; last done.
      destruct b ; auto.
    }
    destruct H; eexists; eauto.
  Qed.

  Lemma rtc_rel_inv y x :
    y = (encode true) ∨ y = (encode false) ->
    rtc (λ x y : positive, convert_rel awk_rel_pub x y ∨ convert_rel awk_rel_priv x y) y x ->
    x = (encode true) ∨ x = (encode false).
  Proof.
    intros Heq Hrtc.
    induction Hrtc; auto.
    destruct Heq; subst.
    + destruct H as [ | ].
      all: inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      all: apply IHHrtc; destruct b; auto.
    + destruct H as [ | ].
      all: inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      all: apply IHHrtc; destruct b; auto.
  Qed.

  Lemma awk_rel_inv (b : bool) (d d' : positive) :
    d = encode b ->
    rtc (λ x y : positive, convert_rel awk_rel_pub x y ∨ convert_rel awk_rel_priv x y) d d' ->
    ∃ b : bool, d' = encode b.
  Proof.
    intros Hd Hrtc.
    assert (d' = encode true ∨ (d' = encode false)).
    { eapply rtc_rel_inv; last done.
      destruct b ; auto.
    }
    destruct H; eexists; eauto.
  Qed.

  (** Updating the awkward flag to [false] is always a private transition.
      Keeping this custom-world calculation opaque avoids repeating it in
      the instruction proof. *)
  Lemma awk_loc_update_false_related_priv
      (W : WORLD) (i : positive) (b : bool) :
    loc W !! i = Some (encode b) ->
    wrel W !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    related_sts_priv_world W (<l[i:=false]l>W).
  Proof.
    intros Hloc Hrel.
    rewrite /related_sts_priv_world /=.
    split; first apply related_sts_std_priv_refl.
    split; [set_solver|split;[set_solver|] ].
    intros d rpub rpriv rpub' rpriv' Hr Hr'; simplify_eq.
    repeat (split; first done).
    intros x y Hd Hd'.
    destruct (decide (d = i)); simplify_map_eq; last apply rtc_refl.
    destruct b; simplify_map_eq; last apply rtc_refl.
    apply rtc_once.
    right; apply convert_rel_of_rel; done.
  Qed.

  (** Updating the awkward flag to [true] is a public transition: once true,
      the public relation prevents a later observer from seeing false. *)
  Lemma awk_loc_update_true_related_pub
      (W : WORLD) (i : positive) (b : bool) :
    loc W !! i = Some (encode b) ->
    wrel W !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    related_sts_pub_world W (<l[i:=true]l>W).
  Proof.
    intros Hloc Hrel.
    rewrite /related_sts_pub_world /=.
    split; first apply related_sts_std_pub_refl.
    split; [set_solver|split;[set_solver|] ].
    intros d rpub rpriv rpub' rpriv' Hr Hr'; simplify_eq.
    repeat (split; first done).
    intros x y Hd Hd'.
    destruct (decide (d = i)); simplify_map_eq; last apply rtc_refl.
    destruct b; simplify_map_eq; first apply rtc_refl.
    apply rtc_once.
    apply convert_rel_of_rel.
    by left.
  Qed.

  (** Private evolution preserves that the awkward location encodes a
      Boolean, without exposing the custom-world tuple to callers. *)
  Lemma awk_loc_is_bool_mono_priv
      (W W' : WORLD) (i : positive) (b : bool) :
    related_sts_priv_world W W' ->
    loc W !! i = Some (encode b) ->
    wrel W !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    exists b' : bool, loc W' !! i = Some (encode b').
  Proof.
    intros (_ & (Hdom_loc & Hdom_rel & Hrtc)) Hloc Hrel.
    assert (is_Some (loc W' !! i)) as [d' Hloc'].
    { apply elem_of_dom, Hdom_loc, elem_of_dom. eauto. }
    assert (is_Some (wrel W' !! i)) as [rr Hrel'].
    { apply elem_of_dom, Hdom_rel, elem_of_dom. eauto. }
    destruct rr as [rpub rpriv].
    specialize (Hrtc i _ _ _ _ Hrel Hrel') as (<- & <- & Hrtc).
    specialize (Hrtc _ _ Hloc Hloc').
    eapply awk_rel_inv in Hrtc as [b' ->]; last done.
    eauto.
  Qed.

  (** Public evolution preserves a true awkward flag. *)
  Lemma awk_loc_true_mono_pub
      (W W' : WORLD) (i : positive) :
    related_sts_pub_world W W' ->
    loc W !! i = Some (encode true) ->
    wrel W !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    loc W' !! i = Some (encode true).
  Proof.
    intros (_ & (Hdom_loc & Hdom_rel & Hrtc)) Hloc Hrel.
    assert (is_Some (loc W' !! i)) as [d' Hloc'].
    { apply elem_of_dom, Hdom_loc, elem_of_dom. eauto. }
    assert (is_Some (wrel W' !! i)) as [rr Hrel'].
    { apply elem_of_dom, Hdom_rel, elem_of_dom. eauto. }
    destruct rr as [rpub rpriv].
    specialize (Hrtc i _ _ _ _ Hrel Hrel') as (<- & <- & Hrtc).
    specialize (Hrtc _ _ Hloc Hloc').
    apply rtc_rel_pub with (y := encode true) in Hrtc; auto.
    by simplify_eq.
  Qed.

  (** Reconcile the custom flag across the two adversary calls and close the
      addresses revoked by the calling convention.  The explicit [closing]
      parameter keeps this pure repair independent of any concrete stack
      layout used by the VAE closure theorem. *)
  Lemma awk_two_call_world_repair
      (W0 W3 W6 : WORLD) (closing : list Addr)
      (b : bool) (i : positive) :
    let W1 := revoke W0 in
    let W2 := <l[i:=false]l>W1 in
    let W4 := revoke W3 in
    let W5 := <l[i:=true]l>W4 in
    let W7 := revoke W6 in
    (forall a : Addr, std W0 !! a = Some Temporary <-> a ∈ closing) ->
    Forall (fun a : Addr => std W7 !! a = Some Revoked) closing ->
    related_sts_pub_world W2 W3 ->
    related_sts_pub_world W5 W6 ->
    loc W1 !! i = Some (encode b) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    loc W7 !! i = Some (encode true) ->
    wrel W7 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    related_sts_pub_world W0 (close_list closing W7).
  Proof.
    intros * Htemporaries_W0 Hrevoked_W7
             Hrelated_pub_W2_W3 Hrelated_pub_W5_W6
             Hwloc_i_0 Hwrel_i_0 Hwrel_i_7 Hwloc_i_7.

    assert (related_sts_priv_world W0 W2) as Hrelated_priv_W0_W2.
    { eapply (related_sts_priv_trans_world _ W1); eauto.
      + apply revoke_related_sts_priv_world.
      + subst W2.
        eapply awk_loc_update_false_related_priv; eauto.
    }
    assert (related_sts_priv_world W3 W5) as Hrelated_priv_W3_W5.
    { eapply (related_sts_priv_trans_world _ W4); eauto.
      + apply revoke_related_sts_priv_world.
      + destruct Hrelated_pub_W2_W3 as
          (HW2_W3_std &
           (Hdom_loc_2_3 & Hdom_rel_2_3 & Hrtc_loc_2_3)).
        assert (exists d_W3, loc W3 !! i = Some d_W3) as [d_W3 Hd_W3].
        { apply elem_of_dom.
          apply Hdom_loc_2_3.
          rewrite dom_insert elem_of_union; right.
          apply elem_of_dom. set_solver+Hwloc_i_0.
        }
        assert (exists r1 r2, wrel W3 !! i = Some (r1, r2))
          as (rpub & rpriv & HW3_rel).
        { assert (is_Some (wrel W0 !! i)) as HW0_rel_some
              by set_solver+Hwrel_i_0.
          apply elem_of_dom in HW0_rel_some.
          apply Hdom_rel_2_3 in HW0_rel_some.
          apply elem_of_dom in HW0_rel_some as [pair HW3_rel].
          destruct pair as [r1 r2].
          eexists _, _; eauto.
        }
        specialize (Hrtc_loc_2_3 i _ _ _ _ Hwrel_i_0 HW3_rel)
          as (<- & <- & Hrtc_loc_0_3).
        ospecialize (Hrtc_loc_0_3 _ _ _ Hd_W3);
          first by simplify_map_eq.
        eapply awk_rel_pub_inv in Hrtc_loc_0_3 as [b0 ->]; last done.
        eapply related_sts_priv_world_loc_update; eauto.
        right; apply convert_rel_of_rel; done.
    }
    assert (related_sts_priv_world W0 W6) as Hrelated_priv_W0_W6.
    { eapply (related_sts_priv_trans_world _ W3); eauto.
      + eapply (related_sts_priv_pub_trans_world _ W2); eauto.
      + eapply (related_sts_priv_pub_trans_world _ W5); eauto.
    }

    split; cbn; cycle 1.
    - destruct W0 as [W0_std [W0_loc W0_rel] ].
      destruct W3 as [W3_std [W3_loc W3_rel] ].
      destruct W6 as [W6_std [W6_loc W6_rel] ].
      cbn.
      destruct Hrelated_pub_W2_W3 as
        (HW2_W3_std & HW2_W3_cus).
      destruct Hrelated_pub_W5_W6 as
        (HW5_W6_std & HW5_W6_cus).
      destruct Hrelated_priv_W0_W6 as
        (HW0_W6_std & HW0_W6_cus).
      destruct HW0_W6_cus as
        (Hdom_loc_0_6 & Hdom_rel_0_6 & Hrtc_loc_0_6); cbn in *.
      split; [|split]; auto.
      intros d rpub rpriv rpub' rpriv' HW0_rel HW6_rel.
      specialize (Hrtc_loc_0_6 d _ _ _ _ HW0_rel HW6_rel)
        as (-> & -> & Hrtc_loc_0_6).
      repeat (split; first done).
      intros d_W0 d_W6 Hd_W0 Hd_W6.
      destruct HW2_W3_cus as
        (Hdom_loc_2_3 & Hdom_rel_2_3 & Hrtc_loc_2_3); cbn in *.
      assert (exists d_W3, W3_loc !! d = Some d_W3) as [d_W3 Hd_W3].
      { apply elem_of_dom.
        apply Hdom_loc_2_3.
        rewrite dom_insert elem_of_union; right.
        apply elem_of_dom. set_solver+Hd_W0.
      }
      assert (exists r1 r2, W3_rel !! d = Some (r1, r2))
        as (rpub & rpriv & HW3_rel).
      { assert (is_Some (W0_rel !! d)) as HW0_rel_some
            by set_solver+HW0_rel.
        apply elem_of_dom in HW0_rel_some.
        apply Hdom_rel_2_3 in HW0_rel_some.
        apply elem_of_dom in HW0_rel_some as [pair HW3_rel].
        destruct pair as [r1 r2].
        eexists _, _; eauto.
      }
      destruct (decide (d = i)); simplify_eq.
      + apply rtc_once.
        destruct HW5_W6_cus as
          (Hdom_loc_5_6 & Hdom_rel_5_6 & Hrtc_loc_5_6); cbn in *.
        apply convert_rel_of_rel. by right.
      + eapply (rtc_trans d_W0 d_W3 d_W6).
        * specialize (Hrtc_loc_2_3 d _ _ _ _ HW0_rel HW3_rel)
            as (-> & -> & Hrtc_loc_0_3).
          ospecialize (Hrtc_loc_0_3 d_W0 d_W3 _ Hd_W3);
            first by simplify_map_eq.
          done.
        * destruct HW5_W6_cus as
            (Hdom_loc_5_6 & Hdom_rel_5_6 & Hrtc_loc_5_6); cbn in *.
          specialize (Hrtc_loc_5_6 d _ _ _ _ HW3_rel HW6_rel)
            as (-> & -> & Hrtc_loc_5_6).
          ospecialize (Hrtc_loc_5_6 d_W3 d_W6 _ Hd_W6);
            first by simplify_map_eq.
          done.
    - cbn in *.
      split.
      { intros a Ha.
        rewrite elem_of_dom -close_list_std_sta_is_Some
          -revoke_std_sta_lookup_Some -elem_of_dom.
        destruct Hrelated_pub_W5_W6 as [ [Hdom_W5_W6 _] _].
        apply Hdom_W5_W6.
        rewrite -revoke_dom_eq.
        destruct Hrelated_pub_W2_W3 as [ [Hdom_W2_W3 _] _].
        apply Hdom_W2_W3. by rewrite -revoke_dom_eq.
      }
      intros a rho0 rho2 Ha0 Ha2.
      destruct rho0; cycle 1.
      + assert (a ∉ closing) as Ha_notin.
        { destruct (Htemporaries_W0 a) as [_ Hnot].
          intro Hcontra; apply Hnot in Hcontra.
          by rewrite Ha0 in Hcontra.
        }
        apply revoke_lookup_Perm in Ha0.
        assert (std W3 !! a = Some Permanent) as Ha0_W3.
        { rewrite (region_state_pub_perm W2); eauto. }
        assert (std W6 !! a = Some Permanent) as Ha0_W6.
        { rewrite (region_state_pub_perm W5); eauto.
          subst W5; cbn. rewrite revoke_lookup_Perm; eauto.
        }
        rewrite -close_list_std_sta_same in Ha2; eauto.
        apply revoke_lookup_Perm in Ha0_W6.
        simplify_map_eq. apply rtc_refl.
      + destruct rho2; last apply rtc_refl; apply rtc_once; constructor.
      + assert (a ∈ closing) as Ha_in.
        { destruct (Htemporaries_W0 a) as [Hin _].
          by apply Hin.
        }
        apply revoke_lookup_Monotemp in Ha0.
        assert (std W1 !! a = Some Revoked) as Ha0_W1 by done.
        assert (std W2 !! a = Some Revoked) as Ha0_W2 by done.
        rewrite Forall_forall in Hrevoked_W7.
        pose proof (Hrevoked_W7 a Ha_in) as Ha_W6.
        eapply (close_list_std_sta_revoked _ _ _ Ha_in) in Ha_W6; eauto.
        rewrite Ha2 in Ha_W6; simplify_eq.
        apply rtc_refl.
  Qed.

End VAE_helper.
