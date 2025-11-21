From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.

Section VAE_helper.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
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
    rtc (λ x y : positive,
         convert_rel awk_rel_pub x y
         ∨ convert_rel awk_rel_pub x y ∨ convert_rel awk_rel_priv x y) y x ->
    x = (encode true) ∨ x = (encode false).
  Proof.
    intros Heq Hrtc.
    induction Hrtc; auto.
    destruct Heq; subst.
    + destruct H as [ | [] ].
      all: inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      all: apply IHHrtc; destruct b; auto.
    + destruct H as [ | [] ].
      all: inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      all: apply IHHrtc; destruct b; auto.
  Qed.

  Lemma awk_rel_inv (b : bool) (d d' : positive) :
    d = encode b ->
    rtc (λ x y : positive,
         convert_rel awk_rel_pub x y
         ∨ convert_rel awk_rel_pub x y ∨ convert_rel awk_rel_priv x y) d d' ->
    ∃ b : bool, d' = encode b.
  Proof.
    intros Hd Hrtc.
    assert (d' = encode true ∨ (d' = encode false)).
    { eapply rtc_rel_inv; last done.
      destruct b ; auto.
    }
    destruct H; eexists; eauto.
  Qed.


  Lemma related_pub_W0_Wfixed (W0 W3 W6 : WORLD) (csp_b csp_e : Addr) (l : list Addr) ( i : positive) :
    let W1 := revoke W0 in
    let W2 := <l[i:=false]l>W1 in
    let W4 := revoke W3 in
    let W5 := <l[i:=true]l>W4 in
    let W7 := (revoke W6) in
    (∀ a : finz MemNum, W0.1 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e) ->
    related_sts_pub_world W2 W3 ->
    related_sts_pub_world
      (std_update_multiple W2 (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) W3 ->
    related_sts_pub_world W5 W6 ->
    related_sts_pub_world
      (std_update_multiple W5 (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) W6 ->
    Forall (λ a : finz MemNum, W6.1 !! a = Some Revoked) l ->
    Forall (λ a : finz MemNum, W6.1 !! a = Some Revoked) (finz.seq_between csp_b (csp_b ^+ 4)%a) ->
    finz.seq_between csp_b csp_e = finz.seq_between csp_b (csp_b ^+ 4)%a ++ finz.seq_between (csp_b ^+ 4)%a csp_e ->
    wrel W6 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    loc W6 !! i = Some (encode true) ->
    wrel W0 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_pub, convert_rel awk_rel_priv) ->
    (exists b : bool, loc W0 !! i = Some (encode b)) ->

    related_sts_pub_world W0
      (close_list (l ++ finz.seq_between csp_b csp_e) W7).
  Proof.
    intros W1 W2 W4 W5 W7.
    intros Htemporaries_W0 Hrelated_pub_W2_W3 Hrelated_pub_W2ext_W3 Hrelated_pub_W5_W6 Hrelated_pub_W5ext_W6
      HW6_revoked_l Hrevoked_stk_l Hsplit_csp Hwrel_i Hwloc_i Hwrel_i_0 Hwloc_i_0.

    assert ( related_sts_priv_world W0 W6 ) as Hrelated_priv_W0_W6.
    { eapply (related_sts_priv_trans_world _ W3); eauto.
      + eapply (related_sts_priv_pub_trans_world _ W2); eauto.
        subst W2 W1.
        eapply (related_sts_priv_trans_world _ (revoke W0)).
        * apply revoke_related_sts_priv_world.
        * destruct Hwloc_i_0 as [b Hwloc_i_0].
          eapply related_sts_priv_world_loc_update; eauto.
          right;right; apply convert_rel_of_rel; done.
      + eapply (related_sts_priv_pub_trans_world _ W5); eauto.
        subst W4 W5.
        eapply (related_sts_priv_trans_world _ (revoke W3)).
        * apply revoke_related_sts_priv_world.
        *
          destruct Hrelated_pub_W2_W3 as [HW2_W3_std (Hdom_loc_2_3 & Hdom_rel_2_3 & Hrtc_loc_2_3)].
          assert (∃ d_W3, loc W3 !! i = Some d_W3) as [d_W3 Hd_W3].
          { apply elem_of_dom.
            apply Hdom_loc_2_3.
            rewrite dom_insert.
            rewrite elem_of_union; right.
            apply elem_of_dom.
            set_solver+Hwloc_i_0.
          }
          assert (∃ r1 r2 r3, wrel W3 !! i = Some (r1, r2, r3)) as (r1 & r2 & r3 & HW3_rel).
          { assert (is_Some (wrel W0 !! i)) as HW0_rel_some by set_solver+Hwrel_i_0.
            apply elem_of_dom in HW0_rel_some.
            apply Hdom_rel_2_3 in HW0_rel_some.
            apply elem_of_dom in HW0_rel_some as [ [ [] ] HW3_rel].
            eexists _,_,_; eauto.
          }
          destruct Hwloc_i_0 as [b Hwloc_i_0].
          specialize (Hrtc_loc_2_3 i _ _ _ _ _ _ Hwrel_i_0 HW3_rel) as (<- & <- & <- & Hrtc_loc_0_3).
          ospecialize (Hrtc_loc_0_3 _ _ _ Hd_W3); first by simplify_map_eq.
          eapply awk_rel_pub_inv in Hrtc_loc_0_3 as [b' ->]; last done.
          eapply related_sts_priv_world_loc_update; eauto.
          right;right; apply convert_rel_of_rel; done.
    }
    split; cbn; cycle 1.
    - destruct W0 as [W0_std [W0_loc W0_rel] ],
                 W3 as [W3_std [W3_loc W3_rel] ],
                   W6 as [W6_std [W6_loc W6_rel] ]
                   ; cbn.
      destruct Hrelated_pub_W2_W3 as [HW2_W3_std HW2_W3_cus].
      destruct Hrelated_pub_W5_W6 as [HW5_W6_std HW5_W6_cus].
      destruct Hrelated_priv_W0_W6 as [HW0_W6_std HW0_W6_cus].
      destruct HW0_W6_cus as (Hdom_loc_0_6 & Hdom_rel_0_6 & Hrtc_loc_0_6); cbn in *.
      split;[|split];auto.
      intros d r1 r2 r1' r2' r3 r3' HW0_rel HW6_rel.
      specialize (Hrtc_loc_0_6 d _ _ _ _ _ _ HW0_rel HW6_rel) as (-> & -> & -> & Hrtc_loc_0_6).
      repeat (split;first done).
      intros d_W0 d_W6 Hd_W0 Hd_W6.
      destruct HW2_W3_cus as (Hdom_loc_2_3 & Hdom_rel_2_3 & Hrtc_loc_2_3); cbn in *.
      assert (∃ d_W3, W3_loc !! d = Some d_W3) as [d_W3 Hd_W3].
      { apply elem_of_dom.
        apply Hdom_loc_2_3.
        rewrite dom_insert.
        rewrite elem_of_union; right.
        apply elem_of_dom.
        set_solver+Hd_W0.
      }
      assert (∃ r1 r2 r3, W3_rel !! d = Some (r1, r2, r3)) as (r1 & r2 & r3 & HW3_rel).
      { assert (is_Some (W0_rel !! d)) as HW0_rel_some by set_solver+HW0_rel.
        apply elem_of_dom in HW0_rel_some.
        apply Hdom_rel_2_3 in HW0_rel_some.
        apply elem_of_dom in HW0_rel_some as [ [ [] ] HW3_rel].
        eexists _,_,_; eauto.
      }

      destruct (decide (d = i)); simplify_eq.
      + destruct Hwloc_i_0 as [b Hwloc_i_0]; simplify_eq.
        apply rtc_once.
        destruct HW5_W6_cus as (Hdom_loc_5_6 & Hdom_rel_5_6 & Hrtc_loc_5_6); cbn in *.
        apply convert_rel_of_rel.
        by right.
      + eapply (rtc_transitive d_W0 d_W3 d_W6).
        * specialize (Hrtc_loc_2_3 d _ _ _ _ _ _ HW0_rel HW3_rel) as (-> & -> & -> & Hrtc_loc_0_3).
          ospecialize (Hrtc_loc_0_3 d_W0 d_W3 _ Hd_W3).
          { by simplify_map_eq. }
          done.
        * destruct HW5_W6_cus as (Hdom_loc_5_6 & Hdom_rel_5_6 & Hrtc_loc_5_6); cbn in *.
          specialize (Hrtc_loc_5_6 d _ _ _ _ _ _ HW3_rel HW6_rel) as (-> & -> & -> & Hrtc_loc_5_6).
          ospecialize (Hrtc_loc_5_6 d_W3 d_W6 _ Hd_W6).
          { by simplify_map_eq. }
          done.
    - cbn in *.
      split.
      {
        intros a Ha.
        rewrite elem_of_dom -close_list_std_sta_is_Some -revoke_std_sta_lookup_Some -elem_of_dom.
        destruct Hrelated_pub_W5_W6 as [ [Hdom_W5_W6 _] _].
        apply Hdom_W5_W6.
        rewrite -revoke_dom_eq.
        destruct Hrelated_pub_W2_W3 as [ [Hdom_W2_W3 _] _].
        apply Hdom_W2_W3.
        by rewrite -revoke_dom_eq.
      }
      intros a ρ0 ρ2 Ha0 Ha2.
      destruct ρ0; cycle 1.
      + (* the initial a was in the Permanent state *)
        assert (a ∉ l ++ finz.seq_between csp_b csp_e) as Ha_notin.
        { destruct (Htemporaries_W0 a) as [_ ?].
          intro Hcontra; apply H in Hcontra. by rewrite Ha0 in Hcontra.
        }
        apply revoke_lookup_Perm in Ha0.
        assert (std W3 !! a = Some Permanent) as Ha0_W3.
        { rewrite (region_state_pub_perm W2); eauto. }
        assert (std W6 !! a = Some Permanent) as Ha0_W6.
        { rewrite (region_state_pub_perm W5); eauto.
          subst W5. cbn.
          rewrite revoke_lookup_Perm; eauto.
        }
        rewrite -close_list_std_sta_same in Ha2; eauto.
        apply revoke_lookup_Perm in Ha0_W6.
        simplify_map_eq.
        apply rtc_refl.
      + (* the initial a was in the Revoked state *)
        destruct ρ2; last apply rtc_refl; apply rtc_once; constructor.
      + (* the initial a was in the Temporary state *)
        assert (a ∈ l ++ finz.seq_between csp_b csp_e) as Ha_in.
        { destruct (Htemporaries_W0 a) as [? _]; by apply Htemporaries_W0. }
        apply revoke_lookup_Monotemp in Ha0.
        assert (std W1 !! a = Some Revoked) as Ha0_W1.
        { done. }
        assert (std W2 !! a = Some Revoked) as Ha0_W2.
        { done. }
        assert (
            std ((std_update_multiple W2 (finz.seq_between (csp_b ^+ 4)%a csp_e)
                    Temporary)) !! a =
            Some (if (decide (a ∈ (finz.seq_between (csp_b ^+ 4)%a csp_e)))
                  then Temporary
                  else Revoked
          )).
        {
          destruct (decide (a ∈ (finz.seq_between (csp_b ^+ 4)%a csp_e))) as [Ha_in_stk | Ha_in_stk].
          + apply std_sta_update_multiple_lookup_in_i; eauto.
          + rewrite std_sta_update_multiple_lookup_same_i; eauto.
        }

        destruct (decide (a ∈ finz.seq_between (csp_b ^+ 4)%a csp_e)) as [Ha_in''|Ha_in''].
        * assert (std W3 !! a = Some Temporary) as Ha0_W3.
          { eapply region_state_pub_temp; eauto. }
          assert (std W4 !! a = Some Revoked) as Ha0_W4.
          { by apply revoke_lookup_Monotemp. }
          assert (std W5 !! a = Some Revoked) as Ha0_W5 by done.
          assert (
              std (std_update_multiple W5 (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) !! a = Some Temporary
            ) as Ha0_W5ext.
          { apply std_sta_update_multiple_lookup_in_i; eauto. }
          assert (std W6 !! a = Some Temporary) as Ha0_W6.
          { eapply region_state_pub_temp; eauto. }
          assert (std W7 !! a = Some Revoked) as Ha0_W7.
          { by apply revoke_lookup_Monotemp. }
          eapply (close_list_std_sta_revoked _ _ _  Ha_in) in Ha0_W7; eauto.
          rewrite Ha2 in Ha0_W7; simplify_eq.
          apply rtc_refl.
        * destruct (decide (a ∈ finz.seq_between csp_b (csp_b ^+ 4)%a)) as [Ha_in_save|Ha_in_save].
          ** rewrite Forall_forall in Hrevoked_stk_l.
             apply Hrevoked_stk_l in Ha_in_save.
             apply revoke_lookup_Revoked in Ha_in_save.
             eapply (close_list_std_sta_revoked _ _ _  Ha_in) in Ha_in_save; eauto.
             rewrite Ha2 in Ha_in_save; simplify_eq.
             apply rtc_refl.
          ** assert (a ∈ l) as Ha_in_l.
             { rewrite Hsplit_csp in Ha_in.
               rewrite elem_of_app in Ha_in.
               destruct Ha_in; first done.
               rewrite elem_of_app in H0.
               destruct H0; contradiction.
             }
             rewrite Forall_forall in HW6_revoked_l.
             apply HW6_revoked_l in Ha_in_l.
             apply revoke_lookup_Revoked in Ha_in_l.
             eapply (close_list_std_sta_revoked _ _ _  Ha_in) in Ha_in_l; eauto.
             rewrite Ha2 in Ha_in_l; simplify_eq.
             apply rtc_refl.
  Qed.

End VAE_helper.
