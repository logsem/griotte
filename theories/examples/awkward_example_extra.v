From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel region_invariants fundamental region_invariants_revocation region_invariants_static
     region_invariants_batch_uninitialized region_invariants_transitions stack_object_helpers.
From cap_machine Require Export stdpp_extra iris_extra.

Section awkward_helpers.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Lemma related_sts_priv_world_Uninitialized_to_Revoked W a w :
    W.1 !! a = Some (Uninitialized w) →
    related_sts_priv_world W (<s[a:=Revoked]s> W).
  Proof.
    intros Huninit.
    split;[|apply related_sts_priv_refl].
    split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (i = a)).
      + subst. simplify_map_eq.
        right with Monotemporary. left. constructor.
        eright;[|left]. right. right. constructor.
      + simplify_map_eq. left.
  Qed.

  (* Notation for overriding W with a map *)
  Notation "m1 >> W" := (override_uninitialize m1 W) (at level 40, left associativity).

  Lemma awkward_world_reconstruct W W' W1 W2 Wmid W3 W4 W5 Wmid2 Wfinal (m m' m2 : gmap Addr Word)
        maddrs lframe' lframe (bstk estk a_param a_param2 a_param3 frame_end a_act_final a_act_end a_act_end': Addr)
        i (framelist1 framelist2 : list Word) :
    W' = std_update_multiple (<s[bstk:=Revoked]s>(uninitialize W m)) (region_addrs a_param frame_end) Revoked →
    W1 = std_update_multiple (W'.1, (<[i:=encode false]> W.2.1, W.2.2)) (elements (dom (gset Addr) lframe))(Monostatic lframe) →
    W2 = <s[a_act_end:=Monotemporary]s>W1 →
    W3 = std_update_multiple (<s[bstk:=Revoked]s>(lframe >> uninitialize Wmid m')) (region_addrs a_param a_act_end) Revoked →
    W4 = std_update_multiple (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2)) (elements (dom (gset Addr) lframe')) (Monostatic lframe') →
    W5 = <s[a_act_final:=Monotemporary]s>W4 →
    Wfinal = initialize_list maddrs (lframe' >> uninitialize Wmid2 m2) →
    maddrs = filter (λ a : Addr, (a < bstk)%a) (elements (dom (gset Addr) m) ++ elements (dom (gset Addr) m')) →
    lframe = list_to_map (zip (region_addrs bstk a_act_end) framelist1) →
    lframe' = list_to_map (zip (region_addrs bstk a_act_final) framelist2) →
    length framelist1 = 10 → length framelist2 = 9 →

    (∀ a' : Addr, is_Some (m !! a') ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    (∀ a' : Addr, (bstk <= a' < estk)%a → ∃ w : Word, (uninitialize W m).1 !! a' = Some (Uninitialized w)) →
    (∀ a' : Addr, is_Some (m' !! a') ↔ std Wmid !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    (∀ a' : Addr, (bstk <= a' < estk)%a → ∃ w : Word, (lframe >> uninitialize Wmid m').1 !! a' = Some (Uninitialized w)) →
    (∀ a' : Addr, is_Some (m2 !! a') ↔ std Wmid2 !! a' = Some Monotemporary ∧ (bstk <= a')%a) →
    (∀ a : Addr, a ∈ dom (gset Addr) lframe → Wmid.1 !! a = Some (Monostatic lframe)) →
    (∀ a : Addr, a ∈ dom (gset Addr) lframe' → Wmid2.1 !! a = Some (Monostatic lframe')) →
    (10%nat + 1%nat < estk - bstk)%Z →
    (bstk + 1%nat)%a = Some a_param →
    (a_param + 1)%a = Some a_param2 →
    (a_param2 + 1)%a = Some a_param3 →
    (a_param + 10)%a = Some frame_end →
    (a_param3 + 6)%a = Some a_act_final →
    (a_param3 + 7)%a = Some a_act_end →
    (a_param2 + 6)%a = Some a_act_end' →
    related_sts_a_world W2 Wmid a_act_end →
    related_sts_a_world W5 Wmid2 a_act_final →
    (∃ b : bool, W.2.1 !! i = Some (encode b)) →
    W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_pub, convert_rel awk_rel_priv) →
    related_sts_a_world W Wfinal bstk.
  Proof.
    intros HW' HW1 HW2 HW3 HW4 HW5 HWfinal Hmaddrs Hlframe Hlframe' Hlen1 Hlen2.
    intros Hmcond Hstk_cond Hmcond' Hstk_cond' Hmcond2 Hall_mono Hall_mono'.
    intros Hsize Ha_param Ha_param2 Ha_param3 Hframe_end Ha_act_final Ha_act_end Ha_act_end'.
    intros HrelatedW2Wmid HrelatedW5Wmid2 Hi Hirel.
    split.
    - split.
      { trans (dom (gset Addr) Wmid2.1);[trans (dom (gset Addr) Wmid.1);[trans (dom (gset Addr) W2.1)|
                                                                         trans (dom (gset Addr) W5.1)]|].
        - rewrite HW2 dom_insert_L HW1 HW'.
          trans (dom (gset Addr) (<s[bstk:=Revoked]s>(uninitialize W m)).1).
          rewrite dom_insert_L uninitialize_dom. clear;set_solver.
          etrans;[apply (std_update_multiple_sta_dom_subseteq _ (region_addrs a_param frame_end) Revoked)|].
          etrans;[apply (std_update_multiple_sta_dom_subseteq _ (elements (dom (gset Addr) lframe))
                                                              (Monostatic lframe))|].
          clear. rewrite -std_update_multiple_std_sta_eq. set_solver.
        - destruct HrelatedW2Wmid as [ [Hdom _] _]. auto.
        - rewrite HW5 dom_insert_L HW4 HW3 -std_update_multiple_std_sta_eq.
          trans (dom (gset Addr) (<s[bstk:=Revoked]s>(lframe >> uninitialize Wmid m')).1).
          trans (dom (gset Addr) (uninitialize Wmid m').1).
          rewrite uninitialize_dom;auto.
          etrans. apply override_uninitialize_std_sta_dom_subseteq with (m:=lframe).
          rewrite dom_insert_L. clear;set_solver.
          etrans;[apply (std_update_multiple_sta_dom_subseteq _ (region_addrs a_param a_act_end) Revoked)|].
          etrans;[apply (std_update_multiple_sta_dom_subseteq _ (elements (dom (gset Addr) lframe'))
                                                              (Monostatic lframe'))|].
          clear. set_solver.
        - destruct HrelatedW5Wmid2 as [ [Hdom _] _]. auto.
        - rewrite HWfinal -initialize_list_dom.
          etrans. 2: apply override_uninitialize_std_sta_dom_subseteq.
          rewrite uninitialize_dom. auto.
      }

      intros s x y Hx Hy.

      destruct (decide (s ∈ region_addrs bstk estk)).
      + (* s ∈ [bstk,estk) *)
        assert (s ∉ maddrs) as Hnin.
        { rewrite Hmaddrs. intros [Hcontr _]%elem_of_list_filter.
          apply elem_of_region_addrs in e. clear -e Hcontr. solve_addr. }
        rewrite HWfinal initialize_list_nin// in Hy.

        destruct (decide (s ∈ region_addrs bstk a_act_final)).
        * (* s ∈ [bstk,a_act_final), i.e. within the first and second frame *)
          assert (s ≠ a_act_end) as Hne.
          { apply elem_of_region_addrs in e0.
            clear -e0 Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final; solve_addr. }
          assert (is_Some (lframe' !! s)) as [w Hw].
          { rewrite Hlframe'. apply list_to_map_lookup_is_Some. rewrite fst_zip//.
            rewrite region_addrs_length /region_size Hlen2.
            clear -Ha_param Ha_param2 Ha_param3 Ha_act_final;solve_addr. }
          rewrite (override_uninitialize_std_sta_lookup_some _ _ _ w)// in Hy. inversion Hy;subst y.
          destruct (m !! s) eqn:Hsome.
          { apply elem_of_region_addrs, Hstk_cond in e as HH. destruct HH as [w' Hw'].
            assert (is_Some (m !! s)) as [Htemp _]%Hmcond;[eauto|].
            rewrite Hx in Htemp. inversion Htemp. subst x. eright;[|left].
            rewrite decide_True;[|clear -e;solve_addr]. right. constructor. }
          { apply elem_of_region_addrs, Hstk_cond in e as HH. destruct HH as [w' Hw'].
            rewrite uninitialize_std_sta_None_lookup// in Hw'. rewrite Hx in Hw'. inversion Hw';subst x.
            right with Monotemporary. rewrite decide_True;[|clear -e;solve_addr]. left. constructor.
            eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor. }

        * destruct (decide (s = a_act_final)).
          ** (* s = a_act_final, i.e. in the first frame but not the second *)
            subst s.
            assert (is_Some (lframe !! a_act_final)) as [w Hw].
            { rewrite Hlframe. apply list_to_map_lookup_is_Some. rewrite fst_zip//.
              apply elem_of_region_addrs. clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end;solve_addr.
              rewrite region_addrs_length /region_size Hlen1.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            assert (lframe' !! a_act_final = None) as Hnone.
            { rewrite Hlframe'. apply not_elem_of_list_to_map. rewrite fst_zip//.
              rewrite region_addrs_length /region_size Hlen2.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            rewrite (override_uninitialize_std_sta_lookup_none)// in Hy.
            apply elem_of_region_addrs, Hstk_cond in e as HH. destruct HH as [w' Hw'].
            destruct (m !! a_act_final) eqn:Hsome.
            *** assert (is_Some (m !! a_act_final)) as [Htemp _]%Hmcond;[eauto|].
                rewrite Hx in Htemp. inversion Htemp. subst x.
                destruct (m2 !! a_act_final) eqn:Hsome'.
                { assert (is_Some (m2 !! a_act_final)) as [Htemp2 _]%Hmcond2;[eauto|].
                  rewrite (uninitialize_std_sta_lookup_in _ _ _ w1)// in Hy. inversion Hy. subst y.
                  eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor. }
                { rewrite uninitialize_std_sta_None_lookup// in Hy.
                  destruct HrelatedW5Wmid2 as [ [Hsub Hrel] _]. specialize (Hrel a_act_final).
                  rewrite HW5 lookup_insert in Hrel. specialize (Hrel _ _ eq_refl Hy).
                  eapply rtc_implies. 2: apply Hrel. intros r q HH. rewrite decide_True.
                  rewrite decide_True in HH. auto. clear;solve_addr.
                  clear -e;solve_addr. }
            *** rewrite uninitialize_std_sta_None_lookup// in Hw'. rewrite Hx in Hw'. inversion Hw';subst x.
                destruct (m2 !! a_act_final) eqn:Hsome'.
                { assert (is_Some (m2 !! a_act_final)) as [Htemp2 _]%Hmcond2;[eauto|].
                  rewrite (uninitialize_std_sta_lookup_in _ _ _ w0)// in Hy. inversion Hy. subst y.
                  right with Monotemporary. rewrite decide_True;[|clear -e;solve_addr]. left;constructor.
                  eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor. }
                { rewrite uninitialize_std_sta_None_lookup// in Hy.
                  destruct HrelatedW5Wmid2 as [ [Hsub Hrel] _]. specialize (Hrel a_act_final).
                  rewrite HW5 lookup_insert in Hrel. specialize (Hrel _ _ eq_refl Hy).
                  apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel.
                  apply std_rel_pub_plus_rtc_Monotemporary in Hrel as [-> | [? ->] ];auto.
                  - eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. left. constructor.
                  - right with Monotemporary. rewrite decide_True;[|clear -e;solve_addr]. left;constructor.
                    eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor.
                  - intros r q Hrq. rewrite decide_True in Hrq. auto. clear;solve_addr. }

          ** (* s is never in any frame *)
            apply elem_of_region_addrs, Hstk_cond in e as HH. destruct HH as [w' Hw'].
            apply Hstk_cond' in e as HH. destruct HH as [w2 Hw2].
            assert (lframe' !! s = None) as Hnone'.
            { rewrite Hlframe'. apply not_elem_of_list_to_map. rewrite fst_zip//.
              rewrite region_addrs_length /region_size Hlen2.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            assert (lframe !! s = None) as Hnone.
            { rewrite Hlframe. apply not_elem_of_list_to_map. rewrite fst_zip//.
              apply not_elem_of_region_addrs in n. apply not_elem_of_region_addrs.
              clear -n n0 e Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end. solve_addr.
              rewrite region_addrs_length /region_size Hlen1.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            destruct HrelatedW2Wmid as [ [Hsub Hrel] _]. specialize (Hrel s).
            destruct HrelatedW5Wmid2 as [ [Hsub2 Hrel2] _]. specialize (Hrel2 s).
            apply not_elem_of_region_addrs in n.
            assert (W5.1 !! s = Some (Uninitialized w2)) as Hw52.
            { rewrite HW5 lookup_insert_ne// HW4 std_sta_update_multiple_lookup_same_i.
              2: rewrite elem_of_elements not_elem_of_dom//.
              rewrite HW3 /= std_sta_update_multiple_lookup_same_i.
              2: apply not_elem_of_region_addrs;
                clear -n n0 e Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end;solve_addr.
              rewrite lookup_insert_ne//.
              clear -n Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end;solve_addr. }
            destruct (m !! s) eqn:Hsome.
            *** assert (is_Some (m !! s)) as [Htemp _]%Hmcond;[eauto|].
                rewrite Hx in Htemp. inversion Htemp. subst x.
                rewrite override_uninitialize_std_sta_lookup_none// in Hy.
                destruct (m2 !! s) eqn:Hsome'.
                { assert (is_Some (m2 !! s)) as [Htemp2 _]%Hmcond2;[eauto|].
                  rewrite (uninitialize_std_sta_lookup_in _ _ _ w0)// in Hy. inversion Hy. subst y.
                  eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor. }
                rewrite uninitialize_std_sta_None_lookup// in Hy.
                specialize (Hrel2 _ _ Hw52 Hy).
                apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
                2: { intros r q Hrq. rewrite decide_True in Hrq. auto. clear -n e;solve_addr. }
                eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto;[left|].
                eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor.
            *** rewrite uninitialize_std_sta_None_lookup// in Hw'. rewrite Hx in Hw'. inversion Hw';subst x.
                rewrite override_uninitialize_std_sta_lookup_none// in Hy.
                destruct (m2 !! s) eqn:Hsome'.
                { assert (is_Some (m2 !! s)) as [Htemp2 _]%Hmcond2;[eauto|].
                  rewrite (uninitialize_std_sta_lookup_in _ _ _ w)// in Hy. inversion Hy. subst y.
                  right with Monotemporary. rewrite decide_True;[|clear -e;solve_addr]. left;constructor.
                  eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor. }
                rewrite (uninitialize_std_sta_None_lookup)// in Hy.
                specialize (Hrel2 _ _ Hw52 Hy).
                apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
                2: { intros r q Hrq. rewrite decide_True in Hrq. auto. clear -n e;solve_addr. }
                eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto.
                eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. left. constructor.
                right with Monotemporary. rewrite decide_True;[|clear -e;solve_addr]. left;constructor.
                eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor.

      + (* s is not a stack address: we will need to potentially reinstate any temporary resources *)
        (* we will now have to track its changes throughout. *)
        (* we begin by destructing on being temporary *)
        apply not_elem_of_region_addrs in n.

        assert (lframe' !! s = None) as Hnone'.
        { rewrite Hlframe'. apply not_elem_of_list_to_map. rewrite fst_zip//.
          apply not_elem_of_region_addrs.
          clear -n Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr.
          rewrite region_addrs_length /region_size Hlen2.
          clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
        assert (lframe !! s = None) as Hnone.
        { rewrite Hlframe. apply not_elem_of_list_to_map. rewrite fst_zip//.
          apply not_elem_of_region_addrs.
          clear -n Ha_param Ha_param2 Ha_param3 Hsize Ha_act_final Ha_act_end. solve_addr.
          rewrite region_addrs_length /region_size Hlen1.
          clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }

        destruct (m !! s) eqn:Hsome.
        * (* s is a temp resource in W *)
          assert (is_Some (m !! s)) as [Htemp _]%Hmcond;[eauto|].
          rewrite Hx in Htemp. inversion Htemp;subst x.
          destruct HrelatedW2Wmid as [ [Hsub Hrel] _].
          destruct HrelatedW5Wmid2 as [ [Hsub2 Hrel2] _].
          assert (W2.1 !! s = Some (Uninitialized w)) as Hw.
          { rewrite HW2 lookup_insert_ne.
            2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
            rewrite HW1 std_sta_update_multiple_lookup_same_i /=.
            2: rewrite elem_of_elements not_elem_of_dom//.
            rewrite HW' std_sta_update_multiple_lookup_same_i /=.
            2: apply not_elem_of_region_addrs;
              clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
            rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
            apply uninitialize_std_sta_lookup_in;auto. }

          assert (is_Some (Wmid.1 !! s)) as [z Hz].
          { apply elem_of_gmap_dom. apply Hsub. apply elem_of_gmap_dom. eauto. }

          specialize (Hrel s _ _ Hw Hz).

          (* we must distinguish between reinstating or not *)
          destruct (decide (s < bstk)%a).
          { assert (s ∈ maddrs) as Hin.
            { rewrite Hmaddrs. apply elem_of_list_filter. split;auto. apply elem_of_app. left.
              apply elem_of_elements,elem_of_gmap_dom. eauto. }

            apply rtc_implies with (Q:=λ x y, Rpub x y) in Hrel.
            2: { intros r q Hrq. rewrite decide_False in Hrq;auto.
                 clear -n l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr. }
            eapply std_rel_pub_rtc_Uninitialized in Hrel as [Heq | Heq];eauto;subst z.

            - assert (is_Some (m' !! s)) as [w' Hw'].
              { apply Hmcond'. split;auto. clear;solve_addr. }

              assert (W5.1 !! s = Some (Uninitialized w')) as Hw5.
              { rewrite HW5 lookup_insert_ne.
                2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
                2: rewrite elem_of_elements not_elem_of_dom//.
                rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
                2: apply not_elem_of_region_addrs;
                  clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
                rewrite override_uninitialize_std_sta_lookup_none//.
                apply uninitialize_std_sta_lookup_in;auto. }

              assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
              { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

              specialize (Hrel2 s _ _ Hw5 Hz2).
              apply rtc_implies with (Q:=λ x y, Rpub x y) in Hrel2.
              2: { intros r q Hrq. rewrite decide_False in Hrq;auto.
                   clear -n l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr. }

              eapply std_rel_pub_rtc_Uninitialized in Hrel2 as [Heq | Heq];eauto;subst z2.

              + rewrite HWfinal initialize_list_nuninit in Hy.
                rewrite override_uninitialize_std_sta_lookup_none// in Hy.
                rewrite uninitialize_std_sta_None_lookup in Hy. rewrite Hz2 in Hy. inversion Hy. subst y. left.
                apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hcontr l;solve_addr.
                rewrite override_uninitialize_std_sta_lookup_none// uninitialize_std_sta_None_lookup//.
                rewrite Hz2. eauto.
                apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hcontr l;solve_addr.
              + rewrite HWfinal (initialize_list_in _ _ _ w') in Hy. inversion Hy. subst y. left. auto.
                rewrite override_uninitialize_std_sta_lookup_none// uninitialize_std_sta_None_lookup//.
                apply eq_None_not_Some. intros [Hcontr _]%Hmcond2. rewrite Hz2 in Hcontr. inversion Hcontr.

            - assert (W5.1 !! s = Some (Uninitialized w)) as Hw5.
              { rewrite HW5 lookup_insert_ne.
                2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
                2: rewrite elem_of_elements not_elem_of_dom//.
                rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
                2: apply not_elem_of_region_addrs;
                  clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
                rewrite override_uninitialize_std_sta_lookup_none//.
                rewrite uninitialize_std_sta_None_lookup;auto. apply eq_None_not_Some.
                intros [Hcontr _]%Hmcond'. rewrite Hz in Hcontr. done. }

              assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
              { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

              specialize (Hrel2 s _ _ Hw5 Hz2).
              apply rtc_implies with (Q:=λ x y, Rpub x y) in Hrel2.
              2: { intros r q Hrq. rewrite decide_False in Hrq;auto.
                   clear -n l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr. }

              eapply std_rel_pub_rtc_Uninitialized in Hrel2 as [Heq | Heq];eauto;subst z2.

              + rewrite HWfinal initialize_list_nuninit in Hy.
                rewrite override_uninitialize_std_sta_lookup_none// in Hy.
                rewrite uninitialize_std_sta_None_lookup in Hy. rewrite Hz2 in Hy. inversion Hy. subst y. left.
                apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hcontr l;solve_addr.
                rewrite override_uninitialize_std_sta_lookup_none// uninitialize_std_sta_None_lookup//.
                rewrite Hz2. eauto.
                apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hcontr l;solve_addr.
              + rewrite HWfinal (initialize_list_in _ _ _ w) in Hy. inversion Hy. subst y. left. auto.
                rewrite override_uninitialize_std_sta_lookup_none// uninitialize_std_sta_None_lookup//.
                apply eq_None_not_Some. intros [Hcontr _]%Hmcond2. rewrite Hz2 in Hcontr. inversion Hcontr.
          }

          (* in the following case, s is not reinstated *)
          assert (s ∉ maddrs) as Hnin.
          { rewrite Hmaddrs. intros [Hcontr _]%elem_of_list_filter. done. }

          apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel.
          2: { intros r q Hrq. destruct (decide (le_a a_act_end s));auto. }
          apply rtc_implies with (R:=λ x y, Rpub x y ∨ Rpubp x y).
          { intros r q Hrq. rewrite decide_True. auto. clear -n0;solve_addr. }

          eapply std_rel_pub_plus_rtc_Uninitialized in Hrel as Heq;eauto.
          assert (∃ w, W5.1 !! s = Some (Uninitialized w)) as [w' Hw'].
          { rewrite HW5 lookup_insert_ne.
            2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
            rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
            2: rewrite elem_of_elements not_elem_of_dom//.
            rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
            2: apply not_elem_of_region_addrs;
              clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
            rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
            rewrite override_uninitialize_std_sta_lookup_none//.
            destruct Heq as [-> | [? ->] ].
            assert (is_Some (m' !! s)) as [? Hm'];[apply Hmcond';split;auto;clear;solve_addr|].
            rewrite (uninitialize_std_sta_lookup_in _ _ _ x)//. eauto.
            rewrite uninitialize_std_sta_None_lookup;auto. rewrite Hz;eauto. apply eq_None_not_Some.
            intros [Hcontr _]%Hmcond'. rewrite Hz in Hcontr. done. }

          assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
          { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

          specialize (Hrel2 s _ _ Hw' Hz2).
          apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
          2: { intros r q Hrq. destruct (decide (le_a a_act_final s));auto. }
          eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto.
          { rewrite HWfinal initialize_list_nin// in Hy.
            assert (is_Some (m2 !! s)) as [? Hw2];[apply Hmcond2;split;auto;clear -n0;solve_addr|].
            rewrite override_uninitialize_std_sta_lookup_none//
                    (uninitialize_std_sta_lookup_in _ _ _ x) in Hy;auto. inversion Hy. subst y.
            eright;[|left]. right. constructor. }
          { rewrite HWfinal initialize_list_nin// in Hy.
            assert (m2 !! s = None) as Hw2.
            { apply eq_None_not_Some. intros [Hcontr _]%Hmcond2. rewrite Hz2 in Hcontr;done. }
            rewrite override_uninitialize_std_sta_lookup_none//
            (uninitialize_std_sta_None_lookup) in Hy;auto.
            rewrite Hz2 in Hy. inversion Hy. subst y.
            eright;[|left]. right. constructor. }

        * (* s is not a temp resource in W *)
          destruct HrelatedW2Wmid as [ [Hsub Hrel] _].
          destruct HrelatedW5Wmid2 as [ [Hsub2 Hrel2] _].
          assert (W2.1 !! s = Some x) as Hx'.
          { rewrite HW2 lookup_insert_ne.
            2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
            rewrite HW1 std_sta_update_multiple_lookup_same_i /=.
            2: rewrite elem_of_elements not_elem_of_dom//.
            rewrite HW' std_sta_update_multiple_lookup_same_i /=.
            2: apply not_elem_of_region_addrs;
              clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
            rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
            rewrite uninitialize_std_sta_None_lookup;auto. }

          assert (is_Some (Wmid.1 !! s)) as [z Hz].
          { apply elem_of_gmap_dom. apply Hsub. apply elem_of_gmap_dom. eauto. }

          specialize (Hrel _ _ _ Hx' Hz).
          trans z.
          eapply rtc_implies. 2:apply Hrel.
          { simpl; intros r q Hrq. destruct (decide (a_act_end <= s)%a).
            rewrite decide_True. auto.
            clear -n l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
            destruct (decide (bstk <= s)%a);auto. }

          destruct (m' !! s) eqn:Hsome'.
          ** assert (is_Some (m' !! s)) as [Htemp _]%Hmcond';eauto.
             rewrite Hz in Htemp. inversion Htemp. subst z.

             (* again we will have to distinguish between reinstating or not *)
             destruct (decide (s < bstk)%a).
             { assert (s ∈ maddrs) as Hin.
               { rewrite Hmaddrs. apply elem_of_list_filter. split;auto. apply elem_of_app. right.
                 apply elem_of_elements,elem_of_gmap_dom. eauto. }
               apply rtc_implies with (Q:=λ x y, Rpub x y) in Hrel.
               2: { intros r q Hrq. rewrite decide_False in Hrq;auto.
                    clear -n l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr. }

               assert (W5.1 !! s = Some (Uninitialized w)) as Hw5.
               { rewrite HW5 lookup_insert_ne.
                 2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                 rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
                 2: rewrite elem_of_elements not_elem_of_dom//.
                 rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
                 2: apply not_elem_of_region_addrs;
                   clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                 rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
                 rewrite override_uninitialize_std_sta_lookup_none//.
                 apply uninitialize_std_sta_lookup_in;auto. }

               assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
               { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

               specialize (Hrel2 s _ _ Hw5 Hz2).
               apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
               2: { intros r q Hrq. destruct (decide (le_a a_act_final s));auto. }
               eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto.
               { assert (m2 !! s = None) as Hnone2.
                 { apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hcontr l;solve_addr. }
                 rewrite HWfinal (initialize_list_nuninit)// in Hy.
                 rewrite override_uninitialize_std_sta_lookup_none//
                 (uninitialize_std_sta_None_lookup) in Hy;auto. rewrite Hz2 in Hy. inversion Hy;subst y.
                 left. rewrite override_uninitialize_std_sta_lookup_none//
                 (uninitialize_std_sta_None_lookup);auto. rewrite Hz2. eauto. }
               { assert (m2 !! s = None) as Hnone2.
                 { apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hcontr l;solve_addr. }
                 rewrite HWfinal (initialize_list_in _ _ _ x0)// in Hy. inversion Hy;subst y;left.
                 rewrite override_uninitialize_std_sta_lookup_none//
                         (uninitialize_std_sta_None_lookup);auto. }
             }
             { assert (s ∉ maddrs) as Hnin.
               { rewrite Hmaddrs. intros [Hcontr _]%elem_of_list_filter. done. }
               apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel.
               2: { intros r q Hrq. destruct (decide (le_a a_act_end s));auto. }
               apply rtc_implies with (R:=λ x y, Rpub x y ∨ Rpubp x y).
               { intros r q Hrq. rewrite decide_True. auto. clear -n0;solve_addr. }

               assert (W5.1 !! s = Some (Uninitialized w)) as Hw5.
               { rewrite HW5 lookup_insert_ne.
                 2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                 rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
                 2: rewrite elem_of_elements not_elem_of_dom//.
                 rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
                 2: apply not_elem_of_region_addrs;
                   clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                 rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
                 rewrite override_uninitialize_std_sta_lookup_none//.
                 apply uninitialize_std_sta_lookup_in;auto. }

               assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
               { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

               specialize (Hrel2 s _ _ Hw5 Hz2).
               apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
               2: { intros r q Hrq. destruct (decide (le_a a_act_final s));auto. }
               eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto.
               { assert (is_Some (m2 !! s)) as [w2 Hw2].
                 { apply Hmcond2. split;auto. clear -n0;solve_addr. }
                 rewrite HWfinal (initialize_list_nin)// in Hy.
                 rewrite override_uninitialize_std_sta_lookup_none//
                         (uninitialize_std_sta_lookup_in _ _ _ w2) in Hy;auto. inversion Hy;subst y.
                 eright;[|left]. right;constructor. }
               { assert (m2 !! s = None) as Hnone2.
                 { apply eq_None_not_Some. intros [Hcontr _]%Hmcond2. by rewrite Hz2 in Hcontr. }
                 rewrite HWfinal (initialize_list_nin)// in Hy.
                 rewrite override_uninitialize_std_sta_lookup_none//
                         (uninitialize_std_sta_None_lookup) in Hy;auto.
                 rewrite Hz2 in Hy. inversion Hy;subst y.
                 eright;[|left]. right;constructor.
               }
             }

          ** (* in this case, it is neither in m or m' and is therefore not reinstated *)
            assert (s ∉ maddrs) as Hnin.
            { rewrite Hmaddrs. intros [_ Hcontr]%elem_of_list_filter.
              apply elem_of_app in Hcontr as [Hcontr%elem_of_elements%elem_of_gmap_dom |
                                              Hcontr%elem_of_elements%elem_of_gmap_dom].
              rewrite Hsome in Hcontr. by inversion Hcontr. rewrite Hsome' in Hcontr. by inversion Hcontr. }

            assert (W5.1 !! s = Some z) as Hz5.
             { rewrite HW5 lookup_insert_ne.
               2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
               rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
               2: rewrite elem_of_elements not_elem_of_dom//.
               rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
               2: apply not_elem_of_region_addrs;
                   clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
               rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
               rewrite override_uninitialize_std_sta_lookup_none//.
               rewrite uninitialize_std_sta_None_lookup;auto. }

             assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
             { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

             specialize (Hrel2 s _ _ Hz5 Hz2).
             rewrite HWfinal initialize_list_nin// override_uninitialize_std_sta_lookup_none// in Hy.

             destruct (m2 !! s) eqn:Hsome2.
            *** trans z2.
                { eapply rtc_implies. 2: apply Hrel2. simpl.
                  intros r q Hrq. destruct (decide (a_act_final <= s)%a).
                  rewrite decide_True;auto.
                  clear -l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                  destruct (decide (bstk <= s)%a);auto. }
                assert (is_Some (m2 !! s)) as [Htemp Hle]%Hmcond2;eauto.
                rewrite (uninitialize_std_sta_lookup_in _ _ _ w)// in Hy. inversion Hy;subst y.
                rewrite Hz2 in Htemp. inversion Htemp. subst z2.
                eright;[|left]. rewrite decide_True. right;constructor. clear -Hle;solve_addr.
            *** rewrite uninitialize_std_sta_None_lookup// in Hy. rewrite Hz2 in Hy. inversion Hy;subst y.
                eapply rtc_implies;[|apply Hrel2].
                intros r q Hrq. destruct (decide (le_a a_act_final s)).
                rewrite decide_True;auto.
                clear -l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                destruct (decide (le_a bstk s));auto.

    - destruct HrelatedW2Wmid as [_ [Hdomsta [Hdomrel Hrel] ] ].
      destruct HrelatedW5Wmid2 as [_ [Hdomsta2 [Hdomrel2 Hrel2] ] ].

      split;[|split].
      + rewrite HWfinal initialize_list_loc /override_uninitialize /=.
        etrans;[|apply Hdomsta2].
        rewrite HW5 HW4 /= std_update_multiple_loc HW3 /= std_update_multiple_loc /=.
        rewrite dom_insert_L.
        clear -Hdomsta HW2 HW1 HW'. trans (dom (gset positive) W2.2.1). 2: set_solver.
        rewrite HW2 HW1 /= std_update_multiple_loc HW' /=. set_solver.
      + rewrite HWfinal initialize_list_loc /override_uninitialize /=.
        etrans;[|apply Hdomrel2].
        rewrite HW5 HW4 /= std_update_multiple_loc HW3 /= std_update_multiple_loc /=.
        clear -Hdomrel HW2 HW1 HW'. trans (dom (gset positive) W2.2.2). 2: set_solver.
        rewrite HW2 HW1 /= std_update_multiple_loc HW' /=. set_solver.
      + intros j r1 r2 r1' r2' r3 r3' Hx Hy.
        assert (W2.2.2 !! j = Some (r1,r2,r3)) as Hx'.
        { rewrite HW2 HW1 /= std_update_multiple_loc /= //. }
        destruct (decide (i = j)).
        * subst i. rewrite Hirel in Hx. inversion Hx.
          (* subst r1 r2 r3. *)
          assert (is_Some (Wmid.2.2 !! j)) as [? Hz].
          { apply elem_of_gmap_dom. apply Hdomrel. apply elem_of_gmap_dom;eauto. }
          destruct x. destruct p.
          specialize (Hrel j _ _ _ _ _ _ Hx' Hz) as [-> [-> [-> Hrel2'] ] ].
          assert (W5.2.2 !! j = Some (P0,P1,P)) as Hx2.
          { rewrite HW5 HW4 /= std_update_multiple_loc /= HW3 std_update_multiple_loc /= //. }
          assert (is_Some (Wmid2.2.2 !! j)) as [? Hz'].
          { apply elem_of_gmap_dom. apply Hdomrel2. apply elem_of_gmap_dom;eauto. }
          destruct x. destruct p.
          specialize (Hrel2 j _ _ _ _ _ _ Hx2 Hz') as [-> [-> [-> Hrel2''] ] ].
          rewrite HWfinal initialize_list_loc /= in Hy.
          rewrite Hz' in Hy. inversion Hy. subst P3 P4 P2. inversion Hy. subst r1' r2' r3'.
          repeat split;auto.
          intros x y Hxx Hyy.
          destruct Hi as [b Hb]. rewrite Hb in Hxx. inversion Hxx. subst x.
          assert (W5.2.1 !! j = Some (encode true)) as Hj.
          { rewrite HW5 HW4 /= std_update_multiple_loc /=. apply lookup_insert. }
          assert (is_Some (Wmid2.2.1 !! j)) as [? Hj'].
          { apply elem_of_gmap_dom. apply Hdomsta2. apply elem_of_gmap_dom;eauto. }
          specialize (Hrel2'' _ _ Hj Hj').
          apply rtc_implies with (Q:=λ x y : positive, convert_rel awk_rel_pub x y) in Hrel2''.
          2: { intros r q [Hrq|Hrq];auto. }
          apply rtc_rel_pub in Hrel2'';auto. subst x.
          rewrite HWfinal initialize_list_loc /= in Hyy. rewrite Hj' in Hyy. inversion Hyy.
          destruct b. left.
          eright;[|left]. left. repeat eexists. constructor. done.
        * assert (is_Some (Wmid.2.2 !! j)) as [? Hz].
          { apply elem_of_gmap_dom. apply Hdomrel. apply elem_of_gmap_dom;eauto. }
          destruct x. destruct p.
          specialize (Hrel j _ _ _ _ _ _ Hx' Hz) as [-> [-> [-> Hrel2'] ] ].
          assert (W5.2.2 !! j = Some (P0,P1,P)) as Hx2.
          { rewrite HW5 HW4 /= std_update_multiple_loc /= HW3 std_update_multiple_loc /= //. }
          assert (is_Some (Wmid2.2.2 !! j)) as [? Hz'].
          { apply elem_of_gmap_dom. apply Hdomrel2. apply elem_of_gmap_dom;eauto. }
          destruct x. destruct p.
          specialize (Hrel2 j _ _ _ _ _ _ Hx2 Hz') as [-> [-> [-> Hrel2''] ] ].
          rewrite HWfinal initialize_list_loc /= in Hy.
          rewrite Hz' in Hy. inversion Hy. subst P3 P4 P2. inversion Hy.
          repeat split;auto.
          intros x y Hxx Hyy.
          assert (W2.2.1 !! j = Some x) as Hj.
          { rewrite HW2 /= HW1 std_update_multiple_loc /=. rewrite lookup_insert_ne//. }
          assert (is_Some (Wmid.2.1 !! j)) as [? Hj'].
          { apply elem_of_gmap_dom. apply Hdomsta. apply elem_of_gmap_dom;eauto. }
          specialize (Hrel2' _ _ Hj Hj').
          assert (W5.2.1 !! j = Some x0) as Hk.
          { rewrite HW5 HW4 /= std_update_multiple_loc /=. rewrite lookup_insert_ne//.
            rewrite HW3 std_update_multiple_loc /= //. }
          assert (is_Some (Wmid2.2.1 !! j)) as [? Hk'].
          { apply elem_of_gmap_dom. apply Hdomsta2. apply elem_of_gmap_dom;eauto. }
          specialize (Hrel2'' _ _ Hk Hk').
          etrans. apply Hrel2'.
          rewrite HWfinal initialize_list_loc /= in Hyy. rewrite Hyy in Hk'. inversion Hk'. subst y.
          apply Hrel2''.
  Qed.

  Lemma awkward_world_reconstruct_mid W W' W1 W2 Wmid W3 W4 W5 Wmid2 Wfinal (m m' m2 : gmap Addr Word)
        maddrs lframe' lframe (bstk estk a_param a_param2 a_param3 frame_end a_act_final a_act_end a_act_end': Addr)
        i (framelist1 framelist2 : list Word) :
    W' = std_update_multiple (<s[bstk:=Revoked]s>(uninitialize W m)) (region_addrs a_param frame_end) Revoked →
    W1 = std_update_multiple (W'.1, (<[i:=encode false]> W.2.1, W.2.2)) (elements (dom (gset Addr) lframe))(Monostatic lframe) →
    W2 = <s[a_act_end:=Monotemporary]s>W1 →
    W3 = std_update_multiple (<s[bstk:=Revoked]s>(lframe >> uninitialize Wmid m')) (region_addrs a_param a_act_end) Revoked →
    W4 = std_update_multiple (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2)) (elements (dom (gset Addr) lframe')) (Monostatic lframe') →
    W5 = <s[a_act_final:=Monotemporary]s>W4 →
    Wfinal = initialize_list maddrs (lframe' >> uninitialize Wmid2 m2) →
    maddrs = filter (λ a : Addr, (a < bstk)%a) (elements (dom (gset Addr) m) ++ elements (dom (gset Addr) m')) →
    lframe = list_to_map (zip (region_addrs bstk a_act_end) framelist1) →
    lframe' = list_to_map (zip (region_addrs bstk a_act_final) framelist2) →
    length framelist1 = 10 → length framelist2 = 9 →

    (∀ a' : Addr, is_Some (m !! a') ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    (∀ a' : Addr, (bstk <= a' < estk)%a → ∃ w : Word, (uninitialize W m).1 !! a' = Some (Uninitialized w)) →
    (∀ a' : Addr, is_Some (m' !! a') ↔ std Wmid !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    (∀ a' : Addr, (bstk <= a' < estk)%a → ∃ w : Word, (lframe >> uninitialize Wmid m').1 !! a' = Some (Uninitialized w)) →
    (∀ a' : Addr, is_Some (m2 !! a') ↔ std Wmid2 !! a' = Some Monotemporary ∧ (bstk <= a')%a) →
    (∀ a : Addr, a ∈ dom (gset Addr) lframe → Wmid.1 !! a = Some (Monostatic lframe)) →
    (∀ a : Addr, a ∈ dom (gset Addr) lframe' → Wmid2.1 !! a = Some (Monostatic lframe')) →
    (10%nat + 1%nat < estk - bstk)%Z →
    (bstk + 1%nat)%a = Some a_param →
    (a_param + 1)%a = Some a_param2 →
    (a_param2 + 1)%a = Some a_param3 →
    (a_param + 10)%a = Some frame_end →
    (a_param3 + 6)%a = Some a_act_final →
    (a_param3 + 7)%a = Some a_act_end →
    (a_param2 + 6)%a = Some a_act_end' →
    related_sts_a_world W2 Wmid a_act_end →
    related_sts_a_world W5 Wmid2 a_act_final →
    (∃ b : bool, W3.2.1 !! i = Some (encode b)) →
    W3.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_pub, convert_rel awk_rel_priv) →
    related_sts_a_world Wmid Wfinal bstk.
  Proof.
    intros HW' HW1 HW2 HW3 HW4 HW5 HWfinal Hmaddrs Hlframe Hlframe' Hlen1 Hlen2.
    intros Hmcond Hstk_cond Hmcond' Hstk_cond' Hmcond2 Hall_mono Hall_mono'.
    intros Hsize Ha_param Ha_param2 Ha_param3 Hframe_end Ha_act_final Ha_act_end Ha_act_end'.
    intros HrelatedW2Wmid HrelatedW5Wmid2 Hi Hirel.
    split.
    - split.
      { trans (dom (gset Addr) Wmid2.1);[trans (dom (gset Addr) W5.1)|].
        - rewrite HW5 dom_insert_L HW4 HW3 -std_update_multiple_std_sta_eq.
          trans (dom (gset Addr) (<s[bstk:=Revoked]s>(lframe >> uninitialize Wmid m')).1).
          trans (dom (gset Addr) (uninitialize Wmid m').1).
          rewrite uninitialize_dom;auto.
          etrans. apply override_uninitialize_std_sta_dom_subseteq with (m:=lframe).
          rewrite dom_insert_L. clear;set_solver.
          etrans;[apply (std_update_multiple_sta_dom_subseteq _ (region_addrs a_param a_act_end) Revoked)|].
          etrans;[apply (std_update_multiple_sta_dom_subseteq _ (elements (dom (gset Addr) lframe'))
                                                              (Monostatic lframe'))|].
          clear. set_solver.
        - destruct HrelatedW5Wmid2 as [ [Hdom _] _]. auto.
        - rewrite HWfinal -initialize_list_dom.
          etrans. 2: apply override_uninitialize_std_sta_dom_subseteq.
          rewrite uninitialize_dom. auto.
      }

      intros s x y Hx Hy.

      destruct (decide (s ∈ region_addrs bstk estk)).
      + (* s ∈ [bstk,estk) *)
        assert (s ∉ maddrs) as Hnin.
        { rewrite Hmaddrs. intros [Hcontr _]%elem_of_list_filter.
          apply elem_of_region_addrs in e. clear -e Hcontr. solve_addr. }
        rewrite HWfinal initialize_list_nin// in Hy.

        destruct (decide (s ∈ region_addrs bstk a_act_final)).
        * (* s ∈ [bstk,a_act_final), i.e. within the first and second frame *)
          assert (s ∈ region_addrs bstk a_act_end) as e1.
          { apply elem_of_region_addrs in e0. apply elem_of_region_addrs.
            clear -e0 Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final; solve_addr. }
          assert (s ≠ a_act_end) as Hne.
          { apply elem_of_region_addrs in e0.
            clear -e0 Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final; solve_addr. }
          assert (is_Some (lframe' !! s)) as [w Hw].
          { rewrite Hlframe'. apply list_to_map_lookup_is_Some. rewrite fst_zip//.
            rewrite region_addrs_length /region_size Hlen2.
            clear -Ha_param Ha_param2 Ha_param3 Ha_act_final;solve_addr. }
          assert (is_Some (lframe !! s)) as [w' Hw'].
          { rewrite Hlframe. apply list_to_map_lookup_is_Some. rewrite fst_zip//.
            rewrite region_addrs_length /region_size Hlen1.
            clear -Ha_param Ha_param2 Ha_param3 Ha_act_end;solve_addr. }
          rewrite (override_uninitialize_std_sta_lookup_some _ _ _ w)// in Hy. inversion Hy;subst y.
          destruct HrelatedW2Wmid as [ [Hdom Hrel] _].
          assert (W2.1 !! s = Some (Monostatic lframe)) as Hw2.
          { rewrite HW2. rewrite lookup_insert_ne//. rewrite HW1. apply std_sta_update_multiple_lookup_in_i.
            apply elem_of_elements, elem_of_gmap_dom;eauto. }
          specialize (Hrel _ _ _ Hw2 Hx).
          apply rtc_implies with (Q:=λ x y, Rpub x y) in Hrel.
          2: { simpl. intros r q. rewrite decide_False. auto. apply elem_of_region_addrs in e1.
               clear -e1. solve_addr. }
          eapply std_rel_pub_rtc_Monostatic in Hrel;eauto. subst x.
          right with (Monotemporary). rewrite decide_True. right;econstructor.
          apply elem_of_region_addrs in e1. clear -e1. solve_addr.
          eright;[|left]. rewrite decide_True. right;econstructor.
          apply elem_of_region_addrs in e1. clear -e1. solve_addr.

        * destruct (decide (s = a_act_final)).
          ** (* s = a_act_final, i.e. in the first frame but not the second *)
            subst s.
            assert (is_Some (lframe !! a_act_final)) as [w Hw].
            { rewrite Hlframe. apply list_to_map_lookup_is_Some. rewrite fst_zip//.
              apply elem_of_region_addrs. clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end;solve_addr.
              rewrite region_addrs_length /region_size Hlen1.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            assert (lframe' !! a_act_final = None) as Hnone.
            { rewrite Hlframe'. apply not_elem_of_list_to_map. rewrite fst_zip//.
              rewrite region_addrs_length /region_size Hlen2.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            rewrite (override_uninitialize_std_sta_lookup_none)// in Hy.
            apply elem_of_region_addrs, Hstk_cond in e as HH. destruct HH as [w' Hw'].
            assert (W2.1 !! a_act_final = Some (Monostatic lframe)) as Hw2.
            { rewrite HW2. rewrite lookup_insert_ne//. rewrite HW1. apply std_sta_update_multiple_lookup_in_i.
              apply elem_of_elements, elem_of_gmap_dom;eauto. clear -Ha_act_end Ha_act_final;solve_addr. }
            destruct HrelatedW5Wmid2 as [ [Hdom2 Hrel2] _].
            destruct HrelatedW2Wmid as [ [Hdom Hrel] _].
            assert (W5.1 !! a_act_final = Some Monotemporary) as Hw5.
            { rewrite HW5 lookup_insert. auto. }

            specialize (Hrel _ _ _ Hw2 Hx).
            apply rtc_implies with (Q:=λ x y, Rpub x y) in Hrel.
            2: { simpl. intros r q. rewrite decide_False. auto. clear -Ha_act_end Ha_act_final;solve_addr. }
            eapply std_rel_pub_rtc_Monostatic in Hrel;eauto. subst x.

            assert (is_Some (Wmid2.1 !! a_act_final)) as [? Hy2].
            { apply elem_of_gmap_dom. apply Hdom2. apply elem_of_gmap_dom. eauto. }
            specialize (Hrel2 _ _ _ Hw5 Hy2).
            apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
            2: { simpl. intros r q. rewrite decide_True. auto. clear;solve_addr. }
            eapply std_rel_pub_plus_rtc_Monotemporary in Hrel2;eauto.
            destruct Hrel2 as [-> | [? ->] ].
            { assert (is_Some (m2 !! a_act_final)) as [? Hw3].
              { apply Hmcond2. split;auto.
                clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
              rewrite (uninitialize_std_sta_lookup_in _ _ _ x)// in Hy. inversion Hy. subst y.
              right with (Monotemporary). rewrite decide_True. right;econstructor.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr.
              eright;[|left]. rewrite decide_True. right;econstructor.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            { assert (m2 !! a_act_final = None) as Hnone'.
              { apply eq_None_not_Some. intros [Hcontr _]%Hmcond2. rewrite Hy2 in Hcontr. congruence. }
              rewrite uninitialize_std_sta_None_lookup// in Hy. rewrite Hy in Hy2. inversion Hy2. subst y.
              right with (Monotemporary). rewrite decide_True. right;econstructor.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr.
              eright;[|left]. rewrite decide_True. right;econstructor.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }

          ** (* s is not in the frame *)
            apply elem_of_region_addrs, Hstk_cond' in e as HH. destruct HH as [w2 Hw2].
            assert (lframe' !! s = None) as Hnone'.
            { rewrite Hlframe'. apply not_elem_of_list_to_map. rewrite fst_zip//.
              rewrite region_addrs_length /region_size Hlen2.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            assert (lframe !! s = None) as Hnone.
            { rewrite Hlframe. apply not_elem_of_list_to_map. rewrite fst_zip//.
              apply not_elem_of_region_addrs in n. apply not_elem_of_region_addrs.
              clear -n n0 e Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end. solve_addr.
              rewrite region_addrs_length /region_size Hlen1.
              clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
            destruct HrelatedW2Wmid as [ [Hsub Hrel] _]. specialize (Hrel s).
            destruct HrelatedW5Wmid2 as [ [Hsub2 Hrel2] _]. specialize (Hrel2 s).
            apply not_elem_of_region_addrs in n.
            assert (W5.1 !! s = Some (Uninitialized w2)) as Hw52.
            { rewrite HW5 lookup_insert_ne// HW4 std_sta_update_multiple_lookup_same_i.
              2: rewrite elem_of_elements not_elem_of_dom//.
              rewrite HW3 /= std_sta_update_multiple_lookup_same_i.
              2: apply not_elem_of_region_addrs;
                clear -n n0 e Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end;solve_addr.
              rewrite lookup_insert_ne//.
              clear -n Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end;solve_addr. }
            destruct (m' !! s) eqn:Hsome.
            *** assert (is_Some (m' !! s)) as [Htemp _]%Hmcond';[eauto|].
                rewrite Hx in Htemp. inversion Htemp. subst x.
                rewrite override_uninitialize_std_sta_lookup_none// in Hy.
                destruct (m2 !! s) eqn:Hsome'.
                { assert (is_Some (m2 !! s)) as [Htemp2 _]%Hmcond2;[eauto|].
                  rewrite (uninitialize_std_sta_lookup_in _ _ _ w0)// in Hy. inversion Hy. subst y.
                  eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor. }
                rewrite uninitialize_std_sta_None_lookup// in Hy.
                specialize (Hrel2 _ _ Hw52 Hy).
                apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
                2: { intros r q Hrq. rewrite decide_True in Hrq. auto. clear -n e;solve_addr. }
                eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto;[left|].
                eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor.
            *** rewrite override_uninitialize_std_sta_lookup_none// in Hw2.
                rewrite uninitialize_std_sta_None_lookup// in Hw2. rewrite Hx in Hw2. inversion Hw2;subst x.
                rewrite override_uninitialize_std_sta_lookup_none// in Hy.
                destruct (m2 !! s) eqn:Hsome'.
                { assert (is_Some (m2 !! s)) as [Htemp2 _]%Hmcond2;[eauto|].
                  rewrite (uninitialize_std_sta_lookup_in _ _ _ w)// in Hy. inversion Hy. subst y.
                  right with Monotemporary. rewrite decide_True;[|clear -e;solve_addr]. left;constructor.
                  eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor. }
                rewrite (uninitialize_std_sta_None_lookup)// in Hy.
                specialize (Hrel2 _ _ Hw52 Hy).
                apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
                2: { intros r q Hrq. rewrite decide_True in Hrq. auto. clear -n e;solve_addr. }
                eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto.
                eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. left. constructor.
                right with Monotemporary. rewrite decide_True;[|clear -e;solve_addr]. left;constructor.
                eright;[|left]. rewrite decide_True;[|clear -e;solve_addr]. right. constructor.

      + (* s is not a stack address: we will need to potentially reinstate any temporary resources *)
        (* we will now have to track its changes throughout. *)
        (* we begin by destructing on being temporary *)
        apply not_elem_of_region_addrs in n.

        assert (lframe' !! s = None) as Hnone'.
        { rewrite Hlframe'. apply not_elem_of_list_to_map. rewrite fst_zip//.
          apply not_elem_of_region_addrs.
          clear -n Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr.
          rewrite region_addrs_length /region_size Hlen2.
          clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }
        assert (lframe !! s = None) as Hnone.
        { rewrite Hlframe. apply not_elem_of_list_to_map. rewrite fst_zip//.
          apply not_elem_of_region_addrs.
          clear -n Ha_param Ha_param2 Ha_param3 Hsize Ha_act_final Ha_act_end. solve_addr.
          rewrite region_addrs_length /region_size Hlen1.
          clear -Ha_param Ha_param2 Ha_param3 Ha_act_final Ha_act_end Hsize;solve_addr. }

        destruct HrelatedW2Wmid as [ [Hsub Hrel] _].
        destruct HrelatedW5Wmid2 as [ [Hsub2 Hrel2] _].

        destruct (m' !! s) eqn:Hsome.
        * (* s is not a temp resource in W *)
          assert (is_Some (m' !! s)) as [Htemp _]%Hmcond';eauto.
             rewrite Hx in Htemp. inversion Htemp. subst x.

             (* again we will have to distinguish between reinstating or not *)
             destruct (decide (s < bstk)%a).
             { assert (s ∈ maddrs) as Hin.
               { rewrite Hmaddrs. apply elem_of_list_filter. split;auto. apply elem_of_app. right.
                 apply elem_of_elements,elem_of_gmap_dom. eauto. }

               assert (W5.1 !! s = Some (Uninitialized w)) as Hw5.
               { rewrite HW5 lookup_insert_ne.
                 2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                 rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
                 2: rewrite elem_of_elements not_elem_of_dom//.
                 rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
                 2: apply not_elem_of_region_addrs;
                   clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                 rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
                 rewrite override_uninitialize_std_sta_lookup_none//.
                 apply uninitialize_std_sta_lookup_in;auto. }

               assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
               { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

               specialize (Hrel2 s _ _ Hw5 Hz2).
               apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
               2: { intros r q Hrq. destruct (decide (le_a a_act_final s));auto. }
               eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto.
               { assert (m2 !! s = None) as Hnone2.
                 { apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hcontr l;solve_addr. }
                 rewrite HWfinal (initialize_list_nuninit)// in Hy.
                 rewrite override_uninitialize_std_sta_lookup_none//
                 (uninitialize_std_sta_None_lookup) in Hy;auto. rewrite Hz2 in Hy. inversion Hy;subst y.
                 left. rewrite override_uninitialize_std_sta_lookup_none//
                 (uninitialize_std_sta_None_lookup);auto. rewrite Hz2. eauto. }
               { assert (m2 !! s = None) as Hnone2.
                 { apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hcontr l;solve_addr. }
                 rewrite HWfinal (initialize_list_in _ _ _ x)// in Hy. inversion Hy;subst y;left.
                 rewrite override_uninitialize_std_sta_lookup_none//
                         (uninitialize_std_sta_None_lookup);auto. }
             }
             { assert (s ∉ maddrs) as Hnin.
               { rewrite Hmaddrs. intros [Hcontr _]%elem_of_list_filter. done. }

               assert (W5.1 !! s = Some (Uninitialized w)) as Hw5.
               { rewrite HW5 lookup_insert_ne.
                 2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                 rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
                 2: rewrite elem_of_elements not_elem_of_dom//.
                 rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
                 2: apply not_elem_of_region_addrs;
                   clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                 rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
                 rewrite override_uninitialize_std_sta_lookup_none//.
                 apply uninitialize_std_sta_lookup_in;auto. }

               assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
               { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

               specialize (Hrel2 s _ _ Hw5 Hz2).
               apply rtc_implies with (Q:=λ x y, Rpub x y ∨ Rpubp x y) in Hrel2.
               2: { intros r q Hrq. destruct (decide (le_a a_act_final s));auto. }
               eapply std_rel_pub_plus_rtc_Uninitialized in Hrel2 as [-> | [? ->] ];eauto.
               { assert (is_Some (m2 !! s)) as [w2 Hw2].
                 { apply Hmcond2. split;auto. clear -n0;solve_addr. }
                 rewrite HWfinal (initialize_list_nin)// in Hy.
                 rewrite override_uninitialize_std_sta_lookup_none//
                         (uninitialize_std_sta_lookup_in _ _ _ w2) in Hy;auto. inversion Hy;subst y.
                 eright;[|left]. rewrite decide_True. right;constructor. clear -n0;solve_addr. }
               { assert (m2 !! s = None) as Hnone2.
                 { apply eq_None_not_Some. intros [Hcontr _]%Hmcond2. by rewrite Hz2 in Hcontr. }
                 rewrite HWfinal (initialize_list_nin)// in Hy.
                 rewrite override_uninitialize_std_sta_lookup_none//
                         (uninitialize_std_sta_None_lookup) in Hy;auto.
                 rewrite Hz2 in Hy. inversion Hy;subst y.
                 eright;[|left]. rewrite decide_True. right;constructor. clear -n0;solve_addr.
               }

             }

          *  assert (W5.1 !! s = Some x) as Hz5.
             { rewrite HW5 lookup_insert_ne.
               2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
               rewrite HW4 std_sta_update_multiple_lookup_same_i /=.
               2: rewrite elem_of_elements not_elem_of_dom//.
               rewrite HW3 std_sta_update_multiple_lookup_same_i /=.
               2: apply not_elem_of_region_addrs;
                   clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
               rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
               rewrite override_uninitialize_std_sta_lookup_none//.
               rewrite uninitialize_std_sta_None_lookup;auto. }

             assert (is_Some (Wmid2.1 !! s)) as [z2 Hz2].
             { apply elem_of_gmap_dom. apply Hsub2. apply elem_of_gmap_dom. eauto. }

             destruct (decide (s ∈ maddrs)).
             { assert (e0:=e). rewrite Hmaddrs in e. apply elem_of_list_filter in e as [Hlt Hin].
               apply elem_of_app in Hin as [ [? Hin]%elem_of_elements%elem_of_gmap_dom |
                                            Hcontr%elem_of_elements%elem_of_gmap_dom].
               2: { rewrite Hsome in Hcontr. by inversion Hcontr. }
               assert (is_Some (m !! s)) as [Htemp _]%Hmcond;eauto.

               assert (W2.1 !! s = Some (Uninitialized x0)) as Hyy.
               { rewrite HW2 lookup_insert_ne.
                 2: clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
                 rewrite HW1 std_sta_update_multiple_lookup_same_i /=.
                 2: rewrite elem_of_elements not_elem_of_dom//.
                 rewrite HW' std_sta_update_multiple_lookup_same_i /=.
                 2: apply not_elem_of_region_addrs;
                   clear -n Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                 rewrite lookup_insert_ne. 2: clear -n Hsize;solve_addr.
                 apply uninitialize_std_sta_lookup_in;auto. }

               specialize (Hrel _ _ _ Hyy Hx).

               apply rtc_implies with (Q:=λ x y, Rpub x y) in Hrel.
               2: { intros r q. rewrite decide_False. auto.
                    clear -Hlt n Ha_param Ha_param2 Ha_param3 Ha_act_end. solve_addr. }
               eapply std_rel_pub_rtc_Uninitialized in Hrel as [-> | Heq];eauto.
               { assert (is_Some(m' !! s)) as Hcontr. apply Hmcond'. split;auto. clear;solve_addr.
                 rewrite Hsome in Hcontr. inversion Hcontr;done. } subst x.
               assert (m2 !! s = None).
               { apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hlt Hcontr;solve_addr. }
               specialize (Hrel2 s _ _ Hz5 Hz2).
               apply rtc_implies with (Q:=λ x y, Rpub x y) in Hrel2.
               2: { intros r q. rewrite decide_False. auto.
                    clear -Hlt n Ha_param Ha_param2 Ha_param3 Ha_act_final. solve_addr. }
               eapply std_rel_pub_rtc_Uninitialized in Hrel2 as [-> | Heq];eauto.
               { rewrite HWfinal (initialize_list_nuninit) in Hy;eauto.
                 rewrite override_uninitialize_std_sta_lookup_none// in Hy.
                 rewrite (uninitialize_std_sta_None_lookup) in Hy;auto.
                 rewrite Hz2 in Hy.
                 inversion Hy;subst y. eright;[|left].
                 destruct (decide (le_a bstk s));[left;constructor|constructor].
                 rewrite override_uninitialize_std_sta_lookup_none//.
                 rewrite (uninitialize_std_sta_None_lookup);auto. rewrite Hz2. eauto. }
               subst z2.
               rewrite HWfinal (initialize_list_in _ _ _ x0) in Hy;eauto.
               2: rewrite override_uninitialize_std_sta_lookup_none//.
               2: rewrite (uninitialize_std_sta_None_lookup);auto.
               inversion Hy;subst y.
               eright;[|left].
               destruct (decide (le_a bstk s));[left;constructor|constructor].
             }

             rewrite HWfinal initialize_list_nin// override_uninitialize_std_sta_lookup_none// in Hy.

             destruct (m2 !! s) eqn:Hsome2.
            *** specialize (Hrel2 s).
                trans z2.
                { eapply rtc_implies. 2: apply Hrel2. simpl.
                  intros r q Hrq. destruct (decide (a_act_final <= s)%a).
                  rewrite decide_True;auto.
                  clear -l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                  destruct (decide (bstk <= s)%a);auto. auto. auto. }
                assert (is_Some (m2 !! s)) as [Htemp Hle]%Hmcond2;eauto.
                rewrite Hz2 in Htemp. inversion Htemp. subst z2.
                rewrite (uninitialize_std_sta_lookup_in _ _ _ w)// in Hy. inversion Hy;subst y.
                eright;[|left]. rewrite decide_True. right;constructor. clear -Hle;solve_addr.
            *** rewrite uninitialize_std_sta_None_lookup// in Hy. rewrite Hz2 in Hy. inversion Hy;subst y.
                eapply rtc_implies;[|apply (Hrel2 s)].
                intros r q Hrq. destruct (decide (le_a a_act_final s)).
                rewrite decide_True;auto.
                clear -l Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hframe_end Hsize;solve_addr.
                destruct (decide (le_a bstk s));auto. auto. auto.

    - destruct HrelatedW5Wmid2 as [_ [Hdomsta2 [Hdomrel2 Hrel2] ] ].

      split;[|split].
      + rewrite HWfinal initialize_list_loc /override_uninitialize /=.
        etrans;[|apply Hdomsta2].
        rewrite HW5 HW4 /= std_update_multiple_loc HW3 /= std_update_multiple_loc /=.
        rewrite dom_insert_L. clear;set_solver.
      + rewrite HWfinal initialize_list_loc /override_uninitialize /=.
        etrans;[|apply Hdomrel2].
        rewrite HW5 HW4 /= std_update_multiple_loc HW3 /= std_update_multiple_loc /=.
        clear;set_solver.
      + intros j r1 r2 r1' r2' r3 r3' Hx Hy.
        assert (W5.2.2 !! j = Some (r1,r2,r3)) as Hx'.
        { rewrite HW5 HW4 HW3 /= !std_update_multiple_loc /= //. }
        destruct (decide (i = j)).
        * subst i.
          rewrite HW3 /= !std_update_multiple_loc /= in Hirel.
          rewrite HW3 /= !std_update_multiple_loc /= in Hi.
          rewrite Hirel in Hx. inversion Hx.
          (* subst r1 r2 r3. *)
          assert (is_Some (Wmid2.2.2 !! j)) as [? Hz].
          { apply elem_of_gmap_dom. apply Hdomrel2. apply elem_of_gmap_dom;eauto. }
          destruct x. destruct p.
          specialize (Hrel2 j _ _ _ _ _ _ Hx' Hz) as [-> [-> [-> Hrel2'] ] ].
          rewrite HWfinal initialize_list_loc /= in Hy.
          rewrite Hz in Hy. inversion Hy. subst P0 P1 P. inversion Hy. subst r1' r2' r3'.
          repeat split;auto.
          intros x y Hxx Hyy.
          destruct Hi as [b Hb]. rewrite Hb in Hxx. inversion Hxx. subst x.
          assert (W5.2.1 !! j = Some (encode true)) as Hj.
          { rewrite HW5 HW4 /= std_update_multiple_loc /=. apply lookup_insert. }
          assert (is_Some (Wmid2.2.1 !! j)) as [? Hj'].
          { apply elem_of_gmap_dom. apply Hdomsta2. apply elem_of_gmap_dom;eauto. }
          specialize (Hrel2' _ _ Hj Hj').
          apply rtc_implies with (Q:=λ x y : positive, convert_rel awk_rel_pub x y) in Hrel2'.
          2: { intros r q [Hrq|Hrq];auto. }
          apply rtc_rel_pub in Hrel2';auto. subst x.
          rewrite HWfinal initialize_list_loc /= in Hyy. rewrite Hj' in Hyy. inversion Hyy.
          destruct b. left.
          eright;[|left]. left. repeat eexists. constructor. done.
        * assert (is_Some (Wmid2.2.2 !! j)) as [? Hz].
          { apply elem_of_gmap_dom. apply Hdomrel2. apply elem_of_gmap_dom;eauto. }
          destruct x. destruct p.
          specialize (Hrel2 j _ _ _ _ _ _ Hx' Hz) as [-> [-> [-> Hrel2'] ] ].
          assert (is_Some (Wmid2.2.2 !! j)) as [? Hz'].
          { apply elem_of_gmap_dom. apply Hdomrel2. apply elem_of_gmap_dom;eauto. }
          destruct x. destruct p.
          rewrite HWfinal initialize_list_loc /= in Hy.
          rewrite Hz' in Hy. inversion Hy. rewrite Hz in Hz'. inversion Hz'. subst P3 P4 P2. subst P0 P1 P.
          repeat split;auto.
          intros x y Hxx Hyy.
          assert (W5.2.1 !! j = Some x) as Hj.
          { rewrite HW5 HW4 /= std_update_multiple_loc /=. rewrite lookup_insert_ne//.
            rewrite HW3 /= std_update_multiple_loc /=. auto. }
          assert (is_Some (Wmid2.2.1 !! j)) as [? Hj'].
          { apply elem_of_gmap_dom. apply Hdomsta2. apply elem_of_gmap_dom;eauto. }
          specialize (Hrel2' _ _ Hj Hj').
          rewrite HWfinal initialize_list_loc /= in Hyy. rewrite Hj' in Hyy. inversion Hyy. subst y.
          auto.
  Qed.

End awkward_helpers.
