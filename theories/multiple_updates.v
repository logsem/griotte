From iris.proofmode Require Import tactics.
From cap_machine Require Export region_invariants_revocation.
From cap_machine Require Import logrel.
Require Import Eqdep_dec List.
From stdpp Require Import countable.

Section std_updates.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------------- UPDATING MULTIPLE REGION STATES ------------------------- *)

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
  Implicit Types C : CmptName.

  Fixpoint std_update_multiple_cview WC l ρ :=
    match l with
    | [] => WC
    | a :: l => std_update_cview (std_update_multiple_cview WC l ρ) a ρ
    end.

  Definition std_multiple_update W C l ρ :=
    match l with
    | [] => W
    | _ => (match W !! C with
           | Some WC => <[C := std_update_multiple_cview WC l ρ]> W
           | None => <[C := std_update_multiple_cview (∅,(∅,∅)) l ρ]> W
           end)
    end.

   Definition std_update_temp_multiple_cview WC l := std_update_multiple_cview WC l Temporary.
   Definition std_update_temp_multiple W C l := std_multiple_update W C l Temporary.

   Lemma std_update_multiple_cview_loc_sta WC l ρ :
     (std_update_multiple_cview WC l ρ).2.1 = WC.2.1.
   Proof.
     induction l; auto.
   Qed.

   Lemma std_update_multiple_cview_loc_rel WC l ρ :
     (std_update_multiple_cview WC l ρ).2.2 = WC.2.2.
   Proof.
     induction l; auto.
   Qed.

   Lemma std_update_multiple_cview_loc WC l ρ :
     (std_update_multiple_cview WC l ρ).2 = WC.2.
   Proof.
     induction l; auto.
   Qed.

   Lemma std_update_multiple_cview_proj_eq WC Wloc l ρ :
     ((std_update_multiple_cview WC l ρ).1, Wloc) = std_update_multiple_cview (WC.1,Wloc) l ρ.
   Proof.
     destruct WC as [Wsta Wloc']. simpl. induction l; auto.
     simpl. rewrite -IHl. auto.
   Qed.

   Lemma std_update_multiple_cview_std_sta_eq WC Wloc l ρ :
     (std_update_multiple_cview WC l ρ).1 = (std_update_multiple_cview (WC.1, Wloc) l ρ).1.
   Proof.
     destruct WC as [Wsta Wloc']. simpl. induction l; auto.
     simpl. rewrite -IHl. auto.
   Qed.

   Lemma std_update_multiple_cview_swap_head WC l a1 a2 ρ :
     std_update_multiple_cview WC (a1 :: a2 :: l) ρ = std_update_multiple_cview WC (a2 :: a1 :: l) ρ.
   Proof.
     induction l.
     - simpl. destruct (decide (a1 = a2)); subst.
       + done.
       + rewrite /std_update_cview.
         repeat rewrite (insert_commute _ a1 a2); auto.
     - destruct (decide (a1 = a2)); subst;[done|].
       simpl. rewrite /std_update_cview.
       repeat rewrite (insert_commute _ a1 a2) ; auto.
   Qed.

   Lemma std_update_multiple_cview_swap WC l1 a l2 ρ :
     std_update_multiple_cview WC (l1 ++ a :: l2) ρ = std_update_multiple_cview WC (a :: l1 ++ l2) ρ.
   Proof.
     induction l1; auto.
     rewrite app_comm_cons std_update_multiple_cview_swap_head /=.
     f_equal;auto.
   Qed.


   Lemma std_update_multiple_cview_permutation WC l1 l2 ρ :
     l1 ≡ₚ l2 →
     std_update_multiple_cview WC l1 ρ = std_update_multiple_cview WC l2 ρ.
   Proof.
     intros Hperm.
     induction Hperm using Permutation_ind.
     - done.
     - simpl. rewrite IHHperm. done.
     - apply (std_update_multiple_cview_swap_head WC l y x).
     - by rewrite IHHperm1 IHHperm2.
   Qed.

   Lemma std_update_multiple_cview_permutation_C W C l1 l2 ρ :
     l1 ≡ₚ l2 →
     std_multiple_update W C l1 ρ = std_multiple_update W C l2 ρ.
   Proof.
     intros Hperm.
     induction Hperm using Permutation_ind.
     - done.
     - rewrite /std_multiple_update.
       destruct (W!!C); erewrite std_update_multiple_cview_permutation; eauto.
     - rewrite /std_multiple_update.
       destruct (W!!C); erewrite std_update_multiple_cview_permutation; eauto
       ; apply Permutation_swap.
     - by rewrite IHHperm1 -IHHperm2.
   Qed.

   Global Instance std_update_multiple_cview_Permutation WC ρ :
     Proper (Permutation ==> eq) (λ l, std_update_multiple_cview WC l ρ).
   Proof. intros y1 y2 Hperm. simpl. by apply std_update_multiple_cview_permutation. Defined.

   Global Instance std_update_multiple_cview_Permutation_C W C ρ :
     Proper (Permutation ==> eq) (λ l, std_multiple_update W C l ρ).
   Proof. intros y1 y2 Hperm. by apply std_update_multiple_cview_permutation_C. Defined.

   Lemma remove_dups_swap_head {A : Type} `{EqDecision A} (a1 a2 : A) (l : list A) :
     remove_dups (a1 :: a2 :: l) ≡ₚ remove_dups (a2 :: a1 :: l).
   Proof.
     destruct (decide (a1 = a2)); subst; auto.
     simpl. destruct (decide_rel elem_of a1 (a2 :: l)), (decide_rel elem_of a2 (a1 :: l)).
     - apply elem_of_cons in e as [Hcontr | Hl];[subst;contradiction|].
       apply elem_of_cons in e0 as [Hcontr | Hl0];[subst;contradiction|].
       destruct (decide_rel elem_of a2 l);[|contradiction].
       destruct (decide_rel elem_of a1 l);[|contradiction].
       done.
     - apply elem_of_cons in e as [Hcontr | Hl];[subst;contradiction|].
       apply not_elem_of_cons in n0 as [Hcontr Hl0].
       destruct (decide_rel elem_of a2 l);[contradiction|].
       destruct (decide_rel elem_of a1 l);[|contradiction].
       done.
     - apply elem_of_cons in e as [Hcontr | Hl];[subst;contradiction|].
       apply not_elem_of_cons in n0 as [Hcontr Hl0].
       destruct (decide_rel elem_of a2 l);[|contradiction].
       destruct (decide_rel elem_of a1 l);[contradiction|].
       done.
     - apply not_elem_of_cons in n1 as [Hcontr Hl].
       apply not_elem_of_cons in n0 as [Hcontr0 Hl0].
       destruct (decide_rel elem_of a2 l); [contradiction|].
       destruct (decide_rel elem_of a1 l);[contradiction|].
       rewrite (Permutation_swap a1 a2 (remove_dups l)). done.
   Qed.

   Lemma remove_dups_swap {A : Type} `{EqDecision A} (l1 : list A) (a : A) (l2 : list A) :
     remove_dups (l1 ++ a :: l2) ≡ₚ remove_dups (a :: l1 ++ l2).
   Proof.
     induction l1; auto.
     rewrite app_comm_cons remove_dups_swap_head (app_comm_cons l1 l2 a) /=.
     destruct (decide_rel elem_of a0 (l1 ++ a :: l2)).
     - rewrite decide_True;[|by rewrite Permutation_middle].
       destruct (decide_rel elem_of a (l1 ++ l2)).
       + rewrite IHl1. simpl. rewrite decide_True; auto.
       + rewrite IHl1. simpl. rewrite decide_False; auto.
     - rewrite decide_False;[|by rewrite Permutation_middle]. f_equiv.
       destruct (decide_rel elem_of a (l1 ++ l2)).
       + rewrite IHl1. simpl. rewrite decide_True; auto.
       + rewrite IHl1. simpl. rewrite decide_False; auto.
   Qed.

   (* --------------------------------------------------------------------------------------------------------- *)
   (* Lookup Lemmas: for each lookup lemma, we will have a version with addresses, and a version with positives *)
   (* --------------------------------------------------------------------------------------------------------- *)

   (* If an element is not in the update list, the state lookup is the same *)
   Lemma std_sta_update_multiple_lookup_same_i WC l ρ i :
     i ∉ l -> (std_cview (std_update_multiple_cview WC l ρ)) !! i =
             (std_cview WC) !! i.
   Proof.
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hne Hnin].
     rewrite lookup_insert_ne; auto.
   Qed.

   (* ------------------------------------------------------------ *)

   (* If an element is in the update list, the state lookup corresponds to the update value *)
   Lemma std_sta_update_multiple_lookup_in_i WC l ρ i :
     i ∈ l -> (std_cview (std_update_multiple_cview WC l ρ)) !! i = Some ρ.
   Proof.
     intros Hnin.
     induction l; auto; first inversion Hnin.
     apply elem_of_cons in Hnin as [Hne | Hnin].
     - subst i. rewrite lookup_insert; auto.
     - destruct (decide (a = i));[subst i; rewrite lookup_insert; auto|].
       rewrite lookup_insert_ne;auto.
   Qed.

   (* ------------------------------------------------------------ *)

   (* if W at a is_Some, the the updated W at a is_Some *)
   Lemma std_sta_update_multiple_is_Some WC l ρ i :
     is_Some (std_cview WC !! i) -> is_Some (std_cview (std_update_multiple_cview WC l ρ) !! i).
   Proof.
     intros Hsome.
     destruct (decide (i ∈ l)).
     - exists ρ. by apply std_sta_update_multiple_lookup_in_i.
     - rewrite std_sta_update_multiple_lookup_same_i;auto.
   Qed.

   (* ------------------------------------------------------------ *)

   (* domains *)
   Lemma std_update_multiple_cview_not_in_sta_i WC l ρ i :
     i ∉ l → i ∈ dom (std_cview WC) ↔
               i ∈ dom (std_cview (std_update_multiple_cview WC l ρ)).
   Proof.
     intros Hnin. induction l; auto.
     apply not_elem_of_cons in Hnin as [Hneq Hnin].
     rewrite /= dom_insert. set_solver.
   Qed.
   Lemma std_update_multiple_cview_in_sta_i WC (l: list Addr) ρ i :
     Forall (λ (a:Addr), is_Some (std_cview WC !! a)) l →
     i ∈ dom (std_cview WC) ↔ i ∈ dom (std_cview (std_update_multiple_cview WC l ρ)).
   Proof.
     intros Hl.
     induction l; auto.
     apply Forall_cons_1 in Hl as [Ha Hll].
     cbn. rewrite dom_insert. split; [ set_solver |].
     rewrite elem_of_union elem_of_singleton. intros [-> | Hi]; [| set_solver].
     rewrite elem_of_dom //.
   Qed.
   Lemma std_update_multiple_cview_not_in_sta WC l ρ (a : Addr) :
     a ∉ l → a ∈ dom (std_cview WC) ↔
             a ∈ dom (std_cview (std_update_multiple_cview WC l ρ)).
   Proof.
     intros Hnin.
     apply std_update_multiple_cview_not_in_sta_i.
     intros Hcontr. contradiction.
   Qed.

   (* ---------------------------------------------------------------------------- *)
   (* Some helper lemmas for various lemmas about using multiple updates in region *)

   Lemma related_sts_pub_update_multiple_cview WC l ρ :
     Forall (λ a, a ∉ dom (std_cview WC)) l →
     related_sts_pub_cview WC (std_update_multiple_cview WC l ρ).
   Proof.
     intros Hforall. induction l.
     - apply related_sts_pub_refl_cview.
     - simpl.
       apply list.Forall_cons in Hforall as [ Ha_std Hforall].
       eapply related_sts_pub_trans_cview;[apply IHl; auto|].
       destruct (decide (a ∈ l)).
       { rewrite (_: <s[a:=ρ]s>(std_update_multiple_cview WC l ρ) = std_update_multiple_cview WC l ρ) /=.
         by apply related_sts_pub_refl_cview.
         rewrite /std_update_cview insert_id /=. by destruct (std_update_multiple_cview WC l ρ).
         by apply std_sta_update_multiple_lookup_in_i. }
       apply related_sts_pub_cview_fresh; auto.
       intros Hcontr. apply std_update_multiple_cview_not_in_sta in Hcontr; auto.
   Qed.

   Lemma related_sts_pub_update_multiple W C l ρ :
     Forall (λ a, a ∉ dom (std W C)) l →
     related_sts_pub_world W (std_multiple_update W C l ρ) C.
   Proof.
     intros Hforall.
     rewrite /std in Hforall.
     rewrite /std_multiple_update.
     destruct l as [|a l]; first apply related_sts_pub_refl_world.
     destruct (W!!C) as [WC|] eqn:HWC.
     - split.
       + rewrite dom_insert_L ; set_solver.
       + intros ? WC' ? HWC' ; rewrite lookup_insert in HWC' ; simplify_eq.
         by apply related_sts_pub_update_multiple_cview.
     - split.
       + rewrite dom_insert_L ; set_solver.
       + intros ? WC' ? HWC' ; rewrite lookup_insert in HWC' ; simplify_eq.
   Qed.

   Lemma std_update_multiple_cview_lookup_cview WC l ρ k y :
     l !! k = Some y ->
     std_cview (std_update_multiple_cview WC l ρ) !! y = Some ρ.
   Proof.
     intros Helem.
     apply elem_of_list_lookup_2 in Helem.
     apply elem_of_list_split in Helem as [l1 [l2 Heq] ].
     rewrite Heq std_update_multiple_cview_swap /= /std_update_cview.
     rewrite /std_cview /=. rewrite lookup_insert. auto.
   Qed.

   Lemma std_update_multiple_cview_lookup W C l ρ k y :
     l !! k = Some y ->
     is_Some (W!!C) ->
     std (std_multiple_update W C l ρ) C !! y = Some ρ.
   Proof.
     intros Helem [WC HWC].
     rewrite /std /std_multiple_update HWC.
     destruct l ; first done.
     rewrite lookup_insert. eapply std_update_multiple_cview_lookup_cview; eauto.
   Qed.

   Lemma std_update_temp_multiple_lookup W C l k y :
     l !! k = Some y →
     is_Some (W!!C) ->
     region_state_pwl (std_update_temp_multiple W C l) C y.
   Proof.
     intros Helem HWC.
     rewrite /std_update_temp_multiple.
     eapply std_update_multiple_cview_lookup; eauto.
   Qed.


   (* Multiple updates does not change dom, as long as the updated elements are a subset of original dom *)
   Lemma std_update_multiple_cview_dom_equal WC l ρ :
     (∀ i : Addr, i ∈ l → i ∈ dom (std_cview WC)) ->
     dom (std_cview WC) = dom (std_cview (std_update_multiple_cview WC l ρ)).
   Proof.
     intros Hsub.
     induction l; auto.
     rewrite /= /std_update_cview.
     rewrite dom_insert_L.
     assert (a ∈ a :: l) as Hin.
     { apply elem_of_cons. by left. }
     pose proof (Hsub _ Hin) as Hain. etrans;[apply IHl|].
     - intros i Hi. apply Hsub. apply elem_of_cons. by right.
     - set_solver.
   Qed.

   (* In general, the domain is a subset of the updated domain *)
   Lemma std_update_multiple_cview_sta_dom_subseteq WC l ρ :
     dom (std_cview WC) ⊆ dom (std_cview (std_update_multiple_cview WC l ρ)).
   Proof.
     apply elem_of_subseteq. intros x Hx.
     destruct (decide (x ∈ l)).
     - rewrite elem_of_dom. exists ρ.
       apply std_sta_update_multiple_lookup_in_i; auto.
     - apply std_update_multiple_cview_not_in_sta_i; auto.
   Qed.

   Lemma std_update_multiple_cview_std_sta_dom_monotone_cview WC WC' l ρ :
     dom (std_cview WC) ⊆ dom (std_cview WC') ->
     dom (std_cview (std_update_multiple_cview WC l ρ)) ⊆ dom (std_cview (std_update_multiple_cview WC' l ρ)).
   Proof.
     induction l;auto.
     simpl. repeat rewrite dom_insert_L. set_solver.
   Qed.

   Lemma std_update_multiple_cview_std_sta_dom_monotone W W' C l ρ :
     dom W ⊆ dom W' ->
     dom (std W C) ⊆ dom (std W' C) ->
     dom (std (std_multiple_update W C l ρ) C) ⊆ dom (std (std_multiple_update W' C l ρ) C).
   Proof.
     rewrite /std /std_multiple_update.
     intros Hdom_W Hdom.
     destruct l ; first done.
     destruct (W !! C) as [WC|] eqn:HWC.
     - rewrite lookup_insert.
       assert (is_Some (W' !! C)) as [WC' HWC'].
       {
         apply (elem_of_dom_2 W) in HWC.
         specialize (Hdom_W _ HWC).
         by eapply (elem_of_dom W').
       }
       rewrite HWC' lookup_insert.
       rewrite HWC' in Hdom.
       by eapply std_update_multiple_cview_std_sta_dom_monotone_cview.
     - rewrite lookup_insert.
       destruct (W'!!C) as [WC'|] eqn:HWC'; rewrite lookup_insert; auto.
       by eapply std_update_multiple_cview_std_sta_dom_monotone_cview.
   Qed.

   Lemma std_update_multiple_related_monotone_cview WC WC' l ρ :
     related_sts_pub_cview WC WC' ->
     related_sts_pub_cview (std_update_multiple_cview WC l ρ) (std_update_multiple_cview WC' l ρ).
   Proof.
     intros Hrelated.
     destruct WC as [ Wstd_sta [Wloc_sta Wloc_rel] ].
     destruct WC' as [ Wstd_sta' [Wloc_sta' Wloc_rel'] ].
     destruct Hrelated as [ [Hstd_dom1 Hstd_related ] Hloc_related].
     simpl in *.
     split;[clear Hloc_related|by repeat rewrite std_update_multiple_cview_loc_rel std_update_multiple_cview_loc_sta].
     split.
     - apply std_update_multiple_cview_std_sta_dom_monotone_cview. auto.
     - intros i x y Hx Hy.
       destruct (decide (i ∈ l)).
       + rewrite std_sta_update_multiple_lookup_in_i in Hx;auto.
         rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
         inversion Hx; inversion Hy; subst. left.
       + rewrite std_sta_update_multiple_lookup_same_i /std_cview /= in Hx;auto.
         rewrite std_sta_update_multiple_lookup_same_i /std_cview /= in Hy;auto.
         apply Hstd_related with i; auto.
   Qed.

   Lemma std_update_multiple_dom_monotone W W' C l ρ :
     dom W ⊆ dom W' ->
     dom (std_multiple_update W C l ρ) ⊆ dom (std_multiple_update W' C l ρ).
    Proof.
      intros Hdom.
      rewrite /std_multiple_update.
      destruct l ; first done.
      destruct (W !! C) as [WC|] eqn:HWC; eauto.
      - destruct (W' !! C) as [WC'|] eqn:HWC'; eauto.
        + rewrite !dom_insert_L; set_solver.
        + eapply (elem_of_dom_2 W) in HWC.
          specialize (Hdom _ HWC).
          by eapply (not_elem_of_dom W') in HWC'.
      - destruct (W' !! C) as [WC'|] eqn:HWC'; eauto.
        + rewrite !dom_insert_L; set_solver.
        + rewrite !dom_insert_L; set_solver.
    Qed.

   Lemma std_update_multiple_related_monotone W W' C l ρ :
     related_sts_pub_world W W' C ->
     related_sts_pub_world (std_multiple_update W C l ρ) (std_multiple_update W' C l ρ) C.
   Proof.
     intros [Hdom Hrelated].
     split.
     - by apply std_update_multiple_dom_monotone.
     - rewrite /std_multiple_update.
       destruct l ; first done.
       intros WC_upd WC_upd' HWC_upd HWC_upd'.
       destruct (W!!C) as [WC|] eqn:HWC.
       + destruct (W'!!C) as [WC'|] eqn:HWC' ; cycle 1.
         { eapply (elem_of_dom_2 W) in HWC.
           specialize (Hdom _ HWC).
           by eapply (not_elem_of_dom W') in HWC'.
         }
         rewrite lookup_insert in HWC_upd; rewrite lookup_insert in HWC_upd'; simplify_eq.
         apply std_update_multiple_related_monotone_cview.
         by apply Hrelated.
       + destruct (W'!!C) as [WC'|] eqn:HWC'; simplify_eq.
         all: rewrite lookup_insert in HWC_upd.
         all: rewrite lookup_insert in HWC_upd'.
         all: simplify_eq.
         * apply std_update_multiple_related_monotone_cview.
           apply related_sts_pub_empty_cview.
         * by apply std_update_multiple_related_monotone_cview.
   Qed.

   (* lemmas for updating a repetition of top *)
   Lemma std_update_multiple_cview_dom_top_sta WC n ρ a :
     a ≠ addr_reg.top ->
     a ∉ dom (std_cview WC) →
     a ∉ dom (std_cview (std_update_multiple_cview WC (repeat addr_reg.top n) ρ)).
   Proof.
     intros Hne Hnin.
     induction n; auto.
     simpl. rewrite dom_insert. apply not_elem_of_union.
     split.
     + apply not_elem_of_singleton.
       intros Hcontr. done.
     + apply IHn.
   Qed.

   Lemma std_update_multiple_cview_dom_sta_i WC n ρ a i :
     a ≠ addr_reg.top → (i > 0)%Z →
     a ∉ dom (std_cview WC) →
     a ∉ dom (std_cview (std_update_multiple_cview WC (finz.seq ((a ^+ i)%a) n) ρ)).
   Proof.
     intros Hneq Hgt.
     destruct (a + i)%a eqn:Hsome.
     - simpl.
       assert (a < f)%a as Hlt;[apply next_lt_i with i; auto|].
       intros Hnin.
       revert Hlt Hsome. generalize i f. induction n; auto; intros j a1 Hlt Hsome.
       simpl. rewrite dom_insert. apply not_elem_of_union.
       split.
       + apply not_elem_of_singleton.
         intros Hcontr. subst. solve_addr.
       + destruct (a1 + 1)%a eqn:Ha2
         ; simpl
         ; replace ((a ^+ j) ^+ 1)%a with (a ^+ (j+1))%a by solve_addr.
         ++ apply (IHn (j+1)%Z f0); solve_addr.
         ++ replace ((a ^+ j) ^+ 1)%a with (a ^+ (j+1))%a by solve_addr.
            apply incr_addr_one_none in Ha2.
            replace (a ^+ (j + 1))%a with (finz.largest 0%a) by solve_addr.
            rewrite finz_seq_top. apply std_update_multiple_cview_dom_top_sta; auto.
     - replace (a ^+ i)%a with (finz.largest 0%a) by solve_addr.
       rewrite finz_seq_top. apply std_update_multiple_cview_dom_top_sta; auto.
   Qed.

   Lemma incr_addr_is_Some_weak a n :
     is_Some (a + S (S n))%a → is_Some (a + (S n))%a.
   Proof.
     intros Hsome.
     solve_addr.
   Qed.

   Lemma std_sta_update_multiple_insert WC (a b a' l : Addr) ρ i :
     (a' < a)%a →
     std_cview (std_update_multiple_cview (std_update_cview WC a' i) (finz.seq_between a b) ρ) !! l =
     std_cview (std_update_cview (std_update_multiple_cview WC (finz.seq_between a b) ρ) a' i) !! l.
   Proof.
     intros Hlt.
     destruct (decide (l ∈ finz.seq_between a b)) as [Hin|Hin].
     - assert (l ≠ a') as Hne.
       { intros ->.
         apply elem_of_finz_seq_between in Hin.
         solve_addr.
       }
       apply elem_of_list_lookup in Hin as [n Hsome].
       assert (std_cview (std_update_multiple_cview WC (finz.seq_between a b) ρ) !! l = Some ρ) as Hpwl.
       { apply std_update_multiple_cview_lookup_cview with n; auto. }
       assert (std_cview (std_update_multiple_cview (std_update_cview WC a' i) (finz.seq_between a b) ρ) !! l = Some ρ) as Hpwl'.
       { apply std_update_multiple_cview_lookup_cview with n; auto. }
       rewrite -Hpwl in Hpwl'. rewrite Hpwl'.
       rewrite lookup_insert_ne; auto.
     - rewrite std_sta_update_multiple_lookup_same_i; auto.
       destruct (decide ( a' =  l)).
       + rewrite /std_update_cview /std_cview /= e. do 2 rewrite lookup_insert. done.
       + rewrite /std_update_cview /std_cview /=. rewrite lookup_insert_ne;auto. rewrite lookup_insert_ne; auto.
         rewrite std_sta_update_multiple_lookup_same_i; auto.
   Qed.

   Lemma std_update_multiple_cview_dom_insert WC (a b a' : Addr) i :
     (a' < a)%a →
     Forall (λ a : Addr,
                   (a ∉ dom (std_cview WC))) (finz.seq_between a b) →
     Forall (λ a : Addr,
                   (a ∉ dom (<[ a' := i]> WC.1))) (finz.seq_between a b).
   Proof.
     intros Hlt.
     do 2 (rewrite list.Forall_forall). intros Hforall.
     intros x Hin.
     assert (x ≠ a') as Hne.
     { intros ->.
       apply elem_of_finz_seq_between in Hin.
       solve_addr.
       }
     apply Hforall with x in Hin.
     rewrite dom_insert. apply not_elem_of_union.
     split;auto. apply not_elem_of_singleton.
     intros Hcontr. contradiction.
   Qed.

   (* commuting updates and revoke *)

   Lemma std_update_multiple_cview_revoke_commute_cview WC (l: list Addr) ρ :
     ρ ≠ Temporary → ρ ≠ Temporary →
     std_update_multiple_cview (revoke_cview WC) l ρ = revoke_cview (std_update_multiple_cview WC l ρ).
   Proof.
     intros Hne Hne'.
     induction l; auto; simpl.
     rewrite IHl.
     rewrite /std_update_cview /revoke_cview /loc /std_cview /=. repeat f_equiv.
     eapply (map_leibniz (M:=gmap Addr) (A:=region_type)). intros i. eapply leibniz_equiv_iff.
     destruct (decide (a = i)).
     - subst. rewrite lookup_insert revoke_monotone_lookup_same;rewrite lookup_insert; auto.
       all: intros Hcontr; inversion Hcontr as [Hcontr']. all:done.
     - rewrite lookup_insert_ne;auto.
       apply revoke_monotone_lookup. rewrite lookup_insert_ne;auto. Unshelve.
       apply _.
       apply option_leibniz.
   Qed.

   Lemma std_update_multiple_cview_revoke_commute W C (l: list Addr) ρ :
     ρ ≠ Temporary → ρ ≠ Temporary →
     std_multiple_update (revoke W C) C l ρ = revoke (std_multiple_update W C l ρ) C.
   Proof.
     intros Hne Hne'.
     rewrite /std_multiple_update /revoke.
     destruct l ; first done.
     destruct (W!!C) as [WC|] eqn:HWC; [|rewrite HWC]
     ; rewrite !lookup_insert !insert_insert.
     - by rewrite std_update_multiple_cview_revoke_commute_cview.
     - rewrite -std_update_multiple_cview_revoke_commute_cview;auto.
   Qed.
   (* std_update_multiple_cview and app *)

   Lemma std_update_multiple_cview_app WC (l1 l2 : list Addr) ρ :
     std_update_multiple_cview WC (l1 ++ l2) ρ = std_update_multiple_cview (std_update_multiple_cview WC l1 ρ) l2 ρ.
   Proof.
     induction l2; auto.
     - by rewrite app_nil_r /=.
     - rewrite std_update_multiple_cview_swap /=. f_equal. auto.
   Qed.

   Lemma std_update_multiple_cview_app_commute WC (l1 l2 : list Addr) ρ :
     std_update_multiple_cview WC (l1 ++ l2) ρ = std_update_multiple_cview WC (l2 ++ l1) ρ.
   Proof.
     induction l2.
     - by rewrite app_nil_r /=.
     - rewrite std_update_multiple_cview_swap /=. by rewrite IHl2.
   Qed.

   Lemma revoke_condition_std_multiple_updates W C l ρ :
     revoke_condition W C
     → ρ ≠ Temporary
     → revoke_condition (std_multiple_update W C l ρ) C.
   Proof.
     induction l as [|a l IHl].
     - intros Hrev Hne.
       rewrite /std_multiple_update; done.
     - simpl. intros Hrev Hne a'.
       destruct (W!!C) as [WC|] eqn:HWC; cycle 1.
       { destruct (decide (a = a')); simplify_map_eq.
         + rewrite /std lookup_insert.
           rewrite lookup_insert. congruence.
         + apply IHl in Hrev; auto.
           rewrite /revoke_condition in Hrev.
           (* rewrite /std /std_multiple_update HWC in Hrev. *)
           rewrite /std lookup_insert.
           rewrite lookup_insert_ne; auto.
           specialize (Hrev a').
           destruct l; first done.
           by rewrite /std /std_multiple_update HWC lookup_insert in Hrev.
       }
       rewrite /std lookup_insert.
       destruct (decide (a = a')).
       + simpl. destruct WC as [Wstd Wloc].
         rewrite (std_update_multiple_cview_std_sta_eq _ Wloc). subst. rewrite lookup_insert.
         congruence.
       + simpl. destruct WC as [Wstd Wloc].
         rewrite (std_update_multiple_cview_std_sta_eq _ Wloc). rewrite lookup_insert_ne//.
         apply IHl in Hrev;auto.
         cbn.
         rewrite /revoke_condition in Hrev.
         destruct l.
         * rewrite /std /std_multiple_update HWC in Hrev.
           done.
         * rewrite /std /std_multiple_update HWC lookup_insert in Hrev.
           done.
   Qed.

   Lemma std_update_multiple_cview_overlap WC l ρ1 ρ2 :
     std_update_multiple_cview (std_update_multiple_cview WC l ρ1) l ρ2 = std_update_multiple_cview WC l ρ2.
   Proof.
     induction l;auto.
     simpl. destruct WC as [Wstd Wloc]. rewrite /std_update_cview /=. rewrite !std_update_multiple_cview_loc /=. f_equiv.
     apply map_eq'. intros k v.
     destruct (decide (a = k)).
     + subst. rewrite !lookup_insert. auto.
     + rewrite !lookup_insert_ne//. destruct (decide (k ∈ l)).
       * rewrite !std_sta_update_multiple_lookup_in_i//.
       * rewrite !std_sta_update_multiple_lookup_same_i// /=.
         rewrite lookup_insert_ne//. rewrite !std_sta_update_multiple_lookup_same_i// /=.
   Qed.

   Lemma std_update_multiple_cview_insert_commute WC a (l: list Addr) ρ ρ' :
     a ∉ l →
     std_update_multiple_cview (<s[a:=ρ']s> WC) l ρ = <s[a:=ρ']s> (std_update_multiple_cview WC l ρ).
   Proof.
     intros Hne.
     induction l; auto; simpl.
     apply not_elem_of_cons in Hne as [Hne Hnin].
     rewrite IHl;auto.
     rewrite /std_update_cview /revoke_cview /loc /std_cview /=. rewrite insert_commute;auto.
   Qed.

   Lemma related_sts_pub_update_multiple_perm_cview WC l :
     Forall (λ k, std_cview WC !! k = Some Revoked) l →
     related_sts_pub_cview WC (std_update_multiple_cview WC l Permanent).
   Proof.
     intros Hforall. induction l.
     - apply related_sts_pub_refl_cview.
     - simpl.
       apply list.Forall_cons in Hforall as [ Ha_std Hforall].
       eapply related_sts_pub_trans_cview;[apply IHl; auto|].
       destruct (decide (a ∈ l)).
       { rewrite (_: <s[a:=Permanent]s>(std_update_multiple_cview WC l Permanent) = std_update_multiple_cview WC l Permanent) /=.
         by apply related_sts_pub_refl_cview.
         rewrite /std_update_cview insert_id /=. by destruct (std_update_multiple_cview WC l Permanent).
         by apply std_sta_update_multiple_lookup_in_i. }
       destruct WC as [Hstd_cview Hloc].
       apply related_sts_pub_world_revoked_permanent_cview in Ha_std.
       eapply related_sts_pub_trans_cview;[apply std_update_multiple_related_monotone_cview,Ha_std|].
       rewrite std_update_multiple_cview_insert_commute //. apply related_sts_pub_refl_cview.
   Qed.

   Lemma related_sts_pub_update_multiple_perm W C l :
     Forall (λ k, std W C !! k = Some Revoked) l →
     related_sts_pub_world W (std_multiple_update W C l Permanent) C.
   Proof.
     intros Hforall.
     destruct l; first apply related_sts_pub_refl_world.
     split.
     - rewrite /std_multiple_update.
       destruct (W!!C) ; rewrite dom_insert_L; set_solver.
     - intros WC WC' HWC HWC'.
       rewrite /std_multiple_update HWC lookup_insert in HWC'; simplify_eq.
       rewrite /std HWC in Hforall.
       by apply related_sts_pub_update_multiple_perm_cview.
   Qed.

  Lemma elem_of_dom_std_multiple_update (W : WORLD) (A : CmptName) (a : Addr) (l : list Addr)
    (ρ: region_type) :
    is_Some (W !! A) ->
    a ∈ (dom (std (std_multiple_update W A l ρ) A)) ->
    a ∈ l \/ a ∈ (dom (std W A)).
  Proof.
    intros [WA HWA].
    induction l as [|a' l] ; intros Ha; first naive_solver.
    destruct (decide (a = a')) as [|Hna]; simplify_eq; first (left; set_solver).
    destruct (decide (a ∈ l)) as [|Hnl]; first (left; set_solver).
    right.
    rewrite /= HWA /std lookup_insert /std_cview dom_insert_L elem_of_union in Ha.
    destruct Ha as [Ha|Ha] ; first ( rewrite elem_of_singleton in Ha ; set_solver ).
    assert (a ∈ dom (std (std_multiple_update W A l ρ) A)).
    { rewrite /std /std_multiple_update.
      destruct l; first (rewrite HWA; done).
      rewrite HWA lookup_insert /std_cview; done.
    }
    apply IHl in H. destruct H; done.
  Qed.

End std_updates.
