From Stdlib Require Import Eqdep_dec List.
From stdpp Require Import countable list_relations.
From griotte Require Import sts world_std_sts.
From griotte Require Export stdpp_extra.

Section std_updates.

  (* --------------------------------------------------------------------------------- *)
  (* ----------------------- UPDATING MULTIPLE REGION STATES ------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Context {Σ:gFunctors}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    `{MP: MachineParameters}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Fixpoint std_update_multiple W l ρ :=
    match l with
    | [] => W
    | a :: l => std_update (std_update_multiple W l ρ) a ρ
    end.

   Lemma std_update_multiple_loc_sta W l ρ :
     loc (std_update_multiple W l ρ) = loc W.
   Proof.
     induction l; auto.
   Qed.

   Lemma std_update_multiple_loc_rel W l ρ :
     wrel (std_update_multiple W l ρ) = wrel W.
   Proof.
     induction l; auto.
   Qed.

   Lemma std_update_multiple_seals W l ρ :
     seal_std (std_update_multiple W l ρ) = seal_std W.
   Proof.
     induction l; auto.
   Qed.

   Lemma std_update_multiple_heap W l ρ :
     heap_std (std_update_multiple W l ρ) = heap_std W.
   Proof. induction l; simpl; auto. Qed.

   Lemma std_update_multiple_swap_head W l a1 a2 ρ :
     std_update_multiple W (a1 :: a2 :: l) ρ = std_update_multiple W (a2 :: a1 :: l) ρ.
   Proof.
     induction l.
     - simpl. destruct (decide (a1 = a2)); subst.
       + done.
       + rewrite /std_update.
         repeat rewrite (insert_insert_ne _ a1 a2); auto.
     - destruct (decide (a1 = a2)); subst;[done|].
       simpl. rewrite /std_update.
       repeat rewrite (insert_insert_ne _ a1 a2) ; auto.
   Qed.


   Lemma std_update_multiple_permutation W l1 l2 ρ :
     l1 ≡ₚ l2 →
     std_update_multiple W l1 ρ = std_update_multiple W l2 ρ.
   Proof.
     intros Hperm.
     induction Hperm using Permutation_ind.
     - done.
     - simpl. rewrite IHHperm. done.
     - apply (std_update_multiple_swap_head W l y x).
     - by rewrite IHHperm1 IHHperm2.
   Qed.

   Global Instance std_update_multiple_Permutation W ρ :
     Proper (Permutation ==> eq) (λ l, std_update_multiple W l ρ).
   Proof. intros y1 y2 Hperm. simpl. by apply std_update_multiple_permutation. Defined.

   (* --------------------------------------------------------------------------------------------------------- *)
   (* Lookup Lemmas: for each lookup lemma, we will have a version with addresses, and a version with positives *)
   (* --------------------------------------------------------------------------------------------------------- *)

   (* If an element is not in the update list, the state lookup is the same *)
   Lemma std_sta_update_multiple_lookup_same_i W l ρ i :
     i ∉ l -> (std (std_update_multiple W l ρ)) !! i =
             (std W) !! i.
   Proof.
     intros Hnin.
     induction l; auto.
     apply not_elem_of_cons in Hnin as [Hne Hnin].
     rewrite lookup_insert_ne; auto.
   Qed.

   (* ------------------------------------------------------------ *)

   (* If an element is in the update list, the state lookup corresponds to the update value *)
   Lemma std_sta_update_multiple_lookup_in_i W l ρ i :
     i ∈ l -> (std (std_update_multiple W l ρ)) !! i = Some ρ.
   Proof.
     intros Hnin.
     induction l; auto; first inversion Hnin.
     apply elem_of_cons in Hnin as [Hne | Hnin].
     - subst i. rewrite lookup_insert_eq; auto.
     - destruct (decide (a = i));[subst i; rewrite lookup_insert_eq; auto|].
       rewrite lookup_insert_ne;auto.
   Qed.

   (* ------------------------------------------------------------ *)

   (* domains *)
   Lemma std_update_multiple_not_in_sta_i W l ρ i :
     i ∉ l → i ∈ dom (std W) ↔
               i ∈ dom (std (std_update_multiple W l ρ)).
   Proof.
     intros Hnin. induction l; auto.
     apply not_elem_of_cons in Hnin as [Hneq Hnin].
     rewrite /= dom_insert. set_solver.
   Qed.

   Lemma std_update_multiple_not_in_sta W l ρ (a : Addr) :
     a ∉ l → a ∈ dom (std W) ↔
             a ∈ dom (std (std_update_multiple W l ρ)).
   Proof.
     intros Hnin.
     apply std_update_multiple_not_in_sta_i.
     intros Hcontr. contradiction.
   Qed.

   (* ---------------------------------------------------------------------------- *)
   (* Some helper lemmas for various lemmas about using multiple updates in region *)

   Lemma related_sts_pub_update_multiple W l ρ :
     Forall (λ a, a ∉ dom (std W)) l →
     related_sts_pub_world W (std_update_multiple W l ρ).
   Proof.
     intros Hforall. induction l.
     - apply related_sts_pub_refl_world.
     - simpl.
       apply Forall_cons in Hforall as [ Ha_std Hforall].
       eapply related_sts_pub_trans_world;[apply IHl; auto|].
       destruct (decide (a ∈ l)).
       { rewrite (_: <s[a:=ρ]s>(std_update_multiple W l ρ) = std_update_multiple W l ρ) /=.
         { by apply related_sts_pub_refl_world. }
         rewrite /std_update insert_id /=.
         { by destruct (std_update_multiple W l ρ) as [ [ [] ] ]. }
         by apply std_sta_update_multiple_lookup_in_i.
       }
       apply related_sts_pub_world_fresh; auto.
       intros Hcontr. apply std_update_multiple_not_in_sta in Hcontr; auto.
   Qed.

   (* Multiple updates does not change dom, as long as the updated elements are a subset of original dom *)

   (* In general, the domain is a subset of the updated domain *)


   Lemma std_update_multiple_std_sta_dom_monotone W W' l ρ :
     dom (std W) ⊆ dom (std W') ->
     dom (std (std_update_multiple W l ρ)) ⊆ dom (std (std_update_multiple W' l ρ)).
   Proof.
     induction l;auto.
     simpl. repeat rewrite dom_insert_L. set_solver.
   Qed.

   Lemma std_update_multiple_related_monotone W W' l ρ :
     related_sts_pub_world W W' ->
     related_sts_pub_world (std_update_multiple W l ρ) (std_update_multiple W' l ρ).
   Proof.
     intros Hrelated.
     destruct W as [ [ [Wstd_sta [Wloc_sta Wloc_rel] ] Wseals ] W_heap ].
     destruct W' as [ [ [ Wstd_sta' [Wloc_sta' Wloc_rel']  ] Wseals' ] W_heap' ].
     destruct Hrelated as ([Hstd_dom1 Hstd_related ] & Hcus_related & Wseals_related).
     simpl in *.
     split;[|split]
     ; [clear Hcus_related
       |by repeat rewrite std_update_multiple_loc_rel std_update_multiple_loc_sta
       |by repeat rewrite std_update_multiple_seals std_update_multiple_heap].
     split.
     - apply std_update_multiple_std_sta_dom_monotone. auto.
     - intros i x y Hx Hy.
       destruct (decide (i ∈ l)).
       + rewrite std_sta_update_multiple_lookup_in_i in Hx;auto.
         rewrite std_sta_update_multiple_lookup_in_i in Hy;auto.
         inversion Hx; inversion Hy; subst. left.
       + rewrite std_sta_update_multiple_lookup_same_i /= in Hx;auto.
         rewrite std_sta_update_multiple_lookup_same_i /= in Hy;auto.
         apply Hstd_related with i; auto.
   Qed.

   (* lemmas for updating a repetition of top *)

   Lemma std_update_multiple_insert_commute W a (l: list Addr) ρ ρ' :
     a ∉ l →
     std_update_multiple (<s[a:=ρ']s> W) l ρ = <s[a:=ρ']s> (std_update_multiple W l ρ).
   Proof.
     intros Hne.
     induction l; auto; simpl.
     apply not_elem_of_cons in Hne as [Hne Hnin].
     rewrite IHl;auto.
     rewrite /std_update /=. rewrite insert_insert_ne;auto.
   Qed.

   Lemma related_sts_pub_world_revoked_temporary W a :
     (std W) !! a = Some Revoked →
     related_sts_pub_world W (<s[a:=Temporary]s>W).
   Proof.
     intros Ha.
     rewrite /related_sts_pub_world /=.
     split;[|split];[|apply related_sts_pub_refl|split; [apply related_sts_seals_std_refl|apply related_sts_heap_std_refl]].
     rewrite /related_sts_pub. split.
     - rewrite dom_insert_L. set_solver.
     - intros i x y Hx Hy.
       destruct (decide (a = i)).
       + subst.
         rewrite Hx in Ha. inversion Ha.
         rewrite lookup_insert_eq in Hy. inversion Hy.
         right with (Temporary);[|left]. constructor.
       + rewrite lookup_insert_ne in Hy;auto.
         rewrite Hx in Hy.
         inversion Hy; subst.
         left.
   Qed.

   Lemma related_sts_pub_world_revoked_temporary' W a :
     (std W) !! a = None →
     related_sts_pub_world W (<s[a:=Temporary]s>W).
   Proof.
     intros Ha.
     rewrite /related_sts_pub_world /=.
     split;[|split];[|apply related_sts_pub_refl|split; [apply related_sts_seals_std_refl|apply related_sts_heap_std_refl]].
     rewrite /related_sts_pub. split.
     - rewrite dom_insert_L. set_solver.
     - intros i x y Hx Hy.
       destruct (decide (a = i)).
       + subst.
         rewrite Hx in Ha. inversion Ha.
       + rewrite lookup_insert_ne in Hy;auto.
         rewrite Hx in Hy.
         inversion Hy; subst.
         left.
   Qed.

   Lemma related_sts_pub_update_multiple_temp W l :
     Forall (λ k, std W !! k = Some Revoked) l →
     related_sts_pub_world W (std_update_multiple W l Temporary).
   Proof.
     intros Hforall. induction l.
     - apply related_sts_pub_refl_world.
     - simpl.
       apply Forall_cons in Hforall as [ Ha_std Hforall].
       eapply related_sts_pub_trans_world;[apply IHl; auto|].
       destruct (decide (a ∈ l)).
       { rewrite (_: <s[a:=Temporary]s>(std_update_multiple W l Temporary) = std_update_multiple W l Temporary) /=
         ; first by apply related_sts_pub_refl_world.
         rewrite /std_update insert_id /=; first  by destruct (std_update_multiple W l Temporary) as [ [ [] ] ].
         by apply std_sta_update_multiple_lookup_in_i.
       }
       destruct W as [ [Hstd Hloc] W_heap ].
       apply related_sts_pub_world_revoked_temporary in Ha_std.
       eapply related_sts_pub_trans_world;[apply std_update_multiple_related_monotone,Ha_std|].
       rewrite std_update_multiple_insert_commute //. apply related_sts_pub_refl_world.
   Qed.

   Lemma elem_of_dom_std_multiple_update (W : WORLD) (a : Addr) (l : list Addr)
     (ρ: region_type) :
     a ∈ (dom (std (std_update_multiple W l ρ))) ->
     a ∈ l \/ a ∈ (dom (std W)).
   Proof.
     induction l as [|a' l] ; intros Ha; first naive_solver.
     destruct (decide (a = a')) as [|Hna]; simplify_eq; first (left; set_solver).
     destruct (decide (a ∈ l)) as [|Hnl]; first (left; set_solver).
     right.
     rewrite /= dom_insert_L elem_of_union in Ha.
     destruct Ha as [Ha|Ha] ; first ( rewrite elem_of_singleton in Ha ; set_solver ).
     apply IHl in Ha. destruct Ha; done.
   Qed.

End std_updates.
