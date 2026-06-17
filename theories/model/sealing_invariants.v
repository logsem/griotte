From iris.algebra Require Import gmap agree auth excl csum excl_auth.
From iris.proofmode Require Import proofmode.
From griotte Require Export stdpp_extra rules_base.
From griotte Require Export sts world_std_sts world_ghost_resources.

Section sealing_interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  (* NOTE It seems that may rules are broken with this kind of normalisation.
     I believe that it makes sense, because now we end up in a situation where
     [normalise_sealed_words_mono] does not hold anymore!

     Indeed, the situation where:
     Hs: s ⊆ s'
     Hbs: (borrow w) ∈ s
     Hbs': (borrow w) ∈ s'
     Hgs: (force_global w) ∉ s
     Hgs': (force_global w) ∈ s'

     means that:
     - Hbs and Hgs → (borrow w) ∈ (normalise_sealed_words s)
     - Hbs' and Hgs' → (borrow w) ∉ (normalise_sealed_words s)

     In other words, by adding (force_global w) in a set,
     we are actually removing (borrow w) from (normalise_sealed_words s)!

     And I think it breaks some of the rule of our sealing_map interface,
     which are not right away obvious for me how to fix / which rules we want exactly.
     In particular, [sealing_map_seal_pred] which says that if we have the seal_points-to,
     (o ↦ₛ ws), then we can extract (Po w) for all (normalise_sealed_words ws)...
     Because we have (ws ⊆ ws') where ws' the real set of words in the world,
     which means that maybe ws contains (borrow w), but not (force_global w)
     (which we would then expect to get (Po (borrow w)))
     but maybe ws' contains (force_global w),
     which means that we don't have (Po (borrow w)) but (Po (force_global w))!
   *)

  (* TODO Use an actual normalisation function, which only keeps the highest authority! *)
  (* The normalisation function ensures that there's no duplicates in the set,
     modulo the locality. *)
  Definition normalise_sealed_words_aux (s : list Word) : list Word :=
    foldr
      (fun w acc =>
         if (isGlobalWord w)
         then
           w::(filter (fun w' => (w' ≠ (borrow w))) acc)
         else
           match find (fun w' => bool_decide (w' = (force_global w))) acc with
           | None => w::acc
           | Some w' => acc
           end
      )
      []
      s.

  Lemma normalise_sealed_words_aux_empty :
    normalise_sealed_words_aux [] = [].
  Proof. by rewrite /normalise_sealed_words_aux /=. Qed.

  Lemma normalise_sealed_words_aux_spec4 (l : list Word) (w : Word) :
    ( w ∉ l -> w ∉ ( normalise_sealed_words_aux l ) ).
  Proof.
    move: w.
    induction l as [| w' l ] ; intros w Hw.
    {  rewrite normalise_sealed_words_aux_empty; set_solver+. }
    apply not_elem_of_cons in Hw as [Hww' Hw].
    pose proof (IHl w Hw) as IH.
    rewrite /normalise_sealed_words_aux.
    rewrite foldr_cons -/(normalise_sealed_words_aux l).
    destruct (isGlobalWord w').
    - apply not_elem_of_cons; split; auto.
      rewrite list_elem_of_filter.
      intro Hcontra; destruct Hcontra as [? Hin]; try done.
    - destruct ( find (λ w'0 : Word, bool_decide (w'0 = force_global w')) (normalise_sealed_words_aux l) ) eqn:Hfind
      ; set_solver.
  Qed.
  Lemma isGlobal_force_global w : is_z w = false -> isGlobalWord (force_global w) = true.
  Proof. intros; destruct_word w; cbn in *; auto. destruct sb; cbn; done. Qed.
  Lemma isGlobal_force_global' w : is_z (force_global w) = false -> isGlobalWord (force_global w) = true.
  Proof. intros; destruct_word w; cbn in *; auto. destruct sb; cbn; done. Qed.

  Lemma force_global_neq_borrow (w w' : Word) :
    is_z w = false -> force_global w ≠ borrow w'.
  Proof. intros Hz; destruct w,w'; cbn; try done; destruct sb,sb0; cbn; try done. Qed.

  Lemma borrow_force_global: ∀ w : Word, borrow (force_global w) = borrow w.
  Proof. destruct w; cbn; try done; destruct sb; cbn; try done. Qed.

  Lemma normalise_sealed_words_aux_spec_force_global_1 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    (force_global w) ∈ l ->
        (force_global w) ∈ ( normalise_sealed_words_aux l ).
  Proof.
    move: w.
    induction l as [| w' l ] ; intros w Hz Hglobal.
    { by apply elem_of_nil in Hglobal. }
    apply Forall_cons in Hz as [Hz_w' Hz_l].
    rewrite /normalise_sealed_words_aux.
    rewrite foldr_cons -/(normalise_sealed_words_aux l).
    apply elem_of_cons in Hglobal as [? | Hglobal] ; simplify_eq.
    - rewrite isGlobal_force_global'; auto.
      apply elem_of_cons; by left.
    - destruct ( isGlobalWord w' ) eqn:Hw'.
      + apply elem_of_cons; right.
        apply list_elem_of_filter; split; auto.
        destruct w,w'; cbn; try done; destruct sb,sb0; cbn; try done.
      + destruct ( find (λ w'0 : Word, bool_decide (w'0 = force_global w')) (normalise_sealed_words_aux l) ); auto.
        apply elem_of_cons; right; auto.
  Qed.

  Lemma normalise_sealed_words_aux_spec_force_global_2 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    (force_global w) ∈ l ->
        (borrow w) ∉ ( normalise_sealed_words_aux l ).
  Proof.
    move: w.
    induction l as [| w' l ] ; intros w Hz Hglobal.
    { by apply elem_of_nil in Hglobal. }
    apply Forall_cons in Hz as [Hz_w' Hz_l].
    rewrite /normalise_sealed_words_aux.
    rewrite foldr_cons -/(normalise_sealed_words_aux l).
    apply elem_of_cons in Hglobal as [? | Hglobal] ; simplify_eq.
    - rewrite isGlobal_force_global'; auto.
      intro Hw; apply elem_of_cons in Hw as [Hw | Hw].
      {  exfalso; eapply (force_global_neq_borrow w w); eauto.
         destruct w; try done.
      }
      apply list_elem_of_filter in Hw as [Hw _].
      by rewrite borrow_force_global in Hw.
    - destruct ( isGlobalWord w' ) eqn:Hw'.
      + intro Hw; apply elem_of_cons in Hw as [Hw | Hw].
        * rewrite -Hw in Hw'.
          destruct w; cbn in *; try done; destruct sb; cbn in *; try done.
        * apply list_elem_of_filter in Hw as [Hw Hw''].
          apply IHl in Hglobal; auto.
      + destruct ( find (λ w'0 : Word, bool_decide (w'0 = force_global w'))
                     (normalise_sealed_words_aux l) ) eqn:Hfind; auto.
        intro Hw; apply elem_of_cons in Hw as [Hw | Hw].
        * pose proof ( normalise_sealed_words_aux_spec_force_global_1 _ _ Hz_l Hglobal) as Hglobal'.
          rewrite list_elem_of_In in Hglobal'.
          apply (find_none _ _ Hfind _) in Hglobal'.
          apply bool_decide_eq_false in Hglobal'.
          apply Hglobal'.
          by rewrite -Hw force_global_borrow.
        * apply IHl in Hglobal; auto.
  Qed.

  Lemma normalise_sealed_words_aux_spec3_1 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    ( (borrow w) ∉ l ∧ (force_global w) ∈ l ->
        (force_global w) ∈ ( normalise_sealed_words_aux l )
    ).
  Proof.
    intros Hz [_ Hglobal].
    apply normalise_sealed_words_aux_spec_force_global_1; auto.
  Qed.

  Lemma normalise_sealed_words_aux_spec3_2 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    ( (borrow w) ∉ l ∧ (force_global w) ∈ l ->
        (borrow w) ∉ ( normalise_sealed_words_aux l )
    ).
  Proof.
    intros Hz [Hborrow _].
    apply normalise_sealed_words_aux_spec4; auto.
  Qed.

  Lemma normalise_sealed_words_aux_spec3 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    ( (borrow w) ∉ l ∧ (force_global w) ∈ l ->
        (force_global w) ∈ ( normalise_sealed_words_aux l ) ∧
        (borrow w) ∉ ( normalise_sealed_words_aux l )
    ).
  Proof.
    intros Hz H.
    split; [ apply normalise_sealed_words_aux_spec3_1| apply normalise_sealed_words_aux_spec3_2]; done.
  Qed.

  Lemma isGlobalWord_borrow w : isGlobalWord (borrow w) = false.
  Proof. destruct_word w ; auto; destruct sb; auto. Qed.

  Lemma normalise_sealed_words_aux_spec1_1 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    ( (borrow w) ∈ l ∧ (force_global w) ∈ l ->
        (force_global w) ∈ ( normalise_sealed_words_aux l )
    ).
  Proof.
    intros Hz [_ Hglobal].
    apply normalise_sealed_words_aux_spec_force_global_1; auto.
  Qed.

  Lemma normalise_sealed_words_aux_spec1_2 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    ( (borrow w) ∈ l ∧ (force_global w) ∈ l ->
        (borrow w) ∉ ( normalise_sealed_words_aux l )
    ).
  Proof.
    intros Hl [_ Hglobal].
    apply normalise_sealed_words_aux_spec_force_global_2; auto.
  Qed.

  Lemma normalise_sealed_words_aux_spec2_1 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    ( (borrow w) ∈ l ∧ (force_global w) ∉ l ->
        (force_global w) ∉ ( normalise_sealed_words_aux l )
    ).
  Proof.
    intros Hz [_ Hglobal].
    apply normalise_sealed_words_aux_spec4; auto.
  Qed.

  Lemma normalise_sealed_words_aux_spec2_2 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    ( (borrow w) ∈ l ∧ (force_global w) ∉ l ->
        (borrow w) ∈ ( normalise_sealed_words_aux l )
    ).
  Proof.
    move: w.
    induction l as [| w' l ] ; intros w Hz [Hborrow Hglobal].
    { by apply elem_of_nil in Hborrow. }
    apply Forall_cons in Hz as [Hz_w' Hz_l].
    apply not_elem_of_cons in Hglobal as [Hww' Hw].
    rewrite /normalise_sealed_words_aux.
    rewrite foldr_cons -/(normalise_sealed_words_aux l).
    apply elem_of_cons in Hborrow as [Hborrow | Hborrow].
    - rewrite -Hborrow isGlobalWord_borrow.
      destruct ( find (λ w'0 : Word, bool_decide (w'0 = force_global (borrow w))) (normalise_sealed_words_aux l) ) eqn:Hfind; auto.
      + exfalso.
        apply find_some in Hfind as [Hin Hfind].
        rewrite bool_decide_eq_true in Hfind; simplify_eq.
        rewrite force_global_borrow in Hin.
        apply list_elem_of_In in Hin.
        apply normalise_sealed_words_aux_spec4 in Hw; auto.
      + apply elem_of_cons; by left.
    - destruct ( isGlobalWord w' ) eqn:Hw'.
      + apply elem_of_cons; right.
        apply list_elem_of_filter; split; auto.
        destruct w,w'; cbn in *; try done
                   ; try (destruct sb, sb0); cbn in *; try done
                   ; destruct g0; intro ; simplify_eq; apply Hww'; try done.
      + destruct ( find (λ w'0 : Word, bool_decide (w'0 = force_global w'))
                     (normalise_sealed_words_aux l) ) eqn:Hfind; auto.
        apply elem_of_cons; right; auto.
  Qed.

  Lemma normalise_sealed_words_aux_spec2 (l : list Word) (w : Word) :
    Forall (fun w => is_z w = false) l ->
    ( (borrow w) ∈ l ∧ (force_global w) ∉ l ->
      (force_global w) ∉ ( normalise_sealed_words_aux l ) ∧
      (borrow w) ∈ ( normalise_sealed_words_aux l )
    ).
  Proof.
    intros Hz H.
    split; [ apply normalise_sealed_words_aux_spec2_1| apply normalise_sealed_words_aux_spec2_2]; done.
  Qed.

  (* Lemma normalise_sealed_words_aux_spec (l : list Word) (w : Word) : *)
  (*   NoDup l -> *)
  (*   ( (borrow w) ∈ l ∧ (force_global w) ∈ l -> *)
  (*       (force_global w) ∈ ( normalise_sealed_words_aux l ) ∧ *)
  (*       (borrow w) ∉ ( normalise_sealed_words_aux l ) *)
  (*   ) *)
  (*   ∧ *)
  (*   ( (borrow w) ∈ l ∧ (force_global w) ∉ l -> *)
  (*       (force_global w) ∉ ( normalise_sealed_words_aux l ) ∧ *)
  (*       (borrow w) ∈ ( normalise_sealed_words_aux l ) *)
  (*   ) *)
  (*   ∧ *)
  (*   ( (borrow w) ∉ l ∧ (force_global w) ∈ l -> *)
  (*       (force_global w) ∈ ( normalise_sealed_words_aux l ) ∧ *)
  (*       (borrow w) ∉ ( normalise_sealed_words_aux l ) *)
  (*   ) *)
  (*   ∧ *)
  (*   ( w ∉ l -> w ∉ ( normalise_sealed_words_aux l ) ). *)
  (* Proof. *)
  (* Admitted. *)

  Lemma normalise_sealed_words_aux_inv (l : list Word) (w : Word) :
    w ∈ normalise_sealed_words_aux l -> w ∈ l.
  Proof.
    move: w.
    induction l as [| w' l]; intros w Hw.
    { by rewrite normalise_sealed_words_aux_empty in Hw. }
    apply elem_of_cons.
    rewrite /normalise_sealed_words_aux foldr_cons -/(normalise_sealed_words_aux l) in Hw.
    destruct ( isGlobalWord w' ) eqn:Hw'.
    - apply elem_of_cons in Hw as [? | Hw]; simplify_eq; first by left.
      apply list_elem_of_filter in Hw as [_ Hl].
      right; auto.
    - destruct ( find (λ w'0 : Word, bool_decide (w'0 = force_global w')) (normalise_sealed_words_aux l) ).
      + right; auto.
      + apply elem_of_cons in Hw as [? | Hw]; simplify_eq; first by left.
        right; auto.
  Qed.

  (* Lemma normalise_sealed_words_aux_empty : *)
  (*   normalise_sealed_words_aux [] = []. *)
  (* Proof. by rewrite /normalise_sealed_words_aux /=. Qed. *)

  Lemma word_either_borrow_or_force_global (w : Word) :
    is_z w = false ->
    { w = force_global w } + { w = borrow w }.
  Proof.
    intros Hz.
    destruct w; cbn; try done; (try destruct sb); destruct g; cbn; try (left; done); try (right; done).
  Qed.

  Lemma normalise_sealed_words_aux_union (s s' : list Word) :
    Forall (fun w => is_z w = false) s ->
    Forall (fun w => is_z w = false) s' ->
    normalise_sealed_words_aux (s ++ s') ⊆ (normalise_sealed_words_aux s) ∪ (normalise_sealed_words_aux s').
  Proof.
    intros Hz Hz' w Hw.
    apply elem_of_union.
    pose proof (normalise_sealed_words_aux_inv _ _ Hw) as Hw_in.
    pose proof Hw_in as Hw_in'.
    apply elem_of_union in Hw_in.
    destruct Hw_in as [Hw_in | Hw_in]; [left | right].
    - pose proof Hz as Hz_forall.
      rewrite Forall_forall in Hz_forall.
      pose proof ( Hz_forall w Hw_in) as Hwz.
      pose proof ( word_either_borrow_or_force_global w ) as [ Hglobal | Hborrow]; auto.
      + rewrite Hglobal in Hw_in; rewrite Hglobal.
        apply normalise_sealed_words_aux_spec_force_global_1; auto.
      + destruct (decide (force_global w ∈ s) ) as [Hw_global | Hw_global]; cycle 1.
        { rewrite Hborrow; rewrite Hborrow in Hw_in.
          apply normalise_sealed_words_aux_spec2_2; auto.
        }
        assert ( force_global w ∈ s ++ s' ) as Hw_global' by ( set_solver+Hw_global).
        rewrite Hborrow in Hw.
        rewrite Hborrow in Hw_in'.
        apply normalise_sealed_words_aux_spec_force_global_2 in Hw_global'; first done.
        apply Forall_app; auto.
    - pose proof Hz' as Hz_forall'.
      rewrite Forall_forall in Hz_forall'.
      pose proof ( Hz_forall' w Hw_in) as Hwz'.
      pose proof ( word_either_borrow_or_force_global w ) as [ Hglobal | Hborrow]; auto.
      + rewrite Hglobal in Hw_in; rewrite Hglobal.
        apply normalise_sealed_words_aux_spec_force_global_1; auto.
      + destruct (decide (force_global w ∈ s') ) as [Hw_global | Hw_global]; cycle 1.
        { rewrite Hborrow; rewrite Hborrow in Hw_in.
          apply normalise_sealed_words_aux_spec2_2; auto.
        }
        assert ( force_global w ∈ s ++ s' ) as Hw_global' by ( set_solver+Hw_global).
        rewrite Hborrow in Hw.
        rewrite Hborrow in Hw_in'.
        apply normalise_sealed_words_aux_spec_force_global_2 in Hw_global'; first done.
        apply Forall_app; auto.
  Qed.

  Lemma normalise_sealed_words_aux_mono (s s' : list Word) :
    Forall (fun w => is_z w = false) s' ->
    s ⊆ s' ->
    normalise_sealed_words_aux s ⊆ normalise_sealed_words_aux s'.
  Proof.
    intros Hz Hs.
    intros w Hw.
    pose proof ( normalise_sealed_words_aux_inv _ _ Hw ) as Hw_s.
    pose proof (Hs _ Hw_s) as Hw_s'.
    assert (is_z w = false) as Hw_z.
    { rewrite Forall_forall in Hz; apply Hz; done. }
    pose proof ( word_either_borrow_or_force_global w ) as [ Hglobal | Hborrow]; auto.
    - rewrite Hglobal in Hw_s'; rewrite Hglobal.
      apply normalise_sealed_words_aux_spec_force_global_1; auto.
    - rewrite Hborrow in Hw_s'; rewrite Hborrow.
      destruct (decide (force_global w ∈ s) ) as [Hw_global | Hw_global].
      + rewrite Hborrow in Hw_s Hw.
        apply normalise_sealed_words_aux_spec_force_global_2 in Hw_global; first done.
        rewrite Forall_forall; rewrite Forall_forall in Hz.
        by intros x Hx; apply Hz; apply Hs.
      + destruct (decide (force_global w ∈ s') ) as [Hw_global' | Hw_global']; cycle 1.
        { apply normalise_sealed_words_aux_spec2_2; auto; split; auto. }
        exfalso.
  Abort.


  Lemma normalise_sealed_words_aux_borrow (w : Word) :
    is_z w = false ->
    w ≠ borrow w ->
    normalise_sealed_words_aux [w; borrow w] = [ w ].
  Proof.
    intros Hz Hw.
    cbn.
    destruct ( isGlobalWord w ) eqn:Hglobal; rewrite isGlobalWord_borrow.
    - rewrite (filter_singleton _ _ []).
      destruct ( decide (borrow w ≠ borrow w) ); done.
    - exfalso.
      destruct w; cbn in *; try done.
      + destruct sb; destruct g ; try done.
      + destruct g ; try done.
      + destruct sb; destruct g ; try done.
  Qed.

  (* Global Instance Permutation_normalise_sealed_words_aux : Proper (Permutation ==> eq) normalise_sealed_words_aux. *)
  (* Proof. *)
  (*   intros l l' Hp. *)
  (* Admitted. *)


  Lemma normalise_sealed_words_aux_singleton (w : Word) :
    normalise_sealed_words_aux {[w]} = {[ w ]}.
  Proof. rewrite /normalise_sealed_words_aux /=.
         destruct ( isGlobalWord w ); auto.
  Qed.

  Definition normalise_sealed_words (s : gset Word) : gset Word :=
    list_to_set (normalise_sealed_words_aux (filter (fun w => is_z w = false) (elements s))).

  Lemma normalise_sealed_words_empty :
    normalise_sealed_words ∅ = ∅.
  Proof. by rewrite /normalise_sealed_words elements_empty filter_nil
           normalise_sealed_words_aux_empty list_to_set_nil.
  Qed.

  Lemma normalise_sealed_words_union (s s' : gset Word) :
    s ## s' ->
    normalise_sealed_words (s ∪ s') ⊆ (normalise_sealed_words s) ∪ (normalise_sealed_words s').
  Proof. intros Hs.
  (*        rewrite /normalise_sealed_words. *)
  (*        rewrite -list_to_set_app_L. *)
  (*        intros w Hw. *)
  (*        apply elem_of_list_to_set in Hw. *)
  (*        apply elem_of_list_to_set. *)
  (*        eapply normalise_sealed_words_aux_union; auto. *)
  (*        { apply Forall_forall; intros x Hx; apply list_elem_of_filter in Hx as [? _]; done. } *)
  (*        { apply Forall_forall; intros x Hx; apply list_elem_of_filter in Hx as [? _]; done. } *)
  (*        rewrite -filter_app. *)
  (*        eapply elem_of_weaken; last eapply normalise_sealed_words_aux_union. *)
  (*        rewrite -filter_app. *)
  (*        eapply normalise_sealed_words_aux_mono; last eauto. *)
  (*        clear w Hw. *)
  (*        intros w Hw. *)
  (*        apply list_elem_of_filter in Hw as [Hw_z Hw]. *)
  (*        apply list_elem_of_filter; split; auto. *)
  (*        apply elem_of_elements in Hw. *)
  (*        apply elem_of_union in Hw. *)
  (*        apply elem_of_app. *)
  (*        rewrite !elem_of_elements. *)
  (*        done. *)
  (* Qed. *)
  Admitted.

  Lemma normalise_sealed_words_singleton (w : Word) :
    is_z w = false ->
    normalise_sealed_words {[w]} = {[ w ]}.
  Proof. intros Hw. rewrite /normalise_sealed_words.
         rewrite elements_singleton (filter_singleton _ _ []) Hw.
         destruct (decide (false = false)) as [_|]; last done.
         rewrite normalise_sealed_words_aux_singleton list_to_set_singleton_L.
         done.
  Qed.

  (* Lemma normalise_sealed_words_mono (s s' : gset Word) : *)
  (*   s ⊆ s' -> *)
  (*   normalise_sealed_words s ⊆ normalise_sealed_words s'. *)
  (* Proof. *)
  (*   intros Hs. *)
  (*   rewrite /normalise_sealed_words. *)
  (*   intros w Hw. *)
  (*   apply elem_of_list_to_set. *)
  (*   apply elem_of_list_to_set in Hw. *)
  (*   eapply normalise_sealed_words_aux_mono; last eauto. *)
  (*   clear w Hw; intros w Hw. *)
  (*   apply list_elem_of_filter in Hw as [Hz Hw]. *)
  (*   apply list_elem_of_filter; split; auto. *)
  (*   apply elem_of_elements in Hw. *)
  (*   apply elem_of_elements. *)
  (*   by apply Hs. *)
  (* Qed. *)

  Global Instance Permutation_normalise_sealed_words_aux : Proper (Permutation ==> Permutation) normalise_sealed_words_aux.
  Proof.
    apply foldr_permutation_proper.
    - admit.
    - intros w l l' Hp.
      destruct (isGlobalWord w).
      + by setoid_rewrite Hp.
      + destruct (find (λ w' : Word, bool_decide (w' = force_global w)) l) eqn:Hfind_l.
        * destruct (find (λ w' : Word, bool_decide (w' = force_global w)) l') eqn:Hfind_l'; auto.
          apply find_some in Hfind_l as [Hl ?].
          setoid_rewrite Hp in Hl.
          eapply (find_none _ _ Hfind_l') in Hl.
          by rewrite Hl in H.
        * destruct (find (λ w' : Word, bool_decide (w' = force_global w)) l') eqn:Hfind_l'; auto.
          apply find_some in Hfind_l' as [Hl' ?].
          setoid_rewrite <- Hp in Hl'.
          eapply (find_none _ _ Hfind_l) in Hl'.
          by rewrite Hl' in H.
    - intros w w' l.
      destruct ( isGlobalWord w ) eqn:Hglobal_w.
      + destruct ( isGlobalWord w' ) eqn:Hglobal_w'.
        * rewrite !filter_cons.
          destruct ( decide (w' ≠ borrow w) ).
          ** destruct ( decide (w ≠ borrow w') ).
             *** rewrite !list_filter_filter.
                 admit.
             *** assert (w = borrow w'); simplify_eq.
                 { admit. }
                 by rewrite isGlobalWord_borrow in Hglobal_w.
          ** destruct ( decide (w ≠ borrow w') ).
             *** assert (w' = borrow w); simplify_eq.
                 { admit. }
                 by rewrite isGlobalWord_borrow in Hglobal_w'.
             *** rewrite !list_filter_filter.
                 admit.
        * destruct ( find (λ w'0 : Word, bool_decide (w'0 = force_global w')) l ) eqn:Hfind.
          ** cbn.
             destruct ( bool_decide (w = force_global w') ) eqn: Hw_global_w'; auto.
             apply find_some in Hfind as [H Hfind].
             apply bool_decide_eq_true in Hfind; simplify_eq.
             destruct (
                 find (λ w'0 : Word, bool_decide (w'0 = force_global w'))
                   (filter (λ w'0 : Word, w'0 ≠ borrow w) l)
               ) eqn:Hfind'; auto.
             assert (In (force_global w') (filter (λ w'0 : Word, w'0 ≠ borrow w) l)) as H'.
             { apply list_elem_of_In, list_elem_of_filter ; split; last by apply list_elem_of_In.
               admit.
             }
             pose proof (find_none _ _ Hfind' (force_global w') H') as Hcontra.
             cbn in *.
             apply bool_decide_eq_false in Hcontra; simplify_eq.
          ** admit.
      + admit.
  Admitted.

  Lemma normalise_sealed_words_borrow (w : Word) :
    is_z w = false ->
    normalise_sealed_words {[w; borrow w]} = {[ w ]}.
  Proof.
    intros Hz.
    assert ( (is_z (borrow w) = false) ) as Hz'.
    { destruct w; cbn in * ;auto. }
    destruct (decide (w = borrow w)) as [H| Hglobal]; simplify_eq.
    { rewrite {1}H {3}H.
      replace {[borrow w; borrow w]} with ({[borrow w]} : gset Word) by set_solver+.
      rewrite normalise_sealed_words_singleton; auto.
    }
    rewrite /normalise_sealed_words.
    assert ((elements ({[w; borrow w]} : gset Word)) ≡ₚ [w ; borrow w]).
    { rewrite elements_disj_union.
      - rewrite !elements_singleton; done.
      - set_solver.
    }
    setoid_rewrite H.
    replace ( (filter (λ w0 : Word, is_z w0 = false) [w; borrow w]) ) with [w; borrow w].
    2: { rewrite !filter_cons.
         destruct ( decide (is_z w = false)); try done.
         destruct ( decide (is_z (borrow w) = false)); try done.
    }
    rewrite normalise_sealed_words_aux_borrow; auto.
    by rewrite list_to_set_singleton_L.
  Qed.

  Local Definition sealing_map_def
    (W : WORLD)
    (C : CmptName)
    : iProp Σ
     := ([∗ map] o↦ws ∈ seal_std W,
           (sts_seals_std C o ws) ∗
           ∃ Po, seal_pred o Po ∗
                 (∀ w, future_priv_mono C Po w) ∗
                 ( [∗ set] w ∈ normalise_sealed_words ws, ▷ Po (W, C, w) )).

  Local Definition sealing_map_aux : { x | x = @sealing_map_def }. by eexists. Qed.
  Definition sealing_map := proj1_sig sealing_map_aux.
  Local Definition sealing_map_eq : @sealing_map = @sealing_map_def := proj2_sig sealing_map_aux.

  Local Lemma sealing_map_def_empty (C : CmptName) : ⊢ (sealing_map_def (∅, (∅, ∅), ∅) C)%I.
  Proof. iStartProof; rewrite /sealing_map_def ; done. Qed.

  Local Lemma sealing_map_def_monotone (C : CmptName) (W W' : WORLD) :
    (seal_std W) = (seal_std W') ->
    related_sts_priv_world W W' →
    sealing_map_def W C -∗
    sealing_map_def W' C.
  Proof.
    iIntros (HWseal Hrelated) "Hr".
    rewrite /sealing_map_def.
    rewrite HWseal.
    iApply big_sepM_mono; iFrame.
    iIntros (o ws Hsome) "Hm".
    iDestruct "Hm" as "($ & %Po & Hpred & #Hmono & HPo)".
    iExists Po; iFrame "∗#".
    clear -Hrelated.
    iStopProof.
    move: (normalise_sealed_words ws); clear ws; intros ws.
    induction ws using set_ind_L; iIntros "[#Hmono Hs]"; first done.
    rewrite big_sepS_union; last set_solver+H.
    rewrite big_sepS_union; last set_solver+H.
    iDestruct "Hs" as "[Hx Hs]".
    iSplitL "Hx"; last (iApply IHws; iFrame "∗#").
    rewrite !big_sepS_singleton.
    iApply "Hmono"; eauto.
  Qed.

  Local Lemma sealing_map_def_alloc (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ) (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    o ∉ dom (seal_std W) ->
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    sealing_map_def W C ∗ sts_full_world W C ==∗
    sealing_map_def W' C ∗ sts_full_world W' C ∗ sts_seals_std C o ws.
  Proof.
    intros W'; subst W'.
    iIntros (Ho) "Hseal_Po Hmono_Po Hws_Po [Hr Hsts]".
    rewrite /sealing_map_def.
    iMod (sts_alloc_seal_std _ _ _ ws with "[] [$Hsts]") as "[Hsts #Hseal]"; eauto.
    iAssert (
        [∗ map] k↦y ∈ W.2, sts_seals_std C k y ∗
                                    ∃ Po0 : WORLD * CmptName * Word → iProp Σ,
                                      seal_pred k Po0 ∗
                                      (∀ w : Word, future_priv_mono C Po0 w) ∗
                                      ([∗ set] w ∈ (normalise_sealed_words y), ▷ Po0 (<o[o:=ws]o>W, C, w))
      )%I with "[Hr]" as "Hr".
    {
      iClear "Hseal".
      clear Po.
      iApply big_sepM_mono; last iFrame.
      iIntros (o' wso' Hswo') "($ & %Po & Hspred & #Hmono & Hwso')".
      iExists Po; iFrame "∗#".
      pose proof (related_sts_priv_world_update_ot W o ws) as Hrelated.
      clear -Hrelated.
      iStopProof.
      move: (normalise_sealed_words wso'); clear wso'; intros wso'.
      induction wso' using set_ind_L; iIntros "[#Hmono Hs]"; first done.
      rewrite big_sepS_union; last set_solver+H.
      rewrite big_sepS_union; last set_solver+H.
      iDestruct "Hs" as "[Hx Hs]".
      iSplitL "Hx"; last ( iApply IHwso'; iFrame "∗#" ).
      rewrite !big_sepS_singleton.
      iApply "Hmono"; eauto.
    }

    iDestruct (big_sepM_insert _ _ o ws with "[$Hr $Hseal $Hseal_Po $Hmono_Po $Hws_Po]") as "Hr".
    { by apply not_elem_of_dom. }
    iModIntro.
    iFrame "#∗".
    rewrite /seals_std_update_default.
    rewrite not_elem_of_dom in Ho; rewrite Ho /= union_empty_r_L.
    done.
  Qed.

  Local Lemma sealing_map_def_update (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws ws' : gset Word)  :
    let W' := (<o[ o := ws' ∪ ws ]o> W) in
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    ([∗ set] w ∈ (normalise_sealed_words ws'), ▷ Po (W', C, w)) -∗
    sealing_map_def W C ∗ sts_full_world W C
    ==∗
    sealing_map_def W' C ∗ sts_full_world W' C ∗ sts_seals_std C o (ws' ∪ ws).
  Proof.
    intros W'; subst W'.
    iIntros (Ho) "Hspred_Po Hws_Po [Hr Hsts]".
    rewrite /sealing_map_def.
    iDestruct (big_sepM_delete with "Hr") as "[(Hseal & %Po' & Hpred & #Hmono & HPo) Hr]"; eauto.
    iMod (sts_update_seal_std _ _ _ _ ws' with "[$Hsts $Hseal]") as "[Hsts #Hseal]"; eauto.
    iDestruct (seal_pred_agree with "Hspred_Po Hpred") as "#Heq".
    pose proof (related_sts_pub_world_update_ot W o (ws' ∪ ws)) as Hrelated.
    iAssert (
         ∃ Po0 : WORLD * CmptName * Word → iProp Σ,
           seal_pred o Po0 ∗
           (∀ w : Word, future_priv_mono C Po0 w) ∗
           ([∗ set] w ∈ (normalise_sealed_words ws' ∪ normalise_sealed_words ws), ▷ Po0 (<o[o:=ws' ∪ ws]o>W, C, w))
      )%I with "[Hws_Po Hpred HPo]" as "H".
    { iFrame "∗#".
      rewrite -!big_sepS_later; iNext.
      (* iApply big_sepS_subseteq; first apply normalise_sealed_words_union; auto. *)
      iApply (big_sepS_union_2 with "[Hws_Po]")
      ; generalize Hrelated; clear Hrelated
      ; generalize (ws' ∪ ws) as ws0; intros ws0 Hrelated.
      - clear -Hrelated; iClear "Hseal".
        iStopProof.
        move: (normalise_sealed_words ws'); clear ws'; intros ws'.
        induction ws' using set_ind_L; iIntros "[ [#Hmono #Heq] Hs]"; first done.
        rewrite big_sepS_union; last set_solver+H.
        rewrite big_sepS_union; last set_solver+H.
        iDestruct "Hs" as "[Hx Hs]".
        iSplitL "Hx"; last ( iApply IHws'; eauto ).
        rewrite !big_sepS_singleton; iRewrite -("Heq" $! (<o[o:=ws0]o>W, C, x)); done.
      - clear -Hrelated; iClear "Hseal".
        iStopProof.
        move: (normalise_sealed_words ws); clear ws; intros ws.
        induction ws using set_ind_L; iIntros "[ [#Hmono #Heq] Hs]"; first done.
        rewrite big_sepS_union; last set_solver+H.
        rewrite big_sepS_union; last set_solver+H.
        iDestruct "Hs" as "[Hx Hs]".
        iSplitL "Hx"; last ( iApply IHws; eauto ).
        rewrite !big_sepS_singleton.
        iApply "Hmono"; eauto.
        iPureIntro.
        by apply related_sts_pub_priv_world.
    }
    iAssert (
        [∗ map] k↦y ∈ delete o W.2, sts_seals_std C k y ∗
                                    ∃ Po0 : WORLD * CmptName * Word → iProp Σ,
                                      seal_pred k Po0 ∗
                                      (∀ w : Word, future_priv_mono C Po0 w) ∗
                                      ([∗ set] w ∈ normalise_sealed_words y, ▷ Po0 (<o[o:=ws' ∪ ws]o>W, C, w))
      )%I with "[Hr]" as "Hr".
    {
      iClear "Heq Hmono Hseal".
      clear Po.
      iApply big_sepM_mono; last iFrame.
      iIntros (o' wso' Hswo') "($ & %Po & Hspred & #Hmono & Hwso')".
      iExists Po; iFrame "∗#".
      clear -Hrelated.
      iStopProof.
      move: (normalise_sealed_words wso'); clear wso'; intros wso'.
      induction wso' using set_ind_L; iIntros "[#Hmono Hs]"; first done.
      rewrite big_sepS_union; last set_solver+H.
      rewrite big_sepS_union; last set_solver+H.
      iDestruct "Hs" as "[Hx Hs]".
      iSplitL "Hx"; last ( iApply IHwso'; iFrame "∗#" ).
      rewrite !big_sepS_singleton.
      iApply "Hmono"; eauto.
      iPureIntro.
      by apply related_sts_pub_priv_world.
    }
    (* iDestruct "H" as "(%P & Hspred_P & HmonoP & HwsP)". *)
    (* iDestruct (big_sepS_union with "HwsP") as "HwsP". *)

    iDestruct (big_sepM_insert with "[$Hr H]") as "Hr"; eauto.
    (* { by simplify_map_eq. } *)
    (* rewrite insert_delete_eq. *)
    (* iFrame "#∗". *)
    (* rewrite /seals_std_update_default. *)
    (* rewrite Ho /=. *)
    (* replace (ws' ∪ ws ∪ ws) with (ws' ∪ ws) by set_solver+. *)
    (* by iFrame. *)
  Admitted.

  Local Lemma sealing_map_def_update' (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    sealing_map_def W C ∗ sts_full_world W C
    ==∗
    sealing_map_def W' C ∗ sts_full_world W' C ∗ sts_seals_std C o ws.
  Proof.
    intros W'; subst W'.
    iIntros "Hspred_Po Hmono_Po Hws_Po [Hr Hsts]".
    destruct ((seal_std W) !! o) eqn:Ho.
    - iMod (sealing_map_def_update _ _ _ _ g ws with "[$Hspred_Po] [Hws_Po] [$Hr $Hsts]")
        as "(Hseals & Hsts & Hseal)"; eauto.
      { rewrite /seals_std_update_default Ho /=.
        replace (ws ∪ g ∪ g) with (ws ∪ g) by set_solver+.
        done.
      }
      iModIntro.
      rewrite /seals_std_update_default Ho /=.
      replace (ws ∪ g ∪ g) with (ws ∪ g) by set_solver+.
      iFrame.
      iApply sts_seals_std_weaken; last done; set_solver+.
    - rewrite -not_elem_of_dom in Ho.
      iMod (sealing_map_def_alloc _ _ _ _ ws Ho with "[$Hspred_Po] [$Hmono_Po] [Hws_Po] [$Hr $Hsts]")
        as "(Hseals & Hsts & Hseal)"; eauto.
      by iFrame.
  Qed.

  Lemma sealing_map_empty (C : CmptName) : ⊢ (sealing_map (∅, (∅, ∅), ∅) C)%I.
  Proof. rewrite sealing_map_eq; apply sealing_map_def_empty. Qed.

  Lemma sealing_map_monotone (C : CmptName) (W W' : WORLD) :
    (seal_std W) = (seal_std W') ->
    related_sts_priv_world W W' →
    sealing_map W C -∗
    sealing_map W' C.
  Proof.
    iIntros (HWseal Hrelated) "Hr".
    rewrite sealing_map_eq.
    iApply sealing_map_def_monotone; eauto.
  Qed.

  Lemma sealing_map_monotone_pub (C : CmptName) (W W' : WORLD) :
    (seal_std W) = (seal_std W') ->
    related_sts_pub_world W W' →
    sealing_map W C -∗
    sealing_map W' C.
  Proof.
    iIntros (HWseal Hrelated) "Hr".
    apply related_sts_pub_priv_world in Hrelated.
    iApply sealing_map_monotone; eauto.
  Qed.

  Lemma sealing_map_alloc (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ) (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    o ∉ dom (seal_std W) ->
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    sealing_map W C ∗ sts_full_world W C ==∗
    sealing_map W' C ∗ sts_full_world W' C ∗ sts_seals_std C o ws.
  Proof. rewrite sealing_map_eq; apply sealing_map_def_alloc. Qed.

  Lemma sealing_map_update (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws ws' : gset Word)  :
    let W' := (<o[ o := ws' ∪ ws ]o> W) in
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    ([∗ set] w ∈ (normalise_sealed_words ws'), ▷ Po (W', C, w)) -∗
    sealing_map W C ∗ sts_full_world W C
    ==∗
    sealing_map W' C ∗ sts_full_world W' C ∗ sts_seals_std C o (ws' ∪ ws).
  Proof. rewrite sealing_map_eq; apply sealing_map_def_update. Qed.

  Lemma sealing_map_update' (W : WORLD) (C : CmptName) (Po : WORLD * CmptName * Word → iProp Σ)
    (o : OType) (ws : gset Word)  :
    let W' := (<o[ o := ws ]o> W) in
    seal_pred o Po -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W', C, w)) -∗
    sealing_map W C ∗ sts_full_world W C
    ==∗
    sealing_map W' C ∗ sts_full_world W' C ∗ sts_seals_std C o ws.
  Proof. rewrite sealing_map_eq; apply sealing_map_def_update'. Qed.

  Lemma sealing_map_seal_pred
    (W : WORLD) (C : CmptName) (o : OType) Po `{Hpers : ∀ WCv, Persistent (Po WCv)}
    (ws : gset Word) :
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    sealing_map W C -∗
    sts_full_world W C -∗
    ▷ (sealing_map W C ∗ sts_full_world W C ∗ [∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w)).
  Proof.
    iIntros "#Hspred Hseal Hseals Hsts".
    iDestruct (sts_full_seals_std_subseteq with "Hsts Hseal") as "(%ws' & %Hws' & %Hws_sub)".
    iEval (rewrite sealing_map_eq /sealing_map_def /=) in "Hseals".
    iDestruct (big_sepM_lookup_acc with "Hseals") as "[H Hseals]"; first done.
    iDestruct "H" as "(Hseal_ws & %Po' & #Hspred_Po' & #Hmono & HPos)".
    iDestruct (seal_pred_agree with "Hspred Hspred_Po'") as "#Heq".
    iNext.
    assert ( (∀ w, Persistent (Po (W, C, w)))).
    { intros w'; apply (Hpers (W,C,w')). }
    iAssert ( [∗ set] w ∈ (normalise_sealed_words ws'), Po (W, C, w))%I with "[HPos]" as "#HPs".
    { iClear "Hspred Hspred_Po' Hmono"; clear.
      iStopProof.
      move: (normalise_sealed_words ws'); clear ws'; intros ws'.
      induction ws' using set_ind_L; iIntros "(#Heq & Hs)"; first done.
      rewrite big_sepS_union; last set_solver+H.
      rewrite big_sepS_union; last set_solver+H.
      iDestruct "Hs" as "[Hx Hs]".
      iSplitL "Hx"; last ( iApply IHws'; iFrame "∗#" ).
      rewrite !big_sepS_singleton.
      by iRewrite -("Heq" $! (W,C,x)) in "Hx".
    }
    iDestruct ("Hseals" with "[$Hseal_ws $Hspred_Po' $Hmono HPos]") as "Hseals".
    { by iApply big_sepS_later; iNext. }
    rewrite -/(sealing_map_def W C) -sealing_map_eq.
    iFrame "∗#".
    iApply (big_sepS_subseteq with "HPs"); eauto.
    apply normalise_sealed_words_mono in Hws_sub.
    iApply big_sepS_subseteq; eauto.
  Qed.

  Lemma sealing_map_seal_pred_singleton (W : WORLD) (C : CmptName) (o : OType) Po `{Hpers: ∀ WCv, Persistent (Po WCv)} (w : Word) :
    is_z w = false ->
    seal_pred o Po -∗
    sts_seals_std C o {[ w ]} -∗
    sealing_map W C -∗
    sts_full_world W C -∗
    ▷ (sealing_map W C ∗ sts_full_world W C ∗ Po (W, C, w)).
  Proof.
    iIntros (Hw) "#Hspred Hseal Hseals Hsts".
    iDestruct (sealing_map_seal_pred with "Hspred Hseal Hseals Hsts") as "($ & $ & H)"; eauto.
    by rewrite normalise_sealed_words_singleton // big_sepS_singleton.
  Qed.


  Local Definition sealing_map_open_def
    (W : WORLD)
    (C : CmptName)
    (o : OType)
    : iProp Σ
     := ([∗ map] o↦ws ∈ (delete o (seal_std W)),
           (sts_seals_std C o ws) ∗
           ∃ Po, seal_pred o Po ∗
                 (∀ w, future_priv_mono C Po w) ∗
                 ( [∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W, C, w) )).
  Local Definition sealing_map_open_aux : { x | x = @sealing_map_open_def }. by eexists. Qed.
  Definition sealing_map_open := proj1_sig sealing_map_open_aux.
  Local Definition sealing_map_open_eq : @sealing_map_open = @sealing_map_open_def := proj2_sig sealing_map_open_aux.

  Definition sealing_map_resource_open (W : WORLD) (C : CmptName) (o : OType) Po ws :=
    ( ∃ (ws' : gset Word),
        ⌜ (seal_std W) !! o = Some ws' ⌝ ∗
        ⌜ ws ⊆ ws'⌝ ∗
        sts_seals_std C o ws' ∗
        (∀ w : Word, future_priv_mono C Po w) ∗
        ([∗ set] w ∈ (normalise_sealed_words ws' ∖ normalise_sealed_words ws), Po (W, C, w))
    )%I.

  Local Lemma open_sealing_map_def (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    sealing_map_def W C -∗
    sts_full_world W C
    -∗
    sealing_map_open_def W C o ∗
    sts_full_world W C ∗
    ▷ (sealing_map_resource_open W C o Po ws
       ∗ ([∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w))).
  Proof.
    iIntros "Hspred Hseal Hseals Hsts".
    iDestruct (sts_full_seals_std_subseteq with "Hsts Hseal") as "(%ws' & %Hws' & %Hws_sub)".
    iEval (rewrite /sealing_map_def /=) in "Hseals".
    rewrite big_sepM_delete; last done.
    iDestruct "Hseals" as "([ Hseal_ws' (%Po' & Hspred_Po' & #Hmono_Po' & Hws_Po') ] & Hseals)".
    iDestruct (seal_pred_agree with "Hspred Hspred_Po'") as "#Heq".
    iFrame "∗%".
    iNext.
    apply normalise_sealed_words_mono in Hws_sub.
    rewrite {1}(union_difference_L (normalise_sealed_words ws) (normalise_sealed_words ws')); last done.
    iDestruct (big_sepS_union with "Hws_Po'") as "[Hws_Po Hws'_Po]"; first set_solver+.
    iSplitR "Hws_Po".
    - iSplitR "Hws'_Po".
      + iIntros (w W0 W1 Hrel) "!>HPo".
        iRewrite ("Heq" $! (W1, C, w)).
        iRewrite ("Heq" $! (W0, C, w)) in "HPo".
        iApply "Hmono_Po'"; eauto.
      + iApply (big_sepS_impl with "Hws'_Po"); eauto.
        iModIntro; iIntros (w _) "HPo'".
        by iRewrite ("Heq" $! (W, C, w)).
    - iApply (big_sepS_impl with "Hws_Po"); eauto.
      iModIntro; iIntros (w _) "HPo'".
      by iRewrite ("Heq" $! (W, C, w)).
  Qed.

  Local Lemma close_sealing_map_def' (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    (seal_std W) !! o = Some ws ->
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    (∀ w : Word, future_priv_mono C Po w) -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), ▷ Po (W, C, w)) -∗
    sealing_map_open_def W C o -∗
    sealing_map_def W C.
  Proof.
    iIntros (Ho) "Hspred_Po Hseal_ws Hmono_Po Hws_Po Hseals".
    rewrite /sealing_map_open_def.
    iDestruct (big_sepM_delete with "[ - $Hseals ]" ) as "Hseals"; eauto.
  Qed.

  Local Lemma close_sealing_map_def (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    seal_pred o Po -∗
    sealing_map_resource_open W C o Po ws -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w)) -∗
    sealing_map_open_def W C o -∗
    sealing_map_def W C.
  Proof.
    iIntros "Hspred_Po (%ws' & %Hws' & %Hws_ws' & Hseal_ws' & Hmono_ws' & Hws'_Po) Hws_Po Hseals".
    rewrite /sealing_map_open_def.
    iDestruct (big_sepS_union with "[$Hws_Po $Hws'_Po]") as "Hws_Po"; first set_solver+.
    apply normalise_sealed_words_mono in Hws_ws'.
    rewrite -(union_difference_L (normalise_sealed_words ws) (normalise_sealed_words ws')) ; last done.
    iDestruct (big_sepM_delete with "[ - $Hseals ]" ) as "Hseals"; eauto; iFrame.
    by rewrite -big_sepS_later.
  Qed.

  Lemma open_sealing_map (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    seal_pred o Po -∗
    sts_seals_std C o ws -∗
    sealing_map W C -∗
    sts_full_world W C
    -∗
    sealing_map_open W C o ∗
    sts_full_world W C ∗
    ▷ (sealing_map_resource_open W C o Po ws ∗ ([∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w))).
  Proof. rewrite sealing_map_eq sealing_map_open_eq; apply open_sealing_map_def. Qed.

  Lemma open_sealing_map_singleton (W : WORLD) (C : CmptName) (o : OType) Po (w : Word) :
    is_z w = false ->
    seal_pred o Po -∗
    sts_seals_std C o {[w]} -∗
    sealing_map W C -∗
    sts_full_world W C
    -∗
    sealing_map_open W C o ∗
    sts_full_world W C ∗
    ▷ (sealing_map_resource_open W C o Po {[w]} ∗ (Po (W, C, w))).
  Proof.
    iIntros (Hw) "Hspred Hseal Hseals Hsts".
    iDestruct (open_sealing_map with "Hspred Hseal Hseals Hsts") as "($ & $ & Hws)".
    by rewrite normalise_sealed_words_singleton // big_sepS_singleton.
  Qed.

  Lemma close_sealing_map (W : WORLD) (C : CmptName) (o : OType) Po (ws : gset Word) :
    seal_pred o Po -∗
    sealing_map_resource_open W C o Po ws -∗
    ([∗ set] w ∈ (normalise_sealed_words ws), Po (W, C, w)) -∗
    sealing_map_open W C o -∗
    sealing_map W C.
  Proof. rewrite sealing_map_eq sealing_map_open_eq; apply close_sealing_map_def. Qed.

  Lemma close_sealing_map_singleton (W : WORLD) (C : CmptName) (o : OType) Po (w : Word) :
    is_z w = false ->
    seal_pred o Po -∗
    sealing_map_resource_open W C o Po {[w]} -∗
    Po (W, C, w) -∗
    sealing_map_open W C o -∗
    sealing_map W C.
  Proof.
    iIntros (Hz) "Hspred Hseal HPo Hseals".
    iAssert ( [∗ set] w ∈ normalise_sealed_words {[ w ]}, Po (W, C, w) )%I with "[HPo]" as "HPo".
    { by rewrite normalise_sealed_words_singleton // big_sepS_singleton. }
    iDestruct (close_sealing_map with "Hspred Hseal HPo Hseals") as "$".
  Qed.

End sealing_interp.
