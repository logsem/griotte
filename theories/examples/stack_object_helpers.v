From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules rules_LoadU_derived logrel fundamental region_invariants_revocation region_invariants_static region_invariants_batch_uninitialized.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers macros.

(* TODO:move this to stdpp_extra *)
Lemma big_sepM_to_big_sepL2:
  ∀ (PROP : bi) (A B : Type),
    EqDecision A
    → ∀ (EqDecision1 : EqDecision A) (H : Countable A) (φ : A → B → PROP) (l1 : list A) (l2 : list B),
      NoDup l1 → length l1 = length l2 → ⊢ ([∗ map] y1↦y2 ∈ list_to_map (zip l1 l2), φ y1 y2) -∗ ([∗ list] y1;y2 ∈ l1;l2, φ y1 y2).
Proof.
  intros bi A B Eq1 Eq2 H φ l1.
  iInduction (l1) as [|x l1] "IH";iIntros (l2 Hdup Hlen) "H".
  - simpl. destruct l2;inversion Hlen.
    simpl. auto.
  - destruct l2;inversion Hlen. simpl.
    apply NoDup_cons in Hdup as [Hnin Hdup].
    iDestruct (big_sepM_insert with "H") as "[Hx H]".
    { eapply not_elem_of_list_to_map. rewrite fst_zip;auto. lia. }
    iFrame. iDestruct ("IH" $! l2 Hdup H1 with "H") as "$".
Qed.


Lemma elements_dom_list_to_map :
      ∀ K V : Type,
        EqDecision K → ∀ (EqDecision1 : EqDecision K) (H : Countable K) (l : list (K*V)),
          NoDup (l.*1) →
          elements (dom (gset K) (list_to_map l : gmap K V)) ≡ₚl.*1.
Proof.
  intros K V ? ? ? l Hdup. induction l.
  - simpl. auto.
  - destruct a as [k v]. simpl in *.
    apply NoDup_cons in Hdup as [Hin Hdup].
    rewrite dom_insert_L elements_union_singleton.
    constructor. auto.
    apply not_elem_of_dom.
    apply not_elem_of_list_to_map_1. auto.
Qed.

Lemma elements_dom_list_to_map_zip :
      ∀ K V : Type,
        EqDecision K → ∀ (EqDecision1 : EqDecision K) (H : Countable K) (l1 : list K) (l2 : list V),
          length l1 <= length l2 →
          NoDup l1 →
          elements (dom (gset K) (list_to_map (zip l1 l2) : gmap K V)) ≡ₚl1.
Proof.
  intros K V ? ? ? l1. induction l1.
  - simpl. auto.
  - intros l2 Hlen Hdup. destruct l2; [simpl in *; inversion Hlen|]. simpl in *.
    apply NoDup_cons in Hdup as [Hin Hdup].
    rewrite dom_insert_L elements_union_singleton.
    constructor. apply IHl1; auto. lia.
    apply not_elem_of_dom.
    apply not_elem_of_list_to_map_1. rewrite fst_zip;auto. lia.
Qed.

Lemma Permutation_disjoint {A : Type} {eq1 : EqDecision A} {a : A} (l1 l2 l3 : list A) :
  l1 ≡ₚl2 → l1 ## l3 -> l2 ## l3.
Proof.
  intros Hperm Hdisj.
  apply elem_of_disjoint.
  intros x Hx Hx'. revert Hx; rewrite -Hperm =>Hx.
  apply elem_of_disjoint in Hdisj. apply Hdisj in Hx. done.
Qed.

Section stack_object.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).

  (* TODO:move this to multiple_updates *)
  Lemma std_update_multiple_disjoint W l1 l2 ρ1 ρ2 :
    l1 ## l2 →
    std_update_multiple (std_update_multiple W l2 ρ2) l1 ρ1 =
    std_update_multiple (std_update_multiple W l1 ρ1) l2 ρ2.
  Proof.
    induction l1; intros Hdisj.
    - simpl. auto.
    - simpl. apply disjoint_cons in Hdisj as Hnin.
      apply disjoint_weak in Hdisj.
      apply IHl1 in Hdisj. rewrite Hdisj.
      rewrite std_update_multiple_insert_commute;auto.
  Qed.

  Lemma region_addrs_disjoint_skip_middle b a2 a3 aend e :
    (a2 + 1)%a = Some a3 → (a3 <= aend)%a →
    region_addrs b a2 ++ region_addrs a3 aend ## [a2] ++ region_addrs aend e.
  Proof.
    intros Hsome Hle.
    simpl. apply elem_of_disjoint.
    intros x Hx Hx'.
    apply elem_of_cons in Hx' as [-> | Hx'].
    - apply elem_of_app in Hx as [Hx%elem_of_region_addrs | Hx%elem_of_region_addrs];solve_addr.
    - apply elem_of_region_addrs in Hx'.
      apply elem_of_app in Hx as [Hx%elem_of_region_addrs | Hx%elem_of_region_addrs];try solve_addr.
  Qed.

  (* The following lemma will be used to make sure that any object passed as a parameter *)
  (* on the stack, will be disjoint from the current stack *)
  Lemma input_stack_disjoint W a0 a1 a2 p l b e a :
    (a0 + 1)%a = Some a1 →
    readAllowed p = true →
    Forall (λ a, W.1 !! a = Some Monotemporary ∨ (∃ w, W.1 !! a = Some (Uninitialized w))) (region_addrs a1 a2) →
    interp W (inr (p,l,b,e,a)) ∗ future_pub_a_mono a0 (λ Wv, interp Wv.1 Wv.2) (inr (p,l,b,e,a)) -∗
    ⌜(region_addrs b e) ## (region_addrs a1 a2)⌝.
  Proof.
    iIntros (Hincr Hra Hforall) "[#Hvalid #Hmono] /=".
    rewrite elem_of_disjoint. iIntros (i Hin1 Hin2).
    iDestruct (readAllowed_implies_region_conditions with "Hvalid") as "Hcond";auto.
    iDestruct (big_sepL_elem_of with "Hcond") as "[Hrwcond %]";eauto.
    assert (W.1 !! i = Some Monotemporary ∨ W.1 !! i = Some Permanent) as Hi.
    { destruct (pwl p);auto. destruct l;auto. }
    revert Hforall; rewrite Forall_forall =>Hforall. apply Hforall in Hin2 as Ha.
    destruct Ha as [Ha | [w Ha] ]; destruct Hi as [Hi | Hi];try congruence.
    apply elem_of_region_addrs in Hin1 as Hlelt1. destruct Hlelt1 as [Hle1 Hlt1].
    apply elem_of_region_addrs in Hin2 as Hlelt2. destruct Hlelt2 as [Hle2 Hlt2].
    assert (related_sts_a_world W (<s[i:=Uninitialized (inl 0%Z)]s> W) a0) as Hpub.
    { split;[|apply related_sts_pub_plus_refl]. simpl.
      split;[rewrite dom_insert_L;set_solver|].
      intros i0 x y Hx Hy. destruct (decide (i = i0));simplify_map_eq.
      - eright;[|left].
        rewrite decide_True;[|solve_addr]. right. constructor.
      - left. }
    iSpecialize ("Hmono" $! W _ Hpub with "Hvalid").
    iDestruct (readAllowed_implies_region_conditions with "Hmono") as "Hcond'";auto.
    iDestruct (big_sepL_elem_of with "Hcond'") as "[_ %]";eauto.
    iPureIntro.
    destruct (pwl p).
    - rewrite /region_state_pwl_mono /= lookup_insert in H1. done.
    - rewrite /region_state_nwl /= lookup_insert in H1. destruct l; try done.
      destruct H1;done.
  Qed.


  (* Useful lemma to extract the states of all the unused part of the stack *)
  Lemma state_unused_stack (i : nat) W lstk (bstk estk astk a : Addr) :
      (bstk + i ≤ astk)%Z →
      (bstk + i)%a = Some a →
      interp W (inr (URWLX, lstk, bstk, estk, astk)) -∗
      ⌜Forall (λ a0 : Addr, W.1 !! a0 = Some Monotemporary ∨ (∃ w : Word, W.1 !! a0 = Some (Uninitialized w))) (region_addrs a estk)⌝.
  Proof.
    iIntros (Hbounds Hsome) "Hvalid".
    rewrite Forall_forall. iIntros (x Hx).
    rewrite fixpoint_interp1_eq /=. destruct lstk;try done.
    iDestruct "Hvalid" as "[Hlo Hhi]".
    apply elem_of_region_addrs in Hx as Hconds. destruct Hconds as [Hle Hlt].
    destruct (decide (astk <= estk)%Z).
    - assert (addr_reg.min astk estk = astk) as ->;[solve_addr|].
      assert (addr_reg.max bstk astk = astk) as ->;[solve_addr|].
      destruct (decide (x < astk)%Z).
      + iDestruct (big_sepL_elem_of _ _ x with "Hlo") as "[Hcond Hpure]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hpure" as %Hcond. auto.
      + iDestruct (big_sepL_elem_of _ _ x with "Hhi") as "[Hcond Hpure]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hpure" as %Hcond. auto.
    - assert (addr_reg.min astk estk = estk) as ->;[solve_addr|].
      iDestruct (big_sepL_elem_of _ _ x with "Hlo") as "[Hcond Hpure]".
      { apply elem_of_region_addrs. solve_addr. }
      iDestruct "Hpure" as %Hcond. auto.
  Qed.

  (* lemma for opening a stack object from region, which may be either a heap object or an uninitialized stack object *)
  Lemma open_stack_object_pre_mid l l' W :
    NoDup l → l ## l' → (∀ a', a' ∈ l → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ open_region_many l' W ∗ ([∗ list] a' ∈ l, ∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∗ read_write_cond a' P ∗ rcond P interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ l;wps, a ↦ₐ wp)
                         ∗ ▷ (([∗ list] a;wp ∈ l;wps, a ↦ₐ wp) -∗ open_region_many l' W)
                    ∗ ([∗ list] a;wp ∈ l;wps, ⌜W.1 !! a = Some Permanent ∨ W.1 !! a = Some (Uninitialized wp)⌝).
  Proof.
    iIntros (Hdup Hdisj Hcond) "[Hsts [Hr #Hrels] ]".
    iInduction l as [|x l] "IH" forall (l' Hdisj).
    - iFrame. iExists []. auto.
    - apply NoDup_cons in Hdup as [Hnin Hdup].
      apply disjoint_cons in Hdisj as Hnin'.
      apply disjoint_swap in Hdisj;auto.
      iSimpl in "Hrels". iDestruct "Hrels" as "[Hx Hrels]".
      iDestruct "Hx" as "Hrel".
      destruct Hcond with x as [Hperm | [w Huninit] ];[constructor|..].
      + iDestruct "Hrel" as (P Hpers) "[Hrel Hrcond]".
        iDestruct (region_open_next_perm with "[$Hrel $Hsts $Hr]") as (v) "(Hsts & Hstate & Hr & Hx & #Hmono & #Hvalid)";auto.
        iDestruct ("IH" with "[] [] [] Hrels Hsts Hr") as "[Hsts Hws]";auto.
        { iPureIntro. intros a Ha. apply Hcond. constructor. auto. }
        iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond)". iExists (v :: wps).
        iFrame. iSplit;auto. iNext.
        iIntros "[Hx Hxs]". simpl.
        iDestruct ("Hcls" with "Hxs") as "Hr".
        iDestruct (region_close_next_perm with "[$Hstate $Hr $Hx]") as "Hr";auto. apply _.
      + iDestruct "Hrel" as (P Hpers) "[Hrel Hrcond]".
        iDestruct (region_open_next_monouninit_w with "[$Hrel $Hsts $Hr]") as "(Hr & Hsts & Hstate & Hx)";eauto.
        iDestruct ("IH" with "[] [] [] Hrels Hsts Hr") as "[Hsts Hws]";auto.
        { iPureIntro. intros a Ha. apply Hcond. constructor. auto. }
        iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond)". iExists (w :: wps).
        iFrame. iSplit;auto. iNext.
        iIntros "[Hx Hxs]". simpl.
        iDestruct ("Hcls" with "Hxs") as "Hr".
        iDestruct (region_close_next_uninit with "[$Hstate $Hr $Hx]") as "Hr";auto. apply _.
  Qed.

  Lemma open_stack_object_pre l W :
    NoDup l → (∀ a', a' ∈ l → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ region W ∗ ([∗ list] a' ∈ l, ∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∗ read_write_cond a' P ∗ rcond P interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ l;wps, a ↦ₐ wp) ∗ ▷ (([∗ list] a;wp ∈ l;wps, a ↦ₐ wp) -∗ region W)
                                                                       ∗ ([∗ list] a;wp ∈ l;wps, ⌜W.1 !! a = Some Permanent ∨ W.1 !! a = Some (Uninitialized wp)⌝).
  Proof.
    iIntros (Hdup Hcond) "[Hsts [Hr #Hrels] ]".
    iDestruct (region_open_nil with "Hr") as "Hr".
    iDestruct (open_stack_object_pre_mid with "[$Hsts $Hr]") as "[Hsts Hws]";eauto. apply disjoint_nil_r. exact (addr_reg.top). (*??*)
    iFrame. iDestruct "Hws" as (ws) "(?&HH&?)". iExists ws. iFrame. iNext. iIntros "H".
    iApply region_open_nil. iApply "HH". iFrame.
  Qed.

  Lemma open_stack_object W b e :
    (∀ a', (b <= a' < e)%a → (W.1 !! a' = Some Permanent ∨ (∃ w, W.1 !! a' = Some (Uninitialized w)))) →
    sts_full_world W ∗ region W ∗ ([∗ list] a' ∈ (region_addrs b e), ∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∗ read_write_cond a' P ∗ rcond P interp) -∗
    sts_full_world W ∗ ∃ wps, ([∗ list] a;wp ∈ (region_addrs b e);wps, a ↦ₐ wp) ∗ ▷ (([∗ list] a;wp ∈ (region_addrs b e);wps, a ↦ₐ wp) -∗ region W)
                                 ∗ ⌜Forall (λ awp, W.1 !! awp.1 = Some Permanent ∨ W.1 !! awp.1 = Some (Uninitialized awp.2)) (zip (region_addrs b e) wps)⌝.
  Proof.
    iIntros (Hcond) "[Hsts [Hr #Hrels] ]".
    iDestruct (open_stack_object_pre with "[$Hsts $Hr $Hrels]") as "[Hsts Hws]".
    apply region_addrs_NoDup.
    intros a' Hin. apply Hcond. apply elem_of_region_addrs. auto.
    iFrame. iDestruct "Hws" as (wps) "(Hws & Hcls & Hcond)". iExists _. iFrame.
    iDestruct (big_sepL2_alt with "Hcond") as "[% Hcond]".
    iDestruct (big_sepL_forall with "Hcond") as %Hforall. iPureIntro.
    apply Forall_forall. intros x [k Hx]%elem_of_list_lookup. eapply Hforall. eauto.
  Qed.

  (* After checking that the input stack object is all ints, we may need to re initialize it *)
  (* For this purpose we will need to define a merge operation for "conditionally" closing the world *)
  Fixpoint initialize_list l := λ W,
    match l with
    | [] => W
    | a :: l' => match W.1 !! a with
               | Some (Uninitialized _) => <s[a:=Monotemporary]s>(initialize_list l' W)
               | _ => initialize_list l' W
               end
    end.

  Lemma initialize_list_nin W l a :
    a ∉ l → (initialize_list l W).1 !! a = W.1 !! a.
  Proof.
    intros Hnin.
    induction l.
    - simpl;auto.
    - simpl. apply not_elem_of_cons in Hnin as [Hne Hnin].
      rewrite -IHl;auto. destruct (W.1 !! a0);auto.
      destruct r;auto. rewrite lookup_insert_ne//.
  Qed.

  Lemma initialize_list_perm W l a :
    W.1 !! a = Some Permanent → (initialize_list l W).1 !! a = W.1 !! a.
  Proof.
    intros Hnin.
    induction l.
    - simpl;auto.
    - simpl. destruct (decide (a0 = a));subst.
      + rewrite Hnin;auto. rewrite IHl. auto.
      + destruct (W.1 !! a0);auto. destruct r;auto. rewrite lookup_insert_ne//.
  Qed.

  Lemma initialize_list_in W l a w :
    a ∈ l → W.1 !! a = Some (Uninitialized w) → (initialize_list l W).1 !! a = Some Monotemporary.
  Proof.
    intros Hin Huninit.
    induction l;[inversion Hin|].
    simpl. apply elem_of_cons in Hin as [-> | Hin].
    - rewrite Huninit lookup_insert. auto.
    - destruct (W.1 !! a0);auto. destruct r;auto.
      destruct (decide (a = a0));subst;[rewrite lookup_insert|rewrite lookup_insert_ne//];auto.
  Qed.

  Lemma related_sts_pub_a_world_monotemporary W W' i a :
    (std W !! i) = Some Monotemporary ->
    (i < a)%a →
    related_sts_a_world W W' a ->
    (std W' !! i) = Some Monotemporary.
  Proof.
    intros Hsta Hcond [ [Hdom1 Hrelated_std] _].
    assert (is_Some (std W' !! i)) as [y Hy].
    { apply elem_of_gmap_dom. assert (i ∈ dom (gset Addr) (std W));[apply elem_of_gmap_dom;eauto|]. set_solver. }
    eapply Hrelated_std in Hsta;[|eauto].
    apply rtc_implies with _ Rpub _ _ in Hsta.
    2: { intros. rewrite decide_False in H0;auto. solve_addr. }
    eapply std_rel_pub_rtc_Monotemporary in Hsta;[|eauto]. subst. auto.
  Qed.
  Lemma related_sts_pub_a_world_monotemporary_le W W' i a :
    (std W !! i) = Some Monotemporary ->
    (a <= i)%a →
    related_sts_a_world W W' a ->
    (std W' !! i) = Some Monotemporary ∨ (∃ w, (std W' !! i) = Some (Uninitialized w)).
  Proof.
    intros Hsta Hcond [ [Hdom1 Hrelated_std] _].
    assert (is_Some (std W' !! i)) as [y Hy].
    { apply elem_of_gmap_dom. assert (i ∈ dom (gset Addr) (std W));[apply elem_of_gmap_dom;eauto|]. set_solver. }
    eapply Hrelated_std in Hsta;[|eauto].
    apply rtc_implies with _ (λ x y, Rpub x y ∨ Rpubp x y) _ _ in Hsta.
    2: { intros. rewrite decide_True in H0;auto. }
    eapply std_rel_pub_plus_rtc_Monotemporary_or_Uninitialized in Hsta;[|eauto].
    destruct Hsta as [? | [? ?] ];subst;eauto.
  Qed.
  Lemma related_sts_pub_a_world_uninitialized W W' w i a :
    (std W !! i) = Some (Uninitialized w) ->
    (i < a)%a →
    related_sts_a_world W W' a ->
    (std W' !! i) = Some Monotemporary ∨ (std W' !! i) = Some (Uninitialized w).
  Proof.
    intros Hsta Hcond [ [Hdom1 Hrelated_std] _].
    assert (is_Some (std W' !! i)) as [y Hy].
    { apply elem_of_gmap_dom. assert (i ∈ dom (gset Addr) (std W));[apply elem_of_gmap_dom;eauto|]. set_solver. }
    eapply Hrelated_std in Hsta;[|eauto].
    apply rtc_implies with _ Rpub _ _ in Hsta.
    2: { intros. rewrite decide_False in H0;auto. solve_addr. }
    eapply std_rel_pub_rtc_Uninitialized in Hsta as [Hsta | Hsta];[..|eauto]. subst. auto.
    subst. auto.
  Qed.
  Lemma related_sts_pub_a_world_uninitialized_le W W' w i a :
    (std W !! i) = Some (Uninitialized w) ->
    (a <= i)%a →
    related_sts_a_world W W' a ->
    (std W' !! i) = Some Monotemporary ∨ (∃ w', (std W' !! i) = Some (Uninitialized w')).
  Proof.
    intros Hsta Hcond [ [Hdom1 Hrelated_std] _].
    assert (is_Some (std W' !! i)) as [y Hy].
    { apply elem_of_gmap_dom. assert (i ∈ dom (gset Addr) (std W));[apply elem_of_gmap_dom;eauto|]. set_solver. }
    eapply Hrelated_std in Hsta;[|eauto].
    apply rtc_implies with _ (λ x y, Rpub x y ∨ Rpubp x y) _ _ in Hsta.
    2: { intros. rewrite decide_True in H0;auto. }
    eapply std_rel_pub_plus_rtc_Uninitialized in Hsta as [Hsta | [? Hsta] ];[..|eauto]. subst. auto.
    subst. eauto.
  Qed.
  Lemma related_sts_pub_world_uninitialized W W' w i :
    (std W !! i) = Some (Uninitialized w) ->
    related_sts_pub_world W W' ->
    (std W' !! i) = Some Monotemporary ∨ (std W' !! i) = Some (Uninitialized w).
  Proof.
    intros Hsta [ [Hdom1 Hrelated_std] _].
    assert (is_Some (std W' !! i)) as [y Hy].
    { apply elem_of_gmap_dom. assert (i ∈ dom (gset Addr) (std W));[apply elem_of_gmap_dom;eauto|]. set_solver. }
    eapply Hrelated_std in Hsta;[|eauto].
    eapply std_rel_pub_rtc_Uninitialized in Hsta as [Hsta | Hsta];[..|eauto]. subst. auto.
    subst. auto.
  Qed.


  Lemma open_parameter lframe a_param af3 actw
        W1 bsec esec m af2 b_r_adv frame_end (W W' : WORLD)
        (bstk estk astk : Addr) m' a14 a15 :
    (lframe = list_to_map (zip (a_param :: region_addrs af3 b_r_adv) (inl 2%Z :: actw))) →
    (W1 = initialize_list (region_addrs bsec esec)
             (std_update_multiple
                (std_update_multiple (uninitialize W m) (a_param :: region_addrs af3 b_r_adv) (Monostatic lframe))
                (af2 :: region_addrs b_r_adv frame_end) Revoked)) →
    region_addrs bsec esec ## region_addrs a_param estk →
    (12%nat + 2%nat < estk - bstk)%Z →
    (bstk + 2%nat ≤ astk)%Z →
    (bstk + 2%nat)%a = Some a_param →
    (a_param + 1)%a = Some af2 →
    (af2 + 1)%a = Some af3 →
    (af3 + 7)%a = Some b_r_adv →
    (b_r_adv + 1)%a = Some a14 →
    (a14 + 1)%a = Some a15 →
    length (a_param :: region_addrs af3 b_r_adv) ≤ length (inl 2%Z :: actw) →

    (∀ a' : Addr,
        is_Some (m !! a')
                ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    (∀ a' : Addr,
        is_Some (m' !! a')
                ↔ std W' !! a' = Some Monotemporary ∧ (bstk <= a')%a) →

    related_sts_a_world
      (<s[a15:=Monotemporary]s>(<s[a14:=Monotemporary]s>
                                (<s[af2:=Monotemporary]s>
                                 (<s[b_r_adv:=Monotemporary]s>W1)))) W' b_r_adv →


    interp W (inr (URWLX, Directed, bstk, estk, astk)) -∗

    □ ([∗ map] a16↦w7 ∈ m, □ ∃ (φ0 : WORLD * Word → iPropI Σ),
        ⌜∀ Wv : WORLD * Word, Persistent (φ0 Wv)⌝
        ∗ monotemp_pers_resources W φ0 a16 w7 ∗ rel a16 φ0) -∗
    □ ([∗ map] a16↦w7 ∈ m', □ ∃ (φ0 : WORLD * Word → iPropI Σ),
        ⌜∀ Wv : WORLD * Word, Persistent (φ0 Wv)⌝
        ∗ monotemp_pers_resources W' φ0 a16 w7 ∗ rel a16 φ0) -∗
    ∃ w, ⌜(override_uninitialize lframe (uninitialize W' m')).1 !! bstk = Some (Uninitialized w)⌝
       ∗ ▷ ((∀ Wfinal, ⌜related_sts_a_world W Wfinal bstk⌝ -∗ interp Wfinal w)
         ∨ (∀ Wfinal, ⌜related_sts_a_world W' Wfinal bstk⌝ -∗ interp Wfinal w)).
  Proof.
    iIntros (Heq1 Heq2 Hdisj Hsize Hbsk1 Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hlen Hmcond Hmcond' Hrelated)
            "#Hval #Hmcond #Hmcond'".
    iDestruct (writeLocalAllowedU_valid_cap_below_implies _ _ _ _ _ _ bstk with "Hval") as %Hmono;auto.
    { apply le_addr_withinBounds. all: solve_addr. }
    { solve_addr. }
    iDestruct (read_allowedU_inv _ bstk with "Hval") as "Hrel";[|auto|].
    { solve_addr. }
    assert (is_Some (m !! bstk)) as [w Hw].
    { apply Hmcond. split;auto. solve_addr. }
    assert (W1.1 !! bstk = Some (Uninitialized w) ∨ W1.1 !! bstk = Some Monotemporary) as Hbstk.
    { rewrite Heq2. destruct (decide (bstk ∈ region_addrs bsec esec)).
      - right. apply initialize_list_in with w;auto.
        erewrite std_sta_update_multiple_lookup_same_i.
        erewrite std_sta_update_multiple_lookup_same_i.
        apply uninitialize_std_sta_lookup_in;auto.
        apply not_elem_of_cons. rewrite elem_of_region_addrs. split;solve_addr.
        apply not_elem_of_cons. rewrite elem_of_region_addrs. split;try solve_addr.
      - left. rewrite initialize_list_nin//.
        erewrite std_sta_update_multiple_lookup_same_i.
        erewrite std_sta_update_multiple_lookup_same_i.
        apply uninitialize_std_sta_lookup_in;auto.
        apply not_elem_of_cons. rewrite elem_of_region_addrs. split;solve_addr.
        apply not_elem_of_cons. rewrite elem_of_region_addrs. split;try solve_addr. }
    assert (W1.1 !! bstk = Some (Uninitialized w) ∧ W'.1 !! bstk = Some (Uninitialized w)
            ∨ W'.1 !! bstk = Some Monotemporary) as Hbstk'.
    { destruct Hbstk as [Hbstk | Hbstk].
      - apply related_sts_pub_a_world_uninitialized with (w:=w) (i:=bstk) in Hrelated as [? | ?];auto.
        repeat (rewrite lookup_insert_ne;[|clear -Ha_param Haf3 Haf2 Hb_r_adv Hparam1 Hparam2;solve_addr]). auto.
        clear -Ha_param Haf3 Haf2 Hb_r_adv. solve_addr.
      - apply related_sts_pub_a_world_monotemporary with (i:=bstk) in Hrelated;auto.
        repeat (rewrite lookup_insert_ne;[|clear -Ha_param Haf3 Haf2 Hb_r_adv Hparam1 Hparam2;solve_addr]). auto.
        clear -Ha_param Haf3 Haf2 Hb_r_adv. solve_addr. }
    destruct Hbstk' as [ [Hbstk' Hbstk''] | Hbstk'].
    - iDestruct (big_sepM_delete with "Hmcond") as "[Hbstk Hmcond_del]";[apply Hw|].
      iDestruct "Hbstk" as (φ' Hpers) "[Hres #Hrel']".
      iDestruct (rel_agree _ (λ Wv, interp Wv.1 Wv.2) with "[$Hrel' $Hrel]") as "Heq".
      iExists w. iSplit.
      + rewrite override_uninitialize_std_sta_lookup_none.
        iPureIntro. rewrite uninitialize_std_sta_not_elem_of_lookup//.
        intros [Hcontr _]%elem_of_gmap_dom%Hmcond'. by rewrite Hbstk'' in Hcontr.
        rewrite Heq1. apply not_elem_of_list_to_map. rewrite fst_zip//.
        apply not_elem_of_cons;split;[clear -Ha_param;solve_addr|].
        rewrite elem_of_region_addrs. clear -Ha_param Haf3 Haf2 Hb_r_adv. solve_addr.
      + iNext. iLeft. iIntros (Wfinal Hrelateda). iSpecialize ("Heq" $! (Wfinal,w)).
        iDestruct "Hres" as "[Hmono Hres]". iSimpl in "Hmono".
        iSimpl in "Heq". rewrite /interp. iSimpl. iRewrite ("Heq").
        iApply "Hmono";eauto.
    - assert (is_Some (m' !! bstk)) as [w' Hw'].
      { apply Hmcond'. split;auto. clear;solve_addr. }
      iExists w'.
      iDestruct (big_sepM_delete with "Hmcond'") as "[Hbstk Hmcond_del]";[apply Hw'|].
      iDestruct "Hbstk" as (φ' Hpers) "[Hres #Hrel']".
      iDestruct (rel_agree _ (λ Wv, interp Wv.1 Wv.2) with "[$Hrel' $Hrel]") as "Heq". iSplit.
      + rewrite override_uninitialize_std_sta_lookup_none.
        iPureIntro. apply uninitialize_std_sta_lookup_in;auto.
        rewrite Heq1. apply not_elem_of_list_to_map. rewrite fst_zip//.
        apply not_elem_of_cons;split;[clear -Ha_param;solve_addr|].
        rewrite elem_of_region_addrs. clear -Ha_param Haf3 Haf2 Hb_r_adv. solve_addr.
      + iNext. iRight. iIntros (Wfinal Hrelateda). iSpecialize ("Heq" $! (Wfinal,w')).
        iDestruct "Hres" as "[Hmono Hres]". iSimpl in "Hmono".
        iSimpl in "Heq". rewrite /interp. iSimpl. iRewrite ("Heq").
        iApply "Hmono";eauto.
  Qed.

  Lemma uninitialize_std_sta_lookup_perm :
    ∀ (i : Addr) (m : Mem) (fs : STS_STD), fs !! i = Some Permanent <-> uninitialize_std_sta m fs !! i = Some Permanent.
  Proof.
    intros i m fs. split;intros Hperm.
    - rewrite uninitialize_std_sta_spec Hperm.
      destruct (m !! i);auto.
    - rewrite uninitialize_std_sta_spec in Hperm.
      destruct (fs !! i);auto. destruct (m !! i); auto.
      inversion Hperm. destruct r;inversion H1. auto.
  Qed.

  Definition sec_res W m bsec esec : iProp Σ :=
    ([∗ list] asec ∈ region_addrs bsec esec, ∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
                                              ∗ read_write_cond asec P
                                              ∗ (□ (∀ W (w : Word), P W w -∗ interp W w))
                                              ∗ (□ (∀ W1 W2 (z : Z), P W1 (inl z) -∗ P W2 (inl z)))
                                              ∗ (□ (∀ w', ⌜(uninitialize W m).1 !! asec = Some (Uninitialized w')⌝
                                                   -∗ monotemp_pers_resources W (λ Wv, P Wv.1 Wv.2) asec w')))%I.

  Lemma pers_res_to_sec_res W m bsec esec l p :
    (∀ a' : Addr,
        is_Some (m !! a')
                ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
     (▷ □ ([∗ map] a16↦w7 ∈ m, □ ∃ (φ0 : WORLD * Word → iPropI Σ),
        ⌜∀ Wv : WORLD * Word, Persistent (φ0 Wv)⌝
                                         ∗ monotemp_pers_resources W φ0 a16 w7 ∗ rel a16 φ0)) -∗
    region_conditions W l p bsec esec -∗
    (▷ ▷ sec_res W m bsec esec).
  Proof.
    iIntros (Hmcond) "#Hm #Hcond".
    rewrite /sec_res.
    iApply big_sepL_later. iApply big_sepL_forall. iIntros (k x Hin).
    assert (x ∈ region_addrs bsec esec) as Hin';[apply elem_of_list_lookup;eauto|].
    iDestruct (big_sepL_elem_of with "Hcond") as "[Hrel Hpwl]";[eauto|].
    iDestruct "Hpwl" as %Hpwl.
    assert (W.1 !! x = Some Monotemporary ∨ W.1 !! x = Some Permanent) as Hp.
    { destruct (pwl l); auto. destruct p;auto. }
    destruct Hp as [Hmono | Hperm].
    - assert (is_Some (m !! x)) as [w Hw].
      { apply Hmcond. split;auto. solve_addr. }
      destruct (writeAllowed l) eqn:Hwa.
      + iDestruct (big_sepM_lookup with "Hm") as "H";[eauto|].
        rewrite (bi.later_intuitionistically (∃ _, _)%I).
        iRevert "H". rewrite bi.later_exist. iIntros "#H".
        iDestruct "H" as (P) "(>Hpers & [Hφ Hmonoa] & Hrela)".
        iDestruct "Hpers" as %Hpers.
        iNext.
        iDestruct (rel_agree _ (λ Wv, interp Wv.1 Wv.2)  with "[Hrel Hrela]") as "Heq".
        rewrite /read_write_cond.
        iSplit;[iFrame "Hrel"|iExact "Hrela"].
        simpl. iNext.
        iExists interp. iSplit;[iPureIntro;apply _|].
        iFrame "Hrel". iSplit;[auto|]. iSplit.
        * iModIntro. iIntros (W1 W2 z) "_". rewrite !fixpoint_interp1_eq. done.
        * iModIntro. iIntros (w'). rewrite (uninitialize_std_sta_lookup_in _ _ _ w);auto.
          iIntros (Heq). inversion Heq;subst w'. rewrite /monotemp_pers_resources /=.
          iSplit.
          { iModIntro. iIntros (W1 W2 Hrelated). simpl.
            iDestruct ("Heq" $! (W1,w)) as "Heq1".
            iDestruct ("Heq" $! (W2,w)) as "Heq2".
            simpl. iRewrite "Heq1". iRewrite "Heq2". iIntros "Ha". iApply "Hφ";eauto. }
          { iSpecialize ("Heq" $! (W,w)). simpl. iRewrite "Heq". iExact "Hmonoa". }
      + iDestruct "Hrel" as (P) "(Hpers & (Hrcond & Hints) & Hrel)".
        iDestruct (big_sepM_lookup with "Hm") as (φ) "[Hpers' [[Hφ Hmonoa] Hrela]]";[eauto|].
        iNext.
        iDestruct (rel_agree _ (λ Wv, P Wv.1 Wv.2)  with "[Hrel Hrela]") as "Heq".
        iSplit;[iExact "Hrel"|iExact "Hrela"].
        iNext. iExists P. iSplit;[auto|]. iFrame "Hrel". iFrame "Hrcond". iFrame "Hints".
        iModIntro. iIntros (w'). rewrite (uninitialize_std_sta_lookup_in _ _ _ w);auto.
        iIntros (Heq). inversion Heq;subst w'. rewrite /monotemp_pers_resources /=. iSplit.
        * iModIntro. iIntros (W1 W2 z). simpl.
          iDestruct ("Heq" $! (W1,w)) as "Heq1".
          iDestruct ("Heq" $! (W2,w)) as "Heq2".
          simpl. iRewrite "Heq1"; iRewrite "Heq2". iIntros "Ha". iApply "Hφ";eauto.
        * iDestruct ("Heq" $! (W,w)) as "Heq1". simpl. iRewrite "Heq1". iExact "Hmonoa".
    - assert (m !! x = None) as Hnon.
      { apply eq_None_not_Some. intros [Hcontr _]%Hmcond. rewrite Hperm in Hcontr. done. }
      destruct (writeAllowed l) eqn:Hwa.
      + iNext. iNext. iExists interp. iSplit;[iPureIntro;apply _|].
        iFrame "Hrel". iSplit;[auto|].
        iSplit.
        { iModIntro. iIntros (W1 W2 z) "_". rewrite fixpoint_interp1_eq. done. }
        iModIntro. iIntros (w'). rewrite uninitialize_std_sta_None_lookup;auto.
        rewrite Hperm. iIntros (Hcontr);inversion Hcontr.
      + iDestruct "Hrel" as (P Hpers) "[(Hrcond & Hints) Hrel]".
        iNext. iNext. iExists P. iFrame "# %".
        iModIntro. iIntros (w'). rewrite uninitialize_std_sta_None_lookup;auto.
        rewrite Hperm. iIntros (Hcontr);inversion Hcontr.
  Qed.

  Lemma close_stack_object_mid W E m la1 la2 ρ wps l p bsec esec asec lsec :
    (bsec <= asec)%a →
    lsec = region_addrs asec esec →
    length (region_addrs bsec esec) = length wps →
    Forall (λ w : (Z + Cap), ∃ z : Z, w = inl z) wps →
    Forall (λ awp : Addr * Word,
                    (uninitialize W m).1 !! awp.1 = Some Permanent ∨ (uninitialize W m).1 !! awp.1 = Some (Uninitialized awp.2))
           (zip (region_addrs bsec esec) wps) →
    (∀ a' : Addr,
        is_Some (m !! a')
                ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →

    region_addrs bsec esec ## (la1 ++ la2) →

    region_conditions W l p bsec esec -∗

    sec_res W m bsec esec -∗
    sts_full_world (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked) -∗
    region (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked) ={E}=∗

    (sts_full_world (initialize_list lsec (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)) ∗
    region (initialize_list lsec (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked))).
  Proof.
    iIntros (Hle Heq Hlen Hints Hwps Hmcond Hdisj) "#Hcond #Hmono Hsts Hr".
    iInduction (lsec) as [|a lsec] "IH" forall (asec Heq Hle).
    - iModIntro. iSimpl. iFrame.
    - assert (asec < esec)%a as Hlt.
      { destruct (decide (esec <= asec))%a;[|solve_addr]. apply region_addrs_empty in l0. rewrite l0 in Heq. inversion Heq. }
      rewrite region_addrs_cons // in Heq.
      destruct (asec + 1)%a eqn:Hasec;[|exfalso;solve_addr].
      simpl in Heq. assert (a = asec) as Heqa;[inversion Heq;auto|subst a].
      assert (asec ∈ region_addrs bsec esec) as Hin.
      { apply elem_of_region_addrs. solve_addr. }
      apply elem_of_disjoint in Hdisj as Hlookup.
      apply Hlookup in Hin as Hnin. apply not_elem_of_app in Hnin as [Hnin1 Hnin2].
      rewrite /= std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//.
      assert (∃ wp, (asec,wp) ∈ zip (region_addrs bsec esec) wps) as [wp Hinwp].
      { apply elem_of_list_lookup in Hin as [k Hk].
        assert ((zip (region_addrs bsec esec) wps).*1 !! k = Some asec).
        { rewrite fst_zip;[|lia]. auto. }
        apply list_lookup_fmap_inv in H0 as [ [a' wp] [Hsubst Hy] ]. inversion Hsubst;subst.
        exists wp. apply elem_of_list_lookup;eauto. }
      revert Hwps; rewrite Forall_forall =>Hwps. apply Hwps in Hinwp as Hstate. simpl in Hstate.
      destruct Hstate as [Hperm | Huninit].
      + (* If the address is permanent, the world will not change *)
        rewrite Hperm. iMod ("IH" $! a0 with "[] [] Hsts Hr") as "[$ $]". inversion Heq;auto. iPureIntro;solve_addr. auto.
      + (* If the address is uninitialized, we need to reinitialise it using the ints assumption *)
        rewrite Huninit. iMod ("IH" $! a0 with "[] [] Hsts Hr") as "[Hsts Hr]". inversion Heq;auto. iPureIntro;solve_addr.
        (* get the read_write condition for asec *)
        iDestruct (big_sepL_elem_of with "Hcond") as "[_ Hasec]";[apply Hin|].
        assert (asec ∉ lsec) as Hnin.
        { inversion Heq. intros Hcontr%elem_of_region_addrs. solve_addr. }
        (* open the world to get the resource *)
        iDestruct "Hasec" as %Hasec'.

        iDestruct (big_sepL_elem_of with "Hmono") as (P Hpers) "(Hrel & Hrcond & Hints & Hif)";[eauto|].
        iSpecialize ("Hif" $! _ Huninit). iDestruct "Hif" as "[ Hmonoa HP]". simpl.

        assert (W.1 !! asec = Some Monotemporary) as Hmono.
        { destruct (pwl l);auto. rewrite /region_state_nwl in Hasec'.
          destruct p;auto.
          all: revert Hasec'; rewrite (uninitialize_std_sta_lookup_perm _ m) =>Hasec'.
          all: rewrite Huninit in Hasec';inversion Hasec';auto. done. }
        assert (is_Some(m !! asec)) as [w' Hw'].
        { apply Hmcond. split;auto. clear; solve_addr. }
        eapply uninitialize_std_sta_lookup_in in Hmono;eauto.
        rewrite Hmono in Huninit. inversion Huninit;subst wp.

        iDestruct (region_open_uninitialized with "[$Hr $Hsts $Hrel]") as "(Hr & Hsts & Hstate & Hl)".
        { rewrite initialize_list_nin// std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//. }
        (* assert that wp.1 is an int *)
        apply elem_of_zip_r in Hinwp.

        revert Hints;rewrite Forall_forall =>Hints. apply Hints in Hinwp as [z Hz].
        simpl in Hz. subst w'.
        (* we can now close the world again and update its state to temp *)
        iMod (region_close_mono_uninit_w with "[$Hr $Hsts $Hstate $Hl $Hrel]") as "[$ $]";auto.
        iSplitR.
        * iModIntro. iIntros (W0 W' Hrelated) "_ /=". iApply "Hmonoa". eauto.
          iApply "Hints". eauto.
        * iModIntro. simpl. iApply "Hints". eauto.
  Qed.

  Lemma close_stack_object W E m la1 la2 ρ wps l p bsec esec asec :
    (if pwl l then p = Directed else True) →
    readAllowed l →
    length (region_addrs bsec esec) = length wps →
    Forall (λ w : (Z + Cap), ∃ z : Z, w = inl z) wps →
    Forall (λ awp : Addr * Word,
                    (uninitialize W m).1 !! awp.1 = Some Permanent ∨ (uninitialize W m).1 !! awp.1 = Some (Uninitialized awp.2))
           (zip (region_addrs bsec esec) wps) →
    (∀ a' : Addr,
        is_Some (m !! a')
                ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →

    region_addrs bsec esec ## (la1 ++ la2) →

    region_conditions W l p bsec esec -∗
    sec_res W m bsec esec -∗
    sts_full_world (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked) -∗
    region (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked) ={E}=∗

    sts_full_world (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)) ∗
    region (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)) ∗
    interp (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) la1 ρ) la2 Revoked)) (inr (l, p, bsec, esec, asec)).
  Proof.
    iIntros (Hmono Hra Hlen Hints Hwps Hmcond Hdisj) "#Hcond #Hmono Hsts Hr".
    iMod (close_stack_object_mid with "Hcond Hmono Hsts Hr") as "[$ $]";eauto. solve_addr.
    iModIntro. rewrite fixpoint_interp1_eq /=.
    assert (forall k y, region_addrs bsec esec !! k = Some y → ∃ wp, (y,wp) ∈ zip (region_addrs bsec esec) wps) as Hinwp.
    { intros k y Hlook.
      assert ((zip (region_addrs bsec esec) wps).*1 !! k = Some y).
      { rewrite fst_zip;[|lia]. auto. }
      apply list_lookup_fmap_inv in H0 as [ [a' wp] [Hsubst Hy] ]. inversion Hsubst;subst.
      exists wp. apply elem_of_list_lookup;eauto. }
    destruct l;inversion Hra.
    3,6: destruct p;inversion Hmono.
    all: try iApply (big_sepL_mono with "Hcond").
    all: iIntros (k y Hk) "Hres /=".
    all: iDestruct "Hres" as "(Hrel & %)".
    all: try (iDestruct "Hrel" as (P) "[? ?]").
    1,5: iExists P;iFrame.
    all: try (iFrame).
    all: revert Hwps;rewrite Forall_forall =>Hwps.
    all: assert (y ∈ region_addrs bsec esec) as Hy;[apply elem_of_list_lookup;eauto|].
    all: apply Hinwp in Hk as [ w Hiny].
    all: apply Hwps in Hiny; simpl in Hiny.
    all: apply elem_of_disjoint in Hdisj.
    all: apply Hdisj in Hy as Hny;apply not_elem_of_app in Hny as [Hy1 Hy2].
    all: rewrite /region_state_nwl /region_state_pwl_mono.
    1,2,3,6: destruct p;simpl in *.
    all: try (apply uninitialize_std_sta_lookup_perm with (m:=m) in H0).
    all: try (rewrite initialize_list_perm;by rewrite std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//).
    5,6: destruct Hiny as [Hiny | Hiny];
      [apply uninitialize_std_sta_lookup_perm in Hiny; congruence
      |rewrite (initialize_list_in _ _ _ w)// std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//].
    all: destruct Hiny as [Hiny | Hiny];
      [iRight;rewrite initialize_list_perm// std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//
      |iLeft;rewrite (initialize_list_in _ _ _ w)// std_sta_update_multiple_lookup_same_i// std_sta_update_multiple_lookup_same_i//].
  Qed.

  Lemma uninitialize_revoke_condition W m :
    (∀ a' : Addr, is_Some (m !! a') ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    revoke_condition (uninitialize W m).
  Proof.
    intros Hforall. intros a.
    destruct (m !! a) eqn:Hsome.
    - assert (is_Some (m !! a)) as HisSome;[eauto|]. apply Hforall in HisSome as [Hmono _].
      eapply uninitialize_std_sta_lookup_in in Hsome;eauto. rewrite Hsome. auto.
    - apply uninitialize_std_sta_None_lookup with (m:=W.1) in Hsome as Heq. rewrite Heq.
      intros Hcontr. assert (is_Some (m !! a)) as [? HisSome];[|congruence].
      apply Hforall. split;auto. solve_addr.
  Qed.

  Lemma read_allowedU_inv_range W p g b e a b' e' :
    (b <= b' ∧ e' < e)%a → readAllowedU p = true →
    interp W (inr (p,g,b,e,a)) -∗
    [∗ list] a ∈ region_addrs b' e', read_write_cond a interp.
  Proof.
    iIntros ([Hle Hlt] HraU) "Hv".
    iApply big_sepL_forall. iIntros (k x Hin).
    assert (x ∈ region_addrs b' e') as [Hle' Hlt']%elem_of_region_addrs.
    { apply elem_of_list_lookup;eauto. }
    iDestruct (read_allowedU_inv _ x with "Hv") as "Hcond";auto. solve_addr.
  Qed.

  Lemma world_eq W W' :
    W = W' <-> W.1 = W'.1 ∧ W.2 = W'.2.
  Proof.
    destruct W as [Wstd Wloc]; destruct W' as [Wstd' Wloc']; simpl.
    split;intros Heq.
    - inversion Heq. auto.
    - destruct Heq as [-> ->]. auto.
  Qed.

  Lemma initialize_list_loc W l :
    (initialize_list l W).2 = W.2.
  Proof.
    induction l;auto.
    simpl. destruct (W.1 !! a);auto. destruct r;auto.
  Qed.

  Lemma initialize_list_nuninit W l a :
    (∀ w, W.1 !! a ≠ Some (Uninitialized w)) → (initialize_list l W).1 !! a = W.1 !! a.
  Proof.
    intros Hnin.
    induction l.
    - simpl;auto.
    - simpl. destruct (decide (a0 = a));subst.
      + destruct (W.1 !! a) eqn:Hsome;auto.
        destruct r;auto. congruence.
      + destruct (W.1 !! a0);auto. destruct r;auto. rewrite lookup_insert_ne//.
  Qed.

  Lemma initialize_list_commute l W x ρ :
    (∀ w, ρ ≠ Uninitialized w) →
    (<s[x:=ρ]s>(initialize_list l W)) = (initialize_list l (<s[x:=ρ]s> W)).
  Proof.
    intros Hne. rewrite /std_update /=.
    apply world_eq. split;[|rewrite !initialize_list_loc;auto].
    induction l;auto.
    simpl. destruct (decide (x = a)).
    - subst. rewrite lookup_insert.
      destruct (W.1 !! a) eqn:Hsome;auto.
      all: destruct ρ;try congruence;auto.
      all: destruct r;auto. all: rewrite insert_insert;auto.
    - rewrite lookup_insert_ne//. destruct (W.1 !! a) eqn:Hsome;auto.
      all: rewrite Hsome//. destruct r;auto. simpl.
      rewrite insert_commute//. f_equiv. auto.
  Qed.

  Lemma initialize_list_twice l W x w :
    x ∈ l → W.1 !! x = Some (Uninitialized w) →
    (<s[x:=Monotemporary]s>(initialize_list l W)) = (initialize_list l W).
  Proof.
    intros Hin Huninit. rewrite /std_update /=.
    apply world_eq. split;[|rewrite !initialize_list_loc;auto].
    simpl. rewrite insert_id;auto. rewrite (initialize_list_in _ _ _ w);auto.
  Qed.

  Lemma initialize_list_related_pub l W :
    related_sts_pub_world W (initialize_list l W).
  Proof.
    induction l.
    - rewrite /initialize_list /=. destruct W. apply related_sts_pub_refl_world.
    - rewrite /initialize_list /=.
      destruct (std W !! a) eqn:Hsome;[|rewrite Hsome;eauto].
      rewrite Hsome. destruct r;simpl;auto.
      apply related_sts_pub_trans_world with (initialize_list l W); auto.
      split;[|apply related_sts_pub_refl].
      split.
      + simpl. rewrite dom_insert /close_list /=.
        apply union_subseteq_r.
      + rewrite /initialize_list /=.
        intros i x y Hx Hy.
        destruct (decide (i = a)); subst.
        ++ rewrite lookup_insert in Hy. inversion Hy.
           subst.
           destruct (decide (a ∈ l)).
           +++ apply initialize_list_in with (l:=l) in Hsome;auto.
               rewrite Hsome in Hx. inversion Hx. left.
           +++ rewrite -(initialize_list_nin _ l) in Hsome;auto.
               rewrite Hsome in Hx. inversion Hx. right with Monotemporary;[|left].
               constructor.
        ++ rewrite lookup_insert_ne in Hy; auto.
           rewrite Hx in Hy. inversion Hy. left.
  Qed.

  Lemma initialize_list_dom l W :
    dom (gset Addr) (std W) = dom (gset Addr) (std (initialize_list l W)).
  Proof.
    apply gset_leibniz. split.
    - intros [a Hin]%elem_of_gmap_dom.
      apply elem_of_gmap_dom. destruct (decide (x ∈ l)).
      + destruct a.
        all: try (by rewrite initialize_list_nuninit;eauto;rewrite Hin;auto).
        rewrite (initialize_list_in _ _ _ w);auto. eauto.
      + rewrite initialize_list_nin;eauto.
    - intros [a Hin]%elem_of_gmap_dom.
      apply elem_of_gmap_dom.
      destruct (W.1 !! x) eqn:Hsome;eauto.
      exfalso. destruct (decide (x ∈ l)).
      + rewrite initialize_list_nuninit in Hin;[congruence|].
        rewrite Hsome. auto.
      + rewrite initialize_list_nin in Hin;auto. congruence.
  Qed.

  Lemma stack_state_W2_params W2 a15 a14 af2 b_r_adv bsec esec W m a_param af3 lframe frame_end x (bstk estk : Addr) :
    W2 = <s[a15:=Monotemporary]s>
         (<s[a14:=Monotemporary]s>
          (<s[af2:=Monotemporary]s>
           (<s[b_r_adv:=Monotemporary]s>
            (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) (a_param :: region_addrs af3 b_r_adv) (Monostatic lframe)) (af2 :: region_addrs b_r_adv frame_end) Revoked))))) ->
    x ∈ region_addrs b_r_adv frame_end →
    (12%nat + 2%nat < estk - bstk)%Z →
    (bstk + 2%nat)%a = Some a_param →
    (a_param + 1)%a = Some af2 →
    (af2 + 1)%a = Some af3 →
    (af3 + 7)%a = Some b_r_adv →
    (b_r_adv + 1)%a = Some a14 →
    (a14 + 1)%a = Some a15 →
    (a15 + 1)%a = Some frame_end →
    region_addrs bsec esec ## region_addrs a_param estk →

    std W2 !! x = Some Monotemporary.
  Proof.
    intros HW2 Hin Hsize Hbstk Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsec_cond.
    subst W2. simpl.
    repeat (match goal with
              |- context [<[ ?a := _ ]> _] =>
              destruct (decide (x = a));[subst;rewrite lookup_insert;auto|rewrite lookup_insert_ne//]
            end).
    apply elem_of_region_addrs in Hin.
    assert (x ∉ region_addrs bsec esec) as Hnin.
    { apply elem_of_disjoint in Hsec_cond. intros Hcontr%Hsec_cond.
      apply Hcontr,elem_of_region_addrs. solve_addr. }
    rewrite initialize_list_nin//.
    assert (x ≠ af2) as Hne.
    { solve_addr. }
    rewrite lookup_insert_ne//.
    assert (region_addrs b_r_adv frame_end = [b_r_adv;a14;a15]) as ->.
    { rewrite region_addrs_cons;[|solve_addr]. rewrite Hb_r_adv /=.
      rewrite region_addrs_cons;[|solve_addr]. rewrite Hparam1 /=.
      rewrite region_addrs_cons;[|solve_addr]. rewrite Hparam2 /=.
      rewrite region_addrs_empty;[|solve_addr]. auto. }
    assert (a_param ≠ x).
    { solve_addr. }
    solve_addr.
  Qed.

  Lemma stack_state_W2 W2 a15 a14 af2 b_r_adv bsec esec W m a_param af3 lframe frame_end x (bstk estk : Addr) :
    W2 = <s[a15:=Monotemporary]s>
         (<s[a14:=Monotemporary]s>
          (<s[af2:=Monotemporary]s>
           (<s[b_r_adv:=Monotemporary]s>
            (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) (a_param :: region_addrs af3 b_r_adv) (Monostatic lframe)) (af2 :: region_addrs b_r_adv frame_end) Revoked))))) ->
    x ∈ region_addrs frame_end estk →
    (12%nat + 2%nat < estk - bstk)%Z →
    (bstk + 2%nat)%a = Some a_param →
    (a_param + 1)%a = Some af2 →
    (af2 + 1)%a = Some af3 →
    (af3 + 7)%a = Some b_r_adv →
    (b_r_adv + 1)%a = Some a14 →
    (a14 + 1)%a = Some a15 →
    (a15 + 1)%a = Some frame_end →
    region_addrs bsec esec ## region_addrs a_param estk →
    (∀ a' : Addr, is_Some (m !! a') ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    Forall (λ a0 : Addr, W.1 !! a0 = Some Monotemporary ∨ (∃ w : Word, W.1 !! a0 = Some (Uninitialized w))) (region_addrs a_param estk) →

    std W2 !! x = Some Monotemporary ∨ (∃ w : leibnizO Word, std W2 !! x = Some (Uninitialized w)).
  Proof.
    intros HW2 Hin Hsize Hbstk Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsec_cond Hmcond Hstk_cond.
    subst W2. simpl.
    repeat (match goal with
              |- context [<[ ?a := _ ]> _] =>
              destruct (decide (x = a));[subst;rewrite lookup_insert;auto|rewrite lookup_insert_ne//]
            end).
    apply elem_of_region_addrs in Hin.
    assert (x ∉ region_addrs bsec esec) as Hnin.
    { apply elem_of_disjoint in Hsec_cond. intros Hcontr%Hsec_cond.
      apply Hcontr,elem_of_region_addrs. solve_addr. }
    rewrite initialize_list_nin//.
    assert (x ≠ af2) as Hne.
    { solve_addr. }
    rewrite lookup_insert_ne//.
    assert (region_addrs b_r_adv frame_end = [b_r_adv;a14;a15]) as ->.
    { rewrite region_addrs_cons;[|solve_addr]. rewrite Hb_r_adv /=.
      rewrite region_addrs_cons;[|solve_addr]. rewrite Hparam1 /=.
      rewrite region_addrs_cons;[|solve_addr]. rewrite Hparam2 /=.
      rewrite region_addrs_empty;[|solve_addr]. auto. }
    assert (a_param ≠ x).
    { solve_addr. }
    simpl. rewrite !lookup_insert_ne//.
    rewrite std_sta_update_multiple_lookup_same_i.
    2: { rewrite elem_of_region_addrs. solve_addr. }
    revert Hstk_cond; rewrite Forall_forall =>Hstk_cond.
    destruct Hstk_cond with x as [Hmono | [w Hw] ].
    { apply elem_of_region_addrs. solve_addr. }
    - right. assert (is_Some (m !! x)) as [v Hv].
      { apply Hmcond. split;auto. clear; solve_addr. }
      exists v. apply uninitialize_std_sta_lookup_in;auto.
    - right. assert (m !! x = None) as Hnone.
      { apply eq_None_not_Some. intros [Hcontr _]%Hmcond.
        rewrite Hcontr in Hw. congruence. }
      rewrite uninitialize_std_sta_None_lookup//.
      eauto.
  Qed.

  (* Future worlds relation proofs needed in the example *)
  Lemma related_sts_priv1 W W2 lframe a15 a14 af2 af3 b_r_adv (bstk estk : Addr) bsec esec m a_param actw frame_end :
    lframe = list_to_map (zip (a_param :: (region_addrs af3 b_r_adv)) (inl 2%Z :: actw)) →

    W2 = <s[a15:=Monotemporary]s>
         (<s[a14:=Monotemporary]s>
          (<s[af2:=Monotemporary]s>
           (<s[b_r_adv:=Monotemporary]s>
            (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) (a_param :: region_addrs af3 b_r_adv) (Monostatic lframe)) (af2 :: region_addrs b_r_adv frame_end) Revoked))))) ->

    (∀ a' : Addr, is_Some (m !! a') ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    Forall (λ a0 : Addr, W.1 !! a0 = Some Monotemporary ∨ (∃ w : Word, W.1 !! a0 = Some (Uninitialized w)))
           (region_addrs a_param estk) →
    (12%nat + 2%nat < estk - bstk)%Z →
    (bstk + 2%nat)%a = Some a_param →
    (a_param + 1)%a = Some af2 →
    (af2 + 1)%a = Some af3 →
    (af3 + 7)%a = Some b_r_adv →
    length actw = 7 →
    (b_r_adv + 1)%a = Some a14 →
    (a14 + 1)%a = Some a15 →
    (a15 + 1)%a = Some frame_end →
    (∀ a' : Addr, (bsec <= a' < esec)%a → (uninitialize W m).1 !! a' = Some Permanent
                                         ∨ (∃ w : Word, (uninitialize W m).1 !! a' = Some (Uninitialized w))) →
    (∀ a' : Addr, (bsec <= a' < esec)%a → W.1 !! a' = Some Permanent
                                         ∨ W.1 !! a' = Some Monotemporary) →
    region_addrs bsec esec ## region_addrs a_param estk →

    related_sts_priv_world W W2.
  Proof.
    intros Heq1 -> Hmcond Hstk_cond Hsize Ha_param Haf2 Haf3 Hb_r_adv Hactlen Hparam1 Hparam2 Hparam3 Hsec_cond Hsec_cond' Hdisj.
    split;simpl.
    2: { rewrite initialize_list_loc. simpl. rewrite !std_update_multiple_loc /= !std_update_multiple_loc.
         apply related_sts_priv_refl. }
    rewrite std_update_multiple_insert_commute.
    2: { rewrite elem_of_region_addrs. solve_addr. }
    split.
    - rewrite !dom_insert_L -initialize_list_dom !dom_insert_L.
      trans (dom (gset Addr)
                       (std_update_multiple
                          (std_update_multiple (uninitialize W m) (region_addrs af3 b_r_adv) (Monostatic lframe))
                          (region_addrs b_r_adv frame_end) Revoked).1);[|set_solver].
      trans (dom (gset Addr) (uninitialize W m).1);[rewrite uninitialize_dom;auto|].
      etrans;[apply std_update_multiple_sta_dom_subseteq with (l:=region_addrs af3 b_r_adv) (ρ:=Monostatic lframe)|].
      etrans;[apply std_update_multiple_sta_dom_subseteq with (l:=region_addrs b_r_adv frame_end) (ρ:=Revoked)|].
      auto.
    - revert Hstk_cond; rewrite Forall_forall =>Hstk_cond.
      intros i x y Hx Hy.
      destruct (decide (i = a15));[subst;rewrite lookup_insert in Hy;simplify_eq|rewrite lookup_insert_ne// in Hy].
      { destruct Hstk_cond with a15 as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..];[|left|].
        apply elem_of_region_addrs. solve_addr. eright;[|left]. left. constructor. }
      destruct (decide (i = a14));[subst;rewrite lookup_insert in Hy;simplify_eq|rewrite lookup_insert_ne// in Hy].
      { destruct Hstk_cond with a14 as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..];[|left|].
        apply elem_of_region_addrs. solve_addr. eright;[|left]. left. constructor. }
      destruct (decide (i = af2));[subst;rewrite lookup_insert in Hy;simplify_eq|rewrite lookup_insert_ne// in Hy].
      { destruct Hstk_cond with af2 as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..];[|left|].
        apply elem_of_region_addrs. solve_addr. eright;[|left]. left. constructor. }
      destruct (decide (i = b_r_adv));[subst;rewrite lookup_insert in Hy;simplify_eq|rewrite lookup_insert_ne// in Hy].
      { destruct Hstk_cond with b_r_adv as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..];[|left|].
        apply elem_of_region_addrs. solve_addr. eright;[|left]. left. constructor. }

      destruct (decide (i ∈ (region_addrs bsec esec))).
      { assert (i ∉ region_addrs af3 b_r_adv ∧
                i ∉ region_addrs b_r_adv frame_end ∧
                a_param ≠ i ∧
                af2 ≠ i) as (? & ? & ? & ?).
        { repeat split. 1,2: rewrite elem_of_region_addrs. all: apply Hdisj in e.
          all: revert e; rewrite elem_of_region_addrs =>e. all: clear Hstk_cond Hdisj Hsec_cond; solve_addr. }
        destruct Hsec_cond' with i as [Hperm | Hmono];[apply elem_of_region_addrs;auto|..].
        - rewrite initialize_list_nuninit in Hy.
          rewrite !lookup_insert_ne// !std_sta_update_multiple_lookup_same_i// in Hy.
          + rewrite Hperm in Hx. revert Hperm; rewrite (uninitialize_std_sta_lookup_perm _ m) =>Hperm.
            rewrite Hy in Hperm. simplify_eq. left.
          + rewrite !lookup_insert_ne// !std_sta_update_multiple_lookup_same_i//.
            revert Hperm; rewrite (uninitialize_std_sta_lookup_perm _ m) =>Hperm.
            rewrite Hperm. auto.
        - assert (is_Some (m !! i)) as [v Hv].
          { apply Hmcond. split;auto. clear. solve_addr. }
          rewrite (initialize_list_in _ _ _ v)// in Hy. rewrite Hx in Hmono. simplify_eq. left.
          rewrite !lookup_insert_ne// !std_sta_update_multiple_lookup_same_i//.
          rewrite (uninitialize_std_sta_lookup_in _ _ _ v)//.
      }
      rewrite initialize_list_nin// in Hy.
      rewrite lookup_insert_ne// in Hy.
      destruct (decide (i = a_param));[subst;rewrite lookup_insert in Hy;simplify_eq|rewrite lookup_insert_ne// in Hy].
      { destruct Hstk_cond with a_param as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
        apply elem_of_region_addrs. solve_addr. eright;[|left]. right;right;constructor.
        right with Monotemporary. left;constructor. eright;[|left]. right;right;constructor. }

      assert (i ∉ region_addrs b_r_adv frame_end).
      { rewrite elem_of_region_addrs. clear -n n0 n2 Hparam1 Hparam2 Hparam3. solve_addr. }
      rewrite std_sta_update_multiple_lookup_same_i// in Hy.

      destruct (decide (i ∈ (region_addrs af3 b_r_adv))).
      { rewrite std_sta_update_multiple_lookup_in_i// in Hy.
        destruct Hstk_cond with i as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
        revert e; rewrite !elem_of_region_addrs =>e. solve_addr.
        all: simplify_eq. 2:right with Monotemporary. 1,3:eright;[|left];right;right;constructor.
        left;constructor. }

      rewrite std_sta_update_multiple_lookup_same_i// in Hy.

      destruct (m !! i) eqn:Hsome.
      { assert (is_Some (m !! i)) as Hissome;eauto. apply Hmcond in Hissome as [Hx' _].
        rewrite (uninitialize_std_sta_lookup_in _ _ _ w)// in Hy. rewrite Hx in Hx'. simplify_eq.
        eright;[|left]. right;left;constructor. }

      rewrite uninitialize_std_sta_None_lookup// in Hy. rewrite Hy in Hx. simplify_eq. left.
  Qed.

  Lemma override_uninitialize_std_sta_dom_subseteq m fs :
    dom (gset Addr) fs ⊆ dom (gset Addr) (override_uninitialize_std_sta m fs).
  Proof.
    induction m using map_ind.
    - rewrite override_uninitialize_std_sta_empty. auto.
    - rewrite override_uninitialize_std_sta_insert dom_insert_L. set_solver.
  Qed.

  Lemma related_sts_pub_a1 W W2 lframe a15 a14 af2 af3 b_r_adv (bstk estk : Addr) bsec esec m m' a_param actw frame_end W' Wfinal maddrs :
    lframe = list_to_map (zip (a_param :: (region_addrs af3 b_r_adv)) (inl 2%Z :: actw)) →

    W2 = <s[a15:=Monotemporary]s>
         (<s[a14:=Monotemporary]s>
          (<s[af2:=Monotemporary]s>
           (<s[b_r_adv:=Monotemporary]s>
            (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) (a_param :: region_addrs af3 b_r_adv) (Monostatic lframe)) (af2 :: region_addrs b_r_adv frame_end) Revoked))))) ->

    Wfinal = initialize_list maddrs (override_uninitialize lframe (uninitialize W' m')) →

    maddrs = filter (λ a : Addr, (a < bstk)%a) (elements (dom (gset Addr) m)) →

    related_sts_a_world W2 W' b_r_adv →

    (∀ a' : Addr, is_Some (m !! a') ↔ std W !! a' = Some Monotemporary ∧ (0 <= a')%a) →
    (∀ a' : Addr, is_Some (m' !! a') ↔ std W' !! a' = Some Monotemporary ∧ (bstk <= a')%a) →

    Forall (λ a0 : Addr, W.1 !! a0 = Some Monotemporary ∨ (∃ w : Word, W.1 !! a0 = Some (Uninitialized w)))
           (region_addrs a_param estk) →
    (12%nat + 2%nat < estk - bstk)%Z →
    (bstk + 2%nat)%a = Some a_param →
    (a_param + 1)%a = Some af2 →
    (af2 + 1)%a = Some af3 →
    (af3 + 7)%a = Some b_r_adv →
    length actw = 7 →
    (b_r_adv + 1)%a = Some a14 →
    (a14 + 1)%a = Some a15 →
    (a15 + 1)%a = Some frame_end →
    (∀ a' : Addr, (bsec <= a' < esec)%a → (uninitialize W m).1 !! a' = Some Permanent
                                         ∨ (∃ w : Word, (uninitialize W m).1 !! a' = Some (Uninitialized w))) →
    (∀ a' : Addr, (bsec <= a' < esec)%a → W.1 !! a' = Some Permanent
                                         ∨ W.1 !! a' = Some Monotemporary) →
    region_addrs bsec esec ## region_addrs a_param estk →

    related_sts_a_world W Wfinal bstk.
  Proof.
    intros Hlframe HW2 HWfinal Hmaddrs [ [Hsub1 Hrel1] Hrelated2 ] Hmcond Hmcond' Hstk_cond Hsize Ha_param Haf2 Haf3 Hb_r_adv Hactlen Hparam1 Hparam2 Hparam3 Hsec_cond Hsec_cond' Hdisj.
    assert (related_sts_priv_world W W2) as [ [Hsub _] _].
    { eapply related_sts_priv1;eauto. }
    split.
    2: { eapply related_sts_pub_plus_trans with (gs:=W'.2.1) (gr:=W'.2.2).
         apply related_sts_pub_plus_trans with (gs:=W2.2.1) (gr:=W2.2.2);auto.
         rewrite HW2 /std_update /=. rewrite initialize_list_loc. simpl.
         rewrite !std_update_multiple_loc /= !std_update_multiple_loc /uninitialize /loc /=.
         apply related_sts_pub_plus_refl.
         rewrite HWfinal. rewrite initialize_list_loc. simpl. apply related_sts_pub_plus_refl. }

    split.
    - trans (dom (gset Addr) W2.1);auto. trans (dom (gset Addr) W'.1);auto.
      rewrite HWfinal. rewrite -initialize_list_dom.
      etrans; [|apply override_uninitialize_std_sta_dom_subseteq].
      rewrite uninitialize_dom. auto.
    - revert Hstk_cond; rewrite Forall_forall =>Hstk_cond.
      intros i x y Hx Hy.
      assert (is_Some (W'.1 !! i)) as [y' Hy'].
      { apply elem_of_gmap_dom. apply Hsub1. apply Hsub. apply elem_of_gmap_dom. eauto. }
      clear Hsub Hsub1.
      specialize (Hrel1 i).

      destruct (decide (i = a15));[subst|].
      { rewrite lookup_insert in Hrel1. rewrite initialize_list_nin in Hy.
        2: { intros [Hcontr _]%elem_of_list_filter.
             clear -Hparam1 Hparam2 Hparam3 Ha_param Hb_r_adv Haf2 Haf3 Hcontr. solve_addr. }
        specialize (Hrel1 Monotemporary _ eq_refl Hy').
        apply rtc_implies with (Q:=λ x y : region_type, Rpub x y ∨ Rpubp x y) in Hrel1.
        2: { intros r q Hrq. rewrite decide_True in Hrq;auto.
             clear -Hparam1 Hparam2 Hparam3 Ha_param Hb_r_adv Haf2 Haf3. solve_addr. }
        apply std_rel_pub_plus_rtc_Monotemporary in Hrel1;auto.
        rewrite override_uninitialize_std_sta_lookup_none in Hy.
        2: { simpl. rewrite lookup_insert_ne; [|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
             apply not_elem_of_list_to_map. rewrite fst_zip. rewrite elem_of_region_addrs.
             2: rewrite Hactlen region_addrs_length /region_size.
             all: clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr. }
        destruct Hrel1 as [ Heq | [v Heq] ].
        - subst.
          assert (is_Some (m' !! a15)) as [v' Hv].
          { apply Hmcond'. split;auto. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr. }
          rewrite (uninitialize_std_sta_lookup_in _ _ _ v')// in Hy.
          destruct Hstk_cond with a15 as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
          apply elem_of_region_addrs. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsize; solve_addr.
          all: simplify_eq. 2: right with Monotemporary. 3,1: eright;[|left].
          all: rewrite decide_True;[|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
          1,2 : right;constructor. left;constructor.
        - assert (m' !! a15 = None) as Hnone.
          { apply eq_None_not_Some. intros [Hcontr _]%Hmcond'. subst. rewrite Hy' in Hcontr. done. }
          rewrite (uninitialize_std_sta_None_lookup)// in Hy. subst. rewrite Hy' in Hy. simplify_eq.
          destruct Hstk_cond with a15 as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
          apply elem_of_region_addrs. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsize; solve_addr.
          all: simplify_eq. 2: right with Monotemporary. 3,1: eright;[|left].
          all: rewrite decide_True;[|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
          1,2 : right;constructor. left;constructor. }

      subst W2. rewrite lookup_insert_ne// in Hrel1.
      destruct (decide (i = a14));[subst|].
      { rewrite lookup_insert in Hrel1. rewrite initialize_list_nin in Hy.
        2: { intros [Hcontr _]%elem_of_list_filter.
             clear -Hparam1 Hparam2 Hparam3 Ha_param Hb_r_adv Haf2 Haf3 Hcontr. solve_addr. }
        specialize (Hrel1 Monotemporary _ eq_refl Hy').
        apply rtc_implies with (Q:=λ x y : region_type, Rpub x y ∨ Rpubp x y) in Hrel1.
        2: { intros r q Hrq. rewrite decide_True in Hrq;auto.
             clear -Hparam1 Hparam2 Hparam3 Ha_param Hb_r_adv Haf2 Haf3. solve_addr. }
        apply std_rel_pub_plus_rtc_Monotemporary in Hrel1;auto.
        rewrite override_uninitialize_std_sta_lookup_none in Hy.
        2: { simpl. rewrite lookup_insert_ne; [|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
             apply not_elem_of_list_to_map. rewrite fst_zip. rewrite elem_of_region_addrs.
             2: rewrite Hactlen region_addrs_length /region_size.
             all: clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr. }
        destruct Hrel1 as [ Heq | [v Heq] ].
        - subst.
          assert (is_Some (m' !! a14)) as [v' Hv].
          { apply Hmcond'. split;auto. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr. }
          rewrite (uninitialize_std_sta_lookup_in _ _ _ v')// in Hy.
          destruct Hstk_cond with a14 as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
          apply elem_of_region_addrs. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsize; solve_addr.
          all: simplify_eq. 2: right with Monotemporary. 3,1: eright;[|left].
          all: rewrite decide_True;[|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
          1,2 : right;constructor. left;constructor.
        - assert (m' !! a14 = None) as Hnone.
          { apply eq_None_not_Some. intros [Hcontr _]%Hmcond'. subst. rewrite Hy' in Hcontr. done. }
          rewrite (uninitialize_std_sta_None_lookup)// in Hy. subst. rewrite Hy' in Hy. simplify_eq.
          destruct Hstk_cond with a14 as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
          apply elem_of_region_addrs. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsize; solve_addr.
          all: simplify_eq. 2: right with Monotemporary. 3,1: eright;[|left].
          all: rewrite decide_True;[|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
          1,2 : right;constructor. left;constructor. }

      rewrite lookup_insert_ne// in Hrel1.
      destruct (decide (i = af2));[subst|].
      { rewrite lookup_insert in Hrel1. rewrite initialize_list_nin in Hy.
        2: { intros [Hcontr _]%elem_of_list_filter.
             clear -Hparam1 Hparam2 Hparam3 Ha_param Hb_r_adv Haf2 Haf3 Hcontr. solve_addr. }
        specialize (Hrel1 Monotemporary _ eq_refl Hy').
        apply rtc_implies with (Q:=λ x y : region_type, Rpub x y) in Hrel1.
        2: { intros r q Hrq. rewrite decide_False in Hrq;auto.
             clear -Hparam1 Hparam2 Hparam3 Ha_param Hb_r_adv Haf2 Haf3. solve_addr. }
        apply std_rel_pub_rtc_Monotemporary in Hrel1;auto.
        rewrite override_uninitialize_std_sta_lookup_none in Hy.
        2: { simpl. rewrite lookup_insert_ne; [|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
             apply not_elem_of_list_to_map. rewrite fst_zip. rewrite elem_of_region_addrs.
             2: rewrite Hactlen region_addrs_length /region_size.
             all: clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr. }
        subst.
        assert (is_Some (m' !! af2)) as [v' Hv].
        { apply Hmcond'. split;auto. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr. }
        rewrite (uninitialize_std_sta_lookup_in _ _ _ v')// in Hy.
        destruct Hstk_cond with af2 as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
        apply elem_of_region_addrs. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsize; solve_addr.
        all: simplify_eq. 2: right with Monotemporary. 3,1: eright;[|left].
        all: rewrite decide_True;[|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
        1,2 : right;constructor. left;constructor. }

      rewrite lookup_insert_ne// in Hrel1.
      destruct (decide (i = b_r_adv));[subst|].
      { rewrite lookup_insert in Hrel1. rewrite initialize_list_nin in Hy.
        2: { intros [Hcontr _]%elem_of_list_filter.
             clear -Hparam1 Hparam2 Hparam3 Ha_param Hb_r_adv Haf2 Haf3 Hcontr. solve_addr. }
        specialize (Hrel1 Monotemporary _ eq_refl Hy').
        apply rtc_implies with (Q:=λ x y : region_type, Rpub x y ∨ Rpubp x y) in Hrel1.
        2: { intros r q Hrq. rewrite decide_True in Hrq;auto.
             clear -Hparam1 Hparam2 Hparam3 Ha_param Hb_r_adv Haf2 Haf3. solve_addr. }
        apply std_rel_pub_plus_rtc_Monotemporary in Hrel1;auto.
        rewrite override_uninitialize_std_sta_lookup_none in Hy.
        2: { simpl. rewrite lookup_insert_ne; [|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
             apply not_elem_of_list_to_map. rewrite fst_zip. rewrite elem_of_region_addrs.
             2: rewrite Hactlen region_addrs_length /region_size.
             all: clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr. }
        destruct Hrel1 as [ Heq | [v Heq] ].
        - subst.
          assert (is_Some (m' !! b_r_adv)) as [v' Hv].
          { apply Hmcond'. split;auto. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr. }
          rewrite (uninitialize_std_sta_lookup_in _ _ _ v')// in Hy.
          destruct Hstk_cond with b_r_adv as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
          apply elem_of_region_addrs. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsize; solve_addr.
          all: simplify_eq. 2: right with Monotemporary. 3,1: eright;[|left].
          all: rewrite decide_True;[|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
          1,2 : right;constructor. left;constructor.
        - assert (m' !! b_r_adv = None) as Hnone.
          { apply eq_None_not_Some. intros [Hcontr _]%Hmcond'. subst. rewrite Hy' in Hcontr. done. }
          rewrite (uninitialize_std_sta_None_lookup)// in Hy. subst. rewrite Hy' in Hy. simplify_eq.
          destruct Hstk_cond with b_r_adv as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
          apply elem_of_region_addrs. clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hsize; solve_addr.
          all: simplify_eq. 2: right with Monotemporary. 3,1: eright;[|left].
          all: rewrite decide_True;[|clear -Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2; solve_addr].
          1,2 : right;constructor. left;constructor. }

      rewrite lookup_insert_ne// in Hrel1.

      destruct (decide (i ∈ (region_addrs bsec esec))).
      { assert (i ∉ region_addrs af3 b_r_adv ∧
                i ∉ region_addrs b_r_adv frame_end ∧
                a_param ≠ i ∧
                af2 ≠ i) as (? & ? & ? & ?).
        { repeat split. 1,2: rewrite elem_of_region_addrs. all: apply Hdisj in e.
          all: revert e; rewrite elem_of_region_addrs =>e. all: clear Hstk_cond Hdisj Hsec_cond; solve_addr. }
        destruct Hsec_cond' with i as [Hperm | Hmono];[apply elem_of_region_addrs;auto|..].
        - rewrite initialize_list_perm in Hrel1.
          2: rewrite !lookup_insert_ne// !std_sta_update_multiple_lookup_same_i//.
          2: rewrite -uninitialize_std_sta_lookup_perm//.
          2: clear -H2 H0; set_solver.
          rewrite !lookup_insert_ne// !std_sta_update_multiple_lookup_same_i// in Hrel1.
          2: clear -H2 H0; set_solver.
          specialize (Hrel1 Permanent y').
          apply Hrel1 in Hy' as Hnew;[|rewrite -uninitialize_std_sta_lookup_perm//].
          apply rtc_implies with (Q:=λ x y : region_type, Rpub x y ∨ Rpubp x y) in Hnew.
          2: { intros. destruct (decide (le_a b_r_adv i));auto. }
          apply std_rel_pub_plus_rtc_Permanent in Hnew as Hperm';auto. subst.
          assert (m !! i = None) as Hnone.
          { apply eq_None_not_Some. intros [Hcontr _]%Hmcond. rewrite Hperm in Hcontr. done. }
          rewrite initialize_list_nin in Hy;auto.
          2: { rewrite elem_of_list_filter elem_of_elements -elem_of_gmap_dom Hnone. intros [_ Hcontr]. inversion Hcontr. done. }
          rewrite override_uninitialize_std_sta_lookup_none in Hy;auto.
          2: { apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_cons;auto.
               rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
          revert Hy'; rewrite (uninitialize_std_sta_lookup_perm _ m') =>Hy';auto.
          rewrite Hx in Hperm. rewrite Hy in Hy'. simplify_eq. left.
        - assert (is_Some (m !! i)) as [v Hv].
          { apply Hmcond. split;auto. clear; solve_addr. }
          rewrite (initialize_list_in _ _ _ v) in Hrel1;auto.
          2: rewrite !lookup_insert_ne// !std_sta_update_multiple_lookup_same_i//.
          2: apply uninitialize_std_sta_lookup_in;auto.
          2: clear -H2 H0; set_solver.
          specialize (Hrel1 (Monotemporary) y' eq_refl Hy').
          destruct (decide (le_a b_r_adv i)).
          + apply std_rel_pub_plus_rtc_Monotemporary in Hrel1;auto.
            destruct Hrel1 as [Heq | [w Heq] ];subst.
            * assert (is_Some (m' !! i)) as [v' Hv'].
              { apply Hmcond'. split;auto. clear -Hb_r_adv Ha_param l Haf2 Haf3; solve_addr. }
              rewrite initialize_list_nin in Hy;auto.
              2: { rewrite elem_of_list_filter elem_of_elements -elem_of_gmap_dom. intros [Hcontr _].
                   clear -Hb_r_adv Ha_param l Haf2 Haf3 Hcontr; solve_addr. }
              rewrite override_uninitialize_std_sta_lookup_none in Hy;auto.
              2: { apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_cons;auto.
                   rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
              rewrite (uninitialize_std_sta_lookup_in _ _ _ v')// in Hy. rewrite Hx in Hmono. simplify_eq.
              eright;[|left]. rewrite decide_True. right. constructor.
              clear -Hb_r_adv Ha_param l Haf2 Haf3; solve_addr.
            * assert (m' !! i = None) as Hnone.
              { apply eq_None_not_Some. intros [Hcontr _]%Hmcond'. rewrite Hy' in Hcontr. done. }
              rewrite initialize_list_nin in Hy;auto.
              2: { rewrite elem_of_list_filter elem_of_elements -elem_of_gmap_dom. intros [Hcontr _].
                   clear -Hb_r_adv Ha_param l Haf2 Haf3 Hcontr; solve_addr. }
              rewrite override_uninitialize_std_sta_lookup_none in Hy;auto.
              2: { apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_cons;auto.
                   rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
              rewrite uninitialize_std_sta_None_lookup in Hy;auto. rewrite Hy' in Hy.
              rewrite Hx in Hmono. simplify_eq.
              eright;[|left]. rewrite decide_True. right. constructor.
              clear -Hb_r_adv Ha_param l Haf2 Haf3; solve_addr.
          + apply std_rel_pub_rtc_Monotemporary in Hrel1;auto. subst.
            destruct (decide (le_a bstk i)).
            { rewrite (initialize_list_nin) in Hy.
              2: { rewrite elem_of_list_filter. intros [Hcontr _]. clear -Hcontr l. solve_addr. }
              rewrite override_uninitialize_std_sta_lookup_none in Hy;auto.
              2: { apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_cons;auto.
                   rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
              assert (is_Some (m' !! i)) as [v' Hv'].
              { apply Hmcond'. split;auto. }
              rewrite (uninitialize_std_sta_lookup_in _ _ _ v')// in Hy. rewrite Hx in Hmono. simplify_eq.
              eright;[|left]. right. constructor. }
            rewrite (initialize_list_nuninit) in Hy.
            2: { rewrite override_uninitialize_std_sta_lookup_none;auto.
                 2: { apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_cons;auto.
                      rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
                 rewrite uninitialize_std_sta_None_lookup. rewrite Hy'. auto.
                 apply eq_None_not_Some. intros [_ Hcontr]%Hmcond'.
                 clear -n4 Hcontr. solve_addr. }
            rewrite override_uninitialize_std_sta_lookup_none in Hy.
            2: { apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_cons;auto.
                 rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
            rewrite uninitialize_std_sta_None_lookup in Hy.
            rewrite Hy' in Hy. rewrite Hx in Hmono. simplify_eq. left.
            apply eq_None_not_Some. intros [_ Hcontr]%Hmcond'.
            clear -n4 Hcontr. solve_addr.
      }

      rewrite initialize_list_nin// in Hrel1. simpl in Hrel1.
      rewrite lookup_insert_ne// in Hrel1.

      assert (i ∉ region_addrs b_r_adv frame_end).
      { rewrite elem_of_region_addrs. clear -n n0 n2 Hparam1 Hparam2 Hparam3. solve_addr. }
      rewrite std_sta_update_multiple_lookup_same_i// in Hrel1.

      destruct (decide (i = a_param));[subst;rewrite lookup_insert in Hrel1|rewrite lookup_insert_ne// in Hrel1].
      { rewrite initialize_list_nin in Hy.
        2: { rewrite elem_of_list_filter. intros [Hcontr _]. clear -Hcontr Ha_param. solve_addr. }
        rewrite (override_uninitialize_std_sta_lookup_some _ _ _ (inl 2%Z)) in Hy.
        2: { simpl. rewrite lookup_insert. auto. }
        destruct Hstk_cond with a_param as [Hx' | [w Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
        apply elem_of_region_addrs. clear -Ha_param Hsize; solve_addr. subst. simplify_eq.
        eright;[|left]. rewrite decide_True. right;constructor. clear -Ha_param Haf2 Haf3 Hb_r_adv. solve_addr.
        simplify_eq. right with Monotemporary.
        rewrite decide_True. left;constructor. clear -Ha_param Haf2 Haf3 Hb_r_adv. solve_addr.
        eright;[|left]. rewrite decide_True. right;constructor. clear -Ha_param Haf2 Haf3 Hb_r_adv. solve_addr. }

      destruct (decide (i ∈ (region_addrs af3 b_r_adv))).
      { subst Wfinal maddrs. rewrite initialize_list_nin in Hy.
        2: { rewrite elem_of_list_filter. intros [Hcontr _]. clear -e Hcontr Ha_param Hb_r_adv Haf2 Haf3.
             revert e; rewrite elem_of_region_addrs =>e. solve_addr. }
        rewrite std_sta_update_multiple_lookup_in_i// in Hrel1.
        eapply Hrel1 in Hy' as Hrtc;[|eauto].
        apply rtc_implies with (Q:=(λ x y : region_type, std_rel_pub x y)) in Hrtc.
        2: { intros r q. rewrite decide_False. auto. apply elem_of_region_addrs in e. clear -e. solve_addr. }
        eapply std_rel_pub_rtc_Monostatic in Hrtc;[|eauto]. subst y'.
        assert (is_Some (lframe !! i)) as [w Hw].
        { rewrite Hlframe. apply list_to_map_lookup_is_Some. rewrite fst_zip. apply elem_of_cons. right. auto.
          rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv. solve_addr. }
        rewrite (override_uninitialize_std_sta_lookup_some _ _ _ w)// in Hy.
        destruct Hstk_cond with i as [Hx' | [w' Hx'] ];[|rewrite Hx in Hx';inversion Hx'..].
        revert e. rewrite !elem_of_region_addrs. clear -Ha_param Haf2 Haf3 Hb_r_adv Hsize. solve_addr.
        simplify_eq. eright;[|left]. rewrite decide_True. right;constructor. apply elem_of_region_addrs in e.
        clear -e Ha_param Haf2 Haf3 Hb_r_adv. solve_addr.
        simplify_eq. right with Monotemporary. rewrite decide_True. left;constructor.
        apply elem_of_region_addrs in e. clear -e Ha_param Haf2 Haf3 Hb_r_adv. solve_addr.
        eright;[|left]. rewrite decide_True. right;constructor. apply elem_of_region_addrs in e.
        clear -e Ha_param Haf2 Haf3 Hb_r_adv. solve_addr. }

      rewrite std_sta_update_multiple_lookup_same_i// in Hrel1.
      destruct (m !! i) eqn:Hsome.
      { assert (is_Some (m !! i)) as [Hmono _]%Hmcond;[eauto|].
        rewrite (uninitialize_std_sta_lookup_in _ _ _ w)// in Hrel1.
        eapply Hrel1 in Hy' as Hrtc;[|eauto].
        destruct (decide (bstk <= i)%a).
        - apply rtc_implies with (Q:=λ x y : region_type, std_rel_pub x y ∨ std_rel_pub_plus x y)in Hrtc.
          2: { intros r q. destruct (decide (b_r_adv <= i)%a);auto. }
          eapply std_rel_pub_plus_rtc_Uninitialized in Hrtc;[|eauto].
          subst. rewrite initialize_list_nin in Hy.
          2: { rewrite elem_of_list_filter. intros [Hcontr _]. clear -l Hcontr Ha_param Haf2 Haf3 Hb_r_adv. solve_addr. }
          rewrite override_uninitialize_std_sta_lookup_none in Hy.
          2: { apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_cons;auto.
               rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv. solve_addr. }
          destruct Hrtc as [Heq | [v Heq] ].
          { subst. assert (is_Some (m' !! i)) as [v' Hissome].
            { apply Hmcond'. split;auto. }
            rewrite (uninitialize_std_sta_lookup_in _ _ _ v')// in Hy. rewrite Hx in Hmono. simplify_eq.
            eright;[|left]. rewrite decide_True. right;constructor. auto. }
          subst. assert (m' !! i = None) as Hnone.
          { apply eq_None_not_Some. intros [Hcontr _]%Hmcond'. rewrite Hy' in Hcontr. done. }
          rewrite uninitialize_std_sta_None_lookup// in Hy. rewrite Hy' in Hy. rewrite Hx in Hmono. simplify_eq.
          eright;[|left]. rewrite decide_True. right;constructor. auto.
        - apply rtc_implies with (Q:=λ x y : region_type, std_rel_pub x y)in Hrtc.
          2: { intros r q. rewrite decide_False//. clear -n6 Ha_param Hb_r_adv Haf2 Haf3. solve_addr. }
          eapply std_rel_pub_rtc_Uninitialized in Hrtc;[|eauto]. destruct Hrtc as [-> | ->].
          + subst. assert (m' !! i = None) as Hnone.
            { apply eq_None_not_Some. intros [_ Hcontr]%Hmcond'. done. }
            rewrite initialize_list_nuninit in Hy.
            2: { rewrite override_uninitialize_std_sta_lookup_none. rewrite uninitialize_std_sta_None_lookup//.
                 rewrite Hy';auto. apply not_elem_of_list_to_map. rewrite fst_zip. rewrite not_elem_of_cons//.
                 rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
            rewrite override_uninitialize_std_sta_lookup_none in Hy.
            2: { apply not_elem_of_list_to_map. rewrite fst_zip. rewrite not_elem_of_cons//.
                 rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
            rewrite uninitialize_std_sta_None_lookup// in Hy. rewrite Hy in Hy'. rewrite Hx in Hmono.
            simplify_eq. left.
          + subst. assert (m' !! i = None) as Hnone.
            { apply eq_None_not_Some. intros [_ Hcontr]%Hmcond'. done. }
            rewrite (initialize_list_in _ _ _ w) in Hy.
            2: { apply elem_of_list_filter. rewrite elem_of_elements -elem_of_gmap_dom.
                 split;eauto. clear -n6;solve_addr. }
            rewrite Hx in Hmono. simplify_eq. left.
            rewrite override_uninitialize_std_sta_lookup_none.
            2: { apply not_elem_of_list_to_map. rewrite fst_zip. rewrite not_elem_of_cons//.
                 rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }
            rewrite uninitialize_std_sta_None_lookup//. }

      rewrite uninitialize_std_sta_None_lookup// in Hrel1.
      eapply Hrel1 in Hx as Hrtc;eauto.
      subst. rewrite initialize_list_nin in Hy.
      2: { rewrite elem_of_list_filter elem_of_elements -elem_of_gmap_dom Hsome /=. intros [_ Hcontr]; inversion Hcontr. done. }
      rewrite override_uninitialize_std_sta_lookup_none in Hy.
      2: { apply not_elem_of_list_to_map. rewrite fst_zip. rewrite not_elem_of_cons//.
           rewrite /= Hactlen region_addrs_length /region_size. clear -Hb_r_adv;solve_addr. }

      destruct (m' !! i) eqn:Hsome'.
      { assert (is_Some (m' !! i)) as [Htemp Hle]%Hmcond';[eauto|].
        assert ((∃ w', W.1 !! i = Some (Uninitialized w')) ∨ (∃ m, W.1 !! i = Some (Monostatic m)) ∨ W.1 !! i = Some Revoked) as Heq.
        { destruct x;rewrite Hx;eauto;exfalso.
          - assert (is_Some (m !! i)) as [? Hcontr];[|congruence].
            apply Hmcond. split;auto. clear;solve_addr.
          - apply rtc_implies with (Q:=λ x y : region_type, std_rel_pub x y ∨ std_rel_pub_plus x y)in Hrtc.
            2: { intros r q. destruct (decide (b_r_adv <= i)%a);auto. }
            apply std_rel_pub_plus_rtc_Permanent in Hrtc;auto. subst. rewrite Hy' in Htemp. congruence. }
        rewrite (uninitialize_std_sta_lookup_in _ _ _ w)// in Hy.
        destruct Heq as [ [w' Hx'] | [ [s Hx'] | Hx'] ].
        all: rewrite Hx in Hx'. all: simplify_eq;clear -Hle.
        all: right with Monotemporary;[rewrite decide_True//;try (left;constructor);right;constructor|].
        all: eright;[|left]. all: rewrite decide_True//;right;constructor. }

      rewrite uninitialize_std_sta_None_lookup// in Hy. rewrite Hy' in Hy. simplify_eq.
      eapply rtc_implies;[|apply Hrtc].
      intros r q. simpl. intros Hrq.
      destruct (decide (bstk <= i)%a). destruct (decide (b_r_adv <= i)%a);auto.
      rewrite decide_False// in Hrq. clear -n6 Ha_param Haf2 Haf3 Hb_r_adv. solve_addr.
  Qed.

  (* TODO: move this to region_invariants.v *)
  Lemma region_close_uninit W l φ w `{forall Wv, Persistent (φ Wv)}:
    ⊢ sts_state_std l (Uninitialized w)
      ∗ open_region l W ∗ l ↦ₐ w ∗ rel l φ
      -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros "(Hstate & Hreg_open & Hl & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.

    iDestruct (region_map_insert_nonmonostatic (Uninitialized w) with "Hpreds") as "Hpreds". by congruence.
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _. iFrame. iSplitR; [by simplify_map_eq|].
      iExists _. iFrame "∗ #". repeat (iSplitR;[eauto|]). auto. }
    iExists _,_. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  (* lemma that reinitialises into our final world *)
  Lemma initialize_list_consolidate W' (l' l : list Addr) :
    ⊢ ⌜l' ⊆+ l⌝ →
    (region (initialize_list l W') ∗ sts_full_world W'
            ∗ ([∗ list] a ∈ l', □ ∃ φ w, ⌜W'.1 !! a = Some (Uninitialized w) ∨ W'.1 !! a = Some Monotemporary⌝
                            ∗ ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                            ∗ monotemp_pers_resources (initialize_list l W') φ a w ∗ rel a φ))
      ==∗ (sts_full_world (initialize_list l' W') ∗ region (initialize_list l W')).
  Proof.
    iIntros (Hsub) "(Hr & Hsts & Htemps)".
    iInduction l' as [|x l'] "IH".
    - simpl. iFrame. done.
    - iDestruct "Htemps" as "[Hx Htemps]".
     assert (l' ⊆+ l) as Hsub'.
      { apply submseteq_cons_l in Hsub as [k [Hperm Hsub] ]. rewrite Hperm.
        apply submseteq_cons_r. left. auto. }
      iMod ("IH" $! Hsub' with "Hr Hsts Htemps") as "[Hsts Hr]".
      iClear "IH".
      iDestruct "Hx" as (φ w Huninit Hpers) "((Hmono & Hφ) & Hrel)".
      simpl. destruct Huninit as [Huninit | Hmono].
      2: { rewrite Hmono. iFrame. done. }
      rewrite Huninit.
      assert (x ∈ l) as Hinl.
      { apply elem_of_submseteq with (x0:=x) in Hsub;[auto|apply elem_of_cons;by left]. }
      destruct (decide (x ∈ l')).
      + (* in this case we have already updated its state, and we just close and finish *)
        rewrite (initialize_list_twice _ _ _ w);auto. iFrame. done.
      + (* otherwise we must update it in the world *)
        rewrite region_eq /region_def /region_map_def.
        iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
        iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
        rewrite RELS_eq rel_eq /RELS_def /rel_def REL_eq /REL_def.
        iDestruct "Hrel" as (γpred) "#[Hrel Hsaved]".
        iDestruct (reg_in with "[$HM $Hrel]") as %HMeq. rewrite HMeq.
        iDestruct (big_sepM_delete _ _ x with "Hr") as "[Hx Hr]";[apply lookup_insert|].
        rewrite delete_insert;[|apply lookup_delete].
        iDestruct "Hx" as (ρ Hx) "[Hstate Hx]".
        iDestruct (sts_full_state_std with "Hsts Hstate") as %Hin.
        rewrite initialize_list_nin// in Hin. rewrite Huninit in Hin;inversion Hin;subst.
        iMod (sts_update_std _ _ _ Monotemporary with "Hsts Hstate") as "[Hsts Hstate]". rewrite HMeq.
        iDestruct (region_map_delete_nonstatic with "Hr") as "Hr";[intros m;by rewrite Hx|].
        iDestruct (region_map_insert_nonmonostatic Monotemporary with "Hr") as "Hr"; auto.
        iDestruct (big_sepM_delete _ _ x with "[Hx Hmono Hφ Hstate $Hr]") as "Hr";[apply lookup_insert|..].
        { iExists Monotemporary. iFrame. rewrite lookup_insert. iSplit;auto. iExists φ. repeat (iSplit;auto).
          iDestruct "Hx" as (φ' Hpers') "(#Hsaved' & Hx)".
          iExists w. iFrame. auto. }
        iFrame. iExists M,_. rewrite -HMeq. iFrame. rewrite -HMeq. iFrame. iModIntro. iSplit; auto.
        iPureIntro. rewrite dom_insert_L. rewrite -Hdom'.
        assert (x ∈ dom (gset Addr) Mρ);[apply elem_of_gmap_dom;eauto|]. set_solver.
  Qed.

  Lemma initialize_list_region W (l : list Addr) :
    (region W ∗ sts_full_world W
    ∗ ([∗ list] a ∈ l, □ ∃ φ w, ⌜W.1 !! a = Some (Uninitialized w) ∨ W.1 !! a = Some Monotemporary⌝
                               ∗ ⌜∀ Wv : WORLD * Word, Persistent (φ Wv)⌝
                               ∗ monotemp_pers_resources (initialize_list l W) φ a w ∗ rel a φ))
      ==∗ (sts_full_world (initialize_list l W) ∗ region (initialize_list l W)).
  Proof.
    iIntros "(Hr & Hsts & Htemp)".
    assert (related_sts_pub_world W (initialize_list l W)) as Hrelated.
    { apply initialize_list_related_pub. }
    assert (dom (gset Addr) (std W) = dom (gset Addr) (std (initialize_list l W))) as Heq.
    { apply initialize_list_dom. }
    iDestruct (region_monotone with "Hr") as "Hr";[apply Heq|apply Hrelated|].
    iMod (initialize_list_consolidate _ _ l with "[] [$Hr $Hsts $Htemp]") as "[Hsts Hr]";[eauto|iFrame;done].
  Qed.

End stack_object.
