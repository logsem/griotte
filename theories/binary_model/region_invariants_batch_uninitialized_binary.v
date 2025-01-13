From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import tactics.
From cap_machine Require Export stdpp_extra iris_extra multiple_updates region.
From cap_machine.binary_model Require Export region_invariants_binary region_invariants_transitions_binary logrel_binary.
Import uPred.

Section heap.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ} {cfgg : cfgSG Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* --------------------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------ UNINITIALIZATION --------------------------------------------- *)
  (* --------------------------------------------------------------------------------------------------------- *)

  (*
     Full uninitialization turns every temporary/monotemporary
     location state to uninitialized.
     Unlike revocation, it is only required to uninitialize
     all addresses above some chosen address a
   *)

  (* Uninitializing only changes the states of the standard STS collection *)
  (* A weaker revocation which only revokes elements from a list *)
  Definition u_merge_op (wo : option (Word * Word)) (ro : option region_type) : option region_type :=
    match wo,ro with
    | Some w, Some r => match r with
                       | Monotemporary => Some (Uninitialized w)
                       | _ => Some r
                       end
    | _, Some r => Some r
    |_, None => None
    end.

  Definition uninitialize_std_sta (m : gmap Addr (Word * Word)) : STS_STD → STS_STD :=
    merge u_merge_op m.

  Definition uninitialize W m : WORLD := (uninitialize_std_sta m (std W),loc W).

  Global Instance diag_none_u_merge_op : DiagNone u_merge_op.
  Proof. by rewrite /u_merge_op /DiagNone /=. Qed.

  Lemma uninitialize_std_sta_empty fs :
    uninitialize_std_sta ∅ fs = fs.
  Proof.
    rewrite map_eq_iff. intros a.
    rewrite /uninitialize_std_sta.
    rewrite lookup_merge lookup_empty /=.
    destruct (fs !! a) eqn:Hsome;rewrite Hsome;auto.
  Qed.

  Lemma uninitialize_empty W :
    uninitialize W ∅ = W.
  Proof.
    rewrite /uninitialize uninitialize_std_sta_empty.
    destruct W;auto.
  Qed.

  Definition uninitialize_i j w :=
    match j with
    | Monotemporary => Uninitialized w
    | _ => j
    end.

  Lemma uninitialize_std_sta_spec (m : gmap Addr (Word * Word)) :
    forall (Wstd_sta : STS_STD) (i : Addr),
      (uninitialize_std_sta m Wstd_sta) !! i = match Wstd_sta !! i with
                                              | None => None
                                              | Some j => Some (match m !! i with
                                                               | Some w => uninitialize_i j w
                                                               | None => j
                                                               end)
                                              end.
  Proof.
    induction m using map_ind; intros.
    - rewrite uninitialize_std_sta_empty.
      destruct (Wstd_sta !! i) eqn:Hsome;auto.
    - destruct (decide (i = i0));subst.
      + simplify_map_eq.
        rewrite lookup_merge.
        destruct (Wstd_sta !! i0) eqn:Hsome.
        * simplify_map_eq. destruct r; auto.
        * simplify_map_eq. auto.
      + simplify_map_eq.
        rewrite lookup_merge. rewrite lookup_insert_ne//.
        specialize (IHm Wstd_sta i0). by rewrite lookup_merge in IHm.
  Qed.

  Lemma uninitialize_std_sta_None_lookup i l m :
    l !! i = None →
    (uninitialize_std_sta l m) !! i = m !! i.
  Proof.
    intros Hnin.
    rewrite lookup_merge Hnin.
    simpl; destruct (m !! i) eqn:Hsome;rewrite Hsome;auto.
  Qed.

  Lemma uninitialize_std_sta_not_elem_of_lookup i l m :
    i ∉ dom (gset Addr) l →
    (uninitialize_std_sta l m) !! i = m !! i.
  Proof.
    intros Hnin. apply not_elem_of_dom in Hnin.
    apply uninitialize_std_sta_None_lookup;auto.
  Qed.

  Lemma uninitialize_std_sta_is_Some i l m :
    is_Some (m !! i) <->
    is_Some ((uninitialize_std_sta l m) !! i).
  Proof.
    split; intros Hsome; destruct Hsome as [x Hx].
    rewrite lookup_merge Hx.
    destruct (l !! i);simpl;destruct x;eauto.
    rewrite lookup_merge in Hx.
    destruct (m !! i) eqn:Hsome;eauto.
    rewrite Hsome /= in Hx.
    destruct (l !! i);simpl in Hx; inversion Hx.
  Qed.

  Lemma uninitialize_dom W m :
    dom (gset Addr) (uninitialize W m).1 = dom (gset Addr) W.1.
  Proof.
    apply set_equiv_spec_L. split.
    - apply elem_of_subseteq. intros x Hx.
      apply elem_of_gmap_dom in Hx as [y Hx].
      apply elem_of_gmap_dom. eapply (uninitialize_std_sta_is_Some _ m). eauto.
    - apply elem_of_subseteq. intros x Hx.
      apply elem_of_gmap_dom. rewrite -(uninitialize_std_sta_is_Some _ m).
      apply elem_of_gmap_dom. auto.
  Qed.

  Lemma uninitialize_std_sta_insert fs m w a :
    fs !! a = Some Monotemporary →
    <[a:=Uninitialized w]> (uninitialize_std_sta m fs) = uninitialize_std_sta (<[a:=w]> m) fs.
  Proof.
    intros Htemps.
    apply map_eq'. intros k v;split.
    - intros Ha. destruct (decide (k = a));subst;simplify_map_eq_alt.
      + rewrite lookup_merge lookup_insert /=.
        rewrite Htemps;auto.
      + rewrite lookup_merge /=. rewrite /u_merge_op. simplify_map_eq.
        destruct (m !! k) eqn:Hsome.
        * destruct (fs !! k) eqn:Hsome';rewrite Hsome';[destruct r;auto|].
          all: rewrite lookup_merge Hsome Hsome' /= in Ha;auto.
        * rewrite lookup_merge Hsome /= in Ha;auto.
    - intros Ha. destruct (decide (k = a));subst;simplify_map_eq_alt;simplify_eq.
      + rewrite lookup_merge lookup_insert in Ha.
        rewrite Htemps /= in Ha;auto. rewrite lookup_insert. auto.
      + rewrite lookup_merge lookup_insert_ne// in Ha.
        rewrite lookup_insert_ne//. rewrite lookup_merge. auto.
  Qed.

  Lemma uninitialize_std_sta_lookup_in i m (fs : STS_STD) (v : Word * Word) :
    m !! i = Some v →
    fs !! i = Some Monotemporary →
    (uninitialize_std_sta m fs) !! i = Some (Uninitialized v).
  Proof.
    intros Hi Hsome.
    rewrite lookup_merge Hi.
    rewrite Hsome; auto.
  Qed.

  Lemma uninitialize_std_sta_singleton fs a v :
    fs !! a = Some Monotemporary ->
    uninitialize_std_sta {[a := v]} fs = <[a:=Uninitialized v]> fs.
  Proof.
    intros Hin.
    apply map_eq'. intros k w. rewrite lookup_merge.
    destruct (decide (a = k));subst;simplify_map_eq;simplify_map_eq_alt;auto.
    rewrite lookup_insert;auto.
    destruct (fs !! k) eqn:Hsome;auto;rewrite lookup_insert_ne//;rewrite Hsome//.
  Qed.

  Lemma uninitialize_related_pub_a W m a :
    (∀ a' : Addr, is_Some (m !! a') ↔ (W.1 !! a' = Some Monotemporary) ∧ (a <= a')%a) →
    related_sts_a_world W (uninitialize W m) a.
  Proof.
    intros Hcond.
    split;[|apply related_sts_pub_plus_refl].
    split.
    - rewrite uninitialize_dom. done.
    - intros i x y Hx Hy.
      destruct (decide (le_a a i)).
      + destruct (decide (x = Monotemporary)).
        * assert (is_Some (m !! i)) as [v Hv].
          { apply Hcond. split;auto. subst;auto. }
          rewrite lookup_merge Hv Hx /= in Hy.
          simplify_eq. eright;[|left]. right. constructor.
        * assert ((m !! i) = None) as Hnone.
          { apply eq_None_not_Some. intros Hcontr%Hcond. destruct Hcontr as [Hcontr _].
            rewrite Hx in Hcontr; inversion Hcontr; congruence. }
          rewrite lookup_merge Hnone Hx /= in Hy. simplify_eq. left.
      + destruct (m !! i) eqn:Hsome.
        2: { rewrite lookup_merge Hsome Hx /= in Hy. simplify_eq. left. }
        destruct (decide (W.1 !! i = Some Monotemporary)).
        2: { rewrite lookup_merge Hsome Hx /= in Hy. destruct x;simplify_eq;try contradiction;left. }
        assert (is_Some (m !! i)) as Hcontr%Hcond;eauto. destruct Hcontr as [_ Hcontr].
        solve_addr.
  Qed.

  (* ------------------------------------------------------------------------------------------------- *)
  (* ------------------------ Binary versions of lemmas in the revocation file ----------------------- *)
  (* ------------------------------------------------------------------------------------------------- *)

  Lemma reg_get (γ : gname) (R : relT) (n : Addr) (r : leibnizO (gname)) :
    own γ (● (to_agree <$> R : relUR)) ∧ ⌜R !! n = Some r⌝ ==∗
    (own γ (● (to_agree <$> R : relUR)) ∗ own γ (◯ {[n := to_agree r]})).
  Proof.
    iIntros "[HR #Hlookup]".
    iDestruct "Hlookup" as %Hlookup.
    iApply own_op.
    iApply (own_update with "HR").
    apply auth_update_core_id; auto. apply gmap_core_id,agree_core_id.
    apply singleton_included_l. exists (to_agree r). split; auto.
    (* apply leibniz_equiv_iff in Hlookup.  *)
    rewrite lookup_fmap. apply fmap_Some_equiv.
    exists r. split; auto.
  Qed.

  Lemma region_rel_get (W : WORLD) (a : Addr) :
    (std W) !! a = Some Monotemporary ->
    region W ∗ sts_full_world W ==∗
     region W ∗ sts_full_world W ∗ ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ rel a φ.
  Proof.
    iIntros (Hlookup) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom & #Hdom' & Hr)".
    iDestruct "Hdom" as %Hdom. iDestruct "Hdom'" as %Hdom'.
    assert (is_Some (M !! a)) as [γp Hγp].
    { apply elem_of_gmap_dom. rewrite -Hdom. apply elem_of_gmap_dom. eauto. }
    rewrite RELS_eq /RELS_def.
    iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
    (* rewrite /region_map_def. iDestruct (reg_in with "[$HM $Hrel]") as %HMeq. *)
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
    iDestruct (sts_full_state_std with "Hsts Hρ") as %Hx''.
    all: rewrite Hlookup in Hx'';inversion Hx'';subst.
    all: iDestruct "Hstate" as (φ Hpers) "(#Hsaved & Ha)".
    all: iDestruct "Ha" as (v v') "(Ha & Ha' & Hmono & #Hφ)".
    all: iDestruct (big_sepM_delete _ _ a with "[Hρ Ha Ha' Hmono Hφ $Hr]") as "Hr";[eauto| |].
    { iExists Monotemporary. iFrame. iSplit;auto. iExists φ. iFrame "∗ # %". iExists _,_;iFrame. auto. }
    all: iModIntro.
    all: iSplitL "HM Hr".
    { iExists M. iFrame. auto. }
    all: iFrame; iExists φ; iSplit;auto; rewrite rel_eq /rel_def REL_eq /REL_def;iExists γp.
    all: iFrame "Hsaved Hrel".
  Qed.

  (* ------------------------------------------------------------------------------------------------- *)
  (* ------------------ A version of uninitialization where we remember the invariants --------------- *)
  (* ------------------------------------------------------------------------------------------------- *)

  Definition monotemp_pers_resources W φ a v1 v2 : iProp Σ :=
    (future_pub_a_mono a φ v1 v2 ∗ φ (W,(v1,v2)))%I.

  Lemma uninitialize_region_last_keep W E :
    region W ∗ sts_full_world W ={E}=∗ ∃ m, ⌜((∃ (v v' : Word), {[addr_reg.top:=(v,v')]} = m) ↔ W.1 !! addr_reg.top = Some Monotemporary)
                                             ∧ (∅ = m <-> W.1 !! addr_reg.top ≠ Some Monotemporary)⌝
                                             ∗ region W ∗ sts_full_world (uninitialize W m)
                                             ∗ □ ▷ ([∗ map] a↦w ∈ m, □ ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ monotemp_pers_resources W φ a w.1 w.2 ∗ rel a φ).
  Proof.
    iIntros "[Hr Hsts]".
    destruct (decide (W.1 !! addr_reg.top = Some Monotemporary)).
    + iMod (region_rel_get with "[$Hr $Hsts]") as "(Hr & Hsts & #Hrel)";eauto.
      iDestruct "Hrel" as (φ' Hpers') "Hrel".
      rewrite region_eq /region_def.
      iDestruct "Hr" as (M Mρ) "(HM & #HM_dom & #HMρ_dom & Hmap)".
      iDestruct "HM_dom" as %HM_dom. iDestruct "HMρ_dom" as %HMρ_dom.
      assert (is_Some (M !! addr_reg.top)) as [γp Hγp].
      { apply elem_of_gmap_dom. rewrite -HM_dom. apply elem_of_gmap_dom. eauto. }
      iDestruct (big_sepM_delete with "Hmap") as "[Ha Hmap]";[apply Hγp|].
      iDestruct "Ha" as (ρ Hlookup) "[Hstate Hresources]".
      iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
      iDestruct "Hresources" as (φ Hpers) "[#Hsaved Ha]".
      rewrite e in Hρ;inversion Hρ;subst ρ.
      iDestruct "Ha" as (v1 v2) "(Ha & Ha' & Hres)".
      iMod (sts_update_std _ _ _ (Uninitialized (v1,v2)) with "Hsts Hstate") as "[Hsts Hstate]".
      iDestruct (region_map_delete_nonstatic with "Hmap") as "Hmap".
      { intros m'. rewrite Hlookup. auto. }
      iDestruct (region_map_insert_nonmonostatic (Uninitialized (v1,v2)) with "Hmap") as "Hmap";auto.
      iDestruct (big_sepM_insert _ _ addr_reg.top with "[$Hmap Ha Ha' Hstate]") as "Hmap";[apply lookup_delete|..].
      { iExists (Uninitialized _). rewrite lookup_insert. iSplit;auto. iFrame. iExists _. iSplit;eauto. }
      rewrite insert_delete. rewrite (insert_id M);[|auto]. iModIntro.
      iExists {[addr_reg.top:= _]}. rewrite /uninitialize uninitialize_std_sta_singleton// /=. iFrame.
      iSplit;[iPureIntro|iSplit].
      * split;split.
        { intros;auto. }
        { intros _. eexists;eauto. }
        { intros Hcontr;inversion Hcontr. }
        { intros Hcontr; contradiction. }
      * iExists _,_. iFrame. iPureIntro. rewrite HM_dom -HMρ_dom. clear -Hlookup. split;auto.
          assert (addr_reg.top ∈ dom (gset Addr) Mρ);[apply elem_of_gmap_dom;eauto|]. rewrite dom_insert_L. set_solver.
      * rewrite rel_eq /rel_def REL_eq /REL_def RELS_eq /RELS_def. iDestruct "Hrel" as (γpred') "[HREL Hsaved']".
        iDestruct (reg_in with "[$HM $HREL]") as %Hmeq. rewrite Hmeq lookup_insert in Hγp;inversion Hγp. simplify_eq.
        iDestruct (saved_pred_agree _ _ _ (W,(v1,v2)) with "Hsaved Hsaved'") as "Heq".
        iDestruct "Hres" as "#Hres". iModIntro.
        rewrite big_sepM_singleton. iModIntro. iExists φ. iModIntro. iSplit;auto. 
    + iModIntro. iExists ∅. rewrite uninitialize_empty. iFrame. rewrite big_sepM_empty. iSplit;[|auto].
      iPureIntro. split. split;intros;try contradiction. destruct H0. inversion H0. done.
      split;intros;auto.
  Qed.


  Lemma uninitialize_region_states_keep W (a : Addr) (l : list Addr) E :
    ⌜l = region_addrs a addr_reg.top ++ [addr_reg.top]⌝ -∗
    region W ∗ sts_full_world W ={E}=∗
    ∃ m, ⌜∀ (a' : Addr), is_Some(m !! a') ↔ ((W.1 !! a' = Some Monotemporary) ∧ (a' ∈ l)%a)⌝
         ∗ region W ∗ sts_full_world (uninitialize W m)
         ∗ □ ▷ ([∗ map] a↦w ∈ m, □ ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ monotemp_pers_resources W φ a w.1 w.2 ∗ rel a φ).
  Proof.
    iIntros (Heq) "(Hr & Hsts)".
    iInduction (l) as [|a' l] "IH" forall (a Heq).
    { destruct (region_addrs a addr_reg.top); inversion Heq. }
    destruct l.
    - iMod (uninitialize_region_last_keep with "[$Hr $Hsts]") as (m [Hcond Hcond']) "[Hr [Hsts #Hresources] ]".
      iExists m. iModIntro. iFrame "∗ #". iPureIntro. intros a0. split;intros Hc.
      + destruct (region_addrs a addr_reg.top);[inversion Heq;subst|destruct l; inversion Heq].
        destruct (decide (W.1 !! addr_reg.top = Some Monotemporary));[|exfalso]. assert (e':=e).
        apply Hcond in e as [v [v' <-] ]. destruct Hc as [c Hc]. apply lookup_singleton_Some in Hc as [Heq1 Heq2];subst.
        split;auto. constructor.
        apply Hcond' in n. subst. rewrite lookup_empty in Hc. inversion Hc. done.
      + destruct Hc as [Hc1 Hc2]. destruct (region_addrs a addr_reg.top);[inversion Heq;subst|destruct l; inversion Heq].
        apply elem_of_list_singleton in Hc2. subst. apply Hcond in Hc1 as [v [v' <-] ]. eauto.
    - assert ((a' + 1)%a = Some a0 ∧ (a' = a) ∧ (region_addrs a addr_reg.top = a :: region_addrs a0 addr_reg.top))
        as [Hnext [Heqa Haddrs_cons ] ].
      { assert (a < addr_reg.top)%a as Hlt.
        { destruct (decide (a < addr_reg.top)%a);auto.
          apply Znot_lt_ge in n. rewrite region_addrs_empty in Heq;[|solve_addr]. inversion Heq. }
        assert (Heq':=Heq).
        rewrite region_addrs_cons in Heq;auto. inversion Heq;subst.
        assert ((a + 1)%a = Some a0) as  Ha''.
        { destruct (a + 1)%a eqn:Hsome;[|solve_addr].
          simpl in *. destruct (decide (a1 = addr_reg.top));subst;auto.
          - rewrite region_addrs_empty in H2;[|solve_addr]. destruct l;inversion H2. auto.
          - rewrite region_addrs_cons in Heq;[|solve_addr]. inversion Heq;auto. }
        repeat split;auto. rewrite region_addrs_cons;auto. rewrite Ha''. auto. }
      subst a'.
      destruct (decide (W.1 !! a = Some Monotemporary)).
      + iMod (region_rel_get with "[$Hr $Hsts]") as "(Hr & Hsts & #Hrel)";eauto.
        iDestruct "Hrel" as (φ' Hpers') "Hrel".
        iMod ("IH" $! a0 with "[] Hr Hsts") as (m Hmcond) "[Hr [Hsts #Hres] ]".
        { rewrite region_addrs_cons in Heq;[|solve_addr]. rewrite Hnext in Heq. inversion Heq;auto. }
        assert (m !! a = None) as Hnone.
        { destruct (m!!a)eqn:Hsome';auto. assert (is_Some (m!!a)) as HisSome;eauto. apply Hmcond in HisSome as [Htemps Hin]. exfalso.
          rewrite Haddrs_cons in Heq. inversion Heq. rewrite H1 in Hin. apply elem_of_app in Hin as [Hin | Heq'].
          apply elem_of_region_addrs in Hin. solve_addr. apply elem_of_list_singleton in Heq';subst;solve_addr. }
        rewrite region_eq /region_def.
        iDestruct "Hr" as (M Mρ) "(HM & #HM_dom & #HMρ_dom & Hmap)".
        iDestruct "HM_dom" as %HM_dom. iDestruct "HMρ_dom" as %HMρ_dom.
        assert (is_Some (M !! a)) as [γp Hγp].
        { apply elem_of_gmap_dom. rewrite -HM_dom. apply elem_of_gmap_dom. eauto. }
        iDestruct (big_sepM_delete with "Hmap") as "[Ha Hmap]";[apply Hγp|].
        iDestruct "Ha" as (ρ Hlookup) "[Hstate Hresources]".
        iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
        rewrite uninitialize_std_sta_None_lookup in Hρ;[|auto].
        iDestruct "Hresources" as (φ Hpers) "[#Hsaved Ha]".
        rewrite e in Hρ;inversion Hρ;subst ρ.
        iDestruct "Ha" as (v v') "(Ha & Ha' & Hres')".
        iMod (sts_update_std _ _ _ (Uninitialized _) with "Hsts Hstate") as "[Hsts Hstate]".
        iDestruct (region_map_delete_nonstatic with "Hmap") as "Hmap".
        { intros m'. rewrite Hlookup. auto. }
        iDestruct(region_map_insert_nonmonostatic (Uninitialized (v,v')) with "Hmap") as "Hmap";auto.
        iDestruct (big_sepM_insert _ _ a with "[$Hmap Ha Ha' Hstate]") as "Hmap";[apply lookup_delete|..].
        { iExists (Uninitialized (v,v')). rewrite lookup_insert. iSplit;auto. iFrame. iExists _. iSplit;eauto. }
        rewrite insert_delete. rewrite (insert_id M);[|auto]. iModIntro.
        iExists (<[a:=(v,v')]> m). rewrite /uninitialize /= uninitialize_std_sta_insert;[|auto]. iFrame.
        iSplit;[iPureIntro|iSplit].
        * intros a'. destruct (decide (a = a'));[subst;rewrite lookup_insert|rewrite lookup_insert_ne//].
          { split;intros;[split;auto;constructor|eauto]. }
          { split;intros Hcond;[apply Hmcond in Hcond as [? ?]|]. split;auto. constructor;auto.
            apply Hmcond. destruct Hcond as [? Hcond]. split;auto. apply elem_of_cons in Hcond as [-> | Hcond];[|auto].
            contradiction. }
        * iExists _,_. iFrame. iPureIntro. rewrite HM_dom -HMρ_dom. clear -Hlookup. split;auto.
          assert (a ∈ dom (gset Addr) Mρ);[apply elem_of_gmap_dom;eauto|]. rewrite dom_insert_L. set_solver.
        * rewrite rel_eq /rel_def REL_eq /REL_def RELS_eq /RELS_def. iDestruct "Hrel" as (γpred') "[HREL Hsaved']".
          iDestruct (reg_in with "[$HM $HREL]") as %Hmeq. rewrite Hmeq lookup_insert in Hγp;inversion Hγp. simplify_eq.
          iDestruct (saved_pred_agree _ _ _ (W,(v,v')) with "Hsaved Hsaved'") as "Heq".
          iDestruct "Hres'" as "#Hres'". iModIntro. iNext. iApply big_sepM_insert;[auto|].
          iFrame "Hres". iExists φ. iModIntro. iSplit;auto.
      + iMod ("IH" $! a0 with "[] Hr Hsts") as (m Hmcond) "[Hr [Hsts #Hres] ]".
        { rewrite region_addrs_cons in Heq;[|solve_addr]. rewrite Hnext in Heq. inversion Heq;auto. }
        assert (m !! a = None) as Hnone.
        { destruct (m!!a)eqn:Hsome';auto. assert (is_Some (m!!a)) as HisSome;eauto. apply Hmcond in HisSome as [Htemps Hin]. exfalso.
          rewrite Haddrs_cons in Heq. inversion Heq. rewrite H1 in Hin. apply elem_of_app in Hin as [Hin | Heq'].
          apply elem_of_region_addrs in Hin. solve_addr. apply elem_of_list_singleton in Heq';subst;solve_addr. }
        iModIntro. iExists m.
        iFrame "∗ #". iPureIntro. intros a'. split.
        * intros Hsome. apply Hmcond in Hsome as [? ?]. split;auto. constructor;auto.
        * intros [Htemps Hin]. apply Hmcond. split;auto.
          apply elem_of_cons in Hin as [-> | Hcons];auto. contradiction.
  Qed.

  Lemma uninitialize_region_world W a m :
    ⌜∀ (a' : Addr), is_Some(m !! a') ↔ ((W.1 !! a' = Some Monotemporary) ∧ (a <= a')%a)⌝ -∗
    region W -∗ sts_full_world (uninitialize W m) -∗ region (uninitialize W m) ∗ sts_full_world (uninitialize W m).
  Proof.
    iIntros (Hcond) "Hr Hsts".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom_m & #Hdom_mρ & Hpreds)".
    iDestruct "Hdom_m" as %Hdom_m. iDestruct "Hdom_mρ" as %Hdom_mρ.
    iApply sep_exist_r. iExists M. iApply sep_exist_r. iExists Mρ.
    iAssert (⌜∀ a ρ, Mρ !! a = Some ρ → (uninitialize W m).1 !! a = Some ρ⌝)%I as %Hρcond.
    { iIntros (a' ρ Ha'). assert (is_Some (M !! a')) as [γp HMa'];[apply elem_of_gmap_dom;rewrite -Hdom_mρ;apply elem_of_gmap_dom;eauto|].
      iDestruct (big_sepM_delete with "Hpreds") as "[Ha _]";[apply HMa'|].
      iDestruct "Ha" as (ρ' Hlookup) "[Hρ' _]".
      iDestruct (sts_full_state_std with "Hsts Hρ'") as %Hρ'. simplify_eq. auto. }
    iFrame. rewrite uninitialize_dom. repeat iSplit;auto.
    iApply (big_sepM_mono with "Hpreds").
    iIntros (a' x Hmx) "Ha".
    iDestruct "Ha" as (ρ Hlookup) "[Hstate Ha]".
    iDestruct "Ha" as (φ Hpers) "[#Hsaved Hres]".
    apply Hρcond in Hlookup as Hρ.
    iExists ρ. iSplit;auto. iFrame. iExists φ. repeat iSplit;auto.
    destruct (decide (W.1 !! a' = Some Monotemporary)).
    - destruct (decide (a <= a')%a).
      + assert (is_Some (m !! a')) as [v Hv];[apply Hcond;auto|].
        pose proof (uninitialize_std_sta_lookup_in a' m W.1 v Hv e) as Hmin.
        rewrite Hρ in Hmin. inversion Hmin;subst ρ. iFrame.
      + assert (m !! a' = None) as Hnone.
        { apply eq_None_not_Some. intros Hcontr%Hcond. destruct Hcontr as [? ?]; contradiction. }
        rewrite uninitialize_std_sta_None_lookup in Hρ;auto.
        rewrite e in Hρ. inversion Hρ;subst ρ.
        iDestruct "Hres" as (v v') "Hres".
        iDestruct "Hres" as "(Ha & Ha' & #Hmono & #Hφ)".
        iExists _,_; iFrame "∗ #".
        iApply ("Hmono" with "[] Hφ"). iPureIntro.
        apply related_sts_a_weak_world with a. clear -n;solve_addr. apply uninitialize_related_pub_a. auto.
    - assert (m !! a' = None) as Hnone.
      { apply eq_None_not_Some. intros Hcontr%Hcond. destruct Hcontr as [ ? ?]; contradiction. }
      rewrite uninitialize_std_sta_None_lookup in Hρ;auto.
      rewrite Hρ in n.
      destruct ρ;auto;try contradiction.
      * iDestruct "Hres" as (v v') "Ha".
        iDestruct "Ha" as "(Ha & Ha' & #Hmono & #Hφ)".
        iExists v,v'. iFrame "∗ #". iNext.
        iApply ("Hmono" with "[] Hφ"). iPureIntro.
        apply related_sts_pub_plus_priv_world.
        apply related_sts_a_pub_plus_world with a.
        apply uninitialize_related_pub_a; auto.
  Qed.

  Lemma uninitialize_region_keep W (a : Addr) E :
    region W ∗ sts_full_world W ={E}=∗
    ∃ m, ⌜∀ (a' : Addr), is_Some(m !! a') ↔ (((std W) !! a' = Some Monotemporary) ∧ (a <= a')%a)⌝
      ∗ region (uninitialize W m) ∗ sts_full_world (uninitialize W m)
      ∗ □ ▷ ([∗ map] a↦w ∈ m, □ ∃ φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ monotemp_pers_resources W φ a w.1 w.2 ∗ rel a φ).
  Proof.
    iIntros "(Hr & Hsts)".
    iMod (uninitialize_region_states_keep _ _ (region_addrs a addr_reg.top ++ [addr_reg.top])
            with "[] [$Hr $Hsts]") as (m Hconds) "[Hr [Hsts #Hres] ]";[eauto|].
    iModIntro. iExists m.
    assert (∀ (a' : Addr), is_Some(m !! a') ↔ ((W.1 !! a' = Some Monotemporary) ∧ (a <= a')%a)) as Hconds'.
    { intros a'. split.
      - intros Hsome. apply Hconds in Hsome. destruct Hsome as [Hmono Hin].
        apply elem_of_app in Hin as [Hin | Hin];[|apply elem_of_list_singleton in Hin;subst].
        apply elem_of_region_addrs in Hin as [Hin ?]. split;auto.
        split;auto. solve_addr.
      - intros [Hmono Hle]. apply Hconds. split;auto. apply elem_of_app. destruct (decide (a' < addr_reg.top)%a).
        left. apply elem_of_region_addrs;auto. right. assert (a' = addr_reg.top);[solve_addr|subst]. constructor. }
    iDestruct (uninitialize_region_world with "[] Hr Hsts") as "[Hr Hsts]";[eauto|iFrame;auto].
  Qed.

  (* ------------------------------------------------------------------------------------------------- *)
  (* ------------------- A version of uninitialization where we forget the invariants ---------------- *)
  (* ------------------------------------------------------------------------------------------------- *)

  Lemma uninitialize_region_last W E :
    region W ∗ sts_full_world W ={E}=∗ ∃ m, ⌜((∃ (v v': Word), {[addr_reg.top:=(v,v')]} = m) ↔ W.1 !! addr_reg.top = Some Monotemporary)
                                             ∧ (∅ = m <-> W.1 !! addr_reg.top ≠ Some Monotemporary)⌝
                                       ∗ region W ∗ sts_full_world (uninitialize W m).
  Proof.
    iIntros "[Hr Hsts]".
    iMod (uninitialize_region_last_keep with "[$Hr $Hsts]") as (m Hforall) "(Hr & Hsts & Hm)".
    iModIntro. iExists m. iFrame. auto.
  Qed.

  Lemma uninitialize_region_states W (a : Addr) (l : list Addr) E :
    ⌜l = region_addrs a addr_reg.top ++ [addr_reg.top]⌝ -∗
    region W ∗ sts_full_world W ={E}=∗
    ∃ m, ⌜∀ (a' : Addr), is_Some(m !! a') ↔ ((W.1 !! a' = Some Monotemporary) ∧ (a' ∈ l)%a)⌝
         ∗ region W ∗ sts_full_world (uninitialize W m).
  Proof.
    iIntros (Heq) "(Hr & Hsts)".
    iMod (uninitialize_region_states_keep with "[] [$Hr $Hsts]") as (m Hforall) "(Hr & Hsts & Hm)". eauto.
    iModIntro. iExists m. iFrame. auto.
  Qed.

  Lemma uninitialize_region W (a : Addr) E :
    region W ∗ sts_full_world W ={E}=∗
    ∃ m, ⌜∀ (a' : Addr), is_Some(m !! a') ↔ (((std W) !! a' = Some Monotemporary) ∧ (a <= a')%a)⌝
         ∗ region (uninitialize W m) ∗ sts_full_world (uninitialize W m).
  Proof.
    iIntros "(Hr & Hsts)".
    iMod (uninitialize_region_keep with "[$Hr $Hsts]") as (m Hforall) "(Hr & Hsts & Hres)".
    iModIntro. iExists m. iFrame. auto.
  Qed.

  (* ------------------------------------------------------------------------------------------------- *)
  (* -------------- We will want to change the values of an already uninitialized region ------------- *)
  (* ------------------------------------------------------------------------------------------------- *)

  Lemma uninitialized_condition W m a :
    (∀ a' : Addr, is_Some (m !! a') ↔ (W.1 !! a' = Some Monotemporary) ∧ (a <= a')%a) →
    ∀ a'' : Addr, (a <= a'')%a → (uninitialize W m).1 !! a'' ≠ Some Monotemporary.
  Proof.
    intros Hcond.
    intros a'' Hle.
    destruct (m !! a'') eqn:Hsome.
    - assert (is_Some (m !! a'')) as Ha'';[eauto|]. apply Hcond in Ha'' as [Hmono Ha''].
      rewrite (uninitialize_std_sta_lookup_in _ _ _ p);auto.
    - intros Hcontr. rewrite uninitialize_std_sta_None_lookup in Hcontr;auto.
      assert (is_Some (m !! a'')) as [v Hv]. apply Hcond. split;auto.
      rewrite Hsome in Hv. done.
  Qed.

  Lemma valid_uninitialized_condition_weak W m a p g b e b' (w : Word) :
    pwlU p = true → isU p = true → (b' <= b)%a →
    (∀ a' : Addr, is_Some (m !! a') ↔ (W.1 !! a' = Some Monotemporary) ∧ (b' <= a')%a) →
    interp W (inr (p,g,b,e,a),w) -∗ ⌜∀ a', (b <= a' < e)%a → (∃ w, (uninitialize W m).1 !! a' = Some (Uninitialized w))⌝.
  Proof.
    iIntros (HpwlU HU Hle' Hcond) "#Hv".
    iDestruct (interp_eq with "Hv") as %<-.
    iIntros (a' [Hle Hlt]).
    iDestruct (writeLocalAllowedU_implies_local with "Hv") as %Hmono;auto.
    destruct g;inversion Hmono.
    destruct p;inversion HU;inversion HpwlU.
    - rewrite fixpoint_interp1_eq /=. iDestruct "Hv" as "[_ [Hv' Hv]]".
      destruct (decide (a <= a'))%a.
      + iDestruct (big_sepL_elem_of _ _ a' with "Hv") as "[Hcond #Hreg]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hreg" as %[Hreg | [? Hreg] ].
        { assert (is_Some (m !! a')) as [v Hv];[apply Hcond;split;auto;solve_addr|].
          rewrite (uninitialize_std_sta_lookup_in _ _ _ v);eauto. }
        { assert (m !! a' = None) as Hv;[|rewrite uninitialize_std_sta_None_lookup//;rewrite Hreg;eauto].
          destruct (m !! a') eqn:Hsome;auto. assert (is_Some (m!!a')) as Hissome;eauto.
          apply Hcond in Hissome as [Heq ?]. rewrite Heq in Hreg;inversion Hreg. }
      + iDestruct (big_sepL_elem_of _ _ a' with "Hv'") as "[Hcond #Hreg]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hreg" as %Hreg.
        assert (is_Some (m !! a')) as [v Hv];[apply Hcond;split;auto;solve_addr|].
        rewrite (uninitialize_std_sta_lookup_in _ _ _ v);eauto.
    - rewrite fixpoint_interp1_eq /=. iDestruct "Hv" as "[_ [Hv' Hv]]".
      destruct (decide (a <= a'))%a.
      + iDestruct (big_sepL_elem_of _ _ a' with "Hv") as "[Hcond #Hreg]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hreg" as %[Hreg | [? Hreg] ].
        { assert (is_Some (m !! a')) as [v Hv];[apply Hcond;split;auto;solve_addr|].
          rewrite (uninitialize_std_sta_lookup_in _ _ _ v);eauto. }
        { assert (m !! a' = None) as Hv;[|rewrite uninitialize_std_sta_None_lookup//;rewrite Hreg;eauto].
          destruct (m !! a') eqn:Hsome;auto. assert (is_Some (m!!a')) as Hissome;eauto.
          apply Hcond in Hissome as [Heq ?]. rewrite Heq in Hreg;inversion Hreg. }
      + iDestruct (big_sepL_elem_of _ _ a' with "Hv'") as "[Hcond #Hreg]".
        { apply elem_of_region_addrs. solve_addr. }
        iDestruct "Hreg" as %Hreg.
        assert (is_Some (m !! a')) as [v Hv];[apply Hcond;split;auto;solve_addr|].
        rewrite (uninitialize_std_sta_lookup_in _ _ _ v);eauto.
  Qed.

  Lemma valid_readAllowed_condition_weak W m a p g b e b' (w : Word) :
    readAllowed p = true → (b' <= b)%a →
    (∀ a' : Addr, is_Some (m !! a') ↔ (W.1 !! a' = Some Monotemporary) ∧ (b' <= a')%a) →
    interp W (inr (p,g,b,e,a),w) -∗ ⌜∀ a', (b <= a' < e)%a → ((uninitialize W m).1 !! a' = Some Permanent ∨ (∃ w, (uninitialize W m).1 !! a' = Some (Uninitialized w)))⌝.
  Proof.
    iIntros (Hra Hle' Hcond) "#Hv".
    iDestruct (interp_eq with "Hv") as %<-.
    iIntros (a' [Hle Hlt]).
    iDestruct (readAllowed_implies_region_conditions with "Hv") as "Hcond";auto.
    rewrite /region_conditions.
    destruct (pwl p).
    - iDestruct (big_sepL_elem_of _ _ a' with "Hcond") as "[Ha' #Hreg]".
      { apply elem_of_region_addrs. solve_addr. }
      rewrite /region_state_pwl_mono. iDestruct "Hreg" as %Hmono.
      iRight.
      assert (is_Some (m !! a')) as [v Hv];[apply Hcond;split;auto;solve_addr|].
      rewrite (uninitialize_std_sta_lookup_in _ _ _ v);eauto.
    - iDestruct (big_sepL_elem_of _ _ a' with "Hcond") as "[Ha' #Hreg]".
      { apply elem_of_region_addrs. solve_addr. }
      rewrite /region_state_nwl. iDestruct "Hreg" as %Hmono.
      destruct g.
      { iLeft;auto.
        assert (m !! a' = None) as Hv;[|rewrite uninitialize_std_sta_None_lookup//;rewrite Hreg;eauto].
        destruct (m !! a') eqn:Hsome;auto. assert (is_Some (m!!a')) as Hissome;eauto.
        apply Hcond in Hissome as [Heq ?]. rewrite Hmono in Heq. congruence. }
      { iLeft;auto.
        assert (m !! a' = None) as Hv;[|rewrite uninitialize_std_sta_None_lookup//;rewrite Hreg;eauto].
        destruct (m !! a') eqn:Hsome;auto. assert (is_Some (m!!a')) as Hissome;eauto.
        apply Hcond in Hissome as [Heq ?]. rewrite Hmono in Heq. congruence. }
      { destruct Hmono as [Hmono | Hmono].
        + assert (is_Some (m !! a')) as [v Hv];[apply Hcond;split;auto;solve_addr|].
          rewrite (uninitialize_std_sta_lookup_in _ _ _ v);eauto.
        + assert (m !! a' = None) as Hv;[|rewrite uninitialize_std_sta_None_lookup//;rewrite Hmono;eauto].
          destruct (m !! a') eqn:Hsome;auto. assert (is_Some (m!!a')) as Hissome;eauto.
          apply Hcond in Hissome as [Heq ?]. rewrite Hmono in Heq. congruence.
      }
  Qed.

  Lemma valid_uninitialized_condition W m a p g b e w :
    pwlU p = true → isU p = true →
    (∀ a' : Addr, is_Some (m !! a') ↔ (W.1 !! a' = Some Monotemporary) ∧ (b <= a')%a) →
    interp W (inr (p,g,b,e,a),w) -∗ ⌜∀ a', (b <= a' < e)%a → (∃ w, (uninitialize W m).1 !! a' = Some (Uninitialized w))⌝.
  Proof.
    iIntros (HpwlU HU Hcond) "#Hv".
    iApply valid_uninitialized_condition_weak;eauto.
    solve_addr.
  Qed.

  Lemma region_map_uninitialized_monotone W W' M Mρ a :
    related_sts_a_world W W' a →
    (∀ a'', (a <= a'')%a → Mρ !! a'' ≠ Some Monotemporary) →
    region_map_def M Mρ W -∗ region_map_def M Mρ W'.
  Proof.
    iIntros (Hrelated Hcond) "Hr".
    iApply big_sepM_mono; iFrame.
    iIntros (a' γ Hsome) "Hm".
    iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
    iExists ρ. iFrame. iSplitR;[auto|].
    destruct ρ.
    - destruct (decide (a' <= a))%a.
      2: { exfalso. assert (a <= a')%a as Hle;[solve_addr|].
           apply Hcond in Hle as ?. congruence. }
      iDestruct "Hm" as (φ Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v1 v2) "(Hl & Hl' & Hmono & Hφ)".
      iExists _. do 2 (iSplitR;[eauto|]).
      iFrame "#". iExists _,_.
      iDestruct "Hmono" as "#Hmono"; iFrame "∗ #";
        iApply "Hmono"; iFrame; auto.
      iPureIntro. eapply related_sts_a_weak_world;eauto.
    - iDestruct "Hm" as (φ Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v v') "(Hl & Hl' & #Hmono & Hφ)".
      iExists _. do 2 (iSplitR;[eauto|]).
      iFrame "∗ #". iExists _,_. iFrame "∗ #".
      iApply "Hmono"; iFrame "∗ #"; auto.
      iPureIntro.
      apply related_sts_pub_plus_priv_world.
      eapply related_sts_a_pub_plus_world;eauto.
    - done.
    - done.
    - done.
  Qed.

  Lemma related_sts_a_uninitialized W a a' w :
    (a <= a')%a →
    (∃ v, W.1 !! a' = Some (Uninitialized v)) →
    related_sts_a_world W (<s[a':=Uninitialized w]s>W) a.
  Proof.
    intros Hle Hcond.
    split;[|apply related_sts_pub_plus_refl].
    split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (i = a')).
      + subst. rewrite lookup_insert in Hy.
        destruct Hcond as [v Hv]. rewrite Hv in Hx.
        simplify_eq. right with Monotemporary.
        rewrite decide_True;auto. left. constructor.
        eright;[|left]. rewrite decide_True;auto. right. constructor.
      + rewrite lookup_insert_ne// in Hy. rewrite Hx in Hy;inversion Hy. left.
  Qed.

  Lemma uninitialize_open_region_change E W a a' φ v w w' `{∀ Wv, Persistent (φ Wv)}:
    (a <= a')%a →
    (∀ a'', (a <= a'')%a → W.1 !! a'' ≠ Some Monotemporary) →
    rel a' φ
    ∗ open_region a' W
    ∗ sts_full_world W
    ∗ a' ↦ₐ w
    ∗ a' ↣ₐ w'
    ∗ sts_state_std a' (Uninitialized v)
    ={E}=∗
    region (<s[a':=Uninitialized (w,w')]s> W) ∗ sts_full_world (<s[a':=Uninitialized (w,w')]s> W).
  Proof.
    iIntros (Hle Hcond) "(#Hrel & Hreg & Hsts & Ha & Ha' & Hstate)".
    rewrite open_region_eq /open_region_def rel_eq /rel_def REL_eq /REL_def RELS_eq /RELS_def.
    iDestruct "Hrel" as (γpred) "[Hown Hsaved]".
    iDestruct "Hreg" as (M Mρ) "(HM & #Hdom_m & #Hdom_mρ & Hpreds)".
    iDestruct "Hdom_m" as %Hdom_m; iDestruct "Hdom_mρ" as %Hdom_mρ.
    assert (Hle':=Hle).
    apply Hcond in Hle' as Hv.
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρ.
    iDestruct (reg_in γrel M with "[$HM $Hown]") as %HMeq.

    iAssert (⌜∀ a ρ, delete a' Mρ !! a = Some ρ ↔ delete a' W.1 !! a = Some ρ⌝)%I as %Hρcond.
    { iIntros (a0 ρ). rewrite iff_to_and.
      iSplit;iIntros (Ha').
      - destruct (decide (a0 = a'));[subst;rewrite lookup_delete in Ha';done|rewrite lookup_delete_ne// in Ha'].
        assert (is_Some (M !! a0)) as [γp HMa'];[apply elem_of_gmap_dom;rewrite -Hdom_mρ;apply elem_of_gmap_dom;eauto|].
        iDestruct (big_sepM_delete with "Hpreds") as "[Ha'' _]";[rewrite lookup_delete_ne// apply HMa'|].
        iDestruct "Ha''" as (ρ' Hlookup) "[Hρ' _]".
        iDestruct (sts_full_state_std with "Hsts Hρ'") as %Hρ';
          rewrite lookup_delete_ne// in Hlookup; rewrite lookup_delete_ne//; simplify_eq; auto.
      - destruct (decide (a0 = a'));[subst;rewrite lookup_delete in Ha';done|rewrite lookup_delete_ne// in Ha'].
        assert (is_Some (M !! a0)) as [γp HMa'];[apply elem_of_gmap_dom;rewrite -Hdom_m;apply elem_of_gmap_dom;eauto|].
        iDestruct (big_sepM_delete with "Hpreds") as "[Ha'' _]";[rewrite lookup_delete_ne// apply HMa'|].
        iDestruct "Ha''" as (ρ' Hlookup) "[Hρ' _]".
        iDestruct (sts_full_state_std with "Hsts Hρ'") as %Hρ'. rewrite Ha' in Hρ'. inversion Hρ'. auto. }

    iDestruct (region_map_insert_nonmonostatic (Uninitialized (w,w')) with "Hpreds") as "Hpreds";[intros;auto|].
    iDestruct (region_map_uninitialized_monotone _ (<s[a':=Uninitialized (w,w')]s>W) _ _ a with "Hpreds") as "Hpreds".
    { apply related_sts_a_uninitialized;auto. rewrite Hρ. eauto. }
    { intros a'' Ha''. destruct (decide (a'' = a')); subst;simplify_map_eq;eauto.
      intros Hcontr. specialize (Hρcond a'' Monotemporary).
      apply Hcond in Ha''. rewrite !lookup_delete_ne// in Hρcond. apply Hρcond in Hcontr. contradiction. }

    iMod (sts_update_std _ _ _ (Uninitialized (w,w')) with "Hsts Hstate") as "[Hsts Hstate]".
    iModIntro. iFrame.

    iDestruct (big_sepM_insert _ (delete a' M) a' with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _. iFrame.
      iSplit;[iPureIntro;apply lookup_insert|].
      iExists _. iFrame "∗ #". repeat iSplitR; auto. }
    rewrite -HMeq. rewrite region_eq /region_def RELS_eq /RELS_def. iExists _,_; iFrame. iPureIntro.
    repeat rewrite dom_insert_L. rewrite Hdom_m Hdom_mρ.
    assert (a' ∈ dom (gset Addr) M) as Hin;[rewrite HMeq dom_insert_L;clear;set_solver|].
    split;clear -Hin;set_solver.
  Qed.

End heap.
