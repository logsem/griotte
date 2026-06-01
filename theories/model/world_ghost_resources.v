From iris.algebra Require Import gmap agree auth excl csum excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine Require Export stdpp_extra cap_lang.
From cap_machine Require Export sts world_std_sts.
Import uPred.

(** CMRA for heap and its predicates. Contains: *)
(* CMRA for relatedness between locations and saved prop names *)
(* CMRA for saved predicates *)
(** M_interp *)

(** REL: saved predicates associating Address to gname and permission *)
Definition relUR : ucmra :=
  (gmapUR Addr (agreeR (leibnizO (gname * Perm)))).
Definition relT :=
  (gmap Addr (leibnizO (gname * Perm))).

Class relGpreS Σ {Cname : CmptNameG} :=
  RelGpreS {
      relPreG_invPreG : invGpreS Σ;
      relPreG_saved_pred :: savedPredG Σ (WorldT * CmptName * Word);
      relPreG_rel :: inG Σ (authR relUR);
    }.

Class relGS Σ {Cname : CmptNameG} :=
  RelGS {
      relG_rel :: inG Σ (authR relUR);
      relG_saved_pred :: savedPredG Σ (WorldT * CmptName * Word);
      γrel : CmptName -> gname
    }.

Definition relPreΣ {Cname : CmptNameG} :=
  #[ GFunctor (authR relUR) ].

Instance subG_relPreΣ {Σ} {Cname : CmptNameG}:
  subG relPreΣ Σ →
  invGpreS Σ →
  subG (savedPredΣ (WorldT * CmptName * Word)) Σ →
  relGpreS Σ.
Proof. solve_inG. Qed.

Section REL_defs.
  Context {Σ:gFunctors} {Cname : CmptNameG} {relg : relGS Σ}.

  Definition REL_def (C : CmptName) (a : Addr) (γ : gname) (p : Perm) : iProp Σ :=
    own (γrel C) (◯ {[ a := to_agree (γ,p) ]}).
  Definition REL_aux : { x | x = @REL_def }. by eexists. Qed.
  Definition REL := proj1_sig REL_aux.
  Definition REL_eq : @REL = @REL_def := proj2_sig REL_aux.

  Definition RELS_def  (C : CmptName) (M : relT) : iProp Σ :=
   own (γrel C) (● (to_agree <$> M : relUR)).
  Definition RELS_aux : { x | x = @RELS_def }. by eexists. Qed.
  Definition RELS := proj1_sig RELS_aux.
  Definition RELS_eq : @RELS = @RELS_def := proj2_sig RELS_aux.

  Definition rel_def (C : CmptName) (a : Addr) (p : Perm)
    (φ : (WorldT * CmptName * Word) -> iProp Σ)
    : iProp Σ :=
    (∃ (γpred : gnameO), REL C a γpred p ∗ saved_pred_own γpred DfracDiscarded φ)%I.
  Definition rel_aux : { x | x = @rel_def }. by eexists. Qed.
  Definition rel := proj1_sig rel_aux.
  Definition rel_eq : @rel = @rel_def := proj2_sig rel_aux.
End REL_defs.

Section relPre.
  Context {Σ:gFunctors} {Cname : CmptNameG} {relpreg : relGpreS Σ}.


  Lemma rel_rel_init :
    ⊢ |==> (∃ γrelC, ([∗ set] C ∈ CNames, own (γrelC C) (● (to_agree <$> ∅)))).
  Proof.
    induction CNames using set_ind_L.
    - iModIntro.
      iExists ( λ C, encode C).
      by iApply big_sepS_empty.
    - iMod IHg as (?) "IH".
      iMod (own_alloc (A:= (authR relUR)) (● (to_agree <$> (∅: relT) : relUR))) as (γrel') "Hrel"
      ; first by apply auth_auth_valid.
      iModIntro.
      iExists (λ C, if (bool_decide (C = x)) then γrel' else γrelC C).
      iApply (big_sepS_union_2 with "[Hrel]").
      + iApply (big_sepS_singleton).
        by rewrite bool_decide_eq_true_2.
      + iApply (big_sepS_mono with "IH").
        iIntros (C HC) "Hr".
        rewrite bool_decide_eq_false_2; [done|set_solver].
  Qed.

  Lemma rel_init :
    ⊢ |==> ∃ (relg: relGS Σ), [∗ set] C ∈ CNames, RELS C (∅ : relT).
  Proof.
    iMod rel_rel_init as (γ) "H".
    iExists (RelGS _ _ _ _ _). rewrite RELS_eq /RELS_def. done.
  Qed.

End relPre.

Section rel.

  Context {Σ:gFunctors}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  Global Instance REL_persistent (C : CmptName) (a : Addr) (γ : gname) (p : Perm) :
    Persistent (REL C a γ p).
  Proof. rewrite REL_eq /REL_def.
         apply _.
  Qed.

  Global Instance rel_persistent (C : CmptName) (a : Addr) (p : Perm)
    (φ : (WORLD * CmptName * Word) -> iProp Σ) :
    Persistent (rel C a p φ).
  Proof. rewrite rel_eq /rel_def REL_eq /REL_def.
         apply _.
  Qed.


  Lemma reg_in
    (C : CmptName) (M : relT)
    (a : Addr) (γ : gnameO) (p : leibnizO Perm) :
    RELS C M ∗ REL C a γ p
    -∗ ⌜M = <[a := (γ,p)]>(delete a M)⌝.
  Proof.
    iIntros "[H1 H2]".
    rewrite REL_eq RELS_eq /REL_def /RELS_def.
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro.
    apply auth_both_valid_discrete in Hv; destruct Hv as [Hv1 Hv2].
    specialize (Hv2 a).
    apply singleton_included_l in Hv1.
    destruct Hv1 as (y & Heq & Hi).
    revert Hv2; rewrite Heq => Hv2.
    revert Hi; rewrite Some_included_total => Hi.
    apply to_agree_uninj in Hv2 as [γp Hγp].
    revert Hi Heq; rewrite -Hγp => Hi Heq.
    apply to_agree_included in Hi; subst.
    revert Heq; rewrite -Hi => Heq.
    rewrite insert_delete_eq insert_id /leibniz_equiv_iff => //; auto.
    revert Heq. rewrite lookup_fmap fmap_Some_equiv =>Hγp'.
    destruct Hγp' as [γp' [? Hrγp'] ].
    apply to_agree_inj, leibniz_equiv_iff in Hrγp' as <-.
    done.
  Qed.

  Lemma reg_get (C : CmptName) (M : relT) (a : Addr)
    (γ : gnameO) (p : leibnizO Perm) :
    RELS C M ∧ ⌜M !! a = Some (γ,p)⌝
    ==∗
    RELS C M ∗ REL C a γ p.
  Proof.
    iIntros "(HR & %Hγp)".
    rewrite RELS_eq /RELS_def REL_eq /REL_def.
    iApply own_op.
    iApply (own_update with "HR").
    apply auth_update_dfrac_alloc; auto.
    - apply gmap_core_id.
      intros; apply agree_core_id.
    - apply singleton_included_l.
      exists (to_agree (γ,p)). split; auto.
      rewrite lookup_fmap. apply fmap_Some_equiv.
      exists (γ,p). split; auto.
  Qed.


  Lemma update_RELS {invg: invGS Σ}
    (E : coPset) (C : CmptName) (M : relT)
    (a : Addr) (γ : gname) (p : Perm) :
    M !! a = None ->
    RELS C M ={E}=∗
    RELS C (<[a := (γ,p)]> M) ∗ REL C a γ p.
  Proof.
    iIntros (HMa) "HRELS".
    rewrite RELS_eq REL_eq /RELS_def /REL_def.
    iMod (own_update _ _
            (● (<[a:=to_agree (γ,p)]> (to_agree <$> M : relUR)) ⋅ ◯ ({[a:=to_agree (γ,p)]}))
           with "HRELS") as "[HRELS HREL]".
    - apply auth_update_alloc.
      apply (alloc_singleton_local_update (to_agree <$> M)); last done.
      rewrite lookup_fmap HMa; done.
    - rewrite fmap_insert. by iFrame.
  Qed.

  Lemma rels_agree C a γ1 γ2 p1 p2 :
    REL C a γ1 p1 ∗ REL C a γ2 p2 -∗ ⌜γ1 = γ2⌝ ∧ ⌜p1 = p2⌝.
  Proof.
    rewrite REL_eq /REL_def.
    iIntros "[Hγ1 Hγ2]".
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
    iPureIntro.
    rewrite -auth_frag_op singleton_op in Hval.
    apply pair_inj.
    apply (to_agree_op_inv_L (A:=leibnizO _)).
    eapply singleton_valid, auth_frag_valid, Hval.
  Qed.

  Lemma rel_agree C a φ1 φ2 p1 p2 :
    rel C a p1 φ1 ∗ rel C a p2 φ2 -∗ ⌜p1 = p2⌝ ∗ (∀ x, ▷ (φ1 x ≡ φ2 x)).
  Proof.
    iIntros "[Hr1 Hr2]".
    rewrite rel_eq /rel_def.
    iDestruct "Hr1" as (γ1) "[Hrel1 Hpred1]".
    iDestruct "Hr2" as (γ2) "[Hrel2 Hpred2]".
    iDestruct (rels_agree with "[$Hrel1 $Hrel2]") as %[-> ->].
    iSplit ; first done.
    iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed.

  Lemma RELS_sub C M (m : gmap Addr Word) :
    RELS C M -∗ ([∗ map] a↦_ ∈ m, ∃ p φ, rel C a p φ) -∗
    ⌜∀ (a : Addr), is_Some(m !! a) -> is_Some(M !! a)⌝.
  Proof.
    iIntros "HM Hmap".
    iIntros (a [x Hx]).
    iDestruct (big_sepM_delete _ _ a with "Hmap") as "[Ha _]";eauto.
    iDestruct "Ha" as (p φ) "#Hrel".
    rewrite rel_eq /rel_def.
    iDestruct "Hrel" as (γpred) "#[Hown _]".
    iDestruct (reg_in with "[$HM $Hown]") as %HMeq; eauto.
    rewrite HMeq. rewrite lookup_insert_eq. eauto.
  Qed.


  Lemma future_pub_mono_eq_pred C γ φ φ' w :
    saved_pred_own γ DfracDiscarded φ
    -∗ saved_pred_own γ DfracDiscarded φ'
    -∗ ▷ future_pub_mono C φ w
    -∗ ▷ future_pub_mono C φ' w.
  Proof.
    iIntros "#Hφ #Hφ' #Hmono".
    iIntros (W0 W1 Hrelated).
    iDestruct (saved_pred_agree _ _ _ _ _ (W0,C,w) with "Hφ Hφ'") as "#Hφeq0".
    iDestruct (saved_pred_agree _ _ _ _ _ (W1,C,w) with "Hφ Hφ'") as "#Hφeq1".
    iNext; iModIntro.
    iIntros "Hφv".
    iRewrite - "Hφeq0" in "Hφv"; iRewrite - "Hφeq1".
    iApply "Hmono"; eauto.
  Qed.

  Lemma mono_pub_eq_pred C γ φ φ' :
    saved_pred_own γ DfracDiscarded φ
    -∗ saved_pred_own γ DfracDiscarded φ'
    -∗ ▷ mono_pub C φ
    -∗ ▷ mono_pub C φ'.
  Proof.
    iIntros "#Hφ #Hφ' #Hmono".
    iIntros (w).
    iSpecialize ("Hmono" $! w).
    iApply (future_pub_mono_eq_pred with "Hφ Hφ' Hmono");auto.
  Qed.

  Lemma future_priv_mono_eq_pred C γ φ φ' w :
    saved_pred_own γ DfracDiscarded φ
    -∗ saved_pred_own γ DfracDiscarded φ'
    -∗ ▷ future_priv_mono C φ w
    -∗ ▷ future_priv_mono C φ' w.
  Proof.
    iIntros "#Hφ #Hφ' #Hmono".
    iIntros (W0 W1 Hrelated).
    iDestruct (saved_pred_agree _ _ _ _ _ (W0,C,w) with "Hφ Hφ'") as "#Hφeq0".
    iDestruct (saved_pred_agree _ _ _ _ _ (W1,C,w) with "Hφ Hφ'") as "#Hφeq1".
    iNext; iModIntro.
    iIntros "Hφv".
    iRewrite - "Hφeq0" in "Hφv"; iRewrite - "Hφeq1".
    iApply "Hmono"; eauto.
  Qed.

  Lemma mono_priv_eq_pred C γ p φ φ':
    saved_pred_own γ DfracDiscarded φ
    -∗ saved_pred_own γ DfracDiscarded φ'
    -∗ ▷ mono_priv C φ p
    -∗ ▷ mono_priv C φ' p.
  Proof.
    iIntros "#Hφ #Hφ' #Hmono".
    iIntros (w Hglobalw).
    iSpecialize ("Hmono" $! w Hglobalw).
    iApply (future_priv_mono_eq_pred with "Hφ Hφ' Hmono");auto.
  Qed.

  Lemma future_pub_mono_eq_pred_rel C γ p p' φ φ' w :
    rel C γ p φ
    -∗ rel C γ p' φ'
    -∗ ▷ future_pub_mono C φ w
    -∗ ▷ future_pub_mono C φ' w.
  Proof.
    iIntros "#Hrel #Hrel' #Hmono".
    iIntros (W0 W1 Hrelated).
    iDestruct (rel_agree C _ φ φ' with "[$Hrel $Hrel']") as "[_ #Hφeq]".
    iNext; iModIntro.
    iIntros "Hφv".
    iDestruct ("Hφeq" $! (W0,C,w)) as "Hφeq0" .
    iDestruct ("Hφeq" $! (W1,C,w)) as "Hφeq1" .
    iRewrite - "Hφeq0" in "Hφv"; iRewrite - "Hφeq1".
    iApply "Hmono"; eauto.
  Qed.

  Lemma mono_pub_eq_pred_rel C γ p p' φ φ' :
    rel C γ p φ
    -∗ rel C γ p' φ'
    -∗ ▷ mono_pub C φ
    -∗ ▷ mono_pub C φ'.
  Proof.
    iIntros "#Hrel #Hrel' #Hmono".
    iIntros (w).
    iSpecialize ("Hmono" $! w).
    iApply (future_pub_mono_eq_pred_rel with "Hrel Hrel' Hmono"); eauto.
  Qed.

  Lemma future_priv_mono_eq_pred_rel C γ p p' φ φ' w :
    rel C γ p φ
    -∗ rel C γ p' φ'
    -∗ ▷ future_priv_mono C φ w
    -∗ ▷ future_priv_mono C φ' w.
  Proof.
    iIntros "#Hrel #Hrel' #Hmono".
    iIntros (W0 W1 Hrelated).
    iDestruct (rel_agree _ _ φ φ' with "[$Hrel $Hrel']") as "[_ #Hφeq]".
    iNext; iModIntro.
    iIntros "Hφv".
    iDestruct ("Hφeq" $! (W0,C,w)) as "Hφeq0" .
    iDestruct ("Hφeq" $! (W1,C,w)) as "Hφeq1" .
    iRewrite - "Hφeq0" in "Hφv"; iRewrite - "Hφeq1".
    iApply "Hmono"; eauto.
  Qed.

  Lemma mono_priv_eq_pred_rel C γ p p' φ φ' :
    rel C γ p φ
    -∗ rel C γ p' φ'
    -∗ ▷ mono_priv C φ p
    -∗ ▷ mono_priv C φ' p.
  Proof.
    iIntros "#Hrel #Hrel' #Hmono".
    iIntros (w Hglobalw).
    iSpecialize ("Hmono" $! w Hglobalw).
    iApply (future_priv_mono_eq_pred_rel with "Hrel Hrel' Hmono"); eauto.
  Qed.

End rel.

(* No Excl' here: do not want the valid option element, as this disallows us from changing the branch in the sum type *)
Lemma csum_alter_l_r {A : cmra} {C : ofe} (a : A) (c : C) : ✓ a → Cinl (Excl c) ~~> Cinr a.
Proof.
  intros Hv. by apply cmra_update_exclusive.
Qed.

Lemma Excl_included_false : ∀ {A : ofe} {a b : A}, Excl a ≼ Excl b → False.
Proof.
  intros * Hi. by apply (exclusive_included _ _ Hi).
Qed.

(* resources *)

Class sealStoreG Σ := SealStoreG { (* Create record constructor for typeclass *)
    SG_sealStore ::  inG Σ (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)));
    SG_sealN : gname;
}.

Definition sealStorePreΣ :=
  #[ GFunctor (gmapUR OType (csumR (exclR unitO) (agreeR gnameO))) ].

Class sealStorePreG Σ := {
    SG_sealStorePre ::  inG Σ (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)));
}.

Instance sealStoreG_preG `{sealStoreG Σ} : sealStorePreG Σ.
Proof. constructor. all: apply _. Defined.

Global Instance subG_sealStorePreΣ {Σ}:
  subG sealStorePreΣ Σ →
  sealStorePreG Σ.
Proof. solve_inG. Qed.

(* Auxiliary lemma's about gmap domains *)
Lemma gmap_none_convert `{Countable K} {A B: Type} (g1 : gmap K A) (g2 : gmap K B) (i : K): dom g1 = dom g2 →
    g1 !! i = None → g2 !! i = None.
Proof.
  intros Hdom Hnon.
  apply not_elem_of_dom in Hnon.
  rewrite Hdom in Hnon.
  by apply not_elem_of_dom.
Qed.

Lemma gmap_isSome_convert `{Countable K} {A B: Type} (g1 : gmap K A) (g2 : gmap K B) (i : K): dom g1 = dom g2 →
    is_Some (g1 !! i) → is_Some (g2 !! i).
Proof.
  intros Hdom Hnon.
  apply elem_of_dom in Hnon.
  rewrite Hdom in Hnon.
  by apply elem_of_dom.
Qed.

Section Store.
  Context `{!sealStoreG Σ}
      {Cname : CmptNameG}
      {stsg : STSG Addr region_type OType Word Σ}
      {relg : relGS Σ}.
  Implicit Types W : WORLD.

  Definition seal_pred (o : OType) (P : WORLD * CmptName * Word → iProp Σ) :=
    (∃ γpred: gname, own SG_sealN ({[o := Cinr (to_agree γpred)]})
                     ∗ saved_pred_own γpred DfracDiscarded P)%I.
  Global Instance seal_pred_persistent i P : Persistent (seal_pred i P).
  Proof. apply _. Qed.
  Definition can_alloc_pred (o : OType) :=
    (own SG_sealN ({[o := Cinl (Excl ())]}))%I.

  Lemma seal_pred_agree o P P':
    seal_pred o P -∗ seal_pred o P' -∗ (∀ x, ▷ (P x ≡ P' x)).
  Proof.
    iIntros "Hr1 Hr2".
    rewrite /seal_pred.
    iDestruct "Hr1" as (γ1) "[Hown1 Hpred1]".
    iDestruct "Hr2" as (γ2) "[Hown2 Hpred2]".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hv.
    rewrite singleton_op singleton_valid -Cinr_op Cinr_valid  to_agree_op_valid_L in Hv. subst.
    iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed.

  Lemma seal_store_update_alloc (o : OType) (P : WORLD * CmptName * Word → iProp Σ):
   can_alloc_pred o ==∗ seal_pred o P.
  Proof.
    rewrite /seal_pred /can_alloc_pred.
    iIntros "Hown".
    iMod (saved_pred_alloc P) as (γalloc) "#HsaveP"; first apply dfrac_valid_discarded.


    iMod (own_update _ _ ({[o := Cinr (to_agree γalloc)]}) with "Hown").
    { apply singleton_update. eauto. by apply csum_alter_l_r. }
    iExists _; iFrame; done.
  Qed.


End Store.

(* Initialize the seal store under an arbitrary name *)
Lemma seal_store_init `{sealStorePreG Σ'}  oset:
 ⊢ (|==> ∃ (_ : sealStoreG Σ'), ([∗ set] o ∈ oset, can_alloc_pred o) : iProp Σ')%I.
Proof.
  iMod (own_alloc (A:= (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)))) ((gset_to_gmap (Cinl (Excl ())) oset): gmap OType (csumR (exclR unitO) (agreeR gnameO)))) as (γ) "H".
  { intros i. destruct (gset_to_gmap _ _ !! i) eqn:Heq; last done.
    apply lookup_gset_to_gmap_Some in Heq. by destruct Heq as [_ <-]. }
  iModIntro. iExists (SealStoreG _ _ γ).

  iInduction oset as [| x oset Hni] "IH" using set_ind_L; first done.
  iApply big_sepS_union; first set_solver.
  rewrite gset_to_gmap_union_singleton.
  rewrite insert_singleton_op. 2: rewrite lookup_gset_to_gmap_None; set_solver.
  iDestruct (own_op with "H") as "[Hx H]".
  iSplitL "Hx".
  - by iApply big_sepS_singleton.
  - by iApply "IH".
Qed.
