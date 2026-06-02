From iris.algebra Require Import gmap agree auth excl csum excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.own invariants na_invariants saved_prop.
From cap_machine Require Export cap_lang sts.
(* import [stdpp.countable] after [cap_machine.cap_lang]; this way [encode] and
   [decode] refer to [countable.encode] and [countable.decode], instead of
   [cap_lang.encode]/[cap_lang.decode]. *)
From stdpp Require Import countable list_relations.
From stdpp Require Import base.
Import uPred.

Section region_invariants_definitions.

  (* We will first define the standard STS for the shared part of the heap *)
  Inductive region_type :=
  | Temporary
  | Permanent
  | Revoked.

  Global Instance LeibnizEquiv_region_type : @LeibnizEquiv region_type (@eq region_type).
  Proof. rewrite /LeibnizEquiv; intros ? ? ?; done. Defined.

  Inductive std_rel_pub : region_type -> region_type -> Prop :=
  | Std_pub_Revoked_Temporary : std_rel_pub Revoked Temporary
  | Std_pub_Revoked_Permanent : std_rel_pub Revoked Permanent.

  Inductive std_rel_priv : region_type -> region_type -> Prop :=
  | Std_priv_Temporary_Revoked : std_rel_priv Temporary Revoked
  | Std_priv_Temporary_Permanent : std_rel_priv Temporary Permanent.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT STD TRANSITIONS -------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Lemma std_rel_pub_Permanent (ρ : region_type) :
    std_rel_pub Permanent ρ → ρ = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_rtc_Permanent (ρ1 ρ2 : region_type) :
    ρ1 = Permanent →
    rtc std_rel_pub ρ1 ρ2 → ρ2 = Permanent.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_pub_Permanent; auto.
  Qed.

  Lemma std_rel_priv_Permanent (ρ : region_type) :
    std_rel_priv Permanent ρ → ρ = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Permanent (ρ1 ρ2 : region_type) :
    ρ1 = Permanent →
    rtc std_rel_priv ρ1 ρ2 → ρ2 = Permanent.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_priv_Permanent; auto.
  Qed.

  Lemma std_rel_Permanent (ρ : region_type) :
    (std_rel_pub Permanent ρ ∨ std_rel_priv Permanent ρ) → ρ = Permanent.
  Proof.
    intros Hrel.
    destruct Hrel.
    + by apply std_rel_pub_Permanent.
    + by apply std_rel_priv_Permanent.
  Qed.

  Lemma std_rtc_Permanent (ρ1 ρ2 : region_type) :
    ρ1 = Permanent →
    rtc (λ x y : region_type, std_rel_pub x y ∨ std_rel_priv x y) ρ1 ρ2 → ρ2 = Permanent.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_Permanent; auto.
  Qed.

  Lemma std_rel_priv_Revoked (ρ : region_type) :
    std_rel_priv Revoked ρ → ρ = Revoked.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Revoked (ρ1 ρ2 : region_type) :
    ρ1 = Revoked →
    rtc std_rel_priv ρ1 ρ2 → ρ2 = Revoked.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_priv_Revoked; auto.
  Qed.

  Lemma std_rel_rtc_Permanent (ρ1 ρ2 : region_type) :
    ρ1 = Permanent →
    rtc (λ ρ0 ρ0' : region_type, std_rel_pub ρ0 ρ0' ∨ std_rel_priv ρ0 ρ0') ρ1 ρ2 →
    ρ2 = Permanent.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc as [|ρ0 ρ1 ρ2 Hrel];auto.
    subst. destruct Hrel as [Hrel | Hrel].
    - apply std_rel_pub_Permanent in Hrel; auto.
    - apply std_rel_priv_Permanent in Hrel; auto.
  Qed.

  Lemma std_rel_pub_Temporary (ρ : region_type) :
    std_rel_pub Temporary ρ → ρ = Temporary.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_rtc_Temporary (ρ1 ρ2 : region_type) :
    ρ1 = Temporary →
    rtc std_rel_pub ρ1 ρ2 → ρ2 = Temporary.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply IHHrtc. apply std_rel_pub_Temporary; auto.
  Qed.

  Lemma std_rel_pub_Revoked (ρ : region_type) :
    std_rel_pub Revoked ρ → ρ = Permanent ∨ ρ = Temporary.
  Proof.
    intros Hrel.
    inversion Hrel; auto.
  Qed.

  Lemma std_rel_pub_rtc_Revoked (ρ1 ρ2 : region_type) :
    ρ1 = Revoked →
    rtc std_rel_pub ρ1 ρ2 → ρ2 = Permanent ∨ ρ2 = Temporary ∨ ρ2 = Revoked.
  Proof.
    intros Hρ1 Hrtc.
    inversion Hrtc; subst; auto.
    apply std_rel_pub_Revoked in H as [-> | ->];auto.
    - left. eapply std_rel_pub_rtc_Permanent;eauto.
    - right. left. eapply std_rel_pub_rtc_Temporary;eauto.
  Qed.

  (* ------------------------- DEFINITION STD STS CLASS -------------------------- *)

  Global Program Instance sts_std : STS_STD region_type :=
    {|
      Rpub := std_rel_pub;
      Rpriv := std_rel_priv;
    |}.

  Global Instance region_type_EqDecision : EqDecision region_type :=
    (fun x y => match x, y with
             | Permanent, Permanent
             | Revoked, Revoked
             | Temporary, Temporary => left eq_refl
             | _, _ => ltac:(right; auto)
             end).

  Global Instance region_type_countable : Countable region_type.
  Proof.
    set encode := fun ty => match ty with
                         | Temporary => 1
                         | Permanent => 2
                         | Revoked => 3
                         end%positive.
    set decode := (fun n =>
                     if decide (n = 1) then Some Temporary
                     else if decide (n = 2) then Some Permanent
                          else if decide (n = 3) then Some Revoked
                               else None)%positive.
    eapply (Build_Countable _ _ encode decode).
    intro ty. destruct ty; try reflexivity;
    unfold encode, decode;
    repeat (match goal with |- context [ decide ?x ] =>
                            destruct (decide x); [ try (exfalso; lia) | ] end).
  Qed.

End region_invariants_definitions.

Notation STS := (leibnizO (STS_states * STS_rels)).
Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
Notation SEAL_STD := (leibnizO (seals_std OType Word)).
Notation WORLD := (prodO (prodO STS_STD STS) SEAL_STD).
Notation WorldT := (((STS_std_states Addr region_type) * (STS_states * STS_rels) * (seals_std OType Word)) : Type).

(** CMRA for heap and its predicates. Contains: *)
(* CMRA for relatedness between locations and saved prop names *)
(* CMRA for saved predicates *)
(** M_interp *)
Definition relUR : ucmra :=
  (gmapUR Addr (agreeR (leibnizO (gname * Perm)))).
Definition relT :=
  (gmap Addr (leibnizO (gname * Perm))).

Class heapGpreS Σ {Cname : CmptNameG} := HeapGpreS {
  heapPreG_invPreG : invGpreS Σ;
  heapPreG_saved_pred ::
    savedPredG Σ ( WorldT * CmptName * Word);
  heapPreG_rel :: inG Σ (authR relUR);
}.

Class heapGS Σ {Cname : CmptNameG} := HeapGS {
  heapG_saved_pred ::
    savedPredG Σ (WorldT * CmptName * Word);
  heapG_rel :: inG Σ (authR relUR);
  γrel : CmptName -> gname
}.

Definition heapPreΣ {Cname : CmptNameG} :=
  #[ GFunctor (authR relUR) ].

Instance subG_heapPreΣ {Σ} {Cname : CmptNameG}:
  subG heapPreΣ Σ →
  invGpreS Σ →
  subG (savedPredΣ (WorldT * CmptName * Word)) Σ →
  heapGpreS Σ.
Proof. solve_inG. Qed.

Section REL_defs.
  Context {Σ:gFunctors} {Cname : CmptNameG} {heapg : heapGS Σ}.

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

  Definition rel_def (C : CmptName) (a : Addr) (p : Perm) (φ : (WorldT * CmptName * Word) -> iProp Σ)
    : iProp Σ :=
    (∃ (γpred : gnameO), REL C a γpred p
                       ∗ saved_pred_own γpred DfracDiscarded φ)%I.
  Definition rel_aux : { x | x = @rel_def }. by eexists. Qed.
  Definition rel := proj1_sig rel_aux.
  Definition rel_eq : @rel = @rel_def := proj2_sig rel_aux.

  Global Instance REL_persistent (C : CmptName) (a : Addr) (γ : gname) (p : Perm) :
    Persistent (REL C a γ p).
  Proof. rewrite REL_eq /REL_def. apply _. Qed.

  Global Instance rel_persistent (C : CmptName) (a : Addr) (p : Perm)
    (φ : (WORLD * CmptName * Word) -> iProp Σ) :
    Persistent (rel C a p φ).
  Proof. rewrite rel_eq /rel_def REL_eq /REL_def. apply _. Qed.


End REL_defs.

Section heapPre.
  Context {Σ:gFunctors} {Cname : CmptNameG} {heappreg : heapGpreS Σ}.


  Lemma heap_rel_init :
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

  Lemma heap_init :
    ⊢ |==> ∃ (heapg: heapGS Σ), [∗ set] C ∈ CNames, RELS C (∅ : relT).
  Proof.
    iMod heap_rel_init as (γ) "H".
    iExists (HeapGS _ _ _ _ _). rewrite RELS_eq /RELS_def. done.
  Qed.

End heapPre.

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
    (* SG_storedPreds ::  savedPredG Σ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word); *)
    SG_sealN : gname;
}.

Definition sealStorePreΣ :=
  #[ GFunctor (gmapUR OType (csumR (exclR unitO) (agreeR gnameO))) ].
     (* ; savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word)]. *)

Class sealStorePreG Σ := {
    SG_sealStorePre ::  inG Σ (gmapUR OType (csumR (exclR unitO) (agreeR gnameO)));
    (* SG_storedPredsPre ::  savedPredG Σ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word); *)
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
      {heapg : heapGS Σ}.
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

Section mono.

  Context {Σ:gFunctors}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type OType Word Σ}
    {heapg : heapGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.


  Definition future_pub_mono (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_pub_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Definition future_priv_mono (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_priv_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Lemma future_priv_mono_is_future_pub_mono (C : CmptName) (φ: (WORLD * CmptName * Word) → iProp Σ) v :
    future_priv_mono C φ v -∗ future_pub_mono C φ v.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrelated) "Hφ".
    iApply "H"; eauto.
    iPureIntro; eauto using related_sts_pub_priv_world.
  Qed.

  Definition mono_pub (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) :=
    (∀ (w : Word), future_pub_mono C φ w)%I.
  Definition mono_priv (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (p : Perm) :=
    (∀ (w : Word), ⌜canStore p w = true⌝ -∗ future_priv_mono C φ w)%I.

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

End mono.
