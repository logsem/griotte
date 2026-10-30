From iris.algebra Require Import gmap agree auth excl csum excl_auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From iris.base_logic.lib Require Import ghost_map.
From griotte Require Export stdpp_extra griotte_lang.
From griotte Require Export sts world_std_sts region_keys.
From griotte Require Import resources.
Import uPred.

(** CMRA for heap and its predicates. Contains: *)
(* CMRA for relatedness between locations and saved prop names *)
(* CMRA for saved predicates *)
(** M_interp *)

(** The region maps of a compartment are over Iris [ghost_map]: a key names a
    saved predicate and a permission (see [region_maps.v]). *)
Class relGpreS Σ {Cname : CmptNameG} :=
  RelGpreS {
      relPreG_invPreG : invGpreS Σ;
      relPreG_saved_pred :: savedPredG Σ (WorldT * CmptName * LWord);
      relPreG_saved_pred_g :: savedPredG Σ (CmptName * LWord);
      relPreG_rel :: ghost_mapG Σ LAddr (gname * Perm);
    }.
#[export] Hint Mode relGpreS - - : typeclass_instances.

Class relGS Σ {Cname : CmptNameG} :=
  RelGS {
      relG_rel :: ghost_mapG Σ LAddr (gname * Perm);
      relG_saved_pred :: savedPredG Σ (WorldT * CmptName * LWord);
      relG_saved_pred_g :: savedPredG Σ (CmptName * LWord);
      (** the map of Permanent regions of a compartment *)
      γrel_g : CmptName -> gname;
      (** the local map of a thread and a compartment *)
      γrel_l : Thread -> CmptName -> gname;
    }.
#[export] Hint Mode relGS - - : typeclass_instances.

Definition relPreΣ {Cname : CmptNameG} :=
  #[ ghost_mapΣ LAddr (gname * Perm); savedPredΣ (CmptName * LWord) ].

#[export] Instance subG_relPreΣ {Σ} {Cname : CmptNameG}:
  subG relPreΣ Σ →
  invGpreS Σ →
  subG (savedPredΣ (WorldT * CmptName * LWord)) Σ →
  relGpreS Σ.
Proof. rewrite /relPreΣ; solve_inG. Qed.

Section relPre.
  Context {Σ:gFunctors} {Cname : CmptNameG} {relpreg : relGpreS Σ}.

  Lemma rel_rel_init :
    ⊢ |==> (∃ γrelC, ([∗ set] C ∈ CNames,
                        ghost_map_auth (γrelC C) 1 (∅ : gmap LAddr (gname * Perm)))).
  Proof.
    induction CNames as [|C' CNs HC' IHg] using set_ind_L.
    - iModIntro.
      iExists ( λ C, encode C).
      by iApply big_sepS_empty.
    - iMod IHg as (γrelC) "IH".
      iMod (ghost_map_alloc_empty (K:=LAddr) (V:=gname * Perm)) as (γrel') "Hrel".
      iModIntro.
      iExists (λ C, if (bool_decide (C = C')) then γrel' else γrelC C).
      iApply (big_sepS_union_2 with "[Hrel]").
      + iApply (big_sepS_singleton).
        by rewrite bool_decide_eq_true_2.
      + iApply (big_sepS_mono with "IH").
        iIntros (C HC) "Hr".
        rewrite bool_decide_eq_false_2; [done|set_solver].
  Qed.

  (** The Permanent maps, and the local maps of the user threads [k], for
      [k < nthreads]: one name each per compartment. The context-switch
      thread and the other user threads share names that are allocated and
      dropped. *)
  Lemma rel_init (nthreads : nat) :
    ⊢ |==> ∃ (relg: relGS Σ),
        ([∗ set] C ∈ CNames, ghost_map_auth (γrel_g C) 1 (∅ : gmap LAddr (gname * Perm))) ∗
        [∗ list] k ∈ seq 0 nthreads, [∗ set] C ∈ CNames,
          ghost_map_auth (γrel_l (UserThread k) C) 1 (∅ : gmap LAddr (gname * Perm)).
  Proof.
    iMod rel_rel_init as (γg) "Hg".
    iMod rel_rel_init as (γd) "_".
    iMod (alloc_thread_names _ γd nthreads rel_rel_init) as (γls) "Hls".
    iExists (RelGS _ _ _ _ _ γg
      (λ th, match th with UserThread k => nth k γls γd | CtxSwitch => γd end)).
    iModIntro. iFrame.
  Qed.

End relPre.

Section rel.

  Context {Σ:gFunctors}
    {Cname : CmptNameG}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  Lemma future_pub_mono_eq_pred `{!savedPredG Σ (WorldT * CmptName * LWord)} C γ φ φ' w :
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

End rel.

(* No Excl' here: do not want the valid option element, as this disallows us from changing the branch in the sum type *)
Lemma csum_alter_l_r {A : cmra} {C : ofe} (a : A) (c : C) : ✓ a → Cinl (Excl c) ~~> Cinr a.
Proof. intros Hv. by apply cmra_update_exclusive. Qed.

(* resources *)

(** The kind of a seal predicate: a Global-kind predicate is constant in the
    thread and the world; a Local-kind one is not supported yet. *)
Inductive seal_kind := SealGlobal | SealLocal.
#[global] Instance seal_kind_eq_dec : EqDecision seal_kind.
Proof. solve_decision. Qed.

Definition sealStoreUR :=
  gmapUR OType (csumR (exclR unitO) (agreeR (leibnizO (seal_kind * gname)))).

Class sealStoreG (Σ : gFunctors) {Cname : CmptNameG} := SealStoreG { (* Create record constructor for typeclass *)
    SG_sealStore :: inG Σ sealStoreUR;
    SG_saved_pred :: savedPredG Σ (Thread * WorldT * CmptName * LWord);
    SG_sealN : gname;
}.
#[export] Hint Mode sealStoreG - - : typeclass_instances.

Definition sealStorePreΣ {Cname : CmptNameG} :=
  #[ GFunctor sealStoreUR; savedPredΣ (Thread * WorldT * CmptName * LWord) ].

Class sealStorePreG (Σ : gFunctors) {Cname : CmptNameG} := {
    SG_sealStorePre :: inG Σ sealStoreUR;
    SG_saved_predPre :: savedPredG Σ (Thread * WorldT * CmptName * LWord);
}.
#[export] Hint Mode sealStorePreG - - : typeclass_instances.

#[export] Instance sealStoreG_preG {Cname : CmptNameG} `{sealStoreG Σ} : sealStorePreG Σ.
Proof. constructor. all: apply _. Defined.

#[global] Instance subG_sealStorePreΣ {Σ} {Cname : CmptNameG}:
  subG sealStorePreΣ Σ →
  sealStorePreG Σ.
Proof.
  intros HR. apply subG_inv in HR as [HR1 HR2].
  constructor; [apply subG_inG in HR1; exact HR1|apply _].
Qed.


Section Store.
  Context {Cname : CmptNameG} `{!sealStoreG Σ}
      `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  (** A seal predicate takes the thread of the holder of the sealed word. *)
  Definition seal_pred_def (o : OType) (κ : seal_kind)
      (P : Thread * WORLD * CmptName * LWord → iProp Σ) : iProp Σ :=
    ∃ γpred : gname, own SG_sealN ({[o := Cinr (to_agree ((κ, γpred) : leibnizO _))]})
                     ∗ saved_pred_own γpred DfracDiscarded P.
  #[local] Definition seal_pred_aux : seal (@seal_pred_def). Proof. by eexists. Qed.
  Definition seal_pred := seal_pred_aux.(unseal).
  #[local] Definition seal_pred_unseal : @seal_pred = @seal_pred_def :=
    seal_pred_aux.(seal_eq).

  #[global] Instance seal_pred_persistent o κ P : Persistent (seal_pred o κ P).
  Proof. rewrite seal_pred_unseal. apply _. Qed.

  Definition can_alloc_pred (o : OType) :=
    (own SG_sealN ({[o := Cinl (Excl ())]}))%I.

  Lemma seal_pred_agree o κ1 κ2 P1 P2 :
    seal_pred o κ1 P1 -∗ seal_pred o κ2 P2 -∗ ⌜κ1 = κ2⌝ ∗ (∀ x, ▷ (P1 x ≡ P2 x)).
  Proof.
    rewrite seal_pred_unseal.
    iIntros "(%γ1 & Hown1 & Hpred1) (%γ2 & Hown2 & Hpred2)".
    iDestruct (own_valid_2 with "Hown1 Hown2") as %Hv.
    rewrite singleton_op singleton_valid -Cinr_op Cinr_valid to_agree_op_valid_L in Hv.
    simplify_eq. iSplit; first done.
    iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed.

  Lemma seal_store_update_alloc (o : OType) (κ : seal_kind)
    (P : Thread * WORLD * CmptName * LWord → iProp Σ) :
    can_alloc_pred o ==∗ seal_pred o κ P.
  Proof.
    rewrite seal_pred_unseal /seal_pred_def /can_alloc_pred.
    iIntros "Hown".
    iMod (saved_pred_alloc P) as (γalloc) "#HsaveP"; first apply dfrac_valid_discarded.
    iMod (own_update _ _ ({[o := Cinr (to_agree ((κ, γalloc) : leibnizO _))]}) with "Hown").
    { apply singleton_update. by apply csum_alter_l_r. }
    iExists _; iFrame; done.
  Qed.

  (** The conditions on a seal predicate, by kind: a Global-kind predicate is
      constant in the thread and the world. *)
  Definition seal_kind_ok (κ : seal_kind) (C : CmptName)
      (P : Thread * WORLD * CmptName * LWord → iProp Σ) : iProp Σ :=
    ⌜∀ x, Persistent (P x)⌝ ∗
    match κ with
    | SealGlobal => □ ∀ t t' W W' w, P (t, W, C, w) -∗ P (t', W', C, w)
    | SealLocal => False
    end.

  #[global] Instance seal_kind_ok_persistent κ C P : Persistent (seal_kind_ok κ C P).
  Proof. destruct κ; apply _. Qed.

  (** The word a seal predicate is applied to: a Global-kind predicate sees
      the sealed word made Global. *)
  Definition norm (κ : seal_kind) (w : LWord) : LWord :=
    if κ is SealGlobal then lforce_global w else w.

End Store.

Notation "o ↪ₒ{ κ } P" := (seal_pred o κ P)
  (at level 20, format "o  ↪ₒ{ κ }  P") : bi_scope.

(* Initialize the seal store under an arbitrary name *)
Lemma seal_store_init {Cname : CmptNameG} `{sealStorePreG Σ'}  oset:
 ⊢ (|==> ∃ (_ : sealStoreG Σ'), ([∗ set] o ∈ oset, can_alloc_pred o) : iProp Σ')%I.
Proof.
  iMod (own_alloc (A:= sealStoreUR) ((gset_to_gmap (Cinl (Excl ())) oset): sealStoreUR)) as (γ) "H".
  { intros i. destruct (gset_to_gmap _ _ !! i) eqn:Heq; last done.
    apply lookup_gset_to_gmap_Some in Heq. by destruct Heq as [_ <-]. }
  iModIntro. iExists (SealStoreG _ _ _ _ γ).

  iInduction oset as [| x oset Hni] "IH" using set_ind_L; first done.
  iApply big_sepS_union; first set_solver.
  rewrite gset_to_gmap_union_singleton.
  rewrite insert_singleton_op. 2: rewrite lookup_gset_to_gmap_None; set_solver.
  iDestruct (own_op with "H") as "[Hx H]".
  iSplitL "Hx".
  - by iApply big_sepS_singleton.
  - by iApply "IH".
Qed.
