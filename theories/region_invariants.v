From iris.algebra Require Import gmap agree auth.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine Require Export stdpp_extra cap_lang sts rules_base.
(* import [stdpp.countable] before [cap_machine.cap_lang]; this way [encode] and
   [decode] refer to [countable.encode] and [countable.decode], instead of
   [cap_lang.encode]/[cap_lang.decode]. *)
From stdpp Require Import countable.
Import uPred.

(* We will first define the standard STS for the shared part of the heap *)
Inductive region_type :=
| Temporary
| Permanent
| Revoked
| Frozen of gmap Addr Word.

Inductive std_rel_pub : region_type -> region_type -> Prop :=
| Std_pub_Revoked_Temporary : std_rel_pub Revoked Temporary
| Std_pub_Revoked_Permanent : std_rel_pub Revoked Permanent
| Std_pub_Frozen_Temporary m : std_rel_pub (Frozen m) Temporary .

Inductive std_rel_priv : region_type -> region_type -> Prop :=
| Std_priv_Temporary_Frozen m : std_rel_priv Temporary (Frozen m)
| Std_priv_Temporary_Revoked : std_rel_priv Temporary Revoked
| Std_priv_Temporary_Permanent : std_rel_priv Temporary Permanent.

Global Instance sts_std : STS_STD region_type :=
  {| Rpub := std_rel_pub; Rpriv := std_rel_priv |}.

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
    savedPredG Σ (
      ((STS_std_states Addr region_type) * (STS_states * STS_rels)) *
        CmptName *
        Word);
  heapPreG_rel :: inG Σ (authR relUR);
}.

Class heapGS Σ {Cname : CmptNameG} := HeapGS {
  heapG_saved_pred ::
    savedPredG Σ (
      ((STS_std_states Addr region_type) * (STS_states * STS_rels)) *
        CmptName *
        Word);
  heapG_rel :: inG Σ (authR relUR);
  γrel : CmptName -> gname
}.

Definition heapPreΣ {Cname : CmptNameG} :=
  #[ GFunctor (authR relUR) ].

Instance subG_heapPreΣ {Σ} {Cname : CmptNameG}:
  subG heapPreΣ Σ →
  invGpreS Σ →
  subG (savedPredΣ
          ((((STS_std_states Addr region_type) * (STS_states * STS_rels))) *
        CmptName *
        Word)) Σ →
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

  Definition rel_def (C : CmptName) (a : Addr) (p : Perm)
    (φ : (((STS_std_states Addr region_type) * (STS_states * STS_rels)) *
        CmptName *
        Word) -> iProp Σ)
    : iProp Σ :=
    (∃ (γpred : gnameO), REL C a γpred p
                       ∗ saved_pred_own γpred DfracDiscarded φ)%I.
  Definition rel_aux : { x | x = @rel_def }. by eexists. Qed.
  Definition rel := proj1_sig rel_aux.
  Definition rel_eq : @rel = @rel_def := proj2_sig rel_aux.
End REL_defs.

Section heapPre.
  (* TODO wsat_alloc had been changed in Iris 4.0.
     Fixed using Hc
   *)
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

Section heap.

  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type Σ}
    {heapg : heapGS Σ}
    `{MP: MachineParameters}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Global Instance region_type_EqDecision : EqDecision region_type :=
    (fun x y => match x, y with
             | Permanent, Permanent
             | Revoked, Revoked
             | Temporary, Temporary => left eq_refl
             | Frozen m1, Frozen m2 => ltac:(solve_decision)
             | _, _ => ltac:(right; auto)
             end).

  Global Instance region_type_countable : Countable region_type.
  Proof.
    set encode := fun ty => match ty with
                         | Temporary => 1
                         | Permanent => 2
                         | Revoked => 3
                         | Frozen m => 4 + 2 * (encode m)
                         end%positive.
    set decode := (fun n =>
                     if decide (n = 1) then Some Temporary
                     else if decide (n = 2) then Some Permanent
                          else if decide (n = 3) then Some Revoked
                               else if decide (Zpos n `mod` 2 = 0)%Z then
                                      match (decode (Z.to_pos (((Zpos n)-4) / 2)%Z)) with
                                      | Some m => Some (Frozen m)
                                      | None => None
                                      end
                                    else None)%positive.
    eapply (Build_Countable _ _ encode decode).
    intro ty. destruct ty; try reflexivity;
    unfold encode, decode;
    repeat (match goal with |- context [ decide ?x ] =>
                            destruct (decide x); [ try (exfalso; lia) | ] end).
    - rewrite Pos2Z.inj_add Z.add_comm Z.add_simpl_r Pos2Z.inj_mul.
      rewrite Z.mul_comm Z.div_mul;[|lia]. rewrite Pos2Z.id decode_encode//.
    - exfalso. apply n2. rewrite Pos2Z.inj_add Pos2Z.inj_mul Z.mul_comm Z_mod_plus;auto. lia.
  Qed.

  Global Instance rel_persistent (C : CmptName) (a : Addr) (p : Perm)
    (φ : (WORLD * CmptName * Word) -> iProp Σ) :
    Persistent (rel C a p φ).
  Proof. rewrite rel_eq /rel_def REL_eq /REL_def.
         apply _.
  Qed.

  Definition future_pub_mono (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_pub_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Definition future_priv_mono (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_priv_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Definition future_special_mono (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_special_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Lemma future_priv_mono_is_future_pub_mono (C : CmptName) (φ: (WORLD * CmptName * Word) → iProp Σ) v :
    future_priv_mono C φ v -∗ future_pub_mono C φ v.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrelated) "Hφ".
    iApply "H"; eauto.
    iPureIntro; eauto using related_sts_pub_priv_world.
  Qed.

  Lemma future_priv_mono_is_future_special_mono (C : CmptName) (φ: (WORLD * CmptName * Word) → iProp Σ) v :
    future_priv_mono C φ v -∗ future_special_mono C φ v.
  Proof.
    iIntros "#H". unfold future_special_mono. iModIntro.
    iIntros (W W' Hrelated) "Hφ".
    iApply "H"; eauto.
    iPureIntro; eauto using related_sts_special_priv_world.
  Qed.

  Lemma future_special_mono_is_future_pub_mono (C : CmptName) (φ: (WORLD * CmptName * Word) → iProp Σ) v :
    future_special_mono C φ v -∗ future_pub_mono C φ v.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrelated) "Hφ".
    iApply "H"; eauto.
    iPureIntro; eauto using related_sts_pub_special_world.
  Qed.

  Definition mono_pub (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) :=
    (∀ (w : Word), future_pub_mono C φ w)%I.
  Definition mono_special (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (p : Perm) :=
    (∀ (w : Word), ⌜canStore p w = true⌝ -∗ future_special_mono C φ w)%I.
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

  Lemma future_special_mono_eq_pred C γ φ φ' w :
    saved_pred_own γ DfracDiscarded φ
    -∗ saved_pred_own γ DfracDiscarded φ'
    -∗ ▷ future_special_mono C φ w
    -∗ ▷ future_special_mono C φ' w.
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

  Lemma mono_special_eq_pred C γ p φ φ':
    saved_pred_own γ DfracDiscarded φ
    -∗ saved_pred_own γ DfracDiscarded φ'
    -∗ ▷ mono_special C φ p
    -∗ ▷ mono_special C φ' p.
  Proof.
    iIntros "#Hφ #Hφ' #Hmono".
    iIntros (w Hglobalw).
    iSpecialize ("Hmono" $! w Hglobalw).
    iApply (future_special_mono_eq_pred with "Hφ Hφ' Hmono");auto.
  Qed.

  (* Asserting that a location is in a specific state in a given World *)

  Definition permanent (W : WORLD) (a : Addr) :=
    match (std W) !! a with
    | Some ρ => ρ = Permanent
    | _ => False
    end.
  Definition revoked (W : WORLD) (a : Addr) :=
    match (std W) !! a with
    | Some ρ => ρ = Revoked
    | _ => False
    end.
  Definition frozen (W : WORLD) (m: gmap Addr Word) (a : Addr) :=
    match (std W) !! a with
    | Some ρ => ρ = (Frozen m)
    | _ => False
    end.
  Definition temporary (W : WORLD) (a : Addr) :=
    match (std W) !! a with
    | Some ρ => ρ = Temporary
    | _ => False
    end.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- REGION_MAP ---------------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  Definition region_map_def
    (W : WORLD)
    (C : CmptName)
    (MC : gmap Addr (gname * Perm))
    (Mρ: gmap Addr region_type) :=
    ([∗ map] a↦γp ∈ MC,
       ∃ ρ, ⌜Mρ !! a = Some ρ⌝
            ∗ sts_state_std C a ρ
            ∗ ∃ γpred p φ, ⌜γp = (γpred,p)⌝
                    ∗ ⌜∀ Wv, Persistent (φ Wv)⌝
                    ∗ saved_pred_own γpred DfracDiscarded φ
                    ∗ match ρ with
                      | Temporary =>
                          ∃ (v : Word), ⌜isO p = false⌝
                                        ∗ a ↦ₐ v
                                        ∗ (if isWL p
                                           then future_pub_mono C φ v
                                           else (if isDL p
                                                 then future_special_mono C φ v
                                                 else future_priv_mono C φ v)
                                          )
                                        ∗ ▷ φ (W,C,v)
                      | Permanent =>
                          ∃ (v : Word), ⌜isO p = false⌝
                                        ∗ a ↦ₐ v
                                        ∗ future_priv_mono C φ v
                                        ∗ ▷ φ (W,C,v)
                      | Frozen m =>
                          ∃ (v : Word), ⌜isO p = false⌝
                                        ∗ ⌜m !! a = Some v⌝
                                        ∗ a ↦ₐ v
                                        ∗ ⌜∀ a', a' ∈ dom m → Mρ !! a' = Some (Frozen m)⌝
                       | Revoked => emp
     end)%I.

  Definition region_def (W : WORLD) (C : CmptName) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap Addr region_type),
        RELS C M
        ∗ ⌜dom (std W) = dom M⌝
        ∗ ⌜dom Mρ = dom M⌝
        ∗ region_map_def W C M Mρ)%I.
  Definition region_aux : { x | x = @region_def }. by eexists. Qed.
  Definition region := proj1_sig region_aux.
  Definition region_eq : @region = @region_def := proj2_sig region_aux.

  Lemma reg_in
    (C : CmptName) (M : relT)
    (a : Addr) (γ : gnameO) (p : leibnizO Perm) :
    RELS C M ∗ REL C a γ p
    -∗ ⌜M = <[a := (γ,p)]>(delete a M)⌝.
  Proof.
    iIntros "[H1 H2]".
    rewrite REL_eq RELS_eq /REL_def /RELS_def /region_map_def.
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
    rewrite insert_delete_insert insert_id /leibniz_equiv_iff => //; auto.
    revert Heq. rewrite lookup_fmap fmap_Some_equiv =>Hγp'.
    destruct Hγp' as [γp' [? Hrγp'] ].
    apply to_agree_inj, leibniz_equiv_iff in Hrγp' as ->.
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

  Lemma region_rel_get (W : WORLD) (C : CmptName) (a : Addr) :
    (std W) !! a = Some Temporary ->
    region W C ∗ sts_full_world W C
    ==∗
    region W C ∗ sts_full_world W C ∗ ∃ p φ, ⌜forall WCv, Persistent (φ WCv)⌝ ∗ rel C a p φ.
  Proof.
    iIntros (Hlookup) "[Hr Hsts]".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & %Hdom' & Hr)".
    assert (is_Some (M !! a)) as [ [γ p] Hγp].
    { apply elem_of_dom. rewrite /std in Hlookup,Hdom'.
      rewrite -Hdom. rewrite elem_of_dom; eauto.
    }
    iMod (reg_get with "[$HM]") as "[HM Hrel]";[eauto|].
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hstate Hr]";[eauto|].
    iDestruct "Hstate" as (ρ Ha) "[Hρ Hstate]".
    iDestruct (sts_full_state_std with "Hsts Hρ") as %Hx''; simplify_eq.
    all: rewrite Hlookup in Hx'';inversion Hx'';subst.
    all: iDestruct "Hstate" as (γpred p' φ Heq Hpers) "(#Hsaved & Ha)".
    all: iDestruct "Ha" as (v Hne) "(Ha & #HmonoV & #Hφ)".
    all: iDestruct (big_sepM_delete _ _ a with "[Hρ Ha HmonoV Hφ $Hr]") as "Hr";[eauto| |].
    { iExists Temporary. iFrame "∗#%". }
    all: iModIntro.
    all: iSplitL "HM Hr".
    { iExists M. iFrame "∗#%". }
    all: iFrame; iExists p,φ; iSplit;auto; rewrite rel_eq /rel_def; iExists γpred.
    all: simplify_eq; iFrame "Hsaved Hrel".
  Qed.

  Lemma update_RELS
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
    rewrite HMeq. rewrite lookup_insert. eauto.
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

  Lemma future_special_mono_eq_pred_rel C γ p p' φ φ' w :
    rel C γ p φ
    -∗ rel C γ p' φ'
    -∗ ▷ future_special_mono C φ w
    -∗ ▷ future_special_mono C φ' w.
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

  Lemma mono_special_eq_pred_rel C γ p p' φ φ' :
    rel C γ p φ
    -∗ rel C γ p' φ'
    -∗ ▷ mono_special C φ p
    -∗ ▷ mono_special C φ' p.
  Proof.
    iIntros "#Hrel #Hrel' #Hmono".
    iIntros (w Hglobalw).
    iSpecialize ("Hmono" $! w Hglobalw).
    iApply (future_special_mono_eq_pred_rel with "Hrel Hrel' Hmono"); eauto.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* region_map is monotone with regards to public future world relation *)
  Lemma region_map_monotone (C : CmptName) (W W' : WORLD) M Mρ :
    related_sts_pub_world W W'
    → region_map_def W C M Mρ
    -∗ region_map_def W' C M Mρ.
  Proof.
    iIntros (Hrelated) "Hr".
    (* destruct Hrelated as (WC & WC' &) *)
    iApply big_sepM_mono; iFrame.
    iIntros (a γ Hsome) "Hm".
    iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
    iExists ρ. iFrame. iSplitR;[auto|].
    destruct ρ.
    - iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
      iFrame "%#∗".
      destruct (isWL p); [| destruct (isDL p)]; (iApply "HmonoV"; eauto; iFrame).
      + iPureIntro; apply related_sts_pub_special_world in Hrelated; naive_solver.
      + iPureIntro; apply related_sts_pub_priv_world in Hrelated; naive_solver.
    - iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
      iFrame "%#∗".
      iApply "HmonoV"; iFrame "∗#"; auto.
      iPureIntro; apply related_sts_pub_priv_world in Hrelated; naive_solver.
    - done.
    - done.
  Qed.

  Lemma region_monotone C W W':
    dom (std W) = dom (std W')
    -> related_sts_pub_world W W'
    → region W C
    -∗ region W' C.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite region_eq.
    iDestruct "HW" as (M Mρ) "(HM & % & % & Hmap)"; simplify_map_eq.
    iExists M, Mρ. iFrame.
    repeat(iSplitR; auto).
    - iPureIntro;congruence.
    - iApply region_map_monotone; last eauto;eauto.
  Qed.

  Lemma uninitialized_mono_related_sts_pub_world W a w :
    (std W) !! a = Some (Frozen {[a:=w]}) ->
    related_sts_pub_world W (<s[ a := Temporary ]s> W).
  Proof.
    intros.
    split;[|apply related_sts_pub_refl].
    split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (i = a)).
      + subst. rewrite /std in H.
        simplify_map_eq. rewrite H in Hx.
        inv Hx.
        right with Temporary;constructor.
      + simplify_map_eq; auto.
        rewrite Hx in Hy.
        simplify_eq. left.
  Qed.

  (* Lemma uninitialized_w_mono_related_sts_pub_world l W w : *)
  (*   (std W) !! l = Some (Uninitialized w) -> *)
  (*   related_sts_pub_world W (<s[ l := Temporary ]s> W). *)
  (* Proof. *)
  (*   intros. split;[|apply related_sts_pub_refl]. *)
  (*   split. *)
  (*   - rewrite dom_insert_L. set_solver. *)
  (*   - intros i x y Hx Hy. *)
  (*     destruct (decide (i = l)). *)
  (*     + subst. simplify_map_eq. *)
  (*       rewrite lookup_insert in Hy. inv Hy. *)
  (*       right with Temporary;[|left]. *)
  (*       constructor. *)
  (*     + simplify_map_eq. rewrite lookup_insert_ne in Hy; auto. *)
  (*       simplify_map_eq. left. *)
  (* Qed. *)

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- OPEN_REGION --------------------------------------- *)

  Definition open_region_def (W : WORLD) (C : CmptName) (a : Addr) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap Addr region_type),
        RELS C M
        ∗ ⌜dom (std W) = dom M⌝
        ∗ ⌜dom Mρ = dom M⌝
        ∗ region_map_def W C (delete a M) (delete a Mρ))%I.
  Definition open_region_aux : { x | x = @open_region_def }. by eexists. Qed.
  Definition open_region := proj1_sig open_region_aux.
  Definition open_region_eq : @open_region = @open_region_def := proj2_sig open_region_aux.

  (* open_region is monotone wrt public future worlds *)
  Lemma open_region_monotone C W W' a :
    dom (std W)  = dom (std W')
    -> related_sts_pub_world W W'
    → open_region W C a
    -∗ open_region W' C a.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite open_region_eq /open_region_def.
    iDestruct "HW" as (M Mρ) "(HM & % & % & Hmap)"; simplify_map_eq.
    iExists M, Mρ. iFrame.
    repeat(iSplitR; auto).
    - iPureIntro;congruence.
    - iApply region_map_monotone; last eauto;eauto.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS FOR OPENING THE REGION MAP ----------------------------------- *)

  Lemma region_map_delete_nonfrozen W C M Mρ a :
    (forall m, Mρ !! a ≠ Some (Frozen m)) →
    region_map_def W C (delete a M) Mρ -∗
    region_map_def W C (delete a M) (delete a Mρ).
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a' γr Ha') "HH".
    iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a' = a)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
    iDestruct "Hl" as (v Hne) "(% & Hφ & Hothers)".
    iFrame "%#∗".
    iDestruct "Hothers" as %Hothers.
    iPureIntro.
    intros a'' Ha''. destruct (decide (a'' = a)).
    { subst. exfalso. apply Hothers in Ha''. destruct Hl with g. congruence. }
    { by simplify_map_eq. }
  Qed.

  Lemma region_map_delete_singleton W C M Mρ l :
    (∃ w, Mρ !! l = Some (Frozen {[l:=w]})) ->
    region_map_def W C (delete l M) Mρ -∗
    region_map_def W C (delete l M) (delete l Mρ).
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a = l)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
    iDestruct "Hl" as (v Hne) "(% & Hφ & Hothers)".
    iFrame "%#∗".
    iDestruct "Hothers" as %Hothers.
    iPureIntro.
    intros a' Ha'. destruct (decide (a' = l)).
    { subst. destruct Hl as [w Hl].
      exfalso. assert (l ≠ a) as Hne';[intros Hcontr;subst;rewrite lookup_delete in Ha;inversion Ha|].
      apply Hothers in Ha'. rewrite Hl in Ha'. inversion Ha'. subst. simplify_map_eq. }
    { by simplify_map_eq. }
  Qed.

  Lemma region_open_temp_pwl W C l p φ :
    (std W) !! l = Some Temporary →
    isWL p = true →
    rel C l p φ ∗ region W C ∗ sts_full_world W C -∗
    ∃ v, open_region W C l
         ∗ sts_full_world W C
         ∗ sts_state_std C l Temporary
         ∗ l ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ future_pub_mono C φ v
         ∗ ▷ φ (W,C,v).
  Proof.
    iIntros (Htemp Hpwl) "(#Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_map_eq.
    (* assert that γrel = γrel' *)
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH1 Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH1; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv".
    - rewrite open_region_eq /open_region_def.
      iExists _,Mρ. rewrite -HMeq.
      iFrame "∗ #".
      repeat (iSplitR; eauto).
      iApply region_map_delete_nonfrozen; auto. by congruence.
    - repeat (iSplitR).
      + auto.
      + iApply future_pub_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame "∗ #".
  Qed.


  Lemma region_open_temp_nwl W C l p φ :
    (std W) !! l = Some Temporary →
    isWL p = false →
    rel C l p φ ∗ region W C ∗ sts_full_world W C -∗
        ∃ v, open_region W C l
           ∗ sts_full_world W C
           ∗ sts_state_std C l Temporary
           ∗ l ↦ₐ v
           ∗ ⌜isO p = false⌝
           ∗ ▷ (if isDL p then future_special_mono C φ v else future_priv_mono C φ v)
           ∗ ▷ φ (W,C,v).
  Proof.
    iIntros (Htemp Hpwl) "(#Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_map_eq.
    (* assert that γrel = γrel' *)
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv".
    - rewrite open_region_eq /open_region_def.
      iExists _,Mρ. iFrame "∗ #".
      rewrite -HMeq.
      repeat (iSplitR; eauto).
      iApply region_map_delete_nonfrozen; auto. by congruence.
    - repeat (iSplitR).
      + auto.
      + destruct (isDL p').
        * iApply future_special_mono_eq_pred; auto.
        * iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame "∗ #".
  Qed.


  (* Lemma region_open_monotemp W a φ : *)
  (*   (std W) !! a = Some Temporary → *)
  (*   rel a p φ ∗ region W ∗ sts_full_world W -∗ *)
  (*       ∃ v, open_region a W *)
  (*          ∗ sts_full_world W *)
  (*          ∗ sts_state_std a Temporary *)
  (*          ∗ a ↦ₐ v *)
  (*          ∗ ▷ future_pub_mono φ v *)
  (*          ∗ ▷ φ (W,v). *)
  (* Proof. *)
  (*   iIntros (Htemp) "(Hrel & Hreg & Hfull)". *)
  (*   rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def. *)
  (*   iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)". *)
  (*   iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)". *)
  (*   (* assert that γrel = γrel' *) *)
  (*   iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq. *)
  (*   rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete]. *)
  (*   iDestruct "Hpreds" as "[Hl Hpreds]". *)
  (*   iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]". *)
  (*   iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst. *)
  (*   rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); []. *)
  (*   iDestruct "Hl" as (φ' Hpers) "(#Hφ' & Hl)". *)
  (*   iDestruct "Hl" as (v) "(Hl & #Hmono & Hφv)". *)
  (*   iDestruct (saved_pred_agree _ _ _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq". *)
  (*   iExists v. iFrame. *)
  (*   iSplitR "Hφv". *)
  (*   - rewrite open_region_eq /open_region_def. *)
  (*     iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #". *)
  (*     iExists Mρ. do 2 (iSplitR; eauto). *)
  (*     iApply region_map_delete_nonfrozen; auto. rewrite Hρ; auto. *)
  (*   - iSplitR. *)
  (*     + rewrite /future_pub_mono. *)
  (*       iApply later_intuitionistically_2. iModIntro. *)
  (*       repeat (iApply later_forall_2; iIntros (?)). *)
  (*       iDestruct (saved_pred_agree _ _ _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq'". *)
  (*       iDestruct (saved_pred_agree _ _ _ _ _ (a1,v) with "Hφ Hφ'") as "#Hφeq''". *)
  (*       iNext. iIntros (Hrel) "Hφw". *)
  (*       iRewrite ("Hφeq''"). *)
  (*       iApply "Hmono"; eauto. *)
  (*       iRewrite -("Hφeq'"). iFrame. *)
  (*     + iNext. iRewrite "Hφeq". iFrame "∗ #". *)
  (* Qed. *)

    Lemma region_open_perm W C l p φ :
    (std W) !! l = Some Permanent →
    rel C l p φ ∗ region W C ∗ sts_full_world W C -∗
        ∃ v, open_region W C l
           ∗ sts_full_world W C
           ∗ sts_state_std C l Permanent
           ∗ l ↦ₐ v
           ∗ ⌜isO p = false⌝
           ∗ ▷ future_priv_mono C φ v
           ∗ ▷ φ (W,C,v).
  Proof.
    iIntros (Htemp) "(#Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_map_eq.
    (* assert that γrel = γrel' *)
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv".
    - rewrite open_region_eq /open_region_def.
      iExists _,Mρ. iFrame "∗ #".
      rewrite -HMeq.
      repeat (iSplitR; eauto).
      iApply region_map_delete_nonfrozen; auto. by congruence.
    - repeat (iSplitR).
      + auto.
      + iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  (* Lemma region_open_uninitialized W l v φ : *)
  (*   (std W) !! l = Some (Uninitialized v) → *)
  (*   rel l φ ∗ region W ∗ sts_full_world W -∗ *)
  (*       open_region l W *)
  (*       ∗ sts_full_world W *)
  (*       ∗ sts_state_std l (Uninitialized v) *)
  (*       ∗ l ↦ₐ v. *)
  (* Proof. *)
  (*   iIntros (Htemp) "(Hrel & Hreg & Hfull)". *)
  (*   rewrite region_eq /region_def /region_map_def rel_eq /rel_def REL_eq /REL_def. *)
  (*   iDestruct "Hreg" as (M Mρ) "(HM & HMW & % & Hpreds)". iDestruct "HMW" as %HMW. *)
  (*   iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]". *)
  (*   rewrite RELS_eq /RELS_def. *)
  (*   iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq. *)
  (*   assert (is_Some(M !! l)) as [γp HX]. *)
  (*   { apply elem_of_dom. rewrite -HMW. apply (elem_of_dom W.1 l). eauto. } *)
  (*   iDestruct (big_sepM_delete with "Hpreds") as "[Hl Hpreds]"; eauto. *)
  (*   iDestruct "Hl" as (ρ) "[ % [Hstate Hl] ]". destruct ρ. *)
  (*   1,2,3,4,5: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr. *)
  (*   1,2,3,4,5: rewrite Htemp in Hcontr; try by inversion Hcontr. *)
  (*   iDestruct "Hl" as (φ') "(#Hpers & #Hsaved & Hl)". inversion Hcontr. *)
  (*   subst. *)
  (*   rewrite open_region_eq /open_region_def RELS_eq /RELS_def. iFrame. *)
  (*   iExists Mρ. iFrame. *)
  (*   repeat iSplit;auto. iApply region_map_delete_nonfrozen; eauto. *)
  (*   rewrite H1. eauto. *)
  (* Qed. *)

  Lemma region_open W C a p φ (ρ : region_type) :
    ρ = Temporary ∨ ρ = Permanent →
    (std W) !! a = Some ρ →
    rel C a p φ ∗ region W C ∗ sts_full_world W C -∗
    ∃ v, open_region W C a
         ∗ sts_full_world W C
         ∗ sts_state_std C a ρ
         ∗ a ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ (▷ if (decide (ρ = Temporary))
              then ( if isWL p
                     then future_pub_mono C φ v
                     else (if isDL p then future_special_mono C φ v else future_priv_mono C φ v))
              else future_priv_mono C φ v)
         ∗ ▷ φ (W,C,v).
  Proof.
    iIntros (Hne Htemp) "(Hrel & Hreg & Hfull)".
    destruct ρ; try (destruct Hne; exfalso; congruence).
    - destruct (isWL p) eqn:Hpwl.
      + iDestruct (region_open_temp_pwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
      + iDestruct (region_open_temp_nwl with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
        iExists _; iFrame.
    - iDestruct (region_open_perm with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hp & Hmono & φ)"; auto.
      iExists _; iFrame.
  Qed.

  (* It is important here that we have (delete l Mρ) and not simply Mρ.
     Otherwise, [Mρ !! l] could in principle map to a frozen region (although
     it's not the case in practice), that it would be incorrect to overwrite
     with a non-frozen state. *)
  Lemma region_map_undelete_nonfrozen W C M Mρ a :
    (forall m, Mρ !! a ≠ Some (Frozen m)) →
    region_map_def W C (delete a M) (delete a Mρ) -∗
    region_map_def W C (delete a M) Mρ.
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a' γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a' = a)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (γpred' p' φ' HH1 Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v HH2 Hne) "(Hl & Hothers)".
    iDestruct "Hothers" as %Hothers.
    iFrame "%#∗".
    iPureIntro.
    intros a'' Ha''. apply Hothers in Ha''.
    destruct (decide (a'' = a)); by simplify_map_eq.
  Qed.

  Lemma region_map_insert_nonfrozen W C M Mρ a ρ :
    (forall m, ρ ≠ Frozen m) →
    region_map_def W C (delete a M) (delete a Mρ) -∗
    region_map_def W C (delete a M) (<[ a := ρ ]> Mρ).
  Proof.
    iIntros (?) "HH".
    rewrite {1}(_: delete a Mρ = delete a (<[ a := ρ ]> Mρ)). 2: by rewrite delete_insert_delete//.
    iDestruct (region_map_undelete_nonfrozen with "HH") as "HH".
    { intro. simplify_map_eq. congruence. }
    auto.
  Qed.

  (* We can apply the same reasoning to singleton frozen regions (i.e. uninitialised regions) *)
  Lemma region_map_undelete_singleton W C M Mρ a :
    (∃ w, Mρ !! a = Some (Frozen {[a:=w]})) →
    region_map_def W C (delete a M) (delete a Mρ) -∗
    region_map_def W C (delete a M) Mρ.
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a' γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a' = a)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (γpred' p' φ' HH1 Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v HH2 Hne) "(Hl & Hothers)".
    iDestruct "Hothers" as %Hothers.
    iFrame "%#∗".
    iPureIntro.
    intros a'' Ha''. apply Hothers in Ha''.
    destruct (decide (a'' = a)); by simplify_map_eq.
  Qed.

  Lemma region_map_insert_singleton W C M Mρ a ρ:
    (∃ w, ρ = Frozen {[a:=w]}) →
    region_map_def W C (delete a M) (delete a Mρ) -∗
    region_map_def W C (delete a M) (<[ a := ρ ]> Mρ).
  Proof.
    iIntros (?) "HH".
    rewrite {1}(_: delete a Mρ = delete a (<[ a := ρ ]> Mρ)). 2: by rewrite delete_insert_delete//.
    iDestruct (region_map_undelete_singleton with "HH") as "HH".
    { simplify_map_eq. naive_solver. }
    auto.
  Qed.


  Lemma full_sts_Mρ_agree W C M Mρ (ρ: region_type) :
    (* NB: only the forward direction of dom_equal (std_sta W) M is actually needed *)
    dom (std W) = dom M →
    (* NB: only one direction of this assumption is needed, and only for the reverse *)
  (*      direction of the lemma *)
    dom Mρ = dom M →
    sts_full_world W C -∗
    region_map_def W C M Mρ -∗
    ⌜∀ a:Addr, (std W) !! a = Some ρ ↔ Mρ !! a = Some ρ⌝.
  Proof.
    iIntros (HWM HMMρ) "Hfull Hr".
    iAssert (∀ a:Addr, ⌜ (std W) !! a = Some ρ ⌝ → ⌜ Mρ !! a = Some ρ ⌝)%I as %?.
    { iIntros (a Haρ).
      assert (is_Some (M !! a)) as [γp Hγp].
      { apply elem_of_dom.
        rewrite -HWM. apply (elem_of_dom (std W)) . eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). apply encode_inj.
      rewrite Haρ in Haρ'. congruence. }
    iAssert (∀ a:Addr, ⌜ Mρ !! a = Some ρ ⌝ → ⌜ (std W) !! a = Some ρ ⌝)%I as %?.
    { iIntros (a HMρa).
      assert (is_Some (M !! a)) as [γp Hγp].
      { rewrite -elem_of_dom -HMMρ elem_of_dom; eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). rewrite HMρa in Hρ'. congruence. }
    iPureIntro. intros. split; eauto.
  Qed.

  Lemma full_sts_frozen_all W C m (a : Addr) :
    (std W) !! a = Some (Frozen m) →
    sts_full_world W C -∗
    region W C -∗
    ⌜forall a', a' ∈ dom m -> frozen W m a'⌝.
  Proof.
    iIntros (Hfrozen) "Hsts Hr".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom1 & %Hdom2 & Hr)"
    ; simplify_eq.
    iIntros (a' Hdom).
    iDestruct (full_sts_Mρ_agree _ _ _ _ (Frozen m) with "Hsts Hr") as "%Hag'"; eauto.
    destruct (Hag' a) as [Hag _]. clear Hag'.
    pose proof (Hag Hfrozen) as Hl.
    assert (is_Some (M !! a)) as [γp Hsome].
    { apply elem_of_dom. rewrite -Hdom1. rewrite elem_of_dom . eauto. }
    rewrite /region_map_def.
    iDestruct (big_sepM_delete _ _ a with "Hr") as "[Hl Hr]";[eauto|].
    iDestruct "Hl" as (ρ Hρ) "(Hstate & Hρ)".
    rewrite Hag in Hρ; auto. inversion Hρ.
    iDestruct "Hρ" as (γpred p φ Hpv Hpers) "(#Hsaved & Hl)".
    iDestruct "Hl" as (v Hpv' Hne') "[Hl #Hall]". iDestruct "Hall" as %Hall.
    iDestruct (big_sepM_delete _ _ a with "[$Hr Hl Hstate]") as "Hr";[eauto|..].
    { iFrame "%#∗". }
    iDestruct (full_sts_Mρ_agree _ _ _ _ (Frozen m) with "Hsts Hr") as "%Hag'"; auto.
    iPureIntro.
    rewrite /std in Hfrozen.
    rewrite /frozen.
    destruct (Hag' a') as [_ Hag2].
    pose proof (Hall _ Hdom) as Ha.
    pose proof (Hag2 Ha) as Hf.
    by rewrite Hf.
  Qed.

   (* Closing the region without updating the sts collection *)
  Lemma region_close_temp_pwl W C a φ p v `{forall Wv, Persistent (φ Wv)} :
    isWL p = true →
    sts_state_std C a Temporary
    ∗ open_region W C a
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ future_pub_mono C φ v
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
    -∗ region W C.
  Proof.
    iIntros (Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Temporary  with "Hpreds") as "Hpreds".
    { by congruence. }
    iDestruct ( (big_sepM_insert _ (delete a M) a) with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "#∗". repeat (iSplitR;eauto).
    }
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    iPureIntro.
    by rewrite HMeq insert_delete_insert !dom_insert_L Hdomρ.
  Qed.

  Lemma region_close_temp_nwl W C a φ p v `{forall Wv, Persistent (φ Wv)} :
    isWL p = false →
    sts_state_std C a Temporary
    ∗ open_region W C a
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ (if isDL p then future_special_mono C φ v else future_priv_mono C φ v)
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
    -∗ region W C.
  Proof.
    iIntros (Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Temporary  with "Hpreds") as "Hpreds".
    { by congruence. }
    iDestruct ( (big_sepM_insert _ (delete a M) a) with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "#∗". repeat (iSplitR;eauto).
    }
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    iPureIntro.
    by rewrite HMeq insert_delete_insert !dom_insert_L Hdomρ.
  Qed.


  (* Closing the region without updating the sts collection *)
  (* Lemma region_close_monotemp W a φ v `{forall Wv, Persistent (φ Wv)} : *)
  (*   ⊢ sts_state_std a Temporary *)
  (*     ∗ open_region a W ∗ a ↦ₐ v ∗ future_pub_mono φ v ∗ ▷ φ (W,v) ∗ rel a φ *)
  (*     -∗ region W. *)
  (* Proof. *)
  (*   rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def *)
  (*           REL_eq RELS_eq /RELS_def /REL_def. *)
  (*   iIntros "(Hstate & Hreg_open & Hl & #Hmono & Hφ & #Hrel)". *)
  (*   iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]". *)
  (*   iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ. *)
  (*   iDestruct (region_map_insert_nonfrozen Temporary with "Hpreds") as "Hpreds". by congruence. *)
  (*   iDestruct (big_sepM_insert _ (delete a M) a with "[-HM]") as "test"; *)
  (*     first by rewrite lookup_delete. *)
  (*   { iFrame. iSplitR; [by simplify_map_eq|]. *)
  (*     iExists _. iFrame "∗ #". repeat (iSplitR;[eauto|]). iFrame. auto. } *)
  (*   iFrame. iFrame "∗ #". *)
  (*   iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq. *)
  (*   rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro. *)
  (*   rewrite HMeq !insert_delete_insert !dom_insert_L Hdomρ. set_solver. *)
  (* Qed. *)

  (* Lemma region_close_mono_uninit_w E W l φ w v `{forall Wv, Persistent (φ Wv)} : *)
  (*   sts_state_std l (Uninitialized w) *)
  (*   ∗ open_region l W *)
  (*   ∗ l ↦ₐ v *)
  (*   ∗ future_pub_a_mono l φ v *)
  (*   ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *) *)
  (*   ∗ rel l φ *)
  (*   ∗ sts_full_world W *)
  (*   ={E}=∗ region (<s[ l := Temporary ]s> W) ∗ sts_full_world (<s[ l := Temporary ]s> W). *)
  (* Proof. *)
  (*   rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def *)
  (*           REL_eq RELS_eq /RELS_def /REL_def. *)
  (*   iIntros "(Hstate & Hreg_open & Hl & #Hmono & #Hφ & #Hrel & Hfull)". *)
  (*   iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]". *)
  (*   iDestruct "Hreg_open" as (M Mρ) "(HM & HMW & HMρ & Hpreds)". *)
  (*   iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ. *)
  (*   iDestruct (sts_full_state_std with "Hfull Hstate") as "%". *)
  (*   iDestruct (sts_update_std with "Hfull Hstate") as ">[Hfull Hstate]". *)
  (*   iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq. *)
  (*   iModIntro. iFrame "Hfull". *)
  (*   iDestruct (region_map_insert_nonfrozen Temporary with "Hpreds") as "Hpreds";[intros;auto|]. *)
  (*   iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test"; *)
  (*     first by rewrite lookup_delete. *)
  (*   { iFrame. iFrame. *)
  (*     iSplit;[iPureIntro;apply lookup_insert|]. *)
  (*     iExists _. iFrame "∗ #". repeat iSplitR; auto. } *)
  (*   assert (Hpub: related_sts_pub_world W (<s[l:=Temporary ]s>W)). *)
  (*   { eapply (uninitialized_w_mono_related_sts_pub_world l W); eauto. } *)
  (*   iDestruct (region_map_monotone _ _ _ _ Hpub with "test") as "HMdef"; eauto. *)
  (*   rewrite -HMeq. iExists M,_; iFrame. iPureIntro. *)
  (*   repeat rewrite dom_insert_L. assert (l ∈ dom W.1) as Hin;[rewrite elem_of_dom;eauto|]. *)
  (*   split;[rewrite -HMW| rewrite HMρ -HMW];set_solver. *)
  (* Qed. *)


  Lemma region_close_perm W C a p φ v `{forall Wv, Persistent (φ Wv)}:
    ⊢ sts_state_std C a Permanent
      ∗ open_region W C a
      ∗ a ↦ₐ v
      ∗ ⌜isO p = false⌝
      ∗ future_priv_mono C φ v
      ∗ ▷ φ (W,C,v)
      ∗ rel C a p φ
      -∗ region W C.
  Proof.
    iIntros "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Permanent  with "Hpreds") as "Hpreds".
    { by congruence. }
    iDestruct ( (big_sepM_insert _ (delete a M) a) with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iFrame "∗ #". repeat (iSplitR;[eauto|]). iFrame. auto. }
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    iPureIntro.
    by rewrite HMeq insert_delete_insert !dom_insert_L Hdomρ.
  Qed.

  Lemma region_close W C a φ p v (ρ : region_type) `{forall Wv, Persistent (φ Wv)} :
    ρ = Temporary ∨ ρ = Permanent →
    sts_state_std C a ρ
    ∗ open_region W C a
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ (if (decide (ρ = Temporary))
       then ( if isWL p
              then future_pub_mono C φ v
              else (if isDL p then future_special_mono C φ v else future_priv_mono C φ v))
       else future_priv_mono C φ v)
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
      -∗ region W C.
  Proof.
    iIntros (Htp) "(Hstate & Hreg_open & Hl & Hp & HmonoV & Hφ & Hrel)".
    destruct ρ; try (destruct Htp; exfalso; congruence).
    - destruct (isWL p) eqn:Hpwl.
      + iApply region_close_temp_pwl; eauto; iFrame.
      + iApply region_close_temp_nwl; eauto; iFrame.
    - iApply region_close_perm; eauto; iFrame.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------------- OPENING MULTIPLE LOCATIONS IN REGION --------------------------- *)
  Definition open_region_many_def  (W : WORLD) (C : CmptName) (l : list Addr) : iProp Σ :=
    (∃ (M : relT) (Mρ: gmap Addr region_type),
        RELS C M
        ∗ ⌜dom (std W) = dom M⌝
        ∗ ⌜dom Mρ = dom M⌝
        ∗ region_map_def W C (delete_list l M) (delete_list l Mρ))%I.
  Definition open_region_many_aux : { x | x = @open_region_many_def }. by eexists. Qed.
  Definition open_region_many := proj1_sig open_region_many_aux.
  Definition open_region_many_eq : @open_region_many = @open_region_many_def := proj2_sig open_region_many_aux.

  Lemma open_region_many_monotone (C : CmptName) (W W' : WORLD) l:
    dom (std W) = dom (std W')
    -> related_sts_pub_world W W'
    -> open_region_many W C l -∗ open_region_many W' C l.
  Proof.
    iIntros (Hdomeq Hrelated) "HW".
    rewrite open_region_many_eq /open_region_many_def.
    iDestruct "HW" as (M Mρ) "(Hm & % & % & Hmap)" ; simplify_eq.
    iExists M, Mρ. iFrame.
    repeat(iSplitR; auto).
    - iPureIntro;congruence.
    - iApply region_map_monotone; last eauto;eauto.
  Qed.

  Lemma open_region_many_permutation W C l1 l2:
    l1 ≡ₚ l2 → open_region_many W C l1 -∗ open_region_many W C l2.
  Proof.
    intros Hperm.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros "H". iDestruct "H" as (? ?) "(? & % & ?)".
    rewrite !(delete_list_permutation l1 l2) //. iExists _,_. iFrame. eauto.
  Qed.

   Lemma region_open_prepare W C a :
    open_region W C a ⊣⊢ open_region_many W C [a].
  Proof.
    iSplit; iIntros "Hopen";
    rewrite open_region_eq open_region_many_eq /=;
    iFrame.
  Qed.

  Lemma region_open_nil W C :
    region W C ⊣⊢ open_region_many W C [].
  Proof.
    iSplit; iIntros "H";
    rewrite region_eq open_region_many_eq /=;
            iFrame.
  Qed.

  Lemma region_open_next_temp_pwl W C φ als a p :
    a ∉ als →
    (std W) !! a = Some Temporary ->
    isWL p = true →
    open_region_many W C als ∗ rel C a p φ ∗ sts_full_world W C -∗
    ∃ v, open_region_many W C (a :: als)
         ∗ sts_full_world W C
         ∗ sts_state_std C a Temporary
         ∗ a ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ future_pub_mono C φ v
         ∗ ▷ φ (W,C,v).
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp Hpwl) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iFrame.
    iSplitR "Hφv".
    - iExists Mρ. repeat (rewrite -HMeq).
      repeat (iSplitR; eauto).
      iApply region_map_delete_nonfrozen; auto. by congruence.
    - repeat (iSplitR).
      + auto.
      + iApply future_pub_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_temp_nwl W C φ als a p :
    a ∉ als →
    (std W) !! a = Some Temporary ->
    isWL p = false →
    open_region_many W C als ∗ rel C a p φ ∗ sts_full_world W C -∗
    ∃ v, open_region_many W C (a :: als)
         ∗ sts_full_world W C
         ∗ sts_state_std C a Temporary
         ∗ a ↦ₐ v
         ∗ ⌜isO p = false⌝
         ∗ ▷ (if isDL p then future_special_mono C φ v else future_priv_mono C φ v)
         ∗ ▷ φ (W,C,v).
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp Hpwl) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inversion HH; subst. rewrite Hpwl.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iFrame.
    iSplitR "Hφv".
    - iExists Mρ. repeat (rewrite -HMeq).
      repeat (iSplitR; eauto).
      iApply region_map_delete_nonfrozen; auto. by congruence.
    - repeat (iSplitR).
      + auto.
      + destruct (isDL p').
        * iApply future_special_mono_eq_pred; auto.
        * iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_perm W C φ als a p :
    a ∉ als → (std W) !! a = Some Permanent ->
    open_region_many W C als
    ∗ rel C a p φ
    ∗ sts_full_world W C
    -∗ ∃ v,
        sts_full_world W C
        ∗ sts_state_std C a Permanent
        ∗ open_region_many W C (a :: als)
        ∗ a ↦ₐ v
        ∗ ⌜isO p = false⌝
        ∗ ▷ (future_priv_mono C φ v)
        ∗ ▷ φ (W,C,v).
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /= /region_map_def.
    rewrite rel_eq /rel_def /rel_def /region_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)"; simplify_eq.
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (γpred' p' φ' HH Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφv)".
    inv HH.
    iDestruct (saved_pred_agree _ _ _ _ _ (W,C,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv".
    - rewrite /open_region.
      iExists Mρ. repeat (rewrite -HMeq).
      repeat (iSplitR; eauto).
      iApply region_map_delete_nonfrozen; auto. by congruence.
    - repeat (iSplitR).
      + auto.
      + iApply future_priv_mono_eq_pred; auto.
      + iNext; iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_uninit W C w als a:
    a ∉ als →
    (std W) !! a = Some (Frozen {[a:=w]}) →
    open_region_many W C als ∗ sts_full_world W C -∗
        ∃ p, open_region_many W C (a :: als)
           ∗ sts_full_world W C
           ∗ sts_state_std C a (Frozen {[a:=w]})
           ∗ a ↦ₐ w
           ∗ ⌜isO p = false⌝.
  Proof.
    iIntros (Hnin Htemp) "(Hreg & Hfull)".
    rewrite open_region_many_eq /open_region_many_def /= /region_map_def.
    iDestruct "Hreg" as (M Mρ) "(HM & %HMW & % & Hpreds)"; simplify_eq.
    assert (is_Some (M !! a)) as [γp HX].
    { apply elem_of_dom. rewrite -HMW. rewrite elem_of_dom. eauto. }
    iDestruct (big_sepM_delete with "Hpreds") as "[Hl Hpreds]"; eauto.
    { rewrite lookup_delete_list_notin; eauto. }
    iDestruct "Hl" as (ρ) "[% [Hstate Hl] ]". destruct ρ.
    1,2,3,4:
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
    1,2,3: rewrite Htemp in Hcontr; by inversion Hcontr.
    iDestruct "Hl" as (γpred p φ Heq Hpers) "[#Hsaved Hl]".
    iDestruct "Hl" as (v Hne Hlookup) "[Hl _]".
    rewrite Htemp in Hcontr. inversion Hcontr; subst g.
    iExists p.
    rewrite lookup_insert in Hlookup;inversion Hlookup.
    iFrame. iSplit;auto.
    iExists _.
    iFrame "∗%#".
    iDestruct (region_map_delete_singleton with "Hpreds") as "Hpreds"; eauto.
  Qed.

  (* Lemma region_open_next_monouninit_w W w ls l φ : *)
  (*   l ∉ ls → *)
  (*   (std W) !! l = Some (Uninitialized w) → *)
  (*   rel l φ ∗ open_region_many ls W ∗ sts_full_world W -∗ *)
  (*       open_region_many (l :: ls) W *)
  (*       ∗ sts_full_world W *)
  (*       ∗ sts_state_std l (Uninitialized w) *)
  (*       ∗ l ↦ₐ w. *)
  (* Proof. *)
  (*   iIntros (Hnin Htemp) "(Hrel & Hreg & Hfull)". *)
  (*   rewrite open_region_many_eq /open_region_many_def /= /region_map_def rel_eq /rel_def REL_eq /REL_def. *)
  (*   iDestruct "Hreg" as (M Mρ) "(HM & HMW & % & Hpreds)". iDestruct "HMW" as %HMW. *)
  (*   rewrite RELS_eq /RELS_def. *)
  (*   iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]". *)
  (*   iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq. *)
  (*   assert (is_Some (M !! l)) as [γp HX]. *)
  (*   { apply elem_of_dom. rewrite -HMW. rewrite elem_of_dom. eauto. } *)
  (*   iDestruct (big_sepM_delete with "Hpreds") as "[Hl Hpreds]"; eauto. *)
  (*   { rewrite lookup_delete_list_notin; eauto. } *)
  (*   iDestruct "Hl" as (ρ) "[% [Hstate Hl] ]". destruct ρ. *)
  (*   1,2,3,4,5: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr. *)
  (*   1,2,3,4,5: rewrite Htemp in Hcontr; try by inversion Hcontr. *)
  (*   iDestruct "Hl" as (φ' Hpers) "[#Hsaved Hl]". *)
  (*   inversion Hcontr; subst w. *)
  (*   iFrame. *)
  (*   iExists Mρ. iFrame "∗ #". *)
  (*   iDestruct (region_map_delete_nonfrozen with "Hpreds") as "Hpreds"; eauto. *)
  (*   rewrite H1. eauto. *)
  (* Qed. *)

   Lemma region_close_next_temp_pwl W C φ als a p v `{forall Wv, Persistent (φ Wv)} :
    a ∉ als ->
    isWL p = true →
    sts_state_std C a Temporary
    ∗ open_region_many W C (a::als)
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ future_pub_mono C φ v
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
    -∗ open_region_many W C als.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Temporary with "Hpreds") as "Hpreds".
    { congruence. }
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete a (delete_list als M)) a with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "∗ #". repeat (iSplitR;[eauto|]).
      auto. }
    rewrite -(delete_list_delete _ M) //.
    rewrite -(delete_list_insert _ (delete a M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[a:=Temporary]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    by rewrite HMeq insert_delete_insert !dom_insert_L Hdomρ.
  Qed.

  Lemma region_close_next_temp_nwl W C φ als a p v `{forall Wv, Persistent (φ Wv)} :
    a ∉ als ->
    isWL p = false →
    sts_state_std C a Temporary
    ∗ open_region_many W C (a::als)
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ (if isDL p then future_special_mono C φ v else future_priv_mono C φ v)
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
      -∗ open_region_many W C als.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin Hpwl) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Temporary with "Hpreds") as "Hpreds".
    { congruence. }
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete a (delete_list als M)) a with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iSplitR; [by simplify_map_eq|].
      iExists _,p,_. rewrite Hpwl. iFrame "∗ #". repeat (iSplitR;[eauto|]).
      auto. }
    rewrite -(delete_list_delete _ M) //.
    rewrite -(delete_list_insert _ (delete a M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[a:=Temporary]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    by rewrite HMeq insert_delete_insert !dom_insert_L Hdomρ.
  Qed.

  (* Lemma region_close_next_mono_uninit_w E W ls l φ w v `{forall Wv, Persistent (φ Wv)} : *)
  (*   l ∉ ls -> *)
  (*   sts_state_std l (Uninitialized w) *)
  (*   ∗ open_region_many (l::ls) W *)
  (*   ∗ l ↦ₐ v *)
  (*   ∗ future_pub_a_mono l φ v *)
  (*   ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *) *)
  (*   ∗ rel l φ *)
  (*   ∗ sts_full_world W *)
  (*   ={E}=∗ open_region_many ls (<s[ l := Temporary ]s> W) ∗ sts_full_world (<s[ l := Temporary ]s> W). *)
  (* Proof. *)
  (*   rewrite open_region_many_eq rel_eq /open_region_many_def /rel_def /region_def *)
  (*           REL_eq RELS_eq /RELS_def /REL_def. *)
  (*   iIntros (Hnin) "(Hstate & Hreg_open & Hl & #Hmono & Hφ & #Hrel & Hfull)". *)
  (*   iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]". *)
  (*   iDestruct "Hreg_open" as (M Mρ) "(HM & HMW & HMρ & Hpreds)". *)
  (*   iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ. *)
  (*   iDestruct (sts_full_state_std with "Hfull Hstate") as "%". *)
  (*   iDestruct (sts_update_std with "Hfull Hstate") as ">[Hfull Hstate]". *)
  (*   iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq. *)
  (*   iModIntro. iSplitR "Hfull". *)
  (*   { iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "Hmap_def"; *)
  (*       first by rewrite lookup_delete. *)
  (*     { simpl. iDestruct (region_map_insert_nonfrozen Temporary with "Hpreds") as "Hpreds". by congruence. *)
  (*       iFrame. *)
  (*       iSplit;[iPureIntro;apply lookup_insert|]. *)
  (*       iExists  _. iFrame "∗ #". repeat iSplitR; auto. } *)
  (*     assert (Hpub: related_sts_pub_world W (<s[l:=Temporary]s>W)). *)
  (*     { eapply (uninitialized_w_mono_related_sts_pub_world l W); eauto. } *)
  (*     iDestruct (region_map_monotone _ _ _ _ Hpub with "Hmap_def") as "HMdef"; eauto. *)
  (*     iExists M,(<[l:=Temporary]>Mρ); iFrame. rewrite HMeq. *)
  (*     repeat rewrite dom_insert_L. rewrite dom_delete_L. *)
  (*     assert (l ∈ dom W.1) as Hin;[rewrite elem_of_dom;eauto|]. *)
  (*     assert ({[l]} ∪ dom (std W) ∖ {[l]} = dom (std W)) as Heq. *)
  (*     { rewrite union_comm_L difference_union_L. set_solver. } *)
  (*     repeat iSplit. *)
  (*     - iPureIntro. rewrite -HMW. set_solver. *)
  (*     - iPureIntro. rewrite HMρ -HMW. *)
  (*       set_solver. *)
  (*     - repeat rewrite insert_delete_insert. rewrite delete_list_insert; auto. *)
  (*       rewrite insert_insert. rewrite delete_list_insert; auto. } *)
  (*   iFrame. *)
  (* Qed. *)

  Lemma region_close_next_perm W C φ als a p v `{forall Wv, Persistent (φ Wv)} :
    a ∉ als ->
    ⊢ sts_state_std C a Permanent
    ∗ open_region_many W C (a::als)
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ future_priv_mono C φ v
    ∗ ▷ φ (W,C,v)
    ∗ rel C a p φ
      -∗ open_region_many W C als.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & % & #HmonoV & Hφ & #Hrel)".
    rewrite rel_eq /rel_def /rel /region.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & %Hdomρ & Hpreds)".
    iDestruct (region_map_insert_nonfrozen _ _ _ _ _ Permanent with "Hpreds") as "Hpreds".
    { congruence. }
    iDestruct (big_sepM_insert _ (delete a (delete_list als M)) a with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame.
      iSplitR; [by simplify_map_eq|].
      iExists _,_,_. iFrame "∗ #". repeat (iSplitR;[eauto|]). auto.
    }
    rewrite -(delete_list_delete _ M) // -(delete_list_insert _ (delete _ M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists M, (<[a:=Permanent]> Mρ).
    iDestruct ( (reg_in C M) with "[$HM $Hγpred]") as %HMeq;eauto.
    rewrite -HMeq.
    iFrame "∗ # %".
    repeat(iSplitR; eauto).
    by rewrite HMeq insert_delete_insert !dom_insert_L Hdomρ.
  Qed.

  Definition monotonicity_guarantees_region
    (C : CmptName) (φ : WORLD * CmptName * Word → iProp Σ)
    (p : Perm) (w : Word) (ρ : region_type) :=
    (match ρ with
     | Temporary => (if isWL p then future_pub_mono else (if isDL p then future_special_mono else future_priv_mono))
     | Permanent => future_priv_mono
     | Revoked | Frozen _ => λ _ _ _, True
     end C φ w)%I.

  Definition monotonicity_guarantees_decide
    (C : CmptName) (φ : WORLD * CmptName * Word → iProp Σ)
    (p : Perm) (w : Word) (ρ : region_type) :=
    (if decide (ρ = Temporary)
     then (if isWL p then future_pub_mono C φ w else (if isDL p then future_special_mono C φ w else future_priv_mono C φ w))
     else future_priv_mono C φ w )%I.

  (*Lemma that allows switching between the two different formulations of monotonicity, to alleviate the effects of inconsistencies*)
  Lemma switch_monotonicity_formulation
    (C : CmptName) (φ : WORLD * CmptName * Word → iProp Σ)
    (p : Perm) (w : Word) (ρ : region_type) :
    ρ ≠ Revoked → (∀ m, ρ ≠ Frozen m) ->
    monotonicity_guarantees_region C φ p w ρ  ≡ monotonicity_guarantees_decide C φ p w ρ.
  Proof.
    intros Hrev Hmono.
    unfold monotonicity_guarantees_region, monotonicity_guarantees_decide.
    iSplit; iIntros "HH".
    - destruct ρ;simpl;auto;try done.
      * destruct (isWL p), (isDL p);done.
      * specialize (Hmono g); done.
    - destruct ρ;simpl;auto;try done.
      destruct (isWL p), (isDL p); done.
  Qed.

  Global Instance monotonicity_guarantees_region_Persistent C P p w ρ :
    Persistent (monotonicity_guarantees_region C P p w ρ).
  Proof.
    destruct ρ; cbn; try apply _.
    all: destruct (isWL p), (isDL p); try apply _.
  Qed.

  Lemma region_open_next
    (W : WORLD) (C : CmptName)
    (φ : WORLD * CmptName * Word → iProp Σ)
    (als : list Addr) (a : Addr) (p : Perm) (ρ : region_type)
    (Hρnotrevoked : ρ <> Revoked)
    (Hρnotfrozen : ¬ exists g, ρ = Frozen g):
    a ∉ als →
    std W !! a = Some ρ →
    ⊢ open_region_many W C als
    ∗ rel C a p φ
    ∗ sts_full_world W C
    -∗ ∃ v : Word,
        sts_full_world W C
        ∗ sts_state_std C a ρ
        ∗ open_region_many W C (a :: als)
        ∗ a ↦ₐ v
        ∗ ▷ monotonicity_guarantees_region C φ p v ρ
        ∗ ▷ φ (W, C, v).
  Proof.
    rewrite /monotonicity_guarantees_region.
    intros. iIntros "H".
    destruct ρ; try congruence.
    - case_eq (isWL p); intros.
      + iDestruct (region_open_next_temp_pwl with "H") as (v) "[A [B [C [D [E [F G]]]]]]"
        ; eauto; iFrame.
      + iDestruct (region_open_next_temp_nwl with "H") as (v) "[A [B [C [D [E [F G]]]]]]"
        ; eauto; iFrame.
        destruct (isDL p); eauto.
    - iDestruct (region_open_next_perm with "H") as (v) "[A [B [C [D [E [F G]]]]]]"
      ; eauto; iFrame.
    - exfalso. apply Hρnotfrozen; eauto.
  Qed.

  Lemma region_close_next
    (W : WORLD) (C : CmptName)
    (φ : WORLD * CmptName * Word → iProp Σ)
    `{forall Wv, Persistent (φ Wv)}
    (als : list Addr) (a : Addr) (p : Perm) (v : Word) (ρ : region_type)
    (Hρnotrevoked : ρ <> Revoked)
    (Hρnotfrozen : ¬ exists g, ρ = Frozen g):
    a ∉ als
    → sts_state_std C a ρ
    ∗ open_region_many W C (a :: als)
    ∗ a ↦ₐ v
    ∗ ⌜isO p = false⌝
    ∗ monotonicity_guarantees_region C φ p v ρ
    ∗ ▷ φ (W, C, v)
    ∗ rel C a p φ
      -∗ open_region_many W C als.
  Proof.
    rewrite /monotonicity_guarantees_region.
    intros. iIntros "[A [B [C [D [E [F G]]]]]]".
    destruct ρ; try congruence.
    - case_eq (isWL p); intros.
      + iApply (region_close_next_temp_pwl with "[A B C D E F G]"); eauto; iFrame.
      + iApply (region_close_next_temp_nwl with "[A B C D E F G]"); eauto; iFrame.
        destruct (isDL p); eauto.
    - iApply (region_close_next_perm with "[A B C D E F G]"); eauto; iFrame.
    - exfalso. apply Hρnotfrozen. eauto.
  Qed.

  Lemma frozen_extend_preserve W (C : CmptName) (M : gmap Addr (gname*Perm)) (Mρ : gmap Addr region_type) (a : Addr) g ρ :
    a ∉ dom (std W) ->
    dom (std W) = dom M ->
    dom Mρ = dom M ->
    (∀ a' : Addr, a' ∈ dom g → Mρ !! a' = Some (Frozen g)) ->
    ∀ a' : Addr, a' ∈ dom g → <[a:=ρ]> Mρ !! a' = Some (Frozen g).
  Proof.
    intros Hl Hdom1 Hdom2 Hall.
    intros a' Hin. pose proof (Hall _ Hin) as Hcontr.
    assert (a' ∈ dom Mρ) as Hincontr;[apply elem_of_dom;eauto|].
    rewrite Hdom2 in Hincontr. apply elem_of_dom in Hincontr. clear Hcontr.
    assert (is_Some (std W !! a')) as Hcontr.
    { rewrite -elem_of_dom. rewrite Hdom1. rewrite elem_of_dom. eauto. }
    rewrite -elem_of_dom in Hcontr.
    assert (a' ≠ a) as Hne';[intros Heq;subst;contradiction|].
    rewrite lookup_insert_ne;auto.
  Qed.

  Lemma related_sts_priv_world_fresh_Permanent W a :
    related_sts_priv_world W (<s[a:=Permanent]s> W).
  Proof.
    apply related_sts_priv_world_fresh.
    intros ρ'; destruct ρ'.
    + eright;[right;constructor|left].
    + left.
    + eright;[left;constructor|].
      eright;[right;constructor|left].
    + eright;[left;constructor|].
      eright;[right;constructor|left].
  Qed.


End heap.
