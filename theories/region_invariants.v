From iris.algebra Require Import gmap agree auth.
From cap_machine Require Export stdpp_extra cap_lang sts rules_base.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export invariants na_invariants saved_prop.
(* import [stdpp.countable] before [cap_machine.lang]; this way [encode] and
   [decode] refer to [countable.encode] and [countable.decode], instead of
   [cap_lang.encode]/[cap_lang.decode]. *)
From stdpp Require Import countable.
Import uPred.

(** CMRA for heap and its predicates. Contains: *)
(* CMRA for relatedness between locations and saved prop names *)
(* CMRA for saved predicates *)
Definition relUR : ucmraT := gmapUR Addr (agreeR (leibnizO (gname))).
Definition relT := gmap Addr (leibnizO (gname)).

(* We will first define the standard STS for the shared part of the heap *)
Inductive region_type :=
| Monotemporary
| Permanent
| Revoked
| Monostatic of gmap Addr Word
| Uninitialized of Word.

Inductive std_rel_pub : region_type -> region_type -> Prop :=
| Std_pub_Revoked_Monotemporary : std_rel_pub Revoked Monotemporary
| Std_pub_Revoked_Permanent : std_rel_pub Revoked Permanent
| Std_pub_Uninitialized_Monotemporary w : std_rel_pub (Uninitialized w) Monotemporary.

Inductive std_rel_priv : region_type -> region_type -> Prop :=
| Std_priv_Monotemporary_Monostatic m : std_rel_priv Monotemporary (Monostatic m)
| Std_priv_Monotemporary_Revoked : std_rel_priv Monotemporary Revoked
| Std_priv_Monotemporary_Temporary : std_rel_priv Monotemporary Permanent.

Inductive std_rel_pub_plus : region_type → region_type → Prop :=
| Std_pub_plus_Monostatic_Monotemporary m : std_rel_pub_plus (Monostatic m) Monotemporary
| Std_pub_plus_Monotemporary_Monostatic w : std_rel_pub_plus Monotemporary (Uninitialized w).

Global Instance sts_std : STS_STD region_type :=
  {| Rpub := std_rel_pub; Rpubp := std_rel_pub_plus; Rpriv := std_rel_priv |}.

Global Instance le_addr_dec (a1 a2 : Addr) : Decision (Z.le a1 a2).
Proof. apply _. Qed.

Global Instance le_addr_preorder : PreOrder le_addr.
Proof.
  apply Build_PreOrder.
  - rewrite /Reflexive. solve_addr.
  - rewrite /Transitive. solve_addr.
Qed.

Global Instance addr_ord : Ord Addr :=
  {| le_a := le_addr;
     le_a_decision := le_addr_dec;
     le_a_preorder := le_addr_preorder |}.

Class heapPreG Σ := HeapPreG {
  heapPreG_invPreG : invPreG Σ;
  heapPreG_saved_pred :> savedPredG Σ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word);
  heapPreG_rel :> inG Σ (authR relUR);
}.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_saved_pred :> savedPredG Σ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word);
  heapG_rel :> inG Σ (authR relUR);
  γrel : gname
}.

Definition heapPreΣ :=
  #[ GFunctor (authR relUR) ].

Instance subG_heapPreΣ {Σ}:
  subG heapPreΣ Σ →
  invPreG Σ →
  subG (savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word)) Σ →
  heapPreG Σ.
Proof. solve_inG. Qed.

Section REL_defs.
  Context {Σ:gFunctors} {heapg : heapG Σ}.

  Definition REL_def l γ : iProp Σ := own γrel (◯ {[ l := to_agree γ ]}).
  Definition REL_aux : { x | x = @REL_def }. by eexists. Qed.
  Definition REL := proj1_sig REL_aux.
  Definition REL_eq : @REL = @REL_def := proj2_sig REL_aux.

  Definition RELS_def (M : relT) : iProp Σ := own γrel (● (to_agree <$> M : relUR)).
  Definition RELS_aux : { x | x = @RELS_def }. by eexists. Qed.
  Definition RELS := proj1_sig RELS_aux.
  Definition RELS_eq : @RELS = @RELS_def := proj2_sig RELS_aux.

  Definition rel_def (l : Addr) (φ : ((STS_std_states Addr region_type * (STS_states * STS_rels)) * Word) -> iProp Σ) : iProp Σ :=
    (∃ (γpred : gnameO), REL l γpred
                       ∗ saved_pred_own γpred φ)%I.
  Definition rel_aux : { x | x = @rel_def }. by eexists. Qed.
  Definition rel := proj1_sig rel_aux.
  Definition rel_eq : @rel = @rel_def := proj2_sig rel_aux.
End REL_defs.

Section heapPre.
  Context {Σ:gFunctors} {heappreg : heapPreG Σ}.

  Lemma heap_init :
    ⊢ |==> ∃ (heapg: heapG Σ), RELS (∅ : relT).
  Proof.
    iMod (own_alloc (A:= (authR relUR)) (● (to_agree <$> (∅: relT) : relUR))) as (γ) "H".
    { rewrite map_fmap_empty. by apply auth_auth_valid. }
    iMod (@wsat.wsat_alloc _ heapPreG_invPreG) as (HI) "?".
    iModIntro. iExists (HeapG _ HI _ _ γ). rewrite RELS_eq /RELS_def. done.
  Qed.

End heapPre.

Section heap.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MachineParameters}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Global Instance region_type_EqDecision : EqDecision region_type :=
    (fun x y => match x, y with
             | Permanent, Permanent
             | Revoked, Revoked
             | Monotemporary, Monotemporary => left eq_refl
             | Monostatic m1, Monostatic m2 => ltac:(solve_decision)
             | Uninitialized w1, Uninitialized w2 => ltac:(solve_decision)
             | _, _ => ltac:(right; auto)
             end).

  Lemma i_div i n m :
    i ≠ 0 ->
    (i | (i * n + m))%Z → (i | m)%Z.
  Proof.
    intros Hne [m' Hdiv].
    assert (((i * n + m) `div` i)%Z = ((m' * i) `div` i)%Z).
    { rewrite Hdiv. auto. }
    rewrite Z.div_mul in H0;[|lia].
    assert ((i * n + m) `div` i = ((i * n) `div` i) + (m `div` i))%Z as Heq.
    { rewrite Z.add_comm Z.mul_comm Z.div_add;[|lia].
      rewrite Z.div_mul;[|lia]. rewrite Z.add_comm. auto. }
    rewrite Heq in H0. rewrite Z.mul_comm Z.div_mul in H0;[|lia].
    assert (m `div` i = m' - n)%Z.
    { rewrite -H0. lia. }
    exists (m' - n)%Z. lia.
  Qed.

  Lemma two_div_odd n m :
    (2 | (2 * n + m))%Z → (2 | m)%Z.
  Proof.
    intros Hdiv. apply (i_div 2 n);auto.
  Qed.

  Lemma i_mod i n m k :
    (i > 0 ->
    (m + i * n) `mod` i = k → m `mod` i = k)%Z.
  Proof.
    intros Hlt Hmod.
    rewrite Z.mul_comm Z_mod_plus in Hmod;auto.
  Qed.

  Lemma three_mod n m k :
    ((m + 3 * n) `mod` 3 = k → m `mod` 3 = k)%Z.
  Proof.
    apply i_mod. lia.
  Qed.

  Lemma two_mod n m k :
    ((m + 2 * n) `mod` 2 = k → m `mod` 2 = k)%Z.
  Proof.
    apply i_mod. lia.
  Qed.

  Lemma four_mod_two :
    (4 `mod` 2 = 0)%Z.
  Proof. auto. Qed.
  Lemma five_mod_two :
    (5 `mod` 2 = 1)%Z.
  Proof. auto. Qed.

  Global Instance divide_dec : forall p1 p2, Decision (Pos.divide p1 p2).
  Proof.
    intros p1 p2.
    destruct (Znumtheory.Zdivide_dec (Z.pos p1) (Z.pos p2)).
    - left. by apply Pos2Z.inj_divide.
    - right. intros Hcontr. apply Pos2Z.inj_divide in Hcontr. done.
  Qed.

  Global Instance region_type_countable : Countable region_type.
  Proof.
    set encode := fun ty => match ty with
                         | Monotemporary => 1
                         | Permanent => 2
                         | Revoked => 3
                         | Monostatic m => 4 + 2 * (encode m)
                         | Uninitialized w => 5 + 2 * (encode w)
                         end%positive.
    set decode := (fun n =>
                     if decide (n = 1) then Some Monotemporary
                     else if decide (n = 2) then Some Permanent
                          else if decide (n = 3) then Some Revoked
                               else if decide (Zpos n `mod` 2 = 0)%Z then
                                      match (decode (Z.to_pos (((Zpos n)-4) / 2)%Z)) with
                                      | Some m => Some (Monostatic m)
                                      | None => None
                                      end
                                    else match (decode (Z.to_pos (((Zpos n)-5) / 2)%Z)) with
                                         | Some w => Some (Uninitialized w)
                                         | None => None
                                         end)%positive.
    eapply (Build_Countable _ _ encode decode).
    intro ty. destruct ty; try reflexivity;
    unfold encode, decode;
    repeat (match goal with |- context [ decide ?x ] =>
                            destruct (decide x); [ try (exfalso; lia) | ] end).
    - rewrite Pos2Z.inj_add Z.add_comm Z.add_simpl_r Pos2Z.inj_mul.
      rewrite Z.mul_comm Z.div_mul;[|lia]. rewrite Pos2Z.id decode_encode//.
    - exfalso. apply n2. rewrite Pos2Z.inj_add Pos2Z.inj_mul Z.mul_comm Z_mod_plus;auto. lia.
    - rewrite Pos2Z.inj_add Z.add_comm Pos2Z.inj_mul Z.add_comm in e. apply two_mod in e.
      rewrite five_mod_two in e. done.
    - rewrite Pos2Z.inj_add Z.add_comm Z.add_simpl_r Pos2Z.inj_mul.
      rewrite Z.mul_comm Z.div_mul;[|lia]. rewrite Pos2Z.id decode_encode//.
  Qed.


  Global Instance rel_persistent l (φ : (WORLD * Word) -> iProp Σ) :
    Persistent (rel l φ).
  Proof. rewrite rel_eq /rel_def REL_eq /REL_def. apply _. Qed.

  Definition future_pub_mono (φ : (WORLD * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ W W', ⌜related_sts_pub_world W W'⌝ → φ (W,v) -∗ φ (W',v))%I.

  Definition future_pub_plus_mono (φ : (WORLD * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ W W', ⌜related_sts_pub_plus_world W W'⌝ → φ (W,v) -∗ φ (W',v))%I.

  Definition future_pub_a_mono (a : Addr) (φ : (WORLD * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ W W', ⌜related_sts_a_world W W' a⌝ → φ (W,v) -∗ φ (W',v))%I.

  Definition future_priv_mono (φ : (WORLD * Word) -> iProp Σ) v : iProp Σ :=
    (□ ∀ W W', ⌜related_sts_priv_world W W'⌝ → φ (W,v) -∗ φ (W',v))%I.

  (* Some practical shorthands for projections *)
  Definition std W := W.1.
  Definition loc W := W.2.

  (* Asserting that a location is in a specific state in a given World *)

  Definition permanent (W : WORLD) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = Permanent
    | _ => False
    end.
  Definition revoked (W : WORLD) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = Revoked
    | _ => False
    end.
  Definition monostatic (W : WORLD) (m: gmap Addr Word) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = (Monostatic m)
    | _ => False
    end.
  Definition uninitialized (W : WORLD) (w:Word) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = Uninitialized w
    | _ => False
    end.
  Definition monotemporary (W : WORLD) (l : Addr) :=
    match W.1 !! l with
    | Some ρ => ρ = Monotemporary
    | _ => False
    end.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- REGION_MAP ---------------------------------------- *)
  (* ----------------------------------------------------------------------------------------------- *)

  Definition region_map_def M (Mρ: gmap Addr region_type) W :=
    ([∗ map] a↦γpred ∈ M, ∃ ρ, ⌜Mρ !! a = Some ρ⌝ ∗
                            sts_state_std a ρ ∗
                            ∃ φ, ⌜∀ Wv, Persistent (φ Wv)⌝ ∗ saved_pred_own γpred φ ∗
                            match ρ with
                            | Monotemporary => ∃ (v : Word),
                                               a ↦ₐ v
                                             ∗ future_pub_a_mono a φ v
                                             ∗ ▷ φ (W,v)
                            | Permanent => ∃ (v : Word),
                                               a ↦ₐ v
                                             ∗ future_priv_mono φ v
                                             ∗ ▷ φ (W,v)
                            | Monostatic m => ∃ v, ⌜m !! a = Some v⌝
                                             ∗ a ↦ₐ v
                                             ∗ ⌜∀ a', a' ∈ dom (gset Addr) m →
                                                      Mρ !! a' = Some (Monostatic m)⌝
                            | Uninitialized w => a ↦ₐ w
                            | Revoked => emp
                            end)%I.

  Definition region_def W : iProp Σ :=
    (∃ (M : relT) Mρ, RELS M ∗ ⌜dom (gset Addr) W.1 = dom (gset Addr) M⌝
                            ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝
                            ∗ region_map_def M Mρ W)%I.
  Definition region_aux : { x | x = @region_def }. by eexists. Qed.
  Definition region := proj1_sig region_aux.
  Definition region_eq : @region = @region_def := proj2_sig region_aux.

  Lemma reg_in γ (R : relT) (n : Addr) (r : leibnizO (gname)) :
    own γ (● (to_agree <$> R : relUR)) ∗ own γ (◯ {[n := to_agree r]}) -∗
        ⌜R = <[n := r]>(delete n R)⌝.
  Proof.
    iIntros "[H1 H2]".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro.
    apply auth_both_valid in Hv; destruct Hv as [Hv1 Hv2].
    specialize (Hv2 n).
    apply singleton_included_l in Hv1.
    destruct Hv1 as (y & Heq & Hi).
    revert Hv2; rewrite Heq => Hv2.
    revert Hi; rewrite Some_included_total => Hi.
    apply to_agree_uninj in Hv2 as [y' Hy].
    revert Hi Heq; rewrite -Hy => Hi Heq.
    apply to_agree_included in Hi; subst.
    revert Heq; rewrite -Hi => Heq.
    rewrite insert_delete insert_id /leibniz_equiv_iff => //; auto.
    revert Heq. rewrite lookup_fmap fmap_Some_equiv =>Hx.
    destruct Hx as [x [-> Hrx] ].
    apply to_agree_inj, leibniz_equiv_iff in Hrx as ->.
    done.
  Qed.

  Lemma rels_agree a γ1 γ2 :
    REL a γ1 ∗ REL a γ2 -∗ ⌜γ1 = γ2⌝.
  Proof.
    rewrite REL_eq /REL_def.
    iIntros "[Hγ1 Hγ2]".
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
    iPureIntro.
    rewrite -auth_frag_op singleton_op in Hval.
    apply singleton_valid in Hval.
    apply (agree_op_invL' (A:=leibnizO _)) in Hval.
    by inversion Hval.
  Qed.

  Lemma rel_agree a φ1 φ2 :
    rel a φ1 ∗ rel a φ2 -∗ (∀ x, ▷ (φ1 x ≡ φ2 x)).
  Proof.
    iIntros "[Hr1 Hr2]".
    rewrite rel_eq /rel_def.
    iDestruct "Hr1" as (γ1) "[Hrel1 Hpred1]".
    iDestruct "Hr2" as (γ2) "[Hrel2 Hpred2]".
    iDestruct (rels_agree with "[$Hrel1 $Hrel2]") as %->.
    iIntros (x). iApply (saved_pred_agree with "Hpred1 Hpred2").
  Qed.


  (* Definition and notation for updating a standard or local state in the STS collection *)
  Definition std_update (W : WORLD) (l : Addr) (a : region_type) : WORLD :=
    (<[ l := a]>W.1, W.2).
  Definition loc_update (W : WORLD) (l : Addr) (a : region_type) (r1 r2 r3 : region_type → region_type -> Prop) : WORLD :=
    (W.1,(<[encode l := encode a]>W.2.1,
          <[encode l := (convert_rel r1,convert_rel r2,convert_rel r3)]>W.2.2)).

  Notation "<s[ a := ρ ]s> W" := (std_update W a ρ) (at level 10, format "<s[ a := ρ ]s> W").
  Notation "<l[ a := ρ , r ]l> W" := (loc_update W a ρ r.1 r.2.1 r.2.2) (at level 10, format "<l[ a := ρ , r ]l> W").

  (* ------------------------------------------------------------------- *)
  (* region_map is monotone with regards to public future world relation *)

  Lemma region_map_monotone W W' M Mρ :
    related_sts_pub_world W W' →
    region_map_def M Mρ W -∗ region_map_def M Mρ W'.
  Proof.
    iIntros (Hrelated) "Hr".
    iApply big_sepM_mono; iFrame.
    iIntros (a γ Hsome) "Hm".
    iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
    iExists ρ. iFrame. iSplitR;[auto|].
    destruct ρ.
    - iDestruct "Hm" as (φ Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v) "(Hl & #Hmono & Hφ)".
      iExists _. do 2 (iSplitR;[eauto|]).
      iFrame "#". iExists _.
      iFrame "∗ #".
      iApply "Hmono"; iFrame; auto.
      iPureIntro. by apply related_sts_pub_a_world.
    - iDestruct "Hm" as (φ Hpers) "(#Hsavedφ & Hl)".
      iDestruct "Hl" as (v) "(Hl & #Hmono & Hφ)".
      iExists _. do 2 (iSplitR;[eauto|]).
      iFrame "∗ #". iExists _. iFrame "∗ #".
      iApply "Hmono"; iFrame "∗ #"; auto.
      iPureIntro.
      by apply related_sts_pub_priv_world.
    - done.
    - done.
    - done.
    Qed.

  Lemma region_monotone W W' :
    dom (gset Addr) W.1 = dom (gset Addr) W'.1 →
    related_sts_pub_world W W' → region W -∗ region W'.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite region_eq.
    iDestruct "HW" as (M Mρ) "(HM & % & % & Hmap)".
    iExists M, Mρ. iFrame.
    iSplitR; [iPureIntro;congruence|].
    iSplitR;[auto|].
    iApply region_map_monotone; eauto.
  Qed.

  Lemma uninitialized_mono_related_sts_pub_plus_world l W w :
    (std W) !! l = Some (Monostatic {[l:=w]}) ->
    related_sts_pub_plus_world W (<s[ l := Monotemporary ]s> W).
  Proof.
    intros. split;[|apply related_sts_pub_plus_refl].
    split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (i = l)).
      + subst. simplify_map_eq.
        rewrite lookup_insert in Hy. inv Hy.
        right with Monotemporary;[|left].
        right. constructor.
      + simplify_map_eq. rewrite lookup_insert_ne in Hy; auto.
        simplify_map_eq. left.
  Qed.

  Lemma uninitialized_w_mono_related_sts_pub_world l W w :
    (std W) !! l = Some (Uninitialized w) ->
    related_sts_pub_world W (<s[ l := Monotemporary ]s> W).
  Proof.
    intros. split;[|apply related_sts_pub_refl].
    split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (i = l)).
      + subst. simplify_map_eq.
        rewrite lookup_insert in Hy. inv Hy.
        right with Monotemporary;[|left].
        constructor.
      + simplify_map_eq. rewrite lookup_insert_ne in Hy; auto.
        simplify_map_eq. left.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------------------------- OPEN_REGION --------------------------------------- *)

  Definition open_region_def (a : Addr) (W : WORLD) : iProp Σ :=
    (∃ (M : relT) Mρ, RELS M ∗ ⌜dom (gset Addr) W.1 = dom (gset Addr) M⌝
                            ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝
                            ∗ region_map_def (delete a M) (delete a Mρ) W)%I.
  Definition open_region_aux : { x | x = @open_region_def }. by eexists. Qed.
  Definition open_region := proj1_sig open_region_aux.
  Definition open_region_eq : @open_region = @open_region_def := proj2_sig open_region_aux.

  (* open_region is monotone wrt public future worlds *)
  Lemma open_region_monotone l W W':
    dom (gset Addr) W.1 = dom (gset Addr) W'.1 →
    related_sts_pub_world W W' →
    open_region l W -∗ open_region l W'.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite open_region_eq /open_region_def.
    iDestruct "HW" as (M Mρ) "(Hm & % & % & Hmap)". iExists M, Mρ. iFrame.
    iSplitR;[iPureIntro;congruence|].
    iSplitR; auto.
    iApply region_map_monotone; eauto.
  Qed.

  (* ----------------------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS FOR OPENING THE REGION MAP ----------------------------------- *)

  Lemma region_map_delete_nonstatic M Mρ W l :
    (forall m, Mρ !! l ≠ Some (Monostatic m)) →
    region_map_def (delete l M) Mρ W -∗
    region_map_def (delete l M) (delete l Mρ) W.
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a = l)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (φ Hpers) "(#Hsavedφ & Hl)".
    iDestruct "Hl" as (v) "(#Hmono & Hφ & Hothers)".
    iExists _. do 2 (iSplitR;[eauto|]).
    iDestruct "Hothers" as %Hothers. iFrame "#".
    iExists _. iSplitR; eauto. iFrame. iPureIntro.
    intros a' Ha'. destruct (decide (a' = l)).
    { subst. exfalso. apply Hothers in Ha'. destruct Hl with g. congruence. }
    { by simplify_map_eq. }
  Qed.

  Lemma region_map_delete_monosingleton M Mρ W l :
    (∃ w, Mρ !! l = Some (Monostatic {[l:=w]})) ->
    region_map_def (delete l M) Mρ W -∗
    region_map_def (delete l M) (delete l Mρ) W.
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a = l)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (φ Hpers) "(#Hsavedφ & Hl)".
    iDestruct "Hl" as (v) "(% & Hφ & Hothers)".
    iExists _. do 2 (iSplitR;[eauto|]).
    iDestruct "Hothers" as %Hothers. iFrame "#".
    iExists _. iSplitR; eauto. iFrame. iPureIntro.
    intros a' Ha'. destruct (decide (a' = l)).
    { subst. destruct Hl as [w Hl].
      exfalso. assert (l ≠ a) as Hne;[intros Hcontr;subst;rewrite lookup_delete in Ha;inversion Ha|].
      apply Hothers in Ha'. rewrite Hl in Ha'. inversion Ha'. subst. simplify_map_eq. }
    { by simplify_map_eq. }
  Qed.

  Lemma region_open_monotemp W l φ :
    (std W) !! l = Some Monotemporary →
    rel l φ ∗ region W ∗ sts_full_world W -∗
        ∃ v, open_region l W
           ∗ sts_full_world W
           ∗ sts_state_std l Monotemporary
           ∗ l ↦ₐ v
           ∗ ▷ future_pub_a_mono l φ v
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Htemp) "(Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#(Hγpred & Hφ)".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)".
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel (M) with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (φ' Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v) "(Hl & #Hmono & Hφv)".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv".
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #".
      iExists Mρ. do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. rewrite Hρ; auto.
    - iSplitR.
      + rewrite /future_pub_mono.
        iApply later_intuitionistically_2. iModIntro.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq''").
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq'"). iFrame.
      + iNext. iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  Lemma region_open_perm W l φ :
    (std W) !! l = Some Permanent →
    rel l φ ∗ region W ∗ sts_full_world W -∗
        ∃ v, open_region l W
           ∗ sts_full_world W
           ∗ sts_state_std l Permanent
           ∗ l ↦ₐ v
           ∗ ▷ future_priv_mono φ v
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Htemp) "(Hrel & Hreg & Hfull)".
    rewrite rel_eq region_eq /rel_def /region_def REL_eq RELS_eq /REL_def /RELS_def /region_map_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hreg" as (M Mρ) "(HM & % & % & Hpreds)".
    (* assert that γrel = γrel' *)
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (φ' Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v) "(Hl & #Hmono & Hφv)".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists v. iFrame.
    iSplitR "Hφv".
    - rewrite open_region_eq /open_region_def.
      iExists _. rewrite RELS_eq /RELS_def -HMeq. iFrame "∗ #".
      iExists _. do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. rewrite Hρ;auto. 
    - iSplitR.
      + rewrite /future_priv_mono.
        iApply later_intuitionistically_2. iModIntro.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq'").
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq''"). iFrame.
      + iNext. iRewrite "Hφeq". iFrame "∗ #".
  Qed.

  Lemma region_open_uninitialized W l v φ :
    (std W) !! l = Some (Uninitialized v) →
    rel l φ ∗ region W ∗ sts_full_world W -∗
        open_region l W
        ∗ sts_full_world W
        ∗ sts_state_std l (Uninitialized v)
        ∗ l ↦ₐ v.
  Proof.
    iIntros (Htemp) "(Hrel & Hreg & Hfull)".
    rewrite region_eq /region_def /region_map_def rel_eq /rel_def REL_eq /REL_def.
    iDestruct "Hreg" as (M Mρ) "(HM & HMW & % & Hpreds)". iDestruct "HMW" as %HMW.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    rewrite RELS_eq /RELS_def.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    assert (is_Some(M !! l)) as [γp HX].
    { apply elem_of_gmap_dom. rewrite -HMW. apply elem_of_gmap_dom. eauto. }
    iDestruct (big_sepM_delete with "Hpreds") as "[Hl Hpreds]"; eauto.
    iDestruct "Hl" as (ρ) "[ % [Hstate Hl] ]". destruct ρ.
    1,2,3,4,5: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
    1,2,3,4,5: rewrite Htemp in Hcontr; try by inversion Hcontr.
    iDestruct "Hl" as (φ') "(#Hpers & #Hsaved & Hl)". inversion Hcontr.
    subst.
    rewrite open_region_eq /open_region_def RELS_eq /RELS_def. iFrame.
    iExists M,Mρ. iFrame.
    repeat iSplit;auto. iApply region_map_delete_nonstatic; eauto.
    rewrite H1. eauto.
  Qed.

  Lemma region_open W l φ (ρ : region_type) :
    ρ = Permanent ∨ ρ = Monotemporary →
    (std W) !! l = Some ρ →
    rel l φ ∗ region W ∗ sts_full_world W -∗
        ∃ v, open_region l W
           ∗ sts_full_world W
           ∗ sts_state_std l ρ
           ∗ l ↦ₐ v
           ∗ (▷ if (decide (ρ = Monotemporary))
                then future_pub_a_mono l φ v
                else future_priv_mono φ v)
           ∗ ▷ φ (W,v).
  Proof.
    iIntros (Hne Htemp) "(Hrel & Hreg & Hfull)".
    destruct ρ; destruct Hne as [Hne | Hne]; try (exfalso; congruence).
    - iDestruct (region_open_monotemp with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hmono & φ)"; auto.
      iExists _; iFrame.
    - iDestruct (region_open_perm with "[$Hrel $Hreg $Hfull]") as (v) "(Hr & Hfull & Hstate & Hl & Hmono & φ)"; auto.
      iExists _; iFrame.
  Qed.

  (* It is important here that we have (delete l Mρ) and not simply Mρ.
     Otherwise, [Mρ !! l] could in principle map to a static region (although
     it's not the case in practice), that it would be incorrect to overwrite
     with a non-static state. *)
  Lemma region_map_undelete_nonmonostatic M Mρ W l :
    (forall m, Mρ !! l ≠ Some (Monostatic m)) →
    region_map_def (delete l M) (delete l Mρ) W -∗
    region_map_def (delete l M) Mρ W.
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a = l)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (φ' Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v HH2) "(Hl & Hothers)".
    iDestruct "Hothers" as %Hothers.
    iExists _. iSplitR; eauto. iFrame "∗ #".
    iExists _. iFrame. repeat iSplit;auto. iPureIntro.
    intros a' Ha'. apply Hothers in Ha'.
    destruct (decide (a' = l)); by simplify_map_eq.
  Qed.

  Lemma region_map_insert_nonmonostatic ρ M Mρ W l :
    (forall m, ρ ≠ Monostatic m) →
    region_map_def (delete l M) (delete l Mρ) W -∗
    region_map_def (delete l M) (<[ l := ρ ]> Mρ) W.
  Proof.
    iIntros (?) "HH".
    rewrite {1}(_: delete l Mρ = delete l (<[ l := ρ ]> Mρ)). 2: by rewrite delete_insert_delete//.
    iDestruct (region_map_undelete_nonmonostatic with "HH") as "HH".
    { intro. simplify_map_eq. congruence. }
    auto.
  Qed.

  (* We can apply the same reasoning to singleton static regions (i.e. uninitialised regions) *)
  Lemma region_map_undelete_monosingleton M Mρ W l :
    (∃ w, Mρ !! l = Some (Monostatic {[l:=w]})) →
    region_map_def (delete l M) (delete l Mρ) W -∗
    region_map_def (delete l M) Mρ W.
  Proof.
    iIntros (Hl) "Hr". iApply (big_sepM_mono with "Hr").
    iIntros (a γr Ha) "HH". iDestruct "HH" as (ρ Hρ) "(Hsts & HH)".
    iExists ρ.
    iSplitR; eauto.
    { iPureIntro. destruct (decide (a = l)); simplify_map_eq/=. congruence. }
    iFrame. destruct ρ; try by iFrame.
    iDestruct "HH" as (φ' Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v HH2) "(Hl & Hothers)".
    iDestruct "Hothers" as %Hothers.
    iExists _. iSplitR; eauto. iFrame "∗ #".
    iExists _. iFrame. repeat iSplit;auto. iPureIntro.
    intros a' Ha'. apply Hothers in Ha'.
    destruct (decide (a' = l)); by simplify_map_eq.
  Qed.

  Lemma region_map_insert_monosingleton ρ M Mρ W l :
    (∃ w, ρ = Monostatic {[l:=w]}) →
    region_map_def (delete l M) (delete l Mρ) W -∗
    region_map_def (delete l M) (<[ l := ρ ]> Mρ) W.
  Proof.
    iIntros (?) "HH".
    rewrite {1}(_: delete l Mρ = delete l (<[ l := ρ ]> Mρ)). 2: by rewrite delete_insert_delete//.
    iDestruct (region_map_undelete_monosingleton with "HH") as "HH".
    { simplify_map_eq. naive_solver. }
    auto.
  Qed.


  Lemma full_sts_Mρ_agree W M Mρ (ρ: region_type) :
    (* NB: only the forward direction of dom_equal (std_sta W) M is actually needed *)
    dom (gset Addr) (std W) = dom (gset Addr) M →
    (* NB: only one direction of this assumption is needed, and only for the reverse *)
  (*      direction of the lemma *)
    dom (gset Addr) Mρ = dom (gset Addr) M →
    sts_full_world W -∗
    region_map_def M Mρ W -∗
    ⌜∀ a:Addr, (std W) !! a = Some ρ ↔ Mρ !! a = Some ρ⌝.
  Proof.
    iIntros (HWM HMMρ) "Hfull Hr".
    iAssert (∀ a:Addr, ⌜ std W !! a = Some ρ ⌝ → ⌜ Mρ !! a = Some ρ ⌝)%I as %?.
    { iIntros (a Haρ).
      assert (is_Some (M !! a)) as [γp Hγp].
      { apply elem_of_gmap_dom.
        rewrite -HWM. apply elem_of_gmap_dom. eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). apply encode_inj.
      rewrite Haρ in Haρ'. congruence. }
    iAssert (∀ a:Addr, ⌜ Mρ !! a = Some ρ ⌝ → ⌜ std W !! a = Some ρ ⌝)%I as %?.
    { iIntros (a HMρa).
      assert (is_Some (M !! a)) as [γp Hγp].
      { rewrite elem_of_gmap_dom -HMMρ -elem_of_gmap_dom. eauto. }
      iDestruct (big_sepM_lookup with "Hr") as (ρ' Hρ') "(Hst & _)"; eauto; [].
      iDestruct (sts_full_state_std with "Hfull Hst") as %Haρ'.
      enough (ρ = ρ') by (subst; eauto). rewrite HMρa in Hρ'. congruence. }
    iPureIntro. intros. split; eauto.
  Qed.

  Lemma full_sts_monostatic_all W m (l : Addr) :
    (std W) !! l = Some (Monostatic m) →
    sts_full_world W -∗
    region W -∗
    ⌜forall a, a ∈ dom (gset Addr) m -> monostatic W m a⌝.
  Proof.
    iIntros (Hstatic) "Hsts Hr".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & #Hdom1 & #Hdom2 & Hr)".
    iDestruct "Hdom1" as %Hdom1. iDestruct "Hdom2" as %Hdom2.
    iDestruct (full_sts_Mρ_agree _ _ _ (Monostatic m) with "Hsts Hr") as %[Hag _]; auto.
    pose proof (Hag Hstatic) as Hl.
    iIntros (a Hdom).
    assert (is_Some (M !! l)) as [γp Hsome].
    { apply elem_of_gmap_dom. rewrite -Hdom1. apply elem_of_gmap_dom. eauto. }
    rewrite /region_map_def.
    iDestruct (big_sepM_delete _ _ l with "Hr") as "[Hl Hr]";[eauto|].
    iDestruct "Hl" as (ρ Hρ) "(Hstate & Hρ)".
    rewrite Hl in Hρ. inversion Hρ.
    iDestruct "Hρ" as (φ Hpers) "(#Hsaved & Hl)".
    iDestruct "Hl" as (v Hpv') "[Hl #Hall]". iDestruct "Hall" as %Hall.
    iDestruct (big_sepM_delete _ _ l with "[$Hr Hl Hstate]") as "Hr";[eauto|..].
    { iExists ρ. iSplitR;subst;auto. iFrame. iExists _. repeat iSplit;eauto. }
    iDestruct (full_sts_Mρ_agree _ _ _ (Monostatic m) with "Hsts Hr") as %[_ Hag']; auto.
    iPureIntro.
    rewrite /monostatic.
    pose proof (Hall _ Hdom) as Ha. rewrite /std in Hag'.
    pose proof (Hag' Ha) as ->. auto.
  Qed.

  (* Closing the region without updating the sts collection *)
  Lemma region_close_monotemp W l φ v `{forall Wv, Persistent (φ Wv)} :
    ⊢ sts_state_std l Monotemporary
      ∗ open_region l W ∗ l ↦ₐ v ∗ future_pub_a_mono l φ v ∗ ▷ φ (W,v) ∗ rel l φ
      -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros "(Hstate & Hreg_open & Hl & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonmonostatic Monotemporary with "Hpreds") as "Hpreds". by congruence.
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Monotemporary. iFrame. iSplitR; [by simplify_map_eq|].
      iExists _. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    iFrame. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    iExists _, _. rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close_mono_uninit_w E W l φ w v `{forall Wv, Persistent (φ Wv)} :
    sts_state_std l (Uninitialized w)
    ∗ open_region l W
    ∗ l ↦ₐ v
    ∗ future_pub_a_mono l φ v
    ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *)
    ∗ rel l φ
    ∗ sts_full_world W
    ={E}=∗ region (<s[ l := Monotemporary ]s> W) ∗ sts_full_world (<s[ l := Monotemporary ]s> W).
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros "(Hstate & Hreg_open & Hl & #Hmono & #Hφ & #Hrel & Hfull)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    iDestruct (sts_full_state_std with "Hfull Hstate") as "%".
    iDestruct (sts_update_std with "Hfull Hstate") as ">[Hfull Hstate]".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    iModIntro. iFrame.
    iDestruct (region_map_insert_nonmonostatic Monotemporary with "Hpreds") as "Hpreds";[intros;auto|].
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Monotemporary. iFrame.
      iSplit;[iPureIntro;apply lookup_insert|].
      iExists _. iFrame "∗ #". repeat iSplitR; auto. }
    assert (Hpub: related_sts_pub_world W (<s[l:=Monotemporary ]s>W)).
    { eapply (uninitialized_w_mono_related_sts_pub_world l W); eauto. }
    iDestruct (region_map_monotone _ _ _ _ Hpub with "test") as "HMdef"; eauto.
    rewrite -HMeq. iExists M,_; iFrame. iPureIntro.
    repeat rewrite dom_insert_L. assert (l ∈ dom (gset Addr) W.1) as Hin;[apply elem_of_gmap_dom;eauto|].
    split;[rewrite -HMW| rewrite HMρ -HMW];set_solver.
  Qed.

  Lemma region_close_perm W l φ v `{forall Wv, Persistent (φ Wv)}:
    ⊢ sts_state_std l Permanent
      ∗ open_region l W ∗ l ↦ₐ v ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l φ
      -∗ region W.
  Proof.
    rewrite open_region_eq rel_eq region_eq /open_region_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros "(Hstate & Hreg_open & Hl & #Hmono & Hφ & #Hrel)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.

    iDestruct (region_map_insert_nonmonostatic Permanent with "Hpreds") as "Hpreds". by congruence.
    iDestruct (big_sepM_insert _ (delete l M) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists Permanent. iFrame. iSplitR; [by simplify_map_eq|].
      iExists _. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    iExists _,_. iFrame "∗ #".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close W l φ v (ρ : region_type) `{forall Wv, Persistent (φ Wv)} :
    ρ = Permanent ∨ ρ = Monotemporary→
    sts_state_std l ρ
                  ∗ open_region l W ∗ l ↦ₐ v ∗
                  (if (decide (ρ = Monotemporary))
                   then future_pub_a_mono l φ v
                   else future_priv_mono φ v) ∗ ▷ φ (W,v) ∗ rel l φ
    -∗ region W.
  Proof.
    iIntros (Htp) "(Hstate & Hreg_open & Hl & Hmono & Hφ & Hrel)".
    destruct ρ; try (destruct Htp as [Htp | Htp ]; exfalso; congruence).
    - iApply region_close_monotemp; eauto. iFrame.
    - iApply region_close_perm; eauto. iFrame.
  Qed.

  (* ---------------------------------------------------------------------------------------- *)
  (* ----------------------- OPENING MULTIPLE LOCATIONS IN REGION --------------------------- *)

  Definition open_region_many_def (l : list Addr) (W : WORLD) : iProp Σ :=
    (∃ M Mρ, RELS M ∗ ⌜dom (gset Addr) (std W) = dom (gset Addr) M⌝
                    ∗ ⌜dom (gset Addr) Mρ = dom (gset Addr) M⌝
                    ∗ region_map_def (delete_list l M) (delete_list l Mρ) W)%I.
  Definition open_region_many_aux : { x | x = @open_region_many_def }. by eexists. Qed.
  Definition open_region_many := proj1_sig open_region_many_aux.
  Definition open_region_many_eq : @open_region_many = @open_region_many_def := proj2_sig open_region_many_aux.

  Lemma open_region_many_monotone l W W':
    dom (gset Addr) (std W) = dom (gset Addr) (std W') →
    related_sts_pub_world W W' →
    open_region_many l W -∗ open_region_many l W'.
  Proof.
    iIntros (Hdomeq Hrelated) "HW". rewrite open_region_many_eq /open_region_many_def.
    iDestruct "HW" as (M Mρ) "(Hm & % & % & Hmap)". iExists M, Mρ. iFrame.
    iSplitR;[iPureIntro;congruence|].
    iSplitR; auto.
    iApply region_map_monotone; eauto.
  Qed.

  Lemma open_region_many_permutation l1 l2 W:
    l1 ≡ₚ l2 → open_region_many l1 W -∗ open_region_many l2 W.
  Proof.
    intros Hperm.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros "H". iDestruct "H" as (? ?) "(? & % & % & ?)".
    rewrite !(delete_list_permutation l1 l2) //. iExists _,_. iFrame. eauto.
  Qed.

   Lemma region_open_prepare l W :
    open_region l W ⊣⊢ open_region_many [l] W.
  Proof.
    iSplit; iIntros "Hopen";
    rewrite open_region_eq open_region_many_eq /=;
    iFrame.
  Qed.

  Lemma region_open_nil W :
    region W ⊣⊢ open_region_many [] W.
  Proof.
    iSplit; iIntros "H";
    rewrite region_eq open_region_many_eq /=;
            iFrame.
  Qed.

  Lemma region_open_next_monotemp W φ ls l :
    l ∉ ls →
    (std W) !! l = Some Monotemporary ->
    open_region_many ls W ∗ rel l φ ∗ sts_full_world W -∗
                     ∃ v, open_region_many (l :: ls) W
                        ∗ sts_full_world W
                        ∗ sts_state_std l Monotemporary
                        ∗ l ↦ₐ v
                        ∗ ▷ future_pub_a_mono l φ v
                        ∗ ▷ φ (W,v).
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /region_map_def /=.
    rewrite rel_eq /rel_def /rel_def /region_def REL_eq RELS_eq /rel /region /REL /RELS.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (φ' Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v) "(Hl & #Hmono & Hφv)".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv".
    - iExists _,_. repeat (rewrite -HMeq). iFrame "∗ #".
      do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. rewrite Hρ;auto. 
    - iSplitR;[auto|].
      + rewrite /future_pub_mono.
        iApply later_intuitionistically_2. iModIntro.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq''").
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq'"). iFrame.
      + iNext.
        iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_perm W φ ls l :
    l ∉ ls → (std W) !! l = Some Permanent ->
    open_region_many ls W ∗ rel l φ ∗ sts_full_world W -∗
                     ∃ v, sts_full_world W
                        ∗ sts_state_std l Permanent
                        ∗ open_region_many (l :: ls) W
                        ∗ l ↦ₐ v
                        ∗ ▷ future_priv_mono φ v
                        ∗ ▷ φ (W,v).
  Proof.
    rewrite open_region_many_eq .
    iIntros (Hnin Htemp) "(Hopen & #Hrel & Hfull)".
    rewrite /open_region_many_def /= /region_map_def.
    rewrite rel_eq /rel_def /rel_def /region_def REL_eq RELS_eq /rel /region /REL /RELS.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct "Hopen" as (M Mρ) "(HM & % & % & Hpreds)".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite HMeq delete_list_insert; auto.
    rewrite delete_list_delete; auto.
    rewrite HMeq big_sepM_insert; [|by rewrite lookup_delete].
    iDestruct "Hpreds" as "[Hl Hpreds]".
    iDestruct "Hl" as (ρ Hρ) "[Hstate Hl]".
    iDestruct (sts_full_state_std with "Hfull Hstate") as %Hst.
    rewrite Htemp in Hst. (destruct ρ; try by simplify_eq); [].
    iDestruct "Hl" as (φ' Hpers) "(#Hφ' & Hl)".
    iDestruct "Hl" as (v) "(Hl & #Hmono & Hφv)".
    iDestruct (saved_pred_agree _ _ _ (W,v) with "Hφ Hφ'") as "#Hφeq".
    iExists _. iFrame.
    iSplitR "Hφv".
    - rewrite /open_region.
      iExists _,_. repeat (rewrite -HMeq). iFrame "∗ #". do 2 (iSplitR; eauto).
      iApply region_map_delete_nonstatic; auto. rewrite Hρ;auto.
    - iSplitR;[auto|].
      + iApply later_intuitionistically_2. iModIntro.
        repeat (iApply later_forall_2; iIntros (?)).
        iDestruct (saved_pred_agree _ _ _ (a0,v) with "Hφ Hφ'") as "#Hφeq'".
        iDestruct (saved_pred_agree _ _ _ (a,v) with "Hφ Hφ'") as "#Hφeq''".
        iNext. iIntros (Hrel) "Hφw".
        iRewrite ("Hφeq'").
        iApply "Hmono"; eauto.
        iRewrite -("Hφeq''"). iFrame.
      + iNext.
        iRewrite "Hφeq". iFrame.
  Qed.

  Lemma region_open_next_monouninit W w ls l φ :
    l ∉ ls →
    (std W) !! l = Some (Monostatic {[l:=w]}) →
    rel l φ ∗ open_region_many ls W ∗ sts_full_world W -∗
        open_region_many (l :: ls) W
        ∗ sts_full_world W
        ∗ sts_state_std l (Monostatic {[l:=w]})
        ∗ l ↦ₐ w.
  Proof.
    iIntros (Hnin Htemp) "(Hrel & Hreg & Hfull)".
    rewrite open_region_many_eq /open_region_many_def /= /region_map_def rel_eq /rel_def REL_eq /REL_def.
    iDestruct "Hreg" as (M Mρ) "(HM & HMW & % & Hpreds)". iDestruct "HMW" as %HMW.
    rewrite RELS_eq /RELS_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    assert (is_Some (M !! l)) as [γp HX].
    { apply elem_of_gmap_dom. rewrite -HMW. apply elem_of_gmap_dom. eauto. }
    iDestruct (big_sepM_delete with "Hpreds") as "[Hl Hpreds]"; eauto.
    { rewrite lookup_delete_list_notin; eauto. }
    iDestruct "Hl" as (ρ) "[% [Hstate Hl] ]". destruct ρ.
    1,2,3,4,5: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
    1,2,3,4,5: rewrite Htemp in Hcontr; try by inversion Hcontr.
    iDestruct "Hl" as (φ' Hpers) "[#Hsaved Hl]".
    iDestruct "Hl" as (v Hlookup) "[Hl _]".
    inversion Hcontr; subst g.
    rewrite lookup_insert in Hlookup;inversion Hlookup. iFrame.
    iExists M,Mρ. iFrame "∗ #".
    iDestruct (region_map_delete_monosingleton with "Hpreds") as "Hpreds"; eauto.
  Qed.

  Lemma region_open_next_monouninit_w W w ls l φ :
    l ∉ ls →
    (std W) !! l = Some (Uninitialized w) →
    rel l φ ∗ open_region_many ls W ∗ sts_full_world W -∗
        open_region_many (l :: ls) W
        ∗ sts_full_world W
        ∗ sts_state_std l (Uninitialized w)
        ∗ l ↦ₐ w.
  Proof.
    iIntros (Hnin Htemp) "(Hrel & Hreg & Hfull)".
    rewrite open_region_many_eq /open_region_many_def /= /region_map_def rel_eq /rel_def REL_eq /REL_def.
    iDestruct "Hreg" as (M Mρ) "(HM & HMW & % & Hpreds)". iDestruct "HMW" as %HMW.
    rewrite RELS_eq /RELS_def.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ]".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    assert (is_Some (M !! l)) as [γp HX].
    { apply elem_of_gmap_dom. rewrite -HMW. apply elem_of_gmap_dom. eauto. }
    iDestruct (big_sepM_delete with "Hpreds") as "[Hl Hpreds]"; eauto.
    { rewrite lookup_delete_list_notin; eauto. }
    iDestruct "Hl" as (ρ) "[% [Hstate Hl] ]". destruct ρ.
    1,2,3,4,5: iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
    1,2,3,4,5: rewrite Htemp in Hcontr; try by inversion Hcontr.
    iDestruct "Hl" as (φ' Hpers) "[#Hsaved Hl]".
    inversion Hcontr; subst w.
    iFrame.
    iExists M,Mρ. iFrame "∗ #".
    iDestruct (region_map_delete_nonstatic with "Hpreds") as "Hpreds"; eauto.
    rewrite H1. eauto.
  Qed.

  Lemma region_close_next_monotemp W φ ls l v `{forall Wv, Persistent (φ Wv)} :
    l ∉ ls ->
    ⊢ sts_state_std l Monotemporary ∗
      open_region_many (l::ls) W ∗ l ↦ₐ v ∗ future_pub_a_mono l φ v ∗ ▷ φ (W,v) ∗ rel l φ
      -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonmonostatic Monotemporary with "Hpreds") as "Hpreds". congruence.
    rewrite -!/delete_list.
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iSplitR; [by simplify_map_eq|].
      iExists _. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    rewrite -(delete_list_delete _ M) //.
    rewrite -(delete_list_insert _ (delete l M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists (<[l:=γpred ]> (delete l M)), (<[l:=Monotemporary]> Mρ). iFrame.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; eauto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Lemma region_close_next_mono_uninit_w E W ls l φ w v `{forall Wv, Persistent (φ Wv)} :
    l ∉ ls ->
    sts_state_std l (Uninitialized w)
    ∗ open_region_many (l::ls) W
    ∗ l ↦ₐ v
    ∗ future_pub_a_mono l φ v
    ∗ ▷ φ (W,v) (* Maybe φ (<l[ l := Temporary, (Rpub, Rpriv) ]l> W, v) *)
    ∗ rel l φ
    ∗ sts_full_world W
    ={E}=∗ open_region_many ls (<s[ l := Monotemporary ]s> W) ∗ sts_full_world (<s[ l := Monotemporary ]s> W).
  Proof.
    rewrite open_region_many_eq rel_eq /open_region_many_def /rel_def /region_def
            REL_eq RELS_eq /RELS_def /REL_def.
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & #Hmono & Hφ & #Hrel & Hfull)".
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & HMW & HMρ & Hpreds)".
    iDestruct "HMW" as %HMW. iDestruct "HMρ" as %HMρ.
    iDestruct (sts_full_state_std with "Hfull Hstate") as "%".
    iDestruct (sts_update_std with "Hfull Hstate") as ">[Hfull Hstate]".
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    iModIntro. iSplitR "Hfull".
    { iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "Hmap_def";
        first by rewrite lookup_delete.
      { simpl. iDestruct (region_map_insert_nonmonostatic Monotemporary with "Hpreds") as "Hpreds". by congruence.
        iFrame. iExists Monotemporary. iFrame.
        iSplit;[iPureIntro;apply lookup_insert|].
        iExists  _. iFrame "∗ #". repeat iSplitR; auto. }
      assert (Hpub: related_sts_pub_world W (<s[l:=Monotemporary]s>W)).
      { eapply (uninitialized_w_mono_related_sts_pub_world l W); eauto. }
      iDestruct (region_map_monotone _ _ _ _ Hpub with "Hmap_def") as "HMdef"; eauto.
      iExists M,(<[l:=Monotemporary]>Mρ); iFrame. rewrite HMeq.
      repeat rewrite dom_insert_L. rewrite dom_delete_L.
      assert (l ∈ dom (gset Addr) W.1) as Hin;[apply elem_of_gmap_dom;eauto|].
      assert ({[l]} ∪ dom (gset Addr) (std W) ∖ {[l]} = dom (gset Addr) (std W)) as Heq.
      { rewrite union_comm_L difference_union_L. set_solver. }
      repeat iSplit.
      - iPureIntro. rewrite -HMW. set_solver.
      - iPureIntro. rewrite HMρ -HMW.
        set_solver.
      - repeat rewrite insert_delete. rewrite delete_list_insert; auto.
        rewrite insert_insert. rewrite delete_list_insert; auto. }
    iFrame.
  Qed.

  Lemma region_close_next_perm W φ ls l v `{forall Wv, Persistent (φ Wv)} :
    l ∉ ls ->
    ⊢ sts_state_std l Permanent ∗
      open_region_many (l::ls) W ∗ l ↦ₐ v ∗ future_priv_mono φ v ∗ ▷ φ (W,v) ∗ rel l φ
      -∗ open_region_many ls W.
  Proof.
    rewrite open_region_many_eq /open_region_many_def.
    iIntros (Hnin) "(Hstate & Hreg_open & Hl & #Hmono & Hφ & #Hrel)".
    rewrite rel_eq /rel_def REL_eq RELS_eq /rel /region /RELS /REL.
    iDestruct "Hrel" as (γpred) "#[Hγpred Hφ_saved]".
    iDestruct "Hreg_open" as (M Mρ) "(HM & % & Hdomρ & Hpreds)". iDestruct "Hdomρ" as %Hdomρ.
    iDestruct (region_map_insert_nonmonostatic Permanent with "Hpreds") as "Hpreds". congruence.
    iDestruct (big_sepM_insert _ (delete l (delete_list ls M)) l with "[-HM]") as "test";
      first by rewrite lookup_delete.
    { iFrame. iExists _; iFrame. iSplitR; [by simplify_map_eq|].
      iExists _. iFrame "∗ #". repeat (iSplitR;[eauto|]). iExists _. iFrame. auto. }
    rewrite -(delete_list_delete _ M) // -(delete_list_insert _ (delete _ M)) //.
    rewrite -(delete_list_insert _ Mρ) //.
    iExists _, _. iFrame.
    iDestruct (reg_in γrel M with "[$HM $Hγpred]") as %HMeq.
    rewrite -HMeq. iFrame. iSplitR; auto. iPureIntro.
    rewrite HMeq !insert_delete !dom_insert_L Hdomρ. set_solver.
  Qed.

  Definition monotonicity_guarantees_region ρ l w φ :=
    (match ρ with
     | Monotemporary => future_pub_a_mono l
     | Permanent => future_priv_mono
     | Revoked | Monostatic _ | Uninitialized _ => λ (_ : WORLD * Word → iProp Σ) (_ : Word), True
     end φ w)%I.

  Definition monotonicity_guarantees_decide ρ l w φ:=
    (if decide (ρ = Monotemporary)
     then future_pub_a_mono l φ w
     else future_priv_mono φ w)%I.

   Lemma region_open_next
        (W : WORLD)
        (φ : WORLD * Word → iProp Σ)
        (ls : list Addr) (l : Addr) (p : Perm) (ρ : region_type)
        (Hρnotrevoked : ρ <> Revoked)
        (Hρnotmonostatic : ¬ exists g, ρ = Monostatic g)
        (Hρnotuninitialized : ¬ exists w, ρ = Uninitialized w):
     l ∉ ls →
     std W !! l = Some ρ →
     ⊢ open_region_many ls W ∗ rel l φ ∗ sts_full_world W
       -∗ ∃ v : Word,
         sts_full_world W
                        ∗ sts_state_std l ρ
                        ∗ open_region_many (l :: ls) W
                        ∗ l ↦ₐ v ∗ ▷ monotonicity_guarantees_region ρ l v φ ∗
                        ▷ φ (W, v).
   Proof.
    unfold monotonicity_guarantees_region.
    intros. iIntros "H".
    destruct ρ; try congruence.
    - iDestruct (region_open_next_monotemp with "H") as (v) "[A [B [C [D [E F]]]]]"; eauto.
      iExists v. iFrame.
    - iApply (region_open_next_perm with "H"); eauto.
    - exfalso. apply Hρnotmonostatic. eauto.
    - exfalso. apply Hρnotuninitialized. eauto.
  Qed.

  Lemma region_close_next
        (W : WORLD)
        (φ : WORLD * Word → iProp Σ)
        `{forall Wv, Persistent (φ Wv)}
        (ls : list Addr) (l : Addr) (v : Word) (ρ : region_type)
        (Hρnotrevoked : ρ <> Revoked)
        (Hρnotmonostatic : ¬ exists g, ρ = Monostatic g)
        (Hρnotuninitialized : ¬ exists w, ρ = Uninitialized w):
    l ∉ ls
    → sts_state_std l ρ
                    ∗ open_region_many (l :: ls) W
                    ∗ l ↦ₐ v ∗ monotonicity_guarantees_region ρ l v φ ∗ ▷ φ (W, v) ∗ rel l φ -∗
                    open_region_many ls W.
  Proof.
    unfold monotonicity_guarantees_region.
    intros. iIntros "[A [B [C [D [E F]]]]]".
    destruct ρ; try congruence.
    - iApply (region_close_next_monotemp with "[A B C D E F]"); eauto; iFrame.
    - iApply (region_close_next_perm with "[A B C D E F]"); eauto; iFrame.
    - exfalso. apply Hρnotmonostatic. eauto.
    - exfalso. apply Hρnotuninitialized. eauto.
  Qed.

End heap.

Notation "<s[ a := ρ ]s> W" := (std_update W a ρ) (at level 10, format "<s[ a := ρ ]s> W").
Notation "<l[ a := ρ , r ]l> W" := (loc_update W a ρ r.1 r.2.1 r.2.2) (at level 10, format "<l[ a := ρ , r ]l> W").

