From iris.base_logic.lib Require Import ghost_map saved_prop.
From iris.proofmode Require Import proofmode.
From griotte Require Import region_keys resources heap_region.

(** ** The generic map *)

Section rmap.
  Context {Σ : gFunctors} `{!allocRegistryG Σ, !gen_heapGS Addr LWord Σ}
    `{!ghost_mapG Σ LAddr (gname * Perm)}.

  (** A key names a saved predicate: a persistent element of the map. *)
  Definition rmap_rel {A} `{!savedPredG Σ A} (γ : gname) (k : LAddr) (p : Perm)
      (φ : A → iProp Σ) : iProp Σ :=
    ∃ γp, k ↪[γ]□ (γp, p) ∗ saved_pred_own γp DfracDiscarded φ.

  Definition rentry {A} `{!savedPredG Σ A} (body : LAddr → Perm → (A → iProp Σ) → iProp Σ)
      (k : LAddr) (γp : gname * Perm) : iProp Σ :=
    ∃ φ, ⌜∀ x, Persistent (φ x)⌝ ∗ saved_pred_own γp.1 DfracDiscarded φ ∗ body k γp.2 φ.

  (** The map keeps a persistent element per entry beside the authority: a
      key whose body is extracted keeps its [rmap_rel]. *)
  Definition rmap {A} `{!savedPredG Σ A} (γ : gname) (M : gmap LAddr (gname * Perm))
      (body : LAddr → Perm → (A → iProp Σ) → iProp Σ) (O : gset LAddr) : iProp Σ :=
    ghost_map_auth γ 1 M ∗
    ([∗ map] k ↦ γp ∈ M, k ↪[γ]□ γp ∗ heap_key_known k) ∗
    [∗ map] k ↦ γp ∈ M, if decide (k ∈ O) then emp else rentry body k γp.

  #[global] Instance rmap_rel_persistent {A} `{!savedPredG Σ A} γ k p (φ : A → iProp Σ) :
    Persistent (rmap_rel γ k p φ).
  Proof. apply _. Qed.

  Lemma sepM_split_set {B} (M : gmap LAddr B) (S : gset LAddr) (Φ : LAddr → B → iProp Σ) :
    ([∗ map] k ↦ x ∈ M, Φ k x) ⊣⊢
    ([∗ map] k ↦ x ∈ M, if decide (k ∈ S) then Φ k x else emp) ∗
    ([∗ map] k ↦ x ∈ M, if decide (k ∈ S) then emp else Φ k x).
  Proof.
    rewrite -big_sepM_sep. apply big_sepM_proper. intros k x _.
    case_decide; by rewrite ?left_id ?right_id.
  Qed.

  Lemma sepM_to_sepS {B} (M : gmap LAddr B) (S : gset LAddr) (Φ : LAddr → B → iProp Σ) :
    S ⊆ dom M →
    ([∗ map] k ↦ x ∈ M, if decide (k ∈ S) then Φ k x else emp) ⊣⊢
    [∗ set] k ∈ S, ∃ x, ⌜M !! k = Some x⌝ ∗ Φ k x.
  Proof.
    intros HS.
    rewrite (big_sepM_proper _ (λ k _, if decide (k ∈ S) then ∃ x, ⌜M !! k = Some x⌝ ∗ Φ k x else emp)%I).
    2:{ intros k x Hk. case_decide; [|done]. iSplit; [iIntros "H"; iExists x; by iFrame|].
        iIntros "(%x' & %Hk' & H)". rewrite Hk in Hk'. by injection Hk' as ->. }
    rewrite big_sepM_dom -(big_sepS_filter' (λ k, k ∈ S)).
    replace (filter (λ k, k ∈ S) (dom M)) with S; [done|].
    apply set_eq. intros k. rewrite elem_of_filter. set_solver.
  Qed.

  Lemma sepM_to_sepS' {B} (M : gmap LAddr B) (S : gset LAddr) (Φ : LAddr → iProp Σ) :
    S ⊆ dom M →
    ([∗ map] k ↦ _ ∈ M, if decide (k ∈ S) then Φ k else emp) ⊣⊢ [∗ set] k ∈ S, Φ k.
  Proof.
    intros HS. rewrite big_sepM_dom -(big_sepS_filter' (λ k, k ∈ S)).
    replace (filter (λ k, k ∈ S) (dom M)) with S; [done|].
    apply set_eq. intros k. rewrite elem_of_filter. set_solver.
  Qed.

  Lemma rmap_split_set {A} `{!savedPredG Σ A} γ M body (O S : gset LAddr) :
    S ⊆ dom M → S ## O →
    rmap γ M body O ⊣⊢
    rmap γ M body (S ∪ O) ∗ [∗ set] k ∈ S, ∃ γp, ⌜M !! k = Some γp⌝ ∗ rentry body k γp.
  Proof.
    intros HS HSO. rewrite /rmap -!assoc. do 2 f_equiv.
    rewrite (sepM_split_set M S) -sepM_to_sepS // comm. f_equiv.
    all: apply big_sepM_proper; intros k x _; repeat case_decide; try done; exfalso; set_solver.
  Qed.

  (** Opening a key [k ∉ O], with other keys open: the stored predicate [φ']
      with its own [rmap_rel], its body, and its equivalence with the client's. *)
  Lemma rmap_open {A} `{!savedPredG Σ A} γ M body O k p (φ : A → iProp Σ) :
    k ∉ O →
    rmap γ M body O -∗ rmap_rel γ k p φ -∗
    rmap γ M body ({[k]} ∪ O) ∗
    ∃ φ', ⌜∀ x, Persistent (φ' x)⌝ ∗ rmap_rel γ k p φ' ∗ body k p φ' ∗ ▷ (∀ x, φ x ≡ φ' x).
  Proof.
    iIntros (Hk) "Hm #Hr". iDestruct "Hr" as (γp) "[Hel Hsp]".
    iAssert ⌜M !! k = Some (γp, p)⌝%I as %HM.
    { iDestruct "Hm" as "[Ha _]". iApply (ghost_map_lookup with "Ha Hel"). }
    rewrite (rmap_split_set _ _ _ _ {[k]}); [|apply elem_of_dom_2 in HM; set_solver|set_solver].
    iDestruct "Hm" as "[$ Hk]". rewrite big_sepS_singleton.
    iDestruct "Hk" as (γp'') "[%HM'' (%φ' & %Hp & #Hsp' & Hb)]".
    rewrite HM in HM''. injection HM'' as <-. iExists φ'. iFrame "∗%".
    iSplitR; [iExists γp; by iFrame "#"|].
    rewrite bi.later_forall. iIntros (x). iApply (saved_pred_agree with "Hsp Hsp'").
  Qed.

  Lemma rmap_close {A} `{!savedPredG Σ A} γ M body O k p (φ : A → iProp Σ) :
    k ∉ O → (∀ x, Persistent (φ x)) →
    rmap γ M body ({[k]} ∪ O) -∗ rmap_rel γ k p φ -∗ body k p φ -∗ rmap γ M body O.
  Proof.
    iIntros (Hk Hp) "Hm #Hr Hb". iDestruct "Hr" as (γp) "[Hel Hsp]".
    iAssert ⌜M !! k = Some (γp, p)⌝%I as %HM.
    { iDestruct "Hm" as "[Ha _]". iApply (ghost_map_lookup with "Ha Hel"). }
    rewrite (rmap_split_set _ _ _ O {[k]}); [|apply elem_of_dom_2 in HM; set_solver|set_solver].
    iFrame "Hm". rewrite big_sepS_singleton. iExists (γp, p). iSplit; [done|].
    iExists φ. by iFrame "∗#%".
  Qed.

  Lemma rmap_insert {A} `{!savedPredG Σ A} γ M body O k p (φ : A → iProp Σ) :
    k ∉ dom M → k ∉ O → (∀ x, Persistent (φ x)) →
    rmap γ M body O -∗ heap_key_known k -∗ body k p φ ==∗
    ∃ γp, rmap γ (<[k := (γp, p)]> M) body O ∗ rmap_rel γ k p φ.
  Proof.
    iIntros (HkM HkO Hp) "(Ha & Hks & Hb) #Hkn Hbody".
    iMod (saved_pred_alloc φ DfracDiscarded) as (γp) "#Hsp"; [done|].
    iMod (ghost_map_insert_persist k (γp, p) with "Ha") as "[Ha #Hel]"; [by apply not_elem_of_dom|].
    iModIntro. iExists γp. iFrame "Ha". iSplitL; [|iExists γp; by iFrame "#"].
    iSplitL "Hks".
    - iApply big_sepM_insert; [by apply not_elem_of_dom|]. by iFrame "∗#".
    - iApply big_sepM_insert; [by apply not_elem_of_dom|]. rewrite decide_False //.
      iFrame "Hb". iExists φ. by iFrame "#∗%".
  Qed.

  (** A fresh key enters a map open, with no body yet. *)
  Lemma rmap_insert_open {A} `{!savedPredG Σ A} γ M body O k p (φ : A → iProp Σ) :
    k ∉ dom M →
    rmap γ M body O -∗ heap_key_known k ==∗
    ∃ γp, rmap γ (<[k := (γp, p)]> M) body ({[k]} ∪ O) ∗ rmap_rel γ k p φ.
  Proof.
    iIntros (HkM) "(Ha & Hks & Hb) #Hkn".
    iMod (saved_pred_alloc φ DfracDiscarded) as (γp) "#Hsp"; [done|].
    iMod (ghost_map_insert_persist k (γp, p) with "Ha") as "[Ha #Hel]"; [by apply not_elem_of_dom|].
    iModIntro. iExists γp. iFrame "Ha". iSplitL; [|iExists γp; by iFrame "#"].
    iSplitL "Hks".
    - iApply big_sepM_insert; [by apply not_elem_of_dom|]. by iFrame "∗#".
    - iApply big_sepM_insert; [by apply not_elem_of_dom|]. rewrite decide_True; [|set_solver].
      iSplitR; [done|]. iApply (big_sepM_mono with "Hb"). iIntros (k' γp' Hk') "Hb".
      assert (k' ≠ k) by (intros ->; apply HkM; by eapply elem_of_dom_2).
      destruct (decide (k' ∈ O)) as [HO|HO];
        [rewrite decide_True; [done|set_solver]|rewrite decide_False; [done|set_solver] ].
  Qed.

  (** Key-wise rewriting of a map: each entry, given an input [Y k], becomes
      an entry for the new body and open set, plus an output [X k]. *)
  Lemma rmap_transform {A} `{!savedPredG Σ A} γ M body body' O O' (Y X : LAddr → iProp Σ) :
    ([∗ map] k ↦ _ ∈ M, Y k) -∗
    (□ ∀ k γp, ⌜M !! k = Some γp⌝ → k ↪[γ]□ γp -∗ Y k -∗
        (if decide (k ∈ O) then emp else rentry body k γp) -∗
        (if decide (k ∈ O') then emp else rentry body' k γp) ∗ X k) -∗
    rmap γ M body O -∗ rmap γ M body' O' ∗ [∗ map] k ↦ _ ∈ M, X k.
  Proof.
    iIntros "HY #Ht (Ha & #Hks & Hb)". iFrame "Ha Hks". rewrite -big_sepM_sep.
    iDestruct (big_sepM_sep_2 with "HY Hb") as "Hb".
    iApply (big_sepM_impl with "Hb"). iIntros "!>" (k γp Hk) "[HY Hb]".
    iDestruct (big_sepM_lookup with "Hks") as "[Hel _]"; [exact Hk|].
    iApply ("Ht" with "[//] Hel HY Hb").
  Qed.

  (** Closing a set of open keys at once, each with a body that a persistent
      fact provides (in use: a tombstone). *)
  Lemma rmap_close_all {A} `{!savedPredG Σ A} γ M body O (S : gset LAddr) :
    S ## O →
    □ (∀ k p (φ : A → iProp Σ), ⌜k ∈ S⌝ -∗ body k p φ) -∗
    ([∗ set] k ∈ S, ∃ p (φ : A → iProp Σ), ⌜∀ x, Persistent (φ x)⌝ ∗ rmap_rel γ k p φ) -∗
    rmap γ M body (S ∪ O) -∗ rmap γ M body O.
  Proof.
    revert O. induction S as [|k S HkS IH] using set_ind_L; iIntros (O HSO) "#Hb HS Hm".
    - by iEval (rewrite union_empty_l_L) in "Hm".
    - rewrite big_sepS_insert //. iDestruct "HS" as "[(%p & %φ & %Hp & #Hr) HS]".
      iEval (rewrite -union_assoc_L) in "Hm".
      iDestruct (rmap_close _ _ _ (S ∪ O) k p φ with "Hm Hr [Hb]") as "Hm";
        [set_solver| |].
      { iApply "Hb". iPureIntro. set_solver. }
      iApply (IH O with "[] HS Hm"); [set_solver|].
      iIntros "!>" (k' p' φ' Hk'). iApply "Hb". iPureIntro. set_solver.
  Qed.

End rmap.
