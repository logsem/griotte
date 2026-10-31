From iris.base_logic.lib Require Import ghost_map saved_prop.
From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra.
From griotte Require Import region_keys resources heap_region.
From griotte Require Export world_std_sts world_ghost_resources world_std_revocation.

(** * Owned region maps

    The region maps of a compartment, over Iris [ghost_map]: a key names a
    saved predicate and a permission. The map owns the body of every key
    that is not open.
    - [rmap γ M body O] is the generic map, with the open keys [O].
    - [world_interp_g_open C O] is the map of [C]'s Permanent regions. Its
      predicates and bodies mention no world.
    - [world_interp_l_open t W C O] is the map of [C]'s Temporary and
      Revoked regions for thread [t], read off the local world [W]: a
      Temporary key owns its body, a Revoked key owns nothing.

    A heap key [LHeap a ι] holds its body or a tombstone [ι ⊒ AQuar]: once
    [ι] is quarantined, its keys close without their cells. *)

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

(** ** The two maps of a compartment *)

Section region_maps.
  Context {Σ : gFunctors} {Cname : CmptNameG}
    `{!allocRegistryG Σ, !gen_heapGS Addr LWord Σ}
    {stsg : STSG Σ} {relg : relGS Σ}.
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Implicit Types t : Thread.

  Definition rel_g_def C k p (φ : CmptName * LWord → iProp Σ) : iProp Σ :=
    rmap_rel (γrel_g C) k p φ.
  #[local] Definition rel_g_aux : seal (@rel_g_def). Proof. by eexists. Qed.
  Definition rel_g := rel_g_aux.(unseal).
  #[local] Definition rel_g_unseal : @rel_g = @rel_g_def := rel_g_aux.(seal_eq).

  (** The thread is explicit: a predicate of one thread can name another
      thread's regions. *)
  Definition rel_l_def t C k p (φ : WORLD * CmptName * LWord → iProp Σ) : iProp Σ :=
    rmap_rel (γrel_l t C) k p φ.
  #[local] Definition rel_l_aux : seal (@rel_l_def). Proof. by eexists. Qed.
  Definition rel_l := rel_l_aux.(unseal).
  #[local] Definition rel_l_unseal : @rel_l = @rel_l_def := rel_l_aux.(seal_eq).

  (* Leibniz, so that [rewrite] also reaches the hypotheses of a goal. *)
  Lemma rel_g_eq C k p φ : rel_g C k p φ = rmap_rel (γrel_g C) k p φ.
  Proof. by rewrite rel_g_unseal. Qed.
  Lemma rel_l_eq t C k p φ : rel_l t C k p φ = rmap_rel (γrel_l t C) k p φ.
  Proof. by rewrite rel_l_unseal. Qed.

  #[global] Instance rel_g_persistent C k p φ : Persistent (rel_g C k p φ).
  Proof. rewrite rel_g_unseal. apply _. Qed.
  #[global] Instance rel_l_persistent t C k p φ : Persistent (rel_l t C k p φ).
  Proof. rewrite rel_l_unseal. apply _. Qed.

  Lemma rel_g_agree C k p1 p2 φ1 φ2 :
    rel_g C k p1 φ1 -∗ rel_g C k p2 φ2 -∗ ⌜p1 = p2⌝ ∗ (∀ x, ▷ (φ1 x ≡ φ2 x)).
  Proof.
    rewrite !rel_g_eq. iIntros "(%γ1 & H1 & S1) (%γ2 & H2 & S2)".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %[= <- <-].
    iSplit; first done. iIntros (x). iApply (saved_pred_agree with "S1 S2").
  Qed.

  Lemma rel_l_agree t C k p1 p2 φ1 φ2 :
    rel_l t C k p1 φ1 -∗ rel_l t C k p2 φ2 -∗ ⌜p1 = p2⌝ ∗ (∀ x, ▷ (φ1 x ≡ φ2 x)).
  Proof.
    rewrite !rel_l_eq. iIntros "(%γ1 & H1 & S1) (%γ2 & H2 & S2)".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %[= <- <-].
    iSplit; first done. iIntros (x). iApply (saved_pred_agree with "S1 S2").
  Qed.

  (** A Permanent body mentions no world. *)
  Definition body_g C (k : LAddr) (p : Perm) (φ : CmptName * LWord → iProp Σ) : iProp Σ :=
    heap_key_resource k (∃ v, ⌜isO p = false⌝ ∗ k ↦ₖ v ∗ ▷ φ (C, v)).

  (** The cell of a Temporary key. *)
  Definition temp_body (k : LAddr) (v : LWord) : iProp Σ := k ↦ₖ v.

  (** Every Temporary key carries public monotonicity: the only private
      steps with Temporary keys present are revocations, which take every
      Temporary body out. *)
  Definition temp_res W C (k : LAddr) (p : Perm) (φ : WORLD * CmptName * LWord → iProp Σ) : iProp Σ :=
    heap_key_resource k
      (∃ v, ⌜isO p = false⌝ ∗ temp_body k v ∗ future_pub_mono C φ v ∗ ▷ φ (W, C, v)).

  (** A local body is read off the world: no state ghost. *)
  Definition body_l W C (k : LAddr) (p : Perm) (φ : WORLD * CmptName * LWord → iProp Σ) : iProp Σ :=
    match std W !! k with
    | Some Temporary => temp_res W C k p φ
    | _ => emp
    end.

  Definition wig_M C (M : gmap LAddr (gname * Perm)) (O : gset LAddr) : iProp Σ :=
    rmap (γrel_g C) M (body_g C) O.
  Definition world_interp_g_open C (O : gset LAddr) : iProp Σ := ∃ M, wig_M C M O.

  Definition wil_M t W C (M : gmap LAddr (gname * Perm)) (O : gset LAddr) : iProp Σ :=
    "%Hdom" ∷ ⌜dom (std W) = dom M⌝ ∗
    "Hm" ∷ rmap (γrel_l t C) M (body_l W C) O ∗
    "Hloc" ∷ sts_full_world (th:=t) W C.
  Definition world_interp_l_open t W C (O : gset LAddr) : iProp Σ := ∃ M, wil_M t W C M O.

  (** ** Bodies *)

  Lemma temp_res_mono_pub W W' C k p φ :
    related_sts_pub_world W W' → temp_res W C k p φ -∗ temp_res W' C k p φ.
  Proof.
    iIntros (Hp). iApply heap_key_resource_mono. iIntros "(%v & %HO & Hv & #Hm & Hφ)".
    iExists v. iFrame "Hv Hm %". iNext. iApply ("Hm" with "[//] Hφ").
  Qed.

  Lemma body_l_mono_pub W W' C k p φ :
    related_sts_pub_world W W' → (std W' !! k = Some Temporary → std W !! k = Some Temporary) →
    body_l W C k p φ -∗ body_l W' C k p φ.
  Proof.
    iIntros (Hp Hk) "H". rewrite /body_l.
    destruct (std W !! k) as [ [] | ] eqn:HW.
    - rewrite (related_pub_Temporary _ _ _ Hp HW). by iApply (temp_res_mono_pub with "H").
    - destruct (std W' !! k) as [ [] | ]; [|done..]. by specialize (Hk eq_refl).
    - destruct (std W' !! k) as [ [] | ]; [|done..]. by specialize (Hk eq_refl).
  Qed.

  (** ** The map of Permanent regions *)

  Lemma g_open C O k p φ :
    k ∉ O →
    world_interp_g_open C O -∗ rel_g C k p φ -∗
    world_interp_g_open C ({[k]} ∪ O) ∗
    ∃ φ', ⌜∀ x, Persistent (φ' x)⌝ ∗ rel_g C k p φ' ∗ body_g C k p φ' ∗ ▷ (∀ x, φ x ≡ φ' x).
  Proof.
    iIntros (Hk) "(%M & Hm) Hr". rewrite /wig_M rel_g_eq.
    iDestruct (rmap_open with "Hm Hr") as "[Hm (%φ' & %Hp & Hr' & Hb & Heq)]"; [done|].
    iSplitL "Hm"; [by iExists M|]. iExists φ'. rewrite rel_g_eq. by iFrame.
  Qed.

  (** The same, in the shape of today's region opening: the body for the
      client's predicate, its content one later away. *)
  Lemma g_open_transport C O k p φ :
    k ∉ O →
    world_interp_g_open C O -∗ rel_g C k p φ -∗
    world_interp_g_open C ({[k]} ∪ O) ∗ body_g C k p φ.
  Proof.
    iIntros (Hk) "Hw Hr".
    iDestruct (g_open with "Hw Hr") as "[$ (%φ' & _ & _ & Hb & #Heq)]"; [done|].
    iApply (heap_key_resource_mono with "[] Hb"). iIntros "(%v & %HO & Hv & Hφ)".
    iExists v. iFrame "Hv %". iNext. iRewrite ("Heq" $! (C, v)). iExact "Hφ".
  Qed.

  Lemma g_close C O k p φ :
    k ∉ O → (∀ x, Persistent (φ x)) →
    world_interp_g_open C ({[k]} ∪ O) -∗ rel_g C k p φ -∗ body_g C k p φ -∗
    world_interp_g_open C O.
  Proof.
    iIntros (Hk Hp) "(%M & Hm) Hr Hb". rewrite rel_g_eq. iExists M.
    iApply (rmap_close with "Hm Hr Hb"); done.
  Qed.

  (** ** The local map *)

  Lemma l_open t W C O k p φ :
    k ∉ O → std W !! k = Some Temporary →
    world_interp_l_open t W C O -∗ rel_l t C k p φ -∗
    world_interp_l_open t W C ({[k]} ∪ O) ∗
    ∃ φ', ⌜∀ x, Persistent (φ' x)⌝ ∗ rel_l t C k p φ' ∗ temp_res W C k p φ' ∗
      ▷ (∀ x, φ x ≡ φ' x).
  Proof.
    iIntros (Hk HT) "(%M & Hw) Hr". iNamed "Hw". rewrite rel_l_eq.
    iDestruct (rmap_open with "Hm Hr") as "[Hm (%φ' & %Hp & Hr' & Hb & Heq)]"; [done|].
    iSplitL "Hm Hloc"; [iExists M; rewrite /wil_M; by iFrame "∗%"|].
    iExists φ'. rewrite rel_l_eq /body_l HT. by iFrame.
  Qed.

  (** The same, in the shape of today's region opening. *)
  Lemma l_open_transport t W C O k p φ :
    k ∉ O → std W !! k = Some Temporary →
    world_interp_l_open t W C O -∗ rel_l t C k p φ -∗
    world_interp_l_open t W C ({[k]} ∪ O) ∗
    heap_key_resource k
      (∃ v, ⌜isO p = false⌝ ∗ temp_body k v ∗ ▷ future_pub_mono C φ v ∗ ▷ φ (W, C, v)).
  Proof.
    iIntros (Hk HT) "Hw Hr".
    iDestruct (l_open with "Hw Hr") as "[$ (%φ' & _ & _ & Hb & #Heq)]"; [done|done|].
    iApply (heap_key_resource_mono with "[] Hb"). iIntros "(%v & %HO & Hv & #Hm & Hφ)".
    iExists v. iFrame "Hv %". iSplitR.
    - iNext. rewrite /future_pub_mono. iIntros "!>" (W1 W2 Hp) "H".
      iRewrite ("Heq" $! (W2, C, v)). iRewrite ("Heq" $! (W1, C, v)) in "H".
      iApply ("Hm" with "[//] H").
    - iNext. iRewrite ("Heq" $! (W, C, v)). iExact "Hφ".
  Qed.

  Lemma l_close t W C O k p φ :
    k ∉ O → std W !! k = Some Temporary → (∀ x, Persistent (φ x)) →
    world_interp_l_open t W C ({[k]} ∪ O) -∗ rel_l t C k p φ -∗ temp_res W C k p φ -∗
    world_interp_l_open t W C O.
  Proof.
    iIntros (Hk HT Hp) "(%M & Hw) Hr Hb". iNamed "Hw". rewrite rel_l_eq.
    iExists M. rewrite /wil_M. iFrame "Hloc %".
    iApply (rmap_close _ _ _ _ k p φ Hk Hp with "Hm Hr [Hb]"). by rewrite /body_l HT.
  Qed.

  (** A public world step of the local map: the closed Temporary bodies move
      by their [future_pub_mono]; a closed key Temporary at [W'] was
      Temporary at [W]. *)
  Lemma rmap_next t W W' C M O :
    related_sts_pub_world W W' →
    (∀ k, k ∉ O → std W' !! k = Some Temporary → std W !! k = Some Temporary) →
    rmap (γrel_l t C) M (body_l W C) O -∗ rmap (γrel_l t C) M (body_l W' C) O.
  Proof.
    iIntros (Hp HT) "Hm".
    iDestruct (rmap_transform _ M _ (body_l W' C) O O (λ _, emp)%I (λ _, emp)%I
      with "[] [] Hm") as "[$ _]".
    { iApply big_sepM_intro. by iIntros "!>" (???). }
    iIntros "!>" (k γp Hk) "_ _ Hb". iSplitL; [|done].
    case_decide as HkO; [done|].
    iDestruct "Hb" as (φ) "(%Hpers & #Hsp & Hb)". iExists φ. iFrame "#%".
    iApply (body_l_mono_pub with "Hb"); [done|]. by apply HT.
  Qed.

  (** The same on the local part, for a step that keeps the domain and the
      custom STS. *)
  Lemma l_next t W W' C O :
    related_sts_pub_world W W' → dom (std W') = dom (std W) →
    loc W' = loc W → wrel W' = wrel W →
    (∀ k, k ∉ O → std W' !! k = Some Temporary → std W !! k = Some Temporary) →
    world_interp_l_open t W C O -∗ world_interp_l_open t W' C O.
  Proof.
    iIntros (Hp Hd Hl Hr HT) "(%M & Hw)". iNamed "Hw".
    iDestruct (rmap_next with "Hm") as "Hm"; [done|done|].
    iExists M. rewrite /wil_M /sts_full_world Hl Hr Hd. by iFrame "∗%".
  Qed.

  (** ** The custom STS of a thread *)

  (** A private step of the custom STS, under [revoke_condition]: no body
      is Temporary, so none needs private monotonicity. *)
  Lemma l_update_loc_priv {D} `{Countable D} t W C O i (d d' : D) :
    revoke_condition W →
    world_interp_l_open t W C O -∗ sts_state_loc (th:=t) C i d ==∗
    world_interp_l_open t (<l[i := d']l> W) C O ∗ sts_state_loc (th:=t) C i d'.
  Proof.
    iIntros (Hrc) "(%M & Hw) Hf". iNamed "Hw".
    iMod (sts_update_loc with "Hloc Hf") as "[Hloc $]". iModIntro.
    iExists M. rewrite /wil_M /=. iFrame "Hloc". iSplit; [done|].
    iDestruct (rmap_transform _ M _ (body_l (<l[i := d']l> W) C) O O
      (λ _, emp)%I (λ _, emp)%I with "[] [] Hm") as "[$ _]".
    { iApply big_sepM_intro. by iIntros "!>" (???). }
    iIntros "!>" (k γp Hk) "_ _ Hb". iSplitL; [|done]. case_decide; [done|].
    iDestruct "Hb" as (φ) "(%Hp & #Hsp & Hb)". iExists φ. iSplit; [done|]. iFrame "Hsp".
    rewrite /body_l /=. specialize (Hrc k). by destruct (std W !! k) as [ [] | ].
  Qed.

  (** ** Revocation and restoration, with keys open *)

  Definition RevokedRes1 t W C (k : LAddr) : iProp Σ :=
    ∃ p φ, ⌜∀ x, Persistent (φ x)⌝ ∗ rel_l t C k p φ ∗ temp_res W C k p φ.
  Definition RevokedRes t W C (S : gset LAddr) : iProp Σ :=
    [∗ set] k ∈ S, RevokedRes1 t W C k.

  Lemma RevokedRes_mono_pub t W W' C S :
    related_sts_pub_world W W' → RevokedRes t W C S -∗ RevokedRes t W' C S.
  Proof.
    iIntros (Hp) "HR". iApply (big_sepS_mono with "HR").
    iIntros (k _) "(%p & %φ & %Hpers & Hr & Hres)". iExists p, φ. iFrame "Hr %".
    by iApply temp_res_mono_pub.
  Qed.

  (** Revocation: every Temporary body that is not open comes out with its
      [rel_l]; the open ones stay with their holder. *)
  Lemma l_revoke t W C O S :
    extract_T W O S →
    world_interp_l_open t W C O -∗
    world_interp_l_open t (revoke W) C O ∗ RevokedRes t W C S.
  Proof.
    iIntros (HS) "(%M & Hw)". iNamed "Hw".
    assert (S ⊆ dom M) as HSM.
    { intros k [HT _]%HS. rewrite -Hdom. by apply elem_of_dom_std_2 in HT. }
    iDestruct (rmap_transform _ M _ (body_l (revoke W) C) O O (λ _, emp)%I
      (λ k, if decide (k ∈ S) then RevokedRes1 t W C k else emp)%I with "[] [] Hm")
      as "[Hm HX]".
    { iApply big_sepM_intro. by iIntros "!>" (???). }
    { iIntros "!>" (k [γ1 p1] Hk) "#Hel _ Hb". case_decide as HkO.
      - rewrite decide_False; [done|]. intros [_ ?]%HS. done.
      - iDestruct "Hb" as (φ) "(%Hp & #Hsp & Hb)". simpl.
        iSplitR "Hb".
        { iExists φ. iFrame "#%". rewrite /body_l revoke_lookup.
          by destruct (std W !! k) as [ [] | ]. }
        case_decide as HkS; [|done].
        destruct (HS k) as [ [HT _] _]; [done|].
        iExists p1, φ. iSplit; [done|]. rewrite rel_l_eq.
        iSplitR; [iExists γ1; by iFrame "#"|].
        by rewrite /body_l HT. }
    iSplitR "HX".
    - iExists M. rewrite /wil_M. iFrame "Hm Hloc". iPureIntro.
      by rewrite dom_revoke.
    - by rewrite sepM_to_sepS'.
  Qed.

  (** Restoring [S] with keys open: the restored keys that are not open take
      fresh bodies, at the later world [close_set S W]; the other Temporary
      bodies move by their [future_pub_mono]. *)
  Lemma l_restore_open t W C O S :
    S ⊆ dom (std W) →
    world_interp_l_open t W C O -∗ RevokedRes t (close_set S W) C (S ∖ O) -∗
    world_interp_l_open t (close_set S W) C O.
  Proof.
    iIntros (HS) "(%M & Hw)". iNamed "Hw".
    rewrite /RevokedRes -(sepM_to_sepS' M); [|rewrite -Hdom; set_solver].
    iIntros "HR".
    iDestruct (rmap_transform _ M _ (body_l (close_set S W) C) O O
      (λ k, if decide (k ∈ S ∖ O) then RevokedRes1 t (close_set S W) C k else emp)%I
      (λ _, emp)%I with "HR [] Hm") as "[Hm _]".
    { iIntros "!>" (k [γ1 p1] Hk) "#Hel HY Hb". iSplitL; [|done].
      destruct (decide (k ∈ O)) as [HkO|HkO]; [by iClear "HY Hb"|]. simpl.
      destruct (decide (k ∈ S ∖ O)) as [HkS'|HkS'].
      - iDestruct "HY" as (p φ) "(%Hp & Hr & Hres)". rewrite rel_l_eq.
        iDestruct "Hr" as (γ2) "[Hel2 Hsp]".
        iDestruct (ghost_map_elem_agree with "Hel Hel2") as %[= <- <-].
        iExists φ. iFrame "%#". rewrite /body_l close_set_Temporary //; [|set_solver..].
        iClear "Hb". iFrame.
      - iDestruct "Hb" as (φ) "(%Hp & #Hsp & Hb)". iExists φ. iFrame "%#".
        iApply (body_l_mono_pub with "Hb"); [apply related_pub_close_set|].
        rewrite close_set_not_elem; [done|set_solver]. }
    iExists M. rewrite /wil_M. iFrame "Hm Hloc". iPureIntro.
    by rewrite dom_close_set.
  Qed.

  (** Today's restore of a call's return: the bodies were taken at an
      earlier world [Wsrc] (the caller's frame stays closed during the
      callee) and the restored world is a public future of it. *)
  Lemma l_restore_from t Wsrc Wcur C O S :
    S ⊆ dom (std Wcur) →
    related_sts_pub_world Wsrc (close_set S Wcur) →
    world_interp_l_open t Wcur C O -∗ RevokedRes t Wsrc C (S ∖ O) -∗
    world_interp_l_open t (close_set S Wcur) C O.
  Proof.
    iIntros (HS Hpub) "Hw HR".
    iDestruct (RevokedRes_mono_pub with "HR") as "HR"; [exact Hpub|].
    iApply (l_restore_open with "Hw HR"). exact HS.
  Qed.

  (** ** Separation *)

  (** A key whose body would conflict with an exclusive [X] is not
      Temporary. *)
  Lemma l_excl_not_T t W C O k p φ (X : iProp Σ) :
    k ∉ O → std W !! k = Some Temporary →
    □ (∀ v, temp_body k v -∗ X -∗ False) -∗
    □ (∀ a ι, ⌜k = LHeap a ι⌝ → ι ⊒ AQuar -∗ X -∗ False) -∗
    world_interp_l_open t W C O -∗ rel_l t C k p φ -∗ X -∗ False.
  Proof.
    iIntros (Hk HT) "#Hc #Ht Hw Hr HX".
    iDestruct (l_open with "Hw Hr") as "[_ (%φ' & _ & _ & Hb & _)]"; [done|done|].
    rewrite /temp_res. destruct k as [a|a ι]; simpl.
    - iDestruct "Hb" as (v) "(_ & Hv & _)". iApply ("Hc" with "Hv HX").
    - iDestruct "Hb" as "[(%v & _ & Hv & _)|Hq]"; [iApply ("Hc" with "Hv HX")|].
      by iApply ("Ht" with "[//] Hq HX").
  Qed.

  (** ** Tombstones *)

  Definition obj_keys (ι : AId) (b e : Addr) : gset LAddr :=
    set_map (λ a, LHeap a ι) (list_to_set (finz.seq_between b e) : gset Addr).

  Lemma obj_keys_heap ι b e k : k ∈ obj_keys ι b e → ∃ a, k = LHeap a ι.
  Proof. intros (a & -> & _)%elem_of_map. eauto. Qed.

  (** From one persistent [ι ⊒ AQuar], every opened key of [ι] closes with
      the tombstone, in either map. *)
  Lemma g_close_all_tomb C M O S ι :
    S ## O → (∀ k, k ∈ S → ∃ a, k = LHeap a ι) →
    ι ⊒ AQuar -∗
    ([∗ set] k ∈ S, ∃ p φ, ⌜∀ x, Persistent (φ x)⌝ ∗ rel_g C k p φ) -∗
    wig_M C M (S ∪ O) -∗ wig_M C M O.
  Proof.
    iIntros (HSO HH) "#Hq HS Hm".
    iApply (rmap_close_all with "[] [HS] Hm"); [done| |].
    - iIntros "!>" (k p φ Hk). destruct (HH k Hk) as [a ->].
      rewrite /body_g /heap_key_resource /=. by iRight.
    - iApply (big_sepS_mono with "HS"). iIntros (k _) "(%p & %φ & %Hp & Hr)".
      iExists p, φ. rewrite rel_g_eq. iFrame "Hr %".
  Qed.

  Lemma l_close_all_tomb t W C M O S ι :
    S ## O → (∀ k, k ∈ S → ∃ a, k = LHeap a ι) →
    ι ⊒ AQuar -∗
    ([∗ set] k ∈ S, ∃ p φ, ⌜∀ x, Persistent (φ x)⌝ ∗ rel_l t C k p φ) -∗
    wil_M t W C M (S ∪ O) -∗ wil_M t W C M O.
  Proof.
    iIntros (HSO HH) "#Hq HS Hw". iNamed "Hw".
    iDestruct (rmap_close_all with "[] [HS] Hm") as "Hm"; [done| | |].
    - iIntros "!>" (k p φ Hk). destruct (HH k Hk) as [a ->]. rewrite /body_l.
      destruct (std W !! LHeap a ι) as [ [] | ];
        [rewrite /temp_res /heap_key_resource /=; by iRight|done..].
    - iApply (big_sepS_mono with "HS"). iIntros (k _) "(%p & %φ & %Hp & Hr)".
      iExists p, φ. rewrite rel_l_eq. iFrame "Hr %".
    - rewrite /wil_M. by iFrame "∗%".
  Qed.

  (** Every key of a live object [ι] whose cells are held is open in the
      map of Permanent regions: a closed one would hold a cell, or a
      tombstone, which the cells' live shares refute. *)
  Lemma no_other_live_entry_g C M O ι b e :
    alloc_obj ι b e -∗ ([∗ set] k ∈ obj_keys ι b e, ∃ v, k ↦ₖ v) -∗ wig_M C M O -∗
    ⌜∀ a, LHeap a ι ∈ dom M → LHeap a ι ∈ O⌝.
  Proof.
    iIntros "#Hobj Hc Hm". iIntros (a [γp Ha]%elem_of_dom).
    destruct (decide (LHeap a ι ∈ O)) as [|HO]; [done|]. iExFalso.
    iDestruct "Hm" as "(_ & #Hks & Hb)".
    iDestruct (big_sepM_lookup _ _ (LHeap a ι) with "Hks") as "[_ (%b' & %e' & Hobj' & %Hin)]";
      [exact Ha|].
    iDestruct (alloc_obj_agree with "Hobj Hobj'") as %[<- <-].
    assert (LHeap a ι ∈ obj_keys ι b e) as Hk.
    { apply elem_of_map. exists a. split; [done|].
      apply elem_of_list_to_set, elem_of_finz_seq_between. done. }
    iDestruct (big_sepS_elem_of with "Hc") as (v') "Hv'"; [exact Hk|].
    iDestruct (big_sepM_lookup _ _ (LHeap a ι) with "Hb") as "Hb"; [exact Ha|].
    rewrite decide_False //. iDestruct "Hb" as (φ) "(_ & _ & [(%v & _ & Hv & _)|Hq])".
    - by iApply (heap_pointsto_valid_2 with "Hv Hv'").
    - by iApply (heap_pointsto_quar_false with "Hv' Hq").
  Qed.

  Lemma no_other_live_entry_l t W C M O ι b e :
    alloc_obj ι b e -∗ ([∗ set] k ∈ obj_keys ι b e, ∃ v, k ↦ₖ v) -∗ wil_M t W C M O -∗
    ⌜∀ a, LHeap a ι ∈ dom M → LHeap a ι ∈ O ∨ std W !! LHeap a ι ≠ Some Temporary⌝.
  Proof.
    iIntros "#Hobj Hc Hw". iNamed "Hw". iIntros (a [γp Ha]%elem_of_dom).
    destruct (decide (LHeap a ι ∈ O)) as [|HO]; [by iLeft|].
    destruct (decide (std W !! LHeap a ι = Some Temporary)) as [HT|HT]; [|by iRight].
    iExFalso.
    iDestruct "Hm" as "(_ & #Hks & Hb)".
    iDestruct (big_sepM_lookup _ _ (LHeap a ι) with "Hks") as "[_ (%b' & %e' & Hobj' & %Hin)]";
      [exact Ha|].
    iDestruct (alloc_obj_agree with "Hobj Hobj'") as %[<- <-].
    assert (LHeap a ι ∈ obj_keys ι b e) as Hk.
    { apply elem_of_map. exists a. split; [done|].
      apply elem_of_list_to_set, elem_of_finz_seq_between. done. }
    iDestruct (big_sepS_elem_of with "Hc") as (v') "Hv'"; [exact Hk|].
    iDestruct (big_sepM_lookup _ _ (LHeap a ι) with "Hb") as "Hb"; [exact Ha|].
    rewrite decide_False //. iDestruct "Hb" as (φ) "(_ & _ & Hb)". rewrite /body_l HT.
    iDestruct "Hb" as "[(%v & _ & Hv & _)|Hq]".
    - by iApply (heap_pointsto_valid_2 with "Hv Hv'").
    - by iApply (heap_pointsto_quar_false with "Hv' Hq").
  Qed.

  (** Case split over a set of bodies, each holding [P k] or the persistent
      [Q]. *)
  Lemma sepS_cases (S : gset LAddr) (E P : LAddr → iProp Σ) (Q : iProp Σ) `{!Persistent Q} :
    (∀ k, k ∈ S → E k ⊢ P k ∨ (Q ∗ E k)) → (∀ k, k ∈ S → P k ⊢ E k) →
    ([∗ set] k ∈ S, E k) ⊢ ([∗ set] k ∈ S, P k) ∨ (Q ∗ [∗ set] k ∈ S, E k).
  Proof.
    induction S as [|x S Hx IH] using set_ind_L; intros HE HP.
    - rewrite !big_sepS_empty. iIntros "_". by iLeft.
    - rewrite !big_sepS_insert //. iIntros "[Ex ES]".
      iDestruct (HE x ltac:(set_solver) with "Ex") as "[Px|[#HQ Ex] ]".
      + iDestruct (IH with "ES") as "[PS|[#HQ ES] ]".
        { intros k Hk. apply HE. set_solver. }
        { intros k Hk. apply HP. set_solver. }
        * iLeft. iFrame.
        * iRight. iFrame "HQ ES". iApply (HP x ltac:(set_solver) with "Px").
      + iRight. iFrame "HQ Ex ES".
  Qed.

  #[local] Definition gentry C (M : gmap LAddr (gname * Perm)) (k : LAddr) : iProp Σ :=
    ∃ γp, ⌜M !! k = Some γp⌝ ∗ rentry (body_g C) k γp.
  #[local] Definition lentry W C (M : gmap LAddr (gname * Perm)) (k : LAddr) : iProp Σ :=
    ∃ γp, ⌜M !! k = Some γp⌝ ∗ rentry (body_l W C) k γp.
  #[local] Definition keep {A} `{!savedPredG Σ A} (M : gmap LAddr (gname * Perm))
      (k : LAddr) : iProp Σ :=
    ∃ γp (φ : A → iProp Σ), ⌜M !! k = Some γp⌝ ∗ ⌜∀ x, Persistent (φ x)⌝ ∗
      saved_pred_own γp.1 DfracDiscarded φ.
  #[local] Definition gcell C (M : gmap LAddr (gname * Perm)) (k : LAddr) : iProp Σ :=
    ∃ γp φ, ⌜M !! k = Some γp⌝ ∗ ⌜∀ x, Persistent (φ x)⌝ ∗
      saved_pred_own γp.1 DfracDiscarded φ ∗
      ∃ v, ⌜isO γp.2 = false⌝ ∗ k ↦ₖ v ∗ ▷ φ (C, v).
  #[local] Definition lcell W C (M : gmap LAddr (gname * Perm)) (k : LAddr) : iProp Σ :=
    ∃ γp φ, ⌜M !! k = Some γp⌝ ∗ ⌜∀ x, Persistent (φ x)⌝ ∗
      saved_pred_own γp.1 DfracDiscarded φ ∗
      ∃ v, ⌜isO γp.2 = false⌝ ∗ temp_body k v ∗ future_pub_mono C φ v ∗ ▷ φ (W, C, v).

  (** [free] in the owned maps, with keys open: the keys of [ι] (each in the
      map that holds it, [Sg] in the map of Permanent regions, [Sl] in the
      local map, where they are Temporary) are opened. Stale branch: some
      body is a tombstone, and every key closes again. Live branch: every
      body is a cell; the cells come out, and once [ι ⊒ AQuar] holds every
      opened key closes with the tombstone. *)
  Lemma free_owned C t W Mg Ml Og Ol ι b e (Sg Sl : gset LAddr) :
    Sg ⊆ dom Mg → Sl ⊆ dom Ml → Sg ## Sl → Sg ∪ Sl = obj_keys ι b e →
    Sg ## Og → Sl ## Ol →
    (∀ k, k ∈ Sl → std W !! k = Some Temporary) →
    wig_M C Mg Og -∗ wil_M t W C Ml Ol -∗
    (ι ⊒ AQuar ∗ wig_M C Mg Og ∗ wil_M t W C Ml Ol) ∨
    (([∗ set] k ∈ obj_keys ι b e, ∃ v, k ↦ₖ v) ∗
     wig_M C Mg (Sg ∪ Og) ∗ wil_M t W C Ml (Sl ∪ Ol) ∗
     (ι ⊒ AQuar -∗ wig_M C Mg (Sg ∪ Og) -∗ wil_M t W C Ml (Sl ∪ Ol) -∗
      wig_M C Mg Og ∗ wil_M t W C Ml Ol)).
  Proof.
    iIntros (HSg HSl Hdisj Hobj HgO HlO HT) "Hg Hl". iNamed "Hl".
    assert (∀ k, k ∈ Sg → ∃ a, k = LHeap a ι) as HHg.
    { intros k Hk. apply (obj_keys_heap ι b e). set_solver. }
    assert (∀ k, k ∈ Sl → ∃ a, k = LHeap a ι) as HHl.
    { intros k Hk. apply (obj_keys_heap ι b e). set_solver. }
    rewrite /wig_M (rmap_split_set _ Mg _ Og Sg HSg HgO).
    rewrite (rmap_split_set _ Ml _ Ol Sl HSl HlO).
    iDestruct "Hg" as "[Hg HEg]". iDestruct "Hm" as "[Hm HEl]".
    iDestruct (sepS_cases Sg (gentry C Mg) (gcell C Mg) (ι ⊒ AQuar) with "HEg")
      as "[HPg|[#Hq HEg] ]".
    { intros k Hk. destruct (HHg k Hk) as [a ->].
      iIntros "(%γp & %HM & %φ & %Hp & #Hsp & [Hc|#Hq])".
      - iLeft. iExists γp, φ. by iFrame "∗#%".
      - iRight. iFrame "Hq". iExists γp. iSplit; [done|]. iExists φ. by iFrame "#%". }
    { intros k Hk. destruct (HHg k Hk) as [a ->].
      iIntros "(%γp & %φ & %HM & %Hp & #Hsp & Hc)". iExists γp. iSplit; [done|].
      iExists φ. iSplit; [done|]. iSplit; [done|]. by iLeft. }
    (* stale, from the map of Permanent regions *)
    2:{ iLeft. iFrame "Hq Hg". iSplitL "HEg"; [by rewrite /gentry|].
        rewrite /wil_M (rmap_split_set _ Ml _ Ol Sl HSl HlO). by iFrame. }
    iDestruct (sepS_cases Sl (lentry W C Ml) (lcell W C Ml) (ι ⊒ AQuar) with "HEl")
      as "[HPl|[#Hq HEl] ]".
    { intros k Hk. destruct (HHl k Hk) as [a ->].
      iIntros "(%γp & %HM & %φ & %Hp & #Hsp & Hb)". rewrite /body_l HT //.
      iDestruct "Hb" as "[Hc|#Hq]".
      - iLeft. iExists γp, φ. iSplit; [done|]. iSplit; [done|]. by iFrame "Hsp".
      - iRight. iFrame "Hq". iExists γp. iSplit; [done|]. iExists φ.
        iSplit; [done|]. iSplit; [done|]. rewrite /body_l HT //. by iRight. }
    { intros k Hk. destruct (HHl k Hk) as [a ->].
      iIntros "(%γp & %φ & %HM & %Hp & #Hsp & Hc)". iExists γp. iSplit; [done|].
      iExists φ. iSplit; [done|]. iSplit; [done|]. rewrite /body_l HT //. by iLeft. }
    (* stale, from the local map *)
    2:{ iLeft. iFrame "Hq Hg". iSplitL "HPg".
        - iApply (big_sepS_impl with "HPg").
          iIntros "!>" (k Hk) "(%γp & %φ & %HM & %Hp & #Hsp & Hc)".
          destruct (HHg k Hk) as [a ->]. iExists γp. iSplit; [done|]. iExists φ.
          iSplit; [done|]. iSplit; [done|]. by iLeft.
        - rewrite /wil_M (rmap_split_set _ Ml _ Ol Sl HSl HlO). iFrame "Hm Hloc".
          iSplit; [done|]. by rewrite /lentry. }
    (* live *)
    iRight.
    iAssert (([∗ set] k ∈ Sg, ∃ v, k ↦ₖ v) ∗ [∗ set] k ∈ Sg, keep (A:=CmptName * LWord) Mg k)%I
      with "[HPg]" as "[HCg #HKg]".
    { rewrite -big_sepS_sep. iApply (big_sepS_mono with "HPg").
      iIntros (k Hk) "(%γp & %φ & %HM & %Hp & #Hsp & %v & _ & Hv & _)".
      iSplitL "Hv"; [by iExists v|]. iExists γp, φ. iSplit; [done|]. by iSplit. }
    iAssert (([∗ set] k ∈ Sl, ∃ v, k ↦ₖ v) ∗
             [∗ set] k ∈ Sl, keep (A:=WORLD * CmptName * LWord) Ml k)%I
      with "[HPl]" as "[HCl #HKl]".
    { rewrite -big_sepS_sep. iApply (big_sepS_mono with "HPl").
      iIntros (k Hk) "(%γp & %φ & %HM & %Hp & #Hsp & %v & _ & Hv & _)".
      iSplitL "Hv"; [by iExists v|]. iExists γp, φ. iSplit; [done|]. by iSplit. }
    iSplitL "HCg HCl". { rewrite -Hobj big_sepS_union //. iFrame. }
    iFrame "Hg". iSplitL "Hm Hloc".
    { rewrite /wil_M. iFrame "Hm Hloc". done. }
    iIntros "#Hq Hg Hl". iDestruct "Hl" as "(_ & Hm & Hloc)". iFrame "Hg".
    iSplitR.
    - iApply (big_sepS_impl with "HKg"). iIntros "!>" (k Hk) "(%γp & %φ & %HM & %Hp & Hsp)".
      destruct (HHg k Hk) as [a ->]. iExists γp. iSplit; [done|]. iExists φ.
      iSplit; [done|]. iFrame "Hsp". by iRight.
    - rewrite /wil_M (rmap_split_set _ Ml _ Ol Sl HSl HlO). iFrame "Hm Hloc".
      iSplit; [done|].
      iApply (big_sepS_impl with "HKl"). iIntros "!>" (k Hk) "(%γp & %φ & %HM & %Hp & Hsp)".
      destruct (HHl k Hk) as [a ->]. iExists γp. iSplit; [done|]. iExists φ.
      iSplit; [done|]. iFrame "Hsp". rewrite /body_l HT //. by iRight.
  Qed.

  (** The full status of a live object from its cells' shares, the client's
      half and the allocator's share; the cells become plain points-tos. *)
  Lemma free_owned_status ι b e :
    alloc_obj ι b e -∗
    ([∗ set] k ∈ obj_keys ι b e, ∃ v, k ↦ₖ v) -∗
    ι ↦st{1/2} ALive -∗ ι ↦st{share (finz.dist b e)} ALive -∗
    ι ↦st{1} ALive ∗
    [∗ set] k ∈ obj_keys ι b e, ∃ v, laddr_addr k ↦ₐ v.
  Proof.
    assert (Inj eq eq (λ a, LHeap a ι)) as Hinj by (intros a1 a2 [= ->]; done).
    iIntros "#Hobj Hc Hhalf Hal".
    rewrite /obj_keys !big_opS_set_map big_sepS_list_to_set; [|apply finz_seq_between_NoDup].
    rewrite big_sepS_list_to_set; [|apply finz_seq_between_NoDup].
    iAssert ([∗ list] a ∈ finz.seq_between b e, a ↦ₐ - ∗ ι ↦st{share (finz.dist b e)} ALive)%I
      with "[Hc]" as "Hc".
    { iApply (big_sepL_impl with "Hc"). iIntros "!>" (i a Ha) "(%v & Hv)".
      iDestruct (heap_pointsto_split with "Hobj Hv") as "[Hv $]". by iExists v. }
    rewrite big_sepL_sep. iDestruct "Hc" as "[$ Hs]".
    rewrite (st_own_split_alloc ι (finz.seq_between b e)) finz_seq_between_length. iFrame.
  Qed.

  (** A Temporary heap key whose object is quarantined while it is open:
      it closes with the tombstone, the revoke extracts it, and the restore
      closes it from the tombstone alone (no cell, no content). *)
  Lemma heap_T_tombstone_cycle t W C O S a ι p φ :
    LHeap a ι ∉ O → (∀ x, Persistent (φ x)) →
    extract_T W O ({[LHeap a ι]} ∪ S) → LHeap a ι ∉ S →
    ι ⊒ AQuar -∗ rel_l t C (LHeap a ι) p φ -∗
    world_interp_l_open t W C ({[LHeap a ι]} ∪ O) -∗
    world_interp_l_open t (close_set {[LHeap a ι]} (revoke W)) C O ∗ RevokedRes t W C S.
  Proof.
    iIntros (HkO Hp HS HkS) "#Hq #Hr Hw".
    destruct (HS (LHeap a ι)) as [ [HT _] _]; [set_solver|].
    iDestruct (l_close _ W _ O (LHeap a ι) p φ HkO HT Hp with "Hw Hr []") as "Hw".
    { rewrite /temp_res /=. by iRight. }
    iDestruct (l_revoke with "Hw") as "[Hw HR]"; [exact HS|].
    rewrite /RevokedRes big_sepS_union; [|set_solver]. iDestruct "HR" as "[_ $]".
    iApply (l_restore_open _ _ _ O {[LHeap a ι]} with "Hw [ ]").
    { rewrite dom_revoke. apply elem_of_dom_std_2 in HT. set_solver. }
    replace ({[LHeap a ι]} ∖ O) with ({[LHeap a ι]} : gset LAddr) by set_solver.
    rewrite /RevokedRes big_sepS_singleton. iExists p, φ. iFrame "Hr %".
    rewrite /temp_res /=. by iRight.
  Qed.

  (** ** The world interpretation of a thread *)

  Context {th : Thread}.

  (** The general form, with the open keys of each part. *)
  Definition world_interp_open_gl W C (Og Ol : gset LAddr) : iProp Σ :=
    world_interp_g_open C Og ∗ world_interp_l_open th W C Ol.

End region_maps.

(** The region predicates: [k ↪ᵍ[C]{p} φ] names a key of the map of
    Permanent regions of [C]; [k ↪ˡ[C]{p} φ] a key of the local map of the
    thread found by typeclass search (in use, the section's thread). A
    statement with two threads in scope writes [rel_l t] explicitly. *)
Notation "k ↪ᵍ[ C ]{ p } φ" := (rel_g C k p φ)
  (at level 20, format "k  ↪ᵍ[ C ]{ p }  φ") : bi_scope.
Notation "k ↪ˡ[ C ]{ p } φ" := (rel_l _ C k p φ)
  (at level 20, format "k  ↪ˡ[ C ]{ p }  φ") : bi_scope.
(** The same with the thread explicit, for statements with several threads
    in scope. *)
Notation "k ↪ˡ[ t , C ]{ p } φ" := (rel_l t C k p φ)
  (at level 20, format "k  ↪ˡ[ t ,  C ]{ p }  φ") : bi_scope.
