From iris.base_logic.lib Require Import ghost_map saved_prop.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From griotte Require Import named_props_extra.
From griotte Require Import region_keys resources heap_region.
From griotte Require Export stdpp_extra griotte_lang sts_ghost region_keys rmap.
From griotte Require Export world_std_sts world_std_revocation.

(** * Owned region maps

    The region maps of a compartment, over Iris [ghost_map]: a key names a
    saved predicate and a permission. The map owns the body of every key
    that is not open.
    - [rmap γ M body O] is the generic map, with the open keys [O].
    - [perm_region_map C O] is the map of [C]'s Permanent regions. Its
      predicates and bodies mention no world.
    - [local_region_map t W C O] is the map of [C]'s Temporary and
      Revoked regions for thread [t], read off the local world [W]: a
      Temporary key owns its body, a Revoked key owns nothing.

    A heap key [LHeap a ι] holds its body or a tombstone [ι ⊒ AQuar]: once
    [ι] is quarantined, its keys close without their cells. *)

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
      relPreG_saved_pred_perm :: savedPredG Σ (CmptName * LWord);
      relPreG_rel :: ghost_mapG Σ LAddr (gname * Perm);
    }.
#[export] Hint Mode relGpreS - - : typeclass_instances.

Class relGS Σ {Cname : CmptNameG} :=
  RelGS {
      relG_rel :: ghost_mapG Σ LAddr (gname * Perm);
      relG_saved_pred :: savedPredG Σ (WorldT * CmptName * LWord);
      relG_saved_pred_perm :: savedPredG Σ (CmptName * LWord);
      (** the map of Permanent regions of a compartment *)
      γrel_perm : CmptName -> gname;
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
        ([∗ set] C ∈ CNames, ghost_map_auth (γrel_perm C) 1 (∅ : gmap LAddr (gname * Perm))) ∗
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

(** ** The two maps of a compartment *)

Section region_maps.
  Context {Σ : gFunctors} {Cname : CmptNameG}
    `{!allocRegistryG Σ, !gen_heapGS Addr LWord Σ}
    {stsg : STSG Σ} {relg : relGS Σ}.
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Implicit Types t : Thread.

  Definition rel_perm_def C k p (φ : CmptName * LWord → iProp Σ) : iProp Σ :=
    rmap_rel (γrel_perm C) k p φ.
  #[local] Definition rel_perm_aux : seal (@rel_perm_def). Proof. by eexists. Qed.
  Definition rel_perm := rel_perm_aux.(unseal).
  #[local] Definition rel_perm_unseal : @rel_perm = @rel_perm_def := rel_perm_aux.(seal_eq).

  (** The thread is explicit: a predicate of one thread can name another
      thread's regions. *)
  Definition rel_l_def t C k p (φ : WORLD * CmptName * LWord → iProp Σ) : iProp Σ :=
    rmap_rel (γrel_l t C) k p φ.
  #[local] Definition rel_l_aux : seal (@rel_l_def). Proof. by eexists. Qed.
  Definition rel_l := rel_l_aux.(unseal).
  #[local] Definition rel_l_unseal : @rel_l = @rel_l_def := rel_l_aux.(seal_eq).

  (* Leibniz, so that [rewrite] also reaches the hypotheses of a goal. *)
  Lemma rel_perm_eq C k p φ : rel_perm C k p φ = rmap_rel (γrel_perm C) k p φ.
  Proof. by rewrite rel_perm_unseal. Qed.
  Lemma rel_l_eq t C k p φ : rel_l t C k p φ = rmap_rel (γrel_l t C) k p φ.
  Proof. by rewrite rel_l_unseal. Qed.

  #[global] Instance rel_perm_persistent C k p φ : Persistent (rel_perm C k p φ).
  Proof. rewrite rel_perm_unseal. apply _. Qed.
  #[global] Instance rel_l_persistent t C k p φ : Persistent (rel_l t C k p φ).
  Proof. rewrite rel_l_unseal. apply _. Qed.

  Lemma rel_perm_agree C k p1 p2 φ1 φ2 :
    rel_perm C k p1 φ1 -∗ rel_perm C k p2 φ2 -∗ ⌜p1 = p2⌝ ∗ (∀ x, ▷ (φ1 x ≡ φ2 x)).
  Proof.
    rewrite !rel_perm_eq. iIntros "(%γ1 & H1 & S1) (%γ2 & H2 & S2)".
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
  Definition body_perm C (k : LAddr) (p : Perm) (φ : CmptName * LWord → iProp Σ) : iProp Σ :=
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

  Definition perm_region_map_M C (M : gmap LAddr (gname * Perm)) (O : gset LAddr) : iProp Σ :=
    rmap (γrel_perm C) M (body_perm C) O.
  Definition perm_region_map C (O : gset LAddr) : iProp Σ := ∃ M, perm_region_map_M C M O.

  Definition local_region_map_M t W C (M : gmap LAddr (gname * Perm)) (O : gset LAddr) : iProp Σ :=
    "%Hdom" ∷ ⌜dom (std W) = dom M⌝ ∗
    "Hm" ∷ rmap (γrel_l t C) M (body_l W C) O ∗
    "Hloc" ∷ sts_full_world (th:=t) W C.
  Definition local_region_map t W C (O : gset LAddr) : iProp Σ := ∃ M, local_region_map_M t W C M O.

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

  Lemma perm_open C O k p φ :
    k ∉ O →
    perm_region_map C O -∗ rel_perm C k p φ -∗
    perm_region_map C ({[k]} ∪ O) ∗
    ∃ φ', ⌜∀ x, Persistent (φ' x)⌝ ∗ rel_perm C k p φ' ∗ body_perm C k p φ' ∗ ▷ (∀ x, φ x ≡ φ' x).
  Proof.
    iIntros (Hk) "(%M & Hm) Hr". rewrite /perm_region_map_M rel_perm_eq.
    iDestruct (rmap_open with "Hm Hr") as "[Hm (%φ' & %Hp & Hr' & Hb & Heq)]"; [done|].
    iSplitL "Hm"; [by iExists M|]. iExists φ'. rewrite rel_perm_eq. by iFrame.
  Qed.

  (** The same, in the shape of today's region opening: the body for the
      client's predicate, its content one later away. *)
  Lemma perm_open_transport C O k p φ :
    k ∉ O →
    perm_region_map C O -∗ rel_perm C k p φ -∗
    perm_region_map C ({[k]} ∪ O) ∗ body_perm C k p φ.
  Proof.
    iIntros (Hk) "Hw Hr".
    iDestruct (perm_open with "Hw Hr") as "[$ (%φ' & _ & _ & Hb & #Heq)]"; [done|].
    iApply (heap_key_resource_mono with "[] Hb"). iIntros "(%v & %HO & Hv & Hφ)".
    iExists v. iFrame "Hv %". iNext. iRewrite ("Heq" $! (C, v)). iExact "Hφ".
  Qed.

  Lemma perm_close C O k p φ :
    k ∉ O → (∀ x, Persistent (φ x)) →
    perm_region_map C ({[k]} ∪ O) -∗ rel_perm C k p φ -∗ body_perm C k p φ -∗
    perm_region_map C O.
  Proof.
    iIntros (Hk Hp) "(%M & Hm) Hr Hb". rewrite rel_perm_eq. iExists M.
    iApply (rmap_close with "Hm Hr Hb"); done.
  Qed.

  (** ** The local map *)

  Lemma l_open t W C O k p φ :
    k ∉ O → std W !! k = Some Temporary →
    local_region_map t W C O -∗ rel_l t C k p φ -∗
    local_region_map t W C ({[k]} ∪ O) ∗
    ∃ φ', ⌜∀ x, Persistent (φ' x)⌝ ∗ rel_l t C k p φ' ∗ temp_res W C k p φ' ∗
      ▷ (∀ x, φ x ≡ φ' x).
  Proof.
    iIntros (Hk HT) "(%M & Hw) Hr". iNamed "Hw". rewrite rel_l_eq.
    iDestruct (rmap_open with "Hm Hr") as "[Hm (%φ' & %Hp & Hr' & Hb & Heq)]"; [done|].
    iSplitL "Hm Hloc"; [iExists M; rewrite /local_region_map_M; by iFrame "∗%"|].
    iExists φ'. rewrite rel_l_eq /body_l HT. by iFrame.
  Qed.

  (** The same, in the shape of today's region opening. *)
  Lemma l_open_transport t W C O k p φ :
    k ∉ O → std W !! k = Some Temporary →
    local_region_map t W C O -∗ rel_l t C k p φ -∗
    local_region_map t W C ({[k]} ∪ O) ∗
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
    local_region_map t W C ({[k]} ∪ O) -∗ rel_l t C k p φ -∗ temp_res W C k p φ -∗
    local_region_map t W C O.
  Proof.
    iIntros (Hk HT Hp) "(%M & Hw) Hr Hb". iNamed "Hw". rewrite rel_l_eq.
    iExists M. rewrite /local_region_map_M. iFrame "Hloc %".
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
    local_region_map t W C O -∗ local_region_map t W' C O.
  Proof.
    iIntros (Hp Hd Hl Hr HT) "(%M & Hw)". iNamed "Hw".
    iDestruct (rmap_next with "Hm") as "Hm"; [done|done|].
    iExists M. rewrite /local_region_map_M /sts_full_world Hl Hr Hd. by iFrame "∗%".
  Qed.

  (** ** The custom STS of a thread *)

  (** A private step of the custom STS, under [revoke_condition]: no body
      is Temporary, so none needs private monotonicity. *)
  Lemma l_update_loc_priv {D} `{Countable D} t W C O i (d d' : D) :
    revoke_condition W →
    local_region_map t W C O -∗ sts_state_loc (th:=t) C i d ==∗
    local_region_map t (<l[i := d']l> W) C O ∗ sts_state_loc (th:=t) C i d'.
  Proof.
    iIntros (Hrc) "(%M & Hw) Hf". iNamed "Hw".
    iMod (sts_update_loc with "Hloc Hf") as "[Hloc $]". iModIntro.
    iExists M. rewrite /local_region_map_M /=. iFrame "Hloc". iSplit; [done|].
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
    local_region_map t W C O -∗
    local_region_map t (revoke W) C O ∗ RevokedRes t W C S.
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
    - iExists M. rewrite /local_region_map_M. iFrame "Hm Hloc". iPureIntro.
      by rewrite dom_revoke.
    - by rewrite sepM_to_sepS'.
  Qed.

  (** Restoring [S] with keys open: the restored keys that are not open take
      fresh bodies, at the later world [close_set S W]; the other Temporary
      bodies move by their [future_pub_mono]. *)
  Lemma l_restore_open t W C O S :
    S ⊆ dom (std W) →
    local_region_map t W C O -∗ RevokedRes t (close_set S W) C (S ∖ O) -∗
    local_region_map t (close_set S W) C O.
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
    iExists M. rewrite /local_region_map_M. iFrame "Hm Hloc". iPureIntro.
    by rewrite dom_close_set.
  Qed.

  (** Today's restore of a call's return: the bodies were taken at an
      earlier world [Wsrc] (the caller's frame stays closed during the
      callee) and the restored world is a public future of it. *)
  Lemma l_restore_from t Wsrc Wcur C O S :
    S ⊆ dom (std Wcur) →
    related_sts_pub_world Wsrc (close_set S Wcur) →
    local_region_map t Wcur C O -∗ RevokedRes t Wsrc C (S ∖ O) -∗
    local_region_map t (close_set S Wcur) C O.
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
    local_region_map t W C O -∗ rel_l t C k p φ -∗ X -∗ False.
  Proof.
    iIntros (Hk HT) "#Hc #Ht Hw Hr HX".
    iDestruct (l_open with "Hw Hr") as "[_ (%φ' & _ & _ & Hb & _)]"; [done|done|].
    rewrite /temp_res. destruct k as [a|a ι]; simpl.
    - iDestruct "Hb" as (v) "(_ & Hv & _)". iApply ("Hc" with "Hv HX").
    - iDestruct "Hb" as "[(%v & _ & Hv & _)|Hq]"; [iApply ("Hc" with "Hv HX")|].
      by iApply ("Ht" with "[//] Hq HX").
  Qed.

  (** ** The world interpretation of a thread *)

  Context {th : Thread}.

  (** The general form, with the open keys of each part. *)
  Definition world_interp_open_gl W C (Og Ol : gset LAddr) : iProp Σ :=
    perm_region_map C Og ∗ local_region_map th W C Ol.

End region_maps.

(** The region predicates: [k ↪ᵖ[C]{p} φ] names a key of the map of
    Permanent regions of [C]; [k ↪ˡ[C]{p} φ] a key of the local map of the
    thread found by typeclass search (in use, the section's thread). A
    statement with two threads in scope writes [rel_l t] explicitly. *)
Notation "k ↪ᵖ[ C ]{ p } φ" := (rel_perm C k p φ)
  (at level 20, format "k  ↪ᵖ[ C ]{ p }  φ") : bi_scope.
Notation "k ↪ˡ[ C ]{ p } φ" := (rel_l _ C k p φ)
  (at level 20, format "k  ↪ˡ[ C ]{ p }  φ") : bi_scope.
(** The same with the thread explicit, for statements with several threads
    in scope. *)
Notation "k ↪ˡ[ t , C ]{ p } φ" := (rel_l t C k p φ)
  (at level 20, format "k  ↪ˡ[ t ,  C ]{ p }  φ") : bi_scope.
