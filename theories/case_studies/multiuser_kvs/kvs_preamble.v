From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import switcher kvs.

Definition kvs_entry : Type := option (Z * Word).
Definition kvs_dom : gset nat := set_seq 0 SIZE_MAP.
Definition kvs_map : Type := gmap nat kvs_entry.

Definition kvs_alloc : Type := gmap Z (gset Z).

(* CMRA for KVS *)
Class kvsG Σ :=
  KvsG {
      kvs_genG :: gen_heapGS nat kvs_entry Σ;
      kvs_alloc_genG :: gen_heapGS Z (gset Z) Σ;
    }.

Definition allocated_keys_auth `{kvsG} ( m : kvs_alloc) : iProp Σ :=
  (gen_heap_interp (L:=Z) (V:= gset Z) m).
Definition allocated_keys_frag `{kvsG} (ku : Z) ( s : gset Z ) : iProp Σ :=
  pointsto (L:=Z) (V:= gset Z) ku (DfracOwn 1) s.

Notation "●(ALLOC) s" := (allocated_keys_auth s)%I (at level 20) : bi_scope.
Notation "◯(ALLOC)[ k ] s" := (allocated_keys_frag k s)%I (at level 20) : bi_scope.

Lemma allocated_keys_valid `{kvsG} (ku : Z) (m : kvs_alloc) (s : gset Z) :
  ●(ALLOC) m -∗ ◯(ALLOC)[ ku ] s -∗ ⌜ m !! ku = Some s  ⌝.
Proof.
  iIntros "Hauth Hfrag".
  by iDestruct (gen_heap_valid with "Hauth Hfrag") as "%Hvalid".
Qed.

Lemma allocated_keys_union `{kvsG} (ku : Z) ( m : kvs_alloc) (s' s'' : gset Z) :
  ●(ALLOC) m -∗ ◯(ALLOC)[ku] s' ==∗ ●(ALLOC) (<[ ku := (s'' ∪ s') ]> m) ∗ ◯(ALLOC)[ku] (s'' ∪ s').
Proof.
  iIntros "Hauth Hfrag".
  by iMod (gen_heap_update m ku _ (s'' ∪ s') with "Hauth Hfrag") as "[$ $]".
Qed.

Lemma allocated_keys_insert `{kvsG} (ku : Z) (kn : Z) ( m : kvs_alloc) (s' : gset Z) :
  ●(ALLOC) m -∗ ◯(ALLOC)[ku] s' ==∗
  ●(ALLOC) (<[ ku := ({[kn]} ∪ s') ]> m) ∗ ◯(ALLOC)[ku] ( {[kn]} ∪ s').
Proof.
  iIntros "Hs Hs'".
  iMod (allocated_keys_union with "Hs Hs'") as "[$ $]" ; last done.
Qed.

Definition kvs_frag_idx_frac `{kvsG} (idx : nat) (k : Z) (w : Word) (q : dfrac) : iProp Σ :=
  (pointsto (L:=nat) (V:=kvs_entry) idx q (Some (k,w))).
Notation "k '⤇(KVS){' q '}[' idx  ']' w" :=
  (kvs_frag_idx_frac idx k w q) (at level 20) : bi_scope.
Notation "k '⤇(KVS){' q '}[' idx  ']' -" :=
  (∃ w, kvs_frag_idx_frac idx k w q)%I (at level 20) : bi_scope.

Notation "idx '⤇(KVS)' 'NONE'" :=
  (pointsto (L:=nat) (V:=kvs_entry) idx (DfracOwn 1) None) (at level 20) : bi_scope.
Notation "k '⤇(KVS)[' idx  ']' w" :=
  (kvs_frag_idx_frac idx k w (DfracOwn 1)) (at level 20) : bi_scope.
Notation "k '⤇(KVS)[' idx  ']' -" :=
  (∃ w, kvs_frag_idx_frac idx k w (DfracOwn 1))%I (at level 20) : bi_scope.

Definition kvs_frag `{kvsG} (k : Z ) (w : Word) : iProp Σ := ∃ idx, k ⤇(KVS)[ idx ] w.
Notation "k '⤇(KVS)' w" := (kvs_frag k w) (at level 20) : bi_scope.
Notation "k '⤇(KVS)' -" := (∃ w, kvs_frag k w)%I (at level 20) : bi_scope.

Notation "●(KVS) m" := (gen_heap_interp (m : kvs_map)) (at level 20) : bi_scope.

Section KVS_preamble.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Definition kvs_keys (m : kvs_map) : list Z :=
    map_fold (
        (fun _ opt_kv acc =>
           match opt_kv with
           | None => acc
           | Some kv => (fst kv)::acc
           end
        )
      )
      []
      m.

  Definition wf_kvs_map (m : kvs_map) : Prop :=
    dom m = kvs_dom ∧ NoDup (kvs_keys m).

  Definition isKVS_entry (a : Addr) (idx : nat) (opt_kw : option (Z * Word)) : iProp Σ :=
    match opt_kw with
    | None =>
        (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx))%a ↦ₐ WInt ASM_NONE ∗
        (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx + 1))%a ↦ₐ - ∗
        (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx + 2))%a ↦ₐ - ∗
        idx ⤇(KVS) NONE
    | Some (k, w) =>
        (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx))%a ↦ₐ WInt ASM_SOME ∗
        (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx + 1))%a ↦ₐ WInt k ∗
        (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx + 2))%a ↦ₐ w
    end.

  Definition kvs_alloc_elem_of (s : kvs_alloc) (ku kn : Z) :=
    (∃ sk, s !! ku = Some sk ∧ kn ∈ sk).

  Local Lemma kvs_alloc_not_elem_of (s : kvs_alloc) (ku kn : Z) :
    ¬ kvs_alloc_elem_of s ku kn ->
    s !! ku = None ∨ ∃ sk, s !! ku = Some sk ∧ kn ∉ sk.
  Proof.
    rewrite /kvs_alloc_elem_of.
    intros H.
    destruct (s !! ku) eqn:H' ;[right|left]; auto.
    exists g.
    destruct (decide (kn ∈ g)); auto.
    exfalso; apply H.
    exists g; split; auto.
  Qed.

  Definition kvs_alloc_insert (s : kvs_alloc) (ku : Z) (ks : gset Z) :=
   <[ku := ks ∪ (default ∅ (s !! ku)) ]> s.

  Definition kvs_alloc_delete (s : kvs_alloc) (ku : Z) (ks : gset Z) :=
   <[ku := (default ∅ (s !! ku)) ∖ ks ]> s.

  Lemma kvs_alloc_insert_lookup_eq s ku ks sk :
    kvs_alloc_insert s ku ks !! ku = Some sk ->
    sk = ks ∪ default ∅ (s !! ku).
  Proof.
    intros H.
    rewrite /kvs_alloc_insert in H; simplify_map_eq.
    done.
  Qed.

  Lemma kvs_alloc_insert_lookup_ne s ku ku' ks sk :
    ku ≠ ku' ->
    kvs_alloc_insert s ku ks !! ku' = Some sk ->
    s !! ku' = Some sk.
  Proof.
    intros Hk H.
    rewrite /kvs_alloc_insert in H; simplify_map_eq.
    done.
  Qed.

  Definition kvs_alloc_synced (m : kvs_map) (s : kvs_alloc) : Prop :=
    ∀ k, wf_kvs_full_key k.1 k.2 ->
         ( kvs_alloc_elem_of s k.1 k.2 ↔ (kvs_full_key k.1 k.2) ∈ kvs_keys m).

  Definition isKVS
    (a : Addr) (m : kvs_map) (s : kvs_alloc) : iProp Σ :=
    ⌜ wf_kvs_map m ⌝ ∗
    ●(KVS) m ∗
    ●(ALLOC) s ∗
    ⌜ kvs_alloc_synced m s ⌝ ∗
    [∗ map] idx ↦ kw ∈ m, isKVS_entry a idx kw.

  Definition isKVS_open
    (a : Addr) (m : kvs_map) (s : kvs_alloc) (open_idx : nat) : iProp Σ :=
    ⌜ wf_kvs_map m ⌝ ∗
    ●(KVS) m ∗
    ●(ALLOC) s ∗
    ⌜ kvs_alloc_synced m s ⌝ ∗
    [∗ map] idx ↦ kw ∈ (delete open_idx m), isKVS_entry a idx kw.

  Lemma wf_kvs_is_Some (m : kvs_map) (idx : nat)  :
    wf_kvs_map m ->
    0 <= idx < SIZE_MAP ->
    is_Some (m !! idx).
  Proof.
    intros [Hkvs_dom _] Hidx.
    apply elem_of_dom.
    rewrite Hkvs_dom /kvs_dom.
    by apply elem_of_set_seq.
  Qed.

  Lemma wf_kvs_indom_idx (m : kvs_map) (idx : nat) :
    idx ∈ dom m ->
    wf_kvs_map m ->
    0 <= idx < SIZE_MAP.
  Proof.
    intros Hm_idx [Hkvs_dom _].
    rewrite Hkvs_dom /kvs_dom in Hm_idx.
    apply elem_of_set_seq in Hm_idx.
    lia.
  Qed.

  Global Instance Permutation_Reflexive {A} : Reflexive (@Permutation A).
  Proof. intros l ; done. Qed.

  Global Instance Permutation_Transitive {A} : Transitive (@Permutation A).
  Proof. intros l1 l2 l3 Hl12 Hl23; eapply Permutation_trans; done. Qed.

  Global Instance Permutation_PreOrder {A} : PreOrder (@Permutation A).
  Proof. split; apply _. Qed.

  Local Instance Proper_get_kvs_key (opt_kv : kvs_entry) :
  Proper (Permutation ==> Permutation)
    (λ acc : list Z, match opt_kv with
                     | Some kv => kv.1 :: acc
                     | None => acc
                     end).
  Proof. intros l1 l2 Hl; destruct opt_kv; auto. Qed.

  Lemma kvs_keys_insert_None idx m :
    m !! idx = None ->
    kvs_keys (<[idx:=None]> m) ≡ₚ kvs_keys m.
  Proof.
    intros Hidx.
    rewrite /kvs_keys.
    setoid_rewrite map_fold_insert; auto; try apply _.
    intros j1 j2 opt_kv1 opt_kv2 l Hk_neq Hj1 Hj2.
    destruct opt_kv1, opt_kv2; auto.
    econstructor.
  Qed.


  Lemma kvs_keys_insert_Some idx k w m :
    m !! idx = None ->
    kvs_keys (<[idx:=Some (k, w)]> m) ≡ₚ (k :: kvs_keys m).
  Proof.
    intros Hidx.
    rewrite /kvs_keys.
    setoid_rewrite map_fold_insert; auto; try apply _.
    intros j1 j2 opt_kv1 opt_kv2 l Hk_neq Hj1 Hj2.
    destruct opt_kv1, opt_kv2; auto.
    econstructor.
  Qed.

  Lemma wf_kvs_neq (m : kvs_map) (idx idx' : nat) (k k' : Z) (w w' : Word) :
    wf_kvs_map m ->
    idx ≠ idx' ->
    m !! idx = Some (Some (k, w)) ->
    m !! idx' = Some (Some (k', w')) ->
    k ≠ k'.
  Proof.
    intros [_ Hkvs_uniqueness] Hidx_ne Hm_idx Hm_idx'.
    rewrite -(insert_id m idx (Some (k, w))) in Hkvs_uniqueness; last done.
    rewrite -insert_delete_eq in Hkvs_uniqueness.
    rewrite kvs_keys_insert_Some in Hkvs_uniqueness; last by simplify_map_eq.
    rewrite -(insert_id (delete idx m) idx' (Some (k', w'))) in Hkvs_uniqueness; last by simplify_map_eq.
    rewrite -insert_delete_eq in Hkvs_uniqueness.
    rewrite kvs_keys_insert_Some in Hkvs_uniqueness; last by simplify_map_eq.
    apply NoDup_cons in Hkvs_uniqueness as [Hk _ ].
    apply not_elem_of_cons in Hk as [ HK _ ].
    done.
  Qed.

  Lemma kvs_keys_empty : kvs_keys ∅ = [].
  Proof. rewrite /kvs_keys map_fold_empty; done. Qed.

  Lemma elem_of_kvs_keys_1 (m : kvs_map) (k : Z) :
    k ∈ kvs_keys m -> (∃ idx w, m !! idx = Some (Some (k, w))).
  Proof.
    move: k.
    induction m using map_ind ; intros k Hk.
    { rewrite kvs_keys_empty in Hk; set_solver+Hk. }
    destruct x as [ [k' w'] |].
    - rewrite kvs_keys_insert_Some in Hk; auto.
      apply elem_of_cons in Hk as [ -> | Hk].
      + exists i, w' ; simplify_map_eq; done.
      + apply IHm in Hk.
        destruct Hk as (idx & w & Hidx).
        exists idx, w.
        assert (i ≠ idx) by (intro; simplify_map_eq;done).
        simplify_map_eq; done.
    - rewrite kvs_keys_insert_None in Hk; auto.
      apply IHm in Hk.
      destruct Hk as (idx & w & Hidx).
      exists idx, w.
      assert (i ≠ idx) by (intro; simplify_map_eq;done).
      simplify_map_eq; done.
  Qed.

  Lemma elem_of_kvs_keys_2 (m : kvs_map) (k : Z) :
    (∃ idx w, m !! idx = Some (Some (k, w))) ->
    k ∈ kvs_keys m.
  Proof.
    intros (idx & w & Hidx).
    rewrite -(insert_id m idx (Some (k, w))); last done.
    rewrite -insert_delete_eq.
    rewrite kvs_keys_insert_Some; last by simplify_map_eq.
    apply elem_of_cons; by left.
  Qed.

  Lemma elem_of_kvs_keys (m : kvs_map) (k : Z) :
    k ∈ kvs_keys m ↔ (∃ idx w, m !! idx = Some (Some (k, w))).
  Proof. split ; [apply elem_of_kvs_keys_1 | apply elem_of_kvs_keys_2]. Qed.

  Lemma NoDup_kvs_keys_update (m : kvs_map) (idx : nat) (k : Z) (w w' : Word) :
    m !! idx = Some (Some (k, w)) ->
    NoDup (kvs_keys m) ->
    NoDup (kvs_keys (<[idx := Some (k, w') ]>m)).
  Proof.
    move: idx k w w'.
    induction m using map_ind; intros idx k w w' Hk Hnodup; first simplify_map_eq.
    destruct (decide (idx = i)); simplify_map_eq.
    - rewrite insert_insert_eq.
      rewrite kvs_keys_insert_Some; auto.
      rewrite kvs_keys_insert_Some in Hnodup; auto.
    - rewrite insert_insert_ne; last done.
      destruct x as [ [k' w''] |].
      + rewrite kvs_keys_insert_Some in Hnodup; auto.
        rewrite kvs_keys_insert_Some; simplify_map_eq; auto.
        apply NoDup_cons in Hnodup as [HkX Hnodup].
        apply NoDup_cons; split; last (eapply IHm; eauto).
        intro Hcontra.
        apply elem_of_kvs_keys in Hcontra as (idx0 & w0 & H0).
        apply HkX.
        apply elem_of_kvs_keys; auto.
        destruct (decide (idx = idx0)); simplify_map_eq.
        { exists idx0, w; done. }
        { exists idx0, w0; done. }
      + rewrite kvs_keys_insert_None in Hnodup; auto.
        rewrite kvs_keys_insert_None; simplify_map_eq; auto.
        eapply IHm; eauto.
  Qed.

  Lemma NoDup_kvs_keys_insert_Some
    (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    k ∉ kvs_keys m ->
    NoDup (kvs_keys m) ->
    NoDup (kvs_keys (<[idx:= Some (k, w)]> m)).
  Proof.
    move: idx k w.
    induction m using map_ind; intros idx k w Hk Hnodup.
    { rewrite kvs_keys_insert_Some; simplify_map_eq; auto.
      rewrite kvs_keys_empty.
      apply NoDup_singleton.
    }
    destruct (decide (idx = i)); simplify_map_eq.
    - rewrite insert_insert_eq.
      rewrite kvs_keys_insert_Some; auto.
      destruct x as [ [k' w''] |].
      + rewrite kvs_keys_insert_Some in Hnodup; auto.
        rewrite kvs_keys_insert_Some in Hk; auto.
        apply not_elem_of_cons in Hk as [Hkk' Hk].
        apply NoDup_cons in Hnodup as [Hk' Hnodup].
        apply NoDup_cons; split; auto.
      + rewrite kvs_keys_insert_None in Hnodup; auto.
        rewrite kvs_keys_insert_None in Hk; auto.
        apply NoDup_cons; split; auto.
    - rewrite insert_insert_ne; last done.
      destruct x as [ [k' w''] |].
      + rewrite kvs_keys_insert_Some in Hnodup; auto.
        rewrite kvs_keys_insert_Some in Hk; auto.
        rewrite kvs_keys_insert_Some; simplify_map_eq; auto.
        apply not_elem_of_cons in Hk as [Hkk' Hk].
        apply NoDup_cons in Hnodup as [Hk' Hnodup].
        apply NoDup_cons; split; auto.
        intro Hcontra.
        apply elem_of_kvs_keys in Hcontra.
        destruct Hcontra as (idx0&w0&Hcontra).
        destruct (decide (idx0 = idx)); simplify_map_eq.
        apply Hk'.
        apply elem_of_kvs_keys.
        eexists _,_;eauto.
      + rewrite kvs_keys_insert_None in Hnodup; auto.
        rewrite kvs_keys_insert_None in Hk; auto.
        rewrite kvs_keys_insert_None; simplify_map_eq; auto.
  Qed.

  Lemma NoDup_kvs_keys_insert_None
    (m : kvs_map) (idx : nat) :
    m !! idx = None ->
    NoDup (kvs_keys m) ->
    NoDup (kvs_keys (<[idx:= None]> m)).
  Proof.
    intros Hidx Hnodup.
    rewrite kvs_keys_insert_None; auto.
  Qed.

  (* Lemma NoDup_kvs_keys_insert *)
  (*   (m : kvs_map) (idx : nat) (opt_kw : kvs_entry) : *)
  (*   m !! idx = None -> *)
  (*   NoDup (kvs_keys m) -> *)
  (*   NoDup (kvs_keys (<[idx:= opt_kw]> m)). *)
  (* Proof. *)
  (*   destruct opt_kw as [ [??] | ]; intros Hidx Hnodup *)
  (*   ; [ apply NoDup_kvs_keys_insert_Some | apply NoDup_kvs_keys_insert_None ]; auto. *)
  (*   intros Hidx Hnodup. *)
  (*   rewrite kvs_keys_insert_None; auto. *)
  (* Qed. *)

  (* Lemma kvs_keys_empty_slot (m : kvs_map) : EMPTY_SLOT ∉ kvs_keys m. *)
  (* Proof. *)
  (*   rewrite /kvs_keys. *)
  (*   intros Hcontra. *)
  (*   apply list_elem_of_filter in Hcontra as [? _]; done. *)
  (* Qed. *)

  Definition kvs_map_init : kvs_map :=
    list_to_map ((fun n => (n, None)) <$> (seq 0 SIZE_MAP)).

  Lemma wf_kvs_map_kvs_map_init : wf_kvs_map kvs_map_init.
  Proof.
    rewrite /kvs_map_init /wf_kvs_map /kvs_dom.
    generalize 0 as k.
    induction SIZE_MAP; intros k; cbn.
    - split.
      + by rewrite dom_empty_L.
      + rewrite kvs_keys_empty.
        by apply NoDup_nil.
    - destruct (IHn (S k)) as [IH_dom IH_nodup].
      split.
      + by rewrite dom_insert_L IH_dom.
      + set (IHl := (list_to_map ((λ n0 : nat, (n0, None)) <$> seq (S k) n))).
        apply NoDup_kvs_keys_insert_None; auto.
        subst IHl.
        apply not_elem_of_list_to_map_1.
        intro Hk; apply list_elem_of_fmap_1 in Hk as ([k' w']&?&Hk); simplify_eq.
        cbn in *.
        apply list_elem_of_fmap_1 in Hk as (idx&?&Hk); simplify_eq.
        apply elem_of_seq in Hk.
        lia.
  Qed.

  Lemma kvs_keys_map_init : kvs_keys kvs_map_init ≡ₚ [].
  Proof.
    rewrite /kvs_map_init.
    generalize 0 as k.
    induction SIZE_MAP; intros k; cbn.
    - by rewrite kvs_keys_empty.
    - specialize (IHn (S k)).
      rewrite kvs_keys_insert_None; auto.
      apply not_elem_of_list_to_map_1.
      intro Hk; apply list_elem_of_fmap_1 in Hk as ([k' w']&?&Hk); simplify_eq.
      cbn in *.
      apply list_elem_of_fmap_1 in Hk as (idx&?&Hk); simplify_eq.
      apply elem_of_seq in Hk.
      lia.
  Qed.

  Lemma kvs_alloc_synced_map_init (m : kvs_alloc) :
    (∀ ku sk, m !! ku = Some sk -> sk = ∅) ->
    kvs_alloc_synced kvs_map_init m.
  Proof.
    intros Hm.
    intros [ku kn] Hwf_k; cbn in *.
    split; intros Hkvs; exfalso.
    - destruct Hkvs as (sk & Hk & Hsk).
      apply Hm in Hk; set_solver.
    - rewrite kvs_keys_map_init in Hkvs.
      set_solver.
  Qed.

  Lemma elem_of_kvs_map_init (idx : nat) (opt_kv : kvs_entry) :
    kvs_map_init !! idx = Some opt_kv -> opt_kv = None.
  Proof.
    intros Hidx.
    rewrite /kvs_map_init in Hidx.
    apply elem_of_list_to_map_2 in Hidx.
    apply list_elem_of_fmap in Hidx as (n&?&Hidx); simplify_eq.
    done.
  Qed.

  Lemma kvs_initial_map_init_None :
  ([∗ map] l↦v ∈ kvs_map_init, pointsto l (DfracOwn 1) v) -∗
  ([∗ map] idx↦_ ∈ kvs_map_init, idx⤇(KVS) NONE).
  Proof.
    iIntros "Hkvs_frags".
    iApply (big_sepM_impl with "Hkvs_frags").
    iModIntro; iIntros (k v Hk) "H".
    apply elem_of_kvs_map_init in Hk; simplify_eq; iFrame.
  Qed.

  Lemma kvs_initial_map_init (b e : Addr) :
    (b + (ASM_SIZEOF_KVS_ENTRY * SIZE_MAP))%a = Some e ->
    ([[b,e]]↦ₐ[[kvs_data]]) -∗
    ([∗ map] idx↦opt_kw ∈ kvs_map_init, idx ⤇(KVS) NONE) -∗
    [∗ map] idx↦kw ∈ kvs_map_init, isKVS_entry b idx kw.
  Proof.
    rewrite /kvs_map_init /kvs_data.
    generalize dependent e.
    replace b with (b^+(ASM_SIZEOF_KVS_ENTRY*0%nat))%a by solve_addr.
    rewrite {3}(_ : (b^+(ASM_SIZEOF_KVS_ENTRY*0%nat))%a = b); last solve_addr.
    generalize 0 as k.
    induction SIZE_MAP; iIntros (k e Hbe) "Hmem Hfrags"; cbn; first done.
    specialize (IHn (S k)).
    iDestruct (big_sepM_insert with "Hfrags") as "[Hf Hfrags]".
    { apply not_elem_of_list_to_map.
      intro Hcontra.
      apply list_elem_of_fmap in Hcontra as ([idx opt_kw ] & ? & Hcontra); simplify_eq.
      apply list_elem_of_fmap in Hcontra as (k' & ? & Hcontra); simplify_eq.
      apply elem_of_seq in Hcontra; cbn in *.
      lia.
    }
    iApply big_sepM_insert.
    { apply not_elem_of_list_to_map.
      intro Hcontra.
      apply list_elem_of_fmap in Hcontra as ([idx opt_kw ] & ? & Hcontra); simplify_eq.
      apply list_elem_of_fmap in Hcontra as (k' & ? & Hcontra); simplify_eq.
      apply elem_of_seq in Hcontra; cbn in *.
      lia.
    }
    iDestruct (region_pointsto_cons _ (b ^+ ((ASM_SIZEOF_KVS_ENTRY * k)+1))%a with "Hmem") as "[Hb0 Hmem]"; [solve_addr+Hbe|solve_addr+Hbe|].
    iDestruct (region_pointsto_cons _ (b ^+ ((ASM_SIZEOF_KVS_ENTRY * k)+2))%a with "Hmem") as "[Hb1 Hmem]"; [solve_addr+Hbe|solve_addr+Hbe|].
    iDestruct (region_pointsto_cons _ (b ^+ ((ASM_SIZEOF_KVS_ENTRY * k)+ASM_SIZEOF_KVS_ENTRY))%a with "Hmem") as "[Hb2 Hmem]"; [solve_addr+Hbe|solve_addr+Hbe|].
    iSplitL "Hf Hb0 Hb1 Hb2".
    - iFrame.
    - iApply (IHn (b ^+ (ASM_SIZEOF_KVS_ENTRY * (k + (S n))))%a with "[Hmem] [$Hfrags]"); first solve_addr+Hbe.
      replace (b ^+ ASM_SIZEOF_KVS_ENTRY * S k)%a with (b ^+ (ASM_SIZEOF_KVS_ENTRY * k + ASM_SIZEOF_KVS_ENTRY))%a by solve_addr.
      replace e with (b ^+ ASM_SIZEOF_KVS_ENTRY * (k + S n))%a by solve_addr.
      done.
  Qed.

  Lemma wf_kvs_map_insert (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    m !! idx = Some None ->
    k ∉ kvs_keys m ->
    wf_kvs_map m ->
    wf_kvs_map (<[idx:= Some (k, w)]> m).
  Proof.
    intros Hidx Hk (Hkvs_dom & Hkvs_unique).
    split.
    - rewrite dom_insert_L -Hkvs_dom.
      assert (idx ∈ dom m).
      { apply elem_of_dom; eauto. }
      set_solver.
    - eapply NoDup_kvs_keys_insert_Some; eauto.
  Qed.

  Local Lemma kvs_alloc_synced_insert_1 (m : kvs_map) ( s : kvs_alloc ) (idx : nat) (ku kn ku' kn' : Z) (w : Word) :
    let fkey := kvs_full_key ku kn in
    wf_kvs_full_key ku kn ->
    m !! idx = Some None ->
    fkey ∉ kvs_keys m ->
    kvs_alloc_synced m s ->
    wf_kvs_full_key ku' kn' ->
    kvs_alloc_elem_of (kvs_alloc_insert s ku {[kn]}) ku' kn' ->
    kvs_full_key ku' kn' ∈ kvs_keys (<[idx:= Some (fkey, w)]> m).
  Proof.
    intros fkey Hwf_full_key Hidx Hk_free Halloc Hwf_full_key' Hk.
    destruct Hk as (sk & Hku' & Hkn').
    destruct (decide (ku = ku')); simplify_map_eq.
    - apply kvs_alloc_insert_lookup_eq in Hku'; simplify_map_eq.
      apply elem_of_union in Hkn'; destruct Hkn' as [Hkn' | Hkn'].
      + apply elem_of_singleton in Hkn' ; simplify_eq.
        eapply elem_of_kvs_keys.
        by exists idx, w; simplify_map_eq.
      + specialize (Halloc (ku', kn') Hwf_full_key'); cbn in *.
        rewrite /kvs_alloc_elem_of in Halloc.
        destruct ( s !! ku' ) as [s_ku|]; last set_solver+Hkn'.
        cbn in Hkn'.
        assert ((∃ sk : gset Z, Some s_ku = Some sk ∧ kn' ∈ sk)) as IH.
        { exists s_ku; split; auto. }
        apply Halloc in IH.
        apply elem_of_kvs_keys in IH as (idx' & v' & Hk).
        eapply elem_of_kvs_keys.
        destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
        by eexists idx', v'; simplify_map_eq.
    - apply kvs_alloc_insert_lookup_ne in Hku'; auto; simplify_map_eq.
      eapply elem_of_kvs_keys.
      assert (∃ sk : gset Z, s !! ku' = Some sk ∧ kn' ∈ sk) as IH.
      { exists sk; split; auto. }
      apply (Halloc (ku', kn') Hwf_full_key') in IH.
      apply elem_of_kvs_keys in IH as (idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
      by eexists idx', v'; simplify_map_eq.
  Qed.

  Local Lemma kvs_alloc_synced_insert_2 (m : kvs_map) ( s : kvs_alloc ) (idx : nat) (ku kn ku' kn' : Z) (w : Word) :
    let fkey := kvs_full_key ku kn in
    wf_kvs_full_key ku kn ->
    m !! idx = Some None ->
    fkey ∉ kvs_keys m ->
    kvs_alloc_synced m s ->
    wf_kvs_full_key ku' kn' ->
    kvs_full_key ku' kn' ∈ kvs_keys (<[idx:= Some (fkey, w)]> m) ->
    kvs_alloc_elem_of (kvs_alloc_insert s ku {[kn]}) ku' kn'.
  Proof.
    intros fkey Hwf_full_key Hidx Hk_free Halloc Hwf_full_key' Hk.
    specialize (Halloc (ku', kn') Hwf_full_key') as IH.
    apply elem_of_kvs_keys in Hk as (idx' & v' & Hk).
    destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
    - apply kvs_full_key_inj in H as [ -> -> ]; eauto.
      rewrite /kvs_alloc_insert;simplify_map_eq.
      apply (iffRLn (Halloc (ku',kn') Hwf_full_key')) in Hk_free.
      apply kvs_alloc_not_elem_of in Hk_free as [Hkfree|Hkfree]; eauto; cbn in *.
      + rewrite Hkfree /default /= union_empty_r_L.
        exists {[kn']}; split; eauto;simplify_map_eq;set_solver+.
      + destruct Hkfree as (sk' & Hsk'' & Hkn''); simplify_map_eq.
        exists ({[kn']} ∪ sk'); split; eauto;simplify_map_eq; set_solver+.
    - assert (kvs_full_key ku' kn' ∈ kvs_keys m) as IHm.
      { apply elem_of_kvs_keys; eauto. }
      apply IH in IHm as (sk & Hsk & Hsk').
      apply (iffRLn (Halloc (ku,kn) Hwf_full_key)) in Hk_free.
      apply kvs_alloc_not_elem_of in Hk_free as [Hkfree|Hkfree]; cbn in *.
      + rewrite /kvs_alloc_insert Hkfree /default union_empty_r_L.
        assert (ku ≠ ku') by (intro;simplify_map_eq).
        exists sk;split; simplify_map_eq; eauto.
      + destruct Hkfree as (sk' & Hsk'' & Hkn''); simplify_map_eq.
        rewrite /kvs_alloc_insert.
        rewrite Hsk'' /default /=.
        destruct (decide (ku = ku')); simplify_map_eq.
        * eexists; split; simplify_map_eq; eauto;apply elem_of_union; by right.
        * exists sk; split; simplify_map_eq;eauto.
  Qed.

  Lemma kvs_alloc_synced_insert (m : kvs_map) ( s : kvs_alloc ) (idx : nat) (ku kn : Z) (w : Word) :
    let fkey := kvs_full_key ku kn in
    wf_kvs_full_key ku kn ->
    m !! idx = Some None ->
    fkey ∉ kvs_keys m ->
    kvs_alloc_synced m s ->
    kvs_alloc_synced (<[idx:=Some (fkey, w)]> m) ( kvs_alloc_insert s ku {[kn]}).
  Proof.
    intros fkey Hwf_full_key Hidx Hk_free Halloc.
    rewrite /kvs_alloc_synced.
    intros [ku' kn'] Hwf_full_key'.
    cbn.
    split; intros Hk.
    - eapply kvs_alloc_synced_insert_1; eauto.
    - eapply kvs_alloc_synced_insert_2; eauto.
  Qed.

  Lemma wf_kvs_map_update (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    (∃ w', m !! idx = Some (Some (k, w'))) ->
    wf_kvs_map m ->
    wf_kvs_map (<[idx:= Some (k, w)]> m).
  Proof.
    intros [w' Hidx] (Hkvs_dom & Hkvs_unique).
    split.
    - rewrite dom_insert_L -Hkvs_dom.
      assert (idx ∈ dom m).
      { apply elem_of_dom; eauto. }
      set_solver.
    - eapply NoDup_kvs_keys_update; eauto.
  Qed.

  Lemma kvs_frag_kvs_frag_idx (k : Z) (w : Word) :
    k ⤇(KVS) w -∗ ∃ idx, k ⤇(KVS)[idx] w.
  Proof. rewrite /kvs_frag; iIntros "?"; done. Qed.

  Lemma kvs_frag_idx_kvs_frag (k : Z) (w : Word) (idx : nat) :
    k ⤇(KVS)[idx] w -∗ k ⤇(KVS) w.
  Proof. rewrite /kvs_frag; iIntros "$".  Qed.

  Lemma kvs_auth_insert (a : Addr) (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    ●(KVS) m -∗ idx ⤇(KVS) NONE
    ==∗
    ●(KVS) (<[idx:= Some (k, w)]> m) ∗ k ⤇(KVS)[ idx ] w.
  Proof.
    iIntros "Hkvs_auth Hkvs_frag".
    by iMod (gen_heap_update m idx _ (Some (k,w)) with "Hkvs_auth Hkvs_frag") as "[$ $]".
  Qed.

  Lemma kvs_auth_update (a : Addr) (m : kvs_map) (idx : nat) (k k' : Z) (w w' : Word) :
    ●(KVS) m -∗ k ⤇(KVS)[ idx ] w
    ==∗
    ●(KVS) (<[idx:= Some (k', w')]> m) ∗ k' ⤇(KVS)[ idx ] w'.
  Proof.
    iIntros "Hkvs_auth Hkvs_frag".
    by iMod (gen_heap_update m idx _ (Some (k',w')) with "Hkvs_auth Hkvs_frag") as "[$ $]".
  Qed.

  Lemma kvs_auth_delete (a : Addr) (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    ●(KVS) m -∗ k ⤇(KVS)[ idx ] w
    ==∗
    ●(KVS) (<[idx:= None]> m) ∗ idx ⤇(KVS) NONE.
  Proof.
    iIntros "Hkvs_auth Hkvs_frag".
    by iMod (gen_heap_update m idx _ None with "Hkvs_auth Hkvs_frag") as "[$ $]".
  Qed.

  Lemma kvs_frag_idx_dupl_false idx k k' w w' :
    k ⤇(KVS)[ idx ] w -∗ k' ⤇(KVS)[ idx ] w' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (pointsto_valid_2 with "H1 H2") as %?.
    destruct H; eapply dfrac_full_exclusive in H; auto.
  Qed.

  Lemma kvs_valid_None (m : kvs_map) (idx : nat) :
    ●(KVS) m -∗
    idx ⤇(KVS) NONE -∗
    ⌜ m !! idx = Some None ⌝.
  Proof.
    iIntros "Hkvs_auth Hk".
    by iDestruct (gen_heap_valid with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma kvs_valid (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    ●(KVS) m -∗
    k ⤇(KVS)[idx] w -∗
    ⌜ m !! idx = Some (Some (k, w)) ⌝.
  Proof.
    iIntros "Hkvs_auth Hk".
    by iDestruct (gen_heap_valid with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma isKVS_valid (m : kvs_map) (s : kvs_alloc) (a : Addr) (idx : nat) (k : Z) (w : Word) :
    isKVS a m s -∗
    k ⤇(KVS)[idx] w -∗
    ⌜ m !! idx = Some (Some (k, w)) ⌝.
  Proof.
    iIntros "(%Hwf_kvs & Hkvs_auth & _) Hk".
    by iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma isKVS_valid_None (m : kvs_map) (s : kvs_alloc) (a : Addr) (idx : nat) :
    isKVS a m s -∗
    idx ⤇(KVS) NONE -∗
    ⌜ m !! idx = Some None ⌝.
  Proof.
    iIntros "(%Hwf_kvs & Hkvs_auth & _) Hk".
    by iDestruct (kvs_valid_None with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma isKVS_open_valid (m : kvs_map) (s : kvs_alloc) (a : Addr) (idx idx' : nat) (k : Z) (w : Word) :
    isKVS_open a m s idx' -∗
    k ⤇(KVS)[idx] w -∗
    ⌜ m !! idx = Some (Some (k, w)) ⌝.
  Proof.
    iIntros "(%Hwf_kvs & Hkvs_auth & _) Hk".
    by iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma isKVS_open_valid_None (m : kvs_map) (s : kvs_alloc) (a : Addr) (idx idx' : nat) :
    isKVS_open a m s idx' -∗
    idx ⤇(KVS) NONE -∗
    ⌜ m !! idx = Some None ⌝.
  Proof.
    iIntros "(%Hwf_kvs & Hkvs_auth & _) Hk".
    by iDestruct (kvs_valid_None with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma open_isKVS_kvs_frag_idx
    (b : Addr) (m : kvs_map) (s : kvs_alloc)
    (idx : nat) (k : Z) (w : Word) :
    isKVS b m s ∗
    k ⤇(KVS)[idx] w -∗
    isKVS_open b m s idx ∗
    isKVS_entry b idx (Some (k, w)) ∗
    k ⤇(KVS)[idx] w.
  Proof.
    iIntros "( (%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) & Hk)".
    iDestruct (gen_heap_valid with "Hkvs_auth Hk") as "%Hidx'".
    rewrite -{2}(insert_id m idx (Some (k,w))); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame; eauto.
  Qed.

  Lemma isKVS_indom_idx (m : kvs_map) (s : kvs_alloc) (a : Addr) (idx : nat) :
    idx ∈ dom m ->
    isKVS a m s -∗
    ⌜ 0 <= idx < SIZE_MAP ⌝.
  Proof.
    iIntros (Hm_idx) "(%Hwf_kvs & _)"; iPureIntro.
    by eapply wf_kvs_indom_idx.
  Qed.

  Lemma isKVS_open_indom_idx (m : kvs_map) (s : kvs_alloc) (a : Addr) (idx idx' : nat) :
    idx ∈ dom m ->
    isKVS_open a m s idx' -∗
    ⌜ 0 <= idx < SIZE_MAP ⌝.
  Proof.
    iIntros (Hm_idx) "(%Hwf_kvs & _)"; iPureIntro.
    by eapply wf_kvs_indom_idx.
  Qed.

  Lemma open_isKVS_kvs_frag_idx_diff
    (b : Addr) (m : kvs_map) (s : kvs_alloc) (idx idx' : nat) (k : Z) (w : Word):
    0 <= idx' < SIZE_MAP ->
    idx ≠ idx' ->
    isKVS b m s ∗
    k ⤇(KVS)[ idx ] w -∗
    ∃ opt_kw',
      k ⤇(KVS)[ idx ] w ∗
      isKVS_open b m s idx' ∗
      ⌜ m !! idx' = Some opt_kw' ⌝ ∗
      isKVS_entry b idx' opt_kw' ∗
      ⌜ match opt_kw' with | Some kw' => k ≠ kw'.1 | None => True end ⌝.
  Proof.
    iIntros (Hidx' Hidx_ne) "( (%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) & Hk)".
    iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hm_idx".
    pose proof (wf_kvs_is_Some _ _ Hwf_kvs Hidx') as [ opt_kw' Hm_idx' ].
    iExists opt_kw'.
    rewrite -{2}(insert_id m idx' opt_kw'); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[ Hk' HKVS]".
    iFrame "∗%".
    iPureIntro.
    destruct opt_kw' as [ [k' w'] |]; auto.
    pose proof (wf_kvs_neq _ _ _ _ _ _ _ Hwf_kvs Hidx_ne Hm_idx Hm_idx') as Hkk'.
    done.
  Qed.

  Lemma open_isKVS_not_alloc
    (b : Addr) (m : kvs_map) (s : kvs_alloc) (s' : gset Z)
    (idx : nat) (ku kn : Z) :
    let fkey := kvs_full_key ku kn in
    wf_kvs_full_key ku kn ->
    (0 ≤ idx < SIZE_MAP)%Z →
    kn ∉ s' →
    isKVS b m s -∗
    ◯(ALLOC)[ku] s' -∗
    ∃ opt_kwidx,
      ⌜ m !! idx = Some opt_kwidx ⌝ ∗
      isKVS_open b m s idx ∗
      ◯(ALLOC)[ku] s' ∗
      isKVS_entry b idx opt_kwidx ∗
      ⌜ match opt_kwidx with | Some kwidx => kwidx.1 ≠ fkey | None => True end ⌝.
  Proof.
    intros fkey Hwf_full_key Hidx Hs'.
    iIntros "(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) Hk".
    iDestruct ( allocated_keys_valid with "Halloc Hk" ) as "%Hss'".
    assert (fkey ∉ kvs_keys m) as Hfkey_not_allocated.
    { intro Hcontra; apply (Hwf_alloc (ku, kn)) in Hcontra.
      2: { by cbn. }
      rewrite /kvs_alloc_synced in Hwf_alloc.
      rewrite /kvs_alloc_elem_of in Hcontra.
      set_solver.
    }
    iFrame.
    assert ( is_Some (m !! idx) ) as [ opt_kwidx Hm_idx].
    { apply wf_kvs_is_Some; auto; lia. }
    rewrite -{1}(insert_id m idx opt_kwidx); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame "∗%".
    iPureIntro.
    destruct opt_kwidx as [ [ kidx widx ]|]; auto.
    cbn.
    assert ( kidx ∈ kvs_keys m ) as Hkidx by (apply elem_of_kvs_keys; eauto).
    set_solver.
  Qed.

  Lemma open_isKVS
    (b : Addr) (m : kvs_map) (s : kvs_alloc)
    (idx : nat) :
    (0 ≤ idx < SIZE_MAP)%Z →
    isKVS b m s -∗
    ∃ opt_kwidx,
      ⌜ m !! idx = Some opt_kwidx ⌝ ∗
      isKVS_open b m s idx ∗
      isKVS_entry b idx opt_kwidx.
  Proof.
    intros Hidx.
    iIntros "(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS)".
    iFrame.
    assert ( is_Some (m !! idx) ) as [ opt_kwidx Hm_idx].
    { apply wf_kvs_is_Some; auto; lia. }
    rewrite -{1}(insert_id m idx opt_kwidx); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame "∗%".
  Qed.

  Lemma close_isKVS
    (b : Addr) (m : kvs_map) (s : kvs_alloc) (idx : nat) (opt_kwidx : kvs_entry):
    m !! idx = Some opt_kwidx ->
    isKVS_open b m s idx ∗
    isKVS_entry b idx opt_kwidx -∗
    isKVS b m s.
  Proof.
    iIntros (Hidx) "[(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) Hkvs_entry]"; cbn.
    iDestruct (big_sepM_delete with "[$HKVS $Hkvs_entry]") as "HKVS"; eauto.
    iFrame; eauto.
  Qed.

  Lemma kvs_alloc_synced_update (m : kvs_map) (s : kvs_alloc) (idx : nat) (k : Z) (w : Word) :
    (∃ w', m !! idx = Some ( Some (k, w'))) ->
    kvs_alloc_synced m s ->
    kvs_alloc_synced (<[idx:= Some (k, w)]> m) s.
  Proof.
    intros [w' Hidx] Halloc.
    rewrite /kvs_alloc_synced.
    intros [ku kn].
    specialize (Halloc (ku, kn)); cbn in *.
    split; intros Hk.
    - apply Halloc in Hk; auto.
      apply elem_of_kvs_keys in Hk as (idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_eq; cbn in *.
      + by eapply elem_of_kvs_keys; eauto; eexists idx',_; simplify_map_eq.
      + by eapply elem_of_kvs_keys; eauto; eexists idx',_; simplify_map_eq.
    - apply Halloc; auto.
      apply elem_of_kvs_keys in Hk as (idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_eq; cbn in *.
      + by eapply elem_of_kvs_keys; eauto; eexists idx',_; simplify_map_eq.
      + by eapply elem_of_kvs_keys; eauto; eexists idx',_; simplify_map_eq.
  Qed.

  Lemma isKVS_open_update (a : Addr) (m : kvs_map) (s : kvs_alloc) (idx : nat) (k : Z) (w w' : Word) :
    isKVS_open a m s idx -∗ k ⤇(KVS)[ idx ] w
    ==∗
    isKVS_open a (<[idx:= Some (k, w')]> m) s idx ∗ k ⤇(KVS)[ idx ] w'.
  Proof.
    iIntros "(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) Hk".
    iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hm_idx".
    iMod (kvs_auth_update a m idx _ k _ w' with "Hkvs_auth Hk") as "[$ $]".
    eapply (wf_kvs_map_update _ _ _ w') in Hwf_kvs; eauto.
    eapply (kvs_alloc_synced_update _ _ _ _ w') in Hwf_alloc; eauto.
    rewrite delete_insert_eq.
    by iFrame "∗ %".
  Qed.

  Lemma isKVS_open_insert (a : Addr) (m : kvs_map) (s : kvs_alloc) (s' : gset Z) (idx : nat) (ku kn : Z) (w : Word) :
    let k := kvs_full_key ku kn in
    kn ∉ s' →
    wf_kvs_full_key ku kn ->
    isKVS_open a m s idx -∗
    ◯(ALLOC)[ku] s' -∗
    idx ⤇(KVS) NONE
    ==∗
    isKVS_open a (<[idx:= Some (k, w)]> m) (kvs_alloc_insert s ku {[kn]}) idx ∗
    ◯(ALLOC)[ku] ({[kn]} ∪ s') ∗
    k ⤇(KVS)[ idx ] w.
  Proof.
    intro k.
    iIntros (Hs' Hwf_kvs_full_key)
      "(%Hwf_kvs & Hkvs_auth & Halloc_auth & %Hwf_alloc & HKVS) Halloc_frag Hk".
    iDestruct (allocated_keys_valid with "Halloc_auth Halloc_frag") as "%Hvalid".
    iDestruct (kvs_valid_None with "Hkvs_auth Hk") as "%Hm_idx".
    iMod (kvs_auth_insert a m idx k w with "Hkvs_auth Hk") as "[$ $]".
    iMod ( allocated_keys_insert ku kn with "Halloc_auth Halloc_frag") as "[Halloc_auth Halloc_frag]".
    rewrite /kvs_alloc_synced in Hwf_alloc.
    assert (k ∉ kvs_keys m) as Hk_notin_keys.
    { intro Hcontra; apply Hs'.
      apply (Hwf_alloc (ku,kn) Hwf_kvs_full_key) in Hcontra.
      destruct Hcontra as (?&?&?); simplify_map_eq; done.
    }
    eapply (wf_kvs_map_insert _ _ _ w) in Hwf_kvs; eauto.
    eapply (kvs_alloc_synced_insert _ _ _ _ _ w) in Hwf_alloc; eauto.
    rewrite delete_insert_eq.
    subst k.
    iFrame "∗ %".
    by rewrite /kvs_alloc_insert Hvalid /=.
  Qed.

  Lemma allocated_keys_delete `{kvsG} (ku : Z) (kn : Z) ( m : kvs_alloc) (s' : gset Z) :
    ●(ALLOC) m -∗ ◯(ALLOC)[ku] s' ==∗
    ●(ALLOC) (<[ ku := (s' ∖ {[kn]}) ]> m) ∗ ◯(ALLOC)[ku] (s' ∖ {[kn]}).
  Proof.
    iIntros "Hs Hs'".
    by iMod (gen_heap_update m ku _ (s' ∖ {[kn]}) with "Hs Hs'") as "[$ $]".
  Qed.

  Lemma kvs_alloc_delete_lookup_eq s ku ks sk :
    kvs_alloc_delete s ku ks !! ku = Some sk ->
    sk = default ∅ (s !! ku) ∖ ks.
  Proof.
    intros H.
    rewrite /kvs_alloc_delete in H; simplify_map_eq.
    done.
  Qed.

  Lemma kvs_alloc_delete_lookup_ne s ku ku' ks sk :
    ku ≠ ku' ->
    kvs_alloc_delete s ku ks !! ku' = Some sk ->
    s !! ku' = Some sk.
  Proof.
    intros Hk H.
    rewrite /kvs_alloc_delete in H; simplify_map_eq.
    done.
  Qed.

  Local Lemma kvs_alloc_synced_delete_1 (m : kvs_map) ( s : kvs_alloc ) (idx : nat) (ku kn ku' kn' : Z) (w : Word) :
    let fkey := kvs_full_key ku kn in
    wf_kvs_full_key ku kn ->
    m !! idx = Some (Some (fkey, w)) ->
    kvs_alloc_synced m s ->
    wf_kvs_full_key ku' kn' ->
    kvs_alloc_elem_of (kvs_alloc_delete s ku {[kn]}) ku' kn' ->
    kvs_full_key ku' kn' ∈ kvs_keys (<[idx:=None]> m).
  Proof.
    intros fkey Hwf_full_key Hidx Halloc Hwf_full_key' Hk.
    destruct Hk as (sk & Hku' & Hkn').
    destruct (decide (ku = ku')); simplify_map_eq.
    - apply kvs_alloc_delete_lookup_eq in Hku'; simplify_map_eq.
      apply elem_of_difference in Hkn' as [Hkn' Hkn'_ne].
      apply not_elem_of_singleton in Hkn'_ne.
      cbn in *.
      specialize (Halloc (ku', kn') Hwf_full_key'); cbn in *.
      assert ( kvs_alloc_elem_of s ku' kn' ).
      {
        rewrite /kvs_alloc_elem_of.
        destruct ( s !! ku' ) as [s_ku|]; last set_solver+Hkn'.
        eauto.
      }
      apply Halloc in H.
      eapply elem_of_kvs_keys in H as (idx' & w' & H).
      eapply elem_of_kvs_keys; auto.
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
      * apply kvs_full_key_inj in H as [_ ->]; eauto; done.
      * by exists idx', w'; simplify_map_eq.
    - apply kvs_alloc_delete_lookup_ne in Hku'; auto; simplify_map_eq.
      eapply elem_of_kvs_keys.
      assert (∃ sk : gset Z, s !! ku' = Some sk ∧ kn' ∈ sk) as IH.
      { exists sk; split; auto. }
      apply (Halloc (ku', kn') Hwf_full_key') in IH.
      apply elem_of_kvs_keys in IH as (idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
      * apply kvs_full_key_inj in H as [-> ->] ;eauto; done.
      * by exists idx', v'; simplify_map_eq.
  Qed.

  Lemma NoDup_kvs_keys_elem_of m idx ku kn w idx' ku' kn' w' :
    let f := kvs_full_key ku kn in
    let f' := kvs_full_key ku' kn' in
    NoDup (kvs_keys m) ->
    idx ≠ idx' ->
    m !! idx = Some (Some (f, w)) ->
    m !! idx' = Some (Some (f', w')) ->
    ku' ≠ ku ∨ kn' ≠ kn.
  Proof.
    intros f f'.
    induction m using map_ind; intros Hnodup Hidx_ne Hm_idx Hm_idx'; first set_solver.
    simplify_map_eq.
    destruct x as [ [kx wx] |]; cycle 1.
    - rewrite kvs_keys_insert_None in Hnodup; auto.
      assert (idx ≠ i) as Hidx_i_ne by (intro; simplify_map_eq; done).
      assert (idx' ≠ i) as Hidx'_i_ne by (intro; simplify_map_eq; done).
      simplify_map_eq.
      auto.
    - rewrite kvs_keys_insert_Some in Hnodup; auto.
      apply NoDup_cons in Hnodup as [Hkx_not_elem_kvs_keys Hnodup].
      destruct (decide (idx = i)); simplify_map_eq.
      + (* idx = i *)
        assert (f' ∈ kvs_keys m) as Hf'.
        { apply elem_of_kvs_keys; eexists _,_; eauto. }
        destruct (decide (ku' = ku)); simplify_eq; [right|left]; auto.
        destruct (decide (kn' = kn)); simplify_eq; auto.
      + destruct (decide (idx' = i)); simplify_map_eq.
        * (* idx ≠ i ∧ idx' = i *)
          assert (f ∈ kvs_keys m) as Hf.
          { apply elem_of_kvs_keys; eexists _,_; eauto. }
          destruct (decide (ku' = ku)); simplify_eq; [right|left]; auto.
          destruct (decide (kn' = kn)); simplify_eq; auto.
        * (* idx ≠ i ∧ idx' ≠ i *)
          eapply IHm; eauto.
  Qed.

  Local Lemma kvs_alloc_synced_delete_2 (m : kvs_map) ( s : kvs_alloc ) (idx : nat) (ku kn ku' kn' : Z) (w : Word) :
    let fkey := kvs_full_key ku kn in
    wf_kvs_full_key ku kn ->
    m !! idx = Some (Some (fkey, w)) ->
    NoDup (kvs_keys m) ->
    kvs_alloc_synced m s ->
    wf_kvs_full_key ku' kn' ->
    kvs_full_key ku' kn' ∈ kvs_keys (<[idx:=None]> m) ->
    kvs_alloc_elem_of (kvs_alloc_delete s ku {[kn]}) ku' kn'.
  Proof.
    intros fkey Hwf_full_key Hidx Hnodup Halloc Hwf_full_key' Hk.
    specialize (Halloc (ku', kn') Hwf_full_key') as IH'.
    cbn in *.
    apply elem_of_kvs_keys in Hk as (idx' & v' & Hk).

    destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
    assert (kvs_full_key ku' kn' ∈ kvs_keys m) as IHm'.
    { apply elem_of_kvs_keys; eauto. }

    apply IH' in IHm' as (sk' & Hsk' & Hkn'_in_sk').
    assert (kvs_full_key ku kn ∈ kvs_keys m) as IHm.
    { apply elem_of_kvs_keys; eauto. }
    rewrite /kvs_alloc_delete.
    destruct (decide (ku = ku')); simplify_map_eq; cycle 1.
    { exists sk'; split; simplify_map_eq;eauto. }
    eexists; split; simplify_map_eq; eauto;apply elem_of_difference; split; auto.
    apply not_elem_of_singleton.
    eapply (NoDup_kvs_keys_elem_of m idx ku' kn _ idx' ku' kn') in Hnodup; eauto.
    destruct Hnodup as [ | ]; auto.
  Qed.

  Lemma kvs_alloc_synced_delete (m : kvs_map) ( s : kvs_alloc ) (idx : nat) (ku kn : Z) (w : Word) :
    let fkey := kvs_full_key ku kn in
    NoDup (kvs_keys m) ->
    wf_kvs_full_key ku kn ->
    m !! idx = Some (Some (fkey, w)) ->
    kvs_alloc_synced m s ->
    kvs_alloc_synced (<[idx:=None]> m) (kvs_alloc_delete s ku {[kn]}).
  Proof.
    intros fkey Hnodup Hwf_full_key Hidx Halloc.
    rewrite /kvs_alloc_synced.
    intros [ku' kn'] Hwf_full_key'.
    cbn.
    split; intros Hk.
    - eapply (kvs_alloc_synced_delete_1 m s idx ku kn ku' kn'); eauto.
    - eapply (kvs_alloc_synced_delete_2 m s idx ku kn ku' kn'); eauto.
  Qed.

  Lemma NoDup_kvs_keys_delete
    (m : kvs_map) (idx : nat)  :
    NoDup (kvs_keys m) ->
    NoDup (kvs_keys (<[idx:=None]> m)).
  Proof.
    generalize dependent idx.
    induction m using map_ind; intros idx Hnodup; first simplify_map_eq.
    { rewrite kvs_keys_insert_None; auto. }
    destruct (decide (idx = i)); simplify_map_eq.
    - rewrite insert_insert_eq.
      rewrite kvs_keys_insert_None; auto.
      destruct x as [ [] |].
      + rewrite kvs_keys_insert_Some in Hnodup; auto.
        apply NoDup_cons in Hnodup as [ _ Hnodup ]; auto.
      + rewrite kvs_keys_insert_None in Hnodup; auto.
    - rewrite insert_insert_ne; auto.
      destruct x as [ [ k' w' ] |].
      + rewrite kvs_keys_insert_Some in Hnodup; auto.
        apply NoDup_cons in Hnodup as [ Hk' Hnodup ]; auto.
        rewrite kvs_keys_insert_Some; simplify_map_eq; auto.
        apply NoDup_cons; split ; auto.
        intro Hk. apply elem_of_kvs_keys in Hk as (idx_k&?&?); simplify_eq.
        destruct (decide (idx_k = idx)); simplify_map_eq.
        apply Hk'.
        apply elem_of_kvs_keys; eexists _,_ ; eauto.
      + rewrite kvs_keys_insert_None in Hnodup; auto.
        rewrite kvs_keys_insert_None; simplify_map_eq; auto.
  Qed.

  Lemma wf_kvs_map_delete (m : kvs_map) (idx : nat) (k : Z) :
    (is_Some (m !! idx)) ->
    wf_kvs_map m ->
    wf_kvs_map (<[idx:=None]> m).
  Proof.
    intros [w' Hidx] (Hkvs_dom & Hkvs_unique).
    split.
    - rewrite dom_insert_L -Hkvs_dom.
      assert (idx ∈ dom m).
      { apply elem_of_dom; eauto. }
      set_solver.
    - eapply NoDup_kvs_keys_delete; eauto.
  Qed.

  Lemma isKVS_open_delete (a : Addr) (m : kvs_map) (s : kvs_alloc) (s' : gset Z)
    (idx : nat) (ku kn : Z) (w : Word) :
    let k := kvs_full_key ku kn in
    kn ∈ s' →
    wf_kvs_full_key ku kn ->
    isKVS_open a m s idx -∗
    ◯(ALLOC)[ku] s' -∗
    k ⤇(KVS)[ idx ] w
    ==∗
    isKVS_open a (<[idx:=None]> m) (kvs_alloc_delete s ku {[kn]}) idx ∗
    ◯(ALLOC)[ku] (s' ∖ {[ kn ]}) ∗
    idx ⤇(KVS) NONE.
  Proof.
    intro k.
    iIntros (Hs' Hwf_kvs_full_key)
      "(%Hwf_kvs & Hkvs_auth & Halloc_auth & %Hwf_alloc & HKVS) Halloc_frag Hk".
    iDestruct (allocated_keys_valid with "Halloc_auth Halloc_frag") as "%Hvalid".
    iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hm_idx".
    iMod (kvs_auth_delete a m idx _ _ with "Hkvs_auth Hk") as "[$ $]".

    iMod ( allocated_keys_delete ku kn with "Halloc_auth Halloc_frag") as "[Halloc_auth Halloc_frag]".
    assert (NoDup (kvs_keys m)) as Hnodup by ( by destruct Hwf_kvs ).
    rewrite /kvs_alloc_synced in Hwf_alloc.
    eapply (wf_kvs_map_delete _ _) in Hwf_kvs; eauto.
    eapply (kvs_alloc_synced_delete _ _ _ _ _ w) in Hwf_alloc; eauto.
    rewrite delete_insert_eq.
    subst k.
    iFrame "∗ %".
    by rewrite /kvs_alloc_delete Hvalid /=.
  Qed.

  Class kvs_namespaces :=
    {
      Nkvs : namespace;
      Nkvs_otype : namespace;
      Nkvs_exp_tbl : namespace;
      Nkvs_namespaces_disjoint :
      Nkvs ## Nkvs_otype ∧ Nkvs ## Nkvs_exp_tbl ∧ Nkvs_otype ## Nkvs_exp_tbl
    }.

  Definition kvs_otype_inv
    {KVS_layout : kvsLayout} {KVS_namespaces : kvs_namespaces}
    (W : WORLD) (C : CmptName) (w : Word) : iProp Σ :=
    ∃ (ku : Z) (a : Addr) (s : gset Z),
      (* Shape of the capability*)
      ⌜ w = WSealable (kvs_user_seal_key_scap Global a) ⌝ ∗
      (* Current address is the user key of the compartment *)
      ⌜ (finz.of_z ku) = Some a ⌝ ∗
      ⌜ (0 <= ku < MAX_USER_KEY)%Z ⌝ ∗
      (* KVS resources *)
      ◯(ALLOC)[ku] s ∗
      ([∗ set] kn ∈ s, ∃ w, (kvs_full_key ku kn) ⤇(KVS) w ∗
                            (∀ W' , ⌜ related_sts_priv_world W W' ⌝ -∗ interp W' C w )
      ).

  Program Definition kvs_otype_prop
    {KVS_layout : kvsLayout} {KVS_namespaces : kvs_namespaces} :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ):=
    λne (W : WORLD) (C : CmptName) (w : Word), (kvs_otype_inv W C w)%I.
  Solve All Obligations with solve_proper.

  Definition kvs_otype_propC
    {KVS : kvsLayout} {KVS_namespaces : kvs_namespaces} :
    WORLD * CmptName * leibnizO Word -> iProp Σ :=
    safeC kvs_otype_prop.

  Lemma mono_priv_ot_kvs
    {KVS : kvsLayout} {KVS_namespaces : kvs_namespaces}
    (C : CmptName) (w : Word) :
    ⊢ future_priv_mono C kvs_otype_propC w.
  Proof.
    iIntros (W W' Hrelated_W_W').
    iModIntro.
    iIntros "Hot_kvs".
    rewrite /kvs_otype_propC /= /kvs_otype_inv.
    iDestruct "Hot_kvs" as "(%ku & %a & %s & % & % & % & ? & Hs)".
    iExists ku, a, s; iFrame "∗%".
    iApply (big_sepS_impl with "Hs").
    iModIntro; iIntros (??) "(%w' & $ & H)".
    iIntros (W'' Hrelated_W'_W'').
    iApply "H".
    iPureIntro.
    by eapply related_sts_priv_trans_world.
  Qed.

  Definition kvs_inv {KVS : kvsLayout} {KVS_namespaces : kvs_namespaces} : iProp Σ :=
    let imports :=
      kvs_imports b_switcher e_switcher a_switcher_call ot_switcher
    in
    ∃ (m : kvs_map) (s : kvs_alloc),
      [[ KVS_pcc_b , KVS_pcc_b' ]] ↦ₐ [[ imports ]] ∗
      codefrag KVS_pcc_b' kvs_service_instrs ∗
      isKVS KVS_cgp_b m s ∗
      seal_pred KVS_OTYPE kvs_otype_propC.

End KVS_preamble.

Global Opaque kvs_map_init.
