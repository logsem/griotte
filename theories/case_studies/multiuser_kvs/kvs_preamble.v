From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import switcher kvs.
From cap_machine Require Import proofmode.

Definition kvs_entry : Type := (Z * Word).
Definition kvs_dom : gset nat := set_seq 0 SIZE_MAP.
Definition kvs_map : Type := gmap nat kvs_entry.

(* CMRA for KVS *)
Class kvsG Σ :=
  KvsG {
      kvs_genG :: gen_heapGS nat kvs_entry Σ;
    }.


Definition allocated_keys_auth `{kvsG} ( s : gset (Z * Z) ) : iProp Σ. Admitted.
Definition allocated_keys_frag `{kvsG} (ku : Z) ( s : gset (Z*Z) ) : iProp Σ. Admitted.

Notation "●(ALLOC) s" := (allocated_keys_auth s)%I (at level 20) : bi_scope.
Notation "◯(ALLOC)[ k ] s" := (allocated_keys_frag k s)%I (at level 20) : bi_scope.

Lemma allocated_keys_valid `{kvsG} (ku : Z) (s s' : gset (Z * Z)) :
  ●(ALLOC) s -∗ ◯(ALLOC)[ ku ] s' -∗ ⌜ s' = filter (λ k, k.1 = ku) s ⌝.
Proof.
Admitted.

Lemma allocated_keys_union `{kvsG} (ku : Z) (s s' s'' : gset (Z * Z)) :
  (forall k, k ∈ s'' -> k.1 = ku) ->
  ●(ALLOC) s -∗ ◯(ALLOC)[ku] s' ==∗ ●(ALLOC) (s'' ∪ s) ∗ ◯(ALLOC)[ku] (s'' ∪ s').
Proof.
Admitted.

Lemma allocated_keys_insert `{kvsG} (ku : Z)  (kn : Z) (s s' : gset (Z * Z)) :
  ●(ALLOC) s -∗ ◯(ALLOC)[ku] s' ==∗
  ●(ALLOC) ( {[ (ku, kn) ]} ∪ s) ∗ ◯(ALLOC)[ku] ( {[ (ku, kn) ]} ∪ s').
Proof.
  iIntros "Hs Hs'".
  iMod (allocated_keys_union with "Hs Hs'") as "[$ $]" ; last done.
  intros k Hk. apply elem_of_singleton in Hk ; simplify_eq; done.
Qed.

Definition kvs_frag_idx_frac `{kvsG} (idx : nat) (k : Z) (w : Word) (q : dfrac) : iProp Σ :=
  (pointsto (L:=nat) (V:=kvs_entry) idx q (k,w)).
Notation "k '⤇(KVS){' q '}[' idx  ']' w" :=
  (kvs_frag_idx_frac idx k w q) (at level 20) : bi_scope.
Notation "k '⤇(KVS){' q '}[' idx  ']' -" :=
  (∃ w, kvs_frag_idx_frac idx k w q)%I (at level 20) : bi_scope.

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
    {ceriseg:ceriseG Σ}
    {kvsg:kvsG Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Definition kvs_keys (m : kvs_map) : list Z :=
    filter (fun k => k ≠ EMPTY_SLOT) (map_to_list m).*2.*1.

  Definition wf_kvs_map (m : kvs_map) : Prop :=
    dom m = kvs_dom ∧ NoDup (kvs_keys m).

  Definition isKVS_entry_empty (idx : nat) (k : Z) : iProp Σ :=
    (if (decide (k = EMPTY_SLOT)) then EMPTY_SLOT ⤇(KVS)[idx] (WInt DEFAULT_VAL) else True)%I.

  Definition isKVS_entry (a : Addr) (idx : nat) (kw : Z * Word) : iProp Σ :=
    let k := kw.1 in
    let w := kw.2 in
    (a ^+ (2*idx))%a ↦ₐ (WInt k) ∗
    (a ^+ (2*idx + 1))%a ↦ₐ w ∗
    isKVS_entry_empty idx k
  .

  Definition kvs_alloc_synced (m : kvs_map) (s : gset (Z * Z)) : Prop :=
    ∀ k, wf_kvs_full_key k.1 k.2 -> (k ∈ s ↔ (kvs_full_key k.1 k.2) ∈ kvs_keys m).

  Definition isKVS
    (a : Addr) (m : kvs_map) (s : gset (Z * Z)) : iProp Σ :=
    ⌜ wf_kvs_map m ⌝ ∗
    ●(KVS) m ∗
    ●(ALLOC) s ∗
    ⌜ kvs_alloc_synced m s ⌝ ∗
    [∗ map] idx ↦ kw ∈ m, isKVS_entry a idx kw.

  Definition isKVS_open
    (a : Addr) (m : kvs_map) (s : gset (Z * Z)) (open_idx : nat) : iProp Σ :=
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

  Lemma wf_kvs_neq (m : kvs_map) (idx idx' : nat) (k k' : Z) (w w' : Word) :
    k ≠ EMPTY_SLOT ->
    wf_kvs_map m ->
    idx ≠ idx' ->
    m !! idx = Some (k, w) ->
    m !! idx' = Some (k', w') ->
    k ≠ k'.
  Proof.
    intros Hk_ne_empty [_ Hkvs_uniqueness] Hidx_ne Hm_idx Hm_idx'.
    rewrite /kvs_keys in Hkvs_uniqueness.
    rewrite -(insert_id m idx (k, w)) in Hkvs_uniqueness; last done.
    rewrite -insert_delete_eq in Hkvs_uniqueness.
    rewrite -(insert_id (<[idx:=(k, w)]> (delete idx m)) idx' (k', w')) in Hkvs_uniqueness; last by simplify_map_eq.
    rewrite -insert_delete_eq in Hkvs_uniqueness.
    rewrite -(insert_delete_ne _ idx idx') in Hkvs_uniqueness; auto.
    rewrite map_to_list_insert in Hkvs_uniqueness; last by simplify_map_eq.
    rewrite map_to_list_insert in Hkvs_uniqueness; last by simplify_map_eq.
    cbn in Hkvs_uniqueness.
    destruct (decide (k' ≠ EMPTY_SLOT)); simplify_eq.
    - destruct (decide (k ≠ EMPTY_SLOT)); simplify_eq.
      apply NoDup_cons_1_1 in Hkvs_uniqueness.
      set_solver+Hkvs_uniqueness.
    - destruct (decide (k ≠ EMPTY_SLOT)); simplify_eq.
      apply NoDup_cons_1_1 in Hkvs_uniqueness.
      lia.
  Qed.

  Lemma elem_of_kvs_keys_1 (m : kvs_map) (k : Z) :
    k ∈ kvs_keys m -> (k ≠ EMPTY_SLOT ∧ ∃ idx w, m !! idx = Some (k, w)).
  Proof.
    intros Hk.
    apply list_elem_of_filter in Hk as [Hk_ne_empty Hk].
    apply list_elem_of_fmap in Hk as ([k' v'] & ? & Hk); cbn in *; simplify_eq.
    apply list_elem_of_fmap in Hk as ([idx' kv'] & ? & Hk); cbn in *; simplify_eq.
    apply elem_of_map_to_list in Hk.
    split; eauto.
  Qed.

  Lemma elem_of_kvs_keys_2 (m : kvs_map) (k : Z) :
    (k ≠ EMPTY_SLOT ∧ ∃ idx w, m !! idx = Some (k, w)) ->
    k ∈ kvs_keys m.
  Proof.
    intros [ Hk_ne_empty (idx & w & Hidx)].
    apply list_elem_of_filter; split; auto.
    apply list_elem_of_fmap; exists (k, w); split; first done.
    apply list_elem_of_fmap; exists (idx, (k, w)); split; first done.
    by apply elem_of_map_to_list.
  Qed.

  Lemma elem_of_kvs_keys (m : kvs_map) (k : Z) :
    k ∈ kvs_keys m ↔ (k ≠ EMPTY_SLOT ∧ ∃ idx w, m !! idx = Some (k, w)).
  Proof. split ; [apply elem_of_kvs_keys_1 | apply elem_of_kvs_keys_2]. Qed.


  Lemma NoDup_kvs_keys_update (m : kvs_map) (idx : nat) (k : Z) (w w' : Word) :
    m !! idx = Some (k, w) ->
    NoDup (kvs_keys m) ->
    NoDup (kvs_keys (<[idx := (k, w')]>m)).
  Proof.
    generalize dependent idx; generalize dependent w.
    rewrite /kvs_keys.
    induction m using map_ind; intros w idx Hk Hnodup; first simplify_map_eq.
    destruct (decide (idx = i)); simplify_map_eq.
    - rewrite insert_insert_eq.
      rewrite map_to_list_insert; auto.
      rewrite map_to_list_insert in Hnodup; auto.
    - rewrite insert_insert_ne; last done.
      rewrite map_to_list_insert in Hnodup; last done.
      rewrite map_to_list_insert; last by simplify_map_eq.
      destruct x as [kX vX]; cbn in *.
      destruct (decide (kX ≠ EMPTY_SLOT)); auto; last (eapply IHm; eauto).
      apply NoDup_cons in Hnodup as [HkX Hnodup].
      apply NoDup_cons; split; last (eapply IHm; eauto).
      rewrite -/(kvs_keys (<[idx:=(k, w')]> m)).
      rewrite -/(kvs_keys m) in HkX.
      intro Hcontra; apply HkX.
      apply elem_of_kvs_keys in Hcontra as (HkX_ne_empty & idx0 & w0 & H0).
      apply elem_of_kvs_keys; split; auto.
      destruct (decide (idx = idx0)); simplify_map_eq; eauto.
  Qed.

  Lemma NoDup_kvs_keys_insert
    (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    k ∉ kvs_keys m ->
    NoDup (kvs_keys m) ->
    NoDup (kvs_keys (<[idx:=(k, w)]> m)).
  Proof.
    generalize dependent k.
    generalize dependent w.
    rewrite /kvs_keys.
    induction m using map_ind; intros w k Hk Hnodup; first simplify_map_eq.
    { rewrite map_to_list_insert; auto; cbn.
      rewrite map_to_list_empty; auto; cbn.
      destruct (decide (k ≠ EMPTY_SLOT)).
      + apply NoDup_singleton.
      + by apply NoDup_nil.
    }
    destruct (decide (idx = i)); simplify_map_eq.
    - rewrite insert_insert_eq.
      rewrite map_to_list_insert; auto; cbn.
      rewrite map_to_list_insert in Hnodup; auto; cbn in Hnodup.
      rewrite map_to_list_insert in Hk; auto; cbn in Hk.
      destruct x as [kx wx]; cbn in *.
      destruct (decide (kx ≠ EMPTY_SLOT)); simplify_eq; auto.
      + apply NoDup_cons in Hnodup as [_ Hnodup].
        apply not_elem_of_cons in Hk as [_ Hk].
        destruct (decide (k ≠ EMPTY_SLOT)); simplify_eq; auto.
        apply NoDup_cons; split; auto.
      + destruct (decide (k ≠ EMPTY_SLOT)); simplify_eq; auto.
        apply NoDup_cons; split; auto.
    - rewrite insert_insert_ne; last done.
      rewrite map_to_list_insert in Hnodup; last done.
      rewrite map_to_list_insert in Hk; last done.
      rewrite map_to_list_insert; last by simplify_map_eq.
      destruct x as [kx wx]; cbn in *.
      destruct (decide (kx ≠ EMPTY_SLOT)); simplify_eq; auto.
      apply NoDup_cons in Hnodup as [Hkx Hnodup].
      apply not_elem_of_cons in Hk as [Hk_ne Hk].
      apply NoDup_cons; split; auto.
      rewrite -/(kvs_keys (<[idx:=(k, w)]> m)).
      rewrite -/(kvs_keys m) in Hkx.
      intro Hcontra; apply Hkx.
      apply elem_of_kvs_keys in Hcontra as (_ & idx0 & w0 & H0).
      apply elem_of_kvs_keys; split ; auto.
      destruct (decide (idx = idx0)); simplify_map_eq; eauto.
  Qed.

  Lemma wf_kvs_map_insert (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    m !! idx = Some (EMPTY_SLOT, WInt DEFAULT_VAL) ->
    k ∉ kvs_keys m ->
    wf_kvs_map m ->
    wf_kvs_map (<[idx:=(k, w)]> m).
  Proof.
    intros Hidx Hk (Hkvs_dom & Hkvs_unique).
    split.
    - rewrite dom_insert_L -Hkvs_dom.
      assert (idx ∈ dom m).
      { apply elem_of_dom; eauto. }
      set_solver.
    - eapply NoDup_kvs_keys_insert; eauto.
  Qed.

  Lemma kvs_alloc_synced_insert (m : kvs_map) ( s : gset (Z*Z) ) (idx : nat) (ku kn : Z) (w : Word) :
    let fkey := kvs_full_key ku kn in
    wf_kvs_full_key ku kn ->
    m !! idx = Some (EMPTY_SLOT, WInt DEFAULT_VAL) ->
    fkey ∉ kvs_keys m ->
    kvs_alloc_synced m s ->
    kvs_alloc_synced (<[idx:=(fkey, w)]> m) ( {[ (ku, kn) ]} ∪ s).
  Proof.
    intros fkey Hwf_full_key Hidx Hk_free Halloc.
    rewrite /kvs_alloc_synced.
    intros [ku' kn'] Hwf_full_key'.
    cbn.
    specialize (Halloc (ku', kn')); cbn in *.
    split; intros Hk.
    - apply elem_of_union in Hk; destruct Hk as [Hk | Hk].
      + apply elem_of_singleton in Hk ; simplify_eq.
        eapply elem_of_kvs_keys.
        split.
        * by apply kvs_full_key_not_empty.
        * by exists idx, w; simplify_map_eq.
      + apply (Halloc Hwf_full_key') in Hk.
        apply elem_of_kvs_keys in Hk as (Hidx' & idx' & v' & Hk).
        eapply elem_of_kvs_keys.
        split.
        * by apply kvs_full_key_not_empty in Hwf_full_key'.
        * destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
          by eexists idx', v'; simplify_map_eq.
    - apply elem_of_union.
      apply elem_of_kvs_keys in Hk as (Hidx' & idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
      + left. apply elem_of_singleton.
        apply kvs_full_key_inj in H as [ -> -> ]; eauto.
      + right.
        apply Halloc; eauto.
        eapply elem_of_kvs_keys.
        split.
        * by apply kvs_full_key_not_empty in Hwf_full_key'.
        * by eexists idx',_; simplify_map_eq.
  Qed.

  Lemma wf_kvs_map_update (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    (∃ w', m !! idx = Some (k, w')) ->
    wf_kvs_map m ->
    wf_kvs_map (<[idx:=(k, w)]> m).
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

  Lemma kvs_auth_update (a : Addr) (m : kvs_map) (idx : nat) (k k' : Z) (w w' : Word) :
    ●(KVS) m -∗ k ⤇(KVS)[ idx ] w
    ==∗
    ●(KVS) (<[idx:=(k', w')]> m) ∗ k' ⤇(KVS)[ idx ] w'.
  Proof.
    iIntros "Hkvs_auth Hkvs_frag".
    by iMod (gen_heap_update m idx _ (k',w') with "Hkvs_auth Hkvs_frag") as "[$ $]".
  Qed.

  Lemma kvs_frag_idx_dupl_false idx k k' w w' :
    k ⤇(KVS)[ idx ] w -∗ k' ⤇(KVS)[ idx ] w' -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (pointsto_valid_2 with "H1 H2") as %?.
    destruct H; eapply dfrac_full_exclusive in H; auto.
  Qed.

  Lemma kvs_frag_kvs_empty_not_empty_slot idx k w :
    k ⤇(KVS)[ idx ] w -∗
    isKVS_entry_empty idx k -∗
    ⌜ k ≠ EMPTY_SLOT ⌝.
  Proof.
    iIntros "Hk Hk'".
    rewrite /isKVS_entry_empty.
    destruct (decide (k = EMPTY_SLOT)); last done.
    iDestruct (kvs_frag_idx_dupl_false with "Hk Hk'") as "H"; done.
  Qed.

  Lemma kvs_valid (m : kvs_map) (idx : nat) (k : Z) (w : Word) :
    ●(KVS) m -∗
    k ⤇(KVS)[idx] w -∗
    ⌜ m !! idx = Some (k, w) ⌝.
  Proof.
    iIntros "Hkvs_auth Hk".
    by iDestruct (gen_heap_valid with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma isKVS_valid (m : kvs_map) (s : gset (Z*Z)) (a : Addr) (idx : nat) (k : Z) (w : Word) :
    isKVS a m s -∗
    k ⤇(KVS)[idx] w -∗
    ⌜ m !! idx = Some (k, w) ⌝.
  Proof.
    iIntros "(%Hwf_kvs & Hkvs_auth & _) Hk".
    by iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma isKVS_open_valid (m : kvs_map) (s : gset (Z*Z)) (a : Addr) (idx idx' : nat) (k : Z) (w : Word) :
    isKVS_open a m s idx' -∗
    k ⤇(KVS)[idx] w -∗
    ⌜ m !! idx = Some (k, w) ⌝.
  Proof.
    iIntros "(%Hwf_kvs & Hkvs_auth & _) Hk".
    by iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hidx'".
  Qed.

  Lemma open_isKVS_kvs_frag_idx
    (b : Addr) (m : kvs_map) (s : gset (Z*Z))
    (idx : nat) (k : Z) (w : Word) :
    isKVS b m s ∗
    k ⤇(KVS)[idx] w -∗
    isKVS_open b m s idx ∗
    isKVS_entry b idx (k, w) ∗
    k ⤇(KVS)[idx] w.
  Proof.
    iIntros "( (%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) & Hk)".
    iDestruct (gen_heap_valid with "Hkvs_auth Hk") as "%Hidx'".
    rewrite -{2}(insert_id m idx (k,w)); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame; eauto.
  Qed.

  Lemma isKVS_indom_idx (m : kvs_map) (s : gset (Z*Z)) (a : Addr) (idx : nat) :
    idx ∈ dom m ->
    isKVS a m s -∗
    ⌜ 0 <= idx < SIZE_MAP ⌝.
  Proof.
    iIntros (Hm_idx) "(%Hwf_kvs & _)"; iPureIntro.
    by eapply wf_kvs_indom_idx.
  Qed.

  Lemma isKVS_open_indom_idx (m : kvs_map) (s : gset (Z*Z)) (a : Addr) (idx idx' : nat) :
    idx ∈ dom m ->
    isKVS_open a m s idx' -∗
    ⌜ 0 <= idx < SIZE_MAP ⌝.
  Proof.
    iIntros (Hm_idx) "(%Hwf_kvs & _)"; iPureIntro.
    by eapply wf_kvs_indom_idx.
  Qed.

  Lemma open_isKVS_kvs_frag_idx_diff
    (b : Addr) (m : kvs_map) (s : gset (Z*Z)) (idx idx' : nat) (k : Z) (w : Word):
    0 <= idx' < SIZE_MAP ->
    k ≠ EMPTY_SLOT ->
    idx ≠ idx' ->
    isKVS b m s ∗
    k ⤇(KVS)[ idx ] w -∗
    ∃ k' w',
      ⌜ k ≠ k' ⌝ ∗ ⌜ m !! idx' = Some (k', w') ⌝ ∗
      isKVS_open b m s idx' ∗
      k ⤇(KVS)[ idx ] w ∗
      isKVS_entry b idx' (k', w').
  Proof.
    iIntros (Hidx' Hk_ne_empty Hidx_ne) "( (%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) & Hk)".
    iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hm_idx".
    pose proof (wf_kvs_is_Some _ _ Hwf_kvs Hidx') as [ [k' w'] Hm_idx' ].
    pose proof (wf_kvs_neq _ _ _ _ _ _ _ Hk_ne_empty Hwf_kvs Hidx_ne Hm_idx Hm_idx') as Hkk'.
    iExists k',w'.
    rewrite -{2}(insert_id m idx' (k',w')); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[ [Hkb' Hkw'] HKVS]".
    iFrame "∗%".
  Qed.

  Lemma open_isKVS_not_alloc
    (b : Addr) (m : kvs_map) (s s' : gset (Z*Z))
    (idx : nat) (ku kn : Z) :
    let fkey := kvs_full_key ku kn in
    wf_kvs_full_key ku kn ->
    (0 ≤ idx < SIZE_MAP)%Z →
    (ku, kn) ∉ s' →
    isKVS b m s -∗
    ◯(ALLOC)[ku] s' -∗
    ∃ kidx widx,
      ⌜ kidx ≠ fkey ⌝ ∗
      ⌜ m !! idx = Some (kidx, widx) ⌝ ∗
      isKVS_open b m s idx ∗
      ◯(ALLOC)[ku] s' ∗
      isKVS_entry b idx (kidx, widx).
  Proof.
    intros fkey Hwf_full_key Hidx Hs'.
    iIntros "(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) Hk".
    iDestruct ( allocated_keys_valid with "Halloc Hk" ) as "%Hss'".
    assert (fkey ∉ kvs_keys m) as Hfkey_not_allocated.
    { intro Hcontra; apply (Hwf_alloc (ku, kn)) in Hcontra.
      2: { by cbn. }
      rewrite /kvs_alloc_synced in Hwf_alloc.
      set_solver.
    }
    iFrame.
    assert ( is_Some (m !! idx) ) as [ [kidx widx] Hm_idx].
    { apply wf_kvs_is_Some; auto; lia. }
    rewrite -{1}(insert_id m idx (kidx, widx)); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame "∗%".
    iPureIntro.
    destruct (decide (kidx = EMPTY_SLOT)); simplify_eq.
    - symmetry; apply kvs_full_key_not_empty; done.
    - assert ( kidx ∈ kvs_keys m ) as Hkidx by (apply elem_of_kvs_keys; split; eauto).
      set_solver.
  Qed.

  Lemma open_isKVS
    (b : Addr) (m : kvs_map) (s  : gset (Z*Z))
    (idx : nat) :
    (0 ≤ idx < SIZE_MAP)%Z →
    isKVS b m s -∗
    ∃ kidx widx,
      ⌜ m !! idx = Some (kidx, widx) ⌝ ∗
      isKVS_open b m s idx ∗
      isKVS_entry b idx (kidx, widx).
  Proof.
    intros Hidx.
    iIntros "(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS)".
    iFrame.
    assert ( is_Some (m !! idx) ) as [ [kidx widx] Hm_idx].
    { apply wf_kvs_is_Some; auto; lia. }
    rewrite -{1}(insert_id m idx (kidx, widx)); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame "∗%".
  Qed.

  Lemma close_isKVS
    (b : Addr) (m : kvs_map) (s : gset (Z*Z)) (idx : nat) (k : Z) (w : Word):
    m !! idx = Some (k, w) ->
    isKVS_open b m s idx ∗
    isKVS_entry b idx (k, w) -∗
    isKVS b m s.
  Proof.
    iIntros (Hidx) "[(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) Hkvs_entry]"; cbn.
    iDestruct (big_sepM_delete with "[$HKVS $Hkvs_entry]") as "HKVS"; eauto.
    iFrame; eauto.
  Qed.

  Lemma kvs_alloc_synced_update (m : kvs_map) ( s : gset (Z*Z) ) (idx : nat) (k : Z) (w : Word) :
    (∃ w', m !! idx = Some (k, w')) ->
    kvs_alloc_synced m s ->
    kvs_alloc_synced (<[idx:=(k, w)]> m) s.
  Proof.
    intros [w' Hidx] Halloc.
    rewrite /kvs_alloc_synced.
    intros [ku kn].
    specialize (Halloc (ku, kn)); cbn in *.
    split; intros Hk.
    - apply Halloc in Hk; auto.
      apply elem_of_kvs_keys in Hk as (Hidx' & idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_eq; cbn in *.
      + by eapply elem_of_kvs_keys; split; eauto; eexists idx',_; simplify_map_eq.
      + by eapply elem_of_kvs_keys; split; eauto; eexists idx',_; simplify_map_eq.
    - apply Halloc; auto.
      apply elem_of_kvs_keys in Hk as (Hidx' & idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_eq; cbn in *.
      + by eapply elem_of_kvs_keys; split; eauto; eexists idx',_; simplify_map_eq.
      + by eapply elem_of_kvs_keys; split; eauto; eexists idx',_; simplify_map_eq.
  Qed.

  Lemma isKVS_open_update (a : Addr) (m : kvs_map) (s : gset (Z*Z)) (idx : nat) (k : Z) (w w' : Word) :
    isKVS_open a m s idx -∗ k ⤇(KVS)[ idx ] w
    ==∗
    isKVS_open a (<[idx:=(k, w')]> m) s idx ∗ k ⤇(KVS)[ idx ] w'.
  Proof.
    iIntros "(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) Hk".
    iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hm_idx".
    iMod (kvs_auth_update a m idx _ k _ w' with "Hkvs_auth Hk") as "[$ $]".
    eapply (wf_kvs_map_update _ _ _ w') in Hwf_kvs; eauto.
    eapply (kvs_alloc_synced_update _ _ _ _ w') in Hwf_alloc; eauto.
    rewrite delete_insert_eq.
    by iFrame "∗ %".
  Qed.

  Lemma isKVS_open_insert (a : Addr) (m : kvs_map) (s s' : gset (Z*Z)) (idx : nat) (ku kn : Z) (w : Word) :
    let k := kvs_full_key ku kn in
    (ku, kn) ∉  s' →
    wf_kvs_full_key ku kn ->
    isKVS_open a m s idx -∗
    ◯(ALLOC)[ku] s' -∗
    EMPTY_SLOT ⤇(KVS)[ idx ] (WInt DEFAULT_VAL)
    ==∗
    isKVS_open a (<[idx:=(k, w)]> m) ({[(ku, kn)]} ∪ s) idx ∗
    ◯(ALLOC)[ku] ({[(ku, kn)]} ∪ s') ∗
    k ⤇(KVS)[ idx ] w.
  Proof.
    intro k.
    iIntros (Hs' Hwf_kvs_full_key)
      "(%Hwf_kvs & Hkvs_auth & Halloc_auth & %Hwf_alloc & HKVS) Halloc_frag Hk".
    iDestruct (allocated_keys_valid with "Halloc_auth Halloc_frag") as "->".
    iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hm_idx".
    iMod (kvs_auth_update a m idx _ k _ w with "Hkvs_auth Hk") as "[$ $]".
    iMod ( allocated_keys_insert ku kn with "Halloc_auth Halloc_frag") as "[Halloc_auth Halloc_frag]".
    rewrite /kvs_alloc_synced in Hwf_alloc.
    assert (k ∉ kvs_keys m) as Hk_notin_keys.
    { intro Hcontra; apply Hs'. apply elem_of_filter; cbn in *; split; auto.
      apply Hwf_alloc; cbn; done. }
    eapply (wf_kvs_map_insert _ _ _ w) in Hwf_kvs; eauto.
    eapply (kvs_alloc_synced_insert _ _ _ _ _ w) in Hwf_alloc; eauto.
    rewrite delete_insert_eq.
    subst k.
    by iFrame "∗ %".
  Qed.

End KVS_preamble.
