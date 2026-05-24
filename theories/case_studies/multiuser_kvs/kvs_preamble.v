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
    (* filter (fun k -> k ≠ EMPTY_SLOT) (map_to_list m).*2.*1. *)
    (map_to_list m).*2.*1.

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
    ∀ k, k ∈ s ↔ (kvs_full_key k.1 k.2) ∈ kvs_keys m.

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
    wf_kvs_map m ->
    idx ≠ idx' ->
    m !! idx = Some (k, w) ->
    m !! idx' = Some (k', w') ->
    k ≠ k'.
  Proof.
    intros [_ Hkvs_uniqueness] Hidx_ne Hm_idx Hm_idx'.
    rewrite /kvs_keys in Hkvs_uniqueness.
    rewrite -(insert_id m idx (k, w)) in Hkvs_uniqueness; last done.
    rewrite -insert_delete_eq in Hkvs_uniqueness.
    rewrite -(insert_id (<[idx:=(k, w)]> (delete idx m)) idx' (k', w')) in Hkvs_uniqueness; last by simplify_map_eq.
    rewrite -insert_delete_eq in Hkvs_uniqueness.
    rewrite -(insert_delete_ne _ idx idx') in Hkvs_uniqueness; auto.
    rewrite map_to_list_insert in Hkvs_uniqueness; last by simplify_map_eq.
    rewrite map_to_list_insert in Hkvs_uniqueness; last by simplify_map_eq.
    cbn in Hkvs_uniqueness.
    apply NoDup_cons_1_1 in Hkvs_uniqueness.
    set_solver+Hkvs_uniqueness.
  Qed.

  Lemma elem_of_kvs_keys_1 (m : kvs_map) (k : Z) :
    k ∈ kvs_keys m -> ∃ idx w, m !! idx = Some (k, w).
  Proof.
    intros Hk.
    apply list_elem_of_fmap in Hk as ([k' v'] & ? & Hk); cbn in *; simplify_eq.
    apply list_elem_of_fmap in Hk as ([idx' kv'] & ? & Hk); cbn in *; simplify_eq.
    apply elem_of_map_to_list in Hk.
    eauto.
  Qed.

  Lemma elem_of_kvs_keys_2 (m : kvs_map) (k : Z) :
    (∃ idx w, m !! idx = Some (k, w)) -> k ∈ kvs_keys m.
  Proof.
    intros (idx & w & Hidx).
    apply list_elem_of_fmap; exists (k, w); split; first done.
    apply list_elem_of_fmap; exists (idx, (k, w)); split; first done.
    by apply elem_of_map_to_list.
  Qed.

  Lemma elem_of_kvs_keys (m : kvs_map) (k : Z) :
    k ∈ kvs_keys m ↔ ∃ idx w, m !! idx = Some (k, w).
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
      apply NoDup_cons in Hnodup as [HkX Hnodup].
      apply NoDup_cons; split.
      + rewrite -/(kvs_keys (<[idx:=(k, w')]> m)).
        rewrite -/(kvs_keys m) in HkX.
        intro Hcontra; apply HkX.
        apply elem_of_kvs_keys in Hcontra as (idx0 & w0 & H0).
        apply elem_of_kvs_keys.
        destruct (decide (idx = idx0)); simplify_map_eq; eauto.
      + eapply IHm; eauto.
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
      apply NoDup_singleton.
    }
    destruct (decide (idx = i)); simplify_map_eq.
    - rewrite insert_insert_eq.
      rewrite map_to_list_insert; auto; cbn.
      rewrite map_to_list_insert in Hnodup; auto; cbn in Hnodup.
      rewrite map_to_list_insert in Hk; auto; cbn in Hk.
      apply NoDup_cons in Hnodup as [_ Hnodup].
      apply not_elem_of_cons in Hk as [_ Hk].
      apply NoDup_cons; split; auto.
    - rewrite insert_insert_ne; last done.
      rewrite map_to_list_insert in Hnodup; last done.
      rewrite map_to_list_insert in Hk; last done.
      rewrite map_to_list_insert; last by simplify_map_eq.
      destruct x as [kX vX]; cbn in *.
      apply not_elem_of_cons in Hk as [Hk_ne Hk].
      apply NoDup_cons in Hnodup as [HkX Hnodup].
      apply NoDup_cons; split.
      + rewrite -/(kvs_keys (<[idx:=(k, w)]> m)).
        rewrite -/(kvs_keys m) in HkX.
        intro Hcontra; apply HkX.
        apply elem_of_kvs_keys in Hcontra as (idx0 & w0 & H0).
        apply elem_of_kvs_keys.
        destruct (decide (idx = idx0)); simplify_map_eq; eauto.
      + eapply IHm; eauto.
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
    m !! idx = Some (EMPTY_SLOT, WInt DEFAULT_VAL) ->
    fkey ∉ kvs_keys m ->
    kvs_alloc_synced m s ->
    kvs_alloc_synced (<[idx:=(fkey, w)]> m) ( {[ (ku, kn) ]} ∪ s).
  Proof.
    intros fkey Hidx Hk_free Halloc.
    rewrite /kvs_alloc_synced.
    intros [ku' kn'].
    cbn.
    specialize (Halloc (ku', kn')); cbn in *.
    split; intros Hk.
    - apply elem_of_union in Hk; destruct Hk as [Hk | Hk].
      + apply elem_of_singleton in Hk ; simplify_eq.
        eapply elem_of_kvs_keys.
        by exists idx, w; simplify_map_eq.
      + apply Halloc in Hk.
        apply elem_of_kvs_keys in Hk as (idx' & v' & Hk).
        eapply elem_of_kvs_keys.
        destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
        * admit. (* see kvs_full_key_not_empty *)
        * by eexists idx', v'; simplify_map_eq.
    - apply elem_of_union.
      apply elem_of_kvs_keys in Hk as (idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
      + left. apply elem_of_singleton.
        (* see kvs_full_key_inj *)
      + right.
        apply Halloc.
        by eapply elem_of_kvs_keys; eexists idx',_; simplify_map_eq.
  Admitted.

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
    idx ≠ idx' ->
    isKVS b m s ∗
    k ⤇(KVS)[ idx ] w -∗
    ∃ k' w',
      ⌜ k ≠ k' ⌝ ∗ ⌜ m !! idx' = Some (k', w') ⌝ ∗
      isKVS_open b m s idx' ∗
      k ⤇(KVS)[ idx ] w ∗
      isKVS_entry b idx' (k', w').
  Proof.
    iIntros (Hidx' Hidx_ne) "( (%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) & Hk)".
    iDestruct (kvs_valid with "Hkvs_auth Hk") as "%Hm_idx".
    pose proof (wf_kvs_is_Some _ _ Hwf_kvs Hidx') as [ [k' w'] Hm_idx' ].
    pose proof (wf_kvs_neq _ _ _ _ _ _ _ Hwf_kvs Hidx_ne Hm_idx Hm_idx') as Hkk'.
    iExists k',w'.
    rewrite -{2}(insert_id m idx' (k',w')); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[ [Hkb' Hkw'] HKVS]".
    iFrame; eauto.
  Qed.

  Lemma open_isKVS_not_alloc
    (b : Addr) (m : kvs_map) (s s' : gset (Z*Z))
    (idx : nat) (ku kn : Z) :
    let fkey := kvs_full_key ku kn in
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
    intros fkey Hidx Hs'.
    iIntros "(%Hwf_kvs & Hkvs_auth & Halloc & %Hwf_alloc & HKVS) Hk".
    iDestruct ( allocated_keys_valid with "Halloc Hk" ) as "%Hss'".
    assert (fkey ∉ kvs_keys m) as Hfkey_not_allocated.
    { intro Hcontra; apply (Hwf_alloc (ku, kn)) in Hcontra.
      rewrite /kvs_alloc_synced in Hwf_alloc.
      set_solver. }
    iFrame.
    assert ( is_Some (m !! idx) ) as [ [kidx widx] Hm_idx].
    { apply wf_kvs_is_Some; auto; lia. }
    rewrite -{1}(insert_id m idx (kidx, widx)); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame "∗%".
    iPureIntro.
    assert ( kidx ∈ kvs_keys m ) as Hkidx by (apply elem_of_kvs_keys; eauto).
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
    - apply Halloc in Hk.
      apply elem_of_kvs_keys in Hk as (idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_eq; cbn in *.
      + by eapply elem_of_kvs_keys; eexists idx',_; simplify_map_eq.
      + by eapply elem_of_kvs_keys; eexists idx',_; simplify_map_eq.
    - apply Halloc.
      apply elem_of_kvs_keys in Hk as (idx' & v' & Hk).
      destruct (decide (idx = idx')); simplify_eq; cbn in *.
      + by eapply elem_of_kvs_keys; eexists idx',_; simplify_map_eq.
      + by eapply elem_of_kvs_keys; eexists idx',_; simplify_map_eq.
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
    isKVS_open a m s idx -∗
    ◯(ALLOC)[ku] s' -∗
    EMPTY_SLOT ⤇(KVS)[ idx ] (WInt DEFAULT_VAL)
    ==∗
    isKVS_open a (<[idx:=(k, w)]> m) ({[(ku, kn)]} ∪ s) idx ∗
    ◯(ALLOC)[ku] ({[(ku, kn)]} ∪ s') ∗
    k ⤇(KVS)[ idx ] w.
  Proof.
    intro k.
    iIntros (Hs') "(%Hwf_kvs & Hkvs_auth & Halloc_auth & %Hwf_alloc & HKVS) Halloc_frag Hk".
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

  Lemma KVS_getFullKey_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rsealkey rkey rscratch : RegName)
    (user_key nkey : Z)
    :
    let instrs := (kvs_getFullKey_instrs rsealkey rsealkey rkey rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    (0 <= user_key < top)%Z ->

    rscratch ≠ cnull ->
    rsealkey ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      rsealkey ↦ᵣ kvs_user_seal_key user_key ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch ↦ᵣ - ∗

      cgp_b ↦ₐ kvs_service_unsealing_key ∗
      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
          rsealkey ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
          rkey ↦ᵣ WInt nkey ∗
          rscratch ↦ᵣ kvs_service_unsealing_key ∗

          cgp_b ↦ₐ kvs_service_unsealing_key ∗
          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hbounds_user_key Hrscratch Hrsealkey Hkey)
      "(HPC & Hcgp & Hrsealkey & Hrkey & [%wscratch Hrscratch] & Hcgp_b & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* load rscratch cgp; *)
    iInstr "Hcode".
    { split; done. }
    iEval (cbn) in "Hrscratch".

    (* unseal rdst rsealkey rscratch; *)
    iInstr "Hcode"; first done.
    { rewrite /withinBounds; pose proof KVS_OTYPE_size; solve_addr. }
    (* geta rdst rdst; *)
    iInstr "Hcode".

    (* lshiftl rdst rdst 16; *)
    iInstr "Hcode".
    (* lor rdst rdst rkey *)
    iInstr "Hcode".

    replace (Z.lor ((0 ^+ user_key)%a ≪ 16) nkey) with (kvs_full_key user_key nkey).
    2: {
      replace (@finz.to_z MemNum (0 ^+ user_key)%a) with user_key; first done.
      solve_addr.
    }
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_search_spec_in `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (m : kvs_map) (s : gset (Z*Z)) (idx : nat) (fkey : Z) (w : Word)
    :
    let instrs := (kvs_search_instrs rkey ridx rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (1 + 2*SIZE_MAP)%Z)%a = Some cgp_e)%a ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1 )%a ∗
      rkey ↦ᵣ WInt fkey ∗
      ridx ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      isKVS (cgp_b ^+ 1)%a m s ∗
      fkey ⤇(KVS)[idx] w ∗

      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (1+2*idx) )%a ∗
          rkey ↦ᵣ WInt fkey ∗
          ridx ↦ᵣ WInt idx ∗
          rscratch ↦ᵣ - ∗

          isKVS_open (cgp_b ^+ 1)%a m s idx ∗
          (cgp_b ^+ (1+2*idx))%a ↦ₐ WInt fkey ∗
          (cgp_b ^+ (2+2*idx))%a ↦ₐ w ∗
          isKVS_entry_empty idx fkey ∗

          ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (2 + 2 * idx))%a = true ⌝ ∗

          fkey ⤇(KVS)[idx] w ∗
          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hkey)
      "(HPC & Hcgp & Hrkey & [%widx Hridx] & Hrscratch & HKVS & Hkvs_frag & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* Mov ridx 0 *)
    iInstr "Hcode".

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{1} (_ : (cgp_b ^+ 1)%a = (cgp_b ^+ (1 + 2 * n))%a); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∃ (k : Z) (w : Word),  m !! i = Some (k,w) ∧ k ≠ fkey)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }
    clear Heqn.

    iLöb as "IH" forall (n Hn Hfkey_notin_nfirst).

    (* sub rscratch SIZE_MAP ridx; *)
    iDestruct "Hrscratch" as "[%wrscratch Hrscratch]".
    iInstr "Hcode".
    replace 16 with SIZE_MAP by (by rewrite /SIZE_MAP).
    destruct (decide ((SIZE_MAP - n) = 0)%Z) as [Hneq|Hneq].
    { (* End of the loop. It means that the key wasn't found in the KVS *)
      (* We know that it should be a contradiction, because `fkey⤇(KVS) w`
         witnesses that it exists
       *)
      rewrite Hneq.
      assert ( n = SIZE_MAP ) as -> by lia.

      iDestruct (isKVS_valid with "HKVS Hkvs_frag") as "%Hm_idx".
      iDestruct (isKVS_indom_idx with "HKVS") as "%Hidx".
      { by apply elem_of_dom_2 in Hm_idx. }
      exfalso.
      apply Hfkey_notin_nfirst in Hidx as (k' & w' & Hm_idx' & Hneq_keys).
      rewrite Hm_idx in Hm_idx'; simplify_eq.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

    destruct (decide (Z.of_nat idx = n)%Z) as [<- | Hneq'].
    - iDestruct (open_isKVS_kvs_frag_idx with "[$HKVS $Hkvs_frag]") as "(HKVS & (Hbk & Hbw & Hfkey) & Hkvs_frag)".
      replace ((cgp_b ^+ 1) ^+ 2 * idx)%a  with (cgp_b ^+ (1 + 2 * idx))%a by solve_addr+Hn.
      replace ((cgp_b ^+ 1) ^+ (2 * idx + 1))%a with (cgp_b ^+ (2 + 2 * idx))%a by solve_addr+Hn.
      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done |solve_addr]. }
      (* sub rscratch rkey rscratch; *)
      iInstr "Hcode".
      (* jnz (".not_same_key")%asm rscratch; *)
      replace (fkey - (fkey, w).1)%Z with 0%Z by (cbn;lia).
      iInstr "Hcode".
      (* jmp (".loop_end_found")%asm; *)
      iInstr "Hcode".

      cbn.
      iApply "Hpost"; iFrame.
      iPureIntro; rewrite /withinBounds; solve_addr.

    - iDestruct (open_isKVS_kvs_frag_idx_diff _ _ _ _ (Z.to_nat n) with "[$HKVS $Hkvs_frag]")
        as "(%k' & %w' & %Hkk' & %Hm_idx' & HKVS  & Hkvs_frag & (Hbk & Hbw & Hfkey))".
      { lia. }
      { lia. }
      replace ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a  with (cgp_b ^+ (1 + 2 * n))%a by solve_addr+Hn.
      replace ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a with (cgp_b ^+ (2 + 2 * n))%a by solve_addr+Hn.
      (* load rscratch cgp; *)
      iInstr "Hcode".
      { split; [done | solve_addr]. }
      (* sub rscratch rkey rscratch; *)
      iInstr "Hcode".
      (* jnz (".not_same_key")%asm rscratch; *)
      iInstr "Hcode".
      { injection; cbn; lia. }
      (* lea cgp 2; *)
      iInstr "Hcode".
      { transitivity (Some ( (cgp_b ^+ (1 + 2 * (n+1)))%a)); solve_addr. }
      (* add ridx ridx 1; *)
      iInstr "Hcode".
      (* jmp (".loop_start"); *)
      iInstr "Hcode".
      { transitivity (Some ( (pc_a ^+ 1)%a)); solve_addr. }

      iDestruct (close_isKVS with "[$HKVS Hbk Hbw Hfkey]") as "HKVS";eauto.
      {
        replace (cgp_b ^+ (1 + 2 * n))%a with ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a by solve_addr+Hn.
        replace (cgp_b ^+ (2 + 2 * n))%a  with ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a by solve_addr+Hn.
        iFrame.
      }

      iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hkvs_frag] [$Hpost] [$Hcode] [$HPC] [$Hridx]").
      + iPureIntro; lia.
      + iPureIntro.
        intros idx' Hidx'_bound.
        destruct (decide (idx' = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
        apply Hfkey_notin_nfirst; lia.
  Qed.

  Lemma KVS_search_spec_notin `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (m : kvs_map) (s s' : gset (Z*Z)) (ku kn : Z)
    :
    let instrs := (kvs_search_instrs rkey ridx rscratch) in
    let fkey := kvs_full_key ku kn in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (1 + 2*SIZE_MAP)%Z)%a = Some cgp_e)%a ->
    (ku, kn) ∉ s' ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1 )%a ∗
      rkey ↦ᵣ WInt fkey ∗
      ridx ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      isKVS (cgp_b ^+ 1)%a m s ∗
      ◯(ALLOC)[ku] s' ∗

      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1)%a ∗
          rkey ↦ᵣ WInt fkey ∗
          ridx ↦ᵣ WInt (-1) ∗
          rscratch ↦ᵣ - ∗

          isKVS (cgp_b ^+ 1)%a m s ∗
          ◯(ALLOC)[ku] s' ∗

          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs fkey ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hs' Hrscratch Hridx Hkey)
      "(HPC & Hcgp & Hrkey & [%wridx Hridx] & Hrscratch & HKVS & Halloc & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* Mov ridx 0 *)
    iInstr "Hcode".

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{1} (_ : (cgp_b ^+ 1)%a = (cgp_b ^+ (1 + 2 * n))%a); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∃ (k : Z) (w : Word),  m !! i = Some (k,w) ∧ k ≠ fkey)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }
    clear Heqn.

    iLöb as "IH" forall (n Hn Hfkey_notin_nfirst).

    (* sub rscratch SIZE_MAP ridx; *)
    iDestruct "Hrscratch" as "[%wrscratch Hrscratch]".
    iInstr "Hcode".
    replace 16 with SIZE_MAP by (by rewrite /SIZE_MAP).
    destruct (decide ((SIZE_MAP - n) = 0)%Z) as [Hneq|Hneq].
    { (* End of the loop. *)
      rewrite Hneq.
      assert ( n = SIZE_MAP ) as -> by lia.

      (* jnz (".loop_body")%asm rscratch; *)
      iInstr "Hcode".
      (* jmp (".loop_end_not_found")%asm; *)
      iInstr "Hcode".

      (* lea cgp (-(2*SIZE_MAP))%Z; *)
      iInstr "Hcode".
      { transitivity (Some (cgp_b ^+ 1)%a); rewrite /SIZE_MAP in Hcgp_bound |- *; solve_addr. }
      (* mov ridx (-1)%Z; *)
      iInstr "Hcode".
      rewrite decide_False //=.
      iApply "Hpost"; iFrame.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

  iDestruct (open_isKVS_not_alloc _ _ _ _ (Z.to_nat n) with "HKVS Halloc")
    as "(%kidx' & %widx & %Hkidx_ne & %Hm_kidx & HKVS & Halloc & (Hbk & Hbw & Hfkey))" ; eauto; [lia|].
  replace ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a  with (cgp_b ^+ (1 + 2 * n))%a by solve_addr+Hn.
  replace ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a with (cgp_b ^+ (2 + 2 * n))%a by solve_addr+Hn.

  (* load rscratch cgp; *)
  iInstr "Hcode".
  { split; [done | solve_addr]. }
  (* sub rscratch rkey rscratch; *)
  iInstr "Hcode".
  (* jnz (".not_same_key")%asm rscratch; *)
  iInstr "Hcode".
  { injection; cbn; lia. }
  (* lea cgp 2; *)
  iInstr "Hcode".
  { transitivity (Some ( (cgp_b ^+ (1 + 2 * (n+1)))%a)); solve_addr. }
  (* add ridx ridx 1; *)
  iInstr "Hcode".
  (* jmp (".loop_start"); *)
  iInstr "Hcode".
  { transitivity (Some ( (pc_a ^+ 1)%a)); solve_addr. }

  iDestruct (close_isKVS with "[$HKVS Hbk Hbw Hfkey]") as "HKVS";eauto.
  {
    replace (cgp_b ^+ (1 + 2 * n))%a with ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a by solve_addr+Hn.
    replace (cgp_b ^+ (2 + 2 * n))%a  with ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a by solve_addr+Hn.
    iFrame.
  }

  iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Halloc] [$Hpost] [$Hcode] [$HPC] [$Hridx]").
    + iPureIntro; lia.
    + iPureIntro.
      intros idx' Hidx'_bound.
      destruct (decide (idx' = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
      apply Hfkey_notin_nfirst; lia.
  Qed.

  Lemma KVS_search_spec_empty_slot `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rkey ridx rscratch : RegName)
    (m : kvs_map) (s : gset (Z*Z))
    :
    let instrs := (kvs_search_instrs rkey ridx rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    ((cgp_b + (1 + 2*SIZE_MAP)%Z)%a = Some cgp_e)%a ->

    rscratch ≠ cnull ->
    ridx ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1 )%a ∗
      rkey ↦ᵣ WInt EMPTY_SLOT ∗
      ridx ↦ᵣ - ∗
      rscratch ↦ᵣ - ∗

      isKVS (cgp_b ^+ 1)%a m s ∗

      codefrag pc_a instrs ∗
      ▷ ( (* An empty slot was found*)
          ( ∃ idx_empty_slot : nat,
            (
            PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
            cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ (1+2*idx_empty_slot))%a ∗
            rkey ↦ᵣ WInt EMPTY_SLOT ∗
            ridx ↦ᵣ WInt idx_empty_slot ∗
            rscratch ↦ᵣ - ∗

            isKVS_open (cgp_b ^+ 1)%a m s idx_empty_slot ∗
            (cgp_b ^+ (1+2*idx_empty_slot))%a ↦ₐ WInt EMPTY_SLOT ∗
            (cgp_b ^+ (2+2*idx_empty_slot))%a ↦ₐ WInt DEFAULT_VAL ∗
            EMPTY_SLOT ⤇(KVS)[ idx_empty_slot ] WInt DEFAULT_VAL ∗

            ⌜ withinBounds cgp_b cgp_e (cgp_b ^+ (2 + 2 * idx_empty_slot))%a = true ⌝ ∗
            ⌜ 0 <= idx_empty_slot ⌝ ∗

            codefrag pc_a instrs
            )
          )
          ∨ (* No empty slot found*)
            (
              PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
              cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1)%a ∗
              rkey ↦ᵣ WInt EMPTY_SLOT ∗
              ridx ↦ᵣ WInt (-1) ∗
              rscratch ↦ᵣ - ∗

              isKVS (cgp_b ^+ 1)%a m s ∗

              codefrag pc_a instrs
            ) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hcgp_bound Hrscratch Hridx Hkey)
      "(HPC & Hcgp & Hrkey & [%wridx Hridx] & Hrscratch & HKVS & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* Mov ridx 0 *)
    iInstr "Hcode".

    remember 0%Z as n.
    iAssert (⌜ (0 <= n <= SIZE_MAP)%Z ⌝)%I as "%Hn"; first (iPureIntro ; lia).
    rewrite{1} (_ : (cgp_b ^+ 1)%a = (cgp_b ^+ (1 + 2 * n))%a); last by solve_addr.
    assert (forall i, (0 <= i < Z.to_nat n) -> ∃ (k : Z) (w : Word),  m !! i = Some (k,w) ∧ k ≠ EMPTY_SLOT)
    as Hfkey_notin_nfirst.
    { rewrite Heqn; intros i Hi; lia. }
    clear Heqn.

    iLöb as "IH" forall (n Hn Hfkey_notin_nfirst).

    (* sub rscratch SIZE_MAP ridx; *)
    iDestruct "Hrscratch" as "[%wrscratch Hrscratch]".
    iInstr "Hcode".
    replace 16 with SIZE_MAP by (by rewrite /SIZE_MAP).
    destruct (decide ((SIZE_MAP - n) = 0)%Z) as [Hneq|Hneq].
    { (* End of the loop. *)
      rewrite Hneq.
      assert ( n = SIZE_MAP ) as -> by lia.

      (* jnz (".loop_body")%asm rscratch; *)
      iInstr "Hcode".
      (* jmp (".loop_end_not_found")%asm; *)
      iInstr "Hcode".

      (* lea cgp (-(2*SIZE_MAP))%Z; *)
      iInstr "Hcode".
      { transitivity (Some (cgp_b ^+ 1)%a); rewrite /SIZE_MAP in Hcgp_bound |- *; solve_addr. }
      (* mov ridx (-1)%Z; *)
      iInstr "Hcode".
      rewrite decide_False //=.
      iApply "Hpost"; iRight; iFrame.
    }
    assert (0 ≤ n < SIZE_MAP)%Z as Hn' by lia.
    (* jnz (".loop_body")%asm rscratch; *)
    iInstr "Hcode".
    { by injection. }

  iDestruct (open_isKVS _ _ _ (Z.to_nat n) with "HKVS") as "(%kidx' & %widx & %Hm_kidx & HKVS & (Hbk & Hbw & Hfkey))"
  ; eauto; [lia|].
  replace ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a  with (cgp_b ^+ (1 + 2 * n))%a by solve_addr+Hn.
  replace ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a with (cgp_b ^+ (2 + 2 * n))%a by solve_addr+Hn.
  iEval (cbn) in "Hbk"; iEval (cbn) in "Hbw"; iEval (cbn) in "Hfkey".

  (* load rscratch cgp; *)
  iInstr "Hcode".
  { split; [done | solve_addr]. }
  (* sub rscratch rkey rscratch; *)
  iInstr "Hcode".

  rewrite /isKVS_entry_empty.
  destruct (decide (kidx' = EMPTY_SLOT)) as [Hkidx'_empty |  Hkidx'_empty]; simplify_eq.
  - (* Empty slot found *)
    replace (Z.sub EMPTY_SLOT EMPTY_SLOT) with 0%Z by lia.
    (* jnz (".not_same_key")%asm rscratch; *)
    iInstr "Hcode".
    (* jmp (".loop_end_found")%asm; *)
    iInstr "Hcode".

    iDestruct (isKVS_open_valid with "HKVS Hfkey") as "%Hm_kidx_eq"; simplify_map_eq.
    replace (cgp_b ^+ (1 + 2 * n))%a with (cgp_b ^+ (1 + 2 * Z.to_nat n))%a by solve_addr+Hn.
    replace (cgp_b ^+ (2 + 2 * n))%a  with (cgp_b ^+ (2 + 2 * Z.to_nat n))%a by solve_addr+Hn.


    assert (((Z.of_nat (Z.to_nat n))) = n) as Hn_eq by lia.
    rewrite -{1}Hn_eq.
    iApply "Hpost"; iLeft; iFrame.
    iPureIntro; rewrite /withinBounds; solve_addr.

  - (* Empty slot not found *)

    (* jnz (".not_same_key")%asm rscratch; *)
    iInstr "Hcode".
    { injection; cbn; lia. }
    (* lea cgp 2; *)
    iInstr "Hcode".
    { transitivity (Some ( (cgp_b ^+ (1 + 2 * (n+1)))%a)); solve_addr. }
    (* add ridx ridx 1; *)
    iInstr "Hcode".
    (* jmp (".loop_start"); *)
    iInstr "Hcode".
    { transitivity (Some ( (pc_a ^+ 1)%a)); solve_addr. }

    iDestruct (close_isKVS with "[$HKVS Hbk Hbw Hfkey]") as "HKVS";eauto.
    {
      replace (cgp_b ^+ (1 + 2 * n))%a with ((cgp_b ^+ 1) ^+ 2 * Z.to_nat n)%a by solve_addr+Hn.
      replace (cgp_b ^+ (2 + 2 * n))%a  with ((cgp_b ^+ 1) ^+ (2 * Z.to_nat n + 1))%a by solve_addr+Hn.
      rewrite /isKVS_entry /isKVS_entry_empty /= decide_False //.
      iFrame.
    }

    iApply ("IH" with "[] [] [$Hcgp] [$Hrkey] [$Hrscratch] [$HKVS] [$Hpost] [$Hcode] [$HPC] [$Hridx]").
    + iPureIntro; lia.
    + iPureIntro.
      intros idx' Hidx'_bound.
      destruct (decide (idx' = Z.to_nat n)%Z) as [-> | Hidx']; eauto.
      apply Hfkey_notin_nfirst; lia.
  Qed.

End KVS_preamble.
