From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import ghost_map.
From iris.algebra Require Import gmap_view.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import switcher kvs.


Definition user_key_t := Z.
Definition map_key_t := Z.
Definition full_key_t := Z.
Definition kvs_idx_t := nat.

Definition kvs_physical_entry : Type := option (full_key_t * Word).
Definition kvs_dom : gset nat := set_seq 0 SIZE_MAP.
Definition kvs_physical_map : Type := gmap kvs_idx_t kvs_physical_entry.


Section KVS_physical_map.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
  .

  Definition kvs_keys (pkvs : kvs_physical_map) : list full_key_t :=
    map_fold (
        (fun _ opt_kv acc =>
           match opt_kv with
           | None => acc
           | Some kv => (fst kv)::acc
           end
        )
      )
      []
      pkvs.

  Definition wf_kvs_physical_map (pkvs : kvs_physical_map) : Prop :=
    dom pkvs = kvs_dom ∧ NoDup (kvs_keys pkvs).

  Definition option_pair_ASM_Some (k : full_key_t) (w : Word) :=
    [ WInt ASM_SOME; WInt k; w].
  Definition option_pair_ASM_None (wuk wmk : Word) :=
    [ WInt ASM_NONE; wuk; wmk].

  Definition option_pair_ASM (opt_kw : kvs_physical_entry) (wuk wmk : Word) :=
    match opt_kw with
    | None => option_pair_ASM_None wuk wmk
    | Some (k, w) => option_pair_ASM_Some k w
    end.

  Definition physical_kvs_entry
    (a : Addr) (idx : kvs_idx_t) (opt_kw : kvs_physical_entry) : iProp Σ :=
    let a_opt_idx := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx))%a in
    let a_opt_idx_next := (a ^+ (ASM_SIZEOF_KVS_ENTRY * idx + ASM_SIZEOF_KVS_ENTRY))%a in
    ∃ (wuk wmk : Word),
      [[ a_opt_idx, a_opt_idx_next ]] ↦ₐ [[ option_pair_ASM opt_kw wuk wmk ]].

  Definition physical_kvs_entry' (a : Addr) (idx : kvs_idx_t) (opt_kw : kvs_physical_entry) : iProp Σ :=
    let a_opt := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx))%a in
    let a_key := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx+1))%a in
    let a_val := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx+2))%a in
    ( a_opt ↦ₐ ( match opt_kw with | None => WInt ASM_NONE | Some _ => WInt ASM_SOME end ) ) ∗
    ( match opt_kw with
      | None =>       a_key ↦ₐ -
      | Some (k,_) => a_key ↦ₐ WInt k
      end ) ∗
    ( match opt_kw with
      | None =>       a_val ↦ₐ -
      | Some (_,w) => a_val ↦ₐ w
      end).

  Definition physical_kvs_entry_some' (a : Addr) (idx : kvs_idx_t) (k : full_key_t) (w : Word) : iProp Σ :=
    let a_opt := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx))%a in
    let a_key := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx+1))%a in
    let a_val := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx+2))%a in
    ( a_opt ↦ₐ WInt ASM_SOME ∗
      a_key ↦ₐ WInt k ∗
      a_val ↦ₐ w).

  Definition physical_kvs_entry_none' (a : Addr) (idx : kvs_idx_t) : iProp Σ :=
    let a_opt := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx))%a in
    let a_key := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx+1))%a in
    let a_val := (a ^+ (ASM_SIZEOF_KVS_ENTRY*idx+2))%a in
    ( a_opt ↦ₐ WInt ASM_NONE ∗
      a_key ↦ₐ - ∗
      a_val ↦ₐ -).

  Lemma destruct_physical_kvs_entry_some (a : Addr) (idx : kvs_idx_t) (k : full_key_t) (w : Word) :
  (a ^+ ASM_SIZEOF_KVS_ENTRY * idx + ASM_SIZEOF_KVS_ENTRY)%a
  = Some (a ^+ (ASM_SIZEOF_KVS_ENTRY * idx + ASM_SIZEOF_KVS_ENTRY))%a
    ->

    physical_kvs_entry a idx (Some (k, w)) ⊣⊢ physical_kvs_entry_some' a idx k w.
  Proof.
    intros H.
    iSplit; iIntros "H".
    - iDestruct "H" as "(%&%&H)".
      iDestruct (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+1))%a with "H") as
        "[$ H]"; try solve_addr.
      iDestruct (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+2))%a with "H") as
        "[$ H]"; try solve_addr.
      iDestruct (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+3))%a with "H") as
        "[$ H]"; try solve_addr.
    - iDestruct "H" as "(?&?&?)".
      iExists (WInt 0), (WInt 0).
      iApply (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+1))%a)
      ; [solve_addr | solve_addr | iFrame].
      iApply (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+2))%a)
      ; [solve_addr | solve_addr | iFrame].
      iApply (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+3))%a)
      ; [solve_addr | solve_addr | iFrame].
      rewrite /region_pointsto.
      rewrite finz_seq_between_empty; done.
  Qed.

  Lemma destruct_physical_kvs_entry_None (a : Addr) (idx : kvs_idx_t) :
    (a ^+ ASM_SIZEOF_KVS_ENTRY * idx + ASM_SIZEOF_KVS_ENTRY)%a
    = Some (a ^+ (ASM_SIZEOF_KVS_ENTRY * idx + ASM_SIZEOF_KVS_ENTRY))%a
    ->

      physical_kvs_entry a idx None ⊣⊢ physical_kvs_entry_none' a idx.
  Proof.
    intros H.
    iSplit; iIntros "H".
    - iDestruct "H" as "(%&%&H)".
      iDestruct (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+1))%a with "H") as
        "[$ H]"; try solve_addr.
      iDestruct (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+2))%a with "H") as
        "[$ H]"; try solve_addr.
      iDestruct (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+3))%a with "H") as
        "[$ H]"; try solve_addr.
    - iDestruct "H" as "( ? & [%wuk ?] & [%wmk ?] )".
      iExists wuk, wmk.
      iApply (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+1))%a)
      ; [solve_addr | solve_addr | iFrame].
      iApply (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+2))%a)
      ; [solve_addr | solve_addr | iFrame].
      iApply (region_pointsto_cons _ (a ^+ ((ASM_SIZEOF_KVS_ENTRY * idx)+3))%a)
      ; [solve_addr | solve_addr | iFrame].
      rewrite /region_pointsto.
      rewrite finz_seq_between_empty; done.
  Qed.

  Lemma destruct_physical_kvs_entry (a : Addr) (idx : kvs_idx_t) (opt_kw : kvs_physical_entry) :
  (a ^+ ASM_SIZEOF_KVS_ENTRY * idx + ASM_SIZEOF_KVS_ENTRY)%a
  = Some (a ^+ (ASM_SIZEOF_KVS_ENTRY * idx + ASM_SIZEOF_KVS_ENTRY))%a
    ->

    physical_kvs_entry a idx opt_kw ⊣⊢ physical_kvs_entry' a idx opt_kw.
  Proof.
    intros H.
    destruct opt_kw as [ [k w] |]; cbn.
    - rewrite destruct_physical_kvs_entry_some; auto.
    - rewrite destruct_physical_kvs_entry_None; auto.
  Qed.

  Definition is_physical_kvs (a : Addr) (pkvs : kvs_physical_map) : iProp Σ :=
    ⌜ wf_kvs_physical_map pkvs ⌝ ∗ [∗ map] idx ↦ opt_kw ∈ pkvs, physical_kvs_entry a idx opt_kw.

  Definition is_physical_kvs_open
    (a : Addr) (pkvs : kvs_physical_map) (open_idx : kvs_idx_t) : iProp Σ :=
    ⌜ wf_kvs_physical_map pkvs ⌝ ∗
    [∗ map] idx ↦ opt_kw ∈ (delete open_idx pkvs), physical_kvs_entry a idx opt_kw.

  Lemma is_physical_kvs_wf (a : Addr) (pkvs : kvs_physical_map) :
    is_physical_kvs a pkvs -∗ ⌜ wf_kvs_physical_map pkvs ⌝.
  Proof. iIntros "[$ _]". Qed.

  Lemma is_physical_kvs_open_wf (a : Addr) (pkvs : kvs_physical_map) (idx : kvs_idx_t) :
    is_physical_kvs_open a pkvs idx -∗ ⌜ wf_kvs_physical_map pkvs ⌝.
  Proof. iIntros "[$ _]". Qed.

  Lemma wf_kvs_indom_idx (pkvs : kvs_physical_map) (idx : kvs_idx_t) :
    idx ∈ dom pkvs ->
    wf_kvs_physical_map pkvs ->
    0 <= idx < SIZE_MAP.
  Proof.
    intros Hm_idx [Hkvs_dom _].
    rewrite Hkvs_dom /kvs_dom in Hm_idx.
    apply elem_of_set_seq in Hm_idx.
    lia.
  Qed.

  Lemma wf_kvs_is_Some (pkvs : kvs_physical_map) (idx : kvs_idx_t)  :
    wf_kvs_physical_map pkvs ->
    0 <= idx < SIZE_MAP ->
    is_Some (pkvs !! idx).
  Proof.
    intros [Hkvs_dom _] Hidx.
    apply elem_of_dom.
    rewrite Hkvs_dom /kvs_dom.
    by apply elem_of_set_seq.
  Qed.

  Lemma kvs_physical_map_indom_idx (pkvs : kvs_physical_map) (a : Addr) (idx : kvs_idx_t) :
    idx ∈ dom pkvs ->
    is_physical_kvs a pkvs -∗
    ⌜ 0 <= idx < SIZE_MAP ⌝.
  Proof.
    iIntros (Hm_idx) "(%Hwf_kvs & _)"; iPureIntro.
    by eapply wf_kvs_indom_idx.
  Qed.

  Lemma kvs_physical_map_open_in
    (a : Addr) (pkvs : kvs_physical_map)
    (idx : kvs_idx_t) (k : full_key_t) (w : Word) :

    pkvs !! idx = Some (Some (k, w)) ->

    is_physical_kvs a pkvs -∗
    is_physical_kvs_open a pkvs idx ∗ physical_kvs_entry a idx (Some (k, w)).
  Proof.
    iIntros (Hpkvs_idx) "[%Hwf_pkvs HKVS]".
    rewrite -{1}(insert_id pkvs idx (Some (k,w))); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[$ HKVS]".
    iFrame; eauto.
  Qed.

  Global Instance Permutation_Reflexive {A} : Reflexive (@Permutation A).
  Proof. intros l ; done. Qed.

  Global Instance Permutation_Transitive {A} : Transitive (@Permutation A).
  Proof. intros l1 l2 l3 Hl12 Hl23; eapply Permutation_trans; done. Qed.

  Global Instance Permutation_PreOrder {A} : PreOrder (@Permutation A).
  Proof. split; apply _. Qed.

  Local Instance Proper_get_kvs_key (opt_kv : kvs_physical_entry) :
  Proper (Permutation ==> Permutation)
    (λ acc : list full_key_t, match opt_kv with
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

  Lemma wf_kvs_neq (pkvs : kvs_physical_map) (idx idx' : nat) (k k' : full_key_t) (w w' : Word) :
    wf_kvs_physical_map pkvs ->
    idx ≠ idx' ->
    pkvs !! idx = Some (Some (k, w)) ->
    pkvs !! idx' = Some (Some (k', w')) ->
    k ≠ k'.
  Proof.
    intros [_ Hkvs_uniqueness] Hidx_ne Hm_idx Hm_idx'.
    rewrite -(insert_id pkvs idx (Some (k, w))) in Hkvs_uniqueness; last done.
    rewrite -insert_delete_eq in Hkvs_uniqueness.
    rewrite kvs_keys_insert_Some in Hkvs_uniqueness; last by simplify_map_eq.
    rewrite -(insert_id (delete idx pkvs) idx' (Some (k', w'))) in Hkvs_uniqueness; last by simplify_map_eq.
    rewrite -insert_delete_eq in Hkvs_uniqueness.
    rewrite kvs_keys_insert_Some in Hkvs_uniqueness; last by simplify_map_eq.
    apply NoDup_cons in Hkvs_uniqueness as [Hk _ ].
    apply not_elem_of_cons in Hk as [ HK _ ].
    done.
  Qed.

  Lemma kvs_physical_map_open_neq
    (a : Addr) (pkvs : kvs_physical_map) (idx idx' : nat) (k : full_key_t) (w : Word):
    pkvs !! idx = Some (Some (k, w)) ->
    0 <= idx' < SIZE_MAP ->
    idx ≠ idx' ->
    is_physical_kvs a pkvs -∗
    ∃ opt_kw',
      is_physical_kvs_open a pkvs idx' ∗
      ⌜ pkvs !! idx' = Some opt_kw' ⌝ ∗
      physical_kvs_entry a idx' opt_kw' ∗
      ⌜ match opt_kw' with | Some kw' => k ≠ kw'.1 | None => True end ⌝.
  Proof.
    iIntros (Hpkvs_idx Hidx' Hidx_ne) "[%Hwf_kvs HKVS]".
    pose proof (wf_kvs_is_Some _ _ Hwf_kvs Hidx') as [ opt_kw' Hm_idx' ].
    iExists opt_kw'.
    rewrite -{1}(insert_id pkvs idx' opt_kw'); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[ Hk' HKVS]".
    iFrame "∗%".
    iPureIntro.
    destruct opt_kw' as [ [k' w'] |]; auto.
    pose proof (wf_kvs_neq _ _ _ _ _ _ _ Hwf_kvs Hidx_ne Hpkvs_idx Hm_idx') as Hkk'.
    done.
  Qed.


  Lemma kvs_physical_map_close
    (a : Addr) (pkvs : kvs_physical_map) (idx : kvs_idx_t) (opt_kwidx : kvs_physical_entry):
    pkvs !! idx = Some opt_kwidx ->

    is_physical_kvs_open a pkvs idx -∗
    physical_kvs_entry a idx opt_kwidx -∗
    is_physical_kvs a pkvs.
  Proof.
    iIntros (Hidx) "[%Hwf_kvs HKVS] Hentry"; cbn.
    iDestruct (big_sepM_delete with "[$HKVS $Hentry]") as "HKVS"; eauto.
    iFrame; eauto.
  Qed.

  Lemma kvs_keys_empty : kvs_keys ∅ = [].
  Proof. rewrite /kvs_keys map_fold_empty; done. Qed.

  Definition kvs_elem_of_kvs (pkvs : kvs_physical_map) (k : full_key_t) ( w : Word ) :=
    (∃ idx, pkvs !! idx = Some (Some (k, w))).
  Lemma elem_of_kvs_keys_1 (pkvs : kvs_physical_map) (k : full_key_t) :
    k ∈ kvs_keys pkvs -> (∃ w, kvs_elem_of_kvs pkvs k w).
  Proof.
    move: k.
    induction pkvs using map_ind ; intros k Hk.
    { rewrite kvs_keys_empty in Hk; set_solver+Hk. }
    destruct x as [ [k' w'] |].
    - rewrite kvs_keys_insert_Some in Hk; auto.
      apply elem_of_cons in Hk as [ -> | Hk].
      + exists w', i ; simplify_map_eq; done.
      + apply IHpkvs in Hk.
        destruct Hk as (w & idx & Hidx).
        exists w, idx.
        assert (i ≠ idx) by (intro; simplify_map_eq;done).
        simplify_map_eq; done.
    - rewrite kvs_keys_insert_None in Hk; auto.
      apply IHpkvs in Hk.
      destruct Hk as (w & idx & Hidx).
      exists w, idx.
      assert (i ≠ idx) by (intro; simplify_map_eq;done).
      simplify_map_eq; done.
  Qed.

  Lemma elem_of_kvs_keys_2 (pkvs : kvs_physical_map) (k : full_key_t) :
    (∃ w, kvs_elem_of_kvs pkvs k w) ->
    k ∈ kvs_keys pkvs.
  Proof.
    intros (w & idx & Hidx).
    rewrite -(insert_id pkvs idx (Some (k, w))); last done.
    rewrite -insert_delete_eq.
    rewrite kvs_keys_insert_Some; last by simplify_map_eq.
    apply elem_of_cons; by left.
  Qed.

  Lemma elem_of_kvs_keys (pkvs : kvs_physical_map) (k : full_key_t) :
    k ∈ kvs_keys pkvs ↔ (∃ w, kvs_elem_of_kvs pkvs k w).
  Proof. split ; [apply elem_of_kvs_keys_1 | apply elem_of_kvs_keys_2]. Qed.

  Lemma kvs_physical_map_open_notin
    (a : Addr) (pkvs : kvs_physical_map)
    (idx : kvs_idx_t) (uk : user_key_t) (mk : map_key_t) :
    let fkey := kvs_full_key uk mk in
    is_uint16 mk ->
    (0 ≤ idx < SIZE_MAP)%Z →
    fkey ∉ kvs_keys pkvs ->
    is_physical_kvs a pkvs -∗
    ∃ opt_kwidx,
      ⌜ pkvs !! idx = Some opt_kwidx ⌝ ∗
      is_physical_kvs_open a pkvs idx ∗
      physical_kvs_entry a idx opt_kwidx ∗
      ⌜ match opt_kwidx with | Some kwidx => kwidx.1 ≠ fkey | None => True end ⌝.
  Proof.
    intros fkey Hwf_full_key Hidx Hs'.
    iIntros "[%Hwf_kvs HKVS]".
    assert ( is_Some (pkvs !! idx) ) as [ opt_kwidx Hm_idx].
    { apply wf_kvs_is_Some; auto; lia. }
    rewrite -{1}(insert_id pkvs idx opt_kwidx); last done.
    iDestruct (big_sepM_insert_delete with "HKVS") as "[Hkvs_entry HKVS]".
    iFrame "∗%".
    iPureIntro.
    destruct opt_kwidx as [ [ kidx widx ]|]; auto.
    cbn.
    assert ( kidx ∈ kvs_keys pkvs ) as Hkidx; last set_solver.
    apply elem_of_kvs_keys; eexists _,_; eauto.
  Qed.

  Lemma NoDup_kvs_keys_update
    (pkvs : kvs_physical_map) (idx : kvs_idx_t) (k : full_key_t) (w w' : Word) :
    pkvs !! idx = Some (Some (k, w)) ->
    NoDup (kvs_keys pkvs) ->
    NoDup (kvs_keys (<[idx := Some (k, w') ]>pkvs)).
  Proof.
    move: idx k w w'.
    induction pkvs using map_ind; intros idx k w w' Hk Hnodup; first simplify_map_eq.
    destruct (decide (idx = i)); simplify_map_eq.
    - rewrite insert_insert_eq.
      rewrite kvs_keys_insert_Some; auto.
      rewrite kvs_keys_insert_Some in Hnodup; auto.
    - rewrite insert_insert_ne; last done.
      destruct x as [ [k' w''] |].
      + rewrite kvs_keys_insert_Some in Hnodup; auto.
        rewrite kvs_keys_insert_Some; simplify_map_eq; auto.
        apply NoDup_cons in Hnodup as [HkX Hnodup].
        apply NoDup_cons; split; last (eapply IHpkvs; eauto).
        intro Hcontra.
        apply elem_of_kvs_keys in Hcontra as (w0 & idx0 & H0).
        apply HkX.
        apply elem_of_kvs_keys; auto.
        destruct (decide (idx = idx0)); simplify_map_eq.
        { exists w, idx0; done. }
        { exists w0, idx0; done. }
      + rewrite kvs_keys_insert_None in Hnodup; auto.
        rewrite kvs_keys_insert_None; simplify_map_eq; auto.
        eapply IHpkvs; eauto.
  Qed.

  Lemma wf_kvs_physical_map_update
    (pkvs : kvs_physical_map) (idx : kvs_idx_t) (k : full_key_t) (w : Word) :
    (∃ w', pkvs !! idx = Some (Some (k, w'))) ->
    wf_kvs_physical_map pkvs ->
    wf_kvs_physical_map (<[idx:= Some (k, w)]> pkvs).
  Proof.
    intros [w' Hidx] (Hkvs_dom & Hkvs_unique).
    split.
    - rewrite dom_insert_L -Hkvs_dom.
      assert (idx ∈ dom pkvs).
      { apply elem_of_dom; eauto. }
      set_solver.
    - eapply NoDup_kvs_keys_update; eauto.
  Qed.

  Lemma kvs_physical_map_close_update
    (a : Addr) (pkvs : kvs_physical_map) (idx : kvs_idx_t) (k : full_key_t) (w : Word):
    (∃ w' : Word, pkvs !! idx = Some (Some (k, w'))) ->

    is_physical_kvs_open a pkvs idx -∗
    physical_kvs_entry a idx (Some (k,w)) -∗
    is_physical_kvs a (<[idx:= Some (k,w)]> pkvs).
  Proof.
    iIntros (Hidx) "[%Hwf_kvs HKVS] Hentry"; cbn.
    iDestruct (big_sepM_insert_delete with "[$HKVS $Hentry]") as "HKVS"; eauto.
    iFrame; eauto.
    iPureIntro.
    eapply wf_kvs_physical_map_update; eauto.
  Qed.

  Lemma NoDup_kvs_keys_insert_Some
    (pkvs : kvs_physical_map) (idx : kvs_idx_t) (k : full_key_t) (w : Word) :
    k ∉ kvs_keys pkvs ->
    NoDup (kvs_keys pkvs) ->
    NoDup (kvs_keys (<[idx:= Some (k, w)]> pkvs)).
  Proof.
    move: idx k w.
    induction pkvs using map_ind; intros idx k w Hk Hnodup.
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
        destruct Hcontra as (w0&idx0&Hcontra).
        destruct (decide (idx0 = idx)); simplify_map_eq.
        apply Hk'.
        apply elem_of_kvs_keys.
        eexists _,_;eauto.
      + rewrite kvs_keys_insert_None in Hnodup; auto.
        rewrite kvs_keys_insert_None in Hk; auto.
        rewrite kvs_keys_insert_None; simplify_map_eq; auto.
  Qed.

  Lemma wf_kvs_physical_map_insert
    (pkvs : kvs_physical_map) (idx : kvs_idx_t) (k : full_key_t) (w : Word) :
    pkvs !! idx = Some None ->
    k ∉ kvs_keys pkvs ->
    wf_kvs_physical_map pkvs ->
    wf_kvs_physical_map (<[idx:= Some (k, w)]> pkvs).
  Proof.
    intros Hidx Hk (Hkvs_dom & Hkvs_unique).
    split.
    - rewrite dom_insert_L -Hkvs_dom.
      assert (idx ∈ dom pkvs).
      { apply elem_of_dom; eauto. }
      set_solver.
    - eapply NoDup_kvs_keys_insert_Some; eauto.
  Qed.

  Lemma kvs_physical_map_close_insert
    (a : Addr) (pkvs : kvs_physical_map) (idx : kvs_idx_t) (k : full_key_t) (w : Word):
    pkvs !! idx = Some None ->
    k ∉ kvs_keys pkvs ->

    is_physical_kvs_open a pkvs idx -∗
    physical_kvs_entry a idx (Some (k,w)) -∗
    is_physical_kvs a (<[idx:= Some (k,w)]> pkvs).
  Proof.
    iIntros (Hidx Hk) "[%Hwf_kvs HKVS] Hentry"; cbn.
    iDestruct (big_sepM_insert_delete with "[$HKVS $Hentry]") as "HKVS"; eauto.
    iFrame; eauto.
    iPureIntro.
    eapply wf_kvs_physical_map_insert; eauto.
  Qed.

  Lemma NoDup_kvs_keys_delete
    (pkvs : kvs_physical_map) (idx : kvs_idx_t)  :
    NoDup (kvs_keys pkvs) ->
    NoDup (kvs_keys (<[idx:=None]> pkvs)).
  Proof.
    generalize dependent idx.
    induction pkvs using map_ind; intros idx Hnodup; first simplify_map_eq.
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
        intro Hk. apply elem_of_kvs_keys in Hk as (?&idx_k&?); simplify_eq.
        destruct (decide (idx_k = idx)); simplify_map_eq.
        apply Hk'.
        apply elem_of_kvs_keys; eexists _,_ ; eauto.
      + rewrite kvs_keys_insert_None in Hnodup; auto.
        rewrite kvs_keys_insert_None; simplify_map_eq; auto.
  Qed.

  Lemma wf_kvs_physical_map_delete (pkvs : kvs_physical_map) (idx : kvs_idx_t) :
    (is_Some (pkvs !! idx)) ->
    wf_kvs_physical_map pkvs ->
    wf_kvs_physical_map (<[idx:=None]> pkvs).
  Proof.
    intros [w' Hidx] (Hkvs_dom & Hkvs_unique).
    split.
    - rewrite dom_insert_L -Hkvs_dom.
      assert (idx ∈ dom pkvs).
      { apply elem_of_dom; eauto. }
      set_solver.
    - eapply NoDup_kvs_keys_delete; eauto.
  Qed.

  Lemma kvs_physical_map_close_delete
    (a : Addr) (pkvs : kvs_physical_map) (idx : kvs_idx_t) :
    is_Some (pkvs !! idx) ->

    is_physical_kvs_open a pkvs idx -∗
    physical_kvs_entry a idx None -∗
    is_physical_kvs a (<[idx:= None ]> pkvs).
  Proof.
    iIntros (Hidx) "[%Hwf_kvs HKVS] Hentry"; cbn.
    iDestruct (big_sepM_insert_delete with "[$HKVS $Hentry]") as "HKVS"; eauto.
    iFrame; eauto.
    iPureIntro.
    eapply wf_kvs_physical_map_delete; eauto.
  Qed.

End KVS_physical_map.


Definition kvs_user_map : Type := gmap map_key_t Word.
Definition kvs_logical_map : Type := gmap user_key_t kvs_user_map.

(* CMRA for KVS *)
Class kvsLogicalG Σ :=
  LogicalKvsG {
      kvs_logical_genG :: gen_heapGS user_key_t kvs_user_map Σ;
    }.

Notation "'↪●LKVS' lkvs" :=
  ( gen_heap_interp (L:=user_key_t) (V:= kvs_user_map) lkvs )%I (at level 20) : bi_scope.
Notation "uk '↦(LKVS)[' dq ']' m" :=
  (pointsto (L:=user_key_t) (V:= kvs_user_map) uk dq m)%I (at level 20) : bi_scope.
Notation "uk '↦(LKVS)' m" :=
  (uk ↦(LKVS)[ (DfracOwn 1) ] m)%I (at level 20) : bi_scope.

Lemma kvs_logical_kvs_valid `{kvsLogicalG}
  (uk : user_key_t) (lkvs : kvs_logical_map) (m : kvs_user_map) :
  ↪●LKVS lkvs  -∗ uk ↦(LKVS) m -∗ ⌜ lkvs !! uk = Some m ⌝.
Proof.
  iIntros "Hauth Hfrag".
  by iDestruct (gen_heap_valid with "Hauth Hfrag") as "%Hvalid".
Qed.

Lemma kvs_logical_kvs_update `{kvsLogicalG}
  (uk : user_key_t) (lkvs : kvs_logical_map) (m m' : kvs_user_map) :
  ↪●LKVS lkvs -∗ uk ↦(LKVS) m
  ==∗
  ↪●LKVS (<[uk := m']> lkvs) ∗ uk ↦(LKVS) m'.
Proof.
  iIntros "Hauth Hfrag".
  by iMod (gen_heap_update lkvs uk _ m' with "Hauth Hfrag") as "[$ $]".
Qed.


Section KVS_logical_map.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvslogicalg:kvsLogicalG Σ}
    `{MP: MachineParameters}
  .


  Definition kvs_elem_of_logical_kvs
    (lkvs : kvs_logical_map) (uk : user_key_t) (mk : map_key_t) ( w : Word ) :=
    (∃ ukvs, lkvs !! uk = Some ukvs ∧  ukvs !! mk = Some w).

  Definition kvs_synced_logical_kvs (pkvs : kvs_physical_map) (lkvs : kvs_logical_map) : Prop :=
    ∀ (k : user_key_t * map_key_t) (w : Word),
    is_uint16 k.2 ->
    ( kvs_elem_of_logical_kvs lkvs k.1 k.2 w ↔ kvs_elem_of_kvs pkvs (kvs_full_key k.1 k.2) w).

  Definition is_logical_kvs (a : Addr) (lkvs : kvs_logical_map) : iProp Σ :=
    ∃ (pkvs : kvs_physical_map),
      ⌜ kvs_synced_logical_kvs pkvs lkvs ⌝ ∗ is_physical_kvs a pkvs.

  Definition logical_kvs_inv (a : Addr) : iProp Σ :=
      ∃ (lkvs : kvs_logical_map), ↪●LKVS lkvs ∗ (is_logical_kvs a lkvs).


  Lemma kvs_synced_logical_lookup_Some
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map) (m : kvs_user_map)
    (uk : user_key_t) (mk : map_key_t) (w : Word) :
    let fkey := kvs_full_key uk mk in
    is_uint16 mk ->
    kvs_synced_logical_kvs pkvs lkvs ->
    lkvs !! uk = Some m ->
    m !! mk = Some w ->
    ∃ idx, pkvs !! idx = Some (Some (fkey, w)).
  Proof.
    rewrite /kvs_synced_logical_kvs.
    intros Huint16_mk Hsync Hlkvs_uk Hm_mk.
    specialize (Hsync (uk,mk) w Huint16_mk); cbn in *.
    apply Hsync.
    eexists; split; eauto.
  Qed.

  Lemma kvs_synced_logical_lookup_None
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map) (m : kvs_user_map)
    (uk : user_key_t) (mk : map_key_t) :
    let fkey := kvs_full_key uk mk in
    is_uint16 mk ->
    kvs_synced_logical_kvs pkvs lkvs ->
    lkvs !! uk = Some m ->
    m !! mk = None ->
    fkey ∉ kvs_keys pkvs.
  Proof.
    rewrite /kvs_synced_logical_kvs.
    intros Huint16_mk Hsync Hlkvs_uk Hm_mk.
    intros Hcontra.
    apply elem_of_kvs_keys in Hcontra as (w & Hcontra).
    specialize (Hsync (uk,mk) w Huint16_mk); cbn in *.
    apply Hsync in Hcontra as (m'&Hm'&Hcontra); simplify_map_eq.
  Qed.


  Definition kvs_logical_kvs_insert
    (lkvs : kvs_logical_map) (uk : user_key_t) (mk : map_key_t) (w : Word) :=
   <[uk := (<[ mk := w ]> (default ∅ (lkvs !! uk))) ]> lkvs.

  Notation "<<[ ( uk , mk ) := w ]>> lkvs" :=
    (kvs_logical_kvs_insert lkvs uk mk w) (at level 10).

  Lemma kvs_logical_kvs_insert_lookup_eq
    (lkvs : kvs_logical_map) (uk : user_key_t) (mk : map_key_t) (w : Word) (m : kvs_user_map) :
    (<<[ ( uk, mk ) := w ]>> lkvs) !! uk = Some m ->
    m = <[mk := w]> (default ∅ (lkvs !! uk)).
  Proof.
    intros H.
    rewrite /kvs_logical_kvs_insert in H; simplify_map_eq.
    done.
  Qed.

  Lemma kvs_logical_kvs_insert_lookup_ne
    (lkvs : kvs_logical_map) (uk uk' : user_key_t) (mk : map_key_t) (w : Word) (m : kvs_user_map) :
    uk ≠ uk' ->
    (<<[ ( uk, mk ) := w ]>> lkvs) !! uk' = Some m ->
    lkvs !! uk' = Some m.
  Proof.
    intros Hk H.
    rewrite /kvs_logical_kvs_insert in H; simplify_map_eq.
    done.
  Qed.

  Lemma NoDup_kvs_keys_elem_of m idx uk mk w idx' uk' mk' w' :
    let f := kvs_full_key uk mk in
    let f' := kvs_full_key uk' mk' in
    NoDup (kvs_keys m) ->
    idx ≠ idx' ->
    m !! idx = Some (Some (f, w)) ->
    m !! idx' = Some (Some (f', w')) ->
    uk' ≠ uk ∨ mk' ≠ mk.
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
        destruct (decide (uk' = uk)); simplify_eq; [right|left]; auto.
        destruct (decide (mk' = mk)); simplify_eq; auto.
      + destruct (decide (idx' = i)); simplify_map_eq.
        * (* idx ≠ i ∧ idx' = i *)
          assert (f ∈ kvs_keys m) as Hf.
          { apply elem_of_kvs_keys; eexists _,_; eauto. }
          destruct (decide (uk' = uk)); simplify_eq; [right|left]; auto.
          destruct (decide (mk' = mk)); simplify_eq; auto.
        * (* idx ≠ i ∧ idx' ≠ i *)
          eapply IHm; eauto.
  Qed.

  Lemma kvs_synced_logical_kvs_update
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map)
    (idx : kvs_idx_t)
    (uk : user_key_t) (mk : map_key_t) (w : Word) :
    let k := kvs_full_key uk mk in
    NoDup (kvs_keys pkvs) ->
    is_uint16 mk ->
    (∃ w', pkvs !! idx = Some ( Some (k, w'))) ->
    kvs_synced_logical_kvs pkvs lkvs ->
    kvs_synced_logical_kvs (<[idx:= Some (k, w)]> pkvs) (<<[ ( uk, mk ) := w ]>> lkvs).
  Proof.
    intros k.
    intros Hnodup Hwf [w' Hidx] Halloc [ku kn] w'' Hwf'.
    specialize (Halloc (ku, kn) w'' Hwf'); cbn in *.
    split; intros Hk.
    - rewrite /kvs_elem_of_logical_kvs in Hk.
      destruct Hk as (umap & Hlm & Hkn).
      destruct (decide (ku = uk)); simplify_map_eq.
      + apply kvs_logical_kvs_insert_lookup_eq in Hlm; simplify_eq.
        destruct (decide (kn = mk)); simplify_map_eq.
        * eexists idx; simplify_map_eq; done.
        * assert ( kvs_elem_of_kvs pkvs (kvs_full_key uk kn) w'' ) as (idx'&?).
          { apply Halloc. eexists;split;eauto.
            destruct (lkvs !! uk) eqn:Hlkvs; try (rewrite Hlkvs in Hkn); cbn in * ; simplify_eq.
            set_solver.
          }
          eexists idx'.
          destruct (decide (idx = idx')); simplify_map_eq; cbn in *.
          ** rewrite Hidx in H; simplify_map_eq.
             apply kvs_full_key_inj in H as [? ?]; eauto; simplify_eq.
          ** by simplify_map_eq.
      + apply kvs_logical_kvs_insert_lookup_ne in Hlm; simplify_eq; auto.
        assert ( kvs_elem_of_logical_kvs lkvs ku kn w'') as Hk'.
        { eexists ; split; eauto. }
        eapply Halloc in Hk' as (idx' & Hk).
        destruct (decide (idx = idx')); simplify_map_eq; cbn in *.
        ** rewrite Hidx in Hk; simplify_map_eq.
           apply kvs_full_key_inj in Hk as [? ?]; eauto; simplify_eq.
        ** by eexists idx'; simplify_map_eq.
    - destruct Hk as (idx' & Hk).
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *.
      + apply kvs_full_key_inj in Hk as [? ?]; eauto; simplify_eq.
        rewrite /kvs_elem_of_logical_kvs /kvs_logical_kvs_insert.
        destruct (lkvs !! ku) as [umap|] eqn:Humap ; simplify_map_eq.
        * by eexists; split; eauto; simplify_map_eq.
        * by eexists; split; eauto; simplify_map_eq.
      + assert ( kvs_elem_of_logical_kvs lkvs ku kn w'' ) as (umap&Hlm&Hkn).
        { apply Halloc; eexists; eauto. }
        rewrite /kvs_elem_of_logical_kvs /kvs_logical_kvs_insert.
        destruct (decide (uk = ku)); simplify_map_eq; cycle 1.
        * eexists; split; eauto.
        * destruct (decide (kn = mk)); simplify_map_eq.
          ** eexists; split; eauto.
             subst k.
             eapply (NoDup_kvs_keys_elem_of pkvs idx ku mk _ idx' ku mk) in Hnodup; eauto.
             destruct Hnodup as [|]; done.
          ** by eexists; split; eauto; simplify_map_eq.
  Qed.

  Local Lemma kvs_synced_logical_kvs_insert_1
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map)
    (idx : kvs_idx_t)
    (uk uk' : user_key_t) (mk mk' : map_key_t) (w w' : Word) :
    let fkey := kvs_full_key uk mk in
    is_uint16 mk ->
    pkvs !! idx = Some None ->
    kvs_synced_logical_kvs pkvs lkvs ->
    is_uint16 mk' ->
    kvs_elem_of_logical_kvs (<<[ ( uk, mk ) := w ]>> lkvs) uk' mk' w' ->
    kvs_elem_of_kvs (<[idx:= Some (fkey, w)]> pkvs) (kvs_full_key uk' mk') w'.
  Proof.
    intros fkey Hwf_full_key Hidx Halloc Hwf_full_key' Hk.
    destruct Hk as (umap & Huk' & Hmk').
    destruct (decide (uk = uk')); simplify_map_eq.
    - apply kvs_logical_kvs_insert_lookup_eq in Huk'; simplify_map_eq.
      destruct (decide (mk' = mk)) as [Hmk_eq | Hmk_eq]; simplify_map_eq.
      + eexists idx; simplify_map_eq; done.
      + specialize (Halloc (uk', mk') w' Hwf_full_key'); cbn in *.
        rewrite /kvs_elem_of_logical_kvs in Halloc.
        destruct ( lkvs !! uk' ) as [umap_uk|] eqn:Hlkvs; try (rewrite Hlm in Hmk'); last set_solver+Hmk'.
        cbn in Hmk'.
        assert (∃ umap : kvs_user_map, Some umap_uk = Some umap
                                       ∧ umap !! mk' = Some w') as IH.
        { exists umap_uk; split; auto. }
        apply Halloc in IH.
        destruct IH as (idx' & Hk).
        destruct (decide (idx = idx')); simplify_map_eq; cbn in *; eauto.
        by eexists idx'; simplify_map_eq.
    - apply kvs_logical_kvs_insert_lookup_ne in Huk'; auto; simplify_map_eq.
      assert (∃ umap : kvs_user_map, lkvs !! uk' = Some umap ∧ umap !! mk' = Some w') as IH.
      { exists umap; split; auto. }
      specialize (Halloc (uk', mk') w' Hwf_full_key'); cbn in *.
      rewrite /kvs_elem_of_logical_kvs in Halloc.
      apply Halloc in IH.
      destruct IH as (idx' & Hk).
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
      by eexists idx'; simplify_map_eq.
  Qed.

  Local Lemma kvs_synced_logical_kvs_insert_2
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map)
    (idx : kvs_idx_t)
    (uk uk' : user_key_t) (mk mk' : map_key_t) (w w' : Word) :
    let fkey := kvs_full_key uk mk in
    is_uint16 mk ->
    pkvs !! idx = Some None ->
    fkey ∉ kvs_keys pkvs ->
    kvs_synced_logical_kvs pkvs lkvs ->
    is_uint16 mk' ->
    kvs_elem_of_kvs (<[idx:= Some (fkey, w)]> pkvs) (kvs_full_key uk' mk') w' ->
    kvs_elem_of_logical_kvs (<<[ ( uk, mk ) := w ]>> lkvs) uk' mk' w'.
  Proof.
    intros fkey Hwf_full_key Hidx Hkfree Halloc Hwf_full_key' Hk.
    specialize (Halloc (uk', mk') w' Hwf_full_key') as IH.
    destruct Hk as (idx' & Hk).
    destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
    - apply kvs_full_key_inj in Hk as [ -> -> ]; eauto.
      rewrite /kvs_logical_kvs_insert;simplify_map_eq.
      rewrite /kvs_elem_of_logical_kvs;simplify_map_eq.
      exists (<[mk':=w']> (default ∅ (lkvs !! uk'))); split; auto.
      by simplify_map_eq.
    - rewrite /kvs_logical_kvs_insert;simplify_map_eq.
      rewrite /kvs_elem_of_logical_kvs;simplify_map_eq.
      assert ( kvs_elem_of_kvs pkvs (kvs_full_key uk' mk') w' ) as IHm.
      { eexists; eauto. }
      destruct (decide (uk = uk')); simplify_map_eq.
      + destruct (decide (mk = mk')); simplify_map_eq.
        * apply (iffLRn (elem_of_kvs_keys pkvs fkey)) in Hkfree.
          exfalso; apply Hkfree; eexists _,_; eauto.
        * apply IH in IHm as (umap & Humap & Humap').
          by eexists ; split; eauto; simplify_map_eq.
      + apply IH in IHm as (umap & Humap & Humap').
        eexists ; split; eauto.
  Qed.

  Lemma kvs_synced_logical_kvs_insert
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map)
    (idx : kvs_idx_t)
    (uk : user_key_t) (mk : map_key_t) (w : Word) :
    let fkey := kvs_full_key uk mk in
    is_uint16 mk ->
    pkvs !! idx = Some None ->
    fkey ∉ kvs_keys pkvs ->
    kvs_synced_logical_kvs pkvs lkvs ->
    kvs_synced_logical_kvs (<[idx:=Some (fkey, w)]> pkvs) (<<[ ( uk, mk ) := w ]>> lkvs).
  Proof.
    intros fkey Hwf_full_key Hidx Hk_free Halloc.
    intros [uk' mk'] Hwf_full_key'.
    cbn.
    split; intros Hk.
    - eapply kvs_synced_logical_kvs_insert_1; eauto.
    - eapply kvs_synced_logical_kvs_insert_2; eauto.
  Qed.


  Definition kvs_logical_kvs_delete
    (lkvs : kvs_logical_map) (uk : user_key_t) (mk : map_key_t) :=
    <[uk := (delete mk (default ∅ (lkvs !! uk))) ]> lkvs.

  Notation "lkvs <∖> ( uk , mk )" :=
    (kvs_logical_kvs_delete lkvs uk mk) (at level 10).

  Lemma kvs_logical_kvs_delete_lookup_eq
    (lkvs : kvs_logical_map) (uk : user_key_t) (mk : map_key_t) (m : kvs_user_map) :
    (lkvs <∖> (uk, mk)) !! uk = Some m ->
    m = delete mk (default ∅ (lkvs !! uk)).
  Proof.
    intros H.
    rewrite /kvs_logical_kvs_delete in H; simplify_map_eq.
    done.
  Qed.

  Lemma kvs_logical_kvs_delete_lookup_ne
    (lkvs : kvs_logical_map) (uk uk' : user_key_t) (mk : map_key_t) (m : kvs_user_map) :
    uk ≠ uk' ->
    (lkvs <∖> (uk, mk)) !! uk' = Some m ->
    lkvs !! uk' = Some m.
  Proof.
    intros Hk H.
    rewrite /kvs_logical_kvs_delete in H; simplify_map_eq.
    done.
  Qed.

  Local Lemma kvs_synced_logical_kvs_delete_1
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map)
    (idx : kvs_idx_t)
    (uk uk' : user_key_t) (mk mk' : map_key_t) (w w' : Word) :
    let fkey := kvs_full_key uk mk in
    is_uint16 mk ->
    pkvs !! idx = Some (Some (fkey, w)) ->
    kvs_synced_logical_kvs pkvs lkvs ->
    is_uint16 mk' ->
    kvs_elem_of_logical_kvs (lkvs <∖> (uk, mk)) uk' mk' w' ->
    kvs_elem_of_kvs (<[idx:= None]> pkvs) (kvs_full_key uk' mk') w'.
  Proof.
    intros fkey Hwf_full_key Hidx Halloc Hwf_full_key' Hk.
    destruct Hk as (umap & Huk' & Hmk').
    destruct (decide (uk = uk')); simplify_map_eq.
    - apply kvs_logical_kvs_delete_lookup_eq in Huk'; simplify_map_eq.
      assert ( mk ≠ mk' ) as Hmk_eq ; simplify_map_eq.
      { intro; simplify_map_eq. }
        destruct ( lkvs !! uk' ) as [umap_uk|] eqn:Hlm; try (rewrite Hlm in Hmk') ; last set_solver+Hmk'.
      cbn in *.
      assert ( kvs_elem_of_logical_kvs lkvs uk' mk' w') as Helem.
      { eexists; split;eauto. }
      specialize (Halloc (uk', mk') w' Hwf_full_key'); cbn in *.
      apply Halloc in Helem as (idx'&Hidx').
      eexists idx'.
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
      rewrite Hidx in Hidx'; simplify_map_eq.
      apply kvs_full_key_inj in Hidx' as [_ ->]; eauto; done.
    - apply kvs_logical_kvs_delete_lookup_ne in Huk'; auto; simplify_map_eq.
      assert (∃ umap : kvs_user_map, lkvs !! uk' = Some umap ∧ umap !! mk' = Some w') as IH.
      { exists umap; split; auto. }
      apply (Halloc (uk', mk') w' Hwf_full_key') in IH as (idx'&Hidx').
      destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
      * rewrite Hidx in Hidx'; simplify_map_eq.
        apply kvs_full_key_inj in Hidx' as [-> ->] ;eauto; done.
      * by exists idx'; simplify_map_eq.
  Qed.

  Local Lemma kvs_synced_logical_kvs_delete_2
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map)
    (idx : kvs_idx_t)
    (uk uk' : user_key_t) (mk mk' : map_key_t) (w w' : Word) :
    let fkey := kvs_full_key uk mk in
    is_uint16 mk ->
    pkvs !! idx = Some (Some (fkey, w)) ->
    NoDup (kvs_keys pkvs) ->
    kvs_synced_logical_kvs pkvs lkvs ->
    is_uint16 mk' ->
    kvs_elem_of_kvs (<[idx:= None]> pkvs) (kvs_full_key uk' mk') w' ->
    kvs_elem_of_logical_kvs (lkvs <∖> (uk, mk)) uk' mk' w'.
  Proof.
    intros fkey Hwf_full_key Hidx Hnodup Halloc Hwf_full_key' Hk.
    specialize (Halloc (uk', mk') w' Hwf_full_key') as IH'.
    cbn in *.
    destruct Hk as (idx' & Hk).

    destruct (decide (idx = idx')); simplify_map_eq; cbn in *; auto.
    assert (kvs_elem_of_kvs pkvs (kvs_full_key uk' mk') w') as IHm'.
    { eexists; eauto. }

    apply IH' in IHm' as (umap' & Humap' & Hmk'_in_umap').
    assert (kvs_full_key uk mk ∈ kvs_keys pkvs) as IHm.
    { apply elem_of_kvs_keys; eexists _,_; eauto. }
    rewrite /kvs_logical_kvs_delete.
    destruct (decide (uk = uk')); simplify_map_eq; cycle 1.
    { exists umap'; split; simplify_map_eq;eauto. }
    eexists (delete mk umap'); split; simplify_map_eq; eauto.
    destruct (decide (mk = mk')); simplify_map_eq; try done.

    eapply (NoDup_kvs_keys_elem_of pkvs idx uk' mk' _ idx' uk' mk') in Hnodup; eauto.
    destruct Hnodup as [ | ]; done.
  Qed.

  Lemma kvs_synced_logical_kvs_delete
    (pkvs : kvs_physical_map) (lkvs : kvs_logical_map)
    (idx : kvs_idx_t)
    (uk : user_key_t) (mk : map_key_t) (w : Word) :
    let fkey := kvs_full_key uk mk in
    NoDup (kvs_keys pkvs) ->
    is_uint16 mk ->
    pkvs !! idx = Some (Some (fkey, w)) ->
    kvs_synced_logical_kvs pkvs lkvs ->
    kvs_synced_logical_kvs (<[idx:=None]> pkvs) (lkvs <∖> (uk, mk)).
  Proof.
    intros fkey Hnodup Hwf_full_key Hidx Halloc.
    intros [uk' mk'] Hwf_full_key'.
    cbn.
    split; intros Hk.
    - eapply (kvs_synced_logical_kvs_delete_1 pkvs lkvs idx uk uk' mk mk'); eauto.
    - eapply (kvs_synced_logical_kvs_delete_2 pkvs lkvs idx uk uk' mk mk'); eauto.
  Qed.


End KVS_logical_map.

Class kvsUserG Σ :=
  UserKvsG {
      kvs_user_genG :: ghost_mapG Σ map_key_t (option Word);
      γkvs_user : user_key_t -> gname;
    }.

Notation "uk '↪●UKVS' ukvs" :=
  ( ghost_map_auth (K:=map_key_t) (V:= option Word) (γkvs_user uk) 1%Qp ukvs)%I (at level 20) : bi_scope.
Notation "k '↦(UKVS)[' dq ']' o" :=
  ( ghost_map_elem (K:=map_key_t) (V:= option Word) (γkvs_user k.1) k.2 dq o)%I (at level 20) : bi_scope.
Notation "k '↦(UKVS)' o" :=
  (k ↦(UKVS)[ (DfracOwn 1) ] o)%I (at level 20) : bi_scope.

Notation "k '↦(KVS)' w" :=
  (k ↦(UKVS) (Some w))%I (at level 20) : bi_scope.
Notation "k '↦(KVS)' -" :=
  (∃ w, k ↦(KVS) w)%I (at level 20) : bi_scope.
Notation "k '↦(KVS)' ⊥" :=
  (k ↦(UKVS) None)%I (at level 20) : bi_scope.

Definition kvs_logical_user_map : Type := gmap map_key_t (option Word).

Lemma kvs_user_kvs_valid `{kvsUserG}
  (uk : user_key_t) (mk : map_key_t) (ukvs : kvs_logical_user_map ) (o : option Word) :
  uk ↪●UKVS ukvs  -∗ (uk,mk) ↦(UKVS) o -∗ ⌜ ukvs !! mk = Some o ⌝.
Proof.
  iIntros "Hauth Hfrag".
  by iDestruct (ghost_map_lookup with "Hauth Hfrag") as "%Hvalid".
Qed.

Lemma kvs_user_kvs_update `{kvsUserG}
  (uk : user_key_t) (mk : map_key_t) (ukvs : kvs_logical_user_map) (o o' : option Word) :
  uk ↪●UKVS ukvs -∗ (uk,mk) ↦(UKVS) o
  ==∗
  uk ↪●UKVS (<[mk := o']> ukvs) ∗ (uk,mk) ↦(UKVS) o'.
Proof.
  iIntros "Hauth Hfrag".
  by iMod (ghost_map_update o' with "Hauth Hfrag") as "[$ $]".
Qed.


Section KVS_user_map.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvslogicalg:kvsLogicalG Σ}
    {kvsuserg:kvsUserG Σ}
    `{MP: MachineParameters}
  .

  Definition kvs_synced_logical_user_kvs
    (m : kvs_user_map) (ukvs : kvs_logical_user_map) : Prop :=
    forall (mk : map_key_t),
    is_Some (ukvs !! mk) <-> (ukvs !! mk) = Some (m !! mk).

  Definition is_logical_user_kvs (uk : user_key_t) (ukvs : kvs_logical_user_map) : iProp Σ :=
    ∃ (m : kvs_user_map),
      uk ↦(LKVS) m ∗
      ⌜ kvs_synced_logical_user_kvs m ukvs ⌝.


  Lemma kvs_synced_logical_user_kvs_Some
    (m : kvs_user_map) (ukvs : kvs_logical_user_map) (uk : user_key_t) (w : Word) :
    kvs_synced_logical_user_kvs m ukvs ->
    ukvs !! uk = Some (Some w) ->
    m !! uk = Some w.
  Proof.
    intros Hsync Hukvs.
    specialize (Hsync uk) as [Hsync _].
    ospecialize (Hsync _); eauto.
    rewrite Hsync in Hukvs; simplify_eq; first done.
  Qed.

  Lemma kvs_synced_logical_user_kvs_None
    (m : kvs_user_map) (ukvs : kvs_logical_user_map) (uk : user_key_t) :
    kvs_synced_logical_user_kvs m ukvs ->
    ukvs !! uk = Some None ->
    m !! uk = None.
  Proof.
    intros Hsync Hukvs.
    specialize (Hsync uk) as [Hsync _].
    ospecialize (Hsync _); eauto.
    rewrite Hsync in Hukvs; simplify_eq; first done.
  Qed.

  Lemma kvs_synced_logical_user_kvs_insert
    (m : kvs_user_map) (ukvs : kvs_logical_user_map) (uk : user_key_t) (w : Word) :
    kvs_synced_logical_user_kvs m ukvs ->
    kvs_synced_logical_user_kvs (<[uk:=w]> m) ( <[uk:=Some w]> ukvs ).
  Proof.
    intros Hsync uk'; split.
    - intros [wuk Hukvs].
      destruct (decide (uk = uk')); simplify_map_eq; first done.
      specialize (Hsync uk') as [Hsync _].
      ospecialize (Hsync _); eauto.
      rewrite Hsync in Hukvs; simplify_eq; first done.
    - intros Hukvs.
      destruct (decide (uk = uk')); simplify_map_eq; first done.
      done.
  Qed.

  Lemma kvs_synced_logical_user_kvs_delete
    (m : kvs_user_map) (ukvs : kvs_logical_user_map) (uk : user_key_t) :
    kvs_synced_logical_user_kvs m ukvs ->
    kvs_synced_logical_user_kvs (delete uk m) ( <[uk:=None]> ukvs ).
  Proof.
    intros Hsync uk'; split.
    - intros [wuk Hukvs].
      destruct (decide (uk = uk')); simplify_map_eq; first done.
      specialize (Hsync uk') as [Hsync _].
      ospecialize (Hsync _); eauto.
      rewrite Hsync in Hukvs; simplify_eq; first done.
    - intros Hukvs.
      destruct (decide (uk = uk')); simplify_map_eq; first done.
      done.
  Qed.

End KVS_user_map.


Class kvsG Σ :=
  KvsG {
      kvs_logicalG :: kvsLogicalG Σ;
      kvs_userG :: kvsUserG Σ;
    }.


Section KVS_init.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvsg:kvsG Σ}
    `{MP: MachineParameters}
  .

  Lemma NoDup_kvs_keys_insert_None
    (pkvs : kvs_physical_map) (idx : kvs_idx_t) :
    pkvs !! idx = None ->
    NoDup (kvs_keys pkvs) ->
    NoDup (kvs_keys (<[idx:= None]> pkvs)).
  Proof.
    intros Hidx Hnodup.
    rewrite kvs_keys_insert_None; auto.
  Qed.

  Definition kvs_physical_map_init : kvs_physical_map :=
    list_to_map ((fun n => (n, None)) <$> (seq 0 SIZE_MAP)).

  Lemma wf_kvs_physical_map_kvs_physical_map_init : wf_kvs_physical_map kvs_physical_map_init.
  Proof.
    rewrite /kvs_physical_map_init /wf_kvs_physical_map /kvs_dom.
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

  Lemma kvs_keys_map_init : kvs_keys kvs_physical_map_init ≡ₚ [].
  Proof.
    rewrite /kvs_physical_map_init.
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

  Lemma kvs_not_elem_of_kvs_physical_map_init_lookup k w :
    ¬ (kvs_elem_of_kvs kvs_physical_map_init k w).
  Proof.
    intros Hkvs.
    cbn in Hkvs.
    rewrite /kvs_elem_of_kvs in Hkvs.
    destruct Hkvs as [idx Hkvs].
    repeat (destruct idx; simplify_map_eq).
  Qed.

  Lemma kvs_alloc_synced_map_init (lkvs : kvs_logical_map) :
    (∀ (uk : user_key_t) (m : kvs_user_map),
       lkvs !! uk = Some m -> m = ∅) ->
    kvs_synced_logical_kvs kvs_physical_map_init lkvs.
  Proof.
    intros Hm.
    intros [uk mk] w Hwf_k; cbn in *.
    split; intros Hkvs; exfalso.
    - destruct Hkvs as (m & Huk & Hm_uk).
      apply Hm in Huk; set_solver.
    - eapply kvs_not_elem_of_kvs_physical_map_init_lookup; eauto.
  Qed.

  Lemma elem_of_kvs_physical_map_init (idx : nat) (opt_kv : kvs_physical_entry) :
    kvs_physical_map_init !! idx = Some opt_kv -> opt_kv = None.
  Proof.
    intros Hidx.
    rewrite /kvs_physical_map_init in Hidx.
    apply elem_of_list_to_map_2 in Hidx.
    apply list_elem_of_fmap in Hidx as (n&?&Hidx); simplify_eq.
    done.
  Qed.

  Lemma kvs_initial_map_init (b e : Addr) :
    (b + (ASM_SIZEOF_KVS_ENTRY * SIZE_MAP))%a = Some e ->
    ([[b,e]]↦ₐ[[kvs_data]]) -∗
    [∗ map] idx↦kw ∈ kvs_physical_map_init, physical_kvs_entry b idx kw.
  Proof.
    rewrite /kvs_physical_map_init /kvs_data.
    generalize dependent e.
    replace b with (b^+(ASM_SIZEOF_KVS_ENTRY*0%nat))%a by solve_addr.
    rewrite {3}(_ : (b^+(ASM_SIZEOF_KVS_ENTRY*0%nat))%a = b); last solve_addr.
    generalize 0 as k.
    induction SIZE_MAP; iIntros (k e Hbe) "Hmem"; cbn; first done.

    specialize (IHn (S k)).
    iApply big_sepM_insert.
    { apply not_elem_of_list_to_map.
      intro Hcontra.
      apply list_elem_of_fmap in Hcontra as ([idx opt_kw ] & ? & Hcontra); simplify_eq.
      apply list_elem_of_fmap in Hcontra as (k' & ? & Hcontra); simplify_eq.
      apply elem_of_seq in Hcontra; cbn in *.
      lia.
    }

    replace (WInt ASM_NONE :: WInt EMPTY_SLOT :: WInt DEFAULT_VAL :: _)
      with (
       [WInt ASM_NONE ; WInt EMPTY_SLOT ; WInt DEFAULT_VAL] ++
         (repeat_list [WInt ASM_NONE; WInt EMPTY_SLOT; WInt DEFAULT_VAL] n)
      ) by done.

    iDestruct (region_pointsto_split
                 (b ^+ ASM_SIZEOF_KVS_ENTRY * k)%a _ (b ^+ ((ASM_SIZEOF_KVS_ENTRY * k)+ASM_SIZEOF_KVS_ENTRY))%a
                 with "Hmem") as "[Hasm_idx Hmem]"
    ; [ solve_addr+Hbe | symmetry; apply finz_incr_iff_dist; solve_addr+Hbe | ].

    iSplitL "Hasm_idx".
    - iFrame.
    - iApply (IHn (b ^+ (ASM_SIZEOF_KVS_ENTRY * (k + (S n))))%a with "[Hmem]"); first solve_addr+Hbe.
      replace (b ^+ ASM_SIZEOF_KVS_ENTRY * S k)%a with (b ^+ (ASM_SIZEOF_KVS_ENTRY * k + ASM_SIZEOF_KVS_ENTRY))%a by solve_addr.
      replace e with (b ^+ ASM_SIZEOF_KVS_ENTRY * (k + S n))%a by solve_addr.
      done.
  Qed.

End KVS_init.

Class kvs_namespaces :=
  {
    Nkvs : namespace;
    Nkvs_user : namespace;
    Nkvs_otype : namespace;
    Nkvs_exp_tbl : namespace;
    Nkvs_namespaces_disjoint :
    Nkvs ## Nkvs_otype ∧
    Nkvs ## Nkvs_exp_tbl ∧
    Nkvs ## Nkvs_user ∧
    Nkvs_user ## Nkvs_otype ∧
    Nkvs_user ## Nkvs_exp_tbl ∧
    Nkvs_otype ## Nkvs_exp_tbl
  }.


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

  Definition kvs_otype_inv
    {KVS_layout : kvsLayout}
    (W : WORLD) (C : CmptName) (w : Word) : iProp Σ :=
    ∃ (uk : user_key_t) (a : Addr) (m : kvs_user_map),
      (* Shape of the capability*)
      ⌜ w = WSealable (kvs_user_seal_key_scap Global a) ⌝ ∗
      ⌜ withinBounds a (a^+1)%a a = true ⌝ ∗
      (* Payload contains the user key *)
      a ↦ₐ WInt uk ∗
      (* KVS resources *)
      uk ↦(LKVS) m ∗
      ([∗ map] mk↦w ∈ m, (∀ W' , ⌜ related_sts_priv_world W W' ⌝ -∗ interp W' C w )
      ).

  Program Definition kvs_otype_prop
    {KVS_layout : kvsLayout} :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ):=
    λne (W : WORLD) (C : CmptName) (w : Word), (kvs_otype_inv W C w)%I.
  Solve All Obligations with solve_proper.

  Definition kvs_otype_propC {KVS : kvsLayout} : WORLD * CmptName * leibnizO Word -> iProp Σ :=
    safeC kvs_otype_prop.

  Lemma mono_priv_ot_kvs {KVS : kvsLayout} (C : CmptName) (w : Word) :
    ⊢ future_priv_mono C kvs_otype_propC w.
  Proof.
    iIntros (W W' Hrelated_W_W').
    iModIntro.
    iIntros "Hot_kvs".
    rewrite /kvs_otype_propC /= /kvs_otype_inv.
    iDestruct "Hot_kvs" as "(%ku & %a & %s & % & % & ? & ? & Hs)".
    iExists ku, a, s; iFrame "∗%".
    iApply (big_sepM_impl with "Hs").
    iModIntro; iIntros (???) "H".
    iIntros (W'' Hrelated_W'_W'').
    iApply "H".
    iPureIntro.
    by eapply related_sts_priv_trans_world.
  Qed.

  Definition kvs_inv {KVS : kvsLayout} : iProp Σ :=
    let imports :=
      kvs_imports b_switcher e_switcher a_switcher_call ot_switcher
    in
      [[ KVS_pcc_b , KVS_pcc_b' ]] ↦ₐ [[ imports ]] ∗
      codefrag KVS_pcc_b' kvs_service_instrs ∗
      logical_kvs_inv KVS_cgp_b ∗
      seal_pred KVS_OTYPE kvs_otype_propC.

  Definition logical_user_kvs_inv (uk : user_key_t) : iProp Σ :=
    ∃ (ukvs : kvs_logical_user_map),
      uk ↪●UKVS ukvs ∗ is_logical_user_kvs uk ukvs.

End KVS_preamble.

Global Opaque kvs_physical_map_init.

Notation "<<[ ( uk , mk ) := w ]>> lkvs" :=
  (kvs_logical_kvs_insert lkvs uk mk w) (at level 10).

Notation "lkvs <∖> ( uk , mk )" :=
  (kvs_logical_kvs_delete lkvs uk mk) (at level 10).
