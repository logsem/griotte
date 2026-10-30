From iris.proofmode Require Import proofmode.
From griotte Require Export addresses region_keys resources machine_parameters machine_base alloc_registry.

(** * The heap branch of the region map

    A heap key [LHeap a ι] is known when the registry records the range of
    [ι] and [a] lies in it. The region of a heap key holds its usual
    resources, or a tombstone: the witness that [ι] reached quarantine. A
    tombstone holds no cell. *)

Section heap_key_resource.
  Context {Σ : gFunctors} `{!allocRegistryG Σ}.

  Definition heap_key_known (k : LAddr) : iProp Σ :=
    match k with
    | LNonHeap _ => True
    | LHeap a ι => ∃ b e, alloc_obj ι b e ∗ ⌜a ∈ₐ [b, e)⌝
    end%I.

  Definition heap_key_resource (k : LAddr) (P : iProp Σ) : iProp Σ :=
    match k with
    | LNonHeap _ => P
    | LHeap _ ι => P ∨ ι ⊒ AQuar
    end%I.

  #[global] Instance heap_key_known_persistent k : Persistent (heap_key_known k).
  Proof. destruct k; apply _. Qed.

  #[global] Instance heap_key_known_timeless k : Timeless (heap_key_known k).
  Proof. destruct k; apply _. Qed.

  #[global] Instance heap_key_resource_ne k : NonExpansive (heap_key_resource k).
  Proof. intros n P Q HPQ. destruct k; simpl; [done|]. by f_equiv. Qed.

  #[global] Instance heap_key_resource_proper k :
    Proper ((≡) ==> (≡)) (heap_key_resource k).
  Proof. apply ne_proper, _. Qed.

  #[global] Instance heap_key_resource_persistent k (P : iProp Σ) :
    Persistent P → Persistent (heap_key_resource k P).
  Proof. destruct k; apply _. Qed.

  Lemma heap_key_resource_nonheap a (P : iProp Σ) :
    heap_key_resource (LNonHeap a) P ⊣⊢ P.
  Proof. done. Qed.

  Lemma heap_key_resource_intro k (P : iProp Σ) :
    P -∗ heap_key_resource k P.
  Proof. iIntros "HP". destruct k; simpl; [done|by iLeft]. Qed.

  Lemma heap_key_resource_mono k (P Q : iProp Σ) :
    (P -∗ Q) -∗ heap_key_resource k P -∗ heap_key_resource k Q.
  Proof.
    iIntros "HPQ H". destruct k; simpl; [by iApply "HPQ"|].
    iDestruct "H" as "[H|H]"; [iLeft; by iApply "HPQ"|by iRight].
  Qed.

  Lemma heap_key_resource_emp k : ⊢ heap_key_resource k emp.
  Proof. by iApply heap_key_resource_intro. Qed.

  Lemma heap_key_open_cases k (P : iProp Σ) :
    heap_key_resource k P ⊢ P ∨ ∃ a ι, ⌜k = LHeap a ι⌝ ∗ ι ⊒ AQuar.
  Proof.
    destruct k as [a|a ι]; simpl; iIntros "H"; [by iLeft|].
    iDestruct "H" as "[H|#Hq]"; [by iLeft|].
    iRight. iExists a, ι. iSplit; [done|iExact "Hq"].
  Qed.

  Lemma heap_key_close_tomb a ι (P : iProp Σ) :
    ι ⊒ AQuar ⊢ heap_key_resource (LHeap a ι) P.
  Proof. iIntros "Hq". rewrite /heap_key_resource /=. by iRight. Qed.

  (** A tombstone is irrelevant to the resource. *)
  Lemma heap_key_resource_tomb a ι (P Q : iProp Σ) :
    ι ⊒ AQuar -∗ heap_key_resource (LHeap a ι) P -∗ heap_key_resource (LHeap a ι) Q.
  Proof. iIntros "Hq _". by iApply heap_key_close_tomb. Qed.

  (** A live status share rules the tombstone out. *)
  Lemma heap_key_resource_live a ι q (P : iProp Σ) :
    ι ↦st{q} ALive -∗ heap_key_resource (LHeap a ι) P -∗ P ∗ ι ↦st{q} ALive.
  Proof.
    iIntros "Hst [HP|Hq]"; [iFrame|].
    iDestruct (live_quar_false with "Hst Hq") as "[]".
  Qed.

  (** A live status share for every heap key; non-heap keys need none. *)
  Definition heap_key_live_share (k : LAddr) (q : Qp) : iProp Σ :=
    match k with
    | LNonHeap _ => True
    | LHeap _ ι => ι ↦st{q} ALive
    end%I.

  Lemma heap_key_resource_live_share k q (P : iProp Σ) :
    heap_key_live_share k q -∗ heap_key_resource k P -∗ P ∗ heap_key_live_share k q.
  Proof.
    destruct k as [a|a ι]; simpl.
    - by iIntros "_ $".
    - iApply (heap_key_resource_live a).
  Qed.

  Lemma heap_key_known_alloc_obj a ι b e :
    alloc_obj ι b e -∗ ⌜a ∈ₐ [b, e)⌝ -∗ heap_key_known (LHeap a ι).
  Proof. iIntros "#H %Ha". iExists b, e. by iFrame "H". Qed.

  Lemma heap_key_known_nonheap_list (l : list Addr) :
    ⊢ [∗ list] k ∈ LNonHeap <$> l, heap_key_known k.
  Proof. rewrite big_sepL_fmap. by iApply big_sepL_intro. Qed.

  Lemma heap_key_live_share_nonheap_list (l : list Addr) q :
    ⊢ [∗ list] k ∈ LNonHeap <$> l, heap_key_live_share k q.
  Proof. rewrite big_sepL_fmap. by iApply big_sepL_intro. Qed.

End heap_key_resource.

Section key_pointsto_known.
  Context {Σ : gFunctors} `{!allocRegistryG Σ, !gen_heapGS Addr LWord Σ}.

  Lemma key_pointsto_known k v :
    k ↦ₖ v -∗ heap_key_known k.
  Proof.
    destruct k as [a|a ι]; simpl; first by iIntros.
    iIntros "[_ (%b & %e & %Hin & #Hobj & _)]". iExists b, e. by iFrame "Hobj".
  Qed.

End key_pointsto_known.
