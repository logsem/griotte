From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode logrel.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte Require Export seal_registry.

(** Sealing predicate of [AllocOtype]. Every capability sealed with the
    allocator's otype is an allocator capability on a static word, recorded
    in the allocator's registry for one compartment. The registry's
    invariant exclusively owns that word and the matching owner token, so an
    allocator capability is valid in one compartment only. The allocator
    specifications consume both and give them back, so the registry is
    opened around a call and closed again right after it. *)

Definition Nallocator_otype : namespace := nroot .@ "allocator_otype".

Section AllocatorOtype.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    {seal_registryg : sealRegistryG LAddr Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout}
  .

  (** Each identifier recorded for an owner is either quarantined, or its
      right to be freed is held by the sealing predicate. It does not depend
      on the world. *)
  Definition allocator_owned_rights (Ω : gset AId) : iProp Σ :=
    [∗ set] ι ∈ Ω, (ι ⊒ AQuar ∨ free_right ι).

  #[global] Instance allocator_owned_rights_timeless Ω :
    Timeless (allocator_owned_rights Ω).
  Proof. rewrite /allocator_owned_rights. apply _. Qed.

  (** A fresh allocation comes with its right to be freed. *)
  Lemma allocator_owned_rights_insert (Ω : gset AId) (ι : AId) :
    ι ∉ Ω ->
    allocator_owned_rights Ω -∗
    free_right ι -∗
    allocator_owned_rights (Ω ∪ {[ι]}).
  Proof.
    iIntros (Hι) "Hrights Hright".
    rewrite /allocator_owned_rights union_comm_L big_sepS_insert //.
    iFrame.
  Qed.

  (** The entry of one recorded identifier. *)
  Lemma allocator_owned_rights_delete (Ω : gset AId) (ι : AId) :
    ι ∈ Ω ->
    allocator_owned_rights Ω ⊣⊢
    (ι ⊒ AQuar ∨ free_right ι) ∗
    allocator_owned_rights (Ω ∖ {[ι]}).
  Proof. intros Hι. by rewrite /allocator_owned_rights big_sepS_delete. Qed.

  (** The contents of the registry at the key of an allocator capability:
      its owner word, the owner token, and the rights of its allocations.
      They do not depend on the world nor on the compartment. *)
  Definition allocator_sealed_obj_resources (k : LAddr) : iProp Σ :=
    ∃ (a : Addr) (id : Z) (Ω : gset AId),
      ⌜ k = LNonHeap a ⌝ ∗
      a ↦ₐ WInt id ∗
      allocator_owner_id id Ω ∗
      allocator_owned_rights Ω.

  #[global] Instance allocator_sealed_obj_resources_timeless k :
    Timeless (allocator_sealed_obj_resources k).
  Proof. rewrite /allocator_sealed_obj_resources. apply _. Qed.

  (** The registry: its invariant holds the contents of every recorded
      key. *)
  Definition allocator_otype_registry : iProp Σ :=
    registry_inv Nallocator_otype AllocOtype (λ _, allocator_sealed_obj_resources).

  #[global] Instance allocator_otype_registry_persistent :
    Persistent allocator_otype_registry.
  Proof. rewrite /allocator_otype_registry. apply _. Qed.

  (** The predicate of a sealed allocator capability: a Global read-only
      capability on a static word, whose key is recorded in the registry for
      the compartment. *)
  Definition allocator_otype_propC : Thread * WORLD * CmptName * LWord -> iProp Σ :=
    registry_propC AllocOtype sealed_cap_key static_word_shape.

  #[global] Instance allocator_otype_propC_persistent x :
    Persistent (allocator_otype_propC x).
  Proof. rewrite /allocator_otype_propC. apply _. Qed.

  #[global] Instance allocator_otype_propC_timeless x :
    Timeless (allocator_otype_propC x).
  Proof. rewrite /allocator_otype_propC. apply _. Qed.

  (** The predicate does not depend on the thread nor on the world. *)
  Lemma allocator_otype_kind_ok (C : CmptName) :
    ⊢ seal_kind_ok SealGlobal C allocator_otype_propC.
  Proof. rewrite /allocator_otype_propC. apply registry_kind_ok. Qed.

  (** A valid word sealed with [AllocOtype] is an allocator capability,
      whose key the registry records for [C]. The owner word and identifier
      are taken out of the registry, which is closed again with any set of
      allocations. The validity of a sealed word does not depend on the
      world, so [w] may be valid in any world [Ww]. *)
  Lemma allocator_otype_acc (E F : coPset) (Ww : WORLD) (C : CmptName) (w : LWord) :
    ↑Nallocator_otype ⊆ F → ↑Nallocator_otype ⊆ E →
    get_tag w.(lw) = true ->
    is_sealed_with_o w.(lw) AllocOtype = true ->
    allocator_otype_registry -∗
    AllocOtype ↪ₒ{SealGlobal} allocator_otype_propC -∗
    interp Ww C w -∗
    na_own (tpool th) F
    ={E}=∗
    ∃ (g : Locality) (a : Addr) (id : Z) (Ω : gset AId),
      ⌜ w = lword_of_word (allocator_capability g a) ⌝ ∗
      ⌜ withinBounds a (a ^+ 1) a = true ⌝ ∗
      ⌜ is_shadow_address a = false ⌝ ∗
      a ↦ₐ WInt id ∗
      allocator_owner_id id Ω ∗
      allocator_owned_rights Ω ∗
      na_own (tpool th) (F ∖ ↑Nallocator_otype) ∗
      (∀ Ω',
        a ↦ₐ WInt id ∗
        allocator_owner_id id Ω' ∗
        allocator_owned_rights Ω' ∗
        na_own (tpool th) (F ∖ ↑Nallocator_otype)
        ={E}=∗ na_own (tpool th) F).
  Proof.
    iIntros (HF HE Htag Hsealed) "#Hreg #Hspred #Hinterp Hna".
    destruct w as [w π].
    destruct w as [ | | | ot sb]; try done.
    rewrite /is_sealed_with_o Z.eqb_eq in Hsealed.
    assert (ot = AllocOtype) as -> by solve_addr+Hsealed.
    iMod (registry_acc Nallocator_otype AllocOtype sealed_cap_key static_word_shape
            (λ _, allocator_sealed_obj_resources) E F Ww C sb π
           with "Hreg Hspred Hinterp Hna")
      as (k) "(%Hkey & %Hshape & Hk & Hna & Hclose)"; [done|done|exact Htag|].
    destruct Hshape as (a & Heq_w & Hbounds & Hshadow).
    rewrite Heq_w in Hkey. cbn in Hkey. injection Hkey as <-.
    destruct sb as [t p g b e a' | ]; cbn in Heq_w; simplify_eq.
    rewrite /lforce_global /lift_word /force_global /= in Heq_w.
    simplify_eq.
    (* The contents are timeless *)
    iEval (cbv beta) in "Hk".
    iMod "Hk" as (a' id Ω) "(%Ha' & Ha & Hid & Hrights)".
    injection Ha' as <-.
    iModIntro.
    iExists g, a, id, Ω. iFrame "Ha Hid Hrights Hna".
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iIntros (Ω') "(Ha & Hid & Hrights & Hna)".
    iApply ("Hclose" with "[- $Hna]").
    iApply bi.later_intro. iEval (cbv beta).
    iExists a, id, Ω'. by iFrame.
  Qed.

End AllocatorOtype.
