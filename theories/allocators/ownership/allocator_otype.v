From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From griotte Require Import proofmode logrel.
From griotte.allocators.ownership Require Import allocator allocator_preamble.

(** Sealing predicate of [AllocOtype]. Every capability sealed with the
    allocator's otype is an allocator capability on a static word, recorded
    in the allocator's registry for one compartment. The registry's
    invariant exclusively owns that word and the matching owner token, so an
    allocator capability is valid in one compartment only. The allocator
    specifications consume both and give them back, so the registry is
    opened around a call and closed again right after it. *)

Definition Nallocator_otype : namespace := nroot .@ "allocator_otype".

(** The ghost state of the registry: a map from the key of each sealed
    object to the compartment it is valid in. *)
Class allocatorOtypePreG {Cname : CmptNameG} Σ := {
  allocator_otype_preG_mapG :: ghost_mapG Σ LAddr CmptName;
}.
#[export] Hint Mode allocatorOtypePreG - - : typeclass_instances.

Class allocatorOtypeG {Cname : CmptNameG} Σ := {
  allocator_otype_inG :: allocatorOtypePreG Σ;
  allocator_otype_name : gname;
}.
#[export] Hint Mode allocatorOtypeG - - : typeclass_instances.

Definition allocator_otypeΣ {Cname : CmptNameG} : gFunctors :=
  #[ghost_mapΣ LAddr CmptName].

#[global] Instance subG_allocator_otypeΣ {Cname : CmptNameG} {Σ} :
  subG allocator_otypeΣ Σ -> allocatorOtypePreG Σ.
Proof. solve_inG. Qed.

Section AllocatorOtype.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    {allocator_otypeg : allocatorOtypeG Σ}
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
  Definition allocator_otype_contents (k : LAddr) : iProp Σ :=
    ∃ (a : Addr) (id : Z) (Ω : gset AId),
      ⌜ k = LNonHeap a ⌝ ∗
      a ↦ₐ WInt id ∗
      allocator_owner_id id Ω ∗
      allocator_owned_rights Ω.

  #[global] Instance allocator_otype_contents_timeless k :
    Timeless (allocator_otype_contents k).
  Proof. rewrite /allocator_otype_contents. apply _. Qed.

  (** The registry: its invariant holds the contents of every recorded
      key. *)
  Definition allocator_otype_registry : iProp Σ :=
    na_inv (tpool th) Nallocator_otype
      (∃ M : gmap LAddr CmptName,
         ghost_map_auth allocator_otype_name 1 M ∗
         [∗ map] k ↦ _ ∈ M, allocator_otype_contents k).

  #[global] Instance allocator_otype_registry_persistent :
    Persistent allocator_otype_registry.
  Proof. apply _. Qed.

  (** The predicate of a sealed allocator capability: its shape, and its key
      recorded in the registry for the compartment [C]. *)
  Definition allocator_otype_inv (W : WORLD) (C : CmptName) (w : LWord) : iProp Σ :=
    ∃ (a : Addr),
      (* Shape of the allocator capability *)
      ⌜ w = lword_of_word (WSealable (allocator_capability_scap Global a)) ⌝ ∗
      ⌜ withinBounds a (a ^+ 1) a = true ⌝ ∗
      ⌜ is_shadow_address a = false ⌝ ∗
      (* Its key in the registry *)
      LNonHeap a ↪[allocator_otype_name]□ C.

  Program Definition allocator_otype_prop :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (w : LWord), (allocator_otype_inv W C w)%I.
  Solve All Obligations with solve_proper.

  Definition allocator_otype_propC : Thread * WORLD * CmptName * LWord -> iProp Σ :=
    λ x, allocator_otype_prop x.1.1.2 x.1.2 x.2.

  #[global] Instance allocator_otype_propC_persistent x :
    Persistent (allocator_otype_propC x).
  Proof. rewrite /allocator_otype_propC /= /allocator_otype_inv. apply _. Qed.

  #[global] Instance allocator_otype_propC_timeless x :
    Timeless (allocator_otype_propC x).
  Proof. rewrite /allocator_otype_propC /= /allocator_otype_inv. apply _. Qed.

  (** The predicate does not depend on the thread nor on the world. *)
  Lemma allocator_otype_kind_ok (C : CmptName) :
    ⊢ seal_kind_ok SealGlobal C allocator_otype_propC.
  Proof.
    iSplit; first (iPureIntro; intros x; apply _).
    iIntros "!>" (t t' W W' w) "H". done.
  Qed.

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
    cbn in Htag.
    iEval (rewrite interp_unfold /= Htag) in "Hinterp".
    iDestruct "Hinterp" as "[(%κ & %P & #Hs & _ & #HP) _]".
    iDestruct (seal_pred_agree with "Hspred Hs") as "[<- #Heq]".
    iAssert (▷ allocator_otype_propC (th, Ww, C, norm SealGlobal (WSealable sb @@? π)))%I
      as "#HP'".
    { iNext. iRewrite ("Heq" $! (th, Ww, C, norm SealGlobal (WSealable sb @@? π))).
      iExact "HP". }
    iMod "HP'" as (a) "(%Heq_w & %Hbounds & %Hshadow & #Hel)".
    destruct sb as [t p g b e a' | ]; cbn in Heq_w; simplify_eq.
    rewrite /lforce_global /lift_word /force_global /= /allocator_capability_scap in Heq_w.
    simplify_eq.
    iMod (na_inv_acc with "Hreg Hna") as "(>(%M & Hauth & Hcontents) & Hna & Hclose)";
      [done|done|].
    iDestruct (ghost_map_lookup with "Hauth Hel") as %HM.
    iDestruct (big_sepM_delete with "Hcontents") as "[Hk Hcontents]"; first exact HM.
    iDestruct "Hk" as (a' id Ω) "(%Ha' & Ha & Hid & Hrights)".
    injection Ha' as <-.
    iModIntro.
    iExists g, a, id, Ω. iFrame "Ha Hid Hrights Hna".
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iIntros (Ω') "(Ha & Hid & Hrights & Hna)".
    iApply ("Hclose" with "[- $Hna]").
    iNext. iExists M. iFrame "Hauth".
    iApply (big_sepM_delete with "[- $Hcontents]"); first exact HM.
    iExists a, id, Ω'. by iFrame.
  Qed.

End AllocatorOtype.
