From iris.algebra Require Import auth gmap excl gset.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.
From griotte Require Import region_keys.
From griotte.program_logic Require Import alloc_registry.

(** * The ownership layer's ghost state (D26, D35, D40)

    Owner identifiers. An allocator capability points to a word holding an
    owner identifier. The exclusive token [allocator_owner_id id Ω] grants the
    authority to act as owner [id]; specifications require it together with
    the matching physical owner word. The set [Ω] is an exact view of the
    allocation identifiers allocated by owner [id], freed ones included (D4);
    the authoritative copy [allocator_owners O] is kept by the allocator
    service. Exclusivity makes owner identifiers of distinct token holders
    distinct. *)

Class allocatorOwnerPreG Σ := {
  allocator_owner_preG_inG :: inG Σ (authR (gmapUR Z (exclR (gsetO AId))));
}.

Class allocatorOwnerG Σ := {
  allocator_owner_inG :: allocatorOwnerPreG Σ;
  allocator_owner_name : gname;
}.

Definition allocator_ownerΣ : gFunctors :=
  #[GFunctor (authR (gmapUR Z (exclR (gsetO AId))))].

#[global] Instance subG_allocator_ownerΣ {Σ} :
  subG allocator_ownerΣ Σ -> allocatorOwnerPreG Σ.
Proof. solve_inG. Qed.

Section AllocatorOwner.
  Context {Σ : gFunctors} {allocator_ownerg : allocatorOwnerG Σ}.

  Definition allocator_owners (O : gmap Z (gset AId)) : iProp Σ :=
    own allocator_owner_name (● (Excl <$> O : gmap Z (excl (gset AId)))).

  Definition allocator_owner_id (id : Z) (Ω : gset AId) : iProp Σ :=
    own allocator_owner_name (◯ {[id := Excl Ω]}).

  #[global] Instance allocator_owners_timeless O : Timeless (allocator_owners O).
  Proof. apply _. Qed.

  #[global] Instance allocator_owner_id_timeless id Ω : Timeless (allocator_owner_id id Ω).
  Proof. apply _. Qed.

  Lemma allocator_owner_id_exclusive id Ω1 Ω2 :
    allocator_owner_id id Ω1 -∗ allocator_owner_id id Ω2 -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite auth_frag_valid singleton_op singleton_valid in Hvalid.
    by destruct Hvalid.
  Qed.

  Lemma allocator_owner_id_ne id1 id2 Ω1 Ω2 :
    allocator_owner_id id1 Ω1 -∗ allocator_owner_id id2 Ω2 -∗ ⌜id1 ≠ id2⌝.
  Proof.
    iIntros "H1 H2" (->). iApply (allocator_owner_id_exclusive with "H1 H2").
  Qed.

  Lemma allocator_owners_agree O id Ω :
    allocator_owners O -∗ allocator_owner_id id Ω -∗ ⌜O !! id = Some Ω⌝.
  Proof.
    iIntros "HO Hid". iDestruct (own_valid_2 with "HO Hid") as %Hvalid.
    apply auth_both_valid_discrete in Hvalid as [Hincl Hvalid].
    apply singleton_included_exclusive_l in Hincl; [|apply _|done].
    rewrite lookup_fmap in Hincl.
    destruct (O !! id) as [Ω'|]; simpl in Hincl; last by inversion Hincl.
    apply (inj Some), (inj Excl) in Hincl. iPureIntro. f_equal.
    by apply leibniz_equiv.
  Qed.

  Lemma allocator_owners_update O id Ω ι :
    allocator_owners O ∗ allocator_owner_id id Ω
    ==∗
    allocator_owners (<[id := Ω ∪ {[ι]}]> O) ∗ allocator_owner_id id (Ω ∪ {[ι]}).
  Proof.
    iIntros "[HO Hid]".
    iDestruct (allocator_owners_agree with "HO Hid") as %HΩ.
    rewrite /allocator_owners /allocator_owner_id -own_op.
    iApply (own_update_2 with "HO Hid").
    apply auth_update. rewrite fmap_insert.
    eapply singleton_local_update.
    - by rewrite lookup_fmap HΩ.
    - by apply exclusive_local_update.
  Qed.
End AllocatorOwner.

Section AllocatorOwnerInit.
  Context {Σ : gFunctors} `{!allocatorOwnerPreG Σ}.

  (** Allocate the authoritative owner map and one empty token for each
      identifier of the finite set [ids]. *)
  Lemma allocator_owners_init (ids : gset Z) :
    ⊢ |==> ∃ og : allocatorOwnerG Σ,
      @allocator_owners Σ og (gset_to_gmap ∅ ids) ∗
      [∗ set] id ∈ ids, @allocator_owner_id Σ og id ∅.
  Proof.
    iMod (own_alloc (● (Excl <$> gset_to_gmap ∅ ids : gmap Z (excl (gset AId))) ⋅
                     ◯ (Excl <$> gset_to_gmap ∅ ids : gmap Z (excl (gset AId)))))
      as (γ) "[HO Hids]".
    { apply auth_both_valid_discrete. split; first done.
      intros i. rewrite lookup_fmap.
      by destruct (gset_to_gmap ∅ ids !! i). }
    iModIntro. iExists {| allocator_owner_name := γ |}. iFrame "HO".
    iInduction ids as [|id ids Hid] "IH" using set_ind_L; first done.
    rewrite big_sepS_union; last set_solver.
    rewrite big_sepS_singleton gset_to_gmap_union_singleton fmap_insert.
    rewrite insert_singleton_op; last first.
    { rewrite lookup_fmap lookup_gset_to_gmap option_guard_False //. }
    rewrite auth_frag_op own_op. iDestruct "Hids" as "[$ Hids]". by iApply "IH".
  Qed.
End AllocatorOwnerInit.

(** * Rights to free (D2, D35)

    The right to free [ι] is the client half of its status token. It is the
    [FreeAuth] instance of the ownership layer: the allocator keeps nothing of
    the client half, and the client holds all of it. It is not exclusive by
    fragments: two copies contradict only together with the state
    interpretation's hidden half, at an instruction step. *)

Section FreeRights.
  Context {Σ : gFunctors} `{!allocRegistryG Σ}.

  Definition free_right (ι : AId) : iProp Σ := ι ↦st{1/2} ALive.

  #[global] Instance free_right_timeless ι : Timeless (free_right ι).
  Proof. rewrite /free_right. apply _. Qed.

  Lemma free_auth_owner_split (ι : AId) :
    (emp ∗ free_right ι ⊣⊢ ι ↦st{1/2} ALive)%I.
  Proof. by rewrite left_id. Qed.
End FreeRights.

(** Passed explicitly, never found by instance resolution, like the core
    instance [free_auth_core]. *)
Definition free_auth_owner {Σ : gFunctors} `{!allocRegistryG Σ} : FreeAuth Σ := {|
  free_auth_kept ι := emp%I;
  free_auth_held ι := free_right ι;
  free_auth_kept_timeless ι := _;
  free_auth_held_timeless ι := _;
  free_auth_split := free_auth_owner_split;
|}.
