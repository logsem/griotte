From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode logrel.
From griotte.allocator Require Import allocator allocator_preamble.

(** Sealing predicate of [AllocOtype] (D3, §4.7′). Every capability sealed
    with the allocator's otype is an allocator capability on a static word;
    the predicate exclusively owns that word and the matching owner token, so
    an allocator capability is valid in one compartment's world only. The
    allocator specifications consume both and give them back, so the
    predicate is opened around a call and closed again right after it. *)

Section AllocatorOtype.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout}
  .

  (** Each identifier recorded for an owner is either quarantined, or its
      right to be freed is held by the sealing predicate. It does not depend
      on the world. *)
  Definition allocator_owned_rights (Ω : gset AId) : iProp Σ :=
    [∗ set] ι ∈ Ω, (ι ⊒ AQuar ∨ free_right ι).

  Global Instance allocator_owned_rights_timeless Ω :
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

  Definition allocator_otype_inv (W : WORLD) (C : CmptName) (w : LWord) : iProp Σ :=
    ∃ (id : Z) (a : Addr) (Ω : gset AId),
      (* Shape of the allocator capability *)
      ⌜ w = lword_of_word (WSealable (allocator_capability_scap Global a)) ⌝ ∗
      ⌜ withinBounds a (a ^+ 1)%a a = true ⌝ ∗
      ⌜ is_shadow_address a = false ⌝ ∗
      (* The owner word, its identifier, and the rights of its allocations *)
      a ↦ₐ WInt id ∗
      allocator_owner_id id Ω ∗
      allocator_owned_rights Ω.

  Program Definition allocator_otype_prop :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (w : LWord), (allocator_otype_inv W C w)%I.
  Solve All Obligations with solve_proper.

  Definition allocator_otype_propC : WORLD * CmptName * leibnizO LWord -> iProp Σ :=
    safeC allocator_otype_prop.

  (** The predicate does not depend on the world. *)
  Lemma mono_priv_ot_allocator (C : CmptName) (w : LWord) :
    ⊢ future_priv_mono C allocator_otype_propC w.
  Proof.
    iIntros (W W' _). iModIntro. iIntros "H". done.
  Qed.

  Global Instance allocator_otype_propC_timeless W C w :
    Timeless (allocator_otype_propC (W, C, w)).
  Proof. rewrite /allocator_otype_propC /= /allocator_otype_inv. apply _. Qed.

  (** A valid word sealed with [AllocOtype] is an allocator capability. The
      owner word and identifier can be taken out of the world without a
      later, since the sealing predicate is timeless. The region and the
      standard states stay available, e.g. to open the payload of a free or
      to revoke the stack, and the sealing predicate can be closed for any
      open list [la] in any private future world [W'] with the same seals.
      The validity of a sealed word does not depend on the world, so [w] may
      be valid in any world [Ww]. *)
  Lemma allocator_otype_sopen
    (Ww W : WORLD) (C : CmptName) (w : LWord) :
    get_tag w.(lw) = true ->
    is_sealed_with_o w.(lw) AllocOtype = true ->
    seal_pred AllocOtype allocator_otype_propC -∗
    interp Ww C w -∗
    world_interp W C -∗
    ◇ (∃ (g : Locality) (a : Addr) (id : Z) (Ω : gset AId),
        ⌜ w = lword_of_word (allocator_capability g a) ⌝ ∗
        ⌜ withinBounds a (a ^+ 1)%a a = true ⌝ ∗
        ⌜ is_shadow_address a = false ⌝ ∗
        a ↦ₐ WInt id ∗
        allocator_owner_id id Ω ∗
        allocator_owned_rights Ω ∗
        region W C ∗
        sts_full_world W C ∗
        (∀ W' la Ω',
          ⌜ seal_std W = seal_std W' ⌝ -∗
          ⌜ related_sts_priv_world W W' ⌝ -∗
          open_region_many W' C la ∗
          sts_full_world W' C ∗
          a ↦ₐ WInt id ∗
          allocator_owner_id id Ω' ∗
          allocator_owned_rights Ω' -∗
          world_interp_open W' C la)).
  Proof.
    iIntros (Htag Hsealed) "#Hspred #Hinterp Hworld".
    destruct w as [w π].
    destruct w as [ | | | ot sb]; try done.
    rewrite /is_sealed_with_o Z.eqb_eq in Hsealed.
    assert (ot = AllocOtype) as -> by solve_addr+Hsealed.
    cbn in Htag.
    iEval (rewrite fixpoint_interp1_eq /= Htag) in "Hinterp".
    iDestruct "Hinterp" as "[#Hseal _]".
    iAssert (sts_seals_std C AllocOtype {[WSealable sb @@? π]})%I as "#Hseal'".
    { iApply sts_seals_std_weaken; last iFrame "Hseal"; set_solver+. }
    rewrite world_interp_eq /world_interp_def.
    iDestruct "Hworld" as "(Hregion & Hsts & Hseals)".
    iDestruct (open_sealing_map_singleton with "Hspred Hseal' Hseals Hsts")
      as "(Hseals & Hsts & Hres & HP)".
    (* Every part of the opened resources is timeless, except the
       monotonicity of the predicate, which holds anyway. *)
    iDestruct "Hres" as (ws') "(>%Hws' & >%Hsub & >#Hseals_ws' & _ & >Hothers)".
    iMod "HP" as (id a Ω) "(%Heq & %Hbounds & %Hshadow & Ha & Hid & Hrights)".
    destruct sb as [t p g b e a' | ]; cbn in Heq; simplify_eq.
    rewrite /lforce_global /lift_word /force_global /= /allocator_capability_scap in Heq.
    simplify_eq.
    iModIntro.
    iExists g, a, id, Ω. iFrame "Ha Hid Hrights Hregion Hsts".
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iIntros (W' la Ω' Hseal_std Hrelated)
      "(Hregion & Hsts & Ha & Hid & Hrights)".
    rewrite world_interp_open_eq /world_interp_open_def.
    iFrame "Hregion Hsts".
    iAssert (sealing_map_resource_open W C AllocOtype allocator_otype_propC
      {[WCap true RO g a (a ^+ 1)%a a @@? None]}) with "[Hothers]" as "Hres".
    { iExists ws'. iFrame "Hseals_ws' Hothers".
      iSplit; first done. iSplit; first done.
      iIntros (w'). iApply mono_priv_ot_allocator. }
    iDestruct (sealing_map_resource_open_monotone with "Hres") as "Hres";
      try done.
    iDestruct (sealing_map_open_monotone with "Hseals") as "Hseals"; try done.
    iApply (close_sealing_map_singleton with "Hspred Hres [Ha Hid Hrights] Hseals").
    iExists id, a, Ω'. iFrame. done.
  Qed.

  (** The same, when the world is not opened further. *)
  Lemma allocator_otype_open
    (Ww W : WORLD) (C : CmptName) (w : LWord) :
    get_tag w.(lw) = true ->
    is_sealed_with_o w.(lw) AllocOtype = true ->
    seal_pred AllocOtype allocator_otype_propC -∗
    interp Ww C w -∗
    world_interp W C -∗
    ◇ (∃ (g : Locality) (a : Addr) (id : Z) (Ω : gset AId),
        ⌜ w = lword_of_word (allocator_capability g a) ⌝ ∗
        ⌜ withinBounds a (a ^+ 1)%a a = true ⌝ ∗
        ⌜ is_shadow_address a = false ⌝ ∗
        a ↦ₐ WInt id ∗
        allocator_owner_id id Ω ∗
        allocator_owned_rights Ω ∗
        (∀ Ω',
          a ↦ₐ WInt id ∗
          allocator_owner_id id Ω' ∗
          allocator_owned_rights Ω' -∗
          world_interp W C)).
  Proof.
    iIntros (Htag Hsealed) "#Hspred #Hinterp Hworld".
    iMod (allocator_otype_sopen with "Hspred Hinterp Hworld")
      as (g a id Ω) "(% & % & % & Ha & Hid & Hrights & Hregion & Hsts & Hclose)";
      try done.
    iModIntro. iExists g, a, id, Ω. iFrame "Ha Hid Hrights". iFrame "%".
    iIntros (Ω') "(Ha & Hid & Hrights)".
    rewrite open_world_interp_empty.
    iApply ("Hclose" with "[] []"); try done.
    - iPureIntro. apply related_sts_priv_refl_world.
    - iFrame "Ha Hid Hrights Hsts". by rewrite -region_open_nil.
  Qed.

End AllocatorOtype.
