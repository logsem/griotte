From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode logrel.
From griotte.allocator Require Import allocator allocator_preamble.

(** Sealing predicate of [AllocOtype]. Every capability sealed with the
    allocator's otype is an allocator capability on a static word; the
    predicate owns that word and the matching owner identifier. The allocator
    specifications consume both and give them back, so the predicate is opened
    around a call and closed again right after it. *)

Section AllocatorOtype.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout}
  .

  (** Each allocation recorded for an owner is either quarantined, or its
      right to be freed is held by the sealing predicate. *)
  Definition allocator_owned_rights (W : WORLD) (S : gset Addr) : iProp Σ :=
    [∗ set] x ∈ S,
      (⌜ ∃ e, heap_std W !! x = Some (MkAllocObject x e AllocObjectQuarantined) ⌝ ∨
       free_right x).

  Global Instance allocator_owned_rights_timeless W S :
    Timeless (allocator_owned_rights W S).
  Proof. rewrite /allocator_owned_rights. apply _. Qed.

  Lemma allocator_owned_rights_mono (W W' : WORLD) (S : gset Addr) :
    related_sts_heap_std (heap_std W) (heap_std W') ->
    allocator_owned_rights W S -∗
    allocator_owned_rights W' S.
  Proof.
    iIntros (Hrelated) "Hrights".
    iApply (big_sepS_mono with "Hrights").
    iIntros (x Hx) "[%Hq|Hright]"; last by iRight.
    iLeft. iPureIntro.
    destruct Hq as [e Hq]. exists e.
    eapply related_sts_heap_std_quarantined; eauto.
  Qed.

  Lemma allocator_owned_rights_mono_priv (W W' : WORLD) (S : gset Addr) :
    related_sts_priv_world W W' ->
    allocator_owned_rights W S -∗
    allocator_owned_rights W' S.
  Proof.
    intros (_ & _ & _ & Hheap).
    by apply allocator_owned_rights_mono.
  Qed.

  (** A fresh allocation comes with its right to be freed. *)
  Lemma allocator_owned_rights_insert (W : WORLD) (S : gset Addr) (b : Addr) :
    allocator_owned_rights W S -∗
    free_right b -∗
    allocator_owned_rights W (S ∪ {[b]}).
  Proof.
    iIntros "Hrights Hright".
    rewrite /allocator_owned_rights.
    destruct (decide (b ∈ S)) as [Hb|Hb].
    - replace (S ∪ {[b]}) with S by set_solver.
      iFrame.
    - rewrite union_comm_L big_sepS_insert; last done.
      iFrame.
  Qed.

  Definition allocator_otype_inv (W : WORLD) (C : CmptName) (w : Word) : iProp Σ :=
    ∃ (id : Z) (a : Addr) (S : gset Addr),
      (* Shape of the allocator capability *)
      ⌜ w = WSealable (allocator_capability_scap Global a) ⌝ ∗
      ⌜ withinBounds a (a ^+ 1)%a a = true ⌝ ∗
      ⌜ is_shadow_address a = false ⌝ ∗
      (* The owner word, its identifier, and the rights of its allocations *)
      a ↦ₐ WInt id ∗
      allocator_owner_id id S ∗
      allocator_owned_rights W S.

  Program Definition allocator_otype_prop :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (w : Word), (allocator_otype_inv W C w)%I.
  Solve All Obligations with solve_proper.

  Definition allocator_otype_propC : WORLD * CmptName * leibnizO Word -> iProp Σ :=
    safeC allocator_otype_prop.

  Lemma mono_priv_ot_allocator (C : CmptName) (w : Word) :
    ⊢ future_priv_mono C allocator_otype_propC w.
  Proof.
    iIntros (W W' Hrelated_W_W' Hheap_wf).
    iModIntro.
    iIntros "Hot_allocator".
    rewrite /allocator_otype_propC /= /allocator_otype_inv.
    iDestruct "Hot_allocator" as (id a S) "(%Hw & %Hbounds & %Hshadow & Ha & Hid & Hrights)".
    iExists id, a, S. iFrame "Ha Hid". iFrame "%".
    iApply (allocator_owned_rights_mono_priv with "Hrights"); done.
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
    (Ww W : WORLD) (C : CmptName) (w : Word) :
    get_tag w = true ->
    is_sealed_with_o w AllocOtype = true ->
    seal_pred AllocOtype allocator_otype_propC -∗
    interp Ww C w -∗
    world_interp W C -∗
    ◇ (∃ (g : Locality) (a : Addr) (id : Z) (S : gset Addr),
        ⌜ w = allocator_capability g a ⌝ ∗
        ⌜ withinBounds a (a ^+ 1)%a a = true ⌝ ∗
        ⌜ is_shadow_address a = false ⌝ ∗
        a ↦ₐ WInt id ∗
        allocator_owner_id id S ∗
        allocator_owned_rights W S ∗
        region W C ∗
        sts_full_world W C ∗
        (∀ W' la S',
          ⌜ heap_wf (heap_std W') ⌝ -∗
          ⌜ seal_std W = seal_std W' ⌝ -∗
          ⌜ related_sts_priv_world W W' ⌝ -∗
          open_region_many W' C la ∗
          sts_full_world W' C ∗
          a ↦ₐ WInt id ∗
          allocator_owner_id id S' ∗
          allocator_owned_rights W' S' -∗
          world_interp_open W' C la)).
  Proof.
    iIntros (Htag Hsealed) "#Hspred #Hinterp Hworld".
    destruct w as [ | | | ot sb]; try done.
    rewrite /is_sealed_with_o Z.eqb_eq in Hsealed.
    assert (ot = AllocOtype) as -> by solve_addr+Hsealed.
    cbn in Htag.
    iEval (rewrite fixpoint_interp1_eq /= /interp_sb Htag) in "Hinterp".
    iDestruct "Hinterp" as "[#Hseal _]".
    iAssert (sts_seals_std C AllocOtype {[WSealable sb]})%I as "#Hseal'".
    { iApply sts_seals_std_weaken; last iFrame "Hseal"; set_solver+. }
    rewrite world_interp_eq /world_interp_def.
    iDestruct "Hworld" as "(Hregion & Hsts & Hseals)".
    iDestruct (open_sealing_map_singleton with "Hspred Hseal' Hseals Hsts")
      as "(Hseals & Hsts & Hres & HP)".
    (* Every part of the opened resources is timeless, except the
       monotonicity of the predicate, which holds anyway. *)
    iDestruct "Hres" as (ws') "(>%Hws' & >%Hsub & >#Hseals_ws' & _ & >Hothers)".
    iMod "HP" as (id a S) "(%Heq & %Hbounds & %Hshadow & Ha & Hid & Hrights)".
    destruct sb as [t p g b e a' | ]; cbn in Heq; simplify_eq.
    iModIntro.
    iExists g, a, id, S. iFrame "Ha Hid Hrights Hregion Hsts".
    iSplit; first done.
    iSplit; first done.
    iSplit; first done.
    iIntros (W' la S' Hheap_wf' Hseal_std Hrelated)
      "(Hregion & Hsts & Ha & Hid & Hrights)".
    rewrite world_interp_open_eq /world_interp_open_def.
    iFrame "Hregion Hsts".
    iAssert (sealing_map_resource_open W C AllocOtype allocator_otype_propC
      {[WCap true RO g a (a ^+ 1)%a a]}) with "[Hothers]" as "Hres".
    { iExists ws'. iFrame "Hseals_ws' Hothers".
      iSplit; first done. iSplit; first done.
      iIntros (w'). iApply mono_priv_ot_allocator. }
    iDestruct (sealing_map_resource_open_monotone with "Hres") as "Hres";
      try done.
    iDestruct (sealing_map_open_monotone with "Hseals") as "Hseals"; try done.
    iApply (close_sealing_map_singleton with "Hspred Hres [Ha Hid Hrights] Hseals").
    iExists id, a, S'. iFrame. done.
  Qed.

  (** The same, when the world is not opened further. *)
  Lemma allocator_otype_open
    (Ww W : WORLD) (C : CmptName) (w : Word) :
    get_tag w = true ->
    is_sealed_with_o w AllocOtype = true ->
    seal_pred AllocOtype allocator_otype_propC -∗
    interp Ww C w -∗
    world_interp W C -∗
    ◇ (∃ (g : Locality) (a : Addr) (id : Z) (S : gset Addr),
        ⌜ w = allocator_capability g a ⌝ ∗
        ⌜ withinBounds a (a ^+ 1)%a a = true ⌝ ∗
        ⌜ is_shadow_address a = false ⌝ ∗
        a ↦ₐ WInt id ∗
        allocator_owner_id id S ∗
        allocator_owned_rights W S ∗
        (∀ S',
          a ↦ₐ WInt id ∗
          allocator_owner_id id S' ∗
          allocator_owned_rights W S' -∗
          world_interp W C)).
  Proof.
    iIntros (Htag Hsealed) "#Hspred #Hinterp Hworld".
    iMod (allocator_otype_sopen with "Hspred Hinterp Hworld")
      as (g a id S) "(% & % & % & Ha & Hid & Hrights & Hregion & Hsts & Hclose)";
      try done.
    iModIntro. iExists g, a, id, S. iFrame "Ha Hid Hrights". iFrame "%".
    iIntros (S') "(Ha & Hid & Hrights)".
    rewrite open_world_interp_empty.
    iDestruct (sts_full_world_heap_wf with "Hsts") as %Hheap_wf.
    iApply ("Hclose" with "[] [] []"); try done.
    - iPureIntro. apply related_sts_priv_refl_world.
    - iFrame "Ha Hid Hrights Hsts". by rewrite -region_open_nil.
  Qed.

End AllocatorOtype.
