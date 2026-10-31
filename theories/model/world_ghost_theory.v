From iris.proofmode Require Import proofmode.
From griotte Require Import world_interp_revocation world_interp_allocation.
From griotte Require Export world_interp sts_ghost world_std_revocation sts_multiple_updates seal_store.
From griotte Require Export stdpp_extra iris_extra.
From griotte Require Import heap_region.

  (*** World Ghost Theory *)

  (** This file defines the ghost theory of worlds.
      It is intended to be a clean interface between the model defined in
      [world_interp.v], [region_maps.v] and [world_interp_*.v], and the user. *)

  (** * Disclaimer to the users of Griotte:

      All the proofs in this file use the Griotte internal model defined in
      [world_interp.v], [region_maps.v] and [world_interp_*.v].
      This file defines the interface that one should use in the proofs.

      The world interpretation of a compartment has two parts: the map of
      Permanent regions ([k ↪ᵖ[C]{p} φ], predicates without a world), and the
      local map of the section's thread ([k ↪ˡ[C]{p} φ]), read off the
      local world [W], whose keys are Temporary or Revoked.
  *)

Section world_ghost_theory.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}
    {th : Thread}
  .
  Notation Vc := (WORLD * CmptName * LWord → iProp Σ).
  Notation Vg := (CmptName * LWord → iProp Σ).

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Definitions of safety resources *)

  (** [PermRes] and [TmpRes] are defined with the region maps
      ([region_maps.v]). *)

  (** Revoked Safety Resources *)
  Definition RevokedResources (W : WORLD) (C : CmptName) (s : list LAddr) : iProp Σ :=
    [∗ list] a ∈ s, RevokedRes1 th W C a.

  Definition reinstate (W : WORLD) (s : list LAddr) := close_list s W.

  (** ** Lemmas about the safety resources *)

  #[global] Instance RevokedResources_Permutation_proper (W : WORLD) (C : CmptName) :
    Proper (Permutation ==> equiv) (RevokedResources W C).
  Proof. iIntros (l l' Hl); rewrite /RevokedResources; setoid_rewrite Hl; done. Defined.

  Lemma RevokedResources_app (W : WORLD) (C' : CmptName) (l l' : list LAddr) :
    RevokedResources W C' (l++l') ⊣⊢ RevokedResources W C' l ∗ RevokedResources W C' l'.
  Proof. apply big_sepL_app. Qed.

  Lemma RevokedResources_mono_pub (W W' : WORLD) (C : CmptName) (l_unk la : list LAddr) :
    related_sts_pub_world W W' ->
    RevokedResources W C l_unk -∗
    RevokedResources W' C l_unk.
  Proof.
    iIntros (Hrelated) "H".
    iApply (big_sepL_impl with "H").
    iIntros "!> %k %a %Ha (%pa & %Φa & %Hpers & Hrel & Hres)".
    iExists pa, Φa. iFrame "Hrel %". by iApply temp_res_mono_pub.
  Qed.

  (* [PermRes] can give access to the current points-to.
     We have to relinquish it to get [PermRes] again. *)
  Lemma PermRes_acc (C : CmptName) (a : LAddr) (p : Perm) (Φ : Vg) (w : LWord) :
    PermRes C a p Φ w -∗
    ( a ↦ₖ w ∗ ▷ Φ (C,w) ) ∗
    ( ( a ↦ₖ w ∗ ▷ Φ (C,w) ) -∗ PermRes C a p Φ w ).
  Proof.
    iIntros "(#Hp&Ha&HΦ)".
    iSplitL "Ha HΦ"; iFrame.
    iIntros "[Ha HΦ]"; iFrame "∗#".
  Qed.

  (** ** World opening/closing *)

  (* A closed world is like a world open on no addresses. *)
  Lemma open_world_interp_empty (W : WORLD) (C : CmptName) :
    world_interp W C ⊣⊢ world_interp_open W C [].
  Proof. by rewrite world_interp_eq world_interp_open_eq open_perm_nil open_l_nil. Qed.

  Lemma open_world_interp_temporary (W : WORLD) (C : CmptName) (s : list LAddr) (a : LAddr) (p : Perm) Φ :
    a ∉ s ->
    (std W) !! a = Some Temporary ->
    world_interp_open W C s -∗
    a ↪ˡ[C]{p} Φ
    -∗
    world_interp_open W C ({[ a ]} ∪ s) ∗
    heap_key_resource a (∃ w, TmpRes W C a p Φ w).
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (Ha HWa) "Hr Hrel".
    rewrite open_l_add_T // open_perm_add_T //.
    iDestruct "Hr" as "[$ Hl]".
    iApply (l_open_transport with "Hl Hrel"); [by apply not_elem_of_open_l|done].
  Qed.

  Lemma close_world_interp_temporary
    (W : WORLD) (C : CmptName) (s : list LAddr) (a : LAddr) (p : Perm) Φ (w : LWord)
    `{forall WCv, Persistent (Φ WCv)}:
    a ∉ s ->
    (std W) !! a = Some Temporary ->
    world_interp_open W C ({[ a ]} ∪ s) -∗
    a ↪ˡ[C]{p} Φ -∗
    TmpRes W C a p Φ w
    -∗
    world_interp_open W C s ∗ a ↪ˡ[C]{p} Φ.
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (Ha HWa) "Hr #Hrel Hres". iFrame "Hrel".
    iAssert (temp_res W C a p Φ) with "[Hres]" as "Hb".
    { iApply heap_key_resource_intro. by iExists w. }
    rewrite open_l_add_T // open_perm_add_T //.
    iDestruct "Hr" as "[$ Hl]".
    iApply (l_close with "Hl Hrel Hb"); [by apply not_elem_of_open_l|done..].
  Qed.

  Lemma open_world_interp_permanent (W : WORLD) (C : CmptName) (s : list LAddr) (a : LAddr) (p : Perm) Φ :
    a ∉ s ->
    (std W) !! a ≠ Some Temporary ->
    world_interp_open W C s -∗
    a ↪ᵖ[C]{p} Φ
    -∗
    world_interp_open W C ({[ a ]} ∪ s) ∗
    heap_key_resource a (∃ w, PermRes C a p Φ w).
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (Ha HWa) "Hr Hrel".
    rewrite open_l_add_nT // open_perm_add_nT //.
    iDestruct "Hr" as "[Hg $]".
    iApply (perm_open_transport with "Hg Hrel"). by apply not_elem_of_open_perm.
  Qed.

  Lemma close_world_interp_permanent (W : WORLD) (C : CmptName)
    (s : list LAddr) (a : LAddr) (p : Perm) Φ (w : LWord) `{forall Cv, Persistent (Φ Cv)}:
    a ∉ s ->
    (std W) !! a ≠ Some Temporary ->
    world_interp_open W C ({[ a ]} ∪ s) -∗
    a ↪ᵖ[C]{p} Φ -∗
    PermRes C a p Φ w
    -∗
    world_interp_open W C s ∗ a ↪ᵖ[C]{p} Φ.
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (Ha HWa) "Hr #Hrel Hres". iFrame "Hrel".
    iAssert (body_perm C a p Φ) with "[Hres]" as "Hb".
    { iApply heap_key_resource_intro. by iExists w. }
    rewrite open_l_add_nT // open_perm_add_nT //.
    iDestruct "Hr" as "[Hg $]".
    iApply (perm_close with "Hg Hrel Hb"); by apply not_elem_of_open_perm.
  Qed.

  (** The map of Permanent regions alone, without the local map: a thread
      outside the compartment's threads opens and closes a Permanent region
      through it. *)
  Lemma open_perm_region_map (C : CmptName) (s : gset LAddr) (a : LAddr) (p : Perm) Φ :
    a ∉ s ->
    perm_region_map C s -∗
    a ↪ᵖ[C]{p} Φ
    -∗
    perm_region_map C ({[ a ]} ∪ s) ∗
    heap_key_resource a (∃ w, PermRes C a p Φ w).
  Proof.
    iIntros (Ha) "Hg Hrel".
    iApply (perm_open_transport with "Hg Hrel"). done.
  Qed.

  Lemma close_perm_region_map (C : CmptName) (s : gset LAddr) (a : LAddr) (p : Perm) Φ
    (w : LWord) `{forall Cv, Persistent (Φ Cv)} :
    a ∉ s ->
    perm_region_map C ({[ a ]} ∪ s) -∗
    a ↪ᵖ[C]{p} Φ -∗
    PermRes C a p Φ w
    -∗
    perm_region_map C s.
  Proof.
    iIntros (Ha) "Hg #Hrel Hres".
    iAssert (body_perm C a p Φ) with "[Hres]" as "Hb".
    { iApply heap_key_resource_intro. by iExists w. }
    iApply (perm_close with "Hg Hrel Hb"); done.
  Qed.

  Lemma close_world_interp_next_quarantined_heap_l W C s a ι p φ
    `{∀ Wv, Persistent (φ Wv)} :
    LHeap a ι ∉ s -> std W !! LHeap a ι = Some Temporary ->
    ι ⊒ AQuar -∗
    world_interp_open W C ({[LHeap a ι]} ∪ s) -∗ LHeap a ι ↪ˡ[C]{p} φ -∗
    world_interp_open W C s.
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (Hnin Hstd) "#Hq Hr Hrel".
    iAssert (temp_res W C (LHeap a ι) p φ) with "[]" as "Hb".
    { rewrite /temp_res /=. by iRight. }
    rewrite open_l_add_T // open_perm_add_T //.
    iDestruct "Hr" as "[$ Hl]".
    iApply (l_close with "Hl Hrel Hb"); [by apply not_elem_of_open_l|done..].
  Qed.

  Lemma close_world_interp_next_quarantined_heap_perm W C s a ι p φ
    `{∀ Cv, Persistent (φ Cv)} :
    LHeap a ι ∉ s -> std W !! LHeap a ι ≠ Some Temporary ->
    ι ⊒ AQuar -∗
    world_interp_open W C ({[LHeap a ι]} ∪ s) -∗ LHeap a ι ↪ᵖ[C]{p} φ -∗
    world_interp_open W C s.
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (Hnin Hstd) "#Hq Hr Hrel".
    iAssert (body_perm C (LHeap a ι) p φ) with "[]" as "Hb".
    { rewrite /body_perm /=. by iRight. }
    rewrite open_l_add_nT // open_perm_add_nT //.
    iDestruct "Hr" as "[Hg $]".
    iApply (perm_close with "Hg Hrel Hb"); by apply not_elem_of_open_perm.
  Qed.

  (** ** The local map: its keys *)

  (** A key of the local world has a predicate in the local map. *)
  Lemma world_interp_rel_get W C (a : LAddr) ρ :
    std W !! a = Some ρ ->
    world_interp W C -∗
    world_interp W C ∗
    ∃ p φ, ⌜∀ WCv, Persistent (φ WCv)⌝ ∗ a ↪ˡ[C]{p} φ.
  Proof.
    rewrite world_interp_eq.
    iIntros (Hlookup) "[Hg (%M & Hw)]". iNamed "Hw".
    assert (is_Some (M !! a)) as [ [γp p] HM].
    { apply elem_of_dom. rewrite -Hdom elem_of_dom_std. eauto. }
    iDestruct "Hm" as "(Ha & #Hks & Hb)".
    iDestruct (big_sepM_lookup with "Hks") as "[#Hel _]"; [exact HM|].
    iDestruct (big_sepM_lookup_acc with "Hb") as "[Hb Hclose]"; [exact HM|].
    iDestruct "Hb" as (φ) "(%Hp & #Hsp & Hbody)".
    iDestruct ("Hclose" with "[Hbody]") as "Hb".
    { iExists φ. by iFrame "∗#%". }
    iSplitR "".
    - iFrame "Hg". iExists M. rewrite /local_region_map_M /rmap. by iFrame "∗#%".
    - iExists p, φ. iSplit; [done|]. rewrite rel_l_eq. iExists γp. by iFrame "#".
  Qed.

  (** A Permanent region outside the heap is not a Temporary key of the local
      world: both would own its cell. *)
  Lemma world_interp_rel_perm_not_temporary_nonheap W C a p φ :
    world_interp W C -∗ LNonHeap a ↪ᵖ[C]{p} φ -∗
    world_interp W C ∗ ⌜std W !! LNonHeap a ≠ Some Temporary⌝.
  Proof.
    iIntros "Hw #Hr".
    destruct (decide (std W !! LNonHeap a = Some Temporary)) as [HT|HnT]; [|by iFrame].
    iExFalso.
    iDestruct (world_interp_rel_get with "Hw") as "[Hw (%p' & %φ' & _ & #Hl)]"; [exact HT|].
    rewrite world_interp_eq. iDestruct "Hw" as "[Hg Hl']".
    iDestruct (perm_open with "Hg Hr") as "[_ (%φ'' & _ & _ & Hb & _)]"; [set_solver|].
    iDestruct "Hb" as (v) "(_ & Hv & _)".
    iApply (l_excl_not_T _ _ _ _ _ _ _ (LNonHeap a ↦ₖ v) with "[] [] Hl' Hl Hv");
      [set_solver|done| |].
    - iIntros "!>" (v') "Hb Hv". iApply (heap_pointsto_valid_2 with "Hb Hv"). done.
    - iIntros "!>" (a' ι Heq). done.
  Qed.

  (** A Permanent region of a key Temporary in the local world: both parts would
      own its cell, so the key is a heap key, with a tombstone. *)
  Lemma world_interp_open_rel_perm_temporary W C s k p φ :
    k ∉ s → std W !! k = Some Temporary →
    world_interp_open W C s -∗ k ↪ᵖ[C]{p} φ -∗
    world_interp_open W C s ∗ ∃ a ι, ⌜k = LHeap a ι⌝ ∗ ι ⊒ AQuar.
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (Hks HT) "[Hg Hl] #Hr".
    assert (k ∉ open_perm W s) as Hkg by (by apply not_elem_of_open_perm).
    assert (k ∉ open_l W s) as Hkl by (by apply not_elem_of_open_l).
    (* The local region of [k] *)
    iDestruct "Hl" as (M) "Hw". iNamed "Hw".
    assert (is_Some (M !! k)) as [ [γp p1] HM].
    { apply elem_of_dom. rewrite -Hdom elem_of_dom_std. eauto. }
    iDestruct "Hm" as "(Ha & #Hks & Hb)".
    iDestruct (big_sepM_lookup with "Hks") as "[#Hel _]"; [exact HM|].
    iDestruct (big_sepM_lookup_acc with "Hb") as "[Hbk Hclose]"; [exact HM|].
    rewrite decide_False //.
    iDestruct "Hbk" as (φ1) "(%Hp1 & #Hsp & Hbody)".
    iDestruct ("Hclose" with "[Hbody]") as "Hb".
    { iExists φ1. by iFrame "∗#%". }
    iAssert (local_region_map th W C (open_l W s)) with "[Ha Hb Hloc]" as "Hl".
    { iExists M. rewrite /local_region_map_M /rmap. by iFrame "∗#%". }
    iAssert (rel_l th C k p1 φ1) as "#Hrl".
    { rewrite rel_l_eq. iExists γp. by iFrame "#". }
    iDestruct (perm_open with "Hg Hr") as "[Hg (%φ' & %Hp' & #Hr' & Hb & _)]"; [done|].
    rewrite /body_perm. destruct k as [a0|a0 ι]; cbn.
    - iDestruct "Hb" as (v) "(_ & Hv & _)". iExFalso.
      iApply (l_excl_not_T _ _ _ _ _ _ _ (LNonHeap a0 ↦ₖ v) with "[] [] Hl Hrl Hv");
        [done|done| |].
      + iIntros "!>" (v') "Hb Hv". iApply (heap_pointsto_valid_2 with "Hb Hv"). done.
      + iIntros "!>" (a' ι Heq). done.
    - iDestruct "Hb" as "[(%v & _ & Hv & _)|#Hq]".
      + iExFalso.
        iApply (l_excl_not_T _ _ _ _ _ _ _ (LHeap a0 ι ↦ₖ v) with "[] [] Hl Hrl Hv");
          [done|done| |].
        * iIntros "!>" (v') "Hb Hv". iApply (heap_pointsto_valid_2 with "Hb Hv"). done.
        * iIntros "!>" (a' ι' [= -> ->]) "Hq Hv". iApply (heap_pointsto_quar_false with "Hv Hq").
      + iSplitL; [|iExists a0, ι; by iFrame "Hq"]. iFrame "Hl".
        iApply (perm_close with "Hg Hr' []"); [done|]. rewrite /body_perm /=. by iRight.
  Qed.

  (** A Permanent region outside the heap whose key is Temporary in the local
      world owns its cell, even with keys open. *)
  Lemma world_interp_open_rel_perm_temporary_cell W C s a p φ w :
    std W !! LNonHeap a = Some Temporary →
    world_interp_open W C s -∗ LNonHeap a ↪ᵖ[C]{p} φ -∗ a ↦ₐ w -∗ False.
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (HT) "[Hg _] #Hr Hw".
    iDestruct (perm_open with "Hg Hr") as "[_ (%φ' & _ & _ & Hb & _)]".
    { rewrite elem_of_open_perm. naive_solver. }
    iDestruct "Hb" as (v) "(_ & Hv & _)".
    iApply (heap_pointsto_valid_2 (LNonHeap a) (LNonHeap a) with "Hv Hw"). done.
  Qed.

  (** A Permanent region whose cell is held is not open: the world owns its
      body. *)
  Lemma world_interp_open_rel_perm_cell_false W C s k p φ w :
    k ∉ s → world_interp_open W C s -∗ k ↪ᵖ[C]{p} φ -∗ k ↦ₖ w -∗ False.
  Proof.
    rewrite !world_interp_open_eq.
    iIntros (Hks) "[Hg _] #Hr Hw".
    iDestruct (perm_open with "Hg Hr") as "[_ (%φ' & _ & _ & Hb & _)]".
    { by apply not_elem_of_open_perm. }
    rewrite /body_perm. destruct k as [a|a ι]; cbn [heap_key_resource].
    - iDestruct "Hb" as (v) "(_ & Hv & _)".
      iApply (heap_pointsto_valid_2 (LNonHeap a) (LNonHeap a) with "Hv Hw"). done.
    - iDestruct "Hb" as "[(%v & _ & Hv & _)|#Hq]".
      + iApply (heap_pointsto_valid_2 (LHeap a ι) (LHeap a ι) with "Hv Hw"). done.
      + iApply (heap_pointsto_quar_false with "Hw Hq").
  Qed.

  (** ** Lemma for world Revocation and Restoration. *)

  (* [extract_temporaries_condition] states that [la] is the full set of addresses
     that are Temporary in [W]. *)
  Definition extract_temporaries_condition (W : WORLD) (la : list LAddr) :=
      NoDup la ∧ (forall (a : LAddr), (std W) !! a = Some Temporary <-> a ∈ la).

  Lemma extract_temporaries_condition_revoke W s :
    extract_temporaries_condition W s -> Forall (λ a, std (revoke W) !! a = Some Revoked) s.
  Proof.
    intros [H1 H2].
    rewrite Forall_forall; intros a Ha.
    apply H2 in Ha.
    by apply revoke_lookup_Monotemp.
  Qed.

  (* Revocation of the world *)

  Lemma world_interp_revoke W C s :
    extract_temporaries_condition W s ->
    world_interp W C
    ==∗
    world_interp (revoke W) C ∗
    ▷ RevokedResources W C s ∗
    ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) s⌝.
  Proof.
    intros Hext. pose proof (extract_temporaries_condition_revoke _ _ Hext) as Hrev.
    destruct Hext as [Hnodup HaS].
    rewrite !world_interp_eq.
    iIntros "[$ Hl]".
    iDestruct (l_revoke th W C ∅ (list_to_set s) with "Hl") as "[$ HR]".
    { intros k. rewrite elem_of_list_to_set HaS. set_solver. }
    iModIntro. iSplitL; [|done]. iNext.
    rewrite /RevokedResources RevokedRes_list //.
  Qed.

  Lemma world_interp_restore W C l :
    world_interp W C ∗
    RevokedResources (close_list l W) C l
    ==∗
    world_interp (close_list l W) C.
  Proof.
    rewrite !world_interp_eq.
    iIntros "([$ Hl] & HR)".
    rewrite /RevokedResources.
    iDestruct (RevokedRes_list_sub with "HR") as "HR".
    rewrite close_list_close_set close_set_dom.
    iDestruct (RevokedRes_subseteq _ _ _ _ (list_to_set l ∩ dom (std W) ∖ ∅) with "HR") as "HR";
      [set_solver|].
    iModIntro. iApply (l_restore_open with "Hl HR"). set_solver.
  Qed.

  (* Restoration of the world, after revocation. *)
  Lemma world_interp_restore_world (W W' : WORLD) (C : CmptName) (s : list LAddr) :
    related_sts_pub_world W (reinstate W' s) →
    world_interp W' C -∗
    RevokedResources W C s
    ==∗
    world_interp (reinstate W' s) C.
  Proof.
    rewrite /reinstate close_list_close_set close_set_dom.
    rewrite !world_interp_eq.
    iIntros (Hpub) "[$ Hl] HR".
    rewrite /RevokedResources.
    iDestruct (RevokedRes_list_sub with "HR") as "HR".
    iDestruct (RevokedRes_subseteq _ _ _ _ (list_to_set s ∩ dom (std W') ∖ ∅) with "HR") as "HR";
      [set_solver|].
    iModIntro. iApply (l_restore_from with "Hl HR"); [set_solver|done].
  Qed.

  (** ** Revocation by separation.

      The following lemmas are useful lemmas to know that same addresses are in the Revoked state in the world.
      When one owns the points-to predicate of an address [a], that the world is closed,
      but that it exists a safety predicate for [a],
      then it means that the address [a] must be Revoked in the world.

      This is an argument by separation.
   *)

  Lemma world_interp_revoked_by_separation
    (W : WORLD) (C' : CmptName)
    (k : LAddr) (w : LWord) (q : Qp) :
    k ∈ dom (std W) →
    heap_key_live_share k q
    ∗ world_interp W C'
    ∗ laddr_addr k ↦ₐ w
    ==∗
    heap_key_live_share k q
    ∗ world_interp W C'
    ∗ laddr_addr k ↦ₐ w
    ∗ ⌜ std W !! k = Some Revoked ⌝
  .
  Proof.
    iIntros ([ρ Hρ]%elem_of_dom_std) "(Hshare & Hw & Ha)".
    destruct ρ; [|by iFrame].
    iExFalso. rewrite world_interp_eq.
    iDestruct "Hw" as "[_ (%M & Hw)]". iNamed "Hw".
    assert (is_Some (M !! k)) as [ [γp p] HM].
    { apply elem_of_dom. rewrite -Hdom elem_of_dom_std. eauto. }
    iDestruct "Hm" as "(_ & _ & Hb)".
    iDestruct (big_sepM_lookup with "Hb") as "Hb"; [exact HM|].
    iDestruct "Hb" as (φ) "(_ & _ & Hb)". rewrite /body_l Hρ /temp_res.
    iDestruct (heap_key_resource_live_share with "Hshare Hb") as "[(%v & _ & Hv & _) _]".
    rewrite key_pointsto_eq. iDestruct "Hv" as "[Hv _]".
    iApply (addr_dupl_false with "Ha Hv").
  Qed.

  Lemma world_interp_revoked_by_separation_many
    (W : WORLD) (C : CmptName)
    (la : list Addr) (lw : list LWord) :
    Forall (λ a, LNonHeap a ∈ dom (std W)) la →
    world_interp W C
    ∗ ([∗ list] a;w ∈ la;lw, a ↦ₐ w)
    ==∗
    world_interp W C
    ∗ ([∗ list] a;w ∈ la;lw, a ↦ₐ w)
    ∗ ⌜ Forall (λ a, std W !! LNonHeap a = Some Revoked) la⌝
  .
  Proof.
    revert lw. induction la as [|a la IH]; iIntros (lw Hdom) "[Hw Hl]".
    - iFrame. iPureIntro. constructor.
    - iDestruct (big_sepL2_cons_inv_l with "Hl") as (w lw' ->) "[Ha Hl]".
      apply Forall_cons in Hdom as [Ha Hdom].
      iMod (world_interp_revoked_by_separation W C (LNonHeap a) w 1%Qp with "[$Hw $Ha]")
        as "(_ & Hw & Ha & %Hrev)"; [done|].
      iMod (IH with "[$Hw $Hl]") as "($ & Hl & %Hrevs)"; [done|].
      iFrame. iPureIntro. by constructor.
  Qed.

  (** ** Extension of the world interpretation for safety invariants. *)

  (** A Permanent region enters the map of Permanent regions of [C]: no world
      step. *)
  Lemma world_interp_extend_perm
    {E : coPset}
    (W : WORLD) (C : CmptName) (a : LAddr) (v : LWord) (p : Perm) (φ : Vg)
    `{∀ Cv, Persistent (φ Cv)} :
    world_interp W C -∗
    PermRes C a p φ v

    ={E}=∗

    world_interp W C ∗
    a ↪ᵖ[C]{p} φ.
  Proof.
    rewrite world_interp_eq.
    iIntros "[Hg $] (%HpO & Ha & Hφ)".
    iDestruct (key_pointsto_known with "Ha") as "#Hkn".
    iMod (perm_extend with "Hg Hkn Ha [Hφ]") as "[$ $]"; [set_solver|done|by iNext|done].
  Qed.

  Lemma world_interp_extend_temp
    {E : coPset}
    (W : WORLD) (C : CmptName) (a : LAddr) (v : LWord) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)} :
    a ∉ dom (std W) →
    world_interp W C -∗
    TmpRes W C a p φ v

    ={E}=∗

    world_interp (<s[a := Temporary ]s>W) C ∗
    a ↪ˡ[C]{p} φ.
  Proof.
    rewrite !world_interp_eq.
    iIntros (Hfresh) "[$ Hl] (%HpO & Ha & Hφ & #Hmono)".
    iDestruct (key_pointsto_known with "Ha") as "#Hkn".
    iMod (l_extend th W C ∅ a Temporary p φ with "Hl Hkn [Ha Hφ]") as "[Hl Hr]"; [done|set_solver| |by iFrame].
    rewrite /body_l /std_update /= lookup_insert_eq.
    iApply heap_key_resource_intro. iExists v. rewrite /TmpRes. iFrame "∗#%".
    iNext. iApply ("Hmono" with "[] Hφ"). iPureIntro. by apply related_sts_pub_world_fresh.
  Qed.

  Lemma world_interp_extend_revoked
    {E : coPset}
    (W : WORLD) (C : CmptName) (a : LAddr) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)} :
    a ∉ dom (std W) →
    heap_key_known a -∗
    world_interp W C

    ={E}=∗

    world_interp (<s[a := Revoked ]s>W) C ∗
    a ↪ˡ[C]{p} φ.
  Proof.
    rewrite !world_interp_eq.
    iIntros (Hfresh) "#Hkn [$ Hl]".
    iMod (l_extend th W C ∅ a Revoked p φ with "Hl Hkn []") as "[Hl Hr]"; [done|set_solver| |by iFrame].
    by rewrite /body_l /std_update /= lookup_insert_eq.
  Qed.

  Lemma world_interp_extend_perm_keys
    {E : coPset}
    (W : WORLD) (C : CmptName) (lk : list LAddr) (lw : list LWord) (p : Perm) (φ : Vg)
    `{∀ Cv, Persistent (φ Cv)} :
    world_interp W C -∗
    ([∗ list] k;v ∈ lk;lw, PermRes C k p φ v)

    ={E}=∗

    world_interp W C ∗
    ([∗ list] k ∈ lk, k ↪ᵖ[C]{p} φ).
  Proof.
    revert lw. induction lk as [|k lk IH]; iIntros (lw) "Hw Hl".
    - iModIntro. by iFrame.
    - iDestruct (big_sepL2_cons_inv_l with "Hl") as (v lw' ->) "[Hk Hl]".
      iMod (world_interp_extend_perm with "Hw Hk") as "[Hw $]".
      iApply (IH with "Hw Hl").
  Qed.

  Lemma world_interp_extend_perm_sepL2
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list LWord) (p : Perm) (φ : Vg)
    `{∀ Cv, Persistent (φ Cv)} :
    world_interp W C -∗
    ([∗ list] a;v ∈ la;lw, PermRes C (LNonHeap a) p φ v)

    ={E}=∗

    world_interp W C ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ).
  Proof.
    iIntros "Hw Hl".
    iMod (world_interp_extend_perm_keys W C (LNonHeap <$> la) lw p φ with "Hw [Hl]") as "[$ Hr]".
    - by rewrite big_sepL2_fmap_l.
    - by rewrite big_sepL_fmap.
  Qed.

  (** Two cells of a list at the same address are impossible. *)
  Lemma sepL2_TmpRes_not_elem_of W C (a : Addr) v p φ (la : list Addr) (lw : list LWord) :
    a ∈ la →
    a ↦ₐ v -∗ ([∗ list] a';v' ∈ la;lw, TmpRes W C (LNonHeap a') p φ v') -∗ False.
  Proof.
    iIntros ([i Hi]%list_elem_of_lookup) "Ha Hl".
    iDestruct (big_sepL2_length with "Hl") as %Hlen.
    destruct (lw !! i) as [v'|] eqn:Hv'.
    2:{ apply lookup_lt_Some in Hi. apply lookup_ge_None in Hv'. lia. }
    iDestruct (big_sepL2_lookup with "Hl") as "(_ & Ha' & _)"; [done..|].
    iApply (addr_dupl_false with "Ha Ha'").
  Qed.

  Lemma world_interp_extend_temp_sepL2
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list LWord) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)} :
    isO p = false ->
    Forall (λ k, std W !! LNonHeap k = None) la →
    world_interp W C -∗
    ([∗ list] a;v ∈ la;lw, TmpRes W C (LNonHeap a) p φ v)

    ={E}=∗

    world_interp (std_update_multiple W la Temporary) C ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ˡ[C]{p} φ).
  Proof.
    revert lw. induction la as [|a la IH]; iIntros (lw HpO Hnone) "Hw Hl".
    - iModIntro. by iFrame.
    - iDestruct (big_sepL2_cons_inv_l with "Hl") as (v lw' ->) "[Ha Hl]".
      pose proof Hnone as Hnone'.
      apply Forall_cons in Hnone as [Ha Hnone].
      destruct (decide (a ∈ la)) as [Hin|Hnin].
      { iExFalso. iDestruct "Ha" as "(_ & Ha & _)".
        iApply (sepL2_TmpRes_not_elem_of with "Ha Hl"). done. }
      iMod (IH with "Hw Hl") as "[Hw $]"; [done..|].
      assert (Forall (λ a, LNonHeap a ∉ dom (std W)) la) as Hnone2.
      { eapply Forall_impl; [exact Hnone|]. intros a' Ha'. by rewrite not_elem_of_dom. }
      iDestruct "Ha" as "(_ & Ha & Hφ & #Hmono)".
      iApply (world_interp_extend_temp with "Hw [Ha Hφ]").
      { intros [Hin|Hdom]%elem_of_dom_std_multiple_update; [done|].
        rewrite elem_of_dom_std Ha in Hdom. by destruct Hdom. }
      rewrite /TmpRes. iFrame "Ha #%". iNext. iApply ("Hmono" with "[] Hφ"). iPureIntro.
      by apply related_sts_pub_update_multiple.
  Qed.

  Lemma world_interp_extend_revoked_sepL2
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (p : Perm) (φ : Vc)
    `{∀ Wv, Persistent (φ Wv)}:
    Forall (λ k, std W !! LNonHeap k = None) la →
    world_interp W C

     ={E}=∗

     world_interp (std_update_multiple W la Revoked) C ∗
     ([∗ list] k ∈ la, LNonHeap k ↪ˡ[C]{p} φ).
  Proof.
    induction la as [|a la IH]; iIntros (Hnone) "Hw".
    - iModIntro. by iFrame.
    - apply Forall_cons in Hnone as [Ha Hnone].
      iMod (IH with "Hw") as "[Hw #Hrels]"; [done|].
      destruct (decide (a ∈ la)) as [Hin|Hnin].
      + iModIntro. rewrite /= /std_update insert_id.
        2:{ by apply std_sta_update_multiple_lookup_in_i. }
        destruct (std_update_multiple W la Revoked). iFrame "Hw Hrels".
        by iApply (big_sepL_elem_of with "Hrels").
      + iMod (world_interp_extend_revoked with "[] Hw") as "[$ $]"; [|done|done].
        intros [Hin|Hdom]%elem_of_dom_std_multiple_update; [done|].
        rewrite elem_of_dom_std Ha in Hdom. by destruct Hdom.
  Qed.

  (** Permanent regions whose predicates need the region predicates: the keys
      enter the map open, then close with their bodies. *)
  Lemma world_interp_extend_perm_sepL2_open
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list LWord) (p : Perm) (φ : Vg)
    `{∀ Cv, Persistent (φ Cv)} :
    NoDup la ->
    isO p = false ->
    world_interp W C -∗
    ([∗ list] k;v ∈ la;lw, k ↦ₐ v) -∗
    (
      ([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ)
      -∗
      ([∗ list] v ∈ lw, φ (C, v))
    )

    ={E}=∗

    world_interp W C ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ) ∗
    ([∗ list] v ∈ lw, φ (C, v)).
  Proof.
    iIntros (Hnd HpO) "Hw Hcells Hφ".
    rewrite !world_interp_eq.
    iDestruct "Hw" as "[(%M & Hm) $]".
    assert (NoDup (LNonHeap <$> la)) as Hnd'.
    { apply NoDup_fmap; [intros ?? [= ->]; done|done]. }
    iMod (perm_insert_open_list C M ∅ (LNonHeap <$> la) lw p φ with "Hm [Hcells]")
      as (M') "(Hm & #Hrels & Hcells)"; [done|set_solver|by rewrite big_sepL2_fmap_l|].
    iDestruct ("Hφ" with "[]") as "#Hφs"; [by rewrite big_sepL_fmap|].
    iModIntro. rewrite big_sepL_fmap. iFrame "Hrels Hφs".
    iExists M'. iApply (perm_close_list with "Hm [Hcells]"); [done|set_solver|done|done|].
    iDestruct (big_sepL2_length with "Hcells") as %Hlen.
    iApply (big_sepL2_impl with "Hcells"). iIntros "!>" (i k v Hk Hv) "Hc".
    iFrame "Hc". apply list_lookup_fmap_Some in Hk as (a & -> & Ha). iSplitR.
    - iNext. by iApply (big_sepL_lookup with "Hφs").
    - by iApply (big_sepL_lookup with "Hrels").
  Qed.

  (** Permanent regions whose predicates need the region predicates, with a
      frame: the keys enter the map open, then close with their bodies. *)
  Lemma world_interp_extend_perm_sepL2_open_frame
    {E : coPset}
    (W : WORLD) (C : CmptName) (la : list Addr) (lw : list LWord) (p : Perm) (φ : CmptName * LWord → iProp Σ)
    (R : iProp Σ) `{∀ Cv, Persistent (φ Cv)} :
    NoDup la ->
    isO p = false ->
    world_interp W C -∗
    ([∗ list] k;v ∈ la;lw, k ↦ₐ v) -∗
    (
      ([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ)
      -∗
      ([∗ list] v ∈ lw, φ (C, v)) ∗ R
    )

    ={E}=∗

    world_interp W C ∗
    ([∗ list] k ∈ la, LNonHeap k ↪ᵖ[C]{p} φ) ∗
    ([∗ list] v ∈ lw, φ (C, v)) ∗
    R.
  Proof.
    iIntros (Hnd HpO) "Hw Hcells Hφ".
    rewrite !world_interp_eq.
    iDestruct "Hw" as "[(%M & Hm) $]".
    assert (NoDup (LNonHeap <$> la)) as Hnd'.
    { apply NoDup_fmap; [intros ?? [= ->]; done|done]. }
    iMod (perm_insert_open_list C M ∅ (LNonHeap <$> la) lw p φ with "Hm [Hcells]")
      as (M') "(Hm & #Hrels & Hcells)"; [done|set_solver|by rewrite big_sepL2_fmap_l|].
    iDestruct ("Hφ" with "[]") as "[#Hφs HR]"; [by rewrite big_sepL_fmap|].
    iModIntro. rewrite big_sepL_fmap. iFrame "Hrels Hφs HR".
    iExists M'. iApply (perm_close_list with "Hm [Hcells]"); [done|set_solver|done|done|].
    iDestruct (big_sepL2_length with "Hcells") as %Hlen.
    iApply (big_sepL2_impl with "Hcells"). iIntros "!>" (i k v Hk Hv) "Hc".
    iFrame "Hc". apply list_lookup_fmap_Some in Hk as (a & -> & Ha). iSplitR.
    - iNext. by iApply (big_sepL_lookup with "Hφs").
    - by iApply (big_sepL_lookup with "Hrels").
  Qed.

  (** ** Custom STS *)

  Lemma world_interp_alloc_loc
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    {E : coPset}
    (W : WORLD) (C : CmptName) (d : D) (rpub rpriv : D → D → Prop) :
    let i := fresh_cus_name W in
    world_interp W C
    ={E}=∗
    world_interp (<l[ i := d , (rpub,rpriv) ]l> W) C ∗
    ⌜i ∉ dom (loc W)⌝ ∗
    ⌜i ∉ dom (wrel W)⌝ ∗
    sts_state_loc C i d ∗ sts_rel_loc C i rpub rpriv.
  Proof.
    intros i.
    rewrite !world_interp_eq.
    iIntros "[$ (%M & Hw)]". iNamed "Hw".
    iMod (sts_alloc_loc W C d rpub rpriv with "Hloc") as "(Hloc & %Hi1 & %Hi2 & $ & $)".
    iModIntro. iSplitL; [|done].
    assert (related_sts_pub_world W (<l[ i := d , (rpub,rpriv) ]l> W)) as Hpub.
    { by apply related_sts_pub_world_fresh_loc. }
    iDestruct (rmap_next th W (<l[ i := d , (rpub,rpriv) ]l> W) C M ∅ with "Hm") as "Hm"; [done|done|].
    iExists M. rewrite /local_region_map_M. by iFrame "∗%".
  Qed.

  (* Update of custom invariant in the world. *)
  Lemma world_interp_update_loc
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    {E : coPset}
    (W : WORLD) (C' : CmptName) (i : positive) (d d' : D) :
    revoke_condition W ->
    related_sts_priv_world W (<l[i:=d']l>W) ->
    world_interp W C' -∗
    sts_state_loc C' i d
    ={E}=∗
    world_interp (<l[ i := d' ]l> W) C' ∗
    sts_state_loc C' i d'.
  Proof.
    rewrite !world_interp_eq.
    iIntros (Hrevoke_conditions Hrelated) "[$ Hl] Hst_i".
    iApply (l_update_loc_priv with "Hl Hst_i"). done.
  Qed.

  (* Get the STS (relations) of a custom invariant in the world. *)
  Lemma world_interp_rel_loc_valid
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    (W : WORLD) (C' : CmptName) (i : positive)
    (rpub rpriv: D -> D -> Prop) :
    world_interp W C' -∗
    sts_rel_loc C' i rpub rpriv
    -∗
    ⌜ wrel W !! i = Some (convert_rel rpub,convert_rel rpriv)⌝.
  Proof.
    rewrite world_interp_eq.
    iIntros "[_ (%M & Hw)] Hsts_rel". iNamed "Hw".
    iApply (sts_full_rel_loc with "Hloc Hsts_rel").
  Qed.

  (* Get the STS (current state) of a custom invariant in the world. *)
  Lemma world_interp_loc_valid
    { D : Type } {eqd : EqDecision D} {countD : Countable D}
    (W : WORLD) (C' : CmptName) (i : positive) (d : D) :
    world_interp W C' -∗
    sts_state_loc C' i d
    -∗
    ⌜loc W !! i = Some (encode d)⌝.
  Proof.
    rewrite world_interp_eq.
    iIntros "[_ (%M & Hw)] Hst_i". iNamed "Hw".
    iApply (sts_full_state_loc with "Hloc Hst_i").
  Qed.

  (* Initialise the permanent resources *)
  Definition init_PermRes (C : CmptName) (a : LAddr) (p : Perm) (Φ : Vg) (w : LWord) :
    isO p = false ->
    a ↦ₖ w -∗
    Φ (C,w)
    -∗
    PermRes C a p Φ w.
  Proof. iIntros (HpO) "Ha HΦ"; iFrame; done. Qed.

  (* Initialise the temporary resources *)
  Definition init_TmpRes (W : WORLD) (C : CmptName) (a : LAddr) (p : Perm) (Φ : Vc) (w : LWord) :
    isO p = false ->
    future_pub_mono C Φ w -∗
    a ↦ₖ w -∗
    Φ (W,C,w)
    -∗
    TmpRes W C a p Φ w.
  Proof. iIntros (HpO) "Hmono Ha HΦ"; iFrame; done. Qed.

  (** ** Fresh allocation identifiers

      The identifiers of the heap keys of a set of keys. An identifier that
      does not occur there names no key of the set. *)
  Definition heap_ids (D : gset LAddr) : gset AId :=
    list_to_set (omap (λ k, match k with LHeap _ ι => Some ι | LNonHeap _ => None end) (elements D)).

  Lemma heap_ids_spec D a ι :
    LHeap a ι ∈ D → ι ∈ heap_ids D.
  Proof.
    intros Hin. rewrite /heap_ids elem_of_list_to_set list_elem_of_omap.
    exists (LHeap a ι). split; last done. by apply elem_of_elements.
  Qed.

  Lemma heap_ids_fresh D a ι :
    ι ∉ heap_ids D → LHeap a ι ∉ D.
  Proof. intros Hι Hin. by apply Hι, (heap_ids_spec _ a). Qed.

End world_ghost_theory.

(** ** The shared resources at two threads

    The registry of the instance of a thread is that of the base, so the
    map of Permanent regions is the same at any two threads. *)
Section thread_indep.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG} {relg : relGS Σ}.

  Lemma perm_region_map_thread_indep (t t' : Thread) C s :
    perm_region_map (allocg := @cerise_registryG Σ (ceriseG_of t))
      (memg := @mem_gen_memG Σ (ceriseG_of t)) C s ⊣⊢
    perm_region_map (allocg := @cerise_registryG Σ (ceriseG_of t'))
      (memg := @mem_gen_memG Σ (ceriseG_of t')) C s.
  Proof. rewrite /ceriseG_of. reflexivity. Qed.

End thread_indep.

(** ** Initialise the world in the adequacy theorem *)
Section world_interp_Pre.
  Context {Σ:gFunctors} `{MP : MachineParameters}
          {Cname : CmptNameG}
          {ceriseg : ceriseG Σ}
          {sts_preg: STS_preG Σ}
          {relpreg : relGpreS Σ}
          {sealstorepreg: sealStorePreG Σ}
.

  (** For the user threads [k < nthreads], with [0 < nthreads]: a world for
      the user thread 0, empty local maps for the others. *)
  Lemma world_interp_init (oset : gset OType) (nthreads : nat) :
    0 < nthreads →
    ⊢ |==> (∃ (relg: relGS Σ) (stsg : STSG Σ) (sstoreg : sealStoreG Σ),
            ([∗ set] C ∈ CNames, world_interp (th := UserThread 0) (MkWorld ∅ (∅,∅)) C) ∗
            ([∗ list] k ∈ seq 1 (nthreads - 1), [∗ set] C ∈ CNames,
               local_region_map (UserThread k) (MkWorld ∅ (∅,∅)) C ∅) ∗
            ([∗ set] o ∈ oset, can_alloc_pred o)).
  Proof.
    intros Hn.
    iMod (gen_sts_init (A:=LAddr) (B:=region_type) nthreads) as (stsg) "Hsts".
    iMod (rel_init nthreads) as (relg) "[Hg HRELS]".
    iMod (seal_store_init) as (sstoreg) "Hseals".
    iExists relg, stsg, sstoreg; iFrame "Hseals".
    assert (seq 0 nthreads = 0 :: seq 1 (nthreads - 1)) as Hseq.
    { destruct nthreads as [|n]; [lia|]. by rewrite /= Nat.sub_0_r. }
    rewrite Hseq !big_sepL_cons.
    iDestruct "Hsts" as "[Hsts0 Hsts]". iDestruct "HRELS" as "[Hl0 HRELS]".
    iModIntro. iSplitL "Hg Hl0 Hsts0".
    - iCombine "Hg Hl0 Hsts0" as "H".
      rewrite -!big_sepS_sep.
      iApply (big_sepS_impl with "H").
      iModIntro; iIntros (C HC) "(Hg & Hl & Hsts)".
      rewrite world_interp_eq.
      iSplitL "Hg".
      + iExists ∅. rewrite /perm_region_map_M /rmap !big_sepM_empty. by iFrame.
      + iExists ∅. rewrite /local_region_map_M /rmap !big_sepM_empty /=. iFrame. iPureIntro. by rewrite !dom_empty_L.
    - iCombine "HRELS" "Hsts" as "H".
      rewrite -big_sepL_sep.
      iApply (big_sepL_impl with "H").
      iModIntro; iIntros (i k Hk) "[Hl Hsts]".
      iCombine "Hl" "Hsts" as "H".
      rewrite -big_sepS_sep.
      iApply (big_sepS_impl with "H").
      iModIntro; iIntros (C HC) "[Hl Hsts]".
      iExists ∅. rewrite /local_region_map_M /rmap !big_sepM_empty /=. iFrame. iPureIntro. by rewrite !dom_empty_L.
  Qed.

End world_interp_Pre.

(** The world premise of a thread under the regime of the compartment [C]
    ([world_resources W C]), and the credit it carries from one step to the
    next ([shared_credit C]). A compartment in exclusive mode owns its world
    interpretation and carries no credit. *)
Section world_resources.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}
  .
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition world_resources_def (W : WORLD) (C : CmptName) : iProp Σ :=
    world_interp W C.
  #[local] Definition world_resources_aux : seal (@world_resources_def). Proof. by eexists. Qed.
  Definition world_resources := world_resources_aux.(unseal).
  #[local] Definition world_resources_unseal :
    @world_resources = @world_resources_def := world_resources_aux.(seal_eq).

  Definition shared_credit_def (C : CmptName) : iProp Σ := True.
  #[local] Definition shared_credit_aux : seal (@shared_credit_def). Proof. by eexists. Qed.
  Definition shared_credit := shared_credit_aux.(unseal).
  #[local] Definition shared_credit_unseal :
    @shared_credit = @shared_credit_def := shared_credit_aux.(seal_eq).

  (** In exclusive mode, the world premise is the owned world interpretation. *)
  Lemma world_resources_exclusive W C :
    world_resources W C ⊣⊢ world_interp W C.
  Proof. by rewrite world_resources_unseal. Qed.

  (** A later credit refills the carried credit. *)
  Lemma shared_credit_refill C :
    £ 1 -∗ shared_credit C.
  Proof. rewrite shared_credit_unseal. by iIntros "_". Qed.

  (** In exclusive mode, the carried credit is free. *)
  Lemma shared_credit_exclusive C :
    ⊢ shared_credit C.
  Proof. by rewrite shared_credit_unseal. Qed.

End world_resources.
