From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map.
From griotte Require Import proofmode logrel.

(** * Seal registries

    The sealing predicate of a trusted sealer, whose sealed objects are
    valid in one compartment each. A sealed object has a key, computed from
    its payload by [key_of]. The registry of the sealer is one [na_inv] at
    the namespace [N]: it holds a ghost map from the keys of the registered
    objects to their compartment, and the resources
    [sealed_obj_resources C k] of every registered key [k] of compartment
    [C]. The sealing predicate holds
    nothing but pure facts (the key and the shape of the payload) and the
    membership [k ↪[γ]□ C]: it is timeless and persistent, and does not
    depend on the thread nor on the world. The resources come out of the
    registry under a later, and may mention [interp].

    The registries share one class, with one ghost name per registry,
    named by the otype of its sealer. *)

(** The ghost state of the registries: for each otype, a map from the key of
    each sealed object to the compartment it is valid in. A key [ObjKey]
    identifies a sealed object. *)
Class sealRegistryPreG {Cname : CmptNameG} (ObjKey : Type) `{Countable ObjKey} Σ := {
  seal_registry_preG_mapG :: ghost_mapG Σ ObjKey CmptName;
}.
#[export] Hint Mode sealRegistryPreG - ! - - - : typeclass_instances.

Class sealRegistryG {Cname : CmptNameG} (ObjKey : Type) `{Countable ObjKey} Σ := {
  seal_registry_inG :: sealRegistryPreG ObjKey Σ;
  seal_registry_name : OType → gname;
}.
#[export] Hint Mode sealRegistryG - ! - - - : typeclass_instances.

Definition seal_registryΣ {Cname : CmptNameG} (ObjKey : Type) `{Countable ObjKey} : gFunctors :=
  #[ghost_mapΣ ObjKey CmptName].

#[global] Instance subG_seal_registryΣ {Cname : CmptNameG} {ObjKey : Type} `{Countable ObjKey} {Σ} :
  subG (seal_registryΣ ObjKey) Σ → sealRegistryPreG ObjKey Σ.
Proof. solve_inG. Qed.

Section SealRegistryNames.
  Context
    {Σ : gFunctors} {Cname : CmptNameG}
    {ObjKey : Type} `{Countable ObjKey}
    {seal_registry_preg : sealRegistryPreG ObjKey Σ}
  .

  (** The ghost names of the registries of several sealers, with distinct
      otypes [os]: an empty map for each of them. The name of the otype [o]
      is that of the first allocation of [o], so the names of [os] are
      distinct. *)
  Lemma seal_registry_names_alloc (os : list OType) :
    NoDup os →
    ⊢ |==> ∃ name : OType → gname,
      [∗ list] o ∈ os, ghost_map_auth (name o) 1 (∅ : gmap ObjKey CmptName).
  Proof.
    induction 1 as [|o os Ho Hnodup IH].
    - iModIntro. iExists (λ _, 1%positive). by rewrite big_sepL_nil.
    - iMod IH as (name) "Hauths".
      iMod (ghost_map_alloc_empty (K := ObjKey) (V := CmptName)) as (γ) "Hauth".
      iModIntro.
      iExists (λ o', if decide (o' = o) then γ else name o').
      rewrite big_sepL_cons decide_True //. iFrame "Hauth".
      iApply (big_sepL_impl with "Hauths").
      iIntros "!>" (i o' Hi) "Hauth".
      rewrite decide_False; first done.
      intros ->. apply Ho. by eapply list_elem_of_lookup_2.
  Qed.
End SealRegistryNames.

Section SealRegistry.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {ObjKey : Type} `{Countable ObjKey}
    {seal_registryg : sealRegistryG ObjKey Σ}
  .

  (** The parameters of a registry: its namespace, the otype of its sealer,
      the key of a payload, a pure condition on the shape of the payload,
      and the resources of a registered key for a compartment. *)
  Context
    (N : namespace)
    (o : OType)
    (key_of : LWord → option ObjKey)
    (shape : LWord → Prop)
    (sealed_obj_resources : CmptName → ObjKey → iProp Σ).

  (** The authoritative map of the registry, before the invariant is
      allocated. *)
  Definition registry_auth (M : gmap ObjKey CmptName) : iProp Σ :=
    ghost_map_auth (seal_registry_name (ObjKey := ObjKey) o) 1 M.

  (** The key [k] is registered for the compartment [C]. *)
  Definition registry_member (k : ObjKey) (C : CmptName) : iProp Σ :=
    k ↪[seal_registry_name (ObjKey := ObjKey) o]□ C.

  #[global] Instance registry_member_persistent k C :
    Persistent (registry_member k C).
  Proof. rewrite /registry_member. apply _. Qed.

  #[global] Instance registry_member_timeless k C :
    Timeless (registry_member k C).
  Proof. rewrite /registry_member. apply _. Qed.

  (** The registry: its invariant holds the contents of every recorded
      key. *)
  Definition registry_inv : iProp Σ :=
    na_inv (tpool th) N
      (∃ M : gmap ObjKey CmptName,
         ghost_map_auth (seal_registry_name (ObjKey := ObjKey) o) 1 M ∗
         [∗ map] k ↦ C ∈ M, sealed_obj_resources C k).

  #[global] Instance registry_inv_persistent : Persistent registry_inv.
  Proof. rewrite /registry_inv. apply _. Qed.

  (** The predicate of a sealed object: the shape of its payload, and its
      key recorded in the registry for the compartment [C]. *)
  Definition registry_word_pred (C : CmptName) (w : LWord) : iProp Σ :=
    ∃ k : ObjKey,
      ⌜ key_of w = Some k ⌝ ∗
      ⌜ shape w ⌝ ∗
      registry_member k C.

  (** The seal predicate: it does not depend on the thread nor on the
      world. *)
  Definition registry_propC (x : Thread * WORLD * CmptName * LWord) : iProp Σ :=
    registry_word_pred x.1.2 x.2.

  #[global] Instance registry_propC_persistent x :
    Persistent (registry_propC x).
  Proof. rewrite /registry_propC /registry_word_pred. apply _. Qed.

  #[global] Instance registry_propC_timeless x :
    Timeless (registry_propC x).
  Proof. rewrite /registry_propC /registry_word_pred. apply _. Qed.

  Lemma registry_propC_intro (t : Thread) (W : WORLD) (C : CmptName) (w : LWord) (k : ObjKey) :
    key_of w = Some k →
    shape w →
    registry_member k C -∗
    registry_propC (t, W, C, w).
  Proof.
    iIntros (Hkey Hshape) "#Hel".
    rewrite /registry_propC /registry_word_pred /=.
    iExists k. iSplit; first done. iSplit; first done. iExact "Hel".
  Qed.

  (** The predicate does not depend on the thread nor on the world. *)
  Lemma registry_kind_ok (C : CmptName) :
    ⊢ seal_kind_ok SealGlobal C registry_propC.
  Proof.
    iSplit; first (iPureIntro; intros x; apply _).
    iIntros "!>" (t t' W W' w) "H". done.
  Qed.

  (** ** Allocation *)

  (** A key that is not in the map is registered for [C]. *)
  Lemma registry_auth_insert (M : gmap ObjKey CmptName) (k : ObjKey) (C : CmptName) :
    M !! k = None →
    registry_auth M
    ==∗
    registry_auth (<[k := C]> M) ∗
    registry_member k C.
  Proof.
    iIntros (HM) "Hauth".
    rewrite /registry_auth /registry_member.
    iMod (ghost_map_insert_persist k C HM with "Hauth") as "[Hauth #Hel]".
    iModIntro. iFrame "Hauth Hel".
  Qed.

  (** The registry, with the contents of the keys of [M]. *)
  Lemma registry_alloc (E : coPset) (M : gmap ObjKey CmptName) :
    registry_auth M -∗
    ▷ ([∗ map] k ↦ C ∈ M, sealed_obj_resources C k)
    ={E}=∗
    registry_inv.
  Proof.
    iIntros "Hauth Hcontents".
    rewrite /registry_inv /registry_auth.
    iApply (na_inv_alloc (tpool th) E N with "[Hauth Hcontents]").
    iExists M. iFrame "Hauth". iExact "Hcontents".
  Qed.

  (** The empty registry. *)
  Lemma registry_alloc_empty (E : coPset) :
    registry_auth ∅
    ={E}=∗
    registry_inv.
  Proof.
    iIntros "Hauth".
    iApply (registry_alloc E ∅ with "Hauth").
    iNext. by rewrite big_sepM_empty.
  Qed.

  (** A new object is registered for [C], with its contents. The contents
      of one key are exclusive: a key that is already registered cannot be
      registered again. *)
  Lemma registry_insert (E F : coPset) (C : CmptName) (k : ObjKey) :
    ↑N ⊆ F → ↑N ⊆ E →
    registry_inv -∗
    (∀ C', ▷ sealed_obj_resources C' k -∗ ▷ sealed_obj_resources C k -∗ ▷ False) -∗
    ▷ sealed_obj_resources C k -∗
    na_own (tpool th) F
    ={E}=∗
    registry_member k C ∗
    na_own (tpool th) F.
  Proof.
    iIntros (HF HE) "#Hreg Hexcl Hk Hna".
    iMod (na_inv_acc with "Hreg Hna") as "(Hopen & Hna & Hclose)"; [done|done|].
    iDestruct "Hopen" as (M) "[>Hauth Hcontents]".
    destruct (M !! k) as [C'|] eqn:HM.
    - iEval (rewrite (big_sepM_delete (λ k' C', sealed_obj_resources C' k') _ _ _ HM)) in "Hcontents".
      iDestruct "Hcontents" as "[Hk' _]".
      iDestruct ("Hexcl" with "Hk' Hk") as ">[]".
    - iMod (ghost_map_insert_persist k C HM with "Hauth") as "[Hauth #Hel]".
      iCombine "Hk Hcontents" as "Hcontents".
      iEval (rewrite -(big_sepM_insert (λ k' C', sealed_obj_resources C' k') _ _ _ HM)) in "Hcontents".
      iMod ("Hclose" with "[- $Hna]") as "Hna".
      { iExists (<[k := C]> M). iFrame "Hauth". iExact "Hcontents". }
      iModIntro. iFrame "Hna". iExact "Hel".
  Qed.

  (** ** Unsealing

      A valid word sealed with [o] has a registered key, whose contents are
      taken out of the registry under a later; the registry is closed again
      with any contents of the same key. The validity of a sealed word does
      not depend on the world, so [W] is any world.

      The contents may mention [interp]: they stay under the later, and no
      [>] goes over them. *)
  Lemma registry_acc (E F : coPset) (W : WORLD) (C : CmptName) (sb : Sealable) (π : option AId) :
    ↑N ⊆ F → ↑N ⊆ E →
    get_tag_sealable sb = true →
    registry_inv -∗
    o ↪ₒ{SealGlobal} registry_propC -∗
    interp W C (WSealed o sb @@? π) -∗
    na_own (tpool th) F
    ={E}=∗
    ∃ k : ObjKey,
      ⌜ key_of (lforce_global (WSealable sb @@? π)) = Some k ⌝ ∗
      ⌜ shape (lforce_global (WSealable sb @@? π)) ⌝ ∗
      ▷ sealed_obj_resources C k ∗
      na_own (tpool th) (F ∖ ↑N) ∗
      (▷ sealed_obj_resources C k ∗
       na_own (tpool th) (F ∖ ↑N)
       ={E}=∗
       na_own (tpool th) F).
  Proof.
    iIntros (HF HE Htag) "#Hreg #Hspred #Hinterp Hna".
    iDestruct (interp_sb_elim W C o SealGlobal registry_propC sb π Htag
                with "Hspred Hinterp") as "[HP _]".
    (* The seal predicate is timeless: its later goes. *)
    iMod "HP" as (k) "(%Hkey & %Hshape & #Hel)".
    iMod (na_inv_acc with "Hreg Hna") as "(Hopen & Hna & Hclose)"; [done|done|].
    iDestruct "Hopen" as (M) "[>Hauth Hcontents]".
    iDestruct (ghost_map_lookup with "Hauth Hel") as %HM.
    iEval (rewrite (big_sepM_delete (λ k' C', sealed_obj_resources C' k') _ _ _ HM)) in "Hcontents".
    iDestruct "Hcontents" as "[Hk Hcontents]".
    iModIntro.
    iExists k. iFrame "Hk Hna".
    iSplit; first (iPureIntro; exact Hkey).
    iSplit; first (iPureIntro; exact Hshape).
    iIntros "[Hk Hna]".
    iCombine "Hk Hcontents" as "Hcontents".
    iEval (rewrite -(big_sepM_delete (λ k' C', sealed_obj_resources C' k') _ _ _ HM)) in "Hcontents".
    iApply ("Hclose" with "[- $Hna]").
    iExists M. iFrame "Hauth". iExact "Hcontents".
  Qed.

  (** ** Validity

      A word sealed with [o] whose key is registered for [C] is valid in
      [C], in every world. *)
  Lemma registry_sealed_interp (W : WORLD) (C : CmptName) (sb : Sealable) (π : option AId) (k : ObjKey) :
    key_of (lforce_global (WSealable sb @@? π)) = Some k →
    shape (lforce_global (WSealable sb @@? π)) →
    o ↪ₒ{SealGlobal} registry_propC -∗
    registry_member k C -∗
    sealed_payload_ok (WSealable sb @@? π) -∗
    interp W C (WSealed o sb @@? π).
  Proof.
    iIntros (Hkey Hshape) "#Hs #Hel #Hpayload".
    iApply (interp_sb_intro_global W C o registry_propC sb π with "[] Hs [] Hpayload").
    - iApply registry_kind_ok.
    - iApply bi.later_intro.
      iApply (registry_propC_intro th W C _ k Hkey Hshape with "Hel").
  Qed.

End SealRegistry.

(** ** Static sealed objects

    The key of a sealed capability: its base, with its identifier for a
    heap object. The shape of a sealed static object: a Global read-only
    capability on one static word, outside the shadow table. *)

Section StaticSealedObjects.
  Context `{MP: MachineParameters}.

  Definition sealed_cap_key (w : LWord) : option LAddr :=
    match w.(lw) with
    | WSealable (SCap _ _ _ b _ _) => Some (addr_key w.(lprov) b)
    | _ => None
    end.

  Definition static_word_shape (w : LWord) : Prop :=
    ∃ a : Addr,
      w = lword_of_word (WSealable (SCap true RO Global a (a ^+ 1) a)) ∧
      withinBounds a (a ^+ 1) a = true ∧
      is_shadow_address a = false.

  Lemma static_word_shape_intro (a : Addr) :
    withinBounds a (a ^+ 1) a = true →
    is_shadow_address a = false →
    static_word_shape (lword_of_word (WSealable (SCap true RO Global a (a ^+ 1) a))).
  Proof. intros Hbounds Hshadow. by exists a. Qed.
End StaticSealedObjects.
