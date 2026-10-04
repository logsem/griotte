From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import switcher_spec_KtK region_keys.
From griotte Require Import heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec allocator_switcher_spec.

(** The trusted calls of [main] to [malloc] and [free] are instances of the
    public switcher-call specifications: [malloc] at size one with the empty
    freshness set, and [free] of the whole object. The allocator-entry
    condition of [free] is discharged inside [allocator_free_switcher_spec]
    (D23). Neither call requires the private
    pointer to satisfy [interp]. Both take the caller's allocator capability
    in [ca0], with its owner token and owner word, which they give back; the
    argument is then in [ca1]. *)

Section Heap_Temporal_Safety_Allocator.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocator_ownerg : allocatorOwnerG Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}.

  Local Instance free_auth_owner_inst : FreeAuth Σ := free_auth_owner.

  Definition hts_malloc_result (a_owner : Addr) (id : Z) (Ω : gset AId)
    : LWord -> LWord -> iProp Σ :=
    allocator_malloc_result ∅ a_owner id Ω 1.

  Lemma hts_malloc_known_function
    (wcgp wcra wcs0 wcs1 : LWord)
    (b_stk e_stk a_stk : Addr) (arg_rmap : LReg) (cstk : CSTK)
    (g_owner : Locality) (a_owner : Addr) (id : Z) (Ω : gset AId) :
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    arg_rmap !! ca0 = Some (lword_of_word (allocator_capability g_owner a_owner)) ->
    arg_rmap !! ca1 = Some (lword_of_word (WInt 1)) ->
    allocator_service_ctx ⊢
    switcher_cc_specification_known_to_known_function
      (allocator_owner_id id Ω ∗
       a_owner ↦ₐ WInt id)
      (hts_malloc_result a_owner id Ω) wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk arg_rmap cstk allocator_malloc_nargs ⊤
      allocator_pcc_b allocator_pcc_e allocator_cgp_b allocator_cgp_e
      allocator_malloc_pcc_off.
  Proof.
    intros.
    by apply (allocator_malloc_switcher_spec ∅ g_owner); [lia|..].
  Qed.

  Definition hts_free_result (a_owner : Addr) (id : Z) (Ω : gset AId)
    (ι : AId) : LWord -> LWord -> iProp Σ :=
    allocator_free_result a_owner id Ω ι.

  Lemma hts_free_known_function
    (wcgp wcra wcs0 wcs1 : LWord)
    (b_stk e_stk a_stk b e a : Addr) (arg_rmap : LReg) (cstk : CSTK)
    (p : Perm) (g : Locality) (ι : AId) (ws : list LWord)
    (g_owner : Locality) (a_owner : Addr) (id : Z) (Ω : gset AId) :
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    length ws = length (finz.seq_between b e) ->
    arg_rmap !! ca0 = Some (lword_of_word (allocator_capability g_owner a_owner)) ->
    arg_rmap !! ca1 = Some (WCap true p g b e a @@ ι) ->
    allocator_service_ctx ⊢
    switcher_cc_specification_known_to_known_function
      (allocator_owner_id id Ω ∗
       ⌜ι ∈ Ω⌝ ∗
       a_owner ↦ₐ WInt id ∗
       alloc_obj ι b e ∗
       free_right ι ∗
       [[b,e]] ↦ₕ[ι] [[ws]])
      (hts_free_result a_owner id Ω ι) wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk arg_rmap cstk allocator_free_nargs ⊤
      allocator_pcc_b allocator_pcc_e allocator_cgp_b allocator_cgp_e
      allocator_free_pcc_off%I.
  Proof. apply allocator_free_switcher_spec. Qed.

End Heap_Temporal_Safety_Allocator.
