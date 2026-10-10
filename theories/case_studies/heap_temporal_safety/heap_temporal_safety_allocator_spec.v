From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import switcher_spec_KtK region_keys.
From griotte Require Import heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec allocator_switcher_spec.

(** The trusted calls of [main] to [malloc] and [free] are instances of the
    public switcher-call specifications: [malloc] at size one with the empty
    freshness set, and [free] of the whole object. The argument is in [ca0]
    (D36), and the allocator-entry condition of [free] is discharged inside
    [allocator_free_switcher_spec] (D23). Neither call requires the private
    pointer to satisfy [interp]. *)

Section Heap_Temporal_Safety_Allocator.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {FA : FreeAuth Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}.

  Definition hts_malloc_result : LWord -> LWord -> iProp Σ :=
    allocator_malloc_result ∅ 1.

  Lemma hts_malloc_known_function
    (wcgp wcra wcs0 wcs1 : LWord)
    (b_stk e_stk a_stk : Addr) (arg_rmap : LReg) (cstk : CSTK) :
    arg_rmap !! ca0 = Some (lword_of_word (WInt 1)) ->
    allocator_service_ctx ⊢
    switcher_cc_specification_known_to_known_function
      emp hts_malloc_result wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk arg_rmap cstk allocator_malloc_nargs ⊤
      allocator_pcc_b allocator_pcc_e allocator_cgp_b allocator_cgp_e
      allocator_malloc_pcc_off.
  Proof.
    intros Harg.
    by apply (allocator_malloc_switcher_spec ∅ 1); [lia|].
  Qed.

  Definition hts_free_result (ι : AId) : LWord -> LWord -> iProp Σ :=
    allocator_free_result ι.

  Lemma hts_free_known_function
    (wcgp wcra wcs0 wcs1 : LWord)
    (b_stk e_stk a_stk b e a : Addr) (arg_rmap : LReg) (cstk : CSTK)
    (p : Perm) (g : Locality) (ι : AId) (ws : list LWord) :
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    length ws = length (finz.seq_between b e) ->
    arg_rmap !! ca0 = Some (WCap true p g b e a @@ ι) ->
    allocator_service_ctx ⊢
    switcher_cc_specification_known_to_known_function
      (alloc_obj ι b e ∗
       free_auth_held ι ∗
       [[b,e]] ↦ₕ[ι] [[ws]])
      (hts_free_result ι) wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk arg_rmap cstk allocator_free_nargs ⊤
      allocator_pcc_b allocator_pcc_e allocator_cgp_b allocator_cgp_e
      allocator_free_pcc_off%I.
  Proof. apply allocator_free_switcher_spec. Qed.

End Heap_Temporal_Safety_Allocator.
