From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec_blocks.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode.

Section Heap_Temporal_Safety_Main.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma hts_main_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (C_f : Sealable)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := hts_main_imports C_f in

    disjoint_from_shadow pc_b pc_e ->
    disjoint_from_shadow cgp_b cgp_e ->
    disjoint_from_heap cgp_b cgp_e ->
    is_heap_address cgp_b = false ->
    (* Incoming saved registers are nonheap; the buffer itself is kept in
       the private data slot and explicitly reloaded after the first call. *)
    is_heap_cap (default (WInt 0) (rmap !! cra)) = false ->
    is_heap_cap (default (WInt 0) (rmap !! cs1)) = false ->
    is_heap_cap (default (WInt 0) (rmap !! cs0)) = false ->
    Nswitcher ## Nassert ->
    Nswitcher ## Nallocator_service ->
    Nassert ## Nallocator_service ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->

    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W_init_C) ->
    (cgp_b ^+1 )%a ∉ dom (std W_init_C) ->

    frame_match Ws Cs cstk W_init_C C ->
    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ allocator_ctx ∗ allocator_service_ctx ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a hts_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ hts_main_data ]]

      ∗ world_interp W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W_init_C C (WCap true RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Allocate: use the physical malloc contract and its known-to-known
       switcher wrapper, then save the buffer in the private CGP slot.

       BLOCKED at the first unknown call: [interp] currently excludes all
       nonempty RW heap ranges. A future heap-world interpretation must
       share the initially safe cell and track adversarial free calls.

       After return: reload and check the tag. Quarantine leads to Halt;
       a live result needs an ownership-recovery lemma, not just a tag fact.
       Overwrite its arbitrary contents with the private capability, then
       call the known allocator to quarantine the cell before any unknown
       code runs again. Restore the world with dangling aliases harmless.

       The second unknown call uses the integer argument zero. Finally apply
       hts_assert_prep_spec and assert_spec. No unfinished lemma is assumed. *)
  Abort.
End Heap_Temporal_Safety_Main.
