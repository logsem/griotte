From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call switcher_exception deep_locality.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import dle_spec_states dle_spec_world
  dle_spec_init_blocks_1 dle_spec_share_blocks_2
  dle_spec_overwrite_blocks_3 dle_spec_assert_blocks_4.

Section DLE.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  Lemma dle_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nswitcher : namespace)
    :

    let imports := dle_main_imports C_f in

    Nswitcher ## N_trap ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    disjoint_from_mmio cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->

    dom rmap = all_registers_s ∖ {[ cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code)%a ->

    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    (pc_b + dle_label ".Ldle_init")%a = Some pc_a ->
    (* The stack holds the spill of the switcher calls *)
    (csp_b + 4 <= csp_e)%Z ->

    LNonHeap (cgp_b)%a ∉ dom (std W0) ->
    LNonHeap (cgp_b ^+1 )%a ∉ dom (std W0) ->

    is_heap_cap (WSealed ot_switcher C_f) = false ->
    frame_match Ws Cs [] W0 C ->
    (
      assert_static b_assert e_assert a_flag
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ switcher_static
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ₚ WCap true RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a dle_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> dle_main_data ]]

      ∗ world_interp W0 C

      ∗ interp_continuation [] Ws Cs

      ∗ cstack_frag []

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ C_f ↦ₑ□{nargs} 1
      ∗ interp W0 C (WCap true RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [dle_init_blocks_1_spec]: block 0, initialise the data,
       - [dle_share_blocks_2_spec]: blocks 1-3, fetch the imports and jump to
         the switcher,
       - [dle_world_share]: share the data in the world,
       - [switcher_cc_specification]: first call to the adversary,
       - [dle_world_return]: revoke the world to get [b] back,
       - [dle_overwrite_blocks_3_spec]: block 3, overwrite [b] and jump to the
         switcher,
       - [switcher_cc_specification]: second call to the adversary,
       - [dle_assert_blocks_4_spec]: blocks 3-5, assert that [b] is unchanged
         and halt. *)
    intros imports; subst imports.
    iIntros (HNtrap Hpc_shadow Hpc_nonheap Hcgp_shadow Hcgp_range Hrmap_dom Hrmap_init
               HsubBounds Hcgp_contiguous Himports_contiguous Hstk_min Hcgp_b Hcgp_a Hsealed_nonheap
               Hframe_match
            )
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      )".
    iExtractList "Hrmap" [cra;ca0;ca1;ct0;ct1;ct2;cs0;cs1]
      as ["Hcra"; "Hca0"; "Hca1"; "Hct0"; "Hct1"; "Hct2"; "Hcs0"; "Hcs1"].
    iEval (cbn [fmap list_fmap dle_main_data dle_main_imports]) in "Hcgp_main Himports_main".
    iRegionSplit "Hcgp_main" as "[Hcgp_b Hcgp_a]".
    iRegionSplit "Himports_main" as "Himports".
    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_mmio Hstk_heap]; first done.

    (* Revoke the world to get the stack frame *)
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_interp_C]")
      as (l) "(_ & Hworld_interp_C & Hstack_revoked_W0 & >%Hstack_revoked_W0
               & >[%stk_mem Hstk] & _ & _)".

    (* Block 0: initialise the data *)
    iApply (dle_init_blocks_1_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hcgp_b $Hcgp_a $Hcode_main]");
      [done|done|done|done|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & [%wct0' Hct0] & [%wct1' Hct1] & [%wct2' Hct2]
                    & Hcgp_b & Hcgp_a & Hcode_main)".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iAssert (dle_static_mem pc_b pc_a C_f) with "[$Himports $Hcode_main]" as "Hmem".
    iApply (dle_share_blocks_2_spec with
             "[- $HPC $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcra $Hmem]");
      first (rewrite /dle_code_bounds; eauto 10).
    iNext; iIntros (mie) "(HPC & Hcra & Hct0 & Hct1 & Hcs0 & Hcs1 & Hmem)".
    iDestruct "Hmem" as "((Himport_switcher & Himport_assert & Himport_C_f) & Hcode_main)".

    (* Share the data in the world *)
    iMod (dle_world_share with "Hworld_interp_C Hstack_revoked_W0 Hinterp_W0_C_f Hcgp_b Hcgp_a")
      as "(Hworld_interp_C & #Hinterp_ca0 & #Hinterp_W3_C_f & #Hstack_revoked_W3
           & %Hstack_revoked_W3)"; [done..|].
    iInsertRegs "Hrmap" ["Hca1"; "Hct0"; "Hct2"].
    iDestruct (switcher_call_args_1 with "Hca0 Hinterp_ca0 Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* First call to the adversary *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W3 $Hcstk_frag
              $Hinterp_W3_C_f $HentryC_f $HK]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { solve_addr+. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    { exact HNtrap. }
    iSplit; first done.
    iSplit; last first.
    { (* The spill cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits; solve_addr+Hstk_min. }
    iNext.
    clear dependent arg_rmap rmap' stk_mem rmap.
    iIntros (W4 rmap stk_mem l' rcgp rcra rcs0 rcs1)
      "( %Hl_unk' & Hrevoked_l' & _
      & %Hrelated_pub_W3ext_W4 & _ & %Hrmap_dom & #Hstack_revoked_W4 & %Hstack_revoked_W4
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & Hrcs1).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= (proj1 Hcgp_range) /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0; [|exact switcher_call_sentry_not_heap].
    apply load_heap_nonheap in Hrcs1; [|exact Hsealed_nonheap].
    subst rcgp rcra rcs0 rcs1.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".

    (* Revoke the world to get b back *)
    iMod (dle_world_return with "Hrevoked_l' Hinterp_W3_C_f Hstack_revoked_W4")
      as "([%wcgp_b Hcgp_b] & #Hinterp_W5_C_f & #Hstack_revoked_W5)"; eauto.
    { solve_addr. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2] as ["Hct0"; "Hct1"; "Hct2"].

    (* Block 3: overwrite b and jump to the switcher *)
    iApply (dle_overwrite_blocks_3_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hcra $Hcs0 $Hcs1 $Hcgp_b $Hcode_main]");
      [done|done|done|].
    iNext; iIntros (mie') "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hcra & Hcs0 & Hcs1 & Hcgp_b & Hcode_main)".
    iInsertRegs "Hrmap" ["Hca1"; "Hct0"; "Hct2"].
    iDestruct (switcher_call_args_1 (revoke W4) C with "Hca0 [] Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { iApply interp_int. }

    (* Second call to the adversary *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W5 $Hcstk_frag
              $Hinterp_W5_C_f $HentryC_f $HK]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { solve_addr+. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { destruct mie'; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    { exact HNtrap. }
    iSplit; first done.
    iSplit; last first.
    { (* The spill cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits; solve_addr+Hstk_min. }
    iNext.
    clear dependent arg_rmap rmap' stk_mem rmap.
    iIntros (W6 rmap stk_mem l0 rcgp rcra rcs0 rcs1)
      "( _ & _ & _ & _ & _ & %Hrmap_dom & _ & _
      & Hna & _ & _ & _
      & HPC & Hcgp & Hcra & _ & _ & _ & _ & _
      & Hrmap & _ & _ & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & _ & _).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= (proj1 Hcgp_range) /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    subst rcgp rcra.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ca2;cnull]
      as ["Hct0"; "Hct1"; "Hct2"; "Hca2"; "Hcnull"].

    (* Blocks 3-5: assert that b is unchanged and halt *)
    iApply (dle_assert_blocks_4_spec _ _ _ _ _ C_f with
             "[$Hassert $Hna $HPC $Hcgp $Hct0 $Hct1 $Hct2 $Hca2 $Hcra
              $Hcgp_b $Himport_assert $Hcode_main]");
      [rewrite /dle_code_bounds; eauto 10|done..].
  Qed.

End DLE.
