From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call deep_locality.
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
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma dle_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := dle_main_imports C_f in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code)%a ->

    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W0) ->
    (cgp_b ^+1 )%a ∉ dom (std W0) ->

    frame_match Ws Cs cstk W0 C ->
    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a dle_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ dle_main_data ]]

      ∗ world_interp W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W0 C (WCap RWL Local csp_b csp_e csp_b)

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
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_a Hframe_match
            )
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      )".
    iExtractList "Hrmap" [cra;ca0;ca1;ct0;ct1;ct2;ct3;cs0;cs1]
      as ["Hcra"; "Hca0"; "Hca1"; "Hct0"; "Hct1"; "Hct2"; "Hct3"; "Hcs0"; "Hcs1"].
    iRegionSplit "Hcgp_main" as "[Hcgp_b Hcgp_a]".
    iRegionSplit "Himports_main" as "Himports".

    (* Revoke the world to get the stack frame *)
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_interp_C]")
      as (l) "(_ & Hworld_interp_C & Hstack_revoked_W0 & >%Hstack_revoked_W0
               & >[%stk_mem Hstk] & _ & _)".

    (* Block 0: initialise the data *)
    iApply (dle_init_blocks_1_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hcgp_b $Hcgp_a $Hcode_main]");
      [done|done|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & [%wct0' Hct0] & [%wct1' Hct1] & [%wct2' Hct2]
                    & Hcgp_b & Hcgp_a & Hcode_main)".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iAssert (dle_static_mem pc_b pc_a C_f) with "[$Himports $Hcode_main]" as "Hmem".
    iApply (dle_share_blocks_2_spec with
             "[- $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hcs0 $Hcs1 $Hcra $Hmem]"); first done.
    iNext; iIntros "(HPC & Hcra & Hct0 & Hct1 & Hct2 & Hct3 & Hcs0 & Hcs1 & Hmem)".
    iDestruct "Hmem" as "((Himport_switcher & Himport_assert & Himport_C_f) & Hcode_main)".

    (* Share the data in the world *)
    iMod (dle_world_share with "Hworld_interp_C Hstack_revoked_W0 Hinterp_W0_C_f Hcgp_b Hcgp_a")
      as "(Hworld_interp_C & #Hinterp_ca0 & #Hinterp_W3_C_f & #Hstack_revoked_W3
           & %Hstack_revoked_W3)"; [done..|].
    iInsertRegs "Hrmap" ["Hca1"; "Hct0"; "Hct2"; "Hct3"].
    iDestruct (switcher_call_args_1 with "Hca0 Hinterp_ca0 Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* First call to the adversary *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W3 $Hcstk_frag
              $Hinterp_W3_C_f $HentryC_f $HK]"); [done|done|].
    iSplit; first done.
    iNext.
    clear dependent arg_rmap rmap' stk_mem rmap.
    iIntros (W4 rmap stk_mem l')
      "( %Hl_unk' & Hrevoked_l' & _
      & %Hrelated_pub_W3ext_W4 & _ & %Hrmap_dom & #Hstack_revoked_W4 & %Hstack_revoked_W4
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn) in "HPC".

    (* Revoke the world to get b back *)
    iMod (dle_world_return with "Hrevoked_l' Hinterp_W3_C_f Hstack_revoked_W4")
      as "([%wcgp_b Hcgp_b] & #Hinterp_W5_C_f & #Hstack_revoked_W5)"; eauto.
    { solve_addr. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3] as ["Hct0"; "Hct1"; "Hct2"; "Hct3"].

    (* Block 3: overwrite b and jump to the switcher *)
    iApply (dle_overwrite_blocks_3_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hcra $Hcs0 $Hcs1 $Hcgp_b $Hcode_main]");
      [done|done|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hcra & Hcs0 & Hcs1 & Hcgp_b & Hcode_main)".
    iInsertRegs "Hrmap" ["Hca1"; "Hct0"; "Hct2"; "Hct3"].
    iDestruct (switcher_call_args_1 (revoke W4) C with "Hca0 [] Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }
    { iApply interp_int. }

    (* Second call to the adversary *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W5 $Hcstk_frag
              $Hinterp_W5_C_f $HentryC_f $HK]"); [done|done|].
    iSplit; first done.
    iNext.
    clear dependent arg_rmap rmap' stk_mem rmap.
    iIntros (W6 rmap stk_mem l0)
      "( _ & _ & _ & _ & _ & %Hrmap_dom & _ & _
      & Hna & _ & _ & _
      & HPC & Hcgp & Hcra & _ & _ & _ & _ & _
      & Hrmap & _ & _)".
    iEval (cbn) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;cnull]
      as ["Hct0"; "Hct1"; "Hct2"; "Hct3"; "Hct4"; "Hcnull"].

    (* Blocks 3-5: assert that b is unchanged and halt *)
    iApply (dle_assert_blocks_4_spec _ _ _ _ _ C_f with
             "[$Hassert $Hna $HPC $Hcgp $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hcnull $Hcra
              $Hcgp_b $Himport_assert $Hcode_main]"); done.
  Qed.

End DLE.
