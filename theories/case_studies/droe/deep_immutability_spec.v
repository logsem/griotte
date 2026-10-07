From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call deep_immutability.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import droe_spec_states droe_spec_world
  droe_spec_init_blocks_1 droe_spec_share_blocks_2 droe_spec_assert_blocks_3.

Section DROE.
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

  Lemma droe_spec

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

    let imports := droe_main_imports C_f in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length droe_main_code)%a ->

    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W_init_C) ->
    (cgp_b ^+1 )%a ∉ dom (std W_init_C) ->

    frame_match Ws Cs cstk W_init_C C ->
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
      ∗ codefrag pc_a droe_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ droe_main_data ]]

      ∗ world_interp W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W_init_C C (WCap RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [droe_init_blocks_1_spec]: block 0, initialise the data,
       - [droe_share_blocks_2_spec]: blocks 1-3, fetch the imports and jump to
         the switcher,
       - [droe_world_share]: share the data in the world, as permanent
         read-only addresses,
       - [switcher_cc_specification]: call to the adversary,
       - [droe_world_return]: open the world to get [b] back, still equal
         to 42,
       - [droe_assert_blocks_3_spec]: blocks 3-5, assert that [b] is
         unchanged and halt. *)
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
    iApply (droe_init_blocks_1_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hcgp_b $Hcgp_a $Hcode_main]");
      [done|done|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & [%wct0' Hct0] & [%wct1' Hct1] & [%wct2' Hct2]
                    & Hcgp_b & Hcgp_a & Hcode_main)".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iAssert (droe_static_mem pc_b pc_a C_f) with "[$Himports $Hcode_main]" as "Hmem".
    iApply (droe_share_blocks_2_spec with
             "[- $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hcs0 $Hcra $Hmem]"); first done.
    iNext; iIntros "(HPC & Hcra & Hct0 & Hct1 & Hct2 & Hct3 & Hcs0 & Hmem)".
    iDestruct "Hmem" as "((Himport_switcher & Himport_assert & Himport_C_f) & Hcode_main)".

    (* Share the data in the world *)
    iMod (droe_world_share with "Hworld_interp_C Hstack_revoked_W0 Hinterp_W0_C_f Hcgp_b Hcgp_a")
      as "(Hworld_interp_C & #Hrel_cgp_b & #Hinterp_ca0 & #Hinterp_W3_C_f
           & #Hstack_revoked_W3 & %Hstack_revoked_W3)"; [done..|].
    iInsertRegs "Hrmap" ["Hca1"; "Hct0"; "Hct2"; "Hct3"].
    iDestruct (switcher_call_args_1 with "Hca0 Hinterp_ca0 Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to the adversary *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W3 $Hcstk_frag
              $Hinterp_W3_C_f $HentryC_f $HK]"); [done|done|].
    iSplit; first done.
    iNext.
    clear dependent arg_rmap rmap' stk_mem rmap.
    iIntros (W4 rmap stk_mem l')
      "( _ & _ & _
      & %Hrelated_pub_W3ext_W4 & _ & %Hrmap_dom & _ & _
      & Hna & [%Hcsp_bounds _]
      & Hworld_interp_C
      & _
      & HPC & Hcgp & Hcra & Hcs0 & _ & _
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & _ & _)".
    iEval (cbn) in "HPC".

    (* Open the world to get b back *)
    iMod (droe_world_return with "Hworld_interp_C Hrel_cgp_b") as "Hcgp_b"; eauto.
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;cnull]
      as ["Hct0"; "Hct1"; "Hct2"; "Hct3"; "Hct4"; "Hcnull"].

    (* Blocks 3-5: assert that b is unchanged and halt *)
    iApply (droe_assert_blocks_3_spec _ _ _ _ _ C_f with
             "[$Hassert $Hna $HPC $Hcgp $Hca0 $Hca1 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hcnull
              $Hcs0 $Hcra $Hcgp_b $Himport_assert $Hcode_main]"); done.
  Qed.

End DROE.
