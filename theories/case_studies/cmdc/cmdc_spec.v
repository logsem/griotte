From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call switcher_exception_stub cmdc.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import cmdc_spec_states cmdc_spec_world
  cmdc_spec_init_blocks_1 cmdc_spec_call_blocks_2 cmdc_spec_check_blocks_3
  cmdc_spec_prep_blocks_4 cmdc_spec_halt_blocks_5.

Section CMDC.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {B C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.


  Lemma cmdc_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list LWord)

    (φ : language.val griotte_lang -> iProp Σ)
    (Nswitcher : namespace)
    :

    let imports := cmdc_main_imports B_f C_g in

    Nswitcher ## N_trap ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_mmio_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    is_mmio_address (cgp_b ^+ 1)%a = false ->
    is_heap_address (cgp_b ^+ 1)%a = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->

    dom rmap = all_registers_s ∖ {[ cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (lword_of_word (WInt 0)) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + cmdc_label ".Lcmdc_init")%a = Some pc_a ->
    (* The stack holds the spill of the switcher calls *)
    (csp_b + 4 <= csp_e)%Z ->

    LNonHeap cgp_b ∉ dom (std W_init_B) ->
    LNonHeap (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    is_heap_cap (WSealed ot_switcher B_f) = false ->
    is_heap_cap (WSealed ot_switcher C_g) = false ->

    (* We suppose that the stack region is already revoked in each worlds.
       It's because the worlds are closed and if they we're Temporary,
       then the points-to predicates would be own by both `world_interp` at the same time,
       which is not possible. *)
    revoked_addresses W_init_B (finz.seq_between csp_b csp_e) ->
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->

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
      ∗ codefrag_pers pc_a cmdc_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> cmdc_main_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ world_interp W_init_B B
      ∗ world_interp W_init_C C

      ∗ interp_continuation [] Ws Cs

      ∗ cstack_frag []

      ∗ interp W_init_B B (WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g)

      ∗ B_f ↦ₑ□{nargs} cmdc_B_f_args
      ∗ C_g ↦ₑ□{nargs} cmdc_C_g_args

      (* initial stack are revoked in both worlds *)
      ∗ StackRevokedResources W_init_B B (finz.seq_between csp_b csp_e)
      ∗ StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e)

      ∗ ▷ (na_own cerise_nais ⊤
              -∗ WP Instr Halted {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [cmdc_init_blocks_1_spec]: block 0, initialise [b] and [c], and
         prepare the argument [b] of the call to [B.f],
       - [cmdc_call_blocks_2_spec cmdc_call_B]: blocks 1-3, fetch the
         imports and jump to the switcher,
       - [cmdc_world_share]: share [b] in the world of [B],
       - [switcher_cc_specification]: call to [B.f],
       - [cmdc_world_return]: get [b] back from the world of [B],
       - [cmdc_check_blocks_3_spec cmdc_call_B]: blocks 3-4, assert that
         [c] is unchanged,
       - [cmdc_prep_blocks_4_spec]: block 5, overwrite [b] and prepare the
         argument [c] of the call to [C.g],
       - [cmdc_call_blocks_2_spec cmdc_call_C]: blocks 6-8, fetch the
         imports and jump to the switcher,
       - [cmdc_world_share]: share [c] in the world of [C],
       - [switcher_cc_specification]: call to [C.g],
       - [cmdc_check_blocks_3_spec cmdc_call_C]: blocks 8-9, assert that
         [b] is unchanged,
       - [cmdc_halt_blocks_5_spec]: block 10, halt. *)
    intros imports; subst imports.
    iIntros (HNtrap Hpc_shadow Hpc_nonheap Hcgp_shadow Hcgp_heap Hcgp1_shadow Hcgp1_heap
               Hstk_shadow Hstk_heap Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hstk_min Hcgp_b Hcgp_c
               HB_f_nonheap HC_g_nonheap
               Hrevoked_stack_B Hrevoked_stack_C)
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_interp_B
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & #HentryB_f & #HentryC_g
      & Hstack_revoked_B & Hstack_revoked_C
      & Hφ)".
    assert (rmap !! cs0 = Some (lword_of_word (WInt 0))) as Hcs0_init.
    { apply Hrmap_init. rewrite Hrmap_dom; set_solver+. }
    assert (rmap !! cs1 = Some (lword_of_word (WInt 0))) as Hcs1_init.
    { apply Hrmap_init. rewrite Hrmap_dom; set_solver+. }
    iExtractList "Hrmap" [ca0;ca1;ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hca0";"Hca1";"Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].
    iEval (cbn [fmap list_fmap cmdc_main_data cmdc_main_imports]) in "Hcgp_main Himports_main".
    iRegionSplit "Hcgp_main" as "[Hcgp_b Hcgp_c]".
    iRegionSplit "Himports_main"
      as "(Himport_switcher & Himport_assert & Himport_B_f & Himport_C_g)".
    assert (cmdc_code_bounds pc_b pc_e pc_a B_f C_g) as Hbounds
      by (rewrite /cmdc_code_bounds; eauto 10).

    (* Block 0: initialise b and c *)
    iApply (cmdc_init_blocks_1_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hcgp_b $Hcgp_c $Hcode_main]");
      [done..|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & [%wct0' Hct0] & [%wct1' Hct1]
                    & Hcgp_b & Hcgp_c & Hcode_main)".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iApply (cmdc_call_blocks_2_spec cmdc_call_B with
             "[- $HPC $Hctp $Hct1 $Hcra
              $Himport_switcher $Himport_B_f $Hcode_main]"); first done.
    iNext; iIntros (mie) "(HPC & Hctp & Hct1 & Hcra
                    & Himport_switcher & Himport_B_f & Hcode_main)".

    (* Share b in the world of B *)
    iMod (cmdc_world_share _ _ _ (cgp_b ^+ 1)%a with
           "Hworld_interp_B Hstack_revoked_B Hinterp_Winit_B_f Hcgp_b Hcsp_stk")
      as "(Hworld_interp_B & #Hrel_cgp_b & #Hinterp_ca0 & #Hinterp_B_f
           & Hstack_revoked_B & %Hrevoked_B & %Hcgp_b_stk & Hcsp_stk)";
      [solve_addr|done..|].
    iInsertRegs "Hrmap" ["Hca1"; "Hctp"; "Hct0"].
    iDestruct (switcher_call_args_1 with "Hca0 Hinterp_ca0 Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to B.f *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $Hworld_interp_B $Hstack_revoked_B $Hcstk_frag
              $Hinterp_B_f $HentryB_f $HK]").
    { exact Hstk_shadow. }
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
    clear dependent arg_rmap rmap' rmap.
    iIntros (W_ret_B rmap stk_mem l rcgp rcra rcs0 rcs1)
      "( _ & _ & _ & %Hrelated_pub_B & _ & %Hrmap_dom & _ & _
      & Hna & %Hcsp_bounds
      & Hworld_interp_B
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hcsp_stk & HK & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & Hrcs1).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0; [|done].
    apply load_heap_nonheap in Hrcs1; [|done].
    subst rcgp rcra rcs0 rcs1.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".

    (* Get b back from the world of B *)
    iMod (cmdc_world_return with "Hworld_interp_B Hrel_cgp_b") as "[%wcgp_b Hcgp_b]";
      [done|done|solve_addr|done|].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ctp;ct0;ct1;ct2;ca2;cnull]
      as ["Hctp";"Hct0";"Hct1";"Hct2";"Hca2";"Hcnull"].

    (* Blocks 3-4: assert that c is unchanged *)
    iApply (cmdc_check_blocks_3_spec cmdc_call_B with
             "[- $Hassert $HPC $Hcgp $Hct0 $Hct1 $Hct2 $Hca2 $Hcra
              $Hcgp_c $Himport_assert $Hcode_main]"); [done|solve_addr|done|].
    iNext; iIntros "(HPC & Hcgp & Hct0 & Hct1 & Hct2 & Hca2 & Hcra
                    & Hcgp_c & Himport_assert & Hcode_main)".

    (* Block 5: overwrite b and prepare the argument c *)
    iApply (cmdc_prep_blocks_4_spec with
             "[- $HPC $Hcgp $Hca0 $Hca1 $Hct0 $Hct1 $Hcgp_b $Hcode_main]");
      [done..|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hca1 & [%wct0'' Hct0] & [%wct1'' Hct1]
                    & Hcgp_b & Hcode_main)".

    (* Blocks 6-8: fetch the imports and jump to the switcher *)
    iApply (cmdc_call_blocks_2_spec cmdc_call_C with
             "[- $HPC $Hctp $Hct1 $Hcra
              $Himport_switcher $Himport_C_g $Hcode_main]"); first done.
    iNext; iIntros (mie') "(HPC & Hctp & Hct1 & Hcra
                    & Himport_switcher & Himport_C_g & Hcode_main)".

    (* Share c in the world of C *)
    iMod (cmdc_world_share _ _ _ (cgp_b ^+ 2)%a with
           "Hworld_interp_C Hstack_revoked_C Hinterp_Winit_C_g Hcgp_c Hcsp_stk")
      as "(Hworld_interp_C & _ & #Hinterp_ca0_C & #Hinterp_C_g
           & Hstack_revoked_C & %Hrevoked_C & _ & Hcsp_stk)";
      [solve_addr|done..|].
    iInsertRegs "Hrmap" ["Hca1"; "Hctp"; "Hct0"; "Hct2"; "Hca2"; "Hcnull"].
    iDestruct (switcher_call_args_1 with "Hca0 Hinterp_ca0_C Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to C.g *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $Hworld_interp_C $Hstack_revoked_C $Hcstk_frag
              $Hinterp_C_g $HentryC_g $HK]").
    { exact Hstk_shadow. }
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
    clear dependent arg_rmap rmap' rmap stk_mem.
    iIntros (W_ret_C rmap stk_mem l' rcgp rcra rcs0 rcs1)
      "( _ & _ & _ & _ & _ & %Hrmap_dom & _ & _
      & Hna & _ & _ & _
      & HPC & Hcgp & Hcra & _ & _ & _ & _ & _
      & Hrmap & _ & _ & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & _ & _).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    subst rcgp rcra.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ca2;cnull]
      as ["Hct0";"Hct1";"Hct2";"Hca2";"Hcnull"].

    (* Blocks 8-9: assert that b is unchanged *)
    iApply (cmdc_check_blocks_3_spec cmdc_call_C with
             "[- $Hassert $HPC $Hcgp $Hct0 $Hct1 $Hct2 $Hca2 $Hcra
              $Hcgp_b $Himport_assert $Hcode_main]"); [done|solve_addr|done|].
    iNext; iIntros "(HPC & _ & _ & _ & _ & _ & _ & _ & _ & Hcode_main)".

    (* Block 10: halt *)
    iApply (cmdc_halt_blocks_5_spec with "[$HPC $Hcode_main Hφ Hna]"); first done.
    iNext; iApply ("Hφ" with "Hna").
  Qed.

  Lemma cmdc_spec_full

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list LWord)

    (φ : language.val griotte_lang -> iProp Σ)
    (Nswitcher : namespace)
    :

    let imports := cmdc_main_imports B_f C_g in

    Nswitcher ## N_trap ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_mmio_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    is_mmio_address (cgp_b ^+ 1)%a = false ->
    is_heap_address (cgp_b ^+ 1)%a = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->

    dom rmap = all_registers_s ∖ {[ cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (lword_of_word (WInt 0)) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + cmdc_label ".Lcmdc_init")%a = Some pc_a ->
    (* The stack holds the spill of the switcher calls *)
    (csp_b + 4 <= csp_e)%Z ->

    LNonHeap cgp_b ∉ dom (std W_init_B) ->
    LNonHeap (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    is_heap_cap (WSealed ot_switcher B_f) = false ->
    is_heap_cap (WSealed ot_switcher C_g) = false ->

    revoked_addresses W_init_B (finz.seq_between csp_b csp_e) ->
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->

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
      ∗ codefrag_pers pc_a cmdc_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> cmdc_main_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ world_interp W_init_B B
      ∗ world_interp W_init_C C

      ∗ interp_continuation [] Ws Cs

      ∗ cstack_frag []

      ∗ interp W_init_B B (WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g)

      ∗ B_f ↦ₑ□{nargs} cmdc_B_f_args
      ∗ C_g ↦ₑ□{nargs} cmdc_C_g_args

      (* initial stack are revoked in both worlds *)
      ∗ StackRevokedResources W_init_B B (finz.seq_between csp_b csp_e)
      ∗ StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e)

      ∗ ▷ ( na_own cerise_nais ⊤
              -∗ WP Instr Halted {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
      ⊢ WP Seq (Instr Executable) {{ λ v, True }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNtrap Hpc_shadow Hpc_nonheap Hcgp_shadow Hcgp_heap Hcgp1_shadow Hcgp1_heap
               Hstk_shadow Hstk_heap Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hstk_min Hcgp_b Hcgp_c
               HB_f_nonheap HC_g_nonheap
               Hrevoked_stack_B Hrevoked_stack_C)
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_interp_B
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & #HentryB_f & #HentryC_g
      & Hstack_revoked_B & Hstack_revoked_C
      & Hφ)".
    iApply (wp_wand with "[-]").
    { iApply (cmdc_spec
                pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e rmap
                B_f C_g W_init_B W_init_C
               Ws Cs csp_content φ Nswitcher); eauto; iFrame "#∗".
    }
    by iIntros (v) "?".
  Qed.

End CMDC.
