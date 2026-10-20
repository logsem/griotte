From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone.
From griotte Require Import fetch_spec assert_spec switcher switcher_spec_call switcher_exception_stub.
From griotte Require Import lse.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import lse_spec_states lse_spec_world
  lse_spec_run_blocks_1 lse_spec_run_blocks_2.

Section LSE.
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

  Lemma lse_run_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (b_lse_exp_tbl e_lse_exp_tbl : Addr)

    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nswitcher Nlse_code LSEN : namespace)
    :

    let imports := lse_main_imports C_f in

    disjoint_from_shadow pc_b pc_e ->
    is_shadow_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    disjoint_from_shadow b_lse_exp_tbl e_lse_exp_tbl ->
    is_heap_address pc_b = false ->
    Nswitcher ## Nlse_code ->

    (b_lse_exp_tbl <= b_lse_exp_tbl ^+ 2 < e_lse_exp_tbl)%a ->

    dom rmap = all_registers_s ∖ {[ cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length lse_main_code)%a ->

    (cgp_b + length lse_main_data)%a = Some cgp_e ->
    (pc_b + lse_label ".Llse_run")%a = Some pc_a ->
    (* The stack holds the spill of the switcher call *)
    (csp_b + 4 <= csp_e)%Z ->

    is_heap_cap (WSealed ot_switcher C_f) = false ->
    frame_match Ws Cs [] W0 C ->
    (
      assert_static b_assert e_assert a_flag
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ switcher_static
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a lse_main_code
      ∗ na_inv cerise_nais LSEN (cgp_b ↦ₐ WInt 2)
      ∗ b_lse_exp_tbl ↦ₐ□ WCap true RX Global pc_b pc_e pc_b
      ∗ (b_lse_exp_tbl ^+ 1)%a ↦ₐ□ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ (b_lse_exp_tbl ^+ 2)%a ↦ₐ□ lse_exp_tbl_entry_f
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ₚ WCap true RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ world_interp W0 C

      ∗ interp_continuation [] Ws Cs

      ∗ cstack_frag []

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ C_f ↦ₑ□{nargs} 0
      ∗ interp W0 C (WCap true RWL Local csp_b csp_e csp_b)

      ∗ seal_pred ot_switcher ot_switcher_propC

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [lse_world_call]: revoke the world, to get the stack frame;
       - [lse_run_blocks_1_spec]: blocks 0-3, set [a] to [2], fetch the
         imports and jump to the switcher;
       - [switcher_call_args_0] and [switcher_cc_specification]: call to
         [C_f];
       - [lse_run_blocks_2_spec]: block 3, halt. *)
    intros imports; subst imports.
    iIntros (Hpc_shadow Hcgp_shadow Hcgp_nonheap Hexp_tbl_shadow Hpc_nonheap
               HNswitcher_lse Hsize_lse_exp_tbl
               Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hstk_min Hsealed_nonheap Hframe_match
            )
      "(#Hassert & #Hswitcher & #Hswitcher_static
      & #Himports_main & #Hcode_main
      & #Hlse
      & #Hlse_exp_tbl_PCC
      & #Hlse_exp_tbl_CGP
      & #Hlse_exp_tbl_awkward
      & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      & #Hot_switcher
      )".
    assert (lse_code_bounds pc_b pc_e pc_a C_f) as Hbounds by (rewrite /lse_code_bounds; eauto 10).
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by (cbn in Hcgp_contiguous; solve_addr).
    iMod (na_inv_acc with "Hlse Hna")
      as "(>Hcgp_b & Hna & Hlse_close)"; auto.
    iEval (cbn [fmap list_fmap lse_main_imports]) in "Himports_main".
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_mmio Hstk_heap]; first done.
    iExtractList "Hrmap" [cra;ct0;ct1;cs0;cs1]
      as ["Hcra"; "Hct0"; "Hct1"; "Hcs0"; "Hcs1"].

    (* Revoke the world, to get the stack frame *)
    iMod (lse_world_call with "Hinterp_W0_csp Hinterp_W0_C_f Hworld_interp_C")
      as (stk_mem) "(%Hrevoked_stk & Hworld_interp_C & #Hinterp_W1_C_f
                     & Hstack_revoked & Hstk)".

    (* Blocks 0-3: set [a] to [2], fetch the imports and jump to the
       switcher *)
    iApply (lse_run_blocks_1_spec with
             "[- $HPC $Hcgp $Hct0 $Hct1 $Hcra $Hcgp_b
              $Himport_switcher $Himport_C_f $Hcode_main]"); [done|done|done|done|].
    iNext; iIntros (mie) "(HPC & Hcgp & Hct0 & Hct1 & Hcra & Hcgp_b
                    & _ & _ & _)".
    iMod ("Hlse_close" with "[$Hna $Hcgp_b]") as "Hna".
    iInsertRegs "Hrmap" ["Hct0"].
    iDestruct (switcher_call_args_0 (revoke W0) C with "Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to [C_f] *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $HentryC_f $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked $Hcstk_frag
              $Hinterp_W1_C_f $HK]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { solve_addr+. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    iSplit; first done.
    iSplit; last first.
    { (* The spill cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits; solve_addr+Hstk_min. }
    iNext.
    clear dependent arg_rmap rmap' stk_mem.
    iIntros (W2 rmap' stk_mem l' rcgp rcra rcs0 rcs1)
      "(_ & _ & _ & _ & _ & _ & _ & _
      & Hna & _
      & _
      & _
      & HPC & Hrest)".
    iDestruct "Hrest" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hrestored)".
    destruct Hrestored as (_ & Hrcra & _ & _).
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    subst rcra.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".

    (* Block 3: halt *)
    iApply (lse_run_blocks_2_spec with "[- $HPC $Hcode_main]"); first done.
    iNext; iIntros "_ !>".
    iExact "Hna".
  Qed.

End LSE.
