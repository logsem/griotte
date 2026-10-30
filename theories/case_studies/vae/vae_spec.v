From iris.proofmode Require Import proofmode.
From griotte Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From griotte Require Import rules logrel world_interp_stack monotone proofmode register_tactics.
From griotte Require Import fetch_spec assert_spec switcher_base switcher_base_interp.
From griotte Require Import vae vae_helper.
From griotte Require Import proofmode.
From griotte Require Import vae_spec_states vae_spec_world_call
  vae_spec_init_blocks_1 vae_spec_init_blocks_2.

Section VAE.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  (** The call stack of a thread that starts in this compartment, with the
      stack [b, e) and the export table word [w] *)
  #[local] Notation main_entry_cstack b e w :=
    (entry_cstack {| tf_csp := Cap RWL Local b e (stk_start_a b e);
                     tf_export_tbl := w;
                     tf_error_count := 0 |}) (only parsing).

  Lemma vae_init_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)

    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)
    (* The capability to the export table of the compartment, as the entry
       frame of the thread records it *)
    (w_main_tbl : LWord)


    (i : positive)
    :

    let imports := vae_main_imports C_f in
    let a_vae_exp_tbl_cgp := (b_vae_exp_tbl ^+ ExportTable_offset_cgp) in
    let a_vae_entry_awkward := (b_vae_exp_tbl ^+ ExportTable_offset_entry vae_entry_awkward) in

    disjoint_from_shadow pc_b pc_e ->
    disjoint_from_shadow b_vae_exp_tbl e_vae_exp_tbl ->
    is_heap_address pc_b = false ->
    is_heap_address cgp_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    is_shadow_address cgp_b = false ->

    a_vae_entry_awkward ∈ₐ [b_vae_exp_tbl, e_vae_exp_tbl) ->

    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length vae_main_code) ->

    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    (pc_b + vae_label ".Lvae_init")%a = Some pc_a ->
    (* The stack holds the spill of the switcher call *)
    (csp_b + SpillSlot_size + StackEntry_reserved_space <= csp_e)%Z ->

    loc W0 !! i = Some (encode false) ->
    frame_match Ws Cs (main_entry_cstack csp_b csp_e w_main_tbl) W0 C ->
    (
      assert_static b_assert e_assert a_flag
      ∗ thread_in th C
      ∗ na_inv (tpool th) Ntstack trusted_stack_inv
      ∗ switcher_static
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a vae_main_code
      ∗ b_vae_exp_tbl ↦ₐ□ Cap RX Global pc_b pc_e pc_b
      ∗ a_vae_exp_tbl_cgp ↦ₐ□ Cap RW Global cgp_b cgp_e cgp_b
      ∗ a_vae_entry_awkward ↦ₐ□ WInt (encode_entry_point InterruptEnabled 1 4 (length (imports ++ VAE_main_code_init)))
      ∗ inv Nawk (awk_inv C i cgp_b)
      ∗ sts_rel_loc C i awk_rel_pub awk_rel_priv
      ∗ na_own (tpool th) ⊤

      (* initial register file *)
      ∗ PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e)
      ∗ cra ↦ᵣ[th] thread_return_sentry
      ∗ regs[th] rmap

      (* initial memory layout *)
      ∗ world_interp W0 C

      ∗ interp_continuation (main_entry_cstack csp_b csp_e w_main_tbl) Ws Cs

      ∗ ◯(CSTK)[th] (main_entry_cstack csp_b csp_e w_main_tbl)

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ C_f ↦ₑ□{nargs} 0
      ∗ interp W0 C (Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e))

      ⊢ safe[th])%I.
  Proof.
    (* Outline of the proof:
       - [vae_world_run_call]: revoke the world, to get the stack frame;
       - [vae_init_blocks_1_spec]: blocks 0-3, set the flag to [0], fetch
         the imports and jump to the switcher;
       - [switcher_call_args_0] and [switcher_cc_specification]: call to
         [B.adv];
       - [vae_init_return_spec]: block 3, return: the thread exits. *)
    intros imports a_vae_exp_tbl_cgp a_vae_entry_awkward.
    subst imports a_vae_exp_tbl_cgp a_vae_entry_awkward.
    iIntros (Hpc_shadow Hexports_shadow Hpc_nonheap Hcgp_nonheap Hsealed_nonheap Hcgp_shadow
               Hsize_vae_exp_tbl Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hstk_min Hloc_i_0 Hframe_match
            )
      "(#Hassert & #Hthread & #Hswitcher & #Hswitcher_static
      & #Himports_main & #Hcode_main
      & #Hvae_exp_tbl_PCC
      & #Hvae_exp_tbl_CGP
      & #Hvae_exp_tbl_awkward
      & #Hawk_inv & #Hrel_ι
      & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      )".
    assert (vae_code_bounds pc_b pc_e pc_a C_f) as Hbounds
      by (rewrite /vae_code_bounds; eauto 10).
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by (cbn in Hcgp_contiguous; solve_addr).
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_mmio Hstk_heap]; first done.
    iExtractList "Hrmap" [ct0;ct1;cs0;cs1]
      as ["Hct0"; "Hct1"; "Hcs0"; "Hcs1"].

    (* Revoke the world, to get the stack frame *)
    iDestruct (switcher_static_seal_pred with "Hswitcher_static") as "#Hseal_switcher".
    iMod (vae_world_run_call with "Hseal_switcher Hinterp_W0_csp Hinterp_W0_C_f Hworld_interp_C")
      as (stk_mem) "(Hworld_interp_C & #Hinterp_W1_C_f & Hstack_revoked & %Hrevoked_stk & Hstk)".

    (* Blocks 0-3: set the flag to [0], fetch the imports and jump to the
       switcher *)
    iApply (vae_init_blocks_1_spec with
             "[- $Hawk_inv $Hworld_interp_C $HPC $Hcgp $Hct0 $Hct1 $Hcs0 $Hcra
              $Himport_switcher $Himport_C_f $Hcode_main]"); [done..|exact Hloc_i_0|].
    iNext; iIntros (mie) "(Hworld_interp_C & HPC & Hcgp & Hct0 & Hct1 & Hcs0 & Hcra
                    & _ & _ & _)".
    iInsertRegs "Hrmap" ["Hct0"].
    iDestruct (switcher_call_args_0 (revoke W0) C with "Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* The free part of the stack, below the space reserved at its top *)
    assert (csp_b + StackEntry_reserved_space <= csp_e)%Z as Hstk_res_size
      by (unfold SpillSlot_size in Hstk_min; solve_addr+Hstk_min).
    iDestruct (stk_start_region_split with "Hstk")
      as (stk_mem_free stk_res) "[Hstk Hstk_res]";
      first exact Hstk_res_size.
    iEval (rewrite (stk_start_revoked_split _ _ _ _ Hstk_res_size)) in "Hstack_revoked".
    iDestruct "Hstack_revoked" as "[Hstack_revoked _]".
    pose proof (stk_start_revoked_addresses _ _ _ Hstk_res_size Hrevoked_stk)
      as Hrevoked_stk_free.

    (* Call to [B.adv] *)
    iApply (switcher_cc_specification with
             "[- $Hthread $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $HentryC_f $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked $Hcstk_frag
              $Hinterp_W1_C_f $HK]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { apply stk_start_cursor_ok; unfold SpillSlot_size in Hstk_min; solve_addr+Hstk_min. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    iSplit; first done.
    iSplit; last first.
    { (* The spill cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits.
      apply stk_start_spill_fits; unfold SpillSlot_size in Hstk_min |- *; solve_addr+Hstk_min. }
    iNext.
    iIntros (W2 rmap'' stk_mem' l' rcgp rcra rcs0 rcs1)
      "(_ & _ & _ & _ & _ & %Hrmap_ret_dom & _ & _ & Hna & _ & _ & Hcstk_frag & HPC
      & _ & Hcra & Hcs0 & _ & _ & _ & _ & Hrmap & _ & _ & %Hrestored)".
    destruct Hrestored as (_ & Hrcra & Hrcs0 & _).
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0; last exact thread_return_sentry_not_heap.
    subst rcra rcs0.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ctp;ct0;ct2] as ["Hctp"; "Hct0"; "Hct2"].

    (* Block 3: return, the thread exits *)
    iApply (vae_init_return_spec with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hcs0 $Hcra $Hctp $Hct0 $Hct2
               $Hcstk_frag $Hcode_main]"); [done | done].
  Qed.

End VAE.
