From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_base temporal_isolation.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import ti_spec_states ti_spec_world
  ti_spec_init_blocks_1 ti_spec_call_blocks_2 ti_spec_assert_blocks_3.

Section TI.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {B : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The call stack of a thread that starts in this compartment, with the
      stack $[b, e)$ and the export table word [w] *)
  #[local] Notation K_entry_cstack b e w :=
    (entry_cstack {| tf_csp := Cap RWL Local b e (stk_start_a b e);
                     tf_export_tbl := w;
                     tf_error_count := 0 |}) (only parsing).

  (** The thread runs [K.run]: it lends a local capability to its global [b]
      to [B.f], then writes [42] to [b] and asserts it. The world of [B] is
      the world premise of its regime: in a shared [B], the thread's own
      local map, where [b] is lent, and the invariant of the map of
      Permanent regions. *)
  Lemma ti_spec
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)
    (B_f : Sealable)
    (W_init : WORLD)
    (Ws : list WORLD)
    (Cs : list CmptName)
    (* The capability to the export table of the compartment, as the entry
       frame of the thread records it *)
    (w_K_tbl : LWord)
    (csp_content : list LWord)
    (* The posture of the thread *)
    (b : InterruptStatus)
    :
    let imports := ti_K_imports B_f in

    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    disjoint_from_mmio cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->

    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (lword_of_word (WInt 0)) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length ti_K_code) ->

    (cgp_b + length ti_K_data)%a = Some cgp_e ->
    (pc_b + ti_label ".Lti_run")%a = Some pc_a ->
    (* The stack holds the spill of the switcher call *)
    (csp_b + SpillSlot_size + StackEntry_reserved_space <= csp_e)%Z ->

    LNonHeap cgp_b ∉ dom (std W_init) ->
    is_heap_cap (WSealed ot_switcher B_f) = false ->
    (* The stack is revoked in the world of [B]: the thread keeps it *)
    revoked_addresses W_init (finz.seq_between csp_b csp_e) ->
    route_pre th b ->

    (
      assert_static b_assert e_assert a_flag
      ∗ thread_in th B
      ∗ na_inv (tpool th) Ntstack trusted_stack_inv
      ∗ switcher_static
      ∗ na_own (tpool th) ⊤

      (* initial register file *)
      ∗ PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e)
      ∗ cra ↦ᵣ[th] thread_return_sentry
      ∗ regs[th] rmap

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a ti_K_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> ti_K_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ world_resources W_init B

      ∗ interp_continuation (K_entry_cstack csp_b csp_e w_K_tbl) Ws Cs
      ∗ ◯(CSTK)[th] (K_entry_cstack csp_b csp_e w_K_tbl)

      ∗ interp W_init B (WSealed ot_switcher B_f)
      ∗ B_f ↦ₑ□{nargs} 1

      (* the initial stack is revoked in the world of [B] *)
      ∗ StackRevokedResources W_init B (finz.seq_between csp_b csp_e)
      ∗ MIE ↦ₜ[th] b
      ∗ held (th := th) b
      ⊢ safe[th])%I.
  Proof.
    (* Outline of the proof:
       - [ti_init_blocks_1_spec]: block 0, initialise [b], and prepare the
         local capability to [b], the argument of the call to [B.f],
       - [ti_call_blocks_2_spec]: blocks 1-3, fetch the imports and jump to
         the switcher,
       - [ti_world_share]: lend [b] in the local map of the thread,
       - [switcher_cc_specification_shared]: call to [B.f],
       - [ti_world_return]: get [b] back from the revoked addresses,
       - [ti_assert_blocks_3_spec]: blocks 3-5, overwrite [b], assert that
         [b = 42] and return: the thread exits. *)
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hcgp_mmio Hcgp_range Hstk_shadow Hstk_heap
               Hrmap_dom Hrmap_init HsubBounds Hcgp_contiguous Himports_contiguous Hstk_min
               Hcgp_b HB_f_nonheap Hrevoked_stack Hroute)
      "(#Hassert & #Hthread & #Hswitcher & #Hswitcher_static & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_B & HK & Hcstk_frag
      & #Hinterp_Winit_B_f & #HentryB_f
      & #Hstack_revoked & Hmie & Hheld)".
    iExtractList "Hrmap" [ca0;ca1;ctp;ct0;ct1;cs0;cs1]
      as ["Hca0";"Hca1";"Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1"].
    iEval (cbn [fmap list_fmap ti_K_data ti_K_imports]) in "Hcgp_main Himports_main".
    iRegionSplit "Hcgp_main" as "Hcgp_b".
    iRegionSplit "Himports_main"
      as "(Himport_switcher & Himport_assert & Himport_B_f)".
    assert (ti_code_bounds pc_b pc_e pc_a B_f) as Hbounds
      by (rewrite /ti_code_bounds; eauto 10).

    (* Block 0: initialise b and the local capability to b *)
    iApply (ti_init_blocks_1_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hcs0 $Hcra $Hcgp_b $Hcode_main]");
      [done..|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & [%wct0' Hct0] & [%wct1' Hct1] & Hcs0 & Hcra
                    & Hcgp_b & Hcode_main)".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iApply (ti_call_blocks_2_spec with
             "[- $HPC $Hctp $Hct1 $Hcra
              $Himport_switcher $Himport_B_f $Hcode_main $Hmie $Hheld]"); [done|done|].
    iNext; iIntros "(HPC & Hctp & Hct1 & Hcra
                    & Himport_switcher & Himport_B_f & Hcode_main & Hmie & Hheld)".

    (* Lend b in the local map of the thread *)
    iDestruct (switcher_static_seal_pred with "Hswitcher_static") as "#Hseal_switcher".
    iMod (ti_world_share with
           "Hthread Hseal_switcher Hworld_B Hstack_revoked Hinterp_Winit_B_f Hcgp_b")
      as "(Hworld_B & #Hinterp_ca0 & #Hinterp_B_f & #Hstack_revoked_W1 & %Hrevoked_W1)";
      [done..|].
    iInsertRegs "Hrmap" ["Hca1"; "Hctp"; "Hct0"].
    iDestruct (switcher_call_args_1 with "Hca0 Hinterp_ca0 Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* The free part of the stack, below the space reserved at its top *)
    assert (csp_b + StackEntry_reserved_space <= csp_e)%Z as Hstk_res_size
      by (unfold SpillSlot_size in Hstk_min; solve_addr+Hstk_min).
    iDestruct (stk_start_region_split with "Hcsp_stk")
      as (stk_mem_free stk_res) "[Hcsp_stk _]";
      first exact Hstk_res_size.
    iDestruct (stk_start_revoked_split _ _ _ _ Hstk_res_size with "Hstack_revoked_W1")
      as "[Hstack_revoked_W1_free _]".
    pose proof (stk_start_revoked_addresses _ _ _ Hstk_res_size Hrevoked_W1)
      as Hrevoked_W1_free.

    (* Call to B.f *)
    iApply (switcher_cc_specification_shared with
             "[- $Hthread $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $Hworld_B $Hstack_revoked_W1_free $Hcstk_frag
              $Hinterp_B_f $HentryB_f $HK $Hmie $Hheld]").
    { exact Hstk_shadow. }
    { exact Hstk_heap. }
    { apply stk_start_cursor_ok; unfold SpillSlot_size in Hstk_min; solve_addr+Hstk_min. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { destruct b; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    iSplit; first done.
    iSplit; last first.
    { (* The spill cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits.
      apply stk_start_spill_fits; unfold SpillSlot_size in Hstk_min |- *; solve_addr+Hstk_min. }
    iNext.
    clear dependent arg_rmap rmap' rmap.
    iIntros (W2 rmap stk_mem l' rcgp rcra rcs0 rcs1 m)
      "( %Hl_unk' & Hrevoked_l' & _
      & %Hrelated_pub_W2 & _ & %Hrmap_dom & _ & _
      & Hna & %Hcsp_bounds
      & _
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & _ & _ & %Hrestored & %Hroute' & Hmie & Hheld)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & _).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= (proj1 Hcgp_range) /=;
        reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0; [|exact thread_return_sentry_not_heap].
    subst rcgp rcra rcs0.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".

    (* Get b back from the revoked addresses *)
    iMod (ti_world_return W_init W2 B cgp_b csp_b csp_e l' with "Hrevoked_l'")
      as "[%wcgp_b Hcgp_b]"; [exact Hcsp_bounds|done|done|done|].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ctp;ct0;ct1;ct2;ca2]
      as ["Hctp";"Hct0";"Hct1";"Hct2";"Hca2"].

    (* Blocks 3-5: overwrite b, assert that b = 42 and return, the thread exits *)
    iDestruct (regs_of_parts _ [(cs1, _); (csp, _)]
                 {[ cgp ; ct1 ; ca0 ; ca1 ; ca2 ; cra ; cs0 ; ctp ; ct0 ; ct2 ]}
                 with "Hrmap [Hcs1 Hcsp]")
      as (rmap_ret) "[%Hrmap_ret Hrmap]".
    { rewrite !dom_delete_L Hrmap_dom. apply set_eq. intros r.
      pose proof (all_registers_s_correct r). set_solver. }
    { cbn. iFrame. }
    iApply (ti_assert_blocks_3_spec _ _ _ _ _ B_f with
             "[$Hassert $Hswitcher $Hswitcher_static $Hna $HPC $Hcgp $Hctp $Hct0 $Hct1 $Hct2
              $Hca0 $Hca1 $Hca2 $Hcra $Hcs0 $Hrmap $Hcstk_frag $Hcgp_b $Himport_assert
              $Hcode_main $Hmie $Hheld]");
      [done..].
  Qed.

End TI.
