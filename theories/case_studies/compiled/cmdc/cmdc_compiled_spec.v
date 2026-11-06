From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules proofmode register_tactics.
From griotte Require Import switcher_base.
From griotte Require Import cmdc_compiled_spec_states cmdc_compiled_spec_world
  cmdc_compiled_spec_prologue_blocks_1 cmdc_compiled_spec_call_blocks_2
  cmdc_compiled_spec_check_blocks_3 cmdc_compiled_spec_prep_blocks_4
  cmdc_compiled_spec_epilogue_blocks_5.

(** * Specification of [run], the compiled CMDC example

    The function [run] of [cmdc_compiled_main_code], as the CHERIoT
    compiler compiles it, run as the entry of a thread: it is safe. Its
    frame holds the callee-saved registers of the thread across the two
    calls to the switcher, which only take the part of the stack below the
    frame. *)

Section CMDC_Compiled.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .
  Context {B C : CmptName}.

  Implicit Types W : WORLD.

  (** The call stack of a thread that starts in this compartment, with the
      stack $[b, e)$ and the export table word [w] *)
  #[local] Notation main_entry_cstack b e w :=
    (entry_cstack {| tf_csp := Cap RWL Local b e (stk_start_a b e);
                     tf_export_tbl := w;
                     tf_error_count := 0 |}) (only parsing).

  Lemma cmdc_compiled_spec
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (* The compiled assert library: its PCC region and its flag *)
    (b_lib e_lib a_flag : Addr)
    (rmap : LReg)
    (B_f C_g : Sealable)
    (W_init_B W_init_C : WORLD)
    (Ws : list WORLD)
    (Cs : list CmptName)
    (* The capability to the export table of the compartment, as the entry
       frame of the thread records it *)
    (w_main_tbl : LWord)
    (csp_content : list LWord)
    (* The posture of the thread *)
    (b : InterruptStatus) :

    let imports := cmdc_compiled_main_imports b_lib e_lib B_f C_g in

    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_mmio_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    is_mmio_address (cgp_b ^+ 1) = false ->
    is_heap_address (cgp_b ^+ 1) = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->

    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (lword_of_word (WInt 0))) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_compiled_main_code) ->

    (cgp_b + length cmdc_compiled_main_data)%a = Some cgp_e ->
    (pc_b + cmdc_compiled_main_run_offset)%a = Some pc_a ->
    (* The stack holds the frame of [run] and the spill of the switcher calls *)
    (csp_b + cmdc_compiled_main_run_min_stack + StackEntry_reserved_space <= csp_e)%Z ->

    is_heap_cap (WSealed ot_switcher B_f) = false ->
    is_heap_cap (WSealed ot_switcher C_g) = false ->

    (* The stack is revoked in both worlds: the worlds are closed, and a
       Temporary stack would be owned by both [world_interp]. *)
    revoked_addresses W_init_B (finz.seq_between csp_b csp_e) ->
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->
    route_pre th b ->
    cmpt_shared B = false ->
    cmpt_shared C = false ->

    assert_compiled_static b_lib e_lib a_flag ∗
    thread_in th B ∗
    thread_in th C ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗

    (* initial register file *)
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    cra ↦ᵣ[th] thread_return_sentry ∗
    regs[th] rmap ∗

    (* initial memory layout *)
    [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]] ∗
    codefrag_pers pc_a cmdc_compiled_main_code ∗
    [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> cmdc_compiled_main_data ]] ∗
    [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]] ∗

    world_interp W_init_B B ∗
    world_interp W_init_C C ∗

    interp_continuation (main_entry_cstack csp_b csp_e w_main_tbl) Ws Cs ∗

    ◯(CSTK)[th] (main_entry_cstack csp_b csp_e w_main_tbl) ∗

    interp W_init_B B (WSealed ot_switcher B_f) ∗
    interp W_init_C C (WSealed ot_switcher C_g) ∗

    B_f ↦ₑ□{nargs} cmdc_B_f_args ∗
    C_g ↦ₑ□{nargs} cmdc_C_g_args ∗

    (* the stack is revoked in both worlds *)
    StackRevokedResources W_init_B B (finz.seq_between csp_b csp_e) ∗
    StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e) ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b
    ⊢ safe[th].
  Proof.
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hcgp_mmio Hcgp_heap Hcgp1_mmio Hcgp1_heap
               Hstk_mmio Hstk_heap Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hstk_min
               HB_f_nonheap HC_g_nonheap
               Hrevoked_stack_B Hrevoked_stack_C Hroute Hshared_B Hshared_C)
      "(#Hassert & #Hthread_B & #Hthread_C & #Hswitcher & #Hswitcher_static & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Himports_main & #Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_interp_B & Hworld_interp_C
      & HK & Hcstk_frag
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & #HentryB_f & #HentryC_g
      & Hstack_revoked_B & Hstack_revoked_C & Hmie & Hheld)".
    (* Outline of the proof:
       - [cmdc_compiled_stack_frame]: cut the stack at the cursor of [run],
         below its frame,
       - [cmdc_compiled_prologue_blocks_1_spec]: block 0, spill [cra],
         [cs0] and [cs1] in the frame, initialise [b] and [c], and prepare
         the argument [b] of the call to [B.f],
       - [cmdc_compiled_call_blocks_2_spec cmdc_compiled_call_B]: block 1,
         fetch the callee and the switcher and jump to the switcher,
       - [cmdc_compiled_world_share]: share [b] in the world of [B],
       - [switcher_cc_specification]: call to [B.f], with the part of the
         stack below the frame,
       - [cmdc_compiled_world_return]: get [b] back from the world of [B],
       - [cmdc_compiled_check_blocks_3_spec cmdc_compiled_call_B]: blocks
         2-3, assert that [c] is unchanged,
       - [cmdc_compiled_prep_blocks_4_spec]: block 4, overwrite [b] and
         prepare the argument [c] of the call to [C.g],
       - [cmdc_compiled_call_blocks_2_spec cmdc_compiled_call_C]: block 5,
       - [cmdc_compiled_world_share]: share [c] in the world of [C],
       - [switcher_cc_specification]: call to [C.g],
       - [cmdc_compiled_check_blocks_3_spec cmdc_compiled_call_C]: blocks
         6-7, assert that [b] is unchanged,
       - [cmdc_compiled_return_spec]: blocks 8-9, reload the spilled
         registers and return: the thread exits. *)
    assert (rmap !! cs0 = Some (lword_of_word (WInt 0))) as Hcs0_init.
    { apply Hrmap_init. rewrite Hrmap_dom; set_solver+. }
    assert (rmap !! cs1 = Some (lword_of_word (WInt 0))) as Hcs1_init.
    { apply Hrmap_init. rewrite Hrmap_dom; set_solver+. }
    iExtractList "Hrmap" [ca0;ct1;ct2;cs0;cs1]
      as ["Hca0";"Hct1";"Hct2";"Hcs0";"Hcs1"].
    iEval (cbn [fmap list_fmap cmdc_compiled_main_data cmdc_compiled_main_imports])
      in "Hcgp_main Himports_main".
    iRegionSplit "Hcgp_main" as "[Hcgp_b Hcgp_c]".
    iRegionSplit "Himports_main"
      as "(#Himport_switcher & #Himport_assert & #Himport_B_f & #Himport_C_g)".
    assert (cmdc_compiled_code_bounds pc_b pc_e pc_a B_f C_g) as Hbounds
      by (rewrite /cmdc_compiled_code_bounds; eauto 10).

    (* The frame of [run], below the space reserved at the top of the
       stack, and the free part below it, which the calls hand to the
       switcher *)
    destruct (cmdc_compiled_frame_a_bounds csp_b csp_e Hstk_min)
      as (Ha_f & Hcsp_b_f & Hstk_start & Hspill_fits).
    iDestruct (cmdc_compiled_stack_frame with "Hcsp_stk")
      as (stk_mem_free wf0 wf1 wf2 stk_res) "(Hstk_free & Hf0 & Hf1 & Hf2 & _)";
      first exact Hstk_min.
    set (a_f := cmdc_compiled_frame_a csp_b csp_e) in *.
    assert (a_f <= csp_e)%a as Ha_f_e.
    { rewrite /cmdc_compiled_main_run_frame_size in Ha_f. solve_addr+Ha_f Hstk_start. }
    iEval (rewrite (stk_cursor_revoked_split _ _ _ _ a_f Hcsp_b_f Ha_f_e)) in "Hstack_revoked_B".
    iDestruct "Hstack_revoked_B" as "[Hstack_revoked_B _]".
    iEval (rewrite (stk_cursor_revoked_split _ _ _ _ a_f Hcsp_b_f Ha_f_e)) in "Hstack_revoked_C".
    iDestruct "Hstack_revoked_C" as "[Hstack_revoked_C _]".
    pose proof (stk_cursor_revoked_addresses _ _ _ a_f Hcsp_b_f Ha_f_e Hrevoked_stack_B)
      as Hrevoked_B_free.
    pose proof (stk_cursor_revoked_addresses _ _ _ a_f Hcsp_b_f Ha_f_e Hrevoked_stack_C)
      as Hrevoked_C_free.
    clear Hrevoked_stack_B Hrevoked_stack_C.

    (* Block 0: the prologue *)
    iApply (cmdc_compiled_prologue_blocks_1_spec with
             "[- $HPC $Hcgp $Hcsp $Hcra $Hcs0 $Hcs1 $Hca0 $Hct1 $Hct2 $Hf0 $Hf1 $Hf2
                 $Hcgp_b $Hcgp_c $Hcode_main]"); [done..|].
    iNext; iIntros "(HPC & Hcgp & Hcsp & Hcra & Hcs0 & Hcs1 & Hca0 & [%wct1' Hct1]
                    & [%wct2' Hct2] & Hf0 & Hf1 & Hf2 & Hcgp_b & Hcgp_c & _)".

    (* Block 1: fetch the callee and the switcher, and jump to the switcher *)
    iApply (cmdc_compiled_call_blocks_2_spec cmdc_compiled_call_B with
             "[- $HPC $Hct1 $Hct2 $Hcra $Himport_switcher $Himport_B_f $Hcode_main
                 $Hmie $Hheld]"); [done | done |].
    iNext; iIntros "(HPC & Hct1 & Hct2 & Hcra & _ & _ & _ & Hmie & Hheld)".
    iEval (cbn [cmdc_compiled_call_target cmdc_compiled_return_label]) in "Hct1 Hcra".

    (* Share b in the world of B *)
    iMod (cmdc_compiled_world_share _ _ cgp_b (cgp_b ^+ 1) with
           "Hworld_interp_B Hinterp_Winit_B_f Hcgp_b")
      as "(Hworld_interp_B & #Hrel_cgp_b & #Hinterp_ca0 & _)";
      [solve_addr | done | done |].
    iInsertRegs "Hrmap" ["Hct2"].
    iDestruct (switcher_call_args_1 with "Hca0 Hinterp_ca0 Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to B.f, with the stack below the frame *)
    iApply (switcher_cc_specification W_init_B B _ _ _ _ csp_b csp_e a_f B_f stk_mem_free
              arg_rmap rmap' _ Ws Cs cmdc_B_f_args with
             "[- $Hthread_B $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk_free $Hworld_interp_B $Hstack_revoked_B $Hcstk_frag
              $Hinterp_Winit_B_f $HentryB_f $HK $Hmie $Hheld]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { exact Ha_f_e. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { destruct b; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    { exact Hshared_B. }
    iSplit; first done.
    iSplit; last first.
    { (* The spill cannot fault: the stack holds it below the frame *)
      iApply switcher_cc_fault_stack_fits. exact Hspill_fits. }
    iNext.
    clear dependent arg_rmap rmap'.
    iIntros (W_ret_B rmap_B stk_mem_B l_B rcgp rcra rcs0 rcs1 m_B)
      "( _ & _ & _ & _ & _ & %Hrmap_B_dom & _ & _
      & Hna & _
      & Hworld_interp_B
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0_B [Hca0 _] ] & [%warg1_B [Hca1 _] ]
      & Hrmap & Hstk_free & HK & %Hrestored & %Hroute_B & Hmie & Hheld)".
    (* The switcher restores [cgp], [cra], [cs0] and [cs1], which point
       outside the heap *)
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & Hrcs1).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcs1;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp1_heap /=; reflexivity].
    subst rcgp rcra rcs0 rcs1.
    assert (∀ a, lupdatePcPerm (Sentry (ret_kind b) RX Global pc_b pc_e a) =
                 Cap RX Global pc_b pc_e a) as Hret_pc by (intros; by destruct b).
    iEval (rewrite Hret_pc) in "HPC".
    rewrite default_jalr_target_mie_ret_kind in Hroute_B.
    iEval (rewrite default_jalr_target_mie_ret_kind) in "Hmie Hheld".

    (* Get b back from the world of B *)
    iMod (cmdc_compiled_world_return with "Hworld_interp_B Hrel_cgp_b") as "[%wcgp_b Hcgp_b]";
      first done.
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct1;ct2] as ["Hct1";"Hct2"].

    (* Blocks 2-3: assert that c is unchanged *)
    assert (cgp_b ^+ 2 = cgp_b ^+ 1 ^+ 1) as Hcgp_c_e by solve_addr.
    iEval (rewrite Hcgp_c_e) in "Hcs1".
    iApply (cmdc_compiled_check_blocks_3_spec cmdc_compiled_call_B with
             "[- $Hassert $HPC $Hcs1 $Hca0 $Hca1 $Hct2 $Hcra $Hcgp_c $Himport_assert
                 $Hcode_main $Hmie $Hheld]"); [done | solve_addr | done | done |].
    iNext; iIntros "(HPC & Hcs1 & Hca0 & Hca1 & [%wct2_B Hct2] & [%wcra_B Hcra] & Hcgp_c & _
                    & _ & Hmie & Hheld)".

    (* Block 4: overwrite b and prepare the argument c *)
    iApply (cmdc_compiled_prep_blocks_4_spec with
             "[- $HPC $Hcs0 $Hcs1 $Hca0 $Hcgp_b $Hcode_main]"); [done | solve_addr | done |].
    iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hca0 & Hcgp_b & _)".

    (* Block 5: fetch the callee and the switcher, and jump to the switcher *)
    iApply (cmdc_compiled_call_blocks_2_spec cmdc_compiled_call_C with
             "[- $HPC $Hct1 $Hct2 $Hcra $Himport_switcher $Himport_C_g $Hcode_main
                 $Hmie $Hheld]"); [done | done |].
    iNext; iIntros "(HPC & Hct1 & Hct2 & Hcra & _ & _ & _ & Hmie & Hheld)".
    iEval (cbn [cmdc_compiled_call_target cmdc_compiled_return_label]) in "Hct1 Hcra".

    (* Share c in the world of C *)
    iMod (cmdc_compiled_world_share _ _ (cgp_b ^+ 1) (cgp_b ^+ 1 ^+ 1) with
           "Hworld_interp_C Hinterp_Winit_C_g Hcgp_c")
      as "(Hworld_interp_C & _ & #Hinterp_ca0_C & _)";
      [solve_addr | done | done |].
    iInsertRegs "Hrmap" ["Hca1"; "Hct2"].
    iDestruct (switcher_call_args_1 with "Hca0 Hinterp_ca0_C Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite !dom_insert_L !dom_delete_L Hrmap_B_dom; set_solver+. }

    (* Call to C.g, with the part of the stack returned by the first call *)
    iApply (switcher_cc_specification W_init_C C _ _ _ _ csp_b csp_e a_f C_g stk_mem_B
              arg_rmap rmap' _ Ws Cs cmdc_C_g_args with
             "[- $Hthread_C $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk_free $Hworld_interp_C $Hstack_revoked_C $Hcstk_frag
              $Hinterp_Winit_C_g $HentryC_g $HK $Hmie $Hheld]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { exact Ha_f_e. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { destruct b; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    { exact Hshared_C. }
    iSplit; first done.
    iSplit; last first.
    { (* The spill cannot fault: the stack holds it below the frame *)
      iApply switcher_cc_fault_stack_fits. exact Hspill_fits. }
    iNext.
    clear dependent arg_rmap rmap'.
    iIntros (W_ret_C rmap_C stk_mem_C l_C rcgp rcra rcs0 rcs1 m_C)
      "( _ & _ & _ & _ & _ & %Hrmap_C_dom & _ & _
      & Hna & _ & _
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0_C [Hca0 _] ] & [%warg1_C [Hca1 _] ]
      & Hrmap & _ & _ & %Hrestored & %Hroute_C & Hmie & Hheld)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & _).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    subst rcgp rcra rcs0.
    iEval (rewrite Hret_pc) in "HPC".
    rewrite default_jalr_target_mie_ret_kind in Hroute_C.
    iEval (rewrite default_jalr_target_mie_ret_kind) in "Hmie Hheld".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ctp;ct0;ct2] as ["Hctp";"Hct0";"Hct2"].

    (* Blocks 6-7: assert that b is unchanged *)
    iApply (cmdc_compiled_check_blocks_3_spec cmdc_compiled_call_C with
             "[- $Hassert $HPC $Hcs0 $Hca0 $Hca1 $Hct2 $Hcra $Hcgp_b $Himport_assert
                 $Hcode_main $Hmie $Hheld]"); [done | solve_addr | done | done |].
    iNext; iIntros "(HPC & Hcs0 & Hca0 & Hca1 & [%wct2_C Hct2] & [%wcra_C Hcra] & _
                    & _ & _ & Hmie & Hheld)".

    (* Blocks 8-9: the epilogue, the thread exits *)
    iInsertRegs "Hrmap" ["Hcgp"].
    iApply (cmdc_compiled_return_spec with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hcsp $Hca0 $Hca1 $Hcs0 $Hcs1 $Hcra
               $Hctp $Hct0 $Hct2 $Hrmap $Hf0 $Hf1 $Hf2 $Hcstk_frag $Hcode_main $Hmie $Hheld]");
      [done | done | | done..].
    rewrite dom_insert_L !dom_delete_L Hrmap_C_dom; set_solver.
  Qed.

End CMDC_Compiled.
