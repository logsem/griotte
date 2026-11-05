From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import switcher_base.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import cmdc_spec_world.
From griotte Require Import ist_spec_states ist_spec_world
  ist_spec_init_blocks_1 ist_spec_call_blocks_2 ist_spec_check_blocks_3.

Section IST.
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

  (** The thread runs [K.run] with interrupts disabled: it shares its global
      [b] with [B.f], then writes [42] to [b] and asserts it. The world of
      [B] is the world premise of its regime: in a shared [B], the thread's
      own local map and the invariant of the map of Permanent regions, which
      the thread opens with the critical-section token it holds while
      interrupts are disabled. *)
  Lemma ist_spec
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
    :
    let imports := ist_K_imports B_f in

    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_mmio_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->

    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (lword_of_word (WInt 0)) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length ist_K_code) ->

    (cgp_b + length ist_K_data)%a = Some cgp_e ->
    (pc_b + ist_label ".Lstatus_run")%a = Some pc_a ->
    (* The stack holds the spill of the switcher call *)
    (csp_b + SpillSlot_size + StackEntry_reserved_space <= csp_e)%Z ->

    is_heap_cap (WSealed ot_switcher B_f) = false ->
    (* The stack is revoked in the world of [B]: the thread keeps it *)
    revoked_addresses W_init (finz.seq_between csp_b csp_e) ->

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
      ∗ codefrag_pers pc_a ist_K_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> ist_K_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ world_resources W_init B

      ∗ interp_continuation (K_entry_cstack csp_b csp_e w_K_tbl) Ws Cs
      ∗ ◯(CSTK)[th] (K_entry_cstack csp_b csp_e w_K_tbl)

      ∗ interp W_init B (WSealed ot_switcher B_f)
      ∗ B_f ↦ₑ□{nargs} 1

      (* the initial stack is revoked in the world of [B] *)
      ∗ StackRevokedResources W_init B (finz.seq_between csp_b csp_e)
      (* the entry of [K.run] disables interrupts *)
      ∗ MIE ↦ₜ[th] InterruptDisabled
      ∗ held (th := th) InterruptDisabled
      ⊢ safe[th])%I.
  Proof.
    (* Outline of the proof:
       - [world_resources_acc]: open the world of [B] with the
         critical-section token, lent out of [held InterruptDisabled],
       - [ist_init_blocks_1_spec]: block 0, initialise [b], and prepare the
         capability to [b], the argument of the call to [B.f],
       - [cmdc_world_share]: share [b] in the world of [B], as a Permanent
         region; close the world of [B],
       - [ist_call_blocks_2_spec]: blocks 1-3, fetch the imports and jump to
         the switcher,
       - [switcher_cc_specification_shared]: call to [B.f], which returns
         with interrupts disabled,
       - [perm_resources_acc], [ist_perm_open]: open the map of Permanent
         regions of [B] with the token, and take [b] out of it,
       - [ist_overwrite_blocks_3_spec]: block 3, overwrite [b] and load it,
       - [ist_perm_close]: put [b] back and close the map,
       - [ist_check_blocks_4_spec]: blocks 4-5, assert that [b = 42] and
         return: the thread exits. *)
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hcgp_mmio Hcgp_heap Hstk_shadow Hstk_heap
               Hrmap_dom Hrmap_init HsubBounds Hcgp_contiguous Himports_contiguous Hstk_min
               HB_f_nonheap Hrevoked_stack)
      "(#Hassert & #Hthread & #Hswitcher & #Hswitcher_static & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_B & HK & Hcstk_frag
      & #Hinterp_Winit_B_f & #HentryB_f
      & Hstack_revoked & Hmie & Hheld)".
    iExtractList "Hrmap" [ca0;ca1;ctp;ct0;ct1;cs0;cs1]
      as ["Hca0";"Hca1";"Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1"].
    iEval (cbn [fmap list_fmap ist_K_data ist_K_imports]) in "Hcgp_main Himports_main".
    iRegionSplit "Hcgp_main" as "Hcgp_b".
    iRegionSplit "Himports_main"
      as "(Himport_switcher & Himport_assert & Himport_B_f)".
    assert (ist_code_bounds pc_b pc_e pc_a B_f) as Hbounds
      by (rewrite /ist_code_bounds; eauto 10).

    (* Open the world of B with the critical-section token *)
    iDestruct (held_crit with "Hheld") as "[Hcrit Hheld_back]".
    iMod (world_resources_acc ⊤ ⊤ W_init B with "Hworld_B Hcrit")
      as "(Hworld_open & Hcrit & Hclose_world)"; [solve_ndisj | solve_ndisj |].

    (* Block 0: initialise b and the capability to b *)
    iApply (ist_init_blocks_1_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hcs0 $Hcra $Hcgp_b $Hcode_main]");
      [done..|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & [%wct0' Hct0] & [%wct1' Hct1] & Hcs0 & Hcra
                    & Hcgp_b & Hcode_main)".

    (* Share b in the world of B, and close it *)
    iMod (cmdc_world_share W_init B cgp_b (cgp_b ^+ 1) csp_b csp_e B_f with
           "Hworld_open Hstack_revoked Hinterp_Winit_B_f Hcgp_b Hcsp_stk")
      as "(Hworld_open & #Hrel_cgp_b & #Hinterp_ca0 & #Hinterp_B_f
           & Hstack_revoked & %Hrevoked & %Hcgp_b_stk & Hcsp_stk)";
      [solve_addr|done..|].
    iDestruct "Hclose_world" as "[Hclose_world _]".
    iMod ("Hclose_world" $! W_init with "Hworld_open Hcrit") as "[Hworld_B Hcrit]".
    iDestruct ("Hheld_back" with "Hcrit") as "Hheld".

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iApply (ist_call_blocks_2_spec with
             "[- $HPC $Hctp $Hct1 $Hcra
              $Himport_switcher $Himport_B_f $Hcode_main $Hmie $Hheld]");
      [done| by intros _ |].
    iNext; iIntros "(HPC & Hctp & Hct1 & Hcra
                    & Himport_switcher & Himport_B_f & Hcode_main & Hmie & Hheld)".
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
    iEval (rewrite (stk_start_revoked_split _ _ _ _ Hstk_res_size)) in "Hstack_revoked".
    iDestruct "Hstack_revoked" as "[Hstack_revoked _]".
    pose proof (stk_start_revoked_addresses _ _ _ Hstk_res_size Hrevoked)
      as Hrevoked_free.

    (* Call to B.f *)
    iApply (switcher_cc_specification_shared W_init B _ _ _ _ csp_b csp_e (stk_start_a csp_b csp_e)
              B_f stk_mem_free arg_rmap rmap' _ Ws Cs 1 with
             "[- $Hthread $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $Hworld_B $Hstack_revoked $Hcstk_frag
              $Hinterp_B_f $HentryB_f $HK $Hmie $Hheld]").
    { exact Hstk_shadow. }
    { exact Hstk_heap. }
    { apply stk_start_cursor_ok; unfold SpillSlot_size in Hstk_min; solve_addr+Hstk_min. }
    { exact Hrmap'_dom. }
    { exact Harg_rmap. }
    { reflexivity. }
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
      "( _ & _ & _ & _ & _ & %Hrmap_dom & _ & _
      & Hna & _
      & Hworld_B
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & _ & _ & %Hrestored & _ & Hmie & Hheld)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & _).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0; [|exact thread_return_sentry_not_heap].
    subst rcgp rcra rcs0.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    (* The return restores the posture of [K]: interrupts disabled *)
    iEval (rewrite default_jalr_target_mie_ret_kind) in "Hmie Hheld".

    (* Open the map of Permanent regions of B, and take b out of it *)
    iDestruct (held_crit with "Hheld") as "[Hcrit Hheld_back]".
    iEval (rewrite world_resources_split) in "Hworld_B".
    iDestruct "Hworld_B" as "[_ Hperm_B]".
    iMod (perm_resources_acc ⊤ ⊤ B with "Hperm_B Hcrit")
      as "(Hmap & Hcrit & Hclose_perm)"; [solve_ndisj | solve_ndisj |].
    iAssert (▷ (perm_region_map B {[ LNonHeap cgp_b ]} ∗ ∃ v, cgp_b ↦ₐ v))%I
      with "[Hmap]" as "[Hmap Hcgp_b]".
    { iNext; iApply (ist_perm_open with "Hmap Hrel_cgp_b"). }
    iDestruct "Hcgp_b" as (wcgp_b) ">Hcgp_b".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ctp;ct0;ct1;ct2;ca2]
      as ["Hctp";"Hct0";"Hct1";"Hct2";"Hca2"].

    (* Block 3: overwrite b and load it *)
    iApply (ist_overwrite_blocks_3_spec _ _ _ _ _ B_f with
             "[- $HPC $Hcgp $Hct0 $Hct1 $Hcgp_b $Hcode_main]"); [done..|].
    iNext; iIntros "(HPC & Hcgp & Hct0 & Hct1 & Hcgp_b & Hcode_main)".

    (* Put b back, close the map of Permanent regions of B *)
    iAssert (▷ perm_region_map B ∅)%I with "[Hmap Hcgp_b]" as "Hmap".
    { iNext; iApply (ist_perm_close with "Hmap Hrel_cgp_b Hcgp_b"). }
    iDestruct "Hclose_perm" as "[_ Hclose_perm]".
    iMod ("Hclose_perm" with "Hmap Hcrit") as "[_ Hcrit]".
    iDestruct ("Hheld_back" with "Hcrit") as "Hheld".

    (* Blocks 4-5: assert that b = 42 and return, the thread exits *)
    iDestruct (regs_of_parts _ [(cs1, _); (csp, _)]
                 {[ cgp ; ct1 ; ca0 ; ca1 ; ca2 ; cra ; cs0 ; ctp ; ct0 ; ct2 ]}
                 with "Hrmap [Hcs1 Hcsp]")
      as (rmap_ret) "[%Hrmap_ret Hrmap]".
    { rewrite !dom_delete_L Hrmap_dom. apply set_eq. intros r.
      pose proof (all_registers_s_correct r). set_solver. }
    { cbn. iFrame. }
    iApply (ist_check_blocks_4_spec _ _ _ B_f with
             "[$Hassert $Hswitcher $Hswitcher_static $Hna $HPC $Hcgp $Hctp $Hct0 $Hct1 $Hct2
              $Hca0 $Hca1 $Hca2 $Hcra $Hcs0 $Hrmap $Hcstk_frag $Himport_assert
              $Hcode_main $Hmie $Hheld]");
      [done | done | done | by intros _].
  Qed.
End IST.
