From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec switcher_base thread_synchronisation.
From griotte Require Import world_ghost_theory world_interp_stack wp_core_full.
From griotte Require Import proofmode register_tactics.
From griotte Require Import cmdc_spec_world.
From griotte Require Import tsy_flag tsy_spec_states
  tsy_spec_init_blocks_1 tsy_spec_call_blocks_2 tsy_spec_exit_blocks_3.

Section TSY_run1.
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

  #[local] Notation K_entry_cstack b e w :=
    (entry_cstack {| tf_csp := Cap RWL Local b e (stk_start_a b e);
                     tf_export_tbl := w;
                     tf_error_count := 0 |}) (only parsing).

  (** After the call: the thread's world of [C] gives what the flag hands
      over, and the thread keeps its local map. *)
  Lemma tsy_handed_of_world W C (b : Addr) :
    world_interp W C -∗
    (LNonHeap b) ↪ᵖ[C]{RW} (safeGC interp_nonlocal) -∗
    tsy_handed C b ∗ local_region_map th W C ∅.
  Proof.
    iIntros "Hworld #Hrel".
    iEval (rewrite world_interp_eq) in "Hworld".
    iDestruct "Hworld" as "[Hperm Hlocal]".
    iFrame "Hlocal".
    rewrite /tsy_handed.
    iFrame "Hperm".
    iExists (safeGC interp_nonlocal).
    iFrame "Hrel".
    iSplit; first (iPureIntro; intros Cv; apply _).
    iIntros "!>" (z).
    iApply interp_nonlocal_int.
  Qed.

  (** The thread runs [K.run1] with interrupts enabled: it shares its
      global [b] with [B.f], which only it runs ([B] is exclusive); after
      the return, it sets [flag] to [1], which hands the map of the
      Permanent regions of [B] to the invariant of [flag], and exits. *)
  Lemma tsy_run1_spec
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
    (γ : gname)
    :
    let imports := tsy_K_imports B_f in

    th ≠ CtxSwitch ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_mmio_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    is_mmio_address (cgp_b ^+ 1) = false ->
    is_heap_address (cgp_b ^+ 1) = false ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->

    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (lword_of_word (WInt 0)) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length tsy_K_code) ->

    (cgp_b + length tsy_K_data)%a = Some cgp_e ->
    (pc_b + tsy_label ".Lsync_run1")%a = Some pc_a ->
    (* The stack holds the spill of the switcher call *)
    (csp_b + SpillSlot_size + StackEntry_reserved_space <= csp_e)%Z ->

    is_heap_cap (WSealed ot_switcher B_f) = false ->
    (* The stack is revoked in the world of [B]: the thread keeps it *)
    revoked_addresses W_init (finz.seq_between csp_b csp_e) ->
    cmpt_shared B = false ->

    (
      thread_in th B
      ∗ na_inv (tpool th) Ntstack trusted_stack_inv
      ∗ switcher_static
      ∗ na_own (tpool th) ⊤

      (* initial register file *)
      ∗ PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e)
      ∗ cra ↦ᵣ[th] thread_return_sentry
      ∗ regs[th] rmap

      (* initial memory layout: the global [b]; [flag] is in its invariant *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a tsy_K_code
      ∗ cgp_b ↦ₐ lword_of_word (WInt 0)
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ world_interp W_init B

      ∗ interp_continuation (K_entry_cstack csp_b csp_e w_K_tbl) Ws Cs
      ∗ ◯(CSTK)[th] (K_entry_cstack csp_b csp_e w_K_tbl)

      ∗ interp W_init B (WSealed ot_switcher B_f)
      ∗ B_f ↦ₑ□{nargs} 1

      (* the initial stack is revoked in the world of [B] *)
      ∗ StackRevokedResources W_init B (finz.seq_between csp_b csp_e)
      (* the invariant of [flag] *)
      ∗ tsy_flag γ B (cgp_b ^+ 1) cgp_b
      (* the entry of [K.run1] keeps interrupts enabled *)
      ∗ MIE ↦ₜ[th] InterruptEnabled
      ∗ held (th := th) InterruptEnabled
      ⊢ safe[th])%I.
  Proof.
    (* Outline of the proof:
       - [tsy_init_blocks_1_spec]: block 0, prepare the capability to [b],
         the argument of the call to [B.f],
       - [cmdc_world_share]: share [b] in the world of [B], as a Permanent
         region,
       - [tsy_call_blocks_2_spec]: blocks 1-3, fetch the imports and jump to
         the switcher,
       - [switcher_cc_specification]: call to [B.f], which returns with
         interrupts enabled,
       - [tsy_handed_of_world]: the world of [B] gives what the flag hands
         over,
       - the store to [flag], one step with the critical-section token:
         [tsy_flag_deposit] puts what the flag hands over into the invariant
         of [flag],
       - [tsy_run1_return_spec]: return, the thread exits. *)
    intros imports; subst imports.
    iIntros (Hth Hpc_shadow Hpc_nonheap Hcgp_mmio Hcgp_heap Hflag_mmio Hflag_heap
               Hstk_shadow Hstk_heap Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hstk_min HB_f_nonheap Hrevoked_stack
               Hshared_B)
      "(#Hthread & #Hswitcher & #Hswitcher_static & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Himports_main & Hcode_main & Hcgp_b & Hcsp_stk
      & Hworld_B & HK & Hcstk_frag
      & #Hinterp_Winit_B_f & #HentryB_f
      & Hstack_revoked & #Hflag_inv & Hmie & Hheld)".
    iExtractList "Hrmap" [ca0;ca1;ctp;ct0;ct1;cs0;cs1]
      as ["Hca0";"Hca1";"Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1"].
    iEval (cbn [fmap list_fmap tsy_K_imports]) in "Himports_main".
    iRegionSplit "Himports_main"
      as "(Himport_switcher & Himport_assert & Himport_B_f)".
    assert (tsy_code_bounds pc_b pc_e pc_a B_f) as Hbounds
      by (rewrite /tsy_code_bounds; eauto 10).

    (* Block 0: the capability to b *)
    iApply (tsy_init_blocks_1_spec with
             "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hcs0 $Hcra $Hcode_main]");
      [done..|].
    iNext; iIntros "(HPC & Hcgp & Hca0 & [%wct0' Hct0] & [%wct1' Hct1] & Hcs0 & Hcra
                    & Hcode_main)".

    (* Share b in the world of B *)
    iMod (cmdc_world_share W_init B cgp_b (cgp_b ^+ 1) csp_b csp_e B_f with
           "Hworld_B Hstack_revoked Hinterp_Winit_B_f Hcgp_b Hcsp_stk")
      as "(Hworld_B & #Hrel_cgp_b & #Hinterp_ca0 & #Hinterp_B_f
           & Hstack_revoked & %Hrevoked & %Hcgp_b_stk & Hcsp_stk)";
      [solve_addr|done..|].

    (* Blocks 1-3: fetch the imports and jump to the switcher *)
    iApply (tsy_call_blocks_2_spec with
             "[- $HPC $Hctp $Hct1 $Hcra
              $Himport_switcher $Himport_B_f $Hcode_main $Hmie $Hheld]");
      [done | by intros ?%Hth |].
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
    iApply (switcher_cc_specification W_init B _ _ _ _ csp_b csp_e (stk_start_a csp_b csp_e)
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
    { exact Hshared_B. }
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
      & Hrmap & _ & _ & %Hrestored & %Hroute_B & Hmie & Hheld)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & _).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0; [|exact thread_return_sentry_not_heap].
    subst rcgp rcra rcs0.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    (* The return restores the posture of [K]: interrupts enabled *)
    iEval (rewrite default_jalr_target_mie_ret_kind) in "Hmie Hheld".

    (* What the flag hands over; the thread never enters B again, and
       drops its local map *)
    iDestruct (tsy_handed_of_world with "Hworld_B Hrel_cgp_b") as "[Hhanded _]".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ctp;ct0;ct2]
      as ["Hctp";"Hct0";"Hct2"].
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code tsy_K_code "Hcode_main".

    (* Block 3, from the return of the call: set [flag] *)
    focus_block (tsy_block ".Lsync_flag") "Hcode_main" of tsy_K_blocks at pc_a
      as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_call ^+ 1).
    (* Lea cgp cgp 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }
    (* Store cgp 1%Z 0: one step with the critical-section token, which
       opens the invariant of [flag] and closes it with what it hands over *)
    iInstr_lookup "Hcode" as "Hi" "Hcode_cont".
    wp_instr.
    iDestruct "Hi" as "#Hi".
    iApply (wp_wand with "[HPC Hcgp Hheld Hmie Hhanded]").
    { iApply (wp_core_full_crit (ceriseg := ceriseG_of th) (th := th) ⊤ InterruptEnabled
                (λ b' v, ⌜b' = InterruptEnabled⌝ ∗ ⌜v = NextIV⌝ ∗
                   PC ↦ₚ[th] Cap RX Global pc_b pc_e (a_call ^+ 3) ∗
                   cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e (cgp_b ^+ 1))%I
               with "Hheld Hmie").
      { by intros ?%Hth. }
      iIntros "Hcrit Hmie".
      iMod (tsy_flag_deposit ⊤ γ B (cgp_b ^+ 1) cgp_b with "Hflag_inv Hcrit")
        as "[ [%wflag Hflag] Hclose]"; first solve_ndisj.
      iApply wp_fupd.
      iAssert (deref_res None 1%Qp) as "Hdr"; first by rewrite /deref_res.
      iApply (wp_store_success_z_imm (ceriseg := ceriseG_of th) (th := th) (CL := link_core)
                with "[$HPC $Hi $Hcgp $Hflag $Hdr]"); try solve_pure.
      { by apply not_mmio_not_shadow. }
      { solve_addr. }
      { solve_addr. }
      iIntros "!> (HPC & _ & Hcgp & Hflag & _)".
      iMod ("Hclose" with "Hflag Hhanded") as "Hcrit".
      iModIntro. iNext. iExists InterruptEnabled. by iFrame. }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (b') "(Hheld & Hmie & >-> & >-> & HPC & Hcgp)".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ tsy_label_offset ".Lsync_run1_return").

    (* Block 3: return, the thread exits *)
    iDestruct (regs_of_parts _ [(cgp, _); (cs1, _); (csp, _)]
                 {[ ca0 ; ca1 ; cs0 ; cra ; ctp ; ct0 ; ct2 ]}
                 with "Hrmap [Hcgp Hcs1 Hcsp]")
      as (rmap_ret) "[%Hrmap_ret Hrmap]".
    { rewrite !dom_delete_L Hrmap_dom. apply set_eq. intros r.
      pose proof (all_registers_s_correct r). set_solver. }
    { cbn. iFrame. }
    iApply (tsy_run1_return_spec _ _ _ B_f with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hca0 $Hca1 $Hcs0 $Hcra $Hctp $Hct0 $Hct2
               $Hrmap $Hcstk_frag $Hcode_main $Hmie $Hheld]");
      [done | done | done | by intros ?%Hth].
  Qed.
End TSY_run1.
