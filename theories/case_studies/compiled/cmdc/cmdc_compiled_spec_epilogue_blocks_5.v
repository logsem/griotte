From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import cmdc_compiled_spec_states.

(** * Compiled cmdc, blocks 8-9: the epilogue of [run]

    Block 8 sets the return values. Block 9 reloads [cra], [cs0] and [cs1]
    from the frame of [run], moves the stack cursor back above the frame
    and returns through [cra], the switcher's return sentry: the thread
    exits. *)

Section CMDC_Compiled_Epilogue_Blocks_5.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Lemma cmdc_compiled_return_spec
    (pc_b pc_e pc_a csp_b csp_e a_f : Addr) (cstk : CSTK) (rmap : LReg)
    (wca0 wca1 wcs0 wcs1 wcra wctp wct0 wct2 : LWord) (b : InterruptStatus) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_compiled_main_code) ->
    cstk.(cstk_frames) = [] ->
    dom rmap = all_registers_s ∖ {[ csp ; ca0 ; ca1 ; cs0 ; cs1 ; cra ; ctp ; ct0 ; ct2 ]} ->
    disjoint_from_mmio csp_b csp_e ->
    (a_f + Z.of_nat cmdc_compiled_main_run_frame_size)%a = Some (stk_start_a csp_b csp_e) ->
    (csp_b <= a_f)%a ->
    (stk_start_a csp_b csp_e <= csp_e)%a ->
    route_pre th b ->
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e
      (pc_a ^+ cmdc_compiled_label_offset ".Lcmdc_run_return_assert_2")%a ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e a_f ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    cra ↦ᵣ[th] wcra ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    regs[th] rmap ∗
    a_f ↦ₐ WInt 0 ∗
    (a_f ^+ 1) ↦ₐ WInt 0 ∗
    (a_f ^+ 2) ↦ₐ thread_return_sentry ∗
    ◯(CSTK)[th] cstk ∗
    codefrag_pers pc_a cmdc_compiled_main_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b
    ⊢ safe[th].
  Proof.
    iIntros (HsubBounds Hframes Hdom Hstk_mmio Ha_f Hcsp_b Hstk_start Hroute)
      "(#Hswitcher & #Hswitcher_static & Hna & HPC & Hcsp & Hca0 & Hca1 & Hcs0 & Hcs1
        & Hcra & Hctp & Hct0 & Hct2 & Hrmap & Hf0 & Hf1 & Hf2 & Hcstk & Hcode_main
        & Hmie & Hheld)".
    rewrite /cmdc_compiled_main_run_frame_size in Ha_f.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code cmdc_compiled_main_code "Hcode_main".

    (* Block 8: the return values *)
    focus_block (cmdc_compiled_block ".Lcmdc_run_return_assert_2") "Hcode_main"
      of cmdc_compiled_main_blocks at pc_a as a_ret Ha_ret "Hcode" "Hcont".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 9: reload the spilled registers and return *)
    focus_block (cmdc_compiled_block ".Lcmdc_run_epilogue") "Hcode_main"
      of cmdc_compiled_main_blocks at pc_a as a_epi Ha_epi "Hcode" "Hcont".
    assert ((a_f + 2)%a = Some (a_f ^+ 2)) as Ha_f2 by solve_addr+Ha_f.
    assert ((a_f + 1)%a = Some (a_f ^+ 1)) as Ha_f1 by solve_addr+Ha_f.
    (* CLoad cra csp 2 *)
    iInstr "Hcode".
    { solve_not_shadow Hstk_mmio. }
    { exact thread_return_sentry_not_heap. }
    { split; [done | rewrite /withinBounds; solve_addr]. }
    (* CLoad cs0 csp 1 *)
    iInstr "Hcode".
    { solve_not_shadow Hstk_mmio. }
    { done. }
    { split; [done | rewrite /withinBounds; solve_addr]. }
    (* CLoad cs1 csp 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hstk_mmio. }
    { done. }
    { split; [done | rewrite /withinBounds; solve_addr]. }
    (* Lea csp csp 3 *)
    iInstr "Hcode".
    iEval (rewrite lload_word_RWL) in "Hcra Hcs0 Hcs1".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".

    (* The thread exits *)
    assert (list_to_set [csp; ca0; ca1; cs0; cs1; cra] ∪ dom rmap =
              all_registers_s ∖ {[ ctp ; ct0 ; ct2 ]}) as Hdom_exit.
    { rewrite Hdom. apply set_eq. intros r. pose proof (all_registers_s_correct r). set_solver. }
    iDestruct (regs_of_parts rmap [(csp, _); (ca0, _); (ca1, _); (cs0, _); (cs1, _); (cra, _)]
                 _ Hdom_exit with "Hrmap [Hcsp Hca0 Hca1 Hcs0 Hcs1 Hcra]")
      as (rmap_exit) "[%Hdom_rmap_exit Hrmap]".
    { cbn. iFrame. }
    iApply (switcher_ret_thread_exit_specification _ _ _ _ rmap_exit _ Hframes Hdom_rmap_exit with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hrmap $Hcstk $Hmie $Hheld]").
  Qed.

End CMDC_Compiled_Epilogue_Blocks_5.
