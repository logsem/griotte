From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import tsy_spec_states.

(** * Thread synchronisation, blocks 3, 5 and 6: the returns and the assertion

    The return of [run1], at the end of block 3, clears the return values,
    restores the return address of the thread, the switcher's return
    sentry saved in [cs0], and returns through it: the thread exits. Block
    5 asserts that [b = 42], in [run2]. Block 6, the return of [run2],
    clears the return values and returns through [cra], which still holds
    the switcher's return sentry: the thread exits. *)

Section TSY_Exit_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The return of [run1]: the thread exits. *)
  Lemma tsy_run1_return_spec
    (pc_b pc_e pc_a : Addr) (B_f : Sealable) (cstk : CSTK) (rmap : LReg)
    (wca0 wca1 wcra wctp wct0 wct2 : LWord) (b : InterruptStatus) :
    tsy_code_bounds pc_b pc_e pc_a B_f ->
    cstk.(cstk_frames) = [] ->
    dom rmap = all_registers_s ∖ {[ ca0 ; ca1 ; cs0 ; cra ; ctp ; ct0 ; ct2 ]} ->
    route_pre th b ->
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ tsy_label_offset ".Lsync_run1_return")%a ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cra ↦ᵣ[th] wcra ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    regs[th] rmap ∗
    ◯(CSTK)[th] cstk ∗
    codefrag_pers pc_a tsy_K_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & HB_f_nonheap)
             Hframes Hdom Hroute)
      "(#Hswitcher & #Hswitcher_static & Hna & HPC & Hca0 & Hca1 & Hcs0 & Hcra & Hctp
        & Hct0 & Hct2 & Hrmap & Hcstk & Hcode_main & Hmie & Hheld)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code tsy_K_code "Hcode_main".

    (* Block 3, after the store to [flag]: return *)
    focus_block (tsy_block ".Lsync_run1_return") "Hcode_main" of tsy_K_blocks at pc_a
      as a_call Ha_call "Hcode" "Hcont".
    change_pc_to (a_call ^+ 3).
    (* Mov ca0 0%Z *)
    iInstr "Hcode".
    (* Mov ca1 0%Z *)
    iInstr "Hcode".
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    assert (list_to_set [ca0; ca1; cs0; cra] ∪ dom rmap = all_registers_s ∖ {[ ctp ; ct0 ; ct2 ]})
      as Hdom_exit.
    { rewrite Hdom. apply set_eq. intros r. pose proof (all_registers_s_correct r). set_solver. }
    iDestruct (regs_of_parts rmap [(ca0, _); (ca1, _); (cs0, _); (cra, _)] _ Hdom_exit
                 with "Hrmap [Hca0 Hca1 Hcs0 Hcra]")
      as (rmap_exit) "[%Hdom_rmap_exit Hrmap]".
    { cbn. iFrame. }
    iApply (switcher_ret_thread_exit_specification _ _ _ _ rmap_exit _ Hframes Hdom_rmap_exit with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hrmap $Hcstk $Hmie $Hheld]").
  Qed.

  (** Block 5: assert that [b = 42]. The lemma takes a continuation, so
      that the caller keeps the region of [b] open across the assertion; the
      continuation is under the step's later. *)
  Lemma tsy_run2_assert_spec
    (pc_b pc_e pc_a : Addr) (B_f : Sealable)
    (wct2 wca2 wcra : LWord) (b : InterruptStatus) :
    tsy_code_bounds pc_b pc_e pc_a B_f ->
    route_pre th b ->
    assert_static b_assert e_assert a_flag ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ tsy_label_offset ".Lsync_assert")%a ∗
    ct0 ↦ᵣ[th] WInt 42 ∗
    ct1 ↦ᵣ[th] WInt 42 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    cra ↦ᵣ[th] wcra ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    codefrag_pers pc_a tsy_K_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ▷ ( PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ tsy_label_offset ".Lsync_run2_return")%a ∗
        ct0 ↦ᵣ[th] WInt 0 ∗
        ct1 ↦ᵣ[th] WInt 0 ∗
        ct2 ↦ᵣ[th] WInt 0 ∗
        ca2 ↦ᵣ[th] WInt 0 ∗
        cra ↦ᵣ[th] wcra ∗
        (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
        codefrag_pers pc_a tsy_K_code ∗
        MIE ↦ₜ[th] b ∗
        held (th := th) b
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & HB_f_nonheap)
             Hroute)
      "(#Hassert & HPC & Hct0 & Hct1 & Hct2 & Hca2 & Hcra & Himport_assert
      & Hcode_main & Hmie & Hheld & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code tsy_K_code "Hcode_main".
    rewrite /assert_entry.

    (* Block 5: assert that b = 42 *)
    focus_block (tsy_block ".Lsync_assert") "Hcode_main" of tsy_K_blocks at pc_a
      as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert $Hmie $Hheld]"); auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1
                    & Hmie & Hheld & _ & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ tsy_label_offset ".Lsync_run2_return").
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

  (** Block 6: the return of [run2], through [cra], which still holds the
      switcher's return sentry: the thread exits. *)
  Lemma tsy_run2_return_spec
    (pc_b pc_e pc_a : Addr) (B_f : Sealable) (cstk : CSTK) (rmap : LReg)
    (wca0 wca1 wctp wct0 wct2 : LWord) (b : InterruptStatus) :
    tsy_code_bounds pc_b pc_e pc_a B_f ->
    cstk.(cstk_frames) = [] ->
    dom rmap = all_registers_s ∖ {[ ca0 ; ca1 ; cra ; ctp ; ct0 ; ct2 ]} ->
    route_pre th b ->
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ tsy_label_offset ".Lsync_run2_return")%a ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    cra ↦ᵣ[th] thread_return_sentry ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    regs[th] rmap ∗
    ◯(CSTK)[th] cstk ∗
    codefrag_pers pc_a tsy_K_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & HB_f_nonheap)
             Hframes Hdom Hroute)
      "(#Hswitcher & #Hswitcher_static & Hna & HPC & Hca0 & Hca1 & Hcra & Hctp
        & Hct0 & Hct2 & Hrmap & Hcstk & Hcode_main & Hmie & Hheld)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code tsy_K_code "Hcode_main".

    (* Block 6: return *)
    focus_block (tsy_block ".Lsync_run2_return") "Hcode_main" of tsy_K_blocks at pc_a
      as a_ret Ha_ret "Hcode" "Hcont".
    (* Mov ca0 0%Z *)
    iInstr "Hcode".
    (* Mov ca1 0%Z *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    assert (list_to_set [ca0; ca1; cra] ∪ dom rmap = all_registers_s ∖ {[ ctp ; ct0 ; ct2 ]})
      as Hdom_exit.
    { rewrite Hdom. apply set_eq. intros r. pose proof (all_registers_s_correct r). set_solver. }
    iDestruct (regs_of_parts rmap [(ca0, _); (ca1, _); (cra, _)] _ Hdom_exit
                 with "Hrmap [Hca0 Hca1 Hcra]")
      as (rmap_exit) "[%Hdom_rmap_exit Hrmap]".
    { cbn. iFrame. }
    iApply (switcher_ret_thread_exit_specification _ _ _ _ rmap_exit _ Hframes Hdom_rmap_exit with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hrmap $Hcstk $Hmie $Hheld]").
  Qed.

End TSY_Exit_Blocks_3.
