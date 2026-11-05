From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import ti_spec_states.

(** * Temporal isolation, blocks 3-5: overwrite, assertion and return

    On return from the call to [B.f], block 3 overwrites [b := 42] and
    loads [b], block 4 asserts that [b = 42] and block 5 clears the return
    values and returns through the switcher's return sentry, saved in
    [cs0]: the thread exits. *)

Section TI_Assert_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma ti_assert_blocks_3_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr) (B_f : Sealable) (cstk : CSTK) (rmap : LReg)
    (wcgp_b wctp wct0 wct1 wct2 wca0 wca1 wca2 wcra : LWord) (b : InterruptStatus) :
    ti_code_bounds pc_b pc_e pc_a B_f ->
    (cgp_b + length ti_K_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    cstk.(cstk_frames) = [] ->
    dom rmap = all_registers_s ∖ {[ cgp ; ct1 ; ca0 ; ca1 ; ca2 ; cra ; cs0 ; ctp ; ct0 ; ct2 ]} ->
    route_pre th b ->
    assert_static b_assert e_assert a_flag ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ ti_label_offset ".Lti_overwrite")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    regs[th] rmap ∗
    ◯(CSTK)[th] cstk ∗
    cgp_b ↦ₐ wcgp_b ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    codefrag_pers pc_a ti_K_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & Hsealed_nonheap)
             Hcgp_contiguous Hcgp_mmio Hframes Hdom Hroute)
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna & HPC & Hcgp & Hctp & Hct0 & Hct1
      & Hct2 & Hca0 & Hca1 & Hca2 & Hcra & Hcs0 & Hrmap & Hcstk & Hcgp_b & Himport_assert
      & Hcode_main & Hmie & Hheld)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code ti_K_code "Hcode_main".
    rewrite /assert_entry.

    (* Block 3: return from the call, overwrite [b] and load it *)
    focus_block (ti_block ".Lti_call_B") "Hcode_main" of ti_K_blocks at pc_a
      as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_call ^+ 1).
    (* Store cgp 42%Z 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hcgp_mmio. }
    { solve_addr+Hcgp_contiguous. }
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hcgp_mmio. }
    { done. }
    { split; [done| solve_addr]. }
    (* Mov ct1 42%Z *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: assert that b = 42 *)
    focus_block (ti_block ".Lti_assert") "Hcode_main" of ti_K_blocks at pc_a
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

    (* Block 5: return, the thread exits *)
    focus_block (ti_block ".Lti_return") "Hcode_main" of ti_K_blocks at pc_a
      as a_ret Ha_ret "Hcode" "Hcont".
    (* Mov ca0 0%Z *)
    iInstr "Hcode".
    (* Mov ca1 0%Z *)
    iInstr "Hcode".
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    assert (list_to_set [cgp; ct1; ca0; ca1; ca2; cra; cs0] ∪ dom rmap
            = all_registers_s ∖ {[ ctp ; ct0 ; ct2 ]})
      as Hdom_exit.
    { rewrite Hdom. apply set_eq. intros r. pose proof (all_registers_s_correct r). set_solver. }
    iDestruct (regs_of_parts rmap
                 [(cgp, _); (ct1, _); (ca0, _); (ca1, _); (ca2, _); (cra, _); (cs0, _)]
                 _ Hdom_exit with "Hrmap [Hcgp Hct1 Hca0 Hca1 Hca2 Hcra Hcs0]")
      as (rmap_exit) "[%Hdom_rmap_exit Hrmap]".
    { cbn. iFrame. }
    iApply (switcher_ret_thread_exit_specification _ _ _ _ rmap_exit _ Hframes Hdom_rmap_exit with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hrmap $Hcstk $Hmie $Hheld]").
  Qed.

End TI_Assert_Blocks_3.
