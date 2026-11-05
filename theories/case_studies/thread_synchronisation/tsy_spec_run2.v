From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel.
From griotte Require Import switcher_base.
From griotte Require Import wp_core_full yield.
From griotte Require Import proofmode register_tactics.
From griotte Require Import tsy_flag tsy_spec_states tsy_spec_exit_blocks_3.

Section TSY_run2.
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

  (** The thread runs [K.run2] with interrupts enabled: it reads [flag],
      yielding while it holds [0]; the read of [1] gives it the map of the
      Permanent regions of [B], which no thread of [B] holds any more; it
      opens the region of [b], writes [42], reads it back and asserts it,
      closes the region, and exits. It is not a thread of [B]. *)
  Lemma tsy_run2_spec
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rmap : LReg)
    (wcsp : LWord)
    (B_f : Sealable)
    (cstk : CSTK)
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

    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length tsy_K_code) ->
    (cgp_b + length tsy_K_data)%a = Some cgp_e ->
    (pc_b + tsy_label ".Lsync_run1")%a = Some pc_a ->
    cstk.(cstk_frames) = [] ->

    (
      assert_static b_assert e_assert a_flag
      ∗ na_inv (tpool th) Ntstack trusted_stack_inv
      ∗ switcher_static
      ∗ na_own (tpool th) ⊤

      (* initial register file *)
      ∗ PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ tsy_label_offset ".Lsync_run2")
      ∗ cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ[th] wcsp
      ∗ cra ↦ᵣ[th] thread_return_sentry
      ∗ regs[th] rmap

      (* the code of [K] *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a tsy_K_code

      ∗ ◯(CSTK)[th] cstk
      (* the invariant of [flag], and the token of the waiting thread *)
      ∗ tsy_flag γ B (cgp_b ^+ 1) cgp_b
      ∗ tsy_tok γ
      (* the entry of [K.run2] keeps interrupts enabled *)
      ∗ MIE ↦ₜ[th] InterruptEnabled
      ∗ held (th := th) InterruptEnabled
      ⊢ safe[th])%I.
  Proof.
    intros imports; subst imports.
    iIntros (Hth Hpc_shadow Hpc_nonheap Hcgp_mmio Hcgp_heap Hflag_mmio Hflag_heap
               Hrmap_dom HsubBounds Hcgp_contiguous Himports_contiguous Hframes)
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & #Himports_main & #Hcode_main
      & Hcstk_frag & #Hflag_inv & Htok & Hmie & Hheld)".
    (* With interrupts enabled, the posture holds nothing *)
    iDestruct "Hheld" as "#Hheld".
    iExtractList "Hrmap" [ct0;ct1;ct2;ca0;ca1;ca2;ctp]
      as ["Hct0";"Hct1";"Hct2";"Hca0";"Hca1";"Hca2";"Hctp"].
    iEval (cbn [fmap list_fmap tsy_K_imports]) in "Himports_main".
    iRegionSplit "Himports_main" as "(_ & Himport_assert & _)".
    (* The block lemmas ask the import of [B.f] not to be a heap
       capability, which they do not use: any sealed capability whose base
       is the code's will do *)
    assert (tsy_code_bounds pc_b pc_e pc_a (SCap false RX Global pc_b pc_e pc_a))
      as Hbounds.
    { rewrite /tsy_code_bounds; split_and!; try done.
      rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code tsy_K_code "Hcode_main".

    (* Block 4: the wait for [flag] *)
    focus_block (tsy_block ".Lsync_run2") "Hcode_main" of tsy_K_blocks at pc_a
      as a_run2 Ha_run2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ct0 cgp *)
    iInstr "Hcode".
    (* Lea ct0 ct0 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }

    (* The loop, at [.Lsync_wait] *)
    iLöb as "IH" forall (wct1).
    (* CLoad ct1 ct0 0: one step with the critical-section token, which
       opens the invariant of [flag]; at [1], it takes what the flag hands
       over and leaves the token of the thread *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_wand with "[HPC Hi Hct0 Hct1 Hmie Htok]").
    { iApply (wp_core_full_crit (ceriseg := ceriseG_of th) (th := th) ⊤ InterruptEnabled
                (λ b' v, ⌜b' = InterruptEnabled⌝ ∗ ⌜v = NextIV⌝ ∗
                   PC ↦ₚ[th] Cap RX Global pc_b pc_e (a_run2 ^+ 3) ∗
                   ct0 ↦ᵣ[th] Cap RW Global cgp_b cgp_e (cgp_b ^+ 1) ∗
                   ∃ z : Z, ⌜z = 0 ∨ z = 1⌝ ∗ ct1 ↦ᵣ[th] WInt z ∗
                     (if decide (z = 1) then tsy_handed B cgp_b else tsy_tok γ))%I
               with "Hheld Hmie").
      { by intros ?%Hth. }
      iIntros "Hcrit Hmie".
      iMod (tsy_flag_take ⊤ γ B (cgp_b ^+ 1) cgp_b with "Hflag_inv Hcrit Htok")
        as (z) "(%Hz & Hflag & Hz & Hclose)"; first solve_ndisj.
      (* The later of what the flag hands over, around both branches *)
      iAssert (▷ (if decide (z = 1) then tsy_handed B cgp_b else tsy_tok γ))%I
        with "[Hz]" as "Hz".
      { case_decide; [done | by iNext]. }
      iApply wp_fupd.
      iAssert (deref_res None 1%Qp) as "Hdr"; first by rewrite /deref_res.
      iApply (wp_load_success_notinstr (ceriseg := ceriseG_of th) (th := th) (CL := link_core)
                with "[$HPC $Hi $Hct1 $Hct0 $Hflag $Hdr]"); try solve_pure.
      { by apply not_mmio_not_shadow. }
      { done. }
      { split; first done. solve_addr. }
      iIntros "!> (HPC & Hct1 & _ & Hct0 & Hflag & _)".
      iMod ("Hclose" with "Hflag") as "Hcrit".
      iModIntro. iNext. iExists InterruptEnabled. iFrame. by iPureIntro. }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (b') "(_ & Hmie & >-> & >-> & HPC & Hct0 & Hz)".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    iDestruct "Hz" as (z) "(%Hz & Hct1 & Hz)".
    destruct Hz as [-> | ->]; iSimpl in "Hz".
    - (* [flag] holds [0]: the thread yields and waits again *)
      (* Jnez ".Lsync_go" ct1 *)
      iInstr "Hcode".
      (* Ecall *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      iApply (wp_yield with "HPC Hi Hmie Hheld"); [done | solve_pure | solve_pure | |].
      { transitivity (Some (a_run2 ^+ 5)); auto; solve_addr. }
      iNext; iIntros "HPC _ Hmie _".
      (* Jmp ".Lsync_wait" *)
      iInstr "Hcode".
      { transitivity (Some (a_run2 ^+ 2)); auto; solve_addr. }
      iApply ("IH" with "Hna Hcsp Hcra Hcstk_frag Hz Hmie Hct1 Hct2 Hca0 Hca1 Hca2
                Hctp Hrmap Hcgp HPC Hct0").
    - (* [flag] holds [1]: the thread holds the map of the Permanent regions
         of [B], and opens the region of [b] *)
      (* Jnez ".Lsync_go" ct1 *)
      iInstr "Hcode".
      iDestruct (tsy_handed_acc B cgp_b with "Hz") as "[ [%wb Hb] Hclose_b]".
      (* Store cgp 42%Z 0 *)
      iInstr "Hcode".
      { by apply not_mmio_not_shadow. }
      { solve_addr. }
      (* CLoad ct0 cgp 0 *)
      iInstr "Hcode".
      { by apply not_mmio_not_shadow. }
      { done. }
      { split; first done. solve_addr. }
      (* Mov ct1 42%Z *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      iSimpl in "Hct0 Hct1".

      (* Block 5: assert that b = 42, the region of [b] still open *)
      change_pc_to (pc_a ^+ tsy_label_offset ".Lsync_assert").
      iApply (tsy_run2_assert_spec _ _ _ (SCap false RX Global pc_b pc_e pc_a) with
               "[- $Hassert $HPC $Hct0 $Hct1 $Hct2 $Hca2 $Hcra $Himport_assert $Hcode_main
                 $Hmie $Hheld]"); [done | by intros ?%Hth |].
      iNext; iIntros "(HPC & Hct0 & Hct1 & Hct2 & Hca2 & Hcra & _ & _ & Hmie & _)".
      (* The region of [b] is closed with [42]; the thread drops the map *)
      iDestruct ("Hclose_b" $! 42%Z with "Hb") as "_".

      (* Block 6: return, the thread exits *)
      iDestruct (regs_of_parts _ [(cgp, _); (csp, _); (ct1, _); (ca2, _)]
                   {[ ca0 ; ca1 ; cra ; ctp ; ct0 ; ct2 ]}
                   with "Hrmap [Hcgp Hcsp Hct1 Hca2]")
        as (rmap_ret) "[%Hrmap_ret Hrmap]".
      { rewrite !dom_delete_L Hrmap_dom. apply set_eq. intros r.
        pose proof (all_registers_s_correct r). set_solver. }
      { cbn. iFrame. }
      iApply (tsy_run2_return_spec _ _ _ (SCap false RX Global pc_b pc_e pc_a) with
               "[$Hswitcher $Hswitcher_static $Hna $HPC $Hca0 $Hca1 $Hcra $Hctp $Hct0 $Hct2
                 $Hrmap $Hcstk_frag $Hcode_main $Hmie $Hheld]");
        [done | done | done | by intros ?%Hth].
  Qed.
End TSY_run2.
