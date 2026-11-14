From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import fundamental switcher_preamble handoff switcher_link.
From griotte Require Import exception_dispatch virtualise context_switch_layout_instance.
From griotte Require Import context_switching_support context_switching_spill.
From griotte Require Import context_switching_hyps context_switching_park.

(** * The scheduler call of the context-switch thread

    After the park, the context-switch thread calls the scheduler: it seals
    the trusted stack of the parked thread with the trusted-stack otype into
    [ca0], passes the cause, the address of MEPCC and mtval in [ca1]–[ca3],
    loads the scheduler's stack, globals and entry from the switcher's data,
    clears the other registers, and jumps to the scheduler, with interrupts
    disabled. The return sentry it passes is valid in the scheduler's world;
    a target that is not a valid PC faults to the trap vector. *)

Section ctx_scheduler_call.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    (C_sched : CmptName) (w_pcc w_cgp w_csp : LWord).

  (** The jump to the scheduler at the [cjalr]: its entry, stack and
      globals in [cra], [csp] and [cgp], its four arguments in [ca0]–[ca3]
      valid in the world [W] of its state, the other registers cleared, with
      interrupts disabled and mtdc at the context-switch thread's home. *)
  Lemma ctx_scheduler_jump_spec (W : WORLD) (cstk : CSTK) (Ws : list WORLD)
      (Cs : list CmptName) (lreg : LReg) :
    CtxSwitch ∈ cmpt_threads C_sched →
    dom lreg = all_registers_s →
    lreg !! cra = Some w_pcc →
    lreg !! csp = Some w_csp →
    lreg !! cgp = Some w_cgp →
    (∀ r, r ∈ registers_scheduler_call → lreg !! r = Some (lword_of_word (WInt 0))) →
    frame_match Ws Cs cstk W C_sched →
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_scheduler_cjalr" ∗
    switcher_code_at CtxSwitch ∗
    scheduler_entry_valid C_sched w_pcc w_cgp ∗
    ctx_trap_vector_safe ∗
    ctx_resume_specs C_sched w_csp ∗
    □ (∀ (r : RegName) (w : LWord),
         ⌜r ∈ [ca0; ca1; ca2; ca3]⌝ → ⌜lreg !! r = Some w⌝ →
         interp (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full) W C_sched w) ∗
    regs[CtxSwitch] lreg ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    mtdc_lent_at (th := CtxSwitch) ∗
    handover_res (ceriseg := ceriseG_of CtxSwitch) ∗
    na_own (tpool CtxSwitch) ⊤ ∗
    world_resources (th := CtxSwitch) W C_sched ∗
    shared_credit C_sched ∗
    ◯(CSTK)[CtxSwitch] cstk ∗
    interp_continuation (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full)
      cstk Ws Cs ∗
    top_cmpt_untrusted (th := CtxSwitch)
      (interp (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full)) W C_sched cstk ∗
    interp (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full) W C_sched w_csp
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hsched_in Hdom Hcra Hcsp Hcgp Hzero Hframe)
      "(HPC & #Hswitcher & #Hentry & #Htrap & #Hresume & #Hargs & Hregs & HMIE & Hmtdc & Hlent
        & Hho & Hna & Hworld & Hcred & Hcstk & Hcont & #Htop & #Hcsp_v)".
    pin_thread_instances CtxSwitch.
    switcher_open_label ".Lexception_scheduler_call" "Hswitcher" as "Hcode" a_call Ha_call.
    switcher_pc_in_block ".Lexception_scheduler_call" ".Lexception_scheduler_cjalr" "HPC".
    assert (∀ r, is_Some (lreg !! r)) as Hsome.
    { intros r. apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }

    (* [cnull] holds [lnull] *)
    destruct (Hsome cnull) as [wnull Hnull].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cnull with "Hregs")
      as "[Hnull Hregs]"; first exact Hnull.
    iMod (cnull_lnull (ceriseg := ceriseG_of CtxSwitch) ⊤ with "Hnull") as "[Hnull %Hwnull]".
    subst wnull.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cnull with "[$Hnull $Hregs]")
      as "Hregs"; first exact Hnull.

    (* The registers but [cra] are valid in [W] *)
    iAssert (∀ (r : RegName) (v : LWord), ⌜r ≠ cra⌝ → ⌜lreg !! r = Some v⌝ →
               interp (th := CtxSwitch) W C_sched v)%I as "#Hregs_v".
    { iIntros (r v Hr Hv).
      pose proof (all_registers_correct r) as Hr_all.
      rewrite /all_registers !elem_of_cons elem_of_nil in Hr_all.
      destruct Hr_all as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> |
        [-> | [-> | [-> | [-> | [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
      1: { rewrite Hnull in Hv. injection Hv as <-. iApply interp_int. }
      1: done.
      1: { rewrite Hcsp in Hv. injection Hv as <-. iExact "Hcsp_v". }
      1: { rewrite Hcgp in Hv. injection Hv as <-. iDestruct ("Hentry" $! W) as "[_ $]". }
      7,8,9,10: iApply ("Hargs" with "[%] [//]"); by apply (bool_decide_unpack _).
      all: rewrite Hzero in Hv;
        [injection Hv as <-; iApply interp_int | by apply (bool_decide_unpack _)]. }

    iAssert (held (th := CtxSwitch) InterruptDisabled) with "[Hho Hmtdc Hlent]" as "Hheld".
    { rewrite held_disabled. iFrame. }
    (* A fault goes to the trap vector, which is safe for any fault *)
    iAssert (∀ (w : LWord) (rmap : LReg), ⌜∀ r, is_Some (rmap !! r)⌝ -∗
               regs[CtxSwitch] rmap -∗ na_own (tpool CtxSwitch) ⊤ -∗ ◯(CSTK)[CtxSwitch] cstk -∗
               MIE ↦ₜ[CtxSwitch] InterruptDisabled -∗ held (th := CtxSwitch) InterruptDisabled -∗
               trap_safe w ⊤ (HO CtxSwitch))%I as "Hfault".
    { iIntros (w rmap Hrmap) "Hrmap Hna Hcstk HMIE Hheld".
      iApply (interp_trap_safe (th := CtxSwitch) with "Htrap"); first done.
      iModIntro. iFrame "Hrmap Hna Hcstk". iSplitR; first by iRight.
      iExists InterruptDisabled. iFrame. done. }

    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cra with "Hregs")
      as "[Hcra Hregs]"; first exact Hcra.
    destruct (jalr_target_ok cra cra w_pcc.(lw)) eqn:Htgt; cycle 1.
    { (* The target is not a valid jump target: the jump faults *)
      (* Jalr cra cra *)
      iInstrStart "Hcode".
      iInstrApply (wp_jalr_fail_target_same (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch))
        with "[$HPC $Hcra]" as "(HPC & Hcra)".
      assert (a_call ^+ Z.to_nat 20 = a_sched_cjalr)%a as Hcjalr.
      { pose proof a_sched_cjalr_label as Hlbl. subst a_call. clear -Hlbl.
        offsets_compute. solve_addr. }
      iEval (rewrite Hcjalr) in "HPC".
      iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cra with "[$Hcra $Hregs]")
        as "Hregs"; first exact Hcra.
      iDestruct ("Hfault" $! (Cap XSRW_ Local b_switcher e_switcher a_sched_cjalr @@? None)
                  with "[//] Hregs Hna Hcstk HMIE Hheld") as "Hts".
      iTrap. }
    assert (get_tag w_pcc.(lw) = true) as Htag.
    { rewrite /jalr_target_ok in Htgt. by destruct (get_tag (lw w_pcc)). }
    iPoseProof (sched_entry_disabled C_sched w_pcc w_cgp Hsched_in Htag with "Hentry") as "%Hdis".
    iDestruct ("Hentry" $! W) as "[Hpcc_v _]".
    iDestruct (jmp_or_fail_spec (th := CtxSwitch) W C_sched w_pcc (HO CtxSwitch) with "Hpcc_v")
      as "Hjmp".
    destruct (decide (isCorrectPC (updatePcPerm w_pcc.(lw)))) as [Hok | Hnok].
    - (* The scheduler runs from its entry in [W] *)
      iDestruct "Hjmp" as (p g b e a π) "(_ & #Hjmp)".
      iDestruct ("Hjmp" $! W InterruptDisabled with "[]") as "Hexpr".
      { iApply futureworld_refl. }
      rewrite Hdis.
      (* Jalr cra cra *)
      iInstrStart "Hcode".
      iInstrApply (wp_jalr_success_call_same_posture (ceriseg := ceriseG_of CtxSwitch)
                     (th := CtxSwitch) (CL := crit_link_full CtxSwitch)
                     (CR := crit_route_full CtxSwitch) _ _ _ _ _ _ _ _ _ w_pcc InterruptDisabled)
        with "[$HPC $Hcra $HMIE $Hheld]" as "(HPC & Hcra & HMIE & Hheld)".
      { by intros _. }
      { intros _ _. by rewrite Hdis. }
      rewrite Hdis.
      assert (a_call ^+ 21 = a_sched_return)%a as Hret.
      { pose proof a_sched_return_label as Hlbl. subst a_call. clear -Hlbl.
        offsets_compute. solve_addr. }
      rewrite Hret.
      iAssert (interp (th := CtxSwitch) W C_sched ctx_resume_sentry)%I as "#Hsentry".
      { iApply (ctx_resume_sentry_valid C_sched w_csp W with "Hcsp_v").
        iModIntro. by iApply "Hresume". }
      iDestruct (big_sepM_insert_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "[$Hcra $Hregs]")
        as "Hregs".
      iApply ("Hexpr" $! cstk Ws Cs with "[-]").
      iFrame "HPC Hregs Hworld Hcred Hcont Hna Hcstk HMIE Hheld Htop".
      iSplit; first by iApply thread_in_intro.
      iSplit; first by iApply (trap_vector_safe_pre_untrusted with "Htrap").
      iSplit.
      { iApply interp_reg_intro.
        { intros r. destruct (decide (r = cra)) as [->|Hne]; first by rewrite lookup_insert_eq.
          rewrite lookup_insert_ne //. }
        iIntros (r v Hv). destruct (decide (r = cra)) as [->|Hne].
        - rewrite lookup_insert_eq in Hv. injection Hv as <-. iExact "Hsentry".
        - rewrite lookup_insert_ne // in Hv. by iApply "Hregs_v". }
      iPureIntro. split; first done. by intros _.
    - (* The target is not a valid PC: the scheduler's entry faults *)
      (* Jalr cra cra *)
      iInstrStart "Hcode".
      iInstrApply (wp_jalr_success_call_same_posture (ceriseg := ceriseG_of CtxSwitch)
                     (th := CtxSwitch) (CL := crit_link_full CtxSwitch)
                     (CR := crit_route_full CtxSwitch) _ _ _ _ _ _ _ _ _ w_pcc InterruptDisabled)
        with "[$HPC $Hcra $HMIE $Hheld]" as "(HPC & Hcra & HMIE & Hheld)".
      { by intros _. }
      { intros _ _. by rewrite Hdis. }
      rewrite Hdis.
      iDestruct (big_sepM_insert_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "[$Hcra $Hregs]")
        as "Hregs".
      iApply "Hjmp". iFrame "HPC".
      iApply ("Hfault" with "[%] Hregs Hna Hcstk HMIE Hheld").
      intros r. destruct (decide (r = cra)) as [->|Hne]; first by rewrite lookup_insert_eq.
      rewrite lookup_insert_ne //.
  Qed.

  (** The scheduler call after the park: the trusted stack of [t] sealed in
      [ca0], the cause, the address of MEPCC and mtval in [ca1]–[ca3], the
      scheduler's stack, globals and entry, the other registers cleared, and
      the jump, with interrupts disabled. *)
  Lemma ctx_scheduler_call_spec (t : nat) (g_tstk : Locality) (lreg : LReg) (wm : LWord)
      (b : InterruptStatus) (cause vt : Z) :
    t < swl_nthreads →
    CtxSwitch ∈ cmpt_threads C_sched →
    dom lreg = all_registers_s →
    lreg !! csp = Some (lword_of_word (tstack_cap g_tstk t)) →
    lreg !! ct0 = Some wm →
    lreg !! ct1 = Some (lword_of_word (WInt cause)) →
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_scheduler_call" ∗
    switcher_static (th := UserThread t) ∗
    scheduler_words w_pcc w_cgp w_csp ∗
    scheduler_entry_valid C_sched w_pcc w_cgp ∗
    ctx_trap_vector_safe ∗
    ctx_resume_specs C_sched w_csp ∗
    regs[CtxSwitch] lreg ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    mtdc_lent_at (th := CtxSwitch) ∗
    handover_at (ceriseg := ceriseG_of CtxSwitch) wm (lword_of_word (WInt cause)) vt b ∗
    na_own (tpool CtxSwitch) ⊤ ∗
    ▷ scheduler_concrete C_sched w_csp
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Ht Hsched_in Hdom Hcsp Hct0 Hct1)
      "(HPC & #Hstatic & #Hwords & #Hentry & #Htrap & #Hresume & Hregs & HMIE & Hmtdc
        & Hlent & Hho & Hna & Hsched)".
    iAssert (□ ∀ W : WORLD, interp (th := CtxSwitch) W C_sched
               (lword_of_word (Sealed ot_trusted_stacks RWL g_tstk
                  (@b_trusted_stack (tlayout_of (UserThread t)))
                  (@e_trusted_stack (tlayout_of (UserThread t)))
                  (@b_trusted_stack (tlayout_of (UserThread t))))))%I as "#Hhandle".
    { iIntros "!>" (W). by iApply (tstack_handle_sealed_valid W C_sched g_tstk t Ht with "Hstatic"). }
    iEval (rewrite /switcher_static) in "Hstatic". iNamed "Hstatic".
    iPoseProof (codefrag_pers_thread_indep (UserThread t) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher".
    iEval (rewrite /scheduler_words) in "Hwords".
    iDestruct "Hwords" as "(Hw_pcc & Hw_cgp & Hw_csp & %Hheap)".
    destruct Hheap as (Hheap_pcc & Hheap_cgp & Hheap_csp).
    pin_thread_instances CtxSwitch.
    switcher_open_label ".Lexception_scheduler_call" "Hswitcher" as "Hcode" a_call Ha_call.
    assert (∀ r, is_Some (lreg !! r)) as Hsome.
    { intros r. apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
    assert (∀ w : LWord, lload_word XSRW_ w = w) as Hload.
    { intros [w π]. rewrite /lload_word /lift_word /= load_word_no_dl_dro //. }
    assert (withinBounds b_switcher e_switcher (b_switcher ^+ 4)%a = true ∧
            withinBounds b_switcher e_switcher (b_switcher ^+ 3)%a = true ∧
            withinBounds b_switcher e_switcher (b_switcher ^+ 2)%a = true)
      as (Hwb4 & Hwb3 & Hwb2).
    { pose proof switcher_call_entry_point; pose proof switcher_size.
      split_and!; apply withinBounds_true_iff; solve_addr. }
    iEval (rewrite /handover_at /volatile_csr_at) in "Hho".
    iDestruct "Hho" as "(Hcrit & HU & Hmepcc & Hmcause & Hmtval & Hmpie)".
    destruct (Hsome ca0) as [wca0 Hca0]. destruct (Hsome ca1) as [wca1 Hca1].
    destruct (Hsome ca2) as [wca2 Hca2]. destruct (Hsome ca3) as [wca3 Hca3].
    destruct (Hsome cgp) as [wcgp Hcgp]. destruct (Hsome cra) as [wcra Hcra].
    destruct (Hsome ctp) as [wctp Hctp]. destruct (Hsome ct2) as [wct2 Hct2].
    destruct (Hsome cs0) as [wcs0 Hcs0]. destruct (Hsome cs1) as [wcs1 Hcs1].
    destruct (Hsome ca4) as [wca4 Hca4]. destruct (Hsome ca5) as [wca5 Hca5].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca0 with "Hregs")
      as "[Hca0 Hregs]"; first exact Hca0.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ csp with "Hregs")
      as "[Hcsp Hregs]"; first by rewrite !lookup_delete_ne.

    (* The trusted stack of [t], sealed *)
    (* Auipcc ca0 .sealing_key_trusted_stacks *)
    iInstr "Hcode".
    { instantiate (1 := b_switcher). switcher_addr_eq. }
    (* CLoad ca0 ca0 0 *)
    iInstr "Hcode".
    iEval (rewrite Hload) in "Hca0".
    (* Seal ca0 ca0 csp *)
    iInstr "Hcode".
    { done. }
    { pose proof ot_trusted_stacks_size; clear_switcher_layout; apply withinBounds_true_iff;
        solve_finz. }

    (* The cause, the address of MEPCC and mtval *)
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca1 with "Hregs")
      as "[Hca1 Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct1 with "Hregs")
      as "[Hct1 Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca2 with "Hregs")
      as "[Hca2 Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct0 with "Hregs")
      as "[Hct0 Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca3 with "Hregs")
      as "[Hca3 Hregs]"; first by rewrite !lookup_delete_ne.
    (* Mov ca1 ct1 *)
    iInstr "Hcode".
    (* GetA ca2 ct0 *)
    iInstr "Hcode".
    (* SpecialRW ca3 mtval cnull *)
    iInstr "Hcode".

    (* The scheduler's stack, globals and entry *)
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cgp with "Hregs")
      as "[Hcgp Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cra with "Hregs")
      as "[Hcra Hregs]"; first by rewrite !lookup_delete_ne.
    (* Auipcc csp .scheduler_entry_csp *)
    iInstr "Hcode".
    { instantiate (1 := (b_switcher ^+ 4)%a). switcher_addr_eq. }
    (* CLoad csp csp 0 *)
    iInstr "Hcode".
    iEval (rewrite Hload) in "Hcsp".
    (* Auipcc cgp .scheduler_entry_cgp *)
    iInstr "Hcode".
    { instantiate (1 := (b_switcher ^+ 3)%a). switcher_addr_eq. }
    (* CLoad cgp cgp 0 *)
    iInstr "Hcode".
    iEval (rewrite Hload) in "Hcgp".
    (* Auipcc cra .scheduler_entry_pcc *)
    iInstr "Hcode".
    { instantiate (1 := (b_switcher ^+ 2)%a). switcher_addr_eq. }
    (* CLoad cra cra 0 *)
    iInstr "Hcode".
    iEval (rewrite Hload) in "Hcra".

    (* The other registers cleared *)
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ctp with "Hregs")
      as "[Hctp Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct2 with "Hregs")
      as "[Hct2 Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cs0 with "Hregs")
      as "[Hcs0 Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cs1 with "Hregs")
      as "[Hcs1 Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca4 with "Hregs")
      as "[Hca4 Hregs]"; first by rewrite !lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca5 with "Hregs")
      as "[Hca5 Hregs]"; first by rewrite !lookup_delete_ne.
    (* Mov ctp 0 *)
    iInstr "Hcode".
    destruct (decide (ctp = cnull)) as [Hn|_]; first done.
    (* Mov ct0 0 *)
    iInstr "Hcode".
    destruct (decide (ct0 = cnull)) as [Hn|_]; first done.
    (* Mov ct1 0 *)
    iInstr "Hcode".
    destruct (decide (ct1 = cnull)) as [Hn|_]; first done.
    (* Mov ct2 0 *)
    iInstr "Hcode".
    destruct (decide (ct2 = cnull)) as [Hn|_]; first done.
    (* Mov cs0 0 *)
    iInstr "Hcode".
    destruct (decide (cs0 = cnull)) as [Hn|_]; first done.
    (* Mov cs1 0 *)
    iInstr "Hcode".
    destruct (decide (cs1 = cnull)) as [Hn|_]; first done.
    (* Mov ca4 0 *)
    iInstr "Hcode".
    destruct (decide (ca4 = cnull)) as [Hn|_]; first done.
    (* Mov ca5 0 *)
    iInstr "Hcode".
    destruct (decide (ca5 = cnull)) as [Hn|_]; first done.
    switcher_change_pc_label ".Lexception_scheduler_cjalr".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca5 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca4 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcs1 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcs0 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct2 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct1 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct0 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hctp Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca3 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca2 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca1 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca0 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcgp Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcsp Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcra Hregs") as "Hregs".

    (* The jump, in the scheduler's world *)
    iEval (rewrite /scheduler_concrete) in "Hsched". iNamed "Hsched".
    iAssert (handover_res (ceriseg := ceriseG_of CtxSwitch))
      with "[Hcrit HU Hmepcc Hmcause Hmtval Hmpie]" as "Hho".
    { iApply handover_res_intro. rewrite /handover_at /volatile_csr_at. iFrame. }
    iPoseProof (codefrag_pers_thread_indep (UserThread t) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher".
    iApply (ctx_scheduler_jump_spec W cstk Ws Cs with
             "[$HPC $Hswitcher $Hentry $Htrap $Hresume $Hregs $HMIE $Hmtdc $Hlent $Hho $Hna
               $Hworld $Hcred $Hcstk $Hcont $Htop $Hcsp]").
    { done. }
    { apply set_eq. intros r. rewrite elem_of_dom.
      split; first (intros _; apply all_registers_s_correct).
      intros _.
      pose proof (all_registers_correct r) as Hr_all.
      rewrite /all_registers !elem_of_cons elem_of_nil in Hr_all.
      repeat (destruct Hr_all as [-> | Hr_all]); last done.
      all: repeat first [ rewrite lookup_insert_eq; by eexists | rewrite lookup_insert_ne; [|done] ].
      rewrite !lookup_delete_ne //. }
    { by rewrite lookup_insert_eq. }
    { by rewrite lookup_insert_ne // lookup_insert_eq. }
    { by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq. }
    { intros r Hr. rewrite /registers_scheduler_call !elem_of_cons elem_of_nil in Hr.
      repeat (destruct Hr as [-> | Hr]); last done.
      all: repeat first [ rewrite lookup_insert_eq; done | rewrite lookup_insert_ne; [|done] ]. }
    { done. }
    iIntros "!>" (r w Hr Hw).
    rewrite !elem_of_cons elem_of_nil in Hr.
    repeat (destruct Hr as [-> | Hr]); last done.
    all: repeat (rewrite lookup_insert_ne in Hw; [|done]); rewrite lookup_insert_eq in Hw;
      injection Hw as <-.
    - iApply "Hhandle".
    - iApply interp_int.
    - iApply interp_int.
    - iApply interp_int.
  Qed.

  (** The entry of the context-switch thread after an interrupt of user
      thread [t]: the spill of [t]'s registers into its save area, the
      dispatch, the park of [t], and the scheduler call. *)
  Lemma ctx_switch_entry_irq_spec (ts : list nat) (t : nat) (v : resume_vals) :
    ctx_switch_env C_sched w_pcc w_cgp w_csp ts -∗
    ctx_resume_specs C_sched w_csp -∗
    ctx_switch_entry_pre (CL := crit_link_full) (CR := crit_route_full) t ParkIrq v -∗
    safe[CtxSwitch].
  Proof.
    iIntros "Henv #Hresume Hpre".
    iNamed "Hpre".
    iDestruct "Hsched" as (P) "[HP_own HP]".
    iNamed "Henv".
    iDestruct "Hparked" as (c) "Hparked". iNamed "Hparked".
    pin_thread_instances CtxSwitch.

    (* [t] is one of the pool's *)
    iMod (pool_cur_in ts t _ ⊤ with "Hpool Hcur") as "[%Ht_in Hcur]"; first solve_ndisj.
    iDestruct (big_sepL_elem_of with "Hstatic") as "#Hstatic_t"; first exact Ht_in.
    pose proof (Hhomes t Ht_in) as Hhome_t.
    assert (t < swl_nthreads) as Ht by (by apply Hts).

    (* The scheduler's state *)
    iAssert (▷ scheduler_concrete C_sched w_csp)%I with "[HP HP_own]" as "Hconc".
    { iDestruct (saved_prop_agree with "Hsched HP_own") as "Heq". iNext. by iRewrite "Heq". }

    (* The posture of [t]: its save area, its mtdc token and its handover *)
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := crit_link_full (UserThread t)) (CR := crit_route_full (UserThread t))
               with "Hposture") as "[Hho Hpart]".
    iDestruct "Hho" as (wm wc vt b) "(%Hb & %Hwm & %Hwc & %Hvt & Hho)".
    cbn in Hb, Hwm, Hwc, Hvt. subst b wm wc vt.
    iDestruct (csl_full_posture_part t with "Hpart") as "[(%ws & _ & Hsave) Hlent_t]".
    iDestruct (handover_at_thread_indep (UserThread t) CtxSwitch with "Hho") as "Hho".
    (* The interrupted PC is a valid PC *)
    iEval (rewrite /handover_at /volatile_csr_at) in "Hho".
    iDestruct "Hho" as "(Hcrit & HU & Hmepcc & Hmcause & Hmtval & Hmpie)".
    iMod (mepcc_word_ok (ceriseg := ceriseG_of CtxSwitch) ⊤ with "Hmepcc")
      as "[Hmepcc %Hpc_ok]".
    iAssert (handover_at (ceriseg := ceriseG_of CtxSwitch) (lword_of_word v.(rv_pc).(lw))
               (lword_of_word (WInt c)) MTVAL_NONE InterruptEnabled)
      with "[Hcrit HU Hmepcc Hmcause Hmtval Hmpie]" as "Hho".
    { rewrite /handover_at /volatile_csr_at. iFrame. }
    (* [cnull] holds [lnull] *)
    assert (∀ r, is_Some (v.(rv_regs) !! r)) as Hsome.
    { intros r. apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
    destruct (Hsome cnull) as [wnull Hwnull].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cnull with "Hregs")
      as "[Hnull Hregs]"; first exact Hwnull.
    iMod (cnull_lnull (ceriseg := ceriseG_of CtxSwitch) ⊤ with "Hnull") as "[Hnull %Hnull]".
    subst wnull.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cnull with "[$Hnull $Hregs]")
      as "Hregs"; first exact Hwnull.
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread t))) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    assert (length ws = 21%nat) as Hlen21.
    { rewrite -Hlen. tstack_unfold. solve_addr. }
    clear Hlen.

    (* The spill *)
    iApply (ctx_spill_spec t v.(rv_regs) ws InterruptEnabled (lword_of_word v.(rv_pc).(lw)) c
              MTVAL_NONE with "[-]"); [done | done | done |].
    iFrame "HPC Hstatic_t Hregs Hmtdc Hsave HMIE Hho".
    iNext. iIntros (g_tstk) "(HPC & Hregs & Hmtdc & Hlent & Hsave & HMIE & Hho)".

    (* The dispatch *)
    iEval (rewrite /switcher_static) in "Hstatic_t". iNamed "Hstatic_t".
    iPoseProof (codefrag_pers_thread_indep (UserThread t) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher".
    assert (falls_to_scheduler_call c) as Hfalls.
    { pose proof scheduler_causes_dispatch as Hall. rewrite Forall_forall in Hall.
      apply Hall. rewrite /scheduler_causes elem_of_app. by left. }
    destruct (Hsome ca0) as [wca0 Hwca0].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct1 with "Hregs")
      as "[Hct1 Hregs]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca0 with "Hregs")
      as "[Hca0 Hregs]"; first by simplify_map_eq.
    iApply (ctx_dispatch_spec c wca0 Hfalls with "[-]").
    iFrame "HPC Hswitcher Hct1 Hca0".
    iNext. iIntros "(HPC & Hct1 & Hca0)".
    iDestruct (big_sepM_insert_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "[$Hca0 $Hregs]")
      as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct1 Hregs") as "Hregs".

    (* The park: [cur] becomes [None], and [Nact] closes *)
    iMod (ctx_park_irq_spec ts t v ws c Hnd Hlen21 Hmie Hc Hdom Hwnull Hpc_ok Hpc
           with "Hpool Hcur Hsave Hlent_t Hna Hclose") as "Hna".

    (* The scheduler call *)
    iDestruct (big_sepL_elem_of with "Hstatic") as "#Hstatic_t"; first exact Ht_in.
    iApply (ctx_scheduler_call_spec t g_tstk _ (lword_of_word v.(rv_pc).(lw)) InterruptEnabled c
              MTVAL_NONE Ht Hsched_in
             with "[$HPC $Hstatic_t $Hwords $Hentry $Htrap $Hresume $Hregs $HMIE $Hmtdc $Hlent
                    $Hho $Hna $Hconc]").
    - rewrite !dom_insert_L dom_delete_L !dom_insert_L Hdom.
      pose proof (all_registers_s_correct ct1). pose proof (all_registers_s_correct ca0).
      pose proof (all_registers_s_correct csp). pose proof (all_registers_s_correct ct0).
      set_solver.
    - by simplify_map_eq.
    - by simplify_map_eq.
    - by simplify_map_eq.
  Qed.

  (** The entry of the context-switch thread after a yield of user thread
      [t]: the spill, the dispatch, the park of [t] with its MIE and PC
      fragments, and the scheduler call. *)
  Lemma ctx_switch_entry_yield_spec (ts : list nat) (t : nat) (b : InterruptStatus) (p : LWord)
      (v : resume_vals) :
    ctx_switch_env C_sched w_pcc w_cgp w_csp ts -∗
    ctx_resume_specs C_sched w_csp -∗
    ctx_switch_entry_pre (CL := crit_link_full) (CR := crit_route_full) t (ParkYield b p) v -∗
    safe[CtxSwitch].
  Proof.
    iIntros "Henv #Hresume Hpre".
    iNamed "Hpre".
    iDestruct "Hsched" as (P) "[HP_own HP]".
    iNamed "Henv".
    iNamed "Hparked". destruct Hv as [Hpc Hmie].
    pin_thread_instances CtxSwitch.

    (* [t] is one of the pool's *)
    iMod (pool_cur_in ts t _ ⊤ with "Hpool Hcur") as "[%Ht_in Hcur]"; first solve_ndisj.
    iDestruct (big_sepL_elem_of with "Hstatic") as "#Hstatic_t"; first exact Ht_in.
    pose proof (Hhomes t Ht_in) as Hhome_t.
    assert (t < swl_nthreads) as Ht by (by apply Hts).

    (* The scheduler's state *)
    iAssert (▷ scheduler_concrete C_sched w_csp)%I with "[HP HP_own]" as "Hconc".
    { iDestruct (saved_prop_agree with "Hsched HP_own") as "Heq". iNext. by iRewrite "Heq". }

    (* The posture of [t]: its save area, its mtdc token and its handover *)
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := crit_link_full (UserThread t)) (CR := crit_route_full (UserThread t))
               with "Hposture") as "[Hho Hpart]".
    iDestruct "Hho" as (wm wc vt b') "(%Hb & %Hwm & %Hwc & _ & Hho)".
    cbn in Hb, Hwm, Hwc. subst b' wm wc.
    iDestruct (csl_full_posture_part t with "Hpart") as "[(%ws & _ & Hsave) Hlent_t]".
    iDestruct (handover_at_thread_indep (UserThread t) CtxSwitch with "Hho") as "Hho".
    (* [cnull] holds [lnull] *)
    assert (∀ r, is_Some (v.(rv_regs) !! r)) as Hsome.
    { intros r. apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
    destruct (Hsome cnull) as [wnull Hwnull].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cnull with "Hregs")
      as "[Hnull Hregs]"; first exact Hwnull.
    iMod (cnull_lnull (ceriseg := ceriseG_of CtxSwitch) ⊤ with "Hnull") as "[Hnull %Hnull]".
    subst wnull.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cnull with "[$Hnull $Hregs]")
      as "Hregs"; first exact Hwnull.
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread t))) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    assert (length ws = 21%nat) as Hlen21.
    { rewrite -Hlen. tstack_unfold. solve_addr. }
    clear Hlen.

    (* The spill *)
    iApply (ctx_spill_spec t v.(rv_regs) ws b p MCAUSE_ECALL_MACHINE vt with "[-]");
      [done | done | done |].
    iFrame "HPC Hstatic_t Hregs Hmtdc Hsave HMIE Hho".
    iNext. iIntros (g_tstk) "(HPC & Hregs & Hmtdc & Hlent & Hsave & HMIE & Hho)".

    (* The dispatch *)
    iEval (rewrite /switcher_static) in "Hstatic_t". iNamed "Hstatic_t".
    iPoseProof (codefrag_pers_thread_indep (UserThread t) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher".
    assert (falls_to_scheduler_call MCAUSE_ECALL_MACHINE) as Hfalls.
    { pose proof scheduler_causes_dispatch as Hall. rewrite Forall_forall in Hall.
      apply Hall. rewrite /scheduler_causes elem_of_app elem_of_cons. by right; left. }
    destruct (Hsome ca0) as [wca0 Hwca0].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct1 with "Hregs")
      as "[Hct1 Hregs]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca0 with "Hregs")
      as "[Hca0 Hregs]"; first by simplify_map_eq.
    iApply (ctx_dispatch_spec MCAUSE_ECALL_MACHINE wca0 Hfalls with "[-]").
    iFrame "HPC Hswitcher Hct1 Hca0".
    iNext. iIntros "(HPC & Hct1 & Hca0)".
    iDestruct (big_sepM_insert_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "[$Hca0 $Hregs]")
      as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct1 Hregs") as "Hregs".

    (* The park: [cur] becomes [None], and [Nact] closes *)
    iMod (ctx_park_yield_spec ts t b p v ws Hnd Hlen21 Hpc Hmie Hdom Hwnull
           with "Hpool Hcur Hsave Hlent_t HMIE_t HPC_t Hna Hclose") as "Hna".

    (* The scheduler call *)
    iDestruct (big_sepL_elem_of with "Hstatic") as "#Hstatic_t"; first exact Ht_in.
    iApply (ctx_scheduler_call_spec t g_tstk _ p b MCAUSE_ECALL_MACHINE vt Ht Hsched_in
             with "[$HPC $Hstatic_t $Hwords $Hentry $Htrap $Hresume $Hregs $HMIE $Hmtdc $Hlent
                    $Hho $Hna $Hconc]").
    - rewrite !dom_insert_L dom_delete_L !dom_insert_L Hdom.
      pose proof (all_registers_s_correct ct1). pose proof (all_registers_s_correct ca0).
      pose proof (all_registers_s_correct csp). pose proof (all_registers_s_correct ct0).
      set_solver.
    - by simplify_map_eq.
    - by simplify_map_eq.
    - by simplify_map_eq.
  Qed.

End ctx_scheduler_call.
