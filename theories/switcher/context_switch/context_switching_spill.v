From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import logrel switcher_preamble switcher_exception_states handoff.
From griotte Require Import switcher_link.
From griotte Require Import exception_dispatch exception_entry context_switch_layout_instance.
From griotte Require Import context_switching_support.

(** * The spill of the context-switch thread

    After the park of a user thread [t] at an interrupt or a yield, the
    context-switch thread runs the exception entry of the switcher, from the
    trap vector to the dispatch on the cause: it swaps [t]'s trusted stack
    in from mtdc, spills [t]'s registers, its stack pointer, MEPCC, mstatus
    and the cause in [t]'s register save area, and ends with mtdc at its own
    home, zero, with its mtdc token. The dispatch on a cause of the
    scheduler falls through to the scheduler call. No step faults. *)

Section ctx_spill.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** The registers [rs] of a register file, as a list, and back. *)
  #[local] Lemma regs_list_acc (th : Thread) (lreg : LReg) (rs : list RegName) :
    NoDup rs →
    (∀ r, r ∈ rs → is_Some (lreg !! r)) →
    regs[th] lreg ⊢
    ([∗ list] r;w ∈ rs;(λ r, default lnull (lreg !! r)) <$> rs, r ↦ᵣ[th] w) ∗
    (([∗ list] r;w ∈ rs;(λ r, default lnull (lreg !! r)) <$> rs, r ↦ᵣ[th] w) -∗
     regs[th] lreg).
  Proof.
    revert lreg. induction rs as [|r rs IH]; intros lreg Hnd Hin.
    { iIntros "Hregs". iSplitR; [done|]. by iIntros "_". }
    apply NoDup_cons in Hnd as [Hr_notin Hnd].
    destruct (Hin r ltac:(set_solver)) as [v Hv].
    iIntros "Hregs".
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[th] y)%I _ r with "Hregs") as "[Hr Hregs]";
      first exact Hv.
    iDestruct (IH (delete r lreg) Hnd with "Hregs") as "[Hl Hclose]".
    { intros r' Hr'. rewrite lookup_delete_ne; [|set_solver]. apply Hin. set_solver. }
    assert ((λ r', default lnull (delete r lreg !! r')) <$> rs =
            (λ r', default lnull (lreg !! r')) <$> rs) as Hws.
    { apply list_fmap_ext. intros i r' Hr'. apply list_elem_of_lookup_2 in Hr'.
      rewrite lookup_delete_ne; [done|set_solver]. }
    rewrite fmap_cons Hws Hv big_sepL2_cons /=. iFrame "Hr Hl".
    iIntros "[Hr Hl]". iSpecialize ("Hclose" with "Hl").
    iApply (big_sepM_delete (λ k y, k ↦ᵣ[th] y)%I _ r); first exact Hv. iFrame.
  Qed.

  (** [cspecialrw csp, mtdc, csp] at the context-switch thread, mtdc at user
      thread [t]'s home: [csp] receives [t]'s trusted stack; the token of
      the context-switch thread comes out if the written word is its home. *)
  Lemma ctx_entry_swap (t : nat) (wcsp : LWord) E Φ :
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    mtdc_home_at (th := UserThread t) = tstack_home t →
    PC ↦ₚ[CtxSwitch] switcher_label_pc "exception_entry_asm" ∗
    switcher_code_at CtxSwitch ∗
    csp ↦ᵣ[CtxSwitch] wcsp ∗
    mtdc ↦ₜ[CtxSwitch] mtdc_home_at (th := UserThread t) ∗
    unwedged ∗
    ▷ ( ∀ g_tstk : Locality,
        PC ↦ₚ[CtxSwitch] switcher_pc (switcher_label_offset "exception_entry_asm" + 1) ∗
        csp ↦ᵣ[CtxSwitch] lword_of_word (tstack_cap g_tstk t) ∗
        mtdc ↦ₜ[CtxSwitch] ExceptionScratch wcsp ∗
        (if decide (ExceptionScratch wcsp = mtdc_home_at (th := CtxSwitch))
         then mtdc_lent_at (th := CtxSwitch) else True) ∗
        unwedged -∗
        WP Exec @[CtxSwitch] E {{ Φ }} )
    ⊢ WP Exec @[CtxSwitch] E {{ Φ }}.
  Proof.
    iIntros (Hhome_ctx Hhome_t) "(HPC & #Hswitcher & Hcsp & Hmtdc & HU & Hpost)".
    pin_thread_instances CtxSwitch.
    switcher_open_label "exception_entry_asm" "Hswitcher" as "Hcode" a_entry Ha_entry.
    (* SpecialRW csp mtdc csp *)
    iInstrApply "Hcode"
      (wp_specialrw_swap_mtdc_ctx_away _ _ _ _ _ _ _ _ _ csp wcsp
         (mtdc_home_at (th := UserThread t)) (ExceptionScratch wcsp))
      with "[$HPC $Hcsp $Hmtdc $HU]" as (vm) "(%Hmatch & HPC & Hcsp & Hmtdc & HU & Hlent)".
    { by rewrite Hhome_t Hhome_ctx. }
    { apply mtdc_match_ExceptionScratch. }
    rewrite Hhome_t in Hmatch.
    destruct (mtdc_match_TStack_cap _ _ _ _ _ Hmatch) as [g_tstk ->].
    switcher_change_pc (switcher_label_offset "exception_entry_asm" + 1)%Z.
    iApply ("Hpost" $! g_tstk). iFrame.
  Qed.

  (** [mov ct1 0; cspecialrw ct1, mtdc, ct1] at the context-switch thread,
      the start of [.Lexception_exiting_threads_rejoin], from any mtdc word
      [wcsp]: [ct1] receives [wcsp], and mtdc the home of the context-switch
      thread, with its token. *)
  Lemma ctx_rejoin_swap (wcsp wct1 : LWord) E Φ :
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
    switcher_code_at CtxSwitch ∗
    ct1 ↦ᵣ[CtxSwitch] wct1 ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch wcsp ∗
    (if decide (ExceptionScratch wcsp = mtdc_home_at (th := CtxSwitch))
     then mtdc_lent_at (th := CtxSwitch) else True) ∗
    unwedged ∗
    ▷ ( PC ↦ₚ[CtxSwitch]
          switcher_pc (switcher_label_offset ".Lexception_exiting_threads_rejoin" + 2) ∗
        ct1 ↦ᵣ[CtxSwitch] wcsp ∗
        mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
        mtdc_lent_at (th := CtxSwitch) ∗
        unwedged -∗
        WP Exec @[CtxSwitch] E {{ Φ }} )
    ⊢ WP Exec @[CtxSwitch] E {{ Φ }}.
  Proof.
    iIntros (Hhome_ctx) "(HPC & #Hswitcher & Hct1 & Hmtdc & Hlent & HU & Hpost)".
    pin_thread_instances CtxSwitch.
    switcher_open_label ".Lexception_exiting_threads_rejoin" "Hswitcher" as "Hcode" a_rejoin
      Ha_rejoin.
    (* Mov ct1 0 *)
    iInstr "Hcode".
    (* SpecialRW ct1 mtdc ct1 *)
    iInstrApply "Hcode"
      (wp_specialrw_swap_mtdc_ctx_home _ _ _ _ _ _ _ _ _ ct1 _ (ExceptionScratch wcsp)
         (ExceptionScratch (lword_of_word (WInt 0))))
      with "[$HPC $Hct1 $Hmtdc $HU $Hlent]" as (vm) "(%Hmatch & HPC & Hct1 & Hmtdc & HU & Hlent)".
    { by rewrite Hhome_ctx. }
    { apply mtdc_match_ExceptionScratch. }
    cbn in Hmatch; subst vm.
    switcher_change_pc (switcher_label_offset ".Lexception_exiting_threads_rejoin" + 2)%Z.
    iApply "Hpost". iFrame.
  Qed.

  (** The rejoin of the context-switch thread, from any mtdc word [wcsp]
      (the interrupted stack pointer, or 0 on the exit path): mtdc ends at
      the context-switch thread's home, with its token; the save area of [t]
      receives [wcsp], MEPCC, mstatus, the cause, MSHWM and MSHWMB. *)
  Lemma ctx_rejoin_spec (t : nat) (g_tstk : Locality) (lreg : LReg) (ws : list LWord)
      (wcsp wm : LWord) (b : InterruptStatus) (cause vt mshwmb_v mshwm_v : Z) :
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    dom lreg = all_registers_s →
    lreg !! csp = Some (lword_of_word (tstack_cap g_tstk t)) →
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
    switcher_code_at CtxSwitch ∗
    regs[CtxSwitch] lreg ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch wcsp ∗
    (if decide (ExceptionScratch wcsp = mtdc_home_at (th := CtxSwitch))
     then mtdc_lent_at (th := CtxSwitch) else True) ∗
    save_area_holed (UserThread t) ws ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    mshwmb ↦ₜ[CtxSwitch] mshwmb_v ∗
    mshwm ↦ₜ[CtxSwitch] mshwm_v ∗
    handover_at (ceriseg := ceriseG_of CtxSwitch) wm (lword_of_word (WInt cause)) vt b ∗
    ▷ ( PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_might_handle" ∗
        regs[CtxSwitch] (<[ct0 := wm]> (<[ct1 := lword_of_word (WInt cause)]> lreg)) ∗
        mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
        mtdc_lent_at (th := CtxSwitch) ∗
        save_area_holed (UserThread t) (rejoin_spill ws wcsp wm b cause mshwmb_v mshwm_v) ∗
        MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
        mshwmb ↦ₜ[CtxSwitch] mshwmb_v ∗
        mshwm ↦ₜ[CtxSwitch] mshwm_v ∗
        handover_at (ceriseg := ceriseG_of CtxSwitch) wm (lword_of_word (WInt cause)) vt b -∗
        safe[CtxSwitch] )
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hhome_ctx Hdom Hcsp)
      "(HPC & #Hswitcher & Hregs & Hmtdc & Hlent & Hsave & HMIE & Hhwmb & Hhwm & Hho & Hpost)".
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread t))) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    assert (length ws = 21%nat) as Hlen21.
    { rewrite -Hlen. tstack_unfold. solve_addr. }
    clear Hlen.
    destruct ws as
      [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10
      [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    clear Hlen21.
    iEval (rewrite save_area_holed_explicit) in "Hsave".
    iDestruct "Hsave" as "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
      & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs17 & Hs18 & Hs19 & Hs20)".
    iEval (rewrite /handover_at /volatile_csr_at) in "Hho".
    iDestruct "Hho" as "(Hcrit & HU & Hmepcc & Hmcause & Hmtval & Hmpie)".
    assert (∀ r, is_Some (lreg !! r)) as Hreg_some.
    { intros r. apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
    destruct (Hreg_some ct0) as [wct0 Hwct0].
    destruct (Hreg_some ct1) as [wct1 Hwct1].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct0 with "Hregs")
      as "[Hct0 Hregs]"; first exact Hwct0.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct1 with "Hregs")
      as "[Hct1 Hregs]"; first by rewrite lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ csp with "Hregs")
      as "[Hcsp Hregs]"; first by rewrite !lookup_delete_ne.

    (* The swap of mtdc *)
    iApply (ctx_rejoin_swap wcsp wct1
             with "[$HPC $Hswitcher $Hct1 $Hmtdc $Hlent $HU Hpost Hregs Hcsp Hct0 Hs0 Hs1 Hs2 Hs3
                    Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15 Hs17 Hs18 Hs19 Hs20
                    HMIE Hhwmb Hhwm Hcrit Hmepcc Hmcause Hmtval Hmpie]"); first done.
    iNext. iIntros "(HPC & Hct1 & Hmtdc & Hlent & HU)".

    (* The saves, at user thread [t]'s register save area *)
    iPoseProof (codefrag_pers_thread_indep CtxSwitch (UserThread t) with "Hswitcher")
      as "#Hswitcher_t".
    iAssert (hwm_regs (ceriseg := ceriseG_of CtxSwitch) mshwmb_v mshwm_v)%I with "[$Hhwmb $Hhwm]" as "Hhwm".
    iApply (exception_rejoin_save_spec (th := CtxSwitch) (UserThread t) g_tstk b cause wm wcsp
              _ _ _ _ _ _ _ mshwmb_v mshwm_v
             with "[$HPC $Hcsp $Hct0 $Hct1 $Hs0 $Hs2 $Hs17 $Hs18 $Hs19 $Hs20 $Hhwm $HMIE $Hmpie
                    $Hmepcc $Hmcause $Hswitcher_t Hpost Hregs Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10
                    Hs11 Hs12 Hs13 Hs14 Hs15 Hcrit Hmtval Hmtdc Hlent HU]").
    iNext. iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hs0 & Hs2 & Hs17 & Hs18 & Hs19 & Hs20 & Hhwm
      & HMIE & Hmpie & Hmepcc & Hmcause)".
    iDestruct "Hhwm" as "[Hhwmb Hhwm]".
    iApply "Hpost". iFrame "HPC Hmtdc Hlent HMIE Hhwmb Hhwm".
    iSplitL "Hregs Hcsp Hct0 Hct1".
    { iApply (big_sepM_insert_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I). iFrame "Hct0".
      rewrite delete_insert_ne //.
      iApply (big_sepM_insert_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I). iFrame "Hct1".
      iApply (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ csp);
        first by rewrite !lookup_delete_ne.
      iFrame. }
    iSplitR "Hcrit HU Hmepcc Hmcause Hmtval Hmpie".
    { rewrite /rejoin_spill /= save_area_holed_explicit. iFrame. }
    rewrite /handover_at /volatile_csr_at. iFrame.
  Qed.

  (** The spill of the context-switch thread after the park of user thread
      [t] at an interrupt or a yield, from the trap vector to the dispatch,
      without a fault: [t]'s registers [lreg], MEPCC [wm], mstatus (MIE
      disabled, MPIE [b]), the cause, MSHWM [mshwm_v] and MSHWMB [mshwmb_v] go to [t]'s
      save area; mtdc ends at the context-switch thread's home, with its
      token. *)
  Lemma ctx_spill_spec (t : nat) (lreg : LReg) (ws : list LWord) (b : InterruptStatus)
      (wm : LWord) (cause vt mshwmb_v mshwm_v : Z) :
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    mtdc_home_at (th := UserThread t) = tstack_home t →
    dom lreg = all_registers_s →
    PC ↦ₚ[CtxSwitch] lword_of_word mtcc_vec ∗
    switcher_static (th := UserThread t) ∗
    regs[CtxSwitch] lreg ∗
    mtdc ↦ₜ[CtxSwitch] mtdc_home_at (th := UserThread t) ∗
    save_area_holed (UserThread t) ws ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    mshwmb ↦ₜ[CtxSwitch] mshwmb_v ∗
    mshwm ↦ₜ[CtxSwitch] mshwm_v ∗
    handover_at (ceriseg := ceriseG_of CtxSwitch) wm (lword_of_word (WInt cause)) vt b ∗
    ▷ ( ∀ g_tstk : Locality,
        PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_might_handle" ∗
        regs[CtxSwitch] (<[csp := lword_of_word (tstack_cap g_tstk t)]>
                          (<[ct0 := wm]> (<[ct1 := lword_of_word (WInt cause)]> lreg))) ∗
        mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
        mtdc_lent_at (th := CtxSwitch) ∗
        save_area_holed (UserThread t) (ctx_spill ws lreg wm b cause mshwmb_v mshwm_v) ∗
        MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
        mshwmb ↦ₜ[CtxSwitch] mshwmb_v ∗
        mshwm ↦ₜ[CtxSwitch] mshwm_v ∗
        handover_at (ceriseg := ceriseG_of CtxSwitch) wm (lword_of_word (WInt cause)) vt b -∗
        safe[CtxSwitch] )
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hhome_ctx Hhome_t Hdom)
      "(HPC & #Hstatic & Hregs & Hmtdc & Hsave & HMIE & Hhwmb & Hhwm & Hho & Hpost)".
    iEval (rewrite /switcher_static) in "Hstatic". iNamed "Hstatic".
    iPoseProof (codefrag_pers_thread_indep (UserThread t) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher".
    rewrite Hmtcc_vec.
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread t))) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    assert (length ws = 21%nat) as Hlen21.
    { rewrite -Hlen. tstack_unfold. solve_addr. }
    clear Hlen.
    destruct ws as
      [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10
      [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    clear Hlen21.
    iEval (rewrite save_area_holed_explicit) in "Hsave".
    iDestruct "Hsave" as "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
      & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs17 & Hs18 & Hs19 & Hs20)".
    iEval (rewrite /handover_at) in "Hho".
    iDestruct "Hho" as "(Hcrit & HU & Hvol)".
    assert (∀ r, is_Some (lreg !! r)) as Hreg_some.
    { intros r. apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
    destruct (Hreg_some csp) as [wcsp Hwcsp].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ csp with "Hregs")
      as "[Hcsp Hregs]"; first exact Hwcsp.
    assert (csp ∉ exception_spill_regs) as Hcsp_notin.
    { by apply (bool_decide_unpack _). }
    iDestruct (regs_list_acc CtxSwitch (delete csp lreg) exception_spill_regs with "Hregs")
      as "[Hl Hclose]".
    { by apply (bool_decide_unpack _). }
    { intros r Hr. rewrite lookup_delete_ne; [apply Hreg_some | intros Heq; subst r; done]. }

    (* The swap of the trusted stack in *)
    iApply (ctx_entry_swap t wcsp
             with "[$HPC $Hswitcher $Hcsp $Hmtdc $HU Hpost Hl Hclose Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6
                    Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15 Hs17 Hs18 Hs19 Hs20 HMIE Hhwmb Hhwm
                    Hcrit Hvol]"); [done | done |].
    iNext. iIntros (g_tstk) "(HPC & Hcsp & Hmtdc & Hlent & HU)".

    (* The spill of the registers but the stack pointer *)
    iApply (exception_entry_spill_spec (th := CtxSwitch) (UserThread t) g_tstk _
              [w1; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15]
             with "[$HPC $Hcsp $Hl $Hswitcher_code Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12
                    Hs13 Hs14 Hs15 Hpost Hclose Hs0 Hs2 Hs17 Hs18 Hs19 Hs20 HMIE Hhwmb Hhwm Hcrit Hvol
                    Hmtdc Hlent HU]").
    iSplitL "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15".
    { cbn [big_sepL2 exception_spill_regs]. iFrame. }
    iNext. iIntros "(HPC & Hcsp & Hl & Hcells)".
    iSpecialize ("Hclose" with "Hl").
    iAssert (regs[CtxSwitch] (<[csp := lword_of_word (tstack_cap g_tstk t)]> lreg))%I
      with "[Hclose Hcsp]" as "Hregs".
    { rewrite -insert_delete_eq.
      iApply (big_sepM_insert_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I).
      rewrite delete_delete_eq. iFrame. }
    iEval (cbn [big_sepL2 exception_spill_regs fmap list_fmap]) in "Hcells".
    iDestruct "Hcells" as "(Hs1 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
      & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & _)".
    iPoseProof (save_area_holed_explicit (UserThread t) w0 _ w2 _ _ _ _ _ _ _ _ _ _ _ _ _
                  w16 w17 w18 w19 w20) as "[_ Hfold]".
    iDestruct ("Hfold" with "[$Hs0 $Hs1 $Hs2 $Hs3 $Hs4 $Hs5 $Hs6 $Hs7 $Hs8 $Hs9 $Hs10 $Hs11 $Hs12
                $Hs13 $Hs14 $Hs15 $Hs17 $Hs18 $Hs19 $Hs20]") as "Hsave".
    iClear "Hfold".

    (* The rejoin *)
    iAssert (handover_at (ceriseg := ceriseG_of CtxSwitch) wm (lword_of_word (WInt cause)) vt b)
      with "[Hcrit HU Hvol]" as "Hho".
    { rewrite /handover_at. iFrame. }
    iApply (ctx_rejoin_spec t g_tstk (<[csp := lword_of_word (tstack_cap g_tstk t)]> lreg) _ wcsp
              wm b cause vt mshwmb_v mshwm_v
             with "[$HPC $Hswitcher $Hregs $Hmtdc $Hlent $Hsave $HMIE $Hhwmb $Hhwm $Hho Hpost]").
    { done. }
    { rewrite dom_insert_L Hdom. pose proof (all_registers_s_correct csp). set_solver. }
    { by rewrite lookup_insert_eq. }
    iNext. iIntros "(HPC & Hregs & Hmtdc & Hlent & Hsave & HMIE & Hhwmb & Hhwm & Hho)".
    iApply ("Hpost" $! g_tstk). iFrame "HPC Hmtdc Hlent HMIE Hhwmb Hhwm Hho".
    iSplitL "Hregs".
    { rewrite (insert_insert_ne _ csp ct0) // (insert_insert_ne _ csp ct1) //. }
    iClear "Hswitcher_code Hswitcher_key Hswitcher_sealing Htstacks_key Hexit_prop Hswitcher".
    rewrite /ctx_spill /exception_spill /spill_words /rejoin_spill /= !lookup_delete_ne // Hwcsp /=.
    iExact "Hsave".
  Qed.

  (** The dispatch on a cause of the scheduler: no test jumps, the code
      falls to the scheduler call. *)
  Lemma ctx_dispatch_spec (cause : Z) (wca0 : LWord) :
    falls_to_scheduler_call cause →
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_might_handle" ∗
    switcher_code_at CtxSwitch ∗
    ct1 ↦ᵣ[CtxSwitch] WInt cause ∗
    ca0 ↦ᵣ[CtxSwitch] wca0 ∗
    ▷ ( PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_scheduler_call" ∗
        ct1 ↦ᵣ[CtxSwitch] WInt cause ∗
        ca0 ↦ᵣ[CtxSwitch] WInt 8 -∗
        safe[CtxSwitch] )
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hfalls) "(HPC & #Hswitcher & Hct1 & Hca0 & Hpost)".
    pin_thread_instances CtxSwitch.
    switcher_open_label ".Lexception_exiting_threads_rejoin" "Hswitcher" as "Hcode" a_rejoin
      Ha_rejoin.
    switcher_hide "Hpost" as hpost.
    switcher_pc_in_block ".Lexception_exiting_threads_rejoin" ".Lexception_might_handle" "HPC".
    destruct (Hfalls (inl 0%Z) ca0 ct1 (inl 0%Z) ct1 ca0) as [Hjeq Hjlt].
    (* Mov ca0 MCAUSE_CHERI *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
    (* Jeq .Lhandle_error ca0 ct1 *)
    iInstr "Hcode".
    (* Mov ca0 8 *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
    (* Jlt .Lhandle_error ct1 ca0 *)
    iInstr "Hcode".
    switcher_change_pc_label ".Lexception_scheduler_call".
    subst hpost. iApply "Hpost". iFrame.
  Qed.

End ctx_spill.
