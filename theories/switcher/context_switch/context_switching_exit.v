From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import logrel switcher_preamble exception_dispatch virtualise.
From griotte Require Import context_switch_layout_instance clear_hazard_slots_spec.
From griotte Require Import context_switching_support context_switching_spill.
From griotte Require Import context_switching_hyps context_switching_park.
From griotte Require Import context_switching_scheduler_call context_switching_exit_tail.

(** * The exit path of the context-switch thread

    After the exit of user thread [t], the context-switch thread starts at
    the exit block, at the PC that [t]'s exit part names. The block writes
    mtval, sets MEPCC to the PCC of an exited thread, swaps [t]'s trusted
    stack in from mtdc, stores 0 in the words x1–x15 of [t]'s save area,
    clears [t]'s hazard slots and joins the exception entry at the rejoin.
    Then [t] is parked: its slot becomes Suspended, with the save area of
    an exited thread and resume values at the PCC of an exited thread, and
    the context-switch thread calls the scheduler. *)

Section ctx_exit.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    (C_sched : CmptName) (w_pcc w_cgp w_csp : LWord).

  (** * The exit PC *)

  #[local] Instance exit_concrete_timeless (t : nat) :
    Timeless (exit_concrete (th := UserThread t)).
  Proof. rewrite /exit_concrete /switcher_hazard. apply _. Qed.

  (** The exit part of a user thread of the switcher: its exit PC and its
      hazard part, from the saved proposition of [switcher_static]. *)
  Lemma exit_part_concrete (t : nat) :
    switcher_static (th := UserThread t) -∗
    exit_part (UserThread t) -∗
    ◇ exit_concrete (th := UserThread t).
  Proof.
    iIntros "#Hstatic [%P [Hown HP] ]".
    iDestruct (switcher_static_exit with "Hstatic") as "Hexit".
    iDestruct (saved_prop_agree with "Hexit Hown") as "Heq".
    iAssert (▷ exit_concrete (th := UserThread t))%I with "[HP Heq]" as "Hc".
    { iNext. by iRewrite "Heq". }
    by iMod "Hc".
  Qed.

  (** The exit PC: the context-switch thread starts at the exit block. *)
  Lemma ctx_exit_pc (ts : list nat) (t : nat) (v : resume_vals) E :
    ↑Npool ⊆ E →
    inv Npool (Pool ts) -∗
    switcher_static (th := UserThread t) -∗
    cur_frag (Some (UserThread t, Saving ParkExit v)) -∗
    exit_part (UserThread t) ={E}=∗
    ⌜v.(rv_pc) = lword_of_word (Cap XSRW_ Local b_switcher e_switcher a_exit)⌝ ∗
    cur_frag (Some (UserThread t, Saving ParkExit v)) ∗
    PC ↦ₚ[u t] v.(rv_pc) ∗
    switcher_hazard (th := UserThread t).
  Proof.
    iIntros (Hmask) "#Hpool #Hstatic Hcur Hexit".
    iMod (exit_part_concrete with "Hstatic Hexit") as "[HPC Hhazard]".
    iMod (pool_saving_pc with "Hpool Hcur HPC") as "(%Hpc & Hcur & HPC)"; first done.
    rewrite Hpc. by iFrame.
  Qed.

  (** * The save area of an exited thread *)

  (** A save area after the exit block's 15 null stores: the words of
      x1–x15 are 0. *)
  Definition exit_zero (ws : list LWord) : list LWord :=
    imap (λ (k : nat) (w : LWord),
            if decide (1 ≤ k ∧ k ≤ 15)%nat then lword_of_word (WInt 0) else w) ws.

  (** The save area of an exited thread after the rejoin: the stack
      pointer word holds mtdc's 0, MEPCC the exited thread's PCC, mstatus
      MPIE [b], the cause the exit cause. *)
  Definition exit_area (ws : list LWord) (b : InterruptStatus) : list LWord :=
    rejoin_spill (exit_zero ws) (lword_of_word (WInt 0)) (lword_of_word exited_thread_pcc) b
      MCAUSE_THREAD_EXIT.

  (** The registers of an exited thread: all 0. *)
  Definition exited_regs : LReg := list_to_map ((λ r, (r, lnull)) <$> all_registers).

  Lemma exited_regs_dom : dom exited_regs = all_registers_s.
  Proof.
    rewrite /exited_regs dom_list_to_map_L -list_fmap_compose /all_registers_s.
    f_equal.
  Qed.

  (** The values an exited thread resumes with. *)
  Definition exited_vals (b : InterruptStatus) : resume_vals :=
    ResumeVals exited_regs (lword_of_word exited_thread_pcc) b.

  Lemma exit_area_resume_ok (ws : list LWord) (b : InterruptStatus) :
    length ws = 21%nat →
    resume_ok_full (exit_area ws b) (exited_vals b) ∧ saved_mie_ok (exit_area ws b).
  Proof.
    intros Hlen.
    destruct ws as
      [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10
      [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    rewrite /resume_ok_full /exited_vals. cbn [rv_regs rv_mie rv_pc].
    split_and!.
    - (* Every register word of the area is 0. *)
      rewrite /exited_regs /resume_regs_of. f_equal.
    - rewrite /save_area_word /exit_area /rejoin_spill /= mpie_of_mstatus_enc //.
    - split; last done.
      rewrite /resume_pc_word /save_area_word /exit_area /rejoin_spill /=.
      by rewrite exited_thread_pcc_legal.
    - intros w Hw. rewrite /exit_area /rejoin_spill /= in Hw. simplify_eq.
      by rewrite /= mie_of_mstatus_enc.
  Qed.

  (** The words x1–x15 of a save area out of it; written back as 0, the
      save area is the one after the exit block. *)
  Lemma save_area_holed_exit_cells (t : nat) (ws : list LWord) :
    length ws = 21%nat →
    save_area_holed (UserThread t) ws -∗
    ([∗ list] k ∈ seq 1 15,
       (@b_trusted_stack (tlayout_of (UserThread t)) ^+ Z.of_nat k)%a ↦ₐ
         save_area_word ws (Z.of_nat k)) ∗
    (([∗ list] k ∈ seq 1 15,
        (@b_trusted_stack (tlayout_of (UserThread t)) ^+ Z.of_nat k)%a ↦ₐ lword_of_word (WInt 0)) -∗
     save_area_holed (UserThread t) (exit_zero ws)).
  Proof.
    intros Hlen.
    destruct ws as
      [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10
      [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    rewrite /exit_zero /save_area_word /= !save_area_holed_explicit.
    iIntros "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
      & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs17 & Hs18 & Hs19 & Hs20)".
    iFrame "Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15".
    iIntros "($ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & _)".
    iFrame.
  Qed.

  (** * The exit block *)

  (** From [.Lcommon_thread_exit_clear] to the rejoin, at the context-switch
      thread: mtdc goes from [t]'s home to the context-switch thread's,
      which releases its token; the words x1–x15 of [t]'s save area become 0
      and [t]'s hazard slots are cleared. *)
  Lemma ctx_exit_clear_spec (t : nat) (ws : list LWord) (wcsp wcs0 : LWord) :
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    mtdc_home_at (th := UserThread t) = tstack_home t →
    length ws = 21%nat →
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lcommon_thread_exit_clear" ∗
    switcher_code_at CtxSwitch ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    unwedged ∗
    csp ↦ᵣ[CtxSwitch] wcsp ∗
    cs0 ↦ᵣ[CtxSwitch] wcs0 ∗
    mtdc ↦ₜ[CtxSwitch] mtdc_home_at (th := UserThread t) ∗
    save_area_holed (UserThread t) ws ∗
    switcher_hazard (th := UserThread t) ∗
    ▷ ( ∀ g_tstk : Locality,
        PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
        MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
        unwedged ∗
        csp ↦ᵣ[CtxSwitch] lword_of_word (tstack_cap g_tstk t) ∗
        cs0 ↦ᵣ[CtxSwitch] lword_of_word (hazard_slots_cap (th := UserThread t)) ∗
        mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
        mtdc_lent_at (th := CtxSwitch) ∗
        save_area_holed (UserThread t) (exit_zero ws) -∗
        safe[CtxSwitch] )
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hhome_ctx Hhome_t Hlen)
      "(HPC & #Hswitcher & HMIE & HU & Hcsp & Hcs0 & Hmtdc & Hsave & Hhazard & Hpost)".
    pin_thread_instances CtxSwitch.
    iDestruct (save_area_holed_exit_cells with "Hsave") as "[Hcells Hsave]"; first done.
    iEval (cbn [seq big_opL]) in "Hcells".
    iDestruct "Hcells" as "(Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
      & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & _)".
    switcher_open_label ".Lcommon_thread_exit_clear" "Hswitcher" as "Hcode" a_clear Ha_clear.
    switcher_hide "Hpost" as hpost.
    (* Mov csp 0. *)
    iInstr "Hcode".
    destruct (decide (csp = cnull)) as [Hcsp_null | _]; first done.
    (* SpecialRW csp mtdc csp. *)
    iInstrApply "Hcode"
      (wp_specialrw_swap_mtdc_ctx_away _ _ _ _ _ _ _ _ _ csp (lword_of_word (WInt 0))
         (mtdc_home_at (th := UserThread t)) (ExceptionScratch (lword_of_word (WInt 0))))
      with "[$HPC $Hcsp $Hmtdc $HU]" as (vm) "(%Hmatch & HPC & Hcsp & Hmtdc & HU & Hlent)".
    { by rewrite Hhome_t Hhome_ctx. }
    { apply mtdc_match_ExceptionScratch. }
    rewrite Hhome_t in Hmatch.
    destruct (mtdc_match_TStack_cap _ _ _ _ _ Hmatch) as [g_tstk ->].
    rewrite decide_True; last by rewrite Hhome_ctx.

    (* The null stores, at [t]'s register save area *)
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread t))) as [n Hfit].
    pose proof (trusted_stack_disjoint_from_shadow (tlayout := tlayout_of (UserThread t)))
      as Hts_shadow.
    assert (∀ k : nat, (k ≤ 21)%nat →
                     (@b_trusted_stack (tlayout_of (UserThread t)) + Z.of_nat k)%a =
                       Some (@b_trusted_stack (tlayout_of (UserThread t)) ^+ Z.of_nat k)) as Hts_k
      by (intros; tstack_unfold; solve_addr).
    assert (∀ k : Z, (0 <= k <= 21)%Z →
                     is_shadow_address (@b_trusted_stack (tlayout_of (UserThread t)) ^+ k) = false)
      as Hts_k_shadow.
    { intros k Hk. tstk_not_shadow Hts_shadow. }
    assert (∀ k : Z, (0 <= k <= 21)%Z →
                     withinBounds (@b_trusted_stack (tlayout_of (UserThread t)))
                       (@e_trusted_stack (tlayout_of (UserThread t)))
                       (@b_trusted_stack (tlayout_of (UserThread t)) ^+ k) = true)
      as Hts_k_bounds.
    { intros k Hk. rewrite /withinBounds. tstack_unfold; solve_addr. }
    pose proof (Hts_k 1 ltac:(lia)) as Hts_1.
    (* Store csp 0 TrustedStack_offset_cra. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 2 ltac:(lia)) as Hts_2.
    (* Store csp 0 TrustedStack_offset_csp. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 3 ltac:(lia)) as Hts_3.
    (* Store csp 0 TrustedStack_offset_cgp. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 4 ltac:(lia)) as Hts_4.
    (* Store csp 0 TrustedStack_offset_ctp. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 5 ltac:(lia)) as Hts_5.
    (* Store csp 0 TrustedStack_offset_ct0. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 6 ltac:(lia)) as Hts_6.
    (* Store csp 0 TrustedStack_offset_ct1. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 7 ltac:(lia)) as Hts_7.
    (* Store csp 0 TrustedStack_offset_ct2. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 8 ltac:(lia)) as Hts_8.
    (* Store csp 0 TrustedStack_offset_cs0. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 9 ltac:(lia)) as Hts_9.
    (* Store csp 0 TrustedStack_offset_cs1. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 10 ltac:(lia)) as Hts_10.
    (* Store csp 0 TrustedStack_offset_ca0. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 11 ltac:(lia)) as Hts_11.
    (* Store csp 0 TrustedStack_offset_ca1. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 12 ltac:(lia)) as Hts_12.
    (* Store csp 0 TrustedStack_offset_ca2. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 13 ltac:(lia)) as Hts_13.
    (* Store csp 0 TrustedStack_offset_ca3. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 14 ltac:(lia)) as Hts_14.
    (* Store csp 0 TrustedStack_offset_ca4. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    pose proof (Hts_k 15 ltac:(lia)) as Hts_15.
    (* Store csp 0 TrustedStack_offset_ca5. *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    clear Hts_1 Hts_2 Hts_3 Hts_4 Hts_5 Hts_6 Hts_7 Hts_8 Hts_9 Hts_10 Hts_11 Hts_12 Hts_13 Hts_14
      Hts_15.
    iSpecialize ("Hsave" with "[Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15]").
    { cbn [seq big_opL]. iFrame. }

    (* clear_hazard_slots_asm csp cs0 *)
    iDestruct "Hhazard" as "[Hhazard_cell [%ws_hz Hslots] ]".
    iDestruct (codefrag_pers_clear_hazard_slots _ _ 17 csp cs0 with "Hcode") as "Hcode_hz";
      [done | cbn; lia |].
    iEval (rewrite /tstack_hazard_cell /hazard_slots_cap) in "Hhazard_cell".
    iEval (rewrite (_ : a_clear ^+ 17%nat = a_clear ^+ 17); last done) in "Hcode_hz".
    pose proof (hazard_slots_size (tlayout := tlayout_of (UserThread t))) as Hhz_size.
    pose proof (hazard_slots_disjoint_from_shadow (tlayout := tlayout_of (UserThread t)))
      as Hhz_shadow.
    pose proof (hazard_slots_not_heap (tlayout := tlayout_of (UserThread t))) as Hhz_heap.
    iApply (clear_hazard_slots_spec (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch)
              (CL := crit_link_full CtxSwitch)
             with "[- $HPC $Hcsp $Hcs0 $Hhazard_cell $Hslots $Hcode_hz]"); try done.
    { rewrite clear_hazard_slots_instrs_length; solve_addr. }
    { rewrite /TrustedStack_offset_hazardPointers; tstack_unfold; solve_addr. }
    { rewrite /withinBounds /TrustedStack_offset_hazardPointers; tstack_unfold; solve_addr. }
    { rewrite /TrustedStack_offset_hazardPointers. tstk_not_shadow Hts_shadow. }
    iNext; iIntros "(HPC & Hcsp & Hcs0 & Hhazard_cell & Hslots)".
    rewrite clear_hazard_slots_instrs_length.
    rewrite (_ : (a_clear ^+ 17) ^+ 3%nat = a_clear ^+ 20); last solve_addr.
    (* Jmp .Lexception_exiting_threads_rejoin *)
    iInstr "Hcode".
    { transitivity
        (Some (a_switcher_call ^+ switcher_label_offset ".Lexception_exiting_threads_rejoin")%a);
        [| reflexivity].
      subst a_clear. pose proof switcher_size as Hsize. pose proof switcher_call_entry_point as Hcall.
      clear - Hsize Hcall. offsets_compute. solve_addr. }
    (* The cleared hazard part is dropped. *)
    subst hpost. iApply ("Hpost" $! g_tstk). iFrame.
  Qed.

  (** The exit block at the context-switch thread, from the mtval write to
      the rejoin: mtval, the setter, the swap with mtdc, the 15 null stores,
      the hazard clear and the jump. *)
  Lemma ctx_exit_block_spec (t : nat) (lreg : LReg) (ws : list LWord) (wm : LWord)
      (b : InterruptStatus) (vt : Z) :
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    mtdc_home_at (th := UserThread t) = tstack_home t →
    dom lreg = all_registers_s →
    PC ↦ₚ[CtxSwitch] lword_of_word (Cap XSRW_ Local b_switcher e_switcher a_exit) ∗
    switcher_static (th := UserThread t) ∗
    regs[CtxSwitch] lreg ∗
    mtdc ↦ₜ[CtxSwitch] mtdc_home_at (th := UserThread t) ∗
    save_area_holed (UserThread t) ws ∗
    switcher_hazard (th := UserThread t) ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    handover_at (ceriseg := ceriseG_of CtxSwitch) wm (lword_of_word (WInt MCAUSE_THREAD_EXIT)) vt b ∗
    ▷ ( ∀ (g_tstk : Locality) (lreg' : LReg),
        ⌜dom lreg' = all_registers_s⌝ ∗
        ⌜lreg' !! csp = Some (lword_of_word (tstack_cap g_tstk t))⌝ ∗
        PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
        regs[CtxSwitch] lreg' ∗
        mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
        mtdc_lent_at (th := CtxSwitch) ∗
        save_area_holed (UserThread t) (exit_zero ws) ∗
        MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
        handover_at (ceriseg := ceriseG_of CtxSwitch) (lword_of_word exited_thread_pcc)
          (lword_of_word (WInt MCAUSE_THREAD_EXIT)) MCAUSE_THREAD_EXIT b -∗
        safe[CtxSwitch] )
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros (Hhome_ctx Hhome_t Hdom)
      "(HPC & #Hstatic & Hregs & Hmtdc & Hsave & Hhazard & HMIE & Hho & Hpost)".
    iEval (rewrite /switcher_static) in "Hstatic". iNamed "Hstatic".
    iPoseProof (codefrag_pers_thread_indep (UserThread t) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher".
    iPoseProof (codefrag_pers_thread_indep (UserThread t) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher_mtval".
    pin_thread_instances CtxSwitch.
    iEval (rewrite /handover_at /volatile_csr_at) in "Hho".
    iDestruct "Hho" as "(Hcrit & HU & Hmepcc & Hmcause & Hmtval & Hmpie)".
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread t))) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    assert (length ws = 21%nat) as Hlen21.
    { rewrite -Hlen. tstack_unfold. solve_addr. }
    clear Hlen.
    assert (∀ r, is_Some (lreg !! r)) as Hreg_some.
    { intros r. apply elem_of_dom. rewrite Hdom. apply all_registers_s_correct. }
    destruct (Hreg_some csp) as [wcsp Hwcsp].
    destruct (Hreg_some ca0) as [wca0 Hwca0].
    destruct (Hreg_some cs0) as [wcs0 Hwcs0].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ csp with "Hregs")
      as "[Hcsp Hregs]"; first exact Hwcsp.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca0 with "Hregs")
      as "[Hca0 Hregs]"; first by rewrite lookup_delete_ne.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ cs0 with "Hregs")
      as "[Hcs0 Hregs]"; first by rewrite !lookup_delete_ne.

    (* The mtval write *)
    switcher_open_label ".Lcommon_thread_exit_mtval" "Hswitcher_mtval" as "Hcode" a_mtval Ha_mtval.
    assert (a_exit = a_mtval) as Hexit.
    { pose proof a_exit_label as Hlabel. subst a_mtval. clear - Hlabel.
      offsets_compute. solve_addr. }
    iEval (rewrite Hexit) in "HPC".
    (* SpecialRW cnull mtval (inl MCAUSE_THREAD_EXIT) *)
    iInstr "Hcode".
    iEval (rewrite legalise_mtval_exit) in "Hmtval".

    (* The setter *)
    assert (a_mtval ^+ 1 = a_exit_set)%a as Hset.
    { pose proof a_exit_set_label as Hlabel. subst a_mtval. clear - Hlabel.
      offsets_compute. solve_addr. }
    iEval (rewrite Hset) in "HPC".
    iDestruct (exited_set_spec_holds with "Hswitcher") as "Hset".
    iApply ("Hset" $! wcsp wca0 wm with "HPC Hswitcher HMIE Hcsp Hca0 Hmepcc").
    iNext. iIntros (wcsp' wca0') "HPC HMIE Hcsp Hca0 Hmepcc".

    (* The swap, the null stores and the hazard clear *)
    iApply (ctx_exit_clear_spec t ws wcsp' wcs0 Hhome_ctx Hhome_t Hlen21
             with "[$HPC $Hswitcher $HMIE $HU $Hcsp $Hcs0 $Hmtdc $Hsave $Hhazard
                    Hpost Hregs Hca0 Hcrit Hmepcc Hmcause Hmtval Hmpie]").
    iNext. iIntros (g_tstk) "(HPC & HMIE & HU & Hcsp & Hcs0 & Hmtdc & Hlent & Hsave)".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hca0 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcs0 Hregs") as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hcsp Hregs") as "Hregs".
    iApply ("Hpost" with "[-]").
    iFrame "HPC Hregs Hmtdc Hlent Hsave HMIE".
    iSplit.
    { iPureIntro. rewrite !dom_insert_L !dom_delete_L Hdom.
      pose proof (all_registers_s_correct csp). pose proof (all_registers_s_correct ca0).
      pose proof (all_registers_s_correct cs0). set_solver. }
    iSplit; first by rewrite lookup_insert_eq.
    rewrite /handover_at /volatile_csr_at. iFrame.
  Qed.

  (** * The park and the entry at the exit kind *)

  (** The park of an exited user thread [t]: its authorities move to the
      values of an exited thread, with its PC, MIE and register fragments,
      which go with the safety of an exited thread into the Suspended
      slot. *)
  Lemma ctx_park_exit_spec (ts : list nat) (t : nat) (v : resume_vals) (ws : list LWord)
      (b : InterruptStatus) :
    NoDup ts →
    length ws = 21%nat →
    v.(rv_mie) = InterruptDisabled →
    v.(rv_pc) = lword_of_word (Cap XSRW_ Local b_switcher e_switcher a_exit) →
    dom v.(rv_regs) = all_registers_s →
    exited_safe t -∗
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread t, Saving ParkExit v)) -∗
    save_area_holed (UserThread t)
      (rejoin_spill (exit_zero ws) (lword_of_word (WInt 0)) (lword_of_word exited_thread_pcc) b
         MCAUSE_THREAD_EXIT) -∗
    mtdc_lent_at (th := UserThread t) -∗
    MIE ↦ₜ[u t] InterruptDisabled -∗
    PC ↦ₚ[u t] v.(rv_pc) -∗
    regs[u t] v.(rv_regs) -∗
    na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) -∗
    close_Nact
    ={⊤}=∗
    na_own (tpool CtxSwitch) ⊤.
  Proof.
    iIntros (Hnd Hlen Hmie Hpc Hdom)
      "Hsafe #Hpool Hcur Hsa Hlent HMIE_t HPC_t Hregs_t Hna Hclose".
    destruct (exit_area_resume_ok ws b Hlen) as [Hok Hmie_ok].
    iMod (pool_park ts t ParkExit v ⊤ Hnd with "Hpool Hcur [Hsafe Hsa Hlent HMIE_t HPC_t Hregs_t]")
      as "Hcur"; [solve_ndisj| |].
    { iIntros "Hauths _".
      rewrite /auths_at /thread_auths.
      iDestruct "Hauths" as "(HPC_a & Hregs_a & Hmtdc_a & HMIE_a)".
      iMod (PC_update _ _ (lword_of_word exited_thread_pcc) with "HPC_a HPC_t") as "[HPC_a HPC_t]".
      iMod (MIE_update _ _ b with "HMIE_a HMIE_t") as "[HMIE_a HMIE_t]".
      iMod (regs_copy v.(rv_regs) exited_regs with "Hregs_a Hregs_t") as "[Hregs_a Hregs_t]".
      { by rewrite Hdom exited_regs_dom. }
      iModIntro.
      iExists (exit_area ws b), (exited_vals b).
      iFrame "Hlent". iSplit.
      - iPureIntro. by apply resume_ok_full_eq.
      - iSplitL "Hsa"; first (rewrite save_area_at_full; by iFrame).
        iSplitL "HPC_a Hregs_a Hmtdc_a HMIE_a"; first (rewrite /auths_at /thread_auths /=; iFrame).
        iNext. iIntros "Hpost _".
        iApply ("Hsafe" $! b exited_regs with "[] HPC_t HMIE_t Hregs_t Hpost").
        by rewrite exited_regs_dom. }
    iApply ("Hclose" with "[$Hcur $Hna]").
  Qed.

  (** The entry of the context-switch thread after the exit of user thread
      [t]: the exit PC, the exit block, the rejoin, the dispatch, the park
      of [t] as an exited thread, and the scheduler call. *)
  Lemma ctx_switch_entry_exit_spec (ts : list nat) (t : nat) (v : resume_vals) :
    ctx_switch_env C_sched w_pcc w_cgp w_csp ts -∗
    ctx_resume_specs C_sched w_csp -∗
    ctx_switch_entry_pre (CL := crit_link_full) (CR := crit_route_full) t ParkExit v -∗
    safe[CtxSwitch].
  Proof.
    iIntros "Henv #Hresume Hpre".
    iNamed "Hpre".
    iDestruct "Hsched" as (P) "[HP_own HP]".
    iNamed "Henv".
    iNamed "Hparked".
    pin_thread_instances CtxSwitch.

    (* [t] is one of the pool's *)
    iMod (pool_cur_in ts t _ ⊤ with "Hpool Hcur") as "[%Ht_in Hcur]"; first solve_ndisj.
    iDestruct (big_sepL_elem_of with "Hstatic") as "#Hstatic_t"; first exact Ht_in.
    pose proof (Hhomes t Ht_in) as Hhome_t.
    assert (t < swl_nthreads) as Ht by (by apply Hts).

    (* The scheduler's state *)
    iAssert (▷ scheduler_concrete C_sched w_csp)%I with "[HP HP_own]" as "Hconc".
    { iDestruct (saved_prop_agree with "Hsched HP_own") as "Heq". iNext. by iRewrite "Heq". }

    (* The exit PC, and [t]'s PC fragment and hazard part *)
    iMod (ctx_exit_pc ts t v ⊤ with "Hpool Hstatic_t Hcur Hexit")
      as "(%Hpc & Hcur & HPC_t & Hhazard)"; first solve_ndisj.
    iEval (rewrite Hpc) in "HPC".

    (* The posture of [t]: its save area, its mtdc token and its handover *)
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := crit_link_full (UserThread t)) (CR := crit_route_full (UserThread t))
               with "Hposture") as "[Hho Hpart]".
    iDestruct "Hho" as (wm wc vt b) "(_ & _ & %Hwc & _ & Hho)".
    cbn in Hwc. subst wc.
    iDestruct (csl_full_posture_part t with "Hpart") as "[(%ws & _ & Hsave) Hlent_t]".
    iDestruct (handover_at_thread_indep (UserThread t) CtxSwitch with "Hho") as "Hho".
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of (UserThread t))) as [n Hfit].
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    assert (length ws = 21%nat) as Hlen21.
    { rewrite -Hlen. tstack_unfold. solve_addr. }
    clear Hlen.

    (* The exit block *)
    iApply (ctx_exit_block_spec t v.(rv_regs) ws wm b vt Hhome_ctx Hhome_t Hdom with "[-]").
    iFrame "HPC Hstatic_t Hregs Hmtdc Hsave Hhazard HMIE Hho".
    iNext. iIntros (g_tstk lreg') "(%Hdom' & %Hcsp' & HPC & Hregs & Hmtdc & Hlent & Hsave & HMIE & Hho)".

    (* The rejoin, from mtdc's 0: the token of the context-switch thread
       stays with it *)
    iEval (rewrite /switcher_static) in "Hstatic_t". iNamed "Hstatic_t".
    iPoseProof (codefrag_pers_thread_indep (UserThread t) CtxSwitch with "Hswitcher_code")
      as "#Hswitcher".
    iApply (ctx_rejoin_spec t g_tstk lreg' (exit_zero ws) (lword_of_word (WInt 0))
              (lword_of_word exited_thread_pcc) b MCAUSE_THREAD_EXIT MCAUSE_THREAD_EXIT
              Hhome_ctx Hdom' Hcsp'
             with "[$HPC $Hswitcher $Hregs $Hmtdc $Hsave $HMIE $Hho Hlent HMIE_t Hregs_t Hconc Hcur
                    HPC_t Hlent_t Hna Hclose]").
    rewrite decide_True; last by rewrite Hhome_ctx.
    iFrame "Hlent".
    iNext. iIntros "(HPC & Hregs & Hmtdc & Hlent & Hsave & HMIE & Hho)".

    (* The dispatch *)
    assert (falls_to_scheduler_call MCAUSE_THREAD_EXIT) as Hfalls.
    { pose proof scheduler_causes_dispatch as Hall. rewrite Forall_forall in Hall.
      apply Hall. rewrite /scheduler_causes elem_of_app !elem_of_cons. by right; right; left. }
    assert (∀ r, is_Some (lreg' !! r)) as Hsome.
    { intros r. apply elem_of_dom. rewrite Hdom'. apply all_registers_s_correct. }
    destruct (Hsome ca0) as [wca0 Hwca0].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ct1 with "Hregs")
      as "[Hct1 Hregs]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca0 with "Hregs")
      as "[Hca0 Hregs]"; first by simplify_map_eq.
    iApply (ctx_dispatch_spec MCAUSE_THREAD_EXIT wca0 Hfalls with "[-]").
    iFrame "HPC Hswitcher Hct1 Hca0".
    iNext. iIntros "(HPC & Hct1 & Hca0)".
    iDestruct (big_sepM_insert_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "[$Hca0 $Hregs]")
      as "Hregs".
    iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I with "Hct1 Hregs") as "Hregs".

    (* The park: [cur] becomes [None], and [Nact] closes *)
    iMod (ctx_park_exit_spec ts t v ws b Hnd Hlen21 Hmie Hpc Hdom
           with "[] Hpool Hcur Hsave Hlent_t HMIE_t HPC_t Hregs_t Hna Hclose") as "Hna".
    { iApply (exited_safe_holds t with "Hswitcher_code"). }

    (* The scheduler call *)
    iDestruct (big_sepL_elem_of with "Hstatic") as "#Hstatic_t"; first exact Ht_in.
    iApply (ctx_scheduler_call_spec C_sched w_pcc w_cgp w_csp t g_tstk _
              (lword_of_word exited_thread_pcc) b MCAUSE_THREAD_EXIT MCAUSE_THREAD_EXIT Ht Hsched_in
             with "[$HPC $Hstatic_t $Hwords $Hentry $Htrap $Hresume $Hregs $HMIE $Hmtdc $Hlent
                    $Hho $Hna $Hconc]").
    - rewrite !dom_insert_L dom_delete_L !dom_insert_L Hdom'.
      pose proof (all_registers_s_correct ct1). pose proof (all_registers_s_correct ca0).
      pose proof (all_registers_s_correct ct0).
      set_solver.
    - by simplify_map_eq.
    - by simplify_map_eq.
    - by simplify_map_eq.
  Qed.

End ctx_exit.
