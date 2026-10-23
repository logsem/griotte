From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_handler
  copy_context_spec.

(** * Exception path, block 32: the setup of a stackful handler

    Block 32 ([.Lhandle_error_stack_setup]) writes the [ErrorState] below
    the moved stack pointer [ct0]: the untagged MEPCC first, then the 15
    registers of the register save area ([copy_context_asm]). The first
    store faults when the faulting [csp] does not allow the stores (a
    sealing range, no write permission, or a cursor below its base); the
    others then succeed. The handler's stack pointer is [ct0], [ca0] the
    faulting [csp] (the [ErrorState]), [ca1] the cause and [ca2] the value
    of the trap. The block falls through to the invocation. *)

Section Switcher_Exception_Blocks_7.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  #[local] Lemma switcher_instrs_32_split :
    switcher_instrs_n 32 =
      encodeInstrsW [ CLoad cs1 csp 0;
                      ClearTag cs1 cs1;
                      Store ct0 (inr cs1) (-16);
                      Mov ca2 (inr csp);
                      Lea ca2 (inl 1%Z);
                      Mov ca3 (inr ct0);
                      Lea ca3 (inl (-15)%Z) ] ++
      copy_context_instrs ca3 ca2 cs1 ca4 ++
      encodeInstrsW [ Mov ca0 (inr ct0);
                      Lea ca0 (inl (-16)%Z);
                      CLoad ca1 csp 18;
                      SpecialRW ca2 MTVAL (inr cnull);
                      Mov csp (inr ct0) ].
  Proof. reflexivity. Qed.

  (** Block 32. [error_state_written i] holds once the first [i] words of
      the [ErrorState] are written, through the accessor given for a
      faulting [csp] that allows the stores. *)
  #[local] Lemma switcher_exception_block_32_spec_aux
    (pc_a : Addr) (save : list LWord) (wcsp wct0 wcs1 wca0 wca1 wca2 wca3 wca4 : LWord)
    (error_state_written : nat → iProp Σ) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 32))%a ->
    length save = 21%nat ->
    lea_result wcsp ErrorState_size = Some wct0 ->
    error_state_fits wcsp ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ tstack_cap ∗
    ct0 ↦ᵣ wct0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca2 ↦ᵣ wca2 ∗
    ca3 ↦ᵣ wca3 ∗
    ca4 ↦ᵣ wca4 ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
    codefrag_pers pc_a (switcher_instrs_n 32) ∗
    error_state_written 0 ∗
    (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
       ⌜wcsp = WCap true p g b e a @@? π⌝ -∗
       ⌜error_state_stores_ok wcsp⌝ -∗
       cells_store_acc error_state_written p a π
         (lclear_tag (save !!! 0%nat) :: take 15 (drop 1 save))) ∗
    ▷ ( ( ⌜¬ error_state_stores_ok wcsp⌝ -∗
          csp ↦ᵣ tstack_cap ∗
          ct0 ↦ᵣ wct0 ∗
          cs1 ↦ᵣ - ∗
          ca0 ↦ᵣ wca0 ∗
          ca1 ↦ᵣ wca1 ∗
          ca2 ↦ᵣ wca2 ∗
          ca3 ↦ᵣ wca3 ∗
          ca4 ↦ᵣ wca4 ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
          error_state_written 0 -∗
          trap_safe (WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 2)%a) ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ⌜error_state_stores_ok wcsp⌝ -∗
          ∀ (mtval : Z) (wcs1' wca3' wca4' : LWord),
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 19)%a ∗
          csp ↦ᵣ wct0 ∗
          ct0 ↦ᵣ wct0 ∗
          cs1 ↦ᵣ wcs1' ∗
          ca0 ↦ᵣ wcsp ∗
          ca1 ↦ᵣ (save !!! 18%nat) ∗
          ca2 ↦ᵣ WInt mtval ∗
          ca3 ↦ᵣ wca3' ∗
          ca4 ↦ᵣ wca4' ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
          codefrag_pers pc_a (switcher_instrs_n 32) ∗
          error_state_written (Z.to_nat ErrorState_size) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hlen Hlea Hfits)
      "(HPC & Hcsp & Hct0 & Hcs1 & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hsave & #Hcode
       & HES & Hacc & Hpost)".
    iPoseProof "Hcode" as "Hcode_all".
    iEval (rewrite switcher_instrs_32_split) in "Hcode_all".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hcopy _]".
    iEval (simpl length) in "Hcopy".
    codefrag_facts "Hcode".
    assert (length (switcher_instrs_n 32) = 19%nat) as Hlen32 by reflexivity.
    rewrite Hlen32 in Hsub.
    destruct (lookup_lt_is_Some_2 save 0%nat) as [w0 Hw0]; first lia.
    pose proof (tstack_save_cell_ok 0 ltac:(lia)) as (Hts_0 & Hts_0_bounds & Hts_0_shadow).
    rewrite (_ : (b_trusted_stack ^+ 0)%a = b_trusted_stack) in Hts_0 Hts_0_bounds Hts_0_shadow;
      last solve_addr.
    iDestruct (tstack_save_area_acc _ _ _ Hw0 with "Hsave") as "[Hs0 Hsave]".
    rewrite /switcher_instrs_n /assembled_switcher_n /tstack_cap.
    (* CLoad cs1 csp TrustedStack_offset_mepcc *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ cs1 csp 0)
      with "[$HPC $Hcs1 $Hcsp $Hs0]" as "(HPC & Hcs1 & Hcsp & Hs0)".
    rewrite lload_word_RWL.
    iDestruct ("Hsave" with "Hs0") as "Hsave".
    (* ClearTag cs1 cs1 *)
    iInstr "Hcode".
    destruct (decide (error_state_stores_ok wcsp)) as [Hok | Hnok]; cycle 1.
    { iDestruct "Hpost" as "[Hfailed _]".
      destruct (error_state_store_fault _ _ Hlea Hfits Hnok)
        as [Hncap | (p & g & b & e & a & ea & Hw & Hea & [Hwa | Hwb])].
      - (* Store ct0 cs1 (TrustedStack_offset_mepcc - ErrorState_size) *)
        iInstrApply "Hcode" wp_store_fail_reg_not_cap_lword_imm with "[$HPC $Hcs1 $Hct0]"
          as "(HPC & Hcs1 & Hct0)".
        iTrap with "Hfailed".
      - destruct wct0 as [w π]; cbn in Hw; subst w.
        (* Store ct0 cs1 (TrustedStack_offset_mepcc - ErrorState_size) *)
        iInstrApply "Hcode" wp_store_fail_reg_perm_imm with "[$HPC $Hcs1 $Hct0]"
          as "(HPC & Hcs1 & Hct0)".
        iTrap with "Hfailed".
      - destruct wct0 as [w π]; cbn in Hw; subst w.
        (* Store ct0 cs1 (TrustedStack_offset_mepcc - ErrorState_size) *)
        iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcs1 $Hct0]"
          as "(HPC & Hcs1 & Hct0)".
        iTrap with "Hfailed". }
    iDestruct "Hpost" as "[_ Hpost]".
    destruct wcsp as [wsp π].
    rewrite /error_state_stores_ok /= in Hok.
    destruct wsp as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb]; try done.
    destruct t; last done.
    destruct Hok as (Hwa & Hba & Hae).
    iPoseProof ("Hacc" $! p g b e a π with "[//] [%]") as "Hacc_es".
    { by rewrite /error_state_stores_ok /=. }
    rewrite /lea_result /ErrorState_size /= in Hlea Hae.
    rewrite (_ : (a + 16)%a = Some (a ^+ 16)%a) in Hlea; last solve_addr.
    injection Hlea as <-.
    iDestruct "Hacc_es" as "#Hacc_es".
    iDestruct (cells_store_acc_tail error_state_written p a π (lclear_tag (save !!! 0%nat))
                 (take 15 (drop 1 save))
                with "[]") as "Hacc_tail".
    { rewrite /= length_take length_drop Hlen /=. solve_addr. }
    { rewrite /cells_store_acc. iModIntro. iExact "Hacc_es". }
    iMod ("Hacc_es" $! 0%nat with "[] HES") as (v q) "(%Hsh & Hcell & Hderef & Hclose)".
    { iPureIntro; cbn; lia. }
    rewrite (_ : (a ^+ 0%nat)%a = a) in Hsh |- *; last solve_addr.
    (* Store ct0 cs1 (TrustedStack_offset_mepcc - ErrorState_size) *)
    iInstrApply "Hcode"
      (wp_store_success_reg_store_word_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-16))
      with "[$HPC $Hcs1 $Hct0 $Hcell $Hderef]"
      as "(HPC & Hcs1 & Hct0 & Hcell & Hderef)".
    { rewrite /withinBounds; solve_addr. }
    { solve_addr. }
    rewrite (list_lookup_total_correct _ _ _ Hw0).
    iMod ("Hclose" with "Hcell Hderef") as "HES".
    (* Mov ca2 csp *)
    iInstr "Hcode".
    (* Lea ca2 TrustedStack_offset_cra *)
    iInstr "Hcode".
    { pose proof (tstack_save_cell_ok 1 ltac:(lia)) as (Hts_1 & _). exact Hts_1. }
    (* Mov ca3 ct0 *)
    iInstr "Hcode".
    (* Lea ca3 (TrustedStack_offset_cra - ErrorState_size) *)
    iInstr "Hcode".
    { transitivity (Some (a ^+ 1)%a); solve_addr. }
    (* The source of the copy: the words 1-15 of the register save area. *)
    assert ((b_trusted_stack + 21)%a = Some tstack_save_end) as Hsave_end.
    { pose proof trusted_stack_frames_fit as [n Hfit].
      rewrite /tstack_save_end. tstack_unfold. solve_addr. }
    pose proof (tstack_save_cell_ok 20 ltac:(lia)) as (_ & Hts_20 & _).
    rewrite /withinBounds in Hts_20.
    assert (save = w0 :: take 15 (drop 1 save) ++ drop 16 save) as Hsave_eq.
    { destruct save as [|w0' rest]; first done.
      cbn in Hw0 |- *. injection Hw0 as ->. by rewrite take_drop. }
    iEval (rewrite {1}Hsave_eq) in "Hsave".
    iEval (rewrite (region_pointsto_cons _ (b_trusted_stack ^+ 1)%a); [|solve_addr|solve_addr])
      in "Hsave".
    iDestruct "Hsave" as "[Hs0 Hsave]".
    iEval (rewrite (region_pointsto_split _ _ (b_trusted_stack ^+ 16)%a);
           [|solve_addr|rewrite length_take length_drop Hlen /finz.dist; solve_addr])
      in "Hsave".
    iDestruct "Hsave" as "[Hsrc Hrest]".
    iEval (rewrite (_ : (b_trusted_stack ^+ 16)%a = ((b_trusted_stack ^+ 1) ^+ 15)%a);
           last solve_addr) in "Hsrc".
    (* copy_context_asm ca3 ca2 cs1 ca4 *)
    iApply (copy_context_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (take 15 (drop 1 save)) _ _ (λ i, error_state_written (S i))
             with "[- $HPC $Hcopy $Hca2 $Hca3 $Hcs1 $Hca4 $HES $Hacc_tail $Hsrc]").
    all: try done.
    all: try (rewrite length_take length_drop Hlen; done).
    all: try (rewrite /= in Hsub; solve_addr).
    { pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
      rewrite /disjoint_from_shadow elem_of_disjoint in Hts_shadow |- *.
      intros x Hx HR. eapply Hts_shadow; last exact HR.
      apply elem_of_finz_seq_between. apply elem_of_finz_seq_between in Hx.
      solve_addr. }
    { clear; set_solver. }
    iIntros "!> (%wscratch' & HPC & Hca2 & Hca3 & Hcs1 & Hca4 & Hsrc & HES)".
    assert (length (copy_context_instrs ca3 ca2 cs1 ca4) = 7%nat) as Hlen_cc by reflexivity.
    rewrite Hlen_cc.
    rewrite (_ : ((pc_a ^+ 7) ^+ 7%nat)%a = (pc_a ^+ 14)%a); last solve_addr.
    iAssert ([[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]])%I
      with "[Hs0 Hsrc Hrest]" as "Hsave".
    { iEval (rewrite Hsave_eq).
      rewrite (region_pointsto_cons _ (b_trusted_stack ^+ 1)%a); [|solve_addr|solve_addr].
      rewrite (region_pointsto_split _ _ (b_trusted_stack ^+ 16)%a);
        [|solve_addr|rewrite length_take length_drop Hlen /finz.dist; solve_addr].
      rewrite (_ : ((b_trusted_stack ^+ 1) ^+ 15)%a = (b_trusted_stack ^+ 16)%a); last solve_addr.
      iFrame. }
    (* Mov ca0 ct0 *)
    iInstr "Hcode".
    (* Lea ca0 (- ErrorState_size) *)
    iInstr "Hcode".
    { transitivity (Some a); solve_addr. }
    destruct (lookup_lt_is_Some_2 save 18%nat) as [w18 Hw18]; first lia.
    rewrite (list_lookup_total_correct _ _ _ Hw18).
    iDestruct (tstack_save_area_acc _ _ _ Hw18 with "Hsave") as "[Hs18 Hsave]".
    pose proof (tstack_save_cell_ok 18 ltac:(lia)) as (Hts_18 & Hts_18_bounds & Hts_18_shadow).
    (* CLoad ca1 csp TrustedStack_offset_mcause *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ ca1 csp 18)
      with "[$HPC $Hca1 $Hcsp $Hs18]" as "(HPC & Hca1 & Hcsp & Hs18)".
    rewrite lload_word_RWL.
    iDestruct ("Hsave" with "Hs18") as "Hsave".
    (* SpecialRW ca2 mtval cnull *)
    iInstrApply "Hcode" wp_csrr_mtval with "[$HPC $Hca2]" as (mtval) "(HPC & Hca2)".
    (* Mov csp ct0 *)
    iInstr "Hcode".
    iApply ("Hpost" with "[%]").
    { by rewrite /error_state_stores_ok /=. }
    iFrame "∗ Hcode".
  Qed.

  (** Block 32, from [.Lhandle_error_stack_setup]: the [ErrorState] of a
      stackful handler is written below [ct0], through the accessor of
      [error_state_written]. The first store faults when the faulting
      [csp] does not allow the stores. Otherwise [csp] and [ct0] are the
      handler's stack, [ca0] the faulting [csp], [ca1] the cause (word 18
      of the register save area) and [ca2] the value of the trap, and the
      PC is at the invocation of the handler. *)
  Lemma switcher_stackful_setup_spec
    (save : list LWord) (wcsp wct0 wcs1 wca0 wca1 wca2 wca3 wca4 : LWord)
    (error_state_written : nat → iProp Σ) :
    length save = 21%nat ->
    lea_result wcsp ErrorState_size = Some wct0 ->
    error_state_fits wcsp ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error_stack_setup" ∗
    csp ↦ᵣ tstack_cap ∗
    ct0 ↦ᵣ wct0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca2 ↦ᵣ wca2 ∗
    ca3 ↦ᵣ wca3 ∗
    ca4 ↦ᵣ wca4 ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
    switcher_code ∗
    error_state_written 0 ∗
    (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
       ⌜wcsp = WCap true p g b e a @@? π⌝ -∗
       ⌜error_state_stores_ok wcsp⌝ -∗
       cells_store_acc error_state_written p a π
         (lclear_tag (save !!! 0%nat) :: take 15 (drop 1 save))) ∗
    ▷ ( ( ⌜¬ error_state_stores_ok wcsp⌝ -∗
          csp ↦ᵣ tstack_cap ∗
          ct0 ↦ᵣ wct0 ∗
          cs1 ↦ᵣ - ∗
          ca0 ↦ᵣ wca0 ∗
          ca1 ↦ᵣ wca1 ∗
          ca2 ↦ᵣ wca2 ∗
          ca3 ↦ᵣ wca3 ∗
          ca4 ↦ᵣ wca4 ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
          switcher_code ∗
          error_state_written 0 -∗
          trap_safe (switcher_pc (switcher_label_offset ".Lhandle_error_stack_setup" + 2)) ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ⌜error_state_stores_ok wcsp⌝ -∗
          ∀ (mtval : Z) (wcs1' wca3' wca4' : LWord),
          PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_invoke" ∗
          csp ↦ᵣ wct0 ∗
          ct0 ↦ᵣ wct0 ∗
          cs1 ↦ᵣ wcs1' ∗
          ca0 ↦ᵣ wcsp ∗
          ca1 ↦ᵣ (save !!! 18%nat) ∗
          ca2 ↦ᵣ WInt mtval ∗
          ca3 ↦ᵣ wca3' ∗
          ca4 ↦ᵣ wca4' ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
          switcher_code ∗
          error_state_written (Z.to_nat ErrorState_size) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hlen Hlea Hfits)
      "(HPC & Hcsp & Hct0 & Hcs1 & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hsave & #Hswitcher
       & HES & Hacc & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lhandle_error_stack_setup") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_32_spec_aux _ save wcsp wct0 wcs1 wca0 wca1 wca2 wca3 wca4
              error_state_written
             with "[- $HPC $Hcsp $Hct0 $Hcs1 $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hsave $Hcode
                      $HES $Hacc]");
      [done | done | done | done |].
    iNext; iSplit.
    - iIntros (Hnok) "(Hcsp & Hct0 & Hcs1 & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hsave & HES)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      iDestruct "Hpost" as "[Hfailed _]".
      rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 32) ^+ 2)%a =
                   (a_switcher_call ^+ (switcher_label_offset ".Lhandle_error_stack_setup" + 2))%a);
        last (offsets_compute; solve_addr+Hsize).
      iApply ("Hfailed" with "[//]"). iFrame "∗ Hswitcher".
    - iIntros (Hok mtval wcs1' wca3' wca4')
        "(HPC & Hcsp & Hct0 & Hcs1 & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hsave & _ & HES)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      switcher_change_pc (switcher_label_offset ".Lhandle_error_handler_invoke").
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[//]"). iFrame "∗ Hswitcher".
  Qed.

End Switcher_Exception_Blocks_7.
