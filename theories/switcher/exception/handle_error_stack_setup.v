From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_state
  copy_context_spec.

(** * Exception path: the setup of a stackful handler

    [.Lhandle_error_stack_setup] writes the [ErrorState] at the moved stack
    pointer [ct0], below the faulting cursor: the untagged MEPCC first,
    then the 15 registers of the register save area ([copy_context_asm]).
    The first store faults when the faulting [csp] does not allow it (a
    sealing range, no write permission, or the base of the [ErrorState] not
    below the end); otherwise a store faults when it reaches the end of the
    faulting [csp], after the words below the end are written, or all the
    stores succeed. The handler's stack pointer and [ca0] are [ct0] (the
    [ErrorState]), [ca1] the cause and [ca2] the value of the trap, from the
    lent mtval. mtval goes back to the state interpretation after it is
    read, or before a store faults. The block falls through to
    [.Lhandle_error_handler_invoke]. *)

Section Handle_Error_Stack_Setup.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The code of [.Lhandle_error_stack_setup], around the copy. *)
  #[local] Definition handle_error_stack_setup_instrs : list Word :=
    encodeInstrsW [ CLoad cs1 csp 0;
                    ClearTag cs1 cs1;
                    Store ct0 (inr cs1) 0;
                    Lea ca2 csp (inl 1%Z);
                    Lea ca3 ct0 (inl 1%Z) ] ++
    copy_context_instrs ca3 ca2 cs1 ca4 ++
    encodeInstrsW [ Mov ca0 (inr ct0);
                    CLoad ca1 csp 18;
                    SpecialRW ca2 MTVAL (inr cnull);
                    Mov csp (inr ca0) ].

  (** From [.Lhandle_error_stack_setup]: the [ErrorState] of a stackful
      handler is written at [ct0], through the accessor of
      [error_state_written]: [error_state_written i] holds once the first
      [i] words of the [ErrorState] are written, through the accessor given
      for a faulting [csp] that allows the first store. When the faulting
      [csp] does not allow the stores, a store faults: the first one, or
      one of the copy, after [k] words are written. Otherwise [csp], [ct0]
      and [ca0] are the handler's stack, at the [ErrorState], [ca1] the
      cause (word 18 of the register save area) and [ca2] the value [mtval]
      of the trap, and the PC is at the invocation of the handler. Either
      way, the lent mtval has gone back to the state interpretation. *)
  Lemma handle_error_stack_setup_spec
    (save : list LWord) (wcsp wct0 wcs1 wca0 wca1 wca2 wca3 wca4 : LWord)
    (error_state_written : nat → iProp Σ) (mtval : Z) :
    length save = 21%nat ->
    lea_result wcsp (- ErrorState_size) = Some wct0 ->
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
    trap_vcsr_res ∗
    vcsr_frag MTVAL (lword_of_word (WInt mtval)) ∗
    switcher_code ∗
    error_state_written 0 ∗
    (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
       ⌜wcsp = WCap true p g b e a @@? π⌝ -∗
       ⌜error_state_first_store_ok wcsp⌝ -∗
       cells_store_acc error_state_written p e (a ^+ (- ErrorState_size))%a π
         (lclear_tag (save !!! 0%nat) :: take 15 (drop 1 save))) ∗
    ▷ ( ( ⌜¬ error_state_stores_ok wcsp⌝ -∗
          ∀ (k : nat) (off : Z),
          ⌜(k < Z.to_nat ErrorState_size)%nat⌝ -∗
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          csp ↦ᵣ tstack_cap ∗
          ct0 ↦ᵣ wct0 ∗
          cs1 ↦ᵣ - ∗
          ca0 ↦ᵣ wca0 ∗
          ca1 ↦ᵣ wca1 ∗
          ca2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
          error_state_written k ∗
          trap_entry_res -∗
          trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ⌜error_state_stores_ok wcsp⌝ -∗
          ∀ (wcs1' wca3' wca4' : LWord),
          PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_invoke" ∗
          csp ↦ᵣ wct0 ∗
          ct0 ↦ᵣ wct0 ∗
          cs1 ↦ᵣ wcs1' ∗
          ca0 ↦ᵣ wct0 ∗
          ca1 ↦ᵣ (save !!! 18%nat) ∗
          ca2 ↦ᵣ WInt mtval ∗
          ca3 ↦ᵣ wca3' ∗
          ca4 ↦ᵣ wca4' ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
          error_state_written (Z.to_nat ErrorState_size) ∗
          trap_entry_res -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hlen Hlea Hfits)
      "(HPC & Hcsp & Hct0 & Hcs1 & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hsave & Htok & Hmtval
       & #Hswitcher & HES & Hacc & Hpost)".
    switcher_open_label ".Lhandle_error_stack_setup" "Hswitcher" as "Hcode" pc_a Hpc_a.
    switcher_hide "Hpost" as hpost.
    iAssert (codefrag_pers pc_a handle_error_stack_setup_instrs) as "Hcode_all";
      first iExact "Hcode".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hcopy _]".
    iEval (simpl length) in "Hcopy".
    destruct (lookup_lt_is_Some_2 save 0%nat) as [w0 Hw0]; first lia.
    pose proof (tstack_save_cell_ok 0 ltac:(lia)) as (Hts_0 & Hts_0_bounds & Hts_0_shadow).
    rewrite (_ : (b_trusted_stack ^+ 0)%a = b_trusted_stack) in Hts_0 Hts_0_bounds Hts_0_shadow;
      last solve_addr.
    iDestruct (tstack_save_area_acc _ _ _ Hw0 with "Hsave") as "[Hs0 Hsave]".
    rewrite /tstack_cap.
    (* CLoad cs1 csp TrustedStack_offset_mepcc *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ cs1 csp 0)
      with "[$HPC $Hcs1 $Hcsp $Hs0]" as "(HPC & Hcs1 & Hcsp & Hs0)".
    rewrite lload_word_RWL.
    iDestruct ("Hsave" with "Hs0") as "Hsave".
    (* ClearTag cs1 cs1 *)
    iInstr "Hcode".
    destruct (decide (error_state_first_store_ok wcsp)) as [Hfirst | Hnfirst]; cycle 1.
    { subst hpost.
      iDestruct "Hpost" as "[Hfailed _]".
      assert (¬ error_state_stores_ok wcsp) as Hnok.
      { by intros ?%error_state_stores_ok_first. }
      destruct (error_state_store_fault _ _ Hlea Hfits Hnok)
        as [ (_ & [Hncap | (p & g & b & e & a & ea & Hw & Hea & [Hwa | Hwb])]) | [? _] ];
        last done.
      - (* Store ct0 cs1 TrustedStack_offset_mepcc *)
        iInstrApply "Hcode" wp_store_fail_reg_not_cap_lword_imm with "[$HPC $Hcs1 $Hct0]"
          as "(HPC & Hcs1 & Hct0)".
        iApply (wp_vcsr_tval_return with "Hmtval Htok"); first done.
        iIntros "Htok".
        iSpecialize ("Hfailed" with "[//]").
        iSpecialize ("Hfailed" $! 0%nat with "[%]"); first (rewrite /ErrorState_size; lia).
        switcher_merge_pc.
        iTrap with "Hfailed".
        apply trap_no_resume_switcher_pc. by vm_compute.
      - destruct wct0 as [w π]; cbn in Hw; subst w.
        (* Store ct0 cs1 TrustedStack_offset_mepcc *)
        iInstrApply "Hcode" wp_store_fail_reg_perm_imm with "[$HPC $Hcs1 $Hct0]"
          as "(HPC & Hcs1 & Hct0)".
        iApply (wp_vcsr_tval_return with "Hmtval Htok"); first done.
        iIntros "Htok".
        iSpecialize ("Hfailed" with "[//]").
        iSpecialize ("Hfailed" $! 0%nat with "[%]"); first (rewrite /ErrorState_size; lia).
        switcher_merge_pc.
        iTrap with "Hfailed".
        apply trap_no_resume_switcher_pc. by vm_compute.
      - destruct wct0 as [w π]; cbn in Hw; subst w.
        (* Store ct0 cs1 TrustedStack_offset_mepcc *)
        iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcs1 $Hct0]"
          as "(HPC & Hcs1 & Hct0)".
        iApply (wp_vcsr_tval_return with "Hmtval Htok"); first done.
        iIntros "Htok".
        iSpecialize ("Hfailed" with "[//]").
        iSpecialize ("Hfailed" $! 0%nat with "[%]"); first (rewrite /ErrorState_size; lia).
        switcher_merge_pc.
        iTrap with "Hfailed".
        apply trap_no_resume_switcher_pc. by vm_compute. }
    destruct wcsp as [wsp π].
    pose proof Hfirst as Hfirst'.
    rewrite /error_state_first_store_ok /= in Hfirst'.
    destruct wsp as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb]; try done.
    destruct t; last done.
    destruct Hfirst' as (Hwa & Hba & Hae).
    iPoseProof ("Hacc" $! p g b e a π with "[//] [//]") as "Hacc_es".
    rewrite /lea_result /= in Hlea.
    destruct (a + - ErrorState_size)%a as [a16|] eqn:Ha16;
      last (exfalso; rewrite /ErrorState_size in Ha16 Hba; solve_addr).
    injection Hlea as <-.
    rewrite /ErrorState_size in Ha16 Hba Hae.
    rewrite (_ : (a ^+ - ErrorState_size)%a = a16); last (rewrite /ErrorState_size; solve_addr).
    iDestruct "Hacc_es" as "#Hacc_es".
    iDestruct (cells_store_acc_tail error_state_written p e a16 π (lclear_tag (save !!! 0%nat))
                 (take 15 (drop 1 save))
                with "[]") as "Hacc_tail".
    { rewrite /cells_store_acc. iModIntro. iExact "Hacc_es". }
    iMod ("Hacc_es" $! 0%nat with "[%] [%] HES") as (v q) "(%Hsh & Hcell & Hderef & Hclose)".
    { cbn; lia. }
    { solve_addr. }
    rewrite (_ : (a16 ^+ 0%nat)%a = a16) in Hsh |- *; last solve_addr.
    (* Store ct0 cs1 TrustedStack_offset_mepcc *)
    iInstrApply "Hcode"
      (wp_store_success_reg_store_word_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0)
      with "[$HPC $Hcs1 $Hct0 $Hcell $Hderef]"
      as "(HPC & Hcs1 & Hct0 & Hcell & Hderef)".
    { rewrite /withinBounds; solve_addr. }
    { solve_addr. }
    rewrite (list_lookup_total_correct _ _ _ Hw0).
    iMod ("Hclose" with "Hcell Hderef") as "HES".
    (* Lea ca2 csp TrustedStack_offset_cra *)
    iInstr "Hcode".
    { pose proof (tstack_save_cell_ok 1 ltac:(lia)) as (Hts_1 & _). exact Hts_1. }
    (* Lea ca3 ct0 TrustedStack_offset_cra *)
    iInstr "Hcode".
    { transitivity (Some (a16 ^+ 1)%a); solve_addr. }
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
    all: try (lazymatch goal with
              | |- environments.envs_entails _ _ => fail
              | |- disjoint_from_shadow _ _ => fail
              | |- _ ∉ _ => fail
              | _ => solve_addr
              end).
    { pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
      rewrite /disjoint_from_shadow elem_of_disjoint in Hts_shadow |- *.
      intros x Hx HR. eapply Hts_shadow; last exact HR.
      apply elem_of_finz_seq_between. apply elem_of_finz_seq_between in Hx.
      solve_addr. }
    { clear; set_solver. }
    (* The register save area, from its parts *)
    iAssert (∀ ws : list LWord,
               ⌜ws = take 15 (drop 1 save)⌝ -∗
               b_trusted_stack ↦ₐ w0 -∗
               [[ (b_trusted_stack ^+ 1)%a , ((b_trusted_stack ^+ 1) ^+ 15)%a ]] ↦ₐ [[ ws ]] -∗
               [[ (b_trusted_stack ^+ 16)%a , tstack_save_end ]] ↦ₐ [[ drop 16 save ]] -∗
               [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]])%I as "Hsave_join".
    { iIntros (ws ->) "Hs0 Hsrc Hrest".
      iEval (rewrite Hsave_eq).
      rewrite (region_pointsto_cons _ (b_trusted_stack ^+ 1)%a); [|solve_addr|solve_addr].
      rewrite (region_pointsto_split _ _ (b_trusted_stack ^+ 16)%a);
        [|solve_addr|rewrite length_take length_drop Hlen /finz.dist; solve_addr].
      rewrite (_ : ((b_trusted_stack ^+ 1) ^+ 15)%a = (b_trusted_stack ^+ 16)%a); last solve_addr.
      iFrame. }
    iNext. iSplit.
    { (* A store of the copy faults, after [S j] words: the cursor of the
         faulting [csp] is past its end *)
      iIntros (j Hj Hout) "Hca2 Hca3 Hcs1 Hca4 Hsrc HES HPC".
      iDestruct ("Hsave_join" with "[//] Hs0 Hsrc Hrest") as "Hsave".
      iApply (wp_vcsr_tval_return with "Hmtval Htok"); first done.
      iIntros "Htok".
      iApply (wp_trap with "HPC").
      subst hpost.
      iDestruct "Hpost" as "[Hfailed _]".
      iSpecialize ("Hfailed" with "[%]").
      { rewrite /error_state_stores_ok /=. intros (_ & _ & Hle). solve_addr. }
      switcher_merge_pc.
      iApply ("Hfailed" $! (S j) with "[%] [%] [$Hcsp $Hct0 $Hcs1 $Hca0 $Hca1 $Hca2 $Hca3
                                           $Hca4 $Hsave $HES $Htok]").
      - rewrite /ErrorState_size; lia.
      - apply trap_no_resume_switcher_pc. by vm_compute. }
    iIntros (wscratch' Hin) "HPC Hca2 Hca3 Hcs1 Hca4 Hsrc HES".
    iDestruct ("Hsave_join" with "[//] Hs0 Hsrc Hrest") as "Hsave".
    assert (length (copy_context_instrs ca3 ca2 cs1 ca4) = 7%nat) as Hlen_cc by reflexivity.
    rewrite Hlen_cc.
    rewrite (_ : ((pc_a ^+ 5) ^+ 7%nat)%a = (pc_a ^+ 12)%a); last solve_addr.
    (* Mov ca0 ct0 *)
    iInstr "Hcode".
    destruct (lookup_lt_is_Some_2 save 18%nat) as [w18 Hw18]; first lia.
    iDestruct (tstack_save_area_acc _ _ _ Hw18 with "Hsave") as "[Hs18 Hsave]".
    pose proof (tstack_save_cell_ok 18 ltac:(lia)) as (Hts_18 & Hts_18_bounds & Hts_18_shadow).
    (* CLoad ca1 csp TrustedStack_offset_mcause *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ ca1 csp 18)
      with "[$HPC $Hca1 $Hcsp $Hs18]" as "(HPC & Hca1 & Hcsp & Hs18)".
    rewrite lload_word_RWL.
    iDestruct ("Hsave" with "Hs18") as "Hsave".
    (* SpecialRW ca2 mtval cnull *)
    iInstrApply "Hcode" wp_cspecialr_vcsr with "[$HPC $Hca2 $Hmtval]"
      as "(HPC & Hca2 & Hmtval)".
    (* mtval goes back to the state interpretation *)
    iApply (wp_vcsr_tval_return with "Hmtval Htok"); first done.
    iIntros "Htok".
    (* Mov csp ca0 *)
    iInstr "Hcode".
    switcher_change_pc_label ".Lhandle_error_handler_invoke".
    subst hpost.
    rewrite (list_lookup_total_correct _ _ _ Hw18).
    iDestruct "Hpost" as "[_ Hpost]".
    iApply ("Hpost" with "[%]").
    { rewrite /error_state_stores_ok /=.
      split_and!; [done | rewrite /ErrorState_size; solve_addr | solve_addr]. }
    iFrame "HPC Hcsp Hct0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hsave HES Htok".
  Qed.

End Handle_Error_Stack_Setup.
