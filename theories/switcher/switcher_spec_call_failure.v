From iris.proofmode Require Import proofmode.
From griotte Require Import switcher_spec_call.
From griotte Require Import switcher_load_spec switcher_spec_call_blocks.
From griotte Require Import logrel memory_region rules proofmode map_simpl register_tactics.

Section Switcher_Call_Failure.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** Exhaustion does not invoke a callee. Without shadow ownership, each
      reloaded word is either preserved or has its tag cleared. *)
  Lemma switcher_call_block_16_spec_general
    pc_b pc_e pc_a
    wcgp wcra wcs0 wcs1 b_stk e_stk a_stk :
    let switcher_instrs_16 := (switcher_instrs_n 16) in
    let len_switcher_16 := length switcher_instrs_16 in
    disjoint_from_shadow b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_16)%a ->

    (pc_a ^+ 10 + -36)%a = Some (pc_a ^+ -26)%a ->

    (b_stk <= a_stk)%a ->
    (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ->

    PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    (∃ wcs0', cs0 ↦ᵣ wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ wcgp') ∗
    (∃ wcra', cra ↦ᵣ wcra') ∗
    (∃ wca0, ca0 ↦ᵣ wca0) ∗
    (∃ wca1, ca1 ↦ᵣ wca1) ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag pc_a switcher_instrs_16 ∗
    ▷ (∀ rcgp rcra rcs0 rcs1,
         ⌜load_heap wcgp rcgp ∧ load_heap wcra rcra ∧
           load_heap wcs0 rcs0 ∧ load_heap wcs1 rcs1⌝ -∗
          ( PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ -26)%a ∗
             cs0 ↦ᵣ rcs0 ∗
             cs1 ↦ᵣ rcs1 ∗
             cgp ↦ᵣ rcgp ∗
             cra ↦ᵣ rcra ∗
             ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
             ca1 ↦ᵣ WInt 0 ∗
             csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
             a_stk ↦ₐ wcs0 ∗
             (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
             (a_stk ^+ 2)%a ↦ₐ wcra ∗
             (a_stk ^+ 3)%a ↦ₐ wcgp ∗
             codefrag pc_a switcher_instrs_16 ∗
             £ 1 -∗
             WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
           )
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_16 len_switcher_16; subst switcher_instrs_16 len_switcher_16.
    iIntros (Hstk_shadow Hsub_reg Hpca_next Hbstk Hbstk')
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0] & [%wca1 Hca1]
      & Hcsp & Hastk0 & Hastk1 & Hastk2 & Hastk3 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    (* Load cgp csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack _ _ _ _ _ _ (pc_a ^+ 2)%a cgp csp
      with "[$HPC $Hi $Hcgp $Hcsp $Hastk3]");
      try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret) "[-> | (%rcgp & -> & %Hrcgp & HPC & Hi & Hcgp & Hcsp & Hastk3)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    (* Load cra csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack _ _ _ _ _ _ (pc_a ^+ 4)%a cra csp
      with "[$HPC $Hi $Hcra $Hcsp $Hastk2]");
      try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret) "[-> | (%rcra & -> & %Hrcra & HPC & Hi & Hcra & Hcsp & Hastk2)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    (* Load cs1 csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack _ _ _ _ _ _ (pc_a ^+ 6)%a cs1 csp
      with "[$HPC $Hi $Hcs1 $Hcsp $Hastk1]");
      try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret) "[-> | (%rcs1 & -> & %Hrcs1 & HPC & Hi & Hcs1 & Hcsp & Hastk1)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    (* Load cs0 csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack _ _ _ _ _ _ (pc_a ^+ 8)%a cs0 csp
      with "[$HPC $Hi $Hcs0 $Hcsp $Hastk0]");
      try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret) "[-> | (%rcs0 & -> & %Hrcs0 & HPC & Hi & Hcs0 & Hcsp & Hastk0)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Mov ca0 (inl (-141)%Z); *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull))as [|_]; first done.
    (* Mov ca1 (inl 0%Z); *)
    iInstr "Hcode" with "Hlc".
    (* Jmp (inl (-36)%Z) *)
    iInstr "Hcode".

    iApply ("Hpost" $! rcgp rcra rcs0 rcs1); iFrame; done.
  Qed.

  (** A malformed callback never reaches a callee. Stack exhaustion can
      still return to the caller, with saved heap words possibly tag-cleared. *)
  Lemma switcher_cc_specification_failure
    (Nswitcher : namespace)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word) (arg_rmap rmap : Reg) :
    let a_stk4 := (a_stk ^+ 4)%a in
    disjoint_from_shadow b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    is_sealed_with_o wct1_caller ot_switcher = false ->
    dom rmap = all_registers_s ∖
      ({[PC; cgp; cra; csp; ct1; cs0; cs1]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ᵣ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ([∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w)
    ∗ cs0 ↦ᵣ wcs0_caller ∗ cs1 ↦ᵣ wcs1_caller
    ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
    ∗ [[a_stk, e_stk]] ↦ₐ [[stk_mem]]
    ∗ ▷ (∀ rmap' rcgp rcra rcs0 rcs1,
        ⌜dom rmap' = all_registers_s ∖ {[PC; cgp; cra; csp; ca0; ca1; cs0; cs1]}⌝
        ∗ ⌜(b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a⌝
        ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
             load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
        ∗ na_own cerise_nais ⊤
        ∗ PC ↦ᵣ updatePcPerm rcra
        ∗ cgp ↦ᵣ rcgp ∗ cra ↦ᵣ rcra ∗ cs0 ↦ᵣ rcs0 ∗ cs1 ↦ᵣ rcs1
        ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
        ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗ ca1 ↦ᵣ WInt 0
        ∗ ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝)
        ∗ [[a_stk, a_stk4]] ↦ₐ [[ [wcs0_caller; wcs1_caller; wcra_caller; wcgp_caller] ]]
        ∗ [[a_stk4, e_stk]] ↦ₐ [[drop 4 stk_mem]]
        ∗ £ 2
        -∗ WP Seq (Instr Executable) {{v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤}})
    ⊢ WP Seq (Instr Executable) {{v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤}}.
  Proof.
    iIntros (a_stk4 Hstk_shadow Hstk_heap Hmalformed Hdom Hrdom)
      "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1
       & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hpost)".
    assert ( exists wr0, rmap !! ct2 = Some wr0) as [wr0 Hwr0].
    { rewrite -/(is_Some (rmap !! ct2)).
      apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hregs") as "[Hct2 Hregs]"; first by simplify_map_eq.
    assert ( exists wr1, rmap !! ctp = Some wr1) as [wr1 Hwr1].
    { rewrite -/(is_Some (rmap !! ctp)).
      apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ctp with "Hregs") as "[Hctp Hregs]"; first by simplify_map_eq.

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.

    rewrite /switcher_instrs /assembled_switcher.
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }

    (* -----------------------------------  *)
    (* ----- Lswitch_csp_check_perm ------  *)
    (* -----------------------------------  *)
    focus_block_0 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_0_spec with
      "[- $HPC $Hctp $Hct2 $Hcsp $Hcode]"); eauto; iFrame; iNext.
    iIntros "(HPC & Hctp & Hct2 & Hcsp & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ------ Lswitch_csp_check_loc ------  *)
    (* -----------------------------------  *)
    focus_block 1 "Hcode" as a_csp_check_loc Ha_csp_check_loc "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_1_spec with
      "[- $HPC $Hctp $Hct2 $Hcsp $Hcode]"); eauto; iFrame; iNext.
    iIntros "(HPC & Hctp & Hct2 & Hcsp & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ---- Lswitch_entry_first_spill ----  *)
    (* -----------------------------------  *)
    focus_block 2 "Hcode" as a_entry_first_spill Ha_entry_first_spill "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_csp_check_loc.
    iApply (switcher_call_block_2_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hcsp $Hstk $Hcode]"); eauto; iNext.
    iIntros (stk_mem')
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hstk
        & %Hastk_bounds_all & %Hstk_mem' & Hcode)".
    destruct Hastk_bounds_all as [Hastk_bstk Hastk_bounds_all].
    destruct Hastk_bounds_all as [Hastk_bounds Hastk_some].
    destruct Hastk_some as [a_stk4' Hastk_some].
    subst stk_mem'.
    assert ((a_stk + 4)%a = Some a_stk4) as Hastk by
      (unfold a_stk4; rewrite (finz_incr_eq Hastk_some); exact Hastk_some).

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* --------------------------------------  *)
    (* ----- Lswitch_trusted_stack_push -----  *)
    (* --------------------------------------  *)
    focus_block 3 "Hcode" as a_tstack_push Ha_tstack_push "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_entry_first_spill.
    iApply (switcher_call_block_3_spec with
      "[- $HPC $Hcs0 $Hctp $Hct2 $Hcsp $Hmtdc $Htstk $Hcode]"); eauto using trusted_stack_disjoint_from_shadow.
    { solve_addr+Ha_tstack_push Hcont_switcher_region. }
    iNext.
    iIntros "[
      (%tstk_next' & HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc
        & Ha_tstk1 & Htstk & %Ha_tstk1_facts & %Htstk_next' & Hcode & Hlc)
      |
      (%Htskt & HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc & Htstk & Hcode)
    ]"
    ; [destruct Ha_tstk1_facts as [Ha_tstk2 Ha_tstk1_bound] | ]
    ; unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont
    ; cycle 1.
    {
      (* ----------------------------------------------  *)
      (* ------ Lswitch_trusted_stack_exhausted -------  *)
      (* ----------------------------------------------  *)
      iExtractList "Hargs" [ca0; ca1] as ["Hca0"; "Hca1"].

      focus_block 16 "Hcode" as a_tstk_exhausted Ha_tstk_exhausted "Hcode" "Hcls"; iHide "Hcls" as hcont.
      iApply (switcher_call_block_16_spec_general with
        "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp
          $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hcode]"); eauto.
      { solve_addr+Ha_tstk_exhausted Hcont_switcher_region. }
      iNext.
      iIntros (rcgp rcra rcs0 rcs1) "%Hrestored
        (HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hlc)".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      (* ---- clear registers  ---- *)
      focus_block 14 "Hcode" as a7 Ha7 "Hcode" "Hcls"; iHide "Hcls" as hcont.

      iExtractList "Hargs" [ca2; ca3; ca4; ca5; ct0]
        as ["Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
      iClear "Hargs".

      iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
      rewrite insert_delete_eq.
      rewrite -delete_insert_ne; last done.
      iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
      rewrite insert_delete_eq.
      iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hca2] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hca3] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hca4] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hca5] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hct0] Hregs") as "Hregs";[iFrame|].

      iApply (clear_registers_post_call_spec with "[- $HPC $Hregs $Hcode]"); try solve_pure.
      { clear -Hdom Hrdom.
        repeat (rewrite -delete_insert_ne //).
        repeat (rewrite dom_delete_L).
        repeat (rewrite dom_insert_L).
        rewrite Hdom /=.
        set_solver.
      }
      iNext; iIntros "H".
      iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Hrmap & Hcode)".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      focus_block 15 "Hcode" as a10 Ha10 "Hcode" "Hcsl"; iHide "Hcsl" as hcont.
      (* Jalr cnull cra *)
      iAssert (⌜map_Forall (λ (_ : RegName) (x : Word), x = WInt 0) arg_rmap' ⌝)%I as
        "%Harg_rmap'_zeroes".
      { iDestruct (big_sepM_sep with "Hrmap") as "[_ %]"; auto. }
      iExtract "Hrmap" cnull as "[Hcnull %]".
      iInstr "Hcode" with "Hlc".
      iAssert ( ∃ wnull, cnull ↦ᵣ wnull ∗ ⌜ wnull = WInt 0⌝ )%I with "[Hcnull]" as (wnull) "Hcnull".
      { iFrame; done. }
      iInsert "Hrmap" cnull.
      iAssert (⌜ <[cnull := wnull]> arg_rmap' = arg_rmap' ⌝)%I as "%Harg_rmap'_id".
      { iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hint]".
        iPureIntro.
        clear -Harg_rmap' Hint Harg_rmap'_zeroes.
        assert (is_Some (arg_rmap' !! cnull)) as [? Hcnull] by (rewrite -elem_of_dom Harg_rmap' ; set_solver).
        apply insert_id.
        pose proof (map_Forall_insert_1_1 _ _ _ _ Hint); cbn in *.
        rewrite H.
        rewrite Hcnull.
        by eapply map_Forall_lookup in Hcnull; eauto; cbn in *; simplify_map_eq.
      }
      rewrite Harg_rmap'_id.
      clear dependent Harg_rmap'_id Harg_rmap'_zeroes wcnull wnull.
      unfocus_block "Hcode" "Hcsl" as "Hcode"; subst hcont.

    (* Close the switcher's invariant *)
      iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hstk_interp]") as "HH".
      { iNext. iExists _,_. iFrame "∗ # %".
        iPureIntro; split; auto.
      }
      iEval (cbn) in "HPC".
      iEval (cbn) in "Hcra".
      iApply ("Hpost" $! _ rcgp rcra rcs0 rcs1 with "[-]"); iFrame "∗%".
      iSplit.
      { iPureIntro.
        split; first solve_addr+Hastk Hastk_bstk.
        split; first solve_addr+Hastk Hastk_bounds Hastk_bstk.
        done.
      }
      iApply region_pointsto_cons; eauto.
      { instantiate (1 := (a_stk ^+ 1)%a); solve_addr+Hastk. }
      { solve_addr+Hastk. }
      iFrame.
      iApply region_pointsto_cons; eauto.
      { instantiate (1 := (a_stk ^+ 2)%a); solve_addr+Hastk. }
      { solve_addr+Hastk. }
      iFrame.
      iApply region_pointsto_cons; eauto.
      { instantiate (1 := (a_stk ^+ 3)%a); solve_addr+Hastk. }
      { solve_addr+Hastk. }
      iFrame.
      iApply region_pointsto_cons; eauto.
      { instantiate (1 := (a_stk ^+ 4)%a); solve_addr+Hastk. }
      { solve_addr+Hastk. }
      iFrame.
      rewrite /region_pointsto.
      rewrite (finz_seq_between_empty a_stk4 a_stk4); last solve_addr.
      done.
    }
    subst tstk_next'.

    (* ------------------------------  *)
    (* ----- Lswitch_stack_chop -----  *)
    (* ------------------------------  *)
    focus_block 4 "Hcode" as a_stack_chop Ha_stack_chop "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_tstack_push.
    iApply (switcher_call_block_4_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcsp $Hcode]"); eauto; [|iNext].
    { rewrite /isWithin; solve_addr+Hastk_bounds. }
    iIntros "(HPC & Hcs0 & Hcs1 & Hcsp & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- Clear stack -----  *)
    (* -----------------------  *)
    focus_block 5 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_stack_chop.
    iApply (clear_stack_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hstk]"); try solve_pure.
    { solve_addr+. }
    { solve_addr. }
    { rewrite /disjoint_from_shadow elem_of_disjoint in Hstk_shadow |- *.
      intros x Hx Hshadow. eapply Hstk_shadow; last exact Hshadow.
      apply elem_of_finz_seq_between. apply elem_of_finz_seq_between in Hx.
      solve_addr. }
    iIntros "!> (HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- LoadCapPCC ------  *)
    (* -----------------------  *)
    focus_block 6 "Hcode" as a_LoadCapPCC Ha_LoadCapPCC "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear_stk1.
    iApply (switcher_call_block_6_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hb_switcher $Hcode]"); eauto using switcher_base_not_shadow; iNext.
    iIntros "(HPC & Hcs0 & Hcs1 & Hb_switcher & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ---- Lswitch_unseal_entry ----  *)
    (* ------------------------------  *)
    focus_block 7 "Hcode" as a_unseal_entry Ha_unseal_entry "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_LoadCapPCC.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_rules_interp.wp_unseal_unknown_sealed with "[$HPC $Hi $Hcs0 $Hct1]");
      try done; try solve_pure.
    iIntros "!>" (ret)
      "[-> |
       [(%o & %wsb & -> & HPC & Hi & Hcs0 & Hct1 & %Heq & %Htag & %Hrange)
       |(%ot & %sb & -> & HPC & Hi & Hcs0 & Hct1 & %Heq & %Hinvalid)]]".
    { wp_pure. wp_end. iIntros "%Hcontr"; done. }
    2: {
      simplify_eq.
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      iInstr "Hcode".
      wp_end; iIntros "%Hcontr"; done. }
    simplify_eq. rename wsb into w_entry_point.
    apply withinBounds_le_addr in Hrange.
    assert (o = ot_switcher) as -> by solve_addr.
    by rewrite /is_sealed_with_o Z.eqb_refl in Hmalformed.
  Qed.

End Switcher_Call_Failure.
