From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import switcher_macros_spec switcher_spec_return_blocks switcher_load_spec.
From griotte Require Import map_simpl register_tactics proofmode.


Section Switcher_KtK_Return.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).


  (** Return borrows the current shadow entries from the allocator. Each
      restored register satisfies [load_heap] for its saved word. *)
  Lemma switcher_cc_specification_return_known_to_known
    (Nswitcher : namespace)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wca0 wca1 : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (rmap : Reg)
    (cstk : CSTK)
    (E : coPset)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let frame :=
           {| wret := wcra_caller;
              wcgp := wcgp_caller;
              wcs0 := wcs0_caller;
              wcs1 := wcs1_caller;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Known
           |}
    in

    disjoint_from_heap b_stk e_stk ->
    disjoint_from_shadow b_stk e_stk ->

    (* NA mask *)
    ↑Nswitcher ⊆ E ->

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ->

    (* Switcher Invariant *)
    allocator_ctx ∗ na_inv cerise_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    (* NA token*)
    ∗ na_own cerise_nais E
    (* Registers *)
    ∗ PC ↦ᵣ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return
    (* Callee-saved registers *)
    ∗ cgp ↦ᵣ - ∗ cra ↦ᵣ - ∗ cs0 ↦ᵣ - ∗ cs1 ↦ᵣ -
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local a_stk4 e_stk a_stk4
    (* Return values *)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1

    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ cstack_frag (frame::cstk)


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ rmap' rcgp rcra rcs0 rcs1,
            (
              ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ⌝
              (* NA token*)
              ∗ na_own cerise_nais E
              (* Registers *)
              ∗ PC ↦ᵣ updatePcPerm (rcra)
              ∗ cgp ↦ᵣ rcgp ∗ cra ↦ᵣ rcra ∗ cs0 ↦ᵣ rcs0 ∗ cs1 ↦ᵣ rcs1
              (* Stack register *)
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              (* Return values *)
              ∗ ca0 ↦ᵣ wca0
              ∗ ca1 ↦ᵣ wca1
              (* All the other registers *)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )

              (* Stack frame *)
              ∗ ([[ a_stk , e_stk ]] ↦ₐ [[region_addrs_zeroes a_stk e_stk]])

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ cstack_frag cstk

                -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
            )
        )
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros astk4 frame.
    iIntros (Hstk_heap Hstk_shadow HE Hdom)
      "(#Halloc & #Hswitcher & Hna & HPC & [%wcgp Hcgp] & [%wcra Hcra] & [%wcs0 Hcs0] & [%wcs1 Hcs1]
      & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk & Hpost)".

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".

    set (Hret := switcher_return_entry_point).
    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    rewrite {2}/switcher_instrs.
    assert (SubBounds b_switcher e_switcher a_switcher_return (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.


    codefrag_facts "Hcode".
    rewrite /switcher_instrs /assembled_switcher.
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    focus_block_nochangePC 12 "Hcode" as a_ret Ha_ret "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.
    replace a_switcher_return with a_ret by solve_addr.

    iExtract "Hregs" ctp as "Hctp".
    iExtract "Hregs" ct0 as "Hct0".
    iExtract "Hregs" ct1 as "Hct1".

    (* --- ReadSR ctp mtdc --- *)
    iInstr "Hcode".

    (* --- Load csp ctp --- *)
    destruct (decide (a_tstk < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    {
      iInstr "Hcode".
      wp_end; by iIntros (?).
    }

    iDestruct (cstack_agree with "Hcstk_full [$]") as %Heq; subst cstk'.

    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    rewrite /frame /cframe_interp; iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "[Ha_tstk Hcframe_interp]".
    iDestruct "Hcframe_interp" as "(%HWF & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3)".
    rewrite -/(cstack_interp cstk (a_tstk ^+ -1)%a).
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4] & _).


    assert (is_shadow_address a_tstk = false) as Hatstk_shadow.
    { eapply disjoint_from_shadow_not_in; first exact trusted_stack_disjoint_from_shadow.
      rewrite /withinBounds; solve_addr. }
    assert (is_heap_address b_stk = false) as Hbstk_nonheap.
    { apply not_true_is_false. intros Hheap.
      apply withinBounds_true_iff in Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hstk_heap.
      eapply (Hstk_heap b_stk); apply elem_of_finz_seq_between; [solve_addr|exact Hheap]. }
    iInstr "Hcode".

    (* --- Lea ctp -1 --- *)
    assert (is_Some (a_tstk + -1))%a as [a_tstk1 Ha_tstk1].
    { cbn in Hlen_cstk. solve_addr+Hlen_cstk. }
    iInstr "Hcode".
    replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.

    (* --- WriteSR mtdc ctp --- *)
    iInstr "Hcode".

    (* --- Lea csp -1 --- *)
    iInstr "Hcode" with "Hlc".

    iApply (switcher_return_block_12_restore_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Halloc $Hcode]"); eauto.
    iNext. iIntros (rcgp rcra rcs1 rcs0) "%Hrestored
      (HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hlc_restore)".
    iCombine "Hlc Hlc_restore" as "Hlc".
    iDestruct "Hlc" as "[Hlc Hlc']".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    (* -------- CLEAR STACK --------- *)
    focus_block 13 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iAssert ([[ a_stk , e_stk ]] ↦ₐ [[wcs0_caller :: wcs1_caller :: wcra_caller :: wcgp_caller :: stk_mem]])%I
      with "[Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hstk]" as "Hstk".
    {
      subst astk4.
      iDestruct (region_pointsto_cons with "[$Ha_stk3 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk2 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iFrame.
    }

    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto; [solve_addr|].
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* -------- CLEAR REGISTERS --------- *)
    focus_block 14 "Hcode" as a9 Ha9 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInsertList "Hregs" [ct1;ct0;ctp].

    iApply (clear_registers_post_call_spec with "[- $HPC $Hregs $Hcode]"); try solve_pure.
    { clear -Hdom.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      rewrite Hdom.
      set_solver.
    }
    iNext; iIntros "H".
    iDestruct "H" as (rmap') "(%Hrmap' & HPC & Hregs & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 15 "Hcode" as a10 Ha10 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Jalr cnull cra *)
    iAssert (⌜map_Forall (λ (_ : RegName) (x : Word), x = WInt 0) rmap' ⌝)%I as
      "%Hrmap'_zeroes".
    { iDestruct (big_sepM_sep with "Hregs") as "[_ %]"; auto. }
    iExtract "Hregs" cnull as "[Hcnull %]".
    iInstr "Hcode" with "Hlc".
    iAssert ( ∃ wnull, cnull ↦ᵣ wnull ∗ ⌜ wnull = WInt 0⌝ )%I with "[Hcnull]" as (wnull) "Hcnull".
    { iFrame; done. }
    iInsert "Hregs" cnull.
    iAssert (⌜ <[cnull := wnull]> rmap' = rmap' ⌝)%I as "%Hrmap'_id".
    { iDestruct (big_sepM_sep with "Hregs") as "[Hregs %Hint]".
      iPureIntro.
      clear -Hrmap' Hint Hrmap'_zeroes.
      assert (is_Some (rmap' !! cnull)) as [? Hcnull] by (rewrite -elem_of_dom Hrmap' ; set_solver).
      apply insert_id.
      pose proof (map_Forall_insert_1_1 _ _ _ _ Hint); cbn in *.
      rewrite H.
      rewrite Hcnull.
      by eapply map_Forall_lookup in Hcnull; eauto; cbn in *; simplify_map_eq.
    }
    rewrite Hrmap'_id.
    clear dependent Hrmap'_id Hrmap'_zeroes wcnull wnull.
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    (* Update the call-stack: depop the topmost frame *)
    iDestruct (cstack_update _ _ cstk with "[$] [$]") as ">[Hcstk_full Hcstk_frag]".


    (* Close the switcher's invariant *)
    iDestruct (region_pointsto_cons with "[$Ha_tstk $Htstk]") as "Htstk"; [solve_addr| solve_addr| ].
    iMod ("Hclose_switcher_inv"
           with "[Hstk_interp_next $Hna $Hmtdc $Hcode $Hb_switcher Htstk $Hcstk_full $Hp_ot_switcher]")
      as "Hna".
    {
      replace (a_tstk1 ^+ 1)%a with a_tstk by solve_addr.
      replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.
      iFrame.
      iNext.
      iSplit; first (iPureIntro; done).
      iSplit; first (iPureIntro; solve_addr+Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Ha_tstk1).
      iPureIntro; solve_addr+Hbounds_tstk_b  Hlen_cstk Ha_tstk1.
    }

    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1); iFrame "∗ # %".
    iPureIntro. tauto.
  Qed.


End Switcher_KtK_Return.
