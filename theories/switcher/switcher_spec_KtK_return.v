From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import switcher_macros_spec.
From griotte Require Import switcher_return_states switcher_return_blocks_1 switcher_return_blocks_2.
From griotte Require Import map_simpl register_tactics proofmode.

(** * Return routine of the switcher, known-to-known calls

    The proof composes the block-group lemmas of [switcher_return_blocks_n],
    shared with [switcher_ret_specification_gen]. *)

Section Switcher_KtK_Return.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).


  Lemma switcher_cc_specification_return_known_to_known
    (Nswitcher : namespace)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wca0 wca1 : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (rmap : LReg)
    (cstk : CSTK)
    (b_callee_exp_tbl : Addr)
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
              b_callee_exp_tbl := b_callee_exp_tbl;
              ccrel := Known_to_Known
           |}
    in

    disjoint_from_heap b_stk e_stk ->
    disjoint_from_mmio b_stk e_stk ->

    (* NA mask *)
    ↑Nswitcher ⊆ E ->

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    (* NA token*)
    ∗ na_own cerise_nais E
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return
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
              ∗ ⌜ dom rmap' = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ⌝
              (* NA token*)
              ∗ na_own cerise_nais E
              (* Registers *)
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
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
    (* Outline of the proof:
       - open the switcher invariant, and read the topmost frame of the call
         stack;
       - [switcher_return_blocks_1_spec]: pop the trusted stack;
       - [switcher_return_blocks_2_spec]: restore the callee-save registers,
         clear the stack frame and the registers, and jump back to the
         caller; the frame records that the return address is a valid
         target, so the jump does not fault;
       - pop the frame and close the switcher invariant. *)
    intros astk4 frame; subst astk4.
    iIntros (Hstk_heap Hstk_mmio HE Hdom)
      "(#Hswitcher & #[Hcode _] & Hna & HPC & [%wcgp Hcgp] & [%wcra Hcra] & [%wcs0 Hcs0] & [%wcs1 Hcs1]
      & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk & Hpost)".

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    (* Read the topmost frame *)
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    rewrite /frame /cframe_interp; iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "(>Ha_tstk & >[%wtbl [Ha_tstk_tbl _]] & >[%ncnt Ha_tstk_cnt] & >%HWF
                                    & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3)".
    destruct HWF as (Hb_a4 & He_a1 & Ha_stk4 & _ & _ & Hret_ok).
    pose proof (switcher_stk_bounds_frame b_stk e_stk a_stk Hb_a4 He_a1 Ha_stk4) as Hstk_bounds.
    pose proof Hstk_bounds as (_ & _ & Ha4).
    iExtract "Hregs" ctp as "Hctp".
    iExtract "Hregs" ct0 as "Hct0".
    iExtract "Hregs" ct1 as "Hct1".
    iExtract "Hregs" ca2 as "Hca2".
    iExtract "Hregs" ct2 as "Hct2".

    (* Block 13: pop the trusted stack *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    iApply (switcher_return_blocks_1_spec with
      "[- $HPC $Hctp $Hct0 $Hct1 $Hct2 $Hcsp $Hmtdc $Hframeoffset $Ha_tstk $Hcode]");
      [done|done|done| |].
    { eapply disjoint_from_heap_not_in; first exact Hstk_heap.
      rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hct2 & Hcsp & Hmtdc & Hframeoffset & Ha_tstk
                    & _ & _)".
    iInsertRegs "Hregs" ["Hct2"].

    (* Blocks 13-16: restore, clear and return *)
    iAssert (switcher_stk_cells a_stk wcs0_caller wcs1_caller wcra_caller wcgp_caller)
      with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3]" as "Hcells".
    iApply (switcher_return_blocks_2_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hregs $Hcode]"); [done|done| |].
    { rewrite dom_insert_L. repeat (rewrite dom_delete_L). rewrite Hdom. set_solver. }
    iNext; iIntros (rmap' rcgp rcra rcs1 rcs0)
      "(%Hrestored & %Hrmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hregs & _ & _)".
    iSplit; cycle 1.
    { (* The return address of the caller is a valid target *)
      iIntros "%Hjalr".
      specialize (Hret_ok eq_refl) as [Hret_jalr Hret_heap].
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_nonheap in Hra; last done.
      subst rcra; congruence. }
    iIntros "[HPC _]".
    iDestruct (region_pointsto_split a_stk e_stk (a_stk ^+ 4)%a with "[$Hstk' $Hstk]") as "Hstk";
      [solve_addr | by rewrite /region_addrs_zeroes length_replicate |].
    assert (region_addrs_zeroes a_stk e_stk =
              region_addrs_zeroes a_stk (a_stk ^+ 4)%a ++ region_addrs_zeroes (a_stk ^+ 4)%a e_stk)
      as Hzeroes by (apply region_addrs_zeroes_split; solve_addr).
    iEval (rewrite -Hzeroes) in "Hstk".

    (* Pop the frame and close the switcher invariant *)
    iMod (cstack_update _ _ cstk with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod ("Hclose_switcher_inv"
           with "[$Hna Hmtdc Hsave_area Hframeoffset HthreadID Ha_tstk Ha_tstk_tbl Ha_tstk_cnt Htstk
                  Hcstk_full Hstk_interp_next]")
      as "Hna".
    { iNext.
      iApply (switcher_inv_pop_frame with
               "Hmtdc Hsave_area Hframeoffset HthreadID Ha_tstk Ha_tstk_tbl Ha_tstk_cnt Htstk
                Hcstk_full Hstk_interp_next Hp_ot_switcher"); done. }

    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1); iFrame.
    iPureIntro; split; first naive_solver. rewrite Hrmap'; set_solver.
  Qed.

End Switcher_KtK_Return.
