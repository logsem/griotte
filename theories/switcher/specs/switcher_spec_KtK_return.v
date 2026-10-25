From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import switcher_macros_spec.
From griotte Require Import switcher_return_states.
From griotte.switcher.callback Require Import callback_path.
From griotte Require Import map_simpl register_tactics proofmode.

(** * Return routine of the switcher, known-to-known calls

    The proof composes the block and path lemmas of [callback/],
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


  (** The return to a known caller: the stack pointer can hold any word,
      since the return routine reloads it from the frame, and the frame may
      have any error handler count [n_cnt]. *)
  Lemma switcher_cc_specification_return_known_to_known_gen
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wca0 wca1 : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (rmap : LReg)
    (cstk : CSTK)
    (w_callee_exp_tbl : LWord)
    (F : coPset)
    (n_cnt : Z)
    :
    let frame :=
           {| cf_tframe :=
                {| tf_csp := WCap true RWL Local b_stk e_stk (stk_saved_a a_stk);
                   tf_export_tbl := w_callee_exp_tbl;
                   tf_error_count := n_cnt |};
              cf_saved :=
                {| cs_cra := wcra_caller;
                   cs_cgp := wcgp_caller;
                   cs_cs0 := wcs0_caller;
                   cs_cs1 := wcs1_caller |};
              ccrel := Known_to_Known
           |}
    in

    disjoint_from_heap b_stk e_stk ->
    disjoint_from_mmio b_stk e_stk ->
    (* The switcher spilled the callee-saved registers of the caller at the
       cursor [a_stk] *)
    stk_spill_ok a_stk ->

    (* NA mask *)
    ↑Nswitcher ⊆ F ->

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    (* NA token*)
    ∗ na_own cerise_nais F
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return
    (* Callee-saved registers *)
    ∗ cgp ↦ᵣ - ∗ cra ↦ᵣ - ∗ cs0 ↦ᵣ - ∗ cs1 ↦ᵣ -
    (* Stack register, any word: the return routine reloads it *)
    ∗ csp ↦ᵣ -
    (* Return values *)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1

    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ cstack_frag (cstack_push frame cstk)


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ rmap' rcgp rcra rcs0 rcs1,
            (
              ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ⌝
              (* NA token*)
              ∗ na_own cerise_nais F
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
              ∗ ([[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ
                   [[region_addrs_zeroes (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk)]])

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
       - [switcher_return_path_spec]: pop the trusted stack, restore the
         callee-save registers, clear the stack frame and the registers,
         and jump back to the caller; the frame records that the return
         address is a valid target, so the jump does not fault;
       - pop the frame and close the switcher invariant
         ([switcher_return_pop_close]). *)
    intros frame.
    iIntros (Hstk_heap Hstk_mmio Ha_stk4 HE Hdom)
      "(#Hswitcher & #[Hcode _] & Hna & HPC & [%wcgp Hcgp] & [%wcra Hcra] & [%wcs0 Hcs0] & [%wcs1 Hcs1]
      & [%wcsp Hcsp] & Hca0 & Hca1 & Hregs & Hstk & Hcstk & Hpost)".

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
    iDestruct (switcher_hazard_open with "Hsave_area Hhazard_slots") as "[Hhazard Hsave_area]";
      first done.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    (* Read the topmost frame *)
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iEval (rewrite /cstack_interp; cbn) in "Hstk_interp".
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    rewrite /frame /cframe_interp.
    iDestruct "Hcframe_interp" as "[>Hcframe_top Hcframe_interp]".
    iNamed "Hcframe_top". iNamed "Hcf_tframe".
    iDestruct "Htf_tbl" as (wtbl) "[Htf_tbl _]".
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "(%b_stk' & %e_stk' & %a_stk' & >%HWF & Hcells)".
    destruct HWF as (Hcsp & Hstk_bounds & _ & _ & Hret_ok).
    apply lword_of_word_inj in Hcsp. injection Hcsp as Hb He Ha. subst b_stk' e_stk'.
    assert (a_stk' = a_stk) as ->.
    { pose proof Hstk_bounds as (_ & _ & Ha4'). revert Ha Ha4' Ha_stk4. stk_unfold.
      intros Ha Ha4' Ha_stk4. solve_addr+Ha Ha_stk4 Ha4'. }
    (* Pop the trusted stack, restore, clear and return *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    iEval (rewrite switcher_return_block_13) in "HPC".
    iApply (switcher_return_path_spec (length cstk.(cstk_frames)) with
      "[- $HPC $Hcsp $Hcgp $Hcra $Hcs0 $Hcs1 $Hregs $Hmtdc $Hframeoffset $Hhazard $Htf_csp $Hcells $Hstk
        $Hcode]"); [done|done|done|done|done|done|].
    iIntros "!>" (rmap' rcgp rcra rcs1 rcs0)
      "(%Hrestored & %Hrmap' & Hmtdc & Hframeoffset & Hhazard & Htf_csp & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp
      & Hstk' & Hstk & Hregs)".
    iSplit; cycle 1.
    { (* The return address of the caller is a valid target *)
      iIntros "%Hjalr".
      specialize (Hret_ok eq_refl) as [Hret_jalr Hret_heap].
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_nonheap in Hra; last done.
      subst rcra; congruence. }
    iIntros "[HPC _]".
    iDestruct (stk_free_split_join with "[$Hstk' $Hstk]") as "Hstk"; first done.
    { rewrite /region_addrs_zeroes length_replicate.
      revert Hstk_bounds; rewrite /switcher_stk_bounds; stk_unfold;
        intros (Hb_a4 & He_a1 & Ha4).
      rewrite /finz.dist. solve_addr. }
    iEval (rewrite -(stk_free_split_zeroes _ _ _ Hstk_bounds)) in "Hstk".

    (* Pop the frame and close the switcher invariant *)
    subst hclose_switcher_inv.
    iMod (switcher_return_pop_close F _ cstk with
           "Hclose_switcher_inv Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htf_csp Htf_tbl
            Htf_cnt Htstk Hcstk_full Hcstk Hstk_interp_next Hp_ot_switcher")
      as "[Hna Hcstk]"; [done|done|done|done|].

    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1).
    iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hregs Hstk Hcstk".
    iPureIntro; split; first naive_solver. rewrite Hrmap'; set_solver.
  Qed.

  Lemma switcher_cc_specification_return_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wca0 wca1 : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (rmap : LReg)
    (cstk : CSTK)
    (w_callee_exp_tbl : LWord)
    (F : coPset)
    :
    let frame :=
           {| cf_tframe :=
                {| tf_csp := WCap true RWL Local b_stk e_stk (stk_saved_a a_stk);
                   tf_export_tbl := w_callee_exp_tbl;
                   tf_error_count := 0 |};
              cf_saved :=
                {| cs_cra := wcra_caller;
                   cs_cgp := wcgp_caller;
                   cs_cs0 := wcs0_caller;
                   cs_cs1 := wcs1_caller |};
              ccrel := Known_to_Known
           |}
    in

    disjoint_from_heap b_stk e_stk ->
    disjoint_from_mmio b_stk e_stk ->
    (* The switcher spilled the callee-saved registers of the caller at the
       cursor [a_stk] *)
    stk_spill_ok a_stk ->

    (* NA mask *)
    ↑Nswitcher ⊆ F ->

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    (* NA token*)
    ∗ na_own cerise_nais F
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return
    (* Callee-saved registers *)
    ∗ cgp ↦ᵣ - ∗ cra ↦ᵣ - ∗ cs0 ↦ᵣ - ∗ cs1 ↦ᵣ -
    (* Stack register *)
    ∗ csp ↦ᵣ callee_csp b_stk e_stk a_stk
    (* Return values *)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1

    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ cstack_frag (cstack_push frame cstk)


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ rmap' rcgp rcra rcs0 rcs1,
            (
              ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ⌝
              (* NA token*)
              ∗ na_own cerise_nais F
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
              ∗ ([[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ
                   [[region_addrs_zeroes (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk)]])

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ cstack_frag cstk

                -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
            )
        )
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros frame.
    iIntros (Hstk_heap Hstk_mmio Ha_stk4 HE Hdom)
      "(Hswitcher & Hstatic & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1
      & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk & Hpost)".
    iApply (switcher_cc_specification_return_known_to_known_gen with
             "[$Hswitcher $Hstatic $Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hregs
               $Hstk $Hcstk $Hpost]"); done.
  Qed.

End Switcher_KtK_Return.
