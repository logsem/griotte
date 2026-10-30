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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  (* TODO: move to switcher/code/clear_stack_spec.v *)
  (** Everything is zeroed from an address below the cells. *)
  Lemma stack_zeroed_from_below (b : Addr) (v : Z) (ws : list LWord) :
    (v <= b)%Z →
    stack_zeroed_from b v ws = replicate (length ws) (lword_of_word (WInt 0)).
  Proof.
    intros Hv. rewrite /stack_zeroed_from Z2Nat.nonpos; last lia.
    by rewrite take_0 Nat.sub_0_r.
  Qed.

  (* TODO: move to switcher/code/clear_stack_spec.v *)
  (** The cells of a stack region above MSHWMB and below MSHWM are cells of
      the zone, which hold 0: zeroing them from MSHWM zeroes them all. *)
  Lemma stack_region_below_hwm E (b e : Addr) (ws : list LWord) (hb h : Z) :
    (hb <= b)%Z →
    stack_region b e ws -∗
    hwm_regs hb h -∗
    |~{E}~>
    ⌜stack_zeroed_from b h ws = replicate (length ws) (lword_of_word (WInt 0))⌝ ∗
    stack_region b e ws ∗
    hwm_regs hb h.
  Proof.
    iInduction ws as [|w ws] "IH" forall (b); iIntros (Hhb) "Hstk Hhwm".
    { iModIntro. iFrame. iPureIntro. by rewrite /stack_zeroed_from take_nil. }
    destruct (decide (h <= b)%Z) as [Hh | Hh].
    { iModIntro. iFrame. iPureIntro. by apply stack_zeroed_from_below. }
    iDestruct (stack_region_length with "Hstk") as %Hlen.
    rewrite finz_seq_between_length /= in Hlen.
    assert (b < e)%a as Hbe by (rewrite /finz.dist in Hlen; solve_addr).
    destruct (b + 1)%a as [b'|] eqn:Hb'; last solve_addr.
    iDestruct (stack_region_cons b b' e with "Hstk") as "[[Hb | [Hb ->]] Hstk]"; [done|done|..].
    - (* A full points-to is outside the zone *)
      iDestruct "Hhwm" as "[Hhb Hh]".
      iMod (hwm_pointsto_outside with "Hb Hhb Hh") as "(%Hout & _)".
      exfalso; lia.
    - iMod ("IH" $! b' with "[%] Hstk Hhwm") as "(%Hz & Hstk & Hhwm)"; first solve_addr.
      iModIntro. iFrame "Hhwm".
      iSplit.
      + iPureIntro. revert Hz. rewrite /stack_zeroed_from.
        rewrite (_ : Z.to_nat (h - b) = S (Z.to_nat (h - b'))); last solve_addr.
        cbn. by intros ->.
      + iApply (stack_region_cons b b' e); [done|done|]. iFrame.
        by iApply stack_cell_of_zone.
  Qed.


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
    (h : Z)
    :
    let frame :=
           {| cf_tframe :=
                {| tf_csp := Cap RWL Local b_stk e_stk (stk_saved_a a_stk);
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
    (* The caller's stack starts at the floor *)
    b_stk = cstk_hwm_floor cstk ->

    (* NA mask *)
    ↑Ntstack ⊆ F ->

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ->

    (* Trusted-stack invariant *)
    na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    (* NA token*)
    ∗ na_own (tpool th) F
    (* Registers *)
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_return
    (* Callee-saved registers *)
    ∗ cgp ↦ᵣ[th] - ∗ cra ↦ᵣ[th] - ∗ cs0 ↦ᵣ[th] - ∗ cs1 ↦ᵣ[th] -
    (* Stack register, any word: the return routine reloads it *)
    ∗ csp ↦ᵣ[th] -
    (* Return values *)
    ∗ ca0 ↦ᵣ[th] wca0
    ∗ ca1 ↦ᵣ[th] wca1

    (* All the other registers *)
    ∗ regs[th] rmap

    (* Stack frame *)
    ∗ stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) stk_mem
    (* The high-water-mark registers *)
    ∗ hwm_res (cstack_push frame cstk) h

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ ◯(CSTK)[th] (cstack_push frame cstk)


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ rmap' rcgp rcra rcs0 rcs1,
            (
              ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ⌝
              (* NA token*)
              ∗ na_own (tpool th) F
              (* Registers *)
              ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ[th] rcgp ∗ cra ↦ᵣ[th] rcra ∗ cs0 ↦ᵣ[th] rcs0 ∗ cs1 ↦ᵣ[th] rcs1
              (* Stack register *)
              ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
              (* Return values *)
              ∗ ca0 ↦ᵣ[th] wca0
              ∗ ca1 ↦ᵣ[th] wca1
              (* All the other registers *)
              ∗ regs₀[th] rmap'

              (* Stack frame *)
              ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk)
                  (region_addrs_zeroes (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk))
              (* The high-water-mark registers, with MSHWM at the cursor *)
              ∗ hwm_res cstk a_stk

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ ◯(CSTK)[th] cstk

                -∗ safe[th]
            )
        )
    ⊢ safe[th].
  Proof.
    (* Outline of the proof:
       - open the trusted-stack invariant, and read the topmost frame of the call
         stack;
       - [switcher_return_path_spec]: pop the trusted stack, restore the
         callee-save registers, clear the stack frame and the registers,
         and jump back to the caller; the frame records that the return
         address is a valid target, so the jump does not fault;
       - pop the frame and close the trusted-stack invariant
         ([switcher_return_pop_close]). *)
    intros frame.
    iIntros (Hstk_heap Hstk_mmio Ha_stk4 Hfloor HE Hdom)
      "(#Hswitcher & #[Hcode _] & Hna & HPC & [%wcgp Hcgp] & [%wcra Hcra] & [%wcs0 Hcs0] & [%wcs1 Hcs1]
      & [%wcsp Hcsp] & Hca0 & Hca1 & Hregs & Hstk & Hhwm & Hcstk & Hpost)".
    (* The caller's stack starts at the floor: pushing its frame leaves the
       high-water-mark registers as they are *)
    rewrite hwm_res_push_ktk //.
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hhwm_ord & Hlocked) #Hts]".

    (* Open the trusted-stack invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed trusted_stack_inv_open "Hswitcher_inv".
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

    (* The spill area is at or above MSHWM, and the cells of the callee's
       stack below MSHWM hold 0 *)
    iDestruct "Hcells" as ">(Hc0 & Hc1 & Hc2 & Hc3)".
    iMod (hwm_pointsto_outside with "Hc0 Hmshwmb Hmshwm")
      as "(%Hspill_out & Hc0 & Hmshwmb & Hmshwm)".
    iMod (stack_region_below_hwm with "Hstk [$Hmshwmb $Hmshwm]")
      as "(%Hzero & Hstk & Hhwm_regs)".
    { rewrite /stk_callee_b. solve_addr. }

    (* Pop the trusted stack, restore, clear and return *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    iEval (rewrite switcher_return_block_13) in "HPC".
    iAssert (switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller)
      with "[$Hc0 $Hc1 $Hc2 $Hc3]" as "Hcells".
    pose proof Hstk_bounds as Hstk_bounds'.
    revert Hstk_bounds'; rewrite /switcher_stk_bounds; stk_unfold; intros (Hb_a4 & He_a1 & Ha4).
    iApply (switcher_return_path_spec (length cstk.(cstk_frames)) with
      "[- $HPC $Hcsp $Hcgp $Hcra $Hcs0 $Hcs1 $Hregs $Hmtdc $Hframeoffset $Hhazard $Htf_csp $Hcells $Hstk
        $Hhwm_regs $Hcode]"); [done|done|done|done|done|done| |].
    { split; [solve_addr | solve_addr]. }
    iNext. iSplit; cycle 1.
    { (* MSHWM is at or above the floor, the base of the caller's stack: the
         zeroing does not fault *)
      iIntros (rmap0 rcgp rcra rcs1 rcs0 off) "(_ & %Hhb & _)". exfalso. solve_addr. }
    iIntros (rmap' rcgp rcra rcs1 rcs0)
      "(%Hrestored & %Hbh & %Hrmap' & Hmtdc & Hframeoffset & Hhazard & Htf_csp & Hcra & Hcgp & Hcs0
      & Hcs1 & Hcsp & Hstk' & Hstk & Hhwm_regs & Hregs)".
    iSplit; cycle 1.
    { (* The return address of the caller is a valid target *)
      iIntros "%Hjalr".
      specialize (Hret_ok eq_refl) as [Hret_jalr Hret_heap].
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_nonheap in Hra; last done.
      subst rcra; congruence. }
    iIntros "[HPC _]".

    (* The free part of the caller's stack holds 0 *)
    stk_unfold.
    iEval (rewrite Hzero) in "Hstk".
    iEval (rewrite stack_zeroed_from_below; last solve_addr) in "Hstk'".
    iDestruct (stack_region_length with "Hstk") as %Hlen_stk.
    rewrite finz_seq_between_length length_replicate in Hlen_stk.
    iAssert (stack_region b_stk a_stk (region_addrs_zeroes b_stk a_stk))
      with "[Hstk Hstk']" as "Hstk".
    { rewrite (_ : (a_stk ^- 4) ^+ SpillSlot_size = a_stk);
        last (rewrite /SpillSlot_size; solve_addr).
      rewrite /region_addrs_zeroes (_ : finz.dist b_stk a_stk = length stk_mem + 4);
        last (rewrite /finz.dist in Hlen_stk |- *; solve_addr).
      rewrite replicate_add.
      iApply (stack_region_app b_stk (a_stk ^- 4) a_stk);
        [solve_addr | solve_addr | by rewrite length_replicate |].
      iFrame. }

    (* Pop the frame and close the trusted-stack invariant *)
    subst hclose_switcher_inv.
    iMod (switcher_return_pop_close F _ cstk with
           "Hclose_switcher_inv Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htf_csp Htf_tbl
            Htf_cnt Htstk Hcstk_full Hcstk Hstk_interp_next")
      as "[Hna Hcstk]"; [done|done|done|].

    iDestruct "Hhwm_regs" as "[Hmshwmb Hmshwm]".
    iApply ("Hpost" $! rmap' rcgp rcra rcs0 rcs1).
    iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hregs Hstk Hcstk Hmshwmb Hmshwm Hlocked Hts".
    iSplit; [iPureIntro; naive_solver|].
    iSplit; [iPureIntro; rewrite Hrmap'; set_solver|].
    iPureIntro; split; solve_addr.
  Qed.

  Lemma switcher_cc_specification_return_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wca0 wca1 : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (rmap : LReg)
    (cstk : CSTK)
    (w_callee_exp_tbl : LWord)
    (F : coPset)
    (h : Z)
    :
    let frame :=
           {| cf_tframe :=
                {| tf_csp := Cap RWL Local b_stk e_stk (stk_saved_a a_stk);
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
    (* The caller's stack starts at the floor *)
    b_stk = cstk_hwm_floor cstk ->

    (* NA mask *)
    ↑Ntstack ⊆ F ->

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ->

    (* Trusted-stack invariant *)
    na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    (* NA token*)
    ∗ na_own (tpool th) F
    (* Registers *)
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_return
    (* Callee-saved registers *)
    ∗ cgp ↦ᵣ[th] - ∗ cra ↦ᵣ[th] - ∗ cs0 ↦ᵣ[th] - ∗ cs1 ↦ᵣ[th] -
    (* Stack register *)
    ∗ csp ↦ᵣ[th] callee_csp b_stk e_stk a_stk
    (* Return values *)
    ∗ ca0 ↦ᵣ[th] wca0
    ∗ ca1 ↦ᵣ[th] wca1

    (* All the other registers *)
    ∗ regs[th] rmap

    (* Stack frame *)
    ∗ stack_region (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) stk_mem
    (* The high-water-mark registers *)
    ∗ hwm_res (cstack_push frame cstk) h

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ ◯(CSTK)[th] (cstack_push frame cstk)


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ rmap' rcgp rcra rcs0 rcs1,
            (
              ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ ({[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]}) ⌝
              (* NA token*)
              ∗ na_own (tpool th) F
              (* Registers *)
              ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ[th] rcgp ∗ cra ↦ᵣ[th] rcra ∗ cs0 ↦ᵣ[th] rcs0 ∗ cs1 ↦ᵣ[th] rcs1
              (* Stack register *)
              ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
              (* Return values *)
              ∗ ca0 ↦ᵣ[th] wca0
              ∗ ca1 ↦ᵣ[th] wca1
              (* All the other registers *)
              ∗ regs₀[th] rmap'

              (* Stack frame *)
              ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk)
                  (region_addrs_zeroes (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk))
              (* The high-water-mark registers, with MSHWM at the cursor *)
              ∗ hwm_res cstk a_stk

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ ◯(CSTK)[th] cstk

                -∗ safe[th]
            )
        )
    ⊢ safe[th].
  Proof.
    intros frame.
    iIntros (Hstk_heap Hstk_mmio Ha_stk4 Hfloor HE Hdom)
      "(Hswitcher & Hstatic & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1
      & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hhwm & Hcstk & Hpost)".
    iApply (switcher_cc_specification_return_known_to_known_gen with
             "[$Hswitcher $Hstatic $Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1 $Hcsp $Hca0 $Hca1 $Hregs
               $Hstk $Hhwm $Hcstk $Hpost]"); done.
  Qed.

End Switcher_KtK_Return.
