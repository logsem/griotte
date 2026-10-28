From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import switcher_macros_spec.
From griotte Require Import switcher_call_states switcher_call_world.
From griotte.switcher.call Require Import call_path.
From griotte Require Import map_simpl register_tactics proofmode.

(** * Call routine of the switcher, known-to-known calls

    The proof composes the block and path lemmas of [call/],
    shared with [switcher_cc_specification_gen]. The caller and the callee
    are both known: the entry point is the sealed capability of a known
    export table, and the arguments are not required to be valid. *)

Section Switcher_KtK_Call.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  (** Failure path of [switcher_cc_specification_known_to_known]: the
      trusted stack is exhausted. *)
  Lemma switcher_cc_spec_tstack_exhausted_known_to_known
    (F : coPset)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller wct2 wctp : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk cstk' : CSTK)
    (a_tstk : Addr) (save_area tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    disjoint_from_mmio b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    (b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->
    save_area !! Z.to_nat TrustedStack_offset_hazardPointers = Some (lword_of_word hazard_slots_cap) ->
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (▷ switcher_inv ∗ na_own (tpool th) (F ∖ ↑Nswitcher) ={⊤}=∗ na_own (tpool th) F) ∗
    na_own (tpool th) (F ∖ ↑Nswitcher) ∗
    mtdc ↦ₜ[th] TStack (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) ∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
    (∃ ws, [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ [[ ws ]]) ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
    (∃ w, a_threadID ↦ₐ w) ∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_static ∗
    ●(CSTK)[th] cstk' ∗
    cstack_interp cstk' a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0, cs0 ↦ᵣ[th] wcs0) ∗
    (∃ wcs1, cs1 ↦ᵣ[th] wcs1) ∗
    cgp ↦ᵣ[th] wcgp_caller ∗
    cra ↦ᵣ[th] wcra_caller ∗
    ctp ↦ᵣ[th] wctp ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ct1 ↦ᵣ[th] wct1_caller ∗
    csp ↦ᵣ[th] WCap true RWL Local b_stk e_stk (stk_saved_a a_stk) ∗
    switcher_stk_cells (stk_spill_a a_stk) wcs0_caller wcs1_caller wcgp_caller wcra_caller ∗
    [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_callee stk_mem ]] ∗
    ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ) ∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), r ↦ᵣ[th] w ) ∗
    ◯(CSTK)[th] cstk ∗
    ▷ ( ( ∃ rmap' stk_mem' rcgp rcra rcs0 rcs1,
            ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
            na_own (tpool th) F ∗
            PC ↦ₚ[th] lupdatePcPerm rcra ∗
            cgp ↦ᵣ[th] rcgp ∗
            cra ↦ᵣ[th] rcra ∗
            csp ↦ᵣ[th] WCap true RWL Local b_stk e_stk a_stk ∗
            cs0 ↦ᵣ[th] rcs0 ∗
            cs1 ↦ᵣ[th] rcs1 ∗
            ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK ∗
            ca1 ↦ᵣ[th] WInt 0 ∗
            ( [∗ map] r↦w ∈ rmap', r ↦ᵣ[th] w ∗ ⌜ w = WInt 0 ⌝ ) ∗
            [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem' ]] ∗
            ◯(CSTK)[th] cstk ∗
            ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
              load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝ )
        -∗ WP Seq (Instr Executable) @[th] {{ HO th }} )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next.
    subst a_frameoffset a_save_end a_threadID a_next.
    (* Outline of the proof: [switcher_cc_exhausted_regs] collects the
       registers, [switch_trusted_stack_exhausted_path_spec] restores the
       registers, clears the others and returns, then close the switcher
       invariant. The return address is a valid
       target, so the jump back does not fault. *)
    iIntros (Hstk_mmio Hdom Hrdom Hstk_bounds Hlen_cstk Ha_tstk_e Hot_bounds Hsave_hazard Hret_jalr
             Hret_heap)
      "(Hclose_switcher_inv & Hna & Hmtdc & Hsave_area & Hhazard_slots & Hframeoffset & HthreadID
      & Htstk & #Hstatic & Hcstk_full & Hstk_interp
      & #Hp_ot_switcher & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hctp & Hct2 & Hct1 & Hcsp & Hcells & Hstk
      & Hargs & Hregs & Hcstk & Hpost)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    stk_unfold. change (4 - 1)%Z with 3%Z in Hastk_bounds.
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iApply (switch_trusted_stack_exhausted_path_spec with
      "[- $HPC $Hcsp $Hcells $Hrmap0 $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1]");
      [done|done|done|].
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "(%Hrestored & %Hrmap' & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp & Hcells & Hrmap & _)".
    iSplit; cycle 1.
    { (* The return address of the caller is a valid target *)
      iIntros "%Hjalr".
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_nonheap in Hra; last done.
      subst rcra; congruence. }
    iIntros "[HPC _]".
    iMod ("Hclose_switcher_inv" with
      "[$Hna $Hcstk_full Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Htstk Hstk_interp]")
      as "Hna".
    { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; first done.
    iApply "Hpost"; iFrame.
    iPureIntro; split; last done. rewrite Hrmap'; set_solver.
  Qed.

  Lemma switcher_cc_specification_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK)
    (nargs minstk_tgt : nat)
    (F : coPset)

    (btbl_tgt atbl_tgt etbl_tgt : Addr)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z) (posture_tgt : InterruptStatus)

    :
    let a_tbl_cgp := (btbl_tgt ^+ ExportTable_offset_cgp)%a in
    let a_tbl_ehs := (btbl_tgt ^+ ExportTable_offset_errorHandlerStackless)%a in
    let wct1_caller := WSealed ot_switcher (SCap true RO Global btbl_tgt etbl_tgt atbl_tgt) in
    let frame :=
           {| cf_tframe :=
                {| tf_csp := WCap true RWL Local b_stk e_stk (stk_saved_a a_stk);
                   tf_export_tbl := WCap true RO Global btbl_tgt etbl_tgt atbl_tgt;
                   tf_error_count := 0 |};
              cf_saved :=
                {| cs_cra := wcra_caller;
                   cs_cgp := wcgp_caller;
                   cs_cs0 := wcs0_caller;
                   cs_cs1 := wcs1_caller |};
              ccrel := Known_to_Known
           |}
    in

    disjoint_from_mmio b_stk e_stk ->
    is_shadow_address atbl_tgt = false ->
    is_shadow_address btbl_tgt = false ->
    is_shadow_address a_tbl_cgp = false ->
    disjoint_from_shadow btbl_tgt etbl_tgt ->
    is_heap_address bpcc_tgt = false ->
    is_heap_address bcgp_tgt = false ->

    (* (* NA mask *) *)
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    ↑Nswitcher ⊆ F ->

    (* Well formed entry point *)
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a →
    (btbl_tgt < a_tbl_cgp)%a →
    (a_tbl_ehs < atbl_tgt)%a  →
    (0 <= nargs <= 7 )%nat →
    is_Some (bpcc_tgt + off_tgt)%a →
    (* The callee's stack is at least its minimum stack size plus the
       reserved space *)
    stk_callee_fits b_stk e_stk a_stk minstk_tgt →

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (* Switcher Invariant *)
    na_inv (tpool th) Nswitcher switcher_inv
    ∗ switcher_static

    (* Export table of the target compartment *)
    ∗ btbl_tgt ↦ₐ□ WCap true RX Global bpcc_tgt epcc_tgt bpcc_tgt
    ∗ a_tbl_cgp ↦ₐ□ WCap true RW Global bcgp_tgt ecgp_tgt bcgp_tgt
    ∗ atbl_tgt ↦ₐ□ WInt (encode_entry_point posture_tgt (Z.of_nat nargs) (Z.of_nat minstk_tgt) off_tgt)


    (* PRE-CONDITION *)
    ∗ na_own (tpool th) F
    (* Registers *)
    ∗ PC ↦ₚ[th] WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ[th] wcgp_caller
    ∗ cra ↦ᵣ[th] wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ[th] WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ[th] wct1_caller
    ∗ cs0 ↦ᵣ[th] wcs0_caller
    ∗ cs1 ↦ᵣ[th] wcs1_caller
    (* All the other registers *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg )
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w )

    (* Stack frame *)
    ∗ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ ◯(CSTK)[th] cstk


    ∗ ▷ ( (∃ mie arg_rmap' rmap',
            ⌜ is_arg_rmap arg_rmap' 8 ⌝
            ∗ ⌜ dom rmap' = dom rmap ∪ {[ ct1 ; cs0 ; cs1 ]} ⌝
            ∗ na_own (tpool th) F
            (* Registers *)
            ∗ PC ↦ₚ[th] WCap true RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a
            ∗ cgp ↦ᵣ[th] WCap true RW Global bcgp_tgt ecgp_tgt bcgp_tgt
            ∗ cra ↦ᵣ[th] (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return)
            (* Stack register *)
            ∗ csp ↦ᵣ[th] callee_csp b_stk e_stk a_stk
            (* All the other registers *)
            (* Entry point of the target compartment *)
            ∗ ( [∗ map] rarg↦warg ∈ arg_rmap', rarg ↦ᵣ[th] warg
                                               ∗ (if decide (rarg ∈ dom_arg_rmap nargs)
                                                  then ⌜ arg_rmap !! rarg = Some warg ⌝
                                                  else ⌜warg = WInt 0⌝)
              )
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ[th] w ∗ ⌜ w = WInt 0 ⌝ )

            (* Stack frame *)
            ∗ ([[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ
                 [[region_addrs_zeroes (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk)]])

            (* Interpretation of the world and stack, at the moment of the switcher_call *)
            ∗ ◯(CSTK)[th] (cstack_push frame cstk)
          )
          ∨
          (
            ∃ rmap' stk_mem' rcgp rcra rcs0 rcs1,
              ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ na_own (tpool th) F
              (* Registers *)
              ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ[th] rcgp
              ∗ cra ↦ᵣ[th] rcra
              ∗ csp ↦ᵣ[th] WCap true RWL Local b_stk e_stk a_stk
              ∗ cs0 ↦ᵣ[th] rcs0
              ∗ cs1 ↦ᵣ[th] rcs1
              ∗ ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ[th] WInt 0
              (* All the other registers *)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ[th] w ∗ ⌜ w = WInt 0 ⌝ )

              (* Stack frame *)
              ∗ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[stk_mem']]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ ◯(CSTK)[th] cstk
              ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                  load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
          )
         -∗ WP Seq (Instr Executable) @[th] {{ HO th }}
        )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - [switcher_call_path_spec]: check the stack pointer, spill the
         callee-save registers, push the frame, clear the callee's stack and
         unseal the entry point; the spill fits on the caller's stack, which
         is at least the callee's minimum stack size plus the reserved space,
         and the entry point is sealed by the switcher; when the trusted
         stack is exhausted, [switcher_cc_spec_tstack_exhausted_known_to_known];
       - [switcher_decode_entry_path_known_spec]: load the callee and jump to it;
         its stack is at least its minimum stack size plus the reserved space,
         so the check passes;
       - [switcher_inv_push_frame]: push the frame and close the switcher
         invariant. *)
    intros a_tbl_cgp a_tbl_ehs wct1_caller frame.
    subst a_tbl_cgp a_tbl_ehs.
    iIntros (Hstk_mmio Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow Htbl_shadow Hbpcc_heap Hbcgp_heap Hstk_heap
             Hb_a HE atbl_tgt_inbounds Hbtbl_cgp Hbtbl_ehs Hnargs Hentry Hminstk Hdom Harg_rmap
             Hret_jalr Hret_heap)
      "(#Hswitcher & #Hstatic & #Hinv_exp_tbl_pcc & #Hinv_exp_tbl_cgp & #Hinv_exp_tbl_entry
        & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hcstk & Hpost)".
    stk_unfold.

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

    (* Open the switcher invariant *)
    iPoseProof "Hstatic" as "(#Hcode & #Hb_switcher & _ & Hswitcher_global)".
    iNamed "Hswitcher_global".
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
    iDestruct (switcher_hazard_open with "Hsave_area Hhazard_slots") as "[Hhazard Hsave_area]";
      first done.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].

    (* [.Lswitch_csp_check] to [.Lswitcher_decode_entry] *)
    iEval (rewrite -switcher_call_entry_label) in "HPC".
    iApply (switcher_call_path_spec with
      "[- $HPC $Hcsp $Hct2 $Hctp $Hcs0 $Hcs1 $Hcra $Hcgp $Hct1 $Hstk $Hmtdc $Hframeoffset $Hhazard
          $Htstk $Hb_switcher $Hcode]"); [done..|].
    iNext.
    iSplit; [ |iSplit; [ |iSplit] ]; cycle 1.
    { (* The entry point is sealed by the switcher: the unsealing does not
         fault *)
      iIntros (g_tstk) "(%Hnot_entry & _)"; exfalso.
      apply Hnot_entry; subst wct1_caller.
      by eexists _, None. }
    { (* The trusted stack is exhausted *)
      iIntros (g_tstk) "(%Hstk_bounds & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hcra & Hcgp & Hct1
        & Hcells & Hstk & Hmtdc & Hframeoffset & Hhazard & Htstk)".
      iDestruct "Hhazard" as "[Hhazard_cell Hhazard_slots]".
      iSpecialize ("Hsave_area" with "Hhazard_cell").
      iApply (switcher_cc_spec_tstack_exhausted_known_to_known with
        "[$Hclose_switcher_inv $Hna $Hmtdc $Hsave_area $Hhazard_slots $Hframeoffset $HthreadID $Htstk
          $Hstatic
          $Hcstk_full $Hstk_interp
          $Hp_ot_switcher $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hctp $Hct2 $Hct1 $Hcsp $Hcells $Hstk
          $Hargs $Hregs $Hcstk Hpost]"); [done..|].
      iNext; iIntros "H"; iApply "Hpost"; iRight; iExact "H". }
    { (* The callee-save registers fit on the caller's stack: the spill does
         not fault *)
      iIntros "(%Hnfits & _)". exfalso. apply Hnfits.
      by apply (stk_callee_fits_spill_fits _ _ _ minstk_tgt); [lia|]. }
    iNext; iIntros (g_tstk wsb π)
      "(%Hwsb & _ & %Hstk_bounds & %Ha_frame & %Ha_frame_e & HPC & Hcs0 & [%wcs1' Hcs1]
      & [%wct2' Hct2] & Hctp & Hcsp & Hcra & Hcgp & Hct1 & Hcells & Hstk & Hmtdc & Hframeoffset
      & Hhazard & Hframe_csp & [%wtbl Hframe_tbl] & Hframe_cnt & [%tstk_next' Htstk] & _)".
    subst wct1_caller; rewrite /lword_of_word in Hwsb; simplify_eq.

    (* [.Lswitcher_decode_entry]: load the callee and jump to it; only the low byte of the
       minimum stack size is encoded *)
    assert (Z.land (Z.of_nat minstk_tgt) 255 = Z.of_nat minstk_tgt `mod` 256)%Z as Hland.
    { change 255%Z with (Z.ones 8). rewrite Z.land_ones //. }
    set (minstk8 := Z.to_nat (Z.of_nat minstk_tgt `mod` 256)).
    assert (Z.land (Z.of_nat minstk_tgt) 255 = Z.of_nat minstk8) as Hminstk8.
    { subst minstk8. rewrite Hland Z2Nat.id //. apply Z.mod_pos_bound; lia. }
    assert (Z.of_nat minstk8 <= Z.of_nat minstk_tgt)%Z as Hminstk8_le.
    { rewrite -Hminstk8 Hland. apply Z.mod_le; lia. }
    assert (Z.of_nat minstk8 < 256)%Z as Hminstk8_lt.
    { rewrite -Hminstk8 Hland. apply Z.mod_pos_bound; lia. }
    iEval (rewrite encode_entry_point_minstk_land Hminstk8) in "Hinv_exp_tbl_entry".
    iApply (switcher_decode_entry_path_known_spec with
      "[- $Hinv_exp_tbl_pcc $Hinv_exp_tbl_cgp $Hinv_exp_tbl_entry $HPC $Hcs0 $Hcs1 $Hct1
        $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra $Hcsp $Hargs $Hregs $Hcode]");
      [done|solve_addr|done|lia|lia|done|done|done|done| | | |done|done| |].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { tstack_unfold; solve_addr. }
    { tstack_unfold; solve_addr. }
    { rewrite !dom_delete_L Hdom. set_solver. }
    iNext; iSplit; cycle 1.
    { (* The callee's stack is at least its minimum stack size plus the
         reserved space *)
      iIntros "(%Hsmall & _)"; exfalso.
      pose proof Hstk_bounds as (_ & _ & Ha4). stk_unfold.
      solve_addr+Hsmall Hminstk Hminstk8_le Ha4. }
    iIntros (mie arg_rmap' rmap')
      "(_ & %Harg_rmap' & %Hrmap' & HPC & Hcgp & Hcra & Hcsp & Hframe_tbl & Hargs & Hregs)".

    (* Push the frame and close the switcher invariant *)
    (* The table cell holds the unsealed entry *)
    pose proof (tf_export_tbl_cell_entry (cf_tframe frame) Global btbl_tgt etbl_tgt atbl_tgt
               eq_refl Hbtbl_ehs ltac:(solve_addr) Htbl_shadow) as Htbl_cell.
    iDestruct "Hhazard" as "[Hhazard_cell Hhazard_slots]".
    iSpecialize ("Hsave_area" with "Hhazard_cell").
    iMod (switcher_inv_push_frame frame cstk with
           "Hcstk_full Hcstk Hmtdc Hsave_area Hhazard_slots Hframeoffset HthreadID Hframe_csp
            Hframe_tbl Hframe_cnt Htstk Hstk_interp [Hcells]")
      as "[Hinv Hcstk]";
      [done|done|done|done|done|exact Hstk_bounds|done|done|by intros _
      |right; split; [done | exact Htbl_cell]|done| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".
    iApply "Hpost"; iLeft; iFrame "∗ %".
    iPureIntro; rewrite Hrmap' Hdom; set_solver.
  Qed.

End Switcher_KtK_Call.
