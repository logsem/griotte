From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants bitblast.
From griotte Require Import interp_weakening.
From griotte Require Import wp_rules_interp switcher_macros_spec.
From griotte Require Import rules proofmode monotone.
From griotte Require Import fundamental.
From griotte Require Import switcher_preamble.
From griotte Require Import interp_switcher_return switcher_exception switcher_helpers.
From griotte Require Import switcher_call_states switcher_call_world
  switcher_call_blocks_1 switcher_call_blocks_2 switcher_call_blocks_3 switcher_call_blocks_4
  switcher_call_blocks_5 switcher_call_blocks_6.
From griotte Require Import map_simpl register_tactics proofmode.


(** The register file at a fault of the first spill of the call path is
    safe: the checks leave integers in [ct2] and [ctp], and the other
    registers hold the caller's safe words. [Hfull] states that the
    caller's register map [regs] is full, the Iris hypothesis [Hreg]
    that its words are safe ([∀ r v, ⌜regs !! r = Some v⌝ → interp W C v]),
    and the Iris hypothesis [Htop] that the topmost compartment is
    untrusted. *)
Ltac first_spill_regs_interp Hfull Hreg :=
  iApply interp_reg_intro;
  [intros ?; repeat (rewrite lookup_insert_is_Some'; right); apply Hfull |];
  let r := fresh "r" in
  let v := fresh "v" in
  let Hv := fresh "Hv" in
  iIntros (r v Hv);
  destruct (decide (r = ct2)) as [-> | ?]; [simplify_map_eq; iApply interp_int |];
  destruct (decide (r = ctp)) as [-> | ?]; [simplify_map_eq; iApply interp_int |];
  iApply (Hreg $! r v); iPureIntro;
  destruct (decide (r = csp)) as [-> | ?]; [by simplify_map_eq |];
  destruct (decide (r = cs0)) as [-> | ?]; [by simplify_map_eq |];
  destruct (decide (r = cs1)) as [-> | ?]; [by simplify_map_eq |];
  destruct (decide (r = cra)) as [-> | ?]; [by simplify_map_eq |];
  destruct (decide (r = cgp)) as [-> | ?]; [by simplify_map_eq |];
  destruct (decide (r = ct1)) as [-> | ?]; [by simplify_map_eq |];
  by simplify_map_eq.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** Failure path of [interp_expr_switcher_call]: the checks on the stack
      pointer fail, and the call is unwound by the return routine. Block 18
      sets the return values, so no register needs to be safe. *)
  Lemma interp_switcher_call_force_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg)
    (a_tstk : Addr) (save_area tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    Nswitcher ## N_trap ->
    (∀ r, is_Some (regs !! r)) ->
    frame_match Ws Cs cstk W C ->
    (b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    na_inv cerise_nais Nswitcher switcher_inv ∗
    (▷ switcher_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) ∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
    (∃ w, a_threadID ↦ₐ w) ∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_static ∗
    cstack_full cstk' ∗
    cstack_interp cstk' a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
    registers_pointsto regs ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    cstack_frag cstk
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next.
    subst a_frameoffset a_save_end a_threadID a_next.
    (* Outline of the proof: [switcher_call_block_18_spec] executes block 18,
       then close the switcher invariant and run the return routine
       ([switcher_return_unwind]) with the integer return values. *)
    iIntros (HNtrap Hfull_rmap Hframe Hlen_cstk Ha_tstk_e Hot_bounds)
      "(#Hinv_switcher & Hclose_switcher_inv & Hna & Hmtdc & Hsave_area & Hframeoffset & HthreadID
      & Htstk & #Hstatic
      & Hcstk_full & Hstk_interp & #Hp_ot_switcher & HPC & Hrmap
      & Hworld_interp & Hcont & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher HNtrap with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_call_block_18_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iMod ("Hclose_switcher_inv" with
      "[$Hna $Hcstk_full Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hstk_interp]") as "Hna".
    { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }

    iInsertList "Hrmap" [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iSplit; iApply interp_int.
  Qed.

  (** Failure path of [interp_expr_switcher_call]: the trusted stack is
      exhausted. *)
  Lemma interp_switcher_call_tstack_exhausted (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (b e a : Addr) (lv : list LWord)
    (wcs0 wcs1 wcra wcgp wct1 wct2 wctp : LWord)
    (a_tstk : Addr) (save_area tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_save_end := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a in
    let a_threadID := (b_trusted_stack ^+ TrustedStack_offset_threadID)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    dom rmap = all_registers_s ∖ {[ csp ; ct2 ; ctp ; cs0 ; cs1 ; cra ; cgp ; ct1 ]} ->
    frame_match Ws Cs cstk W C ->
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    length (finz.seq_between a e) = length lv ->
    (b_trusted_stack + tstack_frame_offset (length cstk'.(cstk_frames)))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) ∗
    interp W C wcs0 ∗
    interp W C wcs1 ∗
    interp W C wcra ∗
    interp W C wcgp ∗
    interp W C (WCap true RWL Local b e a) ∗
    top_cmpt_untrusted interp W C cstk ∗
    (▷ switcher_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) ∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    [[ b_trusted_stack, a_save_end ]] ↦ₐ [[ save_area ]] ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (length cstk'.(cstk_frames))) ∗
    (∃ w, a_threadID ↦ₐ w) ∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_static ∗
    cstack_full cstk' ∗
    cstack_interp cstk' a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ w, cs0 ↦ᵣ w) ∗
    (∃ w, cs1 ↦ᵣ w) ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    ct1 ↦ᵣ wct1 ∗
    csp ↦ᵣ WCap true RWL Local b e (a ^+ 4)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ drop 4 lv ]] ∗
    switcher_stk_opened W C a e lv ∗
    ( [∗ map] k↦y ∈ rmap, k ↦ᵣ y ) ∗
    interp_cont interp cstk Ws Cs ∗
    cstack_frag cstk
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_save_end a_threadID a_next.
    subst a_frameoffset a_save_end a_threadID a_next.
    (* Outline of the proof: [switcher_call_blocks_5_spec] executes blocks 17
       and 14-15, [switcher_call_stk_close] closes the caller's stack frame,
       then close the switcher invariant and
       [switcher_jump_to_caller_cases_spec]. *)
    iIntros (Hdom Hframe Hstk_bounds Hstk_mmio Hlen_lv Hlen_cstk Ha_tstk_e Hot_bounds)
      "(#Htrap & #Hcs0v & #Hcs1v & #Hcrav & #Hcgpv & #Hspv & #Htop & Hclose_switcher_inv & Hna & Hmtdc
      & Hsave_area & Hframeoffset & HthreadID & Htstk
      & #Hstatic & Hcstk_full & Hstk_interp & #Hp_ot_switcher & HPC & Hcs0 & Hcs1 & Hcgp
      & Hcra & Hctp & Hct2 & Hct1 & Hcsp & Hcells & Hstk & Hstk_opened & Hrmap & Hcont & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    pose proof Hstk_bounds as (_ & Hba3 & Ha4).
    assert (4 <= length lv) as Hlen_lv4.
    { rewrite -Hlen_lv finz_seq_between_length /finz.dist. solve_addr. }
    assert (is_Some (rmap !! ca0)) as [? ?] by (apply elem_of_dom; rewrite Hdom; set_solver-).
    assert (is_Some (rmap !! ca1)) as [? ?] by (apply elem_of_dom; rewrite Hdom; set_solver-).
    iExtract "Hrmap" ca0 as "Hca0".
    iExtract "Hrmap" ca1 as "Hca1".
    iInsertRegs "Hrmap" ["Hct1";"Hctp";"Hct2"].
    iApply (switcher_call_blocks_5_spec with
      "[- $HPC $Hcsp $Hcells $Hrmap $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1]"); [done|done| |].
    { repeat (rewrite dom_insert_L). repeat (rewrite dom_delete_L). rewrite Hdom. set_solver. }
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "((%Hrcgp & %Hrcra & %Hrcs0 & %Hrcs1) & %Hrmap' & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Hcells & Hrmap & _ & _)".
    iDestruct (interp_load_heap with "Hcs0v") as "#Hrcs0v"; first done.
    iDestruct (interp_load_heap with "Hcs1v") as "#Hrcs1v"; first done.
    iDestruct (interp_load_heap with "Hcrav") as "#Hrcrav"; first done.
    iDestruct (interp_load_heap with "Hcgpv") as "#Hrcgpv"; first done.

    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
    iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
      as "Hworld_interp".
    { cbn; rewrite length_drop; lia. }
    { iSplitL; first (iRight; iFrame "#").
      iSplitL; first (iRight; iFrame "#").
      iSplitL; first (iRight; iFrame "#").
      iSplitL; first (iRight; iFrame "#").
      iApply big_sepL_forall. iIntros (k w Hk). iLeft. iPureIntro.
      rewrite lookup_drop in Hk. exact Hk. }

    (* Jump back to the caller, or unwind the call when the jump faults;
       close the switcher invariant first *)
    iApply (switcher_jump_to_caller_cases_spec with
             "Htrap Hrcrav Hrcgpv Hrcs0v Hrcs1v Hspv [] [] Htop Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
              Hrmap Hcont [-]"); [done|done|iApply interp_int|iApply interp_int|].
    iMod ("Hclose_switcher_inv" with
      "[$Hna $Hcstk_full Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hstk_interp]") as "HH".
    { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }
    by iFrame.
  Qed.

  Lemma interp_expr_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C (WCap true XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - [switcher_call_stk_open]: open the caller's stack frame in the world
         (when the stack pointer is not a valid stack capability,
         [switcher_call_blocks_2_fail_spec] or, when it is below the base
         and the furthest cell of the spill within bounds,
         [switcher_call_blocks_2_below_spec], and [trap_safe_unwind]);
       - [switcher_call_blocks_1_spec]: checks on the stack pointer;
         when they fail, [interp_switcher_call_force_unwind];
       - [switcher_call_blocks_2_spec]: spill the callee-save registers and
         push the stack pointer on the trusted stack; when the spill faults,
         [trap_safe_unwind];
       - when the trusted stack is exhausted:
         [interp_switcher_call_tstack_exhausted];
       - [switcher_call_blocks_3_spec]: clear the callee's stack frame and
         unseal the entry point; when the unsealing faults, push the frame
         and [trap_safe_unwind];
       - [switcher_call_stk_close]: close the caller's stack frame;
       - [switcher_entry_point_prop]: the entry point satisfies the sealing
         predicate of the switcher;
       - [switcher_call_blocks_4_spec]: check the size of the callee's
         stack, load the callee and jump to it; when the stack is too small,
         push the frame and [switcher_call_stack_too_small_unwind];
       - [switcher_inv_push_frame]: close the switcher invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros (HNtrap) "[#Hinv_switcher #Hstatic] %cstk %Ws %Cs %regs0 (Hregs & #Htop & HPC & Hrmap & Hworld_interp & Hcont & Hna & Hcstk & %Hframe)".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (regs) "%Hfull_rmap #Hreg Hrmap Hworld_interp". clear regs0.
    rewrite /registers_pointsto.
    iPoseProof (switcher_mtcc_vec_safe Nswitcher HNtrap with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    iPoseProof (fundamental_ih with "Htrap") as "IH". (* used for weakening lemma later *)
    iPoseProof "Hstatic" as "(#Hcode & #Hb_switcher & _)".

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].

    specialize (Hfull_rmap csp) as HH;destruct HH as [wcsp Hstk].
    specialize (Hfull_rmap ct2) as HH;destruct HH as [? wct2].
    specialize (Hfull_rmap ctp) as HH;destruct HH as [? wctp].
    iExtract "Hrmap" csp as "Hcsp".
    iExtract "Hrmap" ct2 as "Hct2".
    iExtract "Hrmap" ctp as "Hctp".
    iDestruct ("Hreg" $! csp with "[//]") as "#Hspv".

    specialize (Hfull_rmap cs0) as HH; destruct HH as [wcs0 Hwcs0].
    specialize (Hfull_rmap cs1) as HH; destruct HH as [wcs1 Hwcs1].
    specialize (Hfull_rmap cra) as HH; destruct HH as [wcra Hwcra].
    specialize (Hfull_rmap cgp) as HH; destruct HH as [wcgp Hwcgp].
    specialize (Hfull_rmap ct1) as HH; destruct HH as [wct1 Hwct1].
    iExtract "Hrmap" cs0 as "Hcs0".
    iExtract "Hrmap" cs1 as "Hcs1".
    iExtract "Hrmap" cra as "Hcra".
    iExtract "Hrmap" cgp as "Hcgp".
    iExtract "Hrmap" ct1 as "Hct1".
    iAssert (interp W C wcs0) as "#Hcs0v".
    { iApply "Hreg"; eauto; done. }
    iAssert (interp W C wcs1) as "#Hcs1v".
    { iApply "Hreg"; eauto; done. }
    iAssert (interp W C wcra) as "#Hcrav".
    { iApply "Hreg"; eauto; done. }
    iAssert (interp W C wcgp) as "#Hcgpv".
    { iApply "Hreg"; eauto; done. }
    iAssert (interp W C wct1) as "#Hct1v".
    { iApply "Hreg"; eauto; done. }

    (* Is the stack pointer a valid stack capability? *)
    iAssert (⌜(∃ b e a, wcsp = WCap true RWL Local b e a ∧ (b <= a < e)%a)
            ∨ (∀ b e a, wcsp.(lw) = WCap true RWL Local b e a → (a < b)%a ∨ (e <= a)%a)⌝)%I
      as %[(b & e & a & -> & Hba) | Hnot_stk].
    { destruct wcsp as [ [| [t p g b e a|] | |] π]; try (iPureIntro; right; intros; discriminate).
      destruct t; [|iPureIntro; right; intros; discriminate].
      destruct (decide (p = RWL ∧ g = Local)) as [ [-> ->] | Hpg].
      - destruct (decide (b <= a < e)%a) as [Hbae|Hbae].
        + iDestruct (interp_wl_noid with "Hspv") as %->; [done|solve_addr|].
          iPureIntro; left; eauto.
        + iPureIntro; right; intros ??? Heq; inversion Heq; subst; solve_addr.
      - iPureIntro; right; intros ??? Heq; inversion Heq; subst; tauto. }
    2: { (* The stack pointer is not a valid stack capability: the spill
            faults. Is the furthest cell of the spill within its bounds? *)
         iAssert (⌜(∃ b e a, wcsp = WCap true RWL Local b e a ∧
                              (a + 3)%a = Some (a ^+ 3)%a ∧ (b <= a ^+ 3 < e)%a)
                 ∨ (∀ b e a a3, wcsp.(lw) = WCap true RWL Local b e a →
                                (a + 3)%a = Some a3 → (a3 < b)%a ∨ (e <= a3)%a)⌝)%I
           as %[(b & e & a & -> & Ha3 & Ha3_in) | Hfirst].
         { destruct wcsp as [ [| [t p g b e a|] | |] π]; try (iPureIntro; right; intros; discriminate).
           destruct t; [|iPureIntro; right; intros; discriminate].
           destruct (decide (p = RWL ∧ g = Local)) as [ [-> ->] | Hpg]; cycle 1.
           { iPureIntro; right; intros ???? Heq; inversion Heq; subst; tauto. }
           destruct (a + 3)%a as [a3|] eqn:Ha3; cycle 1.
           { iPureIntro; right; intros ???? Heq Ha3'; inversion Heq; subst; congruence. }
           destruct (decide (b <= a3 < e)%a) as [Ha3_in|Ha3_out]; cycle 1.
           { iPureIntro; right; intros ???? Heq Ha3'; inversion Heq; subst.
             rewrite Ha3 in Ha3'; simplify_eq; solve_addr. }
           iDestruct (interp_wl_noid with "Hspv") as %->; [done|solve_addr|].
           iPureIntro; left; exists b, e, a; split; first done.
           split; solve_addr. }
         2: {
           (* Blocks 0-1: checks on the stack pointer *)
           iApply (switcher_call_blocks_1_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
           iNext; iIntros "[(%Hchecked & HPC & Hcsp & Hct2 & Hctp & _)
                           | (_ & % & % & HPC & Hcsp & Hct2 & Hctp & _)]";
             cycle 1.
           { (* The checks fail: force the unwinding of the call *)
             iInsertList "Hrmap" [csp;ct2;ctp;cs0;cs1;cra;cgp;ct1].
             iApply (interp_switcher_call_force_unwind with
               "[$Hinv_switcher $Hclose_switcher_inv $Hna $Hmtdc $Hsave_area $Hframeoffset $HthreadID
                 $Htstk $Hstatic
                 $Hcstk_full $Hstk_interp $Hp_ot_switcher $HPC $Hrmap
                 $Hworld_interp $Hcont $Hcstk]"); [done| |done..].
             intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
           (* The first store faults, and nothing is written: close the
              switcher invariant, and unwind the call *)
           subst hclose_switcher_inv hinv_switcher.
           iMod ("Hclose_switcher_inv" with
             "[$Hna $Hcstk_full Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hstk_interp]") as "Hna".
           { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }
           iApply (switcher_call_blocks_2_fail_spec with "[- $HPC $Hcsp $Hcgp $Hcode]"); [done | done |].
           iIntros "[Hcsp Hcgp]".
           iInsertList "Hrmap" [csp;ct2;ctp;cs0;cs1;cra;cgp;ct1].
           iApply (interp_trap_safe_untrusted with "Htrap [] Htop [-]");
             [ |done| |by iFrame].
           { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
           (* A fault of the first spill: the registers are safe *)
           first_spill_regs_interp Hfull_rmap "Hreg". }
         (* The cursor is below the base, and the furthest cell within
            bounds: open the caller's stack from that cell *)
         destruct (Hnot_stk b e a eq_refl) as [Hab|Hea]; last solve_addr.
         iDestruct (interp_cap_disjoint_wl with "Hspv") as %[Hstk_mmio _]; first done.
         iPoseProof (interp_lea _ _ _ _ _ _ _ _ (a ^+ 3)%a with "Hspv") as "Hspv3"; first done.
         iDestruct (switcher_call_stk_open with "Hspv3 Hworld_interp")
           as (lv) "(Hstk & Hstk_opened)"; first solve_addr.
         iDestruct (big_sepL2_length with "Hstk") as %Hlen_lv.

         (* Blocks 0-1: checks on the stack pointer *)
         iApply (switcher_call_blocks_1_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
         iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp & _)
                         | (_ & % & % & HPC & Hcsp & Hct2 & Hctp & _)]";
           cycle 1.
         { (* The checks fail: close the caller's stack, and force the
              unwinding of the call *)
           iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
             as "Hworld_interp"; first done.
           { iApply big_sepL_intro; iIntros "!>" (k w Hk); by iLeft. }
           iInsertList "Hrmap" [csp;ct2;ctp;cs0;cs1;cra;cgp;ct1].
           iApply (interp_switcher_call_force_unwind with
             "[$Hinv_switcher $Hclose_switcher_inv $Hna $Hmtdc $Hsave_area $Hframeoffset $HthreadID
               $Htstk $Hstatic
               $Hcstk_full $Hstk_interp $Hp_ot_switcher $HPC $Hrmap
               $Hworld_interp $Hcont $Hcstk]"); [done| |done..].
           intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
         (* The first store writes [cgp] in the caller's stack, and the
            second one faults: close the switcher invariant and the caller's
            stack, and unwind the call *)
         subst hclose_switcher_inv hinv_switcher.
         iMod ("Hclose_switcher_inv" with
           "[$Hna $Hcstk_full Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hstk_interp]") as "Hna".
         { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }
         destruct lv as [|w3 lv];
           first (exfalso; rewrite finz_seq_between_length /finz.dist /= in Hlen_lv; solve_addr).
         iDestruct (region_pointsto_cons _ ((a ^+ 3) ^+ 1)%a with "Hstk") as "[Ha3 Hstk]";
           [solve_addr..|].
         iApply (switcher_call_blocks_2_below_spec with "[- $HPC $Hcsp $Hcs0 $Hcgp $Ha3 $Hcode]");
           [done..|].
         iIntros "(Hcsp & Hcs0 & Hcgp & Ha3)".
         iDestruct (region_pointsto_cons with "[$Ha3 $Hstk]") as "Hstk"; [solve_addr..|].
         iDestruct (switcher_call_stk_close _ _ _ _ (w3 :: lv) with "Hstk_opened Hstk []")
           as "Hworld_interp"; first done.
         { iApply big_sepL_cons; iSplitR; first (iRight; iExact "Hcgpv").
           iApply big_sepL_intro; iIntros "!>" (k w Hk); by iLeft. }
         iInsertList "Hrmap" [csp;ct2;ctp;cs0;cs1;cra;cgp;ct1].
         iApply (trap_safe_unwind_logrel with "Hinv_switcher Hstatic [] [-]");
           [done| |done| | |by iFrame].
         { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
         { (* A fault of the second store of the spill is not resumed *)
           apply trap_no_resume_switcher_pc. by vm_compute. }
         (* The fault is in the switcher *)
         iLeft; iPureIntro. apply switcher_fault_pc_cap. }
    iDestruct (interp_cap_disjoint_wl with "Hspv") as %[Hstk_mmio Hstk_heap]; first done.

    (* Open the caller's stack frame, before the checks: the opened
       resources are then available at a fault of the spill *)
    iDestruct (switcher_call_stk_open with "Hspv Hworld_interp")
      as (lv) "(Hstk & Hstk_opened)"; first solve_addr.
    iDestruct (big_sepL2_length with "Hstk") as %Hlen_lv.

    (* Blocks 0-1: checks on the stack pointer *)
    iApply (switcher_call_blocks_1_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
    iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp & _)
                    | (_ & % & % & HPC & Hcsp & Hct2 & Hctp & _)]";
      cycle 1.
    { (* The checks fail: close the caller's stack frame, and force the
         unwinding of the call *)
      iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
        as "Hworld_interp"; first done.
      { iApply big_sepL_intro; iIntros "!>" (k w Hk); by iLeft. }
      iInsertList "Hrmap" [csp;ct2;ctp;cs0;cs1;cra;cgp;ct1].
      iApply (interp_switcher_call_force_unwind with
        "[$Hinv_switcher $Hclose_switcher_inv $Hna $Hmtdc $Hsave_area $Hframeoffset $HthreadID $Htstk
          $Hstatic
          $Hcstk_full $Hstk_interp $Hp_ot_switcher $HPC $Hrmap
          $Hworld_interp $Hcont $Hcstk]"); [done| |done..].
      intros r. rewrite !lookup_insert_is_Some'. naive_solver.
    }

    (* Blocks 2-3: spill and push on the trusted stack *)
    iApply (switcher_call_blocks_2_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hctp $Hct2 $Hcsp $Hstk $Hmtdc $Hframeoffset $Htstk $Hcode]");
      [done|done|done|].
    iSplit; cycle 1.
    { (* The spill does not fit on the caller's stack: close the caller's
         stack frame and the switcher invariant, and unwind the call *)
      iIntros (a_f stk_mem' Ha_f) "(Hcs0 & Hcs1 & Hcra & Hcgp & Hctp & Hct2 & Hcsp
        & Hstk & Hmtdc & Hframeoffset & Htstk)".
      destruct Ha_f as [ (-> & -> & _) | (Hcontra & _) ]; last (exfalso; solve_addr).
      subst hclose_switcher_inv hinv_switcher.
      iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
        as "Hworld_interp"; first done.
      { iApply big_sepL_intro; iIntros "!>" (k w Hk); by iLeft. }
      iInsertList "Hrmap" [csp;ct2;ctp;cs0;cs1;cra;cgp;ct1].
      iApply (interp_trap_safe_untrusted with "Htrap [] Htop [-]"); [ |done| |]; cycle 2.
      { iMod ("Hclose_switcher_inv" with
          "[$Hna $Hcstk_full Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hstk_interp]") as "Hna".
        { iNext. iExists _,_,_. iFrame "∗ # %". iPureIntro; split; done. }
        by iFrame. }
      { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
      (* A fault of the first spill: the registers are safe *)
      first_spill_regs_interp Hfull_rmap "Hreg". }
    iNext; iIntros "(%Hstk_bounds & Hcra & Hcgp & Hcsp & Hcells & Hstk & Hmtdc & _ & Hbranch)".
    pose proof Hstk_bounds as (_ & Hba3 & Ha4).
    assert (4 <= length lv) as Hlen_lv4.
    { rewrite -Hlen_lv finz_seq_between_length /finz.dist. solve_addr. }
    iDestruct "Hbranch" as
      "[(%Ha_frame & %Ha_frame_e & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hframeoffset
         & Hframe_csp & Hframe_tbl & Hframe_cnt & [%tstk_next' Htstk] & Hlc)
       | (HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hframeoffset & Htstk)]"; cycle 1.
    { (* The trusted stack is exhausted *)
      iApply (interp_switcher_call_tstack_exhausted _ W C Nswitcher cstk _ Ws Cs _ b e a lv
                wcs0 wcs1 wcra wcgp with
        "[$Htrap $Hcs0v $Hcs1v $Hcrav $Hcgpv $Hspv $Htop $Hclose_switcher_inv $Hna $Hmtdc $Hsave_area
          $Hframeoffset $HthreadID $Htstk $Hstatic
          $Hcstk_full $Hstk_interp $Hp_ot_switcher $HPC $Hcs0 $Hcs1 $Hcgp $Hcra
          $Hctp $Hct2 $Hct1 $Hcsp $Hcells $Hstk $Hstk_opened $Hrmap $Hcont $Hcstk]"); try done.
      repeat (rewrite dom_delete_L). clear -Hfull_rmap.
      apply lregmap_full_dom in Hfull_rmap. rewrite Hfull_rmap. set_solver.
    }

    (* Blocks 4-7: clear the callee's stack frame and unseal the entry point *)
    iApply (switcher_call_blocks_3_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcsp $Hstk $Hb_switcher $Hct1 $Hcode]"); [done|done|done|].
    iSplit; cycle 1.
    { (* The entry point is not sealed by the switcher: close the caller's
         stack frame, push the frame, close the switcher invariant, and unwind
         the call *)
      iIntros "_ (Hcs0 & [%wcs1' Hcs1] & Hcsp & Hstk & [%wct1' Hct1])".
      subst hclose_switcher_inv hinv_switcher.
      iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
      iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
        as "Hworld_interp".
      { cbn; rewrite /region_addrs_zeroes length_replicate -Hlen_lv !finz_seq_between_length /finz.dist.
        solve_addr. }
      { iSplitL; first (iRight; iFrame "#").
        iSplitL; first (iRight; iFrame "#").
        iSplitL; first (iRight; iFrame "#").
        iSplitL; first (iRight; iFrame "#").
        iApply big_sepL_forall. iIntros (k w Hk). iRight.
        apply lookup_replicate in Hk as [-> _]. iApply interp_int. }
      set (frame :=
             {| cf_tframe :=
                  {| tf_csp := WCap true RWL Local b e (a ^+ 4)%a;
                     (* the export table cell holds 0: the word is never read *)
                     tf_export_tbl := WInt 0;
                     tf_error_count := 0 |};
                cf_saved :=
                  {| cs_cra := WInt 0;
                     cs_cgp := WInt 0;
                     cs_cs0 := WInt 0;
                     cs_cs1 := WInt 0 |};
                ccrel := Unknown_to_Unknown
             |}).
      iInsertList "Hrmap" [csp;ct2;ctp;cs0;cs1;cra;cgp;ct1].
      iApply (trap_safe_unwind_logrel _ _ _ (cstack_push frame cstk) (W :: Ws) (C :: Cs)
               with "Hinv_switcher Hstatic [] [-]"); [done|..]; cycle 1.
      { simpl. split; auto; first apply related_sts_pub_refl_world.
        split; [reflexivity|]; split; done. }
      { (* The unsealing is not the first spill *)
        apply trap_no_resume_switcher_pc. by vm_compute. }
      { (* The fault is in the switcher *)
        iLeft; iPureIntro. apply switcher_fault_pc_cap. }
      { (* The table cell is still cleared *)
        pose proof (tf_export_tbl_cell_cleared (cf_tframe frame) eq_refl) as Htbl_cell.
        iMod (switcher_inv_push_frame frame cstk with
               "Hcstk_full Hcstk Hmtdc Hsave_area Hframeoffset HthreadID Hframe_csp Hframe_tbl Hframe_cnt
                Htstk Hstk_interp [] Hp_ot_switcher")
          as "[Hinv Hcstk]"; [done..|].
        iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".
        iModIntro.
        iFrame "Hrmap Hworld_interp Hcstk Hna".
        simpl.
        iFrame "Hcont".
        rewrite (spill_cursor a) ?cstack_eta; last by eexists.
        iSplit; last iExact "Htop".
        iSplit; first (iPureIntro; exact Hstk_heap).
        iApply (interp_weakening with "IH Hspv"); auto; solve_addr. }
      intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iNext; iIntros (wsb π)
      "(-> & %Htag & HPC & Hcs0 & [%wcs1' Hcs1] & Hcsp & Hstk & _ & Hct1 & _)".

    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
    iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
      as "Hworld_interp".
    { cbn; rewrite /region_addrs_zeroes length_replicate -Hlen_lv !finz_seq_between_length /finz.dist.
      solve_addr. }
    { iSplitL; first (iRight; iFrame "#").
      iSplitL; first (iRight; iFrame "#").
      iSplitL; first (iRight; iFrame "#").
      iSplitL; first (iRight; iFrame "#").
      iApply big_sepL_forall. iIntros (k w Hk). iRight.
      apply lookup_replicate in Hk as [-> _]. iApply interp_int. }

    (* The entry point satisfies the sealing predicate of the switcher *)
    iDestruct (switcher_entry_point_prop with "Hp_ot_switcher [] Hworld_interp")
      as "[Hworld_interp Hentry_prop]".
    { case_match; [iExact "Hct1v"|done]. }
    iDestruct "Hlc" as "[Hlc _]".
    iMod (lc_fupd_elim_later with "Hlc Hentry_prop") as "Hentry_prop".
    iDestruct ("Hentry_prop" with "[//] [//]") as "Hentry_ot".
    iNamed "Hentry_ot".
    rewrite /lword_of_word in Hw; simplify_eq.
    iSpecialize ("Hentry_cont" $! W with "[]").
    { iPureIntro. apply related_sts_priv_refl_world. }

    (* Blocks 7-12: load the callee and jump to it *)
    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↦ᵣ y)%I ] => set (rmap' := r) end.
    set (params := dom_arg_rmap 8).
    set (Pf := ((λ '(r,_), r ∈ params) : RegName * LWord → Prop)).
    rewrite -(map_filter_union_complement Pf rmap').
    iDestruct (big_sepM_union with "Hrmap") as "[Hparams Hrest]".
    { apply map_disjoint_filter_complement. }
    iAssert ([∗ map] r↦w ∈ filter Pf rmap',
               r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True)%I
      with "[Hparams]" as "Hparams".
    { iApply big_sepM_sep. iFrame. iApply big_sepM_forall.
      { intros k v.
        destruct (decide ( (k ∈ dom_arg_rmap nargs) )); tc_solve.
      }
      iIntros (k v [Hin Hspec]%map_lookup_filter_Some).
      destruct ( decide (k ∈ dom_arg_rmap nargs) ); last done.
      iApply ("Hreg" $! k); iPureIntro.
      repeat (apply lookup_delete_Some in Hin as [_ Hin]); auto.
    }
    iApply (switcher_call_blocks_4_spec W C with
      "[- $Htbl_pcc $Htbl_cgp $Htbl_entry $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hframe_tbl $Hcgp $Hcra $Hcsp
          $Hparams $Hrest $Hcode]");
      [done|solve_addr|done|lia|lia|done|done|done|done| | | | | |].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { tstack_unfold; solve_addr. }
    { tstack_unfold; solve_addr. }
    { rewrite /is_arg_rmap /dom_arg_rmap.
      apply dom_filter_L. clear -Hfull_rmap.
      rewrite /rmap'. split.
      - intros Hi.
        repeat (rewrite lookup_delete_ne;[|set_solver]).
        specialize (Hfull_rmap i) as [x Hx].
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    { clear -Hfull_rmap. apply lregmap_full_dom in Hfull_rmap as Hw'.
      rewrite /rmap' !map_filter_delete !dom_delete_L.
      cut (dom (filter (λ v, ¬ Pf v) regs) = all_registers_s ∖ dom_arg_rmap 8);[set_solver|].
      apply (dom_filter_L _ (regs : gmap RegName LWord)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_rmap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }
    set (frame :=
           {| cf_tframe :=
                {| tf_csp := WCap true RWL Local b e (a ^+ 4)%a;
                   tf_export_tbl := WCap true RO g_tbl b_tbl e_tbl a_tbl;
                   tf_error_count := 0 |};
              cf_saved :=
                {| cs_cra := WInt 0;
                   cs_cgp := WInt 0;
                   cs_cs0 := WInt 0;
                   cs_cs1 := WInt 0 |};
              ccrel := Unknown_to_Unknown
           |}).
    iNext; iSplit; cycle 1.
    { (* The callee's stack is too small: push the frame, close the switcher
         invariant, and return to the caller through the return routine *)
      iIntros "(_ & HPC & [%wcs0' Hcs0] & [%wcs1'' Hcs1] & [%wct1' Hct1] & [%wct2' Hct2]
        & [%wctp' Hctp] & [%wcgp' Hcgp] & [%wcra' Hcra] & Hcsp & Hframe_tbl & Hparams & Hrest & _)".
      (* The table cell holds the unsealed entry *)
      pose proof (or_intror (A := (cf_tframe frame).(tf_export_tbl) = lword_of_word (WInt 0))
                    (tf_export_tbl_cell_entry (cf_tframe frame) g_tbl b_tbl e_tbl a_tbl
                       eq_refl Hbtbl_header ltac:(solve_addr) Htbl_shadow)) as Htbl_cell.
      iMod (switcher_inv_push_frame frame cstk with
             "Hcstk_full Hcstk Hmtdc Hsave_area Hframeoffset HthreadID Hframe_csp Hframe_tbl Hframe_cnt
              Htstk Hstk_interp [] Hp_ot_switcher")
        as "[Hinv Hcstk]"; [done..|].
      iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".
      iDestruct (big_sepM_sep with "Hparams") as "[Hparams _]".
      iDestruct (big_sepM_union with "[$Hparams $Hrest]") as "Hrmap".
      { apply map_disjoint_filter_complement. }
      rewrite map_filter_union_complement.
      subst rmap'.
      iInsertList "Hrmap" [csp;ct2;ctp;cs0;cs1;cra;cgp;ct1].
      iApply (switcher_call_stack_too_small_unwind _ _ _ (cstack_push frame cstk)
               (W :: Ws) (C :: Cs)
               with "[$HPC $Hrmap $Hinv_switcher $Hstatic $Hworld_interp $Hna $Hcstk Hcont]");
        first done.
      { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
      { simpl. split; [apply related_sts_pub_refl_world|done]. }
      simpl.
      iFrame "Hcont".
      rewrite (spill_cursor a) ?cstack_eta; last by eexists.
      iSplit; last iExact "Htop".
      iSplit; first (iPureIntro; exact Hstk_heap).
      iApply (interp_weakening with "IH Hspv"); auto; solve_addr. }
    iIntros (mie arg_rmap' rmap'')
      "(%Hbig & %Harg_rmap' & %Hrmap'' & HPC & Hcgp & Hcra & Hcsp & Hframe_tbl & Hargs & Hregs & _)".

    (* Push the frame, whose table cell holds the unsealed entry, and close the
       switcher invariant *)
    pose proof (tf_export_tbl_cell_entry (cf_tframe frame) g_tbl b_tbl e_tbl a_tbl
                  eq_refl Hbtbl_header ltac:(solve_addr) Htbl_shadow) as Htbl_ok.
    pose proof (or_intror (A := (cf_tframe frame).(tf_export_tbl) = lword_of_word (WInt 0))
                  Htbl_ok) as Htbl_cell.
    iMod (switcher_inv_push_frame frame cstk with
           "Hcstk_full Hcstk Hmtdc Hsave_area Hframeoffset HthreadID Hframe_csp Hframe_tbl Hframe_cnt Htstk
            Hstk_interp [] Hp_ot_switcher")
      as "[Hinv Hcstk]"; [done..|].
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".

    (* Execute the entry point of the callee *)
    iAssert (interp W C (WCap true RWL Local (a ^+ 4)%a e (a ^+ 4)%a)) as "#Hstk4v".
    { iApply (interp_weakening with "IH Hspv"); auto; solve_addr. }
    iDestruct (switcher_call_entry_registers W W C nargs arg_rmap' rmap'' with
                "[$Hcgp $Hcra $Hcsp $Hstk4v $Hargs $Hregs]")
      as (regs') "[Hregs Hregs_interp]"; [apply related_sts_pub_refl_world|done|done|done|].
    iApply ("Hentry_cont" $! (cstack_push frame cstk) (W :: Ws) (C :: Cs) regs' a e).
    iSplitL "Hcont".
    { simpl. iFrame "Hcont".
      rewrite (spill_cursor a) ?cstack_eta; last by eexists.
      iSplit.
      - iSplit; first (iPureIntro; exact Hstk_heap).
        iApply (interp_weakening with "IH Hspv");auto;solve_addr.
      - iExact "Htop". }
    iSplit.
    { iPureIntro. simpl. split;auto. apply related_sts_pub_refl_world. }
    iSplit; first (iPureIntro; split_and!; [done | reflexivity | reflexivity | exact Htbl_ok]).
    iFrame "HPC Hregs Hregs_interp Hworld_interp Hcstk Hna".
    iPureIntro; split;
      [split; [split; [cbn; apply spill_cursor; by eexists | reflexivity] | solve_addr]
      | exact Hbig].
  Qed.

  Lemma interp_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp W C (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros (HNtrap) "[#Hinv #Hstatic]".
    rewrite interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_call with "[$Hinv $Hstatic]"); done.
  Qed.

End fundamental.
