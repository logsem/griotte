From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel_binary region_invariants_binary.
From griotte Require Import switcher_macros_spec_binary.
From griotte Require Import rules proofmode_binary.
From griotte Require Import switcher_preamble_binary switcher_helpers_binary.
From griotte Require Import map_simpl register_tactics_binary.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The switcher-call routine of a trusted caller when the trusted stack is
      exhausted, in both runs: the switcher restores the callee-saved
      registers of each run from its own stack frame, clears the other
      registers and returns to the caller with the error code
      [ENOTENOUGHTRUSTEDSTACK]. The switcher's state is unchanged. *)
  Lemma switcher_cc_tstk_exhausted
    (Nswitcher : namespace)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (b_stk e_stk a_stk a_stk4 : Addr)
    (rmap smap : Reg)
    (wcgp swcgp wcra swcra wcs0 swcs0 wcs1 swcs1 wca0 swca0 wca1 swca1 : Word) :
    (b_stk <= a_stk)%a →
    (a_stk + 4)%a = Some a_stk4 →
    (a_stk ^+ 3 < e_stk)%a →
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} →
    dom smap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} →
    na_inv cerise_nais Nswitcher switcher_inv_binary -∗
    spec_ctx -∗
    na_own cerise_nais ⊤ -∗
    ⤇ Seq (Instr Executable) -∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher
      (a_switcher_call ^+ (default 0%nat (switcher_labels !! ".Lswitch_trusted_stack_exhausted")))%a -∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher
      (a_switcher_call ^+ (default 0%nat (switcher_labels !! ".Lswitch_trusted_stack_exhausted")))%a -∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk4 -∗
    csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk4 -∗
    cgp ↦ᵣ wcgp -∗ cgp ↣ᵣ swcgp -∗
    cra ↦ᵣ wcra -∗ cra ↣ᵣ swcra -∗
    cs1 ↦ᵣ wcs1 -∗ cs1 ↣ᵣ swcs1 -∗
    cs0 ↦ᵣ wcs0 -∗ cs0 ↣ᵣ swcs0 -∗
    ca0 ↦ᵣ wca0 -∗ ca0 ↣ᵣ swca0 -∗
    ca1 ↦ᵣ wca1 -∗ ca1 ↣ᵣ swca1 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ([∗ map] r↦w ∈ smap, r ↣ᵣ w) -∗
    a_stk ↦ₐ wcs0_caller.1 -∗
    (a_stk ^+ 1)%a ↦ₐ wcs1_caller.1 -∗
    (a_stk ^+ 2)%a ↦ₐ wcra_caller.1 -∗
    (a_stk ^+ 3)%a ↦ₐ wcgp_caller.1 -∗
    a_stk ↣ₐ wcs0_caller.2 -∗
    (a_stk ^+ 1)%a ↣ₐ wcs1_caller.2 -∗
    (a_stk ^+ 2)%a ↣ₐ wcra_caller.2 -∗
    (a_stk ^+ 3)%a ↣ₐ wcgp_caller.2 -∗
    ( ∀ (rmap' : Reg),
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
        ∗ na_own cerise_nais ⊤
        ∗ ⤇ Seq (Instr Executable)
        ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
        ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
        ∗ cgp ↦ᵣ wcgp_caller.1
        ∗ cgp ↣ᵣ wcgp_caller.2
        ∗ cra ↦ᵣ wcra_caller.1
        ∗ cra ↣ᵣ wcra_caller.2
        ∗ cs0 ↦ᵣ wcs0_caller.1
        ∗ cs0 ↣ᵣ wcs0_caller.2
        ∗ cs1 ↦ᵣ wcs1_caller.1
        ∗ cs1 ↣ᵣ wcs1_caller.2
        ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
        ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
        ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
        ∗ ca0 ↣ᵣ WInt ENOTENOUGHTRUSTEDSTACK
        ∗ ca1 ↦ᵣ WInt 0
        ∗ ca1 ↣ᵣ WInt 0
        ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
        ∗ a_stk ↦ₐ wcs0_caller.1
        ∗ (a_stk ^+ 1)%a ↦ₐ wcs1_caller.1
        ∗ (a_stk ^+ 2)%a ↦ₐ wcra_caller.1
        ∗ (a_stk ^+ 3)%a ↦ₐ wcgp_caller.1
        ∗ a_stk ↣ₐ wcs0_caller.2
        ∗ (a_stk ^+ 1)%a ↣ₐ wcs1_caller.2
        ∗ (a_stk ^+ 2)%a ↣ₐ wcra_caller.2
        ∗ (a_stk ^+ 3)%a ↣ₐ wcgp_caller.2
        ∗ £ 2
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}
    ) -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hb_astk Ha_stk4 Ha_stk3 Hdom_rmap Hdom_smap)
      "#Hinv_switcher #Hspec Hna Hj HPC HsPC Hcsp Hscsp Hcgp Hscgp Hcra Hscra Hcs1 Hscs1
       Hcs0 Hscs0 Hca0 Hsca0 Hca1 Hsca1 Hrmap Hsmap
       Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hsa_stk Hsa_stk1 Hsa_stk2 Hsa_stk3 Hpost".
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "([Hswitcher_inv Hswitcher_inv_spec] & Hna & Hclose_switcher_inv)" ; auto.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & >Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iDestruct "Hswitcher_inv_spec"
      as (sa_tstk scstk' ststk_next)
           "(>Hsmtdc & >Hscode & >Hsb_switcher & >Hststk & >[%Hsbounds_tstk_b %Hsbounds_tstk_e]
           & >Hcstk_full_spec & >%Hslen_cstk & Hsstk_interp)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    rewrite /switcher_instrs /assembled_switcher.
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    repeat (iEval (cbn [fmap list_fmap]) in "Hscode").
    repeat (iEval (cbn [concat]) in "Hscode").
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }
    iEval (simplify_map_eq) in "HPC".
    iEval (simplify_map_eq) in "HsPC".

    (* ----------------------------------------------  *)
    (* ------ Lswitch_trusted_stack_exhausted -------  *)
    (* ----------------------------------------------  *)
    focus_block_lockstep 16 "Hscode" "Hcode" as a_tstk_exhausted Ha_tstk_exhausted
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (a_stk ^+ 3)%a); auto; solve_addr.
    (* Load cgp csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; auto; solve_addr.
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (a_stk ^+ 2)%a); auto; solve_addr.
    (* Load cra csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; auto; solve_addr.
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (a_stk ^+ 1)%a); auto; solve_addr.
    (* Load cs1 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; auto; solve_addr.
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some a_stk); auto; solve_addr.
    (* Load cs0 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; auto; solve_addr.
    (* Mov ca0 ENOTENOUGHTRUSTEDSTACK *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Mov ca1 0 *)
    iInstr_spec "Hscode".
    (* Mov ca1 0 *)
    iInstr "Hcode" with "Hlc".
    (* Jmp Lswitch_callee_dead_zeros_z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: set (Lswitch_callee_dead_zeros := default 0 (switcher_labels !! ".Lswitch_callee_dead_zeros"));
         transitivity (Some ((a_switcher_call ^+ Lswitch_callee_dead_zeros)%a)); auto;
         subst Lswitch_callee_dead_zeros; rewrite /switcher_labels; simplify_map_eq;
         solve_addr.
    iEval (simplify_map_eq) in "HPC".
    iEval (simplify_map_eq) in "HsPC".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* ---- clear registers  ---- *)
    focus_block_lockstep 14 "Hscode" "Hcode" as a7 Ha7 "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (clear_registers_post_call_spec with "[- $Hspec $Hj $HPC $HsPC $Hrmap $Hsmap $Hcode $Hscode]")
    ; try solve_pure.
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap' arg_smap')
      "(%Harg_rmap' & %Harg_smap' & Hj & HPC & HsPC & Hrmap & Hsmap & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Both register files are cleared: they are the same map *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hrmap_zero]".
    iDestruct (big_sepM_sep with "Hsmap") as "[Hsmap %Hsmap_zero]".
    assert (arg_smap' = arg_rmap') as ->.
    { symmetry; apply zero_rmaps_eq; auto. by rewrite Harg_rmap' Harg_smap'. }
    clear Harg_smap'.

    focus_block_lockstep 15 "Hscode" "Hcode" as a10 Ha10 "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    assert (is_Some (arg_rmap' !! cnull)) as [wcnull Hcnull]
        by (rewrite -elem_of_dom Harg_rmap' ; set_solver).
    iDestruct (big_sepM_delete _ _ cnull with "Hrmap") as "[Hcnull Hrmap]"; first done.
    iDestruct (big_sepM_delete _ _ cnull with "Hsmap") as "[Hscnull Hsmap]"; first done.
    (* Jalr cnull cra *)
    iInstr_spec "Hscode".
    (* Jalr cnull cra *)
    iInstr "Hcode" with "Hlc".
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcnull]") as "Hrmap".
    iDestruct (big_sepM_insert_delete with "[$Hsmap $Hscnull]") as "Hsmap".
    pose proof (Hrmap_zero _ _ Hcnull) as Hwcnull; cbn in Hwcnull; subst wcnull.
    rewrite insert_id; last done.
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Close the switcher's invariant *)
    iMod ("Hclose_switcher_inv"
           with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk
                  Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
    { iNext. iSplitL "Hmtdc Hcode Hb_switcher Htstk Hcstk_full Hstk_interp".
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
    }

    iApply ("Hpost" $! arg_rmap').
    iDestruct (big_sepM_sep with "[$Hrmap $Hsmap]") as "Hrmap".
    iFrame "∗%".
    iApply (big_sepM_impl with "Hrmap").
    iIntros "!> %r %w %Hr [Hr Hsr]".
    iFrame. iPureIntro. by apply (Hrmap_zero r w).
  Qed.

End Switcher.
