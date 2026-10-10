From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import register_tactics register_tactics_binary.
From griotte Require Import switcher_call_states_binary.

(** * Call routine, blocks 4-7: prepare the callee's stack and unseal, binary model

    Block 4 restricts the stack capability to the callee's stack frame,
    block 5 clears it, block 6 loads the unsealing capability of the
    switcher, and the first instruction of block 7 unseals the entry point of
    the callee, the same in both runs. *)

Section Switcher_Call_Blocks_3.
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

  Lemma switcher_call_block_4_spec
    pc_a
    b_stk e_stk a_stk
    wcs0 swcs0 wcs1 swcs1 :
    let switcher_instrs_4 := switcher_instrs_n 4 in
    let len_switcher_4 := length switcher_instrs_4 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_4)%a ->
    (isWithin a_stk e_stk b_stk e_stk = true) ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cs1 ↣ᵣ swcs1 ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    codefrag pc_a switcher_instrs_4 ∗
    spec_codefrag pc_a switcher_instrs_4 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_4)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_4)%a ∗
        cs0 ↦ᵣ WInt e_stk ∗
        cs0 ↣ᵣ WInt e_stk ∗
        cs1 ↦ᵣ WInt a_stk ∗
        cs1 ↣ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap RWL Local a_stk e_stk a_stk ∗
        csp ↣ᵣ WCap RWL Local a_stk e_stk a_stk ∗
        codefrag pc_a switcher_instrs_4 ∗
        spec_codefrag pc_a switcher_instrs_4 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_4 len_switcher_4; subst switcher_instrs_4 len_switcher_4.
    iIntros (Hsub_reg Hastk) "(#Hspec & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1
      & Hcsp & Hscsp & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* GetE cs0 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    (* GetA cs1 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Subseg csp cs1 cs0 *)
    iInstr_lockstep "Hscode" "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_call_block_6_spec
    pc_a
    wcs0 swcs0 wcs1 swcs1 wpc_b :
    let switcher_instrs_6 := switcher_instrs_n 6 in
    let len_switcher_6 := length switcher_instrs_6 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_6)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cs1 ↣ᵣ swcs1 ∗
    b_switcher ↦ₐ wpc_b ∗
    b_switcher ↣ₐ wpc_b ∗
    codefrag pc_a switcher_instrs_6 ∗
    spec_codefrag pc_a switcher_instrs_6 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_6)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_6)%a ∗
        cs0 ↦ᵣ wpc_b ∗
        cs0 ↣ᵣ wpc_b ∗
        cs1 ↦ᵣ WInt (b_switcher - (pc_a ^+ 1)%a) ∗
        cs1 ↣ᵣ WInt (b_switcher - (pc_a ^+ 1)%a) ∗
        b_switcher ↦ₐ wpc_b ∗
        b_switcher ↣ₐ wpc_b ∗
        codefrag pc_a switcher_instrs_6 ∗
        spec_codefrag pc_a switcher_instrs_6 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_6 len_switcher_6; subst switcher_instrs_6 len_switcher_6.
    iIntros (Hsub_reg) "(#Hspec & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hpc_b & Hspc_b
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* GetB cs1 PC *)
    iInstr_lockstep "Hscode" "Hcode".
    (* GetA cs0 PC *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Sub cs1 cs1 cs0 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Mov cs0 PC *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Lea cs0 cs1 *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_lea_success_reg with "[$Hspec $Hj $HsPC $Hsi $Hscs0 $Hscs1]")
      as "(Hj & HsPC & Hsi & Hscs1 & Hscs0)";
      [solve_ndisj|solve_pure|solve_pure|solve_pure| |solve_pure|solve_pure|].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iSpecSeq.
    iSpecialize ("Hscode" with "[$]").
    (* Lea cs0 cs1 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]"); auto; [solve_pure..| |].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    (* Lea cs0 (-2)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:= b_switcher); solve_addr.
    (* Load cs0 cs0 *)
    iInstr_lockstep "Hscode" "Hcode".
    iApply "Hpost"; iFrame.
  Qed.


  (** First instruction of block 7: unseal the entry point. *)
  Lemma switcher_call_block_7_unseal_spec
    pc_a wct1 swct1 :
    let switcher_instrs_7 := switcher_instrs_n 7 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length switcher_instrs_7)%a ->
    (∀ wsb, wct1 = WSealed ot_switcher wsb → swct1 = WSealed ot_switcher wsb) ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    cs0 ↦ᵣ WSealRange (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    cs0 ↣ᵣ WSealRange (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    ct1 ↦ᵣ wct1 ∗
    ct1 ↣ᵣ swct1 ∗
    codefrag pc_a switcher_instrs_7 ∗
    spec_codefrag pc_a switcher_instrs_7 ∗
    ▷ ( ∀ wsb,
        ⌜ wct1 = WSealed ot_switcher wsb ⌝ ∗
        ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
        cs0 ↦ᵣ WSealRange (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        cs0 ↣ᵣ WSealRange (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        ct1 ↦ᵣ WSealable wsb ∗
        ct1 ↣ᵣ WSealable wsb ∗
        codefrag pc_a switcher_instrs_7 ∗
        spec_codefrag pc_a switcher_instrs_7 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_7; subst switcher_instrs_7.
    iIntros (Hsub_reg Hct1) "(#Hspec & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hct1 & Hsct1
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    destruct (is_sealed_with_o wct1 ot_switcher) eqn:Hwct1; cycle 1.
    { (* UnSeal ct1 cs0 ct1 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_unseal_nomatch_r2 with "[$HPC $Hi $Hct1 $Hcs0]"); try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    assert (∃ wsb, wct1 = WSealed ot_switcher wsb) as [wsb ->].
    { destruct wct1 as [ | [] | |]; cbn in Hwct1; try discriminate.
      exists sb. apply Z.eqb_eq in Hwct1.
      replace ot with ot_switcher by solve_addr.
      done. }
    rewrite (Hct1 wsb eq_refl).
    (* UnSeal ct1 cs0 ct1 *)
    iInstr_lockstep "Hscode" "Hcode".
    all: try done.
    1,2: rewrite /withinBounds; pose proof ot_switcher_size; solve_finz.
    iApply "Hpost"; iFrame; done.
  Qed.

  (** Blocks 4-7: restrict the stack capability to the callee's stack frame
      [[a ^+ 4, e)], clear it, load the unsealing capability, and unseal the
      entry point [wct1]. *)
  Lemma switcher_call_blocks_3_spec
    (b e a : Addr) (stk_mem stk_mem_spec : list Word) (wcs0 swcs0 wcs1 swcs1 wct1 swct1 : Word) :
    switcher_stk_bounds b e a ->
    (∀ wsb, wct1 = WSealed ot_switcher wsb → swct1 = WSealed ot_switcher wsb) ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ switcher_block_pc 4 ∗
    PC ↣ᵣ switcher_block_pc 4 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cs1 ↣ᵣ swcs1 ∗
    csp ↦ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    csp ↣ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ stk_mem ]] ∗
    [[ (a ^+ 4)%a , e ]] ↣ₐ [[ stk_mem_spec ]] ∗
    b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    b_switcher ↣ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    ct1 ↦ᵣ wct1 ∗
    ct1 ↣ᵣ swct1 ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ∀ wsb,
        ⌜ wct1 = WSealed ot_switcher wsb ⌝ ∗
        ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ switcher_pc (switcher_block_offset 7 + 1) ∗
        PC ↣ᵣ switcher_pc (switcher_block_offset 7 + 1) ∗
        cs0 ↦ᵣ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        cs0 ↣ᵣ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        (∃ wcs1', cs1 ↦ᵣ wcs1' ∗ cs1 ↣ᵣ wcs1') ∗
        csp ↦ᵣ WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a ∗
        csp ↣ᵣ WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
        [[ (a ^+ 4)%a , e ]] ↣ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
        b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        b_switcher ↣ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        ct1 ↦ᵣ WSealable wsb ∗
        ct1 ↣ᵣ WSealable wsb ∗
        switcher_code ∗
        switcher_spec_code -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hct1_eq)
      "(#Hspec & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcsp & Hscsp & Hstk & Hsstk
      & Hb_switcher & Hsb_switcher & Hct1 & Hsct1 & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".

    (* Block 4: restrict the stack capability *)
    switcher_focus_block_lockstep 4 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_4_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hcsp $Hscsp $Hcode $Hscode]");
      [done| |iNext].
    { rewrite /isWithin; solve_addr+Hba Hba3 Ha4. }
    iIntros "(Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcsp & Hscsp & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Block 5: clear the callee's stack frame *)
    switcher_focus_block_lockstep 5 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (clear_stack_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode $Hcsp $Hscsp $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hstk $Hsstk]");
      try solve_pure.
    { solve_addr+. }
    { solve_addr+Hba Hba3 Ha4. }
    iIntros "!> (Hj & HPC & HsPC & Hcsp & Hscsp & Hcs0 & Hcs1 & Hscs0 & Hscs1 & Hcode & Hscode & Hstk & Hsstk)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Block 6: load the unsealing capability *)
    switcher_focus_block_lockstep 6 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_6_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hb_switcher $Hsb_switcher $Hcode $Hscode]");
      first done.
    iNext; iIntros "(Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hb_switcher & Hsb_switcher
      & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Block 7: unseal the entry point *)
    switcher_focus_block_lockstep 7 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_7_unseal_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hct1 $Hsct1 $Hcode $Hscode]"); [done|done|].
    iNext; iIntros (wsb) "(-> & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hct1 & Hsct1 & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    switcher_change_pc (switcher_block_offset 7 + 1)%Z.
    iApply "Hpost"; iFrame; done.
  Qed.

End Switcher_Call_Blocks_3.
