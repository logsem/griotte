From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import register_tactics register_tactics_binary.
From griotte Require Import switcher_call_states_binary.

(** * Call routine, blocks 2-3: spill and push on the trusted stack, binary model

    Block 2 spills the callee-save registers on the caller's stack, and
    block 3 pushes the caller's stack pointer on the trusted stack, in both
    runs. Both runs have the same stack pointer and the same trusted stack
    pointer, hence take the same branch. When the trusted stack is
    exhausted, the execution jumps to block 16 (see
    [switcher_call_blocks_5_binary]). *)

Section Switcher_Call_Blocks_2.
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

  Lemma switcher_call_block_2_spec
    pc_a
    b_stk e_stk a_stk
    wcs0 swcs0 wcs1 swcs1 wcra swcra wcgp swcgp
    stk_mem stk_mem_spec :
    let switcher_instrs_2 := switcher_instrs_n 2 in
    let len_switcher_2 := length switcher_instrs_2 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_2)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cs1 ↣ᵣ swcs1 ∗
    cra ↦ᵣ wcra ∗
    cra ↣ᵣ swcra ∗
    cgp ↦ᵣ wcgp ∗
    cgp ↣ᵣ swcgp ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    [[a_stk,e_stk]]↦ₐ[[stk_mem]] ∗
    [[a_stk,e_stk]]↣ₐ[[stk_mem_spec]] ∗
    codefrag pc_a switcher_instrs_2 ∗
    spec_codefrag pc_a switcher_instrs_2 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_2)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_2)%a ∗
        cs0 ↦ᵣ wcs0 ∗
        cs0 ↣ᵣ swcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cs1 ↣ᵣ swcs1 ∗
        cra ↦ᵣ wcra ∗
        cra ↣ᵣ swcra ∗
        cgp ↦ᵣ wcgp ∗
        cgp ↣ᵣ swcgp ∗
        csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
        csp ↣ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcra wcgp ∗
        switcher_stk_cells_spec a_stk swcs0 swcs1 swcra swcgp ∗
        [[(a_stk ^+ 4)%a,e_stk]]↦ₐ[[drop 4 stk_mem]] ∗
        [[(a_stk ^+ 4)%a,e_stk]]↣ₐ[[drop 4 stk_mem_spec]] ∗
        ⌜ switcher_stk_bounds b_stk e_stk a_stk ⌝ ∗
        codefrag pc_a switcher_instrs_2 ∗
        spec_codefrag pc_a switcher_instrs_2 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_2 len_switcher_2; subst switcher_instrs_2 len_switcher_2.
    iIntros (Hsub_reg) "(#Hspec & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcra & Hscra
      & Hcgp & Hscgp & Hcsp & Hscsp & Hstk & Hsstk & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    iDestruct (big_sepL2_length with "Hsstk") as %Hsstklen.
    rewrite finz_seq_between_length in Hstklen.
    rewrite finz_seq_between_length in Hsstklen.

    destruct (decide (b_stk <= a_stk < e_stk)%a) as [Hastk_inbounds|Hastk_inbounds]; cycle 1.
    { (* Store csp cs0 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs0 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk_inbounds.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hastk_inbounds.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw0 stk_mem_spec]; simplify_eq.
    assert (is_Some (a_stk + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hastk_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk Hstk]"; eauto.
    { solve_addr+Hastk_inbounds Hastk1. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk Hsstk]"; eauto.
    { solve_addr+Hastk_inbounds Hastk1. }
    (* Store csp cs0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.
    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    destruct (decide (b_stk <= (a_stk ^+ 1)%a < e_stk)%a) as [Hastk1_inbounds|Hastk1_inbounds]; cycle 1.
    { (* Store csp cs1 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs1 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk1_inbounds.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hastk1_inbounds.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw1 stk_mem_spec]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2];[solve_addr+Hastk1 Hastk1_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk1 Hstk]"; eauto.
    { solve_addr+Hastk1_inbounds Hastk1 Hastk2. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk1 Hsstk]"; eauto.
    { solve_addr+Hastk1_inbounds Hastk1 Hastk2. }
    (* Store csp cs1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.
    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    destruct (decide (b_stk <= (a_stk ^+ 2)%a < e_stk)%a) as [Hastk2_inbounds|Hastk2_inbounds]; cycle 1.
    { (* Store csp cra *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcra $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk2_inbounds.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hastk2_inbounds.
    destruct stk_mem as [|w2 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw2 stk_mem_spec]; simplify_eq.
    assert (is_Some (a_stk2 + 1)%a) as [a_stk3 Hastk3];[solve_addr+Hastk1 Hastk2 Hastk2_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk2 Hstk]"; eauto.
    { solve_addr+Hastk2_inbounds Hastk1 Hastk2 Hastk3. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk2 Hsstk]"; eauto.
    { solve_addr+Hastk2_inbounds Hastk1 Hastk2 Hastk3. }
    (* Store csp cra *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.
    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    destruct (decide (b_stk <= (a_stk ^+ 3)%a < e_stk)%a) as [Hastk3_inbounds|Hastk3_inbounds]; cycle 1.
    { (* Store csp cgp *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcgp $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk3_inbounds.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hastk3_inbounds.
    destruct stk_mem as [|w3 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw3 stk_mem_spec]; simplify_eq.
    assert (is_Some (a_stk3 + 1)%a) as [a_stk4 Hastk4];[solve_addr+Hastk1 Hastk2 Hastk3 Hastk3_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk3 Hstk]"; eauto.
    { solve_addr+Hastk3_inbounds Hastk1 Hastk2 Hastk3 Hastk4. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk3 Hsstk]"; eauto.
    { solve_addr+Hastk3_inbounds Hastk1 Hastk2 Hastk3 Hastk4. }
    assert ((a_stk + 4)%a = Some a_stk4) as Hastk by solve_addr.
    (* Store csp cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.
    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    replace a_stk1 with (a_stk ^+ 1)%a by solve_addr.
    replace a_stk2 with (a_stk ^+ 2)%a by solve_addr.
    replace a_stk3 with (a_stk ^+ 3)%a by solve_addr.
    replace a_stk4 with (a_stk ^+ 4)%a by solve_addr.
    iApply "Hpost". cbn [drop]. iFrame.
    iPureIntro; rewrite /switcher_stk_bounds; repeat split; solve_addr.
  Qed.

  Lemma switcher_call_block_3_spec
    pc_a
    a_tstk tstk_next ststk_next
    wcs0 swcs0 wctp swctp wct2 swct2 wstk :
    let switcher_instrs_3 := switcher_instrs_n 3 in
    let len_switcher_3 := length switcher_instrs_3 in
    let a_tstk1 := (a_tstk ^+ 1)%a in
    let a_tstk2 := (a_tstk ^+ 2)%a in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_3)%a ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->
    (pc_a ^+ 6 + 114)%a = Some (pc_a ^+ 120)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    csp ↦ᵣ wstk ∗
    csp ↣ᵣ wstk ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[a_tstk1,e_trusted_stack]]↦ₐ[[tstk_next]] ∗
    [[a_tstk1,e_trusted_stack]]↣ₐ[[ststk_next]] ∗
    codefrag pc_a switcher_instrs_3 ∗
    spec_codefrag pc_a switcher_instrs_3 ∗
    ▷ ( ( ⤇ Seq (Instr Executable) ∗
          PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_3)%a ∗
          PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ len_switcher_3)%a ∗
          cs0 ↦ᵣ WInt a_tstk1 ∗
          cs0 ↣ᵣ WInt a_tstk1 ∗
          ctp ↦ᵣ WInt 1 ∗
          ctp ↣ᵣ WInt 1 ∗
          ct2 ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
          ct2 ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
          csp ↦ᵣ wstk ∗
          csp ↣ᵣ wstk ∗
          mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
          mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
          a_tstk1 ↦ₐ wstk ∗
          a_tstk1 ↣ₐ wstk ∗
          [[a_tstk2,e_trusted_stack]]↦ₐ[[drop 1 tstk_next]] ∗
          [[a_tstk2,e_trusted_stack]]↣ₐ[[drop 1 ststk_next]] ∗
          ⌜ (a_tstk1 + 1)%a = Some a_tstk2 ∧ (a_tstk1 < e_trusted_stack)%a ⌝ ∗
          codefrag pc_a switcher_instrs_3 ∗
          spec_codefrag pc_a switcher_instrs_3 ∗
          £ 2 )
        ∨
        ( ⤇ Seq (Instr Executable) ∗
          PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 120)%a ∗
          PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 120)%a ∗
          cs0 ↦ᵣ WInt (a_tstk + 1) ∗
          cs0 ↣ᵣ WInt (a_tstk + 1) ∗
          ctp ↦ᵣ WInt 0 ∗
          ctp ↣ᵣ WInt 0 ∗
          ct2 ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
          ct2 ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
          csp ↦ᵣ wstk ∗
          csp ↣ᵣ wstk ∗
          mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
          mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
          [[a_tstk1,e_trusted_stack]]↦ₐ[[tstk_next]] ∗
          [[a_tstk1,e_trusted_stack]]↣ₐ[[ststk_next]] ∗
          codefrag pc_a switcher_instrs_3 ∗
          spec_codefrag pc_a switcher_instrs_3 )
        -∗ switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_3 len_switcher_3 a_tstk1 a_tstk2; subst switcher_instrs_3 len_switcher_3.
    iIntros (Hsub_reg Hbounds_tstk_b Hbounds_tstk_e Hpc_fail)
      "(#Hspec & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hctp & Hsctp & Hct2 & Hsct2 & Hcsp & Hscsp
      & Hmtdc & Hsmtdc & Htstk & Hststk & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* ReadSR ct2 mtdc *)
    iInstr_lockstep "Hscode" "Hcode".
    (* GetA cs0 ct2 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Add cs0 cs0 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    (* GetE ctp ct2 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Lt ctp cs0 ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    destruct ( (a_tstk + 1 <? e_trusted_stack)%Z) eqn:Hsize_tstk
    ; iEval (cbn) in "Hctp"
    ; iEval (cbn) in "Hsctp"
    ; cycle 1.
    { (* Jnz 2%Z ctp *)
      iInstr_lockstep "Hscode" "Hcode".
      (* Jmp (".Lswitch_trusted_stack_exhausted")%asm *)
      iInstr_lockstep "Hscode" "Hcode".
      iApply "Hpost".
      iRight.
      iFrame.
    }

    (* Jnz 2%Z ctp *)
    iInstr_spec "Hscode".
    (* Jnz 2%Z ctp *)
    iInstr "Hcode" with "Hlc".

    assert ( ∃ f3, (a_tstk + 1)%a = Some f3) as [f3 Htastk] by (exists (a_tstk ^+ 1)%a; solve_addr+Hsize_tstk).
    (* Lea ct2 1 *)
    iInstr_spec "Hscode".
    (* Lea ct2 1 *)
    iInstr "Hcode" with "Hlc".

    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    iDestruct (big_sepL2_length with "Hststk") as %Hslen.
    subst a_tstk1.
    erewrite finz_incr_eq in Hlen;[|eauto].
    erewrite finz_incr_eq in Hslen;[|eauto].
    rewrite finz_seq_between_length in Hlen.
    rewrite finz_seq_between_length in Hslen.
    destruct tstk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hlen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    destruct ststk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hslen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    assert (is_Some (f3 + 1)%a) as [f4 Hf4];[solve_addr|].
    iDestruct (region_pointsto_cons _ f4 with "Htstk") as "[Hf3 Htstk]";[solve_addr|solve_addr|].
    iDestruct (spec_region_pointsto_cons _ f4 with "Hststk") as "[Hsf3 Hststk]";[solve_addr|solve_addr|].
    replace (a_tstk ^+ 1)%a with f3 by solve_addr.
    (* Store ct2 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.
    (* WriteSR mtdc ct2 *)
    iInstr_lockstep "Hscode" "Hcode".

    replace (@finz.to_z MemNum f3)%Z with ((@finz.to_z MemNum a_tstk) + 1)%Z by solve_addr.
    replace f4 with a_tstk2 by (subst a_tstk2; solve_addr).
    iApply "Hpost"; iLeft; cbn [drop]; rewrite !drop_0; iFrame.
    iPureIntro; split; subst a_tstk2; solve_addr.
  Qed.


  (** Blocks 2-3: spill the callee-save registers on the caller's stack
      [[a, e)], and push the stack pointer on the trusted stack. *)
  Lemma switcher_call_blocks_2_spec
    (b e a : Addr) (stk_mem stk_mem_spec : list Word)
    (wcs0 swcs0 wcs1 swcs1 wcra swcra wcgp swcgp wctp swctp wct2 swct2 : Word)
    (a_tstk : Addr) (tstk_next ststk_next : list Word) :
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ switcher_block_pc 2 ∗
    PC ↣ᵣ switcher_block_pc 2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cs1 ↣ᵣ swcs1 ∗
    cra ↦ᵣ wcra ∗
    cra ↣ᵣ swcra ∗
    cgp ↦ᵣ wcgp ∗
    cgp ↣ᵣ swcgp ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    csp ↦ᵣ WCap RWL Local b e a ∗
    csp ↣ᵣ WCap RWL Local b e a ∗
    [[ a , e ]] ↦ₐ [[ stk_mem ]] ∗
    [[ a , e ]] ↣ₐ [[ stk_mem_spec ]] ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↣ₐ [[ ststk_next ]] ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ⌜ switcher_stk_bounds b e a ⌝ ∗
        ⤇ Seq (Instr Executable) ∗
        cs1 ↦ᵣ wcs1 ∗
        cs1 ↣ᵣ swcs1 ∗
        cra ↦ᵣ wcra ∗
        cra ↣ᵣ swcra ∗
        cgp ↦ᵣ wcgp ∗
        cgp ↣ᵣ swcgp ∗
        csp ↦ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
        csp ↣ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
        switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
        switcher_stk_cells_spec a swcs0 swcs1 swcra swcgp ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ drop 4 stk_mem ]] ∗
        [[ (a ^+ 4)%a , e ]] ↣ₐ [[ drop 4 stk_mem_spec ]] ∗
        switcher_code ∗
        switcher_spec_code ∗
        ( ( ⌜ ((a_tstk ^+ 1) + 1)%a = Some (a_tstk ^+ 2)%a ⌝ ∗
            ⌜ (a_tstk ^+ 1 < e_trusted_stack)%a ⌝ ∗
            PC ↦ᵣ switcher_block_pc 4 ∗
            PC ↣ᵣ switcher_block_pc 4 ∗
            cs0 ↦ᵣ WInt (a_tstk ^+ 1)%a ∗
            cs0 ↣ᵣ WInt (a_tstk ^+ 1)%a ∗
            ctp ↦ᵣ WInt 1 ∗
            ctp ↣ᵣ WInt 1 ∗
            ct2 ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack (a_tstk ^+ 1)%a ∗
            ct2 ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack (a_tstk ^+ 1)%a ∗
            mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack (a_tstk ^+ 1)%a ∗
            mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack (a_tstk ^+ 1)%a ∗
            (a_tstk ^+ 1)%a ↦ₐ WCap RWL Local b e (a ^+ 4)%a ∗
            (a_tstk ^+ 1)%a ↣ₐ WCap RWL Local b e (a ^+ 4)%a ∗
            [[ (a_tstk ^+ 2)%a , e_trusted_stack ]] ↦ₐ [[ drop 1 tstk_next ]] ∗
            [[ (a_tstk ^+ 2)%a , e_trusted_stack ]] ↣ₐ [[ drop 1 ststk_next ]] ∗
            £ 2 )
          ∨
          ( PC ↦ᵣ switcher_block_pc 16 ∗
            PC ↣ᵣ switcher_block_pc 16 ∗
            cs0 ↦ᵣ WInt (a_tstk + 1)%Z ∗
            cs0 ↣ᵣ WInt (a_tstk + 1)%Z ∗
            ctp ↦ᵣ WInt 0 ∗
            ctp ↣ᵣ WInt 0 ∗
            ct2 ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
            ct2 ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
            mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
            mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
            [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
            [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↣ₐ [[ ststk_next ]] ) )
        -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros (Htstk_b Htstk_e)
      "(#Hspec & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcra & Hscra & Hcgp & Hscgp
      & Hctp & Hsctp & Hct2 & Hsct2 & Hcsp & Hscsp & Hstk & Hsstk
      & Hmtdc & Hsmtdc & Htstk & Hststk & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".

    (* Block 2: spill the callee-save registers *)
    switcher_focus_block_lockstep 2 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_2_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hcra $Hscra $Hcgp $Hscgp
        $Hcsp $Hscsp $Hstk $Hsstk $Hcode $Hscode]"); first done.
    iNext; iIntros
      "(Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcra & Hscra & Hcgp & Hscgp & Hcsp & Hscsp
      & Hcells & Hscells & Hstk & Hsstk & %Hbounds & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    pose proof Hbounds as (Hba & Hba3 & Ha4).

    (* Block 3: push the stack pointer on the trusted stack *)
    switcher_focus_block_lockstep 3 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_3_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hctp $Hsctp $Hct2 $Hsct2 $Hcsp $Hscsp
        $Hmtdc $Hsmtdc $Htstk $Hststk $Hcode $Hscode]");
      [done|done|done|offsets_compute; solve_addr|].
    iNext.
    iIntros "[
      (Hj & HPC & HsPC & Hcs0 & Hscs0 & Hctp & Hsctp & Hct2 & Hsct2 & Hcsp & Hscsp & Hmtdc & Hsmtdc
        & Ha_tstk1 & Hsa_tstk1 & Htstk & Hststk & %Ha_tstk1_facts & Hcode & Hscode & Hlc)
      |
      (Hj & HPC & HsPC & Hcs0 & Hscs0 & Hctp & Hsctp & Hct2 & Hsct2 & Hcsp & Hscsp & Hmtdc & Hsmtdc
        & Htstk & Hststk & Hcode & Hscode)
    ]"; subst hcont hscont;
      unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    - destruct Ha_tstk1_facts as [Ha_tstk2 Ha_tstk1_bound].
      switcher_change_pc (switcher_block_offset 4).
      iApply "Hpost"; iFrame.
      iSplit; first done.
      iLeft; iFrame "∗ %".
    - switcher_change_pc (switcher_block_offset 16).
      iApply "Hpost"; iFrame.
      iSplit; first done.
      iRight; iFrame.
  Qed.


  (** Block 2 fails when the stack pointer is not a valid stack capability. *)
  Lemma switcher_call_blocks_2_fail_spec (wcsp wcs0 : Word) :
    switcher_csp_checked wcsp ->
    (∀ b e a, wcsp = WCap RWL Local b e a -> (a < b)%a) ->

    PC ↦ᵣ switcher_block_pc 2 ∗
    csp ↦ᵣ wcsp ∗
    cs0 ↦ᵣ wcs0 ∗
    switcher_code
    ⊢ switcher_wp.
  Proof.
    iIntros (Hchecked Hnot_stk) "(HPC & Hcsp & Hcs0 & Hcode)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    focus_block_nochangePC 2 "Hcode" as a_block Ha_block "Hcode" "Hcls".
    assert (a_block = (a_switcher_call ^+ switcher_block_offset 2)%a) as ->
      by (cbn in Ha_block; offsets_compute; solve_addr).
    (* Store csp cs0 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    destruct (is_cap wcsp) eqn:Hcap; cycle 1.
    { iApply (wp_store_fail_reg_not_cap with "[$HPC $Hi $Hcs0 $Hcsp]"); try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr"; done. }
    destruct wcsp as [| [p g b e a|] | | ]; cbn in Hcap; try discriminate.
    destruct (switcher_csp_checked_cap _ _ _ _ _ Hchecked) as [-> ->].
    specialize (Hnot_stk b e a eq_refl).
    iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs0 $Hcsp]"); try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr"; done.
  Qed.

End Switcher_Call_Blocks_2.
