From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_call_states.

(** * Call routine, blocks 2-3: spill and push on the trusted stack

    Block 2 spills the callee-save registers on the caller's stack, and
    block 3 pushes the caller's stack pointer on the trusted stack. When the
    trusted stack is exhausted, the execution jumps to block 16 (see
    [switcher_call_blocks_5]). *)

Section Switcher_Call_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_call_block_2_spec
    b_stk e_stk a_stk
    pc_b pc_e pc_a
    wcs0 wcs1 wcra wcgp
    stk_mem :
    let switcher_instrs_2 := (switcher_instrs_n 2) in
    let len_switcher_2 := length switcher_instrs_2 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_2)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    cgp ↦ᵣ wcgp ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    [[a_stk,e_stk]]↦ₐ[[stk_mem]] ∗
    codefrag pc_a switcher_instrs_2 ∗
    ▷ ( ∀ stk_mem',
          ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_2)%a ∗
            cs0 ↦ᵣ wcs0 ∗
            cs1 ↦ᵣ wcs1 ∗
            cra ↦ᵣ wcra ∗
            cgp ↦ᵣ wcgp ∗
            csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
            a_stk ↦ₐ wcs0 ∗
            (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
            (a_stk ^+ 2)%a ↦ₐ wcra ∗
            (a_stk ^+ 3)%a ↦ₐ wcgp ∗
            [[(a_stk ^+ 4)%a,e_stk]]↦ₐ[[stk_mem']] ∗
            ⌜ (b_stk <= a_stk)%a ∧ (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ∧ is_Some (a_stk + 4)%a ⌝ ∗
            ⌜ stk_mem' = drop 4 stk_mem ⌝ ∗
            codefrag pc_a switcher_instrs_2 -∗
            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
          )
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_2 len_switcher_2; subst switcher_instrs_2 len_switcher_2.
    iIntros (Hsub_reg) "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hstk & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Store csp cs0 --- *)
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.
    destruct (decide (b_stk <= a_stk < e_stk)%a) as [Hastk_inbounds|Hastk_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs0 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk_inbounds.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    assert (is_Some (a_stk + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hastk_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk Hstk]"; eauto.
    { solve_addr+Hastk_inbounds Hastk1. }

    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".


    (* --- Store csp cs1 --- *)
    destruct (decide (b_stk <= (a_stk ^+ 1)%a < e_stk)%a) as [Hastk1_inbounds|Hastk1_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs1 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk1_inbounds.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2];[solve_addr+Hastk1 Hastk1_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk1 Hstk]"; eauto.
    { solve_addr+Hastk1_inbounds Hastk1 Hastk2. }

    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    (* --- Store csp cra --- *)
    destruct (decide (b_stk <= (a_stk ^+ 2)%a < e_stk)%a) as [Hastk2_inbounds|Hastk2_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcra $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk2_inbounds.
    destruct stk_mem as [|w2 stk_mem]; simplify_eq.
    assert (is_Some (a_stk2 + 1)%a) as [a_stk3 Hastk3];[solve_addr+Hastk1 Hastk2 Hastk2_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk2 Hstk]"; eauto.
    { solve_addr+Hastk2_inbounds Hastk1 Hastk2 Hastk3. }

    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    (* --- Store csp cgp --- *)
    destruct (decide (b_stk <= (a_stk ^+ 3)%a < e_stk)%a) as [Hastk3_inbounds|Hastk3_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcgp $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk3_inbounds.
    destruct stk_mem as [|w3 stk_mem]; simplify_eq.
    assert (is_Some (a_stk3 + 1)%a) as [a_stk4 Hastk4];[solve_addr+Hastk1 Hastk2 Hastk3 Hastk3_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk3 Hstk]"; eauto.
    { solve_addr+Hastk3_inbounds Hastk1 Hastk2 Hastk3 Hastk4. }
    assert ((a_stk + 4)%a = Some a_stk4) as Hastk by solve_addr.

    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    replace (a_stk1) with (a_stk ^+1)%a by solve_addr.
    replace (a_stk2) with (a_stk ^+2)%a by solve_addr.
    replace (a_stk3) with (a_stk ^+3)%a by solve_addr.
    replace (a_stk4) with (a_stk ^+4)%a by solve_addr.
    iApply ("Hpost" $! stk_mem). iFrame.
    iPureIntro; repeat split; solve_addr.
  Qed.

  Lemma switcher_call_block_3_spec
    pc_b pc_e pc_a
    b_trusted_stack e_trusted_stack a_tstk tstk_next
    wcs0 wctp wct2 wstk :
    let switcher_instrs_3 := (switcher_instrs_n 3) in
    let len_switcher_3 := length switcher_instrs_3 in
    let a_tstk1 := (a_tstk ^+ 1)%a in
    let a_tstk2 := (a_tstk ^+ 2)%a in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_3)%a ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->

    (pc_a ^+ 6 + 114)%a = Some (pc_a ^+ 120)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ wstk ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[a_tstk1,e_trusted_stack]]↦ₐ[[tstk_next]] ∗
    codefrag pc_a switcher_instrs_3 ∗
    ▷  (
        (∃ tstk_next',
            PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_3)%a ∗
              cs0 ↦ᵣ WInt (a_tstk1) ∗
              ctp ↦ᵣ WInt 1 ∗
              ct2 ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
              csp ↦ᵣ wstk ∗
              mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
              a_tstk1 ↦ₐ wstk ∗
              [[a_tstk2,e_trusted_stack]]↦ₐ[[tstk_next']] ∗
              ⌜ (a_tstk1 + 1)%a = Some a_tstk2 ∧ (a_tstk1 < e_trusted_stack)%a ⌝ ∗
              ⌜ tstk_next' = drop 1 tstk_next ⌝ ∗
              codefrag pc_a switcher_instrs_3 ∗
              £ 2
        )
        ∨
          (
            ⌜ ¬ (a_tstk + 1 < e_trusted_stack)%Z ⌝ ∗
            PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 120)%a ∗
            cs0 ↦ᵣ WInt (a_tstk + 1) ∗
            ctp ↦ᵣ WInt 0 ∗
            ct2 ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
            csp ↦ᵣ wstk ∗
            mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
            [[a_tstk1,e_trusted_stack]]↦ₐ[[tstk_next]] ∗
            codefrag pc_a switcher_instrs_3
          )
          -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_3 len_switcher_3 a_tstk1 a_tstk2; subst switcher_instrs_3 len_switcher_3.
    iIntros (Hsub_reg Hbounds_tstk_b Hbounds_tstk_e Hpc_fail)
      "(HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc & Htstk & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- ReadSR ct2 mtdc --- *)
    iInstr "Hcode".

    (* --- GetA cs0 ct2 --- *)
    iInstr "Hcode".

    (* --- Add cs0 cs0 1%Z --- *)
    iInstr "Hcode".

    (* --- GetE ctp ct2 --- *)
    iInstr "Hcode".

    (* --- Sub ctp ctp cs0 --- *)
    iInstr "Hcode".

    (* --- Jnz 2%Z ctp --- *)
    destruct ( (a_tstk + 1 <? e_trusted_stack)%Z) eqn:Hsize_tstk
    ; iEval (cbn) in "Hctp"
    ; cycle 1.
    {
      iInstr "Hcode".
      (* Jmp (inl 114%Z) *)
      iInstr "Hcode".
      iApply "Hpost".
      iRight.
      iFrame.
      iPureIntro; solve_addr.
    }

    iInstr "Hcode" with "Hlc".

    (* --- Lea ct2 1 --- *)
    assert ( ∃ f3, (a_tstk + 1)%a = Some f3) as [f3 Htastk] by (exists (a_tstk ^+ 1)%a; solve_addr+Hsize_tstk).
    iInstr "Hcode" with "Hlc".

    (* --- Store ct2 csp --- *)
    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    subst a_tstk1.
    erewrite finz_incr_eq in Hlen;[|eauto].
    rewrite finz_seq_between_length in Hlen.
    destruct tstk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hlen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    assert (is_Some (f3 + 1)%a) as [f4 Hf4];[solve_addr|].
    iDestruct (region_pointsto_cons _ f4 with "Htstk") as "[Hf3 Htstk]";[solve_addr|solve_addr|].
    replace (a_tstk ^+ 1)%a with f3 by solve_addr.
    iInstr "Hcode".
    { rewrite /withinBounds; solve_addr. }

    (* --- WriteSR mtdc ct2 --- *)
    iInstr "Hcode".


    replace (@finz.to_z MemNum f3)%Z with ((@finz.to_z MemNum a_tstk) + 1)%Z by solve_addr.
    replace f4 with a_tstk2 by (subst a_tstk2; solve_addr).
    iApply "Hpost"; iLeft; iFrame.
    iPureIntro; split;[split|].
    - subst a_tstk2; solve_addr.
    - subst a_tstk2; solve_addr.
    - cbn; by rewrite drop_0.
  Qed.


  (** Blocks 2-3: spill the callee-save registers on the caller's stack
      [[a, e)], and push the stack pointer on the trusted stack. *)
  Lemma switcher_call_blocks_2_spec
    (b e a : Addr) (stk_mem : list Word)
    (wcs0 wcs1 wcra wcgp wctp wct2 : Word)
    (a_tstk : Addr) (tstk_next : list Word) :
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->

    PC ↦ᵣ switcher_block_pc 2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    cgp ↦ᵣ wcgp ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap RWL Local b e a ∗
    [[ a , e ]] ↦ₐ [[ stk_mem ]] ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_code ∗
    ▷ ( ⌜ switcher_stk_bounds b e a ⌝ ∗
        cs1 ↦ᵣ wcs1 ∗
        cra ↦ᵣ wcra ∗
        cgp ↦ᵣ wcgp ∗
        csp ↦ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
        switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ drop 4 stk_mem ]] ∗
        switcher_code ∗
        ( ( ⌜ ((a_tstk ^+ 1) + 1)%a = Some (a_tstk ^+ 2)%a ⌝ ∗
            ⌜ (a_tstk ^+ 1 < e_trusted_stack)%a ⌝ ∗
            PC ↦ᵣ switcher_block_pc 4 ∗
            cs0 ↦ᵣ WInt (a_tstk ^+ 1)%a ∗
            ctp ↦ᵣ WInt 1 ∗
            ct2 ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack (a_tstk ^+ 1)%a ∗
            mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack (a_tstk ^+ 1)%a ∗
            (a_tstk ^+ 1)%a ↦ₐ WCap RWL Local b e (a ^+ 4)%a ∗
            [[ (a_tstk ^+ 2)%a , e_trusted_stack ]] ↦ₐ [[ drop 1 tstk_next ]] ∗
            £ 2 )
          ∨
          ( PC ↦ᵣ switcher_block_pc 16 ∗
            cs0 ↦ᵣ WInt (a_tstk + 1)%Z ∗
            ctp ↦ᵣ WInt 0 ∗
            ct2 ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
            mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
            [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ) )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Htstk_b Htstk_e)
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hctp & Hct2 & Hcsp & Hstk
      & Hmtdc & Htstk & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".

    (* Block 2: spill the callee-save registers *)
    switcher_focus_block 2 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_2_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hcsp $Hstk $Hcode]"); first done.
    iNext; iIntros (stk_mem')
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hstk & %Hbounds & -> & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    destruct Hbounds as (Hba & Hba3 & [a4 Ha4]).
    assert ((a + 4)%a = Some (a ^+ 4)%a) as Ha4' by solve_addr.

    (* Block 3: push the stack pointer on the trusted stack *)
    switcher_focus_block 3 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_3_spec with
      "[- $HPC $Hcs0 $Hctp $Hct2 $Hcsp $Hmtdc $Htstk $Hcode]"); [done|done|done|offsets_compute; solve_addr|].
    iNext.
    iIntros "[
      (%tstk_next' & HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc
        & Ha_tstk1 & Htstk & %Ha_tstk1_facts & -> & Hcode & Hlc)
      |
      (%Htstk_full & HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc & Htstk & Hcode)
    ]"; unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    - destruct Ha_tstk1_facts as [Ha_tstk2 Ha_tstk1_bound].
      switcher_change_pc (switcher_block_offset 4).
      iApply "Hpost"; iFrame.
      iSplit; first (iPureIntro; split; [solve_addr|split; [solve_addr|done] ]).
      iLeft; iFrame "∗ %".
    - switcher_change_pc (switcher_block_offset 16).
      iApply "Hpost"; iFrame.
      iSplit; first (iPureIntro; split; [solve_addr|split; [solve_addr|done] ]).
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
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hchecked Hnot_stk) "(HPC & Hcsp & Hcs0 & Hcode)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    switcher_focus_block 2 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
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
