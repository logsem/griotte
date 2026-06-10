From iris.proofmode Require Import proofmode.
From cap_machine Require Import memory_region rules proofmode.
From cap_machine Require Export switcher switcher_preamble.
From cap_machine Require Import switcher_macros_spec.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.


Section Switcher_KtK_Call.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma switcher_cc_spec_0
    pc_b pc_e pc_a
    b_stk e_stk a_stk
    wctp wct2 :
    let switcher_instrs_0 := (switcher_instrs_n 0) in
    let len_switcher_0 := length switcher_instrs_0 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_0)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    codefrag pc_a switcher_instrs_0 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_0)%a ∗
        ctp ↦ᵣ WInt (encodePerm RWL) ∗
        ct2 ↦ᵣ WInt 0 ∗
        csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        codefrag pc_a switcher_instrs_0 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_0 len_switcher_0; subst switcher_instrs_0 len_switcher_0.
    iIntros (Hsub_reg) "(HPC & Hctp & Hct2 & Hcsp & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- GetP ct2 csp --- *)
    iInstr "Hcode".

    (* ---  Mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    replace ( match MP with
              | {| encodePerm := encodePerm |} => encodePerm
              end  ) with encodePerm by done.
    replace ( (if decide (ctp = cnull) then 0 else encodePerm RWL)%Z )
      with ( encodePerm RWL ) by (destruct (decide _); done).
    replace (encodePerm RWL - encodePerm RWL)%Z with 0%Z by lia.
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_cc_spec_1
    pc_b pc_e pc_a
    b_stk e_stk a_stk
    wctp wct2 :
    let switcher_instrs_1 := (switcher_instrs_n 1) in
    let len_switcher_1 := length switcher_instrs_1 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_1)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    codefrag pc_a switcher_instrs_1 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_1)%a ∗
        ct2 ↦ᵣ WInt 0 ∗
        ctp ↦ᵣ WInt (encodeLoc Local) ∗
        csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        codefrag pc_a switcher_instrs_1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_1 len_switcher_1; subst switcher_instrs_1 len_switcher_1.
    iIntros (Hsub_reg) "(HPC & Hctp & Hct2 & Hcsp & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- GetL ct2 csp --- *)
    iInstr "Hcode".

    (* --- Mov ctp (encodeLoc Local) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".
    cbn.

    (* --- Jnz 2 ct2 --- *)
    replace ( match MP with
                 | {| encodeLoc := encodeLoc |} => encodeLoc
                 end  ) with encodeLoc by done.
    replace ( (if decide (ctp = cnull) then 0 else encodeLoc Local )%Z )
      with ( encodeLoc Local ) by (destruct (decide _); done).
    replace (encodeLoc Local - encodeLoc Local)%Z with 0%Z by lia.
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_cc_spec_2
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

  (* TODO: add the failing case *)
  Lemma switcher_cc_spec_3
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
              codefrag pc_a switcher_instrs_3
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

    iInstr "Hcode".

    (* --- Lea ct2 1 --- *)
    assert ( ∃ f3, (a_tstk + 1)%a = Some f3) as [f3 Htastk] by (exists (a_tstk ^+ 1)%a; solve_addr+Hsize_tstk).
    iInstr "Hcode".

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

  Lemma switcher_cc_spec_4
    pc_b pc_e pc_a
    b_stk e_stk a_stk
    wcs0 wcs1 :
    let switcher_instrs_4 := (switcher_instrs_n 4) in
    let len_switcher_4 := length switcher_instrs_4 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_4)%a ->
    (isWithin a_stk e_stk b_stk e_stk = true) ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
    codefrag pc_a switcher_instrs_4 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_4)%a ∗
        cs0 ↦ᵣ WInt e_stk ∗
        cs1 ↦ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap RWL Local a_stk e_stk a_stk ∗
        codefrag pc_a switcher_instrs_4 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_4 len_switcher_4; subst switcher_instrs_4 len_switcher_4.
    iIntros (Hsub_reg Hastk) "(HPC & Hcs0 & Hcs1 & Hcsp & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* --- GetE cs0 csp --- *)
    iInstr "Hcode".

    (* --- GetA cs1 csp --- *)
    iInstr "Hcode".

    (* --- Subseg csp cs1 cs0 --- *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_cc_spec_6
    pc_b pc_e pc_a
    wcs0 wcs1 wpc_b :
    let switcher_instrs_6 := (switcher_instrs_n 6) in
    let len_switcher_6 := length switcher_instrs_6 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_6)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    pc_b ↦ₐ wpc_b ∗
    codefrag pc_a switcher_instrs_6 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_6)%a ∗
        cs0 ↦ᵣ wpc_b ∗
        cs1 ↦ᵣ WInt (pc_b - (pc_a ^+ 1)%a) ∗
        pc_b ↦ₐ wpc_b ∗
        codefrag pc_a switcher_instrs_6 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_6 len_switcher_6; subst switcher_instrs_6 len_switcher_6.
    iIntros (Hsub_reg) "(HPC & Hcs0 & Hcs1 & Hpc_b & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- GetB cs1 PC --- *)
    iInstr "Hcode".

    (* --- GetA cs0 PC --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cs1 cs0 --- *)
    iInstr "Hcode".

    (* --- Mov cs0 PC --- *)
    iInstr "Hcode".

    (* --- Lea cs0 cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]");auto;[solve_pure..| |].
    { instantiate (1:=(pc_b ^+ 2)%a); solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea cs0 -2 --- *)
    iInstr "Hcode".
    { instantiate (1:= pc_b); solve_addr. }

    (* --- Load cs0 cs0 --- *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_cc_spec_7
    pc_b pc_e pc_a
    wct2 o
    btbl_tgt etbl_tgt atbl_tgt
    Nexp_tbl nargs off_tgt :
    let switcher_instrs_7 := (switcher_instrs_n 7) in
    let len_switcher_7 := length switcher_instrs_7 in
    let wct1 := WSealed o (SCap RO Global btbl_tgt etbl_tgt atbl_tgt) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_7)%a ->
    (o < o ^+ 1)%ot ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    0 ≤ nargs ≤ 7 ->

    inv (export_table_entryN Nexp_tbl atbl_tgt)
      (atbl_tgt ↦ₐ WInt (encode_entry_point nargs off_tgt)) ∗
    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ WSealRange (true, true) Global o (o ^+ 1)%ot o ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    codefrag pc_a switcher_instrs_7 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_7)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        ct1 ↦ᵣ WCap RO Global btbl_tgt etbl_tgt atbl_tgt ∗
        ct2 ↦ᵣ WInt nargs ∗
        codefrag pc_a switcher_instrs_7 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_7 len_switcher_7 wct1; subst switcher_instrs_7 len_switcher_7 wct1.
    iIntros (Hsub_reg Hot_bounds atbl_tgt_inbounds Hnargs)
      "(#Hinv_exp_tbl_entry & HPC & Hcs0 & Hct1 & wtc2 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    iInstr "Hcode";[done|..].
    { rewrite /withinBounds; solve_addr. }


    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Hinv_exp_tbl_entry" as ">Ha_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    rewrite encode_entry_point_eq_off.
    rewrite encode_entry_point_eq_nargs; last lia.
    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_cc_spec_8
    pc_b pc_e pc_a
    wcs1 wcgp wcra
    btbl_tgt etbl_tgt atbl_tgt
    (bpcc_tgt epcc_tgt : Addr) wcgp_tgt
    Nexp_tbl nargs off_tgt :
    let switcher_instrs_8 := (switcher_instrs_n 8) in
    let len_switcher_8 := length switcher_instrs_8 in
    let wct1 := WCap RO Global btbl_tgt etbl_tgt atbl_tgt in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_8)%a ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    (btbl_tgt ^+ 1 < atbl_tgt)%a ->

    inv (export_table_PCCN Nexp_tbl) (btbl_tgt ↦ₐ WCap RX Global bpcc_tgt epcc_tgt bpcc_tgt) ∗
    inv (export_table_CGPN Nexp_tbl) ((btbl_tgt ^+ 1)%a ↦ₐ wcgp_tgt) ∗
    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ WInt off_tgt ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ WInt nargs ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    codefrag pc_a switcher_instrs_8 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_8)%a ∗
        cs0 ↦ᵣ WInt off_tgt ∗
        cs1 ↦ᵣ WInt (btbl_tgt - atbl_tgt) ∗
        ct1 ↦ᵣ WCap RO Global btbl_tgt etbl_tgt (btbl_tgt ^+ 1)%a ∗
        ct2 ↦ᵣ WInt (nargs + 1) ∗
        cgp ↦ᵣ wcgp_tgt ∗
        cra ↦ᵣ WCap RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a ∗
        codefrag pc_a switcher_instrs_8 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_8 len_switcher_8 wct1; subst switcher_instrs_8 len_switcher_8 wct1.
    iIntros (Hsub_reg atbl_tgt_inbounds Hbtbl_tgt1)
      "(#Hinv_exp_tbl_pcc & Hinv_exp_tbl_cgp & HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- GetB cgp ct1 --- *)
    iInstr "Hcode".

    (* --- GetA cs1 ct1 --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cgp cs1 --- *)
    iInstr "Hcode".

    (* --- Lea ct1 cs1 --- *)
    iInstr "Hcode".
    { instantiate (1:=btbl_tgt); solve_addr. }

    (* --- Load cra ct1 --- *)
    wp_instr.
    iInv "Hinv_exp_tbl_pcc" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds; solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_"; iModIntro.
    wp_pure.

    (* --- Lea ct1 1 --- *)
    iInstr "Hcode".
    { instantiate (1:=(btbl_tgt ^+ 1)%a); solve_addr. }

    (* --- Load cgp ct1 --- *)
    wp_instr.
    iInv "Hinv_exp_tbl_cgp" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds; solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_"; iModIntro.
    wp_pure.

    (* --- Lea cra cs0 --- *)
    destruct (bpcc_tgt + off_tgt)%a eqn:Hentry;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    replace f with (bpcc_tgt ^+ off_tgt)%a by solve_addr.
    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_cc_spec_16
    pc_b pc_e pc_a
    wcgp wcra wcs0 wcs1 b_stk e_stk a_stk :
    let switcher_instrs_16 := (switcher_instrs_n 16) in
    let len_switcher_16 := length switcher_instrs_16 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_16)%a ->

    (pc_a ^+ 10 + -36)%a = Some (pc_a ^+ -26)%a ->

    (b_stk <= a_stk)%a ->
    (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ - ∗
    cs1 ↦ᵣ - ∗
    cgp ↦ᵣ - ∗
    cra ↦ᵣ - ∗
    ca0 ↦ᵣ - ∗
    ca1 ↦ᵣ - ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag pc_a switcher_instrs_16 ∗
    ▷  (( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ -26)%a ∗
             cs0 ↦ᵣ wcs0 ∗
             cs1 ↦ᵣ wcs1 ∗
             cgp ↦ᵣ wcgp ∗
             cra ↦ᵣ wcra ∗
             ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
             ca1 ↦ᵣ WInt 0 ∗
             csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
             a_stk ↦ₐ wcs0 ∗
             (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
             (a_stk ^+ 2)%a ↦ₐ wcra ∗
             (a_stk ^+ 3)%a ↦ₐ wcgp ∗
             codefrag pc_a switcher_instrs_16 -∗
             WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
           )
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_16 len_switcher_16; subst switcher_instrs_16 len_switcher_16.
    iIntros (Hsub_reg Hpca_next Hbstk Hbstk')
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0] & [%wca1 Hca1]
      & Hcsp & Hastk0 & Hastk1 & Hastk2 & Hastk3 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 3)%a) ; solve_addr. }
    (* Load cgp csp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 2)%a) ; solve_addr. }
    (* Load cra csp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some (a_stk ^+ 1)%a) ; solve_addr. }
    (* Load cs1 csp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    (* Lea csp (inl (-1)%Z); *)
    iInstr "Hcode".
    { transitivity ( Some a_stk ) ; solve_addr. }
    (* Load cs0 csp; *)
    iInstr "Hcode".
    { split; solve_addr. }
    (* Mov ca0 (inl (-141)%Z); *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull))as [|_]; first done.
    (* Mov ca1 (inl 0%Z); *)
    iInstr "Hcode".
    (* Jmp (inl (-36)%Z) *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_cc_specification_known_to_known
    (Nswitcher : namespace)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK)
    (nargs : nat)
    (E : coPset)

    (Nexp_tbl : namespace)
    (btbl_tgt atbl_tgt etbl_tgt : Addr)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z)

    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher (SCap RO Global btbl_tgt etbl_tgt atbl_tgt) in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
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

    (* (* NA mask *) *)
    ↑Nswitcher ⊆ E ->

    (* Well formed entry point *)
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a →
    (btbl_tgt < (btbl_tgt ^+1))%a →
    ((btbl_tgt ^+1) < atbl_tgt)%a  →
    (0 <= nargs <= 7 )%nat →

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv

    (* Entry Point Invariant *)
    ∗ inv (export_table_PCCN Nexp_tbl)             ( btbl_tgt ↦ₐ WCap RX Global bpcc_tgt epcc_tgt bpcc_tgt)
    ∗ inv (export_table_CGPN Nexp_tbl)             ( (btbl_tgt ^+ 1)%a ↦ₐ WCap RW Global bcgp_tgt ecgp_tgt bcgp_tgt)
    ∗ inv (export_table_entryN Nexp_tbl atbl_tgt) ( atbl_tgt ↦ₐ WInt (encode_entry_point (Z.of_nat nargs) off_tgt))


    (* PRE-CONDITION *)
    ∗ na_own cerise_nais E
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* All the other registers *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg )
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ cstack_frag cstk


    ∗ ▷ ( (∃ arg_rmap' rmap',
              ⌜ is_arg_rmap arg_rmap' 8 ⌝
              ∗ ⌜ dom rmap' = dom rmap ∪ {[ ct1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais E
              (* Registers *)
              ∗ PC ↦ᵣ WCap RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a
              ∗ cgp ↦ᵣ WCap RW Global bcgp_tgt ecgp_tgt bcgp_tgt
              ∗ cra ↦ᵣ (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return)
              (* Stack register *)
              ∗ csp ↦ᵣ WCap RWL Local a_stk4 e_stk a_stk4
              (* All the other registers *)
              (* Entry point of the target compartment *)
              ∗ ( [∗ map] rarg↦warg ∈ arg_rmap', rarg ↦ᵣ warg
                                                 ∗ (if decide (rarg ∈ dom_arg_rmap nargs)
                                                    then ⌜ arg_rmap !! rarg = Some warg ⌝
                                                    else ⌜warg = WInt 0⌝)
                )
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )

              (* Stack frame *)
              ∗ ([[ a_stk4 , e_stk ]] ↦ₐ [[region_addrs_zeroes a_stk4 e_stk]])

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ cstack_frag (frame::cstk)
          )
          ∨
            (
              ∃ rmap' stk_mem',
                ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
                ∗ na_own cerise_nais E
                (* Registers *)
                ∗ PC ↦ᵣ updatePcPerm wcra_caller
                ∗ cgp ↦ᵣ wcgp_caller
                ∗ cra ↦ᵣ wcra_caller
                ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
                ∗ cs0 ↦ᵣ wcs0_caller
                ∗ cs1 ↦ᵣ wcs1_caller
                ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
                ∗ ca1 ↦ᵣ WInt 0
                (* All the other registers *)
                ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )

                (* Stack frame *)
                ∗ [[ a_stk , e_stk ]] ↦ₐ [[stk_mem']]

                (* Interpretation of the world and stack, at the moment of the switcher_call *)
                ∗ cstack_frag cstk
            )
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros astk4 wct1_caller callee_stk_region frame.
    iIntros (HE atbl_tgt_inbounds btbl_tgt0 btbl_tgt1 Hnargs Hdom Harg_rmap)
      "(#Hswitcher & Hinv_exp_tbl_pcc & Hinv_exp_tbl_cgp & Hinv_exp_tbl_entry
        & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hcstk & Hpost)".

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

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.

    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }

    (* -----------------------------------  *)
    (* ----- Lswitch_csp_check_perm ------  *)
    (* -----------------------------------  *)
    focus_block_0 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_cc_spec_0 with "[- $HPC $Hctp $Hct2 $Hcsp $Hcode]"); eauto; iFrame; iNext.
    iIntros "(HPC & Hctp & Hct2 & Hcsp & Hcode )".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ------ Lswitch_csp_check_loc ------  *)
    (* -----------------------------------  *)
    focus_block 1 "Hcode" as a_csp_check_loc Ha_csp_check_loc "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_cc_spec_1 with "[- $HPC $Hctp $Hct2 $Hcsp $Hcode]"); eauto; iFrame; iNext.
    iIntros "(HPC & Hctp & Hct2 & Hcsp & Hcode )".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ---- Lswitch_entry_first_spill ----  *)
    (* -----------------------------------  *)
    focus_block 2 "Hcode" as a_entry_first_spill Ha_entry_first_spill "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_csp_check_loc.
    iApply (switcher_cc_spec_2 with "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hcsp $Hstk $Hcode]"); eauto; iNext.
    iIntros (stk_mem')
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hstk & %Hastk & %Hstk_mem' & Hcode)".
    destruct Hastk as [Hastk_bstk [Hastk_bounds Hastk] ].
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* --------------------------------------  *)
    (* ----- Lswitch_trusted_stack_push -----  *)
    (* --------------------------------------  *)
    focus_block 3 "Hcode" as a_tstack_push Ha_tstack_push "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_entry_first_spill.
    iApply (switcher_cc_spec_3 with "[- $HPC $Hcs0 $Hctp $Hct2 $Hcsp $Hmtdc $Htstk $Hcode]"); eauto.
    { solve_addr+Ha_tstack_push Hcont_switcher_region. }
    iNext.
    iIntros "[
    (%tstk_next' & HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc & Ha_tstk1 & Htstk & %Ha_tstk1 & %Htstk_next' & Hcode)
    |
    (%Htskt & HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc & Htstk & Hcode)
    ]"
    ; [destruct Ha_tstk1 as [Ha_tstk1 Ha_tstk1_bound] | ]
    ; unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont
    ; cycle 1.
    { (* case not enough stack*)
      focus_block 16 "Hcode" as a_tstk_exhausted Ha_tstk_exhausted "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent a_tstack_push.
      iExtractList "Hargs" [ca0;ca1] as ["Hca0";"Hca1"].
      iApply (switcher_cc_spec_16 with "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hcsp $Hca0 $Hca1 $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hcode]"); eauto.
      { solve_addr+Ha_tstk_exhausted Hcont_switcher_region. }
      iNext; iIntros "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode)".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      focus_block 14 "Hcode" as a7 Ha7 "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent a_tstk_exhausted.
      iExtractList "Hargs" [ca2;ca3;ca4;ca5;ct0] as ["ca2";"ca3";"ca4";"ca5";"ct0"].
      iInsertList "Hregs" [ctp;ct2;ct1;ca2;ca3;ca4;ca5;ct0].
      iClear "Hargs".
      iApply (clear_registers_post_call_spec with "[- $HPC $Hregs $Hcode]"); try solve_pure.
      { clear -Hdom.
        repeat (rewrite -delete_insert_ne //).
        repeat (rewrite dom_insert_L).
        rewrite Hdom.
        set_solver.
      }
      iNext; iIntros "(%rmap' &%Hrmap' & HPC & Hregs & Hcode)".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      focus_block 15 "Hcode" as a_ret Ha_ret "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent a7.
      iExtract "Hregs" cnull as "[Hcnull _]".
      (* Jalr cnull cra *)
      iInstr "Hcode".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
      iHide "Hcode" as hcode.

      iDestruct (big_sepM_insert _ _ cnull (WInt 0) with "[Hcnull $Hregs]") as "Hregs".
      { by simplify_map_eq. }
      { iFrame; done. }
      map_simpl "Hregs".
      iAssert ([[ a_stk , e_stk ]] ↦ₐ [[wcs0_caller :: wcs1_caller :: wcra_caller :: wcgp_caller :: stk_mem']])%I
        with "[Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hstk]" as "Hstk".
      {
        subst astk4.
        iDestruct (region_pointsto_cons with "[$Ha_stk3 $Hstk]") as "Hstk"; [solve_addr+Hastk_bounds|solve_addr+Hastk_bounds|].
        iDestruct (region_pointsto_cons with "[$Ha_stk2 $Hstk]") as "Hstk"; [solve_addr+Hastk_bounds|solve_addr+Hastk_bounds|].
        iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; [solve_addr+Hastk_bounds|solve_addr+Hastk_bounds|].
        iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk"; [solve_addr+Hastk_bounds|solve_addr+Hastk_bounds|].
        iFrame.
      }

      iMod ("Hclose_switcher_inv"
             with "[Hstk_interp $Hna $Hmtdc $Hcode $Hb_switcher Htstk $Hcstk_full $Hp_ot_switcher]")
        as "Hna".
      {
        iFrame.
        iNext.
        iSplit; first (iPureIntro; done).
        iSplit; first (iPureIntro; done).
        iPureIntro; done.
      }

      iApply "Hpost".
      iRight.
      iFrame.
      iPureIntro.
      clear -Hrmap'.
      rewrite dom_insert_L Hrmap'.
      set_solver+.
    }
    (* case enough stack*)

    (* ------------------------------  *)
    (* ----- Lswitch_stack_chop -----  *)
    (* ------------------------------  *)
    focus_block 4 "Hcode" as a_stack_chop Ha_stack_chop "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_tstack_push.
    iApply (switcher_cc_spec_4 with "[- $HPC $Hcs0 $Hcs1 $Hcsp $Hcode]"); eauto; [|iNext].
    { rewrite /isWithin; solve_addr+Hastk_bounds. }
    iIntros "(HPC & Hcs0 & Hcs1 & Hcsp & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- Clear stack -----  *)
    (* -----------------------  *)
    focus_block 5 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_stack_chop.
    iApply (clear_stack_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hstk]"); try solve_pure.
    { solve_addr+. }
    { solve_addr. }
    iIntros "!> (HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- LoadCapPCC ------  *)
    (* -----------------------  *)
    focus_block 6 "Hcode" as a_LoadCapPCC Ha_LoadCapPCC "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear_stk1.
    iApply (switcher_cc_spec_6 with "[- $HPC $Hcs0 $Hcs1 $Hb_switcher $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hcs0 & Hcs1 & Hb_switcher & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ---- Lswitch_unseal_entry ----  *)
    (* ------------------------------  *)
    focus_block 7 "Hcode" as a_unseal_entry Ha_unseal_entry "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_LoadCapPCC.
    iApply (switcher_cc_spec_7 with "[- $Hinv_exp_tbl_entry $HPC $Hcs0 $Hct1 $Hct2 $Hcode]"); eauto. iNext.
    iIntros "(HPC & Hcs0 & Hct1 & Hct2 & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ---- Lswitch_callee_load -----  *)
    (* ------------------------------  *)
    focus_block 8 "Hcode" as a_callee_load Ha_callee_load "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_unseal_entry.
    iApply (switcher_cc_spec_8 with
             "[- $Hinv_exp_tbl_pcc $Hinv_exp_tbl_cgp $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hcgp $Hcra $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra  & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    (* clear registers except parameters *)

    (* ---------------------------------------- *)
    (* ---- clear_registers_pre_call_skip ----- *)
    (* ---------------------------------------- *)
    focus_block 9 "Hcode" as a_clear Ha_clear "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_callee_load.
    iApply (clear_registers_pre_call_skip_spec_known
              _ _ _ _ _ arg_rmap (nargs+1)
             with "[- $HPC $Hcode]")
    ; try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame.
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ----------------------------------- *)
    (* ---- clear_registers_pre_call ----- *)
    (* ----------------------------------- *)
    focus_block 10 "Hcode" as a_clear' Ha_clear' "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear.

    iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_eq.
    rewrite -delete_insert_ne; last done.
    iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_eq.
    iDestruct (big_sepM_insert_2 with "[Hcs1] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcs0] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs";[iFrame|].

    iApply (clear_registers_pre_call_spec with "[- $HPC $Hcode $Hregs]"); try solve_pure.
    { rewrite !dom_insert_L Hdom. set_solver-. }

    iIntros "!> (%rmap' & %Hrmap' & HPC & Hregs & Hcode)".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    (* ------------------------------ *)
    (* ---- Lswitch_callee_call ----- *)
    (* ------------------------------ *)

    focus_block 11 "Hcode" as a_callee_call Ha_callee_call "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear'.
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq'. subst.
    iMod (cstack_update _ _ (frame :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Ha_tstk1 Hstk_interp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3]") as "HH".
    { iNext. iExists (a_tstk ^+ 1)%a,(drop 1 tstk_next).
      iFrame "Hmtdc Hb_switcher Hp_ot_switcher".
      rewrite (finz_incr_eq Ha_tstk1); simpl.
      replace ((a_tstk ^+ 1)%a ^+ -1)%a with a_tstk by solve_addr+Ha_tstk1.
      iSplit;[auto|]. iFrame "Htstk Hstk_interp".
      iSplit;[iPureIntro;solve_addr+Hbounds_tstk_b Ha_tstk1 Ha_tstk1_bound|].
      iSplit;[iPureIntro;solve_addr+Ha_tstk1 Hlen_cstk|].
      iFrame; cbn.
      iPureIntro.
      repeat split; auto.
      solve_addr+Hastk_bounds.
    }
    pose proof switcher_return_entry_point as Ha_return.
    replace (a_callee_call ^+ 1)%a with a_switcher_return by solve_addr+Ha_return Ha_callee_call Hcall.
    iApply "Hpost"; iLeft; iFrame "∗ # %".
    iPureIntro.
    rewrite Hdom Hrmap'.
    set_solver+.
  Qed.

End Switcher_KtK_Call.
