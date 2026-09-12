From iris.proofmode Require Import proofmode.
From griotte Require Import switcher_load_spec.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher switcher_preamble switcher_macros_spec.
From griotte Require Import map_simpl register_tactics.

Section Switcher_Return_Blocks.
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

  Lemma switcher_return_block_12_load_spec
    pc_b pc_e pc_a
    b_trusted_stack e_trusted_stack a_tstk
    wcsp wtstk :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    disjoint_from_shadow b_trusted_stack e_trusted_stack ->
    is_heap_cap wtstk = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->
    (b_trusted_stack <= a_tstk)%a ->

    PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 1)%a ∗
    ctp ↦ᵣ WCap true RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    csp ↦ᵣ wcsp ∗
    a_tstk ↦ₐ wtstk ∗
    codefrag pc_a switcher_instrs_12 ∗
    ▷ ( PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 2)%a ∗
        ctp ↦ᵣ WCap true RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
        csp ↦ᵣ wtstk ∗
        a_tstk ↦ₐ wtstk ∗
        ⌜ (a_tstk < e_trusted_stack)%a ⌝ ∗
        codefrag pc_a switcher_instrs_12 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Htstk_shadow Hwtstk_nonheap Hsub_reg Hbounds_tstk_b)
      "(HPC & Hctp & Hcsp & Ha_tstk & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Load csp ctp --- *)
    destruct (decide (a_tstk < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    {
      iInstr "Hcode".
      wp_end; by iIntros (?).
    }

    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact Htstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { split; auto. rewrite /withinBounds. solve_addr. }
    iApply "Hpost"; iFrame. iPureIntro; exact Htstk_ae.
  Qed.

  Lemma switcher_return_block_12_empty_spec
    pc_b pc_e pc_a
    b_trusted_stack e_trusted_stack :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->

    PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 2)%a ∗
    ctp ↦ᵣ WCap true RWL Local b_trusted_stack e_trusted_stack b_trusted_stack ∗
    csp ↦ᵣ WInt 0 ∗
    mtdc ↦ₛᵣ WCap true RWL Local b_trusted_stack e_trusted_stack b_trusted_stack ∗
    codefrag pc_a switcher_instrs_12
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hsub_reg) "(HPC & Hctp & Hcsp & Hmtdc & Hcode)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Lea ctp (-1)%Z --- *)
    destruct (decide (b_trusted_stack <= (b_trusted_stack ^+ -1))%a)
      as [Hb_trusted_stack1'|Hb_trusted_stack1'].
    {
      assert ((b_trusted_stack + -1) = None)%a by solve_addr+Hb_trusted_stack1'.
      iInstr "Hcode".

      (* --- WriteSR mtdc ctp --- *)
      iInstr "Hcode".

      (* --- Lea csp (-1)%Z --- *)
      iInstr "Hcode".
      wp_end; by iIntros (?).
    }
    assert (is_Some (b_trusted_stack + -1))%a
      as [b_trusted_stack1 Hb_trusted_stack1] by solve_addr+Hb_trusted_stack1'.
    clear Hb_trusted_stack1'.
    iInstr "Hcode".

    (* --- WriteSR mtdc ctp --- *)
    iInstr "Hcode".

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".
    wp_end; by iIntros (?).
  Qed.

  Lemma switcher_return_block_12_pop_spec
    pc_b pc_e pc_a
    b_trusted_stack e_trusted_stack a_tstk
    b_stk e_stk a_stk a_stk4 :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->
    (b_trusted_stack < a_tstk)%a ->
    (a_stk + 4)%a = Some a_stk4 ->

    PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 2)%a ∗
    ctp ↦ᵣ WCap true RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk4 ∗
    mtdc ↦ₛᵣ WCap true RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    codefrag pc_a switcher_instrs_12 ∗
    ▷ ( (∃ a_tstk1,
            ⌜ (a_tstk + -1)%a = Some a_tstk1 ⌝ ∗
            PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 5)%a ∗
            ctp ↦ᵣ WCap true RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
            csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
            mtdc ↦ₛᵣ WCap true RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
            codefrag pc_a switcher_instrs_12 ∗
            £ 1)
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hsub_reg Hnonempty Ha_stk4) "(HPC & Hctp & Hcsp & Hmtdc & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Lea ctp (-1)%Z --- *)
    assert (is_Some (a_tstk + -1))%a as [a_tstk1 Ha_tstk1]
      by solve_addr+Hnonempty.
    iInstr "Hcode".
    replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.

    (* --- WriteSR mtdc ctp --- *)
    iInstr "Hcode".

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode" with "Hlc".

    iApply "Hpost". iExists a_tstk1. iFrame.
    iPureIntro; exact Ha_tstk1.
  Qed.

  Lemma switcher_return_block_12_restore_spec
    pc_b pc_e pc_a
    b_stk e_stk a_stk a_stk4
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    disjoint_from_shadow b_stk e_stk ->
    is_heap_cap wcgp = false ->
    is_heap_cap wcra = false ->
    is_heap_cap wcs1 = false ->
    is_heap_cap wcs0 = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->
    (a_stk + 4)%a = Some a_stk4 ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->

    PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 5)%a ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag pc_a switcher_instrs_12 ∗
    ▷ ( PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 14)%a ∗
        cgp ↦ᵣ wcgp ∗
        cra ↦ᵣ wcra ∗
        cs1 ↦ᵣ wcs1 ∗
        cs0 ↦ᵣ wcs0 ∗
        ct0 ↦ᵣ WInt e_stk ∗
        ct1 ↦ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
        a_stk ↦ₐ wcs0 ∗
        (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
        (a_stk ^+ 2)%a ↦ₐ wcra ∗
        (a_stk ^+ 3)%a ↦ₐ wcgp ∗
        codefrag pc_a switcher_instrs_12 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hstk_shadow Hwcgp_nonheap Hwcra_nonheap Hwcs1_nonheap Hwcs0_nonheap Hsub_reg Ha_stk4 Hb_a4 He_a1)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Load cgp csp --- *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1]. }

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".

    (* --- Load cra csp --- *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1]. }

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".

    (* --- Load cs1 csp --- *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1]. }

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".

    (* --- Load cs0 csp --- *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1]. }

    (* --- GetE ct0 csp --- *)
    iInstr "Hcode" with "Hlc".

    (* --- GetA ct1 csp --- *)
    iInstr "Hcode" with "Hlc'".

    iCombine "Hlc Hlc'" as "Hlc".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma switcher_return_block_12_restore_general_spec
    pc_b pc_e pc_a
    b_stk e_stk a_stk a_stk4
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    disjoint_from_shadow b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->
    (a_stk + 4)%a = Some a_stk4 ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 5)%a ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag pc_a switcher_instrs_12 ∗
    ▷ ( ∀ rcgp rcra rcs1 rcs0,
        ⌜stack_load_result wcgp rcgp ∧ stack_load_result wcra rcra ∧
          stack_load_result wcs1 rcs1 ∧ stack_load_result wcs0 rcs0⌝ -∗
        PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 14)%a ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ct0 ↦ᵣ WInt e_stk ∗
        ct1 ↦ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
        a_stk ↦ₐ wcs0 ∗
        (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
        (a_stk ^+ 2)%a ↦ₐ wcra ∗
        (a_stk ^+ 3)%a ↦ₐ wcgp ∗
        codefrag pc_a switcher_instrs_12 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hstk_shadow Hsub_reg Ha_stk4 Hb_a4 He_a1)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Load cgp csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack _ _ _ _ _ _ (pc_a ^+ 6)%a cgp csp
      with "[$HPC $Hi $Hcgp $Hcsp $Ha_stk3]"); try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret) "[-> | (%rcgp & -> & %Hrcgp & HPC & Hi & Hcgp & Hcsp & Ha_stk3)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. }

    (* --- Load cra csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack _ _ _ _ _ _ (pc_a ^+ 8)%a cra csp
      with "[$HPC $Hi $Hcra $Hcsp $Ha_stk2]"); try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret) "[-> | (%rcra & -> & %Hrcra & HPC & Hi & Hcra & Hcsp & Ha_stk2)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. }

    (* --- Load cs1 csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack _ _ _ _ _ _ (pc_a ^+ 10)%a cs1 csp
      with "[$HPC $Hi $Hcs1 $Hcsp $Ha_stk1]"); try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret) "[-> | (%rcs1 & -> & %Hrcs1 & HPC & Hi & Hcs1 & Hcsp & Ha_stk1)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some a_stk); solve_addr. }

    (* --- Load cs0 csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (switcher_load_stack _ _ _ _ _ _ (pc_a ^+ 12)%a cs0 csp
      with "[$HPC $Hi $Hcs0 $Hcsp $Ha_stk]"); try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret) "[-> | (%rcs0 & -> & %Hrcs0 & HPC & Hi & Hcs0 & Hcsp & Ha_stk)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").

    (* --- GetE ct0 csp --- *)
    iInstr "Hcode" with "Hlc".

    (* --- GetA ct1 csp --- *)
    iInstr "Hcode" with "Hlc'".

    iCombine "Hlc Hlc'" as "Hlc".
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iFrame.
  Qed.

  Lemma switcher_return_block_15_spec
    pc_b pc_e pc_a
    wret
    (rmap : Reg) :
    let switcher_instrs_15 := switcher_instrs_n 15 in
    let len_switcher_15 := length switcher_instrs_15 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_15)%a ->
    is_Some (rmap !! cnull) ->

    PC ↦ᵣ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    cra ↦ᵣ wret ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝) ∗
    codefrag pc_a switcher_instrs_15 ∗
    ▷ ( PC ↦ᵣ updatePcPerm wret ∗
        cra ↦ᵣ wret ∗
        ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝) ∗
        codefrag pc_a switcher_instrs_15 ∗
        £ 1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_15 len_switcher_15.
    subst switcher_instrs_15 len_switcher_15.
    iIntros (Hsub_reg Hcnull_in) "(HPC & Hcra & Hrmap & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    iAssert (⌜map_Forall (λ (_ : RegName) (x : Word), x = WInt 0) rmap⌝)%I
      as "%Hrmap_zeroes".
    { iDestruct (big_sepM_sep with "Hrmap") as "[_ %]"; auto. }
    destruct Hcnull_in as [wcnull Hcnull_in].
    iExtract "Hrmap" cnull as "[Hcnull %]".

    (* --- Jalr cnull cra --- *)
    iInstr "Hcode" with "Hlc".

    iAssert (∃ wnull, cnull ↦ᵣ wnull ∗ ⌜wnull = WInt 0⌝)%I
      with "[Hcnull]" as (wnull) "Hcnull".
    { iFrame; done. }
    iInsert "Hrmap" cnull.
    iAssert (⌜<[cnull := wnull]> rmap = rmap⌝)%I as "%Hrmap_id".
    { iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hint]".
      iPureIntro.
      clear -Hcnull_in Hint Hrmap_zeroes.
      apply insert_id.
      pose proof (map_Forall_insert_1_1 _ _ _ _ Hint); cbn in *.
      rewrite H.
      rewrite Hcnull_in.
      by eapply map_Forall_lookup in Hcnull_in; eauto; cbn in *; simplify_map_eq.
    }
    rewrite Hrmap_id.
    clear dependent Hrmap_id Hrmap_zeroes wcnull wnull.
    iApply "Hpost"; iFrame.
  Qed.

End Switcher_Return_Blocks.
