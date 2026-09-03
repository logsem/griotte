From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode register_tactics.
From griotte Require Import switcher stack_object.

Section Stack_Object_Blocks.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout}.

  Lemma stack_object_alloc_block_spec
      pc_b pc_e pc_a csp_b csp_e
      (wca1 wcs0 wcs1 : Word) (stk_mem : list Word) :
    let instrs := so_f_alloc_instrs in
    let len := length instrs in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len)%a ->
    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ∗ ca1 ↦ᵣ wca1
    ∗ cs0 ↦ᵣ wcs0
    ∗ cs1 ↦ᵣ wcs1
    ∗ [[csp_b, csp_e]] ↦ₐ [[stk_mem]]
    ∗ codefrag pc_a instrs
    ∗ ▷ (∀ a_stk1 a_stk2 w0 w1 stk_mem',
        ⌜(csp_b + 1)%a = Some a_stk1⌝
        ∗ ⌜(a_stk1 + 1)%a = Some a_stk2⌝
        ∗ ⌜(csp_b < a_stk1)%a ∧ (a_stk1 < a_stk2)%a ∧
            (a_stk2 <= csp_e)%a⌝
        ∗ ⌜stk_mem = w0 :: w1 :: stk_mem'⌝
        ∗ PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ len)%a
        ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e a_stk2
        ∗ ca1 ↦ᵣ WCap RWL Local a_stk1 a_stk2 a_stk1
        ∗ cs0 ↦ᵣ WInt (a_stk1 : Z)
        ∗ cs1 ↦ᵣ WInt (a_stk2 : Z)
        ∗ csp_b ↦ₐ WInt so_secret
        ∗ a_stk1 ↦ₐ WInt 0
        ∗ [[a_stk2, csp_e]] ↦ₐ [[stk_mem']]
        ∗ codefrag pc_a instrs
        -∗ WP Seq (Instr Executable)
            {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros instrs len. subst instrs len.
    iIntros (Hsub) "(HPC & Hcsp & Hca1 & Hcs0 & Hcs1 & Hstk & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /so_f_alloc_instrs.

    destruct (decide ((csp_b < csp_e)%a)) as [Hcsp_size|Hcsp_size]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_z with "[$HPC $Hi $Hcsp]"); try solve_pure.
      { rewrite /withinBounds; solve_addr+Hcsp_size. }
      iIntros "!> _".
      wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.
    rewrite finz_dist_S in Hstklen; last solve_addr+Hcsp_size.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    assert (is_Some (csp_b + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hcsp_size|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Hastk0 Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1. }
    (* --- Store csp so_secret --- *)
    iInstr "Hcode".
    { rewrite /withinBounds; solve_addr+Hcsp_size. }
    (* --- Lea csp 1 --- *)
    iInstr "Hcode".
    (* --- Mov ca1 csp --- *)
    iInstr "Hcode".
    (* --- GetA cs0 ca1 --- *)
    iInstr "Hcode".
    (* --- Add cs1 cs0 1 --- *)
    iInstr "Hcode".

    destruct (decide ((a_stk1 < csp_e)%a)) as [Hcsp_size'|Hcsp_size']; cycle 1.
    {
      destruct (z_to_addr (a_stk1 + 1))%a as [a_stk2|] eqn:Hastk2; cycle 1.
      + iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_subseg_fail_src2_nonaddr with "[$HPC $Hi $Hca1 $Hcs0 $Hcs1]"); try solve_pure.
        iIntros "!> _".
        wp_pure; wp_end; iIntros (?); done.
      + iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_subseg_fail_not_iswithin_cap with "[$HPC $Hi $Hca1 $Hcs0 $Hcs1]"); try solve_pure.
        { eauto. }
        {
          assert (csp_e < a_stk2)%a as Hcsp_e_stk2
            by solve_addr+Hastk1 Hcsp_size Hcsp_size' Hastk2.
          rewrite /isWithin.
          apply andb_false_iff.
          right.
          solve_addr+Hcsp_e_stk2.
        }
        iIntros "!> _".
        wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen'.
    rewrite finz_seq_between_length in Hstklen'.
    rewrite finz_dist_S in Hstklen'; last solve_addr+Hcsp_size'.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2];[solve_addr+Hcsp_size'|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Hastk1 Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* --- Subseg ca1 cs0 cs1 --- *)
    iInstr "Hcode".
    { transitivity (Some a_stk2); auto. solve_addr+Hastk2. }
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* --- Store ca1 0 --- *)
    iInstr "Hcode".
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    replace (a_stk1 ^+ 1)%a with a_stk2 by solve_addr+Hastk2.
    replace ((a_stk1 : Z) + 1)%Z with (a_stk2 : Z) by solve_addr+Hastk2.

    iApply ("Hpost" $! a_stk1 a_stk2 w0 w1 stk_mem).
    iFrame.
    repeat iSplit; iPureIntro; try done; solve_addr.
  Qed.

  Lemma stack_object_call_block_spec
      pc_b pc_e pc_a (wra wcallback : Word) :
    let instrs := so_f_call_instrs in
    let len := length instrs in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len)%a ->
    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ cra ↦ᵣ wra
    ∗ ct0 ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ ct1 ↦ᵣ wcallback
    ∗ cs0 ↦ᵣ WInt 0
    ∗ cs1 ↦ᵣ WInt 0
    ∗ codefrag pc_a instrs
    ∗ ▷ (
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
        ∗ cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ len)%a
        ∗ ct0 ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
        ∗ ct1 ↦ᵣ wcallback
        ∗ cs0 ↦ᵣ wra
        ∗ cs1 ↦ᵣ wcallback
        ∗ codefrag pc_a instrs
        -∗ WP Seq (Instr Executable)
            {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros instrs len. subst instrs len.
    iIntros (Hsub) "(HPC & Hcra & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /so_f_call_instrs.
    (* --- Mov cs0 cra --- *)
    iInstr "Hcode".
    (* --- Mov cs1 ct1 --- *)
    iInstr "Hcode".
    (* --- Jalr cra ct0 --- *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma stack_object_assert_prep_block_spec
      pc_b pc_e pc_a csp_b csp_e a_stk2
      (wct0 wct1 : Word) :
    let instrs := so_f_assert_prep_instrs in
    let len := length instrs in
    (csp_b + 2)%a = Some a_stk2 ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len)%a ->
    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e a_stk2
    ∗ ct0 ↦ᵣ wct0
    ∗ ct1 ↦ᵣ wct1
    ∗ csp_b ↦ₐ WInt so_secret
    ∗ codefrag pc_a instrs
    ∗ ▷ (
        PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ len)%a
        ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
        ∗ ct0 ↦ᵣ WInt so_secret
        ∗ ct1 ↦ᵣ WInt so_secret
        ∗ csp_b ↦ₐ WInt so_secret
        ∗ codefrag pc_a instrs
        -∗ WP Seq (Instr Executable)
            {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros instrs len. subst instrs len.
    iIntros (Hastk2 Hsub) "(HPC & Hcsp & Hct0 & Hct1 & Hsecret & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /so_f_assert_prep_instrs.
    (* --- Lea csp (-2)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some csp_b); auto. solve_addr+Hastk2. }
    destruct (decide (csp_b < csp_e)%a) as [Hcsp_size|Hcsp_size]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Load.wp_load_fail_not_withinbounds with "[HPC Hi Hcsp Hct0]");
        try iFrame; try solve_pure.
      { rewrite /withinBounds. apply andb_false_iff. right. solve_addr+Hcsp_size. }
      iNext; iIntros "_".
      wp_pure; wp_end; by iIntros (?).
    }
    (* --- Load ct0 csp --- *)
    iInstr "Hcode".
    { split; auto. rewrite /withinBounds. solve_addr. }
    (* --- Mov ct1 so_secret --- *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma stack_object_return_block_spec
      pc_b pc_e pc_a (wret wcra wca0 wca1 : Word) :
    let instrs := so_f_return_instrs in
    let len := length instrs in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len)%a ->
    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
    ∗ cra ↦ᵣ wcra
    ∗ cs0 ↦ᵣ wret
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ cnull ↦ᵣ WInt 0
    ∗ codefrag pc_a instrs
    ∗ ▷ (
        PC ↦ᵣ updatePcPerm wret
        ∗ cra ↦ᵣ wret
        ∗ cs0 ↦ᵣ wret
        ∗ ca0 ↦ᵣ WInt 0
        ∗ ca1 ↦ᵣ WInt 0
        ∗ cnull ↦ᵣ WInt 0
        ∗ codefrag pc_a instrs
        -∗ WP Seq (Instr Executable)
            {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros instrs len. subst instrs len.
    iIntros (Hsub) "(HPC & Hcra & Hcs0 & Hca0 & Hca1 & Hcnull & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /so_f_return_instrs.
    (* --- Mov cra cs0 --- *)
    iInstr "Hcode".
    (* --- Mov ca0 0%Z --- *)
    iInstr "Hcode".
    (* --- Mov ca1 0%Z --- *)
    iInstr "Hcode".
    (* --- Jalr cnull cra --- *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

End Stack_Object_Blocks.
