From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import stack_callee_secret_spec_states_binary.

(** * Binary trusted callee, block 3: the body of [T.f]

    Block 3 loads the secret of each run in [ct0], writes it at the base
    [csp_b] of the stack frame of [T.f], sets the return values [ca0] and
    [ca1] to [0], and jumps to the return-to-switcher entry point in [cra].
    When the stack frame is empty, the store fails in the implementation
    run, and so does the machine. *)

Section Stack_callee_secret_F_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Lemma stack_callee_secret_f_blocks_1_spec
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (stk_mem stk_mem_spec : list Word)
    (wct0 swct0 wca0 swca0 wca1 swca1 wcnull swcnull : Word)
    (secret1 secret2 : Z) :
    let wcra := WSentry XSRW_ Local b_switcher e_switcher a_switcher_return in
    stack_callee_secret_code_bounds pc_b pc_e pc_a ->
    (cgp_b + 1)%a = Some cgp_e ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_callee_secret_block_offset 3)%a ∗
    PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_callee_secret_block_offset 3)%a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b ∗
    csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b ∗
    cra ↦ᵣ wcra ∗
    cra ↣ᵣ wcra ∗
    ct0 ↦ᵣ wct0 ∗
    ct0 ↣ᵣ swct0 ∗
    ca0 ↦ᵣ wca0 ∗
    ca0 ↣ᵣ swca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca1 ↣ᵣ swca1 ∗
    cnull ↦ᵣ wcnull ∗
    cnull ↣ᵣ swcnull ∗
    cgp_b ↦ₐ WInt secret1 ∗
    cgp_b ↣ₐ WInt secret2 ∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]] ∗
    [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]] ∗
    codefrag pc_a stack_callee_secret_code ∗
    spec_codefrag pc_a stack_callee_secret_code ∗
    ▷ (∀ stk_mem' stk_mem_spec' wcnull' swcnull',
        ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b ∗
        csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b ∗
        cra ↦ᵣ wcra ∗
        cra ↣ᵣ wcra ∗
        ct0 ↦ᵣ WInt secret1 ∗
        ct0 ↣ᵣ WInt secret2 ∗
        ca0 ↦ᵣ WInt 0 ∗
        ca0 ↣ᵣ WInt 0 ∗
        ca1 ↦ᵣ WInt 0 ∗
        ca1 ↣ᵣ WInt 0 ∗
        cnull ↦ᵣ wcnull' ∗
        cnull ↣ᵣ swcnull' ∗
        cgp_b ↦ₐ WInt secret1 ∗
        cgp_b ↣ₐ WInt secret2 ∗
        [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem' ]] ∗
        [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec' ]] ∗
        codefrag pc_a stack_callee_secret_code ∗
        spec_codefrag pc_a stack_callee_secret_code
        -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    intros wcra; subst wcra.
    iIntros ([HsubBounds Himports_contiguous] Hcgp_contiguous)
      "(#Hspec & Hj & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hcra & Hscra
      & Hct0 & Hsct0 & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcnull & Hscnull
      & Hsecret & Hssecret & Hstk & Hsstk & Hcode_main & Hscode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    stack_callee_secret_unfold_code.

    (* Block 3: the body of T.f *)
    focus_block_lockstep 3 "Hscode_main" "Hcode_main" of stack_callee_secret_blocks at pc_a
      as a_f Ha_f "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.

    (* Load ct0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [done| solve_addr].

    destruct (decide (csp_b < csp_e)%a) as [Hcsp_size|Hcsp_size]; cycle 1.
    { (* The stack frame is empty: the store fails in the implementation run *)
      (* Store csp ct0 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hct0 $Hcsp]"); try solve_pure.
      { rewrite /withinBounds; solve_addr+Hcsp_size. }
      iIntros "!> _".
      wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    iDestruct (big_sepL2_length with "Hsstk") as %Hsstklen.
    rewrite finz_seq_between_length finz_dist_S in Hstklen; last solve_addr+Hcsp_size.
    rewrite finz_seq_between_length finz_dist_S in Hsstklen; last solve_addr+Hcsp_size.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw0 stk_mem_spec]; simplify_eq.
    assert ((csp_b + 1)%a = Some (csp_b ^+ 1)%a) as Hcsp1 by solve_addr+Hcsp_size.
    iDestruct (region_pointsto_cons with "Hstk") as "[Hstk0 Hstk]";
      [exact Hcsp1|solve_addr+Hcsp_size|].
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsstk0 Hsstk]";
      [exact Hcsp1|solve_addr+Hcsp_size|].

    (* Store csp ct0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr+Hcsp_size.

    (* Mov ca0 0%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Mov ca1 0%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Jalr cnull cra *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main".
    iEval (cbn [updatePcPerm]) in "HPC".
    iEval (cbn [updatePcPerm]) in "HsPC".
    iDestruct (region_pointsto_cons with "[$Hstk0 $Hstk]") as "Hstk";
      [exact Hcsp1|solve_addr+Hcsp_size|].
    iDestruct (spec_region_pointsto_cons with "[$Hsstk0 $Hsstk]") as "Hsstk";
      [exact Hcsp1|solve_addr+Hcsp_size|].
    iApply "Hpost"; iFrame.
  Qed.

End Stack_callee_secret_F_Blocks_1.
