From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import stack_secret_spec_states_binary.

(** * Binary stack confidentiality, block 0: the secret on the stack

    Block 0 loads the secret of each run in [ct0], stores it at [csp_b],
    the first word of the stack frame of [main], and at [csp_b + 5], above
    the four words that the switcher spills. The group ends with the stack
    pointer at [csp_b + 1]. *)

Section Stack_secret_Init_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
  .

  Lemma stack_secret_init_blocks_1_spec
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (wct0 swct0 w_stk0 sw_stk0 w_stk5 sw_stk5 : Word)
    (secret1 secret2 : Z)
    (φ : language.val griotte_lang -> iProp Σ) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_secret_main_code)%a ->
    (cgp_b + length (stack_secret_main_data 0))%a = Some cgp_e ->
    (csp_b ^+ 5 < csp_e)%a ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
    PC ↣ᵣ WCap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b ∗
    csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b ∗
    ct0 ↦ᵣ wct0 ∗
    ct0 ↣ᵣ swct0 ∗
    cgp_b ↦ₐ WInt secret1 ∗
    cgp_b ↣ₐ WInt secret2 ∗
    csp_b ↦ₐ w_stk0 ∗
    csp_b ↣ₐ sw_stk0 ∗
    (csp_b ^+ 5)%a ↦ₐ w_stk5 ∗
    (csp_b ^+ 5)%a ↣ₐ sw_stk5 ∗
    codefrag pc_a stack_secret_main_code ∗
    spec_codefrag pc_a stack_secret_main_code ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_secret_block_offset 1)%a ∗
        PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_secret_block_offset 1)%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        csp ↦ᵣ WCap RWL Local csp_b csp_e (csp_b ^+ 1)%a ∗
        csp ↣ᵣ WCap RWL Local csp_b csp_e (csp_b ^+ 1)%a ∗
        ct0 ↦ᵣ WInt secret1 ∗
        ct0 ↣ᵣ WInt secret2 ∗
        cgp_b ↦ₐ WInt secret1 ∗
        cgp_b ↣ₐ WInt secret2 ∗
        csp_b ↦ₐ WInt secret1 ∗
        csp_b ↣ₐ WInt secret2 ∗
        (csp_b ^+ 5)%a ↦ₐ WInt secret1 ∗
        (csp_b ^+ 5)%a ↣ₐ WInt secret2 ∗
        codefrag pc_a stack_secret_main_code ∗
        spec_codefrag pc_a stack_secret_main_code
        -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (HsubBounds Hcgp_contiguous Hcsp_size)
      "(#Hspec & Hj & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hct0 & Hsct0
      & Hsecret & Hssecret & Hstk0 & Hsstk0 & Hstk5 & Hsstk5
      & Hcode_main & Hscode_main & Hpost)".
    cbn in Hcgp_contiguous.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    assert ((csp_b + 1)%a = Some (csp_b ^+ 1)%a) as Hcsp1 by solve_addr.
    assert (((csp_b ^+ 1) + 4)%a = Some (csp_b ^+ 5)%a) as Hcsp5 by solve_addr.
    assert (((csp_b ^+ 5) + -4)%a = Some (csp_b ^+ 1)%a) as Hcsp5' by solve_addr.
    unfold_code stack_secret_main_code "Hcode_main".
    unfold_code stack_secret_main_code "Hscode_main".

    (* Block 0: the secret on the stack *)
    focus_block_0_lockstep "Hscode_main" "Hcode_main" as "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.

    (* Load ct0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [done| solve_addr].

    (* Store csp ct0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* Lea csp 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Lea csp 4%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Store csp ct0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* Lea csp (-4)%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main".
    change_pc_to (pc_a ^+ stack_secret_block_offset 1)%a.
    iApply "Hpost"; iFrame.
  Qed.

End Stack_secret_Init_Blocks_1.
