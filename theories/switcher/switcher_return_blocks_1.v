From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_return_states.

(** * Return routine, first part of block 12: pop the trusted stack

    Block 12 starts by reading the topmost frame of the trusted stack, which
    contains the stack pointer of the caller, and pops it. When the trusted
    stack is empty, the execution fails. *)

Section Switcher_Return_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_return_block_12_load_spec
    pc_b pc_e pc_a
    b_trusted_stack e_trusted_stack a_tstk
    wcsp wtstk :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->
    (b_trusted_stack <= a_tstk)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 1)%a ∗
    ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    csp ↦ᵣ wcsp ∗
    a_tstk ↦ₐ wtstk ∗
    codefrag pc_a switcher_instrs_12 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 2)%a ∗
        ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
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
    iIntros (Hsub_reg Hbounds_tstk_b)
      "(HPC & Hctp & Hcsp & Ha_tstk & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Load csp ctp --- *)
    destruct (decide (a_tstk < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Load.wp_load_fail_not_withinbounds with "[HPC Hi Hctp Hcsp]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds.
        apply andb_false_iff; right.
        solve_addr+Htstk_ae.
      }
      iNext; iIntros "_".
      wp_pure; wp_end; by iIntros (?).
    }

    iInstr "Hcode".
    { split; auto. rewrite /withinBounds. solve_addr. }
    iApply "Hpost"; iFrame. iPureIntro; exact Htstk_ae.
  Qed.

  Lemma switcher_return_block_12_empty_spec
    pc_b pc_e pc_a
    b_trusted_stack e_trusted_stack :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 2)%a ∗
    ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack b_trusted_stack ∗
    csp ↦ᵣ WInt 0 ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack b_trusted_stack ∗
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
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Lea.wp_Lea_fail_none_z with "[HPC Hi Hctp]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_".
      wp_pure; wp_end; by iIntros (?).
    }
    assert (is_Some (b_trusted_stack + -1))%a
      as [b_trusted_stack1 Hb_trusted_stack1] by solve_addr+Hb_trusted_stack1'.
    clear Hb_trusted_stack1'.
    iInstr "Hcode".

    (* --- WriteSR mtdc ctp --- *)
    iInstr "Hcode".

    (* --- Lea csp (-1)%Z --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (rules_Lea.wp_Lea_fail_integer with "[HPC Hi Hcsp]")
    ; try iFrame
    ; try solve_pure.
    iNext; iIntros "_".
    wp_pure; wp_end; by iIntros (?).
  Qed.

  Lemma switcher_return_block_12_pop_spec
    pc_b pc_e pc_a
    b_trusted_stack e_trusted_stack a_tstk
    b_stk e_stk a_stk a_stk4 :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->
    (a_stk + 4)%a = Some a_stk4 ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 2)%a ∗
    ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk4 ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    codefrag pc_a switcher_instrs_12 ∗
    ▷ ( (∃ a_tstk1,
            ⌜ (a_tstk + -1)%a = Some a_tstk1 ⌝ ∗
            PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 5)%a ∗
            ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
            csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
            mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
            codefrag pc_a switcher_instrs_12 ∗
            £ 1)
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hsub_reg Ha_stk4) "(HPC & Hctp & Hcsp & Hmtdc & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Lea ctp (-1)%Z --- *)
    destruct (decide (a_tstk <= (a_tstk ^+ -1))%a) as [Ha_tstk1'|Ha_tstk1'].
    {
      assert ((a_tstk + -1) = None)%a by solve_addr+Ha_tstk1'.
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Lea.wp_Lea_fail_none_z with "[HPC Hi Hctp]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_".
      wp_pure; wp_end; by iIntros (?).
    }
    assert (is_Some (a_tstk + -1))%a as [a_tstk1 Ha_tstk1]
      by solve_addr+Ha_tstk1'.
    iInstr "Hcode".
    replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.

    (* --- WriteSR mtdc ctp --- *)
    iInstr "Hcode".

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode" with "Hlc".
    { transitivity (Some (a_stk ^+ 3)%a); solve_addr+Ha_stk4. }

    iApply "Hpost". iExists a_tstk1. iFrame.
    iPureIntro; exact Ha_tstk1.
  Qed.


  (** Pop the topmost frame of the trusted stack, which contains the stack
      pointer [WCap RWL Local b e (a ^+ 4)] of the caller. *)
  Lemma switcher_return_blocks_1_spec
    (a_tstk b e a : Addr) (wctp wcsp : Word) :
    (b_trusted_stack <= a_tstk)%a ->
    (a + 4)%a = Some (a ^+ 4)%a ->

    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ wcsp ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    a_tstk ↦ₐ WCap RWL Local b e (a ^+ 4)%a ∗
    switcher_code ∗
    ▷ ( ∀ a_tstk1,
        ⌜ (a_tstk + -1)%a = Some a_tstk1 ⌝ ∗
        ⌜ (a_tstk < e_trusted_stack)%a ⌝ ∗
        PC ↦ᵣ switcher_pc (switcher_block_offset 12 + 5) ∗
        ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
        csp ↦ᵣ WCap RWL Local b e (a ^+ 3)%a ∗
        mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
        a_tstk ↦ₐ WCap RWL Local b e (a ^+ 4)%a ∗
        switcher_code ∗
        £ 1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hb_tstk Ha4) "(HPC & Hctp & Hcsp & Hmtdc & Ha_tstk & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    rewrite switcher_return_block_12.
    switcher_unfold_code "Hcode".
    switcher_focus_block 12 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
    iApply (switcher_return_block_12_load_spec with
      "[- $HPC $Hctp $Hcsp $Ha_tstk $Hcode]"); [done|done|].
    iNext; iIntros "(HPC & Hctp & Hcsp & Ha_tstk & %Htstk_ae & Hcode)".
    iApply (switcher_return_block_12_pop_spec with
      "[- $HPC $Hctp $Hcsp $Hmtdc $Hcode]"); [done|done|].
    iNext; iIntros "(%a_tstk1 & %Ha_tstk1 & HPC & Hctp & Hcsp & Hmtdc & Hcode & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    switcher_change_pc (switcher_block_offset 12 + 5)%Z.
    iApply "Hpost"; iFrame; done.
  Qed.

  (** When the trusted stack is empty, the execution fails. *)
  Lemma switcher_return_blocks_1_empty_spec (wctp wcsp : Word) :
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ wcsp ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack b_trusted_stack ∗
    b_trusted_stack ↦ₐ WInt 0 ∗
    switcher_code
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hctp & Hcsp & Hmtdc & Ha_tstk & Hcode)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    rewrite switcher_return_block_12.
    switcher_unfold_code "Hcode".
    switcher_focus_block 12 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
    iApply (switcher_return_block_12_load_spec with
      "[- $HPC $Hctp $Hcsp $Ha_tstk $Hcode]"); [done|solve_addr|].
    iNext; iIntros "(HPC & Hctp & Hcsp & Ha_tstk & %Htstk_ae & Hcode)".
    iApply (switcher_return_block_12_empty_spec with
      "[- $HPC $Hctp $Hcsp $Hmtdc $Hcode]"); done.
  Qed.

End Switcher_Return_Blocks_1.
