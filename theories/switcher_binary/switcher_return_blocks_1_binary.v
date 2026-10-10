From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary.
From griotte Require Import switcher_return_states_binary.

(** * Return routine, first part of block 12: pop the trusted stack, binary model

    Block 12 starts by reading the topmost frame of the trusted stack, which
    contains the stack pointer of the caller, and pops it, in both runs.
    Both trusted stacks have the same depth. When the trusted stack is empty,
    the execution fails. *)

Section Switcher_Return_Blocks_1.
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

  Lemma switcher_return_block_12_load_spec
    pc_a a_tstk
    wcsp swcsp wtstk :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_12)%a ->
    (b_trusted_stack <= a_tstk)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
    ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    ctp ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    csp ↦ᵣ wcsp ∗
    csp ↣ᵣ swcsp ∗
    a_tstk ↦ₐ wtstk ∗
    a_tstk ↣ₐ wtstk ∗
    codefrag pc_a switcher_instrs_12 ∗
    spec_codefrag pc_a switcher_instrs_12 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 2)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 2)%a ∗
        ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
        ctp ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
        csp ↦ᵣ wtstk ∗
        csp ↣ᵣ wtstk ∗
        a_tstk ↦ₐ wtstk ∗
        a_tstk ↣ₐ wtstk ∗
        ⌜ (a_tstk < e_trusted_stack)%a ⌝ ∗
        codefrag pc_a switcher_instrs_12 ∗
        spec_codefrag pc_a switcher_instrs_12 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hsub_reg Hbounds_tstk_b)
      "(#Hspec & Hj & HPC & HsPC & Hctp & Hsctp & Hcsp & Hscsp & Ha_tstk & Hsa_tstk
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    destruct (decide (a_tstk < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    { (* Load csp ctp *)
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
    (* Load csp ctp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; auto; rewrite /withinBounds; solve_addr.
    iApply "Hpost"; iFrame. iPureIntro; exact Htstk_ae.
  Qed.

  Lemma switcher_return_block_12_pop_spec
    pc_a a_tstk
    b_stk e_stk a_stk a_stk4 :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_12)%a ->
    (a_stk + 4)%a = Some a_stk4 ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 2)%a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 2)%a ∗
    ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    ctp ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk4 ∗
    csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk4 ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    codefrag pc_a switcher_instrs_12 ∗
    spec_codefrag pc_a switcher_instrs_12 ∗
    ▷ ( (∃ a_tstk1,
            ⌜ (a_tstk + -1)%a = Some a_tstk1 ⌝ ∗
            ⤇ Seq (Instr Executable) ∗
            PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 5)%a ∗
            PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 5)%a ∗
            ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
            ctp ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
            csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
            csp ↣ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
            mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
            mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
            codefrag pc_a switcher_instrs_12 ∗
            spec_codefrag pc_a switcher_instrs_12 ∗
            £ 1)
        -∗ switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hsub_reg Ha_stk4) "(#Hspec & Hj & HPC & HsPC & Hctp & Hsctp & Hcsp & Hscsp
      & Hmtdc & Hsmtdc & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    destruct (decide (a_tstk <= (a_tstk ^+ -1))%a) as [Ha_tstk1'|Ha_tstk1'].
    { assert ((a_tstk + -1) = None)%a by solve_addr+Ha_tstk1'.
      (* Lea ctp (-1)%Z *)
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
    (* Lea ctp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.
    (* WriteSR mtdc ctp *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Lea csp (-1)%Z *)
    iInstr_spec "Hscode".
    { transitivity (Some (a_stk ^+ 3)%a); solve_addr+Ha_stk4. }
    (* Lea csp (-1)%Z *)
    iInstr "Hcode" with "Hlc".
    { transitivity (Some (a_stk ^+ 3)%a); solve_addr+Ha_stk4. }

    iApply "Hpost". iExists a_tstk1. iFrame.
    iPureIntro; exact Ha_tstk1.
  Qed.


  (** Pop the topmost frame of the trusted stack, which contains the stack
      pointer [WCap RWL Local b e (a ^+ 4)] of the caller. *)
  Lemma switcher_return_blocks_1_spec
    (a_tstk b e a : Addr) (wctp swctp wcsp swcsp : Word) :
    (b_trusted_stack <= a_tstk)%a ->
    (a + 4)%a = Some (a ^+ 4)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    csp ↦ᵣ wcsp ∗
    csp ↣ᵣ swcsp ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    a_tstk ↦ₐ WCap RWL Local b e (a ^+ 4)%a ∗
    a_tstk ↣ₐ WCap RWL Local b e (a ^+ 4)%a ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ∀ a_tstk1,
        ⌜ (a_tstk + -1)%a = Some a_tstk1 ⌝ ∗
        ⌜ (a_tstk < e_trusted_stack)%a ⌝ ∗
        ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ switcher_pc (switcher_block_offset 12 + 5) ∗
        PC ↣ᵣ switcher_pc (switcher_block_offset 12 + 5) ∗
        ctp ↦ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
        ctp ↣ᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
        csp ↦ᵣ WCap RWL Local b e (a ^+ 3)%a ∗
        csp ↣ᵣ WCap RWL Local b e (a ^+ 3)%a ∗
        mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
        mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk1 ∗
        a_tstk ↦ₐ WCap RWL Local b e (a ^+ 4)%a ∗
        a_tstk ↣ₐ WCap RWL Local b e (a ^+ 4)%a ∗
        switcher_code ∗
        switcher_spec_code ∗
        £ 1 -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros (Hb_tstk Ha4) "(#Hspec & Hj & HPC & HsPC & Hctp & Hsctp & Hcsp & Hscsp
      & Hmtdc & Hsmtdc & Ha_tstk & Hsa_tstk & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    rewrite switcher_return_block_12.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".
    switcher_focus_block_lockstep 12 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    (* ReadSR ctp mtdc *)
    iInstr_lockstep "Hscode" "Hcode".
    iApply (switcher_return_block_12_load_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hcsp $Hscsp $Ha_tstk $Hsa_tstk $Hcode $Hscode]");
      [done|done|].
    iNext; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hcsp & Hscsp & Ha_tstk & Hsa_tstk
      & %Htstk_ae & Hcode & Hscode)".
    iApply (switcher_return_block_12_pop_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hcsp $Hscsp $Hmtdc $Hsmtdc $Hcode $Hscode]");
      [done|done|].
    iNext; iIntros "(%a_tstk1 & %Ha_tstk1 & Hj & HPC & HsPC & Hctp & Hsctp & Hcsp & Hscsp
      & Hmtdc & Hsmtdc & Hcode & Hscode & Hlc)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
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
    ⊢ switcher_wp.
  Proof.
    iIntros "(HPC & Hctp & Hcsp & Hmtdc & Ha_tstk & Hcode)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    rewrite switcher_return_block_12.
    switcher_unfold_code "Hcode".
    focus_block_nochangePC 12 "Hcode" as a_block Ha_block "Hcode" "Hcls".
    assert (a_block = (a_switcher_call ^+ switcher_block_offset 12)%a) as ->
      by (cbn in Ha_block; offsets_compute; solve_addr).
    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
    destruct (decide (b_trusted_stack < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    { (* Load csp ctp *)
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
    (* Load csp ctp *)
    iInstr "Hcode".
    { split; auto. rewrite /withinBounds. solve_addr. }
    destruct (decide (b_trusted_stack <= (b_trusted_stack ^+ -1))%a)
      as [Hb_trusted_stack1'|Hb_trusted_stack1'].
    { assert ((b_trusted_stack + -1) = None)%a by solve_addr+Hb_trusted_stack1'.
      (* Lea ctp (-1)%Z *)
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
    (* Lea ctp (-1)%Z *)
    iInstr "Hcode".
    (* WriteSR mtdc ctp *)
    iInstr "Hcode".
    (* Lea csp (-1)%Z *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (rules_Lea.wp_Lea_fail_integer with "[HPC Hi Hcsp]")
    ; try iFrame
    ; try solve_pure.
    iNext; iIntros "_".
    wp_pure; wp_end; by iIntros (?).
  Qed.

End Switcher_Return_Blocks_1.
