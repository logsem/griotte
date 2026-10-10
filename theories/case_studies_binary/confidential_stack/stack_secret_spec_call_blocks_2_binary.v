From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import stack_secret_spec_states_binary.

(** * Binary stack confidentiality, blocks 1-3: call to the switcher

    In both runs, block 1 fetches the entry point of the switcher in [ctp],
    block 2 fetches the entry point of [B.f] in [ct1], and the first
    instruction of block 3 jumps to the switcher. The group ends at the
    entry point of the switcher, with the return address of the call in
    [cra]. *)

Section Stack_secret_Call_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Lemma stack_secret_call_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (B_f : Sealable)
    (wctp swctp wct0 swct0 wct1 swct1 wcs0 swcs0 wcra swcra : Word)
    (φ : language.val griotte_lang -> iProp Σ) :
    let target := WSealed ot_switcher B_f in
    stack_secret_code_bounds pc_b pc_e pc_a ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_secret_block_offset 1)%a ∗
    PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_secret_block_offset 1)%a ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct0 ↣ᵣ swct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct1 ↣ᵣ swct1 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs0 ↣ᵣ swcs0 ∗
    cra ↦ᵣ wcra ∗
    cra ↣ᵣ swcra ∗
    pc_b ↦ₐ stack_secret_switcher_entry ∗
    pc_b ↣ₐ stack_secret_switcher_entry ∗
    (pc_b ^+ 1)%a ↦ₐ target ∗
    (pc_b ^+ 1)%a ↣ₐ target ∗
    codefrag pc_a stack_secret_main_code ∗
    spec_codefrag pc_a stack_secret_main_code ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        ctp ↦ᵣ stack_secret_switcher_entry ∗
        ctp ↣ᵣ stack_secret_switcher_entry ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct0 ↣ᵣ WInt 0 ∗
        ct1 ↦ᵣ target ∗
        ct1 ↣ᵣ target ∗
        cs0 ↦ᵣ WInt 0 ∗
        cs0 ↣ᵣ WInt 0 ∗
        cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ stack_secret_instr_offset 3 1)%a ∗
        cra ↣ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ stack_secret_instr_offset 3 1)%a ∗
        pc_b ↦ₐ stack_secret_switcher_entry ∗
        pc_b ↣ₐ stack_secret_switcher_entry ∗
        (pc_b ^+ 1)%a ↦ₐ target ∗
        (pc_b ^+ 1)%a ↣ₐ target ∗
        codefrag pc_a stack_secret_main_code ∗
        spec_codefrag pc_a stack_secret_main_code
        -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros target; subst target.
    iIntros ([HsubBounds Himports_contiguous])
      "(#Hspec & Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
      & Hcs0 & Hscs0 & Hcra & Hscra
      & Himport_switcher & Hsimport_switcher & Himport_B_f & Hsimport_B_f
      & Hcode_main & Hscode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code stack_secret_main_code "Hcode_main".
    unfold_code stack_secret_main_code "Hscode_main".
    rewrite /stack_secret_switcher_entry.

    (* Block 1: fetch the entry point of the switcher *)
    focus_block_lockstep 1 "Hscode_main" "Hcode_main" of stack_secret_main_blocks at pc_a
      as a_fetch1 Ha_fetch1 "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcode $Hscode]");
      eauto; [solve_addr|].
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher Hsimport_switcher".
    iNext; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                    & Hcode & Hscode & Himport_switcher & Hsimport_switcher)".
    iEval (cbn) in "Hctp". iEval (cbn) in "Hsctp".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main".

    (* Block 2: fetch the entry point of B.f *)
    focus_block_lockstep 2 "Hscode_main" "Hcode_main" of stack_secret_main_blocks at pc_a
      as a_fetch2 Ha_fetch2 "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hct1 $Hsct1 $Hct0 $Hsct0 $Hcs0 $Hscs0 $Hcode $Hscode
                 $Himport_B_f $Hsimport_B_f]");
      eauto; [solve_addr|].
    iNext; iIntros "(Hj & HPC & HsPC & Hct1 & Hsct1 & Hct0 & Hsct0 & Hcs0 & Hscs0
                    & Hcode & Hscode & Himport_B_f & Hsimport_B_f)".
    iEval (cbn) in "Hct1". iEval (cbn) in "Hsct1".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main".

    (* Block 3: jump to the switcher *)
    focus_block_lockstep 3 "Hscode_main" "Hcode_main" of stack_secret_main_blocks at pc_a
      as a_call Ha_call "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    (* Jalr cra ctp *)
    iInstr_lockstep "Hscode" "Hcode".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main".
    assert ((a_call ^+ 1)%a = (pc_a ^+ stack_secret_instr_offset 3 1)%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame.
  Qed.

End Stack_secret_Call_Blocks_2.
