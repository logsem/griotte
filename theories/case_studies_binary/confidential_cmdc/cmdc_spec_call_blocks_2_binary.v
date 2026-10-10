From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import cmdc_spec_states_binary.

(** * Binary CMDC, blocks 1-3 and 5-7: calls to the switcher

    For the call [c], in both runs, the first block fetches the entry point
    of the switcher in [ctp], the second block fetches the entry point of
    the callee in [ct1], and the first instruction of the third block jumps
    to the switcher. The group ends at the entry point of the switcher, with
    the return address of the call in [cra]. *)

Section CMDC_Call_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  (** The proof of [cmdc_call_blocks_2_spec], for the call starting at
      block [n]: the code of the two calls only differs by the import of the
      callee. *)
  Local Ltac cmdc_call_blocks_proof n pc_a pc_b :=
    let hcont := fresh "hcont" in
    let hscont := fresh "hscont" in
    let a_fetch1 := fresh "a_fetch1" in
    let a_fetch2 := fresh "a_fetch2" in
    let a_call := fresh "a_call" in
    let Ha_fetch1 := fresh "Ha_fetch1" in
    let Ha_fetch2 := fresh "Ha_fetch2" in
    let Ha_call := fresh "Ha_call" in
    (* Block n: fetch the entry point of the switcher *)
    focus_block_lockstep n "Hscode_main" "Hcode_main" of cmdc_conf_main_blocks at pc_a
      as a_fetch1 Ha_fetch1 "Hscode" "Hscont" "Hcode" "Hcont";
    iHide "Hcont" as hcont; iHide "Hscont" as hscont;
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcode $Hscode]");
    eauto; [solve_addr|];
    replace (pc_b ^+ 0)%a with pc_b by solve_addr;
    iFrame "Himport_switcher Hsimport_switcher";
    iNext; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                    & Hcode & Hscode & Himport_switcher & Hsimport_switcher)";
    iEval (cbn) in "Hctp"; iEval (cbn) in "Hsctp";
    subst hcont hscont;
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main";

    (* Block n+1: fetch the entry point of the callee *)
    focus_block_lockstep (S n) "Hscode_main" "Hcode_main" of cmdc_conf_main_blocks at pc_a
      as a_fetch2 Ha_fetch2 "Hscode" "Hscont" "Hcode" "Hcont";
    iHide "Hcont" as hcont; iHide "Hscont" as hscont;
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hct1 $Hsct1 $Hct0 $Hsct0 $Hcs0 $Hscs0 $Hcode $Hscode
                 $Himport_target $Hsimport_target]");
    eauto; [solve_addr|];
    iNext; iIntros "(Hj & HPC & HsPC & Hct1 & Hsct1 & Hct0 & Hsct0 & Hcs0 & Hscs0
                    & Hcode & Hscode & Himport_target & Hsimport_target)";
    iEval (cbn) in "Hct1"; iEval (cbn) in "Hsct1";
    subst hcont hscont;
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main";

    (* Block n+2: jump to the switcher *)
    focus_block_lockstep (S (S n)) "Hscode_main" "Hcode_main" of cmdc_conf_main_blocks at pc_a
      as a_call Ha_call "Hscode" "Hscont" "Hcode" "Hcont";
    iHide "Hcont" as hcont; iHide "Hscont" as hscont;
    (* Jalr cra ctp *)
    iInstr_lockstep "Hscode" "Hcode";
    subst hcont hscont;
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main";
    assert ((a_call ^+ 1)%a = (pc_a ^+ cmdc_instr_offset (n + 2) 1)%a) as ->
      by (offsets_compute; solve_addr);
    iApply "Hpost"; iFrame.

  Lemma cmdc_call_blocks_2_spec (c : cmdc_call)
    (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable)
    (wctp swctp wct0 swct0 wct1 swct1 wcs0 swcs0 wcra swcra : Word)
    (φ : language.val griotte_lang -> iProp Σ) :
    let n := cmdc_call_block c in
    let target := WSealed ot_switcher (cmdc_call_target c B_f C_g) in
    cmdc_code_bounds pc_b pc_e pc_a ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset n)%a ∗
    PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset n)%a ∗
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
    pc_b ↦ₐ cmdc_switcher_entry ∗
    pc_b ↣ₐ cmdc_switcher_entry ∗
    (pc_b ^+ cmdc_call_import c)%a ↦ₐ target ∗
    (pc_b ^+ cmdc_call_import c)%a ↣ₐ target ∗
    codefrag pc_a cmdc_conf_main_code ∗
    spec_codefrag pc_a cmdc_conf_main_code ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        ctp ↦ᵣ cmdc_switcher_entry ∗
        ctp ↣ᵣ cmdc_switcher_entry ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct0 ↣ᵣ WInt 0 ∗
        ct1 ↦ᵣ target ∗
        ct1 ↣ᵣ target ∗
        cs0 ↦ᵣ WInt 0 ∗
        cs0 ↣ᵣ WInt 0 ∗
        cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ cmdc_instr_offset (n + 2) 1)%a ∗
        cra ↣ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ cmdc_instr_offset (n + 2) 1)%a ∗
        pc_b ↦ₐ cmdc_switcher_entry ∗
        pc_b ↣ₐ cmdc_switcher_entry ∗
        (pc_b ^+ cmdc_call_import c)%a ↦ₐ target ∗
        (pc_b ^+ cmdc_call_import c)%a ↣ₐ target ∗
        codefrag pc_a cmdc_conf_main_code ∗
        spec_codefrag pc_a cmdc_conf_main_code
        -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros n target.
    destruct c; subst n target; cbn [cmdc_call_block cmdc_call_import cmdc_call_target].
    all: iIntros ([HsubBounds Himports_contiguous])
      "(#Hspec & Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
      & Hcs0 & Hscs0 & Hcra & Hscra
      & Himport_switcher & Hsimport_switcher & Himport_target & Hsimport_target
      & Hcode_main & Hscode_main & Hpost)".
    all: codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    all: unfold_code cmdc_conf_main_code "Hcode_main".
    all: unfold_code cmdc_conf_main_code "Hscode_main".
    all: rewrite /cmdc_switcher_entry.
    - (* Call to [B.f], blocks 1-3 *)
      cmdc_call_blocks_proof 1 pc_a pc_b.
    - (* Call to [C.g], blocks 5-7 *)
      cmdc_call_blocks_proof 5 pc_a pc_b.
  Qed.

End CMDC_Call_Blocks_2.
