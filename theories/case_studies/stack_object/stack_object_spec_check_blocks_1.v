From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import stack_object_spec_states.

(** * Stack object, blocks 3-5: checks of the stack object [in]

    Block 3 saves the callback [g] (in [ca1]) in [ct1]. Block 4 checks
    that the stack object [in] (in [ca0]) is a readable capability, and
    block 5 that it does not overlap with the stack frame. The group ends
    at the beginning of block 6 ([checkints]). *)

Section SO_Check_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_check_blocks_1_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (csp_b csp_e : Addr)
    (wca0 wca1 wct1 wcs0 wcs1 : Word) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ so_block_offset 3)%a ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ct1 ↦ᵣ wct1 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b ∗
    codefrag pc_a so_main_code ∗
    ▷ (∀ p g b e a,
        ⌜readAllowed p = true⌝ ∗
        ⌜wca0 = WCap p g b e a⌝ ∗
        ⌜finz.seq_between b e ## finz.seq_between csp_b csp_e⌝ ∗
        PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ so_block_offset 6)%a ∗
        ca0 ↦ᵣ WCap p g b e a ∗
        ca1 ↦ᵣ wca1 ∗
        ct1 ↦ᵣ wca1 ∗
        cs0 ↦ᵣ WInt 0 ∗
        cs1 ↦ᵣ WInt 0 ∗
        csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b ∗
        codefrag pc_a so_main_code ∗
        £ 1
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous])
      "(HPC & Hca0 & Hca1 & Hct1 & Hcs0 & Hcs1 & Hcsp & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 3: save the callback *)
    focus_block 3 "Hcode_main" of so_main_blocks at pc_a as a_mov Ha_mov "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ct1 ca1 *)
    iInstr "Hcode" with "Hlc".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: check that [in] is readable *)
    focus_block 4 "Hcode_main" of so_main_blocks at pc_a as a_checkra Ha_checkra "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (checkra_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iSplitL; last (iModIntro; iNext; iIntros (?); done).
    iNext; iIntros "H".
    iDestruct "H" as (p g b e a) "([%Hp ->] & HPC & Hca0 & Hcs0 & Hcs1 & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 5: check that [in] does not overlap with the stack frame *)
    focus_block 5 "Hcode_main" of so_main_blocks at pc_a as a_overlap Ha_overlap "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (check_no_overlap_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcsp $Hcode]"); eauto.
    iSplitL; last (iNext; iIntros (?); done).
    iNext; iIntros "(HPC & Hca0 & Hcsp & Hcs1 & Hcs0 & %Hno_overlap & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ so_block_offset 6)%a.
    iApply ("Hpost" $! p g b e a); iFrame "∗%"; done.
  Qed.

End SO_Check_Blocks_1.
