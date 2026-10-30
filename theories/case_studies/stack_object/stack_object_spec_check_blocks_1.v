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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_check_blocks_1_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (csp_b csp_e : Addr)
    (wca0 wca1 wct1 wcs0 wcs1 : LWord) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f")%a ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    codefrag_pers pc_a so_main_code ∗
    ( ▷ (∀ t p g b e a π,
        ⌜readAllowed p = true⌝ ∗
        ⌜wca0 = WCap t p g b e a @@? π⌝ ∗
        ⌜finz.seq_between b e ## finz.seq_between csp_b csp_e⌝ ∗
        PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_checkints")%a ∗
        ca0 ↦ᵣ[th] WCap t p g b e a @@? π ∗
        ca1 ↦ᵣ[th] wca1 ∗
        ct1 ↦ᵣ[th] wca1 ∗
        cs0 ↦ᵣ[th] WInt 0 ∗
        cs1 ↦ᵣ[th] WInt 0 ∗
        csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
        codefrag_pers pc_a so_main_code ∗
        £ 1
        -∗ safe[th]) ∧
    (∀ a_f,
        ⌜a_f ∈ₐ [pc_a ^+ so_label_offset ".Lso_f", pc_a ^+ so_label_offset ".Lso_f_checkints")⌝ -∗
        ca0 ↦ᵣ[th] wca0 ∗
        ca1 ↦ᵣ[th] wca1 ∗
        ct1 ↦ᵣ[th] wca1 ∗
        cs0 ↦ᵣ[th] - ∗
        cs1 ↦ᵣ[th] - ∗
        csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) -∗
        trap_safe (Cap RX Global pc_b pc_e a_f) ⊤
          (HO th)) )
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap))
      "(HPC & Hca0 & Hca1 & Hct1 & Hcs0 & Hcs1 & Hcsp & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 3: save the callback *)
    focus_block (so_block ".Lso_f") "Hcode_main" of so_main_blocks at pc_a as a_mov Ha_mov "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ct1 ca1 *)
    iInstr "Hcode" with "Hlc".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: check that [in] is readable *)
    focus_block (so_block ".Lso_f_checkra") "Hcode_main" of so_main_blocks at pc_a as a_checkra Ha_checkra "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (checkra_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iSplit; cycle 1.
    { iIntros (a_f Ha_f) "(Hca0 & Hcs0 & Hcs1)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[%] [$]").
      offsets_compute; solve_addr. }
    iNext; iIntros "H".
    iDestruct "H" as (t p g b e a π) "([%Hp ->] & HPC & Hca0 & Hcs0 & Hcs1 & _)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 5: check that [in] does not overlap with the stack frame *)
    focus_block (so_block ".Lso_f_check_no_overlap") "Hcode_main" of so_main_blocks at pc_a as a_overlap Ha_overlap "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (check_no_overlap_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcsp $Hcode]"); eauto.
    iSplit; cycle 1.
    { iIntros (a_f Ha_f) "(Hca0 & Hcsp & Hcs0 & Hcs1)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[%] [$]").
      offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hca0 & Hcsp & Hcs1 & Hcs0 & %Hno_overlap & _)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ so_label_offset ".Lso_f_checkints")%a.
    iDestruct "Hpost" as "[Hpost _]".
    iApply ("Hpost" $! t p g b e a π); iFrame "∗% Hcode_main"; done.
  Qed.

End SO_Check_Blocks_1.
