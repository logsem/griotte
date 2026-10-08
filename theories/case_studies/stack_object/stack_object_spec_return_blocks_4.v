From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import stack_object_spec_states.

(** * Stack object, blocks 10-12: return from the callback [g]

    Block 10 pops the stack object [z] and reads back the secret, block 11
    asserts that the secret is unchanged, and block 12 clears the return
    registers and returns to the caller of [f]. *)

Section SO_Return_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_return_blocks_4_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable) (Nassert : namespace) (E : coPset)
    (csp_b csp_e a_stk2 : Addr)
    (wct0 wct1 wct2 wct3 wct4 wcnull wcra wret wca0 wca1 : Word) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    (csp_b + 2)%a = Some a_stk2 ->
    (csp_b < csp_e)%a ->
    ↑Nassert ⊆ E ->
    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
    na_own cerise_nais E ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ so_block_offset 10)%a ∗
    csp ↦ᵣ WCap RWL Local csp_b csp_e a_stk2 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ct3 ↦ᵣ wct3 ∗
    ct4 ↦ᵣ wct4 ∗
    cnull ↦ᵣ wcnull ∗
    cra ↦ᵣ wcra ∗
    cs0 ↦ᵣ wret ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    csp_b ↦ₐ WInt so_secret ∗
    (pc_b ^+ 1)%a ↦ₐ so_assert_entry ∗
    codefrag pc_a so_main_code ∗
    ▷ (na_own cerise_nais E ∗
        PC ↦ᵣ updatePcPerm wret ∗
        csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct1 ↦ᵣ WInt 0 ∗
        ct2 ↦ᵣ WInt 0 ∗
        ct3 ↦ᵣ WInt 0 ∗
        ct4 ↦ᵣ WInt 0 ∗
        cnull ↦ᵣ WInt 0 ∗
        cra ↦ᵣ wret ∗
        cs0 ↦ᵣ wret ∗
        ca0 ↦ᵣ WInt 0 ∗
        ca1 ↦ᵣ WInt 0 ∗
        csp_b ↦ₐ WInt so_secret ∗
        (pc_b ^+ 1)%a ↦ₐ so_assert_entry ∗
        codefrag pc_a so_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous] Hastk2 Hcsp_size HNassert)
      "(#Hassert & Hna & HPC & Hcsp & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hcnull & Hcra
      & Hcs0 & Hca0 & Hca1 & Hsecret & Himport_assert & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.
    rewrite /so_assert_entry.

    (* Block 10: read back the secret *)
    focus_block 10 "Hcode_main" of so_main_blocks at pc_a as a_prep Ha_prep "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Lea csp (-2)%Z *)
    iInstr "Hcode".
    { transitivity (Some csp_b); auto. solve_addr+Hastk2. }
    (* Load ct0 csp *)
    iInstr "Hcode".
    { split; auto. rewrite /withinBounds. solve_addr. }
    (* Mov ct1 so_secret *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 11: assert that the secret is unchanged *)
    focus_block 11 "Hcode_main" of so_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra $Hcnull
              $Hcode $Himport_assert]"); auto.
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 12: return *)
    focus_block 12 "Hcode_main" of so_main_blocks at pc_a as a_return Ha_return "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Mov ca0 0%Z *)
    iInstr "Hcode".
    (* Mov ca1 0%Z *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame.
  Qed.

End SO_Return_Blocks_4.
