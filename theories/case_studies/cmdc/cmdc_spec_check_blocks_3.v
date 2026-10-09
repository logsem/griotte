From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, blocks 3-4 and 8-9: assertions after the calls

    On return from the call [c], the third block of the call loads the
    word pointed to by [cgp] (the data that was not shared with the
    callee), and the next block asserts that it is unchanged. *)

Section CMDC_Check_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The proof of [cmdc_check_blocks_3_spec], for the call starting at
      block [n]: the code of the two calls only differs by the asserted
      value. *)
  Local Ltac cmdc_check_blocks_proof n pc_a :=
    let hcont := fresh "hcont" in
    let a_call := fresh "a_call" in
    let a_assert := fresh "a_assert" in
    let Ha_call := fresh "Ha_call" in
    let Ha_assert := fresh "Ha_assert" in
    (* Block n+2: return from the call *)
    focus_block (S (S n)) "Hcode_main" of cmdc_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    change_pc_to (a_call ^+ 1)%a;
    (* Load ct0 cgp *)
    iInstr "Hcode"; [split; [done | solve_addr] |];
    (* Mov ct1 0%Z, resp. Mov ct1 42%Z *)
    iInstr "Hcode";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";

    (* Block n+3: assert that the data is unchanged *)
    focus_block (S (S (S n))) "Hcode_main" of cmdc_main_blocks at pc_a
      as a_assert Ha_assert "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto; [solve_addr|];
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";
    change_pc_to (pc_a ^+ cmdc_block_offset (n + 4))%a;
    iApply "Hpost"; iFrame.

  Lemma cmdc_check_blocks_3_spec (c : cmdc_call)
    (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable) (Nassert : namespace)
    (cgp_b cgp_e a_chk : Addr)
    (wct0 wct1 wct2 wct3 wct4 wcnull wcra : Word) :
    let n := cmdc_call_block c in
    cmdc_code_bounds pc_b pc_e pc_a B_f C_g ->
    (cgp_b <= a_chk < cgp_e)%a ->
    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
    na_own cerise_nais ⊤ ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_instr_offset (n + 2) 1)%a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e a_chk ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ct3 ↦ᵣ wct3 ∗
    ct4 ↦ᵣ wct4 ∗
    cnull ↦ᵣ wcnull ∗
    cra ↦ᵣ wcra ∗
    a_chk ↦ₐ WInt (cmdc_call_expected c) ∗
    (pc_b ^+ 1)%a ↦ₐ WSentry RX Global b_assert e_assert b_assert ∗
    codefrag pc_a cmdc_main_code ∗
    ▷ ( na_own cerise_nais ⊤ ∗
        PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset (n + 4))%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e a_chk ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct1 ↦ᵣ WInt 0 ∗
        ct2 ↦ᵣ WInt 0 ∗
        ct3 ↦ᵣ WInt 0 ∗
        ct4 ↦ᵣ WInt 0 ∗
        cnull ↦ᵣ WInt 0 ∗
        cra ↦ᵣ wcra ∗
        a_chk ↦ₐ WInt (cmdc_call_expected c) ∗
        (pc_b ^+ 1)%a ↦ₐ WSentry RX Global b_assert e_assert b_assert ∗
        codefrag pc_a cmdc_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros n.
    destruct c; subst n; cbn [cmdc_call_block cmdc_call_expected].
    all: iIntros ([HsubBounds Himports_contiguous] Ha_chk)
      "(#Hassert & Hna & HPC & Hcgp & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hcnull & Hcra
      & Ha_chk & Himport_assert & Hcode_main & Hpost)".
    all: codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    all: unfold_code cmdc_main_code "Hcode_main".
    - (* Return from [B.f], blocks 3-4 *)
      cmdc_check_blocks_proof 1 pc_a.
    - (* Return from [C.g], blocks 8-9 *)
      cmdc_check_blocks_proof 6 pc_a.
  Qed.

End CMDC_Check_Blocks_3.
