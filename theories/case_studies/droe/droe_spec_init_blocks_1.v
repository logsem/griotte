From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import droe_spec_states.

(** * Deep immutability, block 0: initialisation of the data

    Block 0 sets [b := 42] and [a := (RW, Global, b, b+1, b)], and prepares
    the argument [(RO_DRO, Global, a, a+1, a)] of the call in [ca0]. *)

Section DROE_Init_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma droe_init_blocks_1_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (wca0 wct0 wct1 wct2 : Word) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length droe_main_code)%a ->
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ wca0 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cgp_b ↦ₐ WInt 0 ∗
    (cgp_b ^+ 1)%a ↦ₐ WInt 0 ∗
    codefrag pc_a droe_main_code ∗
    ▷ ( PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ droe_block_offset 1)%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ WCap RO_DRO Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a ∗
        (∃ w, ct0 ↦ᵣ w) ∗
        (∃ w, ct1 ↦ᵣ w) ∗
        (∃ w, ct2 ↦ᵣ w) ∗
        cgp_b ↦ₐ WInt 42 ∗
        (cgp_b ^+ 1)%a ↦ₐ WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b ∗
        codefrag pc_a droe_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HsubBounds Hcgp_contiguous)
      "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hcgp_b & Hcgp_a & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.

    (* Block 0: initialisation *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 42%Z *)
    iInstr "Hcode".
    { solve_addr. }
    (* Mov ct0 cgp *)
    iInstr "Hcode".
    (* GetB ct1 cgp *)
    iInstr "Hcode".
    (* Add ct2 ct1 1%Z *)
    iInstr "Hcode".
    (* Subseg ct0 ct1 ct2 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    (* Lea cgp 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    (* Store cgp ct0 *)
    (* [iInstr] does not find the resources of this store *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg with "[$HPC $Hi $Hct0 $Hcgp $Hcgp_a]") ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hcgp_a)".
    iDestruct ("Hcode" with "Hi") as "Hcode".
    wp_pure.
    (* Mov ca0 cgp *)
    iInstr "Hcode".
    (* Lea cgp (-1)%Z *)
    iInstr "Hcode".
    { transitivity (Some cgp_b); auto; solve_addr. }
    (* Add ct1 ct2 1%Z *)
    iInstr "Hcode".
    (* Subseg ca0 ct2 ct1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    (* Restrict ca0 (encodePermPair (RO_DRO, Global)) *)
    iInstr "Hcode".
    { by rewrite decode_encode_permPair_inv. }
    { solve_pure. }
    { solve_pure. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame.
  Qed.

End DROE_Init_Blocks_1.
