From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import dle_spec_states.

(** * Deep locality, block 0: initialisation of the data

    Block 0 sets [b := 0] and [a := (RW, Global, b, b+1, b)], and prepares
    the argument [(RW_DL, Local, a, a+1, a)] of the first call in [ca0]. *)

Section DLE_Init_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma dle_init_blocks_1_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (wca0 wct0 wct1 wct2 : LWord) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code) ->
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cgp_b ↦ₐ WInt 0 ∗
    (cgp_b ^+ 1) ↦ₐ WInt 0 ∗
    codefrag_pers pc_a dle_main_code ∗
    ▷ ( PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ dle_label_offset ".Ldle_fetch_switcher")%a ∗
        cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ[th] Cap RW_DL Local (cgp_b ^+ 1) (cgp_b ^+ 2) (cgp_b ^+ 1) ∗
        (∃ w, ct0 ↦ᵣ[th] w) ∗
        (∃ w, ct1 ↦ᵣ[th] w) ∗
        (∃ w, ct2 ↦ᵣ[th] w) ∗
        cgp_b ↦ₐ WInt 0 ∗
        (cgp_b ^+ 1) ↦ₐ Cap RW Global cgp_b (cgp_b ^+ 1) cgp_b ∗
        codefrag_pers pc_a dle_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (HsubBounds Hcgp_contiguous Hcgp_mmio [Hcgp_nonheap Hcgp_heap])
      "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hcgp_b & Hcgp_a & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.

    (* Block 0: initialisation *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 0%Z 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hcgp_mmio. }
    { solve_addr. }
    (* Mov ct0 cgp *)
    iInstr "Hcode".
    (* GetB ct1 cgp *)
    iInstr "Hcode".
    (* Add ct2 ct1 1%Z *)
    iInstr "Hcode".
    (* Subseg ct0 ct0 ct1 ct2 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }
    { solve_addr. }
    { solve_addr. }
    (* Lea cgp cgp 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }
    iPoseProof deref_res_none as "-#Hdw".
    (* [iInstr] does not find the resources of this store *)
    (* Store cgp ct0 0 *)
    iInstrApply "Hcode" wp_store_success_reg with "[$HPC $Hct0 $Hcgp $Hcgp_a $Hdw]"
      as "(HPC & Hct0 & Hcgp & Hcgp_a & _)".
    { solve_not_shadow Hcgp_mmio. }
    { rewrite /withinBounds; solve_addr. }
    { done. }
    (* Mov ca0 cgp *)
    iInstr "Hcode".
    (* Lea cgp cgp (-1)%Z *)
    iInstr "Hcode".
    { transitivity (Some cgp_b); auto; solve_addr. }
    (* Add ct1 ct2 1%Z *)
    iInstr "Hcode".
    assert (is_heap_address (cgp_b ^+ 1) = false) as Hcgp1_nonheap
      by solve_not_heap Hcgp_heap.
    clear Hcgp_nonheap.
    (* Subseg ca0 ca0 ct2 ct1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }
    { transitivity (Some (cgp_b ^+ 2)); auto; solve_addr. }
    { solve_addr. }
    { solve_addr. }
    (* Restrict ca0 ca0 (encodePermPair (RW_DL, Local)) *)
    iInstr "Hcode".
    { by rewrite decode_encode_permPair_inv. }
    { solve_pure. }
    { solve_pure. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End DLE_Init_Blocks_1.
