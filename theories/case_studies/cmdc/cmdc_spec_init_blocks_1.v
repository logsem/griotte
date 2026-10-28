From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, block 0: initialisation of the data

    Block 0 saves the return address of the thread in [cs0], sets [b := 0]
    and [c := 0], and prepares the argument
    [(RW, Global, b, b+1, b)] of the call to [B.f] in [ca0]. The group ends
    with [cgp] pointing to [c]. *)

Section CMDC_Init_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma cmdc_init_blocks_1_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (wca0 wct0 wct1 wcs0 wcra : LWord) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code) ->
    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    is_mmio_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    is_mmio_address (cgp_b ^+ 1) = false ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cra ↦ᵣ[th] wcra ∗
    cgp_b ↦ₐ WInt 0 ∗
    (cgp_b ^+ 1) ↦ₐ WInt 0 ∗
    codefrag_pers pc_a cmdc_main_code ∗
    ▷ ( PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ cmdc_label_offset ".Lcmdc_call_B")%a ∗
        cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e (cgp_b ^+ 1) ∗
        ca0 ↦ᵣ[th] Cap RW Global cgp_b (cgp_b ^+ 1) cgp_b ∗
        (∃ w, ct0 ↦ᵣ[th] w) ∗
        (∃ w, ct1 ↦ᵣ[th] w) ∗
        cs0 ↦ᵣ[th] wcra ∗
        cra ↦ᵣ[th] wcra ∗
        cgp_b ↦ₐ WInt 0 ∗
        (cgp_b ^+ 1) ↦ₐ WInt 0 ∗
        codefrag_pers pc_a cmdc_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (HsubBounds Hcgp_contiguous Hcgp_mmio Hcgp_heap Hcgp1_mmio)
      "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hcs0 & Hcra & Hcgp_b & Hcgp_c & Hcode_main
        & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.

    (* Block 0: initialisation *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Store cgp 0%Z 0 *)
    iInstr "Hcode".
    { by apply not_mmio_not_shadow. }
    { solve_addr. }
    (* Mov ca0 cgp *)
    iInstr "Hcode".
    (* Lea cgp cgp 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }
    (* Store cgp 0%Z 0 *)
    iInstr "Hcode".
    { by apply not_mmio_not_shadow. }
    { solve_addr. }
    (* GetA ct0 ca0 *)
    iInstr "Hcode".
    (* Add ct1 ct0 1%Z *)
    iInstr "Hcode".
    (* Subseg ca0 ca0 ct0 ct1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }
    { solve_addr. }
    { solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End CMDC_Init_Blocks_1.
