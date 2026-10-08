From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import stack_object_spec_states.

(** * Stack object, block 6: the stack object [in] only contains integers

    Block 6 checks that all the cells of the stack object [in] (in [ca0])
    contain integers. The points-to predicates of the cells are given in
    any order [l]. The group ends at the beginning of block 7. *)

Section SO_Checkints_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_checkints_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (p : Perm) (g : Locality) (b e a : Addr)
    (l : list Addr) (ws : list Word)
    (wcs0 wcs1 : Word) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    readAllowed p = true ->
    l ≡ₚ finz.seq_between b e ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ so_block_offset 6)%a ∗
    ca0 ↦ᵣ WCap p g b e a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ([∗ list] a;v ∈ l;ws, a ↦ₐ v) ∗
    codefrag pc_a so_main_code ∗
    ▷ (⌜Forall (λ w, ∃ z, w = WInt z) ws⌝ ∗
        PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ so_block_offset 7)%a ∗
        ca0 ↦ᵣ WCap p g b e (finz.max b e) ∗
        cs0 ↦ᵣ WInt 0 ∗
        cs1 ↦ᵣ WInt 0 ∗
        ([∗ list] a;v ∈ l;ws, a ↦ₐ v) ∗
        codefrag pc_a so_main_code ∗
        £ 2
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous] Hp Hl)
      "(HPC & Hca0 & Hcs0 & Hcs1 & Hobject & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 6: check that [in] only contains integers *)
    focus_block 6 "Hcode_main" of so_main_blocks at pc_a as a_checkints Ha_checkints "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (checkints_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hobject $Hcode]"); eauto.
    iSplitL; last (iModIntro; iNext; iIntros (?); done).
    iNext; iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hobject & %Hints & Hcode & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ so_block_offset 7)%a.
    iApply "Hpost"; iFrame "∗%".
  Qed.

End SO_Checkints_Blocks_2.
