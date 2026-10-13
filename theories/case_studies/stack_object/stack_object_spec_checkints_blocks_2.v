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
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_checkints_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (t : bool) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (l : list Addr) (ws : list LWord)
    (wcs0 wcs1 : LWord) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    readAllowed p = true ->
    disjoint_from_shadow b e ->
    l ≡ₚ finz.seq_between b e ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_checkints")%a ∗
    ca0 ↦ᵣ WCap t p g b e a @@? π ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ([∗ list] a;v ∈ l;ws, a ↦ₐ v) ∗
    codefrag_pers pc_a so_main_code ∗
    ▷ (⌜Forall (λ w, ∃ z, w.(lw) = WInt z) ws⌝ ∗
        PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_alloc")%a ∗
        ca0 ↦ᵣ WCap t p g b e (finz.max b e) @@? π ∗
        cs0 ↦ᵣ WInt 0 ∗
        cs1 ↦ᵣ WInt 0 ∗
        ([∗ list] a;v ∈ l;ws, a ↦ₐ v) ∗
        codefrag_pers pc_a so_main_code ∗
        £ 2
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hp Hshadow Hl)
      "(HPC & Hca0 & Hcs0 & Hcs1 & Hobject & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 6: check that [in] only contains integers *)
    focus_block (so_block ".Lso_f_checkints") "Hcode_main" of so_main_blocks at pc_a as a_checkints Ha_checkints "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (checkints_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hobject $Hcode]"); eauto.
    iSplitL; last (iModIntro; iNext; iIntros (?); done).
    iNext; iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hobject & %Hints & _ & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ so_label_offset ".Lso_f_alloc")%a.
    iApply "Hpost"; iFrame "∗% Hcode_main".
  Qed.

  (** Failure path of block 6: [checkints] fails on an untagged, non-empty
      stack object [in]. *)
  Lemma so_checkints_blocks_2_untagged_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (wcs0 wcs1 : LWord) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    (b < e)%a ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_checkints")%a ∗
    ca0 ↦ᵣ WCap false p g b e a @@? π ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    codefrag_pers pc_a so_main_code
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hbe)
      "(HPC & Hca0 & Hcs0 & Hcs1 & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 6: [checkints] fails on the untagged object *)
    focus_block (so_block ".Lso_f_checkints") "Hcode_main" of so_main_blocks at pc_a as a_checkints Ha_checkints "Hcode" "Hcont".
    iApply (checkints_fail_untagged with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iModIntro; iNext; iIntros (?); done.
  Qed.

End SO_Checkints_Blocks_2.
