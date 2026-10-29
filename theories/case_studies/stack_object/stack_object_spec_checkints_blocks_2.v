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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
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
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_checkints")%a ∗
    ca0 ↦ᵣ[th] WCap t p g b e a @@? π ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ([∗ list] a;v ∈ l;ws, a ↦ₐ v) ∗
    codefrag_pers pc_a so_main_code ∗
    ( ▷ (⌜Forall (λ w, ∃ z, w.(lw) = WInt z) ws⌝ ∗
        PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_alloc")%a ∗
        ca0 ↦ᵣ[th] WCap t p g b e (finz.max b e) @@? π ∗
        cs0 ↦ᵣ[th] WInt 0 ∗
        cs1 ↦ᵣ[th] WInt 0 ∗
        ([∗ list] a;v ∈ l;ws, a ↦ₐ v) ∗
        codefrag_pers pc_a so_main_code ∗
        £ 2
        -∗ safe[th]) ∧
    ▷ (∀ a_f,
        ⌜a_f ∈ₐ [pc_a ^+ so_label_offset ".Lso_f_checkints", pc_a ^+ so_label_offset ".Lso_f_alloc")⌝ -∗
        (∃ a_r, ca0 ↦ᵣ[th] WCap t p g b e a_r @@? π) ∗
        cs0 ↦ᵣ[th] - ∗
        cs1 ↦ᵣ[th] - ∗
        ([∗ list] a;v ∈ l;ws, a ↦ₐ v) -∗
        trap_safe (Cap RX Global pc_b pc_e a_f) ⊤
          (HO th)) )
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hp Hshadow Hl)
      "(HPC & Hca0 & Hcs0 & Hcs1 & Hobject & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 6: check that [in] only contains integers *)
    focus_block (so_block ".Lso_f_checkints") "Hcode_main" of so_main_blocks at pc_a as a_checkints Ha_checkints "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (checkints_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hobject $Hcode]"); eauto.
    iSplit; cycle 1.
    { iNext; iIntros (a_f Ha_f) "(Hca0 & Hcs0 & Hcs1 & Hobject)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[%] [$]").
      offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hobject & %Hints & _ & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ so_label_offset ".Lso_f_alloc")%a.
    iDestruct "Hpost" as "[Hpost _]".
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
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_checkints")%a ∗
    ca0 ↦ᵣ[th] Cap⁻ p g b e a @@? π ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    codefrag_pers pc_a so_main_code ∗
    ( ca0 ↦ᵣ[th] Cap⁻ p g b e b @@? π ∗
      cs0 ↦ᵣ[th] - ∗
      cs1 ↦ᵣ[th] - -∗
      trap_safe
        (Cap RX Global pc_b pc_e
           ((pc_a ^+ so_label_offset ".Lso_f_checkints") ^+ checkints_loop_offset)%a) ⊤
        (HO th) )
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hbe)
      "(HPC & Hca0 & Hcs0 & Hcs1 & Hcode_main & Hfailed)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 6: [checkints] fails on the untagged object *)
    focus_block (so_block ".Lso_f_checkints") "Hcode_main" of so_main_blocks at pc_a as a_checkints Ha_checkints "Hcode" "Hcont".
    replace a_checkints with (pc_a ^+ so_label_offset ".Lso_f_checkints")%a
      by (offsets_compute; solve_addr).
    iApply (checkints_fail_untagged with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    offsets_compute; solve_addr.
  Qed.

End SO_Checkints_Blocks_2.
