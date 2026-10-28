From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Export rules_Get rules_base.
From griotte Require Import map_simpl register_tactics.
Import CoreWPNotations.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma get_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : LWord) (ρ : region_type) (dst r : RegName) (ins: instr)
        (P:D) :
    is_Get ins dst r →
    ftlr_instr W C regs p p' g b e a w ins ρ P.
  Proof.
    intros Hinstr Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".
    rewrite <- Hi in Hinstr; clear Hi.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Get (CL := link_core) with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    (* GetTag may return 0 on a word whose tag may have been cleared: either
       way an integer is written. *)
    assert ((retv = FaultedV ∧ regs' = regs) ∨
            ∃ z, retv = NextIV ∧ incrementPC (Cap p g b e a) = Some lpc' ∧
              regs' = <[dst := WInt z]ₗ> regs) as [(-> & ->) | (z & -> & Hinc & ->)].
    { destruct HSpec as [wsrc z Hsrc Hz Hinc -> | wsrc Hgt Hsrc Hstrip Hinc -> | Hfail Hlpc Hregs];
        [right; by exists z | right; by exists 0%Z | left; by split]. }
    - iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto.
    - incrementPC_inv; simplify_map_eq.
      iNext.

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp")
        ; eauto.
      + by apply full_map_linsert.
      + iApply (interp_linsert with "Hreg"). iIntros (_). iApply interp_int.
      + iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
