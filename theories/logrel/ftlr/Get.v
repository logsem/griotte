From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Export rules_Get rules_base.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    (trusted_fault : CSTK → LWord → LReg → iProp Σ)
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma get_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : LWord) (ρ : region_type) (dst r : RegName) (ins: instr)
        (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    is_Get ins dst r →
    ftlr_instr trusted_fault W C regs p p' g b e a w ins ρ P cstk Ws Cs.
  Proof.
    intros Hinstr Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".
    rewrite <- Hi in Hinstr; clear Hi.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Get with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    (* GetTag may return 0 on a word whose tag may have been cleared: either
       way an integer is written. *)
    assert ((retv = FaultedV ∧ regs' = regs) ∨
            ∃ z, retv = NextIV ∧ incrementPC (WCap true p g b e a) = Some lpc' ∧
              regs' = <[dst := WInt z]ₗ> regs) as [(-> & ->) | (z & -> & Hinc & ->)].
    { destruct HSpec as [wsrc z Hsrc Hz Hinc -> | wsrc Hgt Hsrc Hstrip Hinc -> | Hfail Hlpc Hregs];
        [right; by exists z | right; by exists 0%Z | left; by split]. }
    - iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply (ftlr_trap with "Htrap Hreg Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.
    - incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ (<[dst := WInt z]ₗ> regs)
               with "[%] [] [HPC] [Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]")
        ; eauto.
      + by apply full_map_linsert.
      + iApply (interp_linsert with "Hreg"). iIntros (_). iApply interp_int.
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
