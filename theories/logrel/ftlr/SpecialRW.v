From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_SpecialRW.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import stdpp_extra.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
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

  (** Code that the logical relation covers has no system-register
      permission, so [SpecialRW] fails. *)
  Lemma specialrw_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (dst : RegName) (sr : SRegName) (src : Z + RegName)
    (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr trusted_fault W C regs p p' g b e a w (SpecialRW dst sr src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    destruct (has_sreg_access p) eqn:HpXRS.
    { iClear "IH Hreg Hinva Hrcond Hwcond Hmono Hworld_interp Htframe Hown Hstate HPC Ha Hmap".
      iEval (rewrite !interp_unfold interp1_eq) in "Hinv_interp".
      destruct (isO p) eqn: HnO.
      { destruct Hp as [Hexec _]
        ; eapply executeAllowed_nonO in Hexec
        ; congruence.
      }
      destruct (has_sreg_access p) eqn:HpXRS'; first done.
      congruence.
    }

    iApply (wp_SpecialRW _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }
    { by rewrite HpXRS. }

    iIntros "!>" (lpc' regs' sregs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap & _)".
    destruct HSpec; cycle 1.
    - subst regs'.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply (ftlr_trap with "Htrap Hreg Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.
    - simplify_map_eq; congruence.
  Qed.

End fundamental.
