From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_SetMIE.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import stdpp_extra.
Import CoreWPNotations.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  (** Code that the logical relation covers has no system-register
      permission, so [SetMIE] fails. *)
  Lemma setmie_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (mie : InterruptStatus)
    (P:D) :
    ftlr_instr W C regs p p' g b e a w (SetMIE mie) ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@".

    iDestruct (pc_open_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    destruct (has_sreg_access p) eqn:HpXRS.
    { iClear "IH Hreg Hinva Hrcond Hwcond Hworld_interp HPC Ha Hmap".
      iEval (rewrite !interp_unfold interp1_eq) in "Hinv_interp".
      destruct (isO p) eqn: HnO.
      { destruct Hp as [Hexec _]
        ; eapply executeAllowed_nonO in Hexec
        ; congruence.
      }
      destruct (has_sreg_access p) eqn:HpXRS'; first done.
      congruence.
    }

    iApply (wp_SetMIE with "[$HPC $Ha]"); eauto.

    iIntros "!>" (lpc' retv). iDestruct 1 as (HSpec) "(HPC & Ha)".
    destruct HSpec; cycle 1.
    - iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto.
    - simplify_eq; congruence.
  Qed.

End fundamental.
