From griotte Require Export logrel.
From griotte Require Export rules_BinOp.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import rules_base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import machine_base.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    (trap_no_resume : LWord → Prop)
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma WorldRes_acc (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) Φ (w : LWord) ρ :
    WorldRes W C a p Φ w ρ -∗
    ( a ↦ₐ w ∗ Φ (W,C,w) ) ∗
    ( ( a ↦ₐ w ∗ Φ (W,C,w) ) -∗ WorldRes W C a p Φ w ρ ).
  Proof.
    iIntros "(Hp&Ha&HΦ&Hmono)".
    iSplitL "Ha HΦ"; iFrame.
    iIntros "[Ha HΦ]"; iFrame "∗#".
  Qed.


  Lemma binop_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg) (p p' : Perm)
    (g : Locality) (b e a : Addr) (w : LWord) (ρ : region_type) (dst : RegName)
    (r1 r2: Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr_base trap_no_resume W C regs p p' g b e a w ρ P
      (decodeInstrW w.(lw) = Add dst r1 r2 \/
       decodeInstrW w.(lw) = Sub dst r1 r2 \/
       decodeInstrW w.(lw) = Mul dst r1 r2 \/
       decodeInstrW w.(lw) = LAnd dst r1 r2 \/
       decodeInstrW w.(lw) = LOr dst r1 r2 \/
       decodeInstrW w.(lw) = LShiftL dst r1 r2 \/
       decodeInstrW w.(lw) = LShiftR dst r1 r2 \/
       decodeInstrW w.(lw) = Lt dst r1 r2
      ) cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_BinOp with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [n1 n2 Hn1 Hn2 Hinc -> | ]; cycle 1.
    - subst regs'.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply (ftlr_trap with "Htrap Hreg HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.
    - incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ₗ> regs) with "[%] [] [HPC] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]")
      ; eauto.
      + intro; cbn. rewrite /linsert_reg. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hregs_ri).
        rewrite /linsert_reg in Hregs_ri.
        destruct (decide (ri = dst)); simplify_map_eq.
        { destruct (decide (dst = cnull)) ; [iApply interp_int|].
         repeat rewrite interp_unfold; auto. }
        { iApply "Hreg"; eauto. }
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
