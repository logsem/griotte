From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base monotone interp_weakening.
From griotte Require Import rules_base rules_Seal.
From griotte Require Import map_simpl register_tactics.
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

  Lemma seal_case (W : WORLD)(C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (dst r1 r2 : RegName) (P:D) :
    ftlr_instr W C regs p p' g b e a w (Seal dst r1 r2) ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@".

    iDestruct (pc_open_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply wp_fupd.
    iApply (wp_Seal (CL := link_core) with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [ * Hr1 Hr2 Htag Hseal Hwb HincrPC Hregs'
                      | * Hr1 Hr2 Hvalid HincrPC Hregs'
                      | * Hr1 Hr2 Hk HincrPC Hregs' | Hfail ].
    - apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      assert (r1 ≠ cnull) as Hr1null.
      { intros ->. rewrite llookup_reg_cnull /lnull in Hr1. simplify_eq. }
      assert (r2 ≠ cnull) as Hr2null.
      { intros ->. rewrite llookup_reg_cnull /lnull in Hr2. simplify_eq. }
      rewrite llookup_reg_not_cnull // in Hr1.
      rewrite llookup_reg_not_cnull // in Hr2.

      (* The sealed payload keeps its identifier. *)
      iAssert (interp W C (WSealable sb @@? π)) as "#HVsb".
      { iApply "Hreg"; eauto. }

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.

      iDestruct ("Hreg" $! r1 _ Hr1) as "HVsr".
      iDestruct (sealing_preserves_interp with "HVsb HVsr") as "#HVsb'"; auto.
      iModIntro. iNext.
      iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp").
      + subst regs'. by apply full_map_linsert.
      + iIntros (ri wi Hregs_ri).
        subst regs'. rewrite /linsert_reg in Hregs_ri.
        case_decide as Hdst_null.
        { by iApply "Hreg". }
        destruct (decide (ri = dst)) as [->|Hne'].
        { rewrite lookup_insert_eq in Hregs_ri. injection Hregs_ri as <-.
          iExact "HVsb'". }
        rewrite !lookup_insert_ne // in Hregs_ri.
        by iApply "Hreg".
      + iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.

    - apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iModIntro. iNext.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.

      iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp").
      + subst regs'. by apply full_map_linsert.
      + subst regs'. iApply (interp_linsert with "Hreg"). iIntros (_).
        iApply interp_untagged.
        by rewrite /= get_tag_clear_tag_sealable.
      + iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    
    - { (* The destination loses its tag. *)
      apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iModIntro. iNext.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (_).
        iApply interp_clear_tag.
      - iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    - assert (regs' = regs) as -> by (destruct Hfail; done).
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iModIntro. iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto.
  Qed.

End fundamental.
