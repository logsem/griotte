From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_UnSeal.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).
  Lemma unseal_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (dst r1 r2 : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (UnSeal dst r1 r2) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_UnSeal with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [ * Hr1 Hr2 Htag Hunseal Hwb HincrPC Hregs'
                      | * Hr1 Hr2 Hvalid HincrPC Hregs'
                      | * Hr1 Hr2 Hk HincrPC Hregs' | ].
    {
      apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.

      assert (r1 ≠ cnull) as Hr1null.
      { intros ->. rewrite /llookup_reg in Hr1. apply bind_Some in Hr1 as (? & _ & Hw). simplify_eq. }
      assert (r2 ≠ cnull) as Hr2null.
      { intros ->. rewrite /llookup_reg in Hr2. apply bind_Some in Hr2 as (? & _ & Hw). simplify_eq. }
      rewrite llookup_reg_not_cnull // in Hr1.
      rewrite llookup_reg_not_cnull // in Hr2.

      iDestruct ("Hreg" $! r1 _ Hr1) as "HVsr".
      iDestruct ("Hreg" $! r2 _ Hr2) as "HVsd".
      (* Generate interp instance before step, so we get rid of the later *)
      iDestruct (unsealing_preserves_interp with "HVsd HVsr Hworld_interp")
        as "(#HVsb & Hworld_interp)"; auto.

      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs'
                 with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]")
      ; eauto.
      + cbn; intros; subst regs'. rewrite /linsert_reg. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert_eq in Hvs; injection Hvs as <-.
          destruct (decide (dst = cnull)) ; [by iApply interp_untagged | done].
        }
        { rewrite !lookup_insert_ne // in Hvs.
          iApply "Hreg"; auto.
        }
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          iApply interp_untagged.
          by rewrite /= get_tag_clear_tag_sealable.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { (* The destination loses its tag. *)
      apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri wi Hregs_ri).
        subst regs'. rewrite /linsert_reg in Hregs_ri.
        destruct (decide (ri = dst)) as [->|Hne].
        { rewrite lookup_insert_eq in Hregs_ri.
          injection Hregs_ri as <-.
          destruct (decide (dst = cnull)); [by iApply interp_untagged | iApply interp_clear_tag]. }
        rewrite !lookup_insert_ne in Hregs_ri; try congruence.
        iApply "Hreg"; eauto.
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto. }
  Qed.

End fundamental.
