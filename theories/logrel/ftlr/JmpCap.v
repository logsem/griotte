From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
From cap_machine Require Import rules_JmpCap.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma jmpcap_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (rsrc : RegName) (P:V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (wstk : Word) :
    ftlr_instr W C regs p p' g b e a w (JmpCap rsrc) ρ P cstk Ws Cs wstk.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hown Hcstk".
    iIntros "Hr Hstate Ha HPC Hmap %Hwstk".
    destruct (decide (rsrc = PC)) as [HrPC|HrPC].
    - subst rsrc.
      iApply (wp_jmpcap_successPC with "[HPC Ha]"); eauto; first iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iNext; iIntros "_".
      iInsert "Hmap" PC.
      (* close region *)
      iDestruct (region_close with "[$Hstate $Hr Hw $Ha $HmonoV]") as "Hr"; eauto.
      { destruct ρ;auto;contradiction. }
      (* apply IH *)
      iApply ("IH" $! _ _ _ _ _ _ _ g _ _ a with "[] [] [Hmap] [%] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$]"); eauto.
      { iPureIntro; apply Hsome. }

    - iAssert (∃ wsrc,
                  ⌜ regs !! rsrc = Some wsrc ⌝
                  ∗ rsrc ↦ᵣ wsrc
                  ∗ ([∗ map] k↦y ∈ delete rsrc (delete PC regs), k ↦ᵣ y)
              )%I with "[Hmap]" as (wsrc) "(%Hsomesrc & Hrsrc & Hmap)".
      { specialize Hsome with rsrc as Hrsrc; destruct Hrsrc as [wsrc Hsomesrc].
        destruct (decide (rsrc = csp)) as [Hr_csp|Hr_csp]; simplify_map_eq.
        + iExtract "Hmap" csp as "Hrsrc"; iFrame; done.
        + iExtract "Hmap" rsrc as "Hrsrc"; iFrame; done.
      }
      iApply (wp_jmpcap_success with "[$HPC $Ha $Hrsrc]"); eauto.
      iNext. iIntros "[HPC [Ha Hrsrc]] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iInsert "Hmap" rsrc;
        rewrite -delete_insert_ne; auto.
      destruct (updatePcPerm wsrc) eqn:Heq ; [ | destruct sb | | ]; cycle 1.
      { destruct (executeAllowed p0) eqn:Hpft; cycle 1.
        { iNext; iIntros "_".
          iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value; iIntros; discriminate.
        }
        iInsert "Hmap" PC.
        rewrite (insert_id regs rsrc); auto.
        iDestruct ("Hreg" $! rsrc _ HrPC Hsomesrc) as "Hwsrc".
        destruct wsrc; simpl in Heq; try congruence; simplify_eq.
        - (* case cap *)
          iEval (rewrite fixpoint_interp1_eq) in "Hinv_interp".
          iNext; iIntros "_".
          iDestruct (region_close with "[$Hstate $Hr Hw $Ha $HmonoV]") as "Hr"; eauto.
          { destruct ρ;auto;contradiction. }
          iApply ("IH" with "[] [] [Hmap] [%] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$]"); eauto.
          auto.
        - (* case sentry *)
          iEval (rewrite fixpoint_interp1_eq) in "Hwsrc".
          simpl; rewrite /enter_cond.
          iDestruct "Hwsrc" as "#H".
          iAssert (future_world g0 W W) as "Hfuture".
          { iApply futureworld_refl. }
          iSpecialize ("H" with "Hfuture").
          pose proof (LocalityFlowsToReflexive g0) as Hg0.
          iSpecialize ("H" $! g0 Hg0).
          iDestruct (region_close with "[$Hstate $Hr Hw $Ha $HmonoV]") as "Hr"; eauto.
          { destruct ρ;auto;contradiction. }
          iDestruct ("H" with "[$Hcont $Hmap $Hr $Hsts $Hcstk $Hown]") as "HA"; eauto.
          iFrame "#%".
      }

      (* Non-capability cases *)
      all: iNext; iIntros "_".
      all: iApply (wp_bind (fill [SeqCtx])).
      all: iApply (wp_notCorrectPC with "HPC"); [intro Hcontra ; inv Hcontra|].
      all: iNext; iIntros "HPC /=".
      all: iApply wp_pure_step_later; auto; iNext; iIntros "_".
      all: iApply wp_value; iIntros; discriminate.
  Qed.

End fundamental.
