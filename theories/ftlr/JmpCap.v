From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base ftlr_switcher_call ftlr_switcher_return.
From cap_machine.rules Require Import rules_JmpCap.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
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
    (w : Word) (ρ : region_type) (rsrc : RegName) (P:V) (cstk : CSTK) (wstk : Word) (Nswitcher : namespace) :
    ftlr_instr W C regs p p' g b e a w (JmpCap rsrc) ρ P cstk wstk Nswitcher.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont Hsts Hown Hcstk".
    iIntros "Hr Hstate Ha HPC Hmap %Hwstk #Hinv_switcher".
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
      iApply ("IH" $! _ _ _ _ _ g _ _ a with "[] [] [Hmap] [%] [$Hr] [$Hsts] [$Hcont] [$Hown] [$]"); eauto.
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
          iApply ("IH" with "[] [] [Hmap] [%] [$Hr] [$Hsts] [$Hcont] [$Hown] [$]"); eauto.
          auto.
        - (* case sentry *)
          iEval (rewrite fixpoint_interp1_eq) in "Hwsrc".
          simpl; rewrite /enter_cond.
          destruct (is_switcher_entry_point p0 g0 b0 e0 a0) eqn:His_switcher_call.
          + (* This is a switcher entry point: execute the switcher *)
            rewrite /is_switcher_entry_point in His_switcher_call.
            destruct (decide (p0 = XSRW_)); simplify_eq;
              [ rewrite bool_decide_eq_true_2 in His_switcher_call; last done
              | rewrite bool_decide_eq_false_2 in His_switcher_call; done ].
            destruct (decide (g0 = Local)); simplify_eq;
              [ rewrite bool_decide_eq_true_2 in His_switcher_call; last done
              | rewrite bool_decide_eq_false_2 in His_switcher_call; done].
            simpl in His_switcher_call.
            destruct (b0 =? b_switcher)%a eqn:Hb0
            ; rewrite Hb0 in His_switcher_call
            ; [apply Z.eqb_eq,finz_to_z_eq in Hb0|by cbn in His_switcher_call]
            ; simplify_eq.
            destruct (e0 =? e_switcher)%a eqn:He0
            ; rewrite He0 in His_switcher_call
            ; [apply Z.eqb_eq,finz_to_z_eq in He0|by cbn in His_switcher_call]
            ; simplify_eq.
            destruct ( (a0 =? a_switcher_call)%Z || (a0 =? a_switcher_return)%Z ) eqn:Ha0
            ; [apply orb_true_iff in Ha0; rewrite !Z.eqb_eq in Ha0|by cbn in His_switcher_call].
            iDestruct (region_close with "[$Hstate $Hr Hw $Ha $HmonoV]") as "Hr"; eauto.
            { destruct ρ;auto;contradiction. }
            iClear "Hmono HmonoV Hinva Hrcond Hwcond Hwsrc Hinv_interp".
            clear dependent p b e a g p' w ρ P rsrc.
            clear Hpft.
            iNext; iIntros "_".
            destruct Ha0 as [Ha0|Ha0]; apply finz_to_z_eq in Ha0; simplify_eq; clear His_switcher_call.
            * (* We jumped to the switcher-cc-call entry point *)
              iApply (switcher_call_ftlr with "[$IH] [$] [$] [$] [$] [$] [$] [$] [$]"); eauto.
            * (* We jumped to the switcher-cc-return entry point *)
              iApply (switcher_return_ftlr with "[$IH] [$] [$] [$] [$] [$] [$] [$] [$]"); eauto.
              intros.
              apply switcher_call_ftlr.
          + (* This is just a regular Sentry, use the IH *)
            iDestruct "Hwsrc" as "#H".
            iAssert (future_world g0 W W) as "Hfuture".
            { iApply futureworld_refl. }
            iSpecialize ("H" with "Hfuture").
            iDestruct "H" as "[H _]".
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
