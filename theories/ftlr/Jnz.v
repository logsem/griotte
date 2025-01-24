From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Jnz.
From cap_machine.proofmode Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ} {sealsg: sealStoreG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma jnz_case (W : WORLD) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (rdst rsrc : RegName) (P:D):
    ftlr_instr W regs p p' g b e a w (Jnz rdst rsrc) ρ P.
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #HmonoV #Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    (* iDestruct (execCond_implies_region_conditions with "Hinv_interp") as "#Hinv"; eauto. *)
    iInsert "Hmap" PC.
    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ | wsrc regs' Hrsrc Hnz Hincr |  wsrc wdst Hrsrc Hrdst Hnz ].
    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    }

    {
      incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      map_simpl "Hmap".
      iDestruct (region_close with "[$Hstate $Hr $Ha Hw $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];try contradiction. }
      iApply ("IH" $! _ regs with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
      iApply (interp_next_PC with "IH Hinv_interp"); eauto.
    }

    map_simpl "Hmap".
    iApply wp_pure_step_later; auto.
    destruct (updatePcPerm wdst) eqn:Hwdst ; [ | destruct sb | ]; cycle 1.
    { destruct (PermFlowsTo RX p0) eqn:Hpft; cycle 1.
      { iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto; iNext; iIntros "_".
        iApply wp_value; iIntros; discriminate.
      }

      destruct_word wdst; cbn in Hwdst; try discriminate.
      assert (Heq: (if (decide (p0 = c)) then True else p0 = RX /\ c = E)
                   /\ g0 = g1 /\ b0 = b1 /\ e0 = e1 /\ a0 = a1)
        by (destruct (decide (p0 = c)); destruct c
            ; inv Hwdst; simpl in Hpft
            ; try congruence; auto; repeat split; auto
        ).
      clear Hwdst.
      destruct (decide (p0 = c));
        [subst c; destruct Heq as (_ & -> & -> & -> & ->)
        | destruct Heq as ((-> & ->) & -> & -> & -> & ->)].
      { iNext ; iIntros "_".
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }
        iApply ("IH" $! _ regs with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]") ; eauto.
        - destruct p0; simpl in Hpft; auto; try discriminate.
          destruct (decide (rdst = PC)) as [HrdstPC|HrdstPC].
          + simplify_map_eq; auto.
          + simplify_map_eq.
            iDestruct ("Hreg" $! rdst _ HrdstPC Hrdst) as "Hrdst".
            iClear "Hinv_interp".
            iEval (rewrite fixpoint_interp1_eq) in "Hrdst".
            simpl; destruct g1; auto.
        - destruct (decide (rdst = PC)) as [HrdstPC|HrdstPC].
          + simplify_map_eq; auto.
          + simplify_map_eq.
            iDestruct ("Hreg" $! rdst _ HrdstPC Hrdst) as "Hrdst"; eauto.
      }
      { assert (rdst <> PC) as HPCnrdst.
        { intro; subst rdst; simplify_map_eq. naive_solver. }
        simplify_map_eq.
        iDestruct ("Hreg" $! rdst _ HPCnrdst Hrdst) as "Hrdst".
        iEval (rewrite fixpoint_interp1_eq //=) in "Hrdst".
        iDestruct (region_close with "[Hw $Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
        { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }
        rewrite /enter_cond.
        rewrite /interp_expr /=.
        iDestruct "Hrdst" as "#H".
        iAssert (future_world g1 W W) as "Hfuture". { iApply futureworld_refl. }
        iSpecialize ("H" with "Hfuture").
        iDestruct ("H" with "[$Hmap $Hr $Hsts $Hown]") as "HA"; auto.
      }
    }

    (* Non-capability cases *)
    all: iExtract "Hmap" PC as "HPC".
    all: iNext; iIntros "_".
    all: iApply (wp_bind (fill [SeqCtx])).
    all: iApply (wp_notCorrectPC with "HPC"); [intro Hcontra ; inv Hcontra|].
    all: iNext; iIntros "HPC /=".
    all: iApply wp_pure_step_later; auto; iNext; iIntros "_".
    all: iApply wp_value; iIntros; discriminate.
  Qed.


End fundamental.
