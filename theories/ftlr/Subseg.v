From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine Require Import addr_reg region map_simpl.
From cap_machine.rules Require Import rules_base rules_Subseg.
From cap_machine.proofmode Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {cstackg : CSTACKG Σ}
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

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma subseg_interp_preserved W C p g b b' e e' a :
      (b <= b')%a ->
      (e' <= e)%a ->
      ftlr_IH -∗
      interp W C (WCap p g b e a) -∗
      interp W C (WCap p g b' e' a).
  Proof.
    intros Hb He. iIntros "#IH Hinterp".
    iApply (interp_weakening with "IH Hinterp"); eauto.
    - destruct p; reflexivity.
    - destruct g; reflexivity.
  Qed.

   Lemma subseg_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
     (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
     (ρ : region_type) (dst : RegName) (r1 r2 : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (wstk : Word)
     (Nswitcher : namespace) :
    ftlr_instr W C regs p p' g b e a w (Subseg dst r1 r2) ρ P cstk Ws Cs wstk Nswitcher.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hown Htframe".
    iIntros "Hr Hstate Ha HPC Hmap %Hsp #Hswitcher".
    iInsert "Hmap" PC.
    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    assert (∀ wdst, is_Some (<[dst := wdst]> regs !! csp)) as Hspdst.
    { intros. destruct (decide (dst = csp));simplify_map_eq=>//. }
    destruct HSpec as [ * Hdst Hao1 Hao2 Hwi HincrPC | * Hdst Hoo1 Hoo2 Hwi HincrPC | ]
                        ; cycle 2.
    { iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. }
    { apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (a'' = a ∧ p'' = p∧ g'' = g) as (-> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iNext ; iIntros "_".
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;contradiction. }
      simplify_map_eq; map_simpl "Hmap".
      
      edestruct Hspdst as [??].
      iApply ("IH" $! _ _ _ _ _ (<[dst:=_]> _) with "[%] [] [Hmap] [] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
      { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert_ne in Hdst; auto; simplify_map_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          rewrite /isWithin in Hwi.
          iApply (interp_weakening with "IH Hreg"); auto; try solve_addr.
          - apply PermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto.
          by rewrite lookup_insert_ne in Hvs; auto; simplify_map_eq.
        }
      }
      {
        iModIntro.
        apply isWithin_implies in Hwi.
        destruct Hwi as [Hwi_b Hwi_e].
        destruct (decide (dst = PC))
        ; simplify_map_eq
        ; [iApply subseg_interp_preserved; eauto|]
        ; iApply (interp_next_PC with "Hinv_interp"); eauto.
      }
    }

    { apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .

      assert (a'' = a ∧ p'' = p∧ g'' = g) as (-> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto.
      iNext ; iIntros "_".
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;contradiction. }
      simplify_map_eq; map_simpl "Hmap".

      edestruct Hspdst as [??].
      iApply ("IH" $! _ _ _ _ _ (<[dst:=_]> _) with "[%] [] [Hmap] [%] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
      { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
      { iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert_ne in Hdst; auto; simplify_map_eq.

          unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          rewrite /isWithin in Hwi.
          iApply (interp_weakening_ot with "Hreg"); auto; try solve_addr.
          - apply SealPermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto.
          by rewrite lookup_insert_ne in Hvs; auto; simplify_map_eq.
        }
      }
      {
        iModIntro.
        apply isWithin_implies in Hwi.
        destruct Hwi as [Hwi_b Hwi_e].
        destruct (decide (dst = PC)) ; simplify_map_eq.
        iApply (interp_next_PC with "Hinv_interp"); eauto.
      }
    }
  Qed.

End fundamental.
