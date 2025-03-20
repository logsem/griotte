From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine Require Import addr_reg region map_simpl.
From cap_machine.rules Require Import rules_base rules_Restrict.
From cap_machine.proofmode Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma PermPairFlows_interp_preserved W C p p' g g' b e a :
    PermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    ftlr_IH -∗
    interp W C (WCap p g b e a) -∗
    interp W C (WCap p' g' b e a).
  Proof.
    intros Hp Hg. iIntros "#IH HA".
    iApply (interp_weakening with "IH HA");eauto;try solve_addr.
  Qed.

  Lemma SealPermPairFlows_interp_preserved W C p p' g g' b e a :
    SealPermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    ftlr_IH -∗
    interp W C (WSealRange p g b e a) -∗
    interp W C (WSealRange p' g' b e a).
  Proof.
    intros Hp Hg. iIntros "#IH HA".
    iApply (interp_weakening_ot with "HA");eauto;try solve_addr.
  Qed.

  Lemma restrict_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D):
    ftlr_instr W C regs p p' g b e a w (Restrict dst src) ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iInsert "Hmap" PC.
    iApply (wp_Restrict with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst Hz Hpair HPfl HLfl HincrPC
                      | * Hdst Hz Hpair HPfl HLfl  HincrPC
                      | ]
    ; cycle 2.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    - apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      assert (HPCsrc: match src with inl _ => True | inr src => PC <> src end).
      { destruct src; auto.
        intro; subst r. simplify_map_eq. }

      destruct (decide (PC=dst)) as [HdstPC|HdstPC].
      { subst dst.
        repeat rewrite insert_insert in HPC.
        rewrite lookup_insert in HPC. inv HPC.
        iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }
        destruct (executeAllowed p'') eqn:Hpft.
        {
          simplify_map_eq ; map_simpl "Hmap".
          iApply ("IH" $! _ _ regs with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
          iModIntro.
          iApply (PermPairFlows_interp_preserved); eauto.
          iApply (interp_next_PC with "Hinv_interp"); eauto.
        }
        { iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; simpl in Hpft; eauto; discriminate|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto. iNext ; iIntros "_".
          iApply wp_value;auto. }
      }
      {
        simplify_map_eq.
        iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotfrozen g)];contradiction. }
        iApply ("IH" $! _ _ (<[dst:=_]> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
        - intros; simpl. repeat (rewrite lookup_insert_is_Some'; right); eauto.
        - iIntros (ri v Hri Hvs).
          destruct (decide (ri = dst)).
          + subst ri. simplify_map_eq.
            destruct (decodePermPair n) as (p1 & g1); simplify_eq.
            iDestruct ("Hreg" $! dst _ Hri Hdst) as "Hdst".
            iApply PermPairFlows_interp_preserved; eauto.
          + simplify_map_eq. iApply "Hreg"; auto.
        - iApply (interp_next_PC with "Hinv_interp"); eauto.
      }
    - apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      assert (HPCsrc: match src with inl _ => True | inr src => PC <> src end).
      { destruct src; auto.
        intro; subst r. simplify_map_eq. }

      destruct (decide (PC=dst)) as [HdstPC|HdstPC].
      { subst dst. repeat rewrite insert_insert.
        repeat rewrite insert_insert in HPC.
        rewrite lookup_insert in HPC. inv HPC.
      }

      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }
      simplify_map_eq; map_simpl "Hmap".
      iApply ("IH" $! _ _ (<[dst:=WSealRange p'0 g' b0 e0 a0]> regs) with
               "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
      + intros. by rewrite lookup_insert_is_Some' ; right.
      + iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        * subst ri. simplify_map_eq.
          destruct (decodeSealPermPair n) as (p1 & g1); simplify_eq.
          iDestruct ("Hreg" $! dst _ Hri Hdst) as "Hdst".
          iApply SealPermPairFlows_interp_preserved; eauto.
        * simplify_map_eq. iApply "Hreg"; auto.
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
