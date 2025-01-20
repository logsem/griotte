From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_base rules_Mov.
From cap_machine.proofmode Require Import map_simpl.
From cap_machine Require Import stdpp_extra.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

   Lemma mov_case (W : WORLD) (regs : leibnizO Reg) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D):
    ftlr_instr W regs p g b e a w (Mov dst src) ρ P.
  Proof.
    intros Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iDestruct (execCond_implies_region_conditions with "Hinv_interp") as "#Hinv"; eauto.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - incrementPC_inv; simplify_map_eq.
      rename x into p'
      ; rename x0 into g'
      ; rename x1 into b'
      ; rename x2 into e'
      ; rename x3 into a'
      ; rename x4 into a''.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      destruct (decide (dst = PC)) as [HdstPC|HdstPC]; simplify_map_eq.
      { map_simpl "Hmap".
        destruct src; simpl in *; try discriminate.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g0)];contradiction. }
        destruct (decide (r = PC)).
        + simplify_map_eq.
          iApply ("IH" $! _ regs with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto.
          rewrite !fixpoint_interp1_eq /=.
          destruct Hp as [-> | [  -> | [-> ->] ] ]; rewrite /region_conditions //=.
        + simplify_map_eq.
          iDestruct ("Hreg" $! r (WCap p' g' b' e' a') n H ) as "Hr0".
          destruct (PermFlowsTo RX p') eqn:Hpft.
        - iApply ("IH" $! _ regs with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto.
          { destruct p'; simpl in Hpft; auto.
            repeat rewrite fixpoint_interp1_eq; simpl.
            destruct g'; auto.
          }
          { rewrite !fixpoint_interp1_eq /=.
            destruct p',g'; try congruence; rewrite /region_conditions //=.
          }
        - iApply (wp_bind (fill [SeqCtx])).
          iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p'; simpl in Hpft; try discriminate; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto;iNext; iIntros "_".
          iApply wp_value.
          iIntros. discriminate. }
      { map_simpl "Hmap".
        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g)];contradiction. }
        iApply ("IH" $! _ (<[dst:=w0]> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (decide (dst = x)); auto; right; split; auto.
        - iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)); simplify_map_eq.
          { (* ri = dst *)
            destruct src; simplify_map_eq.
            * repeat rewrite fixpoint_interp1_eq; auto.
            * destruct (decide (PC = r)); simplify_map_eq.
              ** rewrite (fixpoint_interp1_eq _ (WCap p' g' b' e' a')) /=.
                 destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; subst p'; try subst g';
                   try (iFrame "Hexec"); try (iFrame "Hinv").
                 all: iApply (big_sepL_mono with "Hinv").
                 all: intros; iIntros "(H & ?)".
                 all: simpl; try (iDestruct "H" as (P') "(?&?&?)").
                 iExists _; iFrame.
                 iExists RWLX; iFrame; iPureIntro ; done.
              ** iApply ("Hreg" $! r) ; auto.
          }
          { iApply ("Hreg" $! ri) ; auto. }
        -rewrite !fixpoint_interp1_eq /=.
         destruct Hp as [-> | [  -> | [-> ->] ] ]; rewrite /region_conditions //=.
      }
  Qed.

End fundamental.
