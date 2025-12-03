From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import rules_base rules_UnSeal.
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
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* Proving the meaning of unsealing in the LR sane. Note the use of the later in the result. *)
  Lemma unsealing_preserves_interp W C sb p0 g0 b0 e0 a0:
        permit_unseal p0 = true →
        withinBounds b0 e0 a0 = true →
        interp W C (WSealed a0 sb) -∗
        interp W C (WSealRange p0 g0 b0 e0 a0) -∗
        ▷ interp W C (WSealable sb).
  Proof.
    iIntros (Hpseal Hwb) "#HVsd #HVsr".
    rewrite
      (fixpoint_interp1_eq W C (WSealRange _ _ _ _ _))
      (fixpoint_interp1_eq W C (WSealed _ _)) /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[_ Hss]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "( #Hmono & HsealP & HWcond)".
    iDestruct "HVsd" as (P') "(% & #Hmono' & HsealP' & HP' & HPborrowed')".
    iDestruct (seal_pred_agree with "HsealP HsealP'") as "Hequiv".
    iSpecialize ("Hequiv" $! (W,C,(WSealable sb))).
    rewrite /safeC /=.
    iAssert (▷ P W C (WSealable sb))%I as "HP". { iNext; by iRewrite "Hequiv". }
    by iApply "HWcond".
  Qed.

  Lemma unseal_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst r1 r2 : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (wstk : Word) :
    ftlr_instr W C regs p p' g b e a w (UnSeal dst r1 r2) ρ P cstk Ws Cs wstk.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hown Htframe".
    iIntros "Hr Hstate Ha HPC Hmap %Hsp".
    iInsert "Hmap" PC.
    iApply (wp_UnSeal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Hunseal Hwb HincrPC | ]; cycle 1.
    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    }

    apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .

    assert (r1 ≠ PC) as Hne1.
    { destruct (decide (PC = r1)); last auto. simplify_map_eq; auto. }
    rewrite lookup_insert_ne in Hr1; auto.
    assert (r2 ≠ PC) as Hne2.
    { destruct (decide (PC = r2)); last auto. simplify_map_eq; auto. }
    rewrite lookup_insert_ne in Hr2; auto.

    unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
    unshelve iDestruct ("Hreg" $! r2 _ _ Hr2) as "HVsd"; eauto.
    (* Generate interp instance before step, so we get rid of the later *)
    iDestruct (unsealing_preserves_interp with "HVsd HVsr") as "HVsb"; auto.

    iApply wp_pure_step_later; auto; iNext; iIntros "_".
    iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
    { destruct ρ;auto;contradiction. }

    destruct (decide (PC = dst)) as [Heq | Hne]; cycle 1.
    { (* PC ≠ dst *)
      simplify_map_eq; map_simpl "Hmap".
      assert (is_Some (<[dst:=WSealable sb]> regs !! csp)) as [??].
      { destruct (decide (dst = csp));simplify_map_eq=>//. }
      iApply ("IH" $! _ _ _ _ _ (<[dst:=WSealable sb]> regs)
               with "[%] [] [Hmap] [%] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]")
      ; eauto.
      + cbn; intros. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert in Hvs;
            inversion Hvs.
          auto.
        }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto.
        }
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { (* PC = dst *)
      simplify_map_eq; map_simpl "Hmap".
      destruct (executeAllowed p'') eqn:Hpft.
      - iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [Hmap] [//] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]")
        ; eauto.
        iApply (interp_weakening with "IH HVsb"); eauto; try solve_addr; try done.
      - (* not executable *)
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC with "HPC")
        ; [eapply not_isCorrectPC_perm;  simpl in Hp; try discriminate; eauto|].
        iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto;iNext; iIntros "_".
        iApply wp_value;auto.
    }
    Qed.

End fundamental.
