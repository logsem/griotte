From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import rules_Mov.
From cap_machine.proofmode Require Import map_simpl register_tactics.
Import uPred.

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

   Lemma mov_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
     (p p' : Perm) (g : Locality) (b e a : Addr)
     (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Mov dst src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hown Htframe".
    iIntros "Hr Hstate Ha HPC Hmap".
    iInsert "Hmap" PC.
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    - incrementPC_inv; simplify_map_eq.
      rename x into p0
      ; rename x0 into g0
      ; rename x1 into b0
      ; rename x2 into e0
      ; rename x3 into a0
      ; rename x4 into a0'.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      destruct (decide (dst = PC)) as [HdstPC|HdstPC]; simplify_map_eq.
      { map_simpl "Hmap".
        destruct src; simpl in *; try discriminate.
        iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
        { destruct ρ;auto;contradiction. }
        destruct (decide (r = PC)).
        { simplify_map_eq.
          iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
          iApply (interp_next_PC with "Hinv_interp"); eauto.
        }
        simplify_map_eq.
        assert (r ≠ cnull); simplify_map_eq.
        { intros ->; simplify_map_eq.
          destruct (regs !! cnull) eqn:Heq; rewrite Heq in H; cbn in *; try done. }
        iDestruct ("Hreg" $! r (WCap p0 g0 b0 e0 a0) n H ) as "Hr0".
        destruct (executeAllowed p0) eqn:Hpft; cycle 1.
        { iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value;auto.
        }

        iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        iApply (interp_weakening with "IH Hr0"); eauto; try reflexivity; try solve_addr.
      }
      { map_simpl "Hmap".
        iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
        { destruct ρ;auto;contradiction. }
        assert (is_Some (<[dst:=w0]> regs !! csp)) as [??].
        { destruct (decide (dst = csp));simplify_map_eq =>//. }
        iApply ("IH" $! _ _ _ _ _ (<[dst:=w0]ᵣ> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        - intros; simpl.
          rewrite lookup_insert_is_Some.
          destruct (decide (dst = x0)); auto; right; split; auto.
          destruct (decide (PC = x0)); auto; simplify_map_eq; done. 
        - iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)); simplify_map_eq.
          + (* ri = dst *)
            destruct (decide (dst = cnull)); [iApply interp_int|].
            destruct src; simplify_map_eq.
            * repeat rewrite fixpoint_interp1_eq; auto.
            * destruct (decide (PC = r)); simplify_map_eq; first done.
              destruct (decide (cnull = r)); simplify_map_eq.
              { destruct (regs !! cnull) eqn:Hr; simplify_map_eq; iApply interp_int. }
              iApply ("Hreg" $! r) ; auto.
          + iApply ("Hreg" $! ri) ; auto.
      - iApply (interp_next_PC with "[Hinv_interp]"); eauto.
      }
  Qed.

End fundamental.
