From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import rules_base rules_Seal.
From cap_machine.proofmode Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {heapg : heapGS Σ}
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

  (* Proving the meaning of sealing in the LR sane *)
  (* Lemma sealing_preserves_interp W C sb p0 g0 b0 e0 a0 wso: *)
  (*       permit_seal p0 = true → *)
  (*       withinBounds b0 e0 a0 = true → *)
  (*       sts_seals_std C a0 wso -∗ *)
  (*       interp W C (WSealable sb) -∗ *)
  (*       interp W C (borrow (WSealable sb)) -∗ *)
  (*       interp W C (WSealRange p0 g0 b0 e0 a0) -∗ *)
  (*       interp W C (WSealed a0 sb). *)
  (* Proof. *)
  (*   iIntros (Hpseal Hwb) "#Hws #HVsb #HVsb_borrowed #HVsr". *)
  (*   rewrite *)
  (*     (fixpoint_interp1_eq W C (WSealRange _ _ _ _ _)) *)
  (*     (fixpoint_interp1_eq W C (WSealed _ _)) /= Hpseal /interp_sb. *)
  (*   iDestruct "HVsr" as "[Hss _]". *)
  (*   apply seq_between_dist_Some in Hwb. *)
  (*   iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto. *)
  (*   iDestruct "HSa0" as (P) "(% & HsealP & HWcond)". *)
  (*   iExists P. *)
  (*   repeat iSplitR; auto; by iApply "HWcond". *)
  (* Qed. *)

  Lemma seal_case (W : WORLD)(C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst r1 r2 : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Seal dst r1 r2) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hseals Hown Htframe".
    iIntros "Hr Hstate Ha HPC Hmap".
    iInsert "Hmap" PC.
    iApply (wp_Seal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Hseal Hwb HincrPC | ]; cycle 1.
    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    }

    - apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .
      assert (p'' = p ∧ g'' = g ∧ a'' = a ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }
      assert (r1 ≠ PC) as Hne.
      { destruct (decide (PC = r1)); last auto. simplify_map_eq; auto. }
      assert (r1 ≠ cnull); simplify_map_eq.
      { intros ->; destruct (regs !! cnull) eqn:Hr ; simplify_map_eq. }
      assert (r2 ≠ cnull); simplify_map_eq.
      { intros ->; destruct (regs !! cnull) eqn:Hr ; simplify_map_eq. }

      iAssert (interp W C (WSealable sb)) as "#HVsb".
      { destruct (decide (r2 = PC)) as [Heq|Heq]; simplify_map_eq; first done.
        unshelve iSpecialize ("Hreg" $! r2 _ _ Hr2); eauto.
      }
      iAssert (interp W C (borrow (WSealable sb))) as "#HVsb_borrowed".
      { by iApply interp_borrow_word. }

      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;contradiction. }

      assert (is_Some (<[dst:=WSealed a0 sb]> (<[PC:=WCap p g b e a]> regs) !! csp)) as [??].
      { destruct (decide (dst = csp)); simplify_map_eq=>//. }

      assert ( ∃ ws,  (seal_std W) !! a0 = Some ws ) as [ws Hws].
      { admit. (* Logrel safe to seal / safe to unseal *) }
      set ( W' := <o[ a0 := ({[WSealable sb; borrow (WSealable sb)]} ∪ ws) ]o> W ).
      assert (related_sts_pub_world W W') as Hrelated.
      { admit. }
      iDestruct (region_monotone _ _ W' with "Hr") as "Hr"; auto.

      unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
      iDestruct (monotone.interp_monotone with "[%] [$HVsr]") as "HVsr'"; eauto.
      iClear "HVsr".
      rewrite (fixpoint_interp1_eq W' C (WSealRange _ _ _ _ _)).
      iDestruct "HVsr'" as "[Hss _]".
      rewrite Hseal.
      apply seq_between_dist_Some in Hwb.
      iDestruct (big_sepL_elem_of_acc with "Hss") as "[HSa0 Hss']"; eauto.
      { rewrite list_elem_of_lookup; eauto. }
      iDestruct "HSa0" as "(%Po & %HPo_pers & Hsealpred & #Hwcond_Po)".

      iAssert ([∗ set] w0 ∈ {[WSealable sb; borrow (WSealable sb)]}, ▷ (safeC Po) (W', C, w0))%I as "Hws".
      {
        iAssert (▷ (Po W' C (WSealable sb)))%I as "HPo_sb".
        { iNext; iApply "Hwcond_Po".
          iApply (monotone.interp_monotone with "[%] [$HVsb]"); eauto.
        }
        iAssert (▷ (Po W' C (WSealable (borrow_sb sb))))%I as "HPo_sb_borrowed".
        { iNext; iApply "Hwcond_Po".
          iApply (monotone.interp_monotone with "[%] [$HVsb_borrowed]"); eauto.
        }

        destruct (decide (WSealable sb = borrow (WSealable sb))) as [Heq_sb|Heq_sb].
        - rewrite -Heq_sb.
          replace {[WSealable sb; WSealable sb]} with ({[WSealable sb]} : gset Word) by set_solver+.
          rewrite big_sepS_singleton.
          by rewrite /safeC /=.
        - rewrite big_sepS_insert; last set_solver.
          rewrite big_sepS_singleton.
          rewrite /safeC /=.
          iSplitL; done.
      }
      iDestruct (sealing_map_update with "[$Hws] [$Hseals]") as "Hseals"; eauto.

      Set Nested Proofs Allowed.



      (*   admit. (* sealing_map + Ho *) *)
      (* iAssert (∃ ws, sts_seals_std C a0 ws)%I as "[%wso #Hws]". *)
      (* { *)
      (* } *)

      iApply ("IH" $! _ _ _ _ _ (<[dst := _]> (<[PC := _]> regs))
               with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hseals] [$Hcont] [//] [$Hown] [$Htframe]")
      ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
        { unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
          destruct (decide (dst = cnull)) ; first iApply interp_int.
          iApply (sealing_preserves_interp with "[HVsb HVsr]"); eauto.
        }
        { by iApply "Hreg". }
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
