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
  Lemma sealing_preserves_interp W C sb p g b e a :
    permit_seal p = true ->
    withinBounds b e a = true ->
    interp W C (WSealable sb) -∗
    interp W C (WSealRange p g b e a) -∗
    sts_full_world W C -∗
    sealing_map W C -∗
    region W C
    ==∗
    ∃ W', ⌜ related_sts_pub_world W W' ⌝ ∗
          sts_full_world W' C ∗
          sealing_map W' C ∗
          region W' C ∗
          interp W' C (WSealed a sb).
  Proof.
    iIntros (Hseal Hwb) "#HVsb #HVsr Hsts Hseals Hr".
    rewrite (fixpoint_interp1_eq W C (WSealRange _ _ _ _ _)).
    iDestruct "HVsr" as "[Hss _]"; rewrite Hseal.
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_elem_of_acc with "Hss") as "[HSa0 _]"; eauto.
    { rewrite list_elem_of_lookup; eauto. }
    iDestruct "HSa0" as "(%Po & %HPo_pers & Hsealpred & %Ha0_in_Wseals & #Hwcond_Po)".
    rewrite elem_of_dom in Ha0_in_Wseals; destruct Ha0_in_Wseals as [ws Hws].
    set (new_seals_words := ({[WSealable sb; borrow (WSealable sb)]} : gset Word)).
    set ( W' := <o[ a := ( new_seals_words ∪ ws) ]o> W ).
    assert (related_sts_pub_world W W') as Hrelated.
    { by apply related_sts_pub_world_update_ot. }
    iAssert ([∗ set] w0 ∈ normalise_sealed_words new_seals_words, ▷ (safeC Po) (W', C, w0))%I as "Hws".
    {
      subst new_seals_words.
      rewrite normalise_sealed_words_union !normalise_sealed_words_singleton; cbn.
      rewrite force_global_borrow_sb.
      replace ( {[WSealable (force_global_sb sb); WSealable (force_global_sb sb)]} ) with
        ({[WSealable (force_global_sb sb)]} : gset Word) by set_solver+.
      rewrite big_sepS_singleton -/(force_global (WSealable sb)).
      iNext; iApply "Hwcond_Po".
      iApply (monotone.interp_monotone with "[%] [$HVsb]"); eauto.
    }
    iMod (sealing_map_update with "[$Hsealpred] [$Hws] [$Hseals $Hsts]") as "(Hseals & Hsts & #Hstd_seals)"; eauto.
    iDestruct (region_monotone _ _ W' with "Hr") as "Hr"; auto.
    subst W'.
    iModIntro.
    iExists _; iFrame "∗%".
    iEval (rewrite fixpoint_interp1_eq /= /interp_sb).
    iApply sts_seals_std_weaken; last iFrame "#".
    set_solver+.
  Qed.

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

      (* TODO can I extract a lemma from here? *)
      unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
      iMod (sealing_preserves_interp with "HVsb HVsr Hsts Hseals Hr") as
        "(%W' & %Hrelated & Hsts & Hseals & Hr & #HVsb')"; auto.
      eapply frame_match_mono in Hframe; eauto.
      iApply ("IH" $! _ _ _ _ _ (<[dst := _]> (<[PC := _]> regs))
               with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hseals] [$Hcont] [//] [$Hown] [$Htframe]")
      ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
        {
          destruct (decide (dst = cnull)) ; last done.
          iApply interp_int.
        }
        {
          iApply (monotone.interp_monotone with "[] []"); eauto.
          by iApply "Hreg".
        }
      + iApply (monotone.interp_monotone with "[] []"); eauto.
        iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
