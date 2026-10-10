From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Store rules_Store_binary.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types interp : (V).

  Lemma allow_store_map_or_true_intro (regs : Reg) (r1 : RegName) (r2 : Z + RegName)
    (storev : Word) (mem : gmap Addr Word) :
    is_Some (regs !! r1) →
    word_of_argument regs r2 = Some storev →
    (∀ p g b e a, reg_allows_store regs r1 p g b e a storev → is_Some (mem !! a)) →
    allow_store_map_or_true r1 r2 regs mem.
  Proof.
    intros [wdst Hdst] Hstorev Hmem.
    rewrite /allow_store_map_or_true /read_reg_inr Hdst.
    destruct wdst as [ | [p g b e a|] | | ].
    2: exists p, g, b, e, a, storev.
    1,3-5: exists RO, Global, za, za, za, storev.
    all: split; first done.
    all: split; first done.
    all: case_decide as Hallow; [by apply Hmem in Hallow | done].
  Qed.

  Lemma lookup_reg_cap (regs : Reg) (r : RegName) p g b e a :
    regs !!ᵣ r = Some (WCap p g b e a) → regs !! r = Some (WCap p g b e a).
  Proof.
    rewrite /lookup_reg.
    destruct (regs !! r); cbn; last done.
    case_decide; by intros; simplify_eq.
  Qed.

  (** Storing a pair of related words through [p0] preserves the monotonicity
      requirements of the target address. *)
  Lemma monoReq_mono_invariant W C a p0 p' (P : V) (w1 w2 : Word) ρ :
    std W !! a = Some ρ →
    ρ ≠ Revoked →
    PermFlowsTo p0 p' →
    canStore p0 w1 = true →
    canStore p0 w2 = true →
    monoReq W C a p' P -∗
    mono_invariant C p' (safeC P) (w1, w2) ρ.
  Proof.
    iIntros (Hρ Hne Hfl Hcs1 Hcs2) "Hmono".
    rewrite /monoReq Hρ mono_invariant_eq.
    destruct ρ;[simpl..|exfalso;done].
    - destruct (isWL p');auto.
      destruct (isDL p'); first done.
      iSpecialize ("Hmono" $! (w1, w2) with "[%]"); last done.
      split; eapply canStore_flowsto; eauto.
    - iSpecialize ("Hmono" $! (w1, w2) with "[%]"); last done.
      split; eapply canStore_flowsto; eauto.
  Qed.

  Lemma store_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
    (ρ : region_type) (dst : RegName) (src : Z + RegName) (P : V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Store dst src) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc_forall with "WorldRes") as "[ (>Ha & >Hsa & Hinterp & HmonoV) WorldRes ]".
    cbn [fst snd].
    iClear "Hrcond".

    (* The destination register and the stored word *)
    assert (is_Some (<[PC:=WCap p g b e a]> regs1 !!ᵣ dst)) as [wdst Hwdst].
    { apply is_Some_lookup_reg, lookup_insert_is_Some'; eauto. }
    assert (∃ storev, word_of_argument (<[PC:=WCap p g b e a]> regs1) src = Some storev)
      as [storev1 Hwoa].
    { destruct src as [z|r]; cbn; first by eauto.
      apply is_Some_lookup_reg, lookup_insert_is_Some'; eauto. }
    assert ((∃ p0 g0 b0 e0 a0, wdst = WCap p0 g0 b0 e0 a0 ∧ writeAllowed p0 = true
                               ∧ withinBounds b0 e0 a0 = true ∧ canStore p0 storev1 = true)
            ∨ (∀ p0 g0 b0 e0 a0,
                  ¬ reg_allows_store (<[PC:=WCap p g b e a]> regs1) dst p0 g0 b0 e0 a0 storev1))
      as [(p0 & g0 & b0 & e0 & a0 & -> & Hwa & Hwb & Hcs) | Hnallow].
    { destruct wdst as [ | [p0 g0 b0 e0 a0|] | | ].
      2: destruct (writeAllowed p0) eqn:Hwa; destruct (withinBounds b0 e0 a0) eqn:Hwb;
         destruct (canStore p0 storev1) eqn:Hcs.
      2: left; eauto 10.
      all: right; intros ????? (Hr & Hwa' & Hwb' & Hcs'); simplify_eq; congruence. }
    2: { (* The store fails in the implementation run *)
      iApply (wp_store _ _ _ _ _ _ dst src w (<[a:=w]> ∅) (<[PC:=WCap p g b e a]> regs1)
               with "[Hmap Ha]"); eauto.
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { eapply allow_store_map_or_true_intro; eauto.
        - apply lookup_insert_is_Some'; eauto.
        - intros * Hallow; by apply Hnallow in Hallow. }
      { iSplitL "Ha"; iNext; [by iApply memMap_resource_1 | done]. }
      iNext. iIntros (regs' mem' retv) "(%HSpec & Hmem & Hmap)".
      destruct HSpec as [p1 g1 b1 e1 a1 storev oldv Hwoa' Hallow | ].
      { rewrite Hwoa in Hwoa'; simplify_eq. by apply Hnallow in Hallow. }
      ftlr_impl_fail.
    }

    (* The destination register holds the same capability in both runs,
       the stored words are related *)
    iDestruct (interp_reg_lookup_same with "Hinv_interp Hreg") as %Hwdst2; [exact Hwdst|done|].
    iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "#Hvdst"; [exact Hwdst|exact Hwdst2|].
    iDestruct (interp_reg_word_of_argument_Some _ _ _ _ (WCap p g b e a) src with "Hreg")
      as %[storev2 Hwoa2].
    iDestruct (interp_word_of_argument with "Hinv_interp Hreg") as "#Hvstore"; [exact Hwoa|exact Hwoa2|].
    iDestruct (interp_canStore _ _ p0 with "Hvstore") as %Hcs_eq.
    apply withinBounds_le_addr in Hwb as Hwb'.
    iDestruct (write_allowed_inv _ _ a0 with "Hvdst")
      as (pS PS HflpS HpersS) "(HrelS & HzcondS & HwcondS & HrcondS & HmonoS)"
    ; [solve_addr|by rewrite Hwa|].
    assert (∀ Wv : WORLD * CmptName * (Word * Word), Persistent (PS Wv.1.1 Wv.1.2 Wv.2))
      as HpersS' by apply HpersS.
    destruct (decide (a0 = a)) as [-> | Hne].
    - (* The destination capability points to the instruction *)
      iDestruct (rel_agree C a _ _ p' pS with "[$Hinva $HrelS]") as "[<- _]".
      iAssert (▷ wcond P C interp)%I as "#HwcondP".
      { rewrite decide_True; first done.
        exists dst, (WCap p0 g0 b0 e0 a); split; first by apply lookup_reg_cap.
        split; first done. cbn; split; [solve_addr|done]. }
      iApply (wp_store _ _ _ _ _ _ dst src w (<[a:=w]> ∅) (<[PC:=WCap p g b e a]> regs1)
               with "[Hmap Ha]"); eauto.
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { eapply allow_store_map_or_true_intro; eauto.
        - apply lookup_insert_is_Some'; eauto.
        - intros * (Hr & _); rewrite Hwdst in Hr; simplify_eq; by simplify_map_eq. }
      { iSplitL "Ha"; iNext; [by iApply memMap_resource_1 | done]. }
      iNext. iIntros (regs' mem' retv) "(%HSpec & Hmem & Hmap)".
      destruct HSpec as [p1 g1 b1 e1 a1 storev oldv Hwoa' Hallow Hmem_a -> HincrPC | ]; cycle 1.
      { ftlr_impl_fail. }
      rewrite Hwoa in Hwoa'; injection Hwoa' as <-.
      destruct Hallow as (Hr1 & _ & _); rewrite Hwdst in Hr1; injection Hr1 as <- <- <- <- <-.
      rewrite lookup_insert_eq in Hmem_a; injection Hmem_a as <-.

      iMod (step_store _ _ _ _ _ _ dst src w (<[a:=w]> ∅) (<[PC:=WCap p g b e a]> regs2)
             with "[$Hspec $Hj Hsa $Hsmap]") as (retv2 regs2' mem2') "(Hj & %HSpec2 & Hsmem & Hsmap)".
      { solve_ndisj. }
      { done. }
      { done. }
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { eapply allow_store_map_or_true_intro; eauto.
        - apply lookup_insert_is_Some'; eauto.
        - intros * (Hr & _); rewrite Hwdst2 in Hr; simplify_eq; by simplify_map_eq. }
      { by iApply spec_memMap_resource_1. }
      apply incrementPC_Some_inv in HincrPC as (p2&g2&b2&e2&a2&a3&HPC&Ha2&->).
      eapply Store_spec_determ_arg in HSpec2 as [Hv2 Hregs2];
        last (eapply Store_spec_success;
              [ exact Hwoa2 | split; [exact Hwdst2| split; [done | split; [done| by rewrite -Hcs_eq ] ] ]
              | by simplify_map_eq | reflexivity | transfer_incrementPC HPC Ha2]).
      destruct (Hregs2 eq_refl); subst retv2 regs2' mem2'.
      rewrite !insert_insert_eq.
      iDestruct (memMap_resource_1 with "Hmem") as "Ha".
      iDestruct (spec_memMap_resource_1 with "Hsmem") as "Hsa".
      iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      (* The stored words satisfy the predicate of the address *)
      iAssert (P W C (storev1, storev2)) as "HPstore".
      { iApply ("HwcondP" $! W (storev1, storev2) with "Hvstore"). }
      iDestruct (monoReq_mono_invariant _ _ _ p0 _ _ storev1 storev2 with "Hmono") as "Hmono'"; [eauto|eauto|eauto|eauto|by rewrite -Hcs_eq|].
      iDestruct ("WorldRes" $! (storev1, storev2) with "[$Ha $Hsa $HPstore $Hmono']") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }
      simplify_map_eq.
      iApply ("IH" $! _ _ _ _ _ regs1 regs2
               with "Hspec Hreg Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
      iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.

    - (* The destination capability points to another address: open the world there *)
      iDestruct (writeAllowed_valid_cap_implies _ _ _ _ _ _ a0 with "Hvdst")
        as %(ρ0 & Hstd0 & Hnotrevoked0); eauto.
      iDestruct (open_world_interp_next _ _ _ a0 pS _ ρ0 with "HrelS Hworld_interp")
        as "(Hworld_interp & Hstate0 & HWorldRes0)"; eauto.
      { set_solver. }
      { destruct ρ0; simplify_eq; try done; [by left | by right]. }
      iDestruct "HWorldRes0" as (v) "(>%HpOS & >Ha0 & >Hsa0 & _ & _)".
      iApply (wp_store _ _ _ _ _ _ dst src w (<[a0:=v.1]> (<[a:=w]> ∅)) (<[PC:=WCap p g b e a]> regs1)
               with "[Hmap Ha Ha0]"); eauto.
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { eapply allow_store_map_or_true_intro; eauto.
        - apply lookup_insert_is_Some'; eauto.
        - intros * (Hr & _); rewrite Hwdst in Hr; simplify_eq; by simplify_map_eq. }
      { iSplitL "Ha Ha0"; iNext; [ rewrite memMap_resource_2ne //; iFrame | done]. }
      iNext. iIntros (regs' mem' retv) "(%HSpec & Hmem & Hmap)".
      destruct HSpec as [p1 g1 b1 e1 a1 storev oldv Hwoa' Hallow Hmem_a -> HincrPC | ]; cycle 1.
      { ftlr_impl_fail. }
      rewrite Hwoa in Hwoa'; injection Hwoa' as <-.
      destruct Hallow as (Hr1 & _ & _); rewrite Hwdst in Hr1; injection Hr1 as <- <- <- <- <-.
      rewrite lookup_insert_eq in Hmem_a; injection Hmem_a as <-.

      iMod (step_store _ _ _ _ _ _ dst src w (<[a0:=v.2]> (<[a:=w]> ∅)) (<[PC:=WCap p g b e a]> regs2)
             with "[$Hspec $Hj Hsa Hsa0 $Hsmap]") as (retv2 regs2' mem2') "(Hj & %HSpec2 & Hsmem & Hsmap)".
      { solve_ndisj. }
      { done. }
      { done. }
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { eapply allow_store_map_or_true_intro; eauto.
        - apply lookup_insert_is_Some'; eauto.
        - intros * (Hr & _); rewrite Hwdst2 in Hr; simplify_eq; by simplify_map_eq. }
      { rewrite spec_memMap_resource_2ne //; iFrame. }
      apply incrementPC_Some_inv in HincrPC as (p2&g2&b2&e2&a2&a3&HPC&Ha2&->).
      eapply Store_spec_determ_arg in HSpec2 as [Hv2 Hregs2];
        last (eapply Store_spec_success;
              [ exact Hwoa2 | split; [exact Hwdst2| split; [done | split; [done| by rewrite -Hcs_eq ] ] ]
              | by simplify_map_eq | reflexivity | transfer_incrementPC HPC Ha2]).
      destruct (Hregs2 eq_refl); subst retv2 regs2' mem2'.
      rewrite !insert_insert_eq.
      iDestruct (memMap_resource_2ne with "Hmem") as "[Ha0 Ha]"; first done.
      iDestruct (spec_memMap_resource_2ne with "Hsmem") as "[Hsa0 Hsa]"; first done.
      iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      (* The stored words satisfy the predicate of the destination address *)
      iAssert (PS W C (storev1, storev2)) as "HPstore".
      { by iApply "HwcondS". }
      iDestruct (monoReq_mono_invariant _ _ _ p0 _ _ storev1 storev2 with "HmonoS") as "HmonoS'"; [eauto|eauto|eauto|eauto|by rewrite -Hcs_eq|].
      iDestruct (close_world_interp_next _ _ _ a0 pS _ (storev1, storev2) ρ0
                  with "Hworld_interp Hstate0 HrelS [Ha0 Hsa0]") as "Hworld_interp"; eauto.
      { set_solver. }
      { destruct ρ0; simplify_eq; try done; [by left | by right]. }
      { iFrame "∗#%". }
      iDestruct ("WorldRes" $! (w, w) with "[$Ha $Hsa $Hinterp $HmonoV]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }
      simplify_map_eq.
      iApply ("IH" $! _ _ _ _ _ regs1 regs2
               with "Hspec Hreg Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
      iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
