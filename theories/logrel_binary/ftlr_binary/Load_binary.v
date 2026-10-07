From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Load rules_Load_binary.
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

  Lemma allow_load_map_or_true_intro (regs : Reg) (src : RegName) (mem : gmap Addr Word) :
    is_Some (regs !! src) →
    (∀ p g b e a, reg_allows_load regs src p g b e a → is_Some (mem !! a)) →
    allow_load_map_or_true src regs mem.
  Proof.
    intros [wsrc Hsrc] Hmem.
    rewrite /allow_load_map_or_true /read_reg_inr Hsrc.
    destruct wsrc as [ | [p g b e a|] | | ].
    2: exists p, g, b, e, a.
    1,3-5: exists RO, Global, za, za, za.
    all: split; first done.
    all: case_decide as Hallow; [by apply Hmem in Hallow | done].
  Qed.

  Lemma load_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst src : RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Load dst src) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & >Hsa & Hinterp) WorldRes ]".
    assert (Persistent (▷ P W C (w, w))) as HpersP.
    { apply bi.later_persistent. specialize (Hpers (W,C,(w,w))). auto. }
    iDestruct "Hinterp" as "#Hw".
    cbn [fst snd].

    (* The address of the PC is readable *)
    iAssert (▷ rcond P C p' interp)%I as "#HrcondP".
    { rewrite decide_True; first done.
      exists PC, (WCap p g b e a); split; first by simplify_map_eq.
      split.
      - destruct Hp as [Hexec _]; by apply executeAllowed_is_readAllowed.
      - cbn; split; [solve_addr | done]. }
    iClear "Hrcond Hwcond".

    (* The source register *)
    assert (is_Some (<[PC:=WCap p g b e a]> regs1 !!ᵣ src)) as [wsrc Hwsrc].
    { apply is_Some_lookup_reg, lookup_insert_is_Some'; eauto. }
    assert ((∃ p0 g0 b0 e0 a0, wsrc = WCap p0 g0 b0 e0 a0 ∧ readAllowed p0 = true ∧ withinBounds b0 e0 a0 = true)
            ∨ (∀ p0 g0 b0 e0 a0, ¬ reg_allows_load (<[PC:=WCap p g b e a]> regs1) src p0 g0 b0 e0 a0))
      as [(p0 & g0 & b0 & e0 & a0 & -> & Hra & Hwb) | Hnallow].
    { destruct wsrc as [ | [p0 g0 b0 e0 a0|] | | ].
      2: destruct (readAllowed p0) eqn:Hra; destruct (withinBounds b0 e0 a0) eqn:Hwb.
      2: left; eauto 10.
      all: right; intros ????? (Hr & Hra' & Hwb'); simplify_eq; congruence. }
    2: { (* The load fails in the implementation run *)
      iApply (wp_load _ _ _ _ _ _ dst src w (<[a:=w]> ∅) (<[PC:=WCap p g b e a]> regs1) (DfracOwn 1) with "[Hmap Ha]"); eauto.
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { apply allow_load_map_or_true_intro; first (apply lookup_insert_is_Some'; eauto).
        intros * Hallow; by apply Hnallow in Hallow. }
      { iSplitL "Ha"; iNext; [by iApply memMap_resource_1 | done]. }
      iNext. iIntros (regs' retv) "(%HSpec & Hmem & Hmap)".
      destruct HSpec as [* Hallow | ]; first by apply Hnallow in Hallow.
      ftlr_impl_fail.
    }

    (* The source register holds the same readable capability in both runs *)
    iDestruct (interp_reg_lookup_same with "Hinv_interp Hreg") as %Hwsrc2; [exact Hwsrc|done|].
    iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "#Hvsrc"; [exact Hwsrc|exact Hwsrc2|].
    apply withinBounds_le_addr in Hwb as Hwb'.
    iDestruct (read_allowed_inv _ _ a0 with "Hvsrc")
      as (pS PS HflpS HpersS) "(HrelS & HzcondS & HrcondS & HwcondS & HmonoS)"
    ; [solve_addr|by rewrite Hra|].
    assert (∀ Wv : WORLD * CmptName * (Word * Word), Persistent (PS Wv.1.1 Wv.1.2 Wv.2))
      as HpersS' by apply HpersS.
    destruct (decide (a0 = a)) as [-> | Hne].
    - (* The source capability points to the instruction *)
      iDestruct (rel_agree C a _ _ p' pS with "[$Hinva $HrelS]") as "[<- _]".
      iApply (wp_load _ _ _ _ _ _ dst src w (<[a:=w]> ∅) (<[PC:=WCap p g b e a]> regs1) (DfracOwn 1) with "[Hmap Ha]"); eauto.
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { apply allow_load_map_or_true_intro; first (apply lookup_insert_is_Some'; eauto).
        intros * (Hr & _); rewrite Hwsrc in Hr; simplify_eq; by simplify_map_eq. }
      { iSplitL "Ha"; iNext; [by iApply memMap_resource_1 | done]. }
      iNext. iIntros (regs' retv) "(%HSpec & Hmem & Hmap)".
      destruct HSpec as [p1 g1 b1 e1 a1 loadv Hallow Hmem_a HincrPC | ]; cycle 1.
      { ftlr_impl_fail. }
      destruct Hallow as (Hr1 & _ & _); rewrite Hwsrc in Hr1; injection Hr1 as <- <- <- <- <-.
      rewrite lookup_insert_eq in Hmem_a; injection Hmem_a as <-.

      iMod (step_load _ _ _ _ _ _ dst src w (<[a:=w]> ∅) (<[PC:=WCap p g b e a]> regs2) (DfracOwn 1)
             with "[$Hspec $Hj Hsa $Hsmap]") as (retv2 regs2') "(Hj & %HSpec2 & Hsmem & Hsmap)".
      { solve_ndisj. }
      { done. }
      { done. }
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { apply allow_load_map_or_true_intro; first (apply lookup_insert_is_Some'; eauto).
        intros * (Hr & _); rewrite Hwsrc2 in Hr; simplify_eq; by simplify_map_eq. }
      { by iApply spec_memMap_resource_1. }
      apply incrementPC_Some_inv in HincrPC as (p2&g2&b2&e2&a2&a3&HPC&Ha2&->).
      eapply Load_spec_determ in HSpec2 as [Hv2 Hregs2];
        last (eapply Load_spec_success; [split; eauto | by simplify_map_eq | transfer_incrementPC HPC Ha2]).
      specialize (Hregs2 eq_refl); subst retv2 regs2'.
      iDestruct (memMap_resource_1 with "Hmem") as "Ha".
      iDestruct (spec_memMap_resource_1 with "Hsmem") as "Hsa".
      iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      (* The loaded word is safe *)
      iAssert (interp W C (load_word p0 w, load_word p0 w)) as "#Hload".
      { iDestruct ("HrcondP" $! W (w,w) with "Hw") as "Hl".
        by iApply (interp_weakening_word_load _ _ p0 p' (w,w) with "Hl"). }

      iDestruct ("WorldRes" with "[$Ha $Hsa $Hw]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /insert_reg in HPC; simplify_map_eq.
        iApply ("IH" $! _ _ _ _ _ (<[PC:=_]ᵣ> _) (<[PC:=_]ᵣ> _)
                 with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
        * iApply (interp_reg_insert _ _ _ _ PC with "[]"); first by iApply interp_reg_insert_PC.
          by iIntros (?).
        * iModIntro; iEval (rewrite HPC) in "Hload".
          iApply (interp_weakening with "IH Hload"); eauto; try solve_addr; try reflexivity.
      + rewrite insert_reg_lookup_PC // in HPC; simplify_map_eq.
        iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
                 with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
        * iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
          by iIntros.
        * iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.

    - (* The source capability points to another address: open the world there *)
      iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ a0 with "Hvsrc")
        as %(ρ0 & Hstd0 & Hnotrevoked0); eauto.
      iDestruct (open_world_interp_next _ _ _ a0 pS _ ρ0 with "HrelS Hworld_interp")
        as "(Hworld_interp & Hstate0 & HWorldRes0)"; eauto.
      { set_solver. }
      { destruct ρ0; simplify_eq; try done; [by left | by right]. }
      iDestruct "HWorldRes0" as (v) "(>%HpOS & >Ha0 & >Hsa0 & HP0 & #Hmono0)".
      assert (Persistent (PS W C v)) as HpersPS by apply (HpersS (W,C,v)).
      iDestruct "HP0" as "#HP0".
      iApply (wp_load _ _ _ _ _ _ dst src w (<[a0:=v.1]> (<[a:=w]> ∅)) (<[PC:=WCap p g b e a]> regs1) (DfracOwn 1) with "[Hmap Ha Ha0]"); eauto.
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { apply allow_load_map_or_true_intro; first (apply lookup_insert_is_Some'; eauto).
        intros * (Hr & _); rewrite Hwsrc in Hr; simplify_eq; by simplify_map_eq. }
      { iSplitL "Ha Ha0"; iNext; [ rewrite memMap_resource_2ne //; iFrame | done]. }
      iNext. iIntros (regs' retv) "(%HSpec & Hmem & Hmap)".
      destruct HSpec as [p1 g1 b1 e1 a1 loadv Hallow Hmem_a HincrPC | ]; cycle 1.
      { ftlr_impl_fail. }
      destruct Hallow as (Hr1 & _ & _); rewrite Hwsrc in Hr1; injection Hr1 as <- <- <- <- <-.
      rewrite lookup_insert_eq in Hmem_a; injection Hmem_a as <-.

      (* The loaded words are related *)
      iAssert (interp W C (load_word p0 v.1, load_word p0 v.2)) as "#Hload".
      { iDestruct ("HrcondS" $! W v with "HP0") as "Hl".
        by iApply (interp_weakening_word_load _ _ p0 pS v with "Hl"). }
      apply incrementPC_Some_inv in HincrPC as (p2&g2&b2&e2&a2&a3&HPC&Ha2&->).
      iAssert (⌜dst = PC → load_word p0 v.1 = load_word p0 v.2⌝)%I as %Hdst_eq.
      { iIntros (->).
        rewrite /insert_reg in HPC; simplify_map_eq.
        iDestruct (interp_eq_not_sealed with "Hload") as %Heq; last done.
        by rewrite HPC. }

      iMod (step_load _ _ _ _ _ _ dst src w (<[a0:=v.2]> (<[a:=w]> ∅)) (<[PC:=WCap p g b e a]> regs2) (DfracOwn 1)
             with "[$Hspec $Hj Hsa Hsa0 $Hsmap]") as (retv2 regs2') "(Hj & %HSpec2 & Hsmem & Hsmap)".
      { solve_ndisj. }
      { done. }
      { done. }
      { by simplify_map_eq. }
      { rewrite /subseteq /map_subseteq. intros rr _.
        apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
      { by simplify_map_eq. }
      { apply allow_load_map_or_true_intro; first (apply lookup_insert_is_Some'; eauto).
        intros * (Hr & _); rewrite Hwsrc2 in Hr; simplify_eq; by simplify_map_eq. }
      { rewrite spec_memMap_resource_2ne //; iFrame. }
      destruct (decide (dst = PC)) as [->|HdstPC].
      { specialize (Hdst_eq eq_refl).
        rewrite Hdst_eq in HPC.
        eapply Load_spec_determ in HSpec2 as [Hv2 Hregs2];
          last (eapply Load_spec_success; [split; eauto | by simplify_map_eq | transfer_incrementPC HPC Ha2]).
        specialize (Hregs2 eq_refl); subst retv2 regs2'.
        iDestruct (memMap_resource_2ne with "Hmem") as "[Ha0 Ha]"; first done.
        iDestruct (spec_memMap_resource_2ne with "Hsmem") as "[Hsa0 Hsa]"; first done.
        iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
        iApply wp_pure_step_later; auto; iNext; iIntros "_".
        iDestruct (close_world_interp_next _ _ _ a0 pS _ v ρ0 with "Hworld_interp Hstate0 HrelS [Ha0 Hsa0]")
          as "Hworld_interp"; eauto.
        { set_solver. }
        { destruct ρ0; simplify_eq; try done; [by left | by right]. }
        { iFrame "∗#%". }
        iDestruct ("WorldRes" with "[$Ha $Hsa $Hw]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ;auto;contradiction. }
        rewrite /insert_reg in HPC; simplify_map_eq.
        iApply ("IH" $! _ _ _ _ _ (<[PC:=load_word p0 v.1]ᵣ> _) (<[PC:=load_word p0 v.2]ᵣ> _)
                 with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
        - iApply (interp_reg_insert _ _ _ _ PC (load_word p0 v.1) (load_word p0 v.2) with "[]")
          ; first by iApply interp_reg_insert_PC.
          by iIntros (?).
        - iModIntro. iEval (rewrite Hdst_eq HPC) in "Hload".
          iApply (interp_weakening with "IH Hload"); eauto; try solve_addr; try reflexivity.
      }
      eapply Load_spec_determ in HSpec2 as [Hv2 Hregs2];
        last (eapply Load_spec_success; [split; eauto | by simplify_map_eq | transfer_incrementPC HPC Ha2]).
      specialize (Hregs2 eq_refl); subst retv2 regs2'.
      iDestruct (memMap_resource_2ne with "Hmem") as "[Ha0 Ha]"; first done.
      iDestruct (spec_memMap_resource_2ne with "Hsmem") as "[Hsa0 Hsa]"; first done.
      iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".
      iDestruct (close_world_interp_next _ _ _ a0 pS _ v ρ0 with "Hworld_interp Hstate0 HrelS [Ha0 Hsa0]")
        as "Hworld_interp"; eauto.
      { set_solver. }
      { destruct ρ0; simplify_eq; try done; [by left | by right]. }
      { iFrame "∗#%". }
      iDestruct ("WorldRes" with "[$Ha $Hsa $Hw]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }
      rewrite insert_reg_lookup_PC // in HPC; simplify_map_eq.
      iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
               with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
      + iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
        by iIntros.
      + iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
