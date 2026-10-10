From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Jalr.

(** * Spec rules for [Jalr] (spec copies of [rules_Jalr.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma Jalr_spec_determ regs pc_p pc_g pc_b pc_e pc_a rdst rsrc regs1 regs2 v1 v2 :
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a rdst rsrc regs1 v1 →
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a rdst rsrc regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ Jalr_spec. Qed.

  Lemma step_Jalr Ep pc_p pc_g pc_b pc_e pc_a w rdst rsrc regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = Jalr rdst rsrc ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jalr rdst rsrc) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Jalr_spec regs pc_p pc_g pc_b pc_e pc_a rdst rsrc regs' retv ⌝ ∗
      pc_a ↣ₐ w ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[r sr] m] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
    iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.
    have HrPC := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_mem_valid with "Hm Hpc_a") as %Hpc_a; auto.
    eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rdst) as [wdst [H'rdst Hrdst]]; first by set_solver+.
    destruct (Hri rsrc) as [wsrc [H'rsrc Hrsrc]]; first by set_solver+.
    rewrite /exec in Hstep; cbn in Hstep.
    rewrite Hrsrc HrPC /= in Hstep.

    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; simplify_pair_eq; cycle 1.
    { iFailWP "Hφ" Jalr_spec_failure. }
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; simplify_map_eq; eauto.
    iMod ((spec_regs_update_inSepM _ _ rdst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { destruct (decide (rdst = PC)); simplify_map_eq; auto.
      apply is_Some_lookup_reg; done. }
    iFrame.
    iApply "Hφ"; iFrame.
    iPureIntro; econstructor; eauto.
  Qed.

  Lemma step_jalr_success E pc_p pc_g pc_b pc_e pc_a pc_a' w rsrc wsrc rdst wdst :
    ↑specN ⊆ E →
    decodeInstrW w = Jalr rdst rsrc →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rsrc ↣ᵣ wsrc ∗
    rdst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ updatePcPerm wsrc ∗
    pc_a ↣ₐ w ∗
    rsrc ↣ᵣ wsrc ∗
    rdst ↣ᵣ WSentry pc_p pc_g pc_b pc_e pc_a'.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hrsrc & Hrdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hrsrc Hrdst") as "[Hmap (%&%&%)]".
    iMod (step_Jalr with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

   destruct Hspec as [ | Hfail ]; subst.
   { iModIntro. iFrame. simplify_map_eq.
     rewrite (insert_insert_ne _ rsrc rdst) // insert_insert_eq.
     rewrite (insert_insert_ne _ rdst PC) // insert_insert_eq.
     iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma step_jalr_success_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w rsrc wsrc wdst :
    ↑specN ⊆ E →
    decodeInstrW w = Jalr cnull rsrc →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rsrc ↣ᵣ wsrc ∗
    cnull ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ updatePcPerm wsrc ∗
    pc_a ↣ₐ w ∗
    rsrc ↣ᵣ wsrc ∗
    cnull ↣ᵣ WInt 0.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrsrc & Hrdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hrsrc Hrdst") as "[Hmap (%&%&%)]".
    iMod (step_Jalr with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

   destruct Hspec as [ | Hfail ]; subst.
   { iModIntro. iFrame. simplify_map_eq.
     rewrite (insert_insert_ne _ rsrc cnull) // insert_insert_eq.
     rewrite (insert_insert_ne _ PC cnull) // insert_insert_eq.
     iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma step_jalr_successPC E pc_p pc_g pc_b pc_e pc_a pc_a' w rdst wdst :
    ↑specN ⊆ E →
    decodeInstrW w = Jalr rdst PC →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rdst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ updatePcPerm (WCap pc_p pc_g pc_b pc_e pc_a) ∗
    pc_a ↣ₐ w ∗
    rdst ↣ᵣ WSentry pc_p pc_g pc_b pc_e pc_a'.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hrdst") as "[Hmap %]".
    iMod (step_Jalr with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

   destruct Hspec as [ | Hfail ]; subst.
   { iModIntro. iFrame.
     simplify_map_eq.
     rewrite insert_insert_eq (insert_insert_ne _ rdst PC) // insert_insert_eq.
     iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma step_jalr_success_rdst E pc_p pc_g pc_b pc_e pc_a pc_a' w wdst rdst :
    ↑specN ⊆ E →
    decodeInstrW w = Jalr rdst rdst →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rdst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ updatePcPerm wdst ∗
    pc_a ↣ₐ w ∗
    rdst ↣ᵣ WSentry pc_p pc_g pc_b pc_e pc_a'.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hrdst") as "[Hmap %]".
    iMod (step_Jalr with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

   destruct Hspec as [ | Hfail ]; subst.
   { iModIntro. iFrame.
     simplify_map_eq.
     rewrite insert_insert_eq (insert_insert_ne _ rdst PC) // !insert_insert_eq.
     iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

End spec_rules.
