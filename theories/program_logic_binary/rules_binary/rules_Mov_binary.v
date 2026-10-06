From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Mov.

(** * Spec rules for [Mov] (spec copies of [rules_Mov.v]) *)

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

  Lemma Mov_spec_determ regs dst src regs1 regs2 v1 v2 :
    Mov_spec regs dst src regs1 v1 →
    Mov_spec regs dst src regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ Mov_spec. Qed.

  Lemma step_Mov Ep pc_p pc_g pc_b pc_e pc_a  w dst src regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = Mov dst src ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Mov dst src) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Mov_spec regs dst src regs' retv ⌝ ∗
      pc_a ↣ₐ w ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[r sr] m] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
    iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_mem_valid with "Hm Hpc_a") as %Hpc_a; auto.
    eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.

    assert (exists w, word_of_argument regs src = Some w) as [wsrc Hwsrc].
    { destruct src as [| r0]; eauto; cbn.
      destruct (Hri r0) as [? [? ?]]; first set_solver+. eauto. }

    pose proof Hwsrc as Hwsrc'. eapply word_of_argument_Some_inv' in Hwsrc; eauto.

    assert (exec_opt (Mov dst src) pc_p (r, sr, m) = updatePC (update_reg (r, sr, m) dst wsrc)) as HH.
    { destruct Hwsrc as [ [? [? ?] ] | [? (? & ? & Hr') ] ]; simplify_eq; eauto.
      cbn. by rewrite /= Hr'. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := wsrc ]ᵣ> regs)) as [regs'|] eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (sregs':=sr) (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      rewrite Hregs' in Hstep. simplify_pair_eq.
      iFrame. iApply "Hφ"; iFrame. iPureIntro. econstructor; eauto. }

    eapply (incrementPC_success_updatePC _ sr m) in Hregs'
      as (p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in Hstep. simplify_pair_eq. iFrame.
    iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_move_success_z_gen E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 z :
    ↑specN ⊆ E →
    decodeInstrW w = Mov r1 (inl z) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ wr1
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt (if (decide (r1 = cnull)) then 0 else z).
  Proof.
    iIntros (HE Hinstr Hvpc Hpca') "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iMod (step_Mov with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [|].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      destruct (decide (r1 = cnull)) ; simplify_map_eq.
      all: rewrite (insert_insert_ne _ PC _) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      all: iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_move_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 z :
    ↑specN ⊆ E →
    decodeInstrW w = Mov r1 (inl z) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ wr1
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt z.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    iMod (step_move_success_z_gen with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "H"; eauto.
    destruct (decide (r1 = cnull)); first done.
    by iFrame.
  Qed.

  Lemma step_move_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 rv wrv :
    ↑specN ⊆ E →
    decodeInstrW w = Mov r1 (inr rv) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    rv ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ wr1 ∗
    rv ↣ᵣ wrv
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ wrv ∗
    rv ↣ᵣ wrv.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hrv)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
    iMod (step_Mov with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [|].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ PC r1) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_move_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 :
    ↑specN ⊆ E →
    decodeInstrW w = Mov r1 (inr r1) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ wr1
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ wr1.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iMod (step_Mov with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [|].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_move_success_reg_samePC E pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
    decodeInstrW w = Mov PC (inr PC) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca') "(#Hctx & Hj & HPC & Hpc_a)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iMod (step_Mov with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [|].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
      iDestruct (spec_regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_move_success_reg_toPC E pc_p pc_g pc_b pc_e pc_a w r1 p g b e a a':
    ↑specN ⊆ E →
    decodeInstrW w = Mov PC (inr r1) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (a + 1)%a = Some a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap p g b e a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap p g b e a.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iMod (step_Mov with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [|].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_move_success_reg_fromPC E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 wr1 :
    ↑specN ⊆ E →
    decodeInstrW w = Mov r1 (inr PC) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ wr1
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iMod (step_Mov with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [|].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

End spec_rules.
