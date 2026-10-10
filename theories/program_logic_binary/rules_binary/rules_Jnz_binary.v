From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Jnz.

(** * Spec rules for [Jnz] (spec copies of [rules_Jnz.v]) *)

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

  Lemma Jnz_spec_determ regs rimm rcond regs1 regs2 v1 v2 :
    Jnz_spec regs rimm rcond regs1 v1 →
    Jnz_spec regs rimm rcond regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ Jnz_failure. Qed.

  Lemma step_Jnz Ep pc_p pc_g pc_b pc_e pc_a w rimm rcond regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = Jnz rimm rcond ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jnz rimm rcond) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Jnz_spec regs rimm rcond regs' retv ⌝ ∗
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

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rcond) as [wrcond [H'rcond Hrcond]]; first by set_solver+.
    unfold exec in Hstep; cbn in Hstep.
    rewrite Hrcond /= in Hstep.

    destruct (nonZero wrcond) eqn:Hnz; pose proof Hnz as H'nz; cbn in Hstep.
    - destruct (z_of_argument regs rimm) as [imm|] eqn:Himm
      ; pose proof Himm as H'imm
      ; cycle 1.
      { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
        unfold z_of_argument in Himm, Hstep.
        destruct rimm as [| rimm]; [ congruence |].
        odestruct (Hri rimm) as [rimmv [Hrimm' Hrimm]].
        { unfold regs_of_argument. set_solver+. }
        rewrite Hrimm Hrimm' in Himm Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
        { destruct_word rimmv; cbn in Hstep; try congruence; by simplify_pair_eq. }
        iFailWP "Hφ" Jnz_fail_no_imm. }
      apply (z_of_arg_mono _ r) in Himm; auto.
      rewrite Himm in Hstep; simpl in Hstep.

      destruct (incrementPC_gen regs imm) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      {
        assert (incrementPC_gen r imm = None) as HH.
        { eapply incrementPC_gen_overflow_mono; first eapply Hregs' ; eauto.
        }
        apply (incrementPC_gen_fail_updatePC_gen _ sr m) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->) by (inversion Hstep; auto).
        iFailWP "Hφ" Jnz_fail_PC_overflow_jmp. }

      eapply (incrementPC_gen_success_updatePC_gen _ sr m _ imm) in Hregs'
          as (p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_gen_success_incl with (sregs':=sr) (m':=m) in HuPC; eauto.
      rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { cbn in *; eauto. }
      simplify_pair_eq.

      iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame.
      iApply "Hφ". iFrame. iPureIntro.
      eapply Jnz_spec_success_jmp; eauto.
    - destruct (incrementPC regs) eqn:HX; pose proof HX as H'X; cycle 1.
      { apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) in HX.
        eapply updatePC_fail_incl with (sregs':=sr) (m':=m) in HX; eauto.
        rewrite HX in Hstep. inv Hstep.
        iFailWP "Hφ" Jnz_fail_PC_overflow_next. }

      destruct (incrementPC_success_updatePC _ sr m _ HX)
        as (p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC; eauto. rewrite HuPC in Hstep.
      simplify_pair_eq.
      iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro.
      eapply Jnz_spec_success_next; eauto.
  Qed.

  Lemma step_jnz_success_jmp_z E rcond pc_p pc_g pc_b pc_e pc_a pc_a' w imm wcond :
    ↑specN ⊆ E →
    decodeInstrW w = Jnz (inl imm) rcond →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    wcond ≠ WInt 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rcond ↣ᵣ wcond
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rcond ↣ᵣ wcond.
  Proof.
    iIntros (HE Hinstr Hvpc Hne Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrcond)".
    iDestruct (spec_map_of_regs_2 with "HPC Hrcond") as "[Hmap %]".
    iMod (step_Jnz with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    assert (nonZero wcond = true).
    { unfold nonZero, Z.eqb in *.
      destruct wcond; auto.
      repeat case_match; try congruence; by cbn.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_map_eq; congruence. }
    { iModIntro. iFrame. simplify_map_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      rewrite insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { destruct Hfail; simplify_map_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto; congruence.
    }
  Qed.

  Lemma step_jnz_success_jmp_reg E rcond rimm pc_p pc_g pc_b pc_e pc_a pc_a' w imm wcond :
    ↑specN ⊆ E →
    decodeInstrW w = Jnz (inl imm) rcond →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    wcond ≠ WInt 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->
    rimm ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rimm ↣ᵣ WInt imm ∗
    rcond ↣ᵣ wcond
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rimm ↣ᵣ WInt imm ∗
    rcond ↣ᵣ wcond.
  Proof.
    iIntros (HE Hinstr Hvpc Hne Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hrimm & Hrcond)".
    iDestruct (spec_map_of_regs_3 with "HPC Hrimm Hrcond") as "[Hmap (%&%&%)]".
    iMod (step_Jnz with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    assert (nonZero wcond = true).
    { unfold nonZero, Z.eqb in *.
      destruct wcond; auto.
      repeat case_match; try congruence; by cbn.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_map_eq; congruence. }
    { iModIntro. iFrame. simplify_map_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      rewrite insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { destruct Hfail; simplify_map_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto; congruence.
    }
  Qed.

  Lemma step_jnz_success_jmp_same E rcond pc_p pc_g pc_b pc_e pc_a pc_a' w imm :
    ↑specN ⊆ E →
    decodeInstrW w = Jnz (inr rcond) rcond →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    imm ≠ 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rcond ↣ᵣ WInt imm
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    ▷ rcond ↣ᵣ WInt imm.
  Proof.
    iIntros (HE Hinstr Hvpc Hne Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrcond)".
    iDestruct (spec_map_of_regs_2 with "HPC Hrcond") as "[Hmap %]".
    iMod (step_Jnz with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    assert (nonZero (WInt imm) = true).
    { unfold nonZero, Z.eqb in *.
      destruct imm; auto.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_map_eq; congruence. }
    { iModIntro. iFrame. simplify_map_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      rewrite insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { destruct Hfail; simplify_map_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto; congruence.
    }
  Qed.

  Lemma step_jnz_success_jmpPC_z E pc_p pc_g pc_b pc_e pc_a pc_a' w imm:
    ↑specN ⊆ E →
    decodeInstrW w = Jnz (inl imm) PC →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a' ->
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
    iMod (step_Jnz with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_map_eq; congruence. }
    { iModIntro. iFrame. simplify_map_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      rewrite insert_insert_eq.
      iDestruct (spec_regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { destruct Hfail; simplify_map_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto; congruence.
    }
  Qed.

  Lemma step_jnz_success_jmpPC_reg E rimm pc_p pc_g pc_b pc_e pc_a pc_a' w imm :
    ↑specN ⊆ E →
    decodeInstrW w = Jnz (inl imm) PC →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a' ->
    rimm ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rimm ↣ᵣ WInt imm
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rimm ↣ᵣ WInt imm.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrimm)".
    iDestruct (spec_map_of_regs_2 with "HPC Hrimm") as "[Hmap %]".
    iMod (step_Jnz with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_map_eq; congruence. }
    { iModIntro. iFrame. simplify_map_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
      rewrite insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { destruct Hfail; simplify_map_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto; congruence.
    }
  Qed.

  Lemma step_jnz_success_next_z E rcond pc_p pc_g pc_b pc_e pc_a pc_a' w imm :
    ↑specN ⊆ E →
    decodeInstrW w = Jnz (inl imm) rcond →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rcond ↣ᵣ WInt 0%Z
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rcond ↣ᵣ WInt 0%Z.
  Proof.
    iIntros (HE Hinstr Hvpc Hpc_a') "(#Hctx & Hj & HPC & Hpc_a & Hrcond)".
    iDestruct (spec_map_of_regs_2 with "HPC Hrcond") as "[Hmap %]".
    iMod (step_Jnz with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | Hfail ]; try incrementPC_inv; simplify_map_eq; eauto.
    { iModIntro. iFrame.
      rewrite insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { destruct (decide (rcond = cnull)); cbn in *; done. }
    { destruct Hfail; simplify_map_eq; eauto; try congruence.
      all: destruct (decide (rcond = cnull)); cbn in *; try done.
      all: incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto; congruence.
    }
  Qed.

  Lemma step_jnz_success_next_reg E rimm rcond pc_p pc_g pc_b pc_e pc_a pc_a' w wimm :
    ↑specN ⊆ E →
    decodeInstrW w = Jnz (inr rimm) rcond →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rimm ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rimm ↣ᵣ wimm ∗
    rcond ↣ᵣ WInt 0%Z
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rimm ↣ᵣ wimm ∗
    rcond ↣ᵣ WInt 0%Z.
  Proof.
    iIntros (HE Hinstr Hvpc Hpc_a' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrimm & Hrcond)".
    iDestruct (spec_map_of_regs_3 with "HPC Hrcond Hrimm") as "[Hmap (%&%&%)]".
    iMod (step_Jnz with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | Hfail ]; try incrementPC_inv; simplify_map_eq; eauto.
    { iModIntro. iFrame.
      rewrite insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { destruct (decide (rcond = cnull)); cbn in *; done. }
    { destruct Hfail; simplify_map_eq; eauto; try congruence.
      all: destruct (decide (rcond = cnull)); cbn in *; try done.
      all: try (incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto; congruence).
    }
  Qed.

End spec_rules.
