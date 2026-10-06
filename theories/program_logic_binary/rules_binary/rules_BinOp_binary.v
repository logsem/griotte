From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_BinOp.

(** * Spec rules for [BinOp] (spec copies of [rules_BinOp.v]) *)

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

  (* Copy of the local tactic of [rules_BinOp.v]. *)
  Local Ltac iFail Hcont get_fail_case :=
    cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
    econstructor; eapply get_fail_case; eauto.

  Lemma BinOp_spec_determ i regs dst rv1 rv2 regs1 regs2 v1 v2 :
    BinOp_spec i regs dst rv1 rv2 regs1 v1 →
    BinOp_spec i regs dst rv1 rv2 regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ BinOp_failure. Qed.

  Lemma step_BinOp Ep i pc_p pc_g pc_b pc_e pc_a w dst arg1 arg2 regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = i →
    is_BinOp i dst arg1 arg2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of i ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ BinOp_spec (decodeInstrW w) regs dst arg1 arg2 regs' retv ⌝ ∗
      pc_a ↣ₐ w ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hdecode Hinstr Hvpc HPC Dregs) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[r sr] m] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
    iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_mem_valid with "Hm Hpc_a") as %Hpc_a; auto.
    eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    erewrite regs_of_is_BinOp in Hri, Dregs; eauto.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.

    destruct (z_of_argument regs arg1) as [n1|] eqn:Hn1;
      pose proof Hn1 as Hn1'; cycle 1.
    (* Failure: arg1 is not an integer *)
    { unfold z_of_argument in Hn1. destruct arg1 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]; first by unfold regs_of_argument; set_solver+.
      assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
      { rewrite Hr'0 in Hn1.
        destruct_word r0v; try congruence.
        all: destruct_or! Hinstr; rewrite Hinstr /= in Hstep.
        all: rewrite Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFail "Hφ" BinOp_fail_nonconst1. }
    apply (z_of_arg_mono _ r) in Hn1; auto.

    destruct (z_of_argument regs arg2) as [n2|] eqn:Hn2;
      pose proof Hn2 as Hn2'; cycle 1.
    (* Failure: arg2 is not an integer *)
    { unfold z_of_argument in Hn2. destruct arg2 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]; first by unfold regs_of_argument; set_solver+.
      assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
      {
        rewrite Hr'0 in Hn2. destruct_word r0v; try congruence.
        all: destruct_or! Hinstr; rewrite Hinstr /= Hn1 in Hstep; cbn in Hstep.
        all: rewrite Hr0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iFail "Hφ" BinOp_fail_nonconst2. }
    apply (z_of_arg_mono _ r) in Hn2; auto.

    assert (exec_opt i pc_p (r, sr, m) = updatePC (update_reg (r, sr, m) dst (WInt (denote i n1 n2)))) as HH.
    { all: destruct_or! Hinstr; rewrite Hinstr /= /update_reg /= in Hstep |- *; auto.
      all: by rewrite Hn1 Hn2; cbn. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := WInt (denote i n1 n2) ]ᵣ> regs))
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    (* Failure: Cannot increment PC *)
    { apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (sregs':=sr) (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      rewrite Hregs' in Hstep. inversion Hstep.
      iFail "Hφ" BinOp_fail_incrPC. }


    (* Success *)

    eapply (incrementPC_success_updatePC _ sr m) in Hregs'
      as (p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':= sr) (m':=m) in HuPC.
    2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
    simplify_pair_eq. iFrame.
    iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_binop_success_z_z E dst pc_p pc_g pc_b pc_e pc_a w wdst ins n1 n2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inl n1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WInt (denote ins n1 n2).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_r_z E dst pc_p pc_g pc_b pc_e pc_a w wdst ins r1 n1 n2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inr r1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt n1 ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt n1 ∗
    dst ↣ᵣ WInt (denote ins n1 n2).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
              (insert_insert_ne _ dst PC) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_z_r E dst pc_p pc_g pc_b pc_e pc_a w wdst ins n1 r2 n2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inl n1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WInt n2 ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WInt n2 ∗
    dst ↣ᵣ WInt (denote ins n1 n2).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr2 & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ dst PC) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_r_r E dst pc_p pc_g pc_b pc_e pc_a w wdst ins r1 n1 r2 n2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inr r1) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt n1 ∗
    r2 ↣ᵣ WInt n2 ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt n1 ∗
    r2 ↣ᵣ WInt n2 ∗
    dst ↣ᵣ WInt (denote ins n1 n2).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull Hncull' Hncull'') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2 & Hdst)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_r_r_same E dst pc_p pc_g pc_b pc_e pc_a w wdst ins r n pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inr r) (inr r) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r ↣ᵣ WInt n ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r ↣ᵣ WInt n ∗
    dst ↣ᵣ WInt (denote ins n n).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull Hncull') "(#Hctx & Hj & HPC & Hpc_a & Hr & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr Hdst") as "[Hmap (%&%&%)]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r dst) //
              (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_dst_z E dst pc_p pc_g pc_b pc_e pc_a w ins n1 n2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inr dst) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WInt n1
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WInt (denote ins n1 n2).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_z_dst E dst pc_p pc_g pc_b pc_e pc_a w ins n1 n2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inl n1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WInt n2
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WInt (denote ins n1 n2).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_dst_r E dst pc_p pc_g pc_b pc_e pc_a w ins n1 r2 n2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inr dst) (inr r2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WInt n2 ∗
    dst ↣ᵣ WInt n1
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WInt n2 ∗
    dst ↣ᵣ WInt (denote ins n1 n2).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr2 & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_r_dst E dst pc_p pc_g pc_b pc_e pc_a w ins r1 n1 n2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inr r1) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt n1 ∗
    dst ↣ᵣ WInt n2
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt n1 ∗
    dst ↣ᵣ WInt (denote ins n1 n2).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr2 & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
              (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_success_dst_dst E dst pc_p pc_g pc_b pc_e pc_a w ins n pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inr dst) (inr dst) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WInt n
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WInt (denote ins n n).
  Proof.
    iIntros (HE Hdecode Hinstr Hpc_a Hvpc Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_binop_fail_z_r E ins dst n1 r2 w w2 wdst pc_p pc_g pc_b pc_e pc_a :
    ↑specN ⊆ E →
    decodeInstrW w = ins →
    is_BinOp ins dst (inl n1) (inr r2) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    is_z w2 = false →
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ wdst ∗
    r2 ↣ᵣ w2
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w.
  Proof.
    iIntros (HE Hdecode Hinstr Hvpc Hisnz Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hdst & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hdst Hr2") as "[Hmap (%&%&%)]".
    iMod (step_BinOp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)  destruct w2; simplify_map_eq. }
    { (* Failure, done *) iModIntro. by iFrame. }
  Qed.

End spec_rules.
