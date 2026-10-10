From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Get.

(** * Spec rules for [Get] (spec copies of [rules_Get.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types o : OType.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma Get_spec_determ i regs dst src regs1 regs2 v1 v2 :
    Get_spec i regs dst src regs1 v1 →
    Get_spec i regs dst src regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ Get_failure. Qed.

  Lemma step_Get Ep pc_p pc_g pc_b pc_e pc_a w get_i dst src regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = get_i →
    is_Get get_i dst src →

    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of get_i ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Get_spec (decodeInstrW w) regs dst src regs' retv ⌝ ∗
      pc_a ↣ₐ w ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hdecode Hinstr Hvpc HPC Dregs) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[r sr] m] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
    iPoseProof (spec_regs_valid_inclSepM with "Hr Hmap") as "#H".
    iDestruct "H" as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_mem_valid with "Hm Hpc_a") as %Hpc_a; auto.
    eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    erewrite regs_of_is_Get in Hri; eauto.
    destruct (Hri src) as [wsrc [H'src Hsrc]]; first by set_solver+.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.
    destruct (denote get_i wsrc) as [z | ] eqn:Hwsrc.
    2 : { (* Failure: src is not of the right word type *)
      assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
      { destruct_or! Hinstr; rewrite Hinstr in Hstep; cbn in Hstep.
        all: rewrite Hsrc /= in Hstep.
        all : destruct wsrc as [ | [  |  ] | | ]; try (inversion Hstep; auto);
          rewrite /denote /= in Hwsrc; rewrite Hinstr in Hwsrc; congruence. }
      rewrite Hdecode. iFailWP "Hφ" Get_fail_src_denote. }

    assert (exec_opt get_i pc_p (r, sr, m) = updatePC (update_reg (r, sr, m) dst (WInt z))) as HH.
    { destruct_or! Hinstr; clear Hdecode; subst get_i; cbn in Hstep |- *.
      all: rewrite /update_reg Hsrc /= in Hstep |-*; auto.
      all : destruct wsrc as [ | [  |  ] | | ]; inversion Hwsrc; auto.
    }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := WInt z ]ᵣ> regs))
      as [regs'|] eqn:Hregs'; pose proof Hregs' as H'regs'; cycle 1.
    { (* Failure: incrementing PC overflows *)
      apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (sregs':=sr) (m':=m) in Hregs'.
      2: simpl_map_regs by eauto.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      simplify_pair_eq.
      rewrite Hregs' in Hstep. inversion Hstep.
      iFailWP "Hφ" Get_fail_overflow_PC. }

    (* Success *)

    eapply (incrementPC_success_updatePC _ sr m) in Hregs'
        as (p' & g' & b' & e' & a' & a'' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
    simplify_pair_eq. iFrame.
    iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_Get_PC_success E get_i dst pc_p pc_g pc_b pc_e pc_a w wdst pc_a' z :
    ↑specN ⊆ E →
    decodeInstrW w = get_i →
    is_Get get_i dst PC →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i (WCap pc_p pc_g pc_b pc_e pc_a) = Some z →
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
    dst ↣ᵣ WInt z.
  Proof.
    iIntros (HE Hdecode Hinstr Hvpc Hpca' Hdenote Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iMod (step_Get with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_Get_same_success E get_i r pc_p pc_g pc_b pc_e pc_a w wr pc_a' z:
    ↑specN ⊆ E →
    decodeInstrW w = get_i →
    is_Get get_i r r →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wr = Some z →
    r ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r ↣ᵣ wr
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r ↣ᵣ WInt z.
  Proof.
    iIntros (HE Hdecode Hinstr Hvpc Hpca' Hdenote Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iMod (step_Get with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_Get_success E get_i dst src pc_p pc_g pc_b pc_e pc_a w wsrc wdst pc_a' z :
    ↑specN ⊆ E →
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    denote get_i wsrc = Some z →
    src ≠ cnull ->
    dst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc ∗
    dst ↣ᵣ WInt z.
  Proof.
    iIntros (HE Hdecode Hinstr Hvpc Hpca' Hdenote Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iMod (step_Get with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_Get_unknown E get_i dst src pc_p pc_g pc_b pc_e pc_a pc_a' w wsrc wdst :
    ↑specN ⊆ E →
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    (forall dst' src', get_i <> GetOType dst' src') ->
    (forall dst' src', get_i <> GetWType dst' src') ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull ->
    dst ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ wdst ∗
    src ↣ᵣ wsrc
    ={E}=∗
    ∃ retv,
      ⤇ Seq (of_val retv) ∗
      (⌜ retv = FailedV ⌝ ∨
       (∃ z,
          ⌜ denote get_i wsrc = Some z ⌝ ∗
          ⌜ (is_cap wsrc || is_sealr wsrc || is_sentry wsrc) = true ⌝ ∗
          ⌜ retv = NextIV ⌝ ∗
          PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↣ₐ w ∗
          src ↣ᵣ wsrc ∗
          dst ↣ᵣ WInt z)).
  Proof.
    iIntros (HE Hdecode Hinstr Hnot_otype Hnot_wtype Hvpc Hpc_a' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iMod (step_Get with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)
      iModIntro. iExists NextIV. iFrame "Hj".
      iRight.
      iExists z.
      iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.
      iFrame "%".
      iSplit; last done.
      iPureIntro.
      destruct w0 as [| [|] | |]; cbn; try done
      ; destruct (decodeInstrW w); simplify_map_eq
      ; specialize (Hnot_otype dst0 r)
      ; specialize (Hnot_wtype dst0 r)
      ; try contradiction.
    }
    { (* Failure, done *) iModIntro. iExists FailedV. iFrame. by iLeft. }
  Qed.

End spec_rules.
