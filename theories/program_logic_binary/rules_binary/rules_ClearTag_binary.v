From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_ClearTag.

(** * Spec rules for [ClearTag] (spec copies of [rules_ClearTag.v]) *)

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

  Lemma ClearTag_spec_determ regs dst src regs1 regs2 v1 v2 :
    ClearTag_spec regs dst src regs1 v1 →
    ClearTag_spec regs dst src regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ ClearTag_spec. Qed.

  Lemma step_ClearTag Ep pc_p pc_g pc_b pc_e pc_a  w dst src regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = ClearTag dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (ClearTag dst src) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ ClearTag_spec regs dst src regs' retv ⌝ ∗
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

    destruct (Hri src) as [wsrc [H'src Hsrc]]; first by set_solver+.

    assert (exec_opt (ClearTag dst src) pc_p (r, sr, m) =
      updatePC (update_reg (r, sr, m) dst (clear_tag wsrc))) as HH.
    { cbn. by rewrite Hsrc. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := clear_tag wsrc ]ᵣ> regs)) as [regs'|] eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (sregs':=sr) (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      rewrite Hregs' in Hstep. simplify_pair_eq.
      iFrame. iApply "Hφ"; iFrame. iPureIntro. econstructor; eauto. }

    eapply (incrementPC_success_updatePC _ sr m) in Hregs'
      as (t' & p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in Hstep. simplify_pair_eq. iFrame.
    iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_ClearTag_same_success E r pc_p pc_g pc_b pc_e pc_a w wr pc_a':
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag r r →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    r ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r ↣ᵣ wr
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r ↣ᵣ clear_tag wr.
  Proof.
    iIntros (HE Hdecode Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [|].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_ClearTag_success E dst src pc_p pc_g pc_b pc_e pc_a w wsrc wdst pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    src ≠ cnull ->
    dst ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc ∗
    dst ↣ᵣ clear_tag wsrc.
  Proof.
    iIntros (HE Hdecode Hvpc Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [|].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma step_ClearTag_failure E pc_p pc_g pc_b pc_e pc_a w dst src regs wsrc :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (ClearTag dst src) ⊆ dom regs →
    regs !!ᵣ src = Some wsrc →
    incrementPC (<[dst := clear_tag wsrc]ᵣ> regs) = None →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hdecode Hvpc HPC Hdom Hsrc Hinc) "(#Hctx & Hj & Hpre)".
    iMod (step_ClearTag with "[$Hctx $Hj $Hpre]") as "H"; eauto.
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hregs)".
    destruct Hspec; simplify_eq.
    iModIntro. iFrame.
  Qed.

  Lemma step_ClearTag_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag PC PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↣ₐ w.
  Proof.
    iIntros (HE Hdecode Hvpc Hinc) "(#Hctx & Hj & HPC & Hmem)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
      iDestruct (spec_regs_of_map_1 with "Hmap") as "HPC".
      iModIntro. iFrame.
    - incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.
  Lemma step_ClearTag_fromPC E dst pc_p pc_g pc_b pc_e pc_a pc_a' w wdst :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag dst PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗ dst ↣ᵣ WCap false pc_p pc_g pc_b pc_e pc_a.
  Proof.
    iIntros (HE Hdecode Hvpc Hinc Hcnull) "(#Hctx & Hj & HPC & Hmem & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "[HPC Hdst]"; eauto.
      iModIntro. iFrame.
    - incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.

  Lemma step_ClearTag_toPC E src pc_p pc_g pc_b pc_e pc_a w
      (t : bool) p g b e a a' :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag PC src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (a + 1)%a = Some a' → src ≠ cnull →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗
    src ↣ᵣ WCap t p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap false p g b e a' ∗ pc_a ↣ₐ w ∗
    src ↣ᵣ WCap t p g b e a.
  Proof.
    iIntros (HE Hdecode Hvpc Hinc Hcnull) "(#Hctx & Hj & HPC & Hmem & Hsrc)".
    iDestruct (spec_map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "[HPC Hsrc]"; eauto.
      iModIntro. iFrame.
    - incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.

  Lemma step_ClearTag_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w wn :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag cnull cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ wn
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ WInt 0%Z.
  Proof.
    iIntros (HE Hdecode Hvpc Hinc) "(#Hctx & Hj & HPC & Hmem & Hn)".
    iDestruct (spec_map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto.
      iModIntro. iFrame.
    - incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma step_ClearTag_from_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w dst wd wn :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag dst cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ wn ∗ dst ↣ᵣ wd
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↣ₐ w ∗ dst ↣ᵣ WInt 0%Z ∗ cnull ↣ᵣ wn.
  Proof.
    iIntros (HE Hdecode Hvpc Hinc Hne) "(#Hctx & Hj & HPC & Hmem & Hs & Hd)".
    iDestruct (spec_map_of_regs_3 with "HPC Hd Hs") as "[Hmap (%&%&%)]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto.
      iModIntro. iFrame.
    - incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma step_ClearTag_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w src wn ws :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag cnull src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → src ≠ cnull →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ wn ∗ src ↣ᵣ ws
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ WInt 0%Z ∗ src ↣ᵣ ws.
  Proof.
    iIntros (HE Hdecode Hvpc Hinc Hne) "(#Hctx & Hj & HPC & Hmem & Hd & Hs)".
    iDestruct (spec_map_of_regs_3 with "HPC Hd Hs") as "[Hmap (%&%&%)]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC cnull) // insert_insert_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto.
      iModIntro. iFrame.
    - incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma step_ClearTag_PC_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w wn :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag cnull PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ wn
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ WInt 0%Z.
  Proof.
    iIntros (HE Hdecode Hvpc Hinc) "(#Hctx & Hj & HPC & Hmem & Hn)".
    iDestruct (spec_map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto.
      iModIntro. iFrame.
    - incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma step_ClearTag_cnull_toPC E pc_p pc_g pc_b pc_e pc_a w wn :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag PC cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ wn
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗ cnull ↣ᵣ wn.
  Proof.
    iIntros (HE Hdecode Hvpc) "(#Hctx & Hj & HPC & Hmem & Hn)".
    iDestruct (spec_map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
    - simplify_eq. iDestruct (spec_regs_of_map_2 with "Hmap") as "[HPC Hn]"; eauto.
      iModIntro. iFrame.
  Qed.

  Lemma step_ClearTag_toPC_failure E pc_p pc_g pc_b pc_e pc_a w src ws :
    ↑specN ⊆ E →
    decodeInstrW w = ClearTag PC src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap ws = false →
    src ≠ cnull →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↣ₐ w ∗ src ↣ᵣ ws
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
    iIntros (HE Hdecode Hvpc Hcap Hne) "(#Hctx & Hj & HPC & Hmem & Hsrc)".
    iDestruct (spec_map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iMod (step_ClearTag with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - destruct ws as [| [] | |]; cbn in Hcap; try done;
        incrementPC_inv; simplify_map_eq.
    - by iModIntro; iFrame.
  Qed.

End spec_rules.
