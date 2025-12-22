From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Export check_no_overlap.

Section Check_No_Overlap_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .

  Lemma check_no_overlap_spec
    (rsrc1 rsrc2 r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (w1 w2 : Word)
    (p1 : Perm) (g1 : Locality) (b1 e1 a1 : Addr)
    (p2 : Perm) (g2 : Locality) (b2 e2 a2 : Addr)
    (φ : language.val cap_lang → iPropI Σ) :

    let check_no_overlap := (check_no_overlap_instrs rsrc1 rsrc2 r1 r2) in
    let a_last := (pc_a ^+ length check_no_overlap)%a in
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a a_last →

    ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rsrc1 ↦ᵣ (WCap p1 g1 b1 e1 a1)
    ∗ ▷ rsrc2 ↦ᵣ (WCap p2 g2 b2 e2 a2)
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a check_no_overlap
    ∗ ▷ ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e a_last
          ∗ rsrc1 ↦ᵣ (WCap p1 g1 b1 e1 a1)
          ∗ rsrc2 ↦ᵣ (WCap p2 g2 b2 e2 a2)
          ∗ r1 ↦ᵣ WInt 0%Z
          ∗ r2 ↦ᵣ WInt 0%Z
          ∗ ⌜ (finz.seq_between b1 e1) ## (finz.seq_between b2 e2) ⌝
          ∗ codefrag pc_a check_no_overlap
            -∗ WP Seq (Instr Executable) {{ φ }}
        )
    ∗ ▷ φ FailedV
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros check_no_overlap a_last ; subst check_no_overlap a_last.
    iIntros (Hvpc Hcont)
      "(>HPC & >Hrsrc1 & >Hrsrc2 & >Hr1 & >Hr2 & >Hprog & Hφ & Hfailed)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    codefrag_facts "Hprog".
    rename H into HcontRegion; clear H0.
    cbn.

    iInstr "Hprog".
    iInstr "Hprog".
    iInstr "Hprog".
    destruct (b1 <? b2)%Z eqn:H_b1_b2; iEval (cbn) in "Hr1".
    - (* b1 < b2 *)
      iInstr "Hprog".
      iInstr "Hprog".
      iInstr "Hprog".
      iInstr "Hprog".
      iInstr "Hprog".
      destruct ( (e1 - 1 <? b2)%Z ) eqn:H_e1_b2 ; iEval (cbn) in "Hr1".
      + iInstr "Hprog".
        iInstr "Hprog".
        iInstr "Hprog".
        iInstr "Hprog".
        iApply "Hφ"; iFrame.
        iPureIntro.
        intros a Ha Ha'.
        rewrite !elem_of_finz_seq_between in Ha, Ha'.
        solve_addr.
      + iInstr "Hprog".
        iInstr "Hprog".
        wp_end; iApply "Hfailed".
    - (* b2 <= b1 *)
      iInstr "Hprog".
      iInstr "Hprog".
      iInstr "Hprog".
      iInstr "Hprog".
      iInstr "Hprog".
      destruct ( (e2 - 1 <? b1)%Z ) eqn:H_e2_b1 ; iEval (cbn) in "Hr1".
      + iInstr "Hprog".
        iInstr "Hprog".
        iInstr "Hprog".
        iInstr "Hprog".
        iApply "Hφ"; iFrame.
        iPureIntro.
        intros a Ha Ha'.
        rewrite !elem_of_finz_seq_between in Ha, Ha'.
        solve_addr.
      + iInstr "Hprog".
        iInstr "Hprog".
        wp_end; iApply "Hfailed".
  Qed.

End Check_No_Overlap_spec.
