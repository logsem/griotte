From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  Inductive Jnz_failure (regs : LReg) (rimm: Z + RegName) (rcond : RegName) :=
  | Jnz_fail_PC_overflow_next cond:
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = false →
      incrementPC regs = None →
      Jnz_failure regs rimm rcond
  | Jnz_fail_PC_overflow_jmp imm cond:
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = true →
      lz_of_argument regs rimm = Some imm →
      incrementPC_gen regs imm = None →
      Jnz_failure regs rimm rcond
  | Jnz_fail_no_imm cond:
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = true →
      lz_of_argument regs rimm = None →
      Jnz_failure regs rimm rcond.

  Inductive Jnz_spec (regs : LReg) (rimm: Z + RegName) (rcond : RegName) : LReg → griotte_lang.val → Prop :=
  | Jnz_spec_success_next regs' cond :
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = false →
      incrementPC regs = Some regs' →
      Jnz_spec regs rimm rcond regs' NextIV
  | Jnz_spec_success_jmp regs' imm cond :
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = true →
      lz_of_argument regs rimm = Some imm →
      incrementPC_gen regs imm = Some regs' →
      Jnz_spec regs rimm rcond regs' NextIV
  | Jnz_spec_failure:
      Jnz_failure regs rimm rcond →
      Jnz_spec regs rimm rcond regs FailedV.

  Lemma wp_Jnz Ep pc_p pc_g pc_b pc_e pc_a pc_π w rimm rcond regs :
    decodeInstrW w.(lw) = Jnz rimm rcond ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Jnz rimm rcond) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Jnz_spec regs rimm rcond regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rcond) as [wrcond [H'rcond _]]; first by set_solver+.
    pose proof (llookup_reg_incl _ _ _ _ Hregs H'rcond) as Hrcond.
    rewrite /exec /= Hrcond /= in Hstep.
    destruct (nonZero wrcond.(lw)) eqn:Hnz; cbn in Hstep.
    - destruct (lz_of_argument regs rimm) as [imm|] eqn:Himm.
      2: { rewrite (lz_of_argument_None regs r) /= in Hstep; [|done| |done].
           2: { intros x ->. apply Dregs. set_solver+. }
           simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
           iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
           constructor. by eapply Jnz_fail_no_imm. }
      rewrite (lz_of_argument_incl regs r _ imm) /= in Hstep; [|done|done].
      destruct (incrementPC_gen regs imm) as [regs'|] eqn:Hi.
      + destruct (erasure_incrementPC_gen _ _ _ _ _ _ _ _ _ _ _ Her Hlregs Hi)
          as (t & p & g & b & e & a & a' & π & HPC1 & Ha' & -> & Hu & Her2).
        rewrite Hu in Hstep. injection Hstep as <- <-.
        rewrite HPC1 in HPC. simplify_eq.
        iMod (gen_heap_update_inSepM _ _ PC (WCap true pc_p pc_g pc_b pc_e a' @@? pc_π)
          with "Hr Hmap") as "[Hr Hmap]"; first by eexists.
        iModIntro. iSplitR "Hφ Hmap Hpc_a".
        * iExists _, lmem, R, C. iFrame. iPureIntro. exact Her2.
        * iApply "Hφ". iFrame. iPureIntro. eapply Jnz_spec_success_jmp; eauto.
      + rewrite (incrementPC_gen_fail_updatePC_gen regs r sr m st) in Hstep; [|done|by eexists|done].
        simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
        iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
        constructor. by eapply Jnz_fail_PC_overflow_jmp.
    - destruct (incrementPC regs) as [regs'|] eqn:Hi.
      + destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ Her Hlregs Hi)
          as (t & p & g & b & e & a & a' & π & HPC1 & Ha' & -> & Hu & Her2).
        rewrite Hu in Hstep. injection Hstep as <- <-.
        rewrite HPC1 in HPC. simplify_eq.
        iMod (gen_heap_update_inSepM _ _ PC (WCap true pc_p pc_g pc_b pc_e a' @@? pc_π)
          with "Hr Hmap") as "[Hr Hmap]"; first by eexists.
        iModIntro. iSplitR "Hφ Hmap Hpc_a".
        * iExists _, lmem, R, C. iFrame. iPureIntro. exact Her2.
        * iApply "Hφ". iFrame. iPureIntro. eapply Jnz_spec_success_next; eauto.
      + rewrite (incrementPC_fail_updatePC regs r sr m st) in Hstep; [|done|by eexists|done].
        simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
        iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
        constructor. by eapply Jnz_fail_PC_overflow_next.
  Qed.

  Lemma wp_jnz_success_jmp_z E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond :
    decodeInstrW w.(lw) = Jnz (inl imm) rcond →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    wcond.(lw) ≠ WInt 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rcond ↦ᵣ wcond
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ rcond ↦ᵣ wcond
          }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrcond) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hrcond") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero wcond.(lw) = true).
    { unfold nonZero, Z.eqb in *.
      destruct wcond as [wc πc]; cbn in *. destruct wc; auto.
      repeat case_match; try congruence; by cbn.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_lmap_eq; congruence. }
    { iApply "Hφ". iFrame. simplify_lmap_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq.
      rewrite insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  Lemma wp_jnz_success_jmp_reg E rcond rimm pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wimm imm wcond :
    decodeInstrW w.(lw) = Jnz (inr rimm) rcond →
    IsLInt wimm imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    wcond.(lw) ≠ WInt 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->
    rimm ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rimm ↦ᵣ wimm
        ∗ ▷ rcond ↦ᵣ wcond
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ rimm ↦ᵣ wimm
          ∗ rcond ↦ᵣ wcond
          }}}.
  Proof.
    iIntros (Hinstr Hwimm Hvpc Hne Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hrimm & >Hrcond) Hφ".
    destruct (IsLInt_inv _ _ Hwimm) as [πimm ->].
    iDestruct (map_of_regs_3 with "HPC Hrimm Hrcond") as "[Hmap (%&%&%)]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero wcond.(lw) = true).
    { unfold nonZero, Z.eqb in *.
      destruct wcond as [wc πc]; cbn in *. destruct wc; auto.
      repeat case_match; try congruence; by cbn.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_lmap_eq; congruence. }
    { iApply "Hφ". iFrame. simplify_lmap_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq.
      rewrite insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  Lemma wp_jnz_success_jmp_same E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wcond imm :
    decodeInstrW w.(lw) = Jnz (inr rcond) rcond →
    IsLInt wcond imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    imm ≠ 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rcond ↦ᵣ wcond
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
        ∗ ▷ rcond ↦ᵣ wcond
          }}}.
  Proof.
    iIntros (Hinstr Hwcond Hvpc Hne Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrcond) Hφ".
    destruct (IsLInt_inv _ _ Hwcond) as [πcond ->].
    iDestruct (map_of_regs_2 with "HPC Hrcond") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero (WInt imm) = true).
    { unfold nonZero, Z.eqb in *.
      destruct imm; auto.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_lmap_eq; congruence. }
    { iApply "Hφ". iFrame. simplify_lmap_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq.
      rewrite insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  Lemma wp_jnz_success_jmpPC_z E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm:
    decodeInstrW w.(lw) = Jnz (inl imm) PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a' ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_lmap_eq; congruence. }
    { iApply "Hφ". iFrame. simplify_lmap_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq.
      rewrite insert_insert_eq.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  Lemma wp_jnz_success_jmpPC_reg E rimm pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wimm imm :
    decodeInstrW w.(lw) = Jnz (inr rimm) PC →
    IsLInt wimm imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a' ->
    rimm ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rimm ↦ᵣ wimm
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ rimm ↦ᵣ wimm
          }}}.
  Proof.
    iIntros (Hinstr Hwimm Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrimm) Hφ".
    destruct (IsLInt_inv _ _ Hwimm) as [πimm ->].
    iDestruct (map_of_regs_2 with "HPC Hrimm") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_lmap_eq; congruence. }
    { iApply "Hφ". iFrame. simplify_lmap_eq.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq.
      rewrite insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  Lemma wp_jnz_success_next_z E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond :
    decodeInstrW w.(lw) = Jnz (inl imm) rcond →
    IsLInt wcond 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ rcond ↦ᵣ wcond }}}.
  Proof.
    iIntros (Hinstr Hwcond Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hrcond) Hφ".
    destruct (IsLInt_inv _ _ Hwcond) as [πcond ->].
    iDestruct (map_of_regs_2 with "HPC Hrcond") as "[Hmap %]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | Hfail ]; try incrementPC_inv; simplify_lmap_eq; eauto.
    { iApply "Hφ". iFrame.
      rewrite insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { destruct (decide (rcond = cnull)); cbn in *; done. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      all: destruct (decide (rcond = cnull)); cbn in *; try done.
      all: incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  (* TODO ideally, I would like to not require the register rimm *)
  Lemma wp_jnz_success_next_reg E rimm rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wimm wcond :
    decodeInstrW w.(lw) = Jnz (inr rimm) rcond →
    IsLInt wcond 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rimm ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rimm ↦ᵣ wimm
        ∗ ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ rimm ↦ᵣ wimm
          ∗ rcond ↦ᵣ wcond }}}.
  Proof.
    iIntros (Hinstr Hwcond Hvpc Hpc_a' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrimm & >Hrcond) Hφ".
    destruct (IsLInt_inv _ _ Hwcond) as [πcond ->].
    iDestruct (map_of_regs_3 with "HPC Hrcond Hrimm") as "[Hmap (%&%&%)]".
    iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | Hfail ]; try incrementPC_inv; simplify_lmap_eq; eauto.
    { iApply "Hφ". iFrame.
      rewrite insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { destruct (decide (rcond = cnull)); cbn in *; done. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      all: destruct (decide (rcond = cnull)); cbn in *; try done.
      all: try (incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence).
    }
  Qed.

End griotte_lang_rules.
