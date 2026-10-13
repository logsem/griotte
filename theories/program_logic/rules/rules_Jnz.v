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

  Inductive Jnz_failure (lpc : LWord) (regs : LReg) (rimm: Z + RegName) (rcond : RegName) :=
  | Jnz_fail_PC_overflow_next cond:
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = false →
      incrementPC lpc = None →
      Jnz_failure lpc regs rimm rcond
  | Jnz_fail_PC_overflow_jmp imm cond:
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = true →
      lz_of_argument regs rimm = Some imm →
      incrementPC_gen lpc imm = None →
      Jnz_failure lpc regs rimm rcond
  | Jnz_fail_no_imm cond:
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = true →
      lz_of_argument regs rimm = None →
      Jnz_failure lpc regs rimm rcond.

  Inductive Jnz_spec (lpc : LWord) (regs : LReg) (rimm: Z + RegName) (rcond : RegName) :
    LWord → griotte_lang.val → Prop :=
  | Jnz_spec_success_next lpc' cond :
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = false →
      incrementPC lpc = Some lpc' →
      Jnz_spec lpc regs rimm rcond lpc' NextIV
  | Jnz_spec_success_jmp lpc' imm cond :
      regs !!ₗ rcond = Some cond →
      nonZero cond.(lw) = true →
      lz_of_argument regs rimm = Some imm →
      incrementPC_gen lpc imm = Some lpc' →
      Jnz_spec lpc regs rimm rcond lpc' NextIV
  | Jnz_spec_failure:
      Jnz_failure lpc regs rimm rcond →
      Jnz_spec lpc regs rimm rcond lpc FailedV.

  Lemma wp_Jnz Ep pc_p pc_g pc_b pc_e pc_a pc_π w rimm rcond regs dq :
    decodeInstrW w.(lw) = Jnz rimm rcond ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jnz rimm rcond) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ Jnz_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs rimm rcond lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hpc_a Hmap".
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rcond) as [wrcond [H'rcond _]]; first by set_solver+.
    pose proof (llookup_reg_incl _ _ _ _ Hregs H'rcond) as Hrcond.
    set (φc := (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) in Hstep.
    destruct (nonZero wrcond.(lw)) eqn:Hnz.
    - destruct (lz_of_argument regs rimm) as [imm|] eqn:Himm.
      2: { assert (exec_opt (Jnz rimm rcond) pc_p φc = None) as HH.
           { cbn. rewrite Hrcond /= Hnz.
             rewrite (lz_of_argument_None regs r); [done|done| |done].
             intros x ->. apply Dregs. set_solver+. }
           rewrite HH in Hstep. simplify_eq.
           iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
           iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro.
           constructor. by eapply Jnz_fail_no_imm. }
      assert (exec_opt (Jnz rimm rcond) pc_p φc = updatePC_gen φc imm) as HH.
      { cbn. rewrite Hrcond /= Hnz.
        by rewrite (lz_of_argument_incl regs r _ imm). }
      rewrite HH in Hstep.
      iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ imm _ _ _
        (λ lpc' retv, Jnz_spec _ regs rimm rcond lpc' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]"); first done; first done.
      { intros. by eapply Jnz_spec_success_jmp. }
      { intros. constructor. by eapply Jnz_fail_PC_overflow_jmp. }
      iIntros (lpc' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
    - assert (exec_opt (Jnz rimm rcond) pc_p φc = updatePC_gen φc 1) as HH.
      { cbn. by rewrite Hrcond /= Hnz. }
      rewrite HH in Hstep.
      iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
        (λ lpc' retv, Jnz_spec _ regs rimm rcond lpc' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]"); first done; first done.
      { intros. by eapply Jnz_spec_success_next. }
      { intros. constructor. by eapply Jnz_fail_PC_overflow_next. }
      iIntros (lpc' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_jnz_success_jmp_z E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond dq :
    decodeInstrW w.(lw) = Jnz (inl imm) rcond →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    wcond.(lw) ≠ WInt 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rcond ↦ᵣ wcond
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rcond ↦ᵣ wcond
          }}}.
  Proof.
    iIntros (Hinstr Hvpc Hne Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrcond) Hφ".
    iDestruct (map_of_regs_1 with "Hrcond") as "Hmap".
    iApply (wp_Jnz with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+. }
    iNext. iIntros (lpc' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero wcond.(lw) = true).
    { unfold nonZero, Z.eqb in *.
      destruct wcond as [wc πc]; cbn in *. destruct wc; auto.
      repeat case_match; try congruence; by cbn.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_lmap_eq; congruence. }
    { iApply "Hφ". iFrame. simplify_lmap_eq.
      try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      all: try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  Lemma wp_jnz_success_jmp_reg E rcond rimm pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wimm imm wcond dq :
    decodeInstrW w.(lw) = Jnz (inr rimm) rcond →
    IsLInt wimm imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    wcond.(lw) ≠ WInt 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->
    rimm ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rimm ↦ᵣ wimm
        ∗ ▷ rcond ↦ᵣ wcond
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rimm ↦ᵣ wimm
          ∗ rcond ↦ᵣ wcond
          }}}.
  Proof.
    iIntros (Hinstr Hwimm Hvpc Hne Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hrimm & >Hrcond) Hφ".
    destruct (IsLInt_inv _ _ Hwimm) as [πimm ->].
    iDestruct (map_of_regs_2 with "Hrimm Hrcond") as "[Hmap %]".
    iApply (wp_Jnz with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+. }
    iNext. iIntros (lpc' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero wcond.(lw) = true).
    { unfold nonZero, Z.eqb in *.
      destruct wcond as [wc πc]; cbn in *. destruct wc; auto.
      repeat case_match; try congruence; by cbn.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_lmap_eq; congruence. }
    { iApply "Hφ". iFrame. simplify_lmap_eq.
      try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      all: try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  Lemma wp_jnz_success_jmp_same E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wcond imm dq :
    decodeInstrW w.(lw) = Jnz (inr rcond) rcond →
    IsLInt wcond imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    imm ≠ 0%Z →
    (pc_a + imm)%a = Some pc_a' ->
    rcond ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rcond ↦ᵣ wcond
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
        ∗ ▷ rcond ↦ᵣ wcond
          }}}.
  Proof.
    iIntros (Hinstr Hwcond Hvpc Hne Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrcond) Hφ".
    destruct (IsLInt_inv _ _ Hwcond) as [πcond ->].
    iDestruct (map_of_regs_1 with "Hrcond") as "Hmap".
    iApply (wp_Jnz with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+. }
    iNext. iIntros (lpc' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    assert (nonZero (WInt imm) = true).
    { unfold nonZero, Z.eqb in *.
      destruct imm; auto.
    }

    destruct Hspec as [ | | Hfail ].
    { exfalso; simplify_lmap_eq; congruence. }
    { iApply "Hφ". iFrame. simplify_lmap_eq.
      try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      all: try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  Lemma wp_jnz_success_next_z E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond dq :
    decodeInstrW w.(lw) = Jnz (inl imm) rcond →
    IsLInt wcond 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rcond ↦ᵣ wcond }}}.
  Proof.
    iIntros (Hinstr Hwcond Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hrcond) Hφ".
    destruct (IsLInt_inv _ _ Hwcond) as [πcond ->].
    iDestruct (map_of_regs_1 with "Hrcond") as "Hmap".
    iApply (wp_Jnz with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+. }
    iNext. iIntros (lpc' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | Hfail ]; try incrementPC_inv; simplify_lmap_eq; eauto.
    { iApply "Hφ". iFrame.
      iRegsMap "Hmap"; eauto; iFrame. }
    { destruct (decide (rcond = cnull)); cbn in *; done. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      all: destruct (decide (rcond = cnull)); cbn in *; try done.
      all: try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence.
    }
  Qed.

  (* TODO ideally, I would like to not require the register rimm *)
  Lemma wp_jnz_success_next_reg E rimm rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wimm wcond dq :
    decodeInstrW w.(lw) = Jnz (inr rimm) rcond →
    IsLInt wcond 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rimm ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rimm ↦ᵣ wimm
        ∗ ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rimm ↦ᵣ wimm
          ∗ rcond ↦ᵣ wcond }}}.
  Proof.
    iIntros (Hinstr Hwcond Hvpc Hpc_a' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrimm & >Hrcond) Hφ".
    destruct (IsLInt_inv _ _ Hwcond) as [πcond ->].
    iDestruct (map_of_regs_2 with "Hrcond Hrimm") as "[Hmap %]".
    iApply (wp_Jnz with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+. }
    iNext. iIntros (lpc' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | Hfail ]; try incrementPC_inv; simplify_lmap_eq; eauto.
    { iApply "Hφ". iFrame.
      iRegsMap "Hmap"; eauto; iFrame. }
    { destruct (decide (rcond = cnull)); cbn in *; done. }
    { destruct Hfail; simplify_lmap_eq; eauto; try congruence.
      all: destruct (decide (rcond = cnull)); cbn in *; try done.
      all: try (try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_lmap_eq; eauto; congruence).
    }
  Qed.

End griotte_lang_rules.
