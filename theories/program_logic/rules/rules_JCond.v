From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

(** The conditional jumps, which differ only by their comparison
    [jcond_test]. *)
Definition is_JCond (i : instr) (off arg1 arg2 : Z + RegName) :=
  i = Jeq off arg1 arg2 ∨
  i = Jne off arg1 arg2 ∨
  i = Jlt off arg1 arg2 ∨
  i = Jle off arg1 arg2.

(* Hints to automate proofs of is_JCond *)
Lemma is_JCond_Jeq off arg1 arg2 : is_JCond (Jeq off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jne off arg1 arg2 : is_JCond (Jne off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jlt off arg1 arg2 : is_JCond (Jlt off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jle off arg1 arg2 : is_JCond (Jle off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.

#[export] Hint Resolve is_JCond_Jeq : core.
#[export] Hint Resolve is_JCond_Jne : core.
#[export] Hint Resolve is_JCond_Jlt : core.
#[export] Hint Resolve is_JCond_Jle : core.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {CL : CritLink Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  Lemma operands_of_is_JCond i off arg1 arg2 :
    is_JCond i off arg1 arg2 →
    operands_of i = regs_of_argument off ∪ regs_of_argument arg1 ∪ regs_of_argument arg2.
  Proof. intros HH. destruct_or! HH; subst i; reflexivity. Qed.

  Lemma exec_opt_is_JCond i off arg1 arg2 p φ :
    is_JCond i off arg1 arg2 →
    exec_opt i p φ = exec_jcond (jcond_test i) off arg1 arg2 φ.
  Proof. intros HH. destruct_or! HH; subst i; reflexivity. Qed.

  Inductive JCond_failure (i : instr) (lpc : LWord) (regs : LReg) (off r1 r2 : Z + RegName) :=
  | JCond_fail_PC_overflow_next n1 n2 :
      lz_of_argument regs r1 = Some n1 →
      lz_of_argument regs r2 = Some n2 →
      jcond_test i n1 n2 = false →
      incrementPC lpc = None →
      JCond_failure i lpc regs off r1 r2
  | JCond_fail_PC_overflow_jmp n1 n2 imm :
      lz_of_argument regs r1 = Some n1 →
      lz_of_argument regs r2 = Some n2 →
      jcond_test i n1 n2 = true →
      lz_of_argument regs off = Some imm →
      incrementPC_gen lpc imm = None →
      JCond_failure i lpc regs off r1 r2.

  Inductive JCond_spec (i : instr) (lpc : LWord) (regs : LReg) (off r1 r2 : Z + RegName) :
    LWord → griotte_lang.val → Prop :=
  | JCond_spec_success_next lpc' n1 n2 :
      lz_of_argument regs r1 = Some n1 →
      lz_of_argument regs r2 = Some n2 →
      jcond_test i n1 n2 = false →
      incrementPC lpc = Some lpc' →
      JCond_spec i lpc regs off r1 r2 lpc' NextIV
  | JCond_spec_success_jmp lpc' n1 n2 imm :
      lz_of_argument regs r1 = Some n1 →
      lz_of_argument regs r2 = Some n2 →
      jcond_test i n1 n2 = true →
      lz_of_argument regs off = Some imm →
      incrementPC_gen lpc imm = Some lpc' →
      JCond_spec i lpc regs off r1 r2 lpc' NextIV
  | JCond_spec_failure :
      JCond_failure i lpc regs off r1 r2 →
      JCond_spec i lpc regs off r1 r2 lpc FaultedV.

  Lemma wp_JCond Ep i pc_p pc_g pc_b pc_e pc_a pc_π w off arg1 arg2 regs dq :
    decodeInstrW w.(lw) = i →
    is_JCond i off arg1 arg2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of i ⊆ dom regs →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ JCond_spec i (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs off arg1 arg2 lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hdecode /exec in Hstep.
    rewrite /regs_of in Dregs.
    erewrite operands_of_is_JCond in Dregs; eauto.
    destruct (lz_of_argument_dom regs arg1) as [n1 Hn1].
    { eapply arg_owned_of_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
    apply (lz_of_argument_incl _ _ r _ _ Hregs) in Hn1 as Hn1'.
    destruct (lz_of_argument_dom regs arg2) as [n2 Hn2].
    { eapply arg_owned_of_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
    apply (lz_of_argument_incl _ _ r _ _ Hregs) in Hn2 as Hn2'.
    set (φc := (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) in Hstep.
    rewrite (exec_opt_is_JCond _ _ _ _ _ _ Hi) /exec_jcond /= Hn1' Hn2' /= in Hstep.
    destruct (jcond_test i n1 n2) eqn:Htest.
    - destruct (lz_of_argument_dom regs off) as [imm Himm].
      { eapply arg_owned_of_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
      apply (lz_of_argument_incl _ _ r _ _ Hregs) in Himm as Himm'.
      rewrite Himm' /= in Hstep.
      iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ imm _ _ _
        (λ lpc' retv, JCond_spec i _ regs off arg1 arg2 lpc' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]"); first done; first done.
      { intros. by eapply JCond_spec_success_jmp. }
      { intros. constructor. by eapply JCond_fail_PC_overflow_jmp. }
      iIntros (lpc' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
    - iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
        (λ lpc' retv, JCond_spec i _ regs off arg1 arg2 lpc' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]"); first done; first done.
      { intros. by eapply JCond_spec_success_next. }
      { intros. constructor. by eapply JCond_fail_PC_overflow_next. }
      iIntros (lpc' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (** A taken jump whose target is an address has one outcome. *)
  Lemma JCond_spec_jmp i lpc regs off arg1 arg2 lpc' retv n1 n2 imm lpc0 :
    lz_of_argument regs arg1 = Some n1 →
    lz_of_argument regs arg2 = Some n2 →
    jcond_test i n1 n2 = true →
    lz_of_argument regs off = Some imm →
    incrementPC_gen lpc imm = Some lpc0 →
    JCond_spec i lpc regs off arg1 arg2 lpc' retv →
    retv = NextIV ∧ lpc' = lpc0.
  Proof.
    intros H1 H2 Ht Himm Hinc Hspec.
    destruct Hspec as [lpc'' n1' n2' H1' H2' Ht' Hinc'
                      | lpc'' n1' n2' imm' H1' H2' Ht' Himm' Hinc'
                      | Hfail].
    - rewrite H1 in H1'. rewrite H2 in H2'. simplify_eq. congruence.
    - rewrite Himm in Himm'. simplify_eq. done.
    - destruct Hfail as [n1' n2' H1' H2' Ht' Hinc' | n1' n2' imm' H1' H2' Ht' Himm' Hinc'].
      + rewrite H1 in H1'. rewrite H2 in H2'. simplify_eq. congruence.
      + rewrite Himm in Himm'. simplify_eq; congruence.
  Qed.

  (** A jump not taken whose PC increments has one outcome. *)
  Lemma JCond_spec_next i lpc regs off arg1 arg2 lpc' retv n1 n2 lpc0 :
    lz_of_argument regs arg1 = Some n1 →
    lz_of_argument regs arg2 = Some n2 →
    jcond_test i n1 n2 = false →
    incrementPC lpc = Some lpc0 →
    JCond_spec i lpc regs off arg1 arg2 lpc' retv →
    retv = NextIV ∧ lpc' = lpc0.
  Proof.
    intros H1 H2 Ht Hinc Hspec.
    destruct Hspec as [lpc'' n1' n2' H1' H2' Ht' Hinc'
                      | lpc'' n1' n2' imm' H1' H2' Ht' Himm' Hinc'
                      | Hfail].
    - simplify_eq. done.
    - rewrite H1 in H1'. rewrite H2 in H2'. simplify_eq. congruence.
    - destruct Hfail as [n1' n2' H1' H2' Ht' Hinc' | n1' n2' imm' H1' H2' Ht' Himm' Hinc'].
      + congruence.
      + rewrite H1 in H1'. rewrite H2 in H2'. simplify_eq. congruence.
  Qed.

  (** The map-form rules of a taken jump and of a jump not taken, from which
      the register-shaped ones follow. *)
  Lemma wp_jcond_jmp E i pc_p pc_g pc_b pc_e pc_a pc_π w off arg1 arg2 regs n1 n2 imm lpc' dq :
    decodeInstrW w.(lw) = i →
    is_JCond i off arg1 arg2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (regs_of_argument off ∪ regs_of_argument arg1 ∪ regs_of_argument arg2) ∖ {[ cnull ]} ⊆ dom regs →
    lz_of_argument regs arg1 = Some n1 →
    lz_of_argument regs arg2 = Some n2 →
    jcond_test i n1 n2 = true →
    lz_of_argument regs off = Some imm →
    incrementPC_gen (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) imm = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Hdom H1 H2 Ht Himm Hinc φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_JCond with "[$HPC $Hpc_a $Hmap]"); eauto.
    { rewrite /regs_of. by erewrite operands_of_is_JCond. }
    iIntros "!>" (lpc0 retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct (JCond_spec_jmp _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Ht Himm Hinc Hspec) as (-> & ->).
    iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_jcond_next E i pc_p pc_g pc_b pc_e pc_a pc_π w off arg1 arg2 regs n1 n2 lpc' dq :
    decodeInstrW w.(lw) = i →
    is_JCond i off arg1 arg2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (regs_of_argument off ∪ regs_of_argument arg1 ∪ regs_of_argument arg2) ∖ {[ cnull ]} ⊆ dom regs →
    lz_of_argument regs arg1 = Some n1 →
    lz_of_argument regs arg2 = Some n2 →
    jcond_test i n1 n2 = false →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Hdom H1 H2 Ht Hinc φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_JCond with "[$HPC $Hpc_a $Hmap]"); eauto.
    { rewrite /regs_of. by erewrite operands_of_is_JCond. }
    iIntros "!>" (lpc0 retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct (JCond_spec_next _ _ _ _ _ _ _ _ _ _ _ H1 H2 Ht Hinc Hspec) as (-> & ->).
    iApply "Hφ". by iFrame.
  Qed.

  (* Register-shaped rules: an immediate offset, the test on the addresses
     of the operand words. *)

  Lemma wp_jcond_success_jmp_r_r E ins pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm r1 r2 w1 w2 dq :
    decodeInstrW w.(lw) = ins →
    is_JCond ins (inl imm) (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jcond_test ins (get_a w1.(lw)) (get_a w2.(lw)) = true →
    (pc_a + imm)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ w1 ∗
        r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Ht Hpca' Hcnull1 Hcnull2 ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (wp_jcond_jmp with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try (by apply incrementPC_gen_add); eauto.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jcond_success_next_r_r E ins pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm r1 r2 w1 w2 dq :
    decodeInstrW w.(lw) = ins →
    is_JCond ins (inl imm) (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jcond_test ins (get_a w1.(lw)) (get_a w2.(lw)) = false →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ w1 ∗
        r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Ht Hpca' Hcnull1 Hcnull2 ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (wp_jcond_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; eauto.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jcond_success_jmp_r_r_same E ins pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm r wr dq :
    decodeInstrW w.(lw) = ins →
    is_JCond ins (inl imm) (inr r) (inr r) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jcond_test ins (get_a wr.(lw)) (get_a wr.(lw)) = true →
    (pc_a + imm)%a = Some pc_a' →
    r ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r ↦ᵣ wr }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Ht Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_jcond_jmp with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try (by apply incrementPC_gen_add); eauto.
    iIntros "!> (HPC & Hpc_a & Hmap)". iDestruct (regs_of_map_1 with "Hmap") as "Hr".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jcond_success_next_r_r_same E ins pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm r wr dq :
    decodeInstrW w.(lw) = ins →
    is_JCond ins (inl imm) (inr r) (inr r) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jcond_test ins (get_a wr.(lw)) (get_a wr.(lw)) = false →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r ↦ᵣ wr }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Ht Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_jcond_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; eauto.
    iIntros "!> (HPC & Hpc_a & Hmap)". iDestruct (regs_of_map_1 with "Hmap") as "Hr".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jcond_success_jmp_r_z E ins pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm r1 w1 n2 dq :
    decodeInstrW w.(lw) = ins →
    is_JCond ins (inl imm) (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jcond_test ins (get_a w1.(lw)) n2 = true →
    (pc_a + imm)%a = Some pc_a' →
    r1 ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Ht Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_jcond_jmp with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try (by apply incrementPC_gen_add); eauto.
    iIntros "!> (HPC & Hpc_a & Hmap)". iDestruct (regs_of_map_1 with "Hmap") as "Hr".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jcond_success_next_r_z E ins pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm r1 w1 n2 dq :
    decodeInstrW w.(lw) = ins →
    is_JCond ins (inl imm) (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jcond_test ins (get_a w1.(lw)) n2 = false →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Ht Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_jcond_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; eauto.
    iIntros "!> (HPC & Hpc_a & Hmap)". iDestruct (regs_of_map_1 with "Hmap") as "Hr".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jcond_success_jmp_z_r E ins pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm n1 r2 w2 dq :
    decodeInstrW w.(lw) = ins →
    is_JCond ins (inl imm) (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jcond_test ins n1 (get_a w2.(lw)) = true →
    (pc_a + imm)%a = Some pc_a' →
    r2 ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Ht Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_jcond_jmp with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try (by apply incrementPC_gen_add); eauto.
    iIntros "!> (HPC & Hpc_a & Hmap)". iDestruct (regs_of_map_1 with "Hmap") as "Hr".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jcond_success_next_z_r E ins pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm n1 r2 w2 dq :
    decodeInstrW w.(lw) = ins →
    is_JCond ins (inl imm) (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jcond_test ins n1 (get_a w2.(lw)) = false →
    (pc_a + 1)%a = Some pc_a' →
    r2 ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Ht Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_jcond_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side; eauto.
    iIntros "!> (HPC & Hpc_a & Hmap)". iDestruct (regs_of_map_1 with "Hmap") as "Hr".
    iApply "Hφ". iFrame.
  Qed.

  (* [Jne off r 0] jumps on a word whose address is not zero, [Jeq off r 0] on
     a word whose address is zero. *)

  Lemma wp_jnez_success_jmp_z E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond dq :
    decodeInstrW w.(lw) = Jne (inl imm) (inr rcond) (inl 0%Z) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    nonZero wcond.(lw) = true →
    (pc_a + imm)%a = Some pc_a' →
    rcond ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        rcond ↦ᵣ wcond }}}.
  Proof.
    intros Hdecode Hvpc Hnz Hpca' Hcnull.
    eapply wp_jcond_success_jmp_r_z; eauto.
  Qed.

  Lemma wp_jnez_success_next_z E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond dq :
    decodeInstrW w.(lw) = Jne (inl imm) (inr rcond) (inl 0%Z) →
    IsLInt wcond 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        rcond ↦ᵣ wcond }}}.
  Proof.
    iIntros (Hdecode Hwcond Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    destruct (IsLInt_inv _ _ Hwcond) as [πcond ->].
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_jcond_next _ _ _ _ _ _ _ _ _ _ _ _ _ 0%Z 0%Z with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; eauto.
    { apply lz_of_argument_singleton_zero. }
    iIntros "!> (HPC & Hpc_a & Hmap)". iDestruct (regs_of_map_1 with "Hmap") as "Hr".
    iApply "Hφ". iFrame.
  Qed.

  (** [Jne off r 0] falls through on any word whose address is zero. *)
  Lemma wp_jnez_success_next_any E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond dq :
    decodeInstrW w.(lw) = Jne (inl imm) (inr rcond) (inl 0%Z) →
    nonZero wcond.(lw) = false →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rcond ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        rcond ↦ᵣ wcond }}}.
  Proof.
    intros Hdecode Hnz Hvpc Hpca' Hcnull.
    eapply wp_jcond_success_next_r_z; eauto.
  Qed.

  Lemma wp_jeqz_success_jmp_z E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond dq :
    decodeInstrW w.(lw) = Jeq (inl imm) (inr rcond) (inl 0%Z) →
    IsLInt wcond 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a' →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        rcond ↦ᵣ wcond }}}.
  Proof.
    iIntros (Hdecode Hwcond Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    destruct (IsLInt_inv _ _ Hwcond) as [πcond ->].
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_jcond_jmp _ _ _ _ _ _ _ _ _ _ _ _ _ 0%Z 0%Z with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try (by apply incrementPC_gen_add); eauto.
    { apply lz_of_argument_singleton_zero. }
    iIntros "!> (HPC & Hpc_a & Hmap)". iDestruct (regs_of_map_1 with "Hmap") as "Hr".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jeqz_success_next_z E rcond pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm wcond dq :
    decodeInstrW w.(lw) = Jeq (inl imm) (inr rcond) (inl 0%Z) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    nonZero wcond.(lw) = true →
    (pc_a + 1)%a = Some pc_a' →
    rcond ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rcond ↦ᵣ wcond }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        rcond ↦ᵣ wcond }}}.
  Proof.
    intros Hdecode Hvpc Hnz Hpca' Hcnull.
    eapply wp_jcond_success_next_r_z; eauto.
    rewrite /jcond_test. by apply negb_true_iff.
  Qed.

End griotte_lang_rules.
