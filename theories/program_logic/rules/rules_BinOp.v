From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import machine_base.

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

  Definition denote (i: instr) (n1 n2: Z): Z :=
    match i with
    | machine_instructions.Add _ _ _ => (n1 + n2)%Z
    | Sub _ _ _ => (n1 - n2)%Z
    | Mul _ _ _ => (n1 * n2)%Z
    | LAnd _ _ _ => (Z.land n1 n2)
    | LOr _ _ _ => (Z.lor n1 n2)
    | LShiftL _ _ _ => (n1 ≪ n2)%Z
    | LShiftR _ _ _ => (n1 ≫ n2)%Z
    | Lt _ _ _ => (Z.b2z (n1 <? n2)%Z)
    | _ => 0%Z
    end.

  Definition is_BinOp (i: instr) (r: RegName) (arg1 arg2: Z + RegName) :=
    i = machine_instructions.Add r arg1 arg2 ∨
    i = Sub r arg1 arg2 ∨
    i = Mul r arg1 arg2 ∨
    i = LAnd r arg1 arg2 ∨
    i = LOr r arg1 arg2 ∨
    i = LShiftL r arg1 arg2 ∨
    i = LShiftR r arg1 arg2 ∨
    i = Lt r arg1 arg2.

  Lemma regs_of_is_BinOp i r arg1 arg2 :
    is_BinOp i r arg1 arg2 →
    regs_of i = {[ r ]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2.
  Proof.
    intros HH. destruct_or! HH; subst i; reflexivity.
  Qed.

  Inductive BinOp_failure (i: instr) (lpc : LWord) (regs : LReg) (dst: RegName) (rv1 rv2: Z + RegName) :=
  | BinOp_fail_incrPC n1 n2:
      lz_of_argument regs rv1 = Some n1 ->
      lz_of_argument regs rv2 = Some n2 ->
      incrementPC lpc = None ->
      BinOp_failure i lpc regs dst rv1 rv2.

  Inductive BinOp_spec (i: instr) (lpc : LWord) (regs : LReg) (dst: RegName) (rv1 rv2: Z + RegName)
    (lpc' : LWord) (regs' : LReg): griotte_lang.val -> Prop :=
  | BinOp_spec_success n1 n2:
      lz_of_argument regs rv1 = Some n1 ->
      lz_of_argument regs rv2 = Some n2 ->
      incrementPC lpc = Some lpc' ->
      regs' = <[ dst := WInt (denote i n1 n2) ]ₗ> regs ->
      BinOp_spec i lpc regs dst rv1 rv2 lpc' regs' NextIV
  | BinOp_spec_failure:
      BinOp_failure i lpc regs dst rv1 rv2 ->
      BinOp_spec i lpc regs dst rv1 rv2 lpc' regs' FailedV.

  Lemma wp_BinOp Ep i pc_p pc_g pc_b pc_e pc_a pc_π w dst arg1 arg2 regs dq :
    decodeInstrW w.(lw) = i →
    is_BinOp i dst arg1 arg2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of i ⊆ dom regs →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ BinOp_spec (decodeInstrW w.(lw)) (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst arg1 arg2 lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
          pc_a ↦ₐ{dq} w ∗
          [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    rewrite Hdecode /exec in Hstep. rewrite Hdecode.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    erewrite regs_of_is_BinOp in Hri, Dregs; eauto.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.
    destruct (lz_of_argument_dom regs arg1) as [n1 Hn1].
    { intros x ->. apply Dregs. rewrite /regs_of_argument. set_solver+. }
    apply (lz_of_argument_incl _ _ r _ _ Hregs) in Hn1 as Hn1'.
    destruct (lz_of_argument_dom regs arg2) as [n2 Hn2].
    { intros x ->. apply Dregs. rewrite /regs_of_argument. set_solver+. }
    apply (lz_of_argument_incl _ _ r _ _ Hregs) in Hn2 as Hn2'.

    assert (exec_opt i pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) = updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst (WInt (denote i n1 n2)))) as HH.
    { all: destruct_or! Hinstr; rewrite Hinstr /= /update_reg /= in Hstep |- *; auto.
      all: by rewrite Hn1' Hn2'; cbn. }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt (denote i n1 n2))) _ _ _ _
      (λ lpc' regs' retv, BinOp_spec i _ regs dst arg1 arg2 lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. }
    { apply Dregs. set_solver+. }
    { apply reg_word_ok_int. } { exact Hstep. } { apply reg_phys_lword_of_word. }
    { intros. by econstructor. }
    { intros. constructor. by eapply BinOp_fail_incrPC. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (** A BinOp on two integer operands, whose PC increments, has one
      outcome. *)
  Lemma BinOp_spec_next i lpc regs dst arg1 arg2 lpc' regs' retv n1 n2 lpc0 :
    lz_of_argument regs arg1 = Some n1 →
    lz_of_argument regs arg2 = Some n2 →
    incrementPC lpc = Some lpc0 →
    BinOp_spec i lpc regs dst arg1 arg2 lpc' regs' retv →
    retv = NextIV ∧ lpc' = lpc0 ∧ regs' = <[dst := WInt (denote i n1 n2)]ₗ> regs.
  Proof.
    intros H1 H2 Hinc [n1' n2' H1' H2' Hinc' -> | Hfail].
    - simplify_eq. done.
    - destruct Hfail; simplify_eq; congruence.
  Qed.

  (** The map-form success rule, from which the register-shaped ones
      follow. *)
  Lemma wp_BinOp_next E i pc_p pc_g pc_b pc_e pc_a pc_π w dst arg1 arg2 regs n1 n2 lpc' dq :
    decodeInstrW w.(lw) = i →
    is_BinOp i dst arg1 arg2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    {[dst]} ∪ regs_of_argument arg1 ∪ regs_of_argument arg2 ⊆ dom regs →
    lz_of_argument regs arg1 = Some n1 →
    lz_of_argument regs arg2 = Some n2 →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[dst := WInt (denote i n1 n2)]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hi Hvpc Hdom H1 H2 Hinc φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_BinOp with "[$HPC $Hpc_a $Hmap]"); eauto.
    { by erewrite regs_of_is_BinOp. }
    iIntros "!>" (lpc0 regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    rewrite Hdecode in Hspec.
    destruct (BinOp_spec_next _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hinc Hspec) as (-> & -> & ->).
    iApply "Hφ". by iFrame.
  Qed.

  (* Derived specifications *)
  Lemma wp_binop_success_z_z E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 n2 pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inl n1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc Hcnull ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_r_z E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r1 w1 n1 n2 pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inl n2) →
    IsLInt w1 n1 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ w1
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hw1 Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr1 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    iDestruct (map_of_regs_2 with "Hr1 Hdst") as "[Hmap %]".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_z_r E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 r2 w2 n2 pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inl n1) (inr r2) →
    IsLInt w2 n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ w2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hw2 Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_2 with "Hr2 Hdst") as "[Hmap %]".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_r_r E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r1 w1 n1 r2 w2 n2 pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hw1 Hw2 Hpc_a Hvpc Hcnull Hncull' Hncull'' ϕ) "(HPC & Hpc_a & Hr1 & Hr2 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_r_r_same E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r wr n pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r) (inr r) →
    IsLInt wr n →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r ↦ᵣ wr
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r ↦ᵣ wr
          ∗ dst ↦ᵣ WInt (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwr Hpc_a Hvpc Hcnull Hncull' ϕ) "(HPC & Hpc_a & Hr & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwr) as [πr ->].
    iDestruct (map_of_regs_2 with "Hr Hdst") as "[Hmap %]".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_dst_z E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 n2 pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr dst) (inl n2) →
    IsLInt wdst n1 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwdst Hpc_a Hvpc Hcnull ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_z_dst E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 n2 pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inl n1) (inr dst) →
    IsLInt wdst n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwdst Hpc_a Hvpc Hcnull ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_dst_r E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 r2 w2 n2 pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr dst) (inr r2) →
    IsLInt wdst n1 →
    IsLInt w2 n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ w2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwdst Hw2 Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_2 with "Hr2 Hdst") as "[Hmap %]".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_r_dst E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r1 w1 n1 n2 pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inr dst) →
    IsLInt w1 n1 →
    IsLInt wdst n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ w1
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hw1 Hwdst Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    iDestruct (map_of_regs_2 with "Hr2 Hdst") as "[Hmap %]".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_binop_success_dst_dst E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n pc_a' dq :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr dst) (inr dst) →
    IsLInt wdst n →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->

    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ WInt (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwdst Hpc_a Hvpc Hcnull ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_BinOp_next with "[$HPC $Hpc_a $Hmap]"); try solve_next_side.
    iIntros "!> (HPC & Hpc_a & Hmap)". iRegsMapWrite "Hmap". iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules.

(* Hints to automate proofs of is_BinOp *)
Lemma is_BinOp_Add dst arg1 arg2 :
  is_BinOp (Add dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Sub dst arg1 arg2 :
  is_BinOp (Sub dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Mul dst arg1 arg2 :
  is_BinOp (Mul dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LAnd dst arg1 arg2 :
  is_BinOp (LAnd dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LOr dst arg1 arg2 :
  is_BinOp (LOr dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LShiftL dst arg1 arg2 :
  is_BinOp (LShiftL dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LShiftR dst arg1 arg2 :
  is_BinOp (LShiftR dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Lt dst arg1 arg2 :
  is_BinOp (Lt dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.

#[export] Hint Resolve is_BinOp_Add : core.
#[export] Hint Resolve is_BinOp_Sub : core.
#[export] Hint Resolve is_BinOp_Mul : core.
#[export] Hint Resolve is_BinOp_LAnd : core.
#[export] Hint Resolve is_BinOp_LOr : core.
#[export] Hint Resolve is_BinOp_LShiftL : core.
#[export] Hint Resolve is_BinOp_LShiftR : core.
#[export] Hint Resolve is_BinOp_Lt : core.
