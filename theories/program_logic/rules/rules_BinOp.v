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

  Inductive BinOp_failure (i: instr) (regs : LReg) (dst: RegName) (rv1 rv2: Z + RegName) (regs' : LReg) :=
  | BinOp_fail_nonconst1:
      lz_of_argument regs rv1 = None ->
      BinOp_failure i regs dst rv1 rv2 regs'
  | BinOp_fail_nonconst2:
      lz_of_argument regs rv2 = None ->
      BinOp_failure i regs dst rv1 rv2 regs'
  | BinOp_fail_incrPC n1 n2:
      lz_of_argument regs rv1 = Some n1 ->
      lz_of_argument regs rv2 = Some n2 ->
      incrementPC (<[ dst := WInt (denote i n1 n2) ]ₗ> regs) = None ->
      BinOp_failure i regs dst rv1 rv2 regs'.

  Inductive BinOp_spec (i: instr) (regs : LReg) (dst: RegName) (rv1 rv2: Z + RegName) (regs' : LReg): griotte_lang.val -> Prop :=
  | BinOp_spec_success n1 n2:
      lz_of_argument regs rv1 = Some n1 ->
      lz_of_argument regs rv2 = Some n2 ->
      incrementPC (<[ dst := WInt (denote i n1 n2) ]ₗ> regs) = Some regs' ->
      BinOp_spec i regs dst rv1 rv2 regs' NextIV
  | BinOp_spec_failure:
      BinOp_failure i regs dst rv1 rv2 regs' ->
      BinOp_spec i regs dst rv1 rv2 regs' FailedV.

  Local Ltac iFail Hcont get_fail_case :=
    cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
    econstructor; eapply get_fail_case; eauto.

  Lemma wp_BinOp Ep i pc_p pc_g pc_b pc_e pc_a pc_π w dst arg1 arg2 regs :
    decodeInstrW w.(lw) = i →
    is_BinOp i dst arg1 arg2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of i ⊆ dom regs →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ BinOp_spec (decodeInstrW w.(lw)) regs dst arg1 arg2 regs' retv ⌝ ∗
          pc_a ↦ₐ w ∗
          [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hdecode /exec in Hstep. rewrite Hdecode.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    erewrite regs_of_is_BinOp in Hri, Dregs; eauto.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.
    destruct (lz_of_argument regs arg1) as [n1|] eqn:Hn1;
      pose proof Hn1 as Hn1'; cycle 1.
    (* Failure: arg1 is not an integer *)
    { unfold lz_of_argument in Hn1. destruct arg1 as [| r0]; [ congruence |].
      destruct (Hri r0) as [r0v [Hr'0 Hr0]]; first by unfold regs_of_argument; set_solver+.
      assert (lookup_reg r0 r = Some r0v.(lw)) as Hsrc0.
      { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase Hr'0. }
      assert (c = Failed ∧ σ' = (r, sr, m, st)) as (-> & ->).
      { rewrite Hr'0 in Hn1.
        destruct r0v; try congruence.
        destruct_word lw; try congruence.
        all: destruct_or! Hinstr; rewrite Hinstr /= in Hstep; cbn in Hstep.
        all: rewrite Hsrc0 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first exact Her.
      iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro. constructor.
      by eapply BinOp_fail_nonconst1. }
    rewrite -z_of_argument_erase in Hn1.
    apply (z_of_arg_mono _ r arg1 n1) in Hn1; auto.

    destruct (lz_of_argument regs arg2) as [n2|] eqn:Hn2;
      pose proof Hn2 as Hn2'; cycle 1.
    (* Failure: arg2 is not an integer *)
    { unfold lz_of_argument in Hn2. destruct arg2 as [| r1]; [ congruence |].
      destruct (Hri r1) as [r1v [Hr'1 Hr1]]; first by unfold regs_of_argument; set_solver+.
      assert (lookup_reg r1 r = Some r1v.(lw)) as Hsrc1.
      { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase Hr'1. }
      assert (c = Failed ∧ σ' = (r, sr, m, st)) as (-> & ->).
      { rewrite Hr'1 in Hn2.
        destruct r1v; try congruence.
        destruct_word lw; try congruence.
        all: destruct_or! Hinstr; rewrite Hinstr /= in Hstep; cbn in Hstep.
        all: rewrite Hn1 /= in Hstep.
        all: rewrite Hsrc1 in Hstep. all: repeat case_match; simplify_eq; eauto. }
      iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first exact Her.
      iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro. constructor.
      by eapply BinOp_fail_nonconst2. }
    rewrite -z_of_argument_erase in Hn2.
    apply (z_of_arg_mono _ r arg2 n2) in Hn2; auto.

    assert (exec_opt i pc_p (r, sr, m, st) = updatePC (update_reg (r, sr, m, st) dst (WInt (denote i n1 n2)))) as HH.
    { all: destruct_or! Hinstr; rewrite Hinstr /= /update_reg /= in Hstep |- *; auto.
      all: by rewrite Hn1 Hn2; cbn. }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt (denote i n1 n2))) _ _ _
      (λ regs' retv, BinOp_spec i regs dst arg1 arg2 regs' retv)
      with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. }
    { apply Dregs. set_solver+. } { by eexists. }
    { apply reg_word_ok_int. } { exact Hstep. }
    { intros. by econstructor. }
    { intros. constructor. by eapply BinOp_fail_incrPC. }
    iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  (* Derived specifications *)
  Lemma wp_binop_success_z_z E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 n2 pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inl n1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc Hcnull ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_r_z E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r1 w1 n1 n2 pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inl n2) →
    IsLInt w1 n1 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hw1 Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr1 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
              (insert_insert_ne _ dst PC) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_z_r E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 r2 w2 n2 pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inl n1) (inr r2) →
    IsLInt w2 n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r2 ↦ᵣ w2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hw2 Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ dst PC) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_r_r E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r1 w1 n1 r2 w2 n2 pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hw1 Hw2 Hpc_a Hvpc Hcnull Hncull' Hncull'' ϕ) "(HPC & Hpc_a & Hr1 & Hr2 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_r_r_same E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r wr n pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r) (inr r) →
    IsLInt wr n →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r ↦ᵣ wr
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r ↦ᵣ wr
          ∗ dst ↦ᵣ WInt (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwr Hpc_a Hvpc Hcnull Hncull' ϕ) "(HPC & Hpc_a & Hr & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwr) as [πr ->].
    iDestruct (map_of_regs_3 with "HPC Hr Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r dst) //
              (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_dst_z E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 n2 pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr dst) (inl n2) →
    IsLInt wdst n1 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwdst Hpc_a Hvpc Hcnull ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_z_dst E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 n2 pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inl n1) (inr dst) →
    IsLInt wdst n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwdst Hpc_a Hvpc Hcnull ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_dst_r E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n1 r2 w2 n2 pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr dst) (inr r2) →
    IsLInt wdst n1 →
    IsLInt w2 n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r2 ↦ᵣ w2
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwdst Hw2 Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_r_dst E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r1 w1 n1 n2 pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inr dst) →
    IsLInt w1 n1 →
    IsLInt wdst n2 →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hw1 Hwdst Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr2 & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
              (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_binop_success_dst_dst E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins n pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr dst) (inr dst) →
    IsLInt wdst n →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->

    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WInt (denote ins n n)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hwdst Hpc_a Hvpc Hcnull ϕ) "(HPC & Hpc_a & Hdst) Hφ".
    destruct (IsLInt_inv _ _ Hwdst) as [πdst ->].
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| * Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  (* Slightly generalized: fails in all cases where r2 does not contain an integer. *)
  Lemma wp_binop_fail_z_r E ins dst n1 r2 w w2 wdst pc_p pc_g pc_b pc_e pc_a pc_π :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_z w2.(lw) = false →
    r2 ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ wdst ∗ r2 ↦ᵣ w2 }}}
      Instr Executable
            @ E
    {{{ RET FailedV; pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hisnz Hcnull φ) "(HPC & Hpc_a & Hdst & Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *)  destruct w2 as [[] ?]; simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Lemma wp_binop_fail_r_r_1 E ins dst r1 r2 w wdst w1 w2 pc_p pc_g pc_b pc_e pc_a pc_π :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_z w1.(lw) = false →
    r1 ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ wdst ∗ r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 }}}
      Instr Executable
      @ E
      {{{ RET FailedV; pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hzf Hcnull φ) "(HPC & Hpc_a & Hdst & Hr1 & Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hdst Hr1 Hr2") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) destruct w1 as [[] ?]; simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Lemma wp_binop_fail_r_r_2 E ins dst r1 r2 w wdst w2 w3 pc_p pc_g pc_b pc_e pc_a pc_π :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_z w3.(lw) = false →
    r2 ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ wdst ∗ r1 ↦ᵣ w2 ∗ r2 ↦ᵣ w3}}}
      Instr Executable
      @ E
      {{{ RET FailedV; pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hzf Hcnull φ) "(HPC & Hpc_a & Hdst & Hr1 & Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hdst Hr1 Hr2") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. destruct w3 as [[] ?]; simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
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

Global Hint Resolve is_BinOp_Add : core.
Global Hint Resolve is_BinOp_Sub : core.
Global Hint Resolve is_BinOp_Mul : core.
Global Hint Resolve is_BinOp_LAnd : core.
Global Hint Resolve is_BinOp_LOr : core.
Global Hint Resolve is_BinOp_LShiftL : core.
Global Hint Resolve is_BinOp_LShiftR : core.
Global Hint Resolve is_BinOp_Lt : core.
