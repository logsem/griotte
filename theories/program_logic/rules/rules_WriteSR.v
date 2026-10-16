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
  Implicit Types sreg : gmap SRegName Word.
  Implicit Types ms : gmap Addr LWord.

  (* System registers hold identifier-less words: a successful write stores the
     physical word of an identifier-less register word, which is exact when
     a tagged word has authority or no heap base. *)
  Inductive WriteSR_failure (lpc : LWord) (regs: LReg) (sregs : SReg) (dst: SRegName) (src: RegName) :=
  | WriteSR_fail_nonxrs p g b e a π:
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = false ->
      WriteSR_failure lpc regs sregs dst src
  | WriteSR_fail_incrPC w:
      regs !!ₗ src = Some w →
      incrementPC lpc = None →
      WriteSR_failure lpc regs sregs dst src
  .

  Inductive WriteSR_spec
    (lpc lpc' : LWord) (regs: LReg) (sregs sregs': SReg) (dst: SRegName) (src: RegName)
    : griotte_lang.val -> Prop :=
  | WriteSR_spec_success p g b e a π w:
    lpc = WCap true p g b e a @@? π →
    has_sreg_access p = true ->
    regs !!ₗ src = Some w →
    incrementPC lpc = Some lpc' →
    sregs' = (<[dst := w.(lw)]> sregs) →
    WriteSR_spec lpc lpc' regs sregs sregs' dst src NextIV
  | WriteSR_spec_failure:
    sregs = sregs' ->
    WriteSR_failure lpc regs sregs dst src →
    WriteSR_spec lpc lpc' regs sregs sregs' dst src FailedV.

  (* An identifier-less register word is a valid system register word. *)
  Lemma reg_word_ok_no_id R C (v : LWord) :
    v.(lprov) = None → reg_word_ok R C v → reg_word_ok R C (lword_of_word v.(lw)).
  Proof. destruct v as [w' π]; cbn. by intros ->. Qed.

  Lemma wp_WriteSR Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs sregs dq :
    decodeInstrW w.(lw) = WriteSR dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (WriteSR dst src) ⊆ dom regs →
    (if (has_sreg_access pc_p)
    then sregs_of (WriteSR dst src) ⊆ dom sregs
    else True) →
    (has_sreg_access pc_p = true → ∀ (v : LWord), regs !!ₗ src = Some v →
       v.(lprov) = None ∧ load_exact_cond v) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}
      Instr Executable @ Ep
    {{{ lpc' sregs' retv, RET retv;
        ⌜ WriteSR_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lpc' regs sregs sregs' dst src retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ([∗ map] k↦y ∈ sregs', k ↦ₛᵣ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Dsregs Hnoid φ) "(>HPC & >Hpc_a & >Hmap & >Hsmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    iDestruct (gen_heap_valid_inclSepM with "Hsr Hsmap") as %Hsregs.
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    destruct (Hri src) as [wsrc [H'src _]]; first by set_solver+.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. instr_fail Hstep.
      econstructor; first done. by eapply WriteSR_fail_nonxrs. }
    specialize (indom_sregs_incl _ _ _ Dsregs Hsregs) as Hsri. unfold sregs_of in Hsri.
    destruct (Hsri dst) as [wdst [H'dst Hdst]]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'src) as (s & Hsrc & Hrel).
    destruct (Hnoid eq_refl _ H'src) as [Hπ Hnh].
    rewrite (reg_phys_exact_cond _ _ _ Hrel) in Hsrc.
    2: { intros (ι & x & Hι & _). congruence. }
    2: { done. }
    assert (exec_opt (WriteSR dst src) pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
              updatePC (update_sreg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst wsrc.(lw))) as HH.
    { by cbn; rewrite Hsrc Hxsr /=. }
    rewrite HH in Hstep.
    assert (reg_word_ok R C (lword_of_word wsrc.(lw))) as Hok.
    { apply reg_word_ok_no_id; first done. by eapply erasure_llookup_reg_word. }
    iApply (instr_close_sreg_update _ _ _ _ _ _ _ _ _ _ _ _ dst wsrc.(lw) _ _ _
      (λ lpc' sregs' retv, WriteSR_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lpc' regs sregs sregs' dst src retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hsmap [Hφ Hpc_a]").
    { exact Her. } { by apply elem_of_dom. } { exact Hok. } { exact Hstep. }
    { intros. econstructor; eauto. }
    { intros. econstructor; first done. by eapply WriteSR_fail_incrPC. }
    iIntros (lpc' sregs' retv Hspec) "HPC Hmap Hsmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_writesr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst src (wsrc : Word) dq :
    decodeInstrW w.(lw) = WriteSR dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull ->
    load_exact_cond (lword_of_word wsrc) →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ₛᵣ wdst
        ∗ ▷ src ↦ᵣ lword_of_word wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ₛᵣ wsrc
          ∗ src ↦ᵣ lword_of_word wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' ? Hnh ϕ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hdst") as "Hsmap".
    iApply (wp_WriteSR with "[$HPC $Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    - by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+.
    - by unfold sregs_of; rewrite Hxsr ?dom_insert ?dom_singleton_L; set_solver+.
    - intros _ v Hv; simplify_eq; done.
    - iNext. iIntros (lpc' sregs' retv) "(#Hspec & HPC & Hpc_a & Hmap & Hsmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| -> Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto; iFrame.
      iRegsMap "Hsmap"; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      - simplify_map_eq; eauto; congruence.
      - all: try incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
  Qed.

End griotte_lang_rules.
