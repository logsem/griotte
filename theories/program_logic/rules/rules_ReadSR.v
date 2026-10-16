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

  (* System registers hold identifier-less words: a read gives identifier [None]. *)
  Inductive ReadSR_failure (lpc : LWord) (regs: LReg) (sregs : SReg) (dst: RegName) (src: SRegName) :=
  | ReadSR_fail_nonxrs p g b e a π:
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = false ->
      ReadSR_failure lpc regs sregs dst src
  | ReadSR_fail_incrPC (w : Word):
      sregs !! src = Some w →
      incrementPC lpc = None →
      ReadSR_failure lpc regs sregs dst src
  .

  Inductive ReadSR_spec
  (lpc : LWord) (regs: LReg) (sregs: SReg) (dst: RegName) (src: SRegName) (lpc' : LWord) (regs': LReg)
    : griotte_lang.val -> Prop :=
  | ReadSR_spec_success p g b e a π (w : Word):
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = true ->
      sregs !! src = Some w →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := lword_of_word w ]ₗ> regs →
      ReadSR_spec lpc regs sregs dst src lpc' regs' NextIV
  | ReadSR_spec_failure:
      ReadSR_failure lpc regs sregs dst src →
      ReadSR_spec lpc regs sregs dst src lpc' regs' FailedV.

  Lemma wp_ReadSR Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs sregs dq :
    decodeInstrW w.(lw) = ReadSR dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (ReadSR dst src) ⊆ dom regs →
    (if (has_sreg_access pc_p)
    then sregs_of (ReadSR dst src) ⊆ dom sregs
    else True) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ ReadSR_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs sregs dst src lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Dsregs φ) "(>HPC & >Hpc_a & >Hmap & >Hsmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntrosNamed (r sr m st lreg lmem R C c σ').
    iDestruct (gen_heap_valid_inclSepM with "Hsr Hsmap") as %Hsregs.
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. instr_fail Hstep.
      econstructor. by eapply ReadSR_fail_nonxrs. }
    specialize (indom_sregs_incl _ _ _ Dsregs Hsregs) as Hsri. unfold sregs_of in Hsri.
    destruct (Hsri src) as [wsrc [H'src Hsrc]]; first by set_solver+.
    assert (exec_opt (ReadSR dst src) pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
              updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst
                          (lword_of_word wsrc).(lw))) as HH.
    { by cbn; rewrite Hsrc Hxsr /=. }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word wsrc) _ _ _ _
      (λ lpc' regs' retv, ReadSR_spec _ regs sregs dst src lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hsmap]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
    { by eapply (er_sreg_words _ _ _ _ _ _ Her src). } { exact Hstep. }
    { apply reg_phys_lword_of_word. }
    { intros. by econstructor. }
    { intros. econstructor. by eapply ReadSR_fail_incrPC. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_readsr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst src (wsrc : Word) dq :
    decodeInstrW w.(lw) = ReadSR dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ₛᵣ wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ lword_of_word wsrc
          ∗ src ↦ₛᵣ wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hsrc") as "Hsmap".
    iApply (wp_ReadSR with "[$HPC $Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    - by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+.
    - by unfold sregs_of; rewrite Hxsr ?dom_insert ?dom_singleton_L; set_solver+.
    - iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap & Hsmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto; iFrame.
      iDestruct (sregs_of_map_1 with "Hsmap") as "?"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      - simplify_map_eq; eauto; congruence.
      - all: try incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
  Qed.

End griotte_lang_rules.
