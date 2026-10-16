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
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.

  (** The PC with its address offset by [imm], as Lea on the PC: the tag is
      cleared on an address overflow. The result keeps the PC's identifier. *)
  Definition auipcc_word (lpc : LWord) (imm : Z) : LWord :=
    match lpc with
    | WCap t p g b e a @@? π =>
        match (a + imm)%a with
        | Some a' => WCap t p g b e a' @@? π
        | None => WCap false p g b e a @@? π
        end
    | _ => lpc
    end.

  Inductive Auipcc_spec (lpc : LWord) (regs : LReg) (dst : RegName) (imm : Z)
    (lpc' : LWord) (regs' : LReg) : griotte_lang.val → Prop :=
  | Auipcc_spec_success :
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := auipcc_word lpc imm ]ₗ> regs →
      Auipcc_spec lpc regs dst imm lpc' regs' NextIV
  | Auipcc_spec_failure :
      incrementPC lpc = None →
      Auipcc_spec lpc regs dst imm lpc' regs' FailedV.

  Lemma wp_Auipcc Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst imm regs dq :
    decodeInstrW w.(lw) = Auipcc dst imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Auipcc dst imm) ⊆ dom regs →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Auipcc_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst imm lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    rewrite Hinstr /exec in Hstep.
    set (v := auipcc_word (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) imm).
    assert (exec_opt (Auipcc dst imm) pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
              updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst v.(lw)))
      as HH.
    { rewrite /v /auipcc_word /exec_opt /pcc /=. by destruct (pc_a + imm)%a. }
    rewrite HH in Hstep.
    assert (reg_word_ok R C v) as Hok.
    { pose proof (er_pc_word _ _ _ _ _ _ Her) as HokPC.
      rewrite /v /auipcc_word.
      destruct (pc_a + imm)%a;
        apply (reg_word_ok_derive _ _ (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π));
        [by left|done|done|done|by left|done|done|done]. }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst v _ _ _ _
      (λ lpc' regs' retv,
         Auipcc_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst imm lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
    { exact Hok. } { exact Hstep. }
    { apply reg_phys_no_id. rewrite /v /auipcc_word.
      pose proof (erasure_pc_no_id _ _ _ _ _ _ Her Hvpc) as Hπ. cbn in Hπ. subst pc_π.
      by destruct (pc_a + imm)%a. }
    { intros. by econstructor. }
    { intros. by econstructor. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_auipcc_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' a' w dst wdst imm dq :
    decodeInstrW w.(lw) = Auipcc dst imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (pc_a + imm)%a = Some a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WCap true pc_p pc_g pc_b pc_e a' @@? pc_π }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Ha' Hcnull φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_Auipcc with "[$HPC $Hmap $Hpc_a]"); eauto.
    all: try (by rewrite /regs_of ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [Hinc -> | Hinc].
    - iApply "Hφ". try incrementPC_inv; simplify_map_eq.
      iFrame. iRegsMap "Hmap". iFrame.
    - exfalso. try incrementPC_inv; simplify_map_eq; congruence.
  Qed.

  Lemma wp_auipcc_overflow E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst imm dq :
    decodeInstrW w.(lw) = Auipcc dst imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (pc_a + imm)%a = None →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a @@? pc_π }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Ha' Hcnull φ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_Auipcc with "[$HPC $Hmap $Hpc_a]"); eauto.
    all: try (by rewrite /regs_of ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [Hinc -> | Hinc].
    - iApply "Hφ". try incrementPC_inv; simplify_map_eq.
      iFrame. iRegsMap "Hmap". iFrame.
    - exfalso. try incrementPC_inv; simplify_map_eq; congruence.
  Qed.

End griotte_lang_rules.
