From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

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

  Inductive Mov_spec (lpc : LWord) (regs: LReg) (dst: RegName) (src: Z + RegName)
    (lpc' : LWord) (regs': LReg): griotte_lang.val -> Prop :=
  | Mov_spec_success w:
      lword_of_argument regs src = Some w →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := w ]ₗ> regs →
      Mov_spec lpc regs dst src lpc' regs' NextIV
  | Mov_spec_failure w:
      lword_of_argument regs src = Some w →
      incrementPC lpc = None →
      lpc' = lpc →
      regs' = regs →
      Mov_spec lpc regs dst src lpc' regs' FaultedV.

  Lemma wp_Mov Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs dq :
    decodeInstrW w.(lw) = Mov dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Mov dst src) ⊆ dom regs →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Mov_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of, operands_of in Hri.
    assert (exists w, lword_of_argument regs src = Some w) as [wsrc Hwsrc].
    { destruct src as [| r0]; eauto; cbn.
      destruct (Hri r0) as [? [? ?]]; first set_solver+. eauto. }
    destruct (lword_of_argument_phys _ _ _ _ _ Hregs Hwsrc) as (s & Hsrc & Hrel).
    assert (exec_opt (Mov dst src) pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
              nextPC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst
                (and_tag s wsrc.(lw)))) as HH.
    { cbn. by rewrite Hsrc. }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst wsrc _ _ _ _
      (λ lpc' regs' retv, Mov_spec _ regs dst src lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
    { by eapply erasure_lword_of_argument_word. } { exact Hstep. } { exact Hrel. }
    { intros. by econstructor. }
    { intros. by econstructor. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_move_success_z_gen E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr1 z dq :
    decodeInstrW w.(lw) = Mov r1 (inl z) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ (if (decide (r1 = cnull)) then wr1 else WInt z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (wp_Mov with "[$HPC $Hmap $Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of, operands_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      destruct (decide (r1 = cnull)) ; simplify_map_eq.
      all: iRegsMap "Hmap"; iFrame. }
    { (* Failure (contradiction) *)
      all: try incrementPC_inv; simplify_map_eq; eauto; try congruence. }
  Qed.

  Lemma wp_move_success_reg E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr1 rv wrv dq :
    decodeInstrW w.(lw) = Mov r1 (inr rv) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    rv ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ wr1
        ∗ ▷ rv ↦ᵣ wrv }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ wrv
          ∗ rv ↦ᵣ wrv }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hrv") as "[Hmap %]".
    iApply (wp_Mov with "[$HPC $Hmap $Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of, operands_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; iFrame. }
    { (* Failure (contradiction) *)
      all: try incrementPC_inv; simplify_map_eq; eauto; try congruence. }
  Qed.

  Lemma wp_move_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr1 dq :
    decodeInstrW w.(lw) = Mov r1 (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ wr1 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (wp_Mov with "[$HPC $Hmap $Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of, operands_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; iFrame. }
    { (* Failure (contradiction) *)
      all: try incrementPC_inv; simplify_map_eq; eauto; try congruence. }
  Qed.

End griotte_lang_rules.
