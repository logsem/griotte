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

  Inductive ClearTag_spec (lpc : LWord) (regs : LReg) (dst: RegName) (src: RegName)
    (lpc' : LWord) (regs' : LReg): griotte_lang.val -> Prop :=
  | ClearTag_spec_success w:
      regs !!ₗ src = Some w →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := lclear_tag w ]ₗ> regs →
      ClearTag_spec lpc regs dst src lpc' regs' NextIV
  | ClearTag_spec_failure w:
      regs !!ₗ src = Some w →
      incrementPC lpc = None →
      lpc' = lpc →
      regs' = regs →
      ClearTag_spec lpc regs dst src lpc' regs' FailedV.

  Lemma wp_ClearTag Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs dq :
    decodeInstrW w.(lw) = ClearTag dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (ClearTag dst src) ⊆ dom regs →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ ClearTag_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "Hσ"; iNamed "Hσ".
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    destruct (Hri src) as [wsrc [H'src Hsrc]]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'src) as (s & Hsrc' & Hrel).
    assert (exec_opt (ClearTag dst src) pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
      updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst
        (clear_tag (and_tag s wsrc.(lw))))) as HH.
    { cbn. by rewrite Hsrc'. }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst (lclear_tag wsrc) _ _ _ _
      (λ lpc' regs' retv, ClearTag_spec _ regs dst src lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
    { apply reg_word_ok_lclear_tag. } { exact Hstep. } { by apply reg_phys_lclear_tag. }
    { intros. by econstructor. }
    { intros. by econstructor. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_ClearTag_same_success E r pc_p pc_g pc_b pc_e pc_a pc_π w wr pc_a' dq:
    decodeInstrW w.(lw) = ClearTag r r →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    r ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r ↦ᵣ lclear_tag wr }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_ClearTag with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; try exact lnull.
      iRegsMap "Hmap"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; eauto; try congruence. }
  Qed.

  Lemma wp_ClearTag_success E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' dq :
    decodeInstrW w.(lw) = ClearTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    src ≠ cnull ->
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ lclear_tag wsrc }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_ClearTag with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; try exact lnull.
      iRegsMap "Hmap"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; eauto; try congruence. }
  Qed.

  Lemma wp_ClearTag_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wn dq :
    decodeInstrW w.(lw) = ClearTag cnull cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_1 with "Hn") as "Hmap".
    iApply (wp_ClearTag with "[$HPC $Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; try exact lnull.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_from_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wd wn dq :
    decodeInstrW w.(lw) = ClearTag dst cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ dst ↦ᵣ WInt 0%Z ∗ cnull ↦ᵣ wn }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hs & >Hd) Hφ".
    iDestruct (map_of_regs_2 with "Hd Hs") as "[Hmap %]".
    iApply (wp_ClearTag with "[$HPC $Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; try exact lnull.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src wn ws dq :
    decodeInstrW w.(lw) = ClearTag cnull src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → src ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} w ∗ cnull ↦ᵣ WInt 0%Z ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hd & >Hs) Hφ".
    iDestruct (map_of_regs_2 with "Hd Hs") as "[Hmap %]".
    iApply (wp_ClearTag with "[$HPC $Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; try exact lnull.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; try incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

End griotte_lang_rules.
