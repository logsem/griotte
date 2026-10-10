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

  Inductive ClearTag_spec (regs : LReg) (dst: RegName) (src: RegName) (regs' : LReg): griotte_lang.val -> Prop :=
  | ClearTag_spec_success w:
      regs !!ₗ src = Some w →
      incrementPC (<[ dst := lclear_tag w ]ₗ> regs) = Some regs' →
      ClearTag_spec regs dst src regs' NextIV
  | ClearTag_spec_failure w:
      regs !!ₗ src = Some w →
      incrementPC (<[ dst := lclear_tag w ]ₗ> regs) = None →
      regs' = regs →
      ClearTag_spec regs dst src regs' FailedV.

  Lemma wp_ClearTag Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs :
    decodeInstrW w.(lw) = ClearTag dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (ClearTag dst src) ⊆ dom regs →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ ClearTag_spec regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    destruct (Hri src) as [wsrc [H'src Hsrc]]; first by set_solver+.
    assert (exec_opt (ClearTag dst src) pc_p (r, sr, m, st) =
      updatePC (update_reg (r, sr, m, st) dst (lclear_tag wsrc).(lw))) as HH.
    { cbn. erewrite lookup_reg_weaken; [done| |exact Hregs].
      by rewrite lookup_reg_erase H'src. }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst (lclear_tag wsrc) _ _ _
      (λ regs' retv, ClearTag_spec regs dst src regs' retv)
      with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
    { apply reg_word_ok_lclear_tag. } { exact Hstep. }
    { intros. by econstructor. }
    { intros. by econstructor. }
    iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_ClearTag_same_success E r pc_p pc_g pc_b pc_e pc_a pc_π w wr pc_a':
    decodeInstrW w.(lw) = ClearTag r r →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    r ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r ↦ᵣ lclear_tag wr }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_ClearTag_success E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' :
    decodeInstrW w.(lw) = ClearTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    src ≠ cnull ->
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ lclear_tag wsrc }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_ClearTag with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma ClearTag_spec_failure_regs regs dst src regs' :
    ClearTag_spec regs dst src regs' FailedV → regs' = regs.
  Proof. by inversion 1. Qed.

  Lemma wp_ClearTag_failure E pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs wsrc :
    decodeInstrW w.(lw) = ClearTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (ClearTag dst src) ⊆ dom regs →
    regs !!ₗ src = Some wsrc →
    incrementPC (<[dst := lclear_tag wsrc]ₗ> regs) = None →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc HPC Hdom Hsrc Hinc φ) "Hpre Hφ".
    iApply (wp_ClearTag with "Hpre"); eauto.
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hregs)".
    destruct Hspec; simplify_eq.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_ClearTag_PC E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w :
    decodeInstrW w.(lw) = ClearTag PC PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite !insert_insert_eq.
      iDestruct (regs_of_map_1 with "Hmap") as "HPC".
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.
  Lemma wp_ClearTag_fromPC E dst pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wdst :
    decodeInstrW w.(lw) = ClearTag dst PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗
        ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ w ∗ dst ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a @@? pc_π }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hcnull φ) "(>HPC & >Hmem & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hdst]"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.

  Lemma wp_ClearTag_toPC E src pc_p pc_g pc_b pc_e pc_a pc_π w
      (t : bool) p g b e a a' π :
    decodeInstrW w.(lw) = ClearTag PC src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (a + 1)%a = Some a' → src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗
        ▷ src ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap false p g b e a' @@? π ∗ pc_a ↦ₐ w ∗
        src ↦ᵣ WCap t p g b e a @@? π }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hcnull φ) "(>HPC & >Hmem & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite !insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hsrc]"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.

  Lemma wp_ClearTag_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wn :
    decodeInstrW w.(lw) = ClearTag cnull cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_from_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wd wn :
    decodeInstrW w.(lw) = ClearTag dst cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ WInt 0%Z ∗ cnull ↦ᵣ wn }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hs & >Hd) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hd Hs") as "[Hmap (%&%&%)]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src wn ws :
    decodeInstrW w.(lw) = ClearTag cnull src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hd & >Hs) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hd Hs") as "[Hmap (%&%&%)]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC cnull) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_PC_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wn :
    decodeInstrW w.(lw) = ClearTag cnull PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto.
      iApply "Hφ". iFrame.
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_cnull_toPC E pc_p pc_g pc_b pc_e pc_a pc_π w wn :
    decodeInstrW w.(lw) = ClearTag PC cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ wn }}}.
  Proof.
    iIntros (Hdecode Hvpc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
    - simplify_eq. iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hn]"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  Lemma wp_ClearTag_toPC_failure E pc_p pc_g pc_b pc_e pc_a pc_π w src ws :
    decodeInstrW w.(lw) = ClearTag PC src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap ws.(lw) = false →
    src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ w ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hcap Hne φ) "(>HPC & >Hmem & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - destruct ws as [[| [] | |] ?]; cbn in Hcap; try done;
        unfold lclear_tag, lift_word in *; incrementPC_inv; simplify_map_eq; try exact lnull.
    - by iApply "Hφ".
  Qed.

End griotte_lang_rules.
