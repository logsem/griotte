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

  Inductive Mov_spec (regs: LReg) (dst: RegName) (src: Z + RegName) (regs': LReg): griotte_lang.val -> Prop :=
  | GetTag_spec_success w:
      lword_of_argument regs src = Some w →
      incrementPC (<[ dst := w ]ₗ> regs) = Some regs' →
      Mov_spec regs dst src regs' NextIV
  | Mov_spec_failure w:
      lword_of_argument regs src = Some w →
      incrementPC (<[ dst := w ]ₗ> regs) = None →
      Mov_spec regs dst src regs' FailedV.

  Lemma wp_Mov Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs :
    decodeInstrW w.(lw) = Mov dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Mov dst src) ⊆ dom regs →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Mov_spec regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    assert (exists w, lword_of_argument regs src = Some w) as [wsrc Hwsrc].
    { destruct src as [| r0]; eauto; cbn.
      destruct (Hri r0) as [? [? ?]]; first set_solver+. eauto. }
    assert (exec_opt (Mov dst src) pc_p (r, sr, m, st) =
              updatePC (update_reg (r, sr, m, st) dst wsrc.(lw))) as HH.
    { cbn. erewrite word_of_arg_mono; [done|exact Hregs|].
      by rewrite word_of_argument_erase Hwsrc. }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst wsrc _ _ _
      (λ regs' retv, Mov_spec regs dst src regs' retv)
      with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
    { by eapply erasure_lword_of_argument_word. } { exact Hstep. }
    { intros. by econstructor. }
    { intros. by econstructor. }
    iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_move_success_z_gen E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr1 z :
    decodeInstrW w.(lw) = Mov r1 (inl z) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt (if (decide (r1 = cnull)) then 0 else z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      destruct (decide (r1 = cnull)) ; simplify_map_eq.
      all: rewrite (insert_insert_ne _ PC _) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      all: iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_z E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr1 z :
    decodeInstrW w.(lw) = Mov r1 (inl z) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt z }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iApply (wp_move_success_z_gen with "[$HPC $Hpc_a $Hr1]"); eauto.
    destruct (decide (r1 = cnull)); first done.
    iFrame.
  Qed.

  Lemma wp_move_success_cnull_z E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w w0 z :
    decodeInstrW w.(lw) = Mov cnull (inl z) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ cnull ↦ᵣ w0 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ cnull ↦ᵣ WInt 0 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iApply (wp_move_success_z_gen with "[$HPC $Hpc_a $Hr1]"); eauto.
  Qed.

  Lemma wp_move_success_reg E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr1 rv wrv :
    decodeInstrW w.(lw) = Mov r1 (inr rv) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    rv ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ wr1
        ∗ ▷ rv ↦ᵣ wrv }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ wrv
          ∗ rv ↦ᵣ wrv }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ PC r1) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr1 :
    decodeInstrW w.(lw) = Mov r1 (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ wr1 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_samePC E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w :
    decodeInstrW w.(lw) = Mov PC (inr PC) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_toPC E pc_p pc_g pc_b pc_e pc_a pc_π w r1 (t : bool) p g b e a a' π :
    decodeInstrW w.(lw) = Mov PC (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (a + 1)%a = Some a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap t p g b e a' @@? π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WCap t p g b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_move_success_reg_fromPC E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 wr1 :
    decodeInstrW w.(lw) = Mov r1 (inr PC) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ wr1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Mov with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

End griotte_lang_rules.
