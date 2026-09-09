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
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive ClearTag_spec (regs: Reg) (dst: RegName) (src: RegName) (regs': Reg): griotte_lang.val -> Prop :=
  | ClearTag_spec_success w:
      regs !!ᵣ src = Some w →
      incrementPC (<[ dst := clear_tag w ]ᵣ> regs) = Some regs' →
      ClearTag_spec regs dst src regs' NextIV
  | ClearTag_spec_failure w:
      regs !!ᵣ src = Some w →
      incrementPC (<[ dst := clear_tag w ]ᵣ> regs) = None →
      regs' = regs →
      ClearTag_spec regs dst src regs' FailedV.

  Lemma wp_ClearTag Ep pc_p pc_g pc_b pc_e pc_a  w dst src regs :
    decodeInstrW w = ClearTag dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
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
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[[Hr Hsr] Hm] Hst] /=". destruct σ1 as [ [ [r sr] m] st]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.

    destruct (Hri src) as [wsrc [H'src Hsrc]]; first by set_solver+.

    assert (exec_opt (ClearTag dst src) pc_p (r, sr, m, st) =
      updatePC (update_reg (r, sr, m, st) dst (clear_tag wsrc))) as HH.
    { cbn. by rewrite Hsrc. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := clear_tag wsrc ]ᵣ> regs)) as [regs'|] eqn:Hregs';
      pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) (shadow:=st) in Hregs'.
      eapply updatePC_fail_incl with (sregs':=sr) (m':=m) (shadow':=st) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      rewrite Hregs' in Hstep. simplify_pair_eq.
      iFrame. iApply "Hφ"; iFrame. iPureIntro. econstructor; eauto. }

    eapply (incrementPC_success_updatePC _ sr m st) in Hregs'
      as (t' & p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':=sr) (m':=m) (shadow':=st) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in Hstep. simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_ClearTag_same_success E r pc_p pc_g pc_b pc_e pc_a w wr pc_a':
    decodeInstrW w = ClearTag r r →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    r ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r ↦ᵣ wr }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r ↦ᵣ clear_tag wr }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[? ?]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma wp_ClearTag_success E dst src pc_p pc_g pc_b pc_e pc_a w wsrc wdst pc_a' :
    decodeInstrW w = ClearTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' ->
    src ≠ cnull ->
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ clear_tag wsrc }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull Hcnull' φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_ClearTag with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma ClearTag_spec_failure_regs regs dst src regs' :
    ClearTag_spec regs dst src regs' FailedV → regs' = regs.
  Proof. by inversion 1. Qed.

  Lemma wp_ClearTag_failure E pc_p pc_g pc_b pc_e pc_a w dst src regs wsrc :
    decodeInstrW w = ClearTag dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (ClearTag dst src) ⊆ dom regs →
    regs !!ᵣ src = Some wsrc →
    incrementPC (<[dst := clear_tag wsrc]ᵣ> regs) = None →
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

  Lemma wp_ClearTag_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w :
    decodeInstrW w = ClearTag PC PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
      iDestruct (regs_of_map_1 with "Hmap") as "HPC".
      iApply "Hφ". iFrame.
    - incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.
  Lemma wp_ClearTag_fromPC E dst pc_p pc_g pc_b pc_e pc_a pc_a' w wdst :
    decodeInstrW w = ClearTag dst PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w ∗
        ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ w ∗ dst ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hcnull φ) "(>HPC & >Hmem & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hdst]"; eauto.
      iApply "Hφ". iFrame.
    - incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.

  Lemma wp_ClearTag_toPC E src pc_p pc_g pc_b pc_e pc_a w
      (t : bool) p g b e a a' :
    decodeInstrW w = ClearTag PC src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (a + 1)%a = Some a' → src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w ∗
        ▷ src ↦ᵣ WCap t p g b e a }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap false p g b e a' ∗ pc_a ↦ₐ w ∗
        src ↦ᵣ WCap t p g b e a }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hcnull φ) "(>HPC & >Hmem & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hsrc]"; eauto.
      iApply "Hφ". iFrame.
    - incrementPC_inv; simplify_map_eq; eauto. congruence.
  Qed.

  Lemma wp_ClearTag_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w wn :
    decodeInstrW w = ClearTag cnull cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto.
      iApply "Hφ". iFrame.
    - incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_from_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w dst wd wn :
    decodeInstrW w = ClearTag dst cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → dst ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ w ∗ dst ↦ᵣ WInt 0%Z ∗ cnull ↦ᵣ wn }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hs & >Hd) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hd Hs") as "[Hmap (%&%&%)]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto.
      iApply "Hφ". iFrame.
    - incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w src wn ws :
    decodeInstrW w = ClearTag cnull src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' → src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc Hne φ) "(>HPC & >Hmem & >Hd & >Hs) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hd Hs") as "[Hmap (%&%&%)]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq (insert_insert_ne _ PC cnull) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto.
      iApply "Hφ". iFrame.
    - incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_PC_to_cnull E pc_p pc_g pc_b pc_e pc_a pc_a' w wn :
    decodeInstrW w = ClearTag cnull PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET NextIV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ WInt 0%Z }}}.
  Proof.
    iIntros (Hdecode Hvpc Hinc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
      rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto.
      iApply "Hφ". iFrame.
    - incrementPC_inv; simplify_map_eq; eauto; congruence.
  Qed.

  Lemma wp_ClearTag_cnull_toPC E pc_p pc_g pc_b pc_e pc_a w wn :
    decodeInstrW w = ClearTag PC cnull →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w ∗ ▷ cnull ↦ᵣ wn }}}
      Instr Executable @ E
    {{{ RET FailedV; PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ w ∗ cnull ↦ᵣ wn }}}.
  Proof.
    iIntros (Hdecode Hvpc φ) "(>HPC & >Hmem & >Hn) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hn") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - incrementPC_inv; simplify_map_eq.
    - simplify_eq. iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hn]"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  Lemma wp_ClearTag_toPC_failure E pc_p pc_g pc_b pc_e pc_a w src ws :
    decodeInstrW w = ClearTag PC src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap ws = false →
    src ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ ▷ pc_a ↦ₐ w ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hcap Hne φ) "(>HPC & >Hmem & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iApply (wp_ClearTag with "[$Hmap Hmem]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [|].
    - destruct ws as [| [] | |]; cbn in Hcap; try done;
        incrementPC_inv; simplify_map_eq.
    - by iApply "Hφ".
  Qed.

End griotte_lang_rules.
