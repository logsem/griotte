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
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* The sealed word keeps the identifier of its payload. *)
  Inductive Seal_failure (regs: LReg) (dst: RegName) (src1 src2: RegName) : LReg → Prop :=
  | Seal_fail_sealr w :
      regs !!ₗ src1 = Some w →
      is_sealr w.(lw) = false →
      Seal_failure regs dst src1 src2 regs
  | Seal_fail_sealb w :
      regs !!ₗ src2 = Some w →
      is_sealb w.(lw) = false →
      Seal_failure regs dst src1 src2 regs
  | Seal_fail_invalidated_PC (t : bool) p g b e a π1 sb π :
      regs !!ₗ src1 = Some (WSealRange t p g b e a @@? π1) →
      regs !!ₗ src2 = Some (WSealable sb @@? π) →
      t && get_tag_sealable sb && permit_seal p && withinBounds b e a = false →
      incrementPC (<[ dst := WSealed a (clear_tag_sealable sb) @@? π ]ₗ> regs) = None →
      Seal_failure regs dst src1 src2 regs
  | Seal_fail_incrPC p g b e a π1 sb π :
      regs !!ₗ src1 = Some (WSealRange true p g b e a @@? π1) →
      regs !!ₗ src2 = Some (WSealable sb @@? π) →
      get_tag_sealable sb = true →
      permit_seal p = true →
      withinBounds b e a = true →
      incrementPC (<[ dst := WSealed a sb @@? π ]ₗ> regs) = None →
      Seal_failure regs dst src1 src2 regs.

  Inductive Seal_spec (regs: LReg) (dst: RegName) (src1 src2: RegName) (regs': LReg): griotte_lang.val -> Prop :=
  | Seal_spec_success p g b e a π1 sb π:
      regs !!ₗ src1 = Some (WSealRange true p g b e a @@? π1) →
      regs !!ₗ src2 = Some (WSealable sb @@? π) →
      get_tag_sealable sb = true →
      permit_seal p = true →
      withinBounds b e a = true →
      incrementPC (<[ dst := WSealed a sb @@? π ]ₗ> regs) = Some regs' →
      Seal_spec regs dst src1 src2 regs' NextIV
  | Seal_spec_invalidated (t : bool) p g b e a π1 sb π :
      regs !!ₗ src1 = Some (WSealRange t p g b e a @@? π1) →
      regs !!ₗ src2 = Some (WSealable sb @@? π) →
      t && get_tag_sealable sb && permit_seal p && withinBounds b e a = false →
      incrementPC (<[ dst := WSealed a (clear_tag_sealable sb) @@? π ]ₗ> regs) = Some regs' →
      Seal_spec regs dst src1 src2 regs' NextIV
  | Seal_spec_failure :
      Seal_failure regs dst src1 src2 regs' →
      Seal_spec regs dst src1 src2 regs' FailedV.

  (* The sealed word keeps the bounds of its payload and never gains a tag. *)
  Lemma reg_word_ok_seal R C (sb sb' : Sealable) π o :
    (sb' = sb ∨ sb' = clear_tag_sealable sb) →
    reg_word_ok R C (WSealable sb @@? π) →
    reg_word_ok R C (WSealed o sb' @@? π).
  Proof.
    intros Hsb. apply (reg_word_ok_derive _ _ (WSealable sb @@? π)); cbn.
    - left. destruct Hsb as [-> | ->]; by destruct sb.
    - destruct Hsb as [-> | ->]; first done. by rewrite get_tag_clear_tag_sealable.
  Qed.

  Lemma wp_Seal Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs :
    decodeInstrW w.(lw) = Seal dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Seal dst src1 src2) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Seal_spec regs dst src1 src2 regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    odestruct (Hri src2) as [r2v [Hr2 _]]; first by set_solver+.
    odestruct (Hri src1) as [r1v [Hr1 _]]; first by set_solver+.
    clear Hri.
    assert (lookup_reg src1 r = Some r1v.(lw)) as Hr1'.
    { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase Hr1. }
    assert (lookup_reg src2 r = Some r2v.(lw)) as Hr2'.
    { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase Hr2. }
    rewrite /exec /= Hr2' Hr1' /= in Hstep.
    destruct (is_sealr r1v.(lw)) eqn:Hr1v.
    2:{ assert (c = Failed ∧ σ' = (r, sr, m, st)) as [-> ->].
        { unfold is_sealr in Hr1v. destruct r1v as [[|[]| |] ?]; cbn in *; by simplify_pair_eq. }
        iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
        iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
        econstructor. by eapply Seal_fail_sealr. }
    destruct r1v as [[ | [ | t p g b e a ] | | ] π1]; try inversion Hr1v. clear Hr1v.
    destruct (is_sealb r2v.(lw)) eqn:Hr2v.
    2:{ assert (c = Failed ∧ σ' = (r, sr, m, st)) as [-> ->].
        { unfold is_sealb in Hr2v. destruct r2v as [[|[]| |] ?]; cbn in *; by simplify_pair_eq. }
        iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
        iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
        econstructor. by eapply Seal_fail_sealb. }
    destruct r2v as [[ | sb | | ] π]; try inversion Hr2v. clear Hr2v.
    assert (reg_word_ok R C (WSealable sb @@? π)) as Hok.
    { by eapply erasure_llookup_reg_word. }
    cbn in Hstep.
    destruct (t && get_tag_sealable sb && permit_seal p && withinBounds b e a) eqn:Hvalid.
    - apply andb_true_iff in Hvalid as [Hvalid Hwb].
      apply andb_true_iff in Hvalid as [Hvalid Hps].
      apply andb_true_iff in Hvalid as [-> Htag].
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst (WSealed a sb @@? π) _ _ _
        (λ regs' retv, Seal_spec regs dst src1 src2 regs' retv)
        with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
      { apply (reg_word_ok_seal _ _ sb); auto. } { exact Hstep. }
      { intros. by eapply Seal_spec_success. }
      { intros. econstructor. by eapply Seal_fail_incrPC. }
      iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
    - iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst
        (WSealed a (clear_tag_sealable sb) @@? π) _ _ _
        (λ regs' retv, Seal_spec regs dst src1 src2 regs' retv)
        with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
      { apply (reg_word_ok_seal _ _ sb); auto. } { exact Hstep. }
      { intros. by eapply Seal_spec_invalidated. }
      { intros. econstructor. by eapply Seal_fail_invalidated_PC. }
      iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  (* after pruning impossible or impractical options, 5 wp rules remain *)

  Lemma wp_seal_success E pc_p pc_g pc_b pc_e pc_a pc_π w w' dst r1 r2 p g b e a sb pc_a' πs π :
    decodeInstrW w.(lw) = Seal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ w'
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WSealed a sb @@? π
          ∗ r1 ↦ᵣ WSealRange true p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealable sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull' Hncull'' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq; simplify_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
  Qed.

  Lemma wp_seal_r1 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a sb pc_a' πs π :
    decodeInstrW w.(lw) = Seal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealed a sb @@? π
          ∗ r2 ↦ᵣ WSealable sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq; simplify_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_r2 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a sb pc_a' πs π :
    decodeInstrW w.(lw) = Seal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealRange true p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealed a sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq; simplify_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ r2 PC) // insert_insert_eq (insert_insert_ne _ r1 r2) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  (* the 2 rules where r2=PC (and d=r1 or d≠r2) are also admissible *)

  Lemma wp_seal_PC E pc_p pc_g pc_b pc_e pc_a pc_π w w' dst r1 p g b e a pc_a' πs :
    decodeInstrW w.(lw) = Seal dst r1 PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ w'
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WSealed a (SCap true pc_p pc_g pc_b pc_e pc_a) @@? pc_π
          ∗ r1 ↦ᵣ WSealRange true p g b e a @@? πs
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hr1") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq; simplify_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ dst PC) // insert_insert_eq insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

 Lemma wp_seal_PC_eq E pc_p pc_g pc_b pc_e pc_a pc_π w w' r1 p g b e a pc_a' πs :
    decodeInstrW w.(lw) = Seal r1 r1 PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealed a (SCap true pc_p pc_g pc_b pc_e pc_a) @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq; simplify_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ r1 PC) // !insert_insert_eq.
      iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_nosb_r2 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a (w2 : LWord) pc_a' πs :
    decodeInstrW w.(lw) = Seal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    is_sealb w2.(lw) = false →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
          ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hfalse Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ]; last by iApply "Hφ".
    all: by simplify_lmap_eq.
  Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  Local Lemma seal_invalidated_map E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src1 src2 regs regs' (t : bool) p g b e a πs sb π :
    decodeInstrW w.(lw) = Seal dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Seal dst src1 src2) ⊆ dom regs →
    regs !!ₗ src1 = Some (WSealRange t p g b e a @@? πs) →
    regs !!ₗ src2 = Some (WSealable sb @@? π) →
    t && get_tag_sealable sb && permit_seal p && withinBounds b e a = false →
    incrementPC (<[ dst := WSealed a (clear_tag_sealable sb) @@? π ]ₗ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hr1 Hr2 Hvalid Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Seal with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | Hfail].
    - simplify_eq.
      repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    - simplify_eq. iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; cbn in *; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
  Qed.

  (* Seal: include shared sources, destination aliases, PC sources, and cnull. *)
  Lemma wp_seal_invalidated E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a r2 sb dst (wd : LWord) πs π :
    decodeInstrW w.(lw) = Seal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π
        ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealable sb @@? π
        ∗ dst ↦ᵣ (if decide (dst = cnull) then lnull else WSealed a (clear_tag_sealable (sb)) @@? π) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (seal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealRange t p g b e a @@? πs]> (<[r2 := WSealable sb @@? π]> (<[dst := (if decide (dst
        = cnull) then lnull else WSealed a (clear_tag_sealable (sb)) @@? π)]> (∅ : LReg))))) t p g b e a _ (sb) _ with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_4 with "Hmap"); eauto.
  Qed.

  Lemma wp_seal_invalidated_r1 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a r2 sb πs π :
    decodeInstrW w.(lw) = Seal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealed a (clear_tag_sealable (sb)) @@? π
        ∗ r2 ↦ᵣ WSealable sb @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (seal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealed a (clear_tag_sealable (sb)) @@? π]> (<[r2 := WSealable sb @@? π]> (∅ : LReg))))
        t p g b e a _ (sb) _ with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_seal_invalidated_r2 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a r2 sb πs π :
    decodeInstrW w.(lw) = Seal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealed a (clear_tag_sealable (sb)) @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (seal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealRange t p g b e a @@? πs]> (<[r2 := WSealed a (clear_tag_sealable (sb)) @@? π]> (∅ : LReg)))) t p g b e a _ (sb) _ with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_seal_invalidated_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a dst (wd : LWord) πs :
    decodeInstrW w.(lw) = Seal dst r1 r1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SSealRange t p g b e a) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ dst ↦ᵣ (if decide (dst = cnull) then lnull else WSealed a (clear_tag_sealable (SSealRange t p g b e a)) @@? πs) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (seal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealRange t p g b e a @@? πs]> (<[dst := (if decide (dst = cnull) then lnull else WSealed a (clear_tag_sealable (SSealRange t p g b e a)) @@? πs)]> (∅ : LReg)))) t p g b e a _ (SSealRange t p g b e a) _ with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_seal_invalidated_all E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a πs :
    decodeInstrW w.(lw) = Seal r1 r1 r1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SSealRange t p g b e a) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealed a (clear_tag_sealable (SSealRange t p g b e a)) @@? πs }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (seal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealed a (clear_tag_sealable (SSealRange t p g b e a)) @@? πs]> (∅ : LReg))) t p g b e a _ (SSealRange t p g b e a) _ with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_seal_invalidated_PC E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a dst (wd : LWord) πs :
    decodeInstrW w.(lw) = Seal dst r1 PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ dst ↦ᵣ (if decide (dst = cnull) then lnull else WSealed a (clear_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a)) @@? pc_π) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (seal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealRange t p g b e a @@? πs]> (<[dst := (if decide (dst = cnull) then lnull else WSealed a (clear_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a)) @@? pc_π)]> (∅ : LReg)))) t p g b e a _ (SCap true pc_p pc_g pc_b pc_e pc_a) _ with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_seal_invalidated_PC_eq E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a πs :
    decodeInstrW w.(lw) = Seal r1 r1 PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealed a (clear_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a)) @@? pc_π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (seal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealed a (clear_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a)) @@? pc_π]> (∅ : LReg))) t p g b e a _ (SCap true pc_p pc_g pc_b pc_e pc_a) _ with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.
End instruction_outcomes.
