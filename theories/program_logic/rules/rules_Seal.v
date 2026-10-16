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
  Inductive Seal_failure (lpc : LWord) (regs: LReg) (dst: RegName) (src1 src2: RegName) :
    LWord → LReg → Prop :=
  | Seal_fail_sealr w :
      regs !!ₗ src1 = Some w →
      is_sealr w.(lw) = false →
      Seal_failure lpc regs dst src1 src2 lpc regs
  | Seal_fail_sealb w :
      regs !!ₗ src2 = Some w →
      is_sealb w.(lw) = false →
      Seal_failure lpc regs dst src1 src2 lpc regs
  | Seal_fail_invalidated_PC (t : bool) p g b e a π1 sb π :
      regs !!ₗ src1 = Some (WSealRange t p g b e a @@? π1) →
      regs !!ₗ src2 = Some (WSealable sb @@? π) →
      t && get_tag_sealable sb && permit_seal p && withinBounds b e a = false →
      incrementPC lpc = None →
      Seal_failure lpc regs dst src1 src2 lpc regs
  | Seal_fail_incrPC p g b e a π1 sb π :
      regs !!ₗ src1 = Some (WSealRange true p g b e a @@? π1) →
      regs !!ₗ src2 = Some (WSealable sb @@? π) →
      get_tag_sealable sb = true →
      permit_seal p = true →
      withinBounds b e a = true →
      incrementPC lpc = None →
      Seal_failure lpc regs dst src1 src2 lpc regs.

  Inductive Seal_spec (lpc : LWord) (regs: LReg) (dst: RegName) (src1 src2: RegName)
    (lpc' : LWord) (regs': LReg): griotte_lang.val -> Prop :=
  | Seal_spec_success p g b e a π1 sb π:
      regs !!ₗ src1 = Some (WSealRange true p g b e a @@? π1) →
      regs !!ₗ src2 = Some (WSealable sb @@? π) →
      get_tag_sealable sb = true →
      permit_seal p = true →
      withinBounds b e a = true →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WSealed a sb @@? π ]ₗ> regs →
      Seal_spec lpc regs dst src1 src2 lpc' regs' NextIV
  | Seal_spec_invalidated (t : bool) p g b e a π1 sb π :
      regs !!ₗ src1 = Some (WSealRange t p g b e a @@? π1) →
      regs !!ₗ src2 = Some (WSealable sb @@? π) →
      t && get_tag_sealable sb && permit_seal p && withinBounds b e a = false →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WSealed a (clear_tag_sealable sb) @@? π ]ₗ> regs →
      Seal_spec lpc regs dst src1 src2 lpc' regs' NextIV
  | Seal_spec_failure :
      Seal_failure lpc regs dst src1 src2 lpc' regs' →
      Seal_spec lpc regs dst src1 src2 lpc' regs' FailedV.

  (* The sealed word keeps the bounds of its payload and never gains a tag. *)
  Lemma reg_word_ok_seal R C (sb sb' : Sealable) π o :
    (sb' = sb ∨ sb' = clear_tag_sealable sb) →
    reg_word_ok R C (WSealable sb @@? π) →
    reg_word_ok R C (WSealed o sb' @@? π).
  Proof.
    intros Hsb. apply (reg_word_ok_derive _ _ (WSealable sb @@? π)); cbn.
    - left. destruct Hsb as [-> | ->]; by destruct sb.
    - destruct Hsb as [-> | ->]; first done. by rewrite get_tag_clear_tag_sealable.
    - destruct Hsb as [-> | ->]; by destruct sb.
  Qed.

  Lemma wp_Seal Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs dq :
    decodeInstrW w.(lw) = Seal dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Seal dst src1 src2) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Seal_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "Hσ"; iNamed "Hσ".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    odestruct (Hri src2) as [r2v [Hr2 _]]; first by set_solver+.
    odestruct (Hri src1) as [r1v [Hr1 _]]; first by set_solver+.
    clear Hri.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr1) as (s1 & Hr1' & Hrel1).
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr2) as (s2 & Hr2' & Hrel2).
    rewrite /exec /= Hr2' Hr1' /= in Hstep.
    destruct (is_sealr r1v.(lw)) eqn:Hr1v.
    2:{ assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as [-> ->].
        { unfold is_sealr in Hr1v. destruct r1v as [[|[]| |] ?]; cbn in *; by simplify_pair_eq. }
        instr_fail_close. econstructor. by eapply Seal_fail_sealr. }
    destruct r1v as [[ | [ | t p g b e a ] | | ] π1]; try inversion Hr1v. clear Hr1v.
    (* The sealing key has no bounds: its copy is exact. *)
    pose proof (reg_phys_no_bounds R (WSealRange t p g b e a @@? π1) _ eq_refl Hrel1) as Hk. cbn in Hk.
    assert (s1 && t = t) as Hs1 by congruence.
    destruct (is_sealb r2v.(lw)) eqn:Hr2v.
    2:{ assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as [-> ->].
        { unfold is_sealb in Hr2v. destruct r2v as [[|[]| |] ?]; cbn in *; by simplify_pair_eq. }
        instr_fail_close. econstructor. by eapply Seal_fail_sealb. }
    destruct r2v as [[ | sb | | ] π]; try inversion Hr2v. clear Hr2v.
    assert (reg_word_ok R C (WSealable sb @@? π)) as Hok.
    { by eapply erasure_llookup_reg_word. }
    cbn in Hstep. rewrite Hs1 in Hstep.
    destruct (t && get_tag_sealable sb && permit_seal p && withinBounds b e a) eqn:Hvalid.
    - apply andb_true_iff in Hvalid as [Hvalid Hwb].
      apply andb_true_iff in Hvalid as [Hvalid Hps].
      apply andb_true_iff in Hvalid as [-> Htag].
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst (WSealed a sb @@? π) _ _ _ _
        (λ lpc' regs' retv, Seal_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
      { apply (reg_word_ok_seal _ _ sb); auto. } { exact Hstep. }
      { eapply (reg_phys_derive_eq _ (WSealable sb @@? π) s2); [done|by destruct sb|done|].
        destruct s2; rewrite ?and_tag_sealable_true ?and_tag_sealable_false.
        - rewrite Htag Hps Hwb /=. by destruct sb.
        - rewrite get_tag_clear_tag_sealable andb_false_r /=. by destruct sb. }
      { intros. by eapply Seal_spec_success. }
      { intros. econstructor. by eapply Seal_fail_incrPC. }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
    - iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst
        (WSealed a (clear_tag_sealable sb) @@? π) _ _ _ _
        (λ lpc' regs' retv, Seal_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
      { apply (reg_word_ok_seal _ _ sb); auto. } { exact Hstep. }
      { eapply (reg_phys_derive_eq _ (WSealable sb @@? π) s2); [done|by destruct sb|by destruct sb|].
        destruct s2; rewrite ?and_tag_sealable_true ?and_tag_sealable_false.
        - rewrite Hvalid. by destruct sb.
        - rewrite get_tag_clear_tag_sealable andb_false_r /=. by destruct sb. }
      { intros. by eapply Seal_spec_invalidated. }
      { intros. econstructor. by eapply Seal_fail_invalidated_PC. }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (* after pruning impossible or impractical options, 5 wp rules remain *)

  Lemma wp_seal_success E pc_p pc_g pc_b pc_e pc_a pc_π w w' dst r1 r2 p g b e a sb pc_a' πs π dq :
    decodeInstrW w.(lw) = Seal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ w'
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ WSealed a sb @@? π
          ∗ r1 ↦ᵣ WSealRange true p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealable sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull' Hncull'' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Seal with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq; simplify_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence).
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
  Qed.

  Lemma wp_seal_r1 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a sb pc_a' πs π dq :
    decodeInstrW w.(lw) = Seal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ WSealed a sb @@? π
          ∗ r2 ↦ᵣ WSealable sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iApply (wp_Seal with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq; simplify_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
      iRegsMap "Hmap"; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_seal_r2 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a sb pc_a' πs π dq :
    decodeInstrW w.(lw) = Seal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ WSealRange true p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealed a sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iApply (wp_Seal with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq; simplify_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
      iRegsMap "Hmap"; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  #[local] Lemma seal_invalidated_map E pc_p pc_g pc_b pc_e pc_a pc_π pc_a'
      w dst src1 src2 regs (t : bool) p g b e a πs sb π dq :
    decodeInstrW w.(lw) = Seal dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Seal dst src1 src2) ⊆ dom regs →
    regs !!ₗ src1 = Some (WSealRange t p g b e a @@? πs) →
    regs !!ₗ src2 = Some (WSealable sb @@? π) →
    t && get_tag_sealable sb && permit_seal p && withinBounds b e a = false →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[ dst := WSealed a (clear_tag_sealable sb) @@? π ]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hr1 Hr2 Hvalid Hpca' φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Seal with "[$HPC $Hpc_a $Hmap]"); eauto.
    iNext. iIntros (lpc' regs'' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [ | | Hfail].
    - simplify_eq.
      repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    - simplify_eq. try incrementPC_inv; simplify_eq. iApply "Hφ". iFrame.
    - destruct Hfail; try incrementPC_inv; simplify_eq; cbn in *; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
  Qed.

  (* Seal: include shared sources, destination aliases and cnull. *)
  Lemma wp_seal_invalidated E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a r2 sb dst (wd : LWord) πs π dq :
    decodeInstrW w.(lw) = Seal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π
        ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealable sb @@? π
        ∗ dst ↦ᵣ (if decide (dst = cnull) then lnull else WSealed a (clear_tag_sealable (sb)) @@? π) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (seal_invalidated_map E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a _ (sb) _ with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_seal_invalidated_r1 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a r2 sb πs π dq :
    decodeInstrW w.(lw) = Seal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WSealed a (clear_tag_sealable (sb)) @@? π
        ∗ r2 ↦ᵣ WSealable sb @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (seal_invalidated_map E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a _ (sb) _ with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_seal_invalidated_r2 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a r2 sb πs π dq :
    decodeInstrW w.(lw) = Seal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealable sb @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealed a (clear_tag_sealable (sb)) @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (seal_invalidated_map E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a _ (sb) _ with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_seal_invalidated_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a dst (wd : LWord) πs dq :
    decodeInstrW w.(lw) = Seal dst r1 r1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SSealRange t p g b e a) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ dst ↦ᵣ (if decide (dst = cnull) then lnull else WSealed a (clear_tag_sealable (SSealRange t p g b e a)) @@? πs) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (seal_invalidated_map E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a _ (SSealRange t p g b e a) _ with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_seal_invalidated_all E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a πs dq :
    decodeInstrW w.(lw) = Seal r1 r1 r1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SSealRange t p g b e a) && permit_seal p && withinBounds b e a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WSealed a (clear_tag_sealable (SSealRange t p g b e a)) @@? πs }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (seal_invalidated_map E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a _ (SSealRange t p g b e a) _ with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

End instruction_outcomes.
