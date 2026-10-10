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

  (* The unsealed word keeps the identifier of the sealed word. *)
  Inductive UnSeal_failure  (regs : LReg) (dst: RegName) (src1 src2: RegName) : LReg → Prop :=
  | UnSeal_fail_sealr w :
      regs !!ₗ src1 = Some w →
      is_sealr w.(lw) = false →
      UnSeal_failure regs dst src1 src2 regs
  | UnSeal_fail_sealed w :
      regs !!ₗ src2 = Some w →
      is_sealed w.(lw) = false →
      UnSeal_failure regs dst src1 src2 regs
  | UnSeal_fail_invalidated_PC (t : bool) p g b e a πs a' sb π :
      regs !!ₗ src1 = Some (WSealRange t p g b e a @@? πs) →
      regs !!ₗ src2 = Some (WSealed a' sb @@? π) →
      t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
      incrementPC (<[ dst := WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π ]ₗ> regs) = None →
      UnSeal_failure regs dst src1 src2 regs
  | UnSeal_fail_incrPC p g b e a πs o sb π :
      regs !!ₗ src1 = Some (WSealRange true p g b e a @@? πs) →
      regs !!ₗ src2 = Some (WSealed o sb @@? π) →
      get_tag_sealable sb = true →
      permit_unseal p = true →
      withinBounds b e o = true →
      incrementPC (<[ dst := WSealable (machine_word.unseal g sb) @@? π ]ₗ> regs) = None →
      UnSeal_failure regs dst src1 src2 regs.

  Inductive UnSeal_spec (regs : LReg) (dst: RegName) (src1 src2: RegName) (regs' : LReg): griotte_lang.val -> Prop :=
  | UnSeal_spec_success p g b e a πs o sb π:
      regs !!ₗ src1 = Some (WSealRange true p g b e a @@? πs) →
      regs !!ₗ src2 = Some (WSealed o sb @@? π) →
      get_tag_sealable sb = true →
      permit_unseal p = true →
      withinBounds b e o = true →
      incrementPC (<[ dst := WSealable (machine_word.unseal g sb) @@? π ]ₗ> regs) = Some regs' →
      UnSeal_spec regs dst src1 src2 regs' NextIV
  | UnSeal_spec_invalidated (t : bool) p g b e a πs a' sb π :
      regs !!ₗ src1 = Some (WSealRange t p g b e a @@? πs) →
      regs !!ₗ src2 = Some (WSealed a' sb @@? π) →
      t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
      incrementPC (<[ dst := WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π ]ₗ> regs) = Some regs' →
      UnSeal_spec regs dst src1 src2 regs' NextIV
  | UnSeal_spec_failure :
      UnSeal_failure regs dst src1 src2 regs' →
      UnSeal_spec regs dst src1 src2 regs' FailedV.

  (* The unsealed word keeps the bounds of the sealed one and never gains a tag. *)
  Lemma reg_word_ok_unseal R C (sb sb' : Sealable) π o :
    (memory_cap_bounds (WSealable sb') = memory_cap_bounds (WSealed o sb)) →
    (get_tag_sealable sb' = true → get_tag_sealable sb = true) →
    reg_word_ok R C (WSealed o sb @@? π) →
    reg_word_ok R C (WSealable sb' @@? π).
  Proof.
    intros Hb Ht. apply (reg_word_ok_derive _ _ (WSealed o sb @@? π)); cbn; auto.
  Qed.

  Lemma wp_UnSeal Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs :
    decodeInstrW w.(lw) = UnSeal dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ UnSeal_spec regs dst src1 src2 regs' retv ⌝ ∗
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
        econstructor. by eapply UnSeal_fail_sealr. }
    destruct r1v as [[ | [ | t p g b e a ] | | ] πs]; try inversion Hr1v. clear Hr1v.
    destruct (is_sealed r2v.(lw)) eqn:Hr2v.
    2:{ assert (c = Failed ∧ σ' = (r, sr, m, st)) as [-> ->].
        { unfold is_sealed in Hr2v. destruct r2v as [[|[]| |] ?]; cbn in *; by simplify_pair_eq. }
        iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
        iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
        econstructor. by eapply UnSeal_fail_sealed. }
    destruct r2v as [[ | | | o sb ] π]; try inversion Hr2v. clear Hr2v.
    assert (reg_word_ok R C (WSealed o sb @@? π)) as Hok.
    { by eapply erasure_llookup_reg_word. }
    cbn in Hstep.
    destruct (t && get_tag_sealable sb && permit_unseal p && withinBounds b e o) eqn:Hvalid.
    - apply andb_true_iff in Hvalid as [Hvalid Hwb].
      apply andb_true_iff in Hvalid as [Hvalid Hps].
      apply andb_true_iff in Hvalid as [-> Htag].
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst
        (WSealable (machine_word.unseal g sb) @@? π) _ _ _
        (λ regs' retv, UnSeal_spec regs dst src1 src2 regs' retv)
        with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
      { apply (reg_word_ok_unseal _ _ sb _ _ o); auto.
        by destruct sb.
      }
      { exact Hstep. }
      { intros. by eapply UnSeal_spec_success. }
      { intros. econstructor. by eapply UnSeal_fail_incrPC. }
      iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
    - iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst
        (WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π) _ _ _
        (λ regs' retv, UnSeal_spec regs dst src1 src2 regs' retv)
        with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
      { apply (reg_word_ok_unseal _ _ sb _ _ o); auto.
        - by destruct sb.
        - by rewrite get_tag_clear_tag_sealable. }
      { exact Hstep. }
      { intros. by eapply UnSeal_spec_invalidated. }
      { intros. econstructor. by eapply UnSeal_fail_invalidated_PC. }
      iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_unseal_success E pc_p pc_g pc_b pc_e pc_a pc_π w w' dst r1 r2 p g b e a o sb pc_a' πs π :
    decodeInstrW w.(lw) = UnSeal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ w'
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WSealable (machine_word.unseal g sb) @@? π
          ∗ r1 ↦ᵣ WSealRange true p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealed o sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ??? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_unseal_r1 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a o sb pc_a' πs π :
    decodeInstrW w.(lw) = UnSeal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealable (machine_word.unseal g sb) @@? π
          ∗ r2 ↦ᵣ WSealed o sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_unseal_r2 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a o sb pc_a' πs π :
    decodeInstrW w.(lw) = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealRange true p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealable (machine_word.unseal g sb) @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ r2 PC) // insert_insert_eq (insert_insert_ne _ r1 r2) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  (* The below case could be useful, if what we unseal is a PC capability *)
  Lemma wp_unseal_PC E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a o p' g' b' e' a' a'' πs π :
    decodeInstrW w.(lw) = UnSeal PC r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    permit_unseal p = true →
    withinBounds b e o = true →
    (a' + 1)%a = Some a'' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o (SCap true p' g' b' e' a') @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true p' (unseal_locality g g') b' e' a'' @@? π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealRange true p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealed o (SCap true p' g' b' e' a') @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_lmap_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite !insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  Local Lemma unseal_invalidated_map E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src1 src2 regs regs' (t : bool) p g b e a πs a' sb π :
    decodeInstrW w.(lw) = UnSeal dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →
    regs !!ₗ src1 = Some (WSealRange t p g b e a @@? πs) →
    regs !!ₗ src2 = Some (WSealed a' sb @@? π) →
    t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
    incrementPC (<[ dst := WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π ]ₗ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hr1 Hr2 Hvalid Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_UnSeal with "[$Hpc_a $Hmap]"); eauto.
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

  (* UnSeal: the PC-destination case advances the unsealed payload current address. *)
  Lemma wp_unseal_invalidated E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 r2 (t : bool) p g b e a πs π (o :
      OType) sb dst (wd : LWord) :
    decodeInstrW w.(lw) = UnSeal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o (sb) @@? π
        ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealed o (sb) @@? π
        ∗ dst ↦ᵣ (if decide (dst = cnull) then lnull else WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealRange t p g b e a @@? πs]> (<[r2 := WSealed o (sb) @@? π]> (<[dst := (if decide
        (dst = cnull) then lnull else WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π)]> (∅ : LReg))))) t p g b e a _ o (sb) _ with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_unseal_invalidated_r1 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 r2 (t : bool) p g b e a πs π (o :
      OType) sb :
    decodeInstrW w.(lw) = UnSeal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o (sb) @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π
        ∗ r2 ↦ᵣ WSealed o (sb) @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π]> (<[r2 := WSealed o (sb) @@? π]> (∅ : LReg)))) t p g b e a _ o (sb) _ with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_unseal_invalidated_r2 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 r2 (t : bool) p g b e a πs π (o :
      OType) sb :
    decodeInstrW w.(lw) = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o (sb) @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := WSealRange t p g b e a @@? πs]> (<[r2 := WSealable (clear_tag_sealable (machine_word.unseal g sb)) @@? π]> (∅ : LReg)))) t p g b e a _ o (sb) _ with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_unseal_invalidated_PC E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 r2 (t : bool) p g b e a πs π (o :
      OType) (t' : bool) p' g' b' e' a' :
    decodeInstrW w.(lw) = UnSeal PC r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (a' + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (SCap t' p' g' b' e' a') && permit_unseal p && withinBounds b e o = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o (SCap t' p' g' b' e' a') @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false p' (unseal_locality g g') b' e' pc_a' @@? π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealed o (SCap t' p' g' b' e' a') @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false p' (unseal_locality g g') b' e' pc_a' @@? π]>
        (<[r1 := WSealRange t p g b e a @@? πs]> (<[r2 := WSealed o (SCap t' p' g' b' e' a') @@? π]> (∅ : LReg))))
        t p g b e a _ o (SCap t' p' g' b' e' a') _ with "[$Hmem $Hmap]"); eauto;
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
End instruction_outcomes.
