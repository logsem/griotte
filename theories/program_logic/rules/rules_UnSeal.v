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
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* The unsealed word keeps the identifier of the sealed word. *)
  Inductive UnSeal_failure (lpc : LWord) (regs : LReg) (dst: RegName) (src1 src2: RegName) :
    LWord → LReg → Prop :=
  | UnSeal_fail_PC_untagged w1 w2 :
      regs !!ₗ src1 = Some w1 →
      regs !!ₗ src2 = Some w2 →
      is_sealr w1.(lw) && is_sealed w2.(lw) = false →
      incrementPC lpc = None →
      UnSeal_failure lpc regs dst src1 src2 lpc regs
  | UnSeal_fail_invalidated_PC (t : bool) p g b e a πs a' sb π :
      regs !!ₗ src1 = Some (WSealRange t p g b e a @@? πs) →
      regs !!ₗ src2 = Some (WSealed a' sb @@? π) →
      t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
      incrementPC lpc = None →
      UnSeal_failure lpc regs dst src1 src2 lpc regs
  | UnSeal_fail_incrPC p g b e a πs o sb π :
      regs !!ₗ src1 = Some (SealRange p g b e a @@? πs) →
      regs !!ₗ src2 = Some (WSealed o sb @@? π) →
      get_tag_sealable sb = true →
      permit_unseal p = true →
      withinBounds b e o = true →
      incrementPC lpc = None →
      UnSeal_failure lpc regs dst src1 src2 lpc regs.

  Inductive UnSeal_spec (lpc : LWord) (regs : LReg) (dst: RegName) (src1 src2: RegName)
    (lpc' : LWord) (regs' : LReg): griotte_lang.val -> Prop :=
  | UnSeal_spec_success p g b e a πs o sb π:
      regs !!ₗ src1 = Some (SealRange p g b e a @@? πs) →
      regs !!ₗ src2 = Some (WSealed o sb @@? π) →
      get_tag_sealable sb = true →
      permit_unseal p = true →
      withinBounds b e o = true →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WSealable (unseal_sb g sb) @@? π ]ₗ> regs →
      UnSeal_spec lpc regs dst src1 src2 lpc' regs' NextIV
  | UnSeal_spec_invalidated (t : bool) p g b e a πs a' sb π :
      regs !!ₗ src1 = Some (WSealRange t p g b e a @@? πs) →
      regs !!ₗ src2 = Some (WSealed a' sb @@? π) →
      t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WSealable (clear_tag_sealable (unseal_sb g sb)) @@? π ]ₗ> regs →
      UnSeal_spec lpc regs dst src1 src2 lpc' regs' NextIV
  (* Without a sealing range and a sealed word, the operand loses its tag and
     is not unsealed. *)
  | UnSeal_spec_untagged w1 w2 :
      regs !!ₗ src1 = Some w1 →
      regs !!ₗ src2 = Some w2 →
      is_sealr w1.(lw) && is_sealed w2.(lw) = false →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := lclear_tag w2 ]ₗ> regs →
      UnSeal_spec lpc regs dst src1 src2 lpc' regs' NextIV
  | UnSeal_spec_failure :
      UnSeal_failure lpc regs dst src1 src2 lpc' regs' →
      UnSeal_spec lpc regs dst src1 src2 lpc' regs' FaultedV.

  (* The unsealed word keeps the bounds and the permissions of the sealed one
     and never gains a tag. *)
  Lemma reg_word_ok_unseal R C (sb sb' : Sealable) π o :
    (memory_cap_bounds (WSealable sb') = memory_cap_bounds (WSealed o sb)) →
    (get_tag_sealable sb' = true → get_tag_sealable sb = true) →
    executable_word (WSealable sb') = executable_word (WSealed o sb) →
    reg_word_ok R C (WSealed o sb @@? π) →
    reg_word_ok R C (WSealable sb' @@? π).
  Proof.
    intros Hb Ht Hx. apply (reg_word_ok_derive _ _ (WSealed o sb @@? π)).
    - cbn; auto.
    - cbn; auto.
    - intros _ Hx'. rewrite -Hx. exact Hx'.
  Qed.

  Lemma wp_UnSeal Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs dq :
    decodeInstrW w.(lw) = UnSeal dst src1 src2 ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ UnSeal_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    odestruct (Hri src2) as [r2v [Hr2 _] ]; first by set_solver+.
    odestruct (Hri src1) as [r1v [Hr1 _] ]; first by set_solver+.
    clear Hri.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr1) as (s1 & Hr1' & Hrel1).
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr2) as (s2 & Hr2' & Hrel2).
    rewrite /exec /= Hr2' Hr1' /= in Hstep.
    destruct (decide (is_sealr r1v.(lw) && is_sealed r2v.(lw) = false)) as [Hk | Hk].
    { iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (lclear_tag r2v) (clear_tag r2v.(lw)) _ _ _
        (λ lpc' regs' retv, UnSeal_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
      { apply reg_word_ok_lclear_tag. }
      { rewrite -Hstep.
        by destruct r1v as [ [| [] | | ? [] ] ?], r2v as [ [| [] | | ? [] ] ?], s1, s2. }
      { apply reg_phys_lclear_tag in Hrel2. by rewrite clear_tag_and_tag in Hrel2. }
      { intros. by eapply UnSeal_spec_untagged. }
      { intros. econstructor. by eapply UnSeal_fail_PC_untagged. }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame. }
    apply not_false_is_true, andb_true_iff in Hk as [Hr1v Hr2v].
    destruct r1v as [ [ | [ | t p g b e a ] | | ] πs]; try inversion Hr1v. clear Hr1v.
    (* The unsealing key has no bounds: its copy is exact. *)
    pose proof (reg_phys_no_bounds R (WSealRange t p g b e a @@? πs) _ eq_refl Hrel1) as Hk. cbn in Hk.
    assert (s1 && t = t) as Hs1 by congruence.
    destruct r2v as [ [ | | | o sb ] π]; try inversion Hr2v. clear Hr2v.
    assert (reg_word_ok R C (WSealed o sb @@? π)) as Hok.
    { by eapply erasure_llookup_reg_word. }
    cbn in Hstep. rewrite Hs1 in Hstep.
    destruct (t && get_tag_sealable sb && permit_unseal p && withinBounds b e o) eqn:Hvalid.
    - apply andb_true_iff in Hvalid as [Hvalid Hwb].
      apply andb_true_iff in Hvalid as [Hvalid Hps].
      apply andb_true_iff in Hvalid as [-> Htag].
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst
        (WSealable (unseal_sb g sb) @@? π) _ _ _ _
        (λ lpc' regs' retv, UnSeal_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
      { apply (reg_word_ok_unseal _ _ sb _ _ o); auto; by destruct sb. }
      { exact Hstep. }
      { eapply (reg_phys_derive_eq _ (WSealed o sb @@? π) s2); [done|by destruct sb|by destruct sb|].
        destruct s2; rewrite ?and_tag_sealable_true ?and_tag_sealable_false.
        - rewrite Htag Hps Hwb /=. by destruct sb.
        - rewrite get_tag_clear_tag_sealable andb_false_r /=. by destruct sb. }
      { intros. by eapply UnSeal_spec_success. }
      { intros. econstructor. by eapply UnSeal_fail_incrPC. }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
    - iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst
        (WSealable (clear_tag_sealable (unseal_sb g sb)) @@? π) _ _ _ _
        (λ lpc' regs' retv, UnSeal_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
      { apply (reg_word_ok_unseal _ _ sb _ _ o); auto; by destruct sb. }
      { exact Hstep. }
      { eapply (reg_phys_derive_eq _ (WSealed o sb @@? π) s2); [done|by destruct sb|by destruct sb|].
        destruct s2; rewrite ?and_tag_sealable_true ?and_tag_sealable_false.
        - rewrite Hvalid. by destruct sb.
        - rewrite get_tag_clear_tag_sealable andb_false_r /=. by destruct sb. }
      { intros. by eapply UnSeal_spec_invalidated. }
      { intros. econstructor. by eapply UnSeal_fail_invalidated_PC. }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_unseal_success E pc_p pc_g pc_b pc_e pc_a pc_π w w' dst r1 r2 p g b e a o sb pc_a' πs π dq :
    decodeInstrW w.(lw) = UnSeal dst r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ w'
        ∗ ▷ r1 ↦ᵣ SealRange p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ WSealable (unseal_sb g sb) @@? π
          ∗ r1 ↦ᵣ SealRange p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealed o sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ??? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    all: try (by unfold regs_of, operands_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ? ? ? ? ? ? ? | * Hfail].
    3: (simplify_lmap_eq; by simplify_eq).
    2: (simplify_lmap_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_unseal_r1 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a o sb pc_a' πs π dq :
    decodeInstrW w.(lw) = UnSeal r1 r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ SealRange p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ WSealable (unseal_sb g sb) @@? π
          ∗ r2 ↦ᵣ WSealed o sb @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iApply (wp_UnSeal with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    all: try (by unfold regs_of, operands_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ? ? ? ? ? ? ? | * Hfail].
    3: (simplify_lmap_eq; by simplify_eq).
    2: (simplify_lmap_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
      iRegsMap "Hmap"; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_unseal_r2 E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 p g b e a o sb pc_a' πs π dq :
    decodeInstrW w.(lw) = UnSeal r2 r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ SealRange p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o sb @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ SealRange p g b e a @@? πs
          ∗ r2 ↦ᵣ WSealable (unseal_sb g sb) @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iApply (wp_UnSeal with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    all: try (by unfold regs_of, operands_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | ? ? ? ? ? ? ? | * Hfail].
    3: (simplify_lmap_eq; by simplify_eq).
    2: (simplify_lmap_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
      iRegsMap "Hmap"; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.


End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {CL : CritLink Σ}.

  #[local] Lemma unseal_invalidated_map E pc_p pc_g pc_b pc_e pc_a pc_π pc_a''
      w dst src1 src2 regs (t : bool) p g b e a πs a' sb π dq :
    decodeInstrW w.(lw) = UnSeal dst src1 src2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →
    regs !!ₗ src1 = Some (WSealRange t p g b e a @@? πs) →
    regs !!ₗ src2 = Some (WSealed a' sb @@? π) →
    t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
    (pc_a + 1)%a = Some pc_a'' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a'' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[ dst := WSealable (clear_tag_sealable (unseal_sb g sb)) @@? π ]ₗ> regs,
          k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hr1 Hr2 Hvalid Hpca' φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_UnSeal with "[$HPC $Hpc_a $Hmap]"); eauto.
    iNext. iIntros (lpc' regs'' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [ | | ? ? ? ? ? ? ? | Hfail].
    - simplify_eq.
      repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    - simplify_eq. try incrementPC_inv; simplify_eq. iApply "Hφ". iFrame.
    - by simplify_eq.
    - destruct Hfail; try incrementPC_inv; simplify_eq; cbn in *; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
  Qed.

  Lemma wp_unseal_invalidated E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 r2 (t : bool) p g b e a πs π (o :
      OType) sb dst (wd : LWord) dq :
    decodeInstrW w.(lw) = UnSeal dst r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o (sb) @@? π
        ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealed o (sb) @@? π
        ∗ dst ↦ᵣ (if decide (dst = cnull) then wd else WSealable (clear_tag_sealable (unseal_sb g sb)) @@? π) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a _ o (sb) _ with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /operands_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; case_decide; iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_unseal_invalidated_r1 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 r2 (t : bool) p g b e a πs π (o :
      OType) sb dq :
    decodeInstrW w.(lw) = UnSeal r1 r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o (sb) @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WSealable (clear_tag_sealable (unseal_sb g sb)) @@? π
        ∗ r2 ↦ᵣ WSealed o (sb) @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (unseal_invalidated_map E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a _ o (sb) _ with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /operands_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_unseal_invalidated_r2 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 r2 (t : bool) p g b e a πs π (o :
      OType) sb dq :
    decodeInstrW w.(lw) = UnSeal r2 r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ ▷ r2 ↦ᵣ WSealed o (sb) @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ r1 ↦ᵣ WSealRange t p g b e a @@? πs
        ∗ r2 ↦ᵣ WSealable (clear_tag_sealable (unseal_sb g sb)) @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (unseal_invalidated_map E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a _ o (sb) _ with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /operands_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

End instruction_outcomes.
