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
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  Inductive Restrict_failure (lpc : LWord) (regs : LReg) (dst src : RegName) (arg : Z + RegName) :=
  | Restrict_fail_PC_overflow_other w:
      regs !!ₗ src = Some w →
      is_mutable_range w.(lw) = false →
      incrementPC lpc = None →
      Restrict_failure lpc regs dst src arg
  | Restrict_fail_invalidated_PC_cap (t : bool) p g b e a π n p' g':
      regs !!ₗ src = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs arg = Some n →
      (p',g') = (decodePermPair n) ->
      (PermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      incrementPC lpc = None →
      Restrict_failure lpc regs dst src arg
  | Restrict_fail_PC_overflow_cap (t : bool) p g b e a π n p' g':
      regs !!ₗ src = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs arg = Some n →
      (p',g') = (decodePermPair n) ->
      PermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      incrementPC lpc = None →
      Restrict_failure lpc regs dst src arg
  | Restrict_fail_invalidated_PC_sr (t : bool) p g b e a π n p' g':
      regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs arg = Some n →
      (p',g') = (decodeSealPermPair n) ->
      (SealPermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      incrementPC lpc = None →
      Restrict_failure lpc regs dst src arg
  | Restrict_fail_PC_overflow_sr (t : bool) p g b e a π n p' g':
      regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs arg = Some n →
      (p',g') = (decodeSealPermPair n) ->
      SealPermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      incrementPC lpc = None →
      Restrict_failure lpc regs dst src arg.

  Inductive Restrict_spec (lpc : LWord) (regs : LReg) (dst src : RegName) (arg : Z + RegName) (lpc' : LWord) (regs' : LReg): griotte_lang.val -> Prop :=
  | Restrict_spec_success_cap (t : bool) p g b e a π n p' g':
      regs !!ₗ src = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs arg = Some n →
      (p',g') = (decodePermPair n) ->
      PermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WCap t p' g' b e a @@? π ]ₗ> regs →
      Restrict_spec lpc regs dst src arg lpc' regs' NextIV
  | Restrict_spec_success_sr (t : bool) p g b e a π n p' g':
      regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs arg = Some n →
      (p',g') = (decodeSealPermPair n) ->
      SealPermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WSealRange t p' g' b e a @@? π ]ₗ> regs →
      Restrict_spec lpc regs dst src arg lpc' regs' NextIV
  | Restrict_spec_invalidated_cap (t : bool) p g b e a π n p' g':
      regs !!ₗ src = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs arg = Some n →
      (p',g') = (decodePermPair n) ->
      (PermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := Cap⁻ p' g' b e a @@? π ]ₗ> regs →
      Restrict_spec lpc regs dst src arg lpc' regs' NextIV
  | Restrict_spec_invalidated_sr (t : bool) p g b e a π n p' g':
      regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs arg = Some n →
      (p',g') = (decodeSealPermPair n) ->
      (SealPermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := SealRange⁻ p' g' b e a @@? π ]ₗ> regs →
      Restrict_spec lpc regs dst src arg lpc' regs' NextIV
  (* An integer is unchanged; a sealed word or a sentry loses its tag. *)
  | Restrict_spec_untagged w:
      regs !!ₗ src = Some w →
      is_mutable_range w.(lw) = false →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := lclear_tag w ]ₗ> regs →
      Restrict_spec lpc regs dst src arg lpc' regs' NextIV
  | Restrict_spec_failure:
      Restrict_failure lpc regs dst src arg →
      lpc' = lpc →
      regs' = regs →
      Restrict_spec lpc regs dst src arg lpc' regs' FaultedV.

  Lemma wp_Restrict Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src arg regs dq :
    decodeInstrW w.(lw) = Restrict dst src arg ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Restrict dst src arg) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Restrict_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src arg lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of, operands_of in Hri, Dregs.
    destruct (Hri src) as [wsrc [H'src _] ]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'src) as (s & Hsrc & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs H'src) as Hok.
    rewrite /exec /= Hsrc /= in Hstep.
    destruct (lz_of_argument_dom regs arg) as [n Hn].
    { eapply arg_owned_of_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
    rewrite (lz_of_argument_incl R regs r _ n) /= in Hstep; [|done|done].
    destruct (decide (is_mutable_range wsrc.(lw) = false)) as [Hk | Hk].
    { iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (lclear_tag wsrc) (clear_tag wsrc.(lw)) _ _ _
        (λ lpc' regs' retv, Restrict_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src arg lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
      { apply reg_word_ok_lclear_tag. }
      { rewrite -Hstep. by destruct wsrc as [[| [] | | ? [] ] ?], s. }
      { apply reg_phys_lclear_tag in Hrel. by rewrite clear_tag_and_tag in Hrel. }
      { intros lpc' Hi. eapply Restrict_spec_untagged; eauto. }
      { intros Hi. apply Restrict_spec_failure; [|done..]. eapply Restrict_fail_PC_overflow_other; eauto. }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame. }
    destruct wsrc as [[ | [t p g b e a | t p g b e a] | | ] π]; cbn in Hstep.
    1,4,5: by exfalso; apply Hk.
    - destruct (decodePermPair n) as [p' g'] eqn:HdecPair.
      set (nt := t && PermFlowsTo p' p && LocalityFlowsTo g' g).
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (WCap nt p' g' b e a @@? π) _ _ _ _
        (λ lpc' regs' retv, Restrict_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src arg lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
      { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); last done; first by left.
        - rewrite /nt /=. by intros [[? ?]%andb_prop ?]%andb_prop.
        - rewrite /nt /=. intros [[? Hfl]%andb_prop ?]%andb_prop Hx.
          eapply (executeAllowed_flowsto p' p); [by rewrite Hfl | exact Hx]. }
      { exact Hstep. }
      { eapply (reg_phys_derive_eq _ (WCap t p g b e a @@? π) s); [done|done| |by destruct s].
        rewrite /nt /=. by intros [[? ?]%andb_prop ?]%andb_prop. }
      { intros lpc' Hi. rewrite /nt in Hi |- *.
        destruct (PermFlowsTo p' p) eqn:Hp, (LocalityFlowsTo g' g) eqn:Hl;
          rewrite ?andb_true_r ?andb_false_r /= in Hi |- *;
          [eapply Restrict_spec_success_cap; eauto | (eapply Restrict_spec_invalidated_cap; eauto; by rewrite Hp Hl)..]. }
      { intros Hi. apply Restrict_spec_failure; [|done..]. rewrite /nt in Hi |- *.
        destruct (PermFlowsTo p' p) eqn:Hp, (LocalityFlowsTo g' g) eqn:Hl;
          rewrite ?andb_true_r ?andb_false_r /= in Hi |- *;
          [eapply Restrict_fail_PC_overflow_cap; eauto | (eapply Restrict_fail_invalidated_PC_cap; eauto; by rewrite Hp Hl)..]. }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
    - destruct (decodeSealPermPair n) as [p' g'] eqn:HdecPair.
      set (nt := t && SealPermFlowsTo p' p && LocalityFlowsTo g' g).
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (WSealRange nt p' g' b e a @@? π) _ _ _ _
        (λ lpc' regs' retv, Restrict_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src arg lpc' regs' retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
      { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); last done; first by right.
        - rewrite /nt /=. by intros [[? ?]%andb_prop ?]%andb_prop.
        - done. }
      { exact Hstep. }
      { eapply (reg_phys_derive_eq _ (WSealRange t p g b e a @@? π) s); [done|done| |by destruct s].
        rewrite /nt /=. by intros [[? ?]%andb_prop ?]%andb_prop. }
      { intros lpc' Hi. rewrite /nt in Hi |- *.
        destruct (SealPermFlowsTo p' p) eqn:Hp, (LocalityFlowsTo g' g) eqn:Hl;
          rewrite ?andb_true_r ?andb_false_r /= in Hi |- *;
          [eapply Restrict_spec_success_sr; eauto | (eapply Restrict_spec_invalidated_sr; eauto; by rewrite Hp Hl)..]. }
      { intros Hi. apply Restrict_spec_failure; [|done..]. rewrite /nt in Hi |- *.
        destruct (SealPermFlowsTo p' p) eqn:Hp, (LocalityFlowsTo g' g) eqn:Hl;
          rewrite ?andb_true_r ?andb_false_r /= in Hi |- *;
          [eapply Restrict_fail_PC_overflow_sr; eauto | (eapply Restrict_fail_invalidated_PC_sr; eauto; by rewrite Hp Hl)..]. }
      iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

   Lemma wp_restrict_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a wz z p' g' π dq :
     decodeInstrW w.(lw) = Restrict r1 r1 (inr rv) →
     IsLInt wz z →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ{dq} w
         ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π
         ∗ ▷ rv ↦ᵣ wz }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ{dq} w
           ∗ rv ↦ᵣ wz
           ∗ r1 ↦ᵣ WCap t p' g' b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hwz Hvpc Hpca' HdecPair HPflows HLflows Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     destruct (IsLInt_inv _ _ Hwz) as [πz ->].
     iDestruct (map_of_regs_2 with "Hr1 Hrv") as "[Hmap %]".
     iApply (wp_Restrict with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by unfold regs_of, operands_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | | | ? ? ? ? ? | * Hfail].
    5: (simplify_lmap_eq; done).
     3,4: (simplify_lmap_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
    { (* Success *)
      iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
      simplify_pair_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
      simplify_lmap_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_lmap_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       all: try incrementPC_inv; simplify_lmap_eq; eauto; try congruence. }
   Qed.

   Lemma wp_restrict_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z p' g' π dq :
     decodeInstrW w.(lw) = Restrict r1 r1 (inl z) →
     isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ{dq} w
         ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
         ∗ pc_a ↦ₐ{dq} w
         ∗ r1 ↦ᵣ WCap t p' g' b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
     iApply (wp_Restrict with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     all: try (by unfold regs_of, operands_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
     iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

     destruct Hspec as [| | | | ? ? ? ? ? | * Hfail].
    5: (simplify_lmap_eq; done).
     3,4: (simplify_lmap_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success *)
       iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
       simplify_pair_eq.
       iRegsMap "Hmap"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
      simplify_lmap_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_lmap_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       all: try incrementPC_inv; simplify_lmap_eq; eauto; congruence. }
   Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {CL : CritLink Σ}.

  #[local] Lemma restrict_invalidated_map_cap E pc_p pc_g pc_b pc_e pc_a pc_π pc_a'
      w dst src arg regs (t : bool) p g b e a π n p' g' dq :
    decodeInstrW w.(lw) = Restrict dst src arg →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Restrict dst src arg) ⊆ dom regs →
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs arg = Some n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[ dst := Cap⁻ p' g' b e a @@? π ]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hsrc Harg Hdecode Hflows Hpca' φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Restrict with "[$HPC $Hpc_a $Hmap]"); eauto.
    iNext. iIntros (lpc' regs'' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | ? ? ? ? ? | Hfail]; simplify_eq; simplify_pair_eq.
    all: try (repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence).
    - try incrementPC_inv; simplify_eq. iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; simplify_pair_eq; try congruence.
      all: try incrementPC_inv; simplify_eq; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
  Qed.

  (* Exact register-map continuation, including aliases and special registers. *)
  #[local] Lemma restrict_invalidated_map_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a'
      w dst src arg regs (t : bool) p g b e a π n p' g' dq :
    decodeInstrW w.(lw) = Restrict dst src arg →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Restrict dst src arg) ⊆ dom regs →
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs arg = Some n →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[ dst := SealRange⁻ p' g' b e a @@? π ]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hsrc Harg Hdecode Hflows Hpca' φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Restrict with "[$HPC $Hpc_a $Hmap]"); eauto.
    iNext. iIntros (lpc' regs'' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | ? ? ? ? ? | Hfail]; simplify_eq; simplify_pair_eq.
    all: try (repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence).
    - try incrementPC_inv; simplify_eq. iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; simplify_pair_eq; try congruence.
      all: try incrementPC_inv; simplify_eq; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
  Qed.

  (* Restrict: immediate and register operands, including effective cnull reads. *)
  Lemma wp_restrict_invalidated_z E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n p' g' π dq :
    decodeInstrW w.(lw) = Restrict dst dst (inl n) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ Cap⁻ p' g' b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (restrict_invalidated_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a π n p' g'
        with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /operands_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg decide_False //.
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_restrict_invalidated_reg E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n p'
      g' src (ws : LWord) π dq :
    decodeInstrW w.(lw) = Restrict dst dst (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (src = cnull) then lnull else ws).(lw) = WInt n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ Cap⁻ p' g' b e a @@? π
        ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (restrict_invalidated_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a π n p' g'
        with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /operands_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg decide_False //.
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_restrict_invalidated_z_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n p' g' π dq :
    decodeInstrW w.(lw) = Restrict dst dst (inl n) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ SealRange⁻ p' g' b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (restrict_invalidated_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a π n p' g'
        with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /operands_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg decide_False //.
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_restrict_invalidated_reg_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n
      p' g' src (ws : LWord) π dq :
    decodeInstrW w.(lw) = Restrict dst dst (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (src = cnull) then lnull else ws).(lw) = WInt n →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ SealRange⁻ p' g' b e a @@? π
        ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (restrict_invalidated_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a π n p' g'
        with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /operands_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg decide_False //.
    iRegsMap "Hmap"; iFrame.
  Qed.

End instruction_outcomes.
