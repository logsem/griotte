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
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  Inductive Restrict_failure (regs : LReg) (dst: RegName) (src: Z + RegName) :=
  | Restrict_fail_src_nonz:
      lz_of_argument regs src = None →
      Restrict_failure regs dst src
  | Restrict_fail_allowed w:
      regs !!ₗ dst = Some w →
      is_mutable_range w.(lw) = false →
      Restrict_failure regs dst src
  | Restrict_fail_invalidated_PC_cap (t : bool) p g b e a π n p' g':
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src = Some n →
      (p',g') = (decodePermPair n) ->
      (PermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      incrementPC (<[ dst := WCap false p' g' b e a @@? π ]ₗ> regs) = None →
      Restrict_failure regs dst src
  | Restrict_fail_PC_overflow_cap (t : bool) p g b e a π n p' g':
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src = Some n →
      (p',g') = (decodePermPair n) ->
      PermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      incrementPC (<[ dst := WCap t p' g' b e a @@? π ]ₗ> regs) = None →
      Restrict_failure regs dst src
  | Restrict_fail_invalidated_PC_sr (t : bool) p g b e a π n p' g':
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src = Some n →
      (p',g') = (decodeSealPermPair n) ->
      (SealPermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      incrementPC (<[ dst := WSealRange false p' g' b e a @@? π ]ₗ> regs) = None →
      Restrict_failure regs dst src
  | Restrict_fail_PC_overflow_sr (t : bool) p g b e a π n p' g':
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src = Some n →
      (p',g') = (decodeSealPermPair n) ->
      SealPermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      incrementPC (<[ dst := WSealRange t p' g' b e a @@? π ]ₗ> regs) = None →
      Restrict_failure regs dst src.

  Inductive Restrict_spec (regs : LReg) (dst: RegName) (src: Z + RegName) (regs' : LReg): griotte_lang.val -> Prop :=
  | Restrict_spec_success_cap (t : bool) p g b e a π n p' g':
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src = Some n →
      (p',g') = (decodePermPair n) ->
      PermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      incrementPC (<[ dst := WCap t p' g' b e a @@? π ]ₗ> regs) = Some regs' →
      Restrict_spec regs dst src regs' NextIV
  | Restrict_spec_success_sr (t : bool) p g b e a π n p' g':
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src = Some n →
      (p',g') = (decodeSealPermPair n) ->
      SealPermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      incrementPC (<[ dst := WSealRange t p' g' b e a @@? π ]ₗ> regs) = Some regs' →
      Restrict_spec regs dst src regs' NextIV
  | Restrict_spec_invalidated_cap (t : bool) p g b e a π n p' g':
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src = Some n →
      (p',g') = (decodePermPair n) ->
      (PermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      incrementPC (<[ dst := WCap false p' g' b e a @@? π ]ₗ> regs) = Some regs' →
      Restrict_spec regs dst src regs' NextIV
  | Restrict_spec_invalidated_sr (t : bool) p g b e a π n p' g':
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src = Some n →
      (p',g') = (decodeSealPermPair n) ->
      (SealPermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      incrementPC (<[ dst := WSealRange false p' g' b e a @@? π ]ₗ> regs) = Some regs' →
      Restrict_spec regs dst src regs' NextIV
  | Restrict_spec_failure:
      Restrict_failure regs dst src →
      Restrict_spec regs dst src regs' FailedV.

  Lemma wp_Restrict Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs :
    decodeInstrW w.(lw) = Restrict dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Restrict dst src) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Restrict_spec regs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [H'dst _]]; first by set_solver+.
    pose proof (llookup_reg_incl _ _ _ _ Hregs H'dst) as Hdst.
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ Her Hlregs H'dst) as Hok.
    rewrite /exec /= Hdst /= in Hstep.
    destruct (lz_of_argument regs src) as [n|] eqn:Hn.
    2: { rewrite (lz_of_argument_None regs r) /= in Hstep; [|done| |done].
         2: { intros x ->. apply Dregs. set_solver+. }
         simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
         iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
         constructor. by constructor. }
    rewrite (lz_of_argument_incl regs r _ n) /= in Hstep; [|done|done].
    destruct wdst as [[ | [t p g b e a | t p g b e a] | | ] π]; cbn in Hstep.
    1,4,5: (simplify_eq; iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done;
            iIntros "Hmap"; iApply "Hφ"; iFrame; iPureIntro;
            constructor; eapply Restrict_fail_allowed; eauto).
    - destruct (decodePermPair n) as [p' g'] eqn:HdecPair.
      set (nt := t && PermFlowsTo p' p && LocalityFlowsTo g' g).
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst (WCap nt p' g' b e a @@? π) _ _ _
        (λ regs' retv, Restrict_spec regs dst src regs' retv)
        with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
      { eapply (reg_word_ok_derive _ _ (WCap t p g b e a @@? π)); last done; first by left.
        rewrite /nt /=. by intros [[? ?]%andb_prop ?]%andb_prop. }
      { exact Hstep. }
      { intros regs' Hi. rewrite /nt in Hi.
        destruct (PermFlowsTo p' p) eqn:Hp, (LocalityFlowsTo g' g) eqn:Hl;
          rewrite ?andb_true_r ?andb_false_r /= in Hi;
          [eapply Restrict_spec_success_cap; eauto | (eapply Restrict_spec_invalidated_cap; eauto; by rewrite Hp Hl)..]. }
      { intros Hi. constructor. rewrite /nt in Hi.
        destruct (PermFlowsTo p' p) eqn:Hp, (LocalityFlowsTo g' g) eqn:Hl;
          rewrite ?andb_true_r ?andb_false_r /= in Hi;
          [eapply Restrict_fail_PC_overflow_cap; eauto | (eapply Restrict_fail_invalidated_PC_cap; eauto; by rewrite Hp Hl)..]. }
      iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
    - destruct (decodeSealPermPair n) as [p' g'] eqn:HdecPair.
      set (nt := t && SealPermFlowsTo p' p && LocalityFlowsTo g' g).
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst (WSealRange nt p' g' b e a @@? π) _ _ _
        (λ regs' retv, Restrict_spec regs dst src regs' retv)
        with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a]").
      { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
      { eapply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π)); last done; first by right.
        rewrite /nt /=. by intros [[? ?]%andb_prop ?]%andb_prop. }
      { exact Hstep. }
      { intros regs' Hi. rewrite /nt in Hi.
        destruct (SealPermFlowsTo p' p) eqn:Hp, (LocalityFlowsTo g' g) eqn:Hl;
          rewrite ?andb_true_r ?andb_false_r /= in Hi;
          [eapply Restrict_spec_success_sr; eauto | (eapply Restrict_spec_invalidated_sr; eauto; by rewrite Hp Hl)..]. }
      { intros Hi. constructor. rewrite /nt in Hi.
        destruct (SealPermFlowsTo p' p) eqn:Hp, (LocalityFlowsTo g' g) eqn:Hl;
          rewrite ?andb_true_r ?andb_false_r /= in Hi;
          [eapply Restrict_fail_PC_overflow_sr; eauto | (eapply Restrict_fail_invalidated_PC_sr; eauto; by rewrite Hp Hl)..]. }
      iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_restrict_success_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rv z p' g':
    decodeInstrW w.(lw) = Restrict PC (inr rv) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (p',g') = (decodePermPair z) ->
    PermFlowsTo p' pc_p = true →
    LocalityFlowsTo g' pc_g = true →
    rv ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap true p' g' pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ w
           ∗ rv ↦ᵣ WInt z }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull ϕ) "(>HPC & >Hpc_a & >Hrv) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

     destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_lmap_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       simplify_pair_eq; rewrite !insert_insert_eq.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.
     }
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_lmap_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a z p' g' π :
     decodeInstrW w.(lw) = Restrict r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π
         ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ w
           ∗ rv ↦ᵣ WInt z
           ∗ r1 ↦ᵣ WCap t p' g' b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_lmap_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
              (insert_insert_ne _ PC r1) // insert_insert_eq.
      simplify_pair_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
      simplify_lmap_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_lmap_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w z p' g' :
     decodeInstrW w.(lw) = Restrict PC (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' pc_p = true →
     LocalityFlowsTo g' pc_g = true →

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true p' g' pc_b pc_e pc_a' @@? pc_π
         ∗ pc_a ↦ₐ w }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' HdecPair HPflows HLflows ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [ | | | | * Hfail ].
     3,4: (simplify_lmap_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       simplify_pair_eq.
       rewrite !insert_insert_eq.
       iApply (regs_of_map_1 with "Hmap"). }
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_lmap_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z p' g' π :
     decodeInstrW w.(lw) = Restrict r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WCap t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
         ∗ pc_a ↦ₐ w
         ∗ r1 ↦ᵣ WCap t p' g' b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

     destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_lmap_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
               (insert_insert_ne _ PC r1) // insert_insert_eq. simplify_pair_eq.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
      simplify_lmap_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_lmap_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       incrementPC_inv; simplify_lmap_eq; eauto; congruence. }
   Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

 Lemma wp_restrict_success_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 rv (t : bool) p g b e a z p' g' π :
     decodeInstrW w.(lw) = Restrict r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodeSealPermPair z) ->
     SealPermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π
         ∗ ▷ rv ↦ᵣ WInt z }}}
       Instr Executable @ Ep
       {{{ RET NextIV;
           PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
           ∗ pc_a ↦ₐ w
           ∗ rv ↦ᵣ WInt z
           ∗ r1 ↦ᵣ WSealRange t p' g' b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hrv) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_lmap_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
    { (* Success with WCap (contradiction) *)
      simplify_lmap_eq.
    }
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
               (insert_insert_ne _ PC r1) // insert_insert_eq. simplify_pair_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_lmap_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
   Qed.

   Lemma wp_restrict_success_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r1 (t : bool) p g b e a z p' g' π :
     decodeInstrW w.(lw) = Restrict r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodeSealPermPair z) ->
     SealPermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     r1 ≠ cnull ->

     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a @@? π }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
         ∗ pc_a ↦ₐ w
         ∗ r1 ↦ᵣ WSealRange t p' g' b e a @@? π }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iApply (wp_Restrict with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

     destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_lmap_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success with WSealRange (contradiction) *)
       simplify_lmap_eq.
     }
     { (* Success *)
       iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
         (insert_insert_ne _ PC r1) // insert_insert_eq.
       simplify_pair_eq.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_lmap_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
   Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  Local Lemma restrict_invalidated_map_cap E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src regs regs' (t : bool) p g b e a π n p' g' :
    decodeInstrW w.(lw) = Restrict dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Restrict dst src) ⊆ dom regs →
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs src = Some n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    incrementPC (<[ dst := WCap false p' g' b e a @@? π ]ₗ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc Hdecode Hflows Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq; simplify_pair_eq.
    - repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
    - simplify_eq. iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; simplify_pair_eq; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
  Qed.

  (* Exact register-map continuation, including aliases and special registers. *)
  Local Lemma restrict_invalidated_map_sr E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src regs regs' (t : bool) p g b e a π n p' g' :
    decodeInstrW w.(lw) = Restrict dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Restrict dst src) ⊆ dom regs →
    regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs src = Some n →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    incrementPC (<[ dst := WSealRange false p' g' b e a @@? π ]ₗ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc Hdecode Hflows Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Restrict with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq; simplify_pair_eq.
    - repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
    - simplify_eq. iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; simplify_pair_eq; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
  Qed.

  (* Restrict: immediate and register operands, including effective cnull reads. *)
  Lemma wp_restrict_invalidated_z E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n p' g' π :
    decodeInstrW w.(lw) = Restrict dst (inl n) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p' g' b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (restrict_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a' @@? pc_π]> (<[dst := WCap false p' g' b e a @@? π]> (∅ : LReg))) t p g b e a π n p' g' with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg. simplify_map_eq;
      try (f_equal; apply map_eq; intros i; rewrite !lookup_insert;
           repeat case_decide; simplify_eq; done).
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_restrict_invalidated_reg E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n p'
      g' src (ws : LWord) π :
    decodeInstrW w.(lw) = Restrict dst (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (src = cnull) then lnull else ws).(lw) = WInt n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p' g' b e a @@? π
        ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (restrict_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a' @@? pc_π]> (<[dst := WCap false p' g' b e a @@? π]> (<[src := ws]> (∅ : LReg)))) t p g b e a π n p' g'
        with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg. simplify_map_eq;
      try (f_equal; apply map_eq; intros i; rewrite !lookup_insert;
           repeat case_decide; simplify_eq; done).
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_restrict_invalidated_z_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n p' g' π :
    decodeInstrW w.(lw) = Restrict dst (inl n) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p' g' b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (restrict_invalidated_map_sr E _ _ _ _ _ _ w _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a' @@? pc_π]> (<[dst := WSealRange false p' g' b e a @@? π]> (∅ : LReg))) t p g b e a π n p' g' with
        "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg. simplify_map_eq;
      try (f_equal; apply map_eq; intros i; rewrite !lookup_insert;
           repeat case_decide; simplify_eq; done).
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_restrict_invalidated_reg_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n
      p' g' src (ws : LWord) π :
    decodeInstrW w.(lw) = Restrict dst (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (src = cnull) then lnull else ws).(lw) = WInt n →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p' g' b e a @@? π
        ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (restrict_invalidated_map_sr E _ _ _ _ _ _ w _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a' @@? pc_π]> (<[dst := WSealRange false p' g' b e a @@? π]> (<[src := ws]> (∅ : LReg)))) t p g b e a π n
        p' g' with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg. simplify_map_eq;
      try (f_equal; apply map_eq; intros i; rewrite !lookup_insert;
           repeat case_decide; simplify_eq; done).
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_restrict_invalidated_z_PC E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n p' g' :
    decodeInstrW w.(lw) = Restrict PC (inl n) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (p', g') = decodePermPair n →
    PermFlowsTo p' pc_p && LocalityFlowsTo g' pc_g = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false p' g' pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hdecode Hreject φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (restrict_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ (<[PC := WCap false p' g' pc_b pc_e
        pc_a' @@? pc_π]> (∅ : LReg)) true pc_p pc_g pc_b pc_e pc_a pc_π n p' g' with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg. simplify_map_eq;
      try (f_equal; apply map_eq; intros i; rewrite !lookup_insert;
           repeat case_decide; simplify_eq; done).
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_1 with "Hmap").
  Qed.

  Lemma wp_restrict_invalidated_reg_PC E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n p' g' src (ws : LWord) :
    decodeInstrW w.(lw) = Restrict PC (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (src = cnull) then lnull else ws).(lw) = WInt n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' pc_p && LocalityFlowsTo g' pc_g = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ src ↦ᵣ ws }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false p' g' pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ src ↦ᵣ ws }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread Hdecode Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (restrict_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ (<[PC := WCap false p' g' pc_b pc_e
        pc_a' @@? pc_π]> (<[src := ws]> (∅ : LReg))) true pc_p pc_g pc_b pc_e pc_a pc_π n p' g' with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [rewrite /lz_of_argument /llookup_reg; simplify_map_eq;
                 case_decide; [by inversion Hread|];
                 destruct ws as [[] ?]; by simplify_eq/=].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg. simplify_map_eq;
      try (f_equal; apply map_eq; intros i; rewrite !lookup_insert;
           repeat case_decide; simplify_eq; done).
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.
End instruction_outcomes.
