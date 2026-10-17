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

  (* The addressing capability's identifier does not matter: only its
     physical word is read. *)
  Definition reg_allows_load_imm (regs : LReg) (r : RegName) (imm : Z) p g b e a ea :=
    lw <$> regs !!ₗ r = Some (WCap true p g b e a) ∧
    (a + imm)%a = Some ea ∧ readAllowed p = true ∧ withinBounds b e ea = true.

  Definition reg_allows_load (regs : LReg) (r : RegName) p g b e a  :=
    lw <$> regs !!ₗ r = Some (WCap true p g b e a) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  (** ** Status witnesses

      The loaded word's identifier decides the post. Every load gets the
      plain post: the loaded word, or its untagged copy if it is a heap
      capability. Without a witness the loaded word is exact (variant 1);
      exact posts also follow for non-heap words and for identifier-less
      words with authority (variant 4), and, given a witness, untagged posts
      for quarantined identifiers (variant 2) and exact posts for live ones
      (variant 3). Witnesses are preconditions, returned unchanged. *)
  Inductive load_witness := LoadPlain | LoadQuar (ι : AId) | LoadLive (ι : AId) (q : Qp).

  Definition load_witness_res (wit : load_witness) : iProp Σ :=
    match wit with
    | LoadPlain => emp
    | LoadQuar ι => ι ⊒ AQuar
    | LoadLive ι q => ι ↦st{q} ALive
    end%I.

  #[global] Instance load_witness_res_timeless wit : Timeless (load_witness_res wit).
  Proof. destruct wit; apply _. Qed.

  Definition load_post (wit : load_witness) (p : Perm) (v v' : LWord) : Prop :=
    lload_heap (lload_word p v) v' ∧
    (heap_cap_base v.(lw) = None → v' = lload_word p v) ∧
    (v.(lprov) = None → load_exact_cond v → v' = lload_word p v) ∧
    match wit with
    | LoadPlain => v' = lload_word p v
    | LoadQuar ι => v.(lprov) = Some ι → (get_tag v.(lw) = true → has_authority v.(lw)) →
                    v' = lclear_tag (lload_word p v)
    | LoadLive ι q => v.(lprov) = Some ι → load_exact_cond v → v' = lload_word p v
    end.

  Definition load_witness_ok (R : RegState) (wit : load_witness) : Prop :=
    match wit with
    | LoadPlain => True
    | LoadQuar ι => ∃ x, R !! ι = Some x ∧ lifecycle_enc AQuar ≤ lifecycle_enc (re_status x)
    | LoadLive ι q => ∃ x, R !! ι = Some x ∧ re_status x = ALive
    end.

  Lemma load_witness_lookup R wit :
    reg_auth R -∗ load_witness_res wit -∗ ⌜load_witness_ok R wit⌝.
  Proof.
    iIntros "HR Hw". destruct wit as [|ι|ι q]; cbn; first done.
    - iDestruct (reg_lookup_lb with "HR Hw") as %(b & e & γ & s & HRι & Hle).
      iPureIntro. eexists. split; first done. done.
    - iDestruct (reg_lookup_own with "HR Hw") as %(b & e & γ & HRι).
      iPureIntro. eexists. split; first done. done.
  Qed.

  (** The logical loaded word: a copy of the physical CLoad result by the
      register clause, which satisfies the post. *)
  Lemma load_post_choose R C st wit (v : LWord) pw p pl :
    registry_ok R C st →
    load_witness_ok R wit →
    mem_word_ok R C v pw →
    load_filter st p pw = Some pl →
    ∃ v' : LWord, load_post wit p v v' ∧ reg_word_ok R C v' ∧ reg_phys R v' pl.
  Proof.
    intros Hreg Hwit Hok Hpl.
    pose proof (mem_word_ok_reg_word_ok _ _ _ _ Hok) as Hokv.
    (* The exact loaded word. *)
    assert (load_post LoadPlain p v (lload_word p v) ∧ reg_word_ok R C (lload_word p v) ∧
            reg_phys R (lload_word p v) pl) as (Hpost & Hok' & Hphys).
    { split_and!; [|by apply reg_word_ok_lload_word|by eapply load_filter_reg_phys].
      split_and!; [by left|done|done|done]. }
    destruct wit as [|ι|ι q].
    - by exists (lload_word p v).
    - destruct (decide (v.(lprov) = Some ι ∧ (get_tag v.(lw) = true → has_authority v.(lw))))
        as [[Hι Hside] | Hn].
      + destruct Hwit as (x & Hx & Hle).
        pose proof (load_filter_quarantined _ _ _ _ _ _ _ _ _ Hreg Hok Hpl Hι Hx Hle Hside) as Hpl'.
        exists (lclear_tag (lload_word p v)). split_and!.
        * destruct (get_tag v.(lw)) eqn:Ht.
          -- destruct (Hside eq_refl) as [_ [b Hab]].
             split_and!; [right; split; last done | | |].
             ++ rewrite /= is_heap_cap_load_word /is_heap_cap.
                by rewrite (heap_authority_base_heap_cap_base _ _ Hab).
             ++ intros Hn. apply heap_authority_base_heap_cap_base in Hab. congruence.
             ++ intros Hn. congruence.
             ++ done.
          -- rewrite lclear_tag_untagged; last by rewrite /= get_tag_load_word.
             split_and!; [by left|done|done|].
             intros _ _. by rewrite lclear_tag_untagged // /= get_tag_load_word.
        * by apply reg_word_ok_lclear_tag.
        * rewrite Hpl'. apply reg_phys_untagged. by rewrite /= get_tag_clear_tag.
      + exists (lload_word p v). split_and!; try done.
        destruct Hpost as (? & ? & ? & _). split_and!; try done.
        intros Hι Hside. by exfalso; apply Hn.
    - exists (lload_word p v). split_and!; try done.
      destruct Hpost as (? & ? & ? & _). by split_and!.
  Qed.

  Inductive Load_failure_spec (lpc : LWord) (regs: LReg) (r1 r2: RegName) (imm : Z)
    (mem : LMem) (shadow : ShadowTbl) (wit : load_witness) (dw : deref_witness) :=
  | Load_fail_const w:
      regs !!ₗ r2 = Some w ->
      is_cap w.(lw) = false →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_tag p g b e a:
      lw <$> regs !!ₗ r2 = Some (WCap false p g b e a) →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_addr_imm p g b e a:
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = None →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_bounds_imm p g b e a ea:
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      (readAllowed p = false ∨ withinBounds b e ea = false) →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_invalid_PC_imm p g b e a ea loadv loadv':
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      is_shadow_address ea = false →
      mem !! ea = Some loadv →
      load_post wit p loadv loadv' →
      incrementPC lpc = None ->
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_invalid_PC_shadow_imm p g b e a ea heap_a revoked:
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = Some ea →
      is_shadow_address ea = true →
      shadow_to_heap ea = Some heap_a →
      shadow !! heap_a = Some revoked →
      incrementPC lpc = None →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_invalid_PC_revoker_imm p g b e a ea:
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = Some ea →
      is_revoker_address ea = true →
      mem !! ea = None →
      incrementPC lpc = None →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  (* A source with an identifier not covered by the witness may have been
     revoked: its physical copy is untagged. *)
  | Load_fail_revoked p g b e a π:
      regs !!ₗ r2 = Some (WCap true p g b e a @@? π) →
      π ≠ deref_id dw →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  .

  Definition reg_allows_load_offset (regs : LReg) (r : RegName)
      (imm : Z) p g b e (ea : Addr) : Prop :=
    match imm with
    | 0%Z => reg_allows_load regs r p g b e ea
    | _ => ∃ a, reg_allows_load_imm regs r imm p g b e a ea
    end.

  Lemma reg_allows_load_offset_imm regs r imm p g b e ea :
    reg_allows_load_offset regs r imm p g b e ea →
    ∃ a, reg_allows_load_imm regs r imm p g b e a ea.
  Proof.
    destruct imm as [|imm|imm]; simpl.
    - intros (Hreg & Hra & Hwb). exists ea. repeat split; auto.
      by rewrite finz_add_0.
    - exact (λ H, H).
    - exact (λ H, H).
  Qed.

  Lemma reg_allows_load_imm_offset regs r imm p g b e a ea :
    reg_allows_load_imm regs r imm p g b e a ea →
    reg_allows_load_offset regs r imm p g b e ea.
  Proof.
    destruct imm as [|imm|imm]; simpl; intros Hallow;
      try (by exists a).
    destruct Hallow as (Hreg & Hadd & Hra & Hwb).
    rewrite finz_add_0 in Hadd. inversion Hadd; subst ea.
    repeat split; auto.
  Qed.

  Inductive Load_spec
    (lpc : LWord) (regs: LReg) (r1 r2: RegName) (imm : Z)
    (lpc' : LWord) (regs': LReg) (mem : LMem) (shadow : ShadowTbl) (wit : load_witness)
    (dw : deref_witness) : griotte_lang.val → Prop
  :=
  | Load_spec_success p g b e a loadv loadv' :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = false →
    mem !! a = Some loadv →
    load_post wit p loadv loadv' →
    incrementPC lpc = Some lpc' →
    regs' = <[ r1 := loadv' ]ₗ> regs →
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw NextIV

  | Load_spec_success_shadow p g b e a heap_a revoked :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some revoked →
    incrementPC lpc = Some lpc' →
    regs' = <[ r1 := lword_of_word (WInt (encodeAllocStatus revoked)) ]ₗ> regs →
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw NextIV

  (* The revoker reads as zero. *)
  | Load_spec_success_revoker p g b e a :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_revoker_address a = true →
    mem !! a = None →
    incrementPC lpc = Some lpc' →
    regs' = <[ r1 := lword_of_word (WInt 0) ]ₗ> regs →
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw NextIV

  | Load_spec_failure :
    Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw ->
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw FailedV.

  (* Own the source location, or its shadow entry; the revoker needs no
     resource. *)
  Definition allow_load_mem_or_shadow_offset (r : RegName) (imm : Z)
      (regs : LReg) (mem : LMem) (shadow : ShadowTbl) :=
    ∀ p g b e ea,
      reg_allows_load_offset regs r imm p g b e ea →
      if is_shadow_address ea then
        ∃ heap_a, shadow_to_heap ea = Some heap_a ∧ is_Some (shadow !! heap_a)
      else if is_revoker_address ea then True
      else ∃ loadv, mem !! ea = Some loadv.

  Definition allow_load_mem_or_shadow (r : RegName) (regs : LReg)
    (mem : LMem) (shadow : ShadowTbl) :=
    allow_load_mem_or_shadow_offset r 0 regs mem shadow.

  Lemma wp_load_general_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs shadow sdq wit dw :
   decodeInstrW w.(lw) = CLoad r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (CLoad r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_mem_or_shadow_offset r2 imm regs mem shadow →
   dom mem = dom dfracs →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
       load_witness_res wit ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' regs' retv, RET retv;
       ⌜ Load_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' regs' mem shadow wit dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
         load_witness_res wit ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad Hdomeq φ)
      "(>HPC & >Hmem & >Hshadow & Hwit & Hdw & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ /=".
    destruct σ1 as [ [ [ [pc r] sr] m] st]; cbn.
    iNamed "Hσ".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    pose proof (erasure_pc_correct _ _ _ _ _ _ Her Hvpc) as Hpc. cbn in Hpc. subst pc.
    iEval (rewrite /sreg /shadowtbl /=) in "Hsr Hst".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hlregs.
    pose proof (erasure_regs_incl _ _ _ _ _ _ _ Her Hlregs) as Hregs.
    iDestruct (load_witness_lookup with "HR Hwit") as %Hwit.
    iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
    pose proof (er_registry _ _ _ _ _ _ Her) as Hreg; cbn in Hreg.
    pose proof (er_mmio _ _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.
    iAssert (⌜∀ a loadv, mem !! a = Some loadv → lmem !! a = Some loadv⌝)%I as %Hmem_valid.
    { iIntros (a loadv Hlookup).
      assert (is_Some (dfracs !! a)) as [dq Hdq].
      { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom; eauto. }
      iApply (gen_mem_valid_inSepM_general (prod_merge dfracs mem) with "Hm Hmem").
      by rewrite lookup_merge Hlookup Hdq. }
    iAssert (⌜∀ a revoked, shadow !! a = Some revoked → st !! a = Some revoked⌝)%I as %Hshadow_valid.
    { iIntros (a revoked Hlookup).
      iDestruct (big_sepM_lookup with "Hshadow") as "Ha"; first exact Hlookup.
      iApply (gen_heap_valid with "Hst Ha"). }
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r2) as [r2v [Hr'2 _]]; first by set_solver+.
    odestruct (Hri r1) as [r1v [Hr'1 _]]; first by set_solver+.
    clear Hri.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr'2) as (s2 & Hr2 & Hrel2).
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hmem_pc))
      as (pw & Hpw & Hpwok).
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite (mem_word_ok_decode _ _ _ _ Hpwok) Hinstr in Hstep.
    rewrite /exec /= Hr2 /= in Hstep.

    destruct (is_cap r2v.(lw)) eqn:Hr2v.
    2: {
      assert ((Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) = (c, σ2)) as Hstep'.
      { unfold is_cap in Hr2v. destruct r2v as [r2v ?]; cbn in *.
        destruct_word r2v; by simplify_pair_eq. }
      instr_fail Hstep'. apply Load_spec_failure. by eapply Load_fail_const. }
    destruct r2v as [[ | [t p g b e a | ] | | ] π2]; try inversion Hr2v. clear Hr2v.
    destruct t.
    2: { cbn in Hstep. rewrite ?andb_false_r in Hstep.
         instr_fail Hstep. apply Load_spec_failure. eapply Load_fail_tag. by rewrite Hr'2. }
    destruct s2.
    2: { (* The physical copy of the source is untagged. *)
      cbn in Hstep. instr_fail Hstep. apply Load_spec_failure.
      destruct (decide (π2 = deref_id dw)) as [Hπ|Hπ]; last by eapply Load_fail_revoked.
      destruct (a + imm)%a as [ea|] eqn:Hadd.
      2: by eapply Load_fail_addr_imm; [rewrite Hr'2 | done].
      destruct (withinBounds b e ea) eqn:Hwb.
      2: by eapply Load_fail_bounds_imm; [rewrite Hr'2 | done | right].
      (* A stripped source under its witness is a heap capability without
         authority: its bounds are empty. *)
      exfalso.
      destruct Hrel2 as [[Heq | [_ [[Hst _] | [Hna [base Hh]]]]] _]; cbn in *; try discriminate.
      { by apply (deref_witness_not_stale R dw (WCap true p g b e a @@? π2)). }
      assert (is_heap_address b = true) as Hbh.
      { rewrite /heap_cap_base /= in Hh. by destruct (is_heap_address b). }
      apply withinBounds_true_iff in Hwb. apply Hna. split; first done. exists b.
      apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
      split; [solve_addr | done]. }
    cbn in Hstep.
    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { instr_fail Hstep. apply Load_spec_failure. eapply Load_fail_addr_imm; last done. by rewrite Hr'2. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2: {
      apply andb_false_iff in HRA.
      instr_fail Hstep. apply Load_spec_failure. eapply Load_fail_bounds_imm; eauto. by rewrite Hr'2.
    }
    apply andb_true_iff in HRA as [Hra Hwb].
    assert (Hallow : reg_allows_load_offset regs r2 imm p g b e ea).
    { apply reg_allows_load_imm_offset with (a := a). repeat split; auto. by rewrite Hr'2. }
    specialize (HaLoad p g b e ea Hallow).

    (* Classify the read: the loaded logical word, which the register gets,
       its physical copy, and the spec's success and failure cases. *)
    assert (∃ (v : LWord) (pv : Word),
      reg_word_ok R C v ∧
      reg_phys R v pv ∧
      (match updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) r1 pv) with
       | Some conf => conf | None => (Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) end) = (c, σ2) ∧
      (∀ lpc', incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
         Load_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' (<[r1 := v]ₗ> regs) mem shadow wit dw NextIV) ∧
      (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None →
         Load_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs mem shadow wit dw FailedV))
      as (v & pv & Hok & Hpv & Hstep' & Hsucc & Hfailure).
    {
      destruct (is_shadow_address ea) eqn:Hshadow.
      - destruct HaLoad as (heap_a & Htranslate & revoked & Hlookup).
        rewrite Htranslate /= (Hshadow_valid _ _ Hlookup) /= in Hstep.
        exists (lword_of_word (WInt (encodeAllocStatus revoked))), (WInt (encodeAllocStatus revoked)).
        split; first apply reg_word_ok_int. split; first apply reg_phys_lword_of_word.
        split; first exact Hstep.
        split.
        + intros. by eapply Load_spec_success_shadow.
        + intros. apply Load_spec_failure. by eapply Load_fail_invalid_PC_shadow_imm; eauto; rewrite Hr'2.
      - destruct (is_revoker_address ea) eqn:Hrevoker.
        + rewrite /= in Hstep.
          assert (mem !! ea = None) as Hnone.
          { destruct (mem !! ea) as [v|] eqn:Hv; last done.
            destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hv)) as (pv & Hpv & _).
            by rewrite (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hpv) in Hrevoker. }
          exists (lword_of_word (WInt 0)), (WInt 0).
          split; first apply reg_word_ok_int. split; first apply reg_phys_lword_of_word.
          split; first exact Hstep.
          split.
          * intros. by eapply Load_spec_success_revoker.
          * intros. apply Load_spec_failure. by eapply Load_fail_invalid_PC_revoker_imm; eauto; rewrite Hr'2.
        + destruct HaLoad as (loadv & Hlookup).
          destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hlookup))
            as (pv & Hpv & Hpvok).
          rewrite Hpv /= in Hstep.
          destruct (load_filter_is_Some R C st p pv Hreg) as [pl Hpl].
          assert ((match updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) r1 pl) with
                   | Some conf => conf | None => (Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) end) = (c, σ2))
            as Hstep'.
          { rewrite -Hstep /load_filter in Hpl |- *.
            destruct (heap_cap_base pv) as [base|]; last by simplify_eq.
            destruct (st !! base) as [[]|]; simplify_eq; done. }
          destruct (load_post_choose _ _ _ _ _ _ _ _ Hreg Hwit Hpvok Hpl) as (loadv' & Hpost & Hok' & Hphys).
          exists loadv', pl.
          split; first done. split; first done.
          split; first exact Hstep'.
          split.
          * intros. by eapply Load_spec_success.
          * intros. apply Load_spec_failure. eapply Load_fail_invalid_PC_imm; eauto. by rewrite Hr'2.
    }
    iApply bupd_fupd.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ r1 v pv _ _ _
      (λ lpc' regs' retv, Load_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' regs' mem shadow wit dw retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hmem Hshadow Hwit Hdw]").
    { exact Her. } { exact Hlregs. }
    { apply Dregs. set_solver+. }
    { exact Hok. } { exact Hstep'. } { exact Hpv. } { exact Hsucc. } { exact Hfailure. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_load_general Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs shadow sdq wit dw :
   decodeInstrW w.(lw) = CLoad r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (CLoad r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_mem_or_shadow r2 regs mem shadow →
   dom mem = dom dfracs →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
       load_witness_res wit ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' regs' retv, RET retv;
       ⌜ Load_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 0 lpc' regs' mem shadow wit dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
         load_witness_res wit ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Dregs Hmem_pc HaLoad Hdomeq.
    eapply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π
      r1 r2 0 w mem dfracs regs shadow sdq wit dw); eauto.
  Qed.

  Definition allow_load_map_or_true_imm r (imm : Z) (regs : LReg) (mem : LMem):=
    ∃ t p g b e a, read_reg_inr regs r t p g b e a ∧
      match (a + imm)%a with
      | None => True
      | Some ea => if decide (reg_allows_load_imm regs r imm p g b e a ea) then
        ∃ w, mem !! ea = Some w
      else True
      end.

  Lemma allow_load_implies_loadv_imm r2 imm mem regs p g b e a ea :
    allow_load_map_or_true_imm r2 imm regs mem →
    reg_allows_load_imm regs r2 imm p g b e a ea →
    ∃ loadv, mem !! ea = Some loadv.
  Proof.
    intros (t & p0 & g0 & b0 & e0 & a0 & Hsrc & Hmem) Hallow.
    pose proof Hallow as (Hreg & Hadd & Hra & Hwb).
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hreg) as (Hne & π & Hr2).
    rewrite /read_reg_inr Hr2 in Hsrc. simplify_eq.
    unfold reg_allows_load_imm in Hmem. rewrite Hadd in Hmem. case_decide as Hdec; first done.
    exfalso. by apply Hdec.
  Qed.

  Definition allow_load_map_or_true r (regs : LReg) (mem : LMem):=
    ∃ t p g b e a, read_reg_inr regs r t p g b e a ∧
      if decide (reg_allows_load regs r p g b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma allow_load_implies_loadv:
    ∀ (r2 : RegName) (mem0 : LMem) (r : LReg) (p : Perm)
      (g : Locality) (b e a : Addr),
      allow_load_map_or_true r2 r mem0
      → lw <$> r !!ₗ r2 = Some (WCap true p g b e a)
      → readAllowed p = true
      → withinBounds b e a = true
      → ∃ (loadv : LWord),
          mem0 !! a = Some loadv.
  Proof.
    intros r2 mem0 r p g b e a HaLoad Hr2v Hra Hwb.
    destruct HaLoad as (t&?&?&?&?&?& Hrinr & Hmem).
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hr2v) as (Hne & π & Hr2).
    rewrite /read_reg_inr Hr2 in Hrinr. simplify_eq.
    case_decide as Hrega; first exact Hmem.
    exfalso. apply Hrega. by repeat split.
  Qed.

  Lemma mem_implies_loadv:
    ∀ (pc_a : Addr) (w w' : LWord) (a0 : Addr)
      (mem0 : LMem) (loadv : LWord),
      (if (a0 =? pc_a)%a
       then mem0 = <[pc_a:=w]> ∅
       else mem0 = <[pc_a:=w]> (<[a0:=w']> ∅))→
      mem0 !! a0 = Some loadv →
      loadv = (if (a0 =? pc_a)%a then w else w').
  Proof.
    intros pc_a w w' a0 mem0 loadv H4 H6.
    destruct (a0 =? pc_a)%a eqn:Heq; rewrite H4 in H6.
    + apply Z.eqb_eq, finz_to_z_eq in Heq; subst a0. by rewrite lookup_insert_eq in H6; simplify_eq.
    + apply Z.eqb_neq in Heq. rewrite lookup_insert_ne in H6; last congruence.
      by rewrite lookup_insert_eq in H6; simplify_eq.
  Qed.

  Lemma mem_eq_implies_allow_load_map_imm:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (w : LWord) p g b e a ea (imm : Z),
      mem = <[ea:=w]> ∅
      → lw <$> regs !!ₗ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 w p g b e a ea imm Hmem Hrr2 Hadd.
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hrr2) as (Hne & π & Hr2).
    exists true,p,g,b,e,a; split.
    - by rewrite /read_reg_inr Hr2.
    - unfold reg_allows_load_imm. rewrite Hadd. case_decide; last done.
      exists w. subst mem. by rewrite lookup_insert_eq.
  Qed.

  Lemma mem_neq_implies_allow_load_map_imm:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (pc_a : Addr)
      (w w' : LWord) p g b e a ea (imm : Z),
      ea ≠ pc_a
      → mem = <[pc_a:=w]> (<[ea:=w']> ∅)
      → lw <$> regs !!ₗ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a ea imm Hne' Hmem Hrr2 Hadd.
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hrr2) as (Hne & π & Hr2).
    exists true,p,g,b,e,a; split.
    - by rewrite /read_reg_inr Hr2.
    - unfold reg_allows_load_imm. rewrite Hadd. case_decide; last done.
      exists w'. subst mem.
      rewrite lookup_insert_ne //. by rewrite lookup_insert_eq.
  Qed.

  Lemma mem_implies_allow_load_map_imm:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (pc_a : Addr)
      (w w' : LWord) p g b e a ea (imm : Z),
      (if (ea =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[ea:=w']> ∅))
      → lw <$> regs !!ₗ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a ea imm H4 Hrr2 Hadd.
    destruct (ea =? pc_a)%a eqn:Heq.
    + apply Z.eqb_eq, finz_to_z_eq in Heq. subst ea. eapply mem_eq_implies_allow_load_map_imm; eauto.
    + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_load_map_imm; eauto; try congruence.
  Qed.

  Lemma decode_load_not_heap_cap_imm (w : LWord) dst src imm :
    decodeInstrW w.(lw) = CLoad dst src imm → is_heap_cap w.(lw) = false.
  Proof. destruct w as [[] ?]; cbn; try discriminate; done. Qed.

  Lemma decode_load_not_heap_cap (w : LWord) dst src :
    decodeInstrW w.(lw) = CLoad dst src 0 → is_heap_cap w.(lw) = false.
  Proof. exact (decode_load_not_heap_cap_imm w dst src 0). Qed.

  (** A non-heap word loads exactly, without witness. *)
  Lemma load_post_not_heap_cap wit p (v v' : LWord) :
    is_heap_cap v.(lw) = false → load_post wit p v v' → v' = lload_word p v.
  Proof.
    rewrite /is_heap_cap. intros Hh (_ & Hnone & _). apply Hnone.
    by destruct (heap_cap_base v.(lw)).
  Qed.

  (* Loads of non-heap words: exact, without shadow ownership. The
     dereference witness [dw] is returned unchanged. *)
  Lemma wp_load_general_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs dw :
   decodeInstrW w.(lw) = CLoad r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (CLoad r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea loadv,
      reg_allows_load_imm regs r2 imm p g b e a ea → mem !! ea = Some loadv →
      is_shadow_address ea = false ∧ is_heap_cap loadv.(lw) = false) →
   dom mem = dom dfracs →

   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' regs' retv, RET retv;
       ⌜ ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
      regs' = <[r1 := lload_word p loadv]ₗ> regs) ∨
    (retv = FailedV ∧ ∃ fail : Load_failure_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm mem ∅ LoadPlain dw, True))⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad Hordinary Hdomeq φ) "(HPC & Hmem & Hdw & Hmap) Hφ".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 imm w mem dfracs
      regs ∅ DfracDiscarded LoadPlain dw with "[$HPC $Hmem $Hshadow $Hdw $Hmap]"); eauto.
    { intros p g b e ea Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [-> _].
      pose proof Hallow' as (_ & _ & _ & _).
      destruct (is_revoker_address ea); eauto. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & Hdw & Hmap)".
    iApply "Hφ". iFrame. iPureIntro.
    destruct Hspec as [p g b e ea loadv loadv' Hallow Hsh Hl Hpost Hinc Hregs'
                      |p g b e ea heap_a revoked Hallow Hsh|p g b e ea Hallow Hrev Hinc|Hfail].
    - left. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [_ Hh].
      rewrite (load_post_not_heap_cap _ _ _ _ Hh Hpost) in Hregs'.
      exists p, g, b, e, a, ea, loadv. done.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [Hsh' _]. congruence.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      all: try congruence.
    - right. split; first done. by exists Hfail.
  Qed.

  Lemma wp_load_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem regs dq :
   decodeInstrW w.(lw) = CLoad r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (CLoad r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea loadv,
      reg_allows_load_imm regs r2 imm p g b e a ea → mem !! ea = Some loadv →
      is_shadow_address ea = false ∧ is_heap_cap loadv.(lw) = false) →
   {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' regs' retv, RET retv;
       ⌜ ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
      regs' = <[r1 := lload_word p loadv]ₗ> regs) ∨
    (retv = FailedV ∧ ∃ fail : Load_failure_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm mem ∅ LoadPlain DerefNoId, True))⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "(HPC & Hmem & Hreg) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ DerefNoId
      with "[$HPC $Hmem $Hreg]");eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ? ?) "(?&?&Hmem&_&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  (* A load from ordinary memory without ownership of the revocation bit:
     the plain post (variant 1). *)
  Lemma wp_load_dfracs Ep pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w mem (dfracs : gmap Addr dfrac) regs :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_map_or_true src regs mem →
    (∀ p g b e a, reg_allows_load regs src p g b e a →
      is_shadow_address a = false) →
    dom mem = dom dfracs →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜(match retv with
    | NextIV => ∃ p g b e a loadv actualv,
        reg_allows_load regs src p g b e a ∧
        mem !! a = Some loadv ∧
        lload_heap (lload_word p loadv) actualv ∧
        incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
        regs' = <[dst := actualv]ₗ> regs
    | FailedV => True
    | _ => False
    end)⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad Hnonshadow Hdom φ)
      "(HPC & Hmem & Hmap) Hφ".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π dst src 0 w
      mem dfracs regs ∅ DfracDiscarded LoadPlain DerefNoId with "[$HPC $Hmem $Hshadow $Hmap]"); eauto.
    { intros p g b e a Hallow. rewrite (Hnonshadow _ _ _ _ _ Hallow).
      pose proof Hallow as (Hsrc & Hra & Hwb).
      destruct (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hsrc Hra Hwb) as [loadv Hl].
      destruct (is_revoker_address a); eauto. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & _ & Hmap)".
    iApply "Hφ". iFrame. iPureIntro.
    destruct Hspec as [p g b e a loadv loadv' Hallow Hsh Hl Hpost Hinc Hregs'
                      |p g b e a heap_a revoked Hallow Hsh|p g b e a Hallow Hrev Hnone Hinc|Hfail].
    - exists p, g, b, e, a, loadv, loadv'. by destruct Hpost.
    - exfalso. by rewrite (Hnonshadow _ _ _ _ _ Hallow) in Hsh.
    - exfalso. pose proof Hallow as (Hsrc & Hra & Hwb).
      destruct (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hsrc Hra Hwb) as [loadv Hl].
      all: try congruence.
    - done.
  Qed.

  (* The same, over memory owned with one fraction. *)
  Lemma wp_load Ep pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w mem regs dq :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_map_or_true src regs mem →
    (∀ p g b e a, reg_allows_load regs src p g b e a →
      is_shadow_address a = false) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜(match retv with
    | NextIV => ∃ p g b e a loadv actualv,
        reg_allows_load regs src p g b e a ∧
        mem !! a = Some loadv ∧
        lload_heap (lload_word p loadv) actualv ∧
        incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
        regs' = <[dst := actualv]ₗ> regs
    | FailedV => True
    | _ => False
    end)⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad Hnonshadow φ) "(HPC & Hmem & Hmap) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_dfracs with "[$HPC $Hmem $Hmap]"); eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iIntros "!>" (lpc' regs' retv) "(Hspec & HPC & Hmem & Hmap)".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply "Hφ". iFrame.
  Qed.

  #[local] Ltac load_fail_contra :=
    exfalso;
    lazymatch goal with Hfail : Load_failure_spec _ _ _ _ _ _ _ _ _ |- _ => destruct Hfail end;
    simplify_map_eq; cbn in *; try congruence;
    try (match goal with H : _ ≠ deref_id (deref_witness_of _ _) |- _ =>
           rewrite deref_id_witness_of in H; congruence end);
    try (match goal with H : ?π ≠ None, Hn : ∀ v : LWord, ?lhs = Some v → lprov v = None,
                         Hr : ?lhs = Some (_ @@? ?π) |- _ => by apply H, (Hn _ Hr) end);
    try (match goal with H : (_ + 0)%a = None |- _ => rewrite finz_add_0 in H; discriminate end);
    try (match goal with H : (_ + 0)%a = Some _ |- _ => rewrite finz_add_0 in H; simplify_eq end);
    try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end);
    try (match goal with H : load_post _ _ _ _ |- _ =>
           apply load_post_not_heap_cap in H;
           [subst | first [done | assumption | by rewrite /is_heap_cap /=]] end);
    try (match goal with H : incrementPC _ = None |- _ =>
           eapply incrementPC_None_inv in H; [|first [reflexivity | by simplify_map_eq]]; congruence end);
    try (match goal with H : incrementPC _ = None |- _ =>
           rewrite /incrementPC /incrementPC_gen in H; simplify_map_eq;
           rewrite /lload_word /lift_word /load_word /= in H;
           repeat (case_match; simplify_eq); congruence end);
    try (match goal with H : incrementPC _ = None |- _ =>
           rewrite /incrementPC /incrementPC_gen in H; simplify_map_eq;
           rewrite /lload_word /lift_word /load_word /= in H;
           match type of H with context [isDL ?p] => destruct (isDL p), (isDRO p) end;
           cbn in H; repeat case_match; congruence end);
    try (match goal with H : lw ?w = _, H' : is_cap (lw ?w) = false |- _ =>
           rewrite H in H'; discriminate end);
    try (match goal with H : ?t !! ?k = Some _, H' : ?t !! ?k = Some _ |- _ =>
           rewrite H in H'; simplify_eq; congruence end);
    try (match goal with H : is_revoker_address ?a = true,
                         H' : is_shadow_address ?a = true |- _ =>
           apply is_revoker_address_spec in H; subst;
           by rewrite revoker_not_shadow_address in H' end).

  Lemma wp_load_success_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) pc_a' dq dq' q :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ (if (eqb_addr ea pc_a) then emp else ▷ ea ↦ₐ{dq'} w')
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ (if (eqb_addr ea pc_a) then (lload_word p w) else (lload_word p w'))
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ (if (eqb_addr ea pc_a) then emp else ea ↦ₐ{dq'} w')
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a & Hdw) Hφ".
    rewrite deref_res_witness.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iApply (wp_load_general_imm with "[$HPC $Hmap $Hmem $Hdw]"); eauto; simplify_map_eq; eauto.
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto; by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0.
      simplify_map_eq.
      split; first done.
      pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem Hlookup0) as ->. exact Hheap. }
    { destruct (ea =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hmem & Hdw & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H2 & H3 & Hinc0 & ->) | (-> & (Hfail & _))].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       try incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       simplify_map_eq.
       iRegsMap "Hmap".
       iApply "Hφ". iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *) load_fail_contra. }
  Qed.

  Lemma wp_load_success_same_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a ea πs (imm : Z) pc_a' dq dq' q :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ (if (ea =? pc_a)%a then emp else ▷ ea ↦ₐ{dq'} w')
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ (if (ea =? pc_a)%a then lload_word p w else lload_word p w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (ea =? pc_a)%a then emp else ea ↦ₐ{dq'} w')
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & Hr1a & Hdw) Hφ".
    rewrite deref_res_witness.
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general_imm with "[$HPC $Hmap $Hmem $Hdw]"); eauto; simplify_map_eq; eauto.
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto; by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0.
      simplify_map_eq. split; first done.
      pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem Hlookup0) as ->. exact Hheap. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hmem & Hdw & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H0 & H1 & Hinc0 & ->) | (-> & (Hfail & _))].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       try incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       iRegsMap "Hmap". iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *) load_fail_contra. }
  Qed.

  Lemma wp_load_success_notinstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) pc_a' dq dq' q :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ ea ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ ea ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha & Hdw)".
    destruct (ea =? pc_a)%Z eqn:Ha.
    - rewrite (_: ea = pc_a); cycle 1.
      { apply Z.eqb_eq in Ha. solve_addr. }
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2 $Hdw]"); eauto.
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst ea. by rewrite Z.eqb_refl. }
      { by rewrite Ha. }
      iNext. iIntros "(? & ? & ? & ? & ? & ?)".
      iApply "Hφ".
      rewrite Ha.
      iFrame.
    - iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2 $Hdw Ha]"); eauto.
      { by rewrite Ha. }
      { rewrite Ha. iFrame. }
      iNext. iIntros "(? & ? & ? & ? & ? & ?)". rewrite Ha.
      iApply "Hφ". iFrame.
      Unshelve.
      + apply DfracDiscarded.
      + apply (lword_of_word (WInt 0)).
  Qed.

  Lemma wp_load_success_frominstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w'' p g b e a πs (imm : Z) pc_a' dq q :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ deref_res πs q }}}.
  Proof.
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & Hdw)".
    iIntros "Hφ".
    iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2 $Hdw]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    { by rewrite Z.eqb_refl. }
    iNext. iIntros "(? & ? & ? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_same_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a ea πs (imm : Z) pc_a' dq dq' q :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ ea ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ ea ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Ha & Hdw)".
    destruct (ea =? pc_a)%a eqn:Ha.
    { assert (ea = pc_a) as Heqa.
      { apply Z.eqb_eq in Ha. solve_addr. }
      rewrite Heqa. subst ea.
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1 $Hdw]"); eauto.
      { rewrite Ha; done. }
      { by rewrite Ha. }
      iNext. iIntros "(? & ? & ? & ? & ?)".
      iApply "Hφ". iFrame. rewrite Ha. iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1 $Hdw Ha]"); eauto.
    { by rewrite Ha. }
    { rewrite Ha. iFrame. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame.
    Unshelve.
    + apply (lword_of_word (WInt 0)).
    + apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_same_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e a πs (imm : Z) pc_a' dq q :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ deref_res πs q }}}.
  Proof.
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & Hdw)".
    iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1 $Hdw]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    { by rewrite Z.eqb_refl. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_alt_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) pc_a' dq q :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ ea ↦ₐ w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ ea ↦ₐ w'
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a & Hdw) Hφ".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (pointsto_ne with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_imm with "[$HPC $Hi $Hr1 $Hr2 $Hdw Hr2a]"); eauto; rewrite Hfalse; first iFrame.
    iNext. iIntros "(? & ? & ? & ? & ? & ?)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail_tag_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hsrc Htag φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hsrc) as (s0 & Hsrc' & _).
    rewrite Hinstr /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as [-> ->].
    { destruct wa as [[| [[] p g b e a|] | |] ?]; cbn in Htag; try discriminate.
      all: destruct s0; cbn in Hstep; by simplify_eq. }
    instr_fail_close.
  Qed.

  Lemma wp_load_fail_not_ra_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a πs (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hra Hsrc φ) "(HPC & Hi & Hd & Hs) Hφ".
    iApply (wp_instr_failed_2 with "[$HPC $Hd $Hs $Hi]"); [done | done | | ].
    { intros r sr m st s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H2 /= (decide_False _ _ Hsrc) /=.
      destruct s2; cbn; last done.
      destruct (a + imm)%a; cbn; [by rewrite Hra | done]. }
    iIntros "!> _". by iApply "Hφ".
  Qed.

  Lemma wp_load_fail_not_withinbounds_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e ea = false →
    (a + imm)%a = Some ea →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hwb Hadd Hsrc φ) "(HPC & Hi & Hd & Hs) Hφ".
    iApply (wp_instr_failed_2 with "[$HPC $Hd $Hs $Hi]"); [done | done | | ].
    { intros r sr m st s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H2 /= (decide_False _ _ Hsrc) /=.
      destruct s2; cbn; last done.
      by rewrite Hadd /= Hwb andb_false_r. }
    iIntros "!> _". by iApply "Hφ".
  Qed.

  Lemma wp_load_fail_addr_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa p g b e a dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    wa.(lw) = WCap true p g b e a →
    (a + imm)%a = None →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hsrc Hwa Hadd φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hsrc) as (s0 & Hsrc' & _).
    rewrite Hinstr /exec /= Hsrc' /= in Hstep.
    rewrite Hwa /= in Hstep. destruct s0; cbn in Hstep; rewrite ?Hadd /= in Hstep.
    all: assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as [-> ->] by (by simplify_eq).
    all: instr_fail_close.
  Qed.

  Lemma wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    is_cap wa.(lw) = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hsrc Htag φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hsrc) as (s0 & Hsrc' & _).
    rewrite Hinstr /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as [-> ->].
    { destruct wa as [[| [[] p g b e a|] | |] ?]; cbn in Htag; try discriminate.
      all: destruct s0; cbn in Hstep; by simplify_eq. }
    instr_fail_close.
  Qed.

  Lemma wp_load_fail_not_cap_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' (wsrc : LWord) (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc.(lw) = false ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ wsrc
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hcap φ) "(>HPC & >Hi & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 imm _ (if decide (r2 = cnull) then lnull else wsrc) with "[$HPC $Hi $Hmap]"); eauto; simplify_map_eq; eauto.
    { case_decide; done. }
    iNext. iIntros "_". by iApply "Hφ".
  Qed.

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ a ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ a ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (** Without shadow ownership, a load may fail or clear the loaded tag of a
      heap capability ([lload_heap]), in addition to the permission
      transformation performed by [load_word]. *)
  Lemma wp_load_preserve_or_clear E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' πs
    dst src (wi wd : LWord) p g b e a (raw : LWord) dq :
    readAllowed p = true ->
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = CLoad dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true p g b e a @@? πs ∗ a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ retv, RET retv; ⌜retv = FailedV⌝ ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗
        ⌜lload_heap (lload_word p raw) actual⌝ ∗
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true p g b e a @@? πs ∗ a ↦ₐ raw }}}.
  Proof.
    iIntros (Hread Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load_dfracs E pc_p pc_g pc_b pc_e pc_a pc_π dst src wi with "[$HPC $Hmap $Hmem]");
      eauto; simplify_map_eq; eauto.
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { exists true, p, g, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - case_decide; last done. exists raw. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _). simplify_map_eq. done. }
    all: try (by rewrite !dom_insert_L).
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & Hmap)".
    destruct retv; simpl in Hspec; [contradiction|iApply "Hφ"; by iLeft|].
    destruct Hspec as (p0 & g0 & b0 & e0 & a0 & loadv & actual &
      Hallow & Hlookup & Hactual & Hinc & ->).
    destruct Hallow as (Hsrc0 & _). simplify_map_eq.
    try (unfold incrementPC, incrementPC_gen in Hinc; simplify_map_eq).
    iRegsMap "Hmap"; eauto.
    iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; auto.
    iApply "Hφ". iRight. iExists actual. iFrame. done.
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w'' p g b e pc_a' dq πs q :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e pc_a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e pc_a @@? πs
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ a ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ a ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_same_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_frominstr E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e pc_a' dq πs q :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = CLoad r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e pc_a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_same_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)

  Lemma wp_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' πs dq q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ a ↦ₐ w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ a ↦ₐ w'
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_alt_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
    all: try by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    all: try (destruct (a =? pc_a)%a; eauto using decode_load_not_heap_cap).
  Qed.

  (* Reading a shadow-table entry returns its Boolean value as an integer. *)
  Lemma wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w regs mem dq shadow sdq p g b e a heap_a revoked lpc' :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load regs src p g b e a →
    (∀ v : LWord, regs !!ₗ src = Some v → v.(lprov) = None) →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some revoked →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        [∗ map] k↦y ∈ <[dst:=WInt (encodeAllocStatus revoked)]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem Hallow Hnoid Hshadow Htranslate Hlookup Hinc φ)
      "(>HPC & >Hmem & >Hshadow & >Hmap) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general _ pc_p pc_g pc_b pc_e pc_a pc_π dst src w mem _ regs shadow sdq LoadPlain DerefNoId
      with "[$HPC $Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      destruct Hallow as (Hsrc & _). rewrite Hsrc in Hsrc0. simplify_eq.
      rewrite Hshadow. exists heap_a. split; first done. by eexists. }
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (lpc0 regs0 retv) "(%Hspec & HPC & Hmem & Hshadow & _ & _ & Hmap)".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    destruct Hallow as (Hsrc & Hra & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 v0 v0' (Hsrc0 & _) Hshadow0
      |p0 g0 b0 e0 a0 heap_a0 revoked0 (Hsrc0 & _) Hshadow0 Htranslate0 Hlookup0 Hinc0
      |p0 g0 b0 e0 a0 (Hsrc0 & _) Hrev0
      |Hfail].
    - rewrite Hsrc in Hsrc0. simplify_eq. congruence.
    - rewrite Hsrc in Hsrc0. simplify_eq. rewrite Hlookup in Hlookup0. simplify_eq.
      iApply "Hφ". iFrame.
    - rewrite Hsrc in Hsrc0. simplify_eq. exfalso.
      apply is_revoker_address_spec in Hrev0. subst.
      by rewrite revoker_not_shadow_address in Hshadow.
    - load_fail_contra.
  Qed.

  Lemma wp_load_success_from_shadow E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a pc_a' heap_a revoked dq sdq πs :
    πs = None →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
        ∗ ▷ heap_a ↦ₛ{sdq} revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ r1 ↦ᵣ WInt (encodeAllocStatus revoked)
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
        ∗ heap_a ↦ₛ{sdq} revoked }}}.
  Proof.
    iIntros (-> Hshadow Htranslate Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iAssert ([∗ map] a0↦bit ∈ {[heap_a:=revoked]}, a0 ↦ₛ{sdq} bit)%I
      with "[Ha]" as "Hshadow"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 w _ _ dq _ sdq p g b e a heap_a revoked
      with "[$HPC $Hi $Hmap $Hshadow]"); eauto; simplify_map_eq; eauto.
    all: try (by rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    all: try (by rewrite /incrementPC /incrementPC_gen Hpca').
    iNext. iIntros "(HPC & Hi & Ha & Hmap)".
    rewrite -memMap_resource_1_dq big_sepM_singleton.
    iRegsMap "Hmap"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  (* Non-revoked heap capabilities use the usual load_word transformation. *)

  (* Revocation clears the validity tag after the ordinary load transformation. *)
  Lemma wp_load_fail_tag E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros.
    eapply wp_load_fail_tag_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

End griotte_lang_rules.

Section load_exact.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ}.

  (** Loading an identifier-less word that satisfies [load_exact_cond]
      (e.g. a heap root, which has authority) keeps it exactly: the fourth
      variant of the load rule. *)
  Lemma wp_load_success_exact E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w''
      p g b e a pc_a' πs dq q :
    is_shadow_address a = false →
    w'.(lprov) = None →
    load_exact_cond w' →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    a ≠ pc_a →
    r1 ≠ cnull → r2 ≠ cnull → r1 ≠ r2 →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w'' ∗
        ▷ r2 ↦ᵣ WCap true p g b e a @@? πs ∗
        ▷ a ↦ₐ w' ∗
        deref_res πs q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ lload_word p w' ∗
        r2 ↦ᵣ WCap true p g b e a @@? πs ∗
        a ↦ₐ w' ∗
        deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hπ Hexact Hinstr Hvpc Hra Hwb Hpca' Hne Hr1 Hr2 Hr12 φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha & Hdw) Hφ".
    rewrite deref_res_witness.
    iDestruct (map_of_regs_2 with "Hr2 Hr1") as "[Hmap %]".
    assert ((a =? pc_a)%Z = false) as Hneq.
    { apply Z.eqb_neq. intros Heq. apply Hne. by apply finz_to_z_eq. }
    iDestruct (memMap_resource_2gen_clater_dq pc_a a dq (DfracOwn 1) _ _
                 (λ a dq w, a ↦ₐ{dq} w)%I with "[Hi] [Ha]")
      as (mem dfracs) "[Hmem %Hmem]".
    { iNext. iExact "Hi". }
    { cbn. rewrite Hneq. iNext. iExact "Ha". }
    cbn in Hmem; rewrite Hneq in Hmem; destruct Hmem as [-> ->].
    iApply (wp_load_general _ pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 w _ _ _ ∅ DfracDiscarded LoadPlain
      (deref_witness_of πs q) with "[$HPC $Hmem $Hmap $Hdw]"); try done.
    all: try (by simplify_map_eq).
    all: try (by rewrite /regs_of ?dom_insert_L ?dom_singleton_L; set_solver+).
    all: try (by rewrite !dom_insert_L).
    all: try (by rewrite big_sepM_empty).
    { intros p0 g0 b0 e0 ea (Hreg & _ & _). simplify_map_eq. rewrite Hshadow.
      destruct (is_revoker_address ea); eauto. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & Hdw & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 loadv loadv' Hallow Hsh Hlook Hpost Hinc Hregs'
                      | p0 g0 b0 e0 a0 heap_a revoked Hallow Hsh _ Hlook _
                      | p0 g0 b0 e0 a0 Hallow Hrevk Hlook _
                      | Hfail].
    - destruct Hallow as (Hreg & _ & _). simplify_map_eq.
      destruct Hpost as (_ & _ & Hnone & _).
      first [rewrite (Hnone Hπ Hexact) in Hregs' | rewrite (Hnone Hπ Hexact)].
      try incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto.
      iDestruct (memMap_resource_2gen_d_dq (λ a dq w, a ↦ₐ{dq} w)%I pc_a a0
                   dq (DfracOwn 1) with "[Hmem]") as "[Hi Ha]".
      { iExists _, _. iFrame. iPureIntro. cbn. by rewrite Hneq. }
      cbn. rewrite Hneq.
      iApply "Hφ". iFrame.
    - by rewrite lookup_empty in Hlook.
    - destruct Hallow as (Hreg & _ & _). simplify_map_eq.
    - exfalso. destruct Hfail.
      all: simplify_map_eq; cbn in *; try congruence.
      all: try (match goal with H : _ ≠ deref_id (deref_witness_of _ _) |- _ =>
                  rewrite deref_id_witness_of in H; congruence end).
      all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
      all: try (match goal with H : (_ + 0)%a = _ |- _ => rewrite finz_add_0 in H; simplify_eq end).
      all: try congruence.
      all: try incrementPC_inv; simplify_map_eq; try congruence.
      all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
  Qed.

  (** The general load rule with a status witness, over owned memory. *)
  Lemma wp_load_witness_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 (imm : Z) w
      (mem : LMem) (regs : LReg) wit dw :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad r1 r2 imm) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_mem_or_shadow_offset r2 imm regs mem ∅ →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        load_witness_res wit ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Load_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' regs' mem ∅ wit dw retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        load_witness_res wit ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad φ) "(HPC & Hmem & Hwit & Hdw & Hreg) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm with "[$HPC $Hmem $Hshadow $Hwit $Hdw $Hreg]"); eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ? ?) "(?&?&Hmem&_&Hwit&Hdw&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

End load_exact.
