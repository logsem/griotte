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

  (** ** Status witnesses (§4.5)

      The loaded word's identifier decides the post. Every load gets the
      plain post: the loaded word, or its untagged copy if it is a heap
      capability. Exact posts follow for non-heap words and for
      identifier-less words with authority (variant 4), and, given a
      witness, untagged posts for quarantined identifiers (variant 2) and
      exact posts for live ones (variant 3). Witnesses are preconditions,
      returned unchanged. *)
  Inductive load_witness := LoadPlain | LoadQuar (ι : AId) | LoadLive (ι : AId) (q : Qp).

  Definition load_witness_res (wit : load_witness) : iProp Σ :=
    match wit with
    | LoadPlain => emp
    | LoadQuar ι => ι ⊒ AQuar
    | LoadLive ι q => ι ↦st{q} ALive
    end%I.

  Global Instance load_witness_res_timeless wit : Timeless (load_witness_res wit).
  Proof. destruct wit; apply _. Qed.

  Definition load_post (wit : load_witness) (p : Perm) (v v' : LWord) : Prop :=
    lload_heap (lload_word p v) v' ∧
    (heap_cap_base v.(lw) = None → v' = lload_word p v) ∧
    (v.(lprov) = None → load_exact_cond v → v' = lload_word p v) ∧
    match wit with
    | LoadPlain => True
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

  Lemma load_post_filter R C st wit (v : LWord) pw p pl :
    registry_ok R C st →
    load_witness_ok R wit →
    mem_word_ok R C v pw →
    load_filter st p pw = Some pl →
    load_post wit p v (pl @@? v.(lprov)).
  Proof.
    intros Hreg Hwit Hok Hpl.
    assert (∀ pl', pl = pl' → pl @@? v.(lprov) = pl' @@? v.(lprov)) as Heq by naive_solver.
    split; [|split; [|split]].
    - eapply mem_word_ok_load_lload_heap; eauto.
    - intros Hnone. destruct Hok as (_ & _ & Hnh & _). rewrite (Hnh Hnone) in Hpl.
      rewrite /load_filter Hnone in Hpl. simplify_eq. done.
    - intros Hπ Hcond. rewrite (load_filter_none _ _ _ _ _ _ _ Hreg Hok Hpl Hπ Hcond). done.
    - destruct wit as [|ι|ι q]; first done.
      + destruct Hwit as (x & Hx & Hle). intros Hπ Hside.
        rewrite (load_filter_quarantined _ _ _ _ _ _ _ _ _ Hreg Hok Hpl Hπ Hx Hle Hside). done.
      + destruct Hwit as (x & Hx & Hs). intros Hπ Hcond.
        rewrite (load_filter_live _ _ _ _ _ _ _ _ _ Hreg Hok Hpl Hπ Hx Hs Hcond). done.
  Qed.

  Inductive Load_failure_spec (regs: LReg) (r1 r2: RegName) (imm : Z)
    (mem : LMem) (shadow : ShadowTbl) (wit : load_witness) :=
  | Load_fail_const w:
      regs !!ₗ r2 = Some w ->
      is_cap w.(lw) = false →
      Load_failure_spec regs r1 r2 imm mem shadow wit
  | Load_fail_tag p g b e a:
      lw <$> regs !!ₗ r2 = Some (WCap false p g b e a) →
      Load_failure_spec regs r1 r2 imm mem shadow wit
  | Load_fail_addr_imm p g b e a:
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = None →
      Load_failure_spec regs r1 r2 imm mem shadow wit
  | Load_fail_bounds_imm p g b e a ea:
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      (readAllowed p = false ∨ withinBounds b e ea = false) →
      Load_failure_spec regs r1 r2 imm mem shadow wit
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC_imm p g b e a ea loadv loadv':
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      is_shadow_address ea = false →
      mem !! ea = Some loadv →
      load_post wit p loadv loadv' →
      incrementPC (<[ r1 := loadv' ]ₗ> regs) = None ->
      Load_failure_spec regs r1 r2 imm mem shadow wit
  | Load_fail_invalid_PC_shadow_imm p g b e a ea heap_a revoked:
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = Some ea →
      is_shadow_address ea = true →
      shadow_to_heap ea = Some heap_a →
      shadow !! heap_a = Some revoked →
      incrementPC (<[r1 := lword_of_word (WInt (encodeAllocStatus revoked))]ₗ> regs) = None →
      Load_failure_spec regs r1 r2 imm mem shadow wit
  | Load_fail_invalid_PC_revoker_imm p g b e a ea:
      lw <$> regs !!ₗ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = Some ea →
      is_revoker_address ea = true →
      mem !! ea = None →
      incrementPC (<[r1 := lword_of_word (WInt 0)]ₗ> regs) = None →
      Load_failure_spec regs r1 r2 imm mem shadow wit
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
    (regs: LReg) (r1 r2: RegName) (imm : Z)
    (regs': LReg) (mem : LMem) (shadow : ShadowTbl) (wit : load_witness) : griotte_lang.val → Prop
  :=
  | Load_spec_success p g b e a loadv loadv' :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = false →
    mem !! a = Some loadv →
    load_post wit p loadv loadv' →
    incrementPC (<[ r1 := loadv' ]ₗ> regs) = Some regs' ->
    Load_spec regs r1 r2 imm regs' mem shadow wit NextIV

  | Load_spec_success_shadow p g b e a heap_a revoked :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some revoked →
    incrementPC
      (<[ r1 := lword_of_word (WInt (encodeAllocStatus revoked)) ]ₗ> regs) = Some regs' →
    Load_spec regs r1 r2 imm regs' mem shadow wit NextIV

  (* The revoker reads as zero. *)
  | Load_spec_success_revoker p g b e a :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_revoker_address a = true →
    mem !! a = None →
    incrementPC (<[ r1 := lword_of_word (WInt 0) ]ₗ> regs) = Some regs' →
    Load_spec regs r1 r2 imm regs' mem shadow wit NextIV

  | Load_spec_failure :
    Load_failure_spec regs r1 r2 imm mem shadow wit ->
    Load_spec regs r1 r2 imm regs' mem shadow wit FailedV.

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

  (* Closes a failing load: the state is unchanged. *)
  Local Ltac load_fail Hstep :=
    injection Hstep as <- <-;
    try iApply bupd_fupd;
     iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); [done|];
    iIntros "Hmap"; iApply "Hφ"; iFrame; iPureIntro;
    apply Load_spec_failure.

  Lemma wp_load_general_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs shadow sdq wit :
   decodeInstrW w.(lw) = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_mem_or_shadow_offset r2 imm regs mem shadow →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
       load_witness_res wit ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 imm regs' mem shadow wit retv⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
         load_witness_res wit ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq φ)
      "(>Hmem & >Hshadow & Hwit & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ /=".
    destruct σ1 as [ [ [r sr] m] st]; cbn.
    iDestruct "Hσ" as (lreg lmem R C) "(Hr & Hsr & Hm & Hst & HR & HC & %Her)".
    iEval (rewrite /sreg /shadowtbl /=) in "Hsr Hst".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hlregs.
    pose proof (erasure_regs_incl _ _ _ _ _ _ Her Hlregs) as Hregs.
    iDestruct (load_witness_lookup with "HR Hwit") as %Hwit.
    pose proof (er_registry _ _ _ _ _ Her) as Hreg; cbn in Hreg.
    pose proof (er_mmio _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.
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
    assert (r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a)) as HPCr.
    { eapply lookup_weaken; last exact Hregs. by rewrite lookup_lregs_erase HPC. }
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r2) as [r2v [Hr'2 _]]; first by set_solver+.
    odestruct (Hri r1) as [r1v [Hr'1 _]]; first by set_solver+.
    clear Hri.
    assert (lookup_reg r2 r = Some r2v.(lw)) as Hr2.
    { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase Hr'2. }
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hmem_pc))
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
      assert ((Failed, (r, sr, m, st)) = (c, σ2)) as Hstep'.
      { unfold is_cap in Hr2v. destruct r2v as [r2v ?]; cbn in *.
        destruct_word r2v; by simplify_pair_eq. }
      load_fail Hstep'. by eapply Load_fail_const. }
    destruct r2v as [[ | [t p g b e a | ] | | ] π2]; try inversion Hr2v. clear Hr2v. cbn in Hstep.
    destruct t.
    2: { load_fail Hstep. eapply Load_fail_tag. by rewrite Hr'2. }
    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { load_fail Hstep. eapply Load_fail_addr_imm; last done. by rewrite Hr'2. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2: {
      apply andb_false_iff in HRA.
      load_fail Hstep. eapply Load_fail_bounds_imm; eauto. by rewrite Hr'2.
    }
    apply andb_true_iff in HRA as [Hra Hwb].
    assert (Hallow : reg_allows_load_offset regs r2 imm p g b e ea).
    { apply reg_allows_load_imm_offset with (a := a). repeat split; auto. by rewrite Hr'2. }
    specialize (HaLoad p g b e ea Hallow).

    (* Classify the read: the loaded logical word, which the register gets,
       and the spec's success and failure cases. *)
    assert (∃ v : LWord,
      reg_word_ok R C v ∧
      (match updatePC (update_reg (r, sr, m, st) r1 v.(lw)) with
       | Some conf => conf | None => (Failed, (r, sr, m, st)) end) = (c, σ2) ∧
      (∀ regs', incrementPC (<[r1 := v]ₗ> regs) = Some regs' →
         Load_spec regs r1 r2 imm regs' mem shadow wit NextIV) ∧
      (incrementPC (<[r1 := v]ₗ> regs) = None →
         Load_spec regs r1 r2 imm regs mem shadow wit FailedV))
      as (v & Hok & Hstep' & Hsucc & Hfailure).
    {
      destruct (is_shadow_address ea) eqn:Hshadow.
      - destruct HaLoad as (heap_a & Htranslate & revoked & Hlookup).
        rewrite Htranslate /= (Hshadow_valid _ _ Hlookup) /= in Hstep.
        exists (lword_of_word (WInt (encodeAllocStatus revoked))).
        split; first apply reg_word_ok_int. split; first exact Hstep.
        split.
        + intros. by eapply Load_spec_success_shadow.
        + intros. apply Load_spec_failure. by eapply Load_fail_invalid_PC_shadow_imm; eauto; rewrite Hr'2.
      - destruct (is_revoker_address ea) eqn:Hrevoker.
        + rewrite /= in Hstep.
          assert (mem !! ea = None) as Hnone.
          { destruct (mem !! ea) as [v|] eqn:Hv; last done.
            destruct (erasure_lookup_mem _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hv)) as (pv & Hpv & _).
            by rewrite (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hpv) in Hrevoker. }
          exists (lword_of_word (WInt 0)).
          split; first apply reg_word_ok_int. split; first exact Hstep.
          split.
          * intros. by eapply Load_spec_success_revoker.
          * intros. apply Load_spec_failure. by eapply Load_fail_invalid_PC_revoker_imm; eauto; rewrite Hr'2.
        + destruct HaLoad as (loadv & Hlookup).
          destruct (erasure_lookup_mem _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hlookup))
            as (pv & Hpv & Hpvok).
          rewrite Hpv /= in Hstep.
          destruct (load_filter_is_Some R C st p pv Hreg) as [pl Hpl].
          assert ((match updatePC (update_reg (r, sr, m, st) r1 pl) with
                   | Some conf => conf | None => (Failed, (r, sr, m, st)) end) = (c, σ2))
            as Hstep'.
          { rewrite -Hstep /load_filter in Hpl |- *.
            destruct (heap_cap_base pv) as [base|]; last by simplify_eq.
            destruct (st !! base) as [[]|]; simplify_eq; done. }
          pose proof (load_post_filter _ _ _ _ _ _ _ _ Hreg Hwit Hpvok Hpl) as Hpost.
          exists (pl @@? loadv.(lprov)).
          split; first by eapply mem_word_ok_load_reg_word.
          split; first exact Hstep'.
          split.
          * intros. by eapply Load_spec_success.
          * intros. apply Load_spec_failure. eapply Load_fail_invalid_PC_imm; eauto. by rewrite Hr'2.
    }
    iApply bupd_fupd.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ r1 v _ _ _
      (λ regs' retv, Load_spec regs r1 r2 imm regs' mem shadow wit retv)
      with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hmem Hshadow Hwit]").
    { exact Her. } { exact Hlregs. }
    { apply Dregs. set_solver+. } { by eexists. }
    { exact Hok. } { exact Hstep'. } { exact Hsucc. } { exact Hfailure. }
    iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_load_general Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs shadow sdq wit :
   decodeInstrW w.(lw) = Load r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
   regs_of (Load r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_mem_or_shadow r2 regs mem shadow →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
       load_witness_res wit ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 0 regs' mem shadow wit retv⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
         load_witness_res wit ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq.
    eapply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π
      r1 r2 0 w mem dfracs regs shadow sdq wit); eauto.
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

  Lemma mem_eq_implies_allow_load_map:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (w : LWord) p g b e a,
      mem = <[a:=w]> ∅
      → lw <$> regs !!ₗ r2 = Some (WCap true p g b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 w p g b e a Hmem Hrr2.
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hrr2) as (Hne & π & Hr2).
    exists true,p,g,b,e,a; split.
    - by rewrite /read_reg_inr Hr2.
    - case_decide; last done. exists w. subst mem. by rewrite lookup_insert_eq.
  Qed.

  Lemma mem_neq_implies_allow_load_map:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (pc_a : Addr)
      (w w' : LWord) p g b e a,
      a ≠ pc_a
      → mem = <[pc_a:=w]> (<[a:=w']> ∅)
      → lw <$> regs !!ₗ r2 = Some (WCap true p g b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a Hne' Hmem Hrr2.
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hrr2) as (Hne & π & Hr2).
    exists true,p,g,b,e,a; split.
    - by rewrite /read_reg_inr Hr2.
    - case_decide; last done. exists w'. subst mem.
      rewrite lookup_insert_ne //. by rewrite lookup_insert_eq.
  Qed.

  Lemma mem_implies_allow_load_map:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (pc_a : Addr)
      (w w' : LWord) p g b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[a:=w']> ∅))
      → lw <$> regs !!ₗ r2 = Some (WCap true p g b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a H4 Hrr2.
    destruct (a =? pc_a)%a eqn:Heq.
    + apply Z.eqb_eq, finz_to_z_eq in Heq. subst a. eapply mem_eq_implies_allow_load_map; eauto.
    + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_load_map; eauto. congruence.
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
    + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_load_map_imm; eauto. congruence.
  Qed.

  Lemma decode_load_not_heap_cap_imm (w : LWord) dst src imm :
    decodeInstrW w.(lw) = Load dst src imm → is_heap_cap w.(lw) = false.
  Proof. destruct w as [[] ?]; cbn; try discriminate; done. Qed.

  Lemma decode_load_not_heap_cap (w : LWord) dst src :
    decodeInstrW w.(lw) = Load dst src 0 → is_heap_cap w.(lw) = false.
  Proof. exact (decode_load_not_heap_cap_imm w dst src 0). Qed.

  (** A non-heap word loads exactly, without witness. *)
  Lemma load_post_not_heap_cap wit p (v v' : LWord) :
    is_heap_cap v.(lw) = false → load_post wit p v v' → v' = lload_word p v.
  Proof.
    rewrite /is_heap_cap. intros Hh (_ & Hnone & _). apply Hnone.
    by destruct (heap_cap_base v.(lw)).
  Qed.

  (* Loads of non-heap words: exact, without shadow ownership. *)
  Lemma wp_load_general_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs :
   decodeInstrW w.(lw) = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea loadv,
      reg_allows_load_imm regs r2 imm p g b e a ea → mem !! ea = Some loadv →
      is_shadow_address ea = false ∧ is_heap_cap loadv.(lw) = false) →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (<[r1 := lload_word p loadv]ₗ> regs) = Some regs') ∨
    (retv = FailedV ∧ ∃ fail : Load_failure_spec regs r1 r2 imm mem ∅ LoadPlain, True))⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hordinary Hdomeq φ) "(Hmem & Hmap) Hφ".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 imm w mem dfracs
      regs ∅ DfracDiscarded LoadPlain with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p g b e ea Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [-> _].
      pose proof Hallow' as (_ & _ & _ & _).
      destruct (is_revoker_address ea); eauto. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & _ & _ & Hmap)".
    iApply "Hφ". iFrame. iPureIntro.
    destruct Hspec as [p g b e ea loadv loadv' Hallow Hsh Hl Hpost Hinc
                      |p g b e ea heap_a revoked Hallow Hsh|p g b e ea Hallow Hrev Hinc|Hfail].
    - left. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [_ Hh].
      rewrite (load_post_not_heap_cap _ _ _ _ Hh Hpost) in Hinc.
      exists p, g, b, e, a, ea, loadv. done.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [Hsh' _]. congruence.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      congruence.
    - right. split; first done. by exists Hfail.
  Qed.

  Lemma wp_load_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem regs dq :
   decodeInstrW w.(lw) = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea loadv,
      reg_allows_load_imm regs r2 imm p g b e a ea → mem !! ea = Some loadv →
      is_shadow_address ea = false ∧ is_heap_cap loadv.(lw) = false) →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (<[r1 := lload_word p loadv]ₗ> regs) = Some regs') ∨
    (retv = FailedV ∧ ∃ fail : Load_failure_spec regs r1 r2 imm mem ∅ LoadPlain, True))⌝ ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "[Hmem Hreg] Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general_imm with "[$Hmem $Hreg]");eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ?) "(?&Hmem&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  (* A load from ordinary memory without ownership of the revocation bit:
     the plain post (variant 1). *)
  Lemma wp_load Ep pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w mem regs dq :
    decodeInstrW w.(lw) = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Load dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_map_or_true src regs mem →
    (∀ p g b e a, reg_allows_load regs src p g b e a →
      is_shadow_address a = false) →
    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜(match retv with
    | NextIV => ∃ p g b e a loadv actualv,
        reg_allows_load regs src p g b e a ∧
        mem !! a = Some loadv ∧
        lload_heap (lload_word p loadv) actualv ∧
        incrementPC (<[dst := actualv]ₗ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end)⌝ ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hnonshadow φ)
      "(Hmem & Hmap) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π dst src 0 w
      mem _ regs ∅ DfracDiscarded LoadPlain with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p g b e a Hallow. rewrite (Hnonshadow _ _ _ _ _ Hallow).
      pose proof Hallow as (Hsrc & Hra & Hwb).
      destruct (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hsrc Hra Hwb) as [loadv Hl].
      destruct (is_revoker_address a); eauto. }
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & _ & _ & Hmap)".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply "Hφ". iFrame. iPureIntro.
    destruct Hspec as [p g b e a loadv loadv' Hallow Hsh Hl Hpost Hinc
                      |p g b e a heap_a revoked Hallow Hsh|p g b e a Hallow Hrev Hnone Hinc|Hfail].
    - exists p, g, b, e, a, loadv, loadv'. by destruct Hpost.
    - exfalso. by rewrite (Hnonshadow _ _ _ _ _ Hallow) in Hsh.
    - exfalso. pose proof Hallow as (Hsrc & Hra & Hwb).
      destruct (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hsrc Hra Hwb) as [loadv Hl].
      congruence.
    - done.
  Qed.

  Local Ltac load_fail_contra :=
    exfalso;
    lazymatch goal with Hfail : Load_failure_spec _ _ _ _ _ _ _ |- _ => destruct Hfail end;
    simplify_map_eq; cbn in *; try congruence;
    try (match goal with H : (_ + 0)%a = None |- _ => rewrite finz_add_0 in H; discriminate end);
    try (match goal with H : (_ + 0)%a = Some _ |- _ => rewrite finz_add_0 in H; simplify_eq end);
    try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end);
    try (match goal with H : load_post _ _ _ _ |- _ =>
           apply load_post_not_heap_cap in H;
           [subst | first [done | assumption | by rewrite /is_heap_cap /=]] end);
    try (match goal with H : incrementPC _ = None |- _ =>
           eapply incrementPC_None_inv in H; [|by simplify_map_eq]; congruence end);
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

  Lemma wp_load_success_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ (if (eqb_addr ea pc_a) then emp else ▷ ea ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ (if (eqb_addr ea pc_a) then (lload_word p w) else (lload_word p w'))
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ (if (eqb_addr ea pc_a) then emp else ea ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iApply (wp_load_general_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto; by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0.
      simplify_map_eq.
      split; first done.
      pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem Hlookup0) as ->. exact Hheap. }
    { destruct (ea =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H2 & H3 & Hinc0) | (-> & (Hfail & _))].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iApply "Hφ". iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *) load_fail_contra. }
  Qed.

  Lemma wp_load_success_same_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a ea πs (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ (if (ea =? pc_a)%a then emp else ▷ ea ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ (if (ea =? pc_a)%a then lload_word p w else lload_word p w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (ea =? pc_a)%a then emp else ea ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto; by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0.
      simplify_map_eq. split; first done.
      pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem Hlookup0) as ->. exact Hheap. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H0 & H1 & Hinc0) | (-> & (Hfail & _))].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *) load_fail_contra. }
  Qed.

  Lemma wp_load_success_notinstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ ea ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ ea ↦ₐ{dq'} w' }}}.
  Proof.
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha)".
    destruct (ea =? pc_a)%Z eqn:Ha.
    - rewrite (_: ea = pc_a); cycle 1.
      { apply Z.eqb_eq in Ha. solve_addr. }
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst ea. by rewrite Z.eqb_refl. }
      { by rewrite Ha. }
      iNext. iIntros "(? & ? & ? & ? & ?)".
      iApply "Hφ".
      rewrite Ha.
      iFrame.
    - iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2 Ha]"); eauto.
      { by rewrite Ha. }
      { rewrite Ha. iFrame. }
      iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
      iApply "Hφ". iFrame.
      Unshelve.
      + apply DfracDiscarded.
      + apply (lword_of_word (WInt 0)).
  Qed.

  Lemma wp_load_success_frominstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w'' p g b e a πs (imm : Z) pc_a' dq :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs }}}.
  Proof.
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2)".
    iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    { by rewrite Z.eqb_refl. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_same_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a ea πs (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ ea ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ ea ↦ₐ{dq'} w' }}}.
  Proof.
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Ha)".
    destruct (ea =? pc_a)%a eqn:Ha.
    { assert (ea = pc_a) as Heqa.
      { apply Z.eqb_eq in Ha. solve_addr. }
      rewrite Heqa. subst ea.
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1]"); eauto.
      { rewrite Ha; done. }
      { by rewrite Ha. }
      iNext. iIntros "(? & ? & ? & ?)".
      iApply "Hφ". iFrame. rewrite Ha. iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1 Ha]"); eauto.
    { by rewrite Ha. }
    { rewrite Ha. iFrame. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame.
    Unshelve.
    + apply (lword_of_word (WInt 0)).
    + apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_same_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e a πs (imm : Z) pc_a' dq :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1)".
    iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    { by rewrite Z.eqb_refl. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_alt_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) pc_a' :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ ea ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ ea ↦ₐ w' }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_imm with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_success_same_alt_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a ea πs (imm : Z) pc_a' :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ ea ↦ₐ w'}}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ w
             ∗ ea ↦ₐ w' }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1 Ha]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_fail_tag_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa :
    decodeInstrW w.(lw) = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs !!ₗ src = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hsrc Htag φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hregs Hregs' Hpc_a' Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    assert (lookup_reg src r = Some wa.(lw)) as Hsrc'.
    { eapply lookup_reg_weaken; last exact Hregs'. by rewrite lookup_reg_erase Hsrc. }
    rewrite Hinstr /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ' = (r, sr, m, st)) as [-> ->].
    { destruct wa as [[| [[] p g b e a|] | |] ?]; cbn in Htag; try discriminate.
      all: cbn in Hstep; by simplify_eq. }
    iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
    iIntros "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail_not_ra_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a πs (imm : Z) :
    decodeInstrW w.(lw) = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
     iIntros (Hdecode Hvpc Hbounds Hcnull φ) "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite memMap_resource_1_dq.
     iApply (wp_load_imm with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto;
       try solve [intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & Hra0 & Hwb0) Hlookup0;
         simplify_map_eq; congruence].
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true_imm.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load_imm; simplify_map_eq.
         destruct (a + imm)%a; cbn; last done.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&?&_); done.
     }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H2 & Hmem0 & Hinc0) | (-> & (Hfail & _))].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. congruence.
     }
     by iApply "Hφ".
  Qed.

  Lemma wp_load_fail_not_withinbounds_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) :
    decodeInstrW w.(lw) = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e ea = false →
    (a + imm)%a = Some ea →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
     iIntros (Hdecode Hvpc Hbounds Hadd Hcnull φ) "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite memMap_resource_1_dq.
     iApply (wp_load_imm with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto;
       try solve [intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & Hra0 & Hwb0) Hlookup0;
         simplify_map_eq; congruence].
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true_imm.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load_imm; simplify_map_eq.
         try rewrite Hadd.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&_&?); done.
     }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H2 & Hmem0 & Hinc0) | (-> & (Hfail & _))].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq). congruence.
     }
     by iApply "Hφ".
  Qed.

  Lemma wp_load_success_PC_imm E r2 pc_p pc_g pc_b pc_e pc_a pc_π w πs
        p g b e a ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    is_shadow_address ea = false →
    is_heap_cap (WCap t p' g' b' e' a') = false →
    decodeInstrW w.(lw) = Load PC r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ ea ↦ₐ WCap t p' g' b' e' a' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ lload_word p (WCap t p' g' b' e' a'')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ ea ↦ₐ WCap t p' g' b' e' a' }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0;
        simplify_map_eq; split; assumption].
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map_imm with (a := a) (ea := ea) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H1 & Hmem0 & Hinc0) | (-> & (Hfail & _))].
     { (* Success *)
       iApply "Hφ".
       destruct H1 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto.
       iFrame.
       rewrite /lload_word /lift_word in H1 |- *; cbn in *.
       by destruct p0; destruct dro,dl; rewrite /load_word in H1 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *) load_fail_contra. }
  Qed.

  Lemma wp_load_fail_addr_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa p g b e a :
    decodeInstrW w.(lw) = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs !!ₗ src = Some wa →
    wa.(lw) = WCap true p g b e a →
    (a + imm)%a = None →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hsrc Hwa Hadd φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hregs Hregs' Hpc_a' Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    assert (lookup_reg src r = Some wa.(lw)) as Hsrc'.
    { eapply lookup_reg_weaken; last exact Hregs'. by rewrite lookup_reg_erase Hsrc. }
    rewrite Hinstr /exec /= Hsrc' /= in Hstep.
    rewrite Hwa /= Hadd /= in Hstep.
    assert (c = Failed ∧ σ' = (r, sr, m, st)) as [-> ->] by (by simplify_eq).
    iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
    iIntros "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa :
    decodeInstrW w.(lw) = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs !!ₗ src = Some wa →
    is_cap wa.(lw) = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hsrc Htag φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hregs Hregs' Hpc_a' Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    assert (lookup_reg src r = Some wa.(lw)) as Hsrc'.
    { eapply lookup_reg_weaken; last exact Hregs'. by rewrite lookup_reg_erase Hsrc. }
    rewrite Hinstr /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ' = (r, sr, m, st)) as [-> ->].
    { destruct wa as [[| [[] p g b e a|] | |] ?]; cbn in Htag; try discriminate.
      all: cbn in Hstep; by simplify_eq. }
    iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
    iIntros "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail_not_cap_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' (wsrc : LWord) (imm : Z) :
    decodeInstrW w.(lw) = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc.(lw) = false ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ wsrc
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hcap φ) "(>HPC & >Hi & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 imm _ (if decide (r2 = cnull) then lnull else wsrc) with "[$Hi $Hmap]"); eauto; simplify_map_eq; eauto.
    { case_decide; done. }
    iNext. iIntros "_". by iApply "Hφ".
  Qed.

  Lemma wp_load_success_fromPC_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' ea (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ (if (ea =? pc_a)%a then emp else ▷ ea ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ (if (ea =? pc_a)%a then lload_word pc_p w else lload_word pc_p w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (ea =? pc_a)%a then emp else ea ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hwb Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    assert (readAllowed pc_p = true) as Hra.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc. apply andb_prop_elim in Hpc as [Hra _]. by apply Is_true_true. }
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto; by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0.
      simplify_map_eq. split; first done.
      pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem Hlookup0) as ->.
      case_match; last exact Hheap.
      by eapply decode_load_not_heap_cap_imm. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H0 & H1 & Hinc0) | (-> & (Hfail & _))].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *) load_fail_contra. }
  Qed.

  Lemma wp_load_success_PC_PC_imm E pc_p pc_g pc_b pc_e pc_a pc_π w
        ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    is_shadow_address ea = false →
    is_heap_cap (WCap t p' g' b' e' a') = false →
    decodeInstrW w.(lw) = Load PC PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ ea ↦ₐ WCap t p' g' b' e' a' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ lload_word pc_p (WCap t p' g' b' e' a'')
             ∗ pc_a ↦ₐ w
             ∗ ea ↦ₐ WCap t p' g' b' e' a' }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hwb Hadd Hpca' φ)
            "(>HPC & >Hi & >Hr2a) Hφ".
    assert (readAllowed pc_p = true) as Hra.
    { apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra _]. by apply Is_true_true. }
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0;
        simplify_map_eq; split; assumption].
    { eapply mem_neq_implies_allow_load_map_imm with (a := pc_a) (ea := ea) (pc_a := pc_a); eauto.
    }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H0 & Hmem0 & Hinc0) | (-> & (Hfail & _))].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_1 with "Hmap") as "HPC".
       iFrame.
       rewrite /lload_word /lift_word in H0 |- *; cbn in *.
       by destruct p; destruct dro,dl; rewrite /load_word in H0 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *) load_fail_contra. }
  Qed.

  Lemma wp_load_success_fromPC_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' ea (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ ea ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word pc_p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ ea ↦ₐ{dq'} w' }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hwb Hadd Hincr Hnull φ) "(>HPC & >Hi & >Hr & >Hm) Hφ".
    destruct (ea =? pc_a)%a eqn:Heq.
    - apply Z.eqb_eq, finz_to_z_eq in Heq. subst ea.
      iDestruct (pointsto_agree with "Hi Hm") as %->.
      iApply (wp_load_success_fromPC_imm with "[$HPC $Hi $Hr]"); eauto.
      { rewrite Z.eqb_refl. done. }
      iNext. iIntros "(HPC & Hr & Hi & _)". rewrite Z.eqb_refl.
      iApply "Hφ". iFrame.
    - iApply (wp_load_success_fromPC_imm with "[$HPC $Hi $Hr Hm]"); eauto.
      { rewrite Heq. iFrame. }
      iNext. iIntros "(HPC & Hr & Hi & Hm)". rewrite Heq.
      iApply "Hφ". iFrame.
    Unshelve. all: first [exact (lword_of_word (WInt 0)) | exact DfracDiscarded].
  Qed.

  Lemma wp_load_success_fromPC_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w w'' dq (imm : Z) :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w'' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ pc_a ↦ₐ{dq} w
             ∗ r1 ↦ᵣ lload_word pc_p w }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hadd Hincr Hnull φ) "(>HPC & >Hi & >Hr) Hφ".
    assert (withinBounds pc_b pc_e pc_a = true) as Hwb.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc.
      apply andb_prop_elim in Hpc as [_ Hwb]. by apply Is_true_true. }
    iApply (wp_load_success_fromPC_imm with "[$HPC $Hi $Hr]"); eauto.
    { rewrite Z.eqb_refl. done. }
    iNext. iIntros "(HPC & Hr & Hi & _)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame.
    Unshelve. all: first [exact (lword_of_word (WInt 0)) | exact DfracDiscarded].
  Qed.

  Lemma wp_load_success E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs :
    is_shadow_address a = false →
    is_heap_cap (if (a =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ (if (eqb_addr a pc_a) then (lload_word p w) else (lload_word p w'))
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ (if (eqb_addr a pc_a) then emp else a ↦ₐ{dq'} w') }}}.
  Proof.
    intros Hshadow Hheap Hinstr Hvpc Hbounds Hpc Hdst Hsrc.
    eapply wp_load_success_imm; eauto.
    by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ a ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ a ↦ₐ{dq'} w' }}}.
  Proof.
    intros.
    eapply wp_load_success_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (** Without shadow ownership, a load may fail or clear the loaded tag of a
      heap capability ([lload_heap]), in addition to the permission
      transformation performed by [load_word]. *)
  Lemma wp_load_preserve_or_clear E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' πs
    dst src (wi wd : LWord) p g b e a (raw : LWord) :
    readAllowed p = true ->
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true p g b e a @@? πs ∗ a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ retv, RET retv; ⌜retv = FailedV⌝ ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗
        ⌜lload_heap (lload_word p raw) actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true p g b e a @@? πs ∗ a ↦ₐ raw }}}.
  Proof.
    iIntros (Hread Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load E pc_p pc_g pc_b pc_e pc_a pc_π dst src wi with "[$Hmap $Hmem]");
      eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { exists true, p, g, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - case_decide; last done. exists raw. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _). simplify_map_eq. done. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct retv; simpl in Hspec; [contradiction|iApply "Hφ"; by iLeft|].
    destruct Hspec as (p0 & g0 & b0 & e0 & a0 & loadv & actual &
      Hallow & Hlookup & Hactual & Hinc).
    destruct Hallow as (Hsrc0 & _). simplify_map_eq.
    unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
    rewrite (insert_insert_ne _ dst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iApply "Hφ". iRight. iExists actual. iFrame. done.
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w'' p g b e pc_a' dq πs :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e pc_a @@? πs }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e pc_a @@? πs }}}.
  Proof.
    intros.
    eapply wp_load_success_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs :
    is_shadow_address a = false →
    is_heap_cap (if (a =? pc_a)%a then w else w').(lw) = false →
    decodeInstrW w.(lw) = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ (if (a =? pc_a)%a then lload_word p w else lload_word p w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (a =? pc_a)%a then emp else a ↦ₐ{dq'} w') }}}.
  Proof.
    intros.
    eapply wp_load_success_same_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ a ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ a ↦ₐ{dq'} w' }}}.
  Proof.
    intros.
    eapply wp_load_success_same_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_frominstr E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e pc_a' dq πs :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e pc_a @@? πs }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros.
    eapply wp_load_success_same_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC E r2 pc_p pc_g pc_b pc_e pc_a pc_π w πs
        p g b e a (t' : bool) p' g' b' e' a' a'' :
    is_shadow_address a = false →
    is_heap_address b' = false →
    decodeInstrW w.(lw) = Load PC r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ a ↦ₐ WCap t' p' g' b' e' a' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ lload_word p (WCap t' p' g' b' e' a'')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ a ↦ₐ WCap t' p' g' b' e' a' }}}.
  Proof.
    intros.
    eapply wp_load_success_PC_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
    all: try by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    all: try (destruct (a =? pc_a)%a; eauto using decode_load_not_heap_cap).
    all: by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= H0.
  Qed.

  Lemma wp_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w w'' dq :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = Load r1 PC 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w'' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ pc_a ↦ₐ{dq} w
             ∗ r1 ↦ᵣ lload_word pc_p w }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hpc Hnull Φ) "(>HPC & >Hi & >Hr1) HΦ".
    iApply (wp_load_success_fromPC_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π
      w w w'' pc_a 0 pc_a' dq dq with "[$HPC $Hi $Hr1]"); eauto.
    - exact (decode_load_not_heap_cap w r1 PC Hinstr).
    - apply isCorrectPC_ra_wb in Hvpc.
      apply andb_prop_elim in Hvpc as [_ Hwb].
      apply Is_true_eq_true in Hwb. apply andb_true_iff in Hwb as [Hle Hlt].
      apply withinBounds_true_iff. solve_addr.
    - by rewrite finz_add_0.
    - by rewrite Z.eqb_refl.
    - iNext. iIntros "(HPC & Hr1 & Hi & _)".
      rewrite Z.eqb_refl. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' πs :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ a ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
             ∗ a ↦ₐ w' }}}.
  Proof.
    intros.
    eapply wp_load_success_alt_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
    all: try by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    all: try (destruct (a =? pc_a)%a; eauto using decode_load_not_heap_cap).
  Qed.

  Lemma wp_load_success_same_alt E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a pc_a' πs :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
          ∗ ▷ a ↦ₐ w'}}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ w
             ∗ a ↦ₐ w' }}}.
  Proof.
    intros.
    eapply wp_load_success_same_alt_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
    all: try by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    all: try (destruct (a =? pc_a)%a; eauto using decode_load_not_heap_cap).
  Qed.

  Lemma wp_load_fail_not_cap E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' (wsrc : LWord) :
    decodeInstrW w.(lw) = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc.(lw) = false ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ wsrc
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
    intros.
    eapply wp_load_fail_not_cap_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_fail_not_ra E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a πs :
    decodeInstrW w.(lw) = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
    intros.
    eapply wp_load_fail_not_ra_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_fail_not_withinbounds E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a πs :
    decodeInstrW w.(lw) = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = false →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
    intros.
    eapply wp_load_fail_not_withinbounds_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (* Reading a shadow-table entry returns its Boolean value as an integer. *)
  Lemma wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w regs regs' mem dq shadow sdq p g b e a heap_a revoked :
    decodeInstrW w.(lw) = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Load dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load regs src p g b e a →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some revoked →
    incrementPC (<[dst:=WInt (encodeAllocStatus revoked)]ₗ> regs) = Some regs' →
    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem Hallow Hshadow Htranslate Hlookup Hinc φ)
      "(>Hmem & >Hshadow & >Hmap) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general _ pc_p pc_g pc_b pc_e pc_a pc_π dst src w mem _ regs shadow sdq LoadPlain
      with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      destruct Hallow as (Hsrc & _). rewrite Hsrc in Hsrc0. simplify_eq.
      rewrite Hshadow. exists heap_a. split; first done. by eexists. }
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (regs0 retv) "(%Hspec & Hmem & Hshadow & _ & Hmap)".
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
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ WCap true p g b e a @@? πs
        ∗ ▷ heap_a ↦ₛ{sdq} revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ r1 ↦ᵣ WInt (encodeAllocStatus revoked)
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ WCap true p g b e a @@? πs
        ∗ heap_a ↦ₛ{sdq} revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    rewrite memMap_resource_1_dq.
    iAssert ([∗ map] a0↦bit ∈ {[heap_a:=revoked]}, a0 ↦ₛ{sdq} bit)%I
      with "[Ha]" as "Hshadow"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 w _ _ _ dq _ sdq p g b e a heap_a revoked
      with "[$Hi $Hmap $Hshadow]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hi & Ha & Hmap)".
    rewrite -memMap_resource_1_dq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hr1 & Hr2)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_from_shadow_same E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e a pc_a' heap_a revoked dq sdq πs :
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w.(lw) = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w

        ∗ ▷ r1 ↦ᵣ WCap true p g b e a @@? πs
        ∗ ▷ heap_a ↦ₛ{sdq} revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ r1 ↦ᵣ WInt (encodeAllocStatus revoked)
        ∗ pc_a ↦ₐ{dq} w

        ∗ heap_a ↦ₛ{sdq} revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc [Hra Hwb] Hpca' Hcnull φ)
      "(>HPC & >Hi & >Hr1 & >Ha) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iAssert ([∗ map] a0↦bit ∈ {[heap_a:=revoked]}, a0 ↦ₛ{sdq} bit)%I
      with "[Ha]" as "Hshadow"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π r1 r1 w _ _ _ dq _ sdq p g b e a heap_a revoked
      with "[$Hi $Hmap $Hshadow]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hi & Ha & Hmap)".
    rewrite -memMap_resource_1_dq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(HPC & Hr1)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  (* Non-revoked heap capabilities use the usual load_word transformation. *)
  Lemma wp_load_success_from_shadow_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w w'' heap_a revoked dq sdq :
    is_shadow_address pc_a = true →
    shadow_to_heap pc_a = Some heap_a →
    decodeInstrW w.(lw) = Load r1 PC 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ heap_a ↦ₛ{sdq} revoked }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ pc_a ↦ₐ{dq} w
             ∗ r1 ↦ᵣ WInt (encodeAllocStatus revoked)
             ∗ heap_a ↦ₛ{sdq} revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & >Hs) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iAssert ([∗ map] a0↦bit ∈ {[heap_a:=revoked]}, a0 ↦ₛ{sdq} bit)%I
      with "[Hs]" as "Hs"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a pc_π r1 PC w _ _ _ dq _ sdq pc_p pc_g pc_b pc_e pc_a heap_a revoked
      with "[$Hmap $Hi $Hs]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_load. split; first by simplify_map_eq.
      apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
      split; by apply Is_true_true. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hi & Hs & Hmap)".
    rewrite -memMap_resource_1_dq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hr]"; eauto.
    iApply "Hφ". iFrame.
  Qed.


  (* Revocation clears the validity tag after the ordinary load transformation. *)
  Lemma wp_load_fail_tag E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src regs wa :
    decodeInstrW w.(lw) = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs !!ₗ src = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros.
    eapply wp_load_fail_tag_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

End griotte_lang_rules.
