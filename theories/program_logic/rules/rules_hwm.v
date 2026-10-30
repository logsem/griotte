From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base rules_Store rules_SpecialRW si_modality.

(** * The stack high-water mark

    The rules for MSHWM and MSHWMB, and for the zone of zeroed cells that the
    state interpretation couples to them. MSHWMB and MSHWM are per thread:
    their fragments are [mshwmb ↦ₜ hb] and [mshwm ↦ₜ h], and the physical
    registers hold [hb] and [h]. The zone covers [[hb, h)]. A cell of the
    zone ([zone_cell]) holds half of its points-to, so the load rules read
    it. *)

(** MSHWM after a store at [x] to a cell of the zone: [x] if it is in
    [[hb, h)], [h] otherwise. *)
Definition hwm_after (x : Addr) (hb h : Z) : Z :=
  if decide (hb ≤ x < h)%Z then x else h.

Section hwm.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types w : LWord.

  (** ** The high-water-mark part of [sys_interp] *)

  #[local] Lemma ls_set_hwm_hwmb_id ls : ls_set_hwm (ls_set_hwmb ls (ls_hwmb ls)) (ls_hwm ls) = ls.
  Proof. by destruct ls. Qed.

  (** The two authorities and the zone, and the closing with new values. *)
  #[local] Lemma sys_interp_hwm_open ls :
    sys_interp ls -∗
    mshwmb_auth (ls_hwmb ls) ∗
    mshwm_auth (ls_hwm ls) ∗
    hwm_zone (ls_hwmb ls) (ls_hwm ls) ∗
    (∀ hb h, mshwmb_auth hb -∗ mshwm_auth h -∗ hwm_zone hb h -∗
       sys_interp (ls_set_hwm (ls_set_hwmb ls hb) h)).
  Proof.
    iIntros "Hsys". iNamed "Hsys". iFrame "Hmshwmb_a Hmshwm_a Hzone".
    iIntros (hb h) "Hmshwmb_a Hmshwm_a Hzone". rewrite /sys_interp /=.
    iFrame "Hsr Hmtcc Hmpie Hmpie_f Hmtdc Hmie Hmie_f Hwins Hmshwmb_a Hmshwm_a Hzone".
    iPureIntro. done.
  Qed.

  #[local] Lemma sys_interp_mshwmb_agree ls hb :
    sys_interp ls -∗ mshwmb ↦ₜ hb -∗ ⌜ls_hwmb ls = hb⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (mshwmb_agree with "Hmshwmb_a Hf"). Qed.

  #[local] Lemma sys_interp_mshwm_agree ls h :
    sys_interp ls -∗ mshwm ↦ₜ h -∗ ⌜ls_hwm ls = h⌝.
  Proof. iIntros "Hsys Hf". iNamed "Hsys". iApply (mshwm_agree with "Hmshwm_a Hf"). Qed.

  (** A ghost update that keeps the system registers. *)
  #[local] Lemma si_upd_sys E P Q :
    (∀ ls, sys_interp ls -∗ P ==∗ sys_interp ls ∗ Q) → P ⊢ |~{E}~> Q.
  Proof.
    intros Hupd. apply si_upd_ghost. iIntros (σ) "Hσ HP".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iMod (Hupd with "Hsr HP") as "[Hsr $]".
    iModIntro. iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** The ghost part of a store to the cell [x] of the zone: the cell leaves
      the zone with the other half of its points-to, and MSHWM becomes
      [hwm_after x hb h]. *)
  #[local] Lemma sys_interp_zone_store ls (x : Addr) (hb h : Z) :
    sys_interp ls -∗
    zone_token x -∗
    mshwmb ↦ₜ hb -∗
    mshwm ↦ₜ h
    ==∗
    ⌜ls_hwmb ls = hb ∧ ls_hwm ls = h⌝ ∗
    sys_interp (ls_set_hwm ls (hwm_after x hb h)) ∗
    x ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt 0) ∗
    mshwmb ↦ₜ hb ∗
    mshwm ↦ₜ hwm_after x hb h.
  Proof.
    iIntros "Hsys Htok Hb Hh".
    iDestruct (sys_interp_hwm_open with "Hsys") as "(Hmshwmb_a & Hmshwm_a & Hzone & Hclose)".
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
    iDestruct (mshwm_agree with "Hmshwm_a Hh") as %Hh. subst hb h.
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iDestruct (zone_auth_elem with "Hzone_auth Htok") as %Hxz.
    iMod (zone_auth_delete with "Hzone_auth Htok") as "Hzone_auth".
    iDestruct (big_sepS_delete with "Hzone_cells") as "[Hx Hzone_cells]"; first exact Hxz.
    iMod (mshwm_update _ _ (hwm_after x (ls_hwmb ls) (ls_hwm ls)) with "Hmshwm_a Hh")
      as "[Hmshwm_a Hh]".
    iModIntro. iFrame "Hx Hb Hh". iSplit; first done.
    iApply ("Hclose" with "Hmshwmb_a Hmshwm_a").
    iExists (zone ∖ {[x]}). iFrame "Hzone_auth Hzone_cells". iPureIntro.
    intros a Ha. apply elem_of_difference. rewrite /hwm_after in Ha.
    case_decide as Hin.
    - split; first (apply Hzone_cover; lia).
      apply not_elem_of_singleton. intros ->. lia.
    - split; first by apply Hzone_cover.
      apply not_elem_of_singleton. intros ->. by apply Hin.
  Qed.

  (** ** The cells of the zone *)

  (** A zeroed cell joins the zone. *)
  Lemma zone_deposit E a : a ↦ₐ WInt 0 ⊢ |~{E}~> zone_cell a.
  Proof.
    apply si_upd_sys. iIntros (ls) "Hsys Ha".
    iDestruct (sys_interp_hwm_open with "Hsys") as "(Hmshwmb_a & Hmshwm_a & Hzone & Hclose)".
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iDestruct (zone_cells_not_elem with "Hzone_cells Ha") as %Ha.
    iMod (zone_auth_insert with "Hzone_auth") as "[Hzone_auth Htok]"; first done.
    iDestruct "Ha" as "[Ha1 Ha2]".
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a [Hzone_auth Hzone_cells Ha1]").
    { iExists ({[a]} ∪ zone). iFrame "Hzone_auth".
      rewrite big_sepS_insert //. iFrame "Ha1 Hzone_cells".
      iPureIntro. intros a' Ha'. apply elem_of_union_r. by apply Hzone_cover. }
    rewrite ls_set_hwm_hwmb_id zone_cell_unfold. iModIntro. iFrame.
  Qed.

  Lemma zone_deposit_list E (l : list Addr) :
    ([∗ list] a ∈ l, a ↦ₐ WInt 0) ⊢ |~{E}~> [∗ list] a ∈ l, zone_cell a.
  Proof.
    induction l as [|a l IH]; cbn.
    { iIntros "_". by iModIntro. }
    iIntros "[Ha Hl]".
    iApply (si_upd_bind _ (zone_cell a) with "[Ha]"); first by iApply zone_deposit.
    iIntros "Ha". iApply (si_upd_bind with "[Hl]"); first by iApply IH.
    iIntros "Hl". iModIntro. iFrame.
  Qed.

  (** A cell outside [[MSHWMB, MSHWM)] leaves the zone. *)
  Lemma zone_release E (a : Addr) (hb h : Z) :
    ¬ (hb ≤ a < h)%Z →
    zone_cell a -∗
    mshwmb ↦ₜ hb -∗
    mshwm ↦ₜ h -∗
    |~{E}~>
    a ↦ₐ WInt 0 ∗
    mshwmb ↦ₜ hb ∗
    mshwm ↦ₜ h.
  Proof.
    iIntros (Hout) "Hcell Hb Hh".
    iApply (si_upd_sys _ (zone_cell a ∗ mshwmb ↦ₜ hb ∗ mshwm ↦ₜ h)%I
             with "[$Hcell $Hb $Hh]").
    iIntros (ls) "Hsys (Hcell & Hb & Hh)".
    iDestruct (sys_interp_hwm_open with "Hsys") as "(Hmshwmb_a & Hmshwm_a & Hzone & Hclose)".
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
    iDestruct (mshwm_agree with "Hmshwm_a Hh") as %Hh. subst hb h.
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iDestruct (zone_cell_unfold with "Hcell") as "[Htok Ha2]".
    iDestruct (zone_auth_elem with "Hzone_auth Htok") as %Ha.
    iMod (zone_auth_delete with "Hzone_auth Htok") as "Hzone_auth".
    iDestruct (big_sepS_delete with "Hzone_cells") as "[Ha1 Hzone_cells]"; first exact Ha.
    iCombine "Ha1 Ha2" as "Ha".
    iEval (rewrite ?dfrac_op_own ?Qp.half_half) in "Ha".
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a [Hzone_auth Hzone_cells]").
    { iExists (zone ∖ {[a]}). iFrame "Hzone_auth Hzone_cells". iPureIntro.
      intros a' Ha'. apply elem_of_difference. split; first by apply Hzone_cover.
      apply not_elem_of_singleton. intros ->. by apply Hout. }
    rewrite ls_set_hwm_hwmb_id. iModIntro. iFrame.
  Qed.

  Lemma zone_release_list E (l : list Addr) (hb h : Z) :
    (∀ a : Addr, a ∈ l → ¬ (hb ≤ a < h)%Z) →
    ([∗ list] a ∈ l, zone_cell a) -∗
    mshwmb ↦ₜ hb -∗
    mshwm ↦ₜ h -∗
    |~{E}~>
    ([∗ list] a ∈ l, a ↦ₐ WInt 0) ∗
    mshwmb ↦ₜ hb ∗
    mshwm ↦ₜ h.
  Proof.
    induction l as [|a l IH]; cbn; intros Hout.
    { iIntros "_ Hb Hh". iModIntro. iFrame. }
    iIntros "[Ha Hl] Hb Hh".
    iApply (si_upd_bind _ (a ↦ₐ WInt 0 ∗ mshwmb ↦ₜ hb ∗ mshwm ↦ₜ h)%I
             with "[Ha Hb Hh]").
    { iApply (zone_release with "Ha Hb Hh"). apply Hout. by left. }
    iIntros "(Ha & Hb & Hh)".
    iApply (si_upd_bind with "[Hl Hb Hh]").
    { iApply (IH with "Hl Hb Hh"). intros a' Ha'. apply Hout. by right. }
    iIntros "(Hl & Hb & Hh)". iModIntro. iFrame.
  Qed.

  (** A full points-to is outside [[MSHWMB, MSHWM)]: the zone covers that
      range, and holds half of the points-to of each of its cells. *)
  Lemma hwm_pointsto_outside E (a : Addr) w (hb h : Z) :
    a ↦ₐ w -∗
    mshwmb ↦ₜ hb -∗
    mshwm ↦ₜ h -∗
    |~{E}~>
    ⌜¬ (hb ≤ a < h)%Z⌝ ∗
    a ↦ₐ w ∗
    mshwmb ↦ₜ hb ∗
    mshwm ↦ₜ h.
  Proof.
    iIntros "Ha Hb Hh".
    iApply (si_upd_sys _ (a ↦ₐ w ∗ mshwmb ↦ₜ hb ∗ mshwm ↦ₜ h)%I with "[$Ha $Hb $Hh]").
    iIntros (ls) "Hsys (Ha & Hb & Hh)".
    iDestruct (sys_interp_mshwmb_agree with "Hsys Hb") as %<-.
    iDestruct (sys_interp_mshwm_agree with "Hsys Hh") as %<-.
    iDestruct (sys_interp_pointsto_outside with "Hsys Ha") as %Hout.
    iModIntro. iFrame "Hsys Ha Hb Hh". done.
  Qed.

  (** ** Stores to a cell of the zone *)

  (** A store to a cell [x] of the zone: on success the cell leaves the zone
      with a full points-to, and MSHWM is lowered to [x] if [x] is in
      [[MSHWMB, MSHWM)]. *)
  Lemma wp_store_zone_gen Ep pc_p pc_g pc_b pc_e pc_a pc_π
      r1 (r2 : Z + RegName) (imm : Z) w regs (x : Addr) (hb h : Z) dq dw :
    decodeInstrW w.(lw) = Store r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store r1 r2 imm) ⊆ dom regs →
    (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea → ea = x) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        zone_cell x ∗
        ▷ mshwmb ↦ₜ hb ∗
        ▷ mshwm ↦ₜ h ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' mem' retv, RET retv;
        ⌜Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc'
           {[x := lword_of_word (WInt 0)]} mem' ∅ ∅ dw retv⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        mshwmb ↦ₜ hb ∗
        (match retv with
         | NextIV => ([∗ map] a↦v ∈ mem', a ↦ₐ v) ∗ mshwm ↦ₜ hwm_after x hb h
         | _ => zone_cell x ∗ mshwm ↦ₜ h
         end) ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hx φ) "(>HPC & >Hfetch & Hcell & >Hb & >Hh & Hdw & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hfetch Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
    pose proof (er_mmio _ _ _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of, operands_of in Hri.
    odestruct (Hri r1) as [r1v [Hr1l _] ]; first by set_solver+.
    rewrite Hinstr in Hstep.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr1l) as (s1 & Hr1 & Hrel1).
    rewrite /exec /= Hr1 /= in Hstep.
    destruct (lword_of_argument regs r2) as [ storev | ] eqn:HSV.
    2: {
      destruct r2 as [z | r2].
      - cbn in HSV; inversion HSV.
      - destruct (Hri r2) as [r0v [Hr0 _] ]; first by set_solver+.
        cbn in HSV. rewrite Hr0 in HSV. inversion HSV.
    }
    destruct (lword_of_argument_phys _ _ _ _ _ Hregs HSV) as (sv & HSV' & Hrelv).
    rewrite HSV' in Hstep. cbn in Hstep.
    assert (reg_word_ok R C storev) as Hstore_ok by by eapply erasure_lword_of_argument_word.
    destruct (is_cap r1v.(lw)) eqn:Hr1v.
    2: {
      assert ((Faulted, (Cap pc_p pc_g pc_b pc_e pc_a, r, psr, m, st)) = (c, σ')) as Hstep'.
      { unfold is_cap in Hr1v. destruct r1v as [r1v ?]. cbn in *.
        destruct_word r1v; by simplify_pair_eq. }
      instr_fail Hstep'. apply Store_spec_fail. by eapply Store_fail_const.
    }
    destruct r1v as [ [ | [t p g b e a | ] | | ] π1]; try inversion Hr1v. clear Hr1v. cbn in Hstep.
    destruct t.
    2: { rewrite ?andb_false_r in Hstep.
         instr_fail Hstep. apply Store_spec_fail. eapply Store_fail_tag. by rewrite Hr1l. }
    destruct s1.
    2: { (* The physical copy of the destination is untagged. *)
      cbn in Hstep. instr_fail Hstep. apply Store_spec_fail.
      destruct (decide (π1 = deref_id dw)) as [Hπ|Hπ]; last by eapply Store_fail_revoked.
      destruct (a + imm)%a as [ea|] eqn:Hadd.
      2: by eapply Store_fail_addr; [rewrite Hr1l | done].
      destruct (withinBounds b e ea) eqn:Hwb.
      2: by eapply Store_fail_bounds; [rewrite Hr1l | done | right].
      exfalso.
      destruct Hrel1 as [[Heq | [_ [[Hst _] | [Hna [base Hh']]]]] _]; cbn in *; try discriminate.
      { by apply (deref_witness_not_stale R dw (Cap p g b e a @@? π1)). }
      assert (is_heap_address b = true) as Hbh.
      { rewrite /heap_cap_base /= in Hh'. by destruct (is_heap_address b). }
      apply withinBounds_true_iff in Hwb. apply Hna. split; first done. exists b.
      apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
      split; [solve_addr | done]. }
    cbn in Hstep.
    destruct (a + imm)%a as [ea|] eqn:Hadd.
    2: { instr_fail Hstep. apply Store_spec_fail.
           eapply Store_fail_addr; last done. by rewrite Hr1l. }
    cbn in Hstep.
    destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
    2 : {
      apply andb_false_iff in HWA.
      instr_fail Hstep. apply Store_spec_fail. eapply Store_fail_bounds; eauto. by rewrite Hr1l.
    }
    apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).
    assert (Hallow : reg_allows_store_imm regs r1 imm p g b e a ea)
      by (repeat split; auto; by rewrite Hr1l).
    pose proof (Hx _ _ _ _ _ _ Hallow) as Hea. subst ea.
    (* The cell of the zone *)
    iAssert (⌜lmem !! x = Some (lword_of_word (WInt 0))⌝)%I as %Hlmx.
    { iDestruct (zone_cell_unfold with "Hcell") as "[_ Hx2]".
      iApply (gen_heap_valid with "Hm Hx2"). }
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hlmx) as (pwx & Hmx & _).
    rewrite (mem_avoids_mmio_not_shadow _ _ _ Hmmio Hmx)
      (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hmx) Hmx in Hstep.
    rewrite /update_mem /hwm_store /= in Hstep.
    destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
    2: {
      pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
      unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
      instr_fail Hstep. apply Store_spec_fail. by apply Store_fail_invalid_PC. }
    (* The system registers and the zone *)
    iDestruct (zone_cell_unfold with "Hcell") as "[Htok Hx2]".
    iMod (sys_interp_zone_store with "Hsr Htok Hb Hh") as "([%Hhb %Hh] & Hsr & Hx1 & Hb & Hh)".
    subst hb h.
    iCombine "Hx1 Hx2" as "Hxm".
    iEval (rewrite ?dfrac_op_own ?Qp.half_half) in "Hxm".
    (* The erasure *)
    assert (erasure R C (Cap pc_p pc_g pc_b pc_e pc_a, r, hwm_update x psr, m, st)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_hwm lsreg (hwm_after x (ls_hwmb lsreg) (ls_hwm lsreg)))) lmem)
      as Her0.
    { rewrite ls_join_set_hwm /hwm_after. case_decide as Hin.
      - eapply erasure_hwm_update_lower;
          [exact Her | apply ls_join_mshwmb | apply ls_join_mshwm | exact Hin].
      - rewrite insert_id; last apply ls_join_mshwm.
        eapply erasure_hwm_update;
          [exact Her | apply ls_join_mshwmb | apply ls_join_mshwm | exact Hin]. }
    pose proof (erasure_store _ _ _ _ _ _ _ _ _ _ _ x (lstore_word p storev) _ _ Her0 Hlmx
      (reg_phys_mem_word_ok _ _ _ _ (reg_word_ok_lstore_word _ _ p _ Hstore_ok)
         (reg_phys_lstore_word _ p _ _ Hrelv))) as Her1.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
    pose proof Hregs' as Ha'.
    apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
    injection Heq as <- <- <- <- <- <- <-.
    rewrite /nextPC /advancePC /= Ha'1 in Hu. simplify_eq.
    unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
    simplify_pair_eq.
    iMod (gen_heap_update with "Hm Hxm") as "[Hm Hxm]".
    iMod (PC_update _ _ (Cap pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC")
      as "[HPCa HPC]".
    iModIntro. iSplit.
    { iPureIntro. rewrite /sys_kept /mie_st /= !lookup_hwm_update_ne //. }
    iSplitR "Hφ HPC Hpc_a Hb Hh Hxm Hdw Hmap".
    { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
    iApply "Hφ". iFrame "HPC Hpc_a Hb Hdw Hmap".
    iSplit.
    { iPureIntro. eapply Store_spec_success; eauto.
      - by apply mem_avoids_mmio_not_shadow in Hmx.
      - by rewrite lookup_singleton_eq. }
    rewrite insert_singleton_eq big_sepM_singleton. iFrame.
  Qed.

  (** A store to the cell of the zone that holds the instruction itself: the
      fetch uses the cell's half of the points-to. On success the cell leaves
      the zone with a full points-to, and MSHWM is lowered to [pc_a] if
      [pc_a] is in [[MSHWMB, MSHWM)]. *)
  Lemma wp_store_zone_pc_gen Ep pc_p pc_g pc_b pc_e pc_a pc_π
      r1 (r2 : Z + RegName) (imm : Z) w regs (hb h : Z) dw :
    decodeInstrW w.(lw) = Store r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store r1 r2 imm) ⊆ dom regs →
    (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea → ea = pc_a) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{DfracOwn (1/2)} w ∗
        zone_token pc_a ∗
        ▷ mshwmb ↦ₜ hb ∗
        ▷ mshwm ↦ₜ h ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' mem' retv, RET retv;
        ⌜Store_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc'
           {[pc_a := w]} mem' ∅ ∅ dw retv⌝ ∗
        PC ↦ₚ lpc' ∗
        mshwmb ↦ₜ hb ∗
        (match retv with
         | NextIV => ([∗ map] a↦v ∈ mem', a ↦ₐ v) ∗ mshwm ↦ₜ hwm_after pc_a hb h
         | _ => pc_a ↦ₐ{DfracOwn (1/2)} w ∗ zone_token pc_a ∗ mshwm ↦ₜ h
         end) ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hx φ) "(>HPC & >Hfetch & Htok & >Hb & >Hh & Hdw & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hfetch Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
    pose proof (er_mmio _ _ _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of, operands_of in Hri.
    odestruct (Hri r1) as [r1v [Hr1l _] ]; first by set_solver+.
    rewrite Hinstr in Hstep.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr1l) as (s1 & Hr1 & Hrel1).
    rewrite /exec /= Hr1 /= in Hstep.
    destruct (lword_of_argument regs r2) as [ storev | ] eqn:HSV.
    2: {
      destruct r2 as [z | r2].
      - cbn in HSV; inversion HSV.
      - destruct (Hri r2) as [r0v [Hr0 _] ]; first by set_solver+.
        cbn in HSV. rewrite Hr0 in HSV. inversion HSV.
    }
    destruct (lword_of_argument_phys _ _ _ _ _ Hregs HSV) as (sv & HSV' & Hrelv).
    rewrite HSV' in Hstep. cbn in Hstep.
    assert (reg_word_ok R C storev) as Hstore_ok by by eapply erasure_lword_of_argument_word.
    destruct (is_cap r1v.(lw)) eqn:Hr1v.
    2: {
      assert ((Faulted, (Cap pc_p pc_g pc_b pc_e pc_a, r, psr, m, st)) = (c, σ')) as Hstep'.
      { unfold is_cap in Hr1v. destruct r1v as [r1v ?]. cbn in *.
        destruct_word r1v; by simplify_pair_eq. }
      instr_fail Hstep'. apply Store_spec_fail. by eapply Store_fail_const.
    }
    destruct r1v as [ [ | [t p g b e a | ] | | ] π1]; try inversion Hr1v. clear Hr1v. cbn in Hstep.
    destruct t.
    2: { rewrite ?andb_false_r in Hstep.
         instr_fail Hstep. apply Store_spec_fail. eapply Store_fail_tag. by rewrite Hr1l. }
    destruct s1.
    2: { (* The physical copy of the destination is untagged. *)
      cbn in Hstep. instr_fail Hstep. apply Store_spec_fail.
      destruct (decide (π1 = deref_id dw)) as [Hπ|Hπ]; last by eapply Store_fail_revoked.
      destruct (a + imm)%a as [ea|] eqn:Hadd.
      2: by eapply Store_fail_addr; [rewrite Hr1l | done].
      destruct (withinBounds b e ea) eqn:Hwb.
      2: by eapply Store_fail_bounds; [rewrite Hr1l | done | right].
      exfalso.
      destruct Hrel1 as [[Heq | [_ [[Hst _] | [Hna [base Hh']]]]] _]; cbn in *; try discriminate.
      { by apply (deref_witness_not_stale R dw (Cap p g b e a @@? π1)). }
      assert (is_heap_address b = true) as Hbh.
      { rewrite /heap_cap_base /= in Hh'. by destruct (is_heap_address b). }
      apply withinBounds_true_iff in Hwb. apply Hna. split; first done. exists b.
      apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
      split; [solve_addr | done]. }
    cbn in Hstep.
    destruct (a + imm)%a as [ea|] eqn:Hadd.
    2: { instr_fail Hstep. apply Store_spec_fail.
           eapply Store_fail_addr; last done. by rewrite Hr1l. }
    cbn in Hstep.
    destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
    2 : {
      apply andb_false_iff in HWA.
      instr_fail Hstep. apply Store_spec_fail. eapply Store_fail_bounds; eauto. by rewrite Hr1l.
    }
    apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).
    assert (Hallow : reg_allows_store_imm regs r1 imm p g b e a ea)
      by (repeat split; auto; by rewrite Hr1l).
    pose proof (Hx _ _ _ _ _ _ Hallow) as Hea. subst ea.
    (* The cell of the zone *)
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hpc_a) as (pwx & Hmx & _).
    rewrite (mem_avoids_mmio_not_shadow _ _ _ Hmmio Hmx)
      (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hmx) Hmx in Hstep.
    rewrite /update_mem /hwm_store /= in Hstep.
    destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
    2: {
      pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
      unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
      instr_fail Hstep. apply Store_spec_fail. by apply Store_fail_invalid_PC. }
    (* The system registers and the zone *)
    iMod (sys_interp_zone_store with "Hsr Htok Hb Hh") as "([%Hhb %Hh] & Hsr & Hx1 & Hb & Hh)".
    subst hb h.
    iCombine "Hx1 Hpc_a" as "Hxm" gives %[_ <-].
    iEval (rewrite ?dfrac_op_own ?Qp.half_half) in "Hxm".
    (* The erasure *)
    assert (erasure R C (Cap pc_p pc_g pc_b pc_e pc_a, r, hwm_update pc_a psr, m, st)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_hwm lsreg (hwm_after pc_a (ls_hwmb lsreg) (ls_hwm lsreg))))
              lmem) as Her0.
    { rewrite ls_join_set_hwm /hwm_after. case_decide as Hin.
      - eapply erasure_hwm_update_lower;
          [exact Her | apply ls_join_mshwmb | apply ls_join_mshwm | exact Hin].
      - rewrite insert_id; last apply ls_join_mshwm.
        eapply erasure_hwm_update;
          [exact Her | apply ls_join_mshwmb | apply ls_join_mshwm | exact Hin]. }
    pose proof (erasure_store _ _ _ _ _ _ _ _ _ _ _ pc_a (lstore_word p storev) _ _ Her0 Hpc_a
      (reg_phys_mem_word_ok _ _ _ _ (reg_word_ok_lstore_word _ _ p _ Hstore_ok)
         (reg_phys_lstore_word _ p _ _ Hrelv))) as Her1.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
    pose proof Hregs' as Ha'.
    apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
    injection Heq as <- <- <- <- <- <- <-.
    rewrite /nextPC /advancePC /= Ha'1 in Hu. simplify_eq.
    unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
    simplify_pair_eq.
    iMod (gen_heap_update with "Hm Hxm") as "[Hm Hxm]".
    iMod (PC_update _ _ (Cap pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC")
      as "[HPCa HPC]".
    iModIntro. iSplit.
    { iPureIntro. rewrite /sys_kept /mie_st /= !lookup_hwm_update_ne //. }
    iSplitR "Hφ HPC Hb Hh Hxm Hdw Hmap".
    { iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC"). }
    iApply "Hφ". iFrame "HPC Hb Hdw Hmap".
    iSplit.
    { iPureIntro. eapply Store_spec_success; eauto.
      - by apply mem_avoids_mmio_not_shadow in Hmx.
      - by rewrite lookup_singleton_eq. }
    rewrite insert_singleton_eq big_sepM_singleton. iFrame.
  Qed.

  (** A store of an immediate to a cell of the zone, as [zero_stack] does. *)
  Lemma wp_store_zone_z_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
      p g b e a ea (imm : Z) (hb h : Z) dq q :
    is_shadow_address ea = false →
    decodeInstrW w.(lw) = Store dst (inl z) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        zone_cell ea ∗
        ▷ mshwmb ↦ₜ hb ∗
        ▷ mshwm ↦ₜ h ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ WInt z ∗
        mshwmb ↦ₜ hb ∗
        mshwm ↦ₜ hwm_after ea hb h ∗
        deref_res π q }}}.
  Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst φ)
      "(HPC & Hi & >Hdst & Hcell & Hb & Hh & Hdw) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_zone_gen with "[$HPC $Hi $Hcell $Hb $Hh $Hdw $Hmap]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L. set_solver+. }
    { intros p0 g0 b0 e0 a0 ea0 (Hd & Ha' & _).
      rewrite llookup_reg_not_cnull // lookup_singleton_eq /= in Hd. simplify_eq; congruence. }
    iIntros "!>" (lpc' mem' retv) "(%Hspec & HPC & Hi & Hb & Hres & Hdw & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hd & Ha' & _) Hsh0 Hl0 -> _ Hinc0
                      | p0 g0 b0 e0 a0 ea0 ????? (Hd & Ha' & _) Hsh0
                      | _ _ Hfail].
    - rewrite llookup_reg_not_cnull // lookup_singleton_eq /= in Hd. simplify_eq.
      try rewrite Hadd in Ha'. cbn in Harg0. simplify_eq.
      rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hinc0. simplify_eq.
      iSimpl in "Hres". iDestruct "Hres" as "[Hmem Hh]".
      iEval (rewrite insert_singleton_eq big_sepM_singleton
               (lstore_word_canStore _ (lword_of_word (WInt z))
                  (writeAllowed_canStore_int _ _ Hwa))) in "Hmem".
      iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap").
    - by simplify_map_eq.
    - exfalso. eapply (Store_failure_impossible _ _ _ _ _ _ dw p g b e a ea); eauto.
      + by rewrite llookup_reg_not_cnull // lookup_singleton_eq.
      + intros v Hv. rewrite llookup_reg_not_cnull // lookup_singleton_eq in Hv. by simplify_eq.
      + by rewrite lookup_singleton_eq.
      + by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca').
  Qed.

  (** A store of a register to a cell of the zone. *)
  Lemma wp_store_zone_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src wsrc
      p g b e a ea (imm : Z) (hb h : Z) dq q :
    is_shadow_address ea = false →
    decodeInstrW w.(lw) = Store dst (inr src) imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    src ≠ cnull →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ wsrc ∗
        ▷ dst ↦ᵣ Cap p g b e a @@? π ∗
        zone_cell ea ∗
        ▷ mshwmb ↦ₜ hb ∗
        ▷ mshwm ↦ₜ h ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ wsrc ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ lstore_word p wsrc ∗
        mshwmb ↦ₜ hb ∗
        mshwm ↦ₜ hwm_after ea hb h ∗
        deref_res π q }}}.
  Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hsrc Hdst φ)
      "(HPC & Hi & >Hsrc & >Hdst & Hcell & Hb & Hh & Hdw) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hne]".
    iApply (wp_store_zone_gen with "[$HPC $Hi $Hcell $Hb $Hh $Hdw $Hmap]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument !dom_insert_L. set_solver+. }
    { intros p0 g0 b0 e0 a0 ea0 (Hd & Ha' & _).
      rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq /= in Hd.
      simplify_eq; congruence. }
    iIntros "!>" (lpc' mem' retv) "(%Hspec & HPC & Hi & Hb & Hres & Hdw & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 ea0 v0 oldv0 Harg0 (Hd & Ha' & _) Hsh0 Hl0 -> _ Hinc0
                      | p0 g0 b0 e0 a0 ea0 ????? (Hd & Ha' & _) Hsh0
                      | _ _ Hfail].
    - rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq /= in Hd. simplify_eq.
      try rewrite Hadd in Ha'. simplify_eq.
      rewrite /lword_of_argument llookup_reg_not_cnull // lookup_insert_eq in Harg0. simplify_eq.
      rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hinc0. simplify_eq.
      iSimpl in "Hres". iDestruct "Hres" as "[Hmem Hh]".
      iEval (rewrite insert_singleton_eq big_sepM_singleton) in "Hmem".
      iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
      iApply "Hφ". iFrame.
    - by simplify_map_eq.
    - exfalso. eapply (Store_failure_impossible _ _ _ _ _ _ dw p g b e a ea); eauto.
      + by rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq.
      + intros v Hv. rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq in Hv.
        by simplify_eq.
      + by rewrite lookup_singleton_eq.
      + by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca').
  Qed.


  (** ** Accesses to MSHWM and MSHWMB *)

  (** [csrr dst, mshwm]: reads the integer [h] of MSHWM. *)
  Lemma wp_csrr_mshwm E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst (h : Z) dq :
    decodeInstrW w.(lw) = SpecialRW dst mshwm (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ mshwm ↦ₜ h }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WInt h ∗
        mshwm ↦ₜ h }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst φ) "(>HPC & >Hpc_a & >Hdst & >Hh) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mshwm_agree with "Hsr Hh") as %<-.
    pose proof (ls_join_mshwm lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & Hrel).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    destruct (decide (dst = cnull)) as [Hc|_]; first done. cbn in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst
      (lword_of_word (WInt (ls_hwm lsreg))) wold _ _ _
      (λ lpc' regs' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
         regs' = <[dst := lword_of_word (WInt (ls_hwm lsreg))]ₗ> {[dst := wdst]} ∧
         retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hh]").
    { exact Her. } { exact Hlregs. } { right. set_solver. } { exact Hok. } { exact Hstep. }
    { exact Hrel. }
    { intros lpc' Hi. rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. by simplify_eq. }
    { intros Hi. by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. }
    iIntros (lpc' regs' retv (-> & -> & ->)) "HPC Hmap".
    rewrite linsert_reg_not_cnull // insert_singleton_eq.
    iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [csrr dst, mshwmb]: reads the integer [hb] of MSHWMB. *)
  Lemma wp_csrr_mshwmb E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst (hb : Z) dq :
    decodeInstrW w.(lw) = SpecialRW dst mshwmb (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ mshwmb ↦ₜ hb }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WInt hb ∗
        mshwmb ↦ₜ hb }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst φ) "(>HPC & >Hpc_a & >Hdst & >Hb) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mshwmb_agree with "Hsr Hb") as %<-.
    pose proof (ls_join_mshwmb lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & Hrel).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    destruct (decide (dst = cnull)) as [Hc|_]; first done. cbn in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst
      (lword_of_word (WInt (ls_hwmb lsreg))) wold _ _ _
      (λ lpc' regs' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
         regs' = <[dst := lword_of_word (WInt (ls_hwmb lsreg))]ₗ> {[dst := wdst]} ∧
         retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb]").
    { exact Her. } { exact Hlregs. } { right. set_solver. } { exact Hok. } { exact Hstep. }
    { exact Hrel. }
    { intros lpc' Hi. rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. by simplify_eq. }
    { intros Hi. by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. }
    iIntros (lpc' regs' retv (-> & -> & ->)) "HPC Hmap".
    rewrite linsert_reg_not_cnull // insert_singleton_eq.
    iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [csrw mshwm, src] writing [x]: the zone covers [[MSHWMB, x)], with the
      cells of [l] above MSHWM. *)
  #[local] Lemma wp_csrw_mshwm_cells E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc
      (hb h : Z) (l : list Addr) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    (∀ a : Addr, (hb ≤ a < get_a vsrc.(lw))%Z → (a < h)%Z ∨ a ∈ l) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ hb ∗
        ▷ mshwm ↦ₜ h ∗
        ([∗ list] a ∈ l, zone_cell a) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ hb ∗
        mshwm ↦ₜ get_a vsrc.(lw) ∗
        ([∗ list] a ∈ l, zone_cell a) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hcover φ)
      "(>HPC & >Hpc_a & >Hsrc & >Hb & >Hh & Hcells) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_hwm_open with "Hsr") as "(Hmshwmb_a & Hmshwm_a & Hzone & Hclose)".
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
    iDestruct (mshwm_agree with "Hmshwm_a Hh") as %Hh. subst hb h.
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iAssert (⌜∀ a : Addr, a ∈ l → a ∈ zone⌝)%I as %Hcells.
    { iIntros (a Ha). iDestruct (big_sepL_elem_of with "Hcells") as "Hcell"; first exact Ha.
      iDestruct (zone_cell_unfold with "Hcell") as "[Htok _]".
      iApply (zone_auth_elem with "Hzone_auth Htok"). }
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her (ls_join_mshwm lsreg)) as Hph.
    cbn in Hph.
    assert (({[src := vsrc]} : LReg) !!ₗ src = Some vsrc) as Hv.
    { rewrite llookup_reg_not_cnull //. by rewrite lookup_singleton_eq. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep.
    rewrite Hxsr Hph /= in Hstep.
    repeat (case_decide; try congruence).
    rewrite Hrs /= get_a_and_tag in Hstep.
    set (x := get_a vsrc.(lw)) in *.
    assert (erasure R C (Cap pc_p pc_g pc_b pc_e pc_a, r, <[mshwm := WInt x]> psr, m, st)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_hwm (ls_set_hwmb lsreg (ls_hwmb lsreg)) x)) lmem) as Her1.
    { rewrite ls_join_set_hwm ls_join_set_hwmb (insert_id (ls_join lsreg) mshwmb);
        last apply ls_join_mshwmb.
      apply erasure_insert_sreg; [done | apply reg_word_ok_int | by intros | done |].
      apply reg_phys_lword_of_word. }
    iMod (mshwm_update _ _ x with "Hmshwm_a Hh") as "[Hmshwm_a Hh]".
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a [Hzone_auth Hzone_cells]").
    { iExists zone. iFrame "Hzone_auth Hzone_cells". iPureIntro.
      intros a Ha. destruct (Hcover a Ha) as [Hlt | Hal].
      - apply Hzone_cover. lia.
      - by apply Hcells. }
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
    iApply (instr_close_kept_trans _ _ _ _
              (sys_kept_insert_sreg _ _ _ _ _ mshwm (WInt x) ltac:(done) ltac:(done))).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hclose Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb Hh Hcells]").
    { exact Her1. }
    { rewrite /nextPC in Hu Hstep. rewrite /update_sreg /= in Hstep.
      by rewrite Hu in Hstep |- *. }
    { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
    { intros Hi'. rewrite /incrementPC in Hi. congruence. }
    iIntros (lpc'' retv [-> ->]) "HPC Hmap". iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [csrw mshwm, src]: the new value is between MSHWMB and MSHWM. *)
  Lemma wp_csrw_mshwm E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc (hb h : Z) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    (hb ≤ get_a vsrc.(lw) ≤ h)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ hb ∗
        ▷ mshwm ↦ₜ h }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ hb ∗
        mshwm ↦ₜ get_a vsrc.(lw) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hle φ) "(HPC & Hpc_a & Hsrc & Hb & Hh) Hφ".
    iApply (wp_csrw_mshwm_cells _ _ _ _ _ _ _ _ _ _ _ hb h []
             with "[$HPC $Hpc_a $Hsrc $Hb $Hh]"); try done.
    { intros a Ha. left. lia. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & Hb & Hh & _)". iApply "Hφ". iFrame.
  Qed.

  (** [csrw mshwm, src] with a value below MSHWMB: the zone needs to cover
      nothing. *)
  Lemma wp_csrw_mshwm_below E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc (hb h : Z) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    (get_a vsrc.(lw) < hb)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ hb ∗
        ▷ mshwm ↦ₜ h }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ hb ∗
        mshwm ↦ₜ get_a vsrc.(lw) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hlt φ) "(HPC & Hpc_a & Hsrc & Hb & Hh) Hφ".
    iApply (wp_csrw_mshwm_cells _ _ _ _ _ _ _ _ _ _ _ hb h []
             with "[$HPC $Hpc_a $Hsrc $Hb $Hh]"); try done.
    { intros a Ha. lia. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & Hb & Hh & _)". iApply "Hφ". iFrame.
  Qed.

  (** [csrw mshwm, src] raising MSHWM to [x], at least [lo], the larger of
      MSHWMB and MSHWM: the cells of [[lo, x)] join the cover. *)
  Lemma wp_csrw_mshwm_raise E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc
      (hb h : Z) (lo x : Addr) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = x →
    (Z.max hb h = lo)%Z →
    (lo ≤ x)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ hb ∗
        ▷ mshwm ↦ₜ h ∗
        ([∗ list] a ∈ finz.seq_between lo x, zone_cell a) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ hb ∗
        mshwm ↦ₜ x ∗
        ([∗ list] a ∈ finz.seq_between lo x, zone_cell a) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hx Hlo Hle φ)
      "(HPC & Hpc_a & Hsrc & Hb & Hh & Hcells) Hφ".
    iApply (wp_csrw_mshwm_cells _ _ _ _ _ _ _ _ _ _ _ hb h (finz.seq_between lo x)
             with "[$HPC $Hpc_a $Hsrc $Hb $Hh $Hcells]"); try done.
    { intros a Ha. rewrite Hx in Ha. destruct (decide (a < h)%Z) as [Hlt|Hge]; first by left.
      right. apply elem_of_finz_seq_between. solve_addr. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & Hb & Hh & Hcells)". rewrite Hx.
    iApply "Hφ". iFrame.
  Qed.

  (** [csrw mshwmb, src]: MSHWMB is lowered to [lo], with the cells of
      [[lo, hb)]. *)
  Lemma wp_csrw_mshwmb E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc (lo hb : Addr) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwmb (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = lo →
    (lo ≤ hb)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ hb ∗
        ([∗ list] a ∈ finz.seq_between lo hb, zone_cell a) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ lo ∗
        ([∗ list] a ∈ finz.seq_between lo hb, zone_cell a) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hlo Hle φ)
      "(>HPC & >Hpc_a & >Hsrc & >Hb & Hcells) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_hwm_open with "Hsr") as "(Hmshwmb_a & Hmshwm_a & Hzone & Hclose)".
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iAssert (⌜∀ a : Addr, a ∈ finz.seq_between lo hb → a ∈ zone⌝)%I as %Hcells.
    { iIntros (a Ha). iDestruct (big_sepL_elem_of with "Hcells") as "Hcell"; first exact Ha.
      iDestruct (zone_cell_unfold with "Hcell") as "[Htok _]".
      iApply (zone_auth_elem with "Hzone_auth Htok"). }
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her (ls_join_mshwmb lsreg)) as Hpb.
    cbn in Hpb.
    assert (({[src := vsrc]} : LReg) !!ₗ src = Some vsrc) as Hv.
    { rewrite llookup_reg_not_cnull //. by rewrite lookup_singleton_eq. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep.
    rewrite Hxsr Hpb /= in Hstep.
    repeat (case_decide; try congruence).
    rewrite Hrs /= get_a_and_tag Hlo in Hstep.
    assert (erasure R C (Cap pc_p pc_g pc_b pc_e pc_a, r, <[mshwmb := WInt lo]> psr, m, st)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_hwm (ls_set_hwmb lsreg lo) (ls_hwm lsreg))) lmem) as Her1.
    { rewrite ls_join_set_hwm ls_join_set_hwmb insert_id;
        last by rewrite lookup_insert_ne // ls_join_mshwm.
      apply erasure_insert_sreg; [done | apply reg_word_ok_int | by intros | done |].
      apply reg_phys_lword_of_word. }
    iMod (mshwmb_update _ _ lo with "Hmshwmb_a Hb") as "[Hmshwmb_a Hb]".
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a [Hzone_auth Hzone_cells]").
    { iExists zone. iFrame "Hzone_auth Hzone_cells". iPureIntro.
      intros a Ha. destruct (decide (a < hb)%Z) as [Hlt|Hge].
      - apply Hcells. apply elem_of_finz_seq_between. solve_addr.
      - apply Hzone_cover. lia. }
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
    iApply (instr_close_kept_trans _ _ _ _
              (sys_kept_insert_sreg _ _ _ _ _ mshwmb (WInt lo) ltac:(done) ltac:(done))).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hclose Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb Hcells]").
    { exact Her1. }
    { rewrite /nextPC in Hu Hstep. rewrite /update_sreg /= in Hstep.
      by rewrite Hu in Hstep |- *. }
    { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
    { intros Hi'. rewrite /incrementPC in Hi. congruence. }
    iIntros (lpc'' retv [-> ->]) "HPC Hmap". iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

End hwm.
