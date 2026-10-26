From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base rules_Store rules_SpecialRW si_modality.

(** * The stack high-water mark

    The rules for MSHWM and MSHWMB, and for the zone of zeroed cells that the
    state interpretation couples to them: the zone covers [[MSHWMB, MSHWM)]
    of the logical values, and the physical MSHWM is between MSHWMB and the
    logical MSHWM. A cell of the zone ([zone_cell]) holds half of its
    points-to, so the load rules read it. *)

(** The logical MSHWM after a store at [x] to a cell of the zone: [x] if it
    is in [[hb, h)], [h] otherwise. *)
Definition hwm_after (x : Addr) (vb vh : LWord) : LWord :=
  if decide (get_a vb.(lw) ≤ x < get_a vh.(lw))%Z then lword_of_word (WInt x) else vh.

Section hwm.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types w : LWord.

  (** ** The cells of the zone *)

  (** A full points-to is not in the zone. *)
  Lemma zone_cells_not_elem (zone : gset Addr) a w :
    ([∗ set] a' ∈ zone, a' ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt 0)) -∗
    a ↦ₐ w -∗
    ⌜a ∉ zone⌝.
  Proof.
    iIntros "Hcells Ha". destruct (decide (a ∈ zone)) as [Ha|Ha]; last done.
    iDestruct (big_sepS_elem_of with "Hcells") as "Ha'"; first exact Ha.
    iDestruct (pointsto_valid_2 with "Ha Ha'") as %[Hv _].
    iPureIntro. rewrite dfrac_op_own dfrac_valid_own in Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.

  (** A zeroed cell joins the zone. *)
  Lemma zone_deposit E a : a ↦ₐ WInt 0 ⊢ |~{E}~> zone_cell a.
  Proof.
    apply si_upd_ghost. iIntros (σ) "Hσ Ha". iNamed "Hσ".
    iDestruct "Hsr" as "(Hsr & Hres & Hzone)". iNamed "Hzone".
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iDestruct (zone_cells_not_elem with "Hzone_cells Ha") as %Ha.
    iMod (zone_auth_insert with "Hzone_auth") as "[Hzone_auth Htok]"; first done.
    iDestruct "Ha" as "[Ha1 Ha2]".
    iModIntro. iSplitR "Htok Ha2"; last (rewrite zone_cell_unfold; iFrame).
    iExists lpc, lreg, lsreg, lmem, R, C. iFrame "HPCa Hr Hm Hst HR HC".
    iSplitL; last (iPureIntro; exact Her).
    rewrite /sreg_interp /hwm_zone. iFrame "Hsr Hres".
    iExists ({[a]} ∪ zone), vmshwmb, vmshwm. iFrame "Hzone_auth".
    rewrite big_sepS_insert //. iFrame "Ha1 Hzone_cells".
    iPureIntro. split_and!; [done | done |].
    intros a' Ha'. apply elem_of_union_r. by apply Hzone_cover.
  Qed.

  Lemma si_upd_bind E P Q : (|~{E}~> P) -∗ (P -∗ |~{E}~> Q) -∗ |~{E}~> Q.
  Proof.
    iIntros "HP HPQ". iApply si_upd_trans.
    assert (P ∗ (P -∗ |~{E}~> Q) ⊢ |~{E}~> Q) as HPQ'.
    { iIntros "[HP HPQ]". iApply ("HPQ" with "HP"). }
    iApply (si_upd_mono _ _ _ HPQ'). iApply si_upd_frame_r. iFrame.
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
  Lemma zone_release E (a : Addr) vb vh dqb dqh :
    ¬ (get_a vb.(lw) ≤ a < get_a vh.(lw))%Z →
    zone_cell a -∗
    MSHWMB ↦ₛᵣ{dqb} vb -∗
    MSHWM ↦ₛᵣ{dqh} vh -∗
    |~{E}~>
    a ↦ₐ WInt 0 ∗
    MSHWMB ↦ₛᵣ{dqb} vb ∗
    MSHWM ↦ₛᵣ{dqh} vh.
  Proof.
    iIntros (Hout) "Hcell Hb Hh".
    iApply (si_upd_ghost _ (zone_cell a ∗ MSHWMB ↦ₛᵣ{dqb} vb ∗ MSHWM ↦ₛᵣ{dqh} vh)%I
             with "[$Hcell $Hb $Hh]").
    iIntros (σ) "Hσ (Hcell & Hb & Hh)". iNamed "Hσ".
    iDestruct "Hsr" as "(Hsr & Hres & Hzone)". iNamed "Hzone".
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iDestruct (gen_heap_valid with "Hsr Hb") as %Hb'.
    iDestruct (gen_heap_valid with "Hsr Hh") as %Hh'.
    rewrite Hmshwmb in Hb'. injection Hb' as ->.
    rewrite Hmshwm in Hh'. injection Hh' as ->.
    iDestruct (zone_cell_unfold with "Hcell") as "[Htok Ha2]".
    iDestruct (zone_auth_elem with "Hzone_auth Htok") as %Ha.
    iMod (zone_auth_delete with "Hzone_auth Htok") as "Hzone_auth".
    iDestruct (big_sepS_delete with "Hzone_cells") as "[Ha1 Hzone_cells]"; first exact Ha.
    iCombine "Ha1 Ha2" as "Ha".
    iEval (rewrite ?dfrac_op_own ?Qp.half_half) in "Ha".
    iModIntro. iSplitR "Ha Hb Hh"; last iFrame.
    iExists lpc, lreg, lsreg, lmem, R, C. iFrame "HPCa Hr Hm Hst HR HC".
    iSplitL; last (iPureIntro; exact Her).
    rewrite /sreg_interp /hwm_zone. iFrame "Hsr Hres".
    iExists (zone ∖ {[a]}), vb, vh. iFrame "Hzone_auth Hzone_cells".
    iPureIntro. split_and!; [done | done |].
    intros a' Ha'. apply elem_of_difference. split; first by apply Hzone_cover.
    apply not_elem_of_singleton. intros ->. by apply Hout.
  Qed.

  Lemma zone_release_list E (l : list Addr) vb vh dqb dqh :
    (∀ a : Addr, a ∈ l → ¬ (get_a vb.(lw) ≤ a < get_a vh.(lw))%Z) →
    ([∗ list] a ∈ l, zone_cell a) -∗
    MSHWMB ↦ₛᵣ{dqb} vb -∗
    MSHWM ↦ₛᵣ{dqh} vh -∗
    |~{E}~>
    ([∗ list] a ∈ l, a ↦ₐ WInt 0) ∗
    MSHWMB ↦ₛᵣ{dqb} vb ∗
    MSHWM ↦ₛᵣ{dqh} vh.
  Proof.
    induction l as [|a l IH]; cbn; intros Hout.
    { iIntros "_ Hb Hh". iModIntro. iFrame. }
    iIntros "[Ha Hl] Hb Hh".
    iApply (si_upd_bind _ (a ↦ₐ WInt 0 ∗ MSHWMB ↦ₛᵣ{dqb} vb ∗ MSHWM ↦ₛᵣ{dqh} vh)%I
             with "[Ha Hb Hh]").
    { iApply (zone_release with "Ha Hb Hh"). apply Hout. by left. }
    iIntros "(Ha & Hb & Hh)".
    iApply (si_upd_bind with "[Hl Hb Hh]").
    { iApply (IH with "Hl Hb Hh"). intros a' Ha'. apply Hout. by right. }
    iIntros "(Hl & Hb & Hh)". iModIntro. iFrame.
  Qed.

  (** The logical MSHWM rises to [x], with the cells of [[lo, x)], [lo] at most
      the logical MSHWM. *)
  Lemma hwm_raise E vb vh (lo x : Addr) dqb :
    (lo ≤ get_a vh.(lw) ≤ x)%Z →
    MSHWMB ↦ₛᵣ{dqb} vb -∗
    MSHWM ↦ₛᵣ vh -∗
    ([∗ list] a ∈ finz.seq_between lo x, zone_cell a) -∗
    |~{E}~>
    MSHWMB ↦ₛᵣ{dqb} vb ∗
    MSHWM ↦ₛᵣ WInt x ∗
    ([∗ list] a ∈ finz.seq_between lo x, zone_cell a).
  Proof.
    iIntros (Hle) "Hb Hh Hcells".
    iApply (si_upd_ghost _ (MSHWMB ↦ₛᵣ{dqb} vb ∗ MSHWM ↦ₛᵣ vh ∗
                            [∗ list] a ∈ finz.seq_between lo x, zone_cell a)%I
             with "[$Hb $Hh $Hcells]").
    iIntros (σ) "Hσ (Hb & Hh & Hcells)". iNamed "Hσ".
    iDestruct "Hsr" as "(Hsr & Hres & Hzone)". iNamed "Hzone".
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iDestruct (gen_heap_valid with "Hsr Hb") as %Hb'.
    iDestruct (gen_heap_valid with "Hsr Hh") as %Hh'.
    rewrite Hmshwmb in Hb'. injection Hb' as ->.
    rewrite Hmshwm in Hh'. injection Hh' as ->.
    iAssert (⌜∀ a : Addr, a ∈ finz.seq_between lo x → a ∈ zone⌝)%I as %Hcells.
    { iIntros (a Ha). iDestruct (big_sepL_elem_of with "Hcells") as "Hcell"; first exact Ha.
      iDestruct (zone_cell_unfold with "Hcell") as "[Htok _]".
      iApply (zone_auth_elem with "Hzone_auth Htok"). }
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt x)) with "Hsr Hh") as "[Hsr Hh]".
    iModIntro. iFrame "Hb Hh Hcells".
    iExists lpc, lreg, (<[MSHWM := lword_of_word (WInt x)]> lsreg), lmem, R, C.
    iFrame "HPCa Hr Hm Hst HR HC". iSplitL.
    - rewrite /sreg_interp /hwm_zone. iFrame "Hsr Hres".
      iExists zone, vb, (lword_of_word (WInt x)). iFrame "Hzone_auth Hzone_cells".
      iPureIntro. split_and!; [by rewrite lookup_insert_ne | by rewrite lookup_insert_eq |].
      intros a Ha. cbn in Ha. destruct (decide (a < get_a vh.(lw))%Z) as [Hlt|Hge].
      + apply Hzone_cover. lia.
      + apply Hcells. apply elem_of_finz_seq_between. solve_addr.
    - iPureIntro. apply erasure_insert_lmshwm; [done | apply reg_word_ok_int | done |].
      intros vb' vh' Hvb' Hvh'. rewrite lookup_insert_ne // Hmshwmb in Hvb'.
      rewrite lookup_insert_eq in Hvh'. simplify_eq.
      destruct (erasure_hwm _ _ _ _ _ _ _ _ _ Her Hmshwmb Hmshwm)
        as (wb & z & _ & _ & Hz & Hz_le).
      exists z. split; first done. cbn. lia.
  Qed.

  (** ** Stores to a cell of the zone *)

  (** A store to a cell [x] of the zone: on success the cell leaves the zone
      with a full points-to, and the logical MSHWM is lowered to [x] if [x] is
      in [[MSHWMB, MSHWM)]. *)
  Lemma wp_store_zone_gen Ep pc_p pc_g pc_b pc_e pc_a pc_π
      r1 (r2 : Z + RegName) (imm : Z) w regs (x : Addr) vb vh dq dw :
    decodeInstrW w.(lw) = Store r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store r1 r2 imm) ⊆ dom regs →
    (∀ p g b e a ea, reg_allows_store_imm regs r1 imm p g b e a ea → ea = x) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        zone_cell x ∗
        ▷ MSHWMB ↦ₛᵣ vb ∗
        ▷ MSHWM ↦ₛᵣ vh ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' mem' retv, RET retv;
        ⌜Store_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc'
           {[x := lword_of_word (WInt 0)]} mem' ∅ ∅ dw retv⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        MSHWMB ↦ₛᵣ vb ∗
        (match retv with
         | NextIV => ([∗ map] a↦v ∈ mem', a ↦ₐ v) ∗ MSHWM ↦ₛᵣ hwm_after x vb vh
         | _ => zone_cell x ∗ MSHWM ↦ₛᵣ vh
         end) ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hx φ) "(>HPC & >Hfetch & Hcell & >Hb & >Hh & Hdw & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "Hσ /=".
    destruct σ1 as [ [ [ [pc r] sr] m] st]; cbn.
    iNamed "Hσ".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    pose proof (erasure_pc_correct _ _ _ _ _ _ _ Her Hvpc) as Hpc. cbn in Hpc. subst pc.
    iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
    iEval (rewrite /sreg /shadowtbl /=) in "Hsr Hst".
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hlregs.
    pose proof (erasure_regs_incl _ _ _ _ _ _ _ _ Her Hlregs) as Hregs.
    pose proof (er_mmio _ _ _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of, operands_of in Hri.
    odestruct (Hri r1) as [r1v [Hr1l _] ]; first by set_solver+.
    iDestruct (gen_heap_valid with "Hm Hfetch") as %Hlmem_pc.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hlmem_pc) as (pw & Hpw & Hpwok).
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite (mem_word_ok_decode _ _ _ _ Hpwok) Hinstr in Hstep.
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
      assert ((Faulted, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) = (c, σ2)) as Hstep'.
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
      { by apply (deref_witness_not_stale R dw (WCap true p g b e a @@? π1)). }
      assert (is_heap_address b = true) as Hbh.
      { rewrite /heap_cap_base /= in Hh'. by destruct (is_heap_address b). }
      apply withinBounds_true_iff in Hwb. apply Hna. split; first done. exists b.
      apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
      split; [solve_addr | done]. }
    cbn in Hstep.
    destruct (a + imm)%a as [ea|] eqn:Hadd.
    2: { instr_fail Hstep. apply Store_spec_fail. eapply Store_fail_addr; last done. by rewrite Hr1l. }
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
    iDestruct (zone_cell_unfold with "Hcell") as "[Htok Hx2]".
    iDestruct (gen_heap_valid with "Hm Hx2") as %Hlmx.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hlmx) as (pwx & Hmx & _).
    rewrite (mem_avoids_mmio_not_shadow _ _ _ Hmmio Hmx)
      (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hmx) Hmx in Hstep.
    rewrite /update_mem /hwm_store /= in Hstep.
    destruct (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hregs'.
    2: {
      pose proof Hregs' as Ha'. eapply incrementPC_None_inv in Ha'; [|reflexivity].
      unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha' in Hstep.
      iAssert (zone_cell x) with "[Htok Hx2]" as "Hcell"; first (rewrite zone_cell_unfold; iFrame).
      instr_fail Hstep. apply Store_spec_fail. by apply Store_fail_invalid_PC. }
    (* The system registers and the zone *)
    iDestruct "Hsr" as "(Hsr & Hres & Hzone)". iNamed "Hzone".
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iDestruct (gen_heap_valid with "Hsr Hb") as %Hb'.
    iDestruct (gen_heap_valid with "Hsr Hh") as %Hh'.
    rewrite Hmshwmb in Hb'. injection Hb' as ->.
    rewrite Hmshwm in Hh'. injection Hh' as ->.
    iDestruct (zone_auth_elem with "Hzone_auth Htok") as %Hxz.
    iMod (zone_auth_delete with "Hzone_auth Htok") as "Hzone_auth".
    iDestruct (big_sepS_delete with "Hzone_cells") as "[Hx1 Hzone_cells]"; first exact Hxz.
    iCombine "Hx1 Hx2" as "Hxm".
    iEval (rewrite ?dfrac_op_own ?Qp.half_half) in "Hxm".
    (* The erasure *)
    assert (erasure R C (WCap true pc_p pc_g pc_b pc_e pc_a, r, hwm_update x sr, m, st)
              (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (<[MSHWM := hwm_after x vb vh]> lsreg) lmem) as Her0.
    { rewrite /hwm_after. case_decide as Hin.
      - eapply erasure_hwm_update_lower; [exact Her | exact Hmshwmb | exact Hmshwm | exact Hin].
      - rewrite insert_id //. by apply erasure_hwm_update. }
    pose proof (erasure_store _ _ _ _ _ _ _ _ _ _ _ x (lstore_word p storev) _ _ Her0 Hlmx
      (reg_phys_mem_word_ok _ _ _ _ (reg_word_ok_lstore_word _ _ p _ Hstore_ok)
         (reg_phys_lstore_word _ p _ _ Hrelv))) as Her1.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hregs') as (pc'' & Hu & Her2).
    pose proof Hregs' as Ha'.
    apply incrementPC_Some_inv in Ha' as (t' & p' & g' & b' & e' & a' & a'1 & π' & Heq & Ha'1 & ->).
    injection Heq as <- <- <- <- <- <- <-.
    rewrite /nextPC /advancePC /= Ha'1 in Hu. simplify_eq.
    unfold nextPC, advancePC in Hstep; cbn in Hstep; rewrite Ha'1 in Hstep.
    simplify_pair_eq. cbn.
    iMod (gen_heap_update with "Hm Hxm") as "[Hm Hxm]".
    iMod (gen_heap_update _ _ _ (hwm_after x vb vh) with "Hsr Hh") as "[Hsr Hh]".
    iMod (PC_update _ _ (WCap true pc_p pc_g pc_b pc_e a'1 @@? pc_π) with "HPCa HPC")
      as "[HPCa HPC]".
    iModIntro. iSplitR "Hφ HPC Hfetch Hb Hh Hxm Hdw Hmap".
    { iExists _, _, (<[MSHWM := hwm_after x vb vh]> lsreg), _, R, C.
      iFrame "HPCa Hr Hm Hst HR HC". iSplitL; last (iPureIntro; exact Her2).
      rewrite /sreg_interp /hwm_zone. iFrame "Hsr Hres".
      iExists (zone ∖ {[x]}), vb, (hwm_after x vb vh). iFrame "Hzone_auth Hzone_cells".
      iPureIntro. split_and!; [by rewrite lookup_insert_ne | by rewrite lookup_insert_eq |].
      intros a'' Ha''. apply elem_of_difference. rewrite /hwm_after in Ha''.
      case_decide as Hin; cbn in Ha''.
      - split; first (apply Hzone_cover; lia).
        apply not_elem_of_singleton. intros ->. lia.
      - split; first by apply Hzone_cover.
        apply not_elem_of_singleton. intros ->. by apply Hin. }
    iApply "Hφ". iFrame "HPC Hfetch Hb Hdw Hmap".
    iSplit.
    { iPureIntro. eapply Store_spec_success; eauto.
      - by apply mem_avoids_mmio_not_shadow in Hmx.
      - by rewrite lookup_singleton_eq. }
    rewrite insert_singleton_eq big_sepM_singleton. iFrame.
  Qed.

  (** A store of an immediate to a cell of the zone, as [zero_stack] does. *)
  Lemma wp_store_zone_z_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
      p g b e a ea (imm : Z) vb vh dq q :
    is_shadow_address ea = false →
    decodeInstrW w.(lw) = Store dst (inl z) imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    writeAllowed p = true → withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ WCap true p g b e a @@? π ∗
        zone_cell ea ∗
        ▷ MSHWMB ↦ₛᵣ vb ∗
        ▷ MSHWM ↦ₛᵣ vh ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WCap true p g b e a @@? π ∗
        ea ↦ₐ WInt z ∗
        MSHWMB ↦ₛᵣ vb ∗
        MSHWM ↦ₛᵣ hwm_after ea vb vh ∗
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

  (** ** Accesses to MSHWM and MSHWMB *)

  (** [csrr dst, mshwm]: the physical value [v], between MSHWMB and the
      logical MSHWM, which becomes the logical MSHWM. *)
  Lemma wp_csrr_mshwm E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst vb vh dq :
    decodeInstrW w.(lw) = SpecialRW dst MSHWM (inr cnull) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ MSHWMB ↦ₛᵣ vb ∗
        ▷ MSHWM ↦ₛᵣ vh }}}
      Instr Executable @ E
    {{{ (v : Z), RET NextIV;
        ⌜(get_a vb.(lw) ≤ v ≤ get_a vh.(lw))%Z⌝ ∗
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WInt v ∗
        MSHWMB ↦ₛᵣ vb ∗
        MSHWM ↦ₛᵣ WInt v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst φ) "(>HPC & >Hpc_a & >Hdst & >Hb & >Hh) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct "Hsr" as "(Hsr & Hres & Hzone)".
    iDestruct (gen_heap_valid with "Hsr Hb") as %Hb'.
    iDestruct (gen_heap_valid with "Hsr Hh") as %Hh'.
    destruct (erasure_hwm _ _ _ _ _ _ _ _ _ Her Hb' Hh') as (wb & z & Hwb & Hab & Hz & Hle).
    rewrite Hinstr /exec in Hstep. cbn in Hstep.
    rewrite Hxsr Hz /= in Hstep.
    repeat (case_decide; try congruence).
    (* The logical MSHWM becomes the physical value. *)
    assert (erasure R C (WCap true pc_p pc_g pc_b pc_e pc_a, r, psr, m, st)
              (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (<[MSHWM := lword_of_word (WInt z)]> lsreg) lmem) as Her1.
    { apply erasure_insert_lmshwm; [done | apply reg_word_ok_int | done |].
      intros vb' vh' Hvb' Hvh'. rewrite lookup_insert_ne // Hb' in Hvb'.
      rewrite lookup_insert_eq in Hvh'. simplify_eq.
      exists z. split; first done. cbn. lia. }
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt z)) with "Hsr Hh") as "[Hsr Hh]".
    iAssert (sreg_interp (<[MSHWM := lword_of_word (WInt z)]> lsreg))
      with "[Hsr Hres Hzone]" as "Hsr".
    { iNamed "Hzone". iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
      rewrite /sreg_interp /hwm_zone. iFrame "Hsr Hres".
      rewrite Hmshwmb in Hb'. injection Hb' as ->.
      rewrite Hmshwm in Hh'. injection Hh' as ->.
      iExists zone, vb, (lword_of_word (WInt z)). iFrame "Hzone_auth Hzone_cells".
      iPureIntro. split_and!; [by rewrite lookup_insert_ne | by rewrite lookup_insert_eq |].
      intros a Ha. apply Hzone_cover. cbn in Ha. lia. }
    assert (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _
      (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt z)) (WInt z) Her1
         (reg_word_ok_int _ _ _ _) (reg_phys_int _ _ _)) Hi)
      as (pc' & Hu & _).
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ dst (lword_of_word (WInt z)) (WInt z)
      _ _ _
      (λ lpc' regs' retv, lpc' = WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
                          regs' = <[dst := lword_of_word (WInt z)]> {[dst := wdst]} ∧
                          retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb Hh]").
    { exact Her1. } { exact Hlregs. }
    { right. by rewrite dom_singleton_L elem_of_singleton. }
    { apply reg_word_ok_int. }
    { rewrite /update_reg /= in Hu Hstep |- *. rewrite Hu in Hstep |- *.
      done. }
    { apply reg_phys_int. }
    { intros lpc'' Hi'. rewrite Hi in Hi'. simplify_eq. by rewrite linsert_reg_not_cnull. }
    { intros Hi'. congruence. }
    iIntros (lpc'' regs'' retv (-> & -> & ->)) "HPC Hmap".
    rewrite insert_singleton_eq. iDestruct (regs_of_map_1 with "Hmap") as "Hdst".
    iApply ("Hφ" $! z). iFrame. iPureIntro. lia.
  Qed.

  (** [csrw mshwm, src]: the new value is between MSHWMB and the logical
      MSHWM; [hwm_raise] raises the logical MSHWM first. *)
  Lemma wp_csrw_mshwm E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc vb vh dq :
    decodeInstrW w.(lw) = SpecialRW cnull MSHWM (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    (get_a vb.(lw) ≤ get_a vsrc.(lw) ≤ get_a vh.(lw))%Z →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ MSHWMB ↦ₛᵣ vb ∗
        ▷ MSHWM ↦ₛᵣ vh }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        MSHWMB ↦ₛᵣ vb ∗
        MSHWM ↦ₛᵣ WInt (get_a vsrc.(lw)) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hle φ) "(>HPC & >Hpc_a & >Hsrc & >Hb & >Hh) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct "Hsr" as "(Hsr & Hres & Hzone)".
    iDestruct (gen_heap_valid with "Hsr Hb") as %Hb'.
    iDestruct (gen_heap_valid with "Hsr Hh") as %Hh'.
    destruct (erasure_hwm _ _ _ _ _ _ _ _ _ Her Hb' Hh') as (wb & z & Hwb & Hab & Hz & Hhwm).
    assert (({[src := vsrc]} : LReg) !!ₗ src = Some vsrc) as Hv.
    { rewrite llookup_reg_not_cnull //. by rewrite lookup_singleton_eq. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep.
    rewrite Hxsr Hz /= in Hstep.
    repeat (case_decide; try congruence).
    rewrite Hrs /= get_a_and_tag in Hstep.
    set (x := get_a vsrc.(lw)) in *.
    assert (erasure R C (WCap true pc_p pc_g pc_b pc_e pc_a, r, <[MSHWM := WInt x]> psr, m, st)
              (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (<[MSHWM := lword_of_word (WInt x)]> lsreg) lmem) as Her1.
    { apply erasure_insert_lmshwm; [ | apply reg_word_ok_int | done | ].
      - apply erasure_insert_mshwm; first done.
        intros vb' vh' Hvb' Hvh'. rewrite Hb' in Hvb'. rewrite Hh' in Hvh'. simplify_eq.
        rewrite lookup_insert_eq. eexists. split; first done. lia.
      - intros vb' vh' Hvb' Hvh'. rewrite lookup_insert_ne // Hb' in Hvb'.
        rewrite lookup_insert_eq in Hvh'. simplify_eq. cbn.
        rewrite lookup_insert_eq. eexists. split; first done. cbn. lia. }
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt x)) with "Hsr Hh") as "[Hsr Hh]".
    iAssert (sreg_interp (<[MSHWM := lword_of_word (WInt x)]> lsreg))
      with "[Hsr Hres Hzone]" as "Hsr".
    { iNamed "Hzone". iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
      rewrite /sreg_interp /hwm_zone. iFrame "Hsr Hres".
      rewrite Hmshwmb in Hb'. injection Hb' as ->.
      rewrite Hmshwm in Hh'. injection Hh' as ->.
      iExists zone, vb, (lword_of_word (WInt x)). iFrame "Hzone_auth Hzone_cells".
      iPureIntro. split_and!; [by rewrite lookup_insert_ne | by rewrite lookup_insert_eq |].
      intros a Ha. apply Hzone_cover. cbn in Ha. lia. }
    assert (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb Hh]").
    { exact Her1. }
    { rewrite /nextPC in Hu Hstep. rewrite /update_sreg /= in Hstep.
      by rewrite Hu in Hstep |- *. }
    { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
    { intros Hi'. rewrite /incrementPC in Hi. congruence. }
    iIntros (lpc'' retv [-> ->]) "HPC Hmap". iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [csrw mshwmb, src]: MSHWMB is lowered to [lo], with the cells of
      [[lo, hb)]. *)
  Lemma wp_csrw_mshwmb E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc vb (lo hb : Addr) dq :
    decodeInstrW w.(lw) = SpecialRW cnull MSHWMB (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = lo →
    get_a vb.(lw) = hb →
    (lo ≤ hb)%Z →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ MSHWMB ↦ₛᵣ vb ∗
        ([∗ list] a ∈ finz.seq_between lo hb, zone_cell a) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        MSHWMB ↦ₛᵣ WInt lo ∗
        ([∗ list] a ∈ finz.seq_between lo hb, zone_cell a) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hlo Hhb Hle φ)
      "(>HPC & >Hpc_a & >Hsrc & >Hb & Hcells) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct "Hsr" as "(Hsr & Hres & Hzone)". iNamed "Hzone".
    iEval (rewrite /hwm_zone) in "Hzone". iNamed "Hzone".
    iDestruct (gen_heap_valid with "Hsr Hb") as %Hb'.
    rewrite Hmshwmb in Hb'. injection Hb' as ->.
    iAssert (⌜∀ a : Addr, a ∈ finz.seq_between lo hb → a ∈ zone⌝)%I as %Hcells.
    { iIntros (a Ha). iDestruct (big_sepL_elem_of with "Hcells") as "Hcell"; first exact Ha.
      iDestruct (zone_cell_unfold with "Hcell") as "[Htok _]".
      iApply (zone_auth_elem with "Hzone_auth Htok"). }
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hmshwmb ltac:(done))
      as (wb & Hwb & _).
    assert (({[src := vsrc]} : LReg) !!ₗ src = Some vsrc) as Hv.
    { rewrite llookup_reg_not_cnull //. by rewrite lookup_singleton_eq. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep.
    rewrite Hxsr Hwb /= in Hstep.
    repeat (case_decide; try congruence).
    rewrite Hrs /= get_a_and_tag Hlo in Hstep.
    assert (erasure R C (WCap true pc_p pc_g pc_b pc_e pc_a, r, <[MSHWMB := WInt lo]> psr, m, st)
              (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (<[MSHWMB := lword_of_word (WInt lo)]> lsreg) lmem) as Her1.
    { apply erasure_insert_mshwmb; first done.
      intros vb' vh' Hvb' Hvh'. rewrite lookup_insert_eq in Hvb'. injection Hvb' as <-.
      rewrite lookup_insert_ne // in Hvh'.
      destruct (erasure_hwm _ _ _ _ _ _ _ _ _ Her Hmshwmb Hvh')
        as (wb' & z & _ & _ & Hz & Hz_le).
      exists z. split; first done. cbn. lia. }
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt lo)) with "Hsr Hb") as "[Hsr Hb]".
    iAssert (sreg_interp (<[MSHWMB := lword_of_word (WInt lo)]> lsreg))
      with "[Hsr Hres Hzone_auth Hzone_cells]" as "Hsr".
    { rewrite /sreg_interp /hwm_zone. iFrame "Hsr Hres".
      iExists zone, (lword_of_word (WInt lo)), vmshwm. iFrame "Hzone_auth Hzone_cells".
      iPureIntro. split_and!; [by rewrite lookup_insert_eq | by rewrite lookup_insert_ne |].
      intros a Ha. cbn in Ha. destruct (decide (a < hb)%Z) as [Hlt|Hge].
      + apply Hcells. apply elem_of_finz_seq_between. solve_addr.
      + apply Hzone_cover. lia. }
    assert (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb Hcells]").
    { exact Her1. }
    { rewrite /nextPC in Hu Hstep. rewrite /update_sreg /= in Hstep.
      by rewrite Hu in Hstep |- *. }
    { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
    { intros Hi'. rewrite /incrementPC in Hi. congruence. }
    iIntros (lpc'' retv [-> ->]) "HPC Hmap". iApply "Hφ". iFrame.
    iApply (regs_of_map_1 with "Hmap").
  Qed.

End hwm.
