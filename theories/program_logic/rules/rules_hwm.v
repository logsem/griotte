From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From griotte Require Export shapes.step instructions.memory_accesses instructions.system si_modality.
From griotte Require Import shapes.memory_access.

(** * The stack high-water mark

    The rules for MSHWM and MSHWMB, and for the zone of integer cells that the
    state interpretation couples to them. MSHWMB and MSHWM are per thread:
    their fragments are [mshwmb ↦ₜ mshwmb_v] and [mshwm ↦ₜ mshwm_v], and the physical
    registers hold [mshwmb_v] and [mshwm_v]. The zone covers [hc, mshwm_v), from the cover
    base [hc]: MSHWMB while the HWM restore window of the context-switch
    thread is closed, the target base while it is open. A cell of the zone
    ([zone_cell]) holds half of its points-to, so the load rules read it. *)

(** MSHWM after a store at [x] to a cell of the zone: [x] if it is in
    [mshwmb_v, mshwm_v), [mshwm_v] otherwise. *)
Definition hwm_after (x : Addr) (mshwmb_v mshwm_v : Z) : Z :=
  if decide (mshwmb_v ≤ x < mshwm_v)%Z then x else mshwm_v.

#[local] Arguments erasure_regs_incl {MP R C σ lpc lreg lsreg lmem regs}.
#[local] Arguments erasure_incrementPC_fail {MP R C pc r sr m st td lpc lreg lsreg lmem n}.
#[local] Arguments mem_access_authorised_reg_allows {MP} k {R regs φ r imm p ea}.
#[local] Arguments instr_close_mem_update {MP Σ ceriseg kd pc rf sr m st td lpc lreg lsreg lmem R C
  regs mem dfracs ea v pw c σ' Φ} P.

Section hwm.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types w : LWord.

  (** ** The high-water-mark part of [sys_interp] *)

  #[local] Lemma ls_set_win_hwm_eq ls mshwm_v :
    ls_set_win (ls_set_hwm (ls_set_hwmb ls (ls_hwmb ls)) mshwm_v) (ls_pend ls) (ls_lent ls) =
    ls_set_hwm ls mshwm_v.
  Proof. by destruct ls. Qed.

  #[local] Lemma ls_set_win_hwmb_eq ls mshwmb_v :
    ls_set_win (ls_set_hwm (ls_set_hwmb ls mshwmb_v) (ls_hwm ls)) (ls_pend ls) (ls_lent ls) =
    ls_set_hwmb ls mshwmb_v.
  Proof. by destruct ls. Qed.

  (** A ghost update that keeps the system registers. *)
  #[local] Lemma si_upd_sys E P Q :
    (∀ ls, sys_interp ls -∗ P ==∗ sys_interp ls ∗ Q) → P ⊢ |~{E}~> Q.
  Proof.
    intros Hupd. apply si_upd_ghost. iIntros (σ) "Hσ HP".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iMod (Hupd with "Hsr HP") as "[Hsr $]".
    iModIntro. iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** The ghost part of a store to the cell [x] of the zone, with the
      window closed: the cell leaves the zone with the other half of its
      points-to, and MSHWM becomes [hwm_after x mshwmb_v mshwm_v]. *)
  #[local] Lemma sys_interp_zone_store ls (x : Addr) (mshwmb_v mshwm_v : Z) :
    ls_pend ls = None →
    sys_interp ls -∗
    zone_token x -∗
    mshwmb ↦ₜ mshwmb_v -∗
    mshwm ↦ₜ mshwm_v
    ==∗
    ⌜ls_hwmb ls = mshwmb_v ∧ ls_hwm ls = mshwm_v⌝ ∗
    sys_interp (ls_set_hwm ls (hwm_after x mshwmb_v mshwm_v)) ∗
    (∃ z : Z, x ↦ₐ{DfracOwn (1/2)} lword_of_word (WInt z)) ∗
    mshwmb ↦ₜ mshwmb_v ∗
    mshwm ↦ₜ hwm_after x mshwmb_v mshwm_v.
  Proof.
    iIntros (Hpend) "Hsys Htok Hb Hh".
    iDestruct (sys_interp_hwm_open with "Hsys")
      as "(Hmshwmb_a & Hmshwm_a & Hpend_si & Hlent_a & Hzone & Hclose)".
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
    iDestruct (mshwm_agree with "Hmshwm_a Hh") as %Hh. subst mshwmb_v mshwm_v.
    iEval (rewrite Hpend /hc_of /=) in "Hzone". iNamed "Hzone".
    iDestruct (zone_auth_elem with "Hzone_auth Htok") as %Hxz.
    iMod (zone_auth_delete with "Hzone_auth Htok") as "Hzone_auth".
    iDestruct (big_sepS_delete with "Hzone_cells") as "[Hx Hzone_cells]"; first exact Hxz.
    iMod (mshwm_update _ _ (hwm_after x (ls_hwmb ls) (ls_hwm ls)) with "Hmshwm_a Hh")
      as "[Hmshwm_a Hh]".
    iModIntro. iFrame "Hx Hb Hh". iSplit; first done.
    rewrite -ls_set_win_hwm_eq.
    iApply ("Hclose" with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a").
    rewrite Hpend /hc_of /=.
    iExists (zone ∖ {[x]}). iFrame "Hzone_auth Hzone_cells Hlent_cells". iPureIntro.
    intros a Ha. rewrite /hwm_after in Ha.
    assert (a ≠ x ∧ (ls_hwmb ls ≤ a < ls_hwm ls)%Z) as [Hne Hin'].
    { case_decide as Hin; split; try lia.
      - intros ->. lia.
      - intros ->. by apply Hin. }
    pose proof (Hzone_cover a Hin') as Hc. set_solver.
  Qed.


  (** ** The cells of the zone *)

  (** A cell that holds an integer joins the zone. *)
  Lemma zone_deposit_v E a z : a ↦ₐ WInt z ⊢ |~{E}~> zone_cell_v a z.
  Proof.
    apply si_upd_sys. iIntros (ls) "Hsys Ha".
    iDestruct (sys_interp_hwm_open with "Hsys")
      as "(Hmshwmb_a & Hmshwm_a & Hpend_si & Hlent_a & Hzone & Hclose)".
    iNamed "Hzone".
    iDestruct (zone_cells_not_elem with "Hzone_cells Ha") as %Ha.
    iMod (zone_auth_insert with "Hzone_auth") as "[Hzone_auth Htok]"; first done.
    iDestruct "Ha" as "[Ha1 Ha2]".
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a
                  [Hzone_auth Hzone_cells Hlent_cells Ha1]").
    { iExists ({[a]} ∪ zone). iFrame "Hzone_auth Hlent_cells".
      rewrite /zone_halves big_sepS_insert //. iFrame "Ha1 Hzone_cells".
      iPureIntro. intros a' Ha'. specialize (Hzone_cover a' Ha'). set_solver. }
    rewrite ls_set_win_hwm_id zone_cell_v_unfold. iModIntro. iFrame.
  Qed.

  (** A zeroed cell joins the zone. *)
  Lemma zone_deposit E a : a ↦ₐ WInt 0 ⊢ |~{E}~> zone_cell a.
  Proof.
    iIntros "Ha".
    iApply (si_upd_bind _ (zone_cell_v a 0) with "[Ha]"); first by iApply zone_deposit_v.
    iIntros "Ha". iModIntro. by iExists 0.
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

  Lemma zone_deposit_list_v E (l : list Addr) :
    ([∗ list] a ∈ l, a ↦ₐ WInt 0) ⊢ |~{E}~> [∗ list] a ∈ l, zone_cell_v a 0.
  Proof.
    induction l as [|a l IH]; cbn.
    { iIntros "_". by iModIntro. }
    iIntros "[Ha Hl]".
    iApply (si_upd_bind _ (zone_cell_v a 0) with "[Ha]"); first by iApply zone_deposit_v.
    iIntros "Ha". iApply (si_upd_bind with "[Hl]"); first by iApply IH.
    iIntros "Hl". iModIntro. iFrame.
  Qed.

  (** ** Ghost updates of the zone in front of an instruction

      The window clause of the instance is only visible through the weakest
      precondition: these lemmas open the state interpretation in front of
      an expression that is not a value. The window is closed: [True] at a
      user thread, the code's quarter at [None] at the context-switch
      thread. *)

  (** The window is closed at the state interpretation's system
      registers. *)
  #[local] Lemma hwm_closed_pend_none k σ ls :
    hwm_closed k -∗ hwm_win_si k σ -∗ sys_interp ls -∗ ⌜ls_pend ls = None⌝.
  Proof.
    iIntros "Hcl Hwin Hsr". destruct k; rewrite /hwm_closed /hwm_win_si.
    - iDestruct "Hwin" as "(Hhalf & _)".
      iApply (sys_interp_pend_half_agree with "Hsr Hhalf").
    - iApply (sys_interp_pend_frag_agree with "Hsr Hcl").
  Qed.

  (** A ghost update of [sys_interp] with the window closed, in front of
      [e]. *)
  #[local] Lemma wp_sys_upd_closed E e Φ P Q :
    to_val e = None →
    (∀ ls, ⌜ls_pend ls = None⌝ -∗ sys_interp ls -∗ P ==∗ sys_interp ls ∗ Q) →
    hwm_closed (kind_of th) -∗
    P -∗
    (hwm_closed (kind_of th) -∗ Q -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hupd) "Hcl HP HΦ".
    rewrite wp_unfold /wp_pre /= He.
    iIntros (σ1 ns κ κs nt) "(Hσ & %Hrdom & Hlink & Hirq & Hwin) /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (hwm_closed_pend_none with "Hcl Hwin Hsr") as %Hpend.
    iMod (Hupd with "[//] Hsr HP") as "[Hsr HQ]".
    iSpecialize ("HΦ" with "Hcl HQ").
    iApply ("HΦ" $! σ1 ns κ κs nt). iFrame "Hlink Hirq Hwin %".
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** A cell outside [MSHWMB, MSHWM) leaves the zone. *)
  Lemma wp_zone_release E e Φ (a : Addr) (z : Z) (mshwmb_v mshwm_v : Z) :
    to_val e = None →
    ¬ (mshwmb_v ≤ a < mshwm_v)%Z →
    hwm_closed (kind_of th) -∗
    zone_cell_v a z -∗
    mshwmb ↦ₜ mshwmb_v -∗
    mshwm ↦ₜ mshwm_v -∗
    (hwm_closed (kind_of th) -∗
     a ↦ₐ WInt z -∗
     mshwmb ↦ₜ mshwmb_v -∗
     mshwm ↦ₜ mshwm_v -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hout) "Hcl Hcell Hb Hh HΦ".
    iApply (wp_sys_upd_closed _ _ _ (zone_cell_v a z ∗ mshwmb ↦ₜ mshwmb_v ∗ mshwm ↦ₜ mshwm_v)%I
              (a ↦ₐ WInt z ∗ mshwmb ↦ₜ mshwmb_v ∗ mshwm ↦ₜ mshwm_v)%I
             with "Hcl [$Hcell $Hb $Hh]"); first done.
    - iIntros (ls Hpend) "Hsys (Hcell & Hb & Hh)".
      iDestruct (sys_interp_hwm_open with "Hsys")
        as "(Hmshwmb_a & Hmshwm_a & Hpend_si & Hlent_a & Hzone & Hclose)".
      iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
      iDestruct (mshwm_agree with "Hmshwm_a Hh") as %Hh. subst mshwmb_v mshwm_v.
      iEval (rewrite Hpend /hc_of /=) in "Hzone". iNamed "Hzone".
      iDestruct (zone_cell_v_unfold with "Hcell") as "[Htok Ha2]".
      iDestruct (zone_auth_elem with "Hzone_auth Htok") as %Ha.
      iMod (zone_auth_delete with "Hzone_auth Htok") as "Hzone_auth".
      iDestruct (big_sepS_delete with "Hzone_cells") as "[[%z' Ha1] Hzone_cells]"; first exact Ha.
      iCombine "Ha1 Ha2" as "Ha" gives %[_ Heq]. simplify_eq.
      iEval (rewrite ?dfrac_op_own ?Qp.half_half) in "Ha".
      iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a
                    [Hzone_auth Hzone_cells Hlent_cells]").
      { rewrite Hpend /hc_of /=. iExists (zone ∖ {[a]}).
        iFrame "Hzone_auth Hzone_cells Hlent_cells". iPureIntro.
        intros a' Ha'. specialize (Hzone_cover a' Ha').
        assert (a' ≠ a) by (intros ->; by apply Hout). set_solver. }
      rewrite ls_set_win_hwm_id. iModIntro. iFrame.
    - iIntros "Hcl (Ha & Hb & Hh)". iApply ("HΦ" with "Hcl Ha Hb Hh").
  Qed.

  Lemma wp_zone_release_list E e Φ (l : list Addr) (mshwmb_v mshwm_v : Z) :
    to_val e = None →
    (∀ a : Addr, a ∈ l → ¬ (mshwmb_v ≤ a < mshwm_v)%Z) →
    hwm_closed (kind_of th) -∗
    ([∗ list] a ∈ l, zone_cell a) -∗
    mshwmb ↦ₜ mshwmb_v -∗
    mshwm ↦ₜ mshwm_v -∗
    (hwm_closed (kind_of th) -∗
     ([∗ list] a ∈ l, ∃ z : Z, a ↦ₐ WInt z) -∗
     mshwmb ↦ₜ mshwmb_v -∗
     mshwm ↦ₜ mshwm_v -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He). iInduction l as [|a l] "IH"; iIntros (Hout) "Hcl Hl Hb Hh HΦ".
    { iApply ("HΦ" with "Hcl [//] Hb Hh"). }
    iDestruct "Hl" as "[[%z Ha] Hl]".
    iApply (wp_zone_release with "Hcl Ha Hb Hh"); [done | apply Hout; by left |].
    iIntros "Hcl Ha Hb Hh".
    iApply ("IH" with "[%] Hcl Hl Hb Hh").
    { intros a' Ha'. apply Hout. by right. }
    iIntros "Hcl Hl Hb Hh". iApply ("HΦ" with "Hcl [$Ha $Hl] Hb Hh").
  Qed.

  (** A full points-to is outside [MSHWMB, MSHWM): the zone covers that
      range, and holds half of the points-to of each of its cells. *)
  Lemma wp_hwm_pointsto_outside E e Φ (a : Addr) w (mshwmb_v mshwm_v : Z) :
    to_val e = None →
    hwm_closed (kind_of th) -∗
    a ↦ₐ w -∗
    mshwmb ↦ₜ mshwmb_v -∗
    mshwm ↦ₜ mshwm_v -∗
    (⌜¬ (mshwmb_v ≤ a < mshwm_v)%Z⌝ -∗
     hwm_closed (kind_of th) -∗
     a ↦ₐ w -∗
     mshwmb ↦ₜ mshwmb_v -∗
     mshwm ↦ₜ mshwm_v -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "Hcl Ha Hb Hh HΦ".
    iApply (wp_sys_upd_closed _ _ _ (a ↦ₐ w ∗ mshwmb ↦ₜ mshwmb_v ∗ mshwm ↦ₜ mshwm_v)%I
              (⌜¬ (mshwmb_v ≤ a < mshwm_v)%Z⌝ ∗ a ↦ₐ w ∗ mshwmb ↦ₜ mshwmb_v ∗ mshwm ↦ₜ mshwm_v)%I
             with "Hcl [$Ha $Hb $Hh]"); first done.
    - iIntros (ls Hpend) "Hsys (Ha & Hb & Hh)".
      iDestruct (sys_interp_mshwmb_agree with "Hsys Hb") as %<-.
      iDestruct (sys_interp_mshwm_agree with "Hsys Hh") as %<-.
      iDestruct (sys_interp_pointsto_outside with "Hsys Ha") as %Hout.
      rewrite Hpend /hc_of /= in Hout.
      iModIntro. iFrame "Hsys Ha Hb Hh". done.
    - iIntros "Hcl (%Hout & Ha & Hb & Hh)". iApply ("HΦ" with "[//] Hcl Ha Hb Hh").
  Qed.

  (** ** From code without system-register access

      The window holds a PC with the system-register permission: from a PC
      without it, the window is closed at any thread, without
      [hwm_closed]. *)

  (** From a PC without the system-register permission, the window is
      closed at the system registers of the state interpretation. *)
  #[local] Lemma hwm_win_si_nosr_pend_none k σ ls :
    pc_nosr (pcc σ) = true →
    hwm_win_si k σ -∗ sys_interp ls -∗ ⌜ls_pend ls = None⌝.
  Proof.
    intros Hnsr. destruct k.
    - cbn. iIntros "(Hhalf & _) Hsys".
      iApply (sys_interp_pend_half_agree with "Hsys Hhalf").
    - iIntros "Hwin Hsys".
      iDestruct (hwm_win_si_ctx_nosr σ Hnsr with "Hwin") as "Hcl".
      iApply (sys_interp_pend_cl_agree with "Hsys Hcl").
  Qed.

  (** A ghost update of [sys_interp] in front of [e], from a PC without the
      system-register permission. *)
  #[local] Lemma wp_sys_upd_nosr E e Φ (lpc : LWord) P Q :
    to_val e = None →
    pc_nosr lpc.(lw) = true →
    (∀ ls, ⌜ls_pend ls = None⌝ -∗ sys_interp ls -∗ P ==∗ sys_interp ls ∗ Q) →
    PC ↦ₚ lpc -∗
    P -∗
    (PC ↦ₚ lpc -∗ Q -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hnsr Hupd) "HPC HP HΦ".
    rewrite wp_unfold /wp_pre /= He.
    iIntros (σ1 ns κ κs nt) "(Hσ & %Hrdom & Hlink & Hirq & Hwin) /=".
    iDestruct (SI_open with "Hσ") as (lpc' lreg lsreg lmem R C) "Hσ". iNamed "Hσ".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    iDestruct (hwm_win_si_nosr_pend_none with "Hwin Hsr") as %Hpend.
    { by rewrite (erasure_pc_exact _ _ _ _ _ _ _ Her). }
    iMod (Hupd with "[//] Hsr HP") as "[Hsr HQ]".
    iSpecialize ("HΦ" with "HPC HQ").
    iApply ("HΦ" $! σ1 ns κ κs nt). iFrame "Hlink Hirq Hwin %".
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** A cell outside [MSHWMB, MSHWM) leaves the zone, from a PC without
      the system-register permission. *)
  Lemma wp_zone_release_nosr E e Φ (lpc : LWord) (a : Addr) (z : Z) (mshwmb_v mshwm_v : Z) :
    to_val e = None →
    pc_nosr lpc.(lw) = true →
    ¬ (mshwmb_v ≤ a < mshwm_v)%Z →
    PC ↦ₚ lpc -∗
    zone_cell_v a z -∗
    mshwmb ↦ₜ mshwmb_v -∗
    mshwm ↦ₜ mshwm_v -∗
    (PC ↦ₚ lpc -∗
     a ↦ₐ WInt z -∗
     mshwmb ↦ₜ mshwmb_v -∗
     mshwm ↦ₜ mshwm_v -∗
     WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He Hnsr Hout) "HPC Hcell Hb Hh HΦ".
    iApply (wp_sys_upd_nosr _ _ _ lpc (zone_cell_v a z ∗ mshwmb ↦ₜ mshwmb_v ∗ mshwm ↦ₜ mshwm_v)%I
              (a ↦ₐ WInt z ∗ mshwmb ↦ₜ mshwmb_v ∗ mshwm ↦ₜ mshwm_v)%I
             with "HPC [$Hcell $Hb $Hh]"); [done | done | |].
    - iIntros (ls Hpend) "Hsys (Hcell & Hb & Hh)".
      iDestruct (sys_interp_hwm_open with "Hsys")
        as "(Hmshwmb_a & Hmshwm_a & Hpend_si & Hlent_a & Hzone & Hclose)".
      iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
      iDestruct (mshwm_agree with "Hmshwm_a Hh") as %Hh. subst mshwmb_v mshwm_v.
      iEval (rewrite Hpend /hc_of /=) in "Hzone". iNamed "Hzone".
      iDestruct (zone_cell_v_unfold with "Hcell") as "[Htok Ha2]".
      iDestruct (zone_auth_elem with "Hzone_auth Htok") as %Ha.
      iMod (zone_auth_delete with "Hzone_auth Htok") as "Hzone_auth".
      iDestruct (big_sepS_delete with "Hzone_cells") as "[[%z' Ha1] Hzone_cells]"; first exact Ha.
      iCombine "Ha1 Ha2" as "Ha" gives %[_ Heq]. simplify_eq.
      iEval (rewrite ?dfrac_op_own ?Qp.half_half) in "Ha".
      iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a
                    [Hzone_auth Hzone_cells Hlent_cells]").
      { rewrite Hpend /hc_of /=. iExists (zone ∖ {[a]}).
        iFrame "Hzone_auth Hzone_cells Hlent_cells". iPureIntro.
        intros a' Ha'. specialize (Hzone_cover a' Ha').
        assert (a' ≠ a) by (intros ->; by apply Hout). set_solver. }
      rewrite ls_set_win_hwm_id. iModIntro. iFrame.
    - iIntros "HPC (Ha & Hb & Hh)". iApply ("HΦ" with "HPC Ha Hb Hh").
  Qed.

  (** ** Stores of a memory-access membership to a cell of the zone *)

  (** A store of a membership [store_member exec_opt wok i r imm] (as
      [wp_store_step_gen]) to the cell [x] of the zone: the cells [mem] at
      the fractions [dfracs] (the PC's cell included) hold the zone's half
      of [x], with its token. On success the cell leaves the zone, wholly
      owned and holding the stored word, and MSHWM becomes
      [hwm_after x mshwmb_v mshwm_v]; on a fault, nothing changes. When [L]
      holds, the step agrees with the access, some word is stored and [W]
      keeps the authority live: the access does not fault
      ([mem_access_progress]). *)
  Lemma wp_store_step_zone_gen Ep pc_p pc_g pc_b pc_e pc_a pc_π w i r imm wok (Q : LWord → Prop)
      (L : Prop) (W : iProp Σ) (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) (x : Addr)
      (mshwmb_v mshwm_v : Z) :
    decodeInstrW w.(lw) = i → store_member exec_opt wok i r imm → sw_of (kind_of th) i = None →
    ¬ hwm_window_instr i →
    (L → mem_store_next_ok exec_opt wok i r imm) →
    (L → store_lift_some wok regs) →
    (L → ∀ v, regs !! r = Some v → live_witness W v) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → store_lift wok Q regs →
    mem !! pc_a = Some w → dom dfracs = dom mem →
    is_Some (mem !! x) → dfracs !! x = Some (DfracOwn (1/2)) →
    (∀ p g b e a ea, reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea → ea = x) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        zone_token x ∗
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        PC ↦ₚ lpc' ∗
        mshwmb ↦ₜ mshwmb_v ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W ∗
        ((⌜retv = FaultedV ∧
           (L → mem_access_progress MemAccessWrite regs r imm mem
                  (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) retv)⌝ ∗
          ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
          zone_token x ∗
          mshwm ↦ₜ mshwm_v) ∨
         (∃ p g b e a v,
            ⌜retv = NextIV ∧ reg_allows_mem_access MemAccessWrite regs r imm p g b e a x ∧
             incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧ Q v⌝ ∗
            ([∗ map] a↦dv ∈ prod_merge (<[x := DfracOwn 1]> dfracs) (<[x := lstore_word p v]> mem),
               a ↦ₐ{dv.1} dv.2) ∗
            mshwm ↦ₜ hwm_after x mshwmb_v mshwm_v)) }}}.
  Proof.
    iIntros (Hi Hmember Hsw Hnwin Hagree Hsome Hlive Hvpc Hr Hlift Hmem_pc Hdom [zx Hx] Hdqx Hfoot
             Φ).
    iIntros "(>HPC & >Hmem & Htok & >Hb & >Hh & >Hmap & Hwit) Hφ".
    destruct (prod_merge_lookup_dom _ _ _ _ Hmem_pc Hdom) as [dq_pc Hmerge_pc].
    iDestruct (big_sepM_delete _ _ pc_a with "Hmem") as "[Hpc_a Hmem]"; first exact Hmerge_pc.
    iSimpl in "Hpc_a".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [by rewrite Hi | done | |].
    { intros _. rewrite Hi. apply not_true_is_false. intros Hwr. apply Hnwin. by right. }
    iNext. iIntros (rf sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (big_sepM_delete _ _ pc_a (dq_pc, w) with "[Hpc_a $Hmem]") as "Hmem";
      [exact Hmerge_pc | iExact "Hpc_a" |].
    iAssert (⌜mem ⊆ lmem⌝)%I as %Hmem_incl.
    { rewrite map_subseteq_spec. iIntros (a v Hv).
      destruct (prod_merge_lookup_dom _ _ _ _ Hv Hdom) as [dq Hmerge].
      by iApply (gen_mem_valid_inSepM_general with "Hm Hmem"). }
    iDestruct (live_witness_cond L W regs r R Hlive with "HR Hwit") as %Hlive_ok.
    rewrite Hi /exec in Hstep.
    destruct (exec_opt i pc_p _) as [conf|] eqn:Hexec; cycle 1.
    { (* A fault: with the liveness, not on a cell. *)
      simplify_eq.
      assert (L → mem_access_progress MemAccessWrite regs r imm mem
                    (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
                    (FaultedV : tval (kind_of th))) as Hprog.
      { intros HL (p & g & b & e & a & ea & Hacc & Hin) [lpc' Hinc].
        destruct (store_step_live_inv exec_opt wok _ _ _ _ _ _ _ _ regs r imm mem pc_p
                    p g b e a ea Her Hlregs Hmem_incl (Hagree HL) (Hsome HL)
                    (Hlive_ok HL) Hacc Hin) as (w' & _ & Hnext).
        rewrite Hexec in Hnext.
        destruct (nextPC_is_Some_erasure _ _ _ ((store_effect ea _) .[ea :=ₐ store_word p w'])
                    _ _ _ _ _ Her ltac:(done) Hinc) as [conf Hconf].
        congruence. }
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply "Hφ". iFrame. iLeft. by iFrame. }
    subst conf.
    (* A store is not an instruction of the window: the window is closed. *)
    assert (ls_pend lsreg = None) as Hpend.
    { destruct Hwin as [Hnone | Hw]; first done. rewrite Hi in Hw. by apply Hnwin in Hw. }
    (* The cell [x] is in memory, not a device. *)
    assert (prod_merge dfracs mem !! x = Some (DfracOwn (1/2), zx)) as Hmergex.
    { by rewrite lookup_merge Hx Hdqx. }
    iDestruct (gen_mem_valid_inSepM_general with "Hm Hmem") as %Hlx; first exact Hmergex.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hlx) as (pwx & Hmx & _).
    pose proof (er_mmio _ _ _ _ _ _ _ Her) as Hmmio0; cbn in Hmmio0.
    pose proof (mem_avoids_mmio_lookup _ _ _ Hmmio0 Hmx) as Hxmmio.
    destruct (Hmember _ _ _ Hexec) as [p ea w0 Hauth Hea_mmio Hin Hwok Hnext
                                     |p ea w0 φ' Hauth Hea_mmio Hstore Hnext Hwok].
    all: destruct (mem_access_authorised_reg_allows MemAccessWrite
                     (φ := MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) rf sr m st td) Hregs Hr Hauth)
           as (g & b & e & a & Hacc).
    all: pose proof (Hfoot _ _ _ _ _ _ Hacc) as ->.
    2: { exfalso. congruence. }
    destruct (Hlift _ _ _ _ _ _ _ _ Her Hlregs Hwok) as (v & HQ & Hvok & Hvphys).
    assert (mem_word_ok R C (lstore_word p v) (store_word p w0)) as Hpw.
    { apply reg_phys_mem_word_ok; first by apply reg_word_ok_lstore_word.
      by apply reg_phys_lstore_word. }
    (* The erasure after the update of MSHWM and the store. *)
    assert (erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) rf (hwm_update x sr) m st td)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_hwm lsreg (hwm_after x (ls_hwmb lsreg) (ls_hwm lsreg)))) lmem)
      as Her0.
    { rewrite ls_join_set_hwm /hwm_after. case_decide as Hin'.
      - eapply erasure_hwm_update_lower;
          [exact Her | apply ls_join_mshwmb | apply ls_join_mshwm | exact Hin'].
      - rewrite insert_id; last apply ls_join_mshwm.
        eapply erasure_hwm_update;
          [exact Her | apply ls_join_mshwmb | apply ls_join_mshwm | exact Hin']. }
    pose proof (erasure_store _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ Her0 Hlx Hpw) as Her1.
    rewrite /store_effect /hwm_store /= in Hnext.
    destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hinc.
    2: { pose proof (erasure_incrementPC_fail Her1 Hinc) as Hfail.
         rewrite /nextPC Hfail in Hnext. discriminate. }
    (* The ghost part: the cell leaves the zone, MSHWM moves. *)
    iMod (sys_interp_zone_store with "Hsr Htok Hb Hh")
      as "([%Hhb %Hh] & Hsr & [%z' Hx1] & Hb & Hh)"; first exact Hpend.
    subst mshwmb_v mshwm_v.
    iDestruct (big_sepM_delete _ _ x with "Hmem") as "[Hx2 Hmem]"; first exact Hmergex.
    iSimpl in "Hx2".
    iCombine "Hx1 Hx2" as "Hxm" gives %[_ Hz'].
    iEval (rewrite dfrac_op_own Qp.half_half) in "Hxm".
    iAssert ([∗ map] a↦dv ∈ prod_merge (<[x := DfracOwn 1]> dfracs) mem, a ↦ₐ{dv.1} dv.2)%I
      with "[Hxm Hmem]" as "Hmem".
    { assert (prod_merge (<[x := DfracOwn 1]> dfracs) mem =
              <[x := (DfracOwn 1, zx)]> (prod_merge dfracs mem)) as ->.
      { rewrite /prod_merge -{1}(insert_id mem x zx) //. by erewrite insert_merge. }
      rewrite big_sepM_insert_delete -Hz'. iFrame. }
    iApply (instr_close_kept_trans _ (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) rf
                                       (hwm_update x sr) m st td)).
    { rewrite /sys_kept /mie_st /= !lookup_hwm_update_ne //. }
    iApply (instr_close_mem_update
      (λ lpc'' mem' (retv : tval (kind_of th)),
         retv = NextIV ∧ lpc'' = lpc' ∧ mem' = <[x := lstore_word p v]> mem)
      Her0 (mk_is_Some _ _ Hx) (lookup_insert_eq _ _ _) Hpw
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmem Hmap [Hφ Hb Hh Hwit]").
    { by rewrite Hnext. }
    { intros lpc'' Hinc'. rewrite Hinc in Hinc'. by simplify_eq. }
    { intros Hinc'. congruence. }
    iIntros (lpc'' mem' retv (-> & -> & ->)) "HPC Hmem Hmap".
    iApply "Hφ". iFrame. iRight. iExists p, g, b, e, a, v. iFrame. by iPureIntro.
  Qed.

  (** The store of the fundamental theorem to a cell of the zone: faults
      allowed, no witness. *)
  Lemma wp_store_step_zone Ep pc_p pc_g pc_b pc_e pc_a pc_π w i r imm wok (Q : LWord → Prop)
      (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) (x : Addr) (mshwmb_v mshwm_v : Z) :
    decodeInstrW w.(lw) = i → store_member exec_opt wok i r imm → sw_of (kind_of th) i = None →
    ¬ hwm_window_instr i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → store_lift wok Q regs →
    mem !! pc_a = Some w → dom dfracs = dom mem →
    is_Some (mem !! x) → dfracs !! x = Some (DfracOwn (1/2)) →
    (∀ p g b e a ea, reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea → ea = x) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        zone_token x ∗
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        PC ↦ₚ lpc' ∗
        mshwmb ↦ₜ mshwmb_v ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ((⌜retv = FaultedV⌝ ∗
          ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
          zone_token x ∗
          mshwm ↦ₜ mshwm_v) ∨
         (∃ p g b e a v,
            ⌜retv = NextIV ∧ reg_allows_mem_access MemAccessWrite regs r imm p g b e a x ∧
             incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧ Q v⌝ ∗
            ([∗ map] a↦dv ∈ prod_merge (<[x := DfracOwn 1]> dfracs) (<[x := lstore_word p v]> mem),
               a ↦ₐ{dv.1} dv.2) ∗
            mshwm ↦ₜ hwm_after x mshwmb_v mshwm_v)) }}}.
  Proof.
    iIntros (Hi Hmember Hsw Hnwin Hvpc Hr Hlift Hmem_pc Hdom Hx Hdqx Hfoot Φ)
      "(HPC & Hmem & Htok & Hb & Hh & Hmap) Hφ".
    iApply (wp_store_step_zone_gen _ _ _ _ _ _ _ _ _ _ _ _ _ False emp%I
              with "[$HPC $Hmem $Htok $Hb $Hh $Hmap]");
      [exact Hi | exact Hmember | exact Hsw | exact Hnwin | intros [] | intros [] | intros []
      | exact Hvpc | exact Hr | exact Hlift | exact Hmem_pc | exact Hdom | exact Hx | exact Hdqx
      | exact Hfoot |].
    iIntros "!>" (lpc' retv) "(HPC & Hb & Hmap & _ & [ ([-> _] & Hmem & Htok & Hh) | Hsucc ])".
    - iApply "Hφ". iFrame. iLeft. by iFrame.
    - iApply "Hφ". iFrame.
  Qed.

  (** ** Stores to a cell of the zone *)

  (** A store, by a live authority, to a cell [ea] of the zone: the cell
      leaves the zone with a full points-to, and MSHWM is lowered to [ea] if
      [ea] is in [MSHWMB, MSHWM). *)
  #[local] Lemma wp_store_zone_next E pc_p pc_g pc_b pc_e pc_a pc_π w dst ρ (imm : Z) regs
      p g b e a ea z storev (mshwmb_v mshwm_v : Z) dq dw lpc' :
    decodeInstrW w.(lw) = Store dst ρ imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Store dst ρ imm) ⊆ dom regs →
    regs !!ₗ dst = Some (Cap p g b e a @@? deref_id dw) →
    (a + imm)%a = Some ea →
    writeAllowed p = true → withinBounds b e ea = true →
    lword_of_argument regs ρ = Some storev →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        zone_cell_v ea z ∗
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ea ↦ₐ lstore_word p storev ∗
        mshwmb ↦ₜ mshwmb_v ∗
        mshwm ↦ₜ hwm_after ea mshwmb_v mshwm_v ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs Hdst Hadd Hwa Hwb Harg Hinc φ)
      "(HPC & >Hi & Hcell & Hb & Hh & Hdw & Hmap) Hφ".
    iDestruct (zone_cell_v_unfold with "Hcell") as "[Htok Hx]".
    assert (lw <$> regs !!ₗ dst = Some (Cap p g b e a)) as Hdst' by by rewrite Hdst.
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hdst') as (Hdst_cnull & _).
    assert (reg_allows_mem_access MemAccessWrite regs dst imm p g b e a ea) as Hacc.
    { split_and!; [exact Hdst' | exact Hadd | exact Hwa | exact Hwb]. }
    rewrite llookup_reg_not_cnull // in Hdst.
    assert (dst ∈ dom regs) as Hdst_dom by by eapply elem_of_dom_2.
    assert (∀ p0 g0 b0 e0 a0 ea0,
               reg_allows_mem_access MemAccessWrite regs dst imm p0 g0 b0 e0 a0 ea0 → ea0 = ea)
      as Hfoot.
    { intros p0 g0 b0 e0 a0 ea0 Hacc0.
      by destruct (reg_allows_mem_access_det Hacc Hacc0) as (_ & _ & _ & _ & _ & ->). }
    destruct (decide (pc_a = ea)) as [<- | Hne].
    - (* The instruction's cell is the cell of the zone. *)
      iDestruct (pointsto_agree with "Hi Hx") as %->.
      iEval (rewrite prod_merge_pointsto_1) in "Hx".
      iApply (wp_store_step_zone_gen _ _ _ _ _ _ _ _ _ _ _ _ _ True (deref_witness_res dw)
                (<[pc_a := lword_of_word (WInt z)]> ∅) (<[pc_a := DfracOwn (1/2)]> ∅) regs pc_a
                with "[$HPC $Hx $Htok $Hb $Hh $Hmap $Hdw]");
        [exact Hdecode | apply Store_member_argument | by apply sw_of_none
        | by intros [ (? & ? & ? & ?) | ? ] | intros _; apply store_next_ok
        | intros _; by eapply store_lift_exact_some, store_lift_argument
        | intros _ v1 Hv1; rewrite Hdst in Hv1; simplify_eq; by apply deref_witness_live
        | exact Hvpc | exact Hdst_dom | apply store_lift_exact_lift; by apply store_lift_argument
        | by simplify_map_eq | by rewrite !dom_insert_L | by simplify_map_eq | by simplify_map_eq
        | exact Hfoot |].
      iIntros "!>" (lpc0 retv) "(HPC & Hb & Hmap & Hdw & [ (%Hfault & _) | Hsucc ])".
      { exfalso. destruct Hfault as [-> Hprog].
        assert (mem_access_cell MemAccessWrite regs dst imm (<[pc_a := lword_of_word (WInt z)]> ∅))
          as Hcell.
        { exists p, g, b, e, a, pc_a. split; first done. by simplify_map_eq. }
        specialize (Hprog I Hcell (ex_intro _ _ Hinc)). discriminate. }
      iDestruct "Hsucc" as (p0 g0 b0 e0 a0 v0) "([%Hret [%Hacc0 [%Hinc0 %Hv0] ] ] & Hmem & Hh)".
      subst retv v0.
      destruct (reg_allows_mem_access_det Hacc Hacc0) as (-> & _).
      rewrite Hinc in Hinc0. simplify_eq.
      rewrite !insert_insert_eq -prod_merge_pointsto_1.
      iApply "Hφ". iFrame.
    - (* Another cell. *)
      iAssert ([∗ map] a0↦dv ∈ prod_merge (<[pc_a := dq]> (<[ea := DfracOwn (1/2)]> ∅))
                 (<[pc_a := w]> (<[ea := lword_of_word (WInt z)]> ∅)), a0 ↦ₐ{dv.1} dv.2)%I
        with "[Hi Hx]" as "Hmem".
      { rewrite memMap_resource_2ne_dq //. iFrame. }
      iApply (wp_store_step_zone_gen _ _ _ _ _ _ _ _ _ _ _ _ _ True (deref_witness_res dw)
                (<[pc_a := w]> (<[ea := lword_of_word (WInt z)]> ∅))
                (<[pc_a := dq]> (<[ea := DfracOwn (1/2)]> ∅)) regs ea
                with "[$HPC $Hmem $Htok $Hb $Hh $Hmap $Hdw]");
        [exact Hdecode | apply Store_member_argument | by apply sw_of_none
        | by intros [ (? & ? & ? & ?) | ? ] | intros _; apply store_next_ok
        | intros _; by eapply store_lift_exact_some, store_lift_argument
        | intros _ v1 Hv1; rewrite Hdst in Hv1; simplify_eq; by apply deref_witness_live
        | exact Hvpc | exact Hdst_dom | apply store_lift_exact_lift; by apply store_lift_argument
        | by simplify_map_eq | by rewrite !dom_insert_L | by simplify_map_eq | by simplify_map_eq
        | exact Hfoot |].
      iIntros "!>" (lpc0 retv) "(HPC & Hb & Hmap & Hdw & [ (%Hfault & _) | Hsucc ])".
      { exfalso. destruct Hfault as [-> Hprog].
        assert (mem_access_cell MemAccessWrite regs dst imm
                  (<[pc_a := w]> (<[ea := lword_of_word (WInt z)]> ∅))) as Hcell.
        { exists p, g, b, e, a, ea. split; first done. by simplify_map_eq. }
        specialize (Hprog I Hcell (ex_intro _ _ Hinc)). discriminate. }
      iDestruct "Hsucc" as (p0 g0 b0 e0 a0 v0) "([%Hret [%Hacc0 [%Hinc0 %Hv0] ] ] & Hmem & Hh)".
      subst retv v0.
      destruct (reg_allows_mem_access_det Hacc Hacc0) as (-> & _).
      rewrite Hinc in Hinc0. simplify_eq.
      rewrite !(insert_insert_ne _ ea pc_a) // !insert_insert_eq memMap_resource_2ne_dq //.
      iDestruct "Hmem" as "[Hi Hea]".
      iApply "Hφ". iFrame.
  Qed.

  (** A store of an immediate to a cell of the zone, as [zero_stack] does. *)
  Lemma wp_store_zone_z_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst z
      p g b e a ea (imm : Z) (mshwmb_v mshwm_v : Z) dq q :
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
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ WInt z ∗
        mshwmb ↦ₜ mshwmb_v ∗
        mshwm ↦ₜ hwm_after ea mshwmb_v mshwm_v ∗
        deref_res π q }}}.
  Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hdst φ)
      "(HPC & Hi & >Hdst & [%zc Hcell] & Hb & Hh & Hdw) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_zone_next with "[$HPC $Hi $Hcell $Hb $Hh $Hdw $Hmap]");
      [exact Hdecode | exact Hvpc
      | rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L; set_solver+
      | by rewrite llookup_reg_not_cnull // lookup_singleton_eq | exact Hadd | exact Hwa | exact Hwb
      | done | by apply incrementPC_add |].
    iIntros "!> (HPC & Hi & Hea & Hb & Hh & Hdw & Hmap)".
    iEval (rewrite (lstore_word_canStore _ (lword_of_word (WInt z))
                      (writeAllowed_canStore_int _ _ Hwa))) in "Hea".
    iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** A store of a register to a cell of the zone. *)
  Lemma wp_store_zone_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_π π pc_a' w dst src wsrc
      p g b e a ea (imm : Z) (mshwmb_v mshwm_v : Z) dq q :
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
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v ∗
        deref_res π q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ wsrc ∗
        dst ↦ᵣ Cap p g b e a @@? π ∗
        ea ↦ₐ lstore_word p wsrc ∗
        mshwmb ↦ₜ mshwmb_v ∗
        mshwm ↦ₜ hwm_after ea mshwmb_v mshwm_v ∗
        deref_res π q }}}.
  Proof.
    rewrite deref_res_witness.
    generalize (deref_id_witness_of π q). generalize (deref_witness_of π q).
    intros dw <-.
    iIntros (Hsh Hdecode Hvpc Hpca' Hwa Hwb Hadd Hsrc Hdst φ)
      "(HPC & Hi & >Hsrc & >Hdst & [%zc Hcell] & Hb & Hh & Hdw) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hne]".
    iApply (wp_store_zone_next with "[$HPC $Hi $Hcell $Hb $Hh $Hdw $Hmap]");
      [exact Hdecode | exact Hvpc
      | rewrite /regs_of /operands_of /regs_of_argument !dom_insert_L; set_solver+
      | by rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq
      | exact Hadd | exact Hwa | exact Hwb
      | by rewrite /lword_of_argument llookup_reg_not_cnull // lookup_insert_eq
      | by apply incrementPC_add |].
    iIntros "!> (HPC & Hi & Hea & Hb & Hh & Hdw & Hmap)".
    iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
    iApply "Hφ". iFrame.
  Qed.


  (** ** Accesses to MSHWM and MSHWMB *)

  (** [csrr dst, mshwm]: reads the integer [mshwm_v] of MSHWM. *)
  Lemma wp_csrr_mshwm E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst (mshwm_v : Z) dq :
    decodeInstrW w.(lw) = SpecialRW dst mshwm (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ mshwm ↦ₜ mshwm_v }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WInt mshwm_v ∗
        mshwm ↦ₜ mshwm_v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst φ) "(>HPC & >Hpc_a & >Hdst & >Hh) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|done|solve_writes_mshwmb|].
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mshwm_agree with "Hsr Hh") as %<-.
    pose proof (ls_join_mshwm lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & Hrel).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    destruct (decide (dst = cnull)) as [Hc|_]; first done. cbn in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst
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

  (** [csrr dst, mshwmb]: reads the integer [mshwmb_v] of MSHWMB. *)
  Lemma wp_csrr_mshwmb E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst (mshwmb_v : Z) dq :
    decodeInstrW w.(lw) = SpecialRW dst mshwmb (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ mshwmb ↦ₜ mshwmb_v }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ WInt mshwmb_v ∗
        mshwmb ↦ₜ mshwmb_v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst φ) "(>HPC & >Hpc_a & >Hdst & >Hb) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|done|solve_writes_mshwmb|].
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mshwmb_agree with "Hsr Hb") as %<-.
    pose proof (ls_join_mshwmb lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & Hrel).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    destruct (decide (dst = cnull)) as [Hc|_]; first done. cbn in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst
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

  (** [csrw mshwm, src] writing [x]: the zone covers [MSHWMB, x), with the
      cells of [l] above MSHWM. *)
  #[local] Lemma wp_csrw_mshwm_cells E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc
      (mshwmb_v mshwm_v : Z) (l : list Addr) (zs : list Z) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    (∀ a : Addr, (mshwmb_v ≤ a < get_a vsrc.(lw))%Z → (a < mshwm_v)%Z ∨ a ∈ l) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v ∗
        ([∗ list] a; z ∈ l; zs, zone_cell_v a z) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ mshwmb_v ∗
        mshwm ↦ₜ get_a vsrc.(lw) ∗
        ([∗ list] a; z ∈ l; zs, zone_cell_v a z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hcover φ)
      "(>HPC & >Hpc_a & >Hsrc & >Hb & >Hh & Hcells) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap");
      [rewrite Hinstr; by apply sw_of_none|done|solve_writes_mshwmb|].
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    (* The write to MSHWM is not an instruction of the window: the window is
       closed, and the cover base is MSHWMB. *)
    assert (ls_pend lsreg = None) as Hpend.
    { destruct Hwin as [? | [(? & ? & ? & Heq) | Heq] ]; first done;
        rewrite Hinstr in Heq; [discriminate | by vm_compute in Heq]. }
    iDestruct (sys_interp_hwm_open with "Hsr")
      as "(Hmshwmb_a & Hmshwm_a & Hpend_si & Hlent_a & Hzone & Hclose)".
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
    iDestruct (mshwm_agree with "Hmshwm_a Hh") as %Hh. subst mshwmb_v mshwm_v.
    iEval (rewrite Hpend /hc_of /=) in "Hzone". iNamed "Hzone".
    iAssert (⌜∀ a : Addr, a ∈ l → a ∈ zone⌝)%I as %Hcells.
    { iIntros (a Ha). apply list_elem_of_lookup in Ha as [k Hk].
      iDestruct (big_sepL2_length with "Hcells") as %Hlen.
      destruct (lookup_lt_is_Some_2 zs k) as [z Hz].
      { rewrite -Hlen. by eapply lookup_lt_Some. }
      iDestruct (big_sepL2_lookup with "Hcells") as "Hcell"; [exact Hk | exact Hz |].
      iDestruct (zone_cell_v_unfold with "Hcell") as "[Htok _]".
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
    assert (erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r (<[mshwm := WInt x]> psr) m st td)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_win (ls_set_hwm (ls_set_hwmb lsreg (ls_hwmb lsreg)) x)
                          (ls_pend lsreg) (ls_lent lsreg))) lmem) as Her1.
    { rewrite ls_join_set_win ls_join_set_hwm ls_join_set_hwmb
        (insert_id (ls_join lsreg) mshwmb); last apply ls_join_mshwmb.
      apply erasure_insert_sreg; [done | apply reg_word_ok_int | by intros | done |].
      apply reg_phys_lword_of_word. }
    iMod (mshwm_update _ _ x with "Hmshwm_a Hh") as "[Hmshwm_a Hh]".
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a
                  [Hzone_auth Hzone_cells Hlent_cells]").
    { rewrite Hpend /hc_of /=. iExists zone. iFrame "Hzone_auth Hzone_cells Hlent_cells". iPureIntro.
      intros a Ha. destruct (Hcover a Ha) as [Hlt | Hal].
      - apply Hzone_cover. lia.
      - apply elem_of_union_l. by apply Hcells. }
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
    iApply (instr_close_kept_trans _ _ _ _
              (sys_kept_insert_sreg _ _ _ _ _ _ mshwm (WInt x) ltac:(done) ltac:(done))).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
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
  Lemma wp_csrw_mshwm E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc (mshwmb_v mshwm_v : Z) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    (mshwmb_v ≤ get_a vsrc.(lw) ≤ mshwm_v)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ mshwmb_v ∗
        mshwm ↦ₜ get_a vsrc.(lw) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hle φ) "(HPC & Hpc_a & Hsrc & Hb & Hh) Hφ".
    iApply (wp_csrw_mshwm_cells _ _ _ _ _ _ _ _ _ _ _ mshwmb_v mshwm_v [] []
             with "[$HPC $Hpc_a $Hsrc $Hb $Hh]"); try done.
    { intros a Ha. left. lia. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & Hb & Hh & _)". iApply "Hφ". iFrame.
  Qed.

  (** [csrw mshwm, src] with a value below MSHWMB: the zone needs to cover
      nothing. *)
  Lemma wp_csrw_mshwm_below E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc (mshwmb_v mshwm_v : Z) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    (get_a vsrc.(lw) < mshwmb_v)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ mshwmb_v ∗
        mshwm ↦ₜ get_a vsrc.(lw) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hlt φ) "(HPC & Hpc_a & Hsrc & Hb & Hh) Hφ".
    iApply (wp_csrw_mshwm_cells _ _ _ _ _ _ _ _ _ _ _ mshwmb_v mshwm_v [] []
             with "[$HPC $Hpc_a $Hsrc $Hb $Hh]"); try done.
    { intros a Ha. lia. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & Hb & Hh & _)". iApply "Hφ". iFrame.
  Qed.

  (** [csrw mshwm, src] raising MSHWM to [x], at least [lo], the larger of
      MSHWMB and MSHWM: the cells of [lo, x) join the cover. *)
  Lemma wp_csrw_mshwm_raise E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc
      (mshwmb_v mshwm_v : Z) (lo x : Addr) (zs : list Z) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = x →
    (Z.max mshwmb_v mshwm_v = lo)%Z →
    (lo ≤ x)%Z →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ mshwmb_v ∗
        ▷ mshwm ↦ₜ mshwm_v ∗
        ([∗ list] a; z ∈ finz.seq_between lo x; zs, zone_cell_v a z) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ mshwmb_v ∗
        mshwm ↦ₜ x ∗
        ([∗ list] a; z ∈ finz.seq_between lo x; zs, zone_cell_v a z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hx Hlo Hle φ)
      "(HPC & Hpc_a & Hsrc & Hb & Hh & Hcells) Hφ".
    iApply (wp_csrw_mshwm_cells _ _ _ _ _ _ _ _ _ _ _ mshwmb_v mshwm_v (finz.seq_between lo x) zs
             with "[$HPC $Hpc_a $Hsrc $Hb $Hh $Hcells]"); try done.
    { intros a Ha. rewrite Hx in Ha. destruct (decide (a < mshwm_v)%Z) as [Hlt|Hge]; first by left.
      right. apply elem_of_finz_seq_between. solve_addr. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & Hb & Hh & Hcells)". rewrite Hx.
    iApply "Hφ". iFrame.
  Qed.

  (** [csrw mshwmb, src] at a user thread: MSHWMB is written with its own
      value, the thread's stack base [mshwmb_v]. *)
  Lemma wp_csrw_mshwmb E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src vsrc (mshwmb_v : Addr) dq :
    kind_of th = UserK →
    decodeInstrW w.(lw) = SpecialRW cnull mshwmb (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_a vsrc.(lw) = mshwmb_v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ mshwmb_v }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        src ↦ᵣ vsrc ∗
        mshwmb ↦ₜ mshwmb_v }}}.
  Proof.
    iIntros (Hk Hinstr Hvpc Hxsr Hpca' Hsrc Hlo φ)
      "(>HPC & >Hpc_a & >Hsrc & >Hb) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    assert (sw_of (kind_of th) (decodeInstrW w.(lw)) = None) as Hsw.
    { rewrite Hinstr. by apply sw_of_none. }
    iApply (wp_instr_step_hwmb_user with "HPC Hpc_a Hmap"); [done | done |].
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct "Hwin_si" as "(Hhalf & Hlent0 & #Hbase)".
    iDestruct (sys_interp_pend_half_agree with "Hsr Hhalf") as %Hpend.
    iDestruct (sys_interp_hwm_open with "Hsr")
      as "(Hmshwmb_a & Hmshwm_a & Hpend_si & Hlent_a & Hzone & Hclose)".
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhb.
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her (ls_join_mshwmb lsreg)) as Hpb.
    cbn in Hpb.
    assert (({[src := vsrc]} : LReg) !!ₗ src = Some vsrc) as Hv.
    { rewrite llookup_reg_not_cnull //. by rewrite lookup_singleton_eq. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep.
    rewrite Hxsr Hpb /= in Hstep.
    repeat (case_decide; try congruence).
    rewrite Hrs /= get_a_and_tag Hlo in Hstep.
    assert (erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r (<[mshwmb := WInt mshwmb_v]> psr) m st td)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_win (ls_set_hwm (ls_set_hwmb lsreg mshwmb_v) (ls_hwm lsreg))
                          (ls_pend lsreg) (ls_lent lsreg))) lmem) as Her1.
    { rewrite ls_join_set_win ls_join_set_hwm ls_join_set_hwmb insert_id;
        last by rewrite lookup_insert_ne // ls_join_mshwm.
      apply erasure_insert_sreg; [done | apply reg_word_ok_int | by intros | done |].
      apply reg_phys_lword_of_word. }
    iMod (mshwmb_update _ _ mshwmb_v with "Hmshwmb_a Hb") as "[Hmshwmb_a Hb]".
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a [Hzone]").
    { rewrite -Hhb. iExact "Hzone". }
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
    rewrite /nextPC in Hu Hstep. rewrite /update_sreg /= in Hstep.
    rewrite Hu in Hstep. simplify_eq.
    iMod (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _
      (λ v, φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v))
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hclose Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb]")
      as "(%Hkept & HSI & HΦ)".
    { exact Her1. }
    { by rewrite /nextPC Hu. }
    { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
    { intros Hi'. rewrite /incrementPC in Hi. congruence. }
    { iIntros (lpc'' retv [-> ->]) "HPC Hmap". rewrite tval_sw_none //. iApply "Hφ". iFrame.
      iApply (regs_of_map_1 with "Hmap"). }
    iModIntro. iFrame "HSI HΦ". iSplit.
    { iPureIntro. eapply sys_kept_trans; last exact Hkept.
      by apply sys_kept_insert_sreg. }
    (* The physical MSHWMB keeps its value, the thread's stack base: the
       window clause is kept. *)
    rewrite /hwm_win_si. iFrame "Hhalf Hlent0".
    rewrite /phys_mshwmb /= lookup_insert_eq /=.
    iEval (rewrite Hpb /= Hhb) in "Hbase". iExact "Hbase".
  Qed.

  (** ** The HWM restore window of the context-switch thread *)

  (** The opening write [csrw mshwm, ra] at the context-switch thread,
      followed by the load [pc_a'] of the target base from [csp] and the
      closing write [a3]: MSHWM receives the target's value, the window
      opens at the target base [hbT], and the halves lent from now on are
      [L'] (with [swap], the halves [L] leave and [L'] come in). MSHWMB
      keeps its value until the close. The physical copy of [csp] has its
      tag: a capability without a heap base is never stripped. *)
  Lemma wp_csrw_mshwm_open E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' a3 w w2 w3 vsrc wcsp whb
      (off : Z) (ea : Addr) (hbP hP hbT : Z) (L L' : gset Addr) (swap : bool) dq dq' :
    kind_of th = CtxK →
    decodeInstrW w.(lw) = SpecialRW cnull mshwm (inr cra) →
    decodeInstrW w2.(lw) = CLoad cra csp off →
    decodeInstrW w3.(lw) = csrw_mshwmb_ra →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    (pc_a' + 1)%a = Some a3 →
    (a3 < pc_e)%a →
    (* the load at [pc_a'] cannot fault *)
    csp_cap_load_ok wcsp off ea →
    heap_cap_base wcsp.(lw) = None →
    (* the target covers the new range with the halves lent from now on *)
    zone_covers hbT (get_a vsrc.(lw)) L' →
    (swap = false → L' = L) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        pc_a' ↦ₐ□ w2 ∗
        a3 ↦ₐ□ w3 ∗
        ▷ cra ↦ᵣ vsrc ∗
        ▷ csp ↦ᵣ wcsp ∗
        ▷ ea ↦ₐ{dq'} whb ∗
        ▷ mshwmb ↦ₜ hbP ∗
        ▷ mshwm ↦ₜ hP ∗
        ▷ pend_frag None ∗
        ▷ lent_frag L ∗
        ▷ (if swap then zone_halves L' else True) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        cra ↦ᵣ vsrc ∗
        csp ↦ᵣ wcsp ∗
        ea ↦ₐ{dq'} whb ∗
        mshwmb ↦ₜ hbP ∗
        mshwm ↦ₜ get_a vsrc.(lw) ∗
        pend_frag (Some hbT) ∗
        lent_frag L' ∗
        (if swap then zone_halves L else True) }}}.
  Proof.
    iIntros (Hk Hinstr Hdec2 Hdec3 Hvpc Hxsr Hpca' Ha3 Ha3e Hcsp_ok Hcsp_heap Hcov Hswap φ)
      "(>HPC & >Hpc_a & #Hw2 & #Hw3 & >Hsrc & >Hcsp & >Hea & >Hb & >Hh & >Hpend & >Hlent & >Hin) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hcsp") as "[Hmap %Hne]".
    iApply (wp_instr_step_win with "HPC Hpc_a Hmap Hpend"); [done | done |].
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct "Hwin_si" as (o) "[Hcl _]".
    iDestruct (pend_cl_frag_agree with "Hcl Hpend") as %->.
    iDestruct (gen_heap_valid with "Hm Hea") as %Hea.
    iDestruct (sys_interp_hwm_open with "Hsr")
      as "(Hmshwmb_a & Hmshwm_a & Hpend_si & Hlent_a & Hzone & Hclose)".
    iDestruct (pend_si_agree with "Hpend_si Hcl") as %Hpend.
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhbp.
    iDestruct (mshwm_agree with "Hmshwm_a Hh") as %Hhp.
    iDestruct (lent_agree with "Hlent_a Hlent") as %HL.
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her (ls_join_mshwm lsreg)) as Hph.
    cbn in Hph.
    assert ((<[cra:=vsrc]> (<[csp:=wcsp]> ∅) : LReg) !!ₗ cra = Some vsrc) as Hv.
    { by rewrite llookup_reg_not_cnull. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep.
    rewrite Hxsr Hph /= in Hstep.
    repeat (case_decide; try congruence); first done.
    rewrite Hrs /= get_a_and_tag in Hstep.
    set (x := get_a vsrc.(lw)) in *.
    assert (erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r (<[mshwm := WInt x]> psr) m st td)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_win (ls_set_hwm (ls_set_hwmb lsreg (ls_hwmb lsreg)) x)
                          (Some hbT) L')) lmem) as Her1.
    { rewrite ls_join_set_win ls_join_set_hwm ls_join_set_hwmb
        (insert_id (ls_join lsreg) mshwmb); last apply ls_join_mshwmb.
      apply erasure_insert_sreg; [done | apply reg_word_ok_int | by intros | done |].
      apply reg_phys_lword_of_word. }
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
    rewrite /nextPC in Hu Hstep. rewrite /update_sreg /= in Hstep.
    rewrite Hu in Hstep. simplify_eq.
    rewrite /advancePC /= Hpca' in Hu.
    assert (pc' = Cap pc_p pc_g pc_b pc_e pc_a') as -> by (inversion Hu; done).
    (* MSHWM receives the target's value; the window opens at [hbT], with
       the halves [L'] lent. *)
    iMod (mshwm_update _ _ x with "Hmshwm_a Hh") as "[Hmshwm_a Hh]".
    iEval (rewrite Hpend) in "Hpend_si".
    iMod (pend_update _ (Some hbT) with "Hpend_si Hcl Hpend") as "(Hpend_si & Hcl & Hpend)".
    iMod (lent_update _ _ L' with "Hlent_a Hlent") as "[Hlent_a Hlent]".
    iEval (rewrite Hpend /hc_of /=) in "Hzone". iNamed "Hzone".
    iAssert (zone_halves L' ∗ (if swap then zone_halves (ls_lent lsreg) else True))%I
      with "[Hin Hlent_cells]" as "[Hlent_cells Hout]".
    { destruct swap; first iFrame. rewrite Hswap //. iFrame. }
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a
                  [Hzone_auth Hzone_cells Hlent_cells]").
    { rewrite /hc_of /=. iExists zone. iFrame "Hzone_auth Hzone_cells Hlent_cells". iPureIntro.
      intros a Ha. apply elem_of_union_r. by apply Hcov. }
    (* The window's facts: the PC at [pc_a'], the bounds over [a3], and a load
       from [csp] that succeeds. *)
    assert (pc_in_window (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a') r (<[mshwm:=WInt x]> psr) m st td)
              pc_a' a3) as Hpc_win.
    { destruct (a3 + 1)%a as [a4|] eqn:Ha4; last solve_addr.
      inversion Hvpc as [? ? ? ? ? Hin Hex]; subst.
      exists pc_p, pc_g, pc_b, pc_e, pc_a', a4. split_and!; try done; first by left.
      - constructor; [solve_addr | done].
      - constructor; [solve_addr | done]. }
    destruct Hcsp_ok as (p & g & b & e & a & Hwcsp & Hra & Hea_off & Hwb).
    assert (lreg !! csp = Some wcsp) as Hlcsp.
    { eapply lookup_weaken; last exact Hlregs.
      by rewrite lookup_insert_ne // lookup_insert_eq. }
    (* The physical [csp] is the logical one: without a heap base, it is
       neither stale nor stripped. *)
    assert (r !!ᵣ csp = Some (Cap p g b e a)) as Hrcsp.
    { assert ((<[cra:=vsrc]> (<[csp:=wcsp]> ∅) : LReg) !!ₗ csp = Some wcsp) as Hv'.
      { by rewrite llookup_reg_not_cnull. }
      destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv') as (s' & Hrs' & [Hcopy _]).
      rewrite Hrs'. destruct Hcopy as [-> | [_ Hstrip] ]; first by rewrite Hwcsp.
      exfalso. destruct Hstrip as [ [ (ι & xe & Hι & Hxe & _) _] | [_ Hbase] ].
      - destruct (er_reg_words _ _ _ _ _ _ _ Her _ _ Hlcsp) as [Hprov _].
        apply withinBounds_le_addr in Hwb.
        destruct (Hprov ι b e) as (xe' & Hxe' & Hb & He);
          [by rewrite Hwcsp | by rewrite Hwcsp | solve_addr | done |].
        pose proof (reg_ok_heap _ _ _ (er_registry _ _ _ _ _ _ _ Her) ι xe' b Hxe') as Hheap.
        rewrite (memory_cap_bounds_heap_cap_base _ b e) in Hcsp_heap; [done | by rewrite Hwcsp |].
        apply Hheap. rewrite /re_covers. solve_addr.
      - rewrite Hcsp_heap in Hbase. by destruct Hbase. }
    assert (is_Some (m !! ea)) as [wm Hwm].
    { apply elem_of_dom. rewrite -(er_mem_dom _ _ _ _ _ _ _ Her). by apply elem_of_dom. }
    assert (csp_load_ok (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a') r (<[mshwm:=WInt x]> psr) m st td)
              off) as Hcsp_load.
    { exists p, g, b, e, a, ea, wm. cbn. split_and!; try done.
      - eapply mem_avoids_mmio_lookup; [apply (er_mmio _ _ _ _ _ _ _ Her) | exact Hwm].
      - intros base Hbase.
        apply (reg_ok_shadow _ _ _ (er_registry _ _ _ _ _ _ _ Her)).
        revert Hbase. rewrite /heap_cap_base. destruct (memory_cap_base wm) as [f|]; last done.
        destruct (is_heap_address f) eqn:Hf; last done. by intros [= <-]. }
    iMod (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _
      (λ v, φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v))
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hclose Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb Hh Hpend Hlent Hout Hea]")
      as "(%Hkept & HSI & HΦ)".
    { exact Her1. }
    { rewrite /nextPC /advancePC /= Hpca' //. }
    { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
    { intros Hi'. rewrite /incrementPC in Hi. congruence. }
    { iIntros (lpc'' retv [-> ->]) "HPC Hmap".
      rewrite tval_sw_none; last by rewrite Hinstr; apply sw_of_none.
      iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hcsp]"; first done.
      iApply "Hφ". iFrame. }
    iModIntro. iFrame "HSI HΦ". iSplit.
    { iPureIntro. eapply sys_kept_trans; last exact Hkept.
      by apply sys_kept_insert_sreg. }
    iExists (Some hbT). iFrame "Hcl".
    iExists pc_a', a3, off, w2, w3. iFrame "#". iPureIntro. done.
  Qed.

  (** The closing write [csrw mshwmb, ra] at the context-switch thread:
      MSHWMB receives the cover base [hbT], and the window closes. No
      halves move. *)
  Lemma wp_csrw_mshwmb_close E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w vsrc (hbP hbT : Z) dq :
    kind_of th = CtxK →
    decodeInstrW w.(lw) = csrw_mshwmb_ra →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    get_a vsrc.(lw) = hbT →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ cra ↦ᵣ vsrc ∗
        ▷ mshwmb ↦ₜ hbP ∗
        ▷ pend_frag (Some hbT) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        cra ↦ᵣ vsrc ∗
        mshwmb ↦ₜ hbT ∗
        pend_frag None }}}.
  Proof.
    iIntros (Hk Hinstr Hvpc Hxsr Hpca' Hhb φ) "(>HPC & >Hpc_a & >Hsrc & >Hb & >Hpend) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    assert (sw_of (kind_of th) (decodeInstrW w.(lw)) = None) as Hsw.
    { rewrite Hinstr. by apply sw_of_none. }
    iApply (wp_instr_step_win with "HPC Hpc_a Hmap Hpend"); [done | done |].
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct "Hwin_si" as (o) "[Hcl _]".
    iDestruct (pend_cl_frag_agree with "Hcl Hpend") as %->.
    iDestruct (sys_interp_hwm_open with "Hsr")
      as "(Hmshwmb_a & Hmshwm_a & Hpend_si & Hlent_a & Hzone & Hclose)".
    iDestruct (pend_si_agree with "Hpend_si Hcl") as %Hpend.
    iDestruct (mshwmb_agree with "Hmshwmb_a Hb") as %Hhbp.
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her (ls_join_mshwmb lsreg)) as Hpb.
    cbn in Hpb.
    assert (({[cra := vsrc]} : LReg) !!ₗ cra = Some vsrc) as Hv.
    { by rewrite llookup_reg_not_cnull. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep.
    rewrite Hxsr Hpb /= in Hstep.
    repeat (case_decide; try congruence); first done.
    rewrite Hrs /= get_a_and_tag Hhb in Hstep.
    assert (erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r (<[mshwmb := WInt hbT]> psr) m st td)
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg
              (ls_join (ls_set_win (ls_set_hwm (ls_set_hwmb lsreg hbT) (ls_hwm lsreg))
                          None (ls_lent lsreg))) lmem) as Her1.
    { rewrite ls_join_set_win ls_join_set_hwm ls_join_set_hwmb insert_id;
        last by rewrite lookup_insert_ne // ls_join_mshwm.
      apply erasure_insert_sreg; [done | apply reg_word_ok_int | by intros | done |].
      apply reg_phys_lword_of_word. }
    iMod (mshwmb_update _ _ hbT with "Hmshwmb_a Hb") as "[Hmshwmb_a Hb]".
    iEval (rewrite Hpend) in "Hpend_si".
    iMod (pend_update _ None with "Hpend_si Hcl Hpend") as "(Hpend_si & Hcl & Hpend)".
    (* The cover base was the target [hbT]; it is now MSHWMB, at [hbT]. *)
    iSpecialize ("Hclose" with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a [Hzone]").
    { iEval (rewrite Hpend /hc_of /=) in "Hzone". iExact "Hzone". }
    assert (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) =
              Some (Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hi.
    { by apply incrementPC_add. }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
    rewrite /nextPC in Hu Hstep. rewrite /update_sreg /= in Hstep.
    rewrite Hu in Hstep. simplify_eq.
    iMod (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _
      (λ v, φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v))
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hclose Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hb Hpend]")
      as "(%Hkept & HSI & HΦ)".
    { exact Her1. }
    { by rewrite /nextPC Hu. }
    { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq. done. }
    { intros Hi'. rewrite /incrementPC in Hi. congruence. }
    { iIntros (lpc'' retv [-> ->]) "HPC Hmap". rewrite tval_sw_none //. iApply "Hφ". iFrame.
      iApply (regs_of_map_1 with "Hmap"). }
    iModIntro. iFrame "HSI HΦ". iSplit.
    { iPureIntro. eapply sys_kept_trans; last exact Hkept.
      by apply sys_kept_insert_sreg. }
    iExists None. by iFrame "Hcl".
  Qed.

End hwm.
