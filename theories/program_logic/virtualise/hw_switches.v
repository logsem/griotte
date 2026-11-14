From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra resource_maps.
From griotte Require Export pool hw_instance.

(** * The switches between threads, as ghost updates

    The interrupt, yield and exit hand-ins move the running user thread's
    state interpretation to the context-switch thread (with a copy of the
    registers) and its authorities to its slot; the hand-back at
    [ResumedV] swaps the authorities back; a tick keeps the state
    interpretation; a step of the context-switch thread keeps its resume
    window. No hardware step. *)

(** * Facts on the machine *)

Section machine_facts.
  Context `{MP : MachineParameters}.

  Lemma reg_enter_irq c σ : reg (enter_irq c σ) = reg σ.
  Proof. done. Qed.

  Lemma shadowtbl_enter_irq c σ : shadowtbl (enter_irq c σ) = shadowtbl σ.
  Proof. done. Qed.

  (** The logical system registers after interrupt entry, from the joined
      ones at InterruptEnabled. *)
  Lemma lsregs_enter_irq_join c σ lpc lsh vm mshwmb_v mshwm_v mpie :
    mie_st σ = InterruptEnabled →
    lsregs_enter_irq c σ lpc (lsregs_join lsh vm mshwmb_v mshwm_v InterruptEnabled mpie) =
    lsregs_join
      (<[mtval := lword_of_word (WInt MTVAL_NONE)]>
         (<[mcause := lword_of_word (WInt c)]>
            (<[mepcc := lword_of_word lpc.(lw)]> lsh)))
      vm mshwmb_v mshwm_v InterruptDisabled InterruptEnabled.
  Proof.
    intros Hen. apply map_eq. intros i.
    rewrite /lsregs_enter_irq /lsregs_join mie_old_st Hen.
    destruct i; by simplify_map_eq.
  Qed.

  (** A total register map contained in another is equal to it. *)
  Lemma regs_total_eq (l l' : LReg) :
    dom l' = all_registers_s → l' ⊆ l → l' = l.
  Proof.
    intros Hdom Hsub. apply map_eq. intros r. destruct (l' !! r) eqn:Hr.
    - symmetry. by eapply lookup_weaken.
    - exfalso. apply not_elem_of_dom in Hr. rewrite Hdom in Hr.
      apply Hr, all_registers_s_correct.
  Qed.
End machine_facts.

(** * The register copy *)
Section regs_copy.
  Context {Σ : gFunctors} `{!gen_heapGS RegName LWord Σ}.

  Lemma regs_copy_gen (l1 : LReg) : ∀ (l0 h : LReg),
    dom l0 = dom l1 →
    gen_heap_interp h -∗
    ([∗ map] r ↦ w ∈ l0, r ↦ᵣ w)
    ==∗
    gen_heap_interp (l1 ∪ h) ∗
    ([∗ map] r ↦ w ∈ l1, r ↦ᵣ w).
  Proof.
    induction l1 as [|i x m Hi IH] using map_ind; intros l0 h Hdom.
    - rewrite dom_empty_L in Hdom. apply dom_empty_inv_L in Hdom as ->.
      iIntros "Hh _ !>". rewrite map_empty_union big_sepM_empty. by iFrame.
    - assert (is_Some (l0 !! i)) as [y Hy].
      { apply elem_of_dom. rewrite Hdom dom_insert_L. set_solver. }
      iIntros "Hh Hl0". rewrite (big_sepM_delete _ l0 i y) //.
      iDestruct "Hl0" as "[Hi Hl0]".
      iMod (IH (delete i l0) h with "Hh Hl0") as "[Hh Hm]".
      { rewrite dom_delete_L Hdom dom_insert_L.
        apply not_elem_of_dom in Hi. set_solver. }
      iMod (gen_heap_update _ i _ x with "Hh Hi") as "[Hh Hi]".
      iModIntro. rewrite -insert_union_l big_sepM_insert //. iFrame.
  Qed.

  Lemma regs_copy (l0 l1 : LReg) :
    dom l0 = dom l1 →
    gen_heap_interp l0 -∗
    ([∗ map] r ↦ w ∈ l0, r ↦ᵣ w)
    ==∗
    gen_heap_interp l1 ∗
    ([∗ map] r ↦ w ∈ l1, r ↦ᵣ w).
  Proof.
    iIntros (Hdom) "Hh Hl0".
    iMod (regs_copy_gen l1 l0 l0 Hdom with "Hh Hl0") as "[Hh $]".
    assert (l1 ∪ l0 = l1) as ->; last done.
    apply map_eq. intros r. destruct (l1 !! r) eqn:Hr.
    - by erewrite lookup_union_Some_l.
    - rewrite lookup_union_r //. apply not_elem_of_dom. rewrite Hdom. by apply not_elem_of_dom.
  Qed.
End regs_copy.

(** * The high-water-mark ghosts across a switch

    At a hand-in, the parked user thread's pair and zone authority go to
    its slot at rest, and the halves of its zone to the context-switch
    thread's lent set; at the hand-back, the reverse. Generic in one
    instance of the ghosts. *)
Section hwm_moves.
  Context `{!gen_heapGS Addr LWord Σ, !hwmG Σ}.

  (** A user thread's part, out of its state interpretation and its window
      clause: its authorities at rest, its zone with the cover. *)
  #[local] Lemma hwm_user_out mshwmb_v mshwm_v o L :
    mshwmb_auth mshwmb_v -∗ mshwm_auth mshwm_v -∗ pend_si o -∗ lent_auth L -∗
    hwm_zone (hc_of mshwmb_v o) mshwm_v L -∗
    pend_half None -∗ lent_frag ∅ -∗
    ∃ zn,
      ⌜zone_covers mshwmb_v mshwm_v zn⌝ ∗
      (mshwmb_auth mshwmb_v ∗ mshwm_auth mshwm_v ∗ zone_auth zn ∗ hwm_rest) ∗
      zone_halves zn.
  Proof.
    iIntros "Hb Hh Hpsi Hla Hzone Hph Hlf".
    iDestruct (pend_si_half_agree with "Hpsi Hph") as %->.
    iDestruct (lent_agree with "Hla Hlf") as %->.
    iNamed "Hzone". iExists zone. iFrame "Hb Hh Hzone_auth Hzone_cells Hla Hlf".
    iSplit.
    { iPureIntro. intros a Ha. specialize (Hzone_cover a Ha). set_solver. }
    rewrite pend_full_split. iFrame "Hpsi". iApply (pend_half_split with "Hph").
  Qed.

  (** The context-switch thread's part at a hand-in: its pair at the
      parked thread's, the parked thread's halves lent, the window closed.
      [zc] is its own zone. *)
  #[local] Lemma hwm_ctx_in mshwmb_v mshwm_v zc zn :
    zone_covers mshwmb_v mshwm_v zn →
    mshwmb_auth mshwmb_v -∗ mshwm_auth mshwm_v -∗ zone_auth zc -∗ hwm_rest -∗
    zone_halves zc -∗ zone_halves zn
    ==∗
    (mshwmb_auth mshwmb_v ∗ mshwm_auth mshwm_v ∗ pend_si None ∗ lent_auth zn ∗
     hwm_zone (hc_of mshwmb_v None) mshwm_v zn) ∗
    pend_cl None ∗ pend_frag None ∗ lent_frag zn.
  Proof.
    iIntros (Hcov) "Hb Hh Hza (Hla & Hlf & Hp) Hzc Hzn".
    iMod (lent_update _ _ zn with "Hla Hlf") as "[Hla Hlf]".
    iDestruct (pend_full_split with "Hp") as "(Hpsi & Hpcl & Hpf)".
    iModIntro. iFrame "Hb Hh Hpsi Hla Hpcl Hpf Hlf". iExists zc. iFrame "Hza Hzc Hzn".
    iPureIntro. intros a Ha. apply Hcov in Ha. set_solver.
  Qed.

  (** The context-switch thread's part at the hand-back: the window is
      closed and its lent set is the resumed thread's zone [L']; its
      authorities at rest, its own zone, and the lent halves come out. *)
  #[local] Lemma hwm_ctx_out mshwmb_v mshwm_v o L o' L' :
    pend_si o -∗ lent_auth L -∗ hwm_zone (hc_of mshwmb_v o) mshwm_v L -∗
    pend_cl o' -∗ pend_frag None -∗ lent_frag L'
    ==∗
    ⌜L = L'⌝ ∗ hwm_rest ∗
    ∃ zc, zone_auth zc ∗ zone_halves zc ∗ zone_halves L.
  Proof.
    iIntros "Hpsi Hla Hzone Hpcl Hpf Hlf".
    iDestruct (pend_si_frag_agree with "Hpsi Hpf") as %->.
    iDestruct (pend_cl_frag_agree with "Hpcl Hpf") as %->.
    iDestruct (lent_agree with "Hla Hlf") as %->.
    iMod (lent_update _ _ ∅ with "Hla Hlf") as "[Hla Hlf]".
    iNamed "Hzone". iModIntro. iSplit; first done.
    iSplitL "Hla Hlf Hpsi Hpcl Hpf".
    { iFrame "Hla Hlf". rewrite pend_full_split. iFrame. }
    iExists zone. iFrame.
  Qed.

  (** A user thread's part at the hand-back: its authorities at rest and
      its zone [zn] with its halves give its state interpretation's part
      and its window clause's. *)
  #[local] Lemma hwm_user_in mshwmb_v mshwm_v zn :
    zone_covers mshwmb_v mshwm_v zn →
    zone_auth zn -∗ hwm_rest -∗ zone_halves zn -∗
    pend_si None ∗ lent_auth ∅ ∗ hwm_zone (hc_of mshwmb_v None) mshwm_v ∅ ∗
    pend_half None ∗ lent_frag ∅.
  Proof.
    iIntros (Hcov) "Hza (Hla & Hlf & Hp) Hzn".
    iDestruct (pend_full_split with "Hp") as "(Hpsi & Hpcl & Hpf)".
    iFrame "Hpsi Hla Hlf". iSplitL "Hza Hzn".
    { iExists zn. iFrame "Hza Hzn". rewrite /zone_halves big_sepS_empty. iSplit; last done.
      iPureIntro. intros a Ha. apply Hcov in Ha. set_solver. }
    iApply pend_half_split. iFrame.
  Qed.
End hwm_moves.

(** The window clause is kept by a tick, which changes only the time
    devices. *)
Lemma hwm_win_si_tick `{MP : MachineParameters} {Σ} {ceriseg : ceriseG Σ} k σ :
  hwm_win_si k σ ⊢ hwm_win_si k (tick σ).
Proof.
  destruct k; cbn [hwm_win_si].
  - by rewrite /phys_mshwmb tick_sreg.
  - iIntros "(%o & Hpcl & Hw)". iExists o. iFrame "Hpcl". destruct o; last done.
    iNamed "Hw". iExists a2, a3, off, w2, w3. by iFrame "∗ # %".
Qed.

Section hw_switches.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}
    {CSL : ContextSwitchLayout Σ CL CR}.

  #[local] Notation posture_of x :=
    (posture_res_gen (ceriseg := ceriseG_of x) (th := x) (CL := CL x) (CR := CR x)).
  #[local] Notation part_of x :=
    (@posture_part Σ MP (ceriseG_of x) x (CL x) (CR x)).
  #[local] Notation hwmG_of x := (@cerise_hwmG Σ (ceriseG_of x)).
  #[local] Notation memG_of x := (@mem_gen_memG Σ (ceriseG_of x)).
  (* The shared part of the state interpretation, at the base; the part of
     thread [x], at its instance. *)
  #[local] Notation SI_sh R C σ :=
    (@SI_shared MP Σ (@cb_sreg Σ ceriseb) (@cb_mem Σ ceriseb) (@cb_shadow Σ ceriseb)
       (@cb_registry Σ ceriseb) (@cb_addr_alloc Σ ceriseb) (@cb_trapVector Σ ceriseb)
       (@cb_mpie Σ ceriseb) (@cb_posture Σ ceriseb) R C σ).
  #[local] Notation SI_th_of x R C σ :=
    (@SI_th MP Σ (@cerise_pcG Σ (ceriseG_of x)) (@reg_gen_regG Σ (ceriseG_of x))
       (@mem_gen_memG Σ (ceriseG_of x))
       (@cerise_mtdcG Σ (ceriseG_of x)) (@cerise_mieG Σ (ceriseG_of x))
       (@cerise_mtdc_lentG Σ (ceriseG_of x)) (@cerise_hwmG Σ (ceriseG_of x)) R C σ).

  (** * Helpers *)

  Lemma thread_si_unfold th σ :
    thread_si th σ ⊣⊢
    (∃ R C, SI_sh R C σ ∗ SI_th_of th R C σ) ∗
    ⌜dom (reg σ) = all_registers_s⌝ ∗
    @crit_link Σ th (CL th) σ ∗
    ctx_irq_si (ceriseg := ceriseG_of th) (kind_of th) σ ∗
    hwm_win_si (ceriseg := ceriseG_of th) (kind_of th) σ.
  Proof. done. Qed.

  (** The MIE fragment of a thread agrees with its state interpretation. *)
  Lemma thread_si_mie_st th σ b :
    thread_si th σ -∗ MIE ↦ₜ[th] b -∗ ⌜mie_st σ = b⌝.
  Proof.
    iIntros "Hsi HMIE". iDestruct "Hsi" as "[HSI _]".
    iApply (SI_mie_st with "HSI HMIE").
  Qed.

  (** The homes of a user thread and of the context-switch thread differ. *)
  Lemma homes_differ B :
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0%Z)) →
    (∃ p b e a, mtdc_home_at (th := UserThread B) = TStack p b e a) →
    mtdc_home_at (th := UserThread B) ≠ mtdc_home_at (th := CtxSwitch).
  Proof. intros Hs (p & b & e & a & HB). rewrite HB Hs. discriminate. Qed.

  (** The context-switch thread's resources, its authorities and fragments
      set to [lpc'], [lreg'], [m'], InterruptDisabled, and the pair [mshwmb_v']
      [mshwm_v']; its own zone [zc] stays. *)
  Lemma idle_load lpc' lreg' m' mshwmb_v' mshwm_v' :
    dom lreg' = all_registers_s →
    idle_CtxSwitch
    ==∗
    ∃ zc,
    thread_auths (th := CtxSwitch) lpc' lreg' m' InterruptDisabled mshwmb_v' mshwm_v' zc ∗
    PC ↦ₚ[CtxSwitch] lpc' ∗
    regs[CtxSwitch] lreg' ∗
    mtdc ↦ₜ[CtxSwitch] m' ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    mshwmb ↦ₜ[CtxSwitch] mshwmb_v' ∗
    mshwm ↦ₜ[CtxSwitch] mshwm_v' ∗
    zone_halves[CtxSwitch] zc ∗
    ctx_last_owner_frag None ∗
    mtdc_lent_at (th := CtxSwitch) ∗
    scheduler_state ∗
    na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
    close_Nact.
  Proof.
    iIntros (Hdom') "Hidle". iNamed "Hidle".
    iDestruct "Hauths" as "(HPCa & Hr & Hmtdc_a & HMIE_a & Hhwmb_a & Hhwm_a & Hzone_a & Hrest)".
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iMod (regs_copy lreg lreg' with "Hr Hregs") as "[Hr Hregs]".
    { by rewrite Hdom Hdom'. }
    iMod (mtdc_update _ _ m' with "Hmtdc_a Hmtdc") as "[Hmtdc_a Hmtdc]".
    iMod (MIE_update _ _ InterruptDisabled with "HMIE_a HMIE") as "[HMIE_a HMIE]".
    iMod (mshwmb_update _ _ mshwmb_v' with "Hhwmb_a Hhwmb") as "[Hhwmb_a Hhwmb]".
    iMod (mshwm_update _ _ mshwm_v' with "Hhwm_a Hhwm") as "[Hhwm_a Hhwm]".
    iModIntro. iExists zc. rewrite /thread_auths. iFrame.
  Qed.

  (** The running thread [th] out of the hardware's state interpretation. *)
  Lemma SI_hw_running th σ :
    SI_hw σ -∗
    running_frag th -∗
    running_auth th ∗
    resume_window_si th σ ∗
    thread_si th σ ∗
    (if th is CtxSwitch then True else idle_CtxSwitch) ∗
    running_frag th.
  Proof.
    iIntros "Hhw Hf". iDestruct "Hhw" as (th_r) "Hhw". iNamed "Hhw".
    iDestruct (running_agree th_r th with "Hrun Hf") as %->. iFrame.
  Qed.

  (** The running thread becomes [th'], out of its switch window. *)
  Lemma switch_ghosts th th' σ σ' w :
    (th' = CtxSwitch → mie_st σ' = InterruptDisabled) →
    running_auth th -∗
    running_frag th -∗
    resume_window_si th σ -∗
    resume_window_frag w
    ==∗
    running_auth th' ∗
    running_frag th' ∗
    resume_window_si th' σ' ∗
    resume_window_frag false.
  Proof.
    iIntros (Hdis) "Hrun Hf Hwin Hwf". iDestruct "Hwin" as (w0) "[Hwa _]".
    iMod (running_update th' th th with "Hrun Hf") as "[$ $]".
    iMod (resume_window_update false with "Hwa Hwf") as "[Hwa Hwf]".
    iModIntro. iSplitL "Hwa"; last iExact "Hwf".
    iExists false. iFrame "Hwa". iPureIntro. intros Hth _. by apply Hdis.
  Qed.

  (** * The interrupt hand-in *)

  (** From the running user thread [t] at a state with interrupts
      enabled: the context-switch thread's state interpretation at the
      interrupt entry, [t]'s authorities for its slot (a tagged PC of [t]
      has no identifier), the context-switch thread's fragments at the trap
      vector with a copy of [t]'s registers, its MSHWMB and MSHWM at [t]'s
      pair (MSHWMB is [t]'s stack base), its window closed and [t]'s halves
      lent, and [t]'s posture pinned to the values the entry wrote. *)
  Lemma irq_hand_in t σ (c : Z) :
    mie_st σ = InterruptEnabled →
    thread_si (UserThread t) σ -∗
    idle_CtxSwitch
    ==∗
    ∃ (lpc : LWord) (lreg : LReg) (mshwmb_v mshwm_v : Z) (zn : gset Addr),
      "Hsi" ∷ thread_si CtxSwitch (enter_irq c σ) ∗
      "Hauths" ∷ auths_at t (ResumeVals lreg lpc InterruptEnabled mshwmb_v mshwm_v zn) ∗
      "%Hdom" ∷ ⌜dom lreg = all_registers_s⌝ ∗
      "%Hpc" ∷ ⌜get_tag lpc.(lw) = true → lpc.(lprov) = None⌝ ∗
      "HPC" ∷ PC ↦ₚ[CtxSwitch] lword_of_word mtcc_vec ∗
      "Hregs" ∷ regs[CtxSwitch] lreg ∗
      "HMIE" ∷ MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
      "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread t)) ∗
      "Hhwmb" ∷ mshwmb ↦ₜ[CtxSwitch] mshwmb_v ∗
      "#Hbase" ∷ hwm_base[u t] mshwmb_v ∗
      "Hhwm" ∷ mshwm ↦ₜ[CtxSwitch] mshwm_v ∗
      "Hpend" ∷ pend_frag[CtxSwitch] None ∗
      "Hlent" ∷ lent_frag[CtxSwitch] zn ∗
      "Hlast_owner" ∷ ctx_last_owner_frag None ∗
      "Hposture" ∷ posture_of (UserThread t) (Some InterruptEnabled)
        (Some (lword_of_word lpc.(lw))) (Some (lword_of_word (WInt c))) (Some MTVAL_NONE) ∗
      "Hsched" ∷ scheduler_state ∗
      "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
      "Hclose" ∷ close_Nact.
  Proof.
    iIntros (Hen) "Hsi Hidle".
    iDestruct (thread_si_unfold with "Hsi") as "(HSI & %Hdom_σ & Hlink & _ & Hhwm_win)".
    cbn [hwm_win_si kind_of]. iDestruct "Hhwm_win" as "(Hph & Hlf & #Hbase)".
    iDestruct "HSI" as (R C) "[Hsh Hth]". iNamed "Hsh". iNamed "Hth".
    (* t's link at InterruptEnabled: what it hands over and its posture
       part; its mtdc token pins its mtdc to its home. *)
    iDestruct (csl_link_user_enabled t σ Hen with "Hlink") as "[Hho Hpart]".
    iDestruct (csl_posture_part t with "Hpart") as "[Hsa Hlent_t]".
    iDestruct (mtdc_clause_lent with "Hlent Hlent_t") as %Hhome.
    iDestruct (csl_posture_part t with "[$Hsa $Hlent_t]") as "Hpart".
    iDestruct (handover_res_unfold with "Hho")
      as (p0 c0 v0 b0) "(Hcrit & HU & Hmepcc & Hmcause & Hmtval & Hmpie_f)".
    iDestruct "Hmtcc" as "[ [Hmtcc Hpend] | (%wt & _ & _ & HU' & _)]"; last first.
    { iDestruct (unwedged_excl with "HU HU'") as %[]. }
    (* t's pair, zone and stack base. *)
    assert (phys_mshwmb σ = mshwmb_v) as Hphys.
    { by rewrite /phys_mshwmb (et_hwmb _ _ _ _ _ _ _ _ _ Herth). }
    rewrite Hphys.
    iDestruct (@hwm_user_out Σ (memG_of (UserThread t)) (hwmG_of (UserThread t))
                with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone Hph Hlf")
      as (zn) "(%Hcov & (Hb_t & Hh_t & Hza_t & Hrest_t) & Hzn)".
    iEval (rewrite (zone_halves_thread_indep (UserThread t) CtxSwitch)) in "Hzn".
    (* The erasure at the interrupt entry. *)
    iDestruct (gen_heap_valid with "Hsr Hmtcc") as %Htcc0.
    pose proof (erasure_join R C σ lpc lreg lsh vm mie mpie mshwmb_v mshwm_v lmem Hersh Herth) as Her.
    assert (mie = InterruptEnabled) as ->.
    { rewrite -Hen. symmetry. by eapply erasure_th_mie_st. }
    assert (lsregs_join lsh vm mshwmb_v mshwm_v InterruptEnabled mpie !! mtcc = Some (lword_of_word mtcc_vec))
      as Htcc by rewrite lsregs_join_ne //.
    pose proof (erasure_enter_irq R C σ lpc lreg _ lmem c _ Her Htcc) as Her'.
    rewrite lsregs_enter_irq_join // in Her'.
    set (lsh' := <[mtval := lword_of_word (WInt MTVAL_NONE)]>
                   (<[mcause := lword_of_word (WInt c)]>
                      (<[mepcc := lword_of_word lpc.(lw)]> lsh))).
    destruct (erasure_split R C (enter_irq c σ) (lword_of_word mtcc_vec) lreg lsh' vm
                InterruptDisabled InterruptEnabled mshwmb_v mshwm_v lmem) as [Hsh' Hth'];
      [ | | | | exact Her' | ].
    { rewrite /lsh' !lookup_insert_ne //. apply (es_no_mtdc _ _ _ _ _ _ Hersh). }
    { rewrite /lsh' !lookup_insert_ne //. apply (es_no_mstatus _ _ _ _ _ _ Hersh). }
    { rewrite /lsh' !lookup_insert_ne //. apply (es_no_mshwm _ _ _ _ _ _ Hersh). }
    { rewrite /lsh' !lookup_insert_ne //. apply (es_no_mshwmb _ _ _ _ _ _ Hersh). }
    (* The volatile registers and MPIE take the values the entry wrote. *)
    iMod (gen_heap_update _ _ _ (lword_of_word lpc.(lw)) with "Hsr Hmepcc") as "[Hsr Hmepcc]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt c)) with "Hsr Hmcause") as "[Hsr Hmcause]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt MTVAL_NONE)) with "Hsr Hmtval")
      as "[Hsr Hmtval]".
    iMod (MPIE_update _ _ InterruptEnabled with "Hmpie Hmpie_f") as "[Hmpie Hmpie_f]".
    iMod (idle_load (lword_of_word mtcc_vec) lreg m mshwmb_v mshwm_v with "Hidle")
      as (zc) "(Hauths_s & HPC_s & Hregs_s & Hmtdc_s & HMIE_s & Hhwmb_s & Hhwm_s & Hzc & Hlast_owner &
                Hlent_s & Hsched & Hna & Hclose)".
    { rewrite -Hdom_σ. symmetry. apply (et_regs _ _ _ _ _ _ _ _ _ Herth). }
    iDestruct "Hauths_s" as "(HPCa_s & Hr_s & Hmtdc_a & HMIE_a & Hb_s & Hh_s & Hza_s & Hrest_s)".
    iMod (@hwm_ctx_in Σ (memG_of CtxSwitch) (hwmG_of CtxSwitch) mshwmb_v mshwm_v zc zn Hcov
           with "Hb_s Hh_s Hza_s Hrest_s Hzc Hzn")
      as "((Hb_s & Hh_s & Hpsi_s & Hla_s & Hzone_s) & Hpcl_s & Hpf_s & Hlf_s)".
    subst m.
    iModIntro. iExists lpc, lreg, mshwmb_v, mshwm_v, zn.
    iSplitL "Hmtcc Hpend Hm Hst HR HC Hsr Hmpie HPCa_s Hr_s Hmtdc_a HMIE_a Hlent_s
             Hb_s Hh_s Hpsi_s Hla_s Hzone_s Hpcl_s".
    { iApply thread_si_unfold. iSplitL "Hmtcc Hpend Hm Hst HR HC Hsr Hmpie HPCa_s Hr_s
                                        Hmtdc_a HMIE_a Hlent_s Hb_s Hh_s Hpsi_s Hla_s Hzone_s".
      - iExists R, C. iSplitL "Hmtcc Hpend Hm Hst HR HC Hsr Hmpie".
        + iExists lsh', lmem, InterruptEnabled. rewrite shadowtbl_enter_irq.
          iFrame "Hsr Hm Hst HR HC Hmpie". iSplitL; [iLeft; iFrame | done].
        + (* The context-switch thread's clause holds its token. *)
          iExists (lword_of_word mtcc_vec), lreg, _, vm, InterruptDisabled, mshwmb_v, mshwm_v, None, zn.
          iFrame. iSplit; done.
      - iSplit; first by rewrite reg_enter_irq. iSplitR; [|iSplitR].
        + iApply csl_link_disabled. by eapply erasure_th_mie_st.
        + cbn [ctx_irq_si kind_of]. iLeft. iPureIntro. by eapply erasure_th_mie_st.
        + cbn [hwm_win_si kind_of]. iExists None. iFrame "Hpcl_s". }
    iSplitL "HPCa Hr Hmtdc Hmie Hb_t Hh_t Hza_t Hrest_t".
    { rewrite /auths_at /thread_auths. cbn [rv_pc rv_regs rv_mie rv_hwmb rv_hwm rv_zone].
      iFrame "∗ #". done. }
    iSplitR.
    { iPureIntro. rewrite -Hdom_σ. symmetry. apply (et_regs _ _ _ _ _ _ _ _ _ Herth). }
    iSplitR.
    { iPureIntro. apply (erasure_pc_tagged_no_id _ _ _ _ _ _ _ Her). }
    iFrame "HPC_s Hregs_s HMIE_s Hmtdc_s Hsched Hna Hclose Hhwmb_s Hhwm_s Hpf_s Hlf_s Hlast_owner Hbase".
    iApply (posture_res_gen_intro (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
              (CL := CL (UserThread t)) (CR := CR (UserThread t))
              (lword_of_word lpc.(lw)) (lword_of_word (WInt c)) MTVAL_NONE InterruptEnabled
              with "[Hcrit HU Hmepcc Hmcause Hmtval Hmpie_f] Hpart").
    rewrite /handover_at /volatile_csr_at. iFrame.
  Qed.

  (** * The yield and exit hand-ins *)

  (** The hand-in at a state where the user thread runs with interrupts
      disabled: its authorities to its slot, a copy of its registers to the
      context-switch thread, with its pair, its stack base, and the halves
      of its zone lent. *)
  Lemma hand_in_disabled t σ :
    mie_st σ = InterruptDisabled →
    thread_si (UserThread t) σ -∗
    part_of (UserThread t) -∗
    idle_CtxSwitch
    ==∗
    ∃ (lpc : LWord) (lreg : LReg) (mshwmb_v mshwm_v : Z) (zn : gset Addr),
      "Hsi" ∷ thread_si CtxSwitch σ ∗
      "Hauths" ∷ auths_at t (ResumeVals lreg lpc InterruptDisabled mshwmb_v mshwm_v zn) ∗
      "%Hdom" ∷ ⌜dom lreg = all_registers_s⌝ ∗
      "Hpart" ∷ part_of (UserThread t) ∗
      "HPC" ∷ PC ↦ₚ[CtxSwitch] lpc ∗
      "Hregs" ∷ regs[CtxSwitch] lreg ∗
      "HMIE" ∷ MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
      "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread t)) ∗
      "Hhwmb" ∷ mshwmb ↦ₜ[CtxSwitch] mshwmb_v ∗
      "#Hbase" ∷ hwm_base[u t] mshwmb_v ∗
      "Hhwm" ∷ mshwm ↦ₜ[CtxSwitch] mshwm_v ∗
      "Hpend" ∷ pend_frag[CtxSwitch] None ∗
      "Hlent" ∷ lent_frag[CtxSwitch] zn ∗
      "Hlast_owner" ∷ ctx_last_owner_frag None ∗
      "Hsched" ∷ scheduler_state ∗
      "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
      "Hclose" ∷ close_Nact.
  Proof.
    iIntros (Hdis) "Hsi Hpart Hidle".
    iDestruct (thread_si_unfold with "Hsi") as "(HSI & %Hdom_σ & _ & _ & Hhwm_win)".
    cbn [hwm_win_si kind_of]. iDestruct "Hhwm_win" as "(Hph & Hlf & #Hbase)".
    iDestruct "HSI" as (R C) "[Hsh Hth]". iNamed "Hth".
    iDestruct (csl_posture_part t with "Hpart") as "[Hsa Hlent_t]".
    iDestruct (mtdc_clause_lent with "Hlent Hlent_t") as %Hhome.
    iDestruct (csl_posture_part t with "[$Hsa $Hlent_t]") as "Hpart".
    assert (mie = InterruptDisabled) as ->.
    { rewrite -Hdis. symmetry. by eapply erasure_th_mie_st. }
    (* t's pair, zone and stack base. *)
    assert (phys_mshwmb σ = mshwmb_v) as Hphys.
    { by rewrite /phys_mshwmb (et_hwmb _ _ _ _ _ _ _ _ _ Herth). }
    rewrite Hphys.
    iDestruct (@hwm_user_out Σ (memG_of (UserThread t)) (hwmG_of (UserThread t))
                with "Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone Hph Hlf")
      as (zn) "(%Hcov & (Hb_t & Hh_t & Hza_t & Hrest_t) & Hzn)".
    iEval (rewrite (zone_halves_thread_indep (UserThread t) CtxSwitch)) in "Hzn".
    iMod (idle_load lpc lreg m mshwmb_v mshwm_v with "Hidle")
      as (zc) "(Hauths_s & HPC_s & Hregs_s & Hmtdc_s & HMIE_s & Hhwmb_s & Hhwm_s & Hzc & Hlast_owner &
                Hlent_s & Hsched & Hna & Hclose)".
    { rewrite -Hdom_σ. symmetry. apply (et_regs _ _ _ _ _ _ _ _ _ Herth). }
    iDestruct "Hauths_s" as "(HPCa_s & Hr_s & Hmtdc_a & HMIE_a & Hb_s & Hh_s & Hza_s & Hrest_s)".
    iMod (@hwm_ctx_in Σ (memG_of CtxSwitch) (hwmG_of CtxSwitch) mshwmb_v mshwm_v zc zn Hcov
           with "Hb_s Hh_s Hza_s Hrest_s Hzc Hzn")
      as "((Hb_s & Hh_s & Hpsi_s & Hla_s & Hzone_s) & Hpcl_s & Hpf_s & Hlf_s)".
    subst m.
    iModIntro. iExists lpc, lreg, mshwmb_v, mshwm_v, zn.
    iSplitL "Hsh HPCa_s Hr_s Hmtdc_a HMIE_a Hlent_s Hb_s Hh_s Hpsi_s Hla_s Hzone_s Hpcl_s".
    { iApply thread_si_unfold.
      iSplitL "Hsh HPCa_s Hr_s Hmtdc_a HMIE_a Hlent_s Hb_s Hh_s Hpsi_s Hla_s Hzone_s".
      - iExists R, C. iFrame "Hsh".
        iExists lpc, lreg, _, vm, InterruptDisabled, mshwmb_v, mshwm_v, None, zn.
        iFrame. iSplit; done.
      - iSplit; first done. iSplitR; [|iSplitR].
        + by iApply csl_link_disabled.
        + cbn [ctx_irq_si kind_of]. by iLeft.
        + cbn [hwm_win_si kind_of]. iExists None. iFrame "Hpcl_s". }
    iSplitL "HPCa Hr Hmtdc Hmie Hb_t Hh_t Hza_t Hrest_t".
    { rewrite /auths_at /thread_auths. cbn [rv_pc rv_regs rv_mie rv_hwmb rv_hwm rv_zone].
      iFrame "∗ #". done. }
    iSplitR.
    { iPureIntro. rewrite -Hdom_σ. symmetry. apply (et_regs _ _ _ _ _ _ _ _ _ Herth). }
    iFrame "∗ #".
  Qed.

  (** The yield hand-in: [yield_body]'s continuation is the yield's
      parking continuation, and the context-switch thread starts at the
      trap vector. *)
  Lemma yield_hand_in t σ :
    thread_si (UserThread t) σ -∗
    yield_body safe (UserThread t) -∗
    idle_CtxSwitch
    ==∗
    ∃ (b : InterruptStatus) (p : LWord) (lreg : LReg) (mshwmb_v mshwm_v : Z) (zn : gset Addr),
      "Hsi" ∷ thread_si CtxSwitch σ ∗
      "Hauths" ∷ auths_at t (ResumeVals lreg (lword_of_word mtcc_vec) InterruptDisabled mshwmb_v mshwm_v zn) ∗
      "Hcont" ∷ park_cont t (ParkYield b p) ∗
      "%Hdom" ∷ ⌜dom lreg = all_registers_s⌝ ∗
      "Hposture" ∷ posture_of (UserThread t) (Some b) (Some p)
        (Some (lword_of_word (WInt MCAUSE_ECALL_MACHINE))) None ∗
      "HMIE_t" ∷ MIE ↦ₜ[u t] InterruptDisabled ∗
      "HPC_t" ∷ PC ↦ₚ[u t] lword_of_word mtcc_vec ∗
      "HPC" ∷ PC ↦ₚ[CtxSwitch] lword_of_word mtcc_vec ∗
      "Hregs" ∷ regs[CtxSwitch] lreg ∗
      "HMIE" ∷ MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
      "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread t)) ∗
      "Hhwmb" ∷ mshwmb ↦ₜ[CtxSwitch] mshwmb_v ∗
      "#Hbase" ∷ hwm_base[u t] mshwmb_v ∗
      "Hhwm" ∷ mshwm ↦ₜ[CtxSwitch] mshwm_v ∗
      "Hpend" ∷ pend_frag[CtxSwitch] None ∗
      "Hlent" ∷ lent_frag[CtxSwitch] zn ∗
      "Hlast_owner" ∷ ctx_last_owner_frag None ∗
      "Hsched" ∷ scheduler_state ∗
      "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
      "Hclose" ∷ close_Nact.
  Proof.
    iIntros "Hsi Hyield Hidle".
    iDestruct "Hyield" as (b p) "(Hposture & HMIE_t & HPC_t & Hcont)".
    iDestruct (thread_si_mie_st with "Hsi HMIE_t") as %Hdis.
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := CL (UserThread t)) (CR := CR (UserThread t)) with "Hposture")
      as "[Hho Hpart]".
    iMod (hand_in_disabled t σ Hdis with "Hsi Hpart Hidle") as (lpc lreg mshwmb_v mshwm_v zn) "H".
    iNamed "H".
    iDestruct "Hauths" as "((HPCa_t & Hauths_t) & %Hcov_t & _)".
    iDestruct (PC_agree with "HPCa_t HPC_t") as %Hpc.
    cbn in Hpc. subst lpc.
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := CL (UserThread t)) (CR := CR (UserThread t)) with "[$Hho $Hpart]")
      as "Hposture".
    iModIntro. iExists b, p, lreg, mshwmb_v, mshwm_v, zn.
    iFrame "Hsi HPC Hregs HMIE Hmtdc Hsched Hna Hclose HMIE_t HPC_t Hposture".
    iFrame "Hhwmb Hbase Hhwm Hpend Hlent Hlast_owner".
    iSplitL "HPCa_t Hauths_t".
    { rewrite /auths_at /thread_auths. cbn [rv_pc rv_regs rv_mie rv_hwmb rv_hwm rv_zone].
      iFrame "∗ # %". }
    iSplit; last done. rewrite /park_cont. iExact "Hcont".
  Qed.

  (** The exit hand-in: [exit_body]'s register map is the thread's. *)
  Lemma exit_hand_in t σ :
    thread_si (UserThread t) σ -∗
    exit_body (UserThread t) -∗
    idle_CtxSwitch
    ==∗
    ∃ (lpc : LWord) (lreg : LReg) (mshwmb_v mshwm_v : Z) (zn : gset Addr),
      "Hsi" ∷ thread_si CtxSwitch σ ∗
      "Hauths" ∷ auths_at t (ResumeVals lreg lpc InterruptDisabled mshwmb_v mshwm_v zn) ∗
      "%Hdom" ∷ ⌜dom lreg = all_registers_s⌝ ∗
      "HMIE_t" ∷ MIE ↦ₜ[u t] InterruptDisabled ∗
      "Hposture" ∷ posture_of (UserThread t) None None
        (Some (lword_of_word (WInt MCAUSE_THREAD_EXIT))) None ∗
      "Hregs_t" ∷ regs[u t] lreg ∗
      "Hexit" ∷ exit_part (UserThread t) ∗
      "HPC" ∷ PC ↦ₚ[CtxSwitch] lpc ∗
      "Hregs" ∷ regs[CtxSwitch] lreg ∗
      "HMIE" ∷ MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
      "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread t)) ∗
      "Hhwmb" ∷ mshwmb ↦ₜ[CtxSwitch] mshwmb_v ∗
      "#Hbase" ∷ hwm_base[u t] mshwmb_v ∗
      "Hhwm" ∷ mshwm ↦ₜ[CtxSwitch] mshwm_v ∗
      "Hpend" ∷ pend_frag[CtxSwitch] None ∗
      "Hlent" ∷ lent_frag[CtxSwitch] zn ∗
      "Hlast_owner" ∷ ctx_last_owner_frag None ∗
      "Hsched" ∷ scheduler_state ∗
      "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
      "Hclose" ∷ close_Nact.
  Proof.
    iIntros "Hsi Hexit_b Hidle".
    iDestruct "Hexit_b" as "(HMIE_t & Hposture & (%lreg_e & %Hdom_e & Hregs_t) & Hexit)".
    iDestruct (thread_si_mie_st with "Hsi HMIE_t") as %Hdis.
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := CL (UserThread t)) (CR := CR (UserThread t)) with "Hposture")
      as "[Hho Hpart]".
    iMod (hand_in_disabled t σ Hdis with "Hsi Hpart Hidle") as (lpc lreg mshwmb_v mshwm_v zn) "H".
    iNamed "H".
    iDestruct "Hauths" as "((HPCa_t & Hr_t & Hauths_t) & %Hcov_t & _)".
    iDestruct (gen_heap_valid_inclSepM with "Hr_t Hregs_t") as %Hsub.
    cbn in Hsub. apply regs_total_eq in Hsub as ->; last done.
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := CL (UserThread t)) (CR := CR (UserThread t)) with "[$Hho $Hpart]")
      as "Hposture".
    iModIntro. iExists lpc, lreg, mshwmb_v, mshwm_v, zn.
    iFrame "Hsi HPC Hregs HMIE Hmtdc Hsched Hna Hclose HMIE_t Hposture Hregs_t Hexit".
    iFrame "Hhwmb Hbase Hhwm Hpend Hlent Hlast_owner".
    iSplitL; last done.
    rewrite /auths_at /thread_auths. cbn [rv_pc rv_regs rv_mie rv_hwmb rv_hwm rv_zone].
    iFrame "∗ # %".
  Qed.

  (** * The hand-back at [ResumedV] *)

  (** From the context-switch thread's state interpretation and
      [resumed_body]'s pieces, the resumed thread [B]'s state
      interpretation at the same state, with its authorities, and the
      context-switch thread's resources while [B] runs. B's home is not the
      context-switch thread's, so the latter's mtdc token leaves its
      clause. B's halves leave the context-switch thread's lent set for
      B's zone, and the context-switch thread's window and lending ghosts
      return to rest. *)
  Lemma resumed_hand_back B (v : resume_vals) σ :
    mtdc_home_at (th := UserThread B) ≠ mtdc_home_at (th := CtxSwitch) →
    thread_si CtxSwitch σ -∗
    ⌜dom v.(rv_regs) = all_registers_s⌝ -∗
    regs[CtxSwitch] v.(rv_regs) -∗
    @PC_fragq Σ (@cerise_pcG Σ (ceriseG_of CtxSwitch)) (pc_dq v.(rv_mie)) v.(rv_pc) -∗
    MIE ↦ₜ[CtxSwitch] v.(rv_mie) -∗
    mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread B)) -∗
    mshwmb ↦ₜ[CtxSwitch] v.(rv_hwmb) -∗
    mshwm ↦ₜ[CtxSwitch] v.(rv_hwm) -∗
    pend_frag[CtxSwitch] None -∗
    lent_frag[CtxSwitch] v.(rv_zone) -∗
    ctx_last_owner_frag None -∗
    (if v.(rv_mie) is InterruptEnabled then part_of (UserThread B) else True) -∗
    scheduler_state -∗
    na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) -∗
    close_Nact -∗
    auths_at B v
    ==∗
    thread_si (UserThread B) σ ∗
    idle_CtxSwitch.
  Proof.
    destruct v as [lreg_r lpc_r b hbB hB zB]. cbn [rv_regs rv_pc rv_mie rv_hwmb rv_hwm rv_zone].
    iIntros (Hne) "Hsi %Hdom Hregs HPC HMIE Hmtdc_f Hhwmb_f Hhwm_f Hpf Hlf Hlast_owner Hpart Hsched Hna
      Hclose Hauths".
    iDestruct (thread_si_unfold with "Hsi") as "(HSI & %Hdom_σ & Hlink & Hirq & Hhwm_win)".
    cbn [hwm_win_si kind_of]. iDestruct "Hhwm_win" as (o') "[Hpcl _]".
    iDestruct "HSI" as (R C) "[Hsh Hth]". iNamed "Hth".
    (* The pair is B's; B's halves leave the lent set. *)
    iDestruct (mshwmb_agree with "Hmshwmb_a Hhwmb_f") as %->.
    iDestruct (mshwm_agree with "Hmshwm_a Hhwm_f") as %->.
    iMod (@hwm_ctx_out Σ (memG_of CtxSwitch) (hwmG_of CtxSwitch)
           with "Hpend_si Hlent_a Hzone Hpcl Hpf Hlf")
      as "(-> & Hrest_c & %zc & Hza_c & Hzc & HzB)".
    iDestruct "Hauths" as "((HPCa_B & Hr_B & Hmtdc_B & HMIE_B & Hb_B & Hh_B & Hza_B & Hrest_B) &
                            %Hcov & #Hbase)".
    iEval (rewrite (zone_halves_thread_indep CtxSwitch (UserThread B))) in "HzB".
    iDestruct (@hwm_user_in Σ (memG_of (UserThread B)) (hwmG_of (UserThread B)) hbB hB zB Hcov
                with "Hza_B Hrest_B HzB") as "(Hpsi_B & Hla_B & Hzone_B & Hph_B & Hlf_B)".
    assert (phys_mshwmb σ = hbB) as Hphys.
    { by rewrite /phys_mshwmb (et_hwmb _ _ _ _ _ _ _ _ _ Herth). }
    pose proof (erasure_th_mie_st _ _ _ _ _ _ _ _ _ Herth) as Hmie_st.
    iDestruct (MIE_agree with "Hmie HMIE") as %<-.
    (* The whole PC fragment: at InterruptEnabled, its other half is in the
       interrupt clause. *)
    iAssert (PC ↦ₚ[CtxSwitch] lpc_r)%I with "[HPC Hirq]" as "HPC".
    { destruct mie; cbn [pc_dq].
      - cbn [ctx_irq_si kind_of].
        iDestruct "Hirq" as "[%Hd | (%lpc' & HPC')]"; first congruence.
        iDestruct (PC_halves_merge with "HPC HPC'") as "[_ $]".
      - iExact "HPC". }
    iDestruct (PC_agree with "HPCa HPC") as %<-.
    iDestruct (mtdc_agree with "Hmtdc Hmtdc_f") as %->.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as %Hsub.
    apply regs_total_eq in Hsub as ->; last done.
    iDestruct "Hlent" as "[%Hh | Hlent_s]"; first done.
    (* B's link: from what the context-switch thread hands over and B's
       posture part at InterruptEnabled; trivial at InterruptDisabled. *)
    iAssert (@crit_link Σ (UserThread B) (CL (UserThread B)) σ)%I with "[Hlink Hpart]"
      as "Hlink_B".
    { destruct mie.
      - iDestruct (csl_link_ctx_enabled σ Hmie_st with "Hlink") as "Hho".
        iDestruct (handover_res_thread_indep CtxSwitch (UserThread B) with "Hho") as "Hho".
        iApply (csl_link_user_enabled B σ Hmie_st). iFrame.
      - iApply (csl_link_disabled (UserThread B) σ Hmie_st). }
    iModIntro.
    iSplitL "Hsh HPCa_B Hr_B Hmtdc_B HMIE_B Hb_B Hh_B Hpsi_B Hla_B Hzone_B Hph_B Hlf_B Hlink_B".
    { iApply thread_si_unfold.
      iSplitL "Hsh HPCa_B Hr_B Hmtdc_B HMIE_B Hb_B Hh_B Hpsi_B Hla_B Hzone_B".
      - iExists R, C. iFrame "Hsh". iExists lpc, lreg, _, vm, mie, hbB, hB, None, ∅. iFrame.
        iSplit; [done | ]. iSplit; [by iLeft | done].
      - iSplit; first done. iFrame "Hlink_B". iSplitR; first done.
        cbn [hwm_win_si kind_of]. rewrite Hphys. iFrame "Hph_B Hlf_B Hbase". }
    rewrite /idle_CtxSwitch /thread_auths. iExists lpc, lreg, _, mie, hbB, hB, zc. iFrame. done.
  Qed.

  (** * The tick *)

  Lemma thread_si_tick th σ : thread_si th σ ⊢ thread_si th (tick σ).
  Proof.
    rewrite !thread_si_unfold. iIntros "(HSI & %Hdom & Hlink & Hirq & Hhwm_win)".
    iDestruct "HSI" as (R C) "[Hsh Hth]". iNamed "Hsh". iNamed "Hth".
    assert (mie_st (tick σ) = mie_st σ) as Htk by rewrite /mie_st tick_sreg //.
    iSplitL "Hsr Hmtcc Hm Hst HR HC Hmpie HPCa Hr Hmtdc Hlent Hmie Hmshwmb_a Hmshwm_a Hpend_si
             Hlent_a Hzone".
    { iExists R, C. iSplitL "Hsr Hmtcc Hm Hst HR HC Hmpie".
      - iExists lsh, lmem, mpie. rewrite tick_shadowtbl. iFrame.
        iPureIntro. by apply erasure_sh_tick.
      - iExists lpc, lreg, m, vm, mie, mshwmb_v, mshwm_v, o, L. iFrame.
        iPureIntro. split; [done | by apply erasure_th_tick]. }
    iSplit; first by rewrite tick_reg.
    iSplitL "Hlink".
    { iApply (crit_link_stable with "Hlink"); [done | by rewrite tick_sreg]. }
    iSplitL "Hirq"; first (rewrite /ctx_irq_si Htk; destruct (kind_of th); iExact "Hirq").
    by iApply hwm_win_si_tick.
  Qed.

  Lemma SI_hw_tick σ : SI_hw σ ⊢ SI_hw (tick σ).
  Proof.
    iIntros "Hhw". iDestruct "Hhw" as (th) "Hhw". iNamed "Hhw".
    iExists th. iFrame "Hrun Hidle". iSplitL "Hwin".
    - iDestruct "Hwin" as (w) "[Hwa %Hw]". iExists w. iFrame "Hwa". iPureIntro.
      rewrite /mie_st tick_sreg. done.
    - by iApply thread_si_tick.
  Qed.

  (** * The resume window after a step of the context-switch thread *)

  Lemma resume_window_ctx_step (e e' : thread_langs.expr CtxK) σ κ σ' efs (w : bool) :
    wellshaped e →
    @language.prim_step (tlang CtxK) e σ κ e' σ' efs →
    resume_window_si CtxSwitch σ -∗
    resume_window_frag w -∗
    ⌜w = true → window e⌝
    ==∗
    ∃ w' : bool,
      resume_window_si CtxSwitch σ' ∗
      resume_window_frag w' ∗
      ⌜w' = true → window e'⌝.
  Proof.
    iIntros (Hws Hs) "Hwin Hf %Hw". iDestruct "Hwin" as (w0) "[Ha %Hw0]".
    iDestruct (resume_window_agree with "Ha Hf") as %<-.
    assert (window e ∨ ¬ irq_enabled σ) as Hpre.
    { destruct w0; [left; by apply Hw | right].
      rewrite irq_enabled_mie_st (Hw0 eq_refl eq_refl). discriminate. }
    destruct (ctx_step_resumed_or_disabled e e' σ κ σ' efs Hws Hs Hpre) as [Hwin | Hd].
    - (* The step ends in the switch window. *)
      iMod (resume_window_update true with "Ha Hf") as "[Ha Hf]".
      iModIntro. iExists true. iSplitL "Ha".
      { iExists true. iFrame "Ha". done. }
      iFrame "Hf". done.
    - (* The step ends with interrupts disabled. *)
      iMod (resume_window_update false with "Ha Hf") as "[Ha Hf]".
      iModIntro. iExists false. iSplitL "Ha".
      { iExists false. iFrame "Ha". iPureIntro. intros _ _.
        destruct (mie_st σ') eqn:Hm; last done.
        exfalso. apply Hd. by apply irq_enabled_mie_st. }
      iFrame "Hf". done.
  Qed.

End hw_switches.
