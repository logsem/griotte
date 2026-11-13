From iris.proofmode Require Import proofmode environments spec_patterns.
From griotte Require Export shapes.step.

(** * Trap entry

    The fault causes, the resources of trap entry and the obligation
    [trap_safe] of a fault, the rules of trap entry at any link with a
    routing law, and the [iTrap] tactic. Trap entry writes MIE (and MPIE,
    MEPCC, mcause and mtval): at InterruptDisabled it takes [handover_res]
    from the thread, at InterruptEnabled from the link, through the routing
    law; the continuation receives the volatile registers at the values of
    the entry, and, at InterruptEnabled, the part of the posture. *)

Section trap_entry_res.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th} {CR : CritRoute Σ th CL}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types w : LWord.

  (* Clients close faults with [wp_trap] (through [iTrap]) or with the
     cause-aware rules of [rules_trap_cause.v]; the lemmas below are their
     proof. *)

  (** The fault causes: the named causes below 8, and the CHERI cause. *)
  Definition mcause_ok (z : Z) : Prop := (0 ≤ z < 8)%Z ∨ z = 28%Z.

  Lemma trap_cause_ok φ : mcause_ok (trap_cause φ).
  Proof.
    pose proof (trap_cause_range φ) as Hr.
    rewrite /MCAUSE_INST_ACCESS_FAULT /MCAUSE_ILLEGAL_INSTRUCTION /MCAUSE_LOAD_ACCESS_FAULT
      /MCAUSE_STORE_ACCESS_FAULT /MCAUSE_CHERI in Hr.
    rewrite /mcause_ok. set_unfold. naive_solver lia.
  Qed.

  (* The resources trap entry consumes at posture [b] (the MIE before the
     fault), and those it gives back to the continuation from the trap
     vector, for a fault from the PC [w]. Trap entry consumes the MIE
     fragment and, at InterruptDisabled, [handover_res]. It gives back MIE
     disabled, the critical-section and unwedged tokens, MEPCC, mcause with
     a cause that satisfies the cause predicate [P_mcause], mtval with a
     value that satisfies the value predicate [P_mtval] ([trap_entry_out]
     for the fault causes and any value), MPIE at [b], and, at
     InterruptEnabled, the part of the posture that the link held. Sealed:
     [trap_entry_res_unfold] and [trap_entry_out_unfold] give their
     contents. *)
  Definition trap_entry_res_def (b : InterruptStatus) : iProp Σ :=
    ⌜route_pre th b⌝ ∗
    MIE_frag b ∗
    (if b is InterruptDisabled then handover_res else True).
  #[local] Definition trap_entry_res_aux : seal (@trap_entry_res_def). Proof. by eexists. Qed.
  Definition trap_entry_res := trap_entry_res_aux.(unseal).
  #[local] Definition trap_entry_res_unseal :
    @trap_entry_res = @trap_entry_res_def := trap_entry_res_aux.(seal_eq).

  Definition trap_entry_out_def (P_mcause P_mtval : Z → Prop) (w : LWord) (b : InterruptStatus)
    : iProp Σ :=
    MIE_frag InterruptDisabled ∗
    na_own crit ⊤ ∗
    unwedged ∗
    mepcc ↦ₓ lmepcc_of_pc w ∗
    (∃ c : Z, ⌜P_mcause c⌝ ∗ mcause ↦ₓ lword_of_word (WInt c)) ∗
    (∃ v : Z, ⌜P_mtval v⌝ ∗ mtval ↦ₓ lword_of_word (WInt v)) ∗
    MPIE_frag b ∗
    (if b is InterruptEnabled then @posture_part _ _ _ th CL CR else True).
  #[local] Definition trap_entry_out_aux : seal (@trap_entry_out_def). Proof. by eexists. Qed.
  Definition trap_entry_out_cause := trap_entry_out_aux.(unseal).
  #[local] Definition trap_entry_out_unseal :
    @trap_entry_out_cause = @trap_entry_out_def := trap_entry_out_aux.(seal_eq).

  Lemma trap_entry_res_unfold b :
    trap_entry_res b ⊣⊢
    ⌜route_pre th b⌝ ∗
    MIE_frag b ∗
    (if b is InterruptDisabled then handover_res else True).
  Proof. by rewrite trap_entry_res_unseal. Qed.

  Lemma trap_entry_out_unfold P_mcause P_mtval w b :
    trap_entry_out_cause P_mcause P_mtval w b ⊣⊢
    MIE_frag InterruptDisabled ∗
    na_own crit ⊤ ∗
    unwedged ∗
    mepcc ↦ₓ lmepcc_of_pc w ∗
    (∃ c : Z, ⌜P_mcause c⌝ ∗ mcause ↦ₓ lword_of_word (WInt c)) ∗
    (∃ v : Z, ⌜P_mtval v⌝ ∗ mtval ↦ₓ lword_of_word (WInt v)) ∗
    MPIE_frag b ∗
    (if b is InterruptEnabled then @posture_part _ _ _ th CL CR else True).
  Proof. by rewrite trap_entry_out_unseal. Qed.

  (** The resources trap entry gives back, as the volatile registers handed
      over at the values of the entry. *)
  Lemma trap_entry_out_handover P_mcause P_mtval w b :
    trap_entry_out_cause P_mcause P_mtval w b -∗
    MIE_frag InterruptDisabled ∗
    (∃ c v : Z,
       ⌜P_mcause c⌝ ∗
       ⌜P_mtval v⌝ ∗
       handover_at (lmepcc_of_pc w) (lword_of_word (WInt c)) v b) ∗
    (if b is InterruptEnabled then @posture_part _ _ _ th CL CR else True).
  Proof.
    rewrite trap_entry_out_unseal.
    iIntros "($ & Hcrit & HU & Hmepcc & (%c & %Hc & Hmcause) & (%v & %Hv & Hmtval) & Hmpie & $)".
    iExists c, v. iSplit; first done. iSplit; first done. iFrame.
  Qed.

  (** Weaker cause and value predicates. *)
  Lemma trap_entry_out_cause_mono (P_mcause P_mcause' P_mtval P_mtval' : Z → Prop) w b :
    (∀ c : Z, P_mcause c → P_mcause' c) →
    (∀ v : Z, P_mtval v → P_mtval' v) →
    trap_entry_out_cause P_mcause P_mtval w b -∗
    trap_entry_out_cause P_mcause' P_mtval' w b.
  Proof.
    rewrite trap_entry_out_unseal.
    iIntros (HP_mcause HP_mtval)
      "($ & $ & $ & $ & (%c & %Hc & Hmcause) & (%v & %Hv & Hmtval) & $ & $)".
    iSplitL "Hmcause"; [iExists c | iExists v]; iFrame; iPureIntro;
      [by apply HP_mcause | by apply HP_mtval].
  Qed.

End trap_entry_res.

(** Trap entry, at any link with a routing law. *)
Section griotte_lang_traps.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th} {CR : CritRoute Σ th CL}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.

  (* The obligation of a fault from the PC [w]: under an update at the time
     of the fault, a posture [b], the resources of trap entry at [b] and the
     continuation from the trap vector [mtcc_vec]. Sealed: clients consume
     it with [wp_trap] and produce it through [trap_safe_entry_intro] and its
     forms [trap_safe_window_intro] and [trap_safe_posture_intro]. The
     continuation receives a cause that satisfies the cause predicate
     [P_mcause] and a value that satisfies the value predicate [P_mtval]
     ([trap_safe] for the fault causes and any value). *)
  Definition trap_safe_def (P_mcause P_mtval : Z → Prop) (w : LWord) (E : coPset)
    (Φ : tval (kind_of th) → iProp Σ) : iProp Σ :=
    |={E}=> ∃ ib : InterruptStatus,
      trap_entry_res ib ∗
      ▷ (trap_entry_out_cause P_mcause P_mtval w ib -∗
         PC ↦ₚ lword_of_word mtcc_vec -∗
         WP Exec @ E {{ Φ }}).
  #[local] Definition trap_safe_aux : seal (@trap_safe_def). Proof. by eexists. Qed.
  Definition trap_safe_cause := trap_safe_aux.(unseal).
  #[local] Definition trap_safe_unseal :
    @trap_safe_cause = @trap_safe_def := trap_safe_aux.(seal_eq).

  Lemma trap_safe_entry_intro P_mcause P_mtval w E Φ :
    (|={E}=> ∃ ib : InterruptStatus,
       trap_entry_res ib ∗
       ▷ (trap_entry_out_cause P_mcause P_mtval w ib -∗
          PC ↦ₚ lword_of_word mtcc_vec -∗
          WP Exec @ E {{ Φ }})) -∗
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof. rewrite trap_safe_unseal. by iIntros "H". Qed.

  (** The window form: at InterruptDisabled, the fault takes only
      [handover_res]; the rest of the posture stays with the code. *)
  Lemma trap_safe_window_intro P_mcause P_mtval w E Φ :
    MIE_frag InterruptDisabled -∗
    handover_res -∗
    ▷ (trap_entry_out_cause P_mcause P_mtval w InterruptDisabled -∗
       PC ↦ₚ lword_of_word mtcc_vec -∗
       WP Exec @ E {{ Φ }}) -∗
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof.
    iIntros "Hmie Hho Hcont". iApply trap_safe_entry_intro. iModIntro.
    iExists InterruptDisabled. iFrame "Hcont". iApply trap_entry_res_unfold.
    iFrame. done.
  Qed.

  (** The whole-posture form: at InterruptDisabled, the fault takes the
      whole posture; the continuation gets it back, with MPIE, MEPCC, mcause
      and mtval pinned at the values of the entry. *)
  Lemma trap_safe_posture_intro P_mcause P_mtval w E Φ :
    MIE_frag InterruptDisabled -∗
    posture_res -∗
    ▷ (MIE_frag InterruptDisabled -∗
       (∃ c v : Z,
          ⌜P_mcause c⌝ ∗
          ⌜P_mtval v⌝ ∗
          posture_res_gen (Some InterruptDisabled) (Some (lmepcc_of_pc w))
            (Some (lword_of_word (WInt c))) (Some v)) -∗
       PC ↦ₚ lword_of_word mtcc_vec -∗
       WP Exec @ E {{ Φ }}) -∗
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof.
    iIntros "Hmie Hpost Hcont".
    iDestruct (posture_res_held with "Hpost") as "[Hho Hpart]".
    iApply (trap_safe_window_intro with "Hmie Hho"). iNext.
    iIntros "Hout HPC".
    iDestruct (trap_entry_out_handover with "Hout") as "(Hmie & (%c & %v & %Hc & %Hv & Hh) & _)".
    iApply ("Hcont" with "Hmie [Hh Hpart] HPC").
    iExists c, v. iSplit; first done. iSplit; first done.
    iApply (posture_res_gen_intro with "Hh Hpart").
  Qed.

  (** The fault obligation at the posture [b]: the trap vector receives
      MIE disabled and the whole posture, with MPIE at [b] and MEPCC,
      mcause and mtval pinned at the values of trap entry. *)
  Lemma trap_safe_held_intro P_mcause P_mtval w E Φ (b : InterruptStatus) :
    route_pre th b →
    MIE ↦ₜ b -∗
    held b -∗
    ▷ (MIE ↦ₜ InterruptDisabled -∗
       (∃ (b' : InterruptStatus) (c v : Z),
          ⌜route_pre th b'⌝ ∗
          ⌜P_mcause c⌝ ∗
          ⌜P_mtval v⌝ ∗
          posture_res_gen (Some b') (Some (lmepcc_of_pc w))
            (Some (lword_of_word (WInt c))) (Some v)) -∗
       PC ↦ₚ lword_of_word mtcc_vec -∗
       WP Exec @ E {{ Φ }}) -∗
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof.
    iIntros (Hpre) "Hmie Hheld Hcont".
    iApply trap_safe_entry_intro. iModIntro. iExists b. rewrite /held /held_of.
    iAssert ((if b is InterruptDisabled then handover_res else True) ∗
             (if b is InterruptDisabled then posture_part (th := th) else True))%I
      with "[Hheld]" as "[Hho Hpart]".
    { destruct b; [done | iExact "Hheld"]. }
    iSplitL "Hmie Hho".
    { iApply trap_entry_res_unfold. by iFrame. }
    iIntros "!> Hout HPC".
    iDestruct (trap_entry_out_handover with "Hout")
      as "(Hmie & (%c & %v & %Hc & %Hv & Hh) & Hpart')".
    iApply ("Hcont" with "Hmie [Hh Hpart Hpart'] HPC").
    iExists b, c, v. do 3 (iSplit; first done).
    iApply (posture_res_gen_intro with "Hh"). destruct b; [iExact "Hpart'" | iExact "Hpart"].
  Qed.

  (** The fault obligation at the posture [b], as [trap_safe_held_intro],
      with MPIE pinned at [b]: the trap vector receives the posture of the
      fault. *)
  Lemma trap_safe_held_pinned_intro P_mcause P_mtval w E Φ (b : InterruptStatus) :
    route_pre th b →
    MIE ↦ₜ b -∗
    held b -∗
    ▷ (MIE ↦ₜ InterruptDisabled -∗
       (∃ c v : Z,
          ⌜P_mcause c⌝ ∗
          ⌜P_mtval v⌝ ∗
          posture_res_gen (Some b) (Some (lmepcc_of_pc w))
            (Some (lword_of_word (WInt c))) (Some v)) -∗
       PC ↦ₚ lword_of_word mtcc_vec -∗
       WP Exec @ E {{ Φ }}) -∗
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof.
    iIntros (Hpre) "Hmie Hheld Hcont".
    iApply trap_safe_entry_intro. iModIntro. iExists b. rewrite /held /held_of.
    iAssert ((if b is InterruptDisabled then handover_res else True) ∗
             (if b is InterruptDisabled then posture_part (th := th) else True))%I
      with "[Hheld]" as "[Hho Hpart]".
    { destruct b; [done | iExact "Hheld"]. }
    iSplitL "Hmie Hho".
    { iApply trap_entry_res_unfold. by iFrame. }
    iIntros "!> Hout HPC".
    iDestruct (trap_entry_out_handover with "Hout")
      as "(Hmie & (%c & %v & %Hc & %Hv & Hh) & Hpart')".
    iApply ("Hcont" with "Hmie [Hh Hpart Hpart'] HPC").
    iExists c, v. do 2 (iSplit; first done).
    iApply (posture_res_gen_intro with "Hh"). destruct b; [iExact "Hpart'" | iExact "Hpart"].
  Qed.

  (** Stronger cause and value predicates. *)
  Lemma trap_safe_cause_mono (P_mcause P_mcause' P_mtval P_mtval' : Z → Prop) w E Φ :
    (∀ c : Z, P_mcause c → P_mcause' c) →
    (∀ v : Z, P_mtval v → P_mtval' v) →
    trap_safe_cause P_mcause' P_mtval' w E Φ -∗
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof.
    rewrite trap_safe_unseal /trap_safe_def. iIntros (HP_mcause HP_mtval) ">(%ib & $ & Hcont)".
    iIntros "!> !> Hout". iApply "Hcont". by iApply (trap_entry_out_cause_mono with "Hout").
  Qed.

  (** [trap_safe_cause] under an update. *)
  Lemma trap_safe_fupd (P_mcause P_mtval : Z → Prop) (w : LWord) (E : coPset)
    (Φ : tval (kind_of th) → iProp Σ) :
    (|={E}=> trap_safe_cause P_mcause P_mtval w E Φ) ⊢
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof.
    rewrite trap_safe_unseal /trap_safe_def.
    iIntros ">H". iExact "H".
  Qed.

  (* A fault, for a cause predicate [P_mcause] and a value predicate
     [P_mtval] that the physical cause and value satisfy in every state that
     erases to logical registers and memory containing [lregs] and the words
     of [lm]. Each cell of [lm] is held at its own fraction. The register and
     memory points-to are given back before the obligation
     [trap_safe_cause P_mcause P_mtval w E Φ]. *)
  Lemma wp_trap_gen_frac E Φ w (P_mcause P_mtval : Z → Prop) (lregs : LReg)
    (lm : gmap Addr (dfrac * LWord)) :
    (∀ R C σ lreg lsreg lmem,
       erasure R C σ w lreg lsreg lmem → lregs ⊆ lreg → (snd <$> lm) ⊆ lmem →
       P_mcause (trap_cause σ) ∧ P_mtval (trap_tval σ)) →
    PC ↦ₚ w -∗
    ([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
    ([∗ map] a ↦ qx ∈ lm, a ↦ₐ{qx.1} qx.2) -∗
    (([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
     ([∗ map] a ↦ qx ∈ lm, a ↦ₐ{qx.1} qx.2) -∗
     trap_safe_cause P_mcause P_mtval w E Φ) -∗
    WP Seq (Instr Faulted) @ E {{ Φ }}.
  Proof.
    rewrite trap_safe_unseal /trap_safe_def trap_entry_res_unseal trap_entry_out_unseal.
    iIntros (HP_mcause) "HPC Hregs Hmem Hsafe".
    iApply wp_lift_base_step; first done.
    iIntros (σ1 ns κ κs nt) "(Hσ & %Hrdom & Hlink & Hirq) /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    (* The whole PC fragment refutes the parked half: the clause is
       dropped, and re-established after the entry, at MIE disabled. *)
    iDestruct (ctx_irq_si_held with "Hirq HPC") as "[_ HPC]".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hregs") as %Hregs.
    iAssert ⌜(snd <$> lm) ⊆ lmem⌝%I as %Hmem.
    { rewrite map_subseteq_spec. iIntros (a x Ha).
      rewrite lookup_fmap in Ha.
      destruct (lm !! a) as [ [q x']|] eqn:Hlm; last done.
      injection Ha as <-.
      iDestruct (big_sepM_lookup_acc with "Hmem") as "[Ha _]"; first exact Hlm.
      iApply (gen_heap_valid with "Hm Ha"). }
    pose proof (HP_mcause _ _ _ _ _ _ Her Hregs Hmem) as [Hcause Htval].
    iMod ("Hsafe" with "Hregs Hmem") as (ib) "[(%Hpre & Hmie_f & Hho) HΦ]".
    (* The posture before the fault. *)
    iDestruct (sys_interp_mie_agree with "Hsr Hmie_f") as %<-.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    (* [handover_res], from the thread at InterruptDisabled, from the link
       at InterruptEnabled; the link of the state after the entry, where MIE
       is disabled and mtdc is unchanged. *)
    iAssert (|==> handover_res ∗
               (∀ σ2, cerise_state_interp σ2 -∗
                      ⌜mie_st σ2 = InterruptDisabled⌝ -∗
                      ⌜sreg σ2 !! mtdc = sreg σ1 !! mtdc⌝ ==∗
                      cerise_state_interp σ2 ∗
                      crit_link σ2 ∗
                      (if ls_mie lsreg is InterruptEnabled then @posture_part _ _ _ th CL CR
                       else True)))%I
      with "[Hlink Hho]" as ">[Hho Hrestore]".
    { destruct (ls_mie lsreg) eqn:Hib.
      - iMod (crit_route σ1 with "Hlink []") as "[$ Hr]";
          [by rewrite Hmie_st | by rewrite Hmie_st |].
        iIntros "!>" (σ2) "HSI %Hd %_".
        iMod ("Hr" with "HSI []") as "($ & $ & Hp)"; first by rewrite Hd.
        by rewrite Hd.
      - iFrame "Hho". iIntros "!>" (σ2) "$ %Hd %Hm !>". iSplit; last done.
        iApply (crit_link_stable with "Hlink"); congruence. }
    iDestruct (handover_res_unfold with "Hho")
      as (p0 c0 v0 b0) "(Hcrit & HU & Hvcsr)".
    iDestruct (sys_interp_mtcc with "Hsr HU") as %Htcc.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Htcc) as (wtcc & Hwtcc & Hreltcc).
    (* The trap vector is an executable capability, so its physical copy is
       exact. *)
    assert (wtcc = mtcc_vec) as ->.
    { destruct (er_sreg_pc_ok _ _ _ _ _ _ _ Her mtcc _ eq_refl Htcc mtcc_vec_tagged)
        as [_ Hx].
      apply (reg_phys_executable R C (lword_of_word mtcc_vec)).
      - by apply (er_sreg_words _ _ _ _ _ _ _ Her mtcc).
      - exact Hreltcc.
      - apply mtcc_vec_tagged.
      - exact Hx. }
    assert (trap_halts σ1 = false) as Hnh.
    { by rewrite /trap_halts /sreg_word Hwtcc /= mtcc_vec_tagged andb_false_r. }
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. eexists [], _, _, []. by apply TS_trap. }
    iNext. iIntros (e2 σ2 efs Hstep) "_".
    inversion Hstep as [| | | σ' Hnot_halts | σ' Hhalts |]; subst; last congruence.
    iMod "Hclose" as "_".
    iMod (enter_exc_update σ1 (trap_cause σ1, trap_tval σ1)
            with "HPCa Hr Hsr Hm Hst HR HC HPC Hmie_f HU Hvcsr")
      as "(_ & %Hoff' & HSI & HPC & Hmie_f & HU & Hmepcc & Hmcause & Hmtval & Hmpie_f)";
      first exact Her.
    iMod ("Hrestore" with "HSI [//] []") as "(HSI & Hlink & Hpart)".
    { iPureIntro. destruct σ1 as [pc1 r1 sr1 m1 st1 td1].
      rewrite /enter_exc /=. by rewrite !lookup_insert_ne. }
    iModIntro. iSplitL "HSI Hlink".
    { iFrame "HSI Hlink". iSplitR; first (iPureIntro; exact Hrdom).
      iApply (ctx_irq_si_kept _ _ _ (λ _, Hoff')). apply sys_kept_refl. }
    iSplitL; last done.
    iApply ("HΦ" with "[$Hmie_f $Hcrit $HU $Hmepcc Hmcause Hmtval Hmpie_f Hpart] HPC").
    iFrame "Hmpie_f Hpart".
    iSplitL "Hmcause"; [iExists (trap_cause σ1) | iExists (trap_tval σ1)]; by iFrame.
  Qed.

  (* A fault, from the configuration a faulting instruction returns: trap
     entry, then the continuation from the trap vector. MTCC holds the tagged
     trap vector [mtcc_vec], so the machine never stops on a fault. MEPCC
     receives the PC, untagged if it is not a correct PC and without
     identifier ([lmepcc_of_pc]), and the PC receives the trap vector. *)
  Lemma wp_trap E Φ w :
    PC ↦ₚ w -∗
    trap_safe_cause mcause_ok (λ _ : Z, True%type) w E Φ -∗
    WP Seq (Instr Faulted) @ E {{ Φ }}.
  Proof.
    iIntros "HPC Hsafe".
    iApply (wp_trap_gen_frac _ _ _ mcause_ok (λ _ : Z, True%type) ∅ ∅
             with "HPC [] [] [Hsafe]").
    - intros R C σ lreg lsreg lmem _ _ _. split; [apply trap_cause_ok | done].
    - by rewrite big_sepM_empty.
    - by rewrite big_sepM_empty.
    - iIntros "_ _". iExact "Hsafe".
  Qed.

  (* A fetch fault: the PC is not a correct PC. *)
  Lemma wp_notCorrectPC_trap E Φ w :
    ¬ isCorrectPC w.(lw) →
    PC ↦ₚ w -∗
    trap_safe_cause mcause_ok (λ _ : Z, True%type) w E Φ -∗
    WP Exec @ E {{ Φ }}.
  Proof.
    iIntros (Hnpc) "HPC Htrap".
    iApply (wp_bind (@fill (tlang_ectx _) [SeqCtx])).
    iApply (wp_notCorrectPC with "HPC"); first done.
    iIntros "!> HPC /=".
    iApply (wp_trap with "HPC Htrap").
  Qed.

  (** ** Faults once mtcc is wedged *)

  (* A fault with a tagged PC once mtcc is wedged: trap entry writes
     MEPCC, mcause, mtval and MPIE as usual, and the PC receives the
     untagged word that mtcc holds. *)
  Lemma wp_trap_wedged E Φ (w p c : LWord) (v : Z) (b : InterruptStatus) :
    get_tag w.(lw) = true →
    mtcc_wedged -∗
    PC ↦ₚ w -∗
    MIE_frag InterruptDisabled -∗
    volatile_csr_at p c v b -∗
    ▷ (∀ wv : LWord,
         ⌜get_tag wv.(lw) = false⌝ -∗
         PC ↦ₚ wv -∗
         MIE_frag InterruptDisabled -∗
         (∃ c' v' : Z,
            volatile_csr_at (lmepcc_of_pc w) (lword_of_word (WInt c')) v' InterruptDisabled) -∗
         WP Exec @ E {{ Φ }}) -∗
    WP Seq (Instr Faulted) @ E {{ Φ }}.
  Proof.
    iIntros (Htag) "#Hwedged HPC Hmie_f Hvcsr Hcont".
    iApply wp_lift_base_step; first done.
    iIntros (σ1 ns κ κs nt) "(Hσ & %Hrdom & Hlink & Hirq) /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (ctx_irq_si_held with "Hirq HPC") as "[_ HPC]".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    iDestruct (sys_interp_mie_agree with "Hsr Hmie_f") as %Hmie.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    iDestruct (sys_interp_mtcc_wedged with "Hsr Hwedged") as %(wv & Hwv & Hwv_tag).
    (* The PC is tagged, so the machine enters the exception handler. *)
    assert (trap_halts σ1 = false) as Hnh.
    { by rewrite /trap_halts (erasure_pc_exact _ _ _ _ _ _ _ Her) Htag. }
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. eexists [], _, _, []. by apply TS_trap. }
    iNext. iIntros (e2 σ2 efs Hstep) "_".
    inversion Hstep as [| | | σ' Hnot_halts | σ' Hhalts |]; subst; last congruence.
    iMod "Hclose" as "_".
    iMod (enter_exc_update_wedged σ1 (trap_cause σ1, trap_tval σ1) _ _ _ _ _ _ _ _ _ _ _ wv
            Her Hwv with "HPCa Hr Hsr Hm Hst HR HC HPC Hmie_f Hvcsr")
      as "(_ & %Hoff' & HSI & HPC & Hmie_f & Hvcsr)".
    (* MIE stays disabled and mtdc is unchanged: the link is kept. *)
    iModIntro. iSplitL "HSI Hlink".
    { iFrame "HSI". iSplitR; first (iPureIntro; exact Hrdom).
      iSplitL "Hlink".
      - iApply (crit_link_stable with "Hlink"); first congruence.
        destruct σ1 as [pc1 r1 sr1 m1 st1 td1].
        rewrite /enter_exc /=. by rewrite !lookup_insert_ne.
      - iApply (ctx_irq_si_kept _ _ _ (λ _, Hoff')). apply sys_kept_refl. }
    iSplitL; last done.
    iApply ("Hcont" with "[//] HPC Hmie_f").
    iExists (trap_cause σ1), (trap_tval σ1). iExact "Hvcsr".
  Qed.

  (* A fault with an untagged PC once mtcc is wedged: the machine stops,
     and the thread's value is [FaultedV]. *)
  Lemma wp_trap_halt_wedged E Φ (w : LWord) :
    get_tag w.(lw) = false →
    mtcc_wedged -∗
    PC ↦ₚ w -∗
    ▷ (PC ↦ₚ w -∗ Φ FaultedV) -∗
    WP Seq (Instr Faulted) @ E {{ Φ }}.
  Proof.
    iIntros (Htag) "#Hwedged HPC Hcont".
    iApply wp_lift_base_step; first done.
    iIntros (σ1 ns κ κs nt) "(Hσ & %Hrdom & Hlink & Hirq) /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (ctx_irq_si_held with "Hirq HPC") as "[%Hoff HPC]".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    iDestruct (sys_interp_mtcc_wedged with "Hsr Hwedged") as %(wv & Hwv & Hwv_tag).
    (* Neither the PC nor the physical mtcc is tagged: the machine stops. *)
    assert (trap_halts σ1 = true) as Hh.
    { destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hwv) as (wtcc & Hwtcc & Hrel).
      rewrite /trap_halts /sreg_word (erasure_pc_exact _ _ _ _ _ _ _ Her) Htag Hwtcc /=.
      destruct (reg_phys_cases _ _ _ Hrel) as [-> | ->]; first by rewrite Hwv_tag.
      by rewrite get_tag_clear_tag. }
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit.
    { iPureIntro. eexists [], _, _, []. by apply TS_trap_halt. }
    iNext. iIntros (e2 σ2 efs Hstep) "_".
    inversion Hstep as [| | | σ' Hnot_halts | σ' Hhalts |]; subst; first congruence.
    iMod "Hclose" as "_".
    iModIntro. iSplitR "HPC Hcont".
    { iFrame "Hlink". iSplitL.
      - iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
      - iSplitR; first (iPureIntro; exact Hrdom).
        iApply (ctx_irq_si_kept _ _ _ Hoff). apply sys_kept_refl. }
    iSplitL; last done.
    iApply wp_value. iApply ("Hcont" with "HPC").
  Qed.

End griotte_lang_traps.

(** The resources and the obligation of trap entry for the fault causes
    [mcause_ok] and any value. *)
Notation trap_entry_out := (trap_entry_out_cause mcause_ok (λ _ : Z, True%type)).
Notation trap_safe := (trap_safe_cause mcause_ok (λ _ : Z, True%type)).

(* Closes a fault [WP Seq (Instr Faulted) @ E {{ Φ }}] with [wp_trap], from
   the PC points-to [PC ↦ₚ w] of the context.
   [iTrap] closes the obligation [trap_safe w E Φ] with a hypothesis of the
   context, and fails if none matches.
   [iTrap with "H"] closes the obligation by applying a fault premise ["H"]
   of the form [∀ a, ⌜range⌝ -∗ R -∗ trap_safe (WCap … a) E Φ] (or
   [R -∗ trap_safe w E Φ]): the range side condition is solved with
   [solve_addr], or left to the caller as a pure goal, and the resources
   [R] are framed from the context. *)
Ltac instr_trap_pc :=
  lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ =>
    lazymatch Γs with
    | context [ Esnoc _ ?hpc (PC ↦ₚ _)%I ] => hpc
    | _ => fail "iTrap: no PC points-to in the spatial context"
    end
  end.

Ltac instr_trap_start :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (@Seq ?k ?e) _) => unify e (@Instr k Faulted)
  | _ => fail "iTrap: the goal is not a fault WP Seq (Instr Faulted)"
  end;
  let hpc := instr_trap_pc in
  let pat := constr:(cons (SIdent hpc nil) nil) in
  iApply (wp_trap with pat).

Tactic Notation "iTrap" :=
  instr_trap_start;
  first [ iAssumption
        | fail "iTrap: no hypothesis trap_safe w E Φ in the context; use iTrap with" ].
Tactic Notation "iTrap" "with" constr(H) :=
  instr_trap_start;
  iApply H;
  [ try (iPureIntro; try solve_addr) .. ];
  try iFrame.

