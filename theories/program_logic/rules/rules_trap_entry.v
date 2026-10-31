From iris.proofmode Require Import proofmode environments spec_patterns.
From griotte Require Export rules_base.

(** * Trap entry

    The fault causes, the trap-entry tokens and the trap-entry windows of
    the state interpretation (MEPCC, mcause and mtval), the obligation
    [trap_safe] of a fault and the rules of trap entry, at the core link
    (trap entry writes MIE), and the [iTrap] tactic. *)

Section trap_entry_windows.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {CL : CritLink Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types w : LWord.

  (* ----------------------------------- TRAPS --------------------------------------- *)

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

  (** The trap-entry token is the token exchanged for MEPCC and mcause, and
      the one of [Ntval], exchanged for mtval. *)
  #[local] Lemma trap_token_split :
    na_own cerise_pool (↑Ntrap) ⊣⊢
    na_own cerise_pool (↑Ntrap ∖ ↑Ntval) ∗ na_own cerise_pool (↑Ntval).
  Proof.
    assert (↑Ntval ⊆@{coPset} ↑Ntrap) as Hsub by (rewrite /Ntval; solve_ndisj).
    rewrite -na_own_union; last set_solver.
    rewrite difference_union_L. f_equiv. set_solver.
  Qed.

  #[local] Lemma trap_vcsr_token_excl :
    na_own cerise_pool (↑Ntrap ∖ ↑Ntval) -∗ na_own cerise_pool (↑Ntrap ∖ ↑Ntval) -∗ False.
  Proof.
    iIntros "Htok Htok'". iDestruct (na_own_disjoint with "Htok Htok'") as %Hdisj.
    destruct (nclose_infinite (Ntrap .@ "vcsr") []) as (i & Hi & _).
    assert (↑Ntrap .@ "vcsr" ⊆@{coPset} ↑Ntrap ∖ ↑Ntval) as Hsub
      by (rewrite /Ntval; solve_ndisj).
    set_solver.
  Qed.

  #[local] Lemma trap_tval_token_excl :
    na_own cerise_pool (↑Ntval) -∗ na_own cerise_pool (↑Ntval) -∗ False.
  Proof.
    iIntros "Htok Htok'". iDestruct (na_own_disjoint with "Htok Htok'") as %Hdisj.
    destruct (nclose_infinite Ntval []) as (i & Hi & _). set_solver.
  Qed.

  (* The resources trap entry consumes, and those it gives back to the
     continuation from the trap vector, for a fault from the PC [w]: the
     trap-entry token, and MEPCC, mcause with a cause that satisfies the
     cause predicate [P_mcause], and mtval with a value that satisfies the
     value predicate [P_mtval] ([trap_entry_out] for the fault causes and any
     value). Sealed: [trap_entry_res_split] relates the token to the
     non-atomic token, [trap_entry_res_vcsr_tval] splits it into the parts
     exchanged for MEPCC and mcause ([trap_vcsr_res]) and for mtval
     ([trap_tval_res]), and [trap_entry_out_unfold] gives the registers. *)
  Definition trap_entry_res_def : iProp Σ := na_own cerise_pool (↑Ntrap).
  #[local] Definition trap_entry_res_aux : seal (@trap_entry_res_def). Proof. by eexists. Qed.
  Definition trap_entry_res := trap_entry_res_aux.(unseal).
  #[local] Definition trap_entry_res_unseal :
    @trap_entry_res = @trap_entry_res_def := trap_entry_res_aux.(seal_eq).

  Definition trap_vcsr_res_def : iProp Σ := na_own cerise_pool (↑Ntrap ∖ ↑Ntval).
  #[local] Definition trap_vcsr_res_aux : seal (@trap_vcsr_res_def). Proof. by eexists. Qed.
  Definition trap_vcsr_res := trap_vcsr_res_aux.(unseal).
  #[local] Definition trap_vcsr_res_unseal :
    @trap_vcsr_res = @trap_vcsr_res_def := trap_vcsr_res_aux.(seal_eq).

  Definition trap_tval_res_def : iProp Σ := na_own cerise_pool (↑Ntval).
  #[local] Definition trap_tval_res_aux : seal (@trap_tval_res_def). Proof. by eexists. Qed.
  Definition trap_tval_res := trap_tval_res_aux.(unseal).
  #[local] Definition trap_tval_res_unseal :
    @trap_tval_res = @trap_tval_res_def := trap_tval_res_aux.(seal_eq).

  Definition trap_entry_out_def (P_mcause P_mtval : Z → Prop) (w : LWord) : iProp Σ :=
    mepcc ↦ₓ lmepcc_of_pc w ∗
    (∃ c : Z, ⌜P_mcause c⌝ ∗ mcause ↦ₓ lword_of_word (WInt c)) ∗
    (∃ v : Z, ⌜P_mtval v⌝ ∗ mtval ↦ₓ lword_of_word (WInt v)).
  #[local] Definition trap_entry_out_aux : seal (@trap_entry_out_def). Proof. by eexists. Qed.
  Definition trap_entry_out_cause := trap_entry_out_aux.(unseal).
  #[local] Definition trap_entry_out_unseal :
    @trap_entry_out_cause = @trap_entry_out_def := trap_entry_out_aux.(seal_eq).

  (** The trap-entry token is the part exchanged for MEPCC and mcause, and
      the part exchanged for mtval. *)
  Lemma trap_entry_res_vcsr_tval :
    trap_entry_res ⊣⊢ trap_vcsr_res ∗ trap_tval_res.
  Proof.
    rewrite trap_entry_res_unseal trap_vcsr_res_unseal trap_tval_res_unseal.
    apply trap_token_split.
  Qed.

  (** The resources trap entry gives back, unfolded into MEPCC, mcause and
      mtval ([rules_vcsr] turns them into the views of the lent registers). *)
  Lemma trap_entry_out_unfold P_mcause P_mtval w :
    trap_entry_out_cause P_mcause P_mtval w ⊣⊢
    mepcc ↦ₓ lmepcc_of_pc w ∗
    (∃ c : Z, ⌜P_mcause c⌝ ∗ mcause ↦ₓ lword_of_word (WInt c)) ∗
    (∃ v : Z, ⌜P_mtval v⌝ ∗ mtval ↦ₓ lword_of_word (WInt v)).
  Proof. by rewrite trap_entry_out_unseal. Qed.

  (** Weaker cause and value predicates. *)
  Lemma trap_entry_out_cause_mono (P_mcause P_mcause' P_mtval P_mtval' : Z → Prop) w :
    (∀ c : Z, P_mcause c → P_mcause' c) →
    (∀ v : Z, P_mtval v → P_mtval' v) →
    trap_entry_out_cause P_mcause P_mtval w -∗
    trap_entry_out_cause P_mcause' P_mtval' w.
  Proof.
    rewrite trap_entry_out_unseal.
    iIntros (HP_mcause HP_mtval) "[$ [(%c & %Hc & Hmcause) (%v & %Hv & Hmtval)] ]".
    iSplitL "Hmcause"; [iExists c | iExists v]; iFrame; iPureIntro;
      [by apply HP_mcause | by apply HP_mtval].
  Qed.

  (** Lending MEPCC and mcause from the state interpretation, against the
      trap-entry token without [Ntval]. *)
  Lemma sys_interp_trap_lend lsreg :
    sys_interp lsreg -∗
    trap_vcsr_res -∗
    ∃ wepcc wcause,
      ⌜ls_join lsreg !! mepcc = Some wepcc ∧ ls_join lsreg !! mcause = Some wcause⌝ ∗
      sys_interp lsreg ∗
      mepcc ↦ₓ wepcc ∗
      mcause ↦ₓ wcause.
  Proof.
    rewrite trap_vcsr_res_unseal.
    iIntros "Hsys Htok". iNamed "Hsys". iDestruct "Hwins" as "[Hwin Hwin_tval]".
    iDestruct "Hwin" as "[ [ [%wepcc Hmepcc] [%wcause Hmcause] ] | Htok']"; last first.
    { iDestruct (trap_vcsr_token_excl with "Htok Htok'") as %[]. }
    iDestruct (gen_heap_valid with "Hsr Hmepcc") as %Hmepcc.
    iDestruct (gen_heap_valid with "Hsr Hmcause") as %Hmcause.
    iExists wepcc, wcause. iSplit.
    { iPureIntro. by rewrite /ls_join !lsregs_join_ne. }
    iFrame "Hmepcc Hmcause Hsr Hmtcc Hmpie Hmpie_f Hmtdc Hmie Hmie_f".
    iSplit; first done. iSplitL "Htok Hwin_tval"; last (iPureIntro; done).
    iFrame "Hwin_tval". by iRight.
  Qed.

  (** The return of MEPCC and mcause to the state interpretation: the
      trap-entry token without [Ntval] comes back. *)
  Lemma sys_interp_trap_return lsreg wepcc wcause :
    sys_interp lsreg -∗
    mepcc ↦ₓ wepcc -∗
    mcause ↦ₓ wcause -∗
    ⌜ls_join lsreg !! mepcc = Some wepcc ∧ ls_join lsreg !! mcause = Some wcause⌝ ∗
    sys_interp lsreg ∗
    trap_vcsr_res.
  Proof.
    rewrite trap_vcsr_res_unseal.
    iIntros "Hsys Hmepcc Hmcause". iNamed "Hsys". iDestruct "Hwins" as "[Hwin Hwin_tval]".
    iDestruct (gen_heap_valid with "Hsr Hmepcc") as %Hmepcc.
    iDestruct (gen_heap_valid with "Hsr Hmcause") as %Hmcause.
    iDestruct "Hwin" as "[ [ [%wepcc' Hmepcc'] _] | Htok]".
    { iDestruct (pointsto_ne with "Hmepcc Hmepcc'") as %Hne. by exfalso; apply Hne. }
    iSplit.
    { iPureIntro. by rewrite /ls_join !lsregs_join_ne. }
    iSplitR "Htok"; last done.
    iFrame "Hsr Hmtcc Hmpie Hmpie_f Hmtdc Hmie Hmie_f".
    iSplit; first done. iSplitL "Hmepcc Hmcause Hwin_tval"; last (iPureIntro; done).
    iFrame "Hwin_tval". iLeft. iSplitL "Hmepcc"; by iExists _.
  Qed.

  (** The return of mtval to the state interpretation: the token of
      [Ntval] comes back. *)
  Lemma sys_interp_tval_return lsreg (z : Z) :
    sys_interp lsreg -∗
    mtval ↦ₓ lword_of_word (WInt z) -∗
    sys_interp lsreg ∗
    trap_tval_res.
  Proof.
    rewrite trap_tval_res_unseal.
    iIntros "Hsys Hmtval". iNamed "Hsys". iDestruct "Hwins" as "[Hwin Hwin_tval]".
    iDestruct "Hwin_tval" as "[ [%z' Hmtval'] | Htok]".
    { iDestruct (pointsto_ne with "Hmtval Hmtval'") as %Hne. by exfalso; apply Hne. }
    iSplitR "Htok"; last done.
    iFrame "Hsr Hmtcc Hmpie Hmpie_f Hmtdc Hmie Hmie_f".
    iSplit; first done. iSplitL "Hmtval Hwin"; last (iPureIntro; done).
    iFrame "Hwin". iLeft. by iExists z.
  Qed.

  (** The return of MEPCC and mcause to the state interpretation, in front
      of any instruction: the trap-entry token without [Ntval] comes
      back. *)
  Lemma wp_trap_entry_return E e Φ (wepcc wcause : LWord) :
    to_val e = None →
    mepcc ↦ₓ wepcc -∗
    mcause ↦ₓ wcause -∗
    (trap_vcsr_res -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "Hmepcc Hmcause HΦ".
    rewrite wp_unfold /wp_pre He.
    iIntros (σ1 ns κ κs nt) "[Hσ Hlink] /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (sys_interp_trap_return with "Hsr Hmepcc Hmcause") as "(_ & Hsr & Htok)".
    iSpecialize ("HΦ" with "Htok").
    iApply ("HΦ" $! σ1 ns κ κs nt). iFrame "Hlink".
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** The return of mtval to the state interpretation, in front of any
      instruction: the token of [Ntval] comes back. *)
  Lemma wp_tval_return E e Φ (z : Z) :
    to_val e = None →
    mtval ↦ₓ lword_of_word (WInt z) -∗
    (trap_tval_res -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "Hmtval HΦ".
    rewrite wp_unfold /wp_pre He.
    iIntros (σ1 ns κ κs nt) "[Hσ Hlink] /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (sys_interp_tval_return with "Hsr Hmtval") as "[Hsr Htok]".
    iSpecialize ("HΦ" with "Htok").
    iApply ("HΦ" $! σ1 ns κ κs nt). iFrame "Hlink".
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

End trap_entry_windows.

(** Trap entry, at the core link: it writes MIE (and MPIE). *)
Section griotte_lang_traps.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.

  (* The obligation of a fault from the PC [w]: either, under an update at
     the time of the fault, the trap-entry token and the continuation from
     the trap vector [mtcc_vec], or the postcondition of a stopped machine.
     Sealed: clients consume it with [wp_trap] and produce it through the
     closing lemmas [interp_trap_safe] (logical relation) and those of the
     exception entry of the switcher (trusted code); [trap_safe_entry_intro]
     is used only by those lemmas. The continuation receives a cause that
     satisfies the cause predicate [P_mcause] and a value that satisfies the
     value predicate [P_mtval] ([trap_safe] for the fault causes and any
     value). *)
  Definition trap_safe_def (P_mcause P_mtval : Z → Prop) (w : LWord) (E : coPset)
    (Φ : griotte_lang.val → iProp Σ) : iProp Σ :=
    (|={E}=> trap_entry_res ∗
       ▷ (trap_entry_out_cause P_mcause P_mtval w -∗
          PC ↦ₚ lword_of_word mtcc_vec -∗
          WP Exec @ E {{ Φ }})) ∧
    ▷ Φ FaultedV.
  #[local] Definition trap_safe_aux : seal (@trap_safe_def). Proof. by eexists. Qed.
  Definition trap_safe_cause := trap_safe_aux.(unseal).
  #[local] Definition trap_safe_unseal :
    @trap_safe_cause = @trap_safe_def := trap_safe_aux.(seal_eq).

  Lemma trap_safe_entry_intro P_mcause P_mtval w E Φ :
    ((|={E}=> trap_entry_res ∗
       ▷ (trap_entry_out_cause P_mcause P_mtval w -∗
          PC ↦ₚ lword_of_word mtcc_vec -∗
          WP Exec @ E {{ Φ }})) ∧
     ▷ Φ FaultedV) -∗
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof. rewrite trap_safe_unseal. by iIntros "H". Qed.

  (** Stronger cause and value predicates. *)
  Lemma trap_safe_cause_mono (P_mcause P_mcause' P_mtval P_mtval' : Z → Prop) w E Φ :
    (∀ c : Z, P_mcause c → P_mcause' c) →
    (∀ v : Z, P_mtval v → P_mtval' v) →
    trap_safe_cause P_mcause' P_mtval' w E Φ -∗
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof.
    rewrite trap_safe_unseal /trap_safe_def. iIntros (HP_mcause HP_mtval) "Hsafe". iSplit.
    - iDestruct "Hsafe" as "[Hentry _]". iMod "Hentry" as "[$ Hcont]". iIntros "!> !> Hout".
      iApply "Hcont". by iApply (trap_entry_out_cause_mono with "Hout").
    - iDestruct "Hsafe" as "[_ $]".
  Qed.

  (** [trap_safe_cause] under an update, for a postcondition that holds of a
      fault. *)
  Lemma trap_safe_fupd (P_mcause P_mtval : Z → Prop) (w : LWord) (E : coPset)
    (Φ : griotte_lang.val → iProp Σ) :
    (|={E}=> trap_safe_cause P_mcause P_mtval w E Φ) ∗
    ▷ Φ FaultedV ⊢
    trap_safe_cause P_mcause P_mtval w E Φ.
  Proof.
    rewrite trap_safe_unseal /trap_safe_def.
    iIntros "[H HΦ]". iSplit; last done.
    iMod "H" as "[H _]". iExact "H".
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
    iIntros (σ1 ns κ κs nt) "[Hσ _] /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
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
    iDestruct ("Hsafe" with "Hregs Hmem") as "[>[Htok HΦ] _]".
    iDestruct (sys_interp_mtcc with "Hsr") as %Htcc.
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
    { iPureIntro. eexists [], _, _, []. by apply PS_no_fork_trap. }
    iNext. iIntros (e2 σ2 efs Hstep) "_".
    inversion Hstep as [| | | σ' Hnot_halts | σ' Hhalts]; subst; last congruence.
    iMod "Hclose" as "_".
    pose proof (erasure_enter_exc _ _ _ _ _ _ _ (trap_cause σ1, trap_tval σ1) _ Her Htcc)
      as Her'.
    (* mstatus: MIE is disabled and MPIE receives MIE. *)
    set (mie_old := mie_of (get_a (sreg_word σ1 mstatus))).
    iMod (sys_interp_set_mstatus _ InterruptDisabled mie_old with "Hsr") as "Hsr".
    iNamed "Hsr". destruct Hlsh as [Hn1 Hn2]. iDestruct "Hwins" as "[Hwin Hwin_tval]".
    (* With the token in hand, MEPCC, mcause and mtval are held. *)
    iDestruct (trap_token_split with "Htok") as "[Htok Htok_tval]".
    iDestruct "Hwin" as "[ [Hmepcc Hmcause] | Htok']"; last first.
    { iDestruct (trap_vcsr_token_excl with "Htok Htok'") as %[]. }
    iDestruct "Hwin_tval" as "[Hmtval | Htok']"; last first.
    { iDestruct (trap_tval_token_excl with "Htok_tval Htok'") as %[]. }
    iDestruct "Hmepcc" as (vepcc) "Hmepcc".
    iDestruct "Hmcause" as (vcause) "Hmcause".
    iDestruct "Hmtval" as (ztval) "Hmtval".
    iMod (gen_heap_update _ _ _ (lmepcc_of_pc w) with "Hsr Hmepcc") as "[Hsr Hmepcc]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt (trap_cause σ1)))
           with "Hsr Hmcause") as "[Hsr Hmcause]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt (trap_tval σ1)))
           with "Hsr Hmtval") as "[Hsr Hmtval]".
    iMod (PC_update _ _ (lword_of_word mtcc_vec) with "HPCa HPC") as "[HPCa HPC]".
    pose (ls' := MkLSys
      (<[mtval := lword_of_word (WInt (trap_tval σ1))]>
        (<[mcause := lword_of_word (WInt (trap_cause σ1))]>
          (<[mepcc := lmepcc_of_pc w]> (ls_sh lsreg))))
      (ls_mtdc lsreg) (ls_vmtdc lsreg) InterruptDisabled mie_old).
    assert (lsregs_enter_exc (trap_cause σ1, trap_tval σ1) σ1 w (ls_join lsreg) = ls_join ls')
      as Hjoin.
    { apply map_eq. intros i.
      rewrite /lsregs_enter_exc /ls' /ls_join /lsregs_join /mie_old /=.
      destruct i; by simplify_map_eq. }
    rewrite Hjoin in Her'.
    iAssert (sys_interp ls')
      with "[Hsr Hmtcc Hmpie Hmpie_f Hmtdc Hmie Hmie_f Htok Htok_tval]" as "Hsys".
    { rewrite /sys_interp /ls'. cbn [ls_sh ls_mtdc ls_vmtdc ls_mie ls_mpie ls_set_mstatus] in *.
      iFrame "Hsr Hmtcc Hmpie Hmpie_f Hmtdc Hmie Hmie_f". iSplit; first done.
      iSplitL "Htok Htok_tval".
      - iSplitL "Htok"; by iRight.
      - iPureIntro. split; by simplify_map_eq. }
    iPoseProof (SI_close (enter_exc (trap_cause σ1, trap_tval σ1) σ1) mtcc_vec lreg ls' lmem R C
                  Her' with "HPCa Hr Hsys Hm Hst HR HC") as "HSI".
    iModIntro. iSplitL "HSI"; first by iFrame "HSI".
    iSplitL; last done.
    iApply ("HΦ" with "[$Hmepcc Hmcause Hmtval] HPC").
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

  (* A fault, for a cause predicate [P_mcause] and a value predicate
     [P_mtval] that the physical cause and value satisfy in every state that
     erases to logical registers and memory containing [lregs] and [lm]. The
     register and memory points-to are given back before the obligation
     [trap_safe_cause P_mcause P_mtval w E Φ]. *)
  Lemma wp_trap_gen E Φ w (P_mcause P_mtval : Z → Prop) (lregs : LReg) (lm : LMem) dq :
    (∀ R C σ lreg lsreg lmem,
       erasure R C σ w lreg lsreg lmem → lregs ⊆ lreg → lm ⊆ lmem →
       P_mcause (trap_cause σ) ∧ P_mtval (trap_tval σ)) →
    PC ↦ₚ w -∗
    ([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
    ([∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x) -∗
    (([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
     ([∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x) -∗
     trap_safe_cause P_mcause P_mtval w E Φ) -∗
    WP Seq (Instr Faulted) @ E {{ Φ }}.
  Proof.
    iIntros (HP) "HPC Hregs Hmem Hsafe".
    iApply (wp_trap_gen_frac _ _ _ _ _ _ ((λ x, (dq, x)) <$> lm)
             with "HPC Hregs [Hmem] [Hsafe]").
    - intros R C σ lreg lsreg lmem Her Hsub Hmsub. apply (HP _ _ _ _ _ _ Her Hsub).
      by rewrite -map_fmap_compose map_fmap_id in Hmsub.
    - by rewrite big_sepM_fmap.
    - rewrite big_sepM_fmap /=. iExact "Hsafe".
  Qed.

  (* A fetch fault: the PC is not a correct PC. *)
  Lemma wp_notCorrectPC_trap E Φ w :
    ¬ isCorrectPC w.(lw) →
    PC ↦ₚ w -∗
    trap_safe_cause mcause_ok (λ _ : Z, True%type) w E Φ -∗
    WP Exec @ E {{ Φ }}.
  Proof.
    iIntros (Hnpc) "HPC Htrap".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_notCorrectPC with "HPC"); first done.
    iIntros "!> HPC /=".
    iApply (wp_trap with "HPC Htrap").
  Qed.

End griotte_lang_traps.

(** The trap-entry token of a thread, against the thread's pool. *)
Section thread_trap_tokens.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread}.

  (** The trap-entry token is part of the non-atomic token of any mask that
      contains [Ntrap]. *)
  Lemma trap_entry_res_split F :
    ↑Ntrap ⊆ F →
    na_own (tpool th) F ⊣⊢ trap_entry_res ∗ na_own (tpool th) (F ∖ ↑Ntrap).
  Proof.
    intros HF. rewrite trap_entry_res_unseal /trap_entry_res_def -na_own_union;
      last set_solver.
    by rewrite -union_difference_L.
  Qed.
End thread_trap_tokens.

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
  | |- envs_entails _ (wp _ _ (Seq ?e) _) => unify e (Instr Faulted)
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

