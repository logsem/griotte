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
  Lemma lsregs_enter_irq_join c σ lpc lsh vm mpie :
    mie_st σ = InterruptEnabled →
    lsregs_enter_irq c σ lpc (lsregs_join lsh vm InterruptEnabled mpie) =
    lsregs_join
      (<[mtval := lword_of_word (WInt MTVAL_NONE)]>
         (<[mcause := lword_of_word (WInt c)]>
            (<[mepcc := lword_of_word lpc.(lw)]> lsh)))
      vm InterruptDisabled InterruptEnabled.
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

Section hw_switches.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)}
    {CSL : ContextSwitchLayout Σ CL CR}.

  #[local] Notation posture_of x :=
    (posture_res_gen (ceriseg := ceriseG_of x) (th := x) (CL := CL x) (CR := CR x)).
  #[local] Notation part_of x :=
    (@posture_part Σ MP (ceriseG_of x) x (CL x) (CR x)).
  (* The shared part of the state interpretation, at the base; the part of
     thread [x], at its instance. *)
  #[local] Notation SI_sh R C σ :=
    (@SI_shared MP Σ (@cb_sreg Σ ceriseb) (@cb_mem Σ ceriseb) (@cb_shadow Σ ceriseb)
       (@cb_registry Σ ceriseb) (@cb_addr_alloc Σ ceriseb) (@cb_trapVector Σ ceriseb)
       (@cb_mpie Σ ceriseb) (@cb_posture Σ ceriseb) R C σ).
  #[local] Notation SI_th_of x R C σ :=
    (@SI_th MP Σ (@cerise_pcG Σ (ceriseG_of x)) (@reg_gen_regG Σ (ceriseG_of x))
       (@cerise_mtdcG Σ (ceriseG_of x)) (@cerise_mieG Σ (ceriseG_of x))
       (@cerise_mtdc_lentG Σ (ceriseG_of x)) R C σ).

  (** * Helpers *)

  Lemma thread_si_unfold th σ :
    thread_si th σ ⊣⊢
    (∃ R C, SI_sh R C σ ∗ SI_th_of th R C σ) ∗
    ⌜dom (reg σ) = all_registers_s⌝ ∗
    @crit_link Σ th (CL th) σ ∗
    ctx_irq_si (ceriseg := ceriseG_of th) (kind_of th) σ.
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
      set to [lpc'], [lreg'], [m'] and InterruptDisabled. *)
  Lemma idle_load lpc' lreg' m' :
    dom lreg' = all_registers_s →
    idle_CtxSwitch
    ==∗
    thread_auths (th := CtxSwitch) lpc' lreg' m' InterruptDisabled ∗
    PC ↦ₚ[CtxSwitch] lpc' ∗
    regs[CtxSwitch] lreg' ∗
    mtdc ↦ₜ[CtxSwitch] m' ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    mtdc_lent_at (th := CtxSwitch) ∗
    scheduler_state ∗
    na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
    close_Nact.
  Proof.
    iIntros (Hdom') "Hidle". iNamed "Hidle".
    iDestruct "Hauths" as "(HPCa & Hr & Hmtdc_a & HMIE_a)".
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iMod (regs_copy lreg lreg' with "Hr Hregs") as "[Hr Hregs]".
    { by rewrite Hdom Hdom'. }
    iMod (mtdc_update _ _ m' with "Hmtdc_a Hmtdc") as "[Hmtdc_a Hmtdc]".
    iMod (MIE_update _ _ InterruptDisabled with "HMIE_a HMIE") as "[HMIE_a HMIE]".
    iModIntro. rewrite /thread_auths. iFrame.
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
      vector with a copy of [t]'s registers, and [t]'s posture pinned to the
      values the entry wrote. *)
  Lemma irq_hand_in t σ (c : Z) :
    mie_st σ = InterruptEnabled →
    thread_si (UserThread t) σ -∗
    idle_CtxSwitch
    ==∗
    ∃ (lpc : LWord) (lreg : LReg),
      "Hsi" ∷ thread_si CtxSwitch (enter_irq c σ) ∗
      "Hauths" ∷ auths_at t (ResumeVals lreg lpc InterruptEnabled) ∗
      "%Hdom" ∷ ⌜dom lreg = all_registers_s⌝ ∗
      "%Hpc" ∷ ⌜get_tag lpc.(lw) = true → lpc.(lprov) = None⌝ ∗
      "HPC" ∷ PC ↦ₚ[CtxSwitch] lword_of_word mtcc_vec ∗
      "Hregs" ∷ regs[CtxSwitch] lreg ∗
      "HMIE" ∷ MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
      "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread t)) ∗
      "Hposture" ∷ posture_of (UserThread t) (Some InterruptEnabled)
        (Some (lword_of_word lpc.(lw))) (Some (lword_of_word (WInt c))) (Some MTVAL_NONE) ∗
      "Hsched" ∷ scheduler_state ∗
      "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
      "Hclose" ∷ close_Nact.
  Proof.
    iIntros (Hen) "Hsi Hidle".
    iDestruct (thread_si_unfold with "Hsi") as "(HSI & %Hdom_σ & Hlink & _)".
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
    (* The erasure at the interrupt entry. *)
    iDestruct (gen_heap_valid with "Hsr Hmtcc") as %Htcc0.
    pose proof (erasure_join R C σ lpc lreg lsh vm mie mpie lmem Hersh Herth) as Her.
    assert (mie = InterruptEnabled) as ->.
    { rewrite -Hen. symmetry. by eapply erasure_th_mie_st. }
    assert (lsregs_join lsh vm InterruptEnabled mpie !! mtcc = Some (lword_of_word mtcc_vec))
      as Htcc by rewrite lsregs_join_ne //.
    pose proof (erasure_enter_irq R C σ lpc lreg _ lmem c _ Her Htcc) as Her'.
    rewrite lsregs_enter_irq_join // in Her'.
    set (lsh' := <[mtval := lword_of_word (WInt MTVAL_NONE)]>
                   (<[mcause := lword_of_word (WInt c)]>
                      (<[mepcc := lword_of_word lpc.(lw)]> lsh))).
    destruct (erasure_split R C (enter_irq c σ) (lword_of_word mtcc_vec) lreg lsh' vm
                InterruptDisabled InterruptEnabled lmem) as [Hsh' Hth']; [ | | exact Her' | ].
    { rewrite /lsh' !lookup_insert_ne //. apply (es_no_mtdc _ _ _ _ _ _ Hersh). }
    { rewrite /lsh' !lookup_insert_ne //. apply (es_no_mstatus _ _ _ _ _ _ Hersh). }
    (* The volatile registers and MPIE take the values the entry wrote. *)
    iMod (gen_heap_update _ _ _ (lword_of_word lpc.(lw)) with "Hsr Hmepcc") as "[Hsr Hmepcc]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt c)) with "Hsr Hmcause") as "[Hsr Hmcause]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt MTVAL_NONE)) with "Hsr Hmtval")
      as "[Hsr Hmtval]".
    iMod (MPIE_update _ _ InterruptEnabled with "Hmpie Hmpie_f") as "[Hmpie Hmpie_f]".
    iMod (idle_load (lword_of_word mtcc_vec) lreg m with "Hidle")
      as "(Hauths_s & HPC_s & Hregs_s & Hmtdc_s & HMIE_s & Hlent_s & Hsched & Hna & Hclose)".
    { rewrite -Hdom_σ. symmetry. apply (et_regs _ _ _ _ _ _ _ Herth). }
    subst m.
    iModIntro. iExists lpc, lreg.
    iSplitL "Hmtcc Hpend Hm Hst HR HC Hsr Hmpie Hauths_s Hlent_s".
    { iApply thread_si_unfold. iSplitL.
      - iExists R, C. iSplitL "Hmtcc Hpend Hm Hst HR HC Hsr Hmpie".
        + iExists lsh', lmem, InterruptEnabled. rewrite shadowtbl_enter_irq.
          iFrame "Hsr Hm Hst HR HC Hmpie". iSplitL; [iLeft; iFrame | done].
        + (* The context-switch thread's clause holds its token. *)
          iDestruct "Hauths_s" as "(HPCa_s & Hr_s & Hmtdc_a & HMIE_a)".
          iExists (lword_of_word mtcc_vec), lreg, _, vm, InterruptDisabled.
          iFrame. iSplit; done.
      - iSplit; first by rewrite reg_enter_irq. iSplitR.
        + iApply csl_link_disabled. by eapply erasure_th_mie_st.
        + cbn [ctx_irq_si kind_of]. iLeft. iPureIntro. by eapply erasure_th_mie_st. }
    iSplitL "HPCa Hr Hmtdc Hmie".
    { rewrite /auths_at /thread_auths. cbn [rv_pc rv_regs rv_mie]. iFrame. }
    iSplitR.
    { iPureIntro. rewrite -Hdom_σ. symmetry. apply (et_regs _ _ _ _ _ _ _ Herth). }
    iSplitR.
    { iPureIntro. apply (erasure_pc_tagged_no_id _ _ _ _ _ _ _ Her). }
    iFrame "HPC_s Hregs_s HMIE_s Hmtdc_s Hsched Hna Hclose".
    iApply (posture_res_gen_intro (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
              (CL := CL (UserThread t)) (CR := CR (UserThread t))
              (lword_of_word lpc.(lw)) (lword_of_word (WInt c)) MTVAL_NONE InterruptEnabled
              with "[Hcrit HU Hmepcc Hmcause Hmtval Hmpie_f] Hpart").
    rewrite /handover_at /volatile_csr_at. iFrame.
  Qed.

  (** * The yield and exit hand-ins *)

  (** The hand-in at a state where the user thread runs with interrupts
      disabled: its authorities to its slot, a copy of its registers to the
      context-switch thread. *)
  Lemma hand_in_disabled t σ :
    mie_st σ = InterruptDisabled →
    thread_si (UserThread t) σ -∗
    part_of (UserThread t) -∗
    idle_CtxSwitch
    ==∗
    ∃ (lpc : LWord) (lreg : LReg),
      "Hsi" ∷ thread_si CtxSwitch σ ∗
      "Hauths" ∷ auths_at t (ResumeVals lreg lpc InterruptDisabled) ∗
      "%Hdom" ∷ ⌜dom lreg = all_registers_s⌝ ∗
      "Hpart" ∷ part_of (UserThread t) ∗
      "HPC" ∷ PC ↦ₚ[CtxSwitch] lpc ∗
      "Hregs" ∷ regs[CtxSwitch] lreg ∗
      "HMIE" ∷ MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
      "Hmtdc" ∷ mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread t)) ∗
      "Hsched" ∷ scheduler_state ∗
      "Hna" ∷ na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) ∗
      "Hclose" ∷ close_Nact.
  Proof.
    iIntros (Hdis) "Hsi Hpart Hidle".
    iDestruct (thread_si_unfold with "Hsi") as "(HSI & %Hdom_σ & _ & _)".
    iDestruct "HSI" as (R C) "[Hsh Hth]". iNamed "Hth".
    iDestruct (csl_posture_part t with "Hpart") as "[Hsa Hlent_t]".
    iDestruct (mtdc_clause_lent with "Hlent Hlent_t") as %Hhome.
    iDestruct (csl_posture_part t with "[$Hsa $Hlent_t]") as "Hpart".
    assert (mie = InterruptDisabled) as ->.
    { rewrite -Hdis. symmetry. by eapply erasure_th_mie_st. }
    iMod (idle_load lpc lreg m with "Hidle")
      as "(Hauths_s & HPC_s & Hregs_s & Hmtdc_s & HMIE_s & Hlent_s & Hsched & Hna & Hclose)".
    { rewrite -Hdom_σ. symmetry. apply (et_regs _ _ _ _ _ _ _ Herth). }
    subst m.
    iModIntro. iExists lpc, lreg.
    iSplitL "Hsh Hauths_s Hlent_s".
    { iApply thread_si_unfold. iSplitL.
      - iExists R, C. iFrame "Hsh".
        iDestruct "Hauths_s" as "(HPCa_s & Hr_s & Hmtdc_a & HMIE_a)".
        iExists lpc, lreg, _, vm, InterruptDisabled.
        iFrame. iSplit; done.
      - iSplit; first done. iSplitR.
        + by iApply csl_link_disabled.
        + cbn [ctx_irq_si kind_of]. by iLeft. }
    iSplitL "HPCa Hr Hmtdc Hmie".
    { rewrite /auths_at /thread_auths. cbn [rv_pc rv_regs rv_mie]. iFrame. }
    iSplitR.
    { iPureIntro. rewrite -Hdom_σ. symmetry. apply (et_regs _ _ _ _ _ _ _ Herth). }
    iFrame.
  Qed.

  (** The yield hand-in: [yield_body]'s continuation is the yield's
      parking continuation, and the context-switch thread starts at the
      trap vector. *)
  Lemma yield_hand_in t σ :
    thread_si (UserThread t) σ -∗
    yield_body safe (UserThread t) -∗
    idle_CtxSwitch
    ==∗
    ∃ (b : InterruptStatus) (p : LWord) (lreg : LReg),
      "Hsi" ∷ thread_si CtxSwitch σ ∗
      "Hauths" ∷ auths_at t (ResumeVals lreg (lword_of_word mtcc_vec) InterruptDisabled) ∗
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
    iMod (hand_in_disabled t σ Hdis with "Hsi Hpart Hidle") as (lpc lreg) "H".
    iNamed "H".
    iDestruct "Hauths" as "(HPCa_t & Hr_t & Hmtdc_t & HMIE_a_t)".
    iDestruct (PC_agree with "HPCa_t HPC_t") as %Hpc.
    cbn in Hpc. subst lpc.
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := CL (UserThread t)) (CR := CR (UserThread t)) with "[$Hho $Hpart]")
      as "Hposture".
    iModIntro. iExists b, p, lreg.
    iFrame "Hsi HPC Hregs HMIE Hmtdc Hsched Hna Hclose HMIE_t HPC_t Hposture".
    iSplitL "HPCa_t Hr_t Hmtdc_t HMIE_a_t".
    { rewrite /auths_at /thread_auths. cbn [rv_pc rv_regs rv_mie]. iFrame. }
    iSplit; last done. rewrite /park_cont. iExact "Hcont".
  Qed.

  (** The exit hand-in: [exit_body]'s register map is the thread's. *)
  Lemma exit_hand_in t σ :
    thread_si (UserThread t) σ -∗
    exit_body (UserThread t) -∗
    idle_CtxSwitch
    ==∗
    ∃ (lpc : LWord) (lreg : LReg),
      "Hsi" ∷ thread_si CtxSwitch σ ∗
      "Hauths" ∷ auths_at t (ResumeVals lreg lpc InterruptDisabled) ∗
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
    iMod (hand_in_disabled t σ Hdis with "Hsi Hpart Hidle") as (lpc lreg) "H".
    iNamed "H".
    iDestruct "Hauths" as "(HPCa_t & Hr_t & Hmtdc_t & HMIE_a_t)".
    iDestruct (gen_heap_valid_inclSepM with "Hr_t Hregs_t") as %Hsub.
    cbn in Hsub. apply regs_total_eq in Hsub as ->; last done.
    iDestruct (posture_res_gen_unfold (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
                 (CL := CL (UserThread t)) (CR := CR (UserThread t)) with "[$Hho $Hpart]")
      as "Hposture".
    iModIntro. iExists lpc, lreg.
    iFrame "Hsi HPC Hregs HMIE Hmtdc Hsched Hna Hclose HMIE_t Hposture Hregs_t Hexit".
    iSplitL; last done.
    rewrite /auths_at /thread_auths. cbn [rv_pc rv_regs rv_mie]. iFrame.
  Qed.

  (** * The hand-back at [ResumedV] *)

  (** From the context-switch thread's state interpretation and
      [resumed_body]'s pieces, the resumed thread [B]'s state
      interpretation at the same state, with its authorities, and the
      context-switch thread's resources while [B] runs. B's home is not the
      context-switch thread's, so the latter's mtdc token leaves its
      clause. *)
  Lemma resumed_hand_back B (v : resume_vals) σ :
    mtdc_home_at (th := UserThread B) ≠ mtdc_home_at (th := CtxSwitch) →
    thread_si CtxSwitch σ -∗
    ⌜dom v.(rv_regs) = all_registers_s⌝ -∗
    regs[CtxSwitch] v.(rv_regs) -∗
    @PC_fragq Σ (@cerise_pcG Σ (ceriseG_of CtxSwitch)) (pc_dq v.(rv_mie)) v.(rv_pc) -∗
    MIE ↦ₜ[CtxSwitch] v.(rv_mie) -∗
    mtdc ↦ₜ[CtxSwitch] (mtdc_home_at (th := UserThread B)) -∗
    (if v.(rv_mie) is InterruptEnabled then part_of (UserThread B) else True) -∗
    scheduler_state -∗
    na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) -∗
    close_Nact -∗
    auths_at B v
    ==∗
    thread_si (UserThread B) σ ∗
    idle_CtxSwitch.
  Proof.
    destruct v as [lreg_r lpc_r b]. cbn [rv_regs rv_pc rv_mie].
    iIntros (Hne) "Hsi %Hdom Hregs HPC HMIE Hmtdc_f Hpart Hsched Hna Hclose Hauths".
    iDestruct (thread_si_unfold with "Hsi") as "(HSI & %Hdom_σ & Hlink & Hirq)".
    iDestruct "HSI" as (R C) "[Hsh Hth]". iNamed "Hth".
    pose proof (erasure_th_mie_st _ _ _ _ _ _ _ Herth) as Hmie_st.
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
    iModIntro. iSplitL "Hsh Hauths Hlink_B".
    { iApply thread_si_unfold.
      iDestruct "Hauths" as "(HPCa_B & Hr_B & Hmtdc_B & HMIE_B)".
      iSplitL "Hsh HPCa_B Hr_B Hmtdc_B HMIE_B".
      - iExists R, C. iFrame "Hsh". iExists lpc, lreg, _, vm, mie. iFrame.
        iSplit; [done | ]. iSplit; [by iLeft | done].
      - iSplit; first done. iFrame "Hlink_B". }
    rewrite /idle_CtxSwitch /thread_auths. iExists lpc, lreg, _, mie. iFrame. done.
  Qed.

  (** * The tick *)

  Lemma thread_si_tick th σ : thread_si th σ ⊢ thread_si th (tick σ).
  Proof.
    rewrite !thread_si_unfold. iIntros "(HSI & %Hdom & Hlink & Hirq)".
    iDestruct "HSI" as (R C) "[Hsh Hth]". iNamed "Hsh". iNamed "Hth".
    assert (mie_st (tick σ) = mie_st σ) as Htk by rewrite /mie_st tick_sreg //.
    iSplitL "Hsr Hmtcc Hm Hst HR HC Hmpie HPCa Hr Hmtdc Hlent Hmie".
    { iExists R, C. iSplitL "Hsr Hmtcc Hm Hst HR HC Hmpie".
      - iExists lsh, lmem, mpie. rewrite tick_shadowtbl. iFrame.
        iPureIntro. by apply erasure_sh_tick.
      - iExists lpc, lreg, m, vm, mie. iFrame.
        iPureIntro. split; [done | by apply erasure_th_tick]. }
    iSplit; first by rewrite tick_reg.
    iSplitL "Hlink".
    { iApply (crit_link_stable with "Hlink"); [done | by rewrite tick_sreg]. }
    rewrite /ctx_irq_si Htk. destruct (kind_of th); iExact "Hirq".
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
