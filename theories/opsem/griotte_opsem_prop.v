From stdpp Require Import gmap fin_maps list.
From griotte Require Export griotte_opsem.

Section opsem_prop.
  Context `{MachineParameters}.
(*--- z_of_argument ---*)

Lemma z_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (z:Z) :
  z_of_argument regs arg = Some z →
  (arg = inl z ∨ ∃ r w, arg = inr r ∧ regs !!ᵣ r = Some w ∧ get_a w = z).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto 10.
Qed.

Lemma z_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (z:Z) :
  z_of_argument regs arg = Some z →
  regs ⊆ regs' →
  (arg = inl z ∨ ∃ r w, arg = inr r ∧ regs !!ᵣ r = Some w ∧ regs' !!ᵣ r = Some w ∧
                        get_a w = z).
Proof.
  unfold z_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_reg_weaken _ _ _ _ _ HH); eauto 10.
Qed.

Lemma z_of_arg_mono (regs r: Reg) arg argz:
regs ⊆ r
-> z_of_argument regs arg = Some argz
-> z_of_argument r arg = Some argz.
Proof.
  intros.
  unfold z_of_argument in *.
  destruct arg; auto. destruct (lookup_reg _ _)  eqn:Heq; [| congruence].
  eapply lookup_reg_weaken in Heq as ->; auto.
Qed.

(*--- word_of_argument ---*)
Lemma word_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (w:Word) :
  word_of_argument regs arg = Some w →
  ((∃ z, arg = inl z ∧ w = WInt z) ∨
   (∃ r, arg = inr r ∧ regs !!ᵣ r = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma word_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (w:Word) :
  word_of_argument regs arg = Some w →
  regs ⊆ regs' →
  ((∃ z, arg = inl z ∧ w = WInt z) ∨
   (∃ r, arg = inr r ∧ regs !!ᵣ r = Some w ∧ regs' !!ᵣ r = Some w)).
Proof.
  unfold word_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
  intros HH. unshelve epose proof (lookup_reg_weaken _ _ _ _ _ HH); eauto.
Qed.

Lemma word_of_argument_inr (regs: Reg) (arg: Z + RegName) (t : bool) p g b e a:
  word_of_argument regs arg = Some (WCap t p g b e a) →
  (∃ r : RegName, arg = inr r ∧ regs !!ᵣ r = Some (WCap t p g b e a)).
Proof.
  intros HStoreV.
  unfold word_of_argument in HStoreV.
  destruct arg.
      - by inversion HStoreV.
      - exists r. destruct (regs !!ᵣ r) eqn:Hvr0; last by inversion HStoreV.
        split; auto.
Qed.

Lemma word_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> word_of_argument regs arg = Some w
-> word_of_argument r arg = Some w.
Proof.
  intros.
  unfold word_of_argument in *.
  destruct arg; auto. destruct (_ !!ᵣ _)  eqn:Heq; [| congruence].
  eapply lookup_reg_weaken in Heq as ->; auto.
Qed.

(*--- addr_of_argument ---*)

Lemma addr_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs arg = Some a →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r w, arg = inr r ∧ regs !!ᵣ r = Some w ∧ get_a w = z).
Proof.
  unfold addr_of_argument.
  destruct (z_of_argument regs arg) eqn:Hz; last done.
  intros. eexists. split; eauto. by apply z_of_argument_Some_inv.
Qed.

Lemma addr_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (a:Addr) :
  addr_of_argument regs arg = Some a →
  regs ⊆ regs' →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r w, arg = inr r ∧ regs !!ᵣ r = Some w ∧ regs' !!ᵣ r = Some w ∧
                             get_a w = z).
Proof.
  unfold addr_of_argument.
  destruct (z_of_argument regs arg) eqn:Hz; last done.
  intros ? HH. eexists. split; eauto. by eapply z_of_argument_Some_inv'.
Qed.

Lemma addr_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> addr_of_argument regs arg = Some w
-> addr_of_argument r arg = Some w.
Proof.
  intros.
  unfold addr_of_argument, z_of_argument in *.
  destruct arg; auto. destruct (_ !!ᵣ _)  eqn:Heq; [| congruence].
  eapply lookup_reg_weaken in Heq as ->; auto.
Qed.

(*--- otype_of_argument ---*)

Lemma otype_of_argument_Some_inv (regs: Reg) (arg: Z + RegName) (o:OType) :
  otype_of_argument regs arg = Some o →
  ∃ z, z_to_otype z = Some o ∧
       (arg = inl z ∨ ∃ r w, arg = inr r ∧ regs !!ᵣ r = Some w ∧ get_a w = z).
Proof.
  unfold otype_of_argument.
  destruct (z_of_argument regs arg) eqn:Hz; last done.
  intros. eexists. split; eauto. by apply z_of_argument_Some_inv.
Qed.

Lemma otype_of_argument_Some_inv' (regs regs': Reg) (arg: Z + RegName) (o:OType) :
  otype_of_argument regs arg = Some o →
  regs ⊆ regs' →
  ∃ z, z_to_otype z = Some o ∧
       (arg = inl z ∨ ∃ r w, arg = inr r ∧ regs !!ᵣ r = Some w ∧ regs' !!ᵣ r = Some w ∧
                             get_a w = z).
Proof.
  unfold otype_of_argument.
  destruct (z_of_argument regs arg) eqn:Hz; last done.
  intros ? HH. eexists. split; eauto. by eapply z_of_argument_Some_inv'.
Qed.

Lemma otype_of_arg_mono (regs r: Reg) arg w:
regs ⊆ r
-> otype_of_argument regs arg = Some w
-> otype_of_argument r arg = Some w.
Proof.
  intros.
  unfold otype_of_argument, z_of_argument in *.
  destruct arg; auto. destruct (_ !!ᵣ _)  eqn:Heq; [| congruence].
  eapply lookup_reg_weaken in Heq as ->; auto.
Qed.


  Lemma normal_always_step:
    forall φ, exists cf φ', step (Executable, φ) (cf, φ').
  Proof.
    intros. destruct (isCorrectPC_dec (pcc φ)) as [Hcorr | ]
    ; last (eexists _,_; by econstructor).
    inversion Hcorr as [?????? Hre].
    destruct (mem φ !! a) as [wa | ] eqn:Hmem.
    all: eexists _,_; by econstructor.
  Qed.

  Lemma step_deterministic:
    forall c1 c2 c2' σ1 σ2 σ2',
      step (c1, σ1) (c2, σ2) →
      step (c1, σ1) (c2', σ2') →
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; inv H1; inv H2; auto; try congruence.
  Qed.

  Lemma step_exec_inv
    (regs: Reg) (sregs : SReg) (mem : Mem) (shadow : ShadowTbl)
    (t : bool) (p : Perm) (g : Locality) (b e a : Addr) (w : Word)
    (instr : instr) (c: ConfFlag) (σ: ExecConf) :
    isCorrectPC (WCap t p g b e a) →
    mem !! a = Some w →
    decodeInstrW w = instr →
    step (Executable, (WCap t p g b e a, regs, sregs, mem, shadow)) (c, σ) →
    exec instr p (WCap t p g b e a, regs, sregs, mem, shadow) = (c, σ).
  Proof.
    intros Hpc Hm Hinstr. inversion 1; cbn in *.
    1,2: congruence.
    simplify_eq. by destruct (exec _ _).
  Qed.

  Lemma step_fail_inv (c : ConfFlag) (σ σ': ExecConf) :
    ¬ isCorrectPC (pcc σ) →
    step (Executable, σ) (c, σ') →
    c = Faulted ∧ σ' = σ.
  Proof.
    intros HPC Hs. inversion Hs; subst; auto.
    congruence.
  Qed.

  Lemma advancePC_some φ imm c:
    advancePC φ imm = Some c → ∃ φ', c = (NextI, φ').
  Proof.
    rewrite /advancePC; repeat case_match; try congruence. inversion 1. eauto.
  Qed.

  Lemma nextPC_some φ c:
    nextPC φ = Some c → ∃ φ', c = (NextI, φ').
  Proof.
    rewrite /nextPC; apply advancePC_some.
  Qed.

  Lemma instr_atomic i p φ :
    ∃ φ', (exec i p φ = (Faulted, φ') ) ∨ (exec i p φ = (NextI, φ')) ∨
          (exec i p φ = (Halted, φ')).
  Proof.
    unfold exec, exec_opt, exec_jcond.
    repeat case_match; simplify_eq; eauto;rename H0 into Heqo.
    (* Create more goals through *_of_argument, now that some have been pruned *)
    all: repeat destruct (addr_of_argument (reg φ) _)
    ; repeat destruct (otype_of_argument (reg φ) _)
    ; repeat destruct (word_of_argument (reg φ) _)
    ; repeat destruct (z_of_argument (reg φ) _)
    ; cbn in *; try by exfalso.
    all: repeat destruct (reg _ !!ᵣ _); cbn in *; repeat case_match.
    all: repeat destruct (pcc _); cbn in *; repeat case_match.
    all: repeat destruct (sreg _ !! _); cbn in *; repeat case_match.
    all: repeat destruct (finz.incr _ _); cbn in *; repeat case_match.
    all: repeat destruct (mem _ !! _); cbn in *; repeat case_match.
    all: repeat destruct (shadow_to_heap _); cbn in *; repeat case_match.
    all: repeat destruct (shadowtbl _ !! _); cbn in *; repeat case_match.
    all: simplify_eq; try by exfalso.
    all: try apply nextPC_some in Heqo as [φ' Heqo]; eauto.
    all: try apply advancePC_some in Heqo as [φ' Heqo]; eauto.
  Qed.

  (*--- The revoker's sweep ---*)

  (* The sweep untags a word iff the CLoad filter strips it. *)
  Lemma sweep_word_quarantined shadow w base :
    heap_cap_base w = Some base →
    shadow !! base = Some ShadowQuarantined →
    sweep_word shadow w = clear_tag w.
  Proof. rewrite /sweep_word. by intros -> ->. Qed.

  Lemma sweep_word_unchanged shadow w :
    (∀ base, heap_cap_base w = Some base → shadow !! base ≠ Some ShadowQuarantined) →
    sweep_word shadow w = w.
  Proof.
    rewrite /sweep_word. intros Hnq.
    destruct (heap_cap_base w) as [base|] eqn:Hbase; last done.
    specialize (Hnq base eq_refl).
    destruct (shadow !! base) as [[]|]; done.
  Qed.

  Lemma sweep_word_nonheap shadow w :
    heap_cap_base w = None → sweep_word shadow w = w.
  Proof. rewrite /sweep_word. by intros ->. Qed.

  Lemma sweep_word_cases shadow w :
    sweep_word shadow w = w ∨ sweep_word shadow w = clear_tag w.
  Proof.
    rewrite /sweep_word.
    destruct (heap_cap_base w); last by left.
    destruct (shadow !! _) as [[]|]; auto.
  Qed.

  Lemma lookup_sweep_mem shadow m a :
    sweep_mem shadow m !! a = sweep_word shadow <$> (m !! a).
  Proof. by rewrite /sweep_mem lookup_fmap. Qed.

  Lemma dom_sweep_mem shadow m :
    dom (sweep_mem shadow m) = dom m.
  Proof. by rewrite /sweep_mem dom_fmap_L. Qed.

  Lemma revoker_sweep_pcc φ : pcc (revoker_sweep φ) = pcc φ.
  Proof. done. Qed.

  Lemma revoker_sweep_reg φ : reg (revoker_sweep φ) = reg φ.
  Proof. done. Qed.

  Lemma revoker_sweep_sreg φ : sreg (revoker_sweep φ) = sreg φ.
  Proof. done. Qed.

  Lemma revoker_sweep_mem φ : mem (revoker_sweep φ) = sweep_mem (shadowtbl φ) (mem φ).
  Proof. done. Qed.

  Lemma revoker_sweep_shadowtbl φ : shadowtbl (revoker_sweep φ) = shadowtbl φ.
  Proof. done. Qed.

  Lemma dom_revoker_sweep_mem φ : dom (mem (revoker_sweep φ)) = dom (mem φ).
  Proof. apply dom_sweep_mem. Qed.

  (*--- The stack high-water mark ---*)

  Lemma lookup_hwm_update_ne (ea : Addr) (sr : SReg) x :
    x ≠ mshwm → hwm_update ea sr !! x = sr !! x.
  Proof.
    intros Hx. rewrite /hwm_update. repeat case_match; try done.
    by rewrite lookup_insert_ne.
  Qed.

  (** The update writes MSHWM only, an integer at [ea], when [ea] is in
      [[MSHWMB, MSHWM)]. *)
  Lemma hwm_update_cases (ea : Addr) (sr : SReg) :
    (hwm_update ea sr = sr ∧
       ∀ wb wh, sr !! mshwmb = Some wb → sr !! mshwm = Some wh →
         ¬ (get_a wb ≤ ea < get_a wh)%Z) ∨
    (∃ wb wh, sr !! mshwmb = Some wb ∧ sr !! mshwm = Some wh ∧
       (get_a wb ≤ ea < get_a wh)%Z ∧ hwm_update ea sr = <[mshwm := WInt ea]> sr).
  Proof.
    rewrite /hwm_update.
    destruct (sr !! mshwmb) as [wb|] eqn:Hb; destruct (sr !! mshwm) as [wh|] eqn:Hh.
    - case_decide as Hin.
      + right. by eexists _, _.
      + left. split; first done. intros wb' wh' Hb' Hh'. by simplify_eq.
    - left. split; first done. intros wb' wh' Hb' Hh'. by simplify_eq.
    - left. split; first done. intros wb' wh' Hb' Hh'. by simplify_eq.
    - left. split; first done. intros wb' wh' Hb' Hh'. by simplify_eq.
  Qed.

  Lemma hwm_update_id (ea : Addr) (sr : SReg) :
    (∀ wb wh, sr !! mshwmb = Some wb → sr !! mshwm = Some wh →
       ¬ (get_a wb ≤ ea < get_a wh)%Z) →
    hwm_update ea sr = sr.
  Proof.
    intros Hout. destruct (hwm_update_cases ea sr) as [[? _] | (wb & wh & Hb & Hh & Hin & _)];
      first done.
    by destruct (Hout _ _ Hb Hh).
  Qed.

  (*--- The tagged-PC invariant ---*)

  (** A tagged PC, MTCC or MEPCC is an unsealed executable capability. *)
  Definition sys_pc_ok (φ : ExecConf) : Prop :=
    pc_ok (pcc φ) ∧
    ∀ sr w, is_pc_sreg sr = true → sreg φ !! sr = Some w → pc_ok w.

  Lemma sys_pc_ok_ext φ φ' :
    pcc φ' = pcc φ → sreg φ' = sreg φ → sys_pc_ok φ → sys_pc_ok φ'.
  Proof. rewrite /sys_pc_ok. by intros -> ->. Qed.

  Lemma sys_pc_ok_update_sreg φ sr w :
    sys_pc_ok φ → sys_pc_ok (update_sreg φ sr (legalise sr w)).
  Proof.
    intros [Hpc Hsr]. split; first done.
    intros sr' w' Hsr'. cbn. destruct (decide (sr = sr')) as [<-|Hne].
    - rewrite lookup_insert_eq. intros [= <-]. by apply legalise_pc_sreg_pc_ok.
    - rewrite lookup_insert_ne //. by apply Hsr.
  Qed.

  Lemma sys_pc_ok_hwm_store (ea : Addr) φ : sys_pc_ok φ → sys_pc_ok (hwm_store ea φ).
  Proof.
    intros [Hpc Hsr]. split; first done.
    intros sr' w' Hsr'. cbn. rewrite lookup_hwm_update_ne; first by apply Hsr.
    by intros ->.
  Qed.

  Lemma sys_pc_ok_update_sreg_not_pc φ sr w :
    is_pc_sreg sr = false → sys_pc_ok φ → sys_pc_ok (update_sreg φ sr w).
  Proof.
    intros Hsr_not_pc [Hpc Hsr]. split; first done.
    intros sr' w' Hsr'. cbn. destruct (decide (sr = sr')) as [<-|Hne].
    - by rewrite Hsr_not_pc in Hsr'.
    - rewrite lookup_insert_ne //. by apply Hsr.
  Qed.

  (** A jump to the value of MTCC or MEPCC, as [mret] does. *)
  Lemma sys_pc_ok_update_pcc_sreg φ sr w :
    is_pc_sreg sr = true → sreg φ !! sr = Some w →
    sys_pc_ok φ → sys_pc_ok (update_pcc φ w).
  Proof. intros Hsr Hw [Hpc Hsregs]. split; [by eapply Hsregs | done]. Qed.

  Lemma advancePC_sys_pc_ok φ imm c :
    sys_pc_ok φ → advancePC φ imm = Some c → sys_pc_ok c.2.
  Proof.
    intros [Hpc Hsr]. rewrite /advancePC.
    destruct (pcc φ) as [| [] | | ] eqn:Hφ; try done.
    destruct (_ + _)%a; intros; simplify_eq. split; last done.
    cbn. by eapply pc_ok_cap_addr.
  Qed.

  Lemma nextPC_sys_pc_ok φ c :
    sys_pc_ok φ → nextPC φ = Some c → sys_pc_ok c.2.
  Proof. apply advancePC_sys_pc_ok. Qed.

  Lemma exec_opt_sys_pc_ok i p φ c :
    sys_pc_ok φ → exec_opt i p φ = Some c → sys_pc_ok c.2.
  Proof.
    intros Hinv Hexec.
    rewrite /exec_opt /exec_jcond in Hexec.
    destruct i; cbn in Hexec.
    all: repeat (case_match || simplify_option_eq); simplify_eq/=; try done.
    (* Every instruction but Jalr and Mret writes the PC through [advancePC]. *)
    all: try match goal with
      | Hup : advancePC ?φ' _ = Some _ |- _ => eapply (advancePC_sys_pc_ok φ'); [|exact Hup]
      | Hup : nextPC ?φ' = Some _ |- _ => eapply (nextPC_sys_pc_ok φ'); [|exact Hup]
      end.
    (* MTCC and MEPCC change only by a legalised write. *)
    all: try (eapply sys_pc_ok_ext; [| |exact Hinv]; done).
    all: try (eapply sys_pc_ok_ext; [| |apply sys_pc_ok_update_sreg, Hinv]; done).
    (* A store to memory updates MSHWM. *)
    all: try (eapply sys_pc_ok_ext; [| |apply sys_pc_ok_hwm_store, Hinv]; done).
    (* SetMIE and Mret write mstatus; Mret jumps to MEPCC. *)
    all: try (apply sys_pc_ok_update_sreg_not_pc; [done|]).
    all: try exact Hinv.
    all: try (eapply (sys_pc_ok_update_pcc_sreg _ mepcc); [done|eassumption|exact Hinv]).
    (* Jalr checks its target. *)
    all: match goal with
      | Ht : get_tag ?w = true, Hs : jalr_sealing_ok ?rd ?rs ?w = true,
        Hx : executable_word ?w = true |- _ =>
          split; [apply (jalr_target_ok_pc_ok rd rs) | apply (proj2 Hinv)];
          by rewrite /jalr_target_ok Ht Hs Hx
      end.
  Qed.

  Lemma exec_sys_pc_ok i p φ :
    sys_pc_ok φ → sys_pc_ok (exec i p φ).2.
  Proof.
    intros Hinv. rewrite /exec.
    destruct (exec_opt i p φ) eqn:Hexec; last done.
    by eapply exec_opt_sys_pc_ok.
  Qed.

  (** The machine preserves the tagged-PC invariant. *)
  Lemma step_sys_pc_ok σ σ' :
    sys_pc_ok σ.2 → step σ σ' → sys_pc_ok σ'.2.
  Proof.
    intros Hinv Hstep.
    destruct Hstep as [| |φ p g b e a i c wa _ _ _ _ <-]; try done.
    by apply exec_sys_pc_ok.
  Qed.

  Lemma rtc_step_sys_pc_ok σ σ' :
    sys_pc_ok σ.2 → rtc step σ σ' → sys_pc_ok σ'.2.
  Proof.
    intros Hinv Hsteps. induction Hsteps; eauto using step_sys_pc_ok.
  Qed.

  (** Trap entry preserves the tagged-PC invariant: the PC receives MTCC and
      MEPCC receives the PC, untagged on a fetch fault. *)
  Lemma enter_exc_sys_pc_ok cv φ :
    sys_pc_ok φ → sys_pc_ok (enter_exc cv φ).
  Proof.
    intros [Hpc Hsr]. rewrite /enter_exc /sreg_word. split.
    - cbn. destruct (sreg φ !! mtcc) as [w|] eqn:Hmtcc; cbn; last done.
      by apply (Hsr mtcc).
    - intros sr w Hsr_pc. cbn. destruct sr; try done.
      + rewrite !lookup_insert_ne //. by apply Hsr.
      + rewrite (lookup_insert_ne _ mtval) // (lookup_insert_ne _ mcause) //
          (lookup_insert_ne _ mstatus) // lookup_insert_eq.
        intros [= <-]. rewrite /mepcc_of_pc.
        case_match; last done.
        apply pc_ok_untagged, get_tag_clear_tag.
  Qed.

  (*--- Trap causes ---*)

  (** Every trap cause is one of the named causes, all below 8 but the CHERI
      cause, so the switcher's exception path hands it to the compartment's
      error handler. *)
  Lemma trap_cause_range φ :
    trap_cause φ ∈ [MCAUSE_INST_ACCESS_FAULT; MCAUSE_ILLEGAL_INSTRUCTION;
                    MCAUSE_LOAD_ACCESS_FAULT; MCAUSE_STORE_ACCESS_FAULT;
                    MCAUSE_CHERI].
  Proof. rewrite /trap_cause. destruct (trap_fault φ); set_solver. Qed.

  (** A bounds violation on a data access implies that the earlier checks
      passed: the capability is tagged, unsealed, with the permission. *)
  Lemma data_cap_check_bounds perm_ok perm_code r w imm :
    perm_code ≠ BoundsViolation →
    data_cap_check perm_ok perm_code r w imm = inl (FaultCheri BoundsViolation (CheriGPR r)) →
    ∃ p g b e a, w = Cap p g b e a ∧ perm_ok p = true.
  Proof.
    intros Hcode. rewrite /data_cap_check.
    destruct w as [| [[] p g b e a | [] ] | k [] | ? [ [] | [] ] ]; try (intros [=]; fail);
      try (intros [= ?]; congruence).
    destruct (perm_ok p) eqn:Hp; last (intros [= ?]; congruence).
    intros _. by exists p, g, b, e, a.
  Qed.

End opsem_prop.
