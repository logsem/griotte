From iris.proofmode Require Import proofmode environments spec_patterns.
From iris.base_logic Require Export invariants na_invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap.
From griotte Require Export iris_extra stdpp_extra.
From griotte Require Export machine_base state_interp posture handoff register_file machine_instructions.
From griotte Require Export resource_maps instr_operands.
From griotte Require Export named_props_extra.
Import core_link.

(** * The step of an instruction

    Shape layer, generic over the step function of the instruction: the
    thread values of a step, the lifting of a step to a WP, the lemmas that
    close the state interpretation after a step, the outcome of a step in
    closed form ([faulted_outcome], [step_outcome]), the fault rules
    ([wp_fault_step], [wp_instr_faulted_0] to [wp_instr_faulted_3]), and
    the rules of Halt and Fail ([wp_halt], [wp_fail]). Every other rules
    file builds on it. *)

(* ------------------------- the thread languages ------------------------------ *)

(** The value of a configuration flag, if it is one. *)
Definition flag_val {k} (c : ConfFlag) : option (tval k) :=
  match c with
  | Executable => None
  | Halted => Some HaltedV
  | Faulted => Some FaultedV
  | NextI => Some NextIV
  end.

(** The value of a step of instruction [i] at kind [k]: [NextIV] is the
    switch value when [i] is a switch instruction of [k]. *)
Definition tval_sw (k : kind) (i : instr) (v : tval k) : tval k :=
  match v with
  | NextIV => if sw_of k i is Some s then TSwV s else NextIV
  | _ => v
  end.

Lemma tval_sw_none k i v : sw_of k i = None → tval_sw k i v = v.
Proof. intros Hsw. rewrite /tval_sw Hsw. by destruct v. Qed.

(** Only the exit marker, [Ecall] and [Mret] are switch instructions. *)
Lemma sw_of_none k i : i ≠ exit_marker → i ≠ Ecall → i ≠ Mret → sw_of k i = None.
Proof. intros H1 H2 H3. destruct k; cbn; by repeat case_decide. Qed.

Lemma tres_from_option `{MachineParameters} {PROP : bi} k σ (c : ConfFlag) i
    (Φ : tval k → PROP) :
  decoded_instr σ = Some i →
  from_option Φ False%I (to_val (Instr (tres k σ c) : expr k)) =
  from_option (λ v, Φ (tval_sw k i v)) False%I (flag_val c).
Proof.
  rewrite /tres. intros ->. cbn. rewrite /tval_sw.
  destruct c; cbn; [done..|]. by destruct (sw_of k i).
Qed.

(** * The context-switch thread's interrupt clause: what it gives *)

Section ctx_irq.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ}.

  Definition ctx_irq_off (k : kind) (σ : ExecConf) : Prop := k = CtxK → mie_st σ = InterruptDisabled.

  (** With the whole PC fragment in hand, the clause is its left
      disjunct. *)
  Lemma ctx_irq_si_held k σ lpc : ctx_irq_si k σ -∗ PC ↦ₚ lpc -∗ ⌜ctx_irq_off k σ⌝ ∗ PC ↦ₚ lpc.
  Proof.
    destruct k; iIntros "Hd HPC".
    { iFrame "HPC". iPureIntro. intros Hk. discriminate. }
    iDestruct "Hd" as "[%Hd|[%lpc' HPC'] ]".
    { iFrame "HPC". iPureIntro. by intros _. }
    iDestruct (PC_frag_excl_q with "HPC HPC'") as %[].
  Qed.

  Lemma ctx_irq_si_kept k σ σ' : ctx_irq_off k σ → sys_kept σ σ' → ⊢ ctx_irq_si k σ'.
  Proof. destruct k; intros Hd [Hk _]; [done|]. iLeft. iPureIntro. rewrite Hk. by apply Hd. Qed.

  Lemma blocked_kept k σ σ' : ctx_irq_off k σ → blocked k σ σ' → sys_kept σ σ' → False.
  Proof.
    destruct k; [by intros ? []|]. intros Hd [_ Hen%irq_enabled_mie_st] [Hk _].
    rewrite Hk Hd // in Hen.
  Qed.

  (** What a step that may change MIE gives back at [CtxK]: the clause
      after the resuming [mret], MIE disabled otherwise. *)
  Definition ctx_irq_post (k : kind) (i : instr) (σ' : ExecConf) : iProp Σ :=
    match k with
    | UserK => True
    | CtxK => if decide (i = Mret) then ctx_irq_si CtxK σ' else ⌜mie_st σ' = InterruptDisabled⌝
    end%I.

  Lemma ctx_irq_post_si k i σ' : ctx_irq_post k i σ' -∗ ctx_irq_si k σ'.
  Proof.
    destruct k; rewrite /ctx_irq_post; [by iIntros|]. case_decide; [by iIntros|].
    iIntros "%". by iLeft.
  Qed.

  Lemma ctx_irq_post_blocked k i σ σ' :
    decoded_instr σ = Some i → blocked k σ σ' → ctx_irq_post k i σ' -∗ False.
  Proof.
    destruct k; [by intros ? []|]. intros Hdec [Hne Hen%irq_enabled_mie_st].
    rewrite /ctx_irq_post decide_False; last (intros ->; congruence).
    iIntros "%H". rewrite H in Hen. done.
  Qed.

  (** A step that keeps MIE gives [ctx_irq_post] from the clause before it. *)
  Lemma ctx_irq_post_kept k i σ σ' : ctx_irq_off k σ → sys_kept σ σ' → ⊢ ctx_irq_post k i σ'.
  Proof.
    destruct k; intros Hd [Hk _]; rewrite /ctx_irq_post; [done|].
    case_decide; [iLeft|]; iPureIntro; rewrite Hk; by apply Hd.
  Qed.

  (** The pure part of the clause gives the routing law's precondition. *)
  Lemma ctx_irq_off_route th σ : ctx_irq_off (kind_of th) σ → route_pre th (mie_st σ).
  Proof. destruct th; intros Hoff Hth; [discriminate|]. by apply Hoff. Qed.

  (** A post-state that meets the routing law's precondition gives
      [ctx_irq_post]. *)
  Lemma ctx_irq_post_route th i σ' : route_pre th (mie_st σ') → ⊢ ctx_irq_post (kind_of th) i σ'.
  Proof.
    destruct th; intros Hpre; rewrite /ctx_irq_post /=; [done|].
    case_decide; [iLeft|]; iPureIntro; by apply Hpre.
  Qed.
End ctx_irq.

Section exc_entry.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ}.

  (** Exception entry on the ghost state, as [enter_exc_update], when mtcc
      holds the word [wv]: the PC receives [wv], and the volatile registers
      are given back at their new values. *)
  Lemma enter_exc_update_wedged σ (cv : Z * Z) lpc lreg lsreg lmem R C (p c : LWord) (v : Z)
      (mpie b : InterruptStatus) (wv : LWord) :
    erasure R C σ lpc lreg (ls_join lsreg) lmem →
    ls_join lsreg !! mtcc = Some wv →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗
    sys_interp lsreg -∗
    gen_heap_interp lmem -∗
    gen_heap_interp (shadowtbl σ) -∗
    reg_auth R -∗
    addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    MIE ↦ₜ b -∗
    volatile_csr_at p c v mpie
    ==∗
    ⌜mie_st σ = b⌝ ∗
    ⌜mie_st (enter_exc cv σ) = InterruptDisabled⌝ ∗
    cerise_state_interp (enter_exc cv σ) ∗
    PC ↦ₚ wv ∗
    MIE ↦ₜ InterruptDisabled ∗
    volatile_csr_at (lmepcc_of_pc lpc) (lword_of_word (WInt cv.1)) cv.2 b.
  Proof.
    iIntros (Her Htcc) "HPCa Hr Hsr Hm Hst HR HC HPC Hmie_f (Hmepcc & Hmcause & Hmtval & Hmpie_f)".
    iDestruct (sys_interp_mie_agree with "Hsr Hmie_f") as %<-.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    pose proof (erasure_enter_exc _ _ _ _ _ _ _ cv _ Her Htcc) as Her'.
    (* mstatus: MIE is disabled and MPIE receives MIE. *)
    set (mie_old := mie_of (get_a (sreg_word σ mstatus))).
    assert (mie_old = ls_mie lsreg) as Hmie_old.
    { rewrite -Hmie_st /mie_old /mie_st /sreg_word.
      destruct (sreg σ !! mstatus); done. }
    iMod (sys_interp_set_mstatus _ _ _ InterruptDisabled mie_old with "Hsr Hmie_f Hmpie_f")
      as "(Hsr & Hmie_f & Hmpie_f)".
    (* MEPCC, mcause, mtval and the PC. *)
    iNamed "Hsr". destruct Hlsh as [Hn1 Hn2]. destruct Hlsh_hwm as [Hn3 Hn4].
    iMod (gen_heap_update _ _ _ (lmepcc_of_pc lpc) with "Hsr Hmepcc") as "[Hsr Hmepcc]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt cv.1)) with "Hsr Hmcause")
      as "[Hsr Hmcause]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt cv.2)) with "Hsr Hmtval")
      as "[Hsr Hmtval]".
    iMod (PC_update _ _ wv with "HPCa HPC") as "[HPCa HPC]".
    pose (ls' := MkLSys
      (<[mtval := lword_of_word (WInt cv.2)]>
        (<[mcause := lword_of_word (WInt cv.1)]>
          (<[mepcc := lmepcc_of_pc lpc]> (ls_sh lsreg))))
      (ls_mtdc lsreg) (ls_vmtdc lsreg) InterruptDisabled mie_old
      (ls_hwmb lsreg) (ls_hwm lsreg) (ls_pend lsreg) (ls_lent lsreg)).
    assert (lsregs_enter_exc cv σ lpc (ls_join lsreg) = ls_join ls') as Hjoin.
    { apply map_eq. intros i.
      rewrite /lsregs_enter_exc /ls' /ls_join /lsregs_join /mie_old /=.
      destruct i; by simplify_map_eq. }
    rewrite Hjoin in Her'.
    iAssert (sys_interp ls')
      with "[Hsr Hmtcc Hmpie Hmtdc Hlent Hmie Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone]"
      as "Hsys".
    { rewrite /sys_interp /ls'.
      cbn [ls_sh ls_mtdc ls_vmtdc ls_mie ls_mpie ls_hwmb ls_hwm ls_pend ls_lent
           ls_set_mstatus] in *.
      iFrame "Hsr Hmtcc Hmpie Hmtdc Hlent Hmie Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone".
      iSplit; first done.
      iPureIntro. split_and!; by simplify_map_eq. }
    iPoseProof (SI_close (enter_exc cv σ) wv lreg ls' lmem R C Her'
                  with "HPCa Hr Hsys Hm Hst HR HC") as "HSI".
    iModIntro. iSplit; first done. iSplit.
    { by destruct (erasure_mie_st _ _ _ _ _ _ _ Her') as [-> _]. }
    rewrite Hmie_old. iFrame.
  Qed.

  (** Exception entry on the ghost state, from the opened state
      interpretation at [σ], the PC [lpc], MIE [b], the unwedged token and
      the volatile registers: MEPCC receives [lmepcc_of_pc lpc], mcause and
      mtval the cause [cv], MPIE receives [b], MIE is disabled, and the PC
      receives the trap vector. *)
  Lemma enter_exc_update σ cv lpc lreg lsreg lmem R C p c v mpie b :
    erasure R C σ lpc lreg (ls_join lsreg) lmem →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗
    sys_interp lsreg -∗
    gen_heap_interp lmem -∗
    gen_heap_interp (shadowtbl σ) -∗
    reg_auth R -∗
    addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    MIE ↦ₜ b -∗
    unwedged -∗
    volatile_csr_at p c v mpie
    ==∗
    ⌜mie_st σ = b⌝ ∗
    ⌜mie_st (enter_exc cv σ) = InterruptDisabled⌝ ∗
    cerise_state_interp (enter_exc cv σ) ∗
    PC ↦ₚ lword_of_word mtcc_vec ∗
    MIE ↦ₜ InterruptDisabled ∗
    vol_lent (lmepcc_of_pc lpc) (lword_of_word (WInt cv.1)) cv.2 b.
  Proof.
    iIntros (Her) "HPCa Hr Hsr Hm Hst HR HC HPC Hmie_f HU Hvcsr".
    iDestruct (sys_interp_mtcc with "Hsr HU") as %Htcc.
    iMod (enter_exc_update_wedged with "HPCa Hr Hsr Hm Hst HR HC HPC Hmie_f Hvcsr")
      as "($ & $ & $ & $ & $ & Hvcsr)"; [exact Her | exact Htcc |].
    by iFrame.
  Qed.
End exc_entry.

(** The premise of [wp_instr_step] on a decoded instruction that does not
    write MSHWMB: rewrite the decoding hypothesis, then compute, decide the
    register comparisons, or split the disjunction of a family of
    instructions. *)
Ltac solve_writes_mshwmb :=
  repeat match goal with |- _ → _ => intros _ end;
  try match goal with
      | H : decodeInstrW ?x = _ |- writes_mshwmb (decodeInstrW ?x) = false => rewrite H
      end;
  first
    [ reflexivity
    | solve [rewrite /writes_mshwmb; repeat case_bool_decide; first [done | congruence] ]
    | match goal with
      | |- writes_mshwmb ?i = false =>
          is_var i;
          match goal with
          | H : _ |- _ =>
              let Hi := fresh "Hi" in
              pose proof H as Hi; destruct_or! Hi; rewrite Hi; reflexivity
          end
      end ].

#[export] Hint Extern 5 (writes_mshwmb _ = false) => solve_writes_mshwmb : core.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* ------------------------- the state interpretation --------------------------- *)

  (** The window clause across a step that does not write MSHWMB with the
      system-register permission: the step keeps it, and while the window
      is open the instruction is one of the window's. At [UserK], the step
      keeps the physical MSHWMB. At [CtxK], the window's load moves the PC
      to the closing write and keeps the window's facts; the closing write
      itself writes MSHWMB. *)
  #[local] Lemma hwm_win_si_step k pc_p pc_g pc_b pc_e pc_a σ w lmem lsreg c σ' :
    pcc σ = Cap pc_p pc_g pc_b pc_e pc_a →
    (has_sreg_access pc_p = true → writes_mshwmb (decodeInstrW w.(lw)) = false) →
    lmem !! pc_a = Some w →
    exec (decodeInstrW w.(lw)) pc_p σ = (c, σ') →
    gen_heap_interp lmem -∗
    sys_interp lsreg -∗
    hwm_win_si k σ -∗
    ⌜ls_pend lsreg = None ∨ hwm_window_instr (decodeInstrW w.(lw))⌝ ∗
    gen_heap_interp lmem ∗
    sys_interp lsreg ∗
    hwm_win_si k σ'.
  Proof.
    iIntros (Hpc Hw Hpc_a Hstep) "Hm Hsr Hwin".
    destruct k; cbn.
    - iDestruct "Hwin" as "(Hhalf & Hlent & Hbase)".
      iDestruct (sys_interp_pend_half_agree with "Hsr Hhalf") as %Hnone.
      pose proof (exec_phys_mshwmb _ _ σ Hw) as Hph. rewrite Hstep /= in Hph.
      rewrite Hph. iFrame. by iLeft.
    - iDestruct "Hwin" as (o) "[Hcl Hwin]".
      iDestruct (sys_interp_pend_cl_agree with "Hsr Hcl") as %Ho.
      destruct o as [hbT|]; last first.
      { iFrame. by iLeft. }
      iNamed "Hwin". destruct Hdec_w as [Hdec2 Hdec3].
      iDestruct (gen_heap_valid with "Hm Ha2") as %Hm2.
      iDestruct (gen_heap_valid with "Hm Ha3") as %Hm3.
      pose proof Hpc_win as (p' & g' & b' & e' & a & a4 & Hpc' & Ha23 & Ha34 & Ha & _ & _ & Hx).
      rewrite Hpc in Hpc'. simplify_eq.
      destruct Ha as [-> | ->].
      + (* The window's load. *)
        rewrite Hm2 in Hpc_a. simplify_eq. rewrite Hdec2 in Hstep.
        destruct (window_load_step _ _ _ _ _ _ _ _ _ _ Hpc Hpc_win Hcsp_ok Hstep)
          as (_ & Hpc_win' & Hcsp_ok' & _).
        iFrame "Hm Hsr". iSplit.
        { iPureIntro. right. left. rewrite Hdec2. by eexists _, _, _. }
        iExists (Some hbT). iFrame "Hcl". iExists a2, a3, off, w, w3. iFrame "#".
        iPureIntro. split_and!; done.
      + (* The closing write writes MSHWMB with the permission. *)
        rewrite Hm3 in Hpc_a. simplify_eq.
        specialize (Hw Hx). rewrite Hdec3 in Hw. discriminate.
  Qed.

  (** The common start of every instruction rule, in its most general form:
      the logical PC and the instruction word give the physical ones, and
      the instruction is decoded from the physical copy. The continuation
      receives the link, the pure part of the context-switch thread's
      interrupt clause and the window clause, and gives back the link and
      the window clause of the new state and [ctx_irq_post]. A step that
      [blocked] forbids is excluded: [ctx_irq_post] contradicts it. *)
  #[local] Lemma wp_instr_step_gen E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (td : TimeDevs) (lreg : LReg)
         (lsreg : LSys) (lmem : LMem) (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag)
         (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "Hlink" ∷ crit_link (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) ∗
        "%Hoff" ∷ ⌜ctx_irq_off (kind_of th) (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)⌝ ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        "Hwin_si" ∷ hwm_win_si (kind_of th) (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))
       ==∗
       (cerise_state_interp σ' ∗ crit_link σ') ∗
       ctx_irq_post (kind_of th) (decodeInstrW w.(lw)) σ' ∗
       hwm_win_si (kind_of th) σ' ∗
       from_option (λ v, Φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v)) False (flag_val c))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "(Hσ & %Hrdom & Hlink & Hirq & Hwin_si) /=".
    destruct σ1 as [pc r sr m st td]; cbn.
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iMod "HPC". iMod "Hpc_a". iMod "Hmap".
    iDestruct (ctx_irq_si_held with "Hirq HPC") as "[%Hoff HPC]".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid with "Hm Hpc_a") as %Hpc_a.
    pose proof (erasure_regs_incl _ _ _ _ _ _ _ _ Her Hregs) as Hregs'.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hpc_a) as (pw & Hpw & Hok).
    pose proof (erasure_pc_exact _ _ _ _ _ _ _ Her) as HPCr. cbn in HPCr. subst pc.
    assert (decoded_instr (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) =
              Some (decodeInstrW w.(lw))) as Hdec.
    { rewrite /decoded_instr /= Hpw /=. by rewrite (mem_word_ok_decode _ _ _ _ Hok). }
    destruct (normal_always_step (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))
      as (c0 & σ0 & Hs0).
    destruct (decide (blocked (kind_of th)
                (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) σ0)) as [Hb|Hnb].
    { (* A blocked step: the continuation gives [ctx_irq_post], a contradiction. *)
      eapply step_exec_inv in Hs0; eauto; cbn in Hs0.
      rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hs0.
      iAssert (▷ False)%I with "[-]" as ">[]". iNext.
      iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $Hlink $HPC $Hpc_a $Hmap $Hwin_si]")
        as "(_ & Hpost & _)"; first by iFrame "%".
      iApply (ctx_irq_post_blocked with "Hpost"); done. }
    iModIntro. iSplitR.
    { iPureIntro. eexists [], _, σ0, []. by apply TS_instr. }
    iNext. iIntros (e2 σ2 efs Hpstep).
    inversion Hpstep as [σx c σ' Hstep Hnb'| | | | |]; subst.
    iIntros "_". iSplitR; first done.
    assert (dom (reg σ2) = all_registers_s) as Hrdom'.
    { exact (step_reg_dom (_, _) (_, _) Hrdom Hstep). }
    eapply step_exec_inv in Hstep; eauto; cbn in Hstep.
    rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hstep.
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $Hlink $HPC $Hpc_a $Hmap $Hwin_si]")
      as "([$ $] & Hpost & Hwin_si & HΦ)"; first by iFrame "%".
    iModIntro. iSplitL "Hpost Hwin_si".
    { iSplitR; first (iPureIntro; exact Hrdom'). iFrame "Hwin_si". by iApply ctx_irq_post_si. }
    by rewrite (tres_from_option _ _ _ _ _ Hdec).
  Qed.

  (** The common start of every instruction rule: the logical PC and the
      instruction word give the physical ones, and the instruction is decoded
      from the physical copy. The continuation closes the state
      interpretation after the physical step. The system registers are one
      argument [lsreg] and one hypothesis ["Hsr"]; the continuation shows
      that the step keeps MIE and mtdc ([sys_kept]), so that it keeps the
      link. The value is read through [tval_sw]: a switch instruction of
      the kind gives its switch value. A step that [blocked] forbids is
      excluded inside: it is at [CtxK], where the context-switch thread's
      interrupt clause and [PC ↦ₚ] give MIE disabled before the step, and the [sys_kept] that the continuation
      returns contradicts MIE enabled after it. The instruction does not
      write MSHWMB with the system-register permission, so that the step
      keeps the window clause; the continuation learns that the window is
      closed, or that the instruction is one of the window's
      ([hwm_window_instr]). *)
  Lemma wp_instr_step E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (has_sreg_access pc_p = true → writes_mshwmb (decodeInstrW w.(lw)) = false) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (td : TimeDevs) (lreg : LReg)
         (lsreg : LSys) (lmem : LMem) (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag)
         (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hwin" ∷ ⌜ls_pend lsreg = None ∨ hwm_window_instr (decodeInstrW w.(lw))⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       ⌜sys_kept (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) σ'⌝ ∗
       cerise_state_interp σ' ∗
       from_option (λ v, Φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v)) False (flag_val c))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc Hw) "HPC Hpc_a Hmap Hcont".
    iApply (wp_instr_step_gen with "HPC Hpc_a Hmap"); first done.
    iNext. iIntros (r sr m st td lreg lsreg lmem R C c σ') "Hpre". iNamed "Hpre".
    iDestruct (hwm_win_si_step with "Hm Hsr Hwin_si") as "(%Hwin & Hm & Hsr & Hwin_si)";
      [done | exact Hw | exact Hpc_a | exact Hstep |].
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $HPC $Hpc_a $Hmap]")
      as "(%Hk & $ & HΦ)"; first by iFrame "%".
    iModIntro. iFrame "HΦ Hwin_si". iSplitL "Hlink".
    - iApply (crit_link_stable with "Hlink"); by destruct Hk.
    - by iApply ctx_irq_post_kept.
  Qed.

  (** [wp_instr_step] for an instruction that is not a switch instruction
      of the kind: the value is the flag's ([flag_val]). *)
  Lemma wp_instr_step_nosw E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    sw_of (kind_of th) (decodeInstrW w.(lw)) = None →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (has_sreg_access pc_p = true → writes_mshwmb (decodeInstrW w.(lw)) = false) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (td : TimeDevs) (lreg : LReg)
         (lsreg : LSys) (lmem : LMem) (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag)
         (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hwin" ∷ ⌜ls_pend lsreg = None ∨ hwm_window_instr (decodeInstrW w.(lw))⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       ⌜sys_kept (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) σ'⌝ ∗
       cerise_state_interp σ' ∗
       from_option Φ False (flag_val c))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hsw Hvpc Hw) "HPC Hpc_a Hmap Hcont".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); [done | done |].
    iNext. iIntros (r sr m st td lreg lsreg lmem R C c σ') "Hpre".
    iMod ("Hcont" $! r sr m st td lreg lsreg lmem R C c σ' with "Hpre") as "($ & $ & HΦ)".
    iModIntro. destruct (flag_val c); cbn; [|done].
    by rewrite tval_sw_none.
  Qed.

  (** The same for a step that may change MIE or mtdc. The continuation
      receives the link and the pure part of the clause ([ctx_irq_off]), and
      gives back the link of the new state and [ctx_irq_post]: at [CtxK], the
      clause after a resuming [mret], MIE disabled after any other step
      ([ctx_irq_post_kept] for a step that keeps MIE). *)
  Lemma wp_instr_step_link E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (has_sreg_access pc_p = true → writes_mshwmb (decodeInstrW w.(lw)) = false) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (td : TimeDevs) (lreg : LReg)
         (lsreg : LSys) (lmem : LMem) (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag)
         (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hwin" ∷ ⌜ls_pend lsreg = None ∨ hwm_window_instr (decodeInstrW w.(lw))⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "Hlink" ∷ crit_link (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) ∗
        "%Hoff" ∷ ⌜ctx_irq_off (kind_of th) (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)⌝ ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       (cerise_state_interp σ' ∗ crit_link σ') ∗
       ctx_irq_post (kind_of th) (decodeInstrW w.(lw)) σ' ∗
       from_option (λ v, Φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v)) False (flag_val c))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc Hw) "HPC Hpc_a Hmap Hcont".
    iApply (wp_instr_step_gen with "HPC Hpc_a Hmap"); first done.
    iNext. iIntros (r sr m st td lreg lsreg lmem R C c σ') "Hpre". iNamed "Hpre".
    iDestruct (hwm_win_si_step with "Hm Hsr Hwin_si") as "(%Hwin & Hm & Hsr & Hwin_si)";
      [done | exact Hw | exact Hpc_a | exact Hstep |].
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $Hlink $HPC $Hpc_a $Hmap]")
      as "($ & $ & HΦ)"; first by iFrame "%".
    by iFrame.
  Qed.

  (** [wp_instr_step_link] for an instruction that is not a switch
      instruction of the kind. *)
  Lemma wp_instr_step_link_nosw E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    sw_of (kind_of th) (decodeInstrW w.(lw)) = None →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (has_sreg_access pc_p = true → writes_mshwmb (decodeInstrW w.(lw)) = false) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (td : TimeDevs) (lreg : LReg)
         (lsreg : LSys) (lmem : LMem) (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag)
         (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hwin" ∷ ⌜ls_pend lsreg = None ∨ hwm_window_instr (decodeInstrW w.(lw))⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "Hlink" ∷ crit_link (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) ∗
        "%Hoff" ∷ ⌜ctx_irq_off (kind_of th) (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)⌝ ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       (cerise_state_interp σ' ∗ crit_link σ') ∗
       ctx_irq_post (kind_of th) (decodeInstrW w.(lw)) σ' ∗
       from_option Φ False (flag_val c))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hsw Hvpc Hw) "HPC Hpc_a Hmap Hcont".
    iApply (wp_instr_step_link with "HPC Hpc_a Hmap"); [done | done |].
    iNext. iIntros (r sr m st td lreg lsreg lmem R C c σ') "Hpre".
    iMod ("Hcont" $! r sr m st td lreg lsreg lmem R C c σ' with "Hpre") as "($ & $ & HΦ)".
    iModIntro. destruct (flag_val c); cbn; [|done].
    by rewrite tval_sw_none.
  Qed.

  (** A write to MSHWMB at a user thread: the continuation receives the
      window clause, which holds the thread's stack base, and gives back the
      clause of the new state. *)
  Lemma wp_instr_step_hwmb_user E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
    kind_of th = UserK →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (td : TimeDevs) (lreg : LReg)
         (lsreg : LSys) (lmem : LMem) (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag)
         (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hwin" ∷ ⌜ls_pend lsreg = None ∨ hwm_window_instr (decodeInstrW w.(lw))⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        "Hwin_si" ∷ hwm_win_si UserK (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))
       ==∗
       ⌜sys_kept (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) σ'⌝ ∗
       cerise_state_interp σ' ∗
       hwm_win_si UserK σ' ∗
       from_option (λ v, Φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v)) False (flag_val c))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hk Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply (wp_instr_step_gen with "HPC Hpc_a Hmap"); first done.
    iNext. iIntros (r sr m st td lreg lsreg lmem R C c σ') "Hpre". iNamed "Hpre".
    iAssert (hwm_win_si UserK (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))
      with "[Hwin_si]" as "Hwin_si"; first by rewrite Hk.
    iAssert (⌜ls_pend lsreg = None⌝)%I as %Hnone.
    { iDestruct "Hwin_si" as "(Hhalf & _)".
      iApply (sys_interp_pend_half_agree with "Hsr Hhalf"). }
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $HPC $Hpc_a $Hmap $Hwin_si]")
      as "(%Hkept & $ & Hwin_si & HΦ)"; first (iFrame "%"; iPureIntro; by left).
    iAssert (hwm_win_si (kind_of th) σ') with "[Hwin_si]" as "Hwin_si"; first by rewrite Hk.
    iModIntro. iFrame "HΦ Hwin_si". iSplitL "Hlink".
    - iApply (crit_link_stable with "Hlink"); by destruct Hkept.
    - by iApply ctx_irq_post_kept.
  Qed.

  (** A write of the HWM restore window at the context-switch thread: the
      continuation receives the window clause and the code's quarter of the
      window, and gives back the clause of the new state. *)
  Lemma wp_instr_step_win E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) o Φ :
    kind_of th = CtxK →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    ▷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    ▷ pend_frag o -∗
    ▷ (∀ (r : Reg) (sr : SReg) (m : Mem) (st : ShadowTbl) (td : TimeDevs) (lreg : LReg)
         (lsreg : LSys) (lmem : LMem) (R : RegState) (C : gmap Addr AddrClaim) (c : ConfFlag)
         (σ' : ExecConf),
       ("%Her" ∷ ⌜erasure R C (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)
                    (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lreg (ls_join lsreg) lmem⌝ ∗
        "%Hlregs" ∷ ⌜regs ⊆ lreg⌝ ∗
        "%Hregs" ∷ ⌜lregs_phys R regs r⌝ ∗
        "%Hpc_a" ∷ ⌜lmem !! pc_a = Some w⌝ ∗
        "%Hstep" ∷ ⌜exec (decodeInstrW w.(lw)) pc_p
                     (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) = (c, σ')⌝ ∗
        "HPCa" ∷ PC_auth (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hr" ∷ gen_heap_interp lreg ∗
        "Hsr" ∷ sys_interp lsreg ∗
        "Hm" ∷ gen_heap_interp lmem ∗
        "Hst" ∷ gen_heap_interp st ∗
        "HR" ∷ reg_auth R ∗
        "HC" ∷ addr_alloc_auth C ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        "Hpend" ∷ pend_frag o ∗
        "Hwin_si" ∷ hwm_win_si CtxK (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))
       ==∗
       ⌜sys_kept (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) σ'⌝ ∗
       cerise_state_interp σ' ∗
       hwm_win_si CtxK σ' ∗
       from_option (λ v, Φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v)) False (flag_val c))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hk Hvpc) "HPC Hpc_a Hmap Hpend Hcont".
    iApply (wp_instr_step_gen with "HPC Hpc_a Hmap"); first done.
    iNext. iIntros (r sr m st td lreg lsreg lmem R C c σ') "Hpre". iNamed "Hpre".
    iAssert (hwm_win_si CtxK (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))
      with "[Hwin_si]" as "Hwin_si"; first by rewrite Hk.
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $HPC $Hpc_a $Hmap $Hpend $Hwin_si]")
      as "(%Hkept & $ & Hwin_si & HΦ)"; first by iFrame "%".
    iAssert (hwm_win_si (kind_of th) σ') with "[Hwin_si]" as "Hwin_si"; first by rewrite Hk.
    iModIntro. iFrame "HΦ Hwin_si". iSplitL "Hlink".
    - iApply (crit_link_stable with "Hlink"); by destruct Hkept.
    - by iApply ctx_irq_post_kept.
  Qed.

  (** Closes a step that keeps MIE and mtdc, under [wp_instr_step_link]. *)
  Lemma instr_close_link_kept σ σ' (X : iProp Σ) :
    crit_link σ -∗
    (|==> ⌜sys_kept σ σ'⌝ ∗ cerise_state_interp σ' ∗ X) -∗
    |==> (cerise_state_interp σ' ∗ crit_link σ') ∗ X.
  Proof.
    iIntros "Hlink >([%Hk1 %Hk2] & $ & $)". iModIntro.
    iApply (crit_link_stable with "Hlink"); done.
  Qed.

  (** The same, with the [ctx_irq_post] that [wp_instr_step_link] asks
      for. *)
  Lemma instr_close_link_kept_irq σ σ' i (X : iProp Σ) :
    ctx_irq_off (kind_of th) σ →
    crit_link σ -∗
    (|==> ⌜sys_kept σ σ'⌝ ∗ cerise_state_interp σ' ∗ X) -∗
    |==> (cerise_state_interp σ' ∗ crit_link σ') ∗ ctx_irq_post (kind_of th) i σ' ∗ X.
  Proof.
    iIntros (Hoff) "Hlink >(%Hk & $ & $)". iModIntro. iSplitL "Hlink".
    - iApply (crit_link_stable with "Hlink"); by destruct Hk.
    - by iApply ctx_irq_post_kept.
  Qed.

  (** Closes a step that may change MIE or mtdc from [σ0], through a
      closing from [σ1] (the state after the write): the link is
      transferred with [T1] for [T2], with the state interpretation of the
      new state in hand, and the postcondition receives [T2]; the
      [ctx_irq_post] that [wp_instr_step_link] asks for comes from the
      routing law's precondition after the step. *)
  Lemma instr_close_link_transfer_irq (P : ExecConf → ExecConf → Prop) (T1 T2 : iProp Σ)
      σ0 σ1 σ' i (Ψ : tval (kind_of th) → iProp Σ) (c : ConfFlag) :
    link_transfer_si P T1 T2 →
    (sys_kept σ1 σ' → P σ0 σ') →
    (sys_kept σ1 σ' → route_pre th (mie_st σ')) →
    crit_link σ0 -∗ T1 -∗
    (|==> ⌜sys_kept σ1 σ'⌝ ∗ cerise_state_interp σ' ∗
          from_option (λ v, T2 -∗ Ψ v) False (flag_val c)) -∗
    |==> (cerise_state_interp σ' ∗ crit_link σ') ∗
         ctx_irq_post (kind_of th) i σ' ∗
         from_option Ψ False (flag_val c).
  Proof.
    iIntros (Htr HP Hroute) "Hlink HT >(%Hk & HSI & HΨ)".
    iMod (Htr _ σ' (HP Hk) with "[$HSI $Hlink $HT]") as "($ & $ & HT)". iModIntro.
    iSplitR; first (iApply ctx_irq_post_route; by apply Hroute).
    destruct (flag_val c); cbn; [by iApply "HΨ" | done].
  Qed.

  (** A closing that keeps MIE and mtdc from a state that keeps them. *)
  Lemma instr_close_kept_trans σ0 σ1 σ' (X : iProp Σ) :
    sys_kept σ0 σ1 →
    (|==> ⌜sys_kept σ1 σ'⌝ ∗ X) -∗
    |==> ⌜sys_kept σ0 σ'⌝ ∗ X.
  Proof.
    iIntros (Hk) ">[%Hk' $]". iPureIntro. by eapply sys_kept_trans.
  Qed.

  (* ----------------------------------- FAIL RULES ---------------------------------- *)

  Lemma wp_notCorrectPC:
    forall E (w : LWord),
      ~ isCorrectPC w.(lw) ->
      {{{ PC ↦ₚ w }}}
         Instr Executable @ E
        {{{ RET FaultedV; PC ↦ₚ w }}}.
  Proof.
    intros *. intros Hnpc.
    iIntros (ϕ) "HPC Hϕ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 nt l1 l2 ns) "(Hσ1 & %Hrdom & Hlink & Hirq & Hwin) /=";
      destruct σ1 as [pc r sr m st td]; simpl.
    iDestruct (SI_open with "Hσ1") as "Hσ1". iNamed "Hσ1".
    iDestruct (ctx_irq_si_held with "Hirq HPC") as "[%Hoff HPC]".
    iDestruct (PC_agree with "HPCa HPC") as %->.
    pose proof (erasure_pc_not_correct _ _ _ _ _ _ _ Her Hnpc) as Hnpc'. cbn in Hnpc'.
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro. eexists [], _, _, []. apply TS_instr; first by apply step_exec_corrfail.
      intros Hb. exact (blocked_kept _ _ _ Hoff Hb (sys_kept_refl _)). }
    iModIntro. iIntros (e1 σ2 efs Hstep).
    inversion Hstep as [σx c σ' Hs _| | | | |]; subst.
    eapply step_fail_inv in Hs as [-> ->]; eauto.
    rewrite tres_not_next //.
    iNext. iIntros "_".
    iModIntro. iSplitR; auto. iSplitR "Hϕ HPC"; last by iApply "Hϕ".
    iFrame "Hlink Hwin". iSplitL "HPCa Hr Hsr Hm Hst HR HC".
    - iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
    - iSplitR; first (iPureIntro; done).
      iApply (ctx_irq_si_kept _ _ _ Hoff). apply sys_kept_refl.
  Qed.

  Lemma wp_notCorrectPC_tag E (w : LWord) :
    get_tag w.(lw) = false →
    {{{ PC ↦ₚ w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ w }}}.
  Proof.
    iIntros (Htag φ) "HPC Hφ".
    iApply (wp_notCorrectPC with "HPC").
    { by apply not_isCorrectPC_untagged. }
    iNext. iIntros "HPC". by iApply "Hφ".
  Qed.

  (* ----------------------------------- ATOMIC RULES -------------------------------- *)

  Lemma wp_halt E pc_p pc_g pc_b pc_e pc_a pc_π w dq :
    decodeInstrW w.(lw) = Halt →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET HaltedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply (wp_instr_step E pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "Hpc Hpca [] "); eauto.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec /= in Hstep. simplify_eq.
    iModIntro. iSplit; first (iPureIntro; apply sys_kept_refl).
    iSplitR "Hφ HPC Hpc_a"; last (cbn; iApply "Hφ"; iFrame).
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  Lemma wp_fail E pc_p pc_g pc_b pc_e pc_a pc_π w dq :
    decodeInstrW w.(lw) = Fail →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →

    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros Hinstr Hvpc.
    iIntros (φ) "[Hpc Hpca] Hφ".
    iApply (wp_instr_step E pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "Hpc Hpca [] "); eauto.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec /= in Hstep. simplify_eq.
    iModIntro. iSplit; first (iPureIntro; apply sys_kept_refl).
    iSplitR "Hφ HPC Hpc_a"; last (cbn; iApply "Hφ"; iFrame).
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** The register [cnull] holds the null word: read from the state
      interpretation, in front of any expression that is not a value. *)
  Lemma wp_reg_cnull_lnull E e Φ r w :
    to_val e = None →
    r ↦ᵣ w -∗
    (⌜r = cnull → w = lnull⌝ -∗ r ↦ᵣ w -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (He) "Hr' HΦ".
    rewrite wp_unfold /wp_pre /= He.
    iIntros (σ1 ns κ κs nt) "(Hσ & %Hrdom & Hlink & Hirq & Hwin) /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (gen_heap_valid with "Hr Hr'") as %Hlookup.
    iSpecialize ("HΦ" with "[%] Hr'").
    { intros ->. by eapply er_cnull. }
    iApply ("HΦ" $! σ1 ns κ κs nt). iFrame "Hlink Hirq Hwin %".
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

End griotte_lang_rules.

(** What a register step does to the rest of the machine: nothing. This
    is the place where such an effect (for example on a counter of the
    system registers) enters; a model with one changes this definition
    and the closers and tactics that unfold it ([regs_case] and
    [solve_regs_member] in [ftlr_shapes.v], [wp_regs_step] in
    [shapes/regs.v], the register steps in closed form of [regs_next_ok_db]). *)
Definition regs_effect (φ : ExecConf) : ExecConf := φ.

(** A write to [cnull] is no write. *)
Lemma update_reg_cnull φ w : φ .[cnull :=ᵣ w] = φ.
Proof. destruct φ. by rewrite /update_reg /= insert_reg_cnull. Qed.

(** A faulted step: the PC and the owned part [s] of the state unchanged.
    A model whose fault writes trap state changes this definition. *)
Definition faulted_outcome {k : kind} {A} (lpc : LWord) (s : A) (lpc' : LWord) (s' : A)
    (retv : tval k) : Prop :=
  retv = FaultedV ∧ lpc' = lpc ∧ s' = s.

Lemma faulted_outcome_refl {k : kind} {A} lpc (s : A) :
  faulted_outcome (k := k) lpc s lpc s FaultedV.
Proof. done. Qed.

(** The closed-form outcome of a step whose result [mv] (the new PC and
    owned part [s] of the state) is computed by a pure function, or a
    fault. *)
Definition step_outcome {k : kind} {A} (mv : option (LWord * A)) (lpc : LWord) (s : A)
    (lpc' : LWord) (s' : A) (retv : tval k) : Prop :=
  match mv with
  | Some (l, s1) => retv = NextIV ∧ lpc' = l ∧ s' = s1
  | None => faulted_outcome lpc s lpc' s' retv
  end.

Lemma step_outcome_next {k : kind} {A} mv lpc (s : A) lpc' (s' : A) :
  mv = Some (lpc', s') → step_outcome (k := k) mv lpc s lpc' s' NextIV.
Proof. by intros ->. Qed.

Lemma step_outcome_fault {k : kind} {A} mv lpc (s : A) :
  mv = None → step_outcome (k := k) mv lpc s lpc s FaultedV.
Proof. intros ->. apply faulted_outcome_refl. Qed.

Lemma step_outcome_cases {k : kind} {A} mv lpc (s : A) lpc' (s' : A) (retv : tval k) :
  step_outcome mv lpc s lpc' s' retv →
  (mv = Some (lpc', s') ∧ retv = NextIV) ∨
  (mv = None ∧ faulted_outcome lpc s lpc' s' retv).
Proof.
  destruct mv as [ [l s1] | ]; intros Hout.
  - destruct Hout as (-> & -> & ->). by left.
  - right. split; [done | exact Hout].
Qed.

(** A fault: on every physical copy of the owned registers (each exact or
    stripped) whose PC is the logical one, the step does not happen. *)
Definition regs_fault (step : instr → Perm → ExecConf → option Conf)
    (i : instr) (p : Perm) (lpc : LWord) (regs : LReg) : Prop :=
  ∀ φ, pcc φ = lpc.(lw) →
    (∀ r v, regs !! r = Some v → ∃ s, reg φ !!ᵣ r = Some (and_tag s v.(lw))) →
    step i p φ = None.

Section instruction_closing.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {k : kind}.

  (** The closing lemmas below conclude that the step keeps MIE and mtdc
      ([sys_kept]): they do not change the system registers. *)

  (** Closes a failed instruction: the state is unchanged. *)
  Lemma instr_close_fail pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) (Φ : tval k → iProp Σ) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ FaultedV) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) (MkExecConf pc r sr m st td)⌝ ∗
    cerise_state_interp (MkExecConf pc r sr m st td) ∗
    from_option Φ False (flag_val Faulted).
  Proof.
    iIntros (Her) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ". iModIntro.
    iSplit; first (iPureIntro; apply sys_kept_refl).
    iSplitR "Hφ HPC Hmap"; last by iApply ("Hφ" with "HPC").
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** Closes an instruction that only moves the PC by [n], as the physical
      [advancePC φ n]. The spec [P] holds of the new PC on success, and of
      the old one on failure. *)
  Lemma instr_close_pc_update pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) n c σ' (Φ : tval k → iProp Σ)
      (P : LWord → tval k → Prop) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    (match advancePC (MkExecConf pc r sr m st td) n with
     | Some conf => conf | None => (Faulted, (MkExecConf pc r sr m st td)) end) = (c, σ') →
    (∀ lpc', incrementPC_gen lpc n = Some lpc' → P lpc' NextIV) →
    (incrementPC_gen lpc n = None → P lpc FaultedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' retv, ⌜P lpc' retv⌝ -∗ PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ retv) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) σ'⌝ ∗
    cerise_state_interp σ' ∗ from_option Φ False (flag_val c).
  Proof.
    iIntros (Her Hstep HPs HPf) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    destruct (incrementPC_gen lpc n) as [lpc'|] eqn:Hi.
    - destruct (erasure_incrementPC_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) as (pc' & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
      iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
      iSplitR "Hφ HPC Hmap".
      + iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC").
      + iApply ("Hφ" with "[%] HPC Hmap"). by apply HPs.
    - rewrite (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) in Hstep.
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply ("Hφ" with "[%] HPC Hmap"). by apply HPf.
  Qed.

  (** Writes the logical register [dst], owned unless it is [cnull]. *)
  Lemma lreg_update (lreg regs : LReg) dst v :
    (dst = cnull ∨ dst ∈ dom regs) →
    gen_heap_interp lreg -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ==∗
    gen_heap_interp (<[dst := v]ₗ> lreg) ∗ [∗ map] k↦y ∈ <[dst := v]ₗ> regs, k ↦ᵣ y.
  Proof.
    iIntros (Hdst) "Hr Hmap".
    destruct (decide (dst = cnull)) as [->|Hne].
    { rewrite !linsert_reg_cnull. by iFrame. }
    destruct Hdst as [->|Hdst]; first done.
    rewrite !linsert_reg_not_cnull //.
    iApply (gen_heap_update_inSepM with "Hr Hmap"). by apply elem_of_dom.
  Qed.

  (** Closes an instruction that writes one register then moves the PC by
      [n], as the physical [advancePC (update_reg φ dst w) n]. The spec [P]
      holds of the new PC and owned registers on success, and of the old
      ones on failure. *)
  Lemma instr_close_reg_update_advancePC pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) n c σ' (Φ : tval k → iProp Σ)
      (P : LWord → LReg → tval k → Prop) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    dst = cnull ∨ dst ∈ dom regs →
    reg_word_ok R C v →
    (match advancePC (update_reg (MkExecConf pc r sr m st td) dst w) n with
     | Some conf => conf | None => (Faulted, (MkExecConf pc r sr m st td)) end) = (c, σ') →
    reg_phys R v w →
    (∀ lpc', incrementPC_gen lpc n = Some lpc' → P lpc' (<[dst := v]ₗ> regs) NextIV) →
    (incrementPC_gen lpc n = None → P lpc regs FaultedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗
    sys_interp lsreg -∗
    gen_heap_interp lmem -∗
    gen_heap_interp st -∗
    reg_auth R -∗
    addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' regs' retv,
       ⌜P lpc' regs' retv⌝ -∗
       PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗
       Φ retv)
    ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) σ'⌝ ∗
    cerise_state_interp σ' ∗
    from_option Φ False (flag_val c).
  Proof.
    iIntros (Her Hdst Hok Hstep Hw HPs HPf) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ _ dst v w Her Hok Hw) as Her1.
    rewrite /update_reg /= in Hstep.
    destruct (incrementPC_gen lpc n) as [lpc'|] eqn:Hi.
    - destruct (erasure_incrementPC_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      iMod (lreg_update _ _ dst v Hdst with "Hr Hmap") as "[Hr Hmap]".
      iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
      iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
      iSplitR "Hφ HPC Hmap".
      + iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC").
      + iApply ("Hφ" with "[%] HPC Hmap"). by apply HPs.
    - rewrite (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) in Hstep.
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply ("Hφ" with "[%] HPC Hmap"). by apply HPf.
  Qed.

  (** Closes an instruction that writes one register then increments the PC,
      as the physical [nextPC (update_reg φ dst v)]. The spec [P] holds of
      the new PC and owned registers on success, and of the old ones on
      failure. *)
  Lemma instr_close_reg_update pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) c σ' (Φ : tval k → iProp Σ)
      (P : LWord → LReg → tval k → Prop) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    regs ⊆ lreg →
    dst = cnull ∨ dst ∈ dom regs →
    reg_word_ok R C v →
    (match nextPC (update_reg (MkExecConf pc r sr m st td) dst w) with
     | Some conf => conf | None => (Faulted, (MkExecConf pc r sr m st td)) end) = (c, σ') →
    reg_phys R v w →
    (∀ lpc', incrementPC lpc = Some lpc' → P lpc' (<[dst := v]ₗ> regs) NextIV) →
    (incrementPC lpc = None → P lpc regs FaultedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' regs' retv, ⌜P lpc' regs' retv⌝ -∗ PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗ Φ retv) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) σ'⌝ ∗
    cerise_state_interp σ' ∗ from_option Φ False (flag_val c).
  Proof.
    intros Her _.
    exact (instr_close_reg_update_advancePC pc r sr m st td lpc lreg lsreg lmem R C regs dst v w 1 c σ'
             Φ P Her).
  Qed.

  (** Closes an instruction that sets the PC to [lpc'] and writes one
      register, as the physical [update_reg (update_pcc φ pc') dst w]. *)
  Lemma instr_close_reg_set_pc pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) (lpc' : LWord) (pc' : Word)
      (Φ : tval k → iProp Σ) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    dst = cnull ∨ dst ∈ dom regs →
    reg_word_ok R C v →
    reg_phys R v w →
    reg_word_ok R C lpc' →
    reg_phys R lpc' pc' →
    pc_ok lpc'.(lw) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc' -∗ ([∗ map] k↦y ∈ <[dst := v]ₗ> regs, k ↦ᵣ y) -∗ Φ NextIV) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) (update_reg (update_pcc (MkExecConf pc r sr m st td) pc') dst w)⌝ ∗
    cerise_state_interp (update_reg (update_pcc (MkExecConf pc r sr m st td) pc') dst w) ∗
    from_option Φ False (flag_val NextI).
  Proof.
    iIntros (Her Hdst Hok Hw Hokpc Hwpc Hpcok)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ _ dst v w Her Hok Hw) as Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ _ lpc' pc' Her1 Hokpc Hwpc Hpcok) as Her2.
    iMod (lreg_update _ _ dst v Hdst with "Hr Hmap") as "[Hr Hmap]".
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
    iSplitR "Hφ HPC Hmap".
    - iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC").
    - iApply ("Hφ" with "HPC Hmap").
  Qed.

  (** Closes a step that only sets the PC. *)
  Lemma instr_close_set_pc pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) (lpc' : LWord) (pc' : Word)
      (Φ : tval k → iProp Σ) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    reg_word_ok R C lpc' →
    reg_phys R lpc' pc' →
    pc_ok lpc'.(lw) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc' -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ NextIV) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) (update_pcc (MkExecConf pc r sr m st td) pc')⌝ ∗
    cerise_state_interp (update_pcc (MkExecConf pc r sr m st td) pc') ∗
    from_option Φ False (flag_val NextI).
  Proof.
    iIntros (Her Hokpc Hwpc Hpcok) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ _ lpc' pc' Her Hokpc Hwpc Hpcok) as Her'.
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
    iSplitR "Hφ HPC Hmap".
    - iApply (SI_close _ _ _ _ _ _ _ Her' with "HPCa Hr Hsr Hm Hst HR HC").
    - iApply ("Hφ" with "HPC Hmap").
  Qed.

End instruction_closing.

(** Closes the failing branch of a general rule with [instr_close_fail], then
    the rule's continuation ["Hφ"], and leaves the spec as a pure goal. A
    tactic rather than a lemma: it passes the state hypotheses that
    [wp_instr_step] (and the lifting of the Load and Store rules) introduce
    under fixed names. *)
Ltac instr_fail_close :=
  try iApply bupd_fupd;
  try (iApply (instr_close_link_kept_irq with "Hlink"); [done|]);
  try iApply (instr_close_link_kept with "Hlink");
  iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|];
  iIntros "HPC Hmap"; iApply "Hφ"; iFrame; iPureIntro.

(** The same, after substituting the faulted configuration given by
    [Hstep : (Faulted, φ) = (c, σ')]. *)
Ltac instr_fail Hstep :=
  first [injection Hstep as <- <- | simplify_eq]; instr_fail_close.

(** Pure side conditions of the map-form rules applied to
    register maps built by [map_of_regs_k]: a small closed set of goals
    (instruction decoding, register lookups and domains, the PC increment).
    A tactic because the goals vary with the instruction class. *)
Ltac solve_next_side :=
  first [ done
        | by apply incrementPC_add
        | by rewrite /regs_of /operands_of /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver+
        | by simplify_map_eq
        | by apply llookup_reg_cnull
        | by rewrite /lz_of_argument /=; simplify_map_eq ].

Section instruction_outcomes.

  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (* A failed instruction rolls back every tentative write. The premise is
     about all physical register files that include the erased owned
     registers, so no absent register or memory address can be mistaken for
     evidence of runtime failure. *)
  #[local] Lemma wp_instr_faulted_map E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) i (regs : LReg) dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ R r sr m st td, lregs_phys R regs r → (∀ v, regs !! cnull = Some v → v = lnull) →
       exec i pc_p (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) =
         (Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step_gen with "HPC Hpc_a Hmap"); first done.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr (Hfailed R r sr m st td Hregs) in Hstep.
    2: { intros v0 Hv0. eapply er_cnull; [exact Her | by eapply lookup_weaken]. }
    simplify_eq.
    iModIntro. iFrame "Hlink Hwin_si".
    iSplitR "Hφ HPC Hpc_a Hmap"; last (iSplitR; [by iApply ctx_irq_post_kept | cbn; iApply "Hφ"; iFrame]).
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

  (** The generic fault rule: the step does not happen on any copy of the
      owned registers; all resources are returned unchanged. *)
  Lemma wp_fault_step E pc_p pc_g pc_b pc_e pc_a pc_π w dq i (regs : LReg) :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_fault exec_opt i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Hfault.
    apply (wp_instr_faulted_map _ _ _ _ _ _ _ _ i); [exact Hinstr | exact Hvpc |].
    intros R r sr m st td Hregs Hcnull. apply exec_opt_exec_none, Hfault; first done.
    intros x v Hx. destruct (decide (x = cnull)) as [-> | Hne].
    - rewrite (Hcnull v Hx) lookup_reg_cnull. by exists true.
    - rewrite lookup_reg_not_cnull //. by eapply lregs_phys_lookup.
  Qed.

  (* Failure with PC alone; all resources are returned unchanged. *)
  Lemma wp_instr_faulted_0 E pc_p pc_g pc_b pc_e pc_a pc_π w i dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st td,
       exec i pc_p (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) =
         (Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hmem) Hφ".
    iApply (wp_instr_faulted_map E pc_p pc_g pc_b pc_e pc_a pc_π w i ∅ with "[$HPC $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st td _ _. apply Hfailed.
    - by rewrite big_sepM_empty.
    - iNext. iIntros "(HPC & Hmem & _)".
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 1 explicit register; all resources are returned unchanged. *)
  Lemma wp_instr_faulted_1 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st td s1, r !! r1 = Some (and_tag s1 w1.(lw)) →
       exec i pc_p (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) =
         (Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ r1 ↦ᵣ w1 ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ r1 ↦ᵣ w1 ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (wp_instr_faulted_map E pc_p pc_g pc_b pc_e pc_a pc_π w i (<[r1 := w1]> ∅)
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st td Hincl _.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_1 with "Hmap") as "Hr1"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 2 explicit registers; all resources are returned unchanged. *)
  Lemma wp_instr_faulted_2 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 r2 w2 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st td s1 s2, r !! r1 = Some (and_tag s1 w1.(lw)) →
       r !! r2 = Some (and_tag s2 w2.(lw)) →
       exec i pc_p (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) =
         (Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ ▷ r1 ↦ᵣ w1 ∗ ▷ r2 ↦ᵣ w2 ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ r1 ↦ᵣ w1 ∗ r2 ↦ᵣ w2 ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hr2 & >Hmem) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (wp_instr_faulted_map E pc_p pc_g pc_b pc_e pc_a pc_π w i
      (<[r1 := w1]> (<[r2 := w2]> ∅))
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st td Hincl _.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r2 w2 Hincl) as [s2 Hl2]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_2 with "Hmap") as "(Hr1 & Hr2)"; eauto.
      iApply "Hφ". iFrame.
  Qed.

  (* Failure with PC and 3 explicit registers; all resources are returned unchanged. *)
  Lemma wp_instr_faulted_3 E pc_p pc_g pc_b pc_e pc_a pc_π w i r1 w1 r2 w2 r3 w3 dq :
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (∀ r sr m st td s1 s2 s3, r !! r1 = Some (and_tag s1 w1.(lw)) →
       r !! r2 = Some (and_tag s2 w2.(lw)) →
       r !! r3 = Some (and_tag s3 w3.(lw)) →
       exec i pc_p (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) =
         (Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td))) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          ▷ r1 ↦ᵣ w1 ∗
          ▷ r2 ↦ᵣ w2 ∗
          ▷ r3 ↦ᵣ w3 ∗
          ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET FaultedV; PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          r1 ↦ᵣ w1 ∗
          r2 ↦ᵣ w2 ∗
          r3 ↦ᵣ w3 ∗
          pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfailed φ) "(>HPC & >Hr1 & >Hr2 & >Hr3 & >Hmem) Hφ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (wp_instr_faulted_map E pc_p pc_g pc_b pc_e pc_a pc_π w i
      (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅)))
      with "[$HPC $Hmap $Hmem]").
    - exact Hinstr.
    - exact Hvpc.
    - intros R r sr m st td Hincl _.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r2 w2 Hincl) as [s2 Hl2]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r3 w3 Hincl) as [s3 Hl3]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_3 with "Hmap") as "(Hr1 & Hr2 & Hr3)"; eauto.
      iApply "Hφ". iFrame.
  Qed.
End instruction_outcomes.
