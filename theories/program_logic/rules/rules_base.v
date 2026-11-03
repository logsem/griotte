From iris.proofmode Require Import proofmode environments spec_patterns.
From iris.base_logic Require Export invariants na_invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.algebra Require Import frac auth gmap.
From griotte Require Export iris_extra stdpp_extra.
From griotte Require Export machine_base state_interp posture register_file machine_instructions.
From griotte Require Export resource_maps instr_operands.
From griotte Require Export named_props_extra.
Import core_link.

(* --------------------------- LTAC DEFINITIONS ----------------------------------- *)

Ltac inv_base_step :=
  repeat match goal with
         | _ => progress simplify_map_eq/= (* simplify memory stuff *)
         | H : griotte_lang.to_val _ = Some _ |- _ => apply griotte_lang.of_to_val in H
         | H : _ = griotte_lang.of_val ?v |- _ =>
           is_var v; destruct v; first[discriminate H|injection H as H]
         | H : griotte_lang.prim_step ?e _ _ _ _ _ |- _ =>
           try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
           (*    and can thus better be avoided. *)
           let φ := fresh "φ" in
           inversion H as [| φ]; subst φ; clear H
         end.

(* ------------------------- the thread languages ------------------------------ *)

(** The opsem reads an absent mstatus as 0, the program logic as
    interrupts disabled: the same. *)
Lemma irq_enabled_mie_st `{MachineParameters} σ :
  irq_enabled σ ↔ mie_st σ = InterruptEnabled.
Proof. rewrite /irq_enabled /mie_st /sreg_word. by destruct (sreg σ !! mstatus). Qed.

(** The embedding of [griotte_lang]'s values. *)
Definition tval_of_val {k} (v : griotte_lang.val) : tval k :=
  match v with
  | griotte_lang.HaltedV => HaltedV | griotte_lang.FaultedV => FaultedV
  | griotte_lang.NextIV => NextIV
  end.

(** The value of a step of instruction [i] at kind [k]: [NextIV] is the
    switch value when [i] is a switch instruction of [k]. *)
Definition tval_sw (k : kind) (i : instr) (v : griotte_lang.val) : tval k :=
  match v with
  | griotte_lang.NextIV => if sw_of k i is Some s then TSwV s else NextIV
  | _ => tval_of_val v
  end.

Lemma tval_sw_none k i v : sw_of k i = None → tval_sw k i v = tval_of_val v.
Proof. intros Hsw. rewrite /tval_sw Hsw. by destruct v. Qed.

(** Only the exit marker, [Ecall] and [Mret] are switch instructions. *)
Lemma sw_of_none k i : i ≠ exit_marker → i ≠ Ecall → i ≠ Mret → sw_of k i = None.
Proof. intros H1 H2 H3. destruct k; cbn; by repeat case_decide. Qed.

Lemma tres_from_option `{MachineParameters} {PROP : bi} k σ (c : ConfFlag) i
    (Φ : tval k → PROP) :
  decoded_instr σ = Some i →
  from_option Φ False%I (to_val (Instr (tres k σ c) : expr k)) =
  from_option (λ v, Φ (tval_sw k i v)) False%I (griotte_lang.to_val (griotte_lang.Instr c)).
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
End ctx_irq.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* ------------------------- the state interpretation --------------------------- *)

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
      returns contradicts MIE enabled after it. *)
  Lemma wp_instr_step E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
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
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       ⌜sys_kept (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) σ'⌝ ∗
       cerise_state_interp σ' ∗
       from_option (λ v, Φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v)) False
         (griotte_lang.to_val (griotte_lang.Instr c)))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "(Hσ & %Hrdom & Hlink & Hirq) /=". destruct σ1 as [pc r sr m st td]; cbn.
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
    { (* A blocked step: the continuation gives [sys_kept], a contradiction. *)
      eapply step_exec_inv in Hs0; eauto; cbn in Hs0.
      rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hs0.
      iAssert (▷ False)%I with "[-]" as ">[]". iNext.
      iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $HPC $Hpc_a $Hmap]")
        as "(%Hk & _)"; first by iFrame "%".
      by destruct (blocked_kept _ _ _ Hoff Hb Hk). }
    iModIntro. iSplitR.
    { iPureIntro. eexists [], _, σ0, []. by apply TS_instr. }
    iNext. iIntros (e2 σ2 efs Hpstep).
    inversion Hpstep as [σx c σ' Hstep Hnb'| | | | |]; subst.
    iIntros "_". iSplitR; first done.
    assert (dom (reg σ2) = all_registers_s) as Hrdom'.
    { exact (step_reg_dom (_, _) (_, _) Hrdom Hstep). }
    eapply step_exec_inv in Hstep; eauto; cbn in Hstep.
    rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hstep.
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $HPC $Hpc_a $Hmap]")
      as "(%Hk & $ & HΦ)"; first by iFrame "%".
    iModIntro. iSplitL "Hlink".
    - iSplitR; first (iPureIntro; exact Hrdom').
      iSplitL "Hlink"; first (iApply (crit_link_stable with "Hlink"); by destruct Hk).
      by iApply ctx_irq_si_kept.
    - by rewrite (tres_from_option _ _ _ _ _ Hdec).
  Qed.

  (** The same for a step that may change MIE or mtdc. The continuation
      receives the link and the pure part of the clause ([ctx_irq_off]), and
      gives back the link of the new state and [ctx_irq_post]: at [CtxK], the
      clause after a resuming [mret], MIE disabled after any other step
      ([ctx_irq_post_kept] for a step that keeps MIE). *)
  Lemma wp_instr_step_link E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
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
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       (cerise_state_interp σ' ∗ crit_link σ') ∗
       ctx_irq_post (kind_of th) (decodeInstrW w.(lw)) σ' ∗
       from_option (λ v, Φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v)) False
         (griotte_lang.to_val (griotte_lang.Instr c)))
    -∗ WP Instr Executable @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "(Hσ & %Hrdom & Hlink & Hirq) /=". destruct σ1 as [pc r sr m st td]; cbn.
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
      iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $Hlink $HPC $Hpc_a $Hmap]")
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
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $Hlink $HPC $Hpc_a $Hmap]")
      as "([$ $] & Hpost & HΦ)"; first by iFrame "%".
    iModIntro. iSplitL "Hpost".
    { iSplitR; first (iPureIntro; exact Hrdom'). by iApply ctx_irq_post_si. }
    by rewrite (tres_from_option _ _ _ _ _ Hdec).
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

  (** At the core link, any closing closes a step that may change MIE or
      mtdc. *)
  Lemma instr_close_core σ1 σ' (X : iProp Σ) :
    (|==> ⌜sys_kept σ1 σ'⌝ ∗ cerise_state_interp σ' ∗ X) -∗
    |==> (cerise_state_interp σ' ∗ @crit_link Σ _ link_core σ') ∗ X.
  Proof. iIntros ">(_ & $ & $)". done. Qed.

  (** Closes a step that may change MIE or mtdc from [σ0], through a
      closing from [σ1] (the state after the write): the link is
      transferred with [T1] for [T2], with the state interpretation of the
      new state in hand, and the postcondition receives [T2]. *)
  Lemma instr_close_link_transfer (P : ExecConf → ExecConf → Prop) (T1 T2 : iProp Σ)
      σ0 σ1 σ' (Ψ : griotte_lang.val → iProp Σ) (c : ConfFlag) :
    link_transfer_si P T1 T2 →
    (sys_kept σ1 σ' → P σ0 σ') →
    crit_link σ0 -∗ T1 -∗
    (|==> ⌜sys_kept σ1 σ'⌝ ∗ cerise_state_interp σ' ∗
          from_option (λ v, T2 -∗ Ψ v) False (griotte_lang.to_val (griotte_lang.Instr c))) -∗
    |==> (cerise_state_interp σ' ∗ crit_link σ') ∗
         from_option Ψ False (griotte_lang.to_val (griotte_lang.Instr c)).
  Proof.
    iIntros (Htr HP) "Hlink HT >(%Hk & HSI & HΨ)".
    iMod (Htr _ σ' (HP Hk) with "[$HSI $Hlink $HT]") as "($ & $ & HT)". iModIntro.
    destruct (griotte_lang.to_val (griotte_lang.Instr c)); cbn; [by iApply "HΨ" | done].
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
  (* Bind Scope expr_scope with language.expr griotte_lang. *)

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
    iIntros (σ1 nt l1 l2 ns) "(Hσ1 & %Hrdom & Hlink & Hirq) /="; destruct σ1 as [pc r sr m st td]; simpl.
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
    iFrame "Hlink". iSplitL "HPCa Hr Hsr Hm Hst HR HC".
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
    iIntros (σ1 ns κ κs nt) "(Hσ & %Hrdom & Hlink & Hirq) /=".
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iDestruct (gen_heap_valid with "Hr Hr'") as %Hlookup.
    iSpecialize ("HΦ" with "[%] Hr'").
    { intros ->. by eapply er_cnull. }
    iApply ("HΦ" $! σ1 ns κ κs nt). iFrame "Hlink Hirq %".
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
  Qed.

End griotte_lang_rules.

Section instruction_closing.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {th : Thread}.

  (** The closing lemmas below conclude that the step keeps MIE and mtdc
      ([sys_kept]): they do not change the system registers. *)

  (** Closes a failed instruction: the state is unchanged. *)
  Lemma instr_close_fail pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) (Φ : griotte_lang.val → iProp Σ) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ griotte_lang.FaultedV) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) (MkExecConf pc r sr m st td)⌝ ∗
    cerise_state_interp (MkExecConf pc r sr m st td) ∗
    from_option Φ False (griotte_lang.to_val (griotte_lang.Instr Faulted)).
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
      (regs : LReg) n c σ' (Φ : griotte_lang.val → iProp Σ)
      (P : LWord → griotte_lang.val → Prop) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    (match advancePC (MkExecConf pc r sr m st td) n with
     | Some conf => conf | None => (Faulted, (MkExecConf pc r sr m st td)) end) = (c, σ') →
    (∀ lpc', incrementPC_gen lpc n = Some lpc' → P lpc' griotte_lang.NextIV) →
    (incrementPC_gen lpc n = None → P lpc griotte_lang.FaultedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' retv, ⌜P lpc' retv⌝ -∗ PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ retv) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) σ'⌝ ∗
    cerise_state_interp σ' ∗ from_option Φ False (griotte_lang.to_val (griotte_lang.Instr c)).
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

  (** Closes an instruction that writes one register then increments the PC,
      as the physical [nextPC (update_reg φ dst v)]. The spec [P] holds of
      the new PC and owned registers on success, and of the old ones on
      failure. *)
  Lemma instr_close_reg_update pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) c σ' (Φ : griotte_lang.val → iProp Σ)
      (P : LWord → LReg → griotte_lang.val → Prop) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    regs ⊆ lreg →
    dst = cnull ∨ dst ∈ dom regs →
    reg_word_ok R C v →
    (match nextPC (update_reg (MkExecConf pc r sr m st td) dst w) with
     | Some conf => conf | None => (Faulted, (MkExecConf pc r sr m st td)) end) = (c, σ') →
    reg_phys R v w →
    (∀ lpc', incrementPC lpc = Some lpc' → P lpc' (<[dst := v]ₗ> regs) griotte_lang.NextIV) →
    (incrementPC lpc = None → P lpc regs griotte_lang.FaultedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' regs' retv, ⌜P lpc' regs' retv⌝ -∗ PC ↦ₚ lpc' -∗
       ([∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗ Φ retv) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) σ'⌝ ∗
    cerise_state_interp σ' ∗ from_option Φ False (griotte_lang.to_val (griotte_lang.Instr c)).
  Proof.
    iIntros (Her Hlregs Hdst Hok Hstep Hw HPs HPf) "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hφ".
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ _ dst v w Her Hok Hw) as Her1.
    rewrite /update_reg /= in Hstep.
    destruct (incrementPC lpc) as [lpc'|] eqn:Hi.
    - destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      iMod (lreg_update _ _ dst v Hdst with "Hr Hmap") as "[Hr Hmap]".
      iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
      iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
      iSplitR "Hφ HPC Hmap".
      + iApply (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC").
      + iApply ("Hφ" with "[%] HPC Hmap"). by apply HPs.
    - pose proof (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as Hfail.
      rewrite /nextPC Hfail in Hstep.
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply ("Hφ" with "[%] HPC Hmap"). by apply HPf.
  Qed.

  (** Closes an instruction that sets the PC to [lpc'] and writes one
      register, as the physical [update_reg (update_pcc φ pc') dst w]. *)
  Lemma instr_close_reg_set_pc pc (r : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) dst (v : LWord) (w : Word) (lpc' : LWord) (pc' : Word)
      (Φ : griotte_lang.val → iProp Σ) :
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
    (PC ↦ₚ lpc' -∗ ([∗ map] k↦y ∈ <[dst := v]ₗ> regs, k ↦ᵣ y) -∗ Φ griotte_lang.NextIV) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) (update_reg (update_pcc (MkExecConf pc r sr m st td) pc') dst w)⌝ ∗
    cerise_state_interp (update_reg (update_pcc (MkExecConf pc r sr m st td) pc') dst w) ∗
    from_option Φ False (griotte_lang.to_val (griotte_lang.Instr NextI)).
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
      (Φ : griotte_lang.val → iProp Σ) :
    erasure R C (MkExecConf pc r sr m st td) lpc lreg (ls_join lsreg) lmem →
    reg_word_ok R C lpc' →
    reg_phys R lpc' pc' →
    pc_ok lpc'.(lw) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗ sys_interp lsreg -∗ gen_heap_interp lmem -∗
    gen_heap_interp st -∗ reg_auth R -∗ addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (PC ↦ₚ lpc' -∗ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗ Φ griotte_lang.NextIV) ==∗
    ⌜sys_kept (MkExecConf pc r sr m st td) (update_pcc (MkExecConf pc r sr m st td) pc')⌝ ∗
    cerise_state_interp (update_pcc (MkExecConf pc r sr m st td) pc') ∗
    from_option Φ False (griotte_lang.to_val (griotte_lang.Instr NextI)).
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
  try iApply (instr_close_link_kept with "Hlink");
  iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|];
  iIntros "HPC Hmap"; iApply "Hφ"; iFrame; iPureIntro.

(** The same, after substituting the faulted configuration given by
    [Hstep : (Faulted, φ) = (c, σ')]. *)
Ltac instr_fail Hstep :=
  first [injection Hstep as <- <- | simplify_eq]; instr_fail_close.

(** Pure side conditions of the map-form rules ([wp_Get_next], …) applied to
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
    (∀ R r sr m st td, lregs_phys R regs r →
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
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr (Hfailed R r sr m st td Hregs) in Hstep. simplify_eq.
    iModIntro. iSplit; first (iPureIntro; apply sys_kept_refl).
    iSplitR "Hφ HPC Hpc_a Hmap"; last (cbn; iApply "Hφ"; iFrame).
    iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
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
    - intros R r sr m st td _. apply Hfailed.
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
    - intros R r sr m st td Hincl.
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
    - intros R r sr m st td Hincl.
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
    - intros R r sr m st td Hincl.
      destruct (lregs_phys_lookup _ _ r r1 w1 Hincl) as [s1 Hl1]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r2 w2 Hincl) as [s2 Hl2]; first by simplify_map_eq.
      destruct (lregs_phys_lookup _ _ r r3 w3 Hincl) as [s3 Hl3]; first by simplify_map_eq.
      by eapply Hfailed.
    - iNext. iIntros "(HPC & Hmem & Hmap)".
      iDestruct (regs_of_map_3 with "Hmap") as "(Hr1 & Hr2 & Hr3)"; eauto.
      iApply "Hφ". iFrame.
  Qed.
End instruction_outcomes.
