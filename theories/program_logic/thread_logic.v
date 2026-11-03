(** The program logic of the thread languages.

    - [dev_si]: the clause of the context-switch device in the state
      interpretation. At [CtxK], interrupts are disabled, or half of the PC
      fragment is parked there (after a resuming [mret]); at [UserK],
      [True].
    - [memG_irisG_k]: the Iris instance of thread [th] over
      [tlang (kind_of th)], with [memG_irisG]'s state interpretation and
      the device clause; the notation [WP e @[th] {{ Φ }}].
    - [wp_instr_step_sw], [wp_instr_step_sw_link]: the instruction step of
      a thread. The device is discharged inside: a step it blocks
      contradicts what the continuation returns. The value is read through
      [tval_sw]: a switch instruction of the kind gives its switch value.
    - Copies for [tlang] of the proof-mode pieces that name
      [griotte_lang] or [memG_irisG].

    The instruction rules are still stated over [griotte_lang]
    ([rules_base.v]); this file is beside them. *)
From iris.proofmode Require Import proofmode.
From griotte Require Import rules_base si_modality thread_langs.

(** The opsem reads an absent mstatus as 0, the program logic as
    interrupts disabled: the same. *)
Lemma irq_enabled_mie_st `{MachineParameters} σ :
  irq_enabled σ ↔ mie_st σ = InterruptEnabled.
Proof. rewrite /irq_enabled /mie_st /sreg_word. by destruct (sreg σ !! mstatus). Qed.

(** The clause of the context-switch device. *)
Definition dev_si `{MachineParameters} {Σ} {ceriseg : ceriseG Σ} (k : kind)
    (σ : ExecConf) : iProp Σ :=
  match k with
  | UserK => True
  | CtxK => ⌜mie_st σ = InterruptDisabled⌝ ∨ ∃ lpc, PC_fragq (DfracOwn (1/2)) lpc
  end.

#[global] Instance memG_irisG_k `{MachineParameters} {Σ} {th : Thread} {ceriseg : ceriseG Σ}
    {CL : CritLink Σ th} :
  irisGS (tlang (kind_of th)) Σ := {
  iris_invGS := cerise_invG;
  state_interp σ _ κs _ :=
    (cerise_state_interp σ ∗ @crit_link Σ th CL σ ∗ dev_si (kind_of th) σ)%I;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(** The WP of thread [th] in its thread language. *)
Notation "'WP' e '@[' th ] E {{ Φ } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG_k (th := th) (ceriseg := ceriseG_of th)))
     NotStuck E e%E Φ)
  (at level 20, th custom thread, e, Φ at level 200,
   format "'[hv' 'WP'  e  '/' '@[' th ]  E  '/' {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e '@[' th ] {{ Φ } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG_k (th := th) (ceriseg := ceriseG_of th)))
     NotStuck ⊤ e%E Φ)
  (at level 20, th custom thread, e, Φ at level 200,
   format "'[hv' 'WP'  e  '/' '@[' th ]  '/' {{  Φ  } } ']'") : bi_scope.

(** The embedding of [griotte_lang]'s values. *)
Definition tval_of_val {k} (v : griotte_lang.val) : tval k :=
  match v with
  | griotte_lang.HaltedV => HaltedV | griotte_lang.FaultedV => FaultedV
  | griotte_lang.NextIV => NextIV
  end.

(** The value of a step of instruction [i] at kind [k]: [NextIV] is the
    switch value when [i] is a switch instruction of [k]. *)
Definition tval_sw {k} (k' : kind) (i : instr) (v : griotte_lang.val) : tval k :=
  match v with
  | griotte_lang.NextIV => if sw_of k' i is Some s then TSwV s else NextIV
  | _ => tval_of_val v
  end.

Lemma tres_from_option `{MachineParameters} {PROP : bi} k σ (c : ConfFlag) i
    (Φ : tval k → PROP) :
  decoded_instr σ = Some i →
  from_option Φ False%I (to_val (Instr (tres k σ c) : expr k)) =
  from_option (λ v, Φ (tval_sw k i v)) False%I (griotte_lang.to_val (griotte_lang.Instr c)).
Proof.
  rewrite /tres. intros ->. cbn. rewrite /tval_sw.
  destruct c; cbn; [done..|]. by destruct (sw_of k i).
Qed.

(** * The device: what the clause gives *)

Section device.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ}.

  Definition ctx_dis (k : kind) (σ : ExecConf) : Prop := k = CtxK → mie_st σ = InterruptDisabled.

  (** With the whole PC fragment in hand, the clause is its left
      disjunct. *)
  Lemma dev_si_held k σ lpc : dev_si k σ -∗ PC ↦ₚ lpc -∗ ⌜ctx_dis k σ⌝ ∗ PC ↦ₚ lpc.
  Proof.
    destruct k; iIntros "Hd HPC".
    { iFrame "HPC". iPureIntro. intros Hk. discriminate. }
    iDestruct "Hd" as "[%Hd|[%lpc' HPC'] ]".
    { iFrame "HPC". iPureIntro. by intros _. }
    iDestruct (PC_frag_excl_q with "HPC HPC'") as %[].
  Qed.

  Lemma dev_si_kept k σ σ' : ctx_dis k σ → sys_kept σ σ' → ⊢ dev_si k σ'.
  Proof. destruct k; intros Hd [Hk _]; [done|]. iLeft. iPureIntro. rewrite Hk. by apply Hd. Qed.

  Lemma blocked_kept k σ σ' : ctx_dis k σ → blocked k σ σ' → sys_kept σ σ' → False.
  Proof.
    destruct k; [by intros ? []|]. intros Hd [_ Hen%irq_enabled_mie_st] [Hk _].
    rewrite Hk Hd // in Hen.
  Qed.

  (** What a step that may change MIE gives back at [CtxK]: the clause
      after the resuming [mret], MIE disabled otherwise. *)
  Definition dev_post (k : kind) (i : instr) (σ' : ExecConf) : iProp Σ :=
    match k with
    | UserK => True
    | CtxK => if decide (i = Mret) then dev_si CtxK σ' else ⌜mie_st σ' = InterruptDisabled⌝
    end%I.

  Lemma dev_post_si k i σ' : dev_post k i σ' -∗ dev_si k σ'.
  Proof.
    destruct k; rewrite /dev_post; [by iIntros|]. case_decide; [by iIntros|].
    iIntros "%". by iLeft.
  Qed.

  Lemma dev_post_blocked k i σ σ' :
    decoded_instr σ = Some i → blocked k σ σ' → dev_post k i σ' -∗ False.
  Proof.
    destruct k; [by intros ? []|]. intros Hdec [Hne Hen%irq_enabled_mie_st].
    rewrite /dev_post decide_False; last (intros ->; congruence).
    iIntros "%H". rewrite H in Hen. done.
  Qed.

  (** A step that keeps MIE gives [dev_post] from the clause before it. *)
  Lemma dev_post_kept k i σ σ' : ctx_dis k σ → sys_kept σ σ' → ⊢ dev_post k i σ'.
  Proof.
    destruct k; intros Hd [Hk _]; rewrite /dev_post; [done|].
    case_decide; [iLeft|]; iPureIntro; rewrite Hk; by apply Hd.
  Qed.
End device.

(** * The instruction step of a thread *)

Section rules_t.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (** The instruction step of thread [th]. A step that the device blocks is
      at [CtxK], where the clause and [PC ↦ₚ] give MIE disabled before the
      step, and the [sys_kept] that the continuation returns contradicts
      MIE enabled after it. *)
  Lemma wp_instr_step_sw E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
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
    -∗ WP Instr (TF Executable) @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "(Hσ & Hlink & Hdev) /=". destruct σ1 as [pc r sr m st td]; cbn.
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iMod "HPC". iMod "Hpc_a". iMod "Hmap".
    iDestruct (dev_si_held with "Hdev HPC") as "[%Hdis HPC]".
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
      by destruct (blocked_kept _ _ _ Hdis Hb Hk). }
    iModIntro. iSplitR.
    { iPureIntro. eexists [], _, σ0, []. by apply TS_instr. }
    iNext. iIntros (e2 σ2 efs Hpstep).
    inversion Hpstep as [σx c σ' Hstep Hnb'| | | | |]; subst.
    iIntros "_". iSplitR; first done.
    eapply step_exec_inv in Hstep; eauto; cbn in Hstep.
    rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hstep.
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $HPC $Hpc_a $Hmap]")
      as "(%Hk & $ & HΦ)"; first by iFrame "%".
    iModIntro. iSplitL "Hlink".
    - iSplitL "Hlink"; first (iApply (crit_link_stable with "Hlink"); by destruct Hk).
      by iApply dev_si_kept.
    - by rewrite (tres_from_option _ _ _ _ _ Hdec).
  Qed.

  (** The same for a step that may change MIE or mtdc. The continuation
      receives the link and the pure part of the clause ([ctx_dis]), and
      gives back the link of the new state and [dev_post]: at [CtxK], the
      clause after a resuming [mret], MIE disabled after any other step
      ([dev_post_kept] for a step that keeps MIE). *)
  Lemma wp_instr_step_sw_link E pc_p pc_g pc_b pc_e pc_a pc_π (w : LWord) dq (regs : LReg) Φ :
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
        "%Hdis" ∷ ⌜ctx_dis (kind_of th) (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)⌝ ∗
        "HPC" ∷ PC ↦ₚ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∗
        "Hpc_a" ∷ pc_a ↦ₐ{dq} w ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
       ==∗
       (cerise_state_interp σ' ∗ crit_link σ') ∗
       dev_post (kind_of th) (decodeInstrW w.(lw)) σ' ∗
       from_option (λ v, Φ (tval_sw (kind_of th) (decodeInstrW w.(lw)) v)) False
         (griotte_lang.to_val (griotte_lang.Instr c)))
    -∗ WP Instr (TF Executable) @ E {{ Φ }}.
  Proof.
    iIntros (Hvpc) "HPC Hpc_a Hmap Hcont".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "(Hσ & Hlink & Hdev) /=". destruct σ1 as [pc r sr m st td]; cbn.
    iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
    iMod "HPC". iMod "Hpc_a". iMod "Hmap".
    iDestruct (dev_si_held with "Hdev HPC") as "[%Hdis HPC]".
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
    { (* A blocked step: the continuation gives [dev_post], a contradiction. *)
      eapply step_exec_inv in Hs0; eauto; cbn in Hs0.
      rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hs0.
      iAssert (▷ False)%I with "[-]" as ">[]". iNext.
      iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $Hlink $HPC $Hpc_a $Hmap]")
        as "(_ & Hpost & _)"; first by iFrame "%".
      iApply (dev_post_blocked with "Hpost"); done. }
    iModIntro. iSplitR.
    { iPureIntro. eexists [], _, σ0, []. by apply TS_instr. }
    iNext. iIntros (e2 σ2 efs Hpstep).
    inversion Hpstep as [σx c σ' Hstep Hnb'| | | | |]; subst.
    iIntros "_". iSplitR; first done.
    eapply step_exec_inv in Hstep; eauto; cbn in Hstep.
    rewrite (mem_word_ok_decode _ _ _ _ Hok) in Hstep.
    iMod ("Hcont" with "[$HPCa $Hr $Hsr $Hm $Hst $HR $HC $Hlink $HPC $Hpc_a $Hmap]")
      as "([$ $] & Hpost & HΦ)"; first by iFrame "%".
    iModIntro. iSplitL "Hpost"; first by iApply dev_post_si.
    by rewrite (tres_from_option _ _ _ _ _ Hdec).
  Qed.
End rules_t.

(** * Proof mode for the thread languages *)

(** The [IntoVal] and [AsVal] hints of [griotte_lang.v], for [tlang]. *)
#[export] Hint Extern 5 (IntoVal _ _) => eapply tof_to_val; fast_done : typeclass_instances.
#[export] Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply tof_to_val; rewrite /= !tto_of_val /=; solve [ eauto ]
  : typeclass_instances.
#[export] Hint Extern 5 (AsVal _) => eexists; eapply tof_to_val; fast_done : typeclass_instances.
#[export] Hint Extern 10 (AsVal _) =>
  eexists; rewrite /IntoVal; eapply tof_to_val; rewrite /= !tto_of_val /=; solve [ eauto ]
  : typeclass_instances.

(** [elim_modal_base_fupd_wp], for the WP of a thread language. *)
#[global] Instance elim_modal_base_fupd_wp_t `{MP : MachineParameters} {Σ}
    {ceriseb : ceriseBaseG Σ} (th : Thread) {CL : CritLink Σ th} p E
    (e : expr (kind_of th)) (P : iProp Σ) Φ :
  ElimModal True p false
    (@fupd _ (@bi_fupd_fupd _ (@uPred_bi_fupd HasLc Σ (@cb_invG Σ ceriseb))) E E P) P
    (WP e @[th] E {{ Φ }}) (WP e @[th] E {{ Φ }}).
Proof.
  exact (elim_modal_fupd_wp (irisGS_gen0 := memG_irisG_k (th := th) (ceriseg := ceriseG_of th))
           p NotStuck E e P Φ).
Qed.

(** [elim_modal_cerise_fupd_wp], for the WP of a thread language. Not an
    instance, as the original. *)
Lemma elim_modal_cerise_fupd_wp_t `{MP : MachineParameters} `{ceriseg : ceriseG Σ}
    {th : Thread} {CL : CritLink Σ th} p E (e : expr (kind_of th)) (P : iProp Σ) Φ :
  ElimModal True p false
    (@fupd _ (@bi_fupd_fupd _ (@uPred_bi_fupd HasLc Σ (@cerise_invGS Σ ceriseg))) E E P) P
    (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
Proof.
  exact (elim_modal_fupd_wp (irisGS_gen0 := memG_irisG_k (th := th)) p NotStuck E e P Φ).
Qed.

Section si_upd_t.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (** [wp_si_upd], for the WP of a thread language. *)
  Lemma wp_si_upd_t s E (e : expr (kind_of th)) Φ P :
    language.to_val e = None →
    (|~{E}~> P) -∗ (P -∗ WP e @ s; E {{ Φ }}) -∗ WP e @ s; E {{ Φ }}.
  Proof.
    rewrite griotte.program_logic.si_modality.si_upd_unseal.
    iIntros (He) "HP Hwp". rewrite !wp_unfold /wp_pre He /=.
    iIntros (σ ns κ κs nt) "(Hσ & Hlink & Hdev)".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iSpecialize ("Hwp" with "HP").
    iApply ("Hwp" $! σ ns κ κs nt with "[$Hσ $Hlink $Hdev]").
  Qed.

  #[global] Instance elim_modal_si_upd_wp_t p s E (e : expr (kind_of th)) P Φ :
    ElimModal (language.to_val e = None) p false (|~{E}~> P) P
      (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (He) "[HP Hwp]". iApply (wp_si_upd_t with "HP Hwp"); done.
  Qed.
End si_upd_t.

(** [wp_instr] for the thread languages: binds the instruction under the
    program's [Seq]. The language of [fill] is given: it is not inferred
    from [[SeqCtx]]. *)
Ltac wp_instr_t :=
  iApply (wp_bind (@fill (tlang_ectx _) [SeqCtx]));
  let X := fresh in
  set X := (fill _);
  cbv in X;
  subst X;
  cbv beta.
