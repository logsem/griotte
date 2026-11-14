From iris.proofmode Require Import proofmode.
From griotte Require Import handoff pool switcher_link context_switch_layout_instance.
From griotte Require Import context_switching_support.

(** * The park of a user thread by the context-switch thread

    After the spill, the context-switch thread parks the user thread [t]
    whose Saving token it holds: [t]'s slot becomes Suspended, with the
    spilled save area, [t]'s mtdc token, and resume values that the save
    area allows; [cur] becomes [None], and the context-switch thread's
    open pool token closes. *)

Section ctx_park.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** The resume PC of a save area spilled at an interrupt: the interrupted
      PC, which is already legal. *)
  #[local] Lemma resume_pc_irq (ws : list LWord) (lreg : LReg) (pc : Word) (c mshwmb_v mshwm_v : Z) :
    length ws = 21%nat →
    c ∈ irq_causes →
    pc_ok pc →
    resume_pc_word (ctx_spill ws lreg (lword_of_word pc) InterruptEnabled c mshwmb_v mshwm_v) = pc.
  Proof.
    intros Hlen Hc Hok.
    destruct ws as
      [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10
      [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    rewrite /resume_pc_word /save_area_word /ctx_spill /=.
    rewrite decide_False; first by apply legalise_pc_ok_id.
    rewrite /irq_causes !elem_of_cons elem_of_nil in Hc.
    intros ->. by repeat destruct Hc as [Hc|Hc].
  Qed.

  (** The resume PC of a save area spilled at a yield: the PC after the
      [ecall]. *)
  #[local] Lemma resume_pc_yield (ws : list LWord) (lreg : LReg) (p : LWord)
      (b : InterruptStatus) (mshwmb_v mshwm_v : Z) :
    length ws = 21%nat →
    resume_pc_word (ctx_spill ws lreg p b MCAUSE_ECALL_MACHINE mshwmb_v mshwm_v) = (yield_resume_pc p).(lw).
  Proof.
    intros Hlen.
    destruct ws as
      [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10
      [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      done.
  Qed.

  (** The park of an interrupted user thread [t]: its Saving slot becomes
      Suspended with the spilled save area and its mtdc token; [cur] becomes
      [None], and [Nact] closes. *)
  Lemma ctx_park_irq_spec (ts : list nat) (t : nat) (v : resume_vals) (ws : list LWord) (c : Z) :
    NoDup ts →
    length ws = 21%nat →
    v.(rv_mie) = InterruptEnabled →
    c ∈ irq_causes →
    dom v.(rv_regs) = all_registers_s →
    v.(rv_regs) !! cnull = Some lnull →
    pc_ok v.(rv_pc).(lw) →
    (get_tag v.(rv_pc).(lw) = true → v.(rv_pc).(lprov) = None) →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread t, Saving ParkIrq v)) -∗
    save_area_holed (UserThread t)
      (ctx_spill ws v.(rv_regs) (lword_of_word v.(rv_pc).(lw)) InterruptEnabled c
         v.(rv_hwmb) v.(rv_hwm)) -∗
    mtdc_lent_at (th := UserThread t) -∗
    hwm_base[u t] v.(rv_hwmb) -∗
    na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) -∗
    close_Nact
    ={⊤}=∗
    na_own (tpool CtxSwitch) ⊤.
  Proof.
    iIntros (Hnd Hlen Hmie Hc Hdom Hnull Hpc_ok Hpc_id)
      "#Hpool Hcur Hsa Hlent #Hbase Hna Hclose".
    destruct (resume_ok_ctx_spill ws v.(rv_regs) (lword_of_word v.(rv_pc).(lw))
                InterruptEnabled c v.(rv_hwmb) v.(rv_hwm) Hlen Hdom Hnull)
      as (Hregs & Hmie_ok & Hmpie & Hhwmb & Hhwm).
    iMod (pool_park ts t ParkIrq v ⊤ Hnd with "Hpool Hcur [Hsa Hlent]") as "Hcur";
      [solve_ndisj| |].
    { iIntros "Hauths Hcont". iModIntro.
      iExists _, v. iFrame "Hlent Hauths". iSplit.
      - iPureIntro. split_and!; [done | by rewrite Hmie Hmpie | | by rewrite Hhwmb | by rewrite Hhwm].
        split; last done.
        by rewrite resume_pc_irq.
      - iSplitL "Hsa".
        { rewrite /save_area_at /=. iFrame "Hsa". iSplit; first by iPureIntro.
          iExists v.(rv_hwmb). iFrame "Hbase". iPureIntro.
          exact (ctx_spill_word_mshwmb ws v.(rv_regs) (lword_of_word v.(rv_pc).(lw)) InterruptEnabled c
                   v.(rv_hwmb) v.(rv_hwm) Hlen). }
        iSplitR; first by rewrite decide_True.
        rewrite Hmie. iNext. iIntros "_ Hlc".
        rewrite /park_cont.
        iMod (lc_fupd_elim_later with "Hlc Hcont") as "Hsafe".
        iExact "Hsafe". }
    iApply ("Hclose" with "[$Hcur $Hna]").
  Qed.

  (** The park of a yielded user thread [t]: its authorities move to the
      resume values (PC after the [ecall], MIE [b]) with its MIE and PC
      fragments, which go with its continuation into the Suspended slot. *)
  Lemma ctx_park_yield_spec (ts : list nat) (t : nat) (b : InterruptStatus) (p : LWord)
      (v : resume_vals) (ws : list LWord) :
    NoDup ts →
    length ws = 21%nat →
    v.(rv_pc) = lword_of_word mtcc_vec →
    v.(rv_mie) = InterruptDisabled →
    dom v.(rv_regs) = all_registers_s →
    v.(rv_regs) !! cnull = Some lnull →
    inv Npool (Pool ts) -∗
    cur_frag (Some (UserThread t, Saving (ParkYield b p) v)) -∗
    save_area_holed (UserThread t)
      (ctx_spill ws v.(rv_regs) p b MCAUSE_ECALL_MACHINE v.(rv_hwmb) v.(rv_hwm)) -∗
    mtdc_lent_at (th := UserThread t) -∗
    hwm_base[u t] v.(rv_hwmb) -∗
    MIE ↦ₜ[u t] InterruptDisabled -∗
    PC ↦ₚ[u t] lword_of_word mtcc_vec -∗
    na_own (tpool CtxSwitch) (⊤ ∖ ↑Nact) -∗
    close_Nact
    ={⊤}=∗
    na_own (tpool CtxSwitch) ⊤.
  Proof.
    iIntros (Hnd Hlen Hpc Hmie Hdom Hnull)
      "#Hpool Hcur Hsa Hlent #Hbase HMIE_t HPC_t Hna Hclose".
    destruct (resume_ok_ctx_spill ws v.(rv_regs) p b MCAUSE_ECALL_MACHINE v.(rv_hwmb) v.(rv_hwm)
                Hlen Hdom Hnull)
      as (Hregs & Hmie_ok & Hmpie & Hhwmb & Hhwm).
    iMod (pool_park ts t (ParkYield b p) v ⊤ Hnd with "Hpool Hcur [Hsa Hlent HMIE_t HPC_t]")
      as "Hcur"; [solve_ndisj| |].
    { iIntros "Hauths Hcont".
      rewrite /auths_at /thread_auths.
      iDestruct "Hauths" as
        "( (HPC_a & Hregs_a & Hmtdc_a & HMIE_a & Hhwmb_a & Hhwm_a & Hzone_a & Hrest_a) &
           %Hcov & #Hbase_a)".
      iMod (PC_update _ _ (yield_resume_pc p) with "HPC_a HPC_t") as "[HPC_a HPC_t]".
      iMod (MIE_update _ _ b with "HMIE_a HMIE_t") as "[HMIE_a HMIE_t]".
      iModIntro.
      iExists _, (ResumeVals v.(rv_regs) (yield_resume_pc p) b v.(rv_hwmb) v.(rv_hwm) v.(rv_zone)).
      iFrame "Hlent". iSplit.
      - iPureIntro. split_and!; [done | done | | by rewrite Hhwmb | by rewrite Hhwm].
        split; last done.
        by rewrite resume_pc_yield.
      - iSplitL "Hsa".
        { rewrite /save_area_at /=. iFrame "Hsa". iSplit; first by iPureIntro.
          iExists v.(rv_hwmb). iFrame "Hbase". iPureIntro.
          exact (ctx_spill_word_mshwmb ws v.(rv_regs) p b MCAUSE_ECALL_MACHINE v.(rv_hwmb) v.(rv_hwm)
                   Hlen). }
        iSplitL "HPC_a Hregs_a Hmtdc_a HMIE_a Hhwmb_a Hhwm_a Hzone_a Hrest_a".
        { rewrite /auths_at /thread_auths /=. iFrame "∗ #". by iPureIntro. }
        iSplitR; first by rewrite decide_True.
        iNext. iIntros "Hpost Hlc".
        rewrite /park_cont.
        iMod (lc_fupd_elim_later with "Hlc Hcont") as "Hcont".
        rewrite -safe_unfold.
        iApply ("Hcont" with "HMIE_t HPC_t").
        destruct b; cbn; [done|]. by iApply posture_res_held. }
    iApply ("Hclose" with "[$Hcur $Hna]").
  Qed.

End ctx_park.
