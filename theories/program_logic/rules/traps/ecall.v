From iris.proofmode Require Import proofmode.
From griotte Require Export shapes.step.
From griotte Require Import wp_core_full.
Import core_link.

(** * Environment call

    [ecall] enters the exception handler at the instruction step, with cause
    [MCAUSE_ECALL_MACHINE] and value [MTVAL_NONE]: MEPCC receives the PC,
    MPIE receives MIE, MIE is disabled, and the PC receives the trap vector.
    It writes the volatile registers, so its rules consume them
    ([vol_lent_any]) and the unwedged token, which pins MTCC to the trap
    vector. At a user thread, its value is the switch value [YieldV]. *)

Lemma tval_sw_ecall_user th :
  th ≠ CtxSwitch → tval_sw (kind_of th) Ecall NextIV = YieldV.
Proof. destruct th; [done | by intros []]. Qed.

Lemma tval_sw_ecall_ctx th :
  th = CtxSwitch → tval_sw (kind_of th) Ecall NextIV = NextIV.
Proof. by intros ->. Qed.

Section ecall_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types w : LWord.

  (** [ecall]: the exception entry at the instruction step. MEPCC receives
      the PC, mcause [MCAUSE_ECALL_MACHINE], mtval [MTVAL_NONE], MPIE the
      MIE [b] before the step; MIE is disabled. The premise
      [link_transfer_si (mie_move b InterruptDisabled) T1 T2] moves the
      link. *)
  Lemma wp_ecall_link E pc_p pc_g pc_b pc_e pc_a pc_π w (b : InterruptStatus) dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = Ecall →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    link_transfer_si (mie_move b InterruptDisabled) T1 T2 →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ b ∗
        ▷ vol_lent_any ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET tval_sw (kind_of th) Ecall NextIV;
          PC ↦ₚ lword_of_word mtcc_vec ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ InterruptDisabled ∗
          vol_lent (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
            (lword_of_word (WInt MCAUSE_ECALL_MACHINE)) MTVAL_NONE b ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Htr φ) "(>HPC & >Hpc_a & >Hmie_f & >Hvol & HT) Hφ".
    iDestruct "Hvol" as (p0 c0 v0 b0) "(HU & Hvcsr)".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link E pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "HPC Hpc_a Hmap0");
      [done | solve_writes_mshwmb |].
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec in Hstep. cbn in Hstep. injection Hstep as <- <-.
    rewrite Hinstr.
    set (σ1 := {| pcc := Cap pc_p pc_g pc_b pc_e pc_a; reg := r; sreg := psr; mem := m;
                  shadowtbl := st; timedevs := td |}).
    iMod (enter_exc_update σ1 (MCAUSE_ECALL_MACHINE, MTVAL_NONE)
            with "HPCa Hr Hsr Hm Hst HR HC HPC Hmie_f HU Hvcsr")
      as "(%Hmie & %Hoff' & HSI & HPC & Hmie_f & Hvol)"; first exact Her.
    (* The link moves from MIE [b] to MIE disabled; mtdc is unchanged. *)
    iMod (Htr σ1 (enter_exc (MCAUSE_ECALL_MACHINE, MTVAL_NONE) σ1) with "[$HSI $Hlink $HT]")
      as "(HSI & Hlink & HT)".
    { split_and!; [by rewrite Hmie | exact Hoff' | by rewrite /= !lookup_insert_ne]. }
    iModIntro. iFrame "HSI Hlink". iSplitR.
    { iApply ctx_irq_post_route. rewrite Hoff'. by intros. }
    iApply "Hφ". iFrame.
  Qed.
End ecall_rules.

(** The core corollary: [wp_ecall_link] at the core link. *)
Section ecall_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread}.
  Implicit Types w : LWord.

  Lemma wp_ecall E pc_p pc_g pc_b pc_e pc_a pc_π w (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = Ecall →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ b ∗
        ▷ vol_lent_any }}}
      Instr Executable @ E
      {{{ RET tval_sw (kind_of th) Ecall NextIV;
          PC ↦ₚ lword_of_word mtcc_vec ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ InterruptDisabled ∗
          vol_lent (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
            (lword_of_word (WInt MCAUSE_ECALL_MACHINE)) MTVAL_NONE b }}}.
  Proof.
    iIntros (Hinstr Hvpc φ) "(HPC & Hpc_a & Hmie & Hvol) Hφ".
    iApply (wp_ecall_link E pc_p pc_g pc_b pc_e pc_a pc_π w b dq True%I True%I
             with "[$HPC $Hpc_a $Hmie $Hvol //]");
      [done | done | apply link_transfer_si_core |].
    iIntros "!> (HPC & Hpc_a & Hmie & Hvol & _)". iApply "Hφ". iFrame.
  Qed.
End ecall_rules_core.

(** ** A verified yield

    [wp_yield] is the environment call of verified code at a user thread:
    the thread hands its turn over ([YieldV]) and, when the switcher
    resumes it, continues at the next instruction, at the posture it
    yielded at, with every resource it kept. *)

Section yield.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t} {CR : ∀ t, CritRoute Σ t (CL t)} {th : Thread}.

  Lemma wp_yield (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
      (w : LWord) (dq : dfrac) (b : InterruptStatus) :
    th ≠ CtxSwitch →
    decodeInstrW w.(lw) = Ecall →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a -∗
    pc_a ↦ₐ{dq} w -∗
    MIE ↦ₜ[th] b -∗
    held (th := th) (CL := CL th) (CR := CR th) b -∗
    ▷ (PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' -∗
       pc_a ↦ₐ{dq} w -∗
       MIE ↦ₜ[th] b -∗
       held (th := th) (CL := CL th) (CR := CR th) b -∗
       safe[th]) -∗
    safe[th].
  Proof.
    iIntros (Hth Hi Hpc Ha') "HPC Hpc_a HMIE Hheld Hk".
    iApply (wp_bind (@fill (tlang_ectx _) [SeqCtx])).
    (* Ecall. *)
    iApply (wp_wand with "[HPC Hpc_a HMIE Hheld]").
    { iApply (wp_core_full_ho (ceriseg := ceriseG_of th) (th := th) (CL := CL th)
                (CR := CR th) ⊤ b
                (λ b' v, ⌜b' = InterruptDisabled⌝ ∗ ⌜v = YieldV⌝ ∗
                   PC ↦ₚ[th] lword_of_word mtcc_vec ∗ pc_a ↦ₐ{dq} w ∗
                   vol_lent (ceriseg := ceriseG_of th)
                     (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a))
                     (lword_of_word (WInt MCAUSE_ECALL_MACHINE)) MTVAL_NONE b ∗
                   na_own crit ⊤)%I
               with "Hheld HMIE").
      { by intros ?%Hth. }
      iIntros "Hho HMIE".
      iDestruct (handover_res_vol with "Hho") as "[Hcrit Hvol]".
      iApply (wp_ecall (th := th) with "[$HPC $Hpc_a $HMIE $Hvol]"); [done | done |].
      iIntros "!> (HPC & Hpc_a & HMIE & Hvol)".
      rewrite tval_sw_ecall_user //.
      iNext. iExists InterruptDisabled. by iFrame. }
    iIntros (v) "Hpost".
    iDestruct "Hpost" as (b') "(HMIE & Hpart & >-> & >-> & HPC & Hpc_a & Hvol & Hcrit)".
    iApply wp_pure_step_later; first done. iNext. iIntros "_".
    iApply wp_value. rewrite HO_yield. iSplit; first done.
    rewrite /yield_body. iExists b, (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a)).
    iSplitL "Hcrit Hvol Hpart".
    { rewrite posture_res_gen_unfold. iFrame "Hpart".
      iExists (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a)), _, MTVAL_NONE, b.
      rewrite handover_at_vol. by iFrame. }
    iFrame "HMIE HPC".
    (* The resumed thread continues after the [ecall]. *)
    iApply bi.later_intro. iIntros "HMIE HPC Hheld". rewrite safe_unfold.
    rewrite lmepcc_of_pc_correct //.
    assert (executeAllowed pc_p = true) as Hx by (by inversion Hpc).
    rewrite (yield_resume_pc_cap pc_p pc_g pc_b pc_e pc_a pc_a' Hx Ha').
    iApply ("Hk" with "HPC Hpc_a HMIE Hheld").
  Qed.
End yield.
