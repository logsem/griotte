From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base.
Import core_link.

(** * Environment call

    [ecall] enters the exception handler at the instruction step, with cause
    [MCAUSE_ECALL_MACHINE] and value [MTVAL_NONE]: MEPCC receives the PC,
    MPIE receives MIE, MIE is disabled, and the PC receives the trap vector.
    It writes the volatile registers, so its rules consume them
    ([vol_lent_any]) and the unwedged token, which pins MTCC to the trap
    vector. At a user thread, its value is the switch value [YieldV]. *)

(** The value of a successful [ecall]. *)
Lemma tval_sw_ecall k :
  tval_sw k Ecall NextIV = if k is UserK then YieldV else NextIV.
Proof. by destruct k. Qed.

Lemma tval_sw_ecall_user th :
  th ≠ CtxSwitch → tval_sw (kind_of th) Ecall NextIV = YieldV.
Proof. destruct th; [done | by intros []]. Qed.

Lemma tval_sw_ecall_ctx th :
  th = CtxSwitch → tval_sw (kind_of th) Ecall NextIV = NextIV.
Proof. by intros ->. Qed.

Section griotte_lang_rules.
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
    iDestruct "Hvol" as (p0 c0 v0 b0) "(HU & Hmepcc & Hmcause & Hmtval & Hmpie_f)".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link E pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "HPC Hpc_a Hmap0");
      first done.
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr /exec in Hstep. cbn in Hstep. injection Hstep as <- <-.
    rewrite Hinstr.
    set (σ1 := {| pcc := Cap pc_p pc_g pc_b pc_e pc_a; reg := r; sreg := psr; mem := m;
                  shadowtbl := st; timedevs := td |}).
    (* The trap vector, from the unwedged token. *)
    iDestruct (sys_interp_mie_agree with "Hsr Hmie_f") as %Hmie.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    iDestruct (sys_interp_mtcc with "Hsr HU") as %Htcc.
    pose proof (erasure_enter_exc _ _ _ _ _ _ _ (MCAUSE_ECALL_MACHINE, MTVAL_NONE) _ Her Htcc)
      as Her'.
    (* mstatus: MIE is disabled and MPIE receives MIE. *)
    set (mie_old := mie_of (get_a (sreg_word σ1 mstatus))).
    assert (mie_old = ls_mie lsreg) as Hmie_old.
    { rewrite -Hmie_st /mie_old /mie_st /sreg_word /σ1 /=. by destruct (psr !! mstatus). }
    iMod (sys_interp_set_mstatus _ _ _ InterruptDisabled mie_old with "Hsr Hmie_f Hmpie_f")
      as "(Hsr & Hmie_f & Hmpie_f)".
    (* MEPCC, mcause, mtval and the PC. *)
    iNamed "Hsr". destruct Hlsh as [Hn1 Hn2].
    iMod (gen_heap_update _ _ _ (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
           with "Hsr Hmepcc") as "[Hsr Hmepcc]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt MCAUSE_ECALL_MACHINE))
           with "Hsr Hmcause") as "[Hsr Hmcause]".
    iMod (gen_heap_update _ _ _ (lword_of_word (WInt MTVAL_NONE))
           with "Hsr Hmtval") as "[Hsr Hmtval]".
    iMod (PC_update _ _ (lword_of_word mtcc_vec) with "HPCa HPC") as "[HPCa HPC]".
    pose (ls' := MkLSys
      (<[mtval := lword_of_word (WInt MTVAL_NONE)]>
        (<[mcause := lword_of_word (WInt MCAUSE_ECALL_MACHINE)]>
          (<[mepcc := lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)]> (ls_sh lsreg))))
      (ls_mtdc lsreg) (ls_vmtdc lsreg) InterruptDisabled mie_old).
    assert (lsregs_enter_exc (MCAUSE_ECALL_MACHINE, MTVAL_NONE) σ1
              (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) (ls_join lsreg) = ls_join ls')
      as Hjoin.
    { apply map_eq. intros i.
      rewrite /lsregs_enter_exc /ls' /ls_join /lsregs_join /mie_old /=.
      destruct i; by simplify_map_eq. }
    rewrite Hjoin in Her'.
    iAssert (sys_interp ls') with "[Hsr Hmtcc Hmpie Hmtdc Hlent Hmie]" as "Hsys".
    { rewrite /sys_interp /ls'. cbn [ls_sh ls_mtdc ls_vmtdc ls_mie ls_mpie ls_set_mstatus] in *.
      iFrame "Hsr Hmtcc Hmpie Hmtdc Hlent Hmie". iSplit; first done.
      iPureIntro. split; by simplify_map_eq. }
    iPoseProof (SI_close (enter_exc (MCAUSE_ECALL_MACHINE, MTVAL_NONE) σ1) mtcc_vec lreg ls' lmem
                  R C Her' with "HPCa Hr Hsys Hm Hst HR HC") as "HSI".
    assert (mie_st (enter_exc (MCAUSE_ECALL_MACHINE, MTVAL_NONE) σ1) = InterruptDisabled)
      as Hoff'.
    { exact (proj1 (erasure_mie_st _ _ _ _ _ _ _ Her')). }
    (* The link moves from MIE [b] to MIE disabled; mtdc is unchanged. *)
    iMod (Htr σ1 (enter_exc (MCAUSE_ECALL_MACHINE, MTVAL_NONE) σ1) with "[$HSI $Hlink $HT]")
      as "(HSI & Hlink & HT)".
    { split_and!; [by rewrite Hmie_st Hmie | exact Hoff' | by rewrite /= !lookup_insert_ne]. }
    iModIntro. iFrame "HSI Hlink". iSplitR.
    { iApply ctx_irq_post_route. rewrite Hoff'. by intros. }
    iApply "Hφ". rewrite Hmie_old Hmie. iFrame.
  Qed.

  (** A user thread's [ecall]: the switch value [YieldV], through the
      sequencing context. *)
  Lemma twp_ecall E pc_p pc_g pc_b pc_e pc_a pc_π w (b : InterruptStatus) dq
      (T1 T2 : iProp Σ) (Φ : tval (kind_of th) → iProp Σ) :
    th ≠ CtxSwitch →
    decodeInstrW w.(lw) = Ecall →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    link_transfer_si (mie_move b InterruptDisabled) T1 T2 →
    ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ MIE ↦ₜ b -∗
    ▷ vol_lent_any -∗
    ▷ T1 -∗
    ▷ (PC ↦ₚ lword_of_word mtcc_vec -∗
       pc_a ↦ₐ{dq} w -∗
       MIE ↦ₜ InterruptDisabled -∗
       vol_lent (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
         (lword_of_word (WInt MCAUSE_ECALL_MACHINE)) MTVAL_NONE b -∗
       T2 -∗
       Φ YieldV) -∗
    WP Exec @ E {{ Φ }}.
  Proof.
    iIntros (Hth Hinstr Hvpc Htr) "HPC Hpc_a Hmie Hvol HT Hφ".
    iApply (wp_bind (@fill (tlang_ectx _) [SeqCtx])).
    iApply (wp_ecall_link with "[$HPC $Hpc_a $Hmie $Hvol $HT]"); [done..|].
    iIntros "!> (HPC & Hpc_a & Hmie & Hvol & HT)".
    rewrite tval_sw_ecall_user //=.
    iApply wp_pure_step_later; first done. iIntros "!> _".
    iApply wp_value. iApply ("Hφ" with "HPC Hpc_a Hmie Hvol HT").
  Qed.

  (** The context-switch thread's [ecall]: an ordinary step to the
      exception entry, at MIE disabled. *)
  Lemma wp_ecall_cs E pc_p pc_g pc_b pc_e pc_a pc_π w dq :
    th = CtxSwitch →
    decodeInstrW w.(lw) = Ecall →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ InterruptDisabled ∗
        ▷ vol_lent_any }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lword_of_word mtcc_vec ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ InterruptDisabled ∗
          vol_lent (lmepcc_of_pc (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
            (lword_of_word (WInt MCAUSE_ECALL_MACHINE)) MTVAL_NONE InterruptDisabled }}}.
  Proof.
    iIntros (Hth Hinstr Hvpc φ) "(HPC & Hpc_a & Hmie & Hvol) Hφ".
    iApply (wp_ecall_link E pc_p pc_g pc_b pc_e pc_a pc_π w InterruptDisabled dq True%I True%I
             with "[$HPC $Hpc_a $Hmie $Hvol //]");
      [done | done | apply link_transfer_si_kept |].
    iIntros "!> (HPC & Hpc_a & Hmie & Hvol & _)".
    rewrite tval_sw_ecall_ctx //. iApply "Hφ". iFrame.
  Qed.
End griotte_lang_rules.

(** The core corollary: [wp_ecall_link] at the core link. *)
Section griotte_lang_rules_core.
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
End griotte_lang_rules_core.
