From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
Import core_link.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types sreg : gmap SRegName LWord.

  (** The PC after [SetMIE]: the next one, given the permission to access
      the system registers. mstatus is held by the state interpretation: the
      summary does not expose it. *)
  Definition setmie_outcome pc_p pc_g pc_b pc_e pc_a pc_π : option LWord :=
    if has_sreg_access pc_p then incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) else None.

  (** [SetMIE mie] writes MIE, from [b] to [mie]: the premise
      [link_transfer_si (mie_move b mie) T1 T2] gives [T1] up for [T2] with
      the link on success; [T1] comes back on a fault. *)
  Lemma wp_SetMIE_link Ep pc_p pc_g pc_b pc_e pc_a pc_π w mie (b : InterruptStatus) dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    link_transfer_si (mie_move b mie) T1 T2 →
    (route_pre th b → route_pre th mie) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ b ∗
        ▷ T1
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ step_outcome ((., tt) <$> setmie_outcome pc_p pc_g pc_b pc_e pc_a pc_π)
            (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) tt lpc' tt retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        (⌜retv = NextIV⌝ ∗ MIE ↦ₜ mie ∗ T2 ∨ ⌜retv = FaultedV⌝ ∗ MIE ↦ₜ b ∗ T1)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Htr Hroute φ) "(>HPC & >Hpc_a & >Hmie & HT) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link_nosw Ep pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "HPC Hpc_a Hmap0"); [rewrite Hinstr; by apply sw_of_none|..]; eauto.
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mie_agree with "Hsr Hmie") as %Hb.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    pose proof (ls_join_mstatus lsreg) as Hvst'.
    rewrite Hinstr /exec in Hstep.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. simplify_eq.
      iApply (instr_close_link_kept_irq with "Hlink"); [done|].
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
      iIntros "HPC _". iApply "Hφ". iFrame "HPC Hpc_a". iSplit.
      - iPureIntro. apply step_outcome_fault. by rewrite /setmie_outcome Hxsr.
      - iRight. by iFrame. }
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    apply reg_phys_no_bounds in Hrelst; last done. cbn in Hrelst. subst wst.
    cbn in Hstep. rewrite Hxsr Hwst /= mpie_of_mstatus_enc in Hstep.
    destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hi;
      cycle 1.
    { (* The PC increment fails: the state and the link are unchanged. *)
      pose proof (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) as Hfail.
      rewrite /nextPC /advancePC /= in Hfail.
      destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; first done.
      simplify_eq.
      iApply (instr_close_link_kept_irq with "Hlink"); [done|].
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
      iIntros "HPC _". iApply "Hφ". iFrame "HPC Hpc_a". iSplit.
      - iPureIntro. apply step_outcome_fault. by rewrite /setmie_outcome Hxsr Hi.
      - iRight. by iFrame. }
    (* The new mstatus *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ _ mstatus
                  (lword_of_word (WInt (mstatus_enc mie (ls_mpie lsreg))))
                  (WInt (mstatus_enc mie (ls_mpie lsreg))) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    rewrite -ls_join_set_mstatus in Her1.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & Her2).
    rewrite /nextPC /advancePC /update_pcc /= in Hu. rewrite /update_sreg /update_pcc /nextPC /advancePC /= in Hstep.
    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; last done. simplify_eq.
    cbn [reg sreg mem pcc shadowtbl fst snd].
    iMod (sys_interp_set_mie _ _ mie with "Hsr Hmie") as "[Hsr Hmie]".
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iPoseProof (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC") as "HSI".
    iMod (Htr _ (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a') r
                 (<[mstatus := WInt (mstatus_enc mie (ls_mpie lsreg))]> psr) m st td)
           with "[$HSI $Hlink $HT]") as "(HSI & Hlink & HT)".
    { split_and!.
      - by rewrite Hmie_st.
      - by rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc.
      - by rewrite /= lookup_insert_ne. }
    iModIntro. iFrame "HSI Hlink". iSplitR.
    { iApply ctx_irq_post_route.
      rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc. apply Hroute.
      rewrite -Hmie_st. by apply ctx_irq_off_route. }
    iApply ("Hφ" $! _ NextIV). iFrame "HPC Hpc_a". iSplit.
    - iPureIntro. apply step_outcome_next. by rewrite /setmie_outcome Hxsr Hi.
    - iLeft. by iFrame.
  Qed.

  (** [SetMIE mie], as [csrsi mstatus, 0x8] and [csrci mstatus, 0x8], with
      the link-transfer premise. *)
  Lemma wp_setmie_success_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w mie (b : InterruptStatus) dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    link_transfer_si (mie_move b mie) T1 T2 →
    (route_pre th b → route_pre th mie) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ b ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ mie ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Htr Hroute φ) "(>HPC & >Hpc_a & >Hmie & HT) Hφ".
    iApply (wp_SetMIE_link with "[$HPC $Hpc_a $Hmie $HT]"); eauto.
    iNext. iIntros (lpc' retv) "(%Hspec & HPC & Hpc_a & HT)".
    rewrite /setmie_outcome Hxsr (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hspec.
    destruct Hspec as (-> & -> & _).
    iDestruct "HT" as "[ [_ HT] | [%Hc _] ]"; last done.
    iApply "Hφ". iFrame.
  Qed.

  (** [SetMIE mie] moves the posture of the thread: what it holds at [b]
      becomes what it holds at [mie]. *)
  Lemma wp_setmie_success_posture `{CR : !CritRoute Σ th CL} E pc_p pc_g pc_b pc_e pc_a pc_π
      pc_a' w mie (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    route_pre th b →
    (route_pre th b → route_pre th mie) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ b ∗
        ▷ held b }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ mie ∗
          held mie }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hpre Hroute φ) "H Hφ".
    iApply (wp_setmie_success_link with "H");
      [done | done | done | done | by apply link_transfer_si_route | done |].
    iExact "Hφ".
  Qed.

End griotte_lang_rules.

(** The core corollaries, with today's statements: at the core link, the
    premise holds with [True]. *)
Section griotte_lang_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread}.
  Implicit Types w : LWord.

  (** [SetMIE mie], as [csrsi mstatus, 0x8] and [csrci mstatus, 0x8]: MIE
      becomes [mie], MPIE is unchanged. *)
  Lemma wp_setmie_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w mie (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    (route_pre th b → route_pre th mie) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ b }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ mie }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hroute φ) "(>HPC & >Hpc_a & >Hmie) Hφ".
    iApply (wp_setmie_success_link _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hmie]"); [done..| apply link_transfer_si_core | done | done |].
    iNext. iIntros "(HPC & Hpc_a & Hmie & _)". iApply "Hφ". iFrame.
  Qed.
End griotte_lang_rules_core.
