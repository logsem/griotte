From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export shapes.step.
From griotte Require Import si_modality.
Import core_link.

(** * The system instructions: Mret, SetMIE and SpecialRW

    Each writes MIE or a special register, so it has its own rule, with its
    outcome in closed form as a [step_outcome]; the rules that [iInstr]
    uses are derived from it. *)

(** ** Mret

    The return from the exception handler writes MIE and MPIE. One rule
    ([wp_Mret_link]) with its outcome [mret_outcome]. *)

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types sreg : gmap SRegName LWord.

  (** The PC after [mret]: the value of MEPCC in [sregs], given the
      permission to access the system registers. mstatus is held by the
      state interpretation: the summary does not expose it. *)
  Definition mret_outcome (pc_p : Perm) (sregs : LSReg) : option LWord :=
    if has_sreg_access pc_p then sregs !! mepcc else None.

  (** [mret] writes MIE (it receives MPIE [p]) and MPIE (it becomes
      enabled): the premise [link_transfer_si (mie_move b p) (S ∗ T1) T2]
      gives up [T1], the system registers [S] and the new MPIE fragment for
      [T2] with the link on success; they come back on a fault. *)
  Lemma wp_Mret_link Ep pc_p pc_g pc_b pc_e pc_a pc_π w sregs (b p : InterruptStatus) dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (if has_sreg_access pc_p
     then sregs_of Mret ⊆ dom sregs
     else True) →
    link_transfer_si (mie_move b p)
      (([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗ MPIE_frag InterruptEnabled ∗ T1) T2 →
    (route_pre th b → route_pre th p) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p ∗
        ▷ T1
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET tval_sw (kind_of th) Mret retv;
        ⌜ step_outcome ((., tt) <$> mret_outcome pc_p sregs)
            (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) tt lpc' tt retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        (⌜retv = NextIV⌝ ∗ MIE ↦ₜ p ∗ T2 ∨
         ⌜retv = FaultedV⌝ ∗ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗ MIE ↦ₜ b ∗ MPIE_frag p ∗ T1)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dsregs Htr Hroute φ) "(>HPC & >Hpc_a & >Hsmap & >Hmie & >Hmpie & HT) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link Ep pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mie_agree with "Hsr Hmie") as %<-.
    iDestruct (sys_interp_mpie_agree with "Hsr Hmpie") as %<-.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    iDestruct (sys_interp_valid with "Hsr Hsmap") as %[Hlsregs _].
    pose proof (ls_join_mstatus lsreg) as Hvst'.
    rewrite Hinstr /exec in Hstep. rewrite Hinstr.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. simplify_eq.
      iApply (instr_close_link_kept_irq with "Hlink"); [done|].
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
      iIntros "HPC _". iApply "Hφ". iFrame "HPC Hpc_a". iSplit.
      - iPureIntro. apply step_outcome_fault. by rewrite /mret_outcome Hxsr.
      - iRight. by iFrame. }
    destruct (indom_sregs_incl _ _ _ Dsregs Hlsregs mepcc) as (vepcc & Hvepcc & Hvepcc');
      first (rewrite /sregs_of; set_solver).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvepcc') as (wepcc & Hwepcc & Hrelepcc).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    apply reg_phys_no_bounds in Hrelst; last done. cbn in Hrelst. subst wst.
    cbn in Hstep. rewrite Hxsr Hwepcc Hwst /= mpie_of_mstatus_enc in Hstep.
    injection Hstep as <- <-.
    rewrite /update_pcc /update_sreg /=.
    (* The new mstatus, then the new PC: MEPCC satisfies the PC invariant. *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ _ mstatus
      (lword_of_word (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)))
      (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    rewrite -ls_join_set_mstatus in Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ _ vepcc wepcc Her1) as Her2.
    specialize (Her2 ltac:(by eapply (er_sreg_words _ _ _ _ _ _ _ Her)) Hrelepcc
                  ltac:(by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her mepcc))).
    iMod (sys_interp_set_mstatus _ _ _ (ls_mpie lsreg) InterruptEnabled
           with "Hsr Hmie Hmpie") as "(Hsr & Hmie & Hmpie)".
    iMod (PC_update _ _ vepcc with "HPCa HPC") as "[HPCa HPC]".
    iPoseProof (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC") as "HSI".
    iMod (Htr _ (MkExecConf wepcc r
                 (<[mstatus := WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)]> psr) m st td)
           with "[$HSI $Hlink $Hsmap $Hmpie $HT]") as "(HSI & Hlink & HT)".
    { split_and!.
      - done.
      - by rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc.
      - by rewrite /= lookup_insert_ne. }
    iModIntro. iFrame "HSI Hlink". iSplitR.
    { iApply ctx_irq_post_route.
      rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc. apply Hroute.
      rewrite -Hmie_st. by apply ctx_irq_off_route. }
    iApply ("Hφ" $! _ NextIV). iFrame "HPC Hpc_a". iSplit.
    - iPureIntro. apply step_outcome_next. by rewrite /mret_outcome Hxsr Hvepcc.
    - iLeft. by iFrame.
  Qed.

  (** [mret], with the link-transfer premise: MEPCC and the new MPIE
      fragment go to the transfer. *)
  Lemma wp_mret_success_link E pc_p pc_g pc_b pc_e pc_a pc_π w (vepcc : LWord)
      (b p : InterruptStatus) dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    link_transfer_si (mie_move b p) (mepcc ↦ₓ vepcc ∗ MPIE_frag InterruptEnabled ∗ T1) T2 →
    (route_pre th b → route_pre th p) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mepcc ↦ₓ vepcc ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET tval_sw (kind_of th) Mret NextIV;
          PC ↦ₚ vepcc ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ p ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Htr Hroute φ) "(>HPC & >Hpc_a & >Hepcc & >Hmie & >Hmpie & HT) Hφ".
    iDestruct (map_of_sregs_1 with "Hepcc") as "Hsmap".
    iApply (wp_Mret_link with "[$HPC $Hsmap $Hpc_a $Hmie $Hmpie $HT]"); eauto.
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    { eapply link_transfer_si_weaken; last exact Htr; last done.
      iIntros "(Hsmap & $ & $)". iApply (sregs_of_map_1 with "Hsmap"). }
    iNext. iIntros (lpc' retv) "(%Hspec & HPC & Hpc_a & HT)".
    rewrite /mret_outcome Hxsr lookup_singleton_eq in Hspec.
    destruct Hspec as (-> & -> & _).
    iDestruct "HT" as "[ [_ HT] | [%Hc _] ]"; last done.
    iApply "Hφ". iFrame.
  Qed.

  (** The user [mret] moves the posture by MPIE: from InterruptDisabled,
      with the whole posture at MPIE [p] and MEPCC [vepcc], to [p]. *)
  Lemma wp_mret_success_posture `{CR : !CritRoute Σ th CL} E pc_p pc_g pc_b pc_e pc_a pc_π w
      (vepcc : LWord) (p : InterruptStatus) dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (route_pre th InterruptDisabled → route_pre th p) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ InterruptDisabled ∗
        posture_res{p, vepcc} }}}
      Instr Executable @ E
      {{{ RET tval_sw (kind_of th) Mret NextIV;
          PC ↦ₚ vepcc ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ p ∗
          held p }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hroute φ) "(>HPC & >Hpc_a & >Hmie & Hpost) Hφ".
    rewrite posture_res_gen_unfold.
    iDestruct "Hpost" as "[(%p' & %c & %v & %b' & %Hpb & %Hpp & _ & _ & Hcrit & HU & Hepcc & Hmcause
                            & Hmtval & Hmpie) Hpart]".
    cbn in Hpb, Hpp. subst b' p'.
    iApply (wp_mret_success_link _ _ _ _ _ _ _ _ _ _ _ _
              (na_own crit ⊤ ∗ unwedged ∗ mcause ↦ₓ c ∗ mtval ↦ₓ lword_of_word (WInt v) ∗
               @posture_part _ _ _ th CL CR)%I (held p)
             with "[$HPC $Hpc_a $Hepcc $Hmie $Hmpie $Hcrit $HU $Hmcause $Hmtval $Hpart]");
      [done | done | done | | done |].
    { eapply link_transfer_si_weaken; last apply (link_transfer_si_route InterruptDisabled p);
        [| done | by intros].
      iIntros "(Hepcc & Hmpie & Hcrit & HU & Hmcause & Hmtval & Hpart)".
      rewrite /held /held_of. iFrame "Hpart".
      iApply (handover_res_intro vepcc c v InterruptEnabled).
      rewrite /handover_at /volatile_csr_at. iFrame. }
    iExact "Hφ".
  Qed.

End griotte_lang_rules.

(** The core corollaries, with today's statements. *)
Section griotte_lang_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread}.
  Implicit Types w : LWord.

  (** [mret]: the PC receives MEPCC; MIE receives MPIE and MPIE becomes
      enabled. *)
  Lemma wp_mret_success E pc_p pc_g pc_b pc_e pc_a pc_π w (vepcc : LWord)
      (b p : InterruptStatus) dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (route_pre th b → route_pre th p) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mepcc ↦ₓ vepcc ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p }}}
      Instr Executable @ E
      {{{ RET tval_sw (kind_of th) Mret NextIV;
          PC ↦ₚ vepcc ∗
          pc_a ↦ₐ{dq} w ∗
          mepcc ↦ₓ vepcc ∗
          MIE ↦ₜ p ∗
          MPIE_frag InterruptEnabled }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hroute φ) "(>HPC & >Hpc_a & >Hepcc & >Hmie & >Hmpie) Hφ".
    iApply (wp_mret_success_link _ _ _ _ _ _ _ _ _ _ _ _ True%I
              (mepcc ↦ₓ vepcc ∗ MPIE_frag InterruptEnabled ∗ True)%I
             with "[$HPC $Hpc_a $Hepcc $Hmie $Hmpie]");
      [done..| apply link_transfer_si_core | done | done |].
    iNext. iIntros "(HPC & Hpc_a & Hmie & Hepcc & Hmpie & _)". iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules_core.

(** The resuming [mret] of the context-switch thread. *)
Section griotte_lang_rules_ctx.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {CL : CritLink Σ CtxSwitch}.
  Implicit Types w : LWord.

  (** The resuming [mret], from MIE disabled to the MIE [q] saved in MPIE:
      the value is [ResumedV]. The new PC is [lpc'], the word of mepcc with
      an identifier that may differ when it is untagged. When [q] is
      enabled, half of the new PC fragment goes to the context-switch
      thread's interrupt clause of the state interpretation, the other half
      to the caller; otherwise the caller gets the whole fragment. *)
  Lemma wp_mret_resume E pc_p pc_g pc_b pc_e pc_a pc_π w (vepcc lpc' : LWord)
      (q : InterruptStatus) dq (T1 T2 : iProp Σ) (Φ : tval CtxK → iProp Σ) :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    lpc'.(lw) = vepcc.(lw) →
    (get_tag lpc'.(lw) = true → lpc'.(lprov) = None) →
    link_transfer_si (th := CtxSwitch) (mie_move InterruptDisabled q)
      (mepcc ↦ₓ vepcc ∗ MPIE_frag InterruptEnabled ∗ T1) T2 →
    ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
    ▷ pc_a ↦ₐ{dq} w ∗
    ▷ mepcc ↦ₓ vepcc ∗
    ▷ MIE ↦ₜ InterruptDisabled ∗
    ▷ MPIE_frag q ∗
    ▷ T1 ∗
    ▷ (PC_fragq (if q is InterruptEnabled then DfracOwn (1/2) else DfracOwn 1) lpc' -∗
       pc_a ↦ₐ{dq} w -∗
       MIE ↦ₜ q -∗
       T2 -∗
       Φ ResumedV) ⊢
    @wp _ _ _ _ (@wp' _ _ _ (memG_irisG (th := CtxSwitch))) NotStuck E (Instr Executable) Φ.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hlw Hprov Htr)
      "(>HPC & >Hpc_a & >Hepcc & >Hmie & >Hmpie & HT & Hφ)".
    iDestruct (map_of_sregs_1 with "Hepcc") as "Hsmap".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link E pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "HPC Hpc_a Hmap0");
      [done | solve_writes_mshwmb |].
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr.
    iDestruct (sys_interp_mie_agree with "Hsr Hmie") as %Hmie.
    iDestruct (sys_interp_mpie_agree with "Hsr Hmpie") as %Hmpie.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    iDestruct (sys_interp_valid with "Hsr Hsmap") as %[Hlsregs _].
    pose proof (ls_join_mstatus lsreg) as Hvst'.
    rewrite Hinstr /exec in Hstep.
    assert (ls_join lsreg !! mepcc = Some vepcc) as Hv'.
    { eapply lookup_weaken; [|exact Hlsregs]. by simplify_map_eq. }
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv') as (wepcc & Hwepcc & Hrelepcc).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    apply reg_phys_no_bounds in Hrelst; last done. cbn in Hrelst. subst wst.
    cbn in Hstep. rewrite Hxsr Hwepcc Hwst /= mpie_of_mstatus_enc in Hstep.
    injection Hstep as <- <-.
    rewrite /update_pcc /update_sreg /=.
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ _ mstatus
      (lword_of_word (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)))
      (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    rewrite -ls_join_set_mstatus in Her1.
    (* The new PC [lpc'] is [vepcc] when tagged, and an untagged word
       otherwise: it keeps the clauses of the erasure. *)
    assert (reg_word_ok R C lpc' ∧ reg_phys R lpc' wepcc ∧ pc_ok lpc'.(lw))
      as (Hok' & Hphys' & Hpcok').
    { pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv') as Hokv.
      assert (pc_ok vepcc.(lw)) as Hpcv.
      { by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her mepcc). }
      destruct (get_tag lpc'.(lw)) eqn:Htag.
      - assert (lpc' = vepcc) as ->; last done.
        destruct lpc' as [lw' π'], vepcc as [lw0 π0]; cbn in *. subst lw'.
        rewrite (Hprov eq_refl).
        destruct Hokv as (_ & _ & Hexec). destruct (Hpcv Htag) as [_ Hx].
        by destruct (Hexec Htag Hx) as [Hπ _]; cbn in Hπ; subst π0.
      - split_and!.
        + by apply reg_word_ok_untagged.
        + split.
          * left. rewrite Hlw.
            destruct Hrelepcc as [ [->| [-> _] ] _]; first done.
            rewrite clear_tag_untagged //. by rewrite -Hlw.
          * intros ι x Hauth. apply has_authority_tag in Hauth. congruence.
        + by apply pc_ok_untagged. }
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ _ lpc' wepcc Her1 Hok' Hphys' Hpcok')
      as Her2.
    iMod (sys_interp_set_mstatus _ _ _ (ls_mpie lsreg) InterruptEnabled
           with "Hsr Hmie Hmpie") as "(Hsr & Hmie & Hmpie)".
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iPoseProof (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC") as "HSI".
    iMod (Htr _ (MkExecConf wepcc r
                 (<[mstatus := WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)]> psr) m st td)
           with "[$HSI $Hlink Hsmap $Hmpie $HT]") as "(HSI & Hlink & HT)".
    { split_and!.
      - by rewrite Hmie_st.
      - by rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc Hmpie.
      - by rewrite /= lookup_insert_ne. }
    { iApply (sregs_of_map_1 with "Hsmap"). }
    rewrite Hmpie.
    iModIntro. iFrame "HSI Hlink".
    destruct q.
    - iDestruct (PC_frag_split with "HPC") as "[HPC HPC']".
      iSplitL "HPC".
      + (* Half of the PC fragment is deposited in the clause. *)
        iRight. by iExists _.
      + iApply ("Hφ" with "HPC' Hpc_a Hmie HT").
    - iSplitR.
      + iLeft. by rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc.
      + iApply ("Hφ" with "HPC Hpc_a Hmie HT").
  Qed.
End griotte_lang_rules_ctx.

(** ** SetMIE

    SetMIE writes MIE. One rule ([wp_SetMIE_link]) with its outcome
    [setmie_outcome]. *)

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

(** ** SpecialRW

    SpecialRW reads and writes the special registers. One rule
    ([wp_SpecialRW]) with its outcome [specialrw_outcome], and dedicated
    forms for mtdc and its ghost state. *)

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types sreg : gmap SRegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** The system registers after [SpecialRW _ sr src]: the source [inr cnull]
      does not write [sr], any other source writes its legalised value. *)
  Definition specialrw_sregs (regs : LReg) (sregs : LSReg) (sr : SRegName)
      (src : Z + RegName) : option LSReg :=
    match src with
    | inr r =>
        if decide (r = cnull) then Some sregs
        else v ← regs !!ₗ r; Some (<[sr := llegalise sr v]> sregs)
    | inl z => Some (<[sr := llegalise sr (WInt z)]> sregs)
    end.

  (** The registers after [SpecialRW dst _ _] with old value [vold]: the
      destination [cnull] drops it. *)
  Definition specialrw_regs (regs : LReg) (dst : RegName) (vold : LWord) : LReg :=
    if decide (dst = cnull) then regs else <[dst := vold]> regs.

  Lemma specialrw_regs_cnull regs vold : specialrw_regs regs cnull vold = regs.
  Proof. rewrite /specialrw_regs. by case_decide. Qed.

  Lemma specialrw_regs_ne regs dst vold :
    dst ≠ cnull → specialrw_regs regs dst vold = <[dst := vold]> regs.
  Proof. rewrite /specialrw_regs. by case_decide. Qed.

  (** The PC, registers and system registers after [SpecialRW dst sr src],
      given the permission to access the system registers: the old value of
      [sr] goes to [dst], [sr] receives the source, and the PC is the next
      one. *)
  Definition specialrw_outcome (regs : LReg) (sregs : LSReg) pc_p pc_g pc_b pc_e pc_a pc_π
      (dst : RegName) (sr : SRegName) (src : Z + RegName) : option (LWord * (LReg * LSReg)) :=
    if has_sreg_access pc_p
    then
      vold ← sregs !! sr;
      sregs' ← specialrw_sregs regs sregs sr src;
      lpc' ← incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π);
      Some (lpc', (specialrw_regs regs dst vold, sregs'))
    else None.

  Lemma specialrw_outcome_some regs sregs pc_p pc_g pc_b pc_e pc_a pc_π lpc' dst sr src vold sregs' :
    has_sreg_access pc_p = true →
    sregs !! sr = Some vold →
    specialrw_sregs regs sregs sr src = Some sregs' →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    specialrw_outcome regs sregs pc_p pc_g pc_b pc_e pc_a pc_π dst sr src =
      Some (lpc', (specialrw_regs regs dst vold, sregs')).
  Proof. intros Hxsr Hvold Hsregs' Hi. by rewrite /specialrw_outcome Hxsr Hvold Hsregs' Hi. Qed.

  Lemma specialrw_outcome_fail_pc regs sregs pc_p pc_g pc_b pc_e pc_a pc_π dst sr src :
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None →
    specialrw_outcome regs sregs pc_p pc_g pc_b pc_e pc_a pc_π dst sr src = None.
  Proof.
    intros Hi. rewrite /specialrw_outcome Hi.
    by destruct (has_sreg_access pc_p), (sregs !! sr), (specialrw_sregs regs sregs sr src).
  Qed.

  (** The physical system registers after the write, and the erasure of the
      new logical ones. *)
  Lemma specialrw_sregs_phys R C pc (r : Reg) psr m st td lpc lreg lsreg lmem regs sregs sr src vold :
    erasure R C (MkExecConf pc r psr m st td) lpc lreg lsreg lmem →
    regs ⊆ lreg →
    lregs_phys R regs r →
    sregs ⊆ lsreg →
    regs_of_argument src ∖ {[ cnull ]} ⊆ dom regs →
    sregs !! sr = Some vold →
    ∃ sregs' psr' lsreg',
      specialrw_sregs regs sregs sr src = Some sregs' ∧
      (match src with
       | inr rs =>
           if decide (rs = cnull) then Some (MkExecConf pc r psr m st td)
           else wsrc ← r !!ᵣ rs; Some (update_sreg (MkExecConf pc r psr m st td) sr (legalise sr wsrc))
       | inl z => Some (update_sreg (MkExecConf pc r psr m st td) sr (legalise sr (WInt z)))
       end) = Some (MkExecConf pc r psr' m st td) ∧
      erasure R C (MkExecConf pc r psr' m st td) lpc lreg lsreg' lmem ∧
      ((sregs' = sregs ∧ lsreg' = lsreg) ∨
       ∃ nv, sregs' = <[sr := nv]> sregs ∧ lsreg' = <[sr := nv]> lsreg).
  Proof.
    intros Her Hlregs Hregs Hlsregs Dsrc Hvold.
    assert (∀ (v : LWord) pw, reg_word_ok R C v → reg_phys R v pw →
      ∃ psr' lsreg',
        update_sreg (MkExecConf pc r psr m st td) sr (legalise sr pw) = (MkExecConf pc r psr' m st td) ∧
        erasure R C (MkExecConf pc r psr' m st td) lpc lreg lsreg' lmem ∧
        lsreg' = <[sr := llegalise sr v]> lsreg) as Hwrite.
    { intros v pw Hok Hw. eexists _, _. split; first done.
      split; last done. by apply erasure_write_sreg. }
    destruct src as [z|rs]; cbn.
    - destruct (Hwrite (lword_of_word (WInt z)) (WInt z)) as (psr' & lsreg' & Hu & Her' & ->).
      { apply reg_word_ok_int. } { apply reg_phys_lword_of_word. }
      eexists _, psr', _. split; first done. rewrite Hu. split; first done.
      split; first done. right. by eexists.
    - case_decide as Hrs.
      { eexists sregs, psr, lsreg. split_and!; try done. by left. }
      assert (is_Some (regs !!ₗ rs)) as [v Hv].
      { apply elem_of_dom_lreg. apply Dsrc. set_solver. }
      destruct (llookup_reg_phys _ _ _ _ _ Hregs Hv) as (s & Hrs' & Hrel).
      destruct (Hwrite v (and_tag s v.(lw))) as (psr' & lsreg' & Hu & Her' & ->).
      { by eapply (erasure_llookup_reg_word _ _ _ _ _ _ _ regs). }
      { done. }
      eexists _, psr', _. rewrite Hv Hrs' /= Hu. split; first done. split; first done.
      split; first done. right. by eexists.
  Qed.

  (** The physical write of [SpecialRW] to a register other than MTDC and
      mstatus keeps MIE and mtdc. *)
  Lemma specialrw_sys_kept pc (r : Reg) psr m st td psr' sr src :
    sr ≠ mtdc → sr ≠ mstatus →
    (match src with
     | inr rs =>
         if decide (rs = cnull) then Some (MkExecConf pc r psr m st td)
         else wsrc ← r !!ᵣ rs; Some (update_sreg (MkExecConf pc r psr m st td) sr (legalise sr wsrc))
     | inl z => Some (update_sreg (MkExecConf pc r psr m st td) sr (legalise sr (WInt z)))
     end) = Some (MkExecConf pc r psr' m st td) →
    sys_kept (MkExecConf pc r psr m st td) (MkExecConf pc r psr' m st td).
  Proof.
    intros H1 H2 Hφ. destruct src as [z|rs]; cbn in Hφ; rewrite /update_sreg in Hφ.
    - simplify_eq. by apply sys_kept_insert_sreg.
    - case_decide; first by simplify_eq.
      destruct (r !!ᵣ rs); cbn in Hφ; simplify_eq. by apply sys_kept_insert_sreg.
  Qed.

  Lemma wp_SpecialRW Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst sr src regs sregs dq :
    decodeInstrW w.(lw) = SpecialRW dst sr src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (SpecialRW dst sr src) ⊆ dom regs →
    (if has_sreg_access pc_p
     then sregs_of (SpecialRW dst sr src) ⊆ dom sregs
     else True) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₓ y)
    }}}
      Instr Executable @ Ep
    {{{ lpc' regs' sregs' retv, RET tval_sw (kind_of th) (SpecialRW dst sr src) retv;
        ⌜ step_outcome (specialrw_outcome regs sregs pc_p pc_g pc_b pc_e pc_a pc_π dst sr src)
            (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) (regs, sregs) lpc' (regs', sregs') retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        ([∗ map] k↦y ∈ sregs', k ↦ₓ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Dsregs φ) "(>HPC & >Hpc_a & >Hmap & >Hsmap) Hφ".
    (* The points-to of [sr] is not at MSHWMB, so the step does not write
       it. *)
    iAssert (|~{Ep}~> ⌜has_sreg_access pc_p = true → sr ≠ mshwmb⌝ ∗
                       [∗ map] k↦y ∈ sregs, k ↦ₓ y)%I
      with "[Hsmap]" as "Hsmap".
    { iApply (si_upd_ghost with "Hsmap"). iIntros (σ) "Hσ Hsmap".
      iDestruct (SI_open with "Hσ") as "Hσ". iNamed "Hσ".
      iDestruct (sys_interp_not_hwm_map with "Hsr Hsmap") as %Hnot.
      iModIntro. iSplitR "Hsmap".
      - iApply (SI_close _ _ _ _ _ _ _ Her with "HPCa Hr Hsr Hm Hst HR HC").
      - iFrame "Hsmap". iPureIntro. intros Hx. rewrite Hx /sregs_of in Dsregs.
        apply Hnot. set_solver. }
    iMod "Hsmap" as "[%Hnot_hwmb Hsmap]".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); first done.
    { intros Hx. rewrite Hinstr /writes_mshwmb.
      specialize (Hnot_hwmb Hx). destruct src; by rewrite bool_decide_false. }
    iNext; iIntros (r psr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_valid with "Hsr Hsmap") as %[Hlsregs Hdomsys].
    rewrite Hinstr /exec in Hstep. rewrite Hinstr.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. instr_fail Hstep.
      apply step_outcome_fault. by rewrite /specialrw_outcome Hxsr. }
    destruct (indom_sregs_incl _ _ _ Dsregs Hlsregs sr) as (vold & Hvold & Hvold');
      first (rewrite /sregs_of; set_solver).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvold') as (wold & Hwold & Hrelold).
    destruct (Hdomsys sr) as [Hsr_mtdc Hsr_mst]; first by eapply elem_of_dom_2.
    iAssert (⌜sr ≠ mshwm ∧ sr ≠ mshwmb⌝)%I as %[Hsr_hwm Hsr_hwmb].
    { iDestruct (big_sepM_lookup_acc with "Hsmap") as "[Hp _]"; first exact Hvold.
      iApply (sys_interp_not_hwm with "Hsr Hp"). }
    destruct (specialrw_sregs_phys R C _ r psr m st td _ lreg (ls_join lsreg) lmem regs sregs sr src
                vold Her Hlregs Hregs Hlsregs)
      as (sregs' & psr' & lsreg' & Hsregs' & Hφ1 & Her1 & Hup).
    { rewrite /regs_of /operands_of in Dregs. set_solver. } { done. }
    cbn in Hstep. rewrite Hxsr Hwold /= Hφ1 /= in Hstep.
    destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hi;
      cycle 1.
    { (* The PC increment fails: the state is unchanged. *)
      pose proof (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) as Hfail.
      rewrite /nextPC /advancePC /= in Hfail.
      destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; first done.
      assert (∀ φ', pcc φ' = Cap pc_p pc_g pc_b pc_e pc_a → nextPC φ' = None) as Hfail'.
      { intros φ' Hpc. by rewrite /nextPC /advancePC Hpc Hpca'. }
      rewrite Hfail' in Hstep; last by case_decide.
      instr_fail Hstep.
      apply step_outcome_fault. by apply specialrw_outcome_fail_pc. }
    (* The ghost system registers *)
    iAssert (|==> ∃ ls', ⌜ls_join ls' = lsreg'⌝ ∗ sys_interp ls' ∗
                         [∗ map] k↦y ∈ sregs', k ↦ₓ y)%I
      with "[Hsr Hsmap]" as ">(%ls' & %Hls' & Hsr & Hsmap)".
    { destruct Hup as [ [-> ->] | (nv & -> & ->)]; first by iFrame.
      iMod (sys_interp_update _ _ sr nv with "Hsr Hsmap") as "[Hsr Hsmap]"; first by eexists.
      iModIntro. iExists (ls_insert_sh lsreg sr nv). iFrame. iPureIntro.
      by rewrite ls_join_insert_sh. }
    rewrite -Hls' in Her1.
    pose proof (specialrw_sys_kept _ _ _ _ _ _ _ _ _ Hsr_mtdc Hsr_mst Hφ1) as Hkept.
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hvold') as Hokold.
    case_decide as Hdst.
    - (* The old value is dropped. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
      iApply (instr_close_kept_trans _ _ _ _ Hkept).
      iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
        (λ lpc' retv, step_outcome (specialrw_outcome regs sregs pc_p pc_g pc_b pc_e pc_a pc_π dst sr src)
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) (regs, sregs) lpc' (regs, sregs') retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hsmap]").
      { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
      { intros lpc'' Hi'. apply step_outcome_next.
        rewrite (specialrw_outcome_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hvold Hsregs' Hi').
        by rewrite /specialrw_regs decide_True. }
      { intros Hi'. rewrite /incrementPC in Hi. congruence. }
      iIntros (lpc'' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
    - (* [dst] receives the old value. *)
      destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _
        (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ _ dst vold wold Her1 Hokold Hrelold) Hi)
        as (pc' & Hu & _).
      iApply (instr_close_kept_trans _ _ _ _ Hkept).
      iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst vold wold _ _ _
        (λ lpc' regs' retv,
           step_outcome (specialrw_outcome regs sregs pc_p pc_g pc_b pc_e pc_a pc_π dst sr src)
             (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) (regs, sregs) lpc' (regs', sregs') retv)
        with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hsmap]").
      { exact Her1. } { exact Hlregs. }
      { right. apply Dregs. rewrite /regs_of /operands_of. set_solver. }
      { exact Hokold. }
      { rewrite /update_reg /= in Hu Hstep |- *. by rewrite Hu in Hstep |- *. }
      { exact Hrelold. }
      { intros lpc'' Hi'. apply step_outcome_next.
        rewrite (specialrw_outcome_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hvold Hsregs' Hi').
        by rewrite specialrw_regs_ne // linsert_reg_not_cnull. }
      { intros Hi'. congruence. }
      iIntros (lpc'' regs'' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (** The outcome of [SpecialRW] whose PC increment succeeds, whose PC has
      the system-register permission and whose operands are owned: the
      fault is absurd. *)
  Lemma specialrw_outcome_success_inv {k : kind} pc_p pc_g pc_b pc_e pc_a pc_π pc_a' regs sregs dst sr
      src lpc' regs' sregs' (retv : tval k) :
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    step_outcome (specialrw_outcome regs sregs pc_p pc_g pc_b pc_e pc_a pc_π dst sr src)
      (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) (regs, sregs) lpc' (regs', sregs') retv →
    is_Some (sregs !! sr) →
    regs_of_argument src ∖ {[ cnull ]} ⊆ dom regs →
    retv = NextIV ∧ lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
    ∃ vold, sregs !! sr = Some vold ∧
      specialrw_sregs regs sregs sr src = Some sregs' ∧
      regs' = specialrw_regs regs dst vold.
  Proof.
    intros Hxsr Hpca' Hspec [vold Hvold] Dsrc.
    assert (is_Some (specialrw_sregs regs sregs sr src)) as [sregs1 Hsregs1].
    { destruct src as [z|rs]; rewrite /specialrw_sregs /=; first by eexists.
      case_decide as Hrs; first by eexists.
      assert (is_Some (regs !!ₗ rs)) as [v Hv].
      { apply elem_of_dom_lreg, Dsrc. rewrite /regs_of_argument. set_solver. }
      rewrite Hv. by eexists. }
    rewrite (specialrw_outcome_some _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hvold Hsregs1
               (incrementPC_add _ _ _ _ _ _ _ _ Hpca')) in Hspec.
    destruct Hspec as (-> & -> & Hstate). injection Hstate as -> ->.
    split_and!; [done | done |]. exists vold. by split_and!.
  Qed.

  Lemma wp_readsr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst src (wsrc : Word) dq :
    decodeInstrW w.(lw) = SpecialRW dst src (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ₓ wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ lword_of_word wsrc
          ∗ src ↦ₓ wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hsrc") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    rewrite tval_sw_none; last by apply sw_of_none.
    destruct (specialrw_outcome_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec
                ltac:(eexists; apply lookup_singleton_eq)
                ltac:(rewrite /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver))
      as (-> & -> & vold & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; last done. simplify_map_eq.
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  Lemma wp_writesr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst src (wsrc : Word) dq :
    decodeInstrW w.(lw) = SpecialRW cnull dst (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ₓ wdst
        ∗ ▷ src ↦ᵣ lword_of_word wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ₓ legalise dst wsrc
          ∗ src ↦ᵣ lword_of_word wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hdst") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    rewrite tval_sw_none; last by apply sw_of_none.
    destruct (specialrw_outcome_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec
                ltac:(eexists; apply lookup_singleton_eq)
                ltac:(rewrite /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver))
      as (-> & -> & vold & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; first done.
    rewrite llookup_reg_not_cnull // in Hsr'.
    simplify_map_eq. rewrite insert_singleton_eq.
    rewrite specialrw_regs_cnull.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** [cspecialw mtcc, src] of an untagged word, with the unwedged token:
      the token goes to the state interpretation, which records mtcc as
      wedged. *)
  Lemma wp_writesr_mtcc_wedge E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (wsrc : Word) dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtcc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    get_tag (legalise mtcc wsrc) = false →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ lword_of_word wsrc ∗
        ▷ unwedged }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ lword_of_word wsrc ∗
          mtcc_wedged }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Htag φ) "(>HPC & >Hpc_a & >Hsrc & >HU) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; [done | solve_writes_mshwmb |].
    iNext; iIntros (r psr mm st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mtcc with "Hsr HU") as %Htcc.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Htcc) as (wold & Hwold & _).
    destruct (specialrw_sregs_phys R C _ r psr mm st td _ lreg (ls_join lsreg) lmem
                {[src := lword_of_word wsrc]} {[mtcc := lword_of_word mtcc_vec]} mtcc (inr src)
                (lword_of_word mtcc_vec) Her Hlregs Hregs)
      as (sregs' & psr' & lsreg' & Hsregs' & Hφ1 & Her1 & Hup).
    { by apply map_singleton_subseteq_l. }
    { rewrite /regs_of_argument dom_singleton_L. set_solver. }
    { by simplify_map_eq. }
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= Hφ1 /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    (* The new value of mtcc is the legalised source, untagged. *)
    rewrite /specialrw_sregs decide_False // llookup_reg_not_cnull // lookup_singleton /=
      decide_True //= in Hsregs'.
    injection Hsregs' as <-.
    destruct Hup as [ [Heq _] | (nv & Heq & ->)].
    { exfalso. apply (f_equal (λ m : LSReg, m !! mtcc)) in Heq.
      rewrite lookup_insert_eq lookup_singleton_eq in Heq. injection Heq as Heq.
      cbn in Htag. rewrite Heq mtcc_vec_tagged in Htag. done. }
    apply (f_equal (λ m : LSReg, m !! mtcc)) in Heq.
    rewrite !lookup_insert_eq in Heq. injection Heq as <-.
    (* The wedge: [SI_mtcc] is pending, since the unwedged token is here. *)
    iNamed "Hsr".
    iDestruct "Hmtcc" as "[ [Hmtcc Hpend] | (%w0 & _ & _ & HU' & _)]"; last first.
    { iDestruct (unwedged_excl with "HU HU'") as %[]. }
    iMod (mtcc_wedge_update (ls_sh lsreg) (llegalise mtcc (lword_of_word wsrc))
            with "[$Hsr $Hmtcc $Hpend $HU]") as "(Hsr & Hmtcc & #Hwedged)"; first done.
    iAssert (sys_interp (ls_insert_sh lsreg mtcc (llegalise mtcc (lword_of_word wsrc))))
      with "[Hsr Hmtcc Hmpie Hmtdc Hlent Hmie Hmshwmb_a Hmshwm_a Hpend_si Hlent_a Hzone]"
      as "Hsr".
    { iFrame. iSplit; first done. iSplit.
      - iPureIntro. destruct Hlsh as [Hn1 Hn2].
        rewrite /ls_insert_sh /= !lookup_insert_ne //.
      - iPureIntro. destruct Hlsh_hwm as [Hn3 Hn4].
        rewrite /ls_insert_sh /= !lookup_insert_ne //. }
    rewrite -ls_join_insert_sh // in Her1.
    pose proof (specialrw_sys_kept _ r psr mm st td psr' mtcc (inr src)
                  ltac:(done) ltac:(done) Hφ1) as Hkept.
    iApply (instr_close_kept_trans _ _ _ _ Hkept).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her1. }
    { destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1
                  (incrementPC_add _ _ _ _ _ _ _ _ Hpca')) as (pc' & Hu & _).
      rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
    { intros lpc' Hi.
      rewrite -/(incrementPC _) (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. by simplify_eq. }
    { intros Hi. by rewrite -/(incrementPC _) (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. }
    iIntros (lpc' retv (-> & ->)) "HPC Hmap".
    iApply "Hφ". iFrame "HPC Hpc_a Hwedged".
    iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** The swap of a register with a system register. *)
  Lemma wp_specialrw_swap E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r sr (v vold : LWord) dq :
    decodeInstrW w.(lw) = SpecialRW r sr (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r ↦ᵣ v
        ∗ ▷ sr ↦ₓ vold }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r ↦ᵣ vold
          ∗ sr ↦ₓ llegalise sr v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr & >Hsr) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hsr") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument dom_singleton_L. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    rewrite tval_sw_none; last by apply sw_of_none.
    destruct (specialrw_outcome_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec
                ltac:(eexists; apply lookup_singleton_eq)
                ltac:(rewrite /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver))
      as (-> & -> & vold' & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; first done.
    rewrite llookup_reg_not_cnull // in Hsr'.
    simplify_map_eq. rewrite insert_singleton_eq.
    rewrite specialrw_regs_ne // insert_singleton_eq.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_1 with "Hmap") as "$".
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** A swap between two different registers. *)
  Lemma wp_specialrw_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst sr src
      (v vold : LWord) dq :
    decodeInstrW w.(lw) = SpecialRW dst sr (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    src ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ᵣ v
        ∗ ▷ sr ↦ₓ vold }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ vold
          ∗ src ↦ᵣ v
          ∗ sr ↦ₓ llegalise sr v }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst Hsrc φ) "(>HPC & >Hpc_a & >Hdst & >Hsrc & >Hsr) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hne]".
    iDestruct (map_of_sregs_1 with "Hsr") as "Hsmap".
    iApply (wp_SpecialRW with "[$HPC $Hmap $Hsmap $Hpc_a]"); eauto.
    { rewrite /regs_of /operands_of /regs_of_argument !dom_insert_L. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    rewrite tval_sw_none; last by apply sw_of_none.
    destruct (specialrw_outcome_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec
                ltac:(eexists; apply lookup_singleton_eq)
                ltac:(rewrite /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver))
      as (-> & -> & vold' & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs /= in Hsr'. case_decide as Hc; first done.
    rewrite llookup_reg_not_cnull // in Hsr'.
    simplify_map_eq. rewrite insert_singleton_eq.
    rewrite specialrw_regs_ne // insert_insert_eq.
    iApply "Hφ". iFrame.
    iDestruct (regs_of_map_2 with "Hmap") as "[$ $]"; first done.
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** The write of an immediate, as [csrw sr, z]. *)
  Lemma wp_specialrw_imm_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w sr (z : Z) vold dq :
    decodeInstrW w.(lw) = SpecialRW cnull sr (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    SpecialRW cnull sr (inl z) ≠ exit_marker →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ sr ↦ₓ vold }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ sr ↦ₓ legalise sr (WInt z) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hexit φ) "(>HPC & >Hpc_a & >Hsr) Hφ".
    iDestruct (map_of_sregs_1 with "Hsr") as "Hsmap".
    iApply (wp_SpecialRW _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$HPC $Hsmap $Hpc_a]"); eauto.
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & Hmap & Hsmap)".
    rewrite tval_sw_none; last by apply sw_of_none.
    destruct (specialrw_outcome_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec
                ltac:(eexists; apply lookup_singleton_eq)
                ltac:(rewrite /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver))
      as (-> & -> & vold' & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs in Hsr'. simplify_map_eq. rewrite insert_singleton_eq.
    iApply "Hφ". iFrame.
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** The exit marker of a user thread, [csrw mcause, MCAUSE_THREAD_EXIT]:
      mcause is written and the thread's turn ends in [ExitV], through the
      sequencing context. *)
  Lemma wp_exit_marker E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (vold : LWord) dq
      (Φ : tval (kind_of th) → iProp Σ) :
    th ≠ CtxSwitch →
    decodeInstrW w.(lw) = exit_marker →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π -∗
    ▷ pc_a ↦ₐ{dq} w -∗
    ▷ mcause ↦ₓ vold -∗
    ▷ (PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π -∗
       pc_a ↦ₐ{dq} w -∗
       mcause ↦ₓ lword_of_word (WInt MCAUSE_THREAD_EXIT) -∗
       Φ ExitV) -∗
    WP Exec @ E {{ Φ }}.
  Proof.
    iIntros (Hth Hinstr Hvpc Hxsr Hpca') "HPC Hpc_a Hsr Hφ".
    iApply (wp_bind (@fill (tlang_ectx _) [SeqCtx])).
    iApply (wp_SpecialRW _ _ _ _ _ _ _ _ cnull mcause (inl MCAUSE_THREAD_EXIT) ∅
              {[mcause := vold]} with "[HPC Hpc_a Hsr]"); [exact Hinstr | done | | | |].
    { rewrite /regs_of /operands_of /regs_of_argument. set_solver. }
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    { iFrame "HPC Hpc_a". iSplitR; first by rewrite big_sepM_empty.
      iNext. iApply (map_of_sregs_1 with "Hsr"). }
    iNext. iIntros (lpc' regs' sregs' retv) "(%Hspec & HPC & Hpc_a & _ & Hsmap)".
    destruct (specialrw_outcome_success_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec
                ltac:(eexists; apply lookup_singleton_eq)
                ltac:(rewrite /regs_of_argument ?dom_insert_L ?dom_singleton_L; set_solver))
      as (-> & -> & vold' & Hvold & Hsr' & ->).
    rewrite /specialrw_sregs in Hsr'. simplify_map_eq. rewrite insert_singleton_eq.
    assert (sw_of (kind_of th) (SpecialRW cnull mcause (inl MCAUSE_THREAD_EXIT)) = Some ExitS)
      as ->.
    { destruct th; [done | by destruct Hth]. }
    iApply wp_pure_step_later; first done. iIntros "!> _".
    iApply wp_value. iApply ("Hφ" with "HPC Hpc_a").
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

  (** *** mtdc

      mtdc is a per-thread register with its own ghost state: the fragment
      [mtdc ↦ₜ m] of the thread holds a ghost value [m] that stands for the
      logical word of mtdc ([mtdc_match]). A read gives a word that [m]
      stands for; a write relabels the ghost value with any [m'] that stands
      for the written word, and has a link-transfer premise. *)

  (** [cspecialr dst, mtdc]. *)
  Lemma wp_readsr_mtdc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst m dq :
    decodeInstrW w.(lw) = SpecialRW dst mtdc (inr cnull) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wdst ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          dst ↦ᵣ vm ∗
          mtdc ↦ₜ m }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hdst φ) "(>HPC & >Hpc_a & >Hdst & >Hmtdc_f) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; [done | solve_writes_mshwmb |].
    iNext; iIntros (r psr mm st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mtdc_agree with "Hsr Hmtdc_f") as %[Hmeq Hmatch].
    pose proof (ls_join_mtdc lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & Hrel).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    destruct (decide (dst = cnull)) as [Hc|_]; first done. cbn in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ dst (ls_vmtdc lsreg) wold _ _ _
      (λ lpc' regs' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
                          regs' = <[dst := ls_vmtdc lsreg]ₗ> {[dst := wdst]} ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmtdc_f]").
    { exact Her. } { exact Hlregs. } { right. set_solver. } { exact Hok. } { exact Hstep. }
    { exact Hrel. }
    { intros lpc' Hi. rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. by simplify_eq. }
    { intros Hi. by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. }
    iIntros (lpc' regs' retv (-> & -> & ->)) "HPC Hmap".
    rewrite linsert_reg_not_cnull // insert_singleton_eq.
    iApply "Hφ". iFrame. iDestruct (regs_of_map_1 with "Hmap") as "$".
    iPureIntro. done.
  Qed.

  (** [cspecialw mtdc, src]: the ghost value becomes any [m'] that stands
      for the written word. The clause of the mtdc token is transferred
      with [L1] for [L2]. *)
  Lemma wp_writesr_mtdc_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m m' dq
      (T1 T2 L1 L2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    mtdc_match m' v →
    link_transfer mtdc_written T1 T2 →
    (mtdc_clause m ∗ L1 ⊢ |==> mtdc_clause m' ∗ L2) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ T1 ∗
        ▷ L1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ m' ∗
          T2 ∗
          L2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hm' Htr Hcl φ)
      "(>HPC & >Hpc_a & >Hsrc & >Hmtdc_f & HT & HL) Hφ".
    iDestruct (map_of_regs_1 with "Hsrc") as "Hmap".
    iApply (wp_instr_step_link_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; [done | solve_writes_mshwmb |].
    iNext; iIntros (r psr mm st td lreg lsreg lmem R C c σ') "@".
    pose proof (ls_join_mtdc lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & _).
    assert ({[src := v]} !!ₗ src = Some v) as Hsv.
    { rewrite llookup_reg_not_cnull // lookup_singleton_eq //. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hsv) as (s & Hrs & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs Hsv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (src = cnull)) as [Hc|_]; first done.
    rewrite Hrs /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    pose proof (erasure_write_sreg _ _ _ _ _ _ _ _ _ _ _ _ mtdc v (and_tag s (lw v)) Her Hok Hrel)
      as Her1.
    rewrite llegalise_mtdc -(ls_join_set_mtdc lsreg m' v) in Her1. cbn [legalise] in Her1, Hstep.
    iMod (sys_interp_set_mtdc _ m m' v _ _ Hm' Hcl with "Hsr Hmtdc_f HL")
      as "(Hsr & Hmtdc_f & HL)".
    iApply (instr_close_link_transfer_irq _ _ _ _
              (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r (<[mtdc := and_tag s (lw v)]> psr) mm st td)
              with "Hlink HT"); [by apply link_transfer_si_of | | |].
    { intros Hk. eapply mtdc_written_kept; last exact Hk.
      by rewrite /mtdc_written /mie_st /= lookup_insert_ne. }
    { intros [Hk _]. rewrite Hk /mie_st /= lookup_insert_ne //. exact (ctx_irq_off_route _ _ Hoff). }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1
                (incrementPC_add _ _ _ _ _ _ _ _ Hpca')) as (pc' & Hu & _).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmtdc_f HL]").
    { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
    { intros lpc' Hi. rewrite /incrementPC_gen /= Hpca' in Hi. by simplify_eq. }
    { intros Hi. by rewrite /incrementPC_gen /= Hpca' in Hi. }
    iIntros (lpc' retv [-> ->]) "HPC Hmap HT".
    iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap").
  Qed.

  (** [cspecialrw r, mtdc, r]: the swap of a register with mtdc; [r]
      receives a word that [m] stands for, and the ghost value becomes any
      [m'] that stands for the word written. *)
  Lemma wp_specialrw_swap_mtdc_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord) m m' dq
      (T1 T2 L1 L2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    mtdc_match m' v →
    link_transfer mtdc_written T1 T2 →
    (mtdc_clause m ∗ L1 ⊢ |==> mtdc_clause m' ∗ L2) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ T1 ∗
        ▷ L1 }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ m' ∗
          T2 ∗
          L2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hm' Htr Hcl φ)
      "(>HPC & >Hpc_a & >Hr & >Hmtdc_f & HT & HL) Hφ".
    iDestruct (map_of_regs_1 with "Hr") as "Hmap".
    iApply (wp_instr_step_link_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|..]; [done | solve_writes_mshwmb |].
    iNext; iIntros (rf psr mm st td lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mtdc_agree with "Hsr Hmtdc_f") as %[Hmeq Hmatch].
    pose proof (ls_join_mtdc lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & Hrelold).
    pose proof (er_sreg_words _ _ _ _ _ _ _ Her _ _ Hv) as Hokold.
    assert ({[r := v]} !!ₗ r = Some v) as Hsv.
    { rewrite llookup_reg_not_cnull // lookup_singleton_eq //. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hsv) as (s & Hrs & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs Hsv) as Hok.
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (r = cnull)) as [Hc|_]; first done.
    rewrite Hrs /= in Hstep.
    pose proof (erasure_write_sreg _ _ _ _ _ _ _ _ _ _ _ _ mtdc v (and_tag s (lw v)) Her Hok Hrel)
      as Her1.
    rewrite llegalise_mtdc -(ls_join_set_mtdc lsreg m' v) in Her1. cbn [legalise] in Her1, Hstep.
    iMod (sys_interp_set_mtdc _ m m' v _ _ Hm' Hcl with "Hsr Hmtdc_f HL")
      as "(Hsr & Hmtdc_f & HL)".
    iApply (instr_close_link_transfer_irq _ _ _ _
              (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) rf (<[mtdc := and_tag s (lw v)]> psr) mm st td)
              with "Hlink HT"); [by apply link_transfer_si_of | | |].
    { intros Hk. eapply mtdc_written_kept; last exact Hk.
      by rewrite /mtdc_written /mie_st /= lookup_insert_ne. }
    { intros [Hk _]. rewrite Hk /mie_st /= lookup_insert_ne //. exact (ctx_irq_off_route _ _ Hoff). }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ r (ls_vmtdc lsreg) wold _ _ _
      (λ lpc' regs' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
                          regs' = <[r := ls_vmtdc lsreg]ₗ> {[r := v]} ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmtdc_f HL]").
    { exact Her1. } { exact Hlregs. } { right. set_solver. } { exact Hokold. }
    { destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _
        (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ _ r (ls_vmtdc lsreg) wold Her1 Hokold Hrelold)
        (incrementPC_add _ _ _ _ _ _ _ _ Hpca')) as (pc' & Hu & _).
      rewrite /update_reg /= in Hu Hstep |- *. by rewrite Hu in Hstep |- *. }
    { exact Hrelold. }
    { intros lpc' Hi. rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. by simplify_eq. }
    { intros Hi. by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. }
    iIntros (lpc' regs' retv (-> & -> & ->)) "HPC Hmap HT".
    rewrite linsert_reg_not_cnull // insert_singleton_eq.
    iApply "Hφ". iFrame. iDestruct (regs_of_map_1 with "Hmap") as "$".
    iPureIntro. done.
  Qed.

  (** [cspecialw mtdc, z]: the write of an immediate. *)
  Lemma wp_specialrw_imm_mtdc_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (z : Z) m m' dq
      (T1 T2 L1 L2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    mtdc_match m' (lword_of_word (WInt z)) →
    link_transfer mtdc_written T1 T2 →
    (mtdc_clause m ∗ L1 ⊢ |==> mtdc_clause m' ∗ L2) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ T1 ∗
        ▷ L1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          mtdc ↦ₜ m' ∗
          T2 ∗
          L2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hm' Htr Hcl φ) "(>HPC & >Hpc_a & >Hmtdc_f & HT & HL) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link_nosw E pc_p pc_g pc_b pc_e pc_a pc_π w dq ∅ with "HPC Hpc_a Hmap0"); [rewrite Hinstr; by apply sw_of_none|..]; [done | solve_writes_mshwmb |].
    iNext; iIntros (r psr mm st td lreg lsreg lmem R C c σ') "@".
    pose proof (ls_join_mtdc lsreg) as Hv.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hv) as (wold & Hwold & _).
    rewrite Hinstr /exec in Hstep. cbn in Hstep. rewrite Hxsr Hwold /= in Hstep.
    destruct (decide (cnull = cnull)) as [_|Hc]; last done.
    pose proof (erasure_write_sreg _ _ _ _ _ _ _ _ _ _ _ _ mtdc (lword_of_word (WInt z)) (WInt z)
                  Her (reg_word_ok_int _ _ _ _) (reg_phys_lword_of_word _ _)) as Her1.
    rewrite llegalise_mtdc -(ls_join_set_mtdc lsreg m' (lword_of_word (WInt z))) in Her1.
    cbn [legalise] in Her1, Hstep.
    iMod (sys_interp_set_mtdc _ m m' _ _ _ Hm' Hcl with "Hsr Hmtdc_f HL")
      as "(Hsr & Hmtdc_f & HL)".
    iApply (instr_close_link_transfer_irq _ _ _ _
              (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r (<[mtdc := WInt z]> psr) mm st td)
              with "Hlink HT"); [by apply link_transfer_si_of | | |].
    { intros Hk. eapply mtdc_written_kept; last exact Hk.
      by rewrite /mtdc_written /mie_st /= lookup_insert_ne. }
    { intros [Hk _]. rewrite Hk /mie_st /= lookup_insert_ne //. exact (ctx_irq_off_route _ _ Hoff). }
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ _ Her1
                (incrementPC_add _ _ _ _ _ _ _ _ Hpca')) as (pc' & Hu & _).
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, lpc' = Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧ retv = NextIV)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hmtdc_f HL]").
    { exact Her1. } { rewrite /nextPC in Hu Hstep. by rewrite Hu in Hstep |- *. }
    { intros lpc' Hi. rewrite /incrementPC_gen /= Hpca' in Hi. by simplify_eq. }
    { intros Hi. by rewrite /incrementPC_gen /= Hpca' in Hi. }
    iIntros (lpc' retv [-> ->]) "HPC Hmap HT".
    iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules.

(** The core corollaries of the mtdc writers: at the core link, the link
    premise holds with [True]; the transfer of the clause of the mtdc token
    stays. *)
Section griotte_lang_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread}.
  Implicit Types w : LWord.

  Lemma wp_writesr_mtdc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m m' dq
      (L1 L2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    mtdc_match m' v →
    (mtdc_clause m ∗ L1 ⊢ |==> mtdc_clause m' ∗ L2) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ L1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ m' ∗
          L2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hm' Hcl φ) "(>HPC & >Hpc_a & >Hsrc & >Hmtdc_f & HL) Hφ".
    iApply (wp_writesr_mtdc_link _ _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I L1 L2
             with "[$HPC $Hpc_a $Hsrc $Hmtdc_f $HL]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros "(HPC & Hpc_a & Hsrc & Hmtdc_f & _ & HL)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_specialrw_swap_mtdc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord) m m' dq
      (L1 L2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    mtdc_match m' v →
    (mtdc_clause m ∗ L1 ⊢ |==> mtdc_clause m' ∗ L2) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ L1 }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ m' ∗
          L2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hm' Hcl φ) "(>HPC & >Hpc_a & >Hr & >Hmtdc_f & HL) Hφ".
    iApply (wp_specialrw_swap_mtdc_link _ _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I L1 L2
             with "[$HPC $Hpc_a $Hr $Hmtdc_f $HL]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros (vm) "(Hmatch & HPC & Hpc_a & Hr & Hmtdc_f & _ & HL)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_specialrw_imm_mtdc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (z : Z) m m' dq
      (L1 L2 : iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    mtdc_match m' (lword_of_word (WInt z)) →
    (mtdc_clause m ∗ L1 ⊢ |==> mtdc_clause m' ∗ L2) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ L1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          mtdc ↦ₜ m' ∗
          L2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hm' Hcl φ) "(>HPC & >Hpc_a & >Hmtdc_f & HL) Hφ".
    iApply (wp_specialrw_imm_mtdc_link _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I L1 L2
             with "[$HPC $Hpc_a $Hmtdc_f $HL]").
    all: try done.
    { apply link_transfer_core. }
    iNext. iIntros "(HPC & Hpc_a & Hmtdc_f & _ & HL)". iApply "Hφ". iFrame.
  Qed.

  (** The core rules of the mtdc writers for each transfer of the clause of
      the mtdc token ([mtdc_clause_keep], [_close], [_open], [_ex]): they have
      no clause premise, so that [iInstr] can apply them. *)

  (** The core rule with the ghost value kept. *)
  Lemma wp_writesr_mtdc_keep E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    mtdc_match m v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ m }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hm' φ) "(HPC & Hpc_a & Hsrc & Hmtdc) Hφ".
    pose proof (mtdc_clause_keep m) as Hcl.
    iApply (wp_writesr_mtdc _ _ _ _ _ _ _ _ _ _ _ _ m _ True%I True%I
             with "[$HPC $Hpc_a $Hsrc $Hmtdc]"); try done.
    iIntros "!> (HPC & Hpc_a & Hsrc & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  (** The core rule back to the home value: the token returns. *)
  Lemma wp_writesr_mtdc_close E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    m ≠ mtdc_home →
    mtdc_match mtdc_home v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ mtdc_home ∗
          mtdc_lent }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hne Hm' φ) "(HPC & Hpc_a & Hsrc & Hmtdc) Hφ".
    pose proof (mtdc_clause_close m Hne) as Hcl.
    iApply (wp_writesr_mtdc _ _ _ _ _ _ _ _ _ _ _ _ mtdc_home _ True%I mtdc_lent
             with "[$HPC $Hpc_a $Hsrc $Hmtdc]"); done.
  Qed.

  (** The core rule leaving the home value: the token is lent. *)
  Lemma wp_writesr_mtdc_open E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m m' dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    m = mtdc_home →
    mtdc_match m' v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ mtdc_lent }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hhome Hm' φ) "(HPC & Hpc_a & Hsrc & Hmtdc & HL) Hφ".
    subst m. pose proof (mtdc_clause_open m') as Hcl.
    iApply (wp_writesr_mtdc _ _ _ _ _ _ _ _ _ _ _ _ m' _ mtdc_lent True%I
             with "[$HPC $Hpc_a $Hsrc $Hmtdc $HL]"); try done.
    iIntros "!> (HPC & Hpc_a & Hsrc & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  (** The core rule between values other than the home value. *)
  Lemma wp_writesr_mtdc_ex E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m m' dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    m ≠ mtdc_home →
    mtdc_match m' v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ src ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          src ↦ᵣ v ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hne Hm' φ) "(HPC & Hpc_a & Hsrc & Hmtdc) Hφ".
    pose proof (mtdc_clause_ex m m' Hne) as Hcl.
    iApply (wp_writesr_mtdc _ _ _ _ _ _ _ _ _ _ _ _ m' _ True%I True%I
             with "[$HPC $Hpc_a $Hsrc $Hmtdc]"); try done.
    iIntros "!> (HPC & Hpc_a & Hsrc & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  (** The core rule with the ghost value kept. *)
  Lemma wp_specialrw_swap_mtdc_keep E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord) m dq :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    mtdc_match m v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ m }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hm' φ) "(HPC & Hpc_a & Hr & Hmtdc) Hφ".
    pose proof (mtdc_clause_keep m) as Hcl.
    iApply (wp_specialrw_swap_mtdc _ _ _ _ _ _ _ _ _ _ _ _ m _ True%I True%I
             with "[$HPC $Hpc_a $Hr $Hmtdc]"); try done.
    iIntros "!>" (vm) "(Hm & HPC & Hpc_a & Hr & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  (** The core rule back to the home value: the token returns. *)
  Lemma wp_specialrw_swap_mtdc_close E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord) m dq :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    m ≠ mtdc_home →
    mtdc_match mtdc_home v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ mtdc_home ∗
          mtdc_lent }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hne Hm' φ) "(HPC & Hpc_a & Hr & Hmtdc) Hφ".
    pose proof (mtdc_clause_close m Hne) as Hcl.
    iApply (wp_specialrw_swap_mtdc _ _ _ _ _ _ _ _ _ _ _ _ mtdc_home _ True%I mtdc_lent
             with "[$HPC $Hpc_a $Hr $Hmtdc]"); done.
  Qed.

  (** The core rule leaving the home value: the token is lent. *)
  Lemma wp_specialrw_swap_mtdc_open E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord) m m' dq :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    m = mtdc_home →
    mtdc_match m' v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ mtdc_lent }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hhome Hm' φ) "(HPC & Hpc_a & Hr & Hmtdc & HL) Hφ".
    subst m. pose proof (mtdc_clause_open m') as Hcl.
    iApply (wp_specialrw_swap_mtdc _ _ _ _ _ _ _ _ _ _ _ _ m' _ mtdc_lent True%I
             with "[$HPC $Hpc_a $Hr $Hmtdc $HL]"); try done.
    iIntros "!>" (vm) "(Hm & HPC & Hpc_a & Hr & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  (** The core rule between values other than the home value. *)
  Lemma wp_specialrw_swap_mtdc_ex E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r (v : LWord) m m' dq :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    m ≠ mtdc_home →
    mtdc_match m' v →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r ↦ᵣ v ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ vm, RET NextIV;
          ⌜mtdc_match m vm⌝ ∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          r ↦ᵣ vm ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hne Hm' φ) "(HPC & Hpc_a & Hr & Hmtdc) Hφ".
    pose proof (mtdc_clause_ex m m' Hne) as Hcl.
    iApply (wp_specialrw_swap_mtdc _ _ _ _ _ _ _ _ _ _ _ _ m' _ True%I True%I
             with "[$HPC $Hpc_a $Hr $Hmtdc]"); try done.
    iIntros "!>" (vm) "(Hm & HPC & Hpc_a & Hr & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  (** The core rule with the ghost value kept. *)
  Lemma wp_specialrw_imm_mtdc_keep E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (z : Z) m dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    mtdc_match m (lword_of_word (WInt z)) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          mtdc ↦ₜ m }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hm' φ) "(HPC & Hpc_a & Hmtdc) Hφ".
    pose proof (mtdc_clause_keep m) as Hcl.
    iApply (wp_specialrw_imm_mtdc _ _ _ _ _ _ _ _ _ _ _ m _ True%I True%I
             with "[$HPC $Hpc_a $Hmtdc]"); try done.
    iIntros "!> (HPC & Hpc_a & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  (** The core rule back to the home value: the token returns. *)
  Lemma wp_specialrw_imm_mtdc_close E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (z : Z) m dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    m ≠ mtdc_home →
    mtdc_match mtdc_home (lword_of_word (WInt z)) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          mtdc ↦ₜ mtdc_home ∗
          mtdc_lent }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hne Hm' φ) "(HPC & Hpc_a & Hmtdc) Hφ".
    pose proof (mtdc_clause_close m Hne) as Hcl.
    iApply (wp_specialrw_imm_mtdc _ _ _ _ _ _ _ _ _ _ _ mtdc_home _ True%I mtdc_lent
             with "[$HPC $Hpc_a $Hmtdc]"); done.
  Qed.

  (** The core rule leaving the home value: the token is lent. *)
  Lemma wp_specialrw_imm_mtdc_open E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (z : Z) m m' dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    m = mtdc_home →
    mtdc_match m' (lword_of_word (WInt z)) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mtdc ↦ₜ m ∗
        ▷ mtdc_lent }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hhome Hm' φ) "(HPC & Hpc_a & Hmtdc & HL) Hφ".
    subst m. pose proof (mtdc_clause_open m') as Hcl.
    iApply (wp_specialrw_imm_mtdc _ _ _ _ _ _ _ _ _ _ _ m' _ mtdc_lent True%I
             with "[$HPC $Hpc_a $Hmtdc $HL]"); try done.
    iIntros "!> (HPC & Hpc_a & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

  (** The core rule between values other than the home value. *)
  Lemma wp_specialrw_imm_mtdc_ex E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w (z : Z) m m' dq :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inl z) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    m ≠ mtdc_home →
    mtdc_match m' (lword_of_word (WInt z)) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mtdc ↦ₜ m }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          pc_a ↦ₐ{dq} w ∗
          mtdc ↦ₜ m' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hne Hm' φ) "(HPC & Hpc_a & Hmtdc) Hφ".
    pose proof (mtdc_clause_ex m m' Hne) as Hcl.
    iApply (wp_specialrw_imm_mtdc _ _ _ _ _ _ _ _ _ _ _ m' _ True%I True%I
             with "[$HPC $Hpc_a $Hmtdc]"); try done.
    iIntros "!> (HPC & Hpc_a & Hmtdc & _)". iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules_core.
