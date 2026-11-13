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

  (** mstatus after [Mret] on the value [vst]: MIE receives MPIE, and MPIE
      becomes enabled. *)
  Definition mret_mstatus (vst : LWord) : LWord :=
    WInt (mstatus_enc (mpie_of (get_a vst.(lw))) InterruptEnabled).

  (** The PC after [mret]: the value of MEPCC in [sregs], given the
      permission to access the system registers. mstatus is held by the
      state interpretation: the summary does not expose it. *)
  Definition mret_next (pc_p : Perm) (sregs : LSReg) : option LWord :=
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
        ⌜ step_outcome ((., tt) <$> mret_next pc_p sregs)
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
      - iPureIntro. apply step_outcome_fault. by rewrite /mret_next Hxsr.
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
    - iPureIntro. apply step_outcome_next. by rewrite /mret_next Hxsr Hvepcc.
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
    rewrite /mret_next Hxsr lookup_singleton_eq in Hspec.
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

  (** Without the permission to access the system registers, [mret] faults
      before it reads MEPCC and mstatus: the rule needs no MIE or MPIE
      fragment. *)
  Lemma wp_mret_fail E pc_p pc_g pc_b pc_e pc_a pc_π w dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = false →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
      {{{ RET FaultedV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
          pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr φ) "H Hφ".
    iApply (wp_instr_faulted_0 with "H Hφ"); [exact Hinstr | exact Hvpc |].
    intros r sr m st td. by rewrite /exec /= Hxsr.
  Qed.

End griotte_lang_rules.

(** The core corollaries, with today's statements. *)
Section griotte_lang_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread}.
  Implicit Types w : LWord.

  Lemma wp_Mret Ep pc_p pc_g pc_b pc_e pc_a pc_π w sregs (b p : InterruptStatus) dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (if has_sreg_access pc_p
     then sregs_of Mret ⊆ dom sregs
     else True) →
    (route_pre th b → route_pre th p) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET tval_sw (kind_of th) Mret retv;
        ⌜ step_outcome ((., tt) <$> mret_next pc_p sregs)
            (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) tt lpc' tt retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗
        (⌜retv = NextIV⌝ ∗ MIE ↦ₜ p ∗ MPIE_frag InterruptEnabled ∨
         ⌜retv = FaultedV⌝ ∗ MIE ↦ₜ b ∗ MPIE_frag p)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dsregs Hroute φ) "(>HPC & >Hpc_a & >Hsmap & >Hmie & >Hmpie) Hφ".
    iApply (wp_Mret_link _ _ _ _ _ _ _ _ _ _ _ _ True%I
              (([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗ MPIE_frag InterruptEnabled ∗ True)%I
             with "[$HPC $Hpc_a $Hsmap $Hmie $Hmpie]");
      [done | done | done | apply link_transfer_si_core | done | done |].
    iNext. iIntros (lpc' retv) "(Hspec & HPC & Hpc_a & HT)". iApply "Hφ". iFrame "Hspec HPC Hpc_a".
    iDestruct "HT" as "[ (-> & Hmie & Hsmap & Hmpie & _) | (-> & Hsmap & Hmie & Hmpie & _) ]".
    - iFrame "Hsmap". iLeft. by iFrame.
    - iFrame "Hsmap". iRight. by iFrame.
  Qed.

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
      first done.
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
