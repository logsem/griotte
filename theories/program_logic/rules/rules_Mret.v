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
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types sreg : gmap SRegName LWord.

  (** mstatus after [Mret] on the value [vst]: MIE receives MPIE, and MPIE
      becomes enabled. *)
  Definition mret_mstatus (vst : LWord) : LWord :=
    WInt (mstatus_enc (mpie_of (get_a vst.(lw))) InterruptEnabled).

  Inductive Mret_failure (lpc : LWord) : Prop :=
  | Mret_fail_nonxsr p g b e a π :
      lpc = Cap p g b e a @@? π →
      has_sreg_access p = false →
      Mret_failure lpc.

  (** On success, the new PC is the value of MEPCC. mstatus is held by the
      state interpretation: the rule does not expose it. *)
  Inductive Mret_spec (lpc : LWord) (sregs : LSReg) (lpc' : LWord)
    : griotte_lang.val → Prop :=
  | Mret_spec_success p g b e a π :
      lpc = Cap p g b e a @@? π →
      has_sreg_access p = true →
      sregs !! mepcc = Some lpc' →
      Mret_spec lpc sregs lpc' NextIV
  | Mret_spec_failure :
      lpc' = lpc →
      Mret_failure lpc →
      Mret_spec lpc sregs lpc' FaultedV.

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
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p ∗
        ▷ T1
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ Mret_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) sregs lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        (⌜retv = NextIV⌝ ∗ MIE ↦ₜ p ∗ T2 ∨
         ⌜retv = FaultedV⌝ ∗ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗ MIE ↦ₜ b ∗ MPIE_frag p ∗ T1)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dsregs Htr φ) "(>HPC & >Hpc_a & >Hsmap & >Hmie & >Hmpie & HT) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link _ _ _ _ _ _ _ _ _ _ ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mie_agree with "Hsr Hmie") as %<-.
    iDestruct (sys_interp_mpie_agree with "Hsr Hmpie") as %<-.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    iDestruct (sys_interp_valid with "Hsr Hsmap") as %[Hlsregs _].
    pose proof (ls_join_mstatus lsreg) as Hvst'.
    rewrite Hinstr /exec in Hstep.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. simplify_eq.
      iApply (instr_close_link_kept with "Hlink").
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
      iIntros "HPC _". iApply "Hφ". iFrame "HPC Hpc_a". iSplit.
      - iPureIntro. apply Mret_spec_failure; first done. by eapply Mret_fail_nonxsr.
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
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ mstatus
      (lword_of_word (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)))
      (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    rewrite -ls_join_set_mstatus in Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ vepcc wepcc Her1) as Her2.
    specialize (Her2 ltac:(by eapply (er_sreg_words _ _ _ _ _ _ _ Her)) Hrelepcc
                  ltac:(by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her mepcc))).
    iMod (sys_interp_set_mstatus _ _ _ (ls_mpie lsreg) InterruptEnabled
           with "Hsr Hmie Hmpie") as "(Hsr & Hmie & Hmpie)".
    iMod (PC_update _ _ vepcc with "HPCa HPC") as "[HPCa HPC]".
    iPoseProof (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC") as "HSI".
    iMod (Htr _ (wepcc, r,
                 <[mstatus := WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)]> psr, m, st)
           with "[$HSI $Hlink $Hsmap $Hmpie $HT]") as "(HSI & Hlink & HT)".
    { split_and!.
      - done.
      - by rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc.
      - by rewrite /= lookup_insert_ne. }
    iModIntro. iFrame "HSI Hlink". iApply "Hφ". iFrame "HPC Hpc_a". iSplit.
    - iPureIntro. by eapply Mret_spec_success.
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

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mepcc ↦ₓ vepcc ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p ∗
        ▷ T1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ vepcc ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ p ∗
          T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Htr φ) "(>HPC & >Hpc_a & >Hepcc & >Hmie & >Hmpie & HT) Hφ".
    iDestruct (map_of_sregs_1 with "Hepcc") as "Hsmap".
    iApply (wp_Mret_link with "[$HPC $Hsmap $Hpc_a $Hmie $Hmpie $HT]"); eauto.
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    { eapply link_transfer_si_weaken; last exact Htr; last done.
      iIntros "(Hsmap & $ & $)". iApply (sregs_of_map_1 with "Hsmap"). }
    iNext. iIntros (lpc' retv) "(%Hspec & HPC & Hpc_a & HT)".
    destruct Hspec as [p' g b' e a π Hpc Hx Hvepcc | -> [p' g b' e a π Hpc Hx] ];
      simplify_eq; last by rewrite Hxsr in Hx.
    simplify_map_eq.
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

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ MIE ↦ₜ InterruptDisabled ∗
        posture_res{p, vepcc} }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ vepcc ∗
          pc_a ↦ₐ{dq} w ∗
          MIE ↦ₜ p ∗
          held p }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr φ) "(>HPC & >Hpc_a & >Hmie & Hpost) Hφ".
    rewrite posture_res_gen_unfold.
    iDestruct "Hpost" as "[(%p' & %c & %v & %b' & %Hpb & %Hpp & _ & _ & Hcrit & HU & Hepcc & Hmcause
                            & Hmtval & Hmpie) Hpart]".
    cbn in Hpb, Hpp. subst b' p'.
    iApply (wp_mret_success_link _ _ _ _ _ _ _ _ _ _ _ _
              (na_own crit ⊤ ∗ unwedged ∗ mcause ↦ₓ c ∗ mtval ↦ₓ lword_of_word (WInt v) ∗
               @posture_part _ _ _ th CL CR)%I (held p)
             with "[$HPC $Hpc_a $Hepcc $Hmie $Hmpie $Hcrit $HU $Hmcause $Hmtval $Hpart]");
      [done | done | done | |].
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
    intros r sr m st. by rewrite /exec /= Hxsr.
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
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ Mret_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) sregs lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗
        (⌜retv = NextIV⌝ ∗ MIE ↦ₜ p ∗ MPIE_frag InterruptEnabled ∨
         ⌜retv = FaultedV⌝ ∗ MIE ↦ₜ b ∗ MPIE_frag p)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dsregs φ) "(>HPC & >Hpc_a & >Hsmap & >Hmie & >Hmpie) Hφ".
    iApply (wp_Mret_link _ _ _ _ _ _ _ _ _ _ _ _ True%I
              (([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗ MPIE_frag InterruptEnabled ∗ True)%I
             with "[$HPC $Hpc_a $Hsmap $Hmie $Hmpie]");
      [done | done | done | apply link_transfer_si_core | done |].
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

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ mepcc ↦ₓ vepcc ∗
        ▷ MIE ↦ₜ b ∗
        ▷ MPIE_frag p }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ vepcc ∗
          pc_a ↦ₐ{dq} w ∗
          mepcc ↦ₓ vepcc ∗
          MIE ↦ₜ p ∗
          MPIE_frag InterruptEnabled }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr φ) "(>HPC & >Hpc_a & >Hepcc & >Hmie & >Hmpie) Hφ".
    iApply (wp_mret_success_link _ _ _ _ _ _ _ _ _ _ _ _ True%I
              (mepcc ↦ₓ vepcc ∗ MPIE_frag InterruptEnabled ∗ True)%I
             with "[$HPC $Hpc_a $Hepcc $Hmie $Hmpie]");
      [done..| apply link_transfer_si_core | done |].
    iNext. iIntros "(HPC & Hpc_a & Hmie & Hepcc & Hmpie & _)". iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules_core.
