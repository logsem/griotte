From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {CL : CritLink Σ}.
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
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = false →
      Mret_failure lpc.

  (** On success, the new PC is the value of MEPCC. mstatus is held by the
      state interpretation: the rule does not expose it. *)
  Inductive Mret_spec (lpc : LWord) (sregs : LSReg) (lpc' : LWord)
    : griotte_lang.val → Prop :=
  | Mret_spec_success p g b e a π :
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = true →
      sregs !! MEPCC = Some lpc' →
      Mret_spec lpc sregs lpc' NextIV
  | Mret_spec_failure :
      lpc' = lpc →
      Mret_failure lpc →
      Mret_spec lpc sregs lpc' FaultedV.

  (** [mret] writes MIE (it receives MPIE): the premise
      [link_transfer mie_from_mpie T1 T2] gives [T1] up for [T2] with the
      link on success; [T1] comes back on a fault. *)
  Lemma wp_Mret_link Ep pc_p pc_g pc_b pc_e pc_a pc_π w sregs dq (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (if has_sreg_access pc_p
     then sregs_of Mret ⊆ dom sregs
     else True) →
    link_transfer mie_from_mpie T1 T2 →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗
        ▷ T1
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ Mret_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) sregs lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ sregs, k ↦ₓ y) ∗
        (⌜retv = NextIV⌝ ∗ T2 ∨ ⌜retv = FaultedV⌝ ∗ T1)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dsregs Htr φ) "(>HPC & >Hpc_a & >Hsmap & HT) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link _ _ _ _ _ _ _ _ _ _ ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_valid with "Hsr Hsmap") as %[Hlsregs _].
    pose proof (ls_join_mstatus lsreg) as Hvst'.
    rewrite Hinstr /exec in Hstep.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. simplify_eq.
      iApply (instr_close_link_kept with "Hlink").
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
      iIntros "HPC _". iApply "Hφ". iFrame "HPC Hpc_a Hsmap". iSplit.
      - iPureIntro. apply Mret_spec_failure; first done. by eapply Mret_fail_nonxsr.
      - iRight. by iFrame. }
    destruct (indom_sregs_incl _ _ _ Dsregs Hlsregs MEPCC) as (vepcc & Hvepcc & Hvepcc');
      first (rewrite /sregs_of; set_solver).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvepcc') as (wepcc & Hwepcc & Hrelepcc).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    apply reg_phys_no_bounds in Hrelst; last done. cbn in Hrelst. subst wst.
    cbn in Hstep. rewrite Hxsr Hwepcc Hwst /= mpie_of_mstatus_enc in Hstep.
    injection Hstep as <- <-.
    rewrite /update_pcc /update_sreg /=.
    (* The new mstatus, then the new PC: MEPCC satisfies the PC invariant. *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ MSTATUS
      (lword_of_word (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)))
      (WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    rewrite -ls_join_set_mstatus in Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ vepcc wepcc Her1) as Her2.
    specialize (Her2 ltac:(by eapply (er_sreg_words _ _ _ _ _ _ _ Her)) Hrelepcc
                  ltac:(by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her MEPCC))).
    iMod (sys_interp_set_mstatus _ (ls_mpie lsreg) InterruptEnabled with "Hsr") as "Hsr".
    iMod (PC_update _ _ vepcc with "HPCa HPC") as "[HPCa HPC]".
    iMod (Htr _ (wepcc, r,
                 <[MSTATUS := WInt (mstatus_enc (ls_mpie lsreg) InterruptEnabled)]> psr, m, st)
           with "[$Hlink $HT]") as "[Hlink HT]".
    { split.
      - by rewrite /mie_st /mpie_st /= lookup_insert_eq Hwst /= mie_of_mstatus_enc
          mpie_of_mstatus_enc.
      - by rewrite /= lookup_insert_ne. }
    iPoseProof (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC") as "HSI".
    iModIntro. iFrame "HSI Hlink". iApply "Hφ". iFrame "HPC Hpc_a Hsmap". iSplit.
    - iPureIntro. by eapply Mret_spec_success.
    - iLeft. by iFrame.
  Qed.

  (** [mret], with the link-transfer premise. *)
  Lemma wp_mret_success_link E pc_p pc_g pc_b pc_e pc_a pc_π w (vepcc : LWord) dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    link_transfer mie_from_mpie T1 T2 →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ mepcc ↦ₓ vepcc
        ∗ ▷ T1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ vepcc
          ∗ pc_a ↦ₐ{dq} w
          ∗ mepcc ↦ₓ vepcc
          ∗ T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Htr φ) "(>HPC & >Hpc_a & >Hepcc & HT) Hφ".
    iDestruct (map_of_sregs_1 with "Hepcc") as "Hsmap".
    iApply (wp_Mret_link with "[$HPC $Hsmap $Hpc_a $HT]"); eauto.
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' retv) "(%Hspec & HPC & Hpc_a & Hsmap & HT)".
    destruct Hspec as [p g b e a π Hpc Hx Hvepcc | -> [p g b e a π Hpc Hx]];
      simplify_eq; last by rewrite Hxsr in Hx.
    simplify_map_eq.
    iDestruct "HT" as "[ [_ HT] | [%Hc _] ]"; last done.
    iApply "Hφ". iFrame.
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

End griotte_lang_rules.

(** The core corollaries, with today's statements. *)
Section griotte_lang_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types w : LWord.

  Lemma wp_Mret Ep pc_p pc_g pc_b pc_e pc_a pc_π w sregs dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (if has_sreg_access pc_p
     then sregs_of Mret ⊆ dom sregs
     else True) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₓ y)
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ Mret_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) sregs lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ sregs, k ↦ₓ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dsregs φ) "(>HPC & >Hpc_a & >Hsmap) Hφ".
    iApply (wp_Mret_link _ _ _ _ _ _ _ _ _ _ True%I True%I with "[$HPC $Hpc_a $Hsmap]");
      [done | done | done | apply link_transfer_core | done |].
    iNext. iIntros (lpc' retv) "(Hspec & HPC & Hpc_a & Hsmap & _)". iApply "Hφ". iFrame.
  Qed.

  (** [mret]: the PC receives MEPCC; MIE receives MPIE and MPIE becomes
      enabled, in the state interpretation. *)
  Lemma wp_mret_success E pc_p pc_g pc_b pc_e pc_a pc_π w (vepcc : LWord) dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ mepcc ↦ₓ vepcc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ vepcc
          ∗ pc_a ↦ₐ{dq} w
          ∗ mepcc ↦ₓ vepcc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr φ) "(>HPC & >Hpc_a & >Hepcc) Hφ".
    iApply (wp_mret_success_link _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hepcc]"); [done..| apply link_transfer_core | done |].
    iNext. iIntros "(HPC & Hpc_a & Hepcc & _)". iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules_core.
