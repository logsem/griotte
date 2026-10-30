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

  (** mstatus after [SetMIE mie] on the value [vst]: MIE is [mie], MPIE is
      read from [vst]. *)
  Definition setmie_mstatus (mie : InterruptStatus) (vst : LWord) : LWord :=
    WInt (mstatus_enc mie (mpie_of (get_a vst.(lw)))).

  Inductive SetMIE_failure (lpc : LWord) : Prop :=
  | SetMIE_fail_nonxsr p g b e a π :
      lpc = Cap p g b e a @@? π →
      has_sreg_access p = false →
      SetMIE_failure lpc
  | SetMIE_fail_incrPC :
      incrementPC lpc = None →
      SetMIE_failure lpc.

  (** mstatus is held by the state interpretation: the rule does not expose
      it. *)
  Inductive SetMIE_spec (lpc : LWord) (lpc' : LWord) : griotte_lang.val → Prop :=
  | SetMIE_spec_success p g b e a π :
      lpc = Cap p g b e a @@? π →
      has_sreg_access p = true →
      incrementPC lpc = Some lpc' →
      SetMIE_spec lpc lpc' NextIV
  | SetMIE_spec_failure :
      lpc' = lpc →
      SetMIE_failure lpc →
      SetMIE_spec lpc lpc' FaultedV.

  (** [SetMIE mie] writes MIE: the premise [link_transfer (mie_set mie) T1 T2]
      gives [T1] up for [T2] with the link on success; [T1] comes back on a
      fault. *)
  Lemma wp_SetMIE_link Ep pc_p pc_g pc_b pc_e pc_a pc_π w mie dq (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    link_transfer (mie_set mie) T1 T2 →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ T1
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ SetMIE_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        (⌜retv = NextIV⌝ ∗ T2 ∨ ⌜retv = FaultedV⌝ ∗ T1)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Htr φ) "(>HPC & >Hpc_a & HT) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step_link _ _ _ _ _ _ _ _ _ _ ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    pose proof (ls_join_mstatus lsreg) as Hvst'.
    rewrite Hinstr /exec in Hstep.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. simplify_eq.
      iApply (instr_close_link_kept with "Hlink").
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
      iIntros "HPC _". iApply "Hφ". iFrame "HPC Hpc_a". iSplit.
      - iPureIntro. apply SetMIE_spec_failure; first done. by eapply SetMIE_fail_nonxsr.
      - iRight. by iFrame. }
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    apply reg_phys_no_bounds in Hrelst; last done. cbn in Hrelst. subst wst.
    cbn in Hstep. rewrite Hxsr Hwst /= mpie_of_mstatus_enc in Hstep.
    destruct (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hi;
      cycle 1.
    { (* The PC increment fails: the state and the link are unchanged. *)
      pose proof (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) as Hfail.
      rewrite /nextPC /advancePC /= in Hfail.
      destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; first done.
      simplify_eq.
      iApply (instr_close_link_kept with "Hlink").
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
      iIntros "HPC _". iApply "Hφ". iFrame "HPC Hpc_a". iSplit.
      - iPureIntro. apply SetMIE_spec_failure; first done. by apply SetMIE_fail_incrPC.
      - iRight. by iFrame. }
    (* The new mstatus *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ mstatus
                  (lword_of_word (WInt (mstatus_enc mie (ls_mpie lsreg))))
                  (WInt (mstatus_enc mie (ls_mpie lsreg))) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    rewrite -ls_join_set_mstatus in Her1.
    destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & Her2).
    rewrite /nextPC /advancePC /= in Hu. rewrite /update_sreg /update_pcc /nextPC /advancePC /= in Hstep.
    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; last done. simplify_eq.
    cbn [reg sreg mem pcc shadowtbl fst snd].
    iMod (sys_interp_set_mstatus _ mie (ls_mpie lsreg) with "Hsr") as "Hsr".
    iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
    iMod (Htr _ (Cap pc_p pc_g pc_b pc_e pc_a', r,
                 <[mstatus := WInt (mstatus_enc mie (ls_mpie lsreg))]> psr, m, st)
           with "[$Hlink $HT]") as "[Hlink HT]".
    { split.
      - by rewrite /= lookup_insert_ne.
      - by rewrite /mie_st /= lookup_insert_eq /= mie_of_mstatus_enc. }
    iPoseProof (SI_close _ _ _ _ _ _ _ Her2 with "HPCa Hr Hsr Hm Hst HR HC") as "HSI".
    iModIntro. iFrame "HSI Hlink". iApply "Hφ". iFrame "HPC Hpc_a". iSplit.
    - iPureIntro. rewrite /incrementPC /incrementPC_gen /= Hpca' in Hi. simplify_eq.
      eapply SetMIE_spec_success; [done | done | by apply incrementPC_add].
    - iLeft. by iFrame.
  Qed.

  (** [SetMIE mie], as [csrsi mstatus, 0x8] and [csrci mstatus, 0x8], with
      the link-transfer premise. *)
  Lemma wp_setmie_success_link E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w mie dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    link_transfer (mie_set mie) T1 T2 →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w ∗ ▷ T1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w ∗ T2 }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Htr φ) "(>HPC & >Hpc_a & HT) Hφ".
    iApply (wp_SetMIE_link with "[$HPC $Hpc_a $HT]"); eauto.
    iNext. iIntros (lpc' retv) "(%Hspec & HPC & Hpc_a & HT)".
    destruct Hspec as [p g b e a π Hpc Hx Hi | -> [p g b e a π Hpc Hx | Hi] ];
      simplify_eq.
    - rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. simplify_eq.
      iDestruct "HT" as "[ [_ HT] | [%Hc _] ]"; last done.
      iApply "Hφ". iFrame.
    - by rewrite Hxsr in Hx.
    - by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi.
  Qed.

End griotte_lang_rules.

(** The core corollaries, with today's statements: at the core link, the
    premise holds with [True]. *)
Section griotte_lang_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types w : LWord.

  Lemma wp_SetMIE Ep pc_p pc_g pc_b pc_e pc_a pc_π w mie dq :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ SetMIE_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w
    }}}.
  Proof.
    iIntros (Hinstr Hvpc φ) "(>HPC & >Hpc_a) Hφ".
    iApply (wp_SetMIE_link _ _ _ _ _ _ _ _ _ _ True%I True%I with "[$HPC $Hpc_a]");
      [done | done | apply link_transfer_core | |].
    { done. }
    iNext. iIntros (lpc' retv) "(Hspec & HPC & Hpc_a & _)". iApply "Hφ". iFrame.
  Qed.

  (** [SetMIE mie], as [csrsi mstatus, 0x8] and [csrci mstatus, 0x8]: MIE
      becomes [mie], MPIE is unchanged, in the state interpretation. *)
  Lemma wp_setmie_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w mie dq :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' φ) "(>HPC & >Hpc_a) Hφ".
    iApply (wp_setmie_success_link _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a]"); [done..| apply link_transfer_core | done |].
    iNext. iIntros "(HPC & Hpc_a & _)". iApply "Hφ". iFrame.
  Qed.
End griotte_lang_rules_core.
