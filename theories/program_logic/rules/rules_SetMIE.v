From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
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
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = false →
      SetMIE_failure lpc
  | SetMIE_fail_incrPC :
      incrementPC lpc = None →
      SetMIE_failure lpc.

  (** mstatus is held by the state interpretation: the rule does not expose
      it. *)
  Inductive SetMIE_spec (lpc : LWord) (lpc' : LWord) : griotte_lang.val → Prop :=
  | SetMIE_spec_success p g b e a π :
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = true →
      incrementPC lpc = Some lpc' →
      SetMIE_spec lpc lpc' NextIV
  | SetMIE_spec_failure :
      lpc' = lpc →
      SetMIE_failure lpc →
      SetMIE_spec lpc lpc' FaultedV.

  Lemma wp_SetMIE Ep pc_p pc_g pc_b pc_e pc_a pc_π w mie dq :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w
    }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ SetMIE_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w
    }}}.
  Proof.
    iIntros (Hinstr Hvpc φ) "(>HPC & >Hpc_a) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step _ _ _ _ _ _ _ _ _ _ ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iAssert (⌜∃ vst, lsreg !! MSTATUS = Some vst⌝)%I as %[vst Hvst'].
    { iDestruct "Hsr" as "[Hsr [%v Hmst]]".
      iDestruct (gen_heap_valid with "Hsr Hmst") as %?. iPureIntro. by exists v. }
    rewrite Hinstr /exec in Hstep.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. instr_fail Hstep.
      apply SetMIE_spec_failure; first done. by eapply SetMIE_fail_nonxsr. }
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    assert (get_a wst = get_a vst.(lw)) as Hast.
    { destruct (reg_phys_and_tag _ _ _ Hrelst) as [s ->]. apply get_a_and_tag. }
    cbn in Hstep. rewrite Hxsr Hwst /= Hast in Hstep.
    destruct (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π)) as [lpc'|] eqn:Hi;
      cycle 1.
    { (* The PC increment fails: the state is unchanged. *)
      pose proof (erasure_incrementPC_fail _ _ _ _ _ _ _ _ _ _ _ _ Her Hi) as Hfail.
      rewrite /updatePC /updatePC_gen /= in Hfail.
      destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; first done.
      instr_fail Hstep.
      apply SetMIE_spec_failure; first done. by apply SetMIE_fail_incrPC. }
    (* The new mstatus, in the state interpretation *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ MSTATUS (setmie_mstatus mie vst)
      (WInt (mstatus_enc mie (mpie_of (get_a vst.(lw))))) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) eq_refl ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    iDestruct "Hsr" as "[Hsr [%v Hmst]]".
    iMod (gen_heap_update _ _ _ (setmie_mstatus mie vst) with "Hsr Hmst") as "[Hsr Hmst]".
    iAssert (sreg_interp (<[MSTATUS := setmie_mstatus mie vst]> lsreg))
      with "[Hsr Hmst]" as "Hsr".
    { iFrame "Hsr". by iExists _. }
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, SetMIE_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) lpc' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]").
    { exact Her1. }
    { destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ _ _ Her1 Hi) as (pc' & Hu & _).
      rewrite /updatePC in Hu. rewrite /update_sreg /update_pcc /= in Hstep.
      rewrite Hu. revert Hstep Hu. rewrite /updatePC_gen /=.
      destruct (pc_a + 1)%a; intros Hstep Hu; by simplify_eq. }
    { intros lpc'' Hi'. rewrite /incrementPC in Hi. simplify_eq.
      by eapply SetMIE_spec_success. }
    { intros Hi'. rewrite /incrementPC in Hi. congruence. }
    iIntros (lpc'' retv Hspec) "HPC _". iApply "Hφ". by iFrame.
  Qed.

  (** [SetMIE mie], as [csrsi mstatus, 0x8] and [csrci mstatus, 0x8]: MIE
      becomes [mie], MPIE is unchanged, in the state interpretation. *)
  Lemma wp_setmie_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w mie dq :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' φ) "(>HPC & >Hpc_a) Hφ".
    iApply (wp_SetMIE with "[$HPC $Hpc_a]"); eauto.
    iNext. iIntros (lpc' retv) "(%Hspec & HPC & Hpc_a)".
    destruct Hspec as [p g b e a π Hpc Hx Hi | -> [p g b e a π Hpc Hx | Hi]];
      simplify_eq.
    - rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. simplify_eq.
      iApply "Hφ". iFrame.
    - by rewrite Hxsr in Hx.
    - by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi.
  Qed.

End griotte_lang_rules.
