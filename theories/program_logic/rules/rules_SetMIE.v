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

  Inductive SetMIE_spec
    (lpc : LWord) (sregs : LSReg) (mie : InterruptStatus) (lpc' : LWord) (sregs' : LSReg)
    : griotte_lang.val → Prop :=
  | SetMIE_spec_success p g b e a π vst :
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = true →
      sregs !! MSTATUS = Some vst →
      incrementPC lpc = Some lpc' →
      sregs' = <[MSTATUS := setmie_mstatus mie vst]> sregs →
      SetMIE_spec lpc sregs mie lpc' sregs' NextIV
  | SetMIE_spec_failure :
      lpc' = lpc →
      sregs' = sregs →
      SetMIE_failure lpc →
      SetMIE_spec lpc sregs mie lpc' sregs' FailedV.

  Lemma wp_SetMIE Ep pc_p pc_g pc_b pc_e pc_a pc_π w mie sregs dq :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (if has_sreg_access pc_p
     then sregs_of (SetMIE mie) ⊆ dom sregs
     else True) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}
      Instr Executable @ Ep
    {{{ lpc' sregs' retv, RET retv;
        ⌜ SetMIE_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) sregs mie lpc' sregs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ sregs', k ↦ₛᵣ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc Dsregs φ) "(>HPC & >Hpc_a & >Hsmap) Hφ".
    iAssert ([∗ map] k↦y ∈ (∅ : LReg), k ↦ᵣ y)%I as "Hmap0"; first by rewrite big_sepM_empty.
    iApply (wp_instr_step _ _ _ _ _ _ _ _ _ _ ∅ with "HPC Hpc_a Hmap0"); eauto.
    iNext; iIntros (r psr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (gen_heap_valid_inclSepM with "Hsr Hsmap") as %Hlsregs.
    rewrite Hinstr /exec in Hstep.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. instr_fail Hstep.
      apply SetMIE_spec_failure; [done|done|]. by eapply SetMIE_fail_nonxsr. }
    destruct (indom_sregs_incl _ _ _ Dsregs Hlsregs MSTATUS) as (vst & Hvst & Hvst');
      first (rewrite /sregs_of; set_solver).
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
      apply SetMIE_spec_failure; [done|done|]. by apply SetMIE_fail_incrPC. }
    (* The new mstatus *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ MSTATUS (setmie_mstatus mie vst)
      (WInt (mstatus_enc mie (mpie_of (get_a vst.(lw))))) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) eq_refl ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    iMod (gen_heap_update_inSepM _ _ MSTATUS (setmie_mstatus mie vst) with "Hsr Hsmap")
      as "[Hsr Hsmap]"; first by eexists.
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ _ 1 _ _ _
      (λ lpc' retv, SetMIE_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) sregs mie lpc'
         (<[MSTATUS := setmie_mstatus mie vst]> sregs) retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hsmap]").
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

  (** Inverts a [SetMIE_spec] whose PC increment succeeds and whose PC has the
      system-register permission: the failure case is absurd. *)
  Lemma SetMIE_spec_success_inv pc_p pc_g pc_b pc_e pc_a pc_π pc_a' sregs mie lpc' sregs' retv :
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    SetMIE_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) sregs mie lpc' sregs' retv →
    retv = NextIV ∧ lpc' = WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∧
    ∃ vst, sregs !! MSTATUS = Some vst ∧
      sregs' = <[MSTATUS := setmie_mstatus mie vst]> sregs.
  Proof.
    intros Hxsr Hpca' Hspec.
    destruct Hspec as [p g b e a π vst Hpc Hx Hvst Hi -> | -> -> Hfail].
    - simplify_eq. rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi. simplify_eq.
      split_and!; try done. by eexists.
    - exfalso. destruct Hfail as [p g b e a π Hpc Hx | Hi].
      + simplify_eq. by rewrite Hxsr in Hx.
      + by rewrite (incrementPC_add _ _ _ _ _ _ _ _ Hpca') in Hi.
  Qed.

  (** [SetMIE mie], as [csrsi mstatus, 0x8] and [csrci mstatus, 0x8]: MIE
      becomes [mie], MPIE is unchanged. *)
  Lemma wp_setmie_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w mie mie_old mpie dq :
    decodeInstrW w.(lw) = SetMIE mie →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ mstatus ↦ₛᵣ WInt (mstatus_enc mie_old mpie) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ mstatus ↦ₛᵣ WInt (mstatus_enc mie mpie) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' φ) "(>HPC & >Hpc_a & >Hst) Hφ".
    iDestruct (map_of_sregs_1 with "Hst") as "Hsmap".
    iApply (wp_SetMIE with "[$HPC $Hsmap $Hpc_a]"); eauto.
    { rewrite Hxsr /sregs_of dom_singleton_L. set_solver. }
    iNext. iIntros (lpc' sregs' retv) "(%Hspec & HPC & Hpc_a & Hsmap)".
    destruct (SetMIE_spec_success_inv _ _ _ _ _ _ _ _ _ _ _ _ Hxsr Hpca' Hspec)
      as (-> & -> & vst & Hvst & ->).
    simplify_map_eq. rewrite insert_singleton_eq /setmie_mstatus /= mpie_of_mstatus_enc.
    iApply "Hφ". iFrame.
    iApply (sregs_of_map_1 with "Hsmap").
  Qed.

End griotte_lang_rules.
