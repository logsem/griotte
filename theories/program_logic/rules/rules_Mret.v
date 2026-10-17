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

  (** mstatus after [Mret] on the value [vst]: MIE receives MPIE, and MPIE
      becomes enabled. *)
  Definition mret_mstatus (vst : LWord) : LWord :=
    WInt (mstatus_enc (mpie_of (get_a vst.(lw))) InterruptEnabled).

  Inductive Mret_failure (lpc : LWord) : Prop :=
  | Mret_fail_nonxsr p g b e a π :
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = false →
      Mret_failure lpc.

  (** On success, the new PC is the value of MEPCC. *)
  Inductive Mret_spec (lpc : LWord) (sregs : LSReg) (lpc' : LWord) (sregs' : LSReg)
    : griotte_lang.val → Prop :=
  | Mret_spec_success p g b e a π vst :
      lpc = WCap true p g b e a @@? π →
      has_sreg_access p = true →
      sregs !! MEPCC = Some lpc' →
      sregs !! MSTATUS = Some vst →
      sregs' = <[MSTATUS := mret_mstatus vst]> sregs →
      Mret_spec lpc sregs lpc' sregs' NextIV
  | Mret_spec_failure :
      lpc' = lpc →
      sregs' = sregs →
      Mret_failure lpc →
      Mret_spec lpc sregs lpc' sregs' FailedV.

  Lemma wp_Mret Ep pc_p pc_g pc_b pc_e pc_a pc_π w sregs dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (if has_sreg_access pc_p
     then sregs_of Mret ⊆ dom sregs
     else True) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}
      Instr Executable @ Ep
    {{{ lpc' sregs' retv, RET retv;
        ⌜ Mret_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) sregs lpc' sregs' retv ⌝ ∗
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
      apply Mret_spec_failure; [done|done|]. by eapply Mret_fail_nonxsr. }
    destruct (indom_sregs_incl _ _ _ Dsregs Hlsregs MEPCC) as (vepcc & Hvepcc & Hvepcc');
      first (rewrite /sregs_of; set_solver).
    destruct (indom_sregs_incl _ _ _ Dsregs Hlsregs MSTATUS) as (vst & Hvst & Hvst');
      first (rewrite /sregs_of; set_solver).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvepcc') as (wepcc & Hwepcc & Hrelepcc).
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    assert (get_a wst = get_a vst.(lw)) as Hast.
    { destruct (reg_phys_and_tag _ _ _ Hrelst) as [s ->]. apply get_a_and_tag. }
    cbn in Hstep. rewrite Hxsr Hwepcc Hwst /= Hast in Hstep.
    injection Hstep as <- <-.
    (* The new mstatus, then the new PC: MEPCC satisfies the PC invariant. *)
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ MSTATUS (mret_mstatus vst)
      (WInt (mstatus_enc (mpie_of (get_a vst.(lw))) InterruptEnabled)) Her) as Her1.
    specialize (Her1 ltac:(apply reg_word_ok_int) eq_refl ltac:(by intros)
                  ltac:(apply reg_phys_lword_of_word)).
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ _ vepcc wepcc Her1) as Her2.
    specialize (Her2 ltac:(by eapply (er_sreg_words _ _ _ _ _ _ _ Her)) Hrelepcc
                  ltac:(by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her MEPCC))).
    iMod (gen_heap_update_inSepM _ _ MSTATUS (mret_mstatus vst) with "Hsr Hsmap")
      as "[Hsr Hsmap]"; first by eexists.
    iMod (PC_update _ _ vepcc with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplitR "Hφ HPC Hpc_a Hsmap".
    - iExists vepcc, _, _, lmem, R, C. iFrame. iPureIntro. exact Her2.
    - iApply "Hφ". iFrame. iPureIntro. by eapply Mret_spec_success.
  Qed.

  (** [mret]: the PC receives MEPCC, MIE receives MPIE, and MPIE becomes
      enabled. *)
  Lemma wp_mret_success E pc_p pc_g pc_b pc_e pc_a pc_π w (vepcc : LWord) mie mpie dq :
    decodeInstrW w.(lw) = Mret →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ mepcc ↦ₛᵣ vepcc
        ∗ ▷ mstatus ↦ₛᵣ WInt (mstatus_enc mie mpie) }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ vepcc
          ∗ pc_a ↦ₐ{dq} w
          ∗ mepcc ↦ₛᵣ vepcc
          ∗ mstatus ↦ₛᵣ WInt (mstatus_enc mpie InterruptEnabled) }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr φ) "(>HPC & >Hpc_a & >Hepcc & >Hst) Hφ".
    iDestruct (map_of_sregs_2 with "Hepcc Hst") as "[Hsmap %Hne]".
    iApply (wp_Mret with "[$HPC $Hsmap $Hpc_a]"); eauto.
    { rewrite Hxsr /sregs_of !dom_insert_L. set_solver. }
    iNext. iIntros (lpc' sregs' retv) "(%Hspec & HPC & Hpc_a & Hsmap)".
    destruct Hspec as [p g b e a π vst Hpc Hx Hvepcc Hvst -> | -> -> [p g b e a π Hpc Hx]];
      simplify_eq; last by rewrite Hxsr in Hx.
    simplify_map_eq.
    rewrite (insert_insert_ne _ MSTATUS MEPCC) // insert_insert_eq.
    rewrite /mret_mstatus /= mpie_of_mstatus_enc.
    iApply "Hφ". iFrame.
    iDestruct (sregs_of_map_2 with "Hsmap") as "[$ $]"; done.
  Qed.

End griotte_lang_rules.
