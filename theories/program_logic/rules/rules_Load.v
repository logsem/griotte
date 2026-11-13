From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_mem_access.

(** ** Faults of [CLoad], on every copy of the owned registers *)

(** The physical copy of a register read by the instruction. *)
#[local] Lemma regs_fault_llookup `{MachineParameters} (regs : LReg) φ src wa :
  (∀ r v, regs !! r = Some v → ∃ s, reg φ !!ᵣ r = Some (and_tag s v.(lw))) →
  regs !!ₗ src = Some wa →
  ∃ s, reg φ !!ᵣ src = Some (and_tag s wa.(lw)).
Proof.
  intros Hcopy Hsrc. rewrite /llookup_reg in Hsrc. case_decide as Hcnull; simplify_eq.
  - exists true. simplify_eq. by rewrite lookup_reg_cnull and_tag_true.
  - by apply Hcopy.
Qed.

(** An untagged source faults. *)
Lemma CLoad_fault_untagged `{MachineParameters} dst src imm p lpc (regs : LReg) wa :
  regs !!ₗ src = Some wa → get_tag wa.(lw) = false →
  regs_fault exec_opt (CLoad dst src imm) p lpc regs.
Proof.
  intros Hsrc Htag φ _ Hcopy.
  destruct (regs_fault_llookup regs φ src wa Hcopy Hsrc) as [s Hlook].
  cbn [exec_opt]. rewrite Hlook /=.
  destruct wa as [ [| [ [] p' g b e a|] | |] π]; cbn in Htag; try discriminate;
    destruct s; done.
Qed.

(** A source that is not a capability faults. *)
Lemma CLoad_fault_not_cap `{MachineParameters} dst src imm p lpc (regs : LReg) wa :
  regs !!ₗ src = Some wa → is_cap wa.(lw) = false →
  regs_fault exec_opt (CLoad dst src imm) p lpc regs.
Proof.
  intros Hsrc Hcap φ _ Hcopy.
  destruct (regs_fault_llookup regs φ src wa Hcopy Hsrc) as [s Hlook].
  cbn [exec_opt]. rewrite Hlook /=.
  destruct wa as [ [| [ [] p' g b e a|] | |] π]; cbn in Hcap; try discriminate;
    destruct s; done.
Qed.

(** A source whose address plus the offset overflows faults. *)
Lemma CLoad_fault_address `{MachineParameters} dst src imm p lpc (regs : LReg) wa pa ga ba ea aa :
  regs !!ₗ src = Some wa → wa.(lw) = Cap pa ga ba ea aa → (aa + imm)%a = None →
  regs_fault exec_opt (CLoad dst src imm) p lpc regs.
Proof.
  intros Hsrc Hwa Hadd φ _ Hcopy.
  destruct (regs_fault_llookup regs φ src wa Hcopy Hsrc) as [s Hlook].
  rewrite Hwa in Hlook.
  cbn [exec_opt]. rewrite Hlook /=.
  destruct s; cbn; [by rewrite Hadd | done].
Qed.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* The addressing capability's identifier does not matter: only its
     physical word is read. *)
  Definition reg_allows_load_imm (regs : LReg) (r : RegName) (imm : Z) p g b e a ea :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧
    (a + imm)%a = Some ea ∧ readAllowed p = true ∧ withinBounds b e ea = true.

  Definition reg_allows_load (regs : LReg) (r : RegName) p g b e a  :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  (** The status witnesses ([load_witness_ok], [load_witness_lookup],
      [load_post_choose]) are in [rules_mem_access.v]. *)

  Inductive Load_failure_spec (lpc : LWord) (regs: LReg) (r1 r2: RegName) (imm : Z)
    (mem : LMem) (shadow : ShadowTbl) (wit : load_witness) (dw : deref_witness) :=
  | Load_fail_const w:
      regs !!ₗ r2 = Some w ->
      is_cap w.(lw) = false →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_tag p g b e a:
      lw <$> regs !!ₗ r2 = Some (Cap⁻ p g b e a) →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_addr_imm p g b e a:
      lw <$> regs !!ₗ r2 = Some (Cap p g b e a) →
      (a + imm)%a = None →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_bounds_imm p g b e a ea:
      lw <$> regs !!ₗ r2 = Some (Cap p g b e a) ->
      (a + imm)%a = Some ea →
      (readAllowed p = false ∨ withinBounds b e ea = false) →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_invalid_PC_imm p g b e a ea loadv loadv':
      lw <$> regs !!ₗ r2 = Some (Cap p g b e a) ->
      (a + imm)%a = Some ea →
      is_shadow_address ea = false →
      mem !! ea = Some loadv →
      load_post wit p loadv loadv' →
      incrementPC lpc = None ->
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_invalid_PC_shadow_imm p g b e a ea heap_a revoked:
      lw <$> regs !!ₗ r2 = Some (Cap p g b e a) →
      (a + imm)%a = Some ea →
      is_shadow_address ea = true →
      shadow_to_heap ea = Some heap_a →
      shadow !! heap_a = Some revoked →
      incrementPC lpc = None →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_invalid_PC_revoker_imm p g b e a ea:
      lw <$> regs !!ₗ r2 = Some (Cap p g b e a) →
      (a + imm)%a = Some ea →
      is_revoker_address ea = true →
      mem !! ea = None →
      incrementPC lpc = None →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  | Load_fail_invalid_PC_timedev_imm p g b e a ea:
      lw <$> regs !!ₗ r2 = Some (Cap p g b e a) →
      (a + imm)%a = Some ea →
      is_time_device_address ea = true →
      mem !! ea = None →
      incrementPC lpc = None →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  (* A source with an identifier not covered by the witness may have been
     revoked: its physical copy is untagged. *)
  | Load_fail_revoked p g b e a π:
      regs !!ₗ r2 = Some (Cap p g b e a @@? π) →
      π ≠ deref_id dw →
      Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw
  .

  Definition reg_allows_load_offset (regs : LReg) (r : RegName)
      (imm : Z) p g b e (ea : Addr) : Prop :=
    match imm with
    | 0%Z => reg_allows_load regs r p g b e ea
    | _ => ∃ a, reg_allows_load_imm regs r imm p g b e a ea
    end.

  Lemma reg_allows_load_offset_imm regs r imm p g b e ea :
    reg_allows_load_offset regs r imm p g b e ea →
    ∃ a, reg_allows_load_imm regs r imm p g b e a ea.
  Proof.
    destruct imm as [|imm|imm]; simpl.
    - intros (Hreg & Hra & Hwb). exists ea. repeat split; auto.
      by rewrite finz_add_0.
    - exact (λ H, H).
    - exact (λ H, H).
  Qed.

  Lemma reg_allows_load_imm_offset regs r imm p g b e a ea :
    reg_allows_load_imm regs r imm p g b e a ea →
    reg_allows_load_offset regs r imm p g b e ea.
  Proof.
    destruct imm as [|imm|imm]; simpl; intros Hallow;
      try (by exists a).
    destruct Hallow as (Hreg & Hadd & Hra & Hwb).
    rewrite finz_add_0 in Hadd. inversion Hadd; subst ea.
    repeat split; auto.
  Qed.

  Inductive Load_spec {k : kind}
    (lpc : LWord) (regs: LReg) (r1 r2: RegName) (imm : Z)
    (lpc' : LWord) (regs': LReg) (mem : LMem) (shadow : ShadowTbl) (wit : load_witness)
    (dw : deref_witness) : tval k → Prop
  :=
  | Load_spec_success p g b e a loadv loadv' :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = false →
    mem !! a = Some loadv →
    load_post wit p loadv loadv' →
    incrementPC lpc = Some lpc' →
    regs' = <[ r1 := loadv' ]ₗ> regs →
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw NextIV

  | Load_spec_success_shadow p g b e a heap_a revoked :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some revoked →
    incrementPC lpc = Some lpc' →
    regs' = <[ r1 := lword_of_word (WInt (encodeAllocStatus revoked)) ]ₗ> regs →
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw NextIV

  (* The revoker reads as zero. *)
  | Load_spec_success_revoker p g b e a :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_revoker_address a = true →
    mem !! a = None →
    incrementPC lpc = Some lpc' →
    regs' = <[ r1 := lword_of_word (WInt 0) ]ₗ> regs →
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw NextIV

  (* A time device reads as an integer, the value of its register, which the
     logical state does not record. *)
  | Load_spec_success_timedev p g b e a z :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_time_device_address a = true →
    mem !! a = None →
    incrementPC lpc = Some lpc' →
    regs' = <[ r1 := lword_of_word (WInt z) ]ₗ> regs →
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw NextIV

  | Load_spec_failure :
    Load_failure_spec lpc regs r1 r2 imm mem shadow wit dw ->
    lpc' = lpc ->
    regs' = regs ->
    Load_spec lpc regs r1 r2 imm lpc' regs' mem shadow wit dw FaultedV.

  (* Own the source location, or its shadow entry; neither the revoker nor a
     time device needs a resource. *)
  Definition allow_load_mem_or_shadow_offset (r : RegName) (imm : Z)
      (regs : LReg) (mem : LMem) (shadow : ShadowTbl) :=
    ∀ p g b e ea,
      reg_allows_load_offset regs r imm p g b e ea →
      if is_shadow_address ea then
        ∃ heap_a, shadow_to_heap ea = Some heap_a ∧ is_Some (shadow !! heap_a)
      else if is_revoker_address ea then True
      else if is_time_device_address ea then True
      else ∃ loadv, mem !! ea = Some loadv.

  Definition allow_load_mem_or_shadow (r : RegName) (regs : LReg)
    (mem : LMem) (shadow : ShadowTbl) :=
    allow_load_mem_or_shadow_offset r 0 regs mem shadow.

  Lemma wp_load_general_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs shadow sdq wit dw :
   decodeInstrW w.(lw) = CLoad r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (CLoad r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_mem_or_shadow_offset r2 imm regs mem shadow →
   dom mem = dom dfracs →

   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
       load_witness_res wit ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' regs' retv, RET retv;
       ⌜ Load_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' regs' mem shadow wit dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
         load_witness_res wit ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad Hdomeq φ)
      "(>HPC & >Hmem & >Hshadow & Hwit & Hdw & >Hmap) Hφ".
    (* The instruction word is taken out of the memory map for the step. *)
    assert (is_Some (dfracs !! pc_a)) as [dq_pc Hdq_pc].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom; eauto. }
    assert (prod_merge dfracs mem !! pc_a = Some (dq_pc, w)) as Hmerge_pc.
    { by rewrite lookup_merge Hmem_pc Hdq_pc. }
    iDestruct (big_sepM_delete _ _ pc_a (dq_pc, w) with "Hmem") as "[Hpc_a Hmem]"; first done.
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hinstr; by apply sw_of_none|done|].
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ2) "@".
    iAssert ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2)%I
      with "[Hpc_a Hmem]" as "Hmem".
    { iApply (big_sepM_delete _ _ pc_a (dq_pc, w)); first done. iFrame. }
    iDestruct (load_witness_lookup with "HR Hwit") as %Hwit.
    iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
    pose proof (er_registry _ _ _ _ _ _ _ Her) as Hreg; cbn in Hreg.
    pose proof (er_mmio _ _ _ _ _ _ _ Her) as Hmmio; cbn in Hmmio.
    iAssert (⌜∀ a loadv, mem !! a = Some loadv → lmem !! a = Some loadv⌝)%I as %Hmem_valid.
    { iIntros (a loadv Hlookup).
      assert (is_Some (dfracs !! a)) as [dq Hdq].
      { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom; eauto. }
      iApply (gen_mem_valid_inSepM_general (prod_merge dfracs mem) with "Hm Hmem").
      by rewrite lookup_merge Hlookup Hdq. }
    iAssert (⌜∀ a revoked, shadow !! a = Some revoked → st !! a = Some revoked⌝)%I as %Hshadow_valid.
    { iIntros (a revoked Hlookup).
      iDestruct (big_sepM_lookup with "Hshadow") as "Ha"; first exact Hlookup.
      iApply (gen_heap_valid with "Hst Ha"). }
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of, operands_of in Hri.
    odestruct (Hri r2) as [r2v [Hr'2 _] ]; first by set_solver+.
    odestruct (Hri r1) as [r1v [Hr'1 _] ]; first by set_solver+.
    clear Hri.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hr'2) as (s2 & Hr2 & Hrel2).
    rewrite Hinstr in Hstep.
    rewrite /exec /= Hr2 /= in Hstep.

    destruct (is_cap r2v.(lw)) eqn:Hr2v.
    2: {
      assert ((Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)) = (c, σ2)) as Hstep'.
      { unfold is_cap in Hr2v. destruct r2v as [r2v ?]; cbn in *.
        destruct_word r2v; by simplify_pair_eq. }
      instr_fail Hstep'. apply Load_spec_failure; [|done..]. by eapply Load_fail_const. }
    destruct r2v as [ [ | [t p g b e a | ] | | ] π2]; try inversion Hr2v. clear Hr2v.
    destruct t.
    2: { cbn in Hstep. rewrite ?andb_false_r in Hstep.
         instr_fail Hstep. apply Load_spec_failure; [|done..]. eapply Load_fail_tag. by rewrite Hr'2. }
    destruct s2.
    2: { (* The physical copy of the source is untagged. *)
      cbn in Hstep. instr_fail Hstep. apply Load_spec_failure; [|done..].
      destruct (decide (π2 = deref_id dw)) as [Hπ|Hπ]; last by eapply Load_fail_revoked.
      destruct (a + imm)%a as [ea|] eqn:Hadd.
      2: by eapply Load_fail_addr_imm; [rewrite Hr'2 | done].
      destruct (withinBounds b e ea) eqn:Hwb.
      2: by eapply Load_fail_bounds_imm; [rewrite Hr'2 | done | right].
      (* A stripped source under its witness is a heap capability without
         authority: its bounds are empty. *)
      exfalso.
      destruct Hrel2 as [ [Heq | [_ [ [Hst _] | [Hna [base Hh] ] ] ] ] _]; cbn in *; try discriminate.
      { by apply (deref_witness_not_stale R dw (Cap p g b e a @@? π2)). }
      assert (is_heap_address b = true) as Hbh.
      { rewrite /heap_cap_base /= in Hh. by destruct (is_heap_address b). }
      apply withinBounds_true_iff in Hwb. apply Hna. split; first done. exists b.
      apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
      split; [solve_addr | done]. }
    cbn in Hstep.
    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { instr_fail Hstep. apply Load_spec_failure; [|done..]. eapply Load_fail_addr_imm; last done. by rewrite Hr'2. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2: {
      apply andb_false_iff in HRA.
      instr_fail Hstep. apply Load_spec_failure; [|done..]. eapply Load_fail_bounds_imm; eauto. by rewrite Hr'2.
    }
    apply andb_true_iff in HRA as [Hra Hwb].
    assert (Hallow : reg_allows_load_offset regs r2 imm p g b e ea).
    { apply reg_allows_load_imm_offset with (a := a). repeat split; auto. by rewrite Hr'2. }
    specialize (HaLoad p g b e ea Hallow).

    (* Classify the read: the loaded logical word, which the register gets,
       its physical copy, and the spec's success and failure cases. *)
    assert (∃ (v : LWord) (pv : Word),
      reg_word_ok R C v ∧
      reg_phys R v pv ∧
      (match nextPC (update_reg (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) r1 pv) with
       | Some conf => conf | None => (Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)) end) = (c, σ2) ∧
      (∀ lpc', incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
         Load_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' (<[r1 := v]ₗ> regs) mem shadow wit dw (@NextIV (kind_of th))) ∧
      (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None →
         Load_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs mem shadow wit dw (@FaultedV (kind_of th))))
      as (v & pv & Hok & Hpv & Hstep' & Hsucc & Hfailure).
    {
      rewrite /is_mmio_address /mmio_load /shadow_load /revoker_load in Hstep.
      destruct (is_shadow_address ea) eqn:Hshadow.
      - destruct HaLoad as (heap_a & Htranslate & revoked & Hlookup).
        rewrite Htranslate /= (Hshadow_valid _ _ Hlookup) /= in Hstep.
        exists (lword_of_word (WInt (encodeAllocStatus revoked))), (WInt (encodeAllocStatus revoked)).
        split; first apply reg_word_ok_int. split; first apply reg_phys_lword_of_word.
        split; first exact Hstep.
        split.
        + intros. by eapply Load_spec_success_shadow.
        + intros. apply Load_spec_failure; [|done..]. by eapply Load_fail_invalid_PC_shadow_imm; eauto; rewrite Hr'2.
      - destruct (is_revoker_address ea) eqn:Hrevoker.
        + rewrite /= in Hstep.
          assert (mem !! ea = None) as Hnone.
          { destruct (mem !! ea) as [v|] eqn:Hv; last done.
            destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hv)) as (pv & Hpv & _).
            by rewrite (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hpv) in Hrevoker. }
          exists (lword_of_word (WInt 0)), (WInt 0).
          split; first apply reg_word_ok_int. split; first apply reg_phys_lword_of_word.
          split; first exact Hstep.
          split.
          * intros. by eapply Load_spec_success_revoker.
          * intros. apply Load_spec_failure; [|done..]. by eapply Load_fail_invalid_PC_revoker_imm; eauto; rewrite Hr'2.
        + destruct (is_time_device_address ea) eqn:Htdev.
          * rewrite /time_dev_load /= in Hstep.
            assert (mem !! ea = None) as Hnone.
            { destruct (mem !! ea) as [v|] eqn:Hv; last done.
              destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hv)) as (pv & Hpv & _).
              by rewrite (mem_avoids_mmio_not_time_device _ _ _ Hmmio Hpv) in Htdev. }
            exists (lword_of_word (WInt (time_dev_value td ea))), (WInt (time_dev_value td ea)).
            split; first apply reg_word_ok_int. split; first apply reg_phys_lword_of_word.
            split; first exact Hstep.
            split.
            -- intros. by eapply Load_spec_success_timedev.
            -- intros. apply Load_spec_failure; [|done..].
               by eapply Load_fail_invalid_PC_timedev_imm; eauto; rewrite Hr'2.
          * destruct HaLoad as (loadv & Hlookup).
            destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her (Hmem_valid _ _ Hlookup))
              as (pv & Hpv & Hpvok).
            rewrite Hpv /= in Hstep.
            destruct (load_filter_is_Some R C st p pv Hreg) as [pl Hpl].
            assert ((match nextPC (update_reg (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td) r1 pl) with
                     | Some conf => conf | None => (Faulted, (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) r sr m st td)) end) = (c, σ2))
              as Hstep'.
            { rewrite -Hstep /load_filter in Hpl |- *.
              destruct (heap_cap_base pv) as [base|]; last by simplify_eq.
              destruct (st !! base) as [ []|]; simplify_eq; done. }
            destruct (load_post_choose _ _ _ _ _ _ _ _ Hreg Hwit Hpvok Hpl) as (loadv' & Hpost & Hok' & Hphys).
            exists loadv', pl.
            split; first done. split; first done.
            split; first exact Hstep'.
            split.
            -- intros. by eapply Load_spec_success.
            -- intros. apply Load_spec_failure; [|done..]. eapply Load_fail_invalid_PC_imm; eauto. by rewrite Hr'2.
    }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ _ _ r1 v pv _ _ _
      (λ lpc' regs' retv, Load_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' regs' mem shadow wit dw retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hmem Hshadow Hwit Hdw]").
    { exact Her. } { exact Hlregs. }
    { eapply elem_of_lregs_dom; [exact Dregs | try unfold regs_of, operands_of; set_solver+]. }
    { exact Hok. } { exact Hstep'. } { exact Hpv. } { exact Hsucc. } { exact Hfailure. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (** [wp_load_general_shadow_imm] for a load from memory outside the shadow
      table, with one points-to per resource. *)
  Lemma wp_load_general_shadow_imm_one E pc_p pc_g pc_b pc_e pc_a pc_a' dst src
      (imm : Z) (wi wd : LWord) dq p g b e a_src a (raw : LWord) wit :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (⌜retv = FaultedV⌝ ∗
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
         pc_a ↦ₐ{dq} wi ∗
         dst ↦ᵣ wd ∗
         src ↦ᵣ Cap p g b e a_src ∗
         a ↦ₐ raw ∗
         load_witness_res wit) ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hpca' Hdst Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit) HΦ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ□ revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm E pc_p pc_g pc_b pc_e pc_a None dst src imm wi
      (<[pc_a:=wi]> (<[a:=raw]> ∅)) _ _ ∅ DfracDiscarded wit DerefNoId
      with "[$HPC $Hmem $Hshadow $Hmap $Hwit //]").
    { exact Hinstr. }
    { exact Hvpc. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite Hnot_shadow.
      case_match; first done.
      case_match; first done.
      eexists. by simplify_map_eq. }
    { by rewrite !dom_insert_L. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & Hwit & _ & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv actual Hallow Hsh Hlookup Hactual Hinc ->
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh _ Hlookup _
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hlookup _
                      |p0 g0 b0 e0 ea0 z Hallow Htdev Hlookup _ _
                      |Hfail -> ->].
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite lookup_insert_ne // lookup_insert_eq in Hlookup.
      injection Hlookup as <-.
      rewrite linsert_reg_not_cnull //.
      apply incrementPC_Some_inv in Hinc
        as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
      injection HPC as <- <- <- <- <- <- <-.
      rewrite Hpca' in Hapc. injection Hapc as <-.
      rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; eauto.
      iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; auto.
      iApply "HΦ". iRight. iExists actual. by iFrame.
    - exfalso. by rewrite lookup_empty in Hlookup.
    - exfalso.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      by rewrite lookup_insert_ne // lookup_insert_eq in Hlookup.
    - exfalso.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      by rewrite lookup_insert_ne // lookup_insert_eq in Hlookup.
    - iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; first done.
      iDestruct (memMap_resource_2ne_dq with "Hmem") as "[Hi Ha]"; auto.
      iApply "HΦ". iLeft. by iFrame.
  Qed.

  Lemma wp_load_general Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs shadow sdq wit dw :
   decodeInstrW w.(lw) = CLoad r1 r2 0 →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (CLoad r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_mem_or_shadow r2 regs mem shadow →
   dom mem = dom dfracs →

   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
       load_witness_res wit ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' regs' retv, RET retv;
       ⌜ Load_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 0 lpc' regs' mem shadow wit dw retv⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
         load_witness_res wit ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Dregs Hmem_pc HaLoad Hdomeq.
    eapply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π
      r1 r2 0 w mem dfracs regs shadow sdq wit dw); eauto.
  Qed.

  Definition allow_load_map_or_true_imm r (imm : Z) (regs : LReg) (mem : LMem):=
    ∃ t p g b e a, read_reg_inr regs r t p g b e a ∧
      match (a + imm)%a with
      | None => True
      | Some ea => if decide (reg_allows_load_imm regs r imm p g b e a ea) then
        ∃ w, mem !! ea = Some w
      else True
      end.

  Lemma allow_load_implies_loadv_imm r2 imm mem regs p g b e a ea :
    allow_load_map_or_true_imm r2 imm regs mem →
    reg_allows_load_imm regs r2 imm p g b e a ea →
    ∃ loadv, mem !! ea = Some loadv.
  Proof.
    intros (t & p0 & g0 & b0 & e0 & a0 & Hsrc & Hmem) Hallow.
    pose proof Hallow as (Hreg & Hadd & Hra & Hwb).
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hreg) as (Hne & π & Hr2).
    rewrite /read_reg_inr Hr2 in Hsrc. simplify_eq.
    unfold reg_allows_load_imm in Hmem. rewrite Hadd in Hmem. case_decide as Hdec; first done.
    exfalso. by apply Hdec.
  Qed.

  Definition allow_load_map_or_true r (regs : LReg) (mem : LMem):=
    ∃ t p g b e a, read_reg_inr regs r t p g b e a ∧
      if decide (reg_allows_load regs r p g b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma allow_load_implies_loadv:
    ∀ (r2 : RegName) (mem0 : LMem) (r : LReg) (p : Perm)
      (g : Locality) (b e a : Addr),
      allow_load_map_or_true r2 r mem0
      → lw <$> r !!ₗ r2 = Some (Cap p g b e a)
      → readAllowed p = true
      → withinBounds b e a = true
      → ∃ (loadv : LWord),
          mem0 !! a = Some loadv.
  Proof.
    intros r2 mem0 r p g b e a HaLoad Hr2v Hra Hwb.
    destruct HaLoad as (t&?&?&?&?&?& Hrinr & Hmem).
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hr2v) as (Hne & π & Hr2).
    rewrite /read_reg_inr Hr2 in Hrinr. simplify_eq.
    case_decide as Hrega; first exact Hmem.
    exfalso. apply Hrega. by repeat split.
  Qed.

  Lemma mem_implies_loadv:
    ∀ (pc_a : Addr) (w w' : LWord) (a0 : Addr)
      (mem0 : LMem) (loadv : LWord),
      (if (a0 =? pc_a)%a
       then mem0 = <[pc_a:=w]> ∅
       else mem0 = <[pc_a:=w]> (<[a0:=w']> ∅))→
      mem0 !! a0 = Some loadv →
      loadv = (if (a0 =? pc_a)%a then w else w').
  Proof.
    intros pc_a w w' a0 mem0 loadv H4 H6.
    destruct (a0 =? pc_a)%a eqn:Heq; rewrite H4 in H6.
    + apply Z.eqb_eq, finz_to_z_eq in Heq; subst a0. by rewrite lookup_insert_eq in H6; simplify_eq.
    + apply Z.eqb_neq in Heq. rewrite lookup_insert_ne in H6; last congruence.
      by rewrite lookup_insert_eq in H6; simplify_eq.
  Qed.

  Lemma mem_eq_implies_allow_load_map_imm:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (w : LWord) p g b e a ea (imm : Z),
      mem = <[ea:=w]> ∅
      → lw <$> regs !!ₗ r2 = Some (Cap p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 w p g b e a ea imm Hmem Hrr2 Hadd.
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hrr2) as (Hne & π & Hr2).
    exists true,p,g,b,e,a; split.
    - by rewrite /read_reg_inr Hr2.
    - unfold reg_allows_load_imm. rewrite Hadd. case_decide; last done.
      exists w. subst mem. by rewrite lookup_insert_eq.
  Qed.

  Lemma mem_neq_implies_allow_load_map_imm:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (pc_a : Addr)
      (w w' : LWord) p g b e a ea (imm : Z),
      ea ≠ pc_a
      → mem = <[pc_a:=w]> (<[ea:=w']> ∅)
      → lw <$> regs !!ₗ r2 = Some (Cap p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a ea imm Hne' Hmem Hrr2 Hadd.
    pose proof (llookup_reg_cap _ _ _ _ _ _ _ _ Hrr2) as (Hne & π & Hr2).
    exists true,p,g,b,e,a; split.
    - by rewrite /read_reg_inr Hr2.
    - unfold reg_allows_load_imm. rewrite Hadd. case_decide; last done.
      exists w'. subst mem.
      rewrite lookup_insert_ne //. by rewrite lookup_insert_eq.
  Qed.

  Lemma mem_implies_allow_load_map_imm:
    ∀ (regs : LReg)(mem : LMem)(r2 : RegName) (pc_a : Addr)
      (w w' : LWord) p g b e a ea (imm : Z),
      (if (ea =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[ea:=w']> ∅))
      → lw <$> regs !!ₗ r2 = Some (Cap p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a ea imm H4 Hrr2 Hadd.
    destruct (ea =? pc_a)%a eqn:Heq.
    + apply Z.eqb_eq, finz_to_z_eq in Heq. subst ea. eapply mem_eq_implies_allow_load_map_imm; eauto.
    + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_load_map_imm; eauto; try congruence.
  Qed.

  Lemma decode_load_not_heap_cap_imm (w : LWord) dst src imm :
    decodeInstrW w.(lw) = CLoad dst src imm → is_heap_cap w.(lw) = false.
  Proof. destruct w as [ [] ?]; cbn; try discriminate; done. Qed.

  Lemma decode_load_not_heap_cap (w : LWord) dst src :
    decodeInstrW w.(lw) = CLoad dst src 0 → is_heap_cap w.(lw) = false.
  Proof. exact (decode_load_not_heap_cap_imm w dst src 0). Qed.

  (** A non-heap word loads exactly, without witness. *)
  Lemma load_post_not_heap_cap wit p (v v' : LWord) :
    is_heap_cap v.(lw) = false → load_post wit p v v' → v' = lload_word p v.
  Proof.
    rewrite /is_heap_cap. intros Hh (_ & Hnone & _). apply Hnone.
    by destruct (heap_cap_base v.(lw)).
  Qed.

  (* Loads of non-heap words: exact, without shadow ownership. The
     dereference witness [dw] is returned unchanged. *)
  Lemma wp_load_general_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs dw :
   decodeInstrW w.(lw) = CLoad r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (CLoad r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea loadv,
      reg_allows_load_imm regs r2 imm p g b e a ea → mem !! ea = Some loadv →
      is_shadow_address ea = false ∧ is_heap_cap loadv.(lw) = false) →
   dom mem = dom dfracs →

   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       deref_witness_res dw ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' regs' retv, RET retv;
       ⌜ ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
      regs' = <[r1 := lload_word p loadv]ₗ> regs) ∨
    (retv = FaultedV ∧ ∃ fail : Load_failure_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm mem ∅ LoadPlain dw, True))⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         deref_witness_res dw ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad Hordinary Hdomeq φ) "(HPC & Hmem & Hdw & Hmap) Hφ".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ□ revoked))%I as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 imm w mem dfracs
      regs ∅ DfracDiscarded LoadPlain dw with "[$HPC $Hmem $Hshadow $Hdw $Hmap]"); eauto.
    { intros p g b e ea Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [-> _].
      pose proof Hallow' as (_ & _ & _ & _).
      destruct (is_revoker_address ea); first done.
      destruct (is_time_device_address ea); eauto. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & Hdw & Hmap)".
    iApply "Hφ". iFrame. iPureIntro.
    destruct Hspec as [p g b e ea loadv loadv' Hallow Hsh Hl Hpost Hinc Hregs'
                      |p g b e ea heap_a revoked Hallow Hsh|p g b e ea Hallow Hrev Hinc|p g b e ea z Hallow Htdev Hnone _ _|Hfail].
    - left. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [_ Hh].
      rewrite (load_post_not_heap_cap _ _ _ _ Hh Hpost) in Hregs'.
      exists p, g, b, e, a, ea, loadv. done.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      destruct (Hordinary _ _ _ _ _ _ _ Hallow' Hl) as [Hsh' _]. congruence.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      all: try congruence.
    - exfalso. destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a Hallow'].
      destruct (allow_load_implies_loadv_imm _ _ _ _ _ _ _ _ _ _ HaLoad Hallow') as [loadv Hl].
      all: try congruence.
    - right. split; first done. by exists Hfail.
  Qed.

  Lemma wp_load_imm Ep
     pc_p pc_g pc_b pc_e pc_a pc_π
     r1 r2 (imm : Z) w mem regs dq :
   decodeInstrW w.(lw) = CLoad r1 r2 imm →
   isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (CLoad r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea loadv,
      reg_allows_load_imm regs r2 imm p g b e a ea → mem !! ea = Some loadv →
      is_shadow_address ea = false ∧ is_heap_cap loadv.(lw) = false) →
   {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
       (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ lpc' regs' retv, RET retv;
       ⌜ ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
      regs' = <[r1 := lload_word p loadv]ₗ> regs) ∨
    (retv = FaultedV ∧ ∃ fail : Load_failure_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm mem ∅ LoadPlain DerefNoId, True))⌝ ∗
         PC ↦ₚ lpc' ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "(HPC & Hmem & Hreg) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ DerefNoId
      with "[$HPC $Hmem $Hreg]");eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ? ?) "(?&?&Hmem&_&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  (* A load from ordinary memory without ownership of the revocation bit:
     the plain post (variant 1). *)
  Lemma wp_load_dfracs Ep pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w mem (dfracs : gmap Addr dfrac) regs :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_map_or_true src regs mem →
    (∀ p g b e a, reg_allows_load regs src p g b e a →
      is_shadow_address a = false) →
    dom mem = dom dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜(match retv with
    | NextIV => ∃ p g b e a loadv actualv,
        reg_allows_load regs src p g b e a ∧
        mem !! a = Some loadv ∧
        lload_heap (lload_word p loadv) actualv ∧
        incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
        regs' = <[dst := actualv]ₗ> regs
    | FaultedV => True
    | _ => False
    end)⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad Hnonshadow Hdom φ)
      "(HPC & Hmem & Hmap) Hφ".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ□ revoked))%I as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π dst src 0 w
      mem dfracs regs ∅ DfracDiscarded LoadPlain DerefNoId with "[$HPC $Hmem $Hshadow $Hmap]"); eauto.
    { intros p g b e a Hallow. rewrite (Hnonshadow _ _ _ _ _ Hallow).
      pose proof Hallow as (Hsrc & Hra & Hwb).
      destruct (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hsrc Hra Hwb) as [loadv Hl].
      destruct (is_revoker_address a); first done.
      destruct (is_time_device_address a); eauto. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & _ & Hmap)".
    iApply "Hφ". iFrame. iPureIntro.
    destruct Hspec as [p g b e a loadv loadv' Hallow Hsh Hl Hpost Hinc Hregs'
                      |p g b e a heap_a revoked Hallow Hsh|p g b e a Hallow Hrev Hnone Hinc|p g b e a z Hallow Htdev Hnone Hinc _|Hfail].
    - exists p, g, b, e, a, loadv, loadv'. by destruct Hpost.
    - exfalso. by rewrite (Hnonshadow _ _ _ _ _ Hallow) in Hsh.
    - exfalso. pose proof Hallow as (Hsrc & Hra & Hwb).
      destruct (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hsrc Hra Hwb) as [loadv Hl].
      all: try congruence.
    - exfalso. pose proof Hallow as (Hsrc & Hra & Hwb).
      destruct (allow_load_implies_loadv _ _ _ _ _ _ _ _ HaLoad Hsrc Hra Hwb) as [loadv Hl].
      all: try congruence.
    - done.
  Qed.

  (* The same, over memory owned with one fraction. *)
  Lemma wp_load Ep pc_p pc_g pc_b pc_e pc_a pc_π
    dst src w mem regs dq :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_map_or_true src regs mem →
    (∀ p g b e a, reg_allows_load regs src p g b e a →
      is_shadow_address a = false) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜(match retv with
    | NextIV => ∃ p g b e a loadv actualv,
        reg_allows_load regs src p g b e a ∧
        mem !! a = Some loadv ∧
        lload_heap (lload_word p loadv) actualv ∧
        incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
        regs' = <[dst := actualv]ₗ> regs
    | FaultedV => True
    | _ => False
    end)⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad Hnonshadow φ) "(HPC & Hmem & Hmap) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_dfracs with "[$HPC $Hmem $Hmap]"); eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iIntros "!>" (lpc' regs' retv) "(Hspec & HPC & Hmem & Hmap)".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply "Hφ". iFrame.
  Qed.

  #[local] Ltac load_fail_contra :=
    exfalso;
    lazymatch goal with Hfail : Load_failure_spec _ _ _ _ _ _ _ _ _ |- _ => destruct Hfail end;
    simplify_map_eq; cbn in *; try congruence;
    try (match goal with H : _ ≠ deref_id (deref_witness_of _ _) |- _ =>
           rewrite deref_id_witness_of in H; congruence end);
    try (match goal with H : ?π ≠ None, Hn : ∀ v : LWord, ?lhs = Some v → lprov v = None,
                         Hr : ?lhs = Some (_ @@? ?π) |- _ => by apply H, (Hn _ Hr) end);
    try (match goal with H : (_ + 0)%a = None |- _ => rewrite finz_add_0 in H; discriminate end);
    try (match goal with H : (_ + 0)%a = Some _ |- _ => rewrite finz_add_0 in H; simplify_eq end);
    try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end);
    try (match goal with H : load_post _ _ _ _ |- _ =>
           apply load_post_not_heap_cap in H;
           [subst | first [done | assumption | by rewrite /is_heap_cap /=] ] end);
    try (match goal with H : incrementPC _ = None |- _ =>
           eapply incrementPC_None_inv in H; [|first [reflexivity | by simplify_map_eq] ]; congruence end);
    try (match goal with H : incrementPC _ = None |- _ =>
           rewrite /incrementPC /incrementPC_gen in H; simplify_map_eq;
           rewrite /lload_word /lift_word /load_word /= in H;
           repeat (case_match; simplify_eq); congruence end);
    try (match goal with H : incrementPC _ = None |- _ =>
           rewrite /incrementPC /incrementPC_gen in H; simplify_map_eq;
           rewrite /lload_word /lift_word /load_word /= in H;
           match type of H with context [isDL ?p] => destruct (isDL p), (isDRO p) end;
           cbn in H; repeat case_match; congruence end);
    try (match goal with H : lw ?w = _, H' : is_cap (lw ?w) = false |- _ =>
           rewrite H in H'; discriminate end);
    try (match goal with H : ?t !! ?k = Some _, H' : ?t !! ?k = Some _ |- _ =>
           rewrite H in H'; simplify_eq; congruence end);
    try (match goal with H : is_revoker_address ?a = true,
                         H' : is_shadow_address ?a = true |- _ =>
           apply is_revoker_address_spec in H; subst;
           by rewrite revoker_not_shadow_address in H' end);
    try (match goal with H : is_time_device_address ?a = true,
                         H' : is_shadow_address ?a = true |- _ =>
           by rewrite (time_device_not_shadow_address _ H) in H' end).

  Lemma wp_load_success_notinstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) pc_a' dq dq' q :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ ea ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e a @@? πs
             ∗ ea ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hr1 Hr2 Φ)
      "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Hea & Hdw) HΦ".
    destruct (decide (ea = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Hpc_a Hea") as %<-.
      iApply (wp_load_next_2_pc (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hr2 $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
        | exact Hr1 | exact Hr2 | done | exact Hadd | exact Hra | exact Hwb |].
      iIntros "!> (HPC & Hpc_a & Hr1 & Hr2 & Hdw)". iApply "HΦ". iFrame.
    - iApply (wp_load_next_2 (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hr2 $Hea $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
        | exact Hr1 | exact Hr2 | done | exact Hadd | exact Hra | exact Hwb | exact Hne |].
      iIntros "!> (HPC & Hpc_a & Hr1 & Hr2 & Hea & Hdw)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_frominstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w'' p g b e a πs (imm : Z) pc_a' dq q :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e a @@? πs
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hr1 Hr2 Φ)
      "(>HPC & >Hpc_a & >Hr1 & >Hr2 & Hdw) HΦ".
    iApply (wp_load_next_2_pc (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hr2 $Hdw]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
      | exact Hr1 | exact Hr2 | done | exact Hadd | exact Hra | exact Hwb |].
    iIntros "!> (HPC & Hpc_a & Hr1 & Hr2 & Hdw)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_same_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' p g b e a ea πs (imm : Z) pc_a' dq dq' q :
    is_shadow_address ea = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ ea ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ ea ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hr1 Φ)
      "(>HPC & >Hpc_a & >Hr1 & >Hea & Hdw) HΦ".
    destruct (decide (ea = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Hpc_a Hea") as %<-.
      iApply (wp_load_next_1_pc (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
        | exact Hr1 | done | exact Hadd | exact Hra | exact Hwb |].
      iIntros "!> (HPC & Hpc_a & Hr1 & Hdw)". iApply "HΦ". iFrame.
    - iApply (wp_load_next_1 (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hea $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
        | exact Hr1 | done | exact Hadd | exact Hra | exact Hwb | exact Hne |].
      iIntros "!> (HPC & Hpc_a & Hr1 & Hea & Hdw)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_same_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e a πs (imm : Z) pc_a' dq q :
    is_shadow_address pc_a = false →
    is_heap_cap w.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ Cap p g b e a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hr1 Φ)
      "(>HPC & >Hpc_a & >Hr1 & Hdw) HΦ".
    iApply (wp_load_next_1_pc (W := deref_res πs q) with "[$HPC $Hpc_a $Hr1 $Hdw]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
      | exact Hr1 | done | exact Hadd | exact Hra | exact Hwb |].
    iIntros "!> (HPC & Hpc_a & Hr1 & Hdw)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_fail_tag_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Hsrc Htag.
    eapply wp_fault_step; [exact Hinstr | exact Hvpc |].
    by eapply CLoad_fault_untagged.
  Qed.

  Lemma wp_load_fail_not_ra_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a πs (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           r1 ↦ᵣ w'' ∗
           r2 ↦ᵣ Cap p g b e a @@? πs }}}.
  Proof.
    iIntros (Hdecode Hvpc Hra Hsrc φ) "(HPC & Hi & Hd & Hs) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hd $Hs $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H2 /= (decide_False _ _ Hsrc) /=.
      destruct s2; cbn; last done.
      destruct (a + imm)%a; cbn; [by rewrite Hra | done]. }
    iIntros "!> (HPC & Hd & Hs & Hi)".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail_not_withinbounds_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a ea πs (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e ea = false →
    (a + imm)%a = Some ea →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
    }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           r1 ↦ᵣ w'' ∗
           r2 ↦ᵣ Cap p g b e a @@? πs }}}.
  Proof.
    iIntros (Hdecode Hvpc Hwb Hadd Hsrc φ) "(HPC & Hi & Hd & Hs) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hd $Hs $Hi]"); [done | done | | ].
    { intros r sr m st td s1 s2 H1 H2.
      rewrite /exec /= /lookup_reg H2 /= (decide_False _ _ Hsrc) /=.
      destruct s2; cbn; last done.
      by rewrite Hadd /= Hwb andb_false_r. }
    iIntros "!> (HPC & Hd & Hs & Hi)".
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_fail_addr_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa p g b e a dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    wa.(lw) = Cap p g b e a →
    (a + imm)%a = None →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Hsrc Hwa Hadd.
    eapply wp_fault_step; [exact Hinstr | exact Hvpc |].
    by eapply CLoad_fault_address.
  Qed.

  Lemma wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src (imm : Z) regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    is_cap wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc Hsrc Hcap.
    eapply wp_fault_step; [exact Hinstr | exact Hvpc |].
    by eapply CLoad_fault_not_cap.
  Qed.

  Lemma wp_load_fail_not_cap_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' (wsrc : LWord) (imm : Z) dq :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc.(lw) = false ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ wsrc
    }}}
       Instr Executable @ E
       {{{ RET FaultedV;
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
           pc_a ↦ₐ{dq} w ∗
           r1 ↦ᵣ w'' ∗
           r2 ↦ᵣ wsrc }}}.
  Proof.
    iIntros (Hdecode Hvpc Hcap φ) "(>HPC & >Hi & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hne]".
    iApply (wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 imm _ (if decide (r2 = cnull) then lnull else wsrc) with "[$HPC $Hi $Hmap]"); eauto; simplify_map_eq; eauto.
    1,2: case_decide; done.
    iNext. iIntros "(HPC & Hi & Hmap)".
    iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ a ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e a @@? πs
             ∗ a ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (** Without shadow ownership, a load may fail or clear the loaded tag of a
      heap capability ([lload_heap]), in addition to the permission
      transformation performed by [load_word]. *)
  Lemma wp_load_preserve_or_clear E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' πs
    dst src (wi wd : LWord) p g b e a (raw : LWord) dq :
    readAllowed p = true ->
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = CLoad dst src 0 ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ Cap p g b e a @@? πs ∗ a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (⌜retv = FaultedV⌝ ∗
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
         pc_a ↦ₐ{dq} wi ∗
         dst ↦ᵣ wd ∗
         src ↦ᵣ Cap p g b e a @@? πs ∗
         a ↦ₐ raw) ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗
        ⌜lload_heap (lload_word p raw) actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗ pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ Cap p g b e a @@? πs ∗ a ↦ₐ raw }}}.
  Proof.
    iIntros (Hread Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iDestruct (memMap_resource_2ne_apply_dq with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load_step _ pc_p pc_g pc_b pc_e pc_a pc_π wi (CLoad dst src 0) dst src 0
              griotte_load_filter load_exact (<[pc_a := wi]> (<[a := raw]> ∅))
              (<[pc_a := dq]> (<[a := DfracOwn 1]> ∅)) with "[$HPC $Hmem $Hmap]");
      [exact Hinstr | apply CLoad_member | apply load_choice_exact | solve_mem_instr_ok
      | exact Hvpc | rewrite !dom_insert_L; set_solver
      | right; rewrite !dom_insert_L; set_solver | by simplify_map_eq
      | by rewrite !dom_insert_L | |].
    { intros p0 g0 b0 e0 a0 ea0 (Hsrc0 & Hadd0 & _).
      rewrite llookup_reg_not_cnull // lookup_insert_eq /= in Hsrc0. simplify_eq.
      rewrite finz_add_0 in Hadd0. simplify_eq.
      right. split; [by simplify_map_eq | done]. }
    iIntros "!>" (lpc' regs' retv) "(%Hres & HPC & Hmem & Hmap)".
    iDestruct (memMap_resource_2ne_dq _ _ _ _ _ _ Hpc_a with "Hmem") as "[Hi Ha]".
    destruct Hres as [ (-> & -> & ->)
                     | (p1 & g1 & b1 & e1 & a1 & ea1 & (Hsrc1 & Hadd1 & _) & -> & Hinc & Hcases) ].
    - (* A fault. *)
      iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
      iApply "Hφ". iLeft. by iFrame.
    - (* The cell, exactly. *)
      rewrite llookup_reg_not_cnull // lookup_insert_eq /= in Hsrc1. simplify_eq.
      rewrite finz_add_0 in Hadd1. simplify_eq.
      rewrite /incrementPC /incrementPC_gen /= Hpc' in Hinc. simplify_eq.
      destruct Hcases as [ (lv & v' & Hlv & Hpost & ->) | (_ & Hnone & _) ];
        last by simplify_map_eq.
      simplify_map_eq. rewrite /load_exact in Hpost. subst v'.
      rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
      iApply "Hφ". iRight. iExists (lload_word p1 lv).
      iSplitR; first done.
      iSplitR; first (iPureIntro; by left).
      iFrame.
  Qed.

  (** A load from a register file whose source is a valid, in-bounds
      read capability and whose PC can be incremented does not fail. *)
  Lemma load_failure_spec_impossible (regs : LReg) r1 r2 imm mem wit dw p g b e a ea pc_p pc_g
      pc_b pc_e pc_a pc_a' pc_π :
    lw <$> regs !!ₗ r2 = Some (Cap p g b e a) →
    (∀ v : LWord, regs !!ₗ r2 = Some v → v.(lprov) = deref_id dw) →
    (a + imm)%a = Some ea →
    readAllowed p = true → withinBounds b e ea = true →
    is_shadow_address ea = false →
    is_Some (mem !! ea) →
    (pc_a + 1)%a = Some pc_a' →
    Load_failure_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm mem ∅ wit dw →
    False.
  Proof.
    intros Hr2 Hid Hea Hra Hwb Hsh [v Hv] Hpca' Hfail.
    destruct Hfail as [w0 Hw0 Hcap|? ? ? ? ? H|? ? ? ? ? H H0|? ? ? ? ? ? H H0 H1
                      |? ? ? ? ? ? ? ? H H0 H1 H2 H3 Hinc|? ? ? ? ? ? ? ? H H0 H1|? ? ? ? ? ? H H0 H1 H2 Hinc
                      |? ? ? ? ? ? H H0 H1 H2 Hinc|? ? ? ? ? π H Hπ].
    all: try (by apply Hπ, (Hid _ H)).
    all: try (rewrite Hr2 in H; simplify_eq).
    - rewrite Hw0 /= in Hr2. injection Hr2 as Hw. rewrite Hw in Hcap. discriminate.
    - destruct H1; congruence.
    - rewrite /incrementPC /incrementPC_gen /= Hpca' in Hinc; discriminate.
  Qed.

  (** [wp_load_preserve_or_clear] for a source capability without an
      identifier: the load cannot fault. *)
  Lemma wp_load_preserve_or_clear_noid E pc_p pc_g pc_b pc_e pc_a pc_π pc_a'
    dst src (wi wd : LWord) p g b e a (raw : LWord) dq :
    readAllowed p = true ->
    is_shadow_address a = false ->
    decodeInstrW wi.(lw) = CLoad dst src 0 ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ Cap p g b e a ∗
        a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜lload_heap (lload_word p raw) actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ Cap p g b e a ∗
        a ↦ₐ raw }}}.
  Proof.
    iIntros (Hread Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    iApply (wp_load_next_2 (W := emp%I) with "[$HPC $Hi $Hdst $Hsrc $Ha]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpc'
      | exact Hdst | exact Hsrc | done | by rewrite finz_add_0 | exact Hread | exact Hbounds
      | done |].
    iIntros "!> (HPC & Hi & Hdst & Hsrc & Ha & _)".
    iApply ("Hφ" $! (lload_word p raw)). iSplitR; first (iPureIntro; by left). iFrame.
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w'' p g b e pc_a' dq πs q :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e pc_a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e pc_a @@? πs
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' dq dq' πs q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r1 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ a ↦ₐ{dq'} w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ a ↦ₐ{dq'} w'
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_same_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_frominstr E r1 pc_p pc_g pc_b pc_e pc_a pc_π w p g b e pc_a' dq πs q :
    is_shadow_address pc_a = false →
    decodeInstrW w.(lw) = CLoad r1 r1 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ Cap p g b e pc_a @@? πs
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ deref_res πs q }}}.
  Proof.
    intros.
    eapply wp_load_success_same_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)

  Lemma wp_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w'' p g b e a pc_a' πs dq q :
    is_shadow_address a = false →
    is_heap_cap w'.(lw) = false →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ Cap p g b e a @@? πs
          ∗ ▷ a ↦ₐ w'
          ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
             ∗ r1 ↦ᵣ lload_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ Cap p g b e a @@? πs
             ∗ a ↦ₐ w'
             ∗ deref_res πs q }}}.
  Proof.
    intros. eapply wp_load_success_notinstr; eauto.
  Qed.

  (* Non-revoked heap capabilities use the usual load_word transformation. *)

  (* Revocation clears the validity tag after the ordinary load transformation. *)
  Lemma wp_load_fail_tag E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src regs wa dq :
    decodeInstrW w.(lw) = CLoad dst src 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs !!ₗ src = Some wa →
    get_tag wa.(lw) = false →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FaultedV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    intros.
    eapply wp_load_fail_tag_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

End griotte_lang_rules.

Section load_witness_rules.
  Context `{MP: MachineParameters} `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (** Loading an identifier-less word that satisfies [load_exact_cond]
      (e.g. a heap root, which has authority) keeps it exactly: the fourth
      variant of the load rule. *)
  Lemma wp_load_success_exact E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_π w w' w''
      p g b e a pc_a' πs dq q :
    is_shadow_address a = false →
    w'.(lprov) = None →
    load_exact_cond w' →
    decodeInstrW w.(lw) = CLoad r1 r2 0 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    a ≠ pc_a →
    r1 ≠ cnull → r2 ≠ cnull → r1 ≠ r2 →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w'' ∗
        ▷ r2 ↦ᵣ Cap p g b e a @@? πs ∗
        ▷ a ↦ₐ w' ∗
        deref_res πs q }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ lload_word p w' ∗
        r2 ↦ᵣ Cap p g b e a @@? πs ∗
        a ↦ₐ w' ∗
        deref_res πs q }}}.
  Proof.
    iIntros (Hshadow Hπ Hexact Hinstr Hvpc Hra Hwb Hpca' Hne Hr1 Hr2 Hr12 φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha & Hdw) Hφ".
    iApply (wp_load_next_2 (W := deref_res πs q) with "[$HPC $Hi $Hr1 $Hr2 $Ha $Hdw]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_exact | by apply deref_res_live | exact Hvpc | exact Hpca'
      | exact Hr1 | exact Hr2 | done | by rewrite finz_add_0 | exact Hra | exact Hwb
      | exact Hne |].
    iIntros "!> (HPC & Hi & Hr1 & Hr2 & Ha & Hdw)". iApply "Hφ". iFrame.
  Qed.

  (** The general load rule with a status witness, over owned memory. *)
  Lemma wp_load_witness_imm Ep pc_p pc_g pc_b pc_e pc_a pc_π r1 r2 (imm : Z) w
      (mem : LMem) (regs : LReg) wit dw :
    decodeInstrW w.(lw) = CLoad r1 r2 imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (CLoad r1 r2 imm) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_mem_or_shadow_offset r2 imm regs mem ∅ →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        (▷ [∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        load_witness_res wit ∗
        deref_witness_res dw ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Load_spec (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r1 r2 imm lpc' regs' mem ∅ wit dw retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ w) ∗
        load_witness_res wit ∗
        deref_witness_res dw ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hmem_pc HaLoad φ) "(HPC & Hmem & Hwit & Hdw & Hreg) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ□ revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    iApply (wp_load_general_shadow_imm with "[$HPC $Hmem $Hshadow $Hwit $Hdw $Hreg]"); eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ? ?) "(?&?&Hmem&_&Hwit&Hdw&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  (** [wp_load_witness_imm] for a load from memory outside the shadow table,
      with one points-to per resource. *)
  Lemma wp_load_witness_imm_one E pc_p pc_g pc_b pc_e pc_a pc_a' dst src (imm : Z)
      (wi wd : LWord) p g b e a_src a (raw : LWord) wit :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}
      Instr Executable @ E
    {{{ retv, RET retv;
        (⌜retv = FaultedV⌝ ∗
         PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
         pc_a ↦ₐ wi ∗
         dst ↦ᵣ wd ∗
         src ↦ᵣ Cap p g b e a_src ∗
         a ↦ₐ raw) ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hpca' Hdst Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit) HΦ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load_witness_imm _ pc_p pc_g pc_b pc_e pc_a None dst src imm wi _ _ _ DerefNoId
      with "[$HPC $Hmem $Hwit $Hmap //]").
    { exact Hinstr. }
    { exact Hvpc. }
    { by rewrite !dom_insert; set_solver+. }
    { by simplify_map_eq. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite Hnot_shadow.
      destruct (is_revoker_address a); first done.
      destruct (is_time_device_address a); first done.
      eexists. by simplify_map_eq. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & _ & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv loadv' Hallow Hsh Hl Hpost Hinc ->
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hl
                      |p0 g0 b0 e0 ea0 z Hallow Htdev Hl _ _
                      |Hfail -> ->].
    2,3,4: exfalso;
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)];
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0');
      rewrite lookup_insert_eq in Hsrc0'; injection Hsrc0' as <- <- <- <- <- <-;
      rewrite Hea in Haddr; injection Haddr as <-;
      simplify_map_eq; congruence.
    2: { iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; first done.
         iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
         iApply "HΦ". iLeft. by iFrame. }
    destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
    rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
    rewrite Hea in Haddr. injection Haddr as <-.
    rewrite lookup_insert_ne // lookup_insert_eq in Hl. injection Hl as <-.
    rewrite linsert_reg_not_cnull //.
    apply incrementPC_Some_inv in Hinc
      as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
    injection HPC as <- <- <- <- <- <- <-.
    rewrite Hpca' in Hapc. injection Hapc as <-.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iApply "HΦ". iRight. iExists loadv'. by iFrame.
  Qed.


  (** [wp_load_witness_imm_one] for a readable source capability in bounds:
      the load cannot fault. *)
  Lemma wp_load_witness_imm_one_inbounds E pc_p pc_g pc_b pc_e pc_a pc_a' dst src
      (imm : Z) (wi wd : LWord) dq p g b e a_src a (raw : LWord) wit :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    src ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit) HΦ".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    iApply (wp_load_choice_next_2 (pc_π := None) (W := load_witness_res wit)
              with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_witness | by apply live_witness_no_id | exact Hvpc | exact Hpca'
      | exact Hdst | exact Hsrc | done | exact Hea | exact Hread | exact Hbounds | done |].
    iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & Hwit)".
    iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  (** [wp_load_witness_imm_one_inbounds] for a cell of any fraction: the
      loaded word is exact. *)
  Lemma wp_load_witness_imm_one_inbounds_dq E pc_p pc_g pc_b pc_e pc_a pc_a' dst src
      (imm : Z) (wi wd : LWord) dq dq' p g b e a_src a (raw : LWord) :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    src ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ{dq'} raw }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ lload_word p raw ∗
        src ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ{dq'} raw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) HΦ".
    destruct (decide (a = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Ha Hi") as %->.
      iApply (wp_load_next_2_pc (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hdst $Hsrc]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
        | exact Hdst | exact Hsrc | done | exact Hea | exact Hread | exact Hbounds |].
      iIntros "!> (HPC & Hi & Hdst & Hsrc & _)". iApply "HΦ". iFrame.
    - iApply (wp_load_next_2 (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hdst $Hsrc $Ha]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
        | exact Hdst | exact Hsrc | done | exact Hea | exact Hread | exact Hbounds
        | exact Hne |].
      iIntros "!> (HPC & Hi & Hdst & Hsrc & Ha & _)". iApply "HΦ". iFrame.
  Qed.

  (** A load of a cell of any fraction, through a capability with an
      identifier [π], under a status witness and a dereference witness of
      [π]. *)
  Lemma wp_load_witness_imm_one_inbounds_deref E pc_p pc_g pc_b pc_e pc_a pc_a'
      dst src (imm : Z) (wi wd : LWord) dq dq' p g b e a_src a π (raw : LWord) wit dw :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    π = deref_id dw →
    dst ≠ cnull →
    src ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ (Cap p g b e a_src @@? π) ∗
        a ↦ₐ{dq'} raw ∗
        load_witness_res wit ∗
        deref_witness_res dw }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ (Cap p g b e a_src @@? π) ∗
        a ↦ₐ{dq'} raw ∗
        load_witness_res wit ∗
        deref_witness_res dw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hπ Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit & Hdw) HΦ".
    destruct (decide (a = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Ha Hi") as %->.
      iApply (wp_load_choice_next_2_pc (pc_π := None)
                (W := (load_witness_res wit ∗ deref_witness_res dw)%I)
                with "[$HPC $Hi $Hdst $Hsrc $Hwit $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_sep_l, load_choice_witness
        | apply live_witness_sep_r, deref_witness_live; exact Hπ
        | exact Hvpc | exact Hpca' | exact Hdst | exact Hsrc | done | exact Hea | exact Hread
        | exact Hbounds |].
      iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & [Hwit Hdw])".
      iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
    - iApply (wp_load_choice_next_2 (pc_π := None)
                (W := (load_witness_res wit ∗ deref_witness_res dw)%I)
                with "[$HPC $Hi $Hdst $Hsrc $Ha $Hwit $Hdw]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_sep_l, load_choice_witness
        | apply live_witness_sep_r, deref_witness_live; exact Hπ
        | exact Hvpc | exact Hpca' | exact Hdst | exact Hsrc | done | exact Hea | exact Hread
        | exact Hbounds | exact Hne |].
      iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hdst & Hsrc & Ha & [Hwit Hdw])".
      iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  (** [wp_load_witness_imm_one_inbounds] when the destination is the
      source register. *)
  Lemma wp_load_witness_imm_same_inbounds E pc_p pc_g pc_b pc_e pc_a pc_a' r
      (imm : Z) (wi : LWord) dq p g b e a_src a (raw : LWord) wit :
    decodeInstrW wi.(lw) = CLoad r r imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ actual ∗
        a ↦ₐ raw ∗
        load_witness_res wit }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hr Φ)
      "(HPC & Hi & Hsrc & Ha & Hwit) HΦ".
    iDestruct (pointsto_ne with "Ha Hi") as %Hne.
    iApply (wp_load_choice_next_1 (pc_π := None) (W := load_witness_res wit)
              with "[$HPC $Hi $Hsrc $Ha $Hwit]");
      [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
      | apply load_choice_witness | by apply live_witness_no_id | exact Hvpc | exact Hpca'
      | exact Hr | done | exact Hea | exact Hread | exact Hbounds | done |].
    iIntros "!>" (actual) "(%Hpost & HPC & Hi & Hsrc & Ha & Hwit)".
    iApply ("HΦ" $! actual). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  (** [wp_load_witness_imm_one_inbounds_dq] when the destination is the
      source register: the loaded word is exact. *)
  Lemma wp_load_witness_imm_same_inbounds_dq E pc_p pc_g pc_b pc_e pc_a pc_a' r
      (imm : Z) (wi : LWord) dq dq' p g b e a_src a (raw : LWord) :
    decodeInstrW wi.(lw) = CLoad r r imm →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    {{{ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ Cap p g b e a_src ∗
        a ↦ₐ{dq'} raw }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        r ↦ᵣ lload_word p raw ∗
        a ↦ₐ{dq'} raw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hr Φ)
      "(HPC & Hi & Hsrc & Ha) HΦ".
    destruct (decide (a = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Ha Hi") as %->.
      iApply (wp_load_next_1_pc (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hsrc]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
        | exact Hr | done | exact Hea | exact Hread | exact Hbounds |].
      iIntros "!> (HPC & Hi & Hsrc & _)". iApply "HΦ". iFrame.
    - iApply (wp_load_next_1 (pc_π := None) (W := emp%I) with "[$HPC $Hi $Hsrc $Ha]");
        [exact Hinstr | solve_mem_instr_ok | apply CLoad_member | apply CLoad_agree
        | apply load_choice_exact | by apply live_witness_no_id | exact Hvpc | exact Hpca'
        | exact Hr | done | exact Hea | exact Hread | exact Hbounds | exact Hne |].
      iIntros "!> (HPC & Hi & Hsrc & Ha & _)". iApply "HΦ". iFrame.
  Qed.

End load_witness_rules.
