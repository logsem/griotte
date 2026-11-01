From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
Import core_link.

(** The MIE after a jump through the source [rsrc] of [regs], from MIE [b]:
    a sentry that sets the interrupt status sets MIE. *)
Definition jalr_mie (regs : LReg) (rsrc : RegName) (b : InterruptStatus) : InterruptStatus :=
  match regs !!ₗ rsrc with
  | Some wsrc => default b (jalr_target_mie wsrc.(lw))
  | None => b
  end.

(** A jump that is neither a call nor a return reads and writes no MIE: the
    target is unsealed or an inheriting sentry. *)
Lemma jalr_target_ok_keep_mie rdst rsrc w :
  rdst ≠ cra →
  ¬ (rdst = cnull ∧ rsrc = cra) →
  jalr_target_ok rdst rsrc w = true →
  jalr_target_mie w = None.
Proof.
  intros Hcra Hret Hok. apply andb_prop in Hok as [ [_ Hs]%andb_prop _].
  destruct w as [ | | k ? ? ? ? ? ? | ]; try done.
  rewrite /jalr_sealing_ok in Hs.
  rewrite decide_False // decide_False // in Hs.
  apply bool_decide_eq_true in Hs as ->. done.
Qed.

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
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.


  (* The new PC is the source word with its identifier; the link is built
     from the PC and takes the PC's identifier. A [cnull] destination drops
     the link. The link's kind depends on MIE [mie] before the jump. *)
  Inductive Jalr_spec (regs : LReg) pc_p pc_g pc_b pc_e pc_a pc_π (rdst rsrc: RegName)
      (mie : InterruptStatus) :
    LWord → LReg → griotte_lang.val → Prop :=
  | Jalr_spec_success regs' pc_a' wsrc :
    regs !!ₗ rsrc = Some wsrc ->
    jalr_target_ok rdst rsrc wsrc.(lw) = true ->
    (pc_a + 1)%a = Some pc_a' ->
    regs' = (if decide (rdst = cnull) then regs
             else <[rdst := jalr_link rdst mie true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ]ₗ> regs) →
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc mie (lupdatePcPerm wsrc) regs' NextIV
  | Jalr_spec_failure_target wsrc :
    regs !!ₗ rsrc = Some wsrc ->
    jalr_target_ok rdst rsrc wsrc.(lw) = false ->
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc mie
      (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs FaultedV
  | Jalr_spec_failure :
    (pc_a + 1)%a = None ->
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc mie
      (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs FaultedV.

  (** A jump writes MIE through a sentry that sets the interrupt status:
      the premise [link_transfer_si (mie_move b (jalr_mie regs rsrc b)) T1 T2]
      gives [T1] up for [T2] with the link on success; [T1] comes back on a
      fault. *)
  Lemma wp_Jalr_link Ep pc_p pc_g pc_b pc_e pc_a pc_π w rdst rsrc regs (b : InterruptStatus) dq
      (T1 T2 : iProp Σ) :
    decodeInstrW w.(lw) = Jalr rdst rsrc ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jalr rdst rsrc) ⊆ dom regs →
    link_transfer_si (mie_move b (jalr_mie regs rsrc b)) T1 T2 →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ MIE ↦ₜ b ∗
        ▷ T1 }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc b lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        (⌜retv = NextIV⌝ ∗ MIE ↦ₜ jalr_mie regs rsrc b ∗ T2 ∨
         ⌜retv = FaultedV⌝ ∗ MIE ↦ₜ b ∗ T1) }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Htr φ) "(>HPC & >Hpc_a & >Hmap & >Hmie & HT) Hφ".
    iApply (wp_instr_step_link with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    iDestruct (sys_interp_mie_agree with "Hsr Hmie") as %<-.
    destruct (erasure_mie_st _ _ _ _ _ _ _ Her) as [Hmie_st _].
    assert (∃ vst, ls_join lsreg !! mstatus = Some vst) as [vst Hvst'].
    { eexists. apply ls_join_mstatus. }
    assert (mie_of (get_a vst.(lw)) = ls_mie lsreg ∧ mpie_of (get_a vst.(lw)) = ls_mpie lsreg)
      as [Hvmie Hvmpie].
    { rewrite ls_join_mstatus in Hvst'. injection Hvst' as <-.
      by rewrite /= mie_of_mstatus_enc mpie_of_mstatus_enc. }
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of, operands_of in Hri, Dregs.
    destruct (Hri rsrc) as [wsrc [H'rsrc _] ]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'rsrc) as (s & Hrsrc & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs H'rsrc) as Hoksrc.
    pose proof (er_pc_word _ _ _ _ _ _ _ Her) as HokPC.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    assert (get_a wst = get_a vst.(lw)) as Hast.
    { destruct (reg_phys_and_tag _ _ _ Hrelst) as [s' ->]. apply get_a_and_tag. }
    rewrite /exec /= Hrsrc /= jalr_target_checks in Hstep.
    (* The target checks fail on the physical copy exactly when they fail on
       the logical word: a word that passes them is executable, hence
       exact. *)
    destruct (jalr_target_ok rdst rsrc wsrc.(lw)) eqn:Hok; cycle 1.
    { rewrite jalr_target_ok_and_tag Hok andb_false_r in Hstep.
      first [injection Hstep as <- <- | simplify_eq].
      iApply (instr_close_link_kept with "Hlink").
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
      iIntros "HPC Hmap". iApply "Hφ". iFrame "HPC Hpc_a Hmap". iSplit.
      - iPureIntro. by eapply Jalr_spec_failure_target.
      - iRight. by iFrame. }
    assert (and_tag s wsrc.(lw) = wsrc.(lw)) as Heq.
    { pose proof Hok as Hok'. apply andb_prop in Hok' as [ [Ht _]%andb_prop Hx].
      by apply (reg_phys_executable R C). }
    rewrite Heq in Hstep Hrel. rewrite Hok Hwst /= in Hstep.
    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; cbn in Hstep.
    2: { first [injection Hstep as <- <- | simplify_eq].
         iApply (instr_close_link_kept with "Hlink").
         iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); [done|].
         iIntros "HPC Hmap". iApply "Hφ". iFrame "HPC Hpc_a Hmap". iSplit.
         - iPureIntro. by constructor.
         - iRight. by iFrame. }
    rewrite Hast in Hstep.
    injection Hstep as <- <-.
    rewrite Hvmie.
    set (link := jalr_link rdst (ls_mie lsreg) true pc_p pc_g pc_b pc_e pc_a').
    pose proof (erasure_pc_no_id _ _ _ _ _ _ _ Her Hvpc) as Hπ. cbn in Hπ.
    assert (reg_word_ok R C (link @@? pc_π)) as Hoklink.
    { rewrite /link /jalr_link. case_decide;
        (apply (reg_word_ok_derive _ _ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π));
         [by left|done|done|done]). }
    assert (reg_phys R (link @@? pc_π) link) as Hrellink by (by apply reg_phys_no_id).
    (* mstatus: a sentry that sets the interrupt status writes MIE. *)
    destruct (jalr_mstatus wsrc.(lw) (get_a vst.(lw))) as [z|] eqn:Hmie.
    - pose proof Hmie as Hz. rewrite /jalr_mstatus in Hz.
      apply fmap_Some in Hz as (mie' & Htm & Hzeq). rewrite Hvmpie in Hzeq.
      assert (jalr_mie regs rsrc (ls_mie lsreg) = mie') as Hjm.
      { by rewrite /jalr_mie H'rsrc Htm. }
      pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ _ _ _ mstatus
                    (lword_of_word (WInt (mstatus_enc mie' (ls_mpie lsreg))))
                    (WInt z) Her) as Her1.
      specialize (Her1 ltac:(apply reg_word_ok_int) ltac:(by intros) ltac:(by intros)
                    ltac:(rewrite Hzeq; apply reg_phys_lword_of_word)).
      rewrite -ls_join_set_mstatus in Her1.
      iMod (sys_interp_set_mie _ _ mie' with "Hsr Hmie") as "[Hsr Hmie]".
      iApply (instr_close_link_transfer _ _ _ _
                (Cap pc_p pc_g pc_b pc_e pc_a, r, <[mstatus := WInt z]> sr, m, st)
                with "Hlink HT"); [exact Htr | |].
      { intros Hk. eapply mie_move_kept; last exact Hk. split_and!.
        - done.
        - by rewrite Hjm /mie_st /= lookup_insert_eq Hzeq /= mie_of_mstatus_enc.
        - by rewrite /= lookup_insert_ne. }
      destruct (decide (rdst = cnull)) as [Hnull | Hnull].
      + iApply (instr_close_set_pc (Cap pc_p pc_g pc_b pc_e pc_a) r
                  (<[mstatus := WInt z]> sr) m st _ lreg _ lmem R C _ (lupdatePcPerm wsrc)
                  with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
        * exact Her1.
        * by apply reg_word_ok_lupdatePcPerm.
        * by apply reg_phys_lupdatePcPerm.
        * by eapply jalr_target_ok_pc_ok.
        * iIntros "HPC Hmap HT". iApply "Hφ". iFrame "HPC Hpc_a Hmap". iSplit.
          -- iPureIntro. eapply Jalr_spec_success; [exact H'rsrc | exact Hok | exact Hpca' |].
             by rewrite decide_True.
          -- iLeft. rewrite Hjm. by iFrame.
      + iApply (instr_close_reg_set_pc (Cap pc_p pc_g pc_b pc_e pc_a) r
                  (<[mstatus := WInt z]> sr) m st _ lreg _ lmem R C _ rdst
                  (link @@? pc_π) link (lupdatePcPerm wsrc)
                  with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
        * exact Her1.
        * right. apply Dregs. set_solver.
        * exact Hoklink.
        * exact Hrellink.
        * by apply reg_word_ok_lupdatePcPerm.
        * by apply reg_phys_lupdatePcPerm.
        * by eapply jalr_target_ok_pc_ok.
        * iIntros "HPC Hmap HT". iApply "Hφ". iFrame "HPC Hpc_a Hmap". iSplit.
          -- iPureIntro. eapply Jalr_spec_success; [exact H'rsrc | exact Hok | exact Hpca' |].
             by rewrite decide_False.
          -- iLeft. rewrite Hjm. by iFrame.
    - assert (jalr_mie regs rsrc (ls_mie lsreg) = ls_mie lsreg) as Hjm.
      { rewrite /jalr_mstatus fmap_None in Hmie. by rewrite /jalr_mie H'rsrc Hmie. }
      iApply (instr_close_link_transfer _ _ _ _ (Cap pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)
                with "Hlink HT"); [exact Htr | |].
      { intros Hk. eapply mie_move_kept; last exact Hk.
        split_and!; [done | by rewrite Hjm | done]. }
      destruct (decide (rdst = cnull)) as [Hnull | Hnull].
      + iApply (instr_close_set_pc _ _ _ _ _ _ _ _ _ _ _ _ (lupdatePcPerm wsrc)
                  with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
        * exact Her.
        * by apply reg_word_ok_lupdatePcPerm.
        * by apply reg_phys_lupdatePcPerm.
        * by eapply jalr_target_ok_pc_ok.
        * iIntros "HPC Hmap HT". iApply "Hφ". iFrame "HPC Hpc_a Hmap". iSplit.
          -- iPureIntro. eapply Jalr_spec_success; [exact H'rsrc | exact Hok | exact Hpca' |].
             by rewrite decide_True.
          -- iLeft. rewrite Hjm. by iFrame.
      + iApply (instr_close_reg_set_pc _ _ _ _ _ _ _ _ _ _ _ _ rdst
                  (link @@? pc_π) link (lupdatePcPerm wsrc)
                  with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
        * exact Her.
        * right. apply Dregs. set_solver.
        * exact Hoklink.
        * exact Hrellink.
        * by apply reg_word_ok_lupdatePcPerm.
        * by apply reg_phys_lupdatePcPerm.
        * by eapply jalr_target_ok_pc_ok.
        * iIntros "HPC Hmap HT". iApply "Hφ". iFrame "HPC Hpc_a Hmap". iSplit.
          -- iPureIntro. eapply Jalr_spec_success; [exact H'rsrc | exact Hok | exact Hpca' |].
             by rewrite decide_False.
          -- iLeft. rewrite Hjm. by iFrame.
  Qed.

  (** A jump that is neither a call nor a return: it reads and writes no MIE,
      and the link (if any) is the unsealed PC, for any MIE. *)
  Lemma wp_Jalr_keep Ep pc_p pc_g pc_b pc_e pc_a pc_π w rdst rsrc regs dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jalr rdst rsrc) ⊆ dom regs →
    rdst ≠ cra →
    ¬ (rdst = cnull ∧ rsrc = cra) →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ ∀ mie, Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc mie lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hcra Hret φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step_link with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    assert (∃ vst, ls_join lsreg !! mstatus = Some vst) as [vst Hvst'].
    { eexists. apply ls_join_mstatus. }
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of, operands_of in Hri, Dregs.
    destruct (Hri rsrc) as [wsrc [H'rsrc _] ]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'rsrc) as (s & Hrsrc & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs H'rsrc) as Hoksrc.
    pose proof (er_pc_word _ _ _ _ _ _ _ Her) as HokPC.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hvst') as (wst & Hwst & Hrelst).
    rewrite /exec /= Hrsrc /= jalr_target_checks in Hstep.
    destruct (jalr_target_ok rdst rsrc wsrc.(lw)) eqn:Hok; cycle 1.
    { rewrite jalr_target_ok_and_tag Hok andb_false_r in Hstep.
      instr_fail Hstep. intros mie. by eapply Jalr_spec_failure_target. }
    assert (and_tag s wsrc.(lw) = wsrc.(lw)) as Heq.
    { pose proof Hok as Hok'. apply andb_prop in Hok' as [ [Ht _]%andb_prop Hx].
      by apply (reg_phys_executable R C). }
    rewrite Heq in Hstep Hrel. rewrite Hok Hwst /= in Hstep.
    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; cbn in Hstep.
    2: { instr_fail Hstep. intros mie. by constructor. }
    injection Hstep as <- <-.
    assert (jalr_mstatus wsrc.(lw) (get_a wst) = None) as Hnone.
    { by rewrite /jalr_mstatus (jalr_target_ok_keep_mie rdst rsrc). }
    rewrite Hnone.
    (* The link does not depend on MIE. *)
    assert (∀ mie mie', jalr_link rdst mie true pc_p pc_g pc_b pc_e pc_a' =
                        jalr_link rdst mie' true pc_p pc_g pc_b pc_e pc_a') as Hlink_mie.
    { intros mie mie'. by rewrite /jalr_link !decide_False. }
    set (link := jalr_link rdst (mie_of (get_a wst)) true pc_p pc_g pc_b pc_e pc_a').
    pose proof (erasure_pc_no_id _ _ _ _ _ _ _ Her Hvpc) as Hπ. cbn in Hπ.
    assert (reg_word_ok R C (link @@? pc_π)) as Hoklink.
    { rewrite /link /jalr_link. case_decide;
        (apply (reg_word_ok_derive _ _ (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π));
         [by left|done|done|done]). }
    assert (reg_phys R (link @@? pc_π) link) as Hrellink by (by apply reg_phys_no_id).
    iApply (instr_close_link_kept with "Hlink").
    destruct (decide (rdst = cnull)) as [Hnull | Hnull].
    - iApply (instr_close_set_pc _ _ _ _ _ _ _ _ _ _ _ _ (lupdatePcPerm wsrc)
                with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
      + exact Her.
      + by apply reg_word_ok_lupdatePcPerm.
      + by apply reg_phys_lupdatePcPerm.
      + by eapply jalr_target_ok_pc_ok.
      + iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro. intros mie.
        eapply Jalr_spec_success; [exact H'rsrc | exact Hok | exact Hpca' |].
        by rewrite decide_True.
    - iApply (instr_close_reg_set_pc _ _ _ _ _ _ _ _ _ _ _ _ rdst
                (link @@? pc_π) link (lupdatePcPerm wsrc)
                with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
      + exact Her.
      + right. apply Dregs. set_solver.
      + exact Hoklink.
      + exact Hrellink.
      + by apply reg_word_ok_lupdatePcPerm.
      + by apply reg_phys_lupdatePcPerm.
      + by eapply jalr_target_ok_pc_ok.
      + iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro. intros mie.
        eapply Jalr_spec_success; [exact H'rsrc | exact Hok | exact Hpca' |].
        by rewrite decide_False // /link (Hlink_mie _ mie).
  Qed.

  (** A jump whose destination is neither [cnull] nor [cra]: the target is
      unsealed or an inheriting sentry, and the link is the unsealed PC. *)
  Lemma wp_jalr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc rdst wdst dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok rdst rsrc wsrc.(lw) = true →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->
    rdst ≠ cra ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
          ∗ rdst ↦ᵣ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hcnull' Hcra ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "Hrsrc Hrdst") as "[Hmap %]".
    iApply (wp_Jalr_keep with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    { by intros [? _]. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    specialize (Hspec InterruptDisabled).
   destruct Hspec as [ ? ? ? | ? Hlook Hfail | Hfail ]; subst.
   { rewrite decide_False // /jalr_link decide_False //.
     iApply "Hφ". iFrame. simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  (** [jalr r r] with [r] neither [cnull] nor [cra]. *)
  Lemma wp_jalr_success_rdst E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wdst rdst dq :
    decodeInstrW w.(lw) = Jalr rdst rdst →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok rdst rdst wdst.(lw) = true →
    rdst ≠ cnull ->
    rdst ≠ cra ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wdst
          ∗ pc_a ↦ₐ{dq} w
          ∗ rdst ↦ᵣ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hcra ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_1 with "Hrdst") as "Hmap".
    iApply (wp_Jalr_keep with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    { by intros [? _]. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    specialize (Hspec InterruptDisabled).
   destruct Hspec as [ ? ? ? | ? Hlook Hfail | Hfail ]; subst.
   { rewrite decide_False // /jalr_link decide_False //.
     iApply "Hφ". iFrame.
     simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  (** A target that fails the checks makes Jalr fail, before it writes the
      PC or the link register. *)
  Lemma wp_jalr_fail_target E pc_p pc_g pc_b pc_e pc_a pc_π w rsrc wsrc rdst wdst dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok rdst rsrc wsrc.(lw) = false →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET FaultedV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
          ∗ rdst ↦ᵣ wdst
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iApply (wp_instr_faulted_2 with "[$HPC $Hrsrc $Hrdst $Hpc_a]"); [done | done | | ].
    - intros r sr m st s1 s2 Hr1 _.
      rewrite /exec /= /lookup_reg /=.
      destruct (decide (rsrc = cnull)) as [->|Hne]; first done.
      rewrite Hr1 /= jalr_target_checks.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hrsrc & Hrdst & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jalr_fail_target_cnull E pc_p pc_g pc_b pc_e pc_a pc_π w rsrc wsrc dq :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok cnull rsrc wsrc.(lw) = false →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
    }}}
      Instr Executable @ E
      {{{ RET FaultedV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hrsrc) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hrsrc $Hpc_a]"); [done | done | | ].
    - intros rf sr m st s1 Hr1.
      rewrite /exec /= /lookup_reg /=.
      destruct (decide (rsrc = cnull)) as [->|Hne]; first done.
      rewrite Hr1 /= jalr_target_checks.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hrsrc & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jalr_fail_target_same E pc_p pc_g pc_b pc_e pc_a pc_π w r wr dq :
    decodeInstrW w.(lw) = Jalr r r →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok r r wr.(lw) = false →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r ↦ᵣ wr
    }}}
      Instr Executable @ E
      {{{ RET FaultedV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r ↦ᵣ wr
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iApply (wp_instr_faulted_1 with "[$HPC $Hr $Hpc_a]"); [done | done | | ].
    - intros rf sr m st s1 Hr1.
      rewrite /exec /= /lookup_reg /=.
      destruct (decide (r = cnull)) as [->|Hne]; first done.
      rewrite Hr1 /= jalr_target_checks.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hr & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

  (** A call ([rdst = cra]) moves the posture of the thread to the one the
      target sets, and the return sentry restores the posture of the
      caller. *)
  Lemma wp_jalr_success_call_posture `{CR : !CritRoute Σ th CL} E pc_p pc_g pc_b pc_e pc_a pc_π
      pc_a' w rsrc wsrc wcra (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = Jalr cra rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cra rsrc wsrc.(lw) = true →
    rsrc ≠ cnull ->
    rsrc ≠ cra ->
    route_pre th b →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rsrc ↦ᵣ wsrc ∗
        ▷ cra ↦ᵣ wcra ∗
        ▷ MIE ↦ₜ b ∗
        ▷ held b
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc ∗
          pc_a ↦ₐ{dq} w ∗
          rsrc ↦ᵣ wsrc ∗
          cra ↦ᵣ Sentry (ret_kind b) pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          MIE ↦ₜ default b (jalr_target_mie wsrc.(lw)) ∗
          held (default b (jalr_target_mie wsrc.(lw)))
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hcra Hpre ϕ)
      "(>HPC & >Hpc_a & >Hrsrc & >Hrdst & >Hmie & Hheld) Hφ".
    iDestruct (map_of_regs_2 with "Hrsrc Hrdst") as "[Hmap %]".
    assert (jalr_mie (<[rsrc:=wsrc]> (<[cra:=wcra]> ∅)) rsrc b =
              default b (jalr_target_mie wsrc.(lw))) as Hjm.
    { rewrite /jalr_mie llookup_reg_not_cnull //; by simplify_map_eq. }
    iApply (wp_Jalr_link _ _ _ _ _ _ _ _ _ _ _ _ _ (held b)
              (held (jalr_mie (<[rsrc:=wsrc]> (<[cra:=wcra]> ∅)) rsrc b))
             with "[$HPC $Hmap $Hpc_a $Hmie $Hheld]");
      [done | done | rewrite /regs_of /operands_of /regs_of_argument; set_solver
      | by apply link_transfer_si_route |].
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap & HT)".
    destruct Hspec as [ ? ? ? | ? Hlook Hfail | Hfail ]; subst.
    { destruct (decide (cra = cnull)) as [Hc|_]; first done.
      rewrite /jalr_link. destruct (decide (cra = cra)) as [_|Hc]; last done.
      iDestruct "HT" as "[ (_ & Hmie & HT) | [%Hc _] ]"; last done.
      rewrite Hjm.
      iApply "Hφ". iFrame. simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { simplify_lmap_eq. congruence. }
    { congruence. }
  Qed.

  (** [jalr cra cra]: a call through [cra] itself moves the posture as
      [wp_jalr_success_call_posture]. *)
  Lemma wp_jalr_success_call_same_posture `{CR : !CritRoute Σ th CL} E pc_p pc_g pc_b pc_e pc_a
      pc_π pc_a' w wcra (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = Jalr cra cra →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cra cra wcra.(lw) = true →
    route_pre th b →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ cra ↦ᵣ wcra ∗
        ▷ MIE ↦ₜ b ∗
        ▷ held b
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wcra ∗
          pc_a ↦ₐ{dq} w ∗
          cra ↦ᵣ Sentry (ret_kind b) pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          MIE ↦ₜ default b (jalr_target_mie wcra.(lw)) ∗
          held (default b (jalr_target_mie wcra.(lw)))
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hpre ϕ) "(>HPC & >Hpc_a & >Hrdst & >Hmie & Hheld) Hφ".
    iDestruct (map_of_regs_1 with "Hrdst") as "Hmap".
    assert (jalr_mie {[cra := wcra]} cra b = default b (jalr_target_mie wcra.(lw))) as Hjm.
    { rewrite /jalr_mie llookup_reg_not_cnull //; by simplify_map_eq. }
    iApply (wp_Jalr_link _ _ _ _ _ _ _ _ _ _ _ _ _ (held b)
              (held (jalr_mie {[cra := wcra]} cra b))
             with "[$HPC $Hmap $Hpc_a $Hmie $Hheld]");
      [done | done | rewrite /regs_of /operands_of /regs_of_argument; set_solver
      | by apply link_transfer_si_route |].
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap & HT)".
    destruct Hspec as [ ? ? ? | ? Hlook Hfail | Hfail ]; subst.
    { destruct (decide (cra = cnull)) as [Hc|_]; first done.
      rewrite /jalr_link. destruct (decide (cra = cra)) as [_|Hc]; last done.
      iDestruct "HT" as "[ (_ & Hmie & HT) | [%Hc _] ]"; last done.
      rewrite Hjm.
      iApply "Hφ". iFrame. simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { simplify_lmap_eq. congruence. }
    { congruence. }
  Qed.
  (** A return ([jalr cnull cra]) moves the posture of the thread to the one
      the return sentry restores; a plain jump keeps it. *)
  Lemma wp_jalr_success_cnull_posture `{CR : !CritRoute Σ th CL} E pc_p pc_g pc_b pc_e pc_a pc_π
      pc_a' w rsrc wsrc (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cnull rsrc wsrc.(lw) = true →
    rsrc ≠ cnull ->
    route_pre th b →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rsrc ↦ᵣ wsrc ∗
        ▷ MIE ↦ₜ b ∗
        ▷ held b
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc ∗
          pc_a ↦ₐ{dq} w ∗
          rsrc ↦ᵣ wsrc ∗
          MIE ↦ₜ default b (jalr_target_mie wsrc.(lw)) ∗
          held (default b (jalr_target_mie wsrc.(lw)))
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hpre ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hmie & Hheld) Hφ".
    iDestruct (map_of_regs_1 with "Hrsrc") as "Hmap".
    assert (jalr_mie {[rsrc := wsrc]} rsrc b = default b (jalr_target_mie wsrc.(lw))) as Hjm.
    { rewrite /jalr_mie llookup_reg_not_cnull //; by simplify_map_eq. }
    iApply (wp_Jalr_link _ _ _ _ _ _ _ _ _ _ _ _ _ (held b)
              (held (jalr_mie {[rsrc := wsrc]} rsrc b))
             with "[$HPC $Hmap $Hpc_a $Hmie $Hheld]");
      [done | done | rewrite /regs_of /operands_of /regs_of_argument; set_solver
      | by apply link_transfer_si_route |].
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap & HT)".
    destruct Hspec as [ ? ? ? | ? Hlook Hfail | Hfail ]; subst.
    { destruct (decide (cnull = cnull)) as [_|Hc]; last done.
      iDestruct "HT" as "[ (_ & Hmie & HT) | [%Hc _] ]"; last done.
      rewrite Hjm. simplify_lmap_eq.
      iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap"). }
    { simplify_lmap_eq. congruence. }
    { congruence. }
  Qed.

End griotte_lang_rules.

(** The core rules of the jumps that read or write MIE: a call, whose link
    restores the MIE of the caller, and a return or a jump through a sentry
    that sets MIE. *)
Section griotte_lang_rules_core.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread}.
  Implicit Types w : LWord.

  Lemma wp_Jalr Ep pc_p pc_g pc_b pc_e pc_a pc_π w rdst rsrc regs (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc ->
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jalr rdst rsrc) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ MIE ↦ₜ b }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc b lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        (⌜retv = NextIV⌝ ∗ MIE ↦ₜ jalr_mie regs rsrc b ∨ ⌜retv = FaultedV⌝ ∗ MIE ↦ₜ b) }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap & >Hmie) Hφ".
    iApply (wp_Jalr_link _ _ _ _ _ _ _ _ _ _ _ _ _ True%I True%I
             with "[$HPC $Hpc_a $Hmap $Hmie]");
      [done | done | done | apply link_transfer_si_core | done |].
    iNext. iIntros (lpc' regs' retv) "(Hspec & HPC & Hpc_a & Hmap & HT)". iApply "Hφ".
    iFrame "Hspec HPC Hpc_a Hmap".
    iDestruct "HT" as "[ (-> & Hmie & _) | (-> & Hmie & _) ]"; [iLeft | iRight]; by iFrame.
  Qed.

  (** A call ([rdst = cra]): the target is unsealed or a forward sentry, and
      the link is a return sentry whose kind restores the interrupt status of
      the caller. *)
  Lemma wp_jalr_success_call E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc wcra
      (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = Jalr cra rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cra rsrc wsrc.(lw) = true →
    rsrc ≠ cnull ->
    rsrc ≠ cra ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rsrc ↦ᵣ wsrc ∗
        ▷ cra ↦ᵣ wcra ∗
        ▷ MIE ↦ₜ b
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc ∗
          pc_a ↦ₐ{dq} w ∗
          rsrc ↦ᵣ wsrc ∗
          cra ↦ᵣ Sentry (ret_kind b) pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          MIE ↦ₜ default b (jalr_target_mie wsrc.(lw))
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hcra ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst & >Hmie) Hφ".
    iDestruct (map_of_regs_2 with "Hrsrc Hrdst") as "[Hmap %]".
    assert (jalr_mie (<[rsrc:=wsrc]> (<[cra:=wcra]> ∅)) rsrc b =
              default b (jalr_target_mie wsrc.(lw))) as Hjm.
    { rewrite /jalr_mie llookup_reg_not_cnull //; by simplify_map_eq. }
    iApply (wp_Jalr with "[$HPC $Hmap $Hpc_a $Hmie]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap & HT)".
    destruct Hspec as [ ? ? ? | ? Hlook Hfail | Hfail ]; subst.
    { destruct (decide (cra = cnull)) as [Hc|_]; first done.
      rewrite /jalr_link. destruct (decide (cra = cra)) as [_|Hc]; last done.
      iDestruct "HT" as "[ (_ & Hmie) | [%Hc _] ]"; last done.
      rewrite Hjm.
      iApply "Hφ". iFrame. simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { simplify_lmap_eq. congruence. }
    { congruence. }
  Qed.

  (** [jalr cra cra]: a call through [cra] itself. *)
  Lemma wp_jalr_success_call_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wcra
      (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = Jalr cra cra →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cra cra wcra.(lw) = true →

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ cra ↦ᵣ wcra ∗
        ▷ MIE ↦ₜ b
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wcra ∗
          pc_a ↦ₐ{dq} w ∗
          cra ↦ᵣ Sentry (ret_kind b) pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
          MIE ↦ₜ default b (jalr_target_mie wcra.(lw))
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt ϕ) "(>HPC & >Hpc_a & >Hrdst & >Hmie) Hφ".
    iDestruct (map_of_regs_1 with "Hrdst") as "Hmap".
    assert (jalr_mie {[cra := wcra]} cra b = default b (jalr_target_mie wcra.(lw))) as Hjm.
    { rewrite /jalr_mie llookup_reg_not_cnull //; by simplify_map_eq. }
    iApply (wp_Jalr with "[$HPC $Hmap $Hpc_a $Hmie]"); eauto; simplify_lmap_eq; eauto.
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap & HT)".
    destruct Hspec as [ ? ? ? | ? Hlook Hfail | Hfail ]; subst.
    { destruct (decide (cra = cnull)) as [Hc|_]; first done.
      rewrite /jalr_link. destruct (decide (cra = cra)) as [_|Hc]; last done.
      iDestruct "HT" as "[ (_ & Hmie) | [%Hc _] ]"; last done.
      rewrite Hjm.
      iApply "Hφ". iFrame.
      simplify_lmap_eq.
      iRegsMap "Hmap"; eauto; iFrame. }
    { simplify_lmap_eq. congruence. }
    { congruence. }
  Qed.

  (** A jump with a [cnull] destination: a return through a backward
      sentry ([rsrc = cra]) restores the MIE of the sentry; a plain jump
      keeps MIE. *)
  Lemma wp_jalr_success_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc
      (b : InterruptStatus) dq :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok cnull rsrc wsrc.(lw) = true →
    rsrc ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ rsrc ↦ᵣ wsrc ∗
        ▷ MIE ↦ₜ b
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc ∗
          pc_a ↦ₐ{dq} w ∗
          rsrc ↦ᵣ wsrc ∗
          MIE ↦ₜ default b (jalr_target_mie wsrc.(lw))
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hmie) Hφ".
    iDestruct (map_of_regs_1 with "Hrsrc") as "Hmap".
    assert (jalr_mie {[rsrc := wsrc]} rsrc b = default b (jalr_target_mie wsrc.(lw))) as Hjm.
    { rewrite /jalr_mie llookup_reg_not_cnull //; by simplify_map_eq. }
    iApply (wp_Jalr with "[$HPC $Hmap $Hpc_a $Hmie]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap & HT)".
    destruct Hspec as [ ? ? ? | ? Hlook Hfail | Hfail ]; subst.
    { destruct (decide (cnull = cnull)) as [_|Hc]; last done.
      iDestruct "HT" as "[ (_ & Hmie) | [%Hc _] ]"; last done.
      rewrite Hjm. simplify_lmap_eq.
      iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap"). }
    { simplify_lmap_eq. congruence. }
    { congruence. }
  Qed.
End griotte_lang_rules_core.
