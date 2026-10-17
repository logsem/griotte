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
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.


  (* The new PC is the source word with its identifier; the link sentry is
     built from the PC and takes the PC's identifier. A [cnull] destination
     drops the link. *)
  Inductive Jalr_spec (regs : LReg) pc_p pc_g pc_b pc_e pc_a pc_π (rdst rsrc: RegName) :
    LWord → LReg → griotte_lang.val → Prop :=
  | Jalr_spec_success regs' pc_a' wsrc :
    regs !!ₗ rsrc = Some wsrc ->
    jalr_target_ok wsrc.(lw) = true ->
    (pc_a + 1)%a = Some pc_a' ->
    regs' = (if decide (rdst = cnull) then regs
             else <[rdst := WSentry (ret_kind InterruptDisabled) true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ]ₗ> regs) →
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc (lupdatePcPerm wsrc) regs' NextIV
  | Jalr_spec_failure_target wsrc :
    regs !!ₗ rsrc = Some wsrc ->
    jalr_target_ok wsrc.(lw) = false ->
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc
      (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs FailedV
  | Jalr_spec_failure :
    (pc_a + 1)%a = None ->
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc
      (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs FailedV.

  Lemma wp_Jalr Ep pc_p pc_g pc_b pc_e pc_a pc_π w rdst rsrc regs dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jalr rdst rsrc) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lsreg lmem R C c σ') "@".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rsrc) as [wsrc [H'rsrc _]]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'rsrc) as (s & Hrsrc & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ _ Her Hlregs H'rsrc) as Hoksrc.
    pose proof (er_pc_word _ _ _ _ _ _ _ Her) as HokPC.
    rewrite /exec /= Hrsrc /= jalr_target_checks in Hstep.
    (* The target checks fail on the physical copy exactly when they fail on
       the logical word: a word that passes them is executable, hence
       exact. *)
    destruct (jalr_target_ok wsrc.(lw)) eqn:Hok; cycle 1.
    { rewrite jalr_target_ok_and_tag Hok andb_false_r in Hstep.
      instr_fail Hstep. by eapply Jalr_spec_failure_target. }
    assert (and_tag s wsrc.(lw) = wsrc.(lw)) as Heq.
    { pose proof Hok as Hok'. apply andb_prop in Hok' as [[Ht _]%andb_prop Hx].
      by apply (reg_phys_executable R C). }
    rewrite Heq in Hstep Hrel. rewrite Hok in Hstep.
    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; cbn in Hstep.
    2: { instr_fail Hstep. by constructor. }
    injection Hstep as <- <-.
    assert (reg_word_ok R C (WSentry (ret_kind InterruptDisabled) true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hoksent.
    { apply (reg_word_ok_derive _ _ (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π));
        [by left|done|done|done]. }
    pose proof (erasure_pc_no_id _ _ _ _ _ _ _ Her Hvpc) as Hπ. cbn in Hπ.
    destruct (decide (rdst = cnull)) as [Hnull | Hnull].
    { iApply (instr_close_set_pc _ _ _ _ _ _ _ _ _ _ _ _ (lupdatePcPerm wsrc)
                with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
      - exact Her.
      - by apply reg_word_ok_lupdatePcPerm.
      - by apply reg_phys_lupdatePcPerm.
      - by apply jalr_target_ok_pc_ok.
      - iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro.
        eapply Jalr_spec_success; [exact H'rsrc | exact Hok | exact Hpca' |].
        by rewrite decide_True. }
    iApply (instr_close_reg_set_pc _ _ _ _ _ _ _ _ _ _ _ _ rdst
              (WSentry (ret_kind InterruptDisabled) true pc_p pc_g pc_b pc_e pc_a' @@? pc_π) _ (lupdatePcPerm wsrc)
              with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap").
    - exact Her.
    - apply Dregs. set_solver.
    - exact Hoksent.
    - by apply reg_phys_no_id.
    - by apply reg_word_ok_lupdatePcPerm.
    - by apply reg_phys_lupdatePcPerm.
    - by apply jalr_target_ok_pc_ok.
    - iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro.
      eapply Jalr_spec_success; [exact H'rsrc | exact Hok | exact Hpca' |].
      by rewrite decide_False.
  Qed.

  Lemma wp_jalr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc rdst wdst dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok wsrc.(lw) = true →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
          ∗ rdst ↦ᵣ WSentry (ret_kind InterruptDisabled) true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "Hrsrc Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | ? Hlook Hfail | Hfail ]; subst.
   { rewrite decide_False //.
     iApply "Hφ". iFrame. simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  Lemma wp_jalr_success_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc dq :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok wsrc.(lw) = true →
    rsrc ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull ϕ) "(>HPC & >Hpc_a & >Hrsrc) Hφ".
    iDestruct (map_of_regs_1 with "Hrsrc") as "Hmap".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | ? Hlook Hfail | Hfail ]; subst.
   { destruct (decide (cnull = cnull)) as [_|Hc]; last done.
     simplify_lmap_eq.
     iApply "Hφ". iFrame. iApply (regs_of_map_1 with "Hmap"). }
   { simplify_lmap_eq. congruence. }
   { congruence. }
  Qed.

  Lemma wp_jalr_success_rdst E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wdst rdst dq :
    decodeInstrW w.(lw) = Jalr rdst rdst →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    jalr_target_ok wdst.(lw) = true →
    rdst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wdst
          ∗ pc_a ↦ₐ{dq} w
          ∗ rdst ↦ᵣ WSentry (ret_kind InterruptDisabled) true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Htgt Hcnull ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_1 with "Hrdst") as "Hmap".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | ? Hlook Hfail | Hfail ]; subst.
   { rewrite decide_False //.
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
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok wsrc.(lw) = false →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
          ∗ rdst ↦ᵣ wdst
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iApply (wp_instr_failed_2 with "[$HPC $Hrsrc $Hrdst $Hpc_a]"); [done | done | | ].
    - intros r sr m st s1 s2 Hr1 _.
      rewrite /exec /= /lookup_reg Hr1 /= jalr_target_checks.
      case_decide; first done.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hrsrc & Hrdst & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jalr_fail_target_cnull E pc_p pc_g pc_b pc_e pc_a pc_π w rsrc wsrc dq :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok wsrc.(lw) = false →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
    }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hrsrc) Hφ".
    iApply (wp_instr_failed_1 with "[$HPC $Hrsrc $Hpc_a]"); [done | done | | ].
    - intros rf sr m st s1 Hr1.
      rewrite /exec /= /lookup_reg Hr1 /= jalr_target_checks.
      case_decide; first done.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hrsrc & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_jalr_fail_target_same E pc_p pc_g pc_b pc_e pc_a pc_π w r wr dq :
    decodeInstrW w.(lw) = Jalr r r →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    jalr_target_ok wr.(lw) = false →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r ↦ᵣ wr
    }}}
      Instr Executable @ E
      {{{ RET FailedV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r ↦ᵣ wr
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hfail ϕ) "(>HPC & >Hpc_a & >Hr) Hφ".
    iApply (wp_instr_failed_1 with "[$HPC $Hr $Hpc_a]"); [done | done | | ].
    - intros rf sr m st s1 Hr1.
      rewrite /exec /= /lookup_reg Hr1 /= jalr_target_checks.
      case_decide; first done.
      by rewrite jalr_target_ok_and_tag Hfail andb_false_r.
    - iNext. iIntros "(HPC & Hr & Hpc_a)". iApply "Hφ". iFrame.
  Qed.

End griotte_lang_rules.
