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
     built from the PC and takes the PC's identifier. *)
  Inductive Jalr_spec (regs : LReg) pc_p pc_g pc_b pc_e pc_a pc_π (rdst rsrc: RegName) :
    LWord → LReg → griotte_lang.val → Prop :=
  | Jalr_spec_success regs' pc_a' wsrc :
    regs !!ₗ rsrc = Some wsrc ->
    (pc_a + 1)%a = Some pc_a' ->
    regs' = (<[rdst := WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ]ₗ> regs) →
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc (lupdatePcPerm wsrc) regs' NextIV
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
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hpc_a Hmap".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rsrc) as [wsrc [H'rsrc _]]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs H'rsrc) as (s & Hrsrc & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ Her Hlregs H'rsrc) as Hoksrc.
    pose proof (er_pc_word _ _ _ _ _ _ Her) as HokPC.
    rewrite /exec /= Hrsrc /= in Hstep.
    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; cbn in Hstep.
    2: { simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
         iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro. by constructor. }
    injection Hstep as <- <-.
    assert (reg_word_ok R C (WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hoksent.
    { apply (reg_word_ok_derive _ _ (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π));
        [by left|done|done|done]. }
    pose proof (erasure_pc_no_id _ _ _ _ _ _ Her Hvpc) as Hπ. cbn in Hπ.
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ rdst
                  (WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π) _ Her Hoksent
                  ltac:(by apply reg_phys_no_id)) as Her1.
    pose proof (erasure_set_pc _ _ _ _ _ _ _ _ _ _ (lupdatePcPerm wsrc) _ Her1
                  (reg_word_ok_lupdatePcPerm _ _ _ Hoksrc) (reg_phys_lupdatePcPerm _ _ _ Hrel)) as Her2.
    assert (is_Some (regs !! rdst)) as [wdst Hwdst].
    { apply elem_of_dom, Dregs. set_solver+. }
    iMod (gen_heap_update_inSepM _ _ rdst
      (if decide (rdst = cnull) then lnull else WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)
      with "Hr Hmap") as "[Hr Hmap]"; first by eexists.
    iMod (PC_update _ _ (lupdatePcPerm wsrc) with "HPCa HPC") as "[HPCa HPC]".
    iModIntro. iSplitR "Hφ HPC Hmap Hpc_a".
    - iExists _, _, lmem, R, C. iFrame "HPCa Hr Hsr Hm Hst HR HC". iPureIntro.
      exact Her2.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_jalr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc rdst wdst dq :
    decodeInstrW w.(lw) = Jalr rdst rsrc →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
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
          ∗ rdst ↦ᵣ WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "Hrsrc Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame. simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma wp_jalr_success_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc wdst dq :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ cnull ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ{dq} w
          ∗ rsrc ↦ᵣ wsrc
          ∗ cnull ↦ᵣ WInt 0
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "Hrsrc Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame. simplify_lmap_eq; [|exact lnull..].
     iRegsMap "Hmap"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma wp_jalr_success_rdst E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wdst rdst dq :
    decodeInstrW w.(lw) = Jalr rdst rdst →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ lupdatePcPerm wdst
          ∗ pc_a ↦ₐ{dq} w
          ∗ rdst ↦ᵣ WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_1 with "Hrdst") as "Hmap".
    iApply (wp_Jalr with "[$HPC $Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame.
     simplify_lmap_eq.
     iRegsMap "Hmap"; eauto; iFrame. }
   { congruence. }
  Qed.

End griotte_lang_rules.
