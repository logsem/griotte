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
  Inductive Jalr_spec (regs : LReg) pc_p pc_g pc_b pc_e pc_a pc_π (rdst rsrc: RegName) : LReg → griotte_lang.val → Prop :=
  | Jalr_spec_success regs' pc_a' wsrc :
    regs !!ₗ rsrc = Some wsrc ->
    (pc_a + 1)%a = Some pc_a' ->
    regs' = (<[rdst := WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ]ₗ>
              (<[PC := lupdatePcPerm wsrc ]ₗ>
               regs)) →
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc regs' NextIV
  | Jalr_spec_failure :
    (pc_a + 1)%a = None ->
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc regs FailedV.

  Lemma wp_Jalr Ep pc_p pc_g pc_b pc_e pc_a pc_π w rdst rsrc regs :
    decodeInstrW w.(lw) = Jalr rdst rsrc ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Jalr rdst rsrc) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Jalr_spec regs pc_p pc_g pc_b pc_e pc_a pc_π rdst rsrc regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rsrc) as [wsrc [H'rsrc _]]; first by set_solver+.
    pose proof (llookup_reg_incl _ _ _ _ Hregs H'rsrc) as Hrsrc.
    assert (r !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a)) as HrPC.
    { eapply lookup_weaken; last exact Hregs. by rewrite lookup_lregs_erase HPC. }
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ Her Hlregs H'rsrc) as Hoksrc.
    pose proof (er_reg_words _ _ _ _ _ Her PC _ (lookup_weaken _ _ _ _ HPC Hlregs)) as HokPC.
    rewrite /exec /= Hrsrc HrPC /= in Hstep.
    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; cbn in Hstep.
    2: { simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
         iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro. by constructor. }
    injection Hstep as <- <-.
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ PC (lupdatePcPerm wsrc) Her
                  (reg_word_ok_lupdatePcPerm _ _ _ Hoksrc)) as Her1.
    assert (reg_word_ok R C (WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)) as Hoksent.
    { apply (reg_word_ok_derive _ _ (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π));
        [by left|done|done]. }
    pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ rdst
                  (WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π) Her1 Hoksent) as Her2.
    assert (is_Some (regs !! rdst)) as [wdst Hwdst].
    { apply elem_of_dom, Dregs. set_solver+. }
    iMod (gen_heap_update_inSepM _ _ PC (if decide (PC = cnull) then lnull else lupdatePcPerm wsrc)
      with "Hr Hmap") as "[Hr Hmap]"; first by eexists.
    iMod (gen_heap_update_inSepM _ _ rdst
      (if decide (rdst = cnull) then lnull else WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π)
      with "Hr Hmap") as "[Hr Hmap]".
    { by rewrite lookup_insert_is_Some'; right. }
    iModIntro. iSplitR "Hφ Hmap Hpc_a".
    - iExists _, lmem, R, C. iFrame "Hr Hsr Hm Hst HR HC". iPureIntro. exact Her2.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_jalr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc rdst wdst :
    decodeInstrW w.(lw) = Jalr rdst rsrc →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->
    rdst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ w
          ∗ rsrc ↦ᵣ wsrc
          ∗ rdst ↦ᵣ WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull Hcnull' ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hrsrc Hrdst") as "[Hmap (%&%&%)]".
    iApply (wp_Jalr with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame. simplify_lmap_eq.
     rewrite (insert_insert_ne _ rsrc rdst) // insert_insert_eq.
     rewrite (insert_insert_ne _ rdst PC) // insert_insert_eq.
     iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma wp_jalr_success_cnull E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rsrc wsrc wdst :
    decodeInstrW w.(lw) = Jalr cnull rsrc →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rsrc ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ cnull ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ lupdatePcPerm wsrc
          ∗ pc_a ↦ₐ w
          ∗ rsrc ↦ᵣ wsrc
          ∗ cnull ↦ᵣ WInt 0
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hrsrc Hrdst") as "[Hmap (%&%&%)]".
    iApply (wp_Jalr with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame. simplify_lmap_eq; [|exact lnull..].
     rewrite insert_insert_eq (insert_insert_ne _ cnull PC); last by apply not_eq_sym.
     rewrite (insert_insert_ne _ cnull rsrc); last by apply not_eq_sym.
     rewrite insert_insert_eq.
     iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma wp_jalr_successPC E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rdst wdst :
    decodeInstrW w.(lw) = Jalr rdst PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ lupdatePcPerm (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π)
          ∗ pc_a ↦ₐ w
          ∗ rdst ↦ᵣ WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame.
     simplify_lmap_eq.
     rewrite insert_insert_eq (insert_insert_ne _ rdst PC) // insert_insert_eq.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma wp_jalr_success_rdst E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w wdst rdst :
    decodeInstrW w.(lw) = Jalr rdst rdst →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    rdst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ lupdatePcPerm wdst
          ∗ pc_a ↦ₐ w
          ∗ rdst ↦ᵣ WSentry true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$Hmap Hpc_a]"); eauto; simplify_lmap_eq; eauto.
    { set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame.
     simplify_lmap_eq.
     rewrite insert_insert_eq (insert_insert_ne _ rdst PC) // !insert_insert_eq.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

End griotte_lang_rules.
