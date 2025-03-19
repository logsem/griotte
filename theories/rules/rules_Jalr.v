From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.


  Inductive Jalr_spec (regs: Reg) pc_p pc_g pc_b pc_e pc_a (rdst rsrc: RegName) : Reg → cap_lang.val → Prop :=
  | Jalr_spec_success regs' pc_a' wsrc :
    regs !! rsrc = Some wsrc ->
    (pc_a + 1)%a = Some pc_a' ->
    regs' = (<[rdst := (WSentry pc_p pc_g pc_b pc_e pc_a') ]>
              (<[PC :=  updatePcPerm wsrc ]>
               regs)) →
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a rdst rsrc regs' NextIV
  | Jalr_spec_failure :
    (pc_a + 1)%a = None ->
    Jalr_spec regs pc_p pc_g pc_b pc_e pc_a rdst rsrc regs FailedV.

  Lemma wp_Jalr Ep pc_p pc_g pc_b pc_e pc_a w rdst rsrc regs :
    decodeInstrW w = Jalr rdst rsrc ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jalr rdst rsrc) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Jalr_spec regs pc_p pc_g pc_b pc_e pc_a rdst rsrc regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr Hsr] Hm ] /=". destruct σ1 as [ [r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have HrPC := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_base_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rdst) as [wdst [H'rdst Hrdst]]; first by set_solver+.
    destruct (Hri rsrc) as [wsrc [H'rsrc Hrsrc]]; first by set_solver+.
    rewrite /exec in Hstep; cbn in Hstep.
    rewrite Hrsrc HrPC /= in Hstep.

    destruct (pc_a + 1)%a as [pc_a'|] eqn:Hpca'; simplify_pair_eq; cycle 1.
    { iFailWP "Hφ" Jalr_spec_failure. }
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ rdst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { destruct (decide (rdst = PC)); simplify_map_eq; done. }
    iFrame.
    iApply "Hφ"; iFrame.
    iPureIntro; econstructor; eauto.
  Qed.

  Lemma wp_jalr_success E pc_p pc_g pc_b pc_e pc_a pc_a' w rsrc wsrc rdst wdst :
    decodeInstrW w = Jalr rdst rsrc →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rsrc ↦ᵣ wsrc
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm wsrc
          ∗ pc_a ↦ₐ w
          ∗ rsrc ↦ᵣ wsrc
          ∗ rdst ↦ᵣ WSentry pc_p pc_g pc_b pc_e pc_a'
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hrsrc & >Hrdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hrsrc Hrdst") as "[Hmap (%&%&%)]".
    iApply (wp_Jalr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame. simplify_map_eq.
     rewrite (insert_commute _ rsrc rdst) // insert_insert.
     rewrite (insert_commute _ rdst PC) // insert_insert.
     iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma wp_jalr_successPC E pc_p pc_g pc_b pc_e pc_a pc_a' w rdst wdst :
    decodeInstrW w = Jalr rdst PC →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm (WCap pc_p pc_g pc_b pc_e pc_a)
          ∗ pc_a ↦ₐ w
          ∗ rdst ↦ᵣ WSentry pc_p pc_g pc_b pc_e pc_a'
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame.
     simplify_map_eq.
     rewrite insert_insert (insert_commute _ rdst PC) // insert_insert.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

  Lemma wp_jalr_success_rdst E pc_p pc_g pc_b pc_e pc_a pc_a' w wdst rdst :
    decodeInstrW w = Jalr rdst rdst →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rdst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm wdst
          ∗ pc_a ↦ₐ w
          ∗ rdst ↦ᵣ WSentry pc_p pc_g pc_b pc_e pc_a'
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hrdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hrdst") as "[Hmap %]".
    iApply (wp_Jalr with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

   destruct Hspec as [ | Hfail ]; subst.
   { iApply "Hφ". iFrame.
     simplify_map_eq.
     rewrite insert_insert (insert_commute _ rdst PC) // !insert_insert.
     iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
   { congruence. }
  Qed.

End cap_lang_rules.
