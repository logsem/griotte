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

  Lemma wp_jalr_success E pc_p pc_g pc_b pc_e pc_a pc_a' w rdst wdst wra :
    decodeInstrW w = Jalr rdst →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ rdst ↦ᵣ wdst
        ∗ ▷ cra ↦ᵣ wra
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm wdst
          ∗ pc_a ↦ₐ w
          ∗ rdst ↦ᵣ wdst
          ∗ cra ↦ᵣ WCap (seal_perm_sentry pc_p) pc_g pc_b pc_e pc_a'
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hrdst & >Hcra) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr0 Hsr] Hm ] /=". destruct σ1 as [ [r0 sr] m]; cbn.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?; auto.
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %?.
    iDestruct (@gen_heap_valid with "Hr0 Hrdst") as %Hr_rdst.
    iDestruct (@gen_heap_valid with "Hr0 Hcra") as %Hr_cra.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_base_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    unfold exec, exec_opt in Hstep.
    rewrite Hr_rdst //= H0 //= Hpca' in Hstep.
    simplify_pair_eq.

    iMod (@gen_heap_update with "Hr0 Hcra") as "[Hr0 Hcra]".
    iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
    iFrame.
    iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_jalr_successPC E pc_p pc_g pc_b pc_e pc_a pc_a' w wra :
    decodeInstrW w = Jalr PC →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ cra ↦ᵣ wra
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm (WCap pc_p pc_g pc_b pc_e pc_a)
          ∗ pc_a ↦ₐ w
          ∗ cra ↦ᵣ WCap (seal_perm_sentry pc_p) pc_g pc_b pc_e pc_a'
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hcra) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr0 Hsr] Hm ] /=". destruct σ1 as [ [r0 sr] m]; cbn.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?; auto.
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %Hr_PC.
    iDestruct (@gen_heap_valid with "Hr0 Hcra") as %Hr_cra.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_base_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    unfold exec, exec_opt in Hstep.
    rewrite Hr_PC /= Hpca' /= in Hstep.
    simplify_pair_eq.

    iMod (@gen_heap_update with "Hr0 Hcra") as "[Hr0 Hcra]".
    iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
    iFrame.
    iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_jalr_success_cra E pc_p pc_g pc_b pc_e pc_a pc_a' w wra :
    decodeInstrW w = Jalr cra →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ cra ↦ᵣ wra
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ updatePcPerm wra
          ∗ pc_a ↦ₐ w
          ∗ cra ↦ᵣ WCap (seal_perm_sentry pc_p) pc_g pc_b pc_e pc_a'
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a & >Hcra) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr0 Hsr] Hm ] /=". destruct σ1 as [ [r0 sr] m]; cbn.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %?; auto.
    iDestruct (@gen_heap_valid with "Hr0 HPC") as %Hr_PC.
    iDestruct (@gen_heap_valid with "Hr0 Hcra") as %Hr_cra.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_base_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    unfold exec, exec_opt in Hstep.
    rewrite Hr_PC /= Hr_cra /= Hpca' /= in Hstep.
    simplify_pair_eq.

    iMod (@gen_heap_update with "Hr0 Hcra") as "[Hr0 Hcra]".
    iMod (@gen_heap_update with "Hr0 HPC") as "[Hr0 HPC]".
    iFrame.
    iApply "Hφ". by iFrame.
  Qed.

End cap_lang_rules.
