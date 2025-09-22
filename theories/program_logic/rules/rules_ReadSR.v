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
  Implicit Types sreg : gmap SRegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive ReadSR_failure (regs: Reg) (sregs : SReg) (dst: RegName) (src: SRegName) :=
  | ReadSR_fail_nonxrs p g b e a:
      regs !! PC = Some (WCap p g b e a) →
      has_sreg_access p = false ->
      ReadSR_failure regs sregs dst src
  | ReadSR_fail_incrPC p g b e a w:
      regs !! PC = Some (WCap p g b e a) →
      sregs !! src = Some w →
      incrementPC (<[ dst := w ]> regs) = None →
      ReadSR_failure regs sregs dst src
  .

  Inductive ReadSR_spec
  (regs: Reg) (sregs: SReg) (dst: RegName) (src: SRegName) (regs': Reg)
    : cap_lang.val -> Prop :=
  | ReadSR_spec_success p g b e a w:
      regs !! PC = Some (WCap p g b e a) →
      has_sreg_access p = true ->
      sregs !! src = Some w →
      incrementPC (<[ dst := w ]> regs) = Some regs' →
      ReadSR_spec regs sregs dst src regs' NextIV
  | ReadSR_spec_failure:
      ReadSR_failure regs sregs dst src →
      ReadSR_spec regs sregs dst src regs' FailedV.

  Lemma wp_ReadSR Ep pc_p pc_g pc_b pc_e pc_a w dst src regs sregs :
    decodeInstrW w = ReadSR dst src ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (ReadSR dst src) ⊆ dom regs →
    (if (has_sreg_access pc_p)
    then sregs_of (ReadSR dst src) ⊆ dom sregs
    else True) →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ ReadSR_spec regs sregs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Dsregs φ) "(>Hpc_a & >Hmap & >Hsmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr Hsr] Hm ] /=". destruct σ1 as [ [r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid_inclSepM with "Hsr Hsmap") as %Hsregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.

    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep.
      simplify_eq.
      iFailWP "Hφ" ReadSR_fail_nonxrs.
    }

    specialize (indom_sregs_incl _ _ _ Dsregs Hsregs) as Hsri. unfold sregs_of in Hsri.
    destruct (Hsri src) as [wsrc [H'src Hsrc]]; first by set_solver+.

    assert (exec_opt (ReadSR dst src) pc_p (r, sr, m) = updatePC (update_reg (r, sr, m) dst wsrc)) as HH.
    { by cbn; rewrite Hsrc Hxsr /=. }
    rewrite HH in Hstep. rewrite /update_reg /= in Hstep.

    destruct (incrementPC (<[ dst := wsrc ]> regs)) as [regs'|] eqn:Hregs'
    ; pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (sregs':=sr) (m':=m) in Hregs'.
      2: by apply lookup_insert_is_Some'; eauto.
      2: by apply insert_mono; eauto.
      rewrite Hregs' in Hstep. simplify_pair_eq.
      iFailWP "Hφ" ReadSR_fail_incrPC.
    }

    eapply (incrementPC_success_updatePC _ sr m) in Hregs'
      as (p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC. 2: by eapply insert_mono; eauto.
    rewrite HuPC in Hstep. simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma wp_readsr_success E pc_p pc_g pc_b pc_e pc_a pc_a' w dst wdst src wsrc :
    decodeInstrW w = ReadSR dst src →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ₛᵣ wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ wsrc
          ∗ src ↦ₛᵣ wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (map_of_sregs_1 with "Hsrc") as "Hsmap".
    iApply (wp_ReadSR with "[$Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    - by unfold regs_of; rewrite !dom_insert; set_solver+.
    - by unfold sregs_of; rewrite Hxsr !dom_insert; set_solver+.
    - iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap & Hsmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC dst) // insert_insert (insert_commute _ PC dst) // insert_insert.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?&?)"; eauto; iFrame.
      iDestruct (sregs_of_map_1 with "Hsmap") as "?"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      - simplify_map_eq; eauto; congruence.
      - incrementPC_inv; simplify_map_eq; eauto.
        congruence.
    }
  Qed.

  Lemma wp_readsr_success_toPC E pc_p pc_g pc_b pc_e pc_a w src p g b e a a':
    decodeInstrW w = ReadSR PC src →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (a + 1)%a = Some a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ src ↦ₛᵣ WCap p g b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap p g b e a'
          ∗ pc_a ↦ₐ w
          ∗ src ↦ₛᵣ WCap p g b e a }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' ϕ) "(>HPC & >Hpc_a & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hsrc") as "Hsmap".
    iApply (wp_ReadSR with "[$Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold sregs_of; rewrite Hxsr !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap & Hsmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame.
      iDestruct (sregs_of_map_1 with "Hsmap") as "?"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      - simplify_map_eq; eauto; congruence.
      - incrementPC_inv; simplify_map_eq; eauto.
        congruence.
    }
  Qed.

End cap_lang_rules.
