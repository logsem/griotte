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

  Inductive WriteSR_failure (regs: Reg) (sregs : SReg) (dst: SRegName) (src: RegName) :=
  | WriteSR_fail_nonxrs p g b e a:
      regs !! PC = Some (WCap p g b e a) →
      has_sreg_access p = false ->
      WriteSR_failure regs sregs dst src
  | WriteSR_fail_incrPC p g b e a w:
      regs !! PC = Some (WCap p g b e a) →
      regs !! src = Some w →
      incrementPC regs = None →
      WriteSR_failure regs sregs dst src
  .

  Inductive WriteSR_spec
    (regs regs': Reg) (sregs sregs': SReg) (dst: SRegName) (src: RegName)
    : cap_lang.val -> Prop :=
  | WriteSR_spec_success p g b e a w:
    regs !! PC = Some (WCap p g b e a) →
    has_sreg_access p = true ->
    regs !! src = Some w →
    incrementPC regs = Some regs' →
    sregs' = (<[dst := w]> sregs) →
    WriteSR_spec regs regs' sregs sregs' dst src NextIV
  | WriteSR_spec_failure:
    sregs = sregs' ->
    WriteSR_failure regs sregs dst src →
    WriteSR_spec regs regs' sregs sregs' dst src FailedV.

  Lemma wp_WriteSR Ep pc_p pc_g pc_b pc_e pc_a w dst src regs sregs :
    decodeInstrW w = WriteSR dst src ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (WriteSR dst src) ⊆ dom regs →
    sregs_of (WriteSR dst src) ⊆ dom sregs →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}
      Instr Executable @ Ep
    {{{ regs' sregs' retv, RET retv;
        ⌜ WriteSR_spec regs regs' sregs sregs' dst src retv ⌝ ∗
        pc_a ↦ₐ w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        ([∗ map] k↦y ∈ sregs', k ↦ₛᵣ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Dsregs φ) "(>Hpc_a & >Hmap & >Hsmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr Hsr] Hm ] /=". destruct σ1 as [ [r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (gen_heap_valid_inclSepM with "Hsr Hsmap") as %Hsregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_base_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    destruct (Hri src) as [wsrc [H'src Hsrc]]. by set_solver+.

    specialize (indom_sregs_incl _ _ _ Dsregs Hsregs) as Hsri. unfold sregs_of in Hsri.
    destruct (Hsri dst) as [wdst [H'dst Hdst]]. by set_solver+.

    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep.
      rewrite Hxsr in Hstep; simplify_eq.
      iFailWP "Hφ" WriteSR_fail_nonxrs.
    }

    assert (exec_opt (WriteSR dst src) pc_p (r, sr, m) = updatePC (update_sreg (r, sr, m) dst wsrc)) as HH.
    { by cbn; rewrite Hsrc Hxsr /=. }
    rewrite HH in Hstep. rewrite /update_sreg /= in Hstep.

    destruct (incrementPC regs) as [regs'|] eqn:Hregs'
    ; pose proof Hregs' as H'regs'; cycle 1.
    { apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) in Hregs'.
      eapply updatePC_fail_incl with (sregs':= <[dst:=wsrc]>sr) (m':=m) in Hregs'; eauto.
      rewrite Hregs' in Hstep. simplify_pair_eq.
      iFailWP "Hφ" WriteSR_fail_incrPC.
    }

    eapply (incrementPC_success_updatePC _ (<[dst:=wsrc]> sr) m) in Hregs'
      as (p' & g' & b' & e' & a'' & a''' & HPC'' & a_pc' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':=<[dst:=wsrc]>sr) (m':=m) in HuPC; eauto.
    rewrite HuPC in Hstep. simplify_pair_eq. iFrame.
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hsr Hsmap") as "[Hsr Hsmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    rewrite /incrementPC in H'regs'; simplify_map_eq.
    by rewrite HPC in HPC''; inv HPC''.
  Qed.

  Lemma wp_writesr_success E pc_p pc_g pc_b pc_e pc_a pc_a' w dst wdst src wsrc :
    decodeInstrW w = WriteSR dst src →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ₛᵣ wdst
        ∗ ▷ src ↦ᵣ wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ₛᵣ wsrc
          ∗ src ↦ᵣ wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iDestruct (map_of_sregs_1 with "Hdst") as "Hsmap".
    iApply (wp_WriteSR with "[$Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    - by unfold regs_of; rewrite !dom_insert; set_solver+.
    - by unfold sregs_of; rewrite !dom_insert; set_solver+.
    - iNext. iIntros (regs' sregs' retv) "(#Hspec & Hpc_a & Hmap & Hsmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| -> Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_commute _ PC src) // insert_insert (insert_commute _ PC src) // insert_insert.
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

  Lemma wp_writesr_success_fromPC E pc_p pc_g pc_b pc_e pc_a pc_a' w dst wdst :
    decodeInstrW w = WriteSR dst PC →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ₛᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ₛᵣ WCap pc_p pc_g pc_b pc_e pc_a }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxrs Hpca' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hdst") as "Hsmap".
    iApply (wp_WriteSR with "[$Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' sregs' retv) "(#Hspec & Hpc_a & Hmap & Hsmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| -> Hfail].
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
