From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_WriteSR.

(** * Spec rules for [WriteSR] (spec copies of [rules_WriteSR.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types sreg : gmap SRegName Word.
  Implicit Types ms : gmap Addr Word.

  (** Physical spec-side outcomes, for the spec run. *)

  Inductive spec_WriteSR_failure (regs: Reg) (sregs : SReg) (dst: SRegName) (src: RegName) :=
  | spec_WriteSR_fail_nonxrs p g b e a:
      regs !! PC = Some (WCap true p g b e a) →
      has_sreg_access p = false ->
      spec_WriteSR_failure regs sregs dst src
  | spec_WriteSR_fail_incrPC p g b e a w:
      regs !! PC = Some (WCap true p g b e a) →
      regs !!ᵣ src = Some w →
      spec_incrementPC regs = None →
      spec_WriteSR_failure regs sregs dst src
  .

  Inductive spec_WriteSR_spec
    (regs regs': Reg) (sregs sregs': SReg) (dst: SRegName) (src: RegName)
    : griotte_lang.val -> Prop :=
  | spec_WriteSR_spec_success p g b e a w:
    regs !! PC = Some (WCap true p g b e a) →
    has_sreg_access p = true ->
    regs !!ᵣ src = Some w →
    spec_incrementPC regs = Some regs' →
    sregs' = (<[dst := w]> sregs) →
    spec_WriteSR_spec regs regs' sregs sregs' dst src NextIV
  | spec_WriteSR_spec_failure:
    sregs = sregs' ->
    spec_WriteSR_failure regs sregs dst src →
    spec_WriteSR_spec regs regs' sregs sregs' dst src FailedV.

  Lemma WriteSR_spec_determ regs sregs dst src regs1 regs2 sregs1 sregs2 v1 v2 :
    spec_WriteSR_spec regs regs1 sregs sregs1 dst src v1 →
    spec_WriteSR_spec regs regs2 sregs sregs2 dst src v2 →
    v1 = v2 ∧ sregs1 = sregs2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ spec_WriteSR_failure. Qed.

  Lemma WriteSR_spec_lift regs sregs dst src lregs' sregs' v :
    WriteSR_spec (lift_regs regs) lregs' sregs sregs' dst src v →
    ∃ regs', (v = NextIV → lregs' = lift_regs regs') ∧ spec_WriteSR_spec regs regs' sregs sregs' dst src v.
  Proof. spec_lift WriteSR_failure regs. Qed.

  Lemma step_WriteSR Ep pc_p pc_g pc_b pc_e pc_a w dst src regs sregs :
    ↑specN ⊆ Ep →
    decodeInstrW w = WriteSR dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (WriteSR dst src) ⊆ dom regs →
    (if (has_sreg_access pc_p)
    then sregs_of (WriteSR dst src) ⊆ dom sregs
    else True) →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y) ∗
    ([∗ map] k↦y ∈ sregs, k ↣ₛᵣ y)
    ={Ep}=∗
    ∃ retv regs' sregs',
      ⤇ Seq (of_val retv) ∗
      ⌜ spec_WriteSR_spec regs regs' sregs sregs' dst src retv ⌝ ∗
      pc_a ↣ₐ w ∗
      ([∗ map] k↦y ∈ regs', k ↣ᵣ y) ∗
      ([∗ map] k↦y ∈ sregs', k ↣ₛᵣ y).
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Dsregs) "(#Hctx & Hj & Hpc_a & Hmap & Hsmap)".
    iApply (spec_step_exec_2 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[[r sr] m] st] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
    iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.
    iDestruct (spec_sregs_valid_inclSepM with "Hsr Hsmap") as %Hsregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_mem_valid with "Hm Hpc_a") as %Hpc_a; auto.
    eapply step_exec_inv in Hstep; eauto.
    unfold exec in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    destruct (Hri src) as [wsrc [H'src Hsrc]]; first by set_solver+.

    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep.
      rewrite Hxsr in Hstep; simplify_eq.
      iFailWP "Hφ" spec_WriteSR_fail_nonxrs.
    }

    specialize (indom_sregs_incl _ _ _ Dsregs Hsregs) as Hsri. unfold sregs_of in Hsri.
    destruct (Hsri dst) as [wdst [H'dst Hdst]]; first by set_solver+.

    assert (exec_opt (WriteSR dst src) pc_p (r, sr, m, st) = updatePC (update_sreg (r, sr, m, st) dst wsrc)) as HH.
    { by cbn; rewrite Hsrc Hxsr /=. }
    rewrite HH in Hstep. rewrite /update_sreg /= in Hstep.

    destruct (spec_incrementPC regs) as [regs'|] eqn:Hregs'
    ; pose proof Hregs' as H'regs'; cycle 1.
    { apply spec_incrementPC_fail_updatePC with (sregs:=sr) (m:=m) (shadow:=st) in Hregs'.
      eapply updatePC_fail_incl with (sregs':= <[dst:=wsrc]>sr) (m':=m) (shadow':=st) in Hregs'; eauto.
      rewrite Hregs' in Hstep. simplify_pair_eq.
      iFailWP "Hφ" spec_WriteSR_fail_incrPC.
    }

    eapply (spec_incrementPC_success_updatePC _ (<[dst:=wsrc]> sr) m st) in Hregs'
      as (t' & p' & g' & b' & e' & a'' & a''' & HPC'' & a_pc' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':=<[dst:=wsrc]>sr) (m':=m) (shadow':=st) in HuPC; eauto.
    rewrite HuPC in Hstep. simplify_pair_eq. iFrame.
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iMod ((spec_sregs_update_inSepM _ _ dst) with "Hsr Hsmap") as "[Hsr Hsmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

  Lemma step_writesr_success E pc_p pc_g pc_b pc_e pc_a pc_a' w dst wdst src wsrc :
    ↑specN ⊆ E →
    decodeInstrW w = WriteSR dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ₛᵣ wdst ∗
    src ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ₛᵣ wsrc ∗
    src ↣ᵣ wsrc.
  Proof.
    iIntros (HE Hinstr Hvpc Hxsr Hpca' ?) "(#Hctx & Hj & HPC & Hpc_a & Hdst & Hsrc)".
    iDestruct (spec_map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iDestruct (spec_map_of_sregs_1 with "Hdst") as "Hsmap".
    iMod (step_WriteSR with "[$Hctx $Hj $Hmap $Hsmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    - by unfold regs_of; rewrite !dom_insert; set_solver+.
    - by unfold sregs_of; rewrite Hxsr !dom_insert; set_solver+.
    - iDestruct "H" as (retv regs' sregs') "(Hj & %Hspec & Hpc_a & Hmap & Hsmap)".

    destruct Hspec as [| -> Hfail].
    { (* Success *)
      iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC src) // insert_insert_eq (insert_insert_ne _ PC src) // insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.
      iDestruct (spec_sregs_of_map_1 with "Hsmap") as "?"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      - simplify_map_eq; eauto; congruence.
      - spec_incrementPC_inv; simplify_map_eq; eauto.
        congruence.
    }
  Qed.

  Lemma step_writesr_success_fromPC E pc_p pc_g pc_b pc_e pc_a pc_a' w dst wdst :
    ↑specN ⊆ E →
    decodeInstrW w = WriteSR dst PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ₛᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ₛᵣ WCap true pc_p pc_g pc_b pc_e pc_a.
  Proof.
    iIntros (HE Hinstr Hvpc Hxsr Hpca') "(#Hctx & Hj & HPC & Hpc_a & Hdst)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_map_of_sregs_1 with "Hdst") as "Hsmap".
    iMod (step_WriteSR with "[$Hctx $Hj $Hmap $Hsmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold sregs_of; rewrite Hxsr !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs' sregs') "(Hj & %Hspec & Hpc_a & Hmap & Hsmap)".

    destruct Hspec as [| -> Hfail].
    { (* Success *)
      iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
      iDestruct (spec_regs_of_map_1 with "Hmap") as "?"; eauto; iFrame.
      iDestruct (spec_sregs_of_map_1 with "Hsmap") as "?"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      - simplify_map_eq; eauto; congruence.
      - spec_incrementPC_inv; simplify_map_eq; eauto.
        congruence.
    }
  Qed.


End spec_rules.
