From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Jmp.

(** * Spec rules for [Jmp] (spec copies of [rules_Jmp.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma Jmp_spec_determ regs rimm regs1 regs2 v1 v2 :
    Jmp_spec regs rimm regs1 v1 →
    Jmp_spec regs rimm regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ Jmp_failure. Qed.

  Lemma step_Jmp Ep pc_p pc_g pc_b pc_e pc_a w rimm regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = Jmp rimm ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jmp rimm) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Jmp_spec regs rimm regs' retv ⌝ ∗
      pc_a ↣ₐ w ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[r sr] m] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
    iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (spec_mem_valid with "Hm Hpc_a") as %Hpc_a; auto.
    eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.

    destruct (z_of_argument regs rimm) as [imm|] eqn:Himm
    ; pose proof Himm as H'imm
    ; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Himm, Hstep.
       destruct rimm as [| rimm]; [ congruence |].
       odestruct (Hri rimm) as [rimmv [Hrimm' Hrimm]].
       { unfold regs_of_argument. set_solver+. }
       rewrite Hrimm Hrimm' in Himm Hstep.
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       { destruct_word rimmv; cbn in Hstep; try congruence; by simplify_pair_eq. }
       iFailWP "Hφ" Jmp_fail_no_imm. }
     apply (z_of_arg_mono _ r) in Himm; auto.
     rewrite Himm in Hstep; simpl in Hstep.


     destruct (incrementPC_gen regs imm) eqn:Hregs';
       pose proof Hregs' as H'regs'; cycle 1.
     {
       assert (incrementPC_gen r imm = None) as HH.
       { eapply incrementPC_gen_overflow_mono; first eapply Hregs' ; eauto.
       }
       apply (incrementPC_gen_fail_updatePC_gen _ sr m) in HH. rewrite HH in Hstep.
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->) by (inversion Hstep; auto).
       iFailWP "Hφ" Jmp_fail_PC_overflow. }

       eapply (incrementPC_gen_success_updatePC_gen _ sr m _ imm) in Hregs'
         as (p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_gen_success_incl with (sregs':=sr) (m':=m) in HuPC; eauto.
       rewrite HuPC in Hstep.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { cbn in *; eauto. }
       simplify_pair_eq.

       iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame.
       iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

   Lemma step_jmp_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w imm :
     ↑specN ⊆ Ep →
     decodeInstrW w = Jmp (inl imm) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + imm)%a = Some pc_a' →
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w
     ={Ep}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca') "(#Hctx & Hj & HPC & Hpc_a)".
     iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
     iMod (step_Jmp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [| * Hfail].
     { (* Success *)
       iModIntro. iFrame.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
       rewrite insert_insert_eq //.
       iDestruct (spec_regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto ; congruence.
     }
   Qed.

   Lemma step_jmp_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w rimm imm:
     ↑specN ⊆ Ep →
     decodeInstrW w = Jmp (inr rimm) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + imm)%a = Some pc_a' →
     rimm ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     rimm ↣ᵣ WInt imm
     ={Ep}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w ∗
     rimm ↣ᵣ WInt imm.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrimm)".
     iDestruct (spec_map_of_regs_2 with "HPC Hrimm") as "[Hmap %]".
     iMod (step_Jmp with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [| * Hfail].
     { (* Success *)
       iModIntro. iFrame.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
       rewrite insert_insert_eq //.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto ; congruence.
     }
   Qed.

End spec_rules.
