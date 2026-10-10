From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Seal.

(** * Spec rules for [Seal] (spec copies of [rules_Seal.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma Seal_spec_determ regs dst src1 src2 regs1 regs2 v1 v2 :
    Seal_spec regs dst src1 src2 regs1 v1 →
    Seal_spec regs dst src1 src2 regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ Seal_failure. Qed.

  Lemma step_Seal Ep pc_p pc_g pc_b pc_e pc_a w dst src1 src2 regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = Seal dst src1 src2 ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Seal dst src1 src2) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Seal_spec regs dst src1 src2 regs' retv ⌝ ∗
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

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    odestruct (Hri src2) as [r2v [Hr'2 Hr2]]; first by set_solver+.
    odestruct (Hri src1) as [r1v [Hr'1 Hr1]]; first  by set_solver+.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first  by set_solver+.
    clear Hri.

    rewrite /exec /= Hr2 Hr1 /= in Hstep.

    (* Now we start splitting on the different cases in the Seal spec, and prove them one at a time *)
     destruct (is_sealr r1v) eqn:Hr1v.
     2:{ (* Failure: r2 is not a sealrange *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_sealr in Hr1v.
         destruct_word r1v; by simplify_pair_eq.
       }
        iFailWP "Hφ" Seal_fail_sealr.
     }
     destruct r1v as [ | [ | p g b e a ] | | ]; try inversion Hr1v. clear Hr1v.

     destruct (is_sealb r2v) eqn:Hr2v.
     2:{ (* Failure: r2 is not a sealrange *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_sealed in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" Seal_fail_sealb.
     }
     destruct r2v as [ | sb | | ]; try inversion Hr2v. clear Hr2v.

     destruct (permit_seal p && withinBounds b e a) eqn:HSA.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow sealing *)
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       apply andb_false_iff in HSA.
       iFailWP "Hφ" Seal_fail_bounds.
     }
     apply andb_true_iff in HSA; destruct HSA as (Hps & Hwb).

     destruct (incrementPC (<[ dst := (WSealed a sb) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC (<[ dst := (WSealed a sb) ]ᵣ> r) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         + by rewrite lookup_insert_is_Some'; eauto.
         + by apply insert_mono; eauto.
       }

       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iFailWP "Hφ" Seal_fail_incrPC.
     }

     (* Success *)
     rewrite /update_reg /= in Hstep.
     eapply (incrementPC_success_updatePC _ sr m) in Hregs'
       as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     { apply is_Some_lookup_reg; done. }
     iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply Seal_spec_success; eauto.
     rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
     Unshelve. all: auto.
  Qed.

End spec_rules.
