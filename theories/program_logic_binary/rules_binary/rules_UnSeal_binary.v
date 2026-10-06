From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_UnSeal.

(** * Spec rules for [UnSeal] (spec copies of [rules_UnSeal.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma UnSeal_spec_determ regs dst src1 src2 regs1 regs2 v1 v2 :
    UnSeal_spec regs dst src1 src2 regs1 v1 →
    UnSeal_spec regs dst src1 src2 regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ UnSeal_failure. Qed.

  Lemma step_UnSeal Ep pc_p pc_g pc_b pc_e pc_a w dst src1 src2 regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = UnSeal dst src1 src2 ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ UnSeal_spec regs dst src1 src2 regs' retv ⌝ ∗
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
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first  by set_solver+. clear Hri.

    rewrite /exec /= Hr2 Hr1 /= in Hstep.

    (* Now we start splitting on the different cases in the UnSeal spec, and prove them one at a time *)
     destruct (is_sealr r1v) eqn:Hr1v.
     2:{ (* Failure: r2 is not a sealrange *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_sealr in Hr1v.
         destruct_word r1v; by simplify_pair_eq.
       }
        iFailWP "Hφ" UnSeal_fail_sealr.
     }
     destruct r1v as [ | [ | p g b e a ] | | ]; try inversion Hr1v. clear Hr1v.

     destruct (is_sealed r2v) eqn:Hr2v.
     2:{ (* Failure: r2 is not a sealrange *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_sealed in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" UnSeal_fail_sealed.
     }
     destruct r2v as [ | [ | ] | | a' sb ]; try inversion Hr2v. clear Hr2v.

     destruct (decide (permit_unseal p = true ∧ withinBounds b e a = true ∧ a' = a)) as [ [ Hpu [Hwb ->] ] | HFalse].
     2 : { (* Failure: one of the side conditions failed *)
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       assert (permit_unseal p = false ∨ withinBounds b e a = false ∨ a' ≠ a) as Hnot.
       { apply not_and_l in HFalse as [Hdone | HFalse].
         { apply not_true_is_false in Hdone. auto. }
         apply not_and_l in HFalse as [Hdone | HFalse].
         { apply not_true_is_false in Hdone. auto. }
         auto. }
       iFailWP "Hφ" UnSeal_fail_bounds.
     }

     destruct (incrementPC (<[ dst := (WSealable sb) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC (<[ dst := (WSealable sb) ]ᵣ> r) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         + by rewrite lookup_insert_is_Some'; eauto.
         + by apply insert_mono; eauto.
       }

       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iFailWP "Hφ" UnSeal_fail_incrPC.
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
     iPureIntro. eapply UnSeal_spec_success; eauto.
     rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
     Unshelve. all: auto.
  Qed.

  Lemma step_unseal_success E pc_p pc_g pc_b pc_e pc_a w w' dst r1 r2 p g b e a sb pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal dst r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    permit_unseal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ w' ∗
    r1 ↣ᵣ WSealRange p g b e a ∗
    r2 ↣ᵣ WSealed a sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealable sb ∗
    r1 ↣ᵣ WSealRange p g b e a ∗
    r2 ↣ᵣ WSealed a sb.
  Proof.
    iIntros (HE Hinstr Hvpc Hps Hwb Hpc_a' ???) "(#Hctx & Hj & HPC & Hpc_a & Hdst & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iMod (step_UnSeal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; last congruence.
      match goal with H: _ ∨ _ ∨ _ |- _ => destruct H as [ | [ | ] ] end; congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma step_unseal_r2 E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a sb pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    permit_unseal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange p g b e a ∗
    r2 ↣ᵣ WSealed a sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange p g b e a ∗
    r2 ↣ᵣ WSealable sb.
  Proof.
    iIntros (HE Hinstr Hvpc Hps Hwb Hpc_a' ??) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_UnSeal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ r2 PC) // insert_insert_eq (insert_insert_ne _ r1 r2) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; last congruence.
      match goal with H: _ ∨ _ ∨ _ |- _ => destruct H as [ | [ | ] ] end; congruence.
    }
    Unshelve. all: auto.
  Qed.

End spec_rules.
