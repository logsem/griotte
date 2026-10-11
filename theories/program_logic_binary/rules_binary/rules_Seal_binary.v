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
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
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
     2:{ (* Failure: the source has the wrong shape *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_sealr in Hr1v.
         destruct_word r1v; by simplify_pair_eq.
       }
        iFailWP "Hφ" Seal_fail_sealr.
     }
     destruct r1v as [ | [ | t p g b e a ] | | ]; try inversion Hr1v. clear Hr1v.
     destruct (is_sealb r2v) eqn:Hr2v.
     2:{ (* Failure: the source has the wrong shape *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_sealb in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" Seal_fail_sealb.
     }
     destruct r2v as [ | sb | | ]; try inversion Hr2v. clear Hr2v.

     destruct (t && get_tag_sealable sb && permit_seal p && withinBounds b e a) eqn:Hvalid.
     2: { (* Invalidation continues with the wrapper changed and the payload tag cleared. *)
     destruct (incrementPC (<[ dst := (WSealed a (clear_tag_sealable sb)) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC (<[ dst := (WSealed a (clear_tag_sealable sb)) ]ᵣ> r) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         + by rewrite lookup_insert_is_Some'; eauto.
         + by apply insert_mono; eauto.
       }

       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iFailWP "Hφ" Seal_fail_invalidated_PC.
     }

     (* Success *)
     rewrite /update_reg /= in Hstep.
     eapply (incrementPC_success_updatePC _ sr m) in Hregs'
       as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     { apply is_Some_lookup_reg; done. }
     iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply Seal_spec_invalidated; eauto.
     rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
     }
     apply andb_true_iff in Hvalid as [Hvalid Hwb].
     apply andb_true_iff in Hvalid as [Hvalid Hps].
     apply andb_true_iff in Hvalid as [-> Htag].
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
       as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
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

  Lemma step_seal_success E pc_p pc_g pc_b pc_e pc_a w w' dst r1 r2 p g b e a sb pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Seal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ w' ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealable sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealed a sb ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealable sb.
  Proof.
    iIntros (HE Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull' Hncull'') "(#Hctx & Hj & HPC & Hpc_a & Hdst & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iMod (step_Seal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
  Qed.

  Lemma step_seal_r1 E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a sb pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Seal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealable sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealed a sb ∗
    r2 ↣ᵣ WSealable sb.
  Proof.
    iIntros (HE Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_Seal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma step_seal_r2 E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a sb pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Seal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealable sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealed a sb.
  Proof.
    iIntros (HE Hinstr Hvpc Htag Hps Hwb Hpc_a' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_Seal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ r2 PC) // insert_insert_eq (insert_insert_ne _ r1 r2) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma step_seal_PC E pc_p pc_g pc_b pc_e pc_a w w' dst r1 p g b e a pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Seal dst r1 PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ w' ∗
    r1 ↣ᵣ WSealRange true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealed a (SCap true pc_p pc_g pc_b pc_e pc_a) ∗
    r1 ↣ᵣ WSealRange true p g b e a.
  Proof.
    iIntros (HE Hinstr Hvpc Hps Hwb Hpc_a' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hdst & Hr1)".
    iDestruct (spec_map_of_regs_3 with "HPC Hdst Hr1") as "[Hmap (%&%&%)]".
    iMod (step_Seal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ dst PC) // insert_insert_eq (insert_insert_ne _ dst r1) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

 Lemma step_seal_PC_eq E pc_p pc_g pc_b pc_e pc_a w w' r1 p g b e a pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Seal r1 r1 PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    permit_seal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealed a (SCap true pc_p pc_g pc_b pc_e pc_a).
  Proof.
    iIntros (HE Hinstr Hvpc Hps Hwb Hpc_a' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iMod (step_Seal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ r1 PC) // !insert_insert_eq.
      iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma step_seal_nosb_r2 E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a w2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Seal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    is_sealb w2 = false →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ w2
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
    iIntros (HE Hinstr Hvpc Hpc_a' Hfalse Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".

    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_Seal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | ]; last by iModIntro; iFrame.
    all: by simplify_map_eq.
  Qed.

  Local Lemma seal_invalidated_map E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a sb :
    ↑specN ⊆ E →
    decodeInstrW w = Seal dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Seal dst src1 src2) ⊆ dom regs →
    regs !!ᵣ src1 = Some (WSealRange t p g b e a) →
    regs !!ᵣ src2 = Some (WSealable sb) →
    t && get_tag_sealable sb && permit_seal p && withinBounds b e a = false →
    incrementPC (<[ dst := WSealed a (clear_tag_sealable sb) ]ᵣ> regs) = Some regs' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Hr1 Hr2 Hvalid Hincr) "(#Hctx & Hj & Hpc_a & Hmap)".
    iMod (step_Seal with "[$Hctx $Hj $Hpc_a $Hmap]") as "H"; eauto.
    iDestruct "H" as (retv regs'') "(Hj & %Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | Hfail].
    - simplify_eq.
      repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
    - simplify_eq. iModIntro. iFrame.
    - destruct Hfail; simplify_eq; cbn in *; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
  Qed.

  Lemma step_seal_invalidated E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a r2 sb dst (wd : Word) :
    ↑specN ⊆ E →
    decodeInstrW w = Seal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealable sb ∗
    dst ↣ᵣ wd
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealable sb ∗
    dst ↣ᵣ (if decide (dst = cnull) then WInt 0 else WSealed a (clear_tag_sealable (sb))).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hnull2 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2 & Hr3)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iMod (seal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealRange t p g b e a]> (<[r2 := WSealable sb]> (<[dst := (if decide (dst
        = cnull) then WInt 0 else WSealed a (clear_tag_sealable (sb)))]> (∅ : Reg))))) t p g b e a
        (sb) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_4 with "Hmap"); eauto.
  Qed.

  Lemma step_seal_invalidated_r1 E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a r2 sb :
    ↑specN ⊆ E →
    decodeInstrW w = Seal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealable sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealed a (clear_tag_sealable (sb)) ∗
    r2 ↣ᵣ WSealable sb.
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hnull2 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (seal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealed a (clear_tag_sealable (sb))]> (<[r2 := WSealable sb]> (∅ : Reg))))
        t p g b e a (sb) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma step_seal_invalidated_r2 E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a r2 sb :
    ↑specN ⊆ E →
    decodeInstrW w = Seal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_seal p && withinBounds b e a = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealable sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealed a (clear_tag_sealable (sb)).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hnull2 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (seal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealRange t p g b e a]> (<[r2 := WSealed a (clear_tag_sealable (sb))]> (∅
        : Reg)))) t p g b e a (sb) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma step_seal_invalidated_same E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a dst (wd : Word) :
    ↑specN ⊆ E →
    decodeInstrW w = Seal dst r1 r1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SSealRange t p g b e a) && permit_seal p && withinBounds b e a = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    dst ↣ᵣ wd
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    dst ↣ᵣ (if decide (dst = cnull) then WInt 0 else WSealed a (clear_tag_sealable (SSealRange t p g b e a))).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (seal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealRange t p g b e a]> (<[dst := (if decide (dst = cnull) then WInt 0
        else WSealed a (clear_tag_sealable (SSealRange t p g b e a)))]> (∅ : Reg)))) t p g b e a
        (SSealRange t p g b e a) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma step_seal_invalidated_all E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Seal r1 r1 r1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SSealRange t p g b e a) && permit_seal p && withinBounds b e a = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealed a (clear_tag_sealable (SSealRange t p g b e a)).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iMod (seal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealed a (clear_tag_sealable (SSealRange t p g b e a))]> (∅ : Reg))) t p g
        b e a (SSealRange t p g b e a) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma step_seal_invalidated_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a dst (wd : Word) :
    ↑specN ⊆ E →
    decodeInstrW w = Seal dst r1 PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a) && permit_seal p && withinBounds b e a = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    dst ↣ᵣ wd
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    dst ↣ᵣ (if decide (dst = cnull) then WInt 0 else WSealed a (clear_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a))).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (seal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealRange t p g b e a]> (<[dst := (if decide (dst = cnull) then WInt 0
        else WSealed a (clear_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a)))]> (∅ : Reg)))) t p
        g b e a (SCap true pc_p pc_g pc_b pc_e pc_a) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma step_seal_invalidated_PC_eq E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Seal r1 r1 PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    t && get_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a) && permit_seal p && withinBounds b e a = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealed a (clear_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a)).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iMod (seal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealed a (clear_tag_sealable (SCap true pc_p pc_g pc_b pc_e pc_a))]> (∅ :
        Reg))) t p g b e a (SCap true pc_p pc_g pc_b pc_e pc_a) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_2 with "Hmap"); eauto.
  Qed.


End spec_rules.
