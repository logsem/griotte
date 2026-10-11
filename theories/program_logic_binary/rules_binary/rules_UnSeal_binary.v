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

  (** Physical spec-side outcomes, for the spec run. *)

  Inductive spec_UnSeal_failure  (regs: Reg) (dst: RegName) (src1 src2: RegName) : Reg → Prop :=
  | spec_UnSeal_fail_sealr w :
      regs !!ᵣ src1 = Some w →
      is_sealr w = false →
      spec_UnSeal_failure regs dst src1 src2 regs
  | spec_UnSeal_fail_sealed w :
      regs !!ᵣ src2 = Some w →
      is_sealed w = false →
      spec_UnSeal_failure regs dst src1 src2 regs
  | spec_UnSeal_fail_invalidated_PC (t : bool) p g b e a a' sb :
      regs !!ᵣ src1 = Some (WSealRange t p g b e a) →
      regs !!ᵣ src2 = Some (WSealed a' sb) →
      t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
      spec_incrementPC (<[ dst := WSealable (clear_tag_sealable (machine_word.unseal g sb)) ]ᵣ> regs) = None →
      spec_UnSeal_failure regs dst src1 src2 regs
  | spec_UnSeal_fail_incrPC p g b e a o sb :
      regs !!ᵣ src1 = Some (WSealRange true p g b e a) →
      regs !!ᵣ src2 = Some (WSealed o sb) →
      get_tag_sealable sb = true →
      permit_unseal p = true →
      withinBounds b e o = true →
      spec_incrementPC (<[ dst := WSealable (machine_word.unseal g sb) ]ᵣ> regs) = None →
      spec_UnSeal_failure regs dst src1 src2 regs.

  Inductive spec_UnSeal_spec (regs: Reg) (dst: RegName) (src1 src2: RegName) (regs': Reg): griotte_lang.val -> Prop :=
  | spec_UnSeal_spec_success p g b e a o sb:
      regs !!ᵣ src1 = Some (WSealRange true p g b e a) →
      regs !!ᵣ src2 = Some (WSealed o sb) →
      get_tag_sealable sb = true →
      permit_unseal p = true →
      withinBounds b e o = true →
      spec_incrementPC (<[ dst := WSealable (machine_word.unseal g sb) ]ᵣ> regs) = Some regs' →
      spec_UnSeal_spec regs dst src1 src2 regs' NextIV
  | spec_UnSeal_spec_invalidated (t : bool) p g b e a a' sb :
      regs !!ᵣ src1 = Some (WSealRange t p g b e a) →
      regs !!ᵣ src2 = Some (WSealed a' sb) →
      t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
      spec_incrementPC (<[ dst := WSealable (clear_tag_sealable (machine_word.unseal g sb)) ]ᵣ> regs) = Some regs' →
      spec_UnSeal_spec regs dst src1 src2 regs' NextIV
  | spec_UnSeal_spec_failure :
      spec_UnSeal_failure regs dst src1 src2 regs' →
      spec_UnSeal_spec regs dst src1 src2 regs' FailedV.

  Lemma UnSeal_spec_determ regs dst src1 src2 regs1 regs2 v1 v2 :
    spec_UnSeal_spec regs dst src1 src2 regs1 v1 →
    spec_UnSeal_spec regs dst src1 src2 regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ spec_UnSeal_failure. Qed.

  Lemma UnSeal_spec_lift regs dst src1 src2 lregs' v :
    UnSeal_spec (lift_regs regs) dst src1 src2 lregs' v →
    ∃ regs', (v = NextIV → lregs' = lift_regs regs') ∧ spec_UnSeal_spec regs dst src1 src2 regs' v.
  Proof. spec_lift UnSeal_failure regs. Qed.

  Lemma step_UnSeal Ep pc_p pc_g pc_b pc_e pc_a w dst src1 src2 regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = UnSeal dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ spec_UnSeal_spec regs dst src1 src2 regs' retv ⌝ ∗
      pc_a ↣ₐ w ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[[r sr] m] st] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
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
     2:{ (* Failure: the source has the wrong shape *)
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       {
         unfold is_sealr in Hr1v.
         destruct_word r1v; by simplify_pair_eq.
       }
        iFailWP "Hφ" spec_UnSeal_fail_sealr.
     }
     destruct r1v as [ | [ | t p g b e a ] | | ]; try inversion Hr1v. clear Hr1v.
     destruct (is_sealed r2v) eqn:Hr2v.
     2:{ (* Failure: the source has the wrong shape *)
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       {
         unfold is_sealed in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" spec_UnSeal_fail_sealed.
     }
     destruct r2v as [ | [ | ] | | a' sb ]; try inversion Hr2v. clear Hr2v.

     destruct (t && get_tag_sealable sb && permit_unseal p && withinBounds b e a') eqn:Hvalid.
     2: { (* Invalidation continues with the wrapper changed and the payload tag cleared. *)
     destruct (spec_incrementPC (<[ dst := (WSealable (clear_tag_sealable (machine_word.unseal g sb))) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (spec_incrementPC (<[ dst := (WSealable (clear_tag_sealable (machine_word.unseal g sb))) ]ᵣ> r) = None).
       { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
         + by rewrite lookup_insert_is_Some'; eauto.
         + by apply insert_mono; eauto.
       }

       rewrite spec_incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iFailWP "Hφ" spec_UnSeal_fail_invalidated_PC.
     }

     (* Success *)
     rewrite /update_reg /= in Hstep.
     eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
       as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     { apply is_Some_lookup_reg; done. }
     iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply spec_UnSeal_spec_invalidated; eauto.
     rewrite /spec_incrementPC /spec_incrementPC_gen. by rewrite HPC'' Ha_pc'.
     }
     apply andb_true_iff in Hvalid as [Hvalid Hwb].
     apply andb_true_iff in Hvalid as [Hvalid Hps].
     apply andb_true_iff in Hvalid as [-> Htag].
     destruct (spec_incrementPC (<[ dst := (WSealable (machine_word.unseal g sb)) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (spec_incrementPC (<[ dst := (WSealable (machine_word.unseal g sb)) ]ᵣ> r) = None).
       { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
         + by rewrite lookup_insert_is_Some'; eauto.
         + by apply insert_mono; eauto.
       }

       rewrite spec_incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iFailWP "Hφ" spec_UnSeal_fail_incrPC.
     }

     (* Success *)
     rewrite /update_reg /= in Hstep.
     eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
       as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     { apply is_Some_lookup_reg; done. }
     iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply spec_UnSeal_spec_success; eauto.
     rewrite /spec_incrementPC /spec_incrementPC_gen. by rewrite HPC'' Ha_pc'.
     Unshelve. all: auto.
  Qed.

  Lemma step_unseal_success E pc_p pc_g pc_b pc_e pc_a w w' dst r1 r2 p g b e a o sb pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
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
    r2 ↣ᵣ WSealed o sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealable (machine_word.unseal g sb) ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealed o sb.
  Proof.
    iIntros (HE Hinstr Hvpc Htag Hps Hwb Hpc_a' ???) "(#Hctx & Hj & HPC & Hpc_a & Hdst & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iMod (step_UnSeal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma step_unseal_r1 E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a o sb pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealed o sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealable (machine_word.unseal g sb) ∗
    r2 ↣ᵣ WSealed o sb.
  Proof.
    iIntros (HE Hinstr Hvpc Htag Hps Hwb Hpc_a' ??) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_UnSeal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma step_unseal_r2 E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a o sb pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealed o sb
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealable (machine_word.unseal g sb).
  Proof.
    iIntros (HE Hinstr Hvpc Htag Hps Hwb Hpc_a' ??) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_UnSeal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ r2 PC) // insert_insert_eq (insert_insert_ne _ r1 r2) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma step_unseal_PC E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a o p' g' b' e' a' a'' :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal PC r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    permit_unseal p = true →
    withinBounds b e o = true →
    (a' + 1)%a = Some a'' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealed o (SCap true p' g' b' e' a')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true p' (unseal_locality g g') b' e' a'' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange true p g b e a ∗
    r2 ↣ᵣ WSealed o (SCap true p' g' b' e' a').
  Proof.
    iIntros (HE Hinstr Hvpc Hps Hwb Hpc_a' ??) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iMod (step_UnSeal with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; congruence).
    { (* Success *)
      iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Local Lemma unseal_invalidated_map E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a a' sb :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →
    regs !!ᵣ src1 = Some (WSealRange t p g b e a) →
    regs !!ᵣ src2 = Some (WSealed a' sb) →
    t && get_tag_sealable sb && permit_unseal p && withinBounds b e a' = false →
    spec_incrementPC (<[ dst := WSealable (clear_tag_sealable (machine_word.unseal g sb)) ]ᵣ> regs) = Some regs' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Hr1 Hr2 Hvalid Hincr) "(#Hctx & Hj & Hpc_a & Hmap)".
    iMod (step_UnSeal with "[$Hctx $Hj $Hpc_a $Hmap]") as "H"; eauto.
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

  Lemma step_unseal_invalidated E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 (t : bool) p g b e a (o :
      OType) sb dst (wd : Word) :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealed o (sb) ∗
    dst ↣ᵣ wd
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealed o (sb) ∗
    dst ↣ᵣ (if decide (dst = cnull) then WInt 0 else WSealable (clear_tag_sealable (machine_word.unseal g sb))).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hnull2 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2 & Hr3)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iMod (unseal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealRange t p g b e a]> (<[r2 := WSealed o (sb)]> (<[dst := (if decide
        (dst = cnull) then WInt 0 else WSealable (clear_tag_sealable (machine_word.unseal g sb)))]> (∅ : Reg))))) t p g b
        e a o (sb) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /spec_incrementPC /spec_incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_4 with "Hmap"); eauto.
  Qed.

  Lemma step_unseal_invalidated_r1 E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 (t : bool) p g b e a (o :
      OType) sb :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealed o (sb)
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealable (clear_tag_sealable (machine_word.unseal g sb)) ∗
    r2 ↣ᵣ WSealed o (sb).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hnull2 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (unseal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealable (clear_tag_sealable (machine_word.unseal g sb))]> (<[r2 := WSealed o (sb)]> (∅ :
        Reg)))) t p g b e a o (sb) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /spec_incrementPC /spec_incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma step_unseal_invalidated_r2 E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 (t : bool) p g b e a (o :
      OType) sb :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e o = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealed o (sb)
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealable (clear_tag_sealable (machine_word.unseal g sb)).
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hnull2 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (unseal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealRange t p g b e a]> (<[r2 := WSealable (clear_tag_sealable (machine_word.unseal g sb))]> (∅
        : Reg)))) t p g b e a o (sb) with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /spec_incrementPC /spec_incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma step_unseal_invalidated_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 (t : bool) p g b e a (o :
      OType) (t' : bool) p' g' b' e' a' :
    ↑specN ⊆ E →
    decodeInstrW w = UnSeal PC r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (a' + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (SCap t' p' g' b' e' a') && permit_unseal p && withinBounds b e o = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealed o (SCap t' p' g' b' e' a')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap false p' (unseal_locality g g') b' e' pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    r2 ↣ᵣ WSealed o (SCap t' p' g' b' e' a').
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull1 Hnull2 Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (unseal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false p' (unseal_locality g g') b' e' pc_a']>
        (<[r1 := WSealRange t p g b e a]> (<[r2 := WSealed o (SCap t' p' g' b' e' a')]> (∅ : Reg))))
        t p g b e a o (SCap t' p' g' b' e' a') with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /spec_incrementPC /spec_incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_3 with "Hmap"); eauto.
  Qed.


End spec_rules.
