From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Load.

(** * Spec rules for [Load] (spec copies of [rules_Load.v]) *)

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

  Lemma Load_spec_determ regs r1 r2 mem regs1 regs2 v1 v2 :
    Load_spec regs r1 r2 regs1 mem v1 →
    Load_spec regs r1 r2 regs2 mem v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ_gen Load_failure ltac:(unfold reg_allows_load in * ). Qed.

  Lemma Load_spec_imm_determ regs r1 r2 imm mem regs1 regs2 v1 v2 :
    Load_spec_imm regs r1 r2 imm regs1 mem v1 →
    Load_spec_imm regs r1 r2 imm regs2 mem v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ_gen Load_failure_imm ltac:(unfold reg_allows_load_imm in * ). Qed.

  Lemma step_load_general_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   dom mem = dom dfracs →

   spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↣ₐ{dw.1} dw.2) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Load_spec_imm regs r1 r2 imm regs' mem retv⌝ ∗
      ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↣ₐ{dw.1} dw.2) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq) "(#Hctx & Hj & Hmem & Hmap)".
    iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[r sr] m] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
    iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r2) as [r2v [Hr'2 Hr2]]; first by set_solver+.
    odestruct (Hri r1) as [r1v [Hr'1 _]]; first by set_solver+.
    clear Hri.
    (* Derive the PC in memory *)
    assert (is_Some (dfracs !! pc_a)) as [dq Hdq].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! pc_a = Some (dq,w)) as Hmem_dpc.
    { rewrite lookup_merge Hmem_pc Hdq //. }
    iDestruct (spec_mem_valid_inSepM_general (prod_merge dfracs mem) m with "Hm Hmem") as %Hma; eauto.

    eapply step_exec_inv in Hstep; eauto.

    rewrite /exec /= Hr2 /= in Hstep.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct (is_cap r2v) eqn:Hr2v.
     2:{ (* Failure: r2 is not a capability *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_cap in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" Load_fail_const_imm.
     }
     destruct r2v as [ | [t p g b e a | ] | | ]; try inversion Hr2v. clear Hr2v.
     destruct t.
     2: {
       inversion Hstep; subst c σ2.
       iFailWP "Hφ" Load_fail_tag_imm.
     }

    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { inversion Hstep; subst c σ2. iFailWP "Hφ" Load_fail_addr_imm. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iFailWP "Hφ" Load_fail_bounds_imm.
    }
    apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

    (* Prove that a is in the memory map now, otherwise we cannot continue *)
    assert (reg_allows_load_imm regs r2 imm p g b e a ea) as Hallow.
    { repeat split; auto. }
    destruct (allow_load_implies_loadv_imm r2 imm mem regs p g b e a ea HaLoad Hallow) as (loadv & Hmema).

    assert (is_Some (dfracs !! ea)) as [dq' Hdq'].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! ea = Some (dq',loadv)) as Hmemadq.
    { rewrite lookup_merge Hmema Hdq' //. }
    iDestruct (spec_mem_valid_inSepM_general (prod_merge dfracs mem) m ea loadv with "Hm Hmem" ) as %Hma' ; eauto.

    rewrite Hma' /= in Hstep.
    destruct (incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
    2: { (* Failure: the PC could not be incremented correctly *)
      assert (incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> r) = None).
      { eapply incrementPC_overflow_mono; first eapply Hregs'.
          + simplify_map_eq; by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto. }

      rewrite incrementPC_fail_updatePC /= in Hstep; auto.
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
      iFailWP "Hφ" Load_fail_invalid_PC_imm.
    }

    (* Success *)
    rewrite /update_reg /= in Hstep.
    eapply (incrementPC_success_updatePC _ sr m) in Hregs'
      as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
    iFrame.
    iMod ((spec_regs_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame.
    iPureIntro. eapply Load_spec_success_imm; auto.
    * exact Hallow.
    * exact Hmema.
    * rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
      Unshelve. all: auto.
  Qed.

  Lemma step_load_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem regs dq :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Load_spec_imm regs r1 r2 imm regs' mem retv⌝ ∗
      ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    intros. iIntros "(#Hctx & Hj & Hmem & Hreg)".
    iDestruct (spec_mem_remove_dq with "Hmem") as "Hmem".
    iMod (step_load_general_imm with "[$Hctx $Hj $Hmem $Hreg]")
      as (retv regs') "(Hj & Hspec & Hmem & Hmap)"; eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iDestruct (spec_mem_remove_dq with "Hmem") as "Hmem".
    iModIntro. iExists retv, regs'. iFrame.
  Qed.

  Lemma step_load_general Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true r2 regs mem →
   dom mem = dom dfracs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↣ₐ{dw.1} dw.2) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Load_spec regs r1 r2 regs' mem retv⌝ ∗
      ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↣ₐ{dw.1} dw.2) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Hmem HaLoad Hdom) "(#Hctx & Hj & Hres)".
    iMod (step_load_general_imm with "[$Hctx $Hj $Hres]")
      as (retv regs') "(Hj & %Hspec & Hmem & Hregs)"; eauto.
    { by apply allow_load_map_or_true_imm_zero. }
    iModIntro. iExists retv, regs'. iFrame. iPureIntro. by apply Load_spec_imm_zero.
  Qed.

  Lemma step_load Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem regs dq :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true r2 regs mem →
   spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Load_spec regs r1 r2 regs' mem retv⌝ ∗
      ([∗ map] a↦w ∈ mem, a ↣ₐ{dq} w) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    intros. iIntros "(#Hctx & Hj & Hmem & Hreg)".
    iDestruct (spec_mem_remove_dq with "Hmem") as "Hmem".
    iMod (step_load_general with "[$Hctx $Hj $Hmem $Hreg]")
      as (retv regs') "(Hj & Hspec & Hmem & Hmap)"; eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iDestruct (spec_mem_remove_dq with "Hmem") as "Hmem".
    iModIntro. iExists retv, regs'. iFrame.
  Qed.

  Lemma step_load_success E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    (if (eqb_addr a pc_a) then emp else a ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (eqb_addr a pc_a) then (load_word p w) else (load_word p w')) ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    (if (eqb_addr a pc_a) then emp else a ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hi & Hr1 & Hr2 & Hr2a)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iMod (step_load_general with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    { destruct (a =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iModIntro. iFrame.
       by destruct (a0 =? x4)%Z.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; [destruct o|].
       all: congruence.
     }
  Qed.

  Lemma step_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hinstr Hvpc Hrawb Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2 & Ha)".
    destruct (a =? pc_a)%Z eqn:Ha.
    - rewrite (_: a = pc_a); cycle 1.
      { apply Z.eqb_eq in Ha. solve_addr. }
      iDestruct (spec_mem_pointsto_agree with "Hpc_a Ha") as %->.
      iMod (step_load_success _ _ _ _ _ _ _ _ _ w' _ _ _ _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2]") as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & _)"; eauto.
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst a. auto. }
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst a. by rewrite /eqb_addr Z.eqb_refl. }
      rewrite /eqb_addr Z.eqb_refl.
      iModIntro. iFrame.
    - iMod (step_load_success with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2 Ha]")
        as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & Ha)"; eauto.
      { rewrite /eqb_addr Ha. iFrame. }
      rewrite /eqb_addr Ha.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e pc_a' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e pc_a.
  Proof.
    iIntros (HE Hinstr Hvpc Hrawb Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    iMod (step_load_success _ _ _ _ _ _ _ _ _ w _ _ _ _ _ _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2]") as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & _)"; eauto.
    { by rewrite /eqb_addr Z.eqb_refl. }
    rewrite /eqb_addr Z.eqb_refl.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    (if (a =? pc_a)%a then emp else a ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (a =? pc_a)%a then load_word p w else load_word p w') ∗
    pc_a ↣ₐ{dq} w ∗
    (if (a =? pc_a)%a then emp else a ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hinstr Hvpc Hra Hwb Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr1 & Hr1a)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iMod (step_load_general with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    { destruct (a =? pc_a)%a; by set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by destruct (a0 =? x4)%Z.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; [ destruct o |]; congruence. }
    Qed.

  Lemma step_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    a ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hinstr Hvpc Hra Hwb Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Ha)".
    destruct (a =? pc_a)%a eqn:Ha.
    - assert (a = pc_a) as -> by (apply Z.eqb_eq in Ha; solve_addr).
      iDestruct (spec_mem_pointsto_agree with "Hpc_a Ha") as %->.
      iMod (step_load_success_same _ _ _ _ _ _ _ _ w' w'' _ _ _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "(Hj & HPC & Hr1 & Hpc_a & _)"; eauto.
      { by rewrite Ha. }
      rewrite Ha.
      iModIntro. iFrame.
    - iMod (step_load_success_same with "[$Hctx $Hj $HPC $Hpc_a $Hr1 Ha]")
        as "(Hj & HPC & Hr1 & Hpc_a & Ha)"; eauto.
      { rewrite Ha. iFrame. }
      rewrite Ha.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same_frominstr E r1 pc_p pc_g pc_b pc_e pc_a w p g b e pc_a' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w.
  Proof.
    iIntros (HE Hinstr Hvpc Hra Hwb Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    iMod (step_load_success_same _ _ _ _ _ _ _ _ w w _ _ _ _ _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "(Hj & HPC & Hr1 & Hpc_a & _)"; eauto.
    { by rewrite Z.eqb_refl. }
    rewrite Z.eqb_refl.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_PC E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a (t : bool) p' g' b' e' a' a'' :
    ↑specN ⊆ E →
    decodeInstrW w = Load PC r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ WCap t p' g' b' e' a'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ load_word p (WCap t p' g' b' e' a'') ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ WCap t p' g' b' e' a'.
  Proof.
    iIntros (HE Hinstr Hvpc [Hra Hwb] Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr2 & Hr2a)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iMod (step_load with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map with (a := a) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H1 as [Hrr2 _]. simplify_map_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto.
       iFrame.
       by destruct p0; destruct dro,dl; rewrite /load_word in H1 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail.
       + simplify_map_eq; eauto.
       + simplify_map_eq; eauto.
       + simplify_map_eq; eauto.
         destruct o ; congruence.
       + simplify_map_eq; eauto.
         rewrite /load_word in e3 |- *.
         destruct (isDRO p0) eqn:HDRO, (isDL p0) eqn:HDL; cbn.
         all: try incrementPC_inv; simplify_map_eq; eauto.
         all: try congruence.
     }
  Qed.

  Lemma step_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 PC 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w''
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ load_word pc_p w.
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite spec_memMap_resource_1_dq.
    iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_load_map with (a := pc_a); eauto.
      by simplify_map_eq. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite -spec_memMap_resource_1_dq.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_ne //= insert_insert_eq insert_insert_ne //= insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       + apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
         destruct o; apply Is_true_false in H0; try congruence. done.
       + congruence.
     }
  Qed.

  Lemma step_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'.
  Proof.
    iIntros (HE Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hi & Hr1 & Hr2 & Hr2a)".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (spec_address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iMod (step_load_success with "[$Hctx $Hj $HPC $Hi $Hr1 $Hr2 Hr2a]")
      as "(Hj & HPC & Hr1 & Hi & Hr2 & Hr2a)"; eauto.
    { rewrite /eqb_addr Hfalse. iFrame. }
    rewrite /eqb_addr Hfalse.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same_alt E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    a ↣ₐ w'.
  Proof.
    iIntros (HE Hinstr Hvpc [Hra Hwb] Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Ha)".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (spec_address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iMod (step_load_success_same with "[$Hctx $Hj $HPC $Hpc_a $Hr1 Ha]") as "H"; eauto.
    { rewrite /eqb_addr Hfalse. iFrame. }
    rewrite /eqb_addr Hfalse.
    iModIntro. iExact "H".
  Qed.

  Lemma step_load_fail_not_cap E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' wsrc :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc = false ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true.
       destruct_word wsrc; cbn in *; try done.
       all: eexists true, RO, Global, za, za, za. (* dummy values *)
       all: split; rewrite /read_reg_inr; first by simplify_map_eq.
       all: rewrite /reg_allows_load; simplify_map_eq.
       all: rewrite decide_False; first done.
       all: intros (?&_&_); try done;  simplify_map_eq.
       all: destruct (decide (r2 = cnull)); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       rewrite /reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & _ & ?); simplify_eq.
       destruct (decide (r2 = cnull)); first done.
       simplify_eq.
     }
     by iModIntro; iFrame.
  Qed.

  Lemma step_load_fail_not_ra E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load; simplify_map_eq.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&?&_); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       rewrite /reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & ? & ?); simplify_eq.
       by rewrite H5 in Hbounds.
     }
     by iModIntro; iFrame.
  Qed.

  Lemma step_load_fail_not_withinbounds E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = false →
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed).
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load; simplify_map_eq.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&?); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       rewrite /reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & _ & ?); simplify_eq.
       by rewrite H5 in Hbounds.
     }
     by iModIntro.
  Qed.

  Lemma step_load_fail_tag E pc_p pc_g pc_b pc_e pc_a
      w dst src regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    get_tag wa = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hsrc Htag) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (step_instr_failed_map with "[$Hctx $Hj $Hpc_a $Hmap]"); [done..|].
    intros r sr m Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    rewrite /exec /= Hsrc' /=.
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
      subst; done.
  Qed.

  Lemma step_load_success_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    (if (eqb_addr ea pc_a) then emp else ea ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (eqb_addr ea pc_a) then (load_word p w) else (load_word p w')) ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    (if (eqb_addr ea pc_a) then emp else ea ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hi & Hr1 & Hr2 & Hr2a)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iMod (step_load_general_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iModIntro. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma step_load_success_same_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    (if (ea =? pc_a)%a then emp else ea ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (ea =? pc_a)%a then load_word p w else load_word p w') ∗
    pc_a ↣ₐ{dq} w ∗
    (if (ea =? pc_a)%a then emp else ea ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr1 & Hr1a)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iMod (step_load_general_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma step_load_success_notinstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hinstr Hvpc Hrawb Hadd Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2 & Ha)".
    destruct (ea =? pc_a)%a eqn:Ha.
    - assert (ea = pc_a) as -> by (apply Z.eqb_eq in Ha; solve_addr).
      iDestruct (spec_mem_pointsto_agree with "Hpc_a Ha") as %<-.
      iMod (step_load_success_imm _ _ _ _ _ _ _ _ _ w _ _ _ _ _ _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2]") as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & _)"; eauto.
      { by rewrite /eqb_addr Ha. }
      rewrite /eqb_addr Ha.
      iModIntro. iFrame.
    - iMod (step_load_success_imm with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2 Ha]")
        as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & Ha)"; eauto.
      { rewrite /eqb_addr Ha. iFrame. }
      rewrite /eqb_addr Ha.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_frominstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e a (imm : Z) pc_a' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap true p g b e a.
  Proof.
    iIntros (HE Hinstr Hvpc Hrawb Hadd Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hr2)".
    iMod (step_load_success_imm _ _ _ _ _ _ _ _ _ w _ _ _ _ _ _ pc_a _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hpc_a $Hr1 $Hr2]") as "(Hj & HPC & Hr1 & Hpc_a & Hr2 & _)"; eauto.
    { by rewrite /eqb_addr Z.eqb_refl. }
    rewrite /eqb_addr Z.eqb_refl.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    ea ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Ha)".
    destruct (ea =? pc_a)%a eqn:Ha.
    - assert (ea = pc_a) as -> by (apply Z.eqb_eq in Ha; solve_addr).
      iDestruct (spec_mem_pointsto_agree with "Hpc_a Ha") as %<-.
      iMod (step_load_success_same_imm _ _ _ _ _ _ _ _ w _ _ _ _ _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "(Hj & HPC & Hr1 & Hpc_a & _)"; eauto.
      { by rewrite Ha. }
      rewrite Ha.
      iModIntro. iFrame.
    - iMod (step_load_success_same_imm with "[$Hctx $Hj $HPC $Hpc_a $Hr1 Ha]")
        as "(Hj & HPC & Hr1 & Hpc_a & Ha)"; eauto.
      { rewrite Ha. iFrame. }
      rewrite Ha.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_same_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w p g b e a (imm : Z) pc_a' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w.
  Proof.
    iIntros (HE Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
    iMod (step_load_success_same_imm _ _ _ _ _ _ _ _ w _ _ _ _ _ pc_a _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hpc_a $Hr1]") as "(Hj & HPC & Hr1 & Hpc_a & _)"; eauto.
    { by rewrite Z.eqb_refl. }
    rewrite Z.eqb_refl.
    iModIntro. iFrame.
  Qed.

  Lemma step_load_success_alt_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'.
  Proof.
    iIntros (HE Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hi & Hr1 & Hr2 & Hr2a)".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (spec_address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iMod (step_load_success_imm with "[$Hctx $Hj $HPC $Hi $Hr1 $Hr2 Hr2a]") as "H"; eauto.
    { rewrite /eqb_addr Hfalse. iFrame. }
    rewrite /eqb_addr Hfalse.
    iModIntro. iExact "H".
  Qed.

  Lemma step_load_success_same_alt_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ w'.
  Proof.
    iIntros (HE Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Ha)".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (spec_address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iMod (step_load_success_same_imm with "[$Hctx $Hj $HPC $Hpc_a $Hr1 Ha]") as "H"; eauto.
    { rewrite /eqb_addr Hfalse. iFrame. }
    rewrite /eqb_addr Hfalse.
    iModIntro. iExact "H".
  Qed.

  Lemma step_load_fail_tag_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    get_tag wa = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hsrc Htag) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (step_instr_failed_map with "[$Hctx $Hj $Hpc_a $Hmap]"); [done..|].
    intros r sr m Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    rewrite /exec /= Hsrc' /=.
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
      subst; done.
  Qed.

  Lemma step_load_fail_not_ra_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a (imm : Z) :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load_imm with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true_imm.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load_imm; simplify_map_eq.
         destruct (a + imm)%a; cbn; last done.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&?&_); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. congruence.
     }
     by iModIntro; iFrame.
  Qed.

  Lemma step_load_fail_not_withinbounds_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e ea = false →
    (a + imm)%a = Some ea →
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hadd Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load_imm with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true_imm.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load_imm; simplify_map_eq.
         try rewrite Hadd.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&_&?); done.
     }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [| Hfail].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq). congruence.
     }
     by iModIntro; iFrame.
  Qed.

  Lemma step_load_success_PC_imm E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    ↑specN ⊆ E →
    decodeInstrW w = Load PC r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ WCap t p' g' b' e' a'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ load_word p (WCap t p' g' b' e' a'') ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ WCap t p' g' b' e' a'.
  Proof.
    iIntros (HE Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr2 & Hr2a)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iMod (step_load_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map_imm with (a := a) (ea := ea) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H1 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto.
       iFrame.
       by destruct p0; destruct dro,dl; rewrite /load_word in H1 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
       all: match goal with H : incrementPC _ = None |- _ =>
         rewrite /load_word in H end.
       all: destruct (isDRO p0) eqn:HDRO, (isDL p0) eqn:HDL; cbn.
       all: try incrementPC_inv; simplify_map_eq; eauto; try congruence.
     }
  Qed.

  Lemma step_load_fail_addr_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some (WCap true p g b e a) →
    (a + imm)%a = None →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hsrc Hadd) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (step_instr_failed_map with "[$Hctx $Hj $Hpc_a $Hmap]"); [done..|].
    intros r sr m Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    rewrite /exec /= Hsrc' /=.
    rewrite Hadd /=. done.
  Qed.

  Lemma step_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    is_cap wa = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs, k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Hsrc Htag) "(#Hctx & Hj & Hpc_a & Hmap)".
    iApply (step_instr_failed_map with "[$Hctx $Hj $Hpc_a $Hmap]"); [done..|].
    intros r sr m Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    rewrite /exec /= Hsrc' /=.
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
      subst; done.
  Qed.

  Lemma step_load_fail_not_cap_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' wsrc (imm : Z) :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc = false ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
  Proof.
    iIntros (HE Hdecode Hvpc Hcap) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrc)".
    iDestruct (spec_map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iMod (step_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a w r1 r2 imm _ (if decide (r2 = cnull) then WInt 0 else wsrc) with "[$Hctx $Hj $Hi $Hmap]") as "(Hj & _)"; eauto; simplify_map_eq; eauto.
    all: try by case_decide.
    all: by iModIntro; iFrame.
  Qed.

  Lemma step_load_success_fromPC_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    (if (ea =? pc_a)%a then emp else ea ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (ea =? pc_a)%a then load_word pc_p w else load_word pc_p w') ∗
    pc_a ↣ₐ{dq} w ∗
    (if (ea =? pc_a)%a then emp else ea ↣ₐ{dq'} w').
  Proof.
    iIntros (HE Hinstr Hvpc Hwb Hadd Hpca' Hcnull) "(#Hctx & Hj & HPC & Hi & Hr1 & Hr1a)".
    assert (readAllowed pc_p = true) as Hra.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc. apply andb_prop_elim in Hpc as [Hra _]. by apply Is_true_true. }
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_dq _ _ _ _ _ _ (λ a dq w, a ↣ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iMod (step_load_general_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma step_load_success_PC_PC_imm E pc_p pc_g pc_b pc_e pc_a w
        ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    ↑specN ⊆ E →
    decodeInstrW w = Load PC PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (a' + 1)%a = Some a'' →

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ WCap t p' g' b' e' a'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ load_word pc_p (WCap t p' g' b' e' a'') ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ WCap t p' g' b' e' a'.
  Proof.
    iIntros (HE Hinstr Hvpc Hwb Hadd Hpca') "(#Hctx & Hj & HPC & Hi & Hr2a)".
    assert (readAllowed pc_p = true) as Hra.
    { apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra _]. by apply Is_true_true. }
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iMod (step_load_imm with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply mem_neq_implies_allow_load_map_imm with (a := pc_a) (ea := ea) (pc_a := pc_a); eauto.
    }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iModIntro.
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "Hmap") as "HPC".
       iFrame.
       by destruct p; destruct dro,dl; rewrite /load_word in H0 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
       all: match goal with H : incrementPC _ = None |- _ =>
         rewrite /load_word in H end.
       all: destruct (isDRO p) eqn:HDRO, (isDL p) eqn:HDL; cbn.
       all: try incrementPC_inv; simplify_map_eq; eauto; try congruence.
     }
  Qed.

  Lemma step_load_success_fromPC_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' ea (imm : Z) pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    ea ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word pc_p w' ∗
    pc_a ↣ₐ{dq} w ∗
    ea ↣ₐ{dq'} w'.
  Proof.
    iIntros (HE Hinstr Hvpc Hwb Hadd Hincr Hnull) "(#Hctx & Hj & HPC & Hi & Hr & Hm)".
    destruct (ea =? pc_a)%a eqn:Heq.
    - assert (ea = pc_a) as -> by (apply Z.eqb_eq in Heq; solve_addr).
      iDestruct (spec_mem_pointsto_agree with "Hi Hm") as %<-.
      iMod (step_load_success_fromPC_imm _ _ _ _ _ _ _ _ w _ _ _ _ _ dq'
             with "[$Hctx $Hj $HPC $Hi $Hr]") as "(Hj & HPC & Hr & Hi & _)"; eauto.
      { by rewrite Heq. }
      rewrite Heq.
      iModIntro. iFrame.
    - iMod (step_load_success_fromPC_imm with "[$Hctx $Hj $HPC $Hi $Hr Hm]")
        as "(Hj & HPC & Hr & Hi & Hm)"; eauto.
      { rewrite Heq. iFrame. }
      rewrite Heq.
      iModIntro. iFrame.
  Qed.

  Lemma step_load_success_fromPC_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' dq (imm : Z) :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w''
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ load_word pc_p w.
  Proof.
    iIntros (HE Hinstr Hvpc Hadd Hincr Hnull) "(#Hctx & Hj & HPC & Hi & Hr)".
    assert (withinBounds pc_b pc_e pc_a = true) as Hwb.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc.
      apply andb_prop_elim in Hpc as [_ Hwb]. by apply Is_true_true. }
    iMod (step_load_success_fromPC_imm _ _ _ _ _ _ _ _ w _ pc_a _ _ _ DfracDiscarded
           with "[$Hctx $Hj $HPC $Hi $Hr]") as "(Hj & HPC & Hr & Hi & _)"; eauto.
    { by rewrite Z.eqb_refl. }
    rewrite Z.eqb_refl.
    iModIntro. iFrame.
  Qed.


End spec_rules.
