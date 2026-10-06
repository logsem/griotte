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

  Lemma step_load_general Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Load r1 r2 →
   isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2) ⊆ dom regs →
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
        iFailWP "Hφ" Load_fail_const.
     }
     destruct r2v as [ | [p g b e a | ] | | ]; try inversion Hr2v. clear Hr2v.

    destruct (readAllowed p && withinBounds b e a) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iFailWP "Hφ" Load_fail_bounds.
    }
    apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

    (* Prove that a is in the memory map now, otherwise we cannot continue *)
    pose proof (allow_load_implies_loadv r2 mem regs p g b e a) as (loadv & Hmema); auto.

    assert (is_Some (dfracs !! a)) as [dq' Hdq'].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! a = Some (dq',loadv)) as Hmemadq.
    { rewrite lookup_merge Hmema Hdq' //. }
    iDestruct (spec_mem_valid_inSepM_general (prod_merge dfracs mem) m a loadv with "Hm Hmem" ) as %Hma' ; eauto.

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
      iFailWP "Hφ" Load_fail_invalid_PC.
    }

    (* Success *)
    rewrite /update_reg /= in Hstep.
    eapply (incrementPC_success_updatePC _ sr m) in Hregs'
      as (p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
    iFrame.
    iMod ((spec_regs_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame.
    iPureIntro. eapply Load_spec_success; auto.
    * split; eauto.
    * exact Hmema.
    * rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
      Unshelve. all: auto.
  Qed.

  Lemma step_load Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem regs dq :
    ↑specN ⊆ Ep →
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Load r1 r2) ⊆ dom regs →
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
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap p g b e a ∗
    (if (eqb_addr a pc_a) then emp else a ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ (if (eqb_addr a pc_a) then (load_word p w) else (load_word p w')) ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap p g b e a ∗
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
       by destruct (a0 =? x3)%Z.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; [destruct o|].
       all: congruence.
     }
  Qed.

  Lemma step_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap p g b e a ∗
    a ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap p g b e a ∗
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
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w ∗
    pc_a ↣ₐ{dq} w ∗
    r2 ↣ᵣ WCap p g b e pc_a.
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
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap p g b e a ∗
    (if (a =? pc_a)%a then emp else a ↣ₐ{dq'} w')
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
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
       by destruct (a0 =? x3)%Z.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; [ destruct o |]; congruence. }
    Qed.

  Lemma step_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap p g b e a ∗
    a ↣ₐ{dq'} w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
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
    decodeInstrW w = Load r1 r1 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ WCap p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
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

  Lemma step_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↣ᵣ load_word p w' ∗
    pc_a ↣ₐ w ∗
    r2 ↣ᵣ WCap p g b e a ∗
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

  Lemma step_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' dq :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 PC →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ{dq} w ∗
    r1 ↣ᵣ w''
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
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

  Lemma step_load_fail_not_withinbounds E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a :
    ↑specN ⊆ E →
    decodeInstrW w = Load r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = false →
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ w'' ∗
    r2 ↣ᵣ WCap p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed).
  Proof.
     iIntros (HE Hdecode Hvpc Hbounds Hcnull) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite spec_memMap_resource_1_dq.
     iMod (step_load with "[$Hctx $Hj $Hmap $Hi]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true.
       exists p, g, b, e, a.
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

End spec_rules.
