From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Store.

(** * Spec rules for [Store] (spec copies of [rules_Store.v]) *)

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

  Lemma Store_spec_determ regs r1 r2 mem regs1 regs2 mem1 mem2 v1 v2 :
    Store_spec regs r1 r2 regs1 mem mem1 v1 →
    Store_spec regs r1 r2 regs2 mem mem2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2 ∧ mem1 = mem2).
  Proof. solve_spec_determ_gen Store_failure ltac:(unfold reg_allows_store in * ). Qed.

  Lemma Store_spec_determ_arg regs r1 (r2 : Z + RegName) mem regs1 regs2 mem1 mem2 v1 v2 :
    Store_spec regs r1 r2 regs1 mem mem1 v1 →
    Store_spec regs r1 r2 regs2 mem mem2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2 ∧ mem1 = mem2).
  Proof. solve_spec_determ_gen Store_failure ltac:(unfold reg_allows_store in * ). Qed.

  Lemma Store_spec_imm_determ regs r1 (r2 : Z + RegName) imm mem regs1 regs2 mem1 mem2 v1 v2 :
    Store_spec_imm regs r1 r2 imm regs1 mem mem1 v1 →
    Store_spec_imm regs r1 r2 imm regs2 mem mem2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2 ∧ mem1 = mem2).
  Proof. solve_spec_determ_gen Store_failure_imm ltac:(unfold reg_allows_store_imm in * ). Qed.

   Lemma step_store_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) (imm : Z) w mem regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Store r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true_imm r1 r2 imm regs mem →

   spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    ([∗ map] a↦w ∈ mem, a ↣ₐ w) ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs' mem',
      ⤇ Seq (of_val retv) ∗
      ⌜ Store_spec_imm regs r1 r2 imm regs' mem mem' retv⌝ ∗
      ([∗ map] a↦w ∈ mem', a ↣ₐ w) ∗
      [∗ map] k↦y ∈ regs', k ↣ᵣ y.
   Proof.
     iIntros (HE Hinstr Hvpc HPC Dregs Hmem_pc HaStore) "(#Hctx & Hj & Hmem & Hmap)".
     iApply (spec_step_exec_2 with "Hctx Hj"); first done.
     iIntros (Φ) "Hφ". iIntros ([[r sr] m] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
     iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.

     (* Derive necessary register values in r *)
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
     odestruct (Hri r1) as [r1v [Hr'1 Hr1]]; first by set_solver+.
     iDestruct (spec_mem_valid_inSepM mem m with "Hm Hmem") as %Hma; eauto.

     eapply step_exec_inv in Hstep; eauto.

     rewrite /exec /= Hr1 /= in Hstep.

     (* Now we start splitting on the different cases in the Store spec, and prove them one at a time *)

     destruct (word_of_argument regs r2) as [ storev | ] eqn:HSV.
     2: {
       destruct r2 as [z | r2].
       - cbn in HSV; inversion HSV.
       - destruct (Hri r2) as [r0v [Hr0 _] ]; first by set_solver+.
         cbn in HSV. rewrite Hr0 in HSV. inversion HSV.
     }
     apply (word_of_arg_mono _ r) in HSV as HSV'; auto. rewrite HSV' in Hstep. cbn in Hstep.

     destruct (is_cap r1v) eqn:Hr1v.
     2: { (* Failure: r1 is not a capability *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_cap in Hr1v.
         destruct_word r1v; by simplify_pair_eq.
       }
       iFailWP "Hφ" Store_fail_const_imm.
     }
     destruct r1v as [ | [t p g b e a | ] | | ]; try inversion Hr1v. clear Hr1v.
     destruct t.
     2: {
       inversion Hstep; subst c σ2.
       iFailWP "Hφ" Store_fail_tag_imm.
     }

     destruct (a + imm)%a as [ea|] eqn:Hadd.
     2: { inversion Hstep; subst. iFailWP "Hφ" Store_fail_addr_imm. }
     cbn in Hstep.
     destruct (writeAllowed p && withinBounds b e ea) eqn:HWA.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
       inversion Hstep.
       apply andb_false_iff in HWA.
       iFailWP "Hφ" Store_fail_bounds_imm.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_store_implies_storev_imm r1 r2 mem regs p g b e a ea imm storev) as (oldv & Hmema); auto.

     (* Given this, prove that a is also present in the memory itself *)
     iDestruct (spec_mem_valid_inSepM mem m ea oldv with "Hm Hmem" ) as %Hma' ; auto.

     destruct (incrementPC regs ) as [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC r = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. }
       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       inversion Hstep.
       cbn; iFrame; iApply "Hφ"; iFrame.
       iPureIntro. eapply Store_spec_failure_store_imm;eauto. by constructor.
     }

     iMod ((spec_mem_update_inSepM _ _ ea) with "Hm Hmem") as "[Hm Hmem]"; eauto.

     (* Success *)
     rewrite /update_mem /= in Hstep.
     eapply (incrementPC_success_updatePC _ sr (<[ea:=store_word p storev]> m)) in Hregs'
         as (t1 & p1 & g1 & b1 & e1 & a1 & a'1 & a_pc1 & HPC'' & HuPC & ->).
     eapply (updatePC_success_incl _ (<[ea:=store_word p storev]> m)) in HuPC. 2: by eauto.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2; cbn in *.

     iFrame.
     iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply Store_spec_success_imm; eauto.
     * split; first exact Hr'1. repeat split; assumption.
     * rewrite /incrementPC /incrementPC_gen. rewrite a_pc1 HPC''.
       Unshelve. all: auto.
   Qed.

   Lemma step_store Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) w mem regs :
    ↑specN ⊆ Ep →
   decodeInstrW w = Store r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_store_map_or_true r1 r2 regs mem →
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     ([∗ map] a↦w ∈ mem, a ↣ₐ w) ∗
     ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
     ={Ep}=∗
     ∃ retv regs' mem',
       ⤇ Seq (of_val retv) ∗
       ⌜ Store_spec regs r1 r2 regs' mem mem' retv⌝ ∗
       ([∗ map] a↦w ∈ mem', a ↣ₐ w) ∗
       [∗ map] k↦y ∈ regs', k ↣ᵣ y.
   Proof.
     iIntros (HE Hinstr Hvpc HPC Dregs Hmem_pc HaStore) "(#Hctx & Hj & Hres)".
     have HaStore0 : allow_store_map_or_true_imm r1 r2 0 regs mem.
     { destruct HaStore as (t & p & g & b & e & a & storev & Hr & Hv & Hmem).
       exists t, p, g, b, e, a, storev. split; first done. split; first done.
       unfold reg_allows_store_imm. rewrite finz_add_0.
       unfold reg_allows_store in Hmem.
       case_decide; case_decide; naive_solver. }
     iMod (step_store_imm with "[$Hctx $Hj $Hres]") as (retv regs' mem') "(Hj & %Hspec & Hmem & Hregs)"; eauto.
     iModIntro. iExists retv, regs', mem'. iFrame. iPureIntro.
     destruct Hspec as [p g b e a ea storev oldv Hv Hr Hm Hm' Hpc | Hm Hfail].
     - destruct Hr as (Hr & Hadd & Hwa & Hwb).
       rewrite finz_add_0 in Hadd. simplify_eq.
       eapply Store_spec_success; eauto. split; first exact Hr. split; assumption.
     - eapply Store_spec_failure_store; eauto.
       destruct Hfail as [wv Hr Hcap | p g b e a Hr | p g b e a Hr Hadd | p g b e a ea Hr Hadd Hbounds | Hpc].
       + eapply Store_fail_const; eauto.
       + eapply Store_fail_tag; eauto.
       + rewrite finz_add_0 in Hadd. discriminate.
       + rewrite finz_add_0 in Hadd. simplify_eq. eapply Store_fail_bounds; eauto.
       + by apply Store_fail_invalid_PC.
   Qed.

  Lemma step_store_success_z_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w z :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ (WInt z).
  Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa) "(#Hctx & Hj & HPC & Hi)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply mem_eq_implies_allow_store_map; eauto. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       rewrite /store_word (writeAllowed_canStore_int _ _ Hwa).
       iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto.
       - apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
         destruct o as [Hwa' | Hbounds]; first congruence.
         apply Is_true_false in Hbounds. done.
       - congruence.
     }
   Qed.

   Lemma step_store_success_reg_PC_store_word E src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     src ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word pc_p wsrc ∗
    src ↣ᵣ wsrc.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa ?) "(#Hctx & Hj & HPC & Hi & Hsrc)".
     iDestruct (spec_map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as (Hrdst & Hwa' & Hbounds).
       simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto
       ; try congruence.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H1; try congruence ; try done.
     }
    Qed.

   Lemma step_store_success_reg_PC_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a).
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa) "(#Hctx & Hj & HPC & Hi)".
     iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       do 2 rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: iFrame. }
      { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [_ Hwb].
       destruct o; last apply Is_true_false in H; [congruence| done].
     }
    Qed.

   Lemma step_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ (WInt z) ∗
    dst ↣ᵣ WCap true p g b e pc_a.
    Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? _]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto.
       - destruct o; congruence.
       - congruence.
     }
     Qed.

   Lemma step_store_success_reg_same'_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p (WCap true p g b e pc_a) ∗
    dst ↣ᵣ WCap true p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? _]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
   Qed.

   Lemma step_store_success_reg_same_a_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p w'' ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H5 as [? _]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
   Qed.

   Lemma step_store_success_reg_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ store_word p w''.
    Proof.
      iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H6 as [? _]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_reg_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ store_word p (WCap true p g b e a).
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 _]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; last congruence.
       - destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_reg_PC E src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     canStore pc_p wsrc = true →
     src ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ wsrc ∗
    src ↣ᵣ wsrc.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa HcanStore Hsrc) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_PC_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_PC_same E pc_p pc_g pc_b pc_e pc_a pc_a' w w' :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     canStore pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ WCap true pc_p pc_g pc_b pc_e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa HcanStore) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_PC_same_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_same' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
       p g b e :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p (WCap true p g b e pc_a) = true →
     dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ WCap true p g b e pc_a ∗
    dst ↣ᵣ WCap true p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same'_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hdst)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_same_a E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
       p g b e w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e pc_a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w'' ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hsrc Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same_a_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc & Hdst)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
       p g b e a w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w''.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hsrc Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc & Hdst & Ha)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
       p g b e a :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p (WCap true p g b e a) = true →
     dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    a ↣ₐ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same_store_word with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hdst & Ha)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_fail_reg_not_cap E pc_p pc_g pc_b pc_e pc_a w
     dst src wdst wstore :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     src ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wstore ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hnot_cap ?) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store; simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H4.
       destruct H4 as (? & ? & ?); simplify_map_eq.
       destruct (decide (dst = cnull)); first done.
       simplify_map_eq.
     }
     by iModIntro; iFrame.
     Unshelve. all: done.
    Qed.

    Lemma step_store_fail_z_not_cap E pc_p pc_g pc_b pc_e pc_a w
     dst z wdst :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hnot_cap ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store; simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H2.
       simplify_map_eq.
       destruct H2 as (? & ? & ?); simplify_map_eq.
     }
     by iModIntro; iFrame.
     Unshelve. all: done.
    Qed.

   Lemma step_store_fail_reg_perm E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hwa ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store.
      rewrite Hwa.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H5.
       destruct H5 as (? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

    Lemma step_store_fail_z_perm E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc HcanStore ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        eauto.
      }
      rewrite /reg_allows_store.
      rewrite HcanStore.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H2.
       destruct H2 as (? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

   Lemma step_store_fail_reg E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     src ≠ cnull ->
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed).
    Proof.
      iIntros (HE Hinstr Hvpc Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store.
      rewrite Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H5.
       destruct H5 as (? & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro.
     }
    Qed.

    Lemma step_store_fail_z E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) 0 →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed).
    Proof.
      iIntros (HE Hinstr Hvpc Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /reg_allows_store.
      rewrite Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store in H2.
       destruct H2 as (? & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro.
     }
    Qed.

  Lemma step_store_fail_tag E pc_p pc_g pc_b pc_e pc_a
      w dst (src : Z + RegName) regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Store dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ dst = Some wa →
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
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag; subst; cbn.
    all: destruct (word_of_argument r src); done.
  Qed.

   Lemma step_store_success_reg_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a ea (imm : Z) w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ store_word p w''.
    Proof.
      iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H6 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_reg_same_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ store_word p (WCap true p g b e a).
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_z_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; last congruence.
       - destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_reg_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
       p g b e a ea (imm : Z) w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w''.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_store_word_imm with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc & Hdst & Ha)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Ha".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z
         p g b e a (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ (WInt z) ∗
    dst ↣ᵣ WCap true p g b e a.
    Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     have Hstore_word : store_word p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto.
       - destruct o; congruence.
       - congruence.
     }
     Qed.

   Lemma step_store_success_reg_same'_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e a (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p (WCap true p g b e a) ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
   Qed.

   Lemma step_store_success_reg_same_a_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e a (imm : Z) w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p w'' ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H5 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
   Qed.

   Lemma step_store_success_reg_same'_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
       p g b e a (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     canStore p (WCap true p g b e a) = true →
     dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ WCap true p g b e a ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same'_store_word_imm with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hdst)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_same_a_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
       p g b e a (imm : Z) w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     canStore p w'' = true →
     src ≠ cnull → dst ≠ cnull →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w'' ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore Hsrc Hdst) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same_a_store_word_imm with "[$Hctx $Hj $Hres]") as "(Hj & HPC & Hi & Hsrc & Hdst)"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hi".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_fail_reg_not_cap_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w
     dst src wdst wstore :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     src ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wstore ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hnot_cap ?) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H4.
       destruct H4 as (? & ? & ? & ?); simplify_map_eq.
       destruct (decide (dst = cnull)); first done.
       simplify_map_eq.
     }
     by iModIntro; iFrame.
     Unshelve. all: done.
    Qed.

    Lemma step_store_fail_z_not_cap_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w
     dst z wdst :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     is_cap wdst = false ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ wdst
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hnot_cap ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,_,_,_,_,_,_; eauto.
      simplify_map_eq.
      split; [|split]; eauto.
      - rewrite /read_reg_inr; simplify_map_eq.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; done.
      - rewrite /reg_allows_store_imm.
        destruct (_ + imm)%a; simpl; last done. simplify_map_eq.
        rewrite decide_False; auto.
        intros [].
        destruct (decide (dst = cnull)); first done.
        destruct wdst as [| [] | |]; cbn in Hnot_cap; simplify_eq.
    }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H2.
       simplify_map_eq.
       destruct H2 as (? & ? & ? & ?); simplify_map_eq.
     }
     by iModIntro; iFrame.
     Unshelve. all: done.
    Qed.

   Lemma step_store_fail_reg_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hwa ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store_imm.
      destruct (a + imm)%a eqn:Haddr; simpl; last done.
      rewrite Hwa.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H5.
       destruct H5 as (? & ? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

    Lemma step_store_fail_z_perm_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     writeAllowed p = false ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc HcanStore ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        eauto.
      }
      rewrite /reg_allows_store_imm.
      destruct (a + imm)%a eqn:Haddr; simpl; last done.
      rewrite HcanStore.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H2.
       destruct H2 as (? & ? & Hwa' & ?); simplify_map_eq.
       congruence.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

   Lemma step_store_fail_reg_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a ea w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hadd Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store_imm.
      rewrite Hadd Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H5.
       destruct H5 as (? & Haddr & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

    Lemma step_store_fail_z_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a ea z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = Some ea →
     withinBounds b e ea = false →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hadd Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /reg_allows_store_imm.
      rewrite Hadd Hwb.
      rewrite decide_False; auto.
      intro; naive_solver.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H2.
       destruct H2 as (? & Haddr & ? & Hbounds); simplify_map_eq.
       by rewrite Hbounds in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

  Lemma step_store_fail_tag_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a
      w dst (src : Z + RegName) regs wa :
    ↑specN ⊆ E →
    decodeInstrW w = Store dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ dst = Some wa →
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
    destruct wa as [| [t p g b e a|] | |]; cbn in Htag; subst; cbn.
    all: destruct (word_of_argument r src); done.
  Qed.

   Lemma step_store_success_reg_PC_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w src w'
         ea (imm : Z) w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →
     src ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    ea ↣ₐ store_word pc_p w''.
    Proof.
      iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hsrc & Hsrca)".
    iDestruct (spec_map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hold Hmem' Hinc | Hmem' Hfail].
     { (* Success *)
       iModIntro.
       destruct Hallow as [Hrr2 [Hadd2 _]]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_reg_PC_same_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w w'
         ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a).
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd) "(#Hctx & Hj & HPC & Hi & Hsrca)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hold Hmem' Hinc | Hmem' Hfail].
     { (* Success *)
       iModIntro.
       destruct Hallow as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_z_PC_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w z w'
         ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd) "(#Hctx & Hj & HPC & Hi & Hsrca)".
     have Hstore_word : store_word pc_p (WInt z) = WInt z.
     { apply store_word_canStore, writeAllowed_canStore_int, Hwa. }
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { eapply mem_neq_implies_allow_store_map_imm with (a := pc_a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [p0 g0 b0 e0 a0 ea0 storev oldv Harg Hallow Hold Hmem' Hinc | Hmem' Hfail].
     { (* Success *)
       iModIntro.
       destruct Hallow as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       try rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_1 with "[$Hmap]") as "HPC"; eauto.
       all: try rewrite Hstore_word; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; last congruence.
       - destruct o; congruence.
     }
    Qed.

Lemma step_store_fail_reg_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     src ≠ cnull ->
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hadd ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,w''.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument.
        by simplify_map_eq.
      }
      rewrite /reg_allows_store_imm.
      by rewrite Hadd.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H5.
       destruct H5 as (? & Haddr & ? & Hbounds); simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

Lemma step_store_fail_z_overflow_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
    ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a + imm)%a = None →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
    Proof.
      iIntros (HE Hinstr Hvpc Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true_imm.
      eexists true,p,g,b,e,a,_.
      split.
      { rewrite /read_reg_inr.
        by rewrite lookup_insert_ne // lookup_insert_eq.
      }
      split.
      { rewrite /word_of_argument. eauto.
      }
      rewrite /reg_allows_store_imm.
      by rewrite Hadd.
      }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success (contradiction) *)
       exfalso.
       rewrite /reg_allows_store_imm in H2.
       destruct H2 as (? & Haddr & ? & Hbounds); simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro; iFrame.
     }
    Qed.

   Lemma step_store_success_reg_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     canStore p (WCap true p g b e a) = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ? HcanStore) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_same_store_word_imm with "[$Hctx $Hj $Hres]") as "[Hj Hpost]"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_PC_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w src w'
         ea (imm : Z) w'' :
    ↑specN ⊆ E →
      decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →
     src ≠ cnull ->

     canStore pc_p (w'') = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ w'' ∗
    ea ↣ₐ w''.
    Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ? HcanStore) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_PC_store_word_imm with "[$Hctx $Hj $Hres]") as "[Hj Hpost]"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_PC_same_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w w'
         ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true → withinBounds pc_b pc_e ea = true →
     (pc_a + imm)%a = Some ea →

     canStore pc_p (WCap true pc_p pc_g pc_b pc_e pc_a) = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    ea ↣ₐ WCap true pc_p pc_g pc_b pc_e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd HcanStore) "(#Hctx & Hj & Hres)".
     iMod (step_store_success_reg_PC_same_store_word_imm with "[$Hctx $Hj $Hres]") as "[Hj Hpost]"; eauto.
     iEval (rewrite (store_word_canStore _ _ HcanStore)) in "Hpost".
     iModIntro. iFrame.
   Qed.

   Lemma step_store_success_reg_fromPC_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a ea (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e ea = true →
     (a + imm)%a = Some ea →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ w'
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a ∗
    ea ↣ₐ store_word p (WCap true pc_p pc_g pc_b pc_e pc_a).
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map_imm with (a := a) (ea := ea); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H3 as [Hrr2 [Hadd2 _]]. simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
    Qed.

   Lemma step_store_success_reg_fromPC_same_a_store_word_imm E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e a (imm : Z) :
    ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     (a + imm)%a = Some pc_a →
     dst ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap true p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word p (WCap true pc_p pc_g pc_b pc_e pc_a) ∗
    dst ↣ᵣ WCap true p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb Hadd ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
     iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store_imm _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map_imm; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & #Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H2 as [? [Hadd2 _]]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto.
       all: iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence; try (destruct o; congruence).

     }
   Qed.

Lemma step_store_success_z_PC_same_a_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_a' w z :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inl z) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     (pc_a + imm)%a = Some pc_a →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ (WInt z).
  Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hadd) "(#Hctx & Hj & Hres)".
     have Himm : imm = 0 by solve_finz. subst imm.
     iApply (step_store_success_z_PC with "[$Hctx $Hj $Hres]"); eauto.
   Qed.

Lemma step_store_success_reg_PC_same_a_store_word_imm E (imm : Z) src wsrc pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr src) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →
     src ≠ cnull ->

     (pc_a + imm)%a = Some pc_a →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ wsrc
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word pc_p wsrc ∗
    src ↣ᵣ wsrc.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa ? Hadd) "(#Hctx & Hj & Hres)".
     have Himm : imm = 0 by solve_finz. subst imm.
     iApply (step_store_success_reg_PC_store_word with "[$Hctx $Hj $Hres]"); eauto.
   Qed.

Lemma step_store_success_reg_PC_same_same_a_store_word_imm E (imm : Z) pc_p pc_g pc_b pc_e pc_a pc_a' w :
    ↑specN ⊆ E →
     decodeInstrW w = Store PC (inr PC) imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed pc_p = true →

     (pc_a + imm)%a = Some pc_a →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ store_word pc_p (WCap true pc_p pc_g pc_b pc_e pc_a).
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hadd) "(#Hctx & Hj & Hres)".
     have Himm : imm = 0 by solve_finz. subst imm.
     iApply (step_store_success_reg_PC_same_store_word E pc_p pc_g pc_b pc_e pc_a pc_a' w (WInt 0) with "[$Hctx $Hj $Hres]"); eauto.
   Qed.


End spec_rules.
