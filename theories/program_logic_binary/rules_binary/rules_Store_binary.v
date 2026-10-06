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

   Lemma step_store Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 (r2 : Z + RegName) w mem regs :
     ↑specN ⊆ Ep →
   decodeInstrW w = Store r1 r2 →
   isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Store r1 r2) ⊆ dom regs →
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
       iFailWP "Hφ" Store_fail_const.
     }
     destruct r1v as [ | [p g b e a | ] | | ]; try inversion Hr1v. clear Hr1v.

     destruct (writeAllowed p && withinBounds b e a) eqn:HWA.
     2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
       inversion Hstep.
       apply andb_false_iff in HWA.
       iFailWP "Hφ" Store_fail_bounds.
     }
     apply andb_true_iff in HWA; destruct HWA as (Hwa & Hwb).

     case_eq (canStore p storev); intro HcanStore.
     2:{ destruct r2.
         - simpl in HSV; inv HSV.
           rewrite writeAllowed_canStore_int in HcanStore; auto; congruence.
         - assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
           { simpl in HSV; inv HSV. rewrite HcanStore /= in Hstep.
             destruct (r !!ᵣ r0); try congruence; inv Hstep; auto.
           }
           iFailWP "Hφ" Store_fail_invalid_locality.
     }
     rewrite HcanStore /= in Hstep.

     (* Prove that a is in the memory map now, otherwise we cannot continue *)
     pose proof (allow_store_implies_storev r1 r2 mem regs p g b e a storev) as (oldv & Hmema); auto.

     (* Given this, prove that a is also present in the memory itself *)
     iDestruct (spec_mem_valid_inSepM mem m a oldv with "Hm Hmem" ) as %Hma' ; auto.

     destruct (incrementPC regs ) as [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC r = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'; eauto. }
       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       inversion Hstep.
       cbn; iFrame; iApply "Hφ"; iFrame.
       iPureIntro. eapply Store_spec_failure_store;eauto. by constructor.
     }

     iMod ((spec_mem_update_inSepM _ _ a) with "Hm Hmem") as "[Hm Hmem]"; eauto.

     (* Success *)
     rewrite /update_mem /= in Hstep.
     eapply (incrementPC_success_updatePC _ sr (<[a:=storev]> m)) in Hregs'
         as (p1 & g1 & b1 & e1 & a1 & a'1 & a_pc1 & HPC'' & HuPC & ->).
     eapply (updatePC_success_incl _ (<[a:=storev]> m)) in HuPC. 2: by eauto.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2; cbn in *.

     iFrame.
     iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply Store_spec_success; eauto.
     * split; auto; [exact Hr'1|]; auto.
     * rewrite /incrementPC /incrementPC_gen. rewrite a_pc1 HPC''.
       Unshelve. all: auto.
   Qed.

   Lemma step_store_success_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e :
     ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     dst ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     dst ↣ᵣ WCap p g b e pc_a
     ={E}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ (WInt z) ∗
     dst ↣ᵣ WCap p g b e pc_a.
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
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto.
       - destruct o; congruence.
       - rewrite writeAllowed_canStore_int in e3; auto; congruence.
       - congruence.
     }
     Qed.

   Lemma step_store_success_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst z w'
         p g b e a :
     ↑specN ⊆ E →
     decodeInstrW w = Store dst (inl z) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     dst ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     dst ↣ᵣ WCap p g b e a ∗
     a ↣ₐ w'
     ={E}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w ∗
     dst ↣ᵣ WCap p g b e a ∗
     a ↣ₐ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
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
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; last congruence.
       - destruct o; congruence.
       - rewrite writeAllowed_canStore_int in e3; auto; congruence.
     }
    Qed.

   Lemma step_store_success_reg_same' E pc_p pc_g pc_b pc_e pc_a pc_a' w dst
         p g b e :
     ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p (WCap p g b e pc_a) = true ->
     dst ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     dst ↣ᵣ WCap p g b e pc_a
     ={E}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ WCap p g b e pc_a ∗
     dst ↣ᵣ WCap p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
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
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hsrc]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
   Qed.

   Lemma step_store_success_reg_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst w'
         p g b e a :
     ↑specN ⊆ E →
     decodeInstrW w = Store dst (inr dst) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p (WCap p g b e a) = true ->
     dst ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     dst ↣ᵣ WCap p g b e a ∗
     a ↣ₐ w'
     ={E}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w ∗
     dst ↣ᵣ WCap p g b e a ∗
     a ↣ₐ WCap p g b e a.
   Proof.
    iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore ?) "(#Hctx & Hj & HPC & Hi & Hdst & Hsrca)".
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
       iDestruct (spec_regs_of_map_2 with "[$Hmap]") as "[HPC Hdst]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
    Qed.

   Lemma step_store_success_reg_same_a E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src
         p g b e w'' :
     ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e pc_a = true →
     canStore p w'' = true ->
     src ≠ cnull ->
     dst ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     src ↣ᵣ w'' ∗
     dst ↣ᵣ WCap p g b e pc_a
     ={E}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w'' ∗
     src ↣ᵣ w'' ∗
     dst ↣ᵣ WCap p g b e pc_a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
     iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem".

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_store_map; eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H5 as [? _]; simplify_map_eq.
       rewrite spec_memMap_resource_1.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
   Qed.

   Lemma step_store_success_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst src w'
         p g b e a w'' :
     ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     writeAllowed p = true → withinBounds b e a = true →
     canStore p w'' = true ->
     src ≠ cnull ->
     dst ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     src ↣ᵣ w'' ∗
     dst ↣ᵣ WCap p g b e a ∗
     a ↣ₐ w'
     ={E}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w ∗
     src ↣ᵣ w'' ∗
     dst ↣ᵣ WCap p g b e a ∗
     a ↣ₐ w''.
    Proof.
      iIntros (HE Hinstr Hvpc Hpca' Hwa Hwb HcanStore ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst & Hsrca)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_2ne_apply with "Hi Hsrca") as "[Hmem %]"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_store_map with (a := a); eauto.
      all: by simplify_map_eq. }
    iDestruct "H" as (retv regs' mem') "(Hj & %Hspec & Hmem & Hmap)".

    destruct Hspec.
     { (* Success *)
       iModIntro.
       destruct H6 as [? _]; simplify_map_eq.
       rewrite insert_insert_ne // insert_insert_eq.
       iDestruct (spec_memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq.
       iDestruct (spec_regs_of_map_3 with "[$Hmap]") as "[HPC [Hsrc Hdst] ]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       destruct o; congruence.
     }
    Qed.

    Lemma step_store_fail_z E pc_p pc_g pc_b pc_e pc_a w dst
         p g b e a z :
      ↑specN ⊆ E →
      decodeInstrW w = Store dst (inl z) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     dst ≠ cnull ->
      spec_ctx ∗
      ⤇ Seq (Instr Executable) ∗
      PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
      pc_a ↣ₐ w ∗
      dst ↣ᵣ WCap p g b e a
      ={E}=∗
      ⤇ Seq (Instr Failed).
    Proof.
      iIntros (HE Hinstr Hvpc Hwb ?) "(#Hctx & Hj & HPC & Hi & Hdst)".
    iDestruct (spec_map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists p,g,b,e,a,_.
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
       destruct H2 as (?&?&Hcontra&?); simplify_map_eq.
       by rewrite Hcontra in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro.
     }
    Qed.

   Lemma step_store_fail_reg E pc_p pc_g pc_b pc_e pc_a w dst src
         p g b e a w'' :
     ↑specN ⊆ E →
      decodeInstrW w = Store dst (inr src) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     withinBounds b e a = false →
     src ≠ cnull ->
     dst ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     src ↣ᵣ w'' ∗
     dst ↣ᵣ WCap p g b e a
     ={E}=∗
     ⤇ Seq (Instr Failed).
    Proof.
      iIntros (HE Hinstr Hvpc Hwb ??) "(#Hctx & Hj & HPC & Hi & Hsrc & Hdst)".
    iDestruct (spec_map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iDestruct (spec_memMap_resource_1 with "Hi") as "Hmem"; auto.

    iMod (step_store _ pc_p pc_g with "[$Hctx $Hj $Hmap $Hmem]") as "H"; eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { rewrite /allow_store_map_or_true.
      eexists p,g,b,e,a,w''.
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
       destruct H5 as (?&?&Hcontra&?); simplify_map_eq.
       by rewrite Hcontra in Hwb.
     }
     { (* Failure (contradiction) *)
       destruct X; try incrementPC_inv; simplify_map_eq; eauto; by iModIntro.
     }
    Qed.

End spec_rules.
