From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Restrict.

(** * Spec rules for [Restrict] (spec copies of [rules_Restrict.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types c : griotte_lang.expr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma Restrict_spec_determ regs dst src regs1 regs2 v1 v2 :
    Restrict_spec regs dst src regs1 v1 →
    Restrict_spec regs dst src regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ Restrict_failure. Qed.

  Lemma step_Restrict Ep pc_p pc_g pc_b pc_e pc_a w dst src regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = Restrict dst src ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Restrict dst src) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Restrict_spec regs dst src regs' retv ⌝ ∗
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
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.

    rewrite /exec /= Hdst /= in Hstep.

    destruct (z_of_argument regs src) as [wsrc|] eqn:Hwsrc;
      pose proof Hwsrc as H'wsrc; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Hwsrc, Hstep. destruct src as [| r0]; [ congruence |].
       odestruct (Hri r0) as [r0v [Hr'0 Hr0]].
       { unfold regs_of_argument. set_solver+. }
       rewrite Hr0 Hr'0 in Hwsrc Hstep.
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       { destruct_word r0v; cbn in Hstep; try congruence; by simplify_pair_eq. }
       iFailWP "Hφ" Restrict_fail_src_nonz. }
    apply (z_of_arg_mono _ r) in Hwsrc; auto. rewrite Hwsrc in Hstep; simpl in Hstep.

    destruct (is_mutable_range wdst) eqn:Hwdst.
     2: { (* Failure: wdst is not of the right type *)
       unfold is_mutable_range in Hwdst.
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       { destruct wdst as [ | [p b e a | ] | | ]; try by inversion Hwdst.
         all: try by simplify_pair_eq.
       }
       iFailWP "Hφ" Restrict_fail_allowed. }

    (* Now the proof splits depending on the type of value in wdst *)
    destruct wdst as [ | [p g b e a | p g b e a] | | ].
    1,4,5: inversion Hwdst.
    - destruct (decodePermPair wsrc) as [p' g'] eqn:HdecPair.
      (* First, the case where r1v is a capability *)
      destruct (PermFlowsTo p' p) eqn:HPflows; cycle 1.
      { destruct p; try congruence; inv Hstep
        ; iFailWP "Hφ" Restrict_fail_invalid_perm_cap. }

      destruct (LocalityFlowsTo g' g) eqn:HLflows; cycle 1.
      { destruct p; try congruence; inv Hstep
        ; iFailWP "Hφ" Restrict_fail_invalid_loc_cap. }
      rewrite /update_reg /= in Hstep.

      destruct (incrementPC (<[ dst := WCap p' g' b e a ]ᵣ> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      {
        assert (incrementPC (<[ dst := WCap p' g' b e a ]ᵣ> r) = None) as HH.
        { eapply incrementPC_overflow_mono; first eapply Hregs'.
          + by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto.
        }
        apply (incrementPC_fail_updatePC _ sr m) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->)
                                                   by (destruct p; inversion Hstep; auto).
        iFailWP "Hφ" Restrict_fail_PC_overflow_cap.
      }

      eapply (incrementPC_success_updatePC _ sr m) in Hregs'
          as (p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { destruct_perm p; cbn in *; eauto. }
      simplify_pair_eq.

      iFrame.
      iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      { apply is_Some_lookup_reg; done. }
      iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    (* Now, the case where wsrc is a sealrange *)
    - destruct (decodeSealPermPair wsrc) as [p' g'] eqn:HdecPair.

      destruct (SealPermFlowsTo p' p) eqn:HPflows; cycle 1.
      { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Restrict_fail_invalid_perm_sr. }
      rewrite /update_reg /= in Hstep.

      destruct (LocalityFlowsTo g' g) eqn:HLflows; cycle 1.
      { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Restrict_fail_invalid_loc_sr. }
      rewrite /update_reg /= in Hstep.

      destruct (incrementPC (<[ dst := WSealRange p' g' b e a ]ᵣ> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      {
        assert (incrementPC (<[ dst := WSealRange p' g' b e a ]ᵣ> r) = None) as HH.
        { eapply incrementPC_overflow_mono; first eapply Hregs'.
          + by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto.
        }
        apply (incrementPC_fail_updatePC _ sr m) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->)
                                                   by (destruct p; inversion Hstep; auto).
        iFailWP "Hφ" Restrict_fail_PC_overflow_sr. }

      eapply (incrementPC_success_updatePC _ sr m) in Hregs'
          as (p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { destruct p; cbn in Hstep; eauto. }
      simplify_pair_eq.

      iFrame.
      iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      { apply is_Some_lookup_reg; done. }
      iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 2; eauto.
  Qed.

  Lemma step_restrict_success_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w rv z p' g':
    ↑specN ⊆ Ep →
    decodeInstrW w = Restrict PC (inr rv) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (p',g') = (decodePermPair z) ->
    PermFlowsTo p' pc_p = true →
    LocalityFlowsTo g' pc_g = true →
    rv ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap p' g' pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrv)".
     iDestruct (spec_map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [| | * Hfail].
     { (* Success *)
       iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
       simplify_pair_eq; rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.
     }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma step_restrict_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv p g b e a z p' g' :
     ↑specN ⊆ Ep →
     decodeInstrW w = Restrict r1 (inr rv) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     rv ≠ cnull ->
     r1 ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     r1 ↣ᵣ WCap p g b e a ∗
     rv ↣ᵣ WInt z
     ={Ep}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w ∗
     rv ↣ᵣ WInt z ∗
     r1 ↣ᵣ WCap p' g' b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hrv)".
     iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
              (insert_insert_ne _ PC r1) // insert_insert_eq.
      simplify_pair_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
      simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma step_restrict_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w z p' g' :
     ↑specN ⊆ Ep →
     decodeInstrW w = Restrict PC (inl z) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' pc_p = true →
     LocalityFlowsTo g' pc_g = true →
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w
     ={Ep}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap p' g' pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows) "(#Hctx & Hj & HPC & Hpc_a)".
     iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | * Hfail ].
     { (* Success *)
       iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
       simplify_pair_eq.
       rewrite !insert_insert_eq.
       iApply (spec_regs_of_map_1 with "Hmap"). }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma step_restrict_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 p g b e a z p' g' :
     ↑specN ⊆ Ep →
     decodeInstrW w = Restrict r1 (inl z) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     r1 ≠ cnull ->
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
     pc_a ↣ₐ w ∗
     r1 ↣ᵣ WCap p g b e a
     ={Ep}=∗
     ⤇ Seq (Instr NextI) ∗
     PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
     pc_a ↣ₐ w ∗
     r1 ↣ᵣ WCap p' g' b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
     iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [| | * Hfail].
     { (* Success *)
       iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
               (insert_insert_ne _ PC r1) // insert_insert_eq. simplify_pair_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
      simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv; simplify_map_eq; eauto; congruence. }
   Qed.

End spec_rules.
