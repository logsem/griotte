From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Subseg.

(** * Spec rules for [Subseg] (spec copies of [rules_Subseg.v]) *)

Section spec_rules.
  Context `{MP: MachineParameters} `{!invGS Σ} `{specg : specG Σ}.
  Implicit Types σ : ExecConf.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma Subseg_spec_determ regs dst src1 src2 regs1 regs2 v1 v2 :
    Subseg_spec regs dst src1 src2 regs1 v1 →
    Subseg_spec regs dst src1 src2 regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ Subseg_failure. Qed.

  Lemma step_Subseg Ep pc_p pc_g pc_b pc_e pc_a w dst src1 src2 regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = Subseg dst src1 src2 ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗
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

    destruct (is_mutable_range wdst) eqn:Hwdst.
     2: { (* Failure: wdst is not of the right type *)
       unfold is_mutable_range in Hwdst.
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       { destruct wdst as [ | [p b e a | ] | | ]; try by inversion Hwdst.
         all: try by simplify_pair_eq.
         all: repeat destruct (addr_of_argument r _); cbn in *; simplify_pair_eq; auto. }
       iFailWP "Hφ" Subseg_fail_allowed. }

    (* Now the proof splits depending on the type of value in wdst *)
    destruct wdst as [ | [p g b e a | p g b e a] | | ].
    1,4,5: inversion Hwdst.

    (* First, the case where r1v is a capability *)
    + destruct (addr_of_argument regs src1) as [a1|] eqn:Ha1;
        pose proof Ha1 as H'a1; cycle 1.
      { destruct src1 as [| r1] eqn:?; cbn in Ha1, Hstep.
        { rewrite Ha1 /= in Hstep.
          assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
          { repeat case_match; inv Hstep; auto. }
          iFailWP "Hφ" Subseg_fail_src1_nonaddr. }
        subst src1.
        destruct (Hri r1) as [r1v [Hr'1 Hr1]] ; first (by unfold regs_of_argument; set_solver+).
        rewrite /addr_of_argument /= Hr'1 in Ha1.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
        { destruct r1v ; simplify_pair_eq.
          all: unfold addr_of_argument, z_of_argument at 2 in Hstep.
          all: rewrite /= Hr1 ?Ha1 /= in Hstep.
          all: inv Hstep; auto.
        }
        repeat case_match; try congruence.
        all: iFailWP "Hφ" Subseg_fail_src1_nonaddr. }
      apply (addr_of_arg_mono _ r) in Ha1; auto. rewrite Ha1 /= in Hstep.

      destruct (addr_of_argument regs src2) as [a2|] eqn:Ha2;
        pose proof Ha2 as H'a2; cycle 1.
      { destruct src2 as [| r2] eqn:?; cbn in Ha2, Hstep.
        { rewrite Ha2 /= in Hstep.
          assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
          { repeat case_match; inv Hstep; auto. }
          iFailWP "Hφ" Subseg_fail_src2_nonaddr.
        }
        subst src2.
        destruct (Hri r2) as [r2v [Hr'2 Hr2]]; first (by unfold regs_of_argument; set_solver+).
        rewrite /addr_of_argument /= Hr'2 in Ha2.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
        { destruct r2v ; simplify_pair_eq.
          all: unfold addr_of_argument, z_of_argument  in Hstep.
          all: rewrite /= Hr2 ?Ha2 /= in Hstep.
          all: inv Hstep; auto.
        }
        repeat case_match; try congruence.
        all: iFailWP "Hφ" Subseg_fail_src2_nonaddr. }
      apply (addr_of_arg_mono _ r) in Ha2; auto. rewrite Ha2 /= in Hstep.
      rewrite /update_reg /= in Hstep.

      destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1.
      { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Subseg_fail_not_iswithin_cap. }

      destruct (incrementPC (<[ dst := (WCap p g a1 a2 a) ]ᵣ> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      { assert (incrementPC (<[ dst := (WCap p g a1 a2 a) ]ᵣ> r) = None) as HH.
        { eapply incrementPC_overflow_mono; first eapply Hregs'.
            + by rewrite lookup_insert_is_Some'; eauto.
            + by apply insert_mono; eauto.
        }
        apply (incrementPC_fail_updatePC _ sr m) in HH.
        rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->)
            by (destruct p; inversion Hstep; auto).
        iFailWP "Hφ" Subseg_fail_incrPC_cap. }

      eapply (incrementPC_success_updatePC _ sr m) in Hregs'
          as (p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { destruct_perm p; cbn in Hstep; eauto. }
      simplify_pair_eq. iFrame.
      iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      { apply is_Some_lookup_reg; done. }
      iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    (* Now, the case where wsrc is a capability *)
    + destruct (otype_of_argument regs src1) as [a1|] eqn:Ha1;
        pose proof Ha1 as H'a1; cycle 1.
      { destruct src1 as [| r1] eqn:?; cbn in Ha1, Hstep.
        { rewrite Ha1 /= in Hstep.
          assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
          { repeat case_match; inv Hstep; auto. }
          iFailWP "Hφ" Subseg_fail_src1_nonotype.
        }
        subst src1.
        destruct (Hri r1) as [r1v [Hr'1 Hr1]]; first (by unfold regs_of_argument; set_solver+).
        rewrite /otype_of_argument /= Hr'1 in Ha1.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
        { destruct r1v ; simplify_pair_eq.
          all: unfold otype_of_argument, z_of_argument at 2 in Hstep.
          all: rewrite /= Hr1 ?Ha1 /= in Hstep.
          all: inv Hstep; auto.
        }
        repeat case_match; try congruence.
        all: iFailWP "Hφ" Subseg_fail_src1_nonotype. }
      apply (otype_of_arg_mono _ r) in Ha1; auto. rewrite Ha1 /= in Hstep.

      destruct (otype_of_argument regs src2) as [a2|] eqn:Ha2;
        pose proof Ha2 as H'a2; cycle 1.
      { destruct src2 as [| r2] eqn:?; cbn in Ha2, Hstep.
        { rewrite Ha2 /= in Hstep.
          assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
          { repeat case_match; inv Hstep; auto. }
          iFailWP "Hφ" Subseg_fail_src2_nonotype.
        }
        subst src2.
        destruct (Hri r2) as [r2v [Hr'2 Hr2]]; first (by unfold regs_of_argument; set_solver+).
          rewrite /otype_of_argument /= Hr'2 in Ha2.
          assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
          { destruct r2v ; simplify_pair_eq.
            all: unfold otype_of_argument, z_of_argument  in Hstep.
            all: rewrite /= Hr2 ?Ha2 /= in Hstep.
            all: inv Hstep; auto.
          }
          repeat case_match; try congruence.
          all: iFailWP "Hφ" Subseg_fail_src2_nonotype. }
      apply (otype_of_arg_mono _ r) in Ha2; auto. rewrite Ha2 /= in Hstep.
      rewrite /update_reg /= in Hstep.

      destruct (isWithin a1 a2 b e) eqn:Hiw; cycle 1.
      { destruct p; try congruence; inv Hstep ; iFailWP "Hφ" Subseg_fail_not_iswithin_sr. }

      destruct (incrementPC (<[ dst := (WSealRange p g a1 a2 a) ]ᵣ> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      { assert (incrementPC (<[ dst := (WSealRange p g a1 a2 a) ]ᵣ> r) = None) as HH.
        { eapply incrementPC_overflow_mono; first eapply Hregs'.
          + by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto.
        }
        apply (incrementPC_fail_updatePC _ sr m) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->)
            by (destruct p; inversion Hstep; auto).
        iFailWP "Hφ" Subseg_fail_incrPC_sr. }

      eapply (incrementPC_success_updatePC _ sr m) in Hregs'
        as (p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { destruct p; cbn in Hstep; eauto. }
      simplify_pair_eq. iFrame.
      iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      { apply is_Some_lookup_reg; done. }
      iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro. econstructor 2; eauto.
  Qed.

  Lemma step_subseg_success E pc_p pc_g pc_b pc_e pc_a w dst r1 r2 p g b e a n1 n2 a1 a2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap p g b e a ∗
    r1 ↣ᵣ WInt n1 ∗
    r2 ↣ᵣ WInt n2
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt n1 ∗
    r2 ↣ᵣ WInt n2 ∗
    dst ↣ᵣ WCap p g a1 a2 a.
  Proof.
    iIntros (HE Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' Hcnull Hcnull' Hcnull'') "(#Hctx & Hj & HPC & Hpc_a & Hdst & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iMod (step_Subseg with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| | * Hfail].
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
        simplify_map_eq. }
    { (* Failure (contradiction) *)
      exfalso; eapply (Subseg_failure_cap_contra _ _ _ _ _ _ _ _ _ _ a1 a2 Hfail);
        rewrite /incrementPC /incrementPC_gen /insert_reg /lookup_reg /addr_of_argument /z_of_argument;
        simplify_map_eq; eauto. }
    Unshelve. all: auto.
  Qed.

  Lemma step_subseg_success_sr E pc_p pc_g pc_b pc_e pc_a w dst r1 r2 p g b e a n1 n2 a1 a2 pc_a' :
    ↑specN ⊆ E →
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealRange p g b e a ∗
    r1 ↣ᵣ WInt n1 ∗
    r2 ↣ᵣ WInt n2
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt n1 ∗
    r2 ↣ᵣ WInt n2 ∗
    dst ↣ᵣ WSealRange p g a1 a2 a.
  Proof.
    iIntros (HE Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ???) "(#Hctx & Hj & HPC & Hpc_a & Hdst & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iMod (step_Subseg with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| | * Hfail].
    { (* Success with WCap (contradiction) *)
       simplify_map_eq. }
    { (* Success *)
      iModIntro. iFrame. incrementPC_inv; simplify_map_eq.
      unfold otype_of_argument, z_of_argument in *. simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (spec_regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      exfalso; eapply (Subseg_failure_sr_contra _ _ _ _ _ _ _ _ _ _ a1 a2 Hfail);
        rewrite /incrementPC /incrementPC_gen /insert_reg /lookup_reg /otype_of_argument /z_of_argument;
        simplify_map_eq; eauto. }
    Unshelve. all: auto.
  Qed.

End spec_rules.
