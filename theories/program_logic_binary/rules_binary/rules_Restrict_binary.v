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

  (** Physical spec-side outcomes, for the spec run. *)

  Inductive spec_Restrict_failure (regs: Reg) (dst: RegName) (src: Z + RegName) :=
  | spec_Restrict_fail_src_nonz:
      z_of_argument regs src = None →
      spec_Restrict_failure regs dst src
  | spec_Restrict_fail_allowed w:
      regs !!ᵣ dst = Some w →
      is_mutable_range w = false →
      spec_Restrict_failure regs dst src
  | spec_Restrict_fail_invalidated_PC_cap (t : bool) p g b e a n p' g':
      regs !!ᵣ dst = Some (WCap t p g b e a) →
      z_of_argument regs src = Some n →
      (p',g') = (decodePermPair n) ->
      (PermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      spec_incrementPC (<[ dst := WCap false p' g' b e a ]ᵣ> regs) = None →
      spec_Restrict_failure regs dst src
  | spec_Restrict_fail_PC_overflow_cap (t : bool) p g b e a n p' g':
      regs !!ᵣ dst = Some (WCap t p g b e a) →
      z_of_argument regs src = Some n →
      (p',g') = (decodePermPair n) ->
      PermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      spec_incrementPC (<[ dst := WCap t p' g' b e a ]ᵣ> regs) = None →
      spec_Restrict_failure regs dst src
  | spec_Restrict_fail_invalidated_PC_sr (t : bool) p g b e a n p' g':
      regs !!ᵣ dst = Some (WSealRange t p g b e a) →
      z_of_argument regs src = Some n →
      (p',g') = (decodeSealPermPair n) ->
      (SealPermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      spec_incrementPC (<[ dst := WSealRange false p' g' b e a ]ᵣ> regs) = None →
      spec_Restrict_failure regs dst src
  | spec_Restrict_fail_PC_overflow_sr (t : bool) p g b e a n p' g':
      regs !!ᵣ dst = Some (WSealRange t p g b e a) →
      z_of_argument regs src = Some n →
      (p',g') = (decodeSealPermPair n) ->
      SealPermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      spec_incrementPC (<[ dst := WSealRange t p' g' b e a ]ᵣ> regs) = None →
      spec_Restrict_failure regs dst src.

  Inductive spec_Restrict_spec (regs: Reg) (dst: RegName) (src: Z + RegName) (regs': Reg): griotte_lang.val -> Prop :=
  | spec_Restrict_spec_success_cap (t : bool) p g b e a n p' g':
      regs !!ᵣ dst = Some (WCap t p g b e a) →
      z_of_argument regs src = Some n →
      (p',g') = (decodePermPair n) ->
      PermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      spec_incrementPC (<[ dst := WCap t p' g' b e a ]ᵣ> regs) = Some regs' →
      spec_Restrict_spec regs dst src regs' NextIV
  | spec_Restrict_spec_success_sr (t : bool) p g b e a n p' g':
      regs !!ᵣ dst = Some (WSealRange t p g b e a) →
      z_of_argument regs src = Some n →
      (p',g') = (decodeSealPermPair n) ->
      SealPermFlowsTo p' p = true →
      LocalityFlowsTo g' g = true →
      spec_incrementPC (<[ dst := WSealRange t p' g' b e a ]ᵣ> regs) = Some regs' →
      spec_Restrict_spec regs dst src regs' NextIV
  | spec_Restrict_spec_invalidated_cap (t : bool) p g b e a n p' g':
      regs !!ᵣ dst = Some (WCap t p g b e a) →
      z_of_argument regs src = Some n →
      (p',g') = (decodePermPair n) ->
      (PermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      spec_incrementPC (<[ dst := WCap false p' g' b e a ]ᵣ> regs) = Some regs' →
      spec_Restrict_spec regs dst src regs' NextIV
  | spec_Restrict_spec_invalidated_sr (t : bool) p g b e a n p' g':
      regs !!ᵣ dst = Some (WSealRange t p g b e a) →
      z_of_argument regs src = Some n →
      (p',g') = (decodeSealPermPair n) ->
      (SealPermFlowsTo p' p && LocalityFlowsTo g' g) = false →
      spec_incrementPC (<[ dst := WSealRange false p' g' b e a ]ᵣ> regs) = Some regs' →
      spec_Restrict_spec regs dst src regs' NextIV
  | spec_Restrict_spec_failure:
      spec_Restrict_failure regs dst src →
      spec_Restrict_spec regs dst src regs' FailedV.

  Lemma Restrict_spec_determ regs dst src regs1 regs2 v1 v2 :
    spec_Restrict_spec regs dst src regs1 v1 →
    spec_Restrict_spec regs dst src regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ spec_Restrict_failure. Qed.

  Lemma Restrict_spec_lift regs dst src lregs' v :
    Restrict_spec (lift_regs regs) dst src lregs' v →
    ∃ regs', (v = NextIV → lregs' = lift_regs regs') ∧ spec_Restrict_spec regs dst src regs' v.
  Proof. spec_lift Restrict_failure regs. Qed.

  Lemma step_Restrict Ep pc_p pc_g pc_b pc_e pc_a w dst src regs :
    ↑specN ⊆ Ep →
    decodeInstrW w = Restrict dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Restrict dst src) ⊆ dom regs →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗
    ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={Ep}=∗
    ∃ retv regs',
      ⤇ Seq (of_val retv) ∗
      ⌜ spec_Restrict_spec regs dst src regs' retv ⌝ ∗
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
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       { destruct_word r0v; cbn in Hstep; try congruence; by simplify_pair_eq. }
       iFailWP "Hφ" spec_Restrict_fail_src_nonz. }
    apply (z_of_arg_mono _ r) in Hwsrc; auto. rewrite Hwsrc in Hstep; simpl in Hstep.

    destruct (is_mutable_range wdst) eqn:Hwdst.
     2: { (* Failure: wdst is not of the right type *)
       unfold is_mutable_range in Hwdst.
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       { destruct wdst as [ | [t p b e a | ] | | ]; try by inversion Hwdst.
         all: try by simplify_pair_eq.
       }
       iFailWP "Hφ" spec_Restrict_fail_allowed. }

    (* Now the proof splits depending on the type of value in wdst *)
    destruct wdst as [ | [t p g b e a | t p g b e a] | | ].
    1,4,5: inversion Hwdst.
    - destruct (decodePermPair wsrc) as [p' g'] eqn:HdecPair.
      (* First, the case where r1v is a capability *)
      destruct (PermFlowsTo p' p && LocalityFlowsTo g' g) eqn:Hflows; cycle 1.
      { assert (Htag : t && PermFlowsTo p' p && LocalityFlowsTo g' g = false).
        { destruct t; simpl; auto. }
        rewrite Htag /update_reg /= in Hstep.
      destruct (spec_incrementPC (<[ dst := WCap false p' g' b e a ]ᵣ> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      {
        assert (spec_incrementPC (<[ dst := WCap false p' g' b e a ]ᵣ> r) = None) as HH.
        { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
          + by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto.
        }
        apply (spec_incrementPC_fail_updatePC _ sr m st) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
                                                   by (destruct p; inversion Hstep; auto).
        iFailWP "Hφ" spec_Restrict_fail_invalidated_PC_cap.
      }

      eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
          as (t'' & p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) (shadow':=st) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { destruct_perm p; cbn in *; eauto. }
      simplify_pair_eq.

      iFrame.
      iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      { apply is_Some_lookup_reg; done. }
      iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro. eapply spec_Restrict_spec_invalidated_cap; eauto.
      }
      apply andb_true_iff in Hflows as [HPflows HLflows].
      rewrite HPflows HLflows !andb_true_r /update_reg /= in Hstep.

      destruct (spec_incrementPC (<[ dst := WCap t p' g' b e a ]ᵣ> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      {
        assert (spec_incrementPC (<[ dst := WCap t p' g' b e a ]ᵣ> r) = None) as HH.
        { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
          + by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto.
        }
        apply (spec_incrementPC_fail_updatePC _ sr m st) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
                                                   by (destruct p; inversion Hstep; auto).
        iFailWP "Hφ" spec_Restrict_fail_PC_overflow_cap.
      }

      eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
          as (t'' & p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) (shadow':=st) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
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

      destruct (SealPermFlowsTo p' p && LocalityFlowsTo g' g) eqn:Hflows; cycle 1.
      { assert (Htag : t && SealPermFlowsTo p' p && LocalityFlowsTo g' g = false).
        { destruct t; simpl; auto. }
        rewrite Htag /update_reg /= in Hstep.
      destruct (spec_incrementPC (<[ dst := WSealRange false p' g' b e a ]ᵣ> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      {
        assert (spec_incrementPC (<[ dst := WSealRange false p' g' b e a ]ᵣ> r) = None) as HH.
        { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
          + by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto.
        }
        apply (spec_incrementPC_fail_updatePC _ sr m st) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
                                                   by (destruct p; inversion Hstep; auto).
        iFailWP "Hφ" spec_Restrict_fail_invalidated_PC_sr. }

      eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
          as (t'' & p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) (shadow':=st) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { destruct p; cbn in Hstep; eauto. }
      simplify_pair_eq.

      iFrame.
      iMod ((spec_regs_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      { apply is_Some_lookup_reg; done. }
      iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro. eapply spec_Restrict_spec_invalidated_sr; eauto.
      }
      apply andb_true_iff in Hflows as [HPflows HLflows].
      rewrite HPflows HLflows !andb_true_r /update_reg /= in Hstep.

      destruct (spec_incrementPC (<[ dst := WSealRange t p' g' b e a ]ᵣ> regs)) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      {
        assert (spec_incrementPC (<[ dst := WSealRange t p' g' b e a ]ᵣ> r) = None) as HH.
        { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
          + by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto.
        }
        apply (spec_incrementPC_fail_updatePC _ sr m st) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
                                                   by (destruct p; inversion Hstep; auto).
        iFailWP "Hφ" spec_Restrict_fail_PC_overflow_sr. }

      eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
          as (t'' & p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) (shadow':=st) in HuPC. 2: by eapply insert_mono; eauto. rewrite HuPC in Hstep.
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
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (p',g') = (decodePermPair z) ->
    PermFlowsTo p' pc_p = true →
    LocalityFlowsTo g' pc_g = true →
    rv ≠ cnull ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true p' g' pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrv)".
     iDestruct (spec_map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_map_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       simplify_pair_eq; rewrite !insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.
     }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       spec_incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma step_restrict_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv (t : bool) p g b e a z p' g' :
    ↑specN ⊆ Ep →
     decodeInstrW w = Restrict r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     rv ≠ cnull ->
     r1 ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap t p g b e a ∗
    rv ↣ᵣ WInt z
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z ∗
    r1 ↣ᵣ WCap t p' g' b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hrv)".
     iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_map_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
    { (* Success *)
      iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
              (insert_insert_ne _ PC r1) // insert_insert_eq.
      simplify_pair_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
      simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       spec_incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma step_restrict_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w z p' g' :
     ↑specN ⊆ Ep →
     decodeInstrW w = Restrict PC (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' pc_p = true →
     LocalityFlowsTo g' pc_g = true →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true p' g' pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows) "(#Hctx & Hj & HPC & Hpc_a)".
     iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     3,4: (simplify_map_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       simplify_pair_eq.
       rewrite !insert_insert_eq.
       iApply (spec_regs_of_map_1 with "Hmap"). }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       spec_incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma step_restrict_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a z p' g' :
    ↑specN ⊆ Ep →
     decodeInstrW w = Restrict r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodePermPair z) ->
     PermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     r1 ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap t p g b e a
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WCap t p' g' b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
     iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_map_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
               (insert_insert_ne _ PC r1) // insert_insert_eq. simplify_pair_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Success with WSealRange (contradiction) *)
      simplify_map_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       spec_incrementPC_inv; simplify_map_eq; eauto; congruence. }
   Qed.

 Lemma step_restrict_success_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv (t : bool) p g b e a z p' g' :
    ↑specN ⊆ Ep →
     decodeInstrW w = Restrict r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodeSealPermPair z) ->
     SealPermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     rv ≠ cnull ->
     r1 ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a ∗
    rv ↣ᵣ WInt z
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z ∗
    r1 ↣ᵣ WSealRange t p' g' b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hrv)".
     iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hrv") as "[Hmap (%&%&%)]".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

    destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_map_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
    { (* Success with WCap (contradiction) *)
      simplify_map_eq.
    }
    { (* Success *)
      iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
               (insert_insert_ne _ PC r1) // insert_insert_eq. simplify_pair_eq.
      iDestruct (spec_regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; simplify_map_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
      spec_incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

   Lemma step_restrict_success_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a z p' g' :
    ↑specN ⊆ Ep →
     decodeInstrW w = Restrict r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (p',g') = (decodeSealPermPair z) ->
     SealPermFlowsTo p' p = true →
     LocalityFlowsTo g' g = true →
     r1 ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p g b e a
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WSealRange t p' g' b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' HdecPair HPflows HLflows Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
     iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_Restrict with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by unfold regs_of; rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [| | | | * Hfail].
     3,4: (simplify_map_eq; simplify_pair_eq;
       match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end).
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq.
     }
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq
         (insert_insert_ne _ PC r1) // insert_insert_eq.
       simplify_pair_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       all: simplify_pair_eq; try match goal with Hbad : _ && _ = false |- _ =>
         rewrite HPflows HLflows in Hbad; discriminate
       end.
       spec_incrementPC_inv; simplify_map_eq; eauto. congruence. }
   Qed.

  Local Lemma restrict_invalidated_map_cap E pc_p pc_g pc_b pc_e pc_a
      w dst src regs regs' (t : bool) p g b e a n p' g' :
    ↑specN ⊆ E →
    decodeInstrW w = Restrict dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Restrict dst src) ⊆ dom regs →
    regs !!ᵣ dst = Some (WCap t p g b e a) →
    z_of_argument regs src = Some n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    spec_incrementPC (<[ dst := WCap false p' g' b e a ]ᵣ> regs) = Some regs' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Hdst Hsrc Hdecode Hflows Hincr) "(#Hctx & Hj & Hpc_a & Hmap)".
    iMod (step_Restrict with "[$Hctx $Hj $Hpc_a $Hmap]") as "H"; eauto.
    iDestruct "H" as (retv regs'') "(Hj & %Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq; simplify_pair_eq.
    - repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
    - simplify_eq. iModIntro. iFrame.
    - destruct Hfail; simplify_eq; simplify_pair_eq; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
  Qed.

  Local Lemma restrict_invalidated_map_sr E pc_p pc_g pc_b pc_e pc_a
      w dst src regs regs' (t : bool) p g b e a n p' g' :
    ↑specN ⊆ E →
    decodeInstrW w = Restrict dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Restrict dst src) ⊆ dom regs →
    regs !!ᵣ dst = Some (WSealRange t p g b e a) →
    z_of_argument regs src = Some n →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    spec_incrementPC (<[ dst := WSealRange false p' g' b e a ]ᵣ> regs) = Some regs' →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    pc_a ↣ₐ w ∗ [∗ map] k↦y ∈ regs', k ↣ᵣ y.
  Proof.
    iIntros (HE Hinstr Hvpc HPC Dregs Hdst Hsrc Hdecode Hflows Hincr) "(#Hctx & Hj & Hpc_a & Hmap)".
    iMod (step_Restrict with "[$Hctx $Hj $Hpc_a $Hmap]") as "H"; eauto.
    iDestruct "H" as (retv regs'') "(Hj & %Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq; simplify_pair_eq.
    - repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
    - simplify_eq. iModIntro. iFrame.
    - destruct Hfail; simplify_eq; simplify_pair_eq; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; congruence.
  Qed.

  Lemma step_restrict_invalidated_z E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n p' g' :
    ↑specN ⊆ E →
    decodeInstrW w = Restrict dst (inl n) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap t p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap false p' g' b e a.
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull Hdecode Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iMod (restrict_invalidated_map_cap E _ _ _ _ _ w _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WCap false p' g' b e a]> (∅ : Reg))) t p g b e a n p' g' with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /spec_incrementPC /spec_incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma step_restrict_invalidated_reg E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n p'
      g' src (ws : Word) :
    ↑specN ⊆ E →
    decodeInstrW w = Restrict dst (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (src = cnull) then WInt 0 else ws) = WInt n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p && LocalityFlowsTo g' g = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap t p g b e a ∗
    src ↣ᵣ ws
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WCap false p' g' b e a ∗
    src ↣ᵣ ws.
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull Hread Hdecode Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (restrict_invalidated_map_cap E _ _ _ _ _ w _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WCap false p' g' b e a]> (<[src := ws]> (∅ : Reg)))) t p g b e a n p' g'
        with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
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

  Lemma step_restrict_invalidated_z_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n p' g' :
    ↑specN ⊆ E →
    decodeInstrW w = Restrict dst (inl n) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealRange t p g b e a
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealRange false p' g' b e a.
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull Hdecode Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iMod (restrict_invalidated_map_sr E _ _ _ _ _ w _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WSealRange false p' g' b e a]> (∅ : Reg))) t p g b e a n p' g' with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /spec_incrementPC /spec_incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma step_restrict_invalidated_reg_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n
      p' g' src (ws : Word) :
    ↑specN ⊆ E →
    decodeInstrW w = Restrict dst (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (src = cnull) then WInt 0 else ws) = WInt n →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p && LocalityFlowsTo g' g = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealRange t p g b e a ∗
    src ↣ᵣ ws
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    dst ↣ᵣ WSealRange false p' g' b e a ∗
    src ↣ᵣ ws.
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hnull Hread Hdecode Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1 & Hr2)".
    iDestruct (spec_map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iMod (restrict_invalidated_map_sr E _ _ _ _ _ w _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WSealRange false p' g' b e a]> (<[src := ws]> (∅ : Reg)))) t p g b e a n
        p' g' with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
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

  Lemma step_restrict_invalidated_z_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w n p' g' :
    ↑specN ⊆ E →
    decodeInstrW w = Restrict PC (inl n) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (p', g') = decodePermPair n →
    PermFlowsTo p' pc_p && LocalityFlowsTo g' pc_g = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap false p' g' pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w.
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hdecode Hreject) "(#Hctx & Hj & HPC & Hmem)".
    iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
    iMod (restrict_invalidated_map_cap E _ _ _ _ _ w _ _ _ (<[PC := WCap false p' g' pc_b pc_e
        pc_a']> (∅ : Reg)) true pc_p pc_g pc_b pc_e pc_a n p' g' with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /spec_incrementPC /spec_incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_1 with "Hmap").
  Qed.

  Lemma step_restrict_invalidated_reg_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w n p' g' src (ws : Word) :
    ↑specN ⊆ E →
    decodeInstrW w = Restrict PC (inr src) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (src = cnull) then WInt 0 else ws) = WInt n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' pc_p && LocalityFlowsTo g' pc_g = false →
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ ws
    ={E}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap false p' g' pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    src ↣ᵣ ws.
  Proof.
    iIntros (HE Hinstr Hpc Hincr Hread Hdecode Hreject) "(#Hctx & Hj & HPC & Hmem & Hr1)".
    iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iMod (restrict_invalidated_map_cap E _ _ _ _ _ w _ _ _ (<[PC := WCap false p' g' pc_b pc_e
        pc_a']> (<[src := ws]> (∅ : Reg))) true pc_p pc_g pc_b pc_e pc_a n p' g' with "[$Hctx $Hj $Hmem $Hmap]") as "H"; eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /spec_incrementPC /spec_incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iDestruct "H" as "(Hj & Hmem & Hmap)". iModIntro. iFrame "Hj Hmem".
      iApply (spec_regs_of_map_2 with "Hmap"); eauto.
  Qed.


End spec_rules.
