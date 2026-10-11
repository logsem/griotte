From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base_binary.
From griotte Require Import rules_Lea.

(** * Spec rules for [Lea] (spec copies of [rules_Lea.v]) *)

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

  Inductive spec_Lea_failure (regs: Reg) (r1: RegName) (rv: Z + RegName) :=
  | spec_Lea_fail_rv_nonconst :
     z_of_argument regs rv = None ->
     spec_Lea_failure regs r1 rv
  | spec_Lea_fail_allowed : forall w,
     regs !!ᵣ r1 = Some w ->
     is_mutable_range w = false →
     spec_Lea_failure regs r1 rv
  | spec_Lea_fail_overflow_cap : forall (t : bool) p g b e a z,
     regs !!ᵣ r1 = Some (WCap t p g b e a) ->
     z_of_argument regs rv = Some z ->
     (a + z)%a = None ->
     spec_incrementPC (<[ r1 := WCap false p g b e a ]ᵣ> regs) = None ->
     spec_Lea_failure regs r1 rv
  | spec_Lea_fail_overflow_PC_cap : forall (t : bool) p g b e a z a',
     regs !!ᵣ r1 = Some (WCap t p g b e a) ->
     z_of_argument regs rv = Some z ->
     (a + z)%a = Some a' ->
     spec_incrementPC (<[ r1 := WCap t p g b e a' ]ᵣ> regs) = None ->
     spec_Lea_failure regs r1 rv
  | spec_Lea_fail_overflow_sr : forall (t : bool) p g b e a z,
     regs !!ᵣ r1 = Some (WSealRange t p g b e a) ->
     z_of_argument regs rv = Some z ->
     (a + z)%ot = None ->
     spec_incrementPC (<[ r1 := WSealRange false p g b e a ]ᵣ> regs) = None ->
     spec_Lea_failure regs r1 rv
  | spec_Lea_fail_overflow_PC_sr : forall (t : bool) p g b e a z a',
     regs !!ᵣ r1 = Some (WSealRange t p g b e a) ->
     z_of_argument regs rv = Some z ->
     (a + z)%ot = Some a' ->
     spec_incrementPC (<[ r1 := WSealRange t p g b e a' ]ᵣ> regs) = None ->
     spec_Lea_failure regs r1 rv
  .

  Inductive spec_Lea_spec
    (regs: Reg) (r1: RegName) (rv: Z + RegName)
    (regs': Reg) : griotte_lang.val → Prop
  :=
  | spec_Lea_spec_success_cap: forall (t : bool) p g b e a z a',
    regs !!ᵣ r1 = Some (WCap t p g b e a) ->
    z_of_argument regs rv = Some z ->
    (a + z)%a = Some a' ->
    spec_incrementPC
      (<[ r1 := WCap t p g b e a' ]ᵣ> regs) = Some regs' ->
    spec_Lea_spec regs r1 rv regs' NextIV
  | spec_Lea_spec_success_sr: forall (t : bool) p g b e a z a',
    regs !!ᵣ r1 = Some (WSealRange t p g b e a) ->
    z_of_argument regs rv = Some z ->
    (a + z)%ot = Some a' ->
    spec_incrementPC
      (<[ r1 := WSealRange t p g b e a' ]ᵣ> regs) = Some regs' ->
    spec_Lea_spec regs r1 rv regs' NextIV
  | spec_Lea_spec_invalidated_cap: forall (t : bool) p g b e a z,
    regs !!ᵣ r1 = Some (WCap t p g b e a) ->
    z_of_argument regs rv = Some z ->
    (a + z)%a = None ->
    spec_incrementPC
      (<[ r1 := WCap false p g b e a ]ᵣ> regs) = Some regs' ->
    spec_Lea_spec regs r1 rv regs' NextIV
  | spec_Lea_spec_invalidated_sr: forall (t : bool) p g b e a z,
    regs !!ᵣ r1 = Some (WSealRange t p g b e a) ->
    z_of_argument regs rv = Some z ->
    (a + z)%ot = None ->
    spec_incrementPC
      (<[ r1 := WSealRange false p g b e a ]ᵣ> regs) = Some regs' ->
    spec_Lea_spec regs r1 rv regs' NextIV
  | spec_Lea_spec_failure :
    spec_Lea_failure regs r1 rv ->
    spec_Lea_spec regs r1 rv regs' FailedV.

  Lemma Lea_spec_determ regs r rv regs1 regs2 v1 v2 :
    spec_Lea_spec regs r rv regs1 v1 →
    spec_Lea_spec regs r rv regs2 v2 →
    v1 = v2 ∧ (v1 = NextIV → regs1 = regs2).
  Proof. solve_spec_determ spec_Lea_failure. Qed.

   Lemma Lea_spec_lift regs r1 rv lregs' v :
    Lea_spec (lift_regs regs) r1 rv lregs' v →
    ∃ regs', (v = NextIV → lregs' = lift_regs regs') ∧ spec_Lea_spec regs r1 rv regs' v.
  Proof. spec_lift Lea_failure regs. Qed.

  Lemma step_lea Ep pc_p pc_g pc_b pc_e pc_a r1 w arg (regs: Reg) :
     ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 arg →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
     regs_of (Lea r1 arg) ⊆ dom regs →
     spec_ctx ∗
     ⤇ Seq (Instr Executable) ∗
     pc_a ↣ₐ w ∗
     ([∗ map] k↦y ∈ regs, k ↣ᵣ y)
     ={Ep}=∗
     ∃ retv regs',
       ⤇ Seq (of_val retv) ∗
       ⌜ spec_Lea_spec regs r1 arg regs' retv ⌝ ∗
       pc_a ↣ₐ w ∗
       [∗ map] k↦y ∈ regs', k ↣ᵣ y.
   Proof.
     iIntros (HE Hinstr Hvpc HPC Dregs) "(#Hctx & Hj & Hpc_a & Hmap)".
     iApply (spec_step_exec_1 with "Hctx Hj"); first done.
    iIntros (Φ) "Hφ". iIntros ([[[r sr] m] st] c σ2 Hstep) "[[Hr Hsr] Hm] /=".
     iDestruct (spec_regs_valid_inclSepM with "Hr Hmap") as %Hregs.
     pose proof (lookup_weaken _ _ _ _ HPC Hregs).
     iDestruct (spec_mem_valid with "Hm Hpc_a") as %Hpc_a; auto.
     eapply step_exec_inv in Hstep; eauto.
     unfold exec in Hstep; simpl in Hstep.

     specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.

     odestruct (Hri r1) as [r1v [Hr'1 Hr1]]; first by set_solver+.
     rewrite Hr1 /= in Hstep.

     destruct (z_of_argument regs arg) as [ argz |] eqn:Harg;
       pose proof Harg as Harg'; cycle 1.
     { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
       unfold z_of_argument in Harg, Hstep. destruct arg as [| r0]; [ congruence |].
       odestruct (Hri r0) as [r0v [Hr'0 Hr0]].
       { unfold regs_of_argument. set_solver+. }
       rewrite Hr0 Hr'0 in Harg Hstep.
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       { destruct_word r0v; cbn in Hstep; try congruence; by simplify_pair_eq. }
       iFailWP "Hφ" spec_Lea_fail_rv_nonconst. }
     apply (z_of_arg_mono _ r) in Harg; auto. rewrite Harg in Hstep; cbn in Hstep.

     destruct (is_mutable_range r1v) eqn:Hr1v.
     2: { (* Failure: r1v is not of the right type *)
       unfold is_mutable_range in Hr1v.
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       { destruct r1v as [ | [t p b e a | ] | | ]; try by inversion Hr1v.
         all: by simplify_pair_eq. }
       iFailWP "Hφ" spec_Lea_fail_allowed. }

     (* Now the proof splits depending on the type of value in r1v *)
     destruct r1v as [ | [t p g b e a | t p g b e a] | | ].
     1,4,5: inversion Hr1v.

     (* First, the case where r1v is a capability *)
     + destruct (a + argz)%a as [ a' |] eqn:Hoffset; cycle 1.
       { (* Current-address overflow invalidates; PC advancement may still roll back. *)
       rewrite /update_reg /= in Hstep.
       destruct (spec_incrementPC (<[ r1 := WCap false p g b e a ]ᵣ> regs)) as [ regs' |] eqn:Hregs';
         pose proof Hregs' as Hregs'2; cycle 1.
       { (* Failure: incrementing PC overflows *)
         assert (spec_incrementPC (<[ r1 := WCap false p g b e a ]ᵣ> r) = None) as HH.
         { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
           + simplify_map_eq. by rewrite lookup_insert_is_Some'; eauto.
           + by apply insert_mono; eauto.
         }
         apply (spec_incrementPC_fail_updatePC _ sr m st) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" spec_Lea_fail_overflow_cap. }

       (* Success *)
       eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
         as (t' & p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
       rewrite HuPC in Hstep; clear HuPC.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct_perm p; cbn in Hstep; eauto. }
       simplify_pair_eq.

       iFrame.
       iMod ((spec_regs_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       { apply is_Some_lookup_reg; done. }
       iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
       eapply spec_Lea_spec_invalidated_cap; eauto. }

       rewrite /update_reg /= in Hstep.
       destruct (spec_incrementPC (<[ r1 := WCap t p g b e a' ]ᵣ> regs)) as [ regs' |] eqn:Hregs';
         pose proof Hregs' as Hregs'2; cycle 1.
       { (* Failure: incrementing PC overflows *)
         assert (spec_incrementPC (<[ r1 := WCap t p g b e a' ]ᵣ> r) = None) as HH.
         { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
           + simplify_map_eq. by rewrite lookup_insert_is_Some'; eauto.
           + by apply insert_mono; eauto.
         }
         apply (spec_incrementPC_fail_updatePC _ sr m st) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" spec_Lea_fail_overflow_PC_cap. }

       (* Success *)
       eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
         as (t' & p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
       rewrite HuPC in Hstep; clear HuPC.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct_perm p; cbn in Hstep; eauto. }
       simplify_pair_eq.

       iFrame.
       iMod ((spec_regs_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       { apply is_Some_lookup_reg; done. }
       iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
       eapply spec_Lea_spec_success_cap; eauto.
    (* Now, the case where r1v is a sealrange *)
     + destruct (a + argz)%ot as [ a' |] eqn:Hoffset; cycle 1.
       { (* Current-address overflow invalidates; PC advancement may still roll back. *)
       rewrite /update_reg /= in Hstep.
       destruct (spec_incrementPC (<[ r1 := WSealRange false p g b e a ]ᵣ> regs)) as [ regs' |] eqn:Hregs';
         pose proof Hregs' as Hregs'2; cycle 1.
       { (* Failure: incrementing PC overflows *)
         assert (spec_incrementPC (<[ r1 := WSealRange false p g b e a ]ᵣ> r) = None) as HH.
         { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
           + simplify_map_eq; by rewrite lookup_insert_is_Some'; eauto.
           + by apply insert_mono; eauto. }
         apply (spec_incrementPC_fail_updatePC _ sr m st) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" spec_Lea_fail_overflow_sr. }

       (* Success *)
       eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
         as (t' & p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
       rewrite HuPC in Hstep; clear HuPC.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct p; cbn in Hstep; eauto. }
       simplify_pair_eq.

       iFrame.
       iMod ((spec_regs_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       { apply is_Some_lookup_reg; done. }
       iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
       eapply spec_Lea_spec_invalidated_sr; eauto. }

       rewrite /update_reg /= in Hstep.
       destruct (spec_incrementPC (<[ r1 := WSealRange t p g b e a' ]ᵣ> regs)) as [ regs' |] eqn:Hregs';
         pose proof Hregs' as Hregs'2; cycle 1.
       { (* Failure: incrementing PC overflows *)
         assert (spec_incrementPC (<[ r1 := WSealRange t p g b e a' ]ᵣ> r) = None) as HH.
         { eapply spec_incrementPC_overflow_mono; first eapply Hregs'.
           + simplify_map_eq; by rewrite lookup_insert_is_Some'; eauto.
           + by apply insert_mono; eauto. }
         apply (spec_incrementPC_fail_updatePC _ sr m st) in HH. rewrite HH in Hstep.
         assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->)
             by (destruct p; inversion Hstep; auto).
         iFailWP "Hφ" spec_Lea_fail_overflow_PC_sr. }

       (* Success *)
       eapply (spec_incrementPC_success_updatePC _ sr m st) in Hregs'
         as (t' & p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
       rewrite HuPC in Hstep; clear HuPC.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { destruct p; cbn in Hstep; eauto. }
       simplify_pair_eq.

       iFrame.
       iMod ((spec_regs_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       { apply is_Some_lookup_reg; done. }
       iMod ((spec_regs_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame. iModIntro. iApply "Hφ". iFrame. iPureIntro.
       eapply spec_Lea_spec_success_sr; eauto.
   Unshelve. all: auto.
   Qed.

   Lemma step_lea_success_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w rv z a' :
     ↑specN ⊆ Ep →
     decodeInstrW w = Lea PC (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     rv ≠ cnull ->
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrv)".
     iDestruct (spec_map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert_eq. (* TODO: add to simplify_map_eq via simpl_map? *)
       iApply (spec_regs_of_map_2 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try destruct pc_p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma step_lea_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv (t : bool) p g b e a z a' :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
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
    r1 ↣ᵣ WCap t p g b e a'.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hrv)".
     iDestruct (spec_map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq.
       rewrite (insert_insert_ne _ r1 PC) // (insert_insert_ne _ r1 rv) // insert_insert_eq.
       iApply (spec_regs_of_map_3 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma step_lea_success_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w z a' :
     ↑specN ⊆ Ep →
     decodeInstrW w = Lea PC (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (a' + 1)%a = Some pc_a' →
     (pc_a + z)%a = Some a' →
     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha') "(#Hctx & Hj & HPC & Hpc_a)".
     iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert_eq. iApply (spec_regs_of_map_1 with "Hmap"); eauto. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try destruct pc_p; cbn in * ; congruence. }
     Unshelve. all: auto.
   Qed.

   Lemma step_lea_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a z a' :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = Some a' →
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
    r1 ↣ᵣ WCap t p g b e a'.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
     iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
     Unshelve. all:auto.
   Qed.

   Lemma step_lea_success_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv (t : bool) p g b e a z a' :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →
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
    r1 ↣ᵣ WSealRange t p g b e a'.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hrv)".
     iDestruct (spec_map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_map_eq.
     { (* Success with WSealCap (contradiction) *)
       simplify_map_eq. }
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq.
       rewrite (insert_insert_ne _ r1 PC) // (insert_insert_ne _ r1 rv) // insert_insert_eq.
       iApply (spec_regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       congruence.
     }
    Unshelve. all: auto.
   Qed.

  Lemma step_lea_success_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a z a' :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = Some a' →
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
    r1 ↣ᵣ WSealRange t p g b e a'.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
     iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     3,4: by simplify_map_eq.
     { (* Success with WSealRange (contradiction) *)
       simplify_map_eq. }
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       congruence.
     }
     Unshelve. all:auto.
   Qed.

   Lemma step_lea_overflow_reg_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w rv z :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea PC (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (pc_a + z)%a = None →
     rv ≠ cnull ->

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w ∗
    rv ↣ᵣ WInt z.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hrv)".
     iDestruct (spec_map_of_regs_2 with "HPC Hrv") as "[Hmap %]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert_eq. (* TODO: add to simplify_map_eq via simpl_map? *)
       iApply (spec_regs_of_map_2 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try destruct pc_p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma step_lea_overflow_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv (t : bool) p g b e a z :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = None →
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
    r1 ↣ᵣ WCap false p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hrv)".
     iDestruct (spec_map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq.
       rewrite (insert_insert_ne _ r1 PC) // (insert_insert_ne _ r1 rv) // insert_insert_eq.
       iApply (spec_regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
    Unshelve. all: auto.
   Qed.

   Lemma step_lea_overflow_z_PC Ep pc_p pc_g pc_b pc_e pc_a pc_a' w z :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea PC (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (pc_a + z)%a = None →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w
    ={Ep}=∗
    ⤇ Seq (Instr NextI) ∗
    PC ↣ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↣ₐ w.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha') "(#Hctx & Hj & HPC & Hpc_a)".
     iDestruct (spec_map_of_regs_1 with "HPC") as "Hmap".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       rewrite !insert_insert_eq. iApply (spec_regs_of_map_1 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try destruct pc_p; cbn in * ; congruence. }
     Unshelve. all: auto.
   Qed.

   Lemma step_lea_overflow_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a z :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%a = None →
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
    r1 ↣ᵣ WCap false p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
     iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     1,2,4: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       all: try destruct p; cbn in * ; congruence. }
     Unshelve. all:auto.
   Qed.

   Lemma step_lea_overflow_reg_sr Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 rv (t : bool) p g b e a z :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inr rv) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = None →
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
    r1 ↣ᵣ WSealRange false p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull Hcnull') "(#Hctx & Hj & HPC & Hpc_a & Hr1 & Hrv)".
     iDestruct (spec_map_of_regs_3 with "HPC Hrv Hr1") as "[Hmap (%&%&%)]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     1,2,3: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq.
       rewrite (insert_insert_ne _ r1 PC) // (insert_insert_ne _ r1 rv) // insert_insert_eq.
       iApply (spec_regs_of_map_3 with "Hmap"); eauto. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       congruence.
     }
    Unshelve. all: auto.
   Qed.

   Lemma step_lea_overflow_z_sr Ep pc_p pc_g pc_b pc_e pc_a pc_a' w r1 (t : bool) p g b e a z :
    ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + 1)%a = Some pc_a' →
     (a + z)%ot = None →
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
    r1 ↣ᵣ WSealRange false p g b e a.
   Proof.
     iIntros (HE Hinstr Hvpc Hpca' Ha' Hcnull) "(#Hctx & Hj & HPC & Hpc_a & Hr1)".
     iDestruct (spec_map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".

     destruct Hspec as [ | | | | * Hfail ].
     1,2,3: by simplify_map_eq.
     { (* Success *)
       iModIntro. iFrame. spec_incrementPC_inv; simplify_map_eq.
       (* FIXME: tedious *)
       rewrite insert_insert_ne // insert_insert_eq insert_insert_ne // insert_insert_eq.
       iDestruct (spec_regs_of_map_2 with "Hmap") as "[? ?]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try spec_incrementPC_inv; simplify_map_eq; eauto.
       congruence.
     }
     Unshelve. all:auto.
   Qed.

   Lemma step_Lea_fail_integer Ep pc_p pc_g pc_b pc_e pc_a w r1 z z' :
     ↑specN ⊆ Ep →
     decodeInstrW w = Lea r1 (inl z) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →

     spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↣ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    pc_a ↣ₐ w ∗
    r1 ↣ᵣ WInt z'
    ={Ep}=∗
    ⤇ Seq (Instr Failed) ∗
    True.
   Proof.
     iIntros (HE Hdecode Hvpc) "(#Hctx & Hj & HPC & Hpc_a & Hsrc)".
     iDestruct (spec_map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
     iMod (step_lea with "[$Hctx $Hj $Hmap $Hpc_a]") as "H"; eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     iDestruct "H" as (retv regs') "(Hj & %Hspec & Hpc_a & Hmap)".
     destruct Hspec as [* Hsucc | * Hsucc | * Hsucc | * Hsucc |].
     3,4: (destruct (decide (r1 = cnull)); simplify_map_eq).
     { (* Success (contradiction) *) simplify_map_eq.
       destruct (decide (r1 = cnull)); done.
     }
     { (* Success (contradiction) *) simplify_map_eq.
       destruct (decide (r1 = cnull)); done.
     }
     { (* Failure, done *) iModIntro. by iFrame. }
   Qed.




End spec_rules.
