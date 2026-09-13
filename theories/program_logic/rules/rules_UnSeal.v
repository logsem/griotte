From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive UnSeal_failure  (regs: Reg) (dst: RegName) (src1 src2: RegName) : Reg → Prop :=
  | UnSeal_fail_sealr w :
      regs !!ᵣ src1 = Some w →
      is_sealr w = false →
      UnSeal_failure regs dst src1 src2 regs
  | UnSeal_fail_sealed w :
      regs !!ᵣ src2 = Some w →
      is_sealed w = false →
      UnSeal_failure regs dst src1 src2 regs
  | UnSeal_fail_invalidated_PC (t : bool) p g b e a a' sb :
      regs !!ᵣ src1 = Some (WSealRange t p g b e a) →
      regs !!ᵣ src2 = Some (WSealed a' sb) →
      t && get_tag_sealable sb && permit_unseal p && withinBounds b e a && (a' =? a)%Z = false →
      incrementPC (<[ dst := WSealable (clear_tag_sealable sb) ]ᵣ> regs) = None →
      UnSeal_failure regs dst src1 src2 regs
  | UnSeal_fail_incrPC p g b e a sb :
      regs !!ᵣ src1 = Some (WSealRange true p g b e a) →
      regs !!ᵣ src2 = Some (WSealed a sb) →
      get_tag_sealable sb = true →
      permit_unseal p = true →
      withinBounds b e a = true →
      incrementPC (<[ dst := WSealable sb ]ᵣ> regs) = None →
      UnSeal_failure regs dst src1 src2 regs.

  Inductive UnSeal_spec (regs: Reg) (dst: RegName) (src1 src2: RegName) (regs': Reg): griotte_lang.val -> Prop :=
  | UnSeal_spec_success p g b e a sb:
      regs !!ᵣ src1 = Some (WSealRange true p g b e a) →
      regs !!ᵣ src2 = Some (WSealed a sb) →
      get_tag_sealable sb = true →
      permit_unseal p = true →
      withinBounds b e a = true →
      incrementPC (<[ dst := WSealable sb ]ᵣ> regs) = Some regs' →
      UnSeal_spec regs dst src1 src2 regs' NextIV
  | UnSeal_spec_invalidated (t : bool) p g b e a a' sb :
      regs !!ᵣ src1 = Some (WSealRange t p g b e a) →
      regs !!ᵣ src2 = Some (WSealed a' sb) →
      t && get_tag_sealable sb && permit_unseal p && withinBounds b e a && (a' =? a)%Z = false →
      incrementPC (<[ dst := WSealable (clear_tag_sealable sb) ]ᵣ> regs) = Some regs' →
      UnSeal_spec regs dst src1 src2 regs' NextIV
  | UnSeal_spec_failure :
      UnSeal_failure regs dst src1 src2 regs' →
      UnSeal_spec regs dst src1 src2 regs' FailedV.

  Lemma wp_UnSeal Ep pc_p pc_g pc_b pc_e pc_a w dst src1 src2 regs :
    decodeInstrW w = UnSeal dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ UnSeal_spec regs dst src1 src2 regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr Hsr] Hm ] /=". destruct σ1 as [ [r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    odestruct (Hri src2) as [r2v [Hr'2 Hr2]]; first by set_solver+.
    odestruct (Hri src1) as [r1v [Hr'1 Hr1]]; first  by set_solver+.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first  by set_solver+. clear Hri.

    rewrite /exec /= Hr2 Hr1 /= in Hstep.

    (* Now we start splitting on the different cases in the UnSeal spec, and prove them one at a time *)
     destruct (is_sealr r1v) eqn:Hr1v.
     2:{ (* Failure: the source has the wrong shape *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_sealr in Hr1v.
         destruct_word r1v; by simplify_pair_eq.
       }
        iFailWP "Hφ" UnSeal_fail_sealr.
     }
     destruct r1v as [ | [ | t p g b e a ] | | ]; try inversion Hr1v. clear Hr1v.
     destruct (is_sealed r2v) eqn:Hr2v.
     2:{ (* Failure: the source has the wrong shape *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_sealed in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" UnSeal_fail_sealed.
     }
     destruct r2v as [ | [ | ] | | a' sb ]; try inversion Hr2v. clear Hr2v.

     destruct (t && get_tag_sealable sb && permit_unseal p && withinBounds b e a && (a' =? a)%Z) eqn:Hvalid.
     2: { (* Invalidation continues with the wrapper changed and the payload tag cleared. *)
     destruct (incrementPC (<[ dst := (WSealable (clear_tag_sealable sb)) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC (<[ dst := (WSealable (clear_tag_sealable sb)) ]ᵣ> r) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         + by rewrite lookup_insert_is_Some'; eauto.
         + by apply insert_mono; eauto.
       }

       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iFailWP "Hφ" UnSeal_fail_invalidated_PC.
     }

     (* Success *)
     rewrite /update_reg /= in Hstep.
     eapply (incrementPC_success_updatePC _ sr m) in Hregs'
       as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     { apply is_Some_lookup_reg; done. }
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply UnSeal_spec_invalidated; eauto.
     rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
     }
     apply andb_true_iff in Hvalid as [Hvalid Heq].
     apply Z.eqb_eq, finz_to_z_eq in Heq. subst a'.
     apply andb_true_iff in Hvalid as [Hvalid Hwb].
     apply andb_true_iff in Hvalid as [Hvalid Hps].
     apply andb_true_iff in Hvalid as [-> Htag].
     destruct (incrementPC (<[ dst := (WSealable sb) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
     2: { (* Failure: the PC could not be incremented correctly *)
       assert (incrementPC (<[ dst := (WSealable sb) ]ᵣ> r) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         + by rewrite lookup_insert_is_Some'; eauto.
         + by apply insert_mono; eauto.
       }

       rewrite incrementPC_fail_updatePC /= in Hstep; auto.
       symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
       iFailWP "Hφ" UnSeal_fail_incrPC.
     }

     (* Success *)
     rewrite /update_reg /= in Hstep.
     eapply (incrementPC_success_updatePC _ sr m) in Hregs'
       as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
     iFrame.
     iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     { apply is_Some_lookup_reg; done. }
     iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
     iFrame. iModIntro. iApply "Hφ". iFrame.
     iPureIntro. eapply UnSeal_spec_success; eauto.
     rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
     Unshelve. all: auto.
  Qed.

  (* after pruning impossible or impractical options, 4 wp rules remain *)

  Lemma wp_unseal_success E pc_p pc_g pc_b pc_e pc_a w w' dst r1 r2 p g b e a sb pc_a' :
    decodeInstrW w = UnSeal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ w'
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a
        ∗ ▷ r2 ↦ᵣ WSealed a sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WSealable sb
          ∗ r1 ↦ᵣ WSealRange true p g b e a
          ∗ r2 ↦ᵣ WSealed a sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ??? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_unseal_r1 E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a sb pc_a' :
    decodeInstrW w = UnSeal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a
        ∗ ▷ r2 ↦ᵣ WSealed a sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealable sb
          ∗ r2 ↦ᵣ WSealed a sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  Lemma wp_unseal_r2 E pc_p pc_g pc_b pc_e pc_a w r1 r2 p g b e a sb pc_a' :
    decodeInstrW w = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a
        ∗ ▷ r2 ↦ᵣ WSealed a sb }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealRange true p g b e a
          ∗ r2 ↦ᵣ WSealable sb
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Htag Hps Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ r2 PC) // insert_insert_eq (insert_insert_ne _ r1 r2) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

  (* The below case could be useful, if what we unseal is a PC capability *)
  Lemma wp_unseal_PC E pc_p pc_g pc_b pc_e pc_a w w' r1 r2 p g b e a p' g' b' e' a' a'' :
    decodeInstrW w = UnSeal PC r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    permit_unseal p = true →
    withinBounds b e a = true →
    (a' + 1)%a = Some a'' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange true p g b e a
        ∗ ▷ r2 ↦ᵣ WSealed a (SCap true p' g' b' e' a') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true p' g' b' e' a''
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WSealRange true p g b e a
          ∗ r2 ↦ᵣ WSealed a (SCap true p' g' b' e' a')
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hps Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | | * Hfail].
    2: (simplify_map_eq;
        repeat match goal with Hbad : _ && _ = false |- _ =>
          apply andb_false_iff in Hbad; destruct Hbad
        end; try congruence; match goal with Hbad : (_ =? _)%Z = false |- _ =>
          rewrite Z.eqb_refl in Hbad; discriminate
        end).
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto; iFrame. }
    { (* Failure (contradiction) *)
      destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; try congruence.
    }
    Unshelve. all: auto.
  Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  Local Lemma unseal_invalidated_map E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a a' sb :
    decodeInstrW w = UnSeal dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (UnSeal dst src1 src2) ⊆ dom regs →
    regs !!ᵣ src1 = Some (WSealRange t p g b e a) →
    regs !!ᵣ src2 = Some (WSealed a' sb) →
    t && get_tag_sealable sb && permit_unseal p && withinBounds b e a && (a' =? a)%Z = false →
    incrementPC (<[ dst := WSealable (clear_tag_sealable sb) ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hr1 Hr2 Hvalid Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_UnSeal with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | Hfail].
    - simplify_eq.
      repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
      match goal with Hbad : (_ =? _)%Z = false |- _ =>
        rewrite Z.eqb_refl in Hbad; discriminate
      end.
    - simplify_eq. iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; cbn in *; try congruence.
      all: repeat match goal with Hbad : _ && _ = false |- _ =>
        apply andb_false_iff in Hbad; destruct Hbad
      end; try congruence.
      all: match goal with Hbad : (_ =? _)%Z = false |- _ =>
        rewrite Z.eqb_refl in Hbad; discriminate
      end.
  Qed.

  (* UnSeal: the PC-destination case advances the unsealed payload cursor. *)
  Lemma wp_unseal_invalidated E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 (t : bool) p g b e a (o :
      OType) sb dst (wd : Word) :
    decodeInstrW w = UnSeal dst r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e a && (o =? a)%Z = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r2 ↦ᵣ WSealed o (sb)
        ∗ ▷ dst ↦ᵣ wd }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a
        ∗ r2 ↦ᵣ WSealed o (sb)
        ∗ dst ↦ᵣ (if decide (dst = cnull) then WInt 0 else WSealable (clear_tag_sealable (sb))) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealRange t p g b e a]> (<[r2 := WSealed o (sb)]> (<[dst := (if decide
        (dst = cnull) then WInt 0 else WSealable (clear_tag_sealable (sb)))]> (∅ : Reg))))) t p g b
        e a o (sb) with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_4 with "Hmap"); eauto.
  Qed.

  Lemma wp_unseal_invalidated_r1 E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 (t : bool) p g b e a (o :
      OType) sb :
    decodeInstrW w = UnSeal r1 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e a && (o =? a)%Z = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r2 ↦ᵣ WSealed o (sb) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealable (clear_tag_sealable (sb))
        ∗ r2 ↦ᵣ WSealed o (sb) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealable (clear_tag_sealable (sb))]> (<[r2 := WSealed o (sb)]> (∅ :
        Reg)))) t p g b e a o (sb) with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_unseal_invalidated_r2 E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 (t : bool) p g b e a (o :
      OType) sb :
    decodeInstrW w = UnSeal r2 r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (sb) && permit_unseal p && withinBounds b e a && (o =? a)%Z = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r2 ↦ᵣ WSealed o (sb) }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a
        ∗ r2 ↦ᵣ WSealable (clear_tag_sealable (sb)) }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[r1 := WSealRange t p g b e a]> (<[r2 := WSealable (clear_tag_sealable (sb))]> (∅
        : Reg)))) t p g b e a o (sb) with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_unseal_invalidated_PC E pc_p pc_g pc_b pc_e pc_a pc_a' w r1 r2 (t : bool) p g b e a (o :
      OType) (t' : bool) p' g' b' e' a' :
    decodeInstrW w = UnSeal PC r1 r2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (a' + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    t && get_tag_sealable (SCap t' p' g' b' e' a') && permit_unseal p && withinBounds b e a && (o =? a)%Z = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r2 ↦ᵣ WSealed o (SCap t' p' g' b' e' a') }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false p' g' b' e' pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WSealRange t p g b e a
        ∗ r2 ↦ᵣ WSealed o (SCap t' p' g' b' e' a') }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull1 Hnull2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (unseal_invalidated_map E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false p' g' b' e' pc_a']>
        (<[r1 := WSealRange t p g b e a]> (<[r2 := WSealed o (SCap t' p' g' b' e' a')]> (∅ : Reg))))
        t p g b e a o (SCap t' p' g' b' e' a') with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.
End instruction_outcomes.
