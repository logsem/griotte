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

  Inductive Subseg_failure  (regs: Reg) (dst: RegName) (src1 src2: Z + RegName) : Reg → Prop :=
  | Subseg_fail_allowed w :
      regs !!ᵣ dst = Some w →
      is_mutable_range w = false →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_src1_nonz :
      z_of_argument regs src1 = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_src2_nonz :
      z_of_argument regs src2 = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC_cap (t : bool) p g b e a n1 n2 a1 a2 :
      regs !!ᵣ dst = Some (WCap t p g b e a) →
      z_of_argument regs src1 = Some n1 →
      z_of_argument regs src2 = Some n2 →
      z_to_addr n1 = Some a1 →
      z_to_addr n2 = Some a2 →
      incrementPC (<[ dst := WCap (t && isWithin a1 a2 b e) p g a1 a2 a ]ᵣ> regs) = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC_unrepresentable_cap (t : bool) p g b e a n1 n2 :
      regs !!ᵣ dst = Some (WCap t p g b e a) →
      z_of_argument regs src1 = Some n1 →
      z_of_argument regs src2 = Some n2 →
      (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
      incrementPC (<[ dst := WCap false p g b e a ]ᵣ> regs) = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC_sr (t : bool) p g b e a n1 n2 a1 a2 :
      regs !!ᵣ dst = Some (WSealRange t p g b e a) →
      z_of_argument regs src1 = Some n1 →
      z_of_argument regs src2 = Some n2 →
      z_to_otype n1 = Some a1 →
      z_to_otype n2 = Some a2 →
      incrementPC (<[ dst := WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a ]ᵣ> regs) = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC_unrepresentable_sr (t : bool) p g b e a n1 n2 :
      regs !!ᵣ dst = Some (WSealRange t p g b e a) →
      z_of_argument regs src1 = Some n1 →
      z_of_argument regs src2 = Some n2 →
      (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
      incrementPC (<[ dst := WSealRange false p g b e a ]ᵣ> regs) = None →
      Subseg_failure regs dst src1 src2 regs.

  (* Both operands must be integers. If either endpoint cannot be represented,
     the instruction clears the tag and preserves both original endpoints. *)
  Inductive Subseg_spec (regs : Reg) (dst : RegName)
      (src1 src2 : Z + RegName) (regs' : Reg) : griotte_lang.val → Prop :=
  | Subseg_spec_success_cap (t : bool) p g b e a n1 n2 a1 a2 :
      regs !!ᵣ dst = Some (WCap t p g b e a) →
      z_of_argument regs src1 = Some n1 →
      z_of_argument regs src2 = Some n2 →
      z_to_addr n1 = Some a1 →
      z_to_addr n2 = Some a2 →
      incrementPC (<[ dst := WCap (t && isWithin a1 a2 b e) p g a1 a2 a ]ᵣ> regs) = Some regs' →
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_unrepresentable_cap (t : bool) p g b e a n1 n2 :
      regs !!ᵣ dst = Some (WCap t p g b e a) →
      z_of_argument regs src1 = Some n1 →
      z_of_argument regs src2 = Some n2 →
      (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
      incrementPC (<[ dst := WCap false p g b e a ]ᵣ> regs) = Some regs' →
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_success_sr (t : bool) p g b e a n1 n2 a1 a2 :
      regs !!ᵣ dst = Some (WSealRange t p g b e a) →
      z_of_argument regs src1 = Some n1 →
      z_of_argument regs src2 = Some n2 →
      z_to_otype n1 = Some a1 →
      z_to_otype n2 = Some a2 →
      incrementPC (<[ dst := WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a ]ᵣ> regs) = Some regs' →
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_unrepresentable_sr (t : bool) p g b e a n1 n2 :
      regs !!ᵣ dst = Some (WSealRange t p g b e a) →
      z_of_argument regs src1 = Some n1 →
      z_of_argument regs src2 = Some n2 →
      (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
      incrementPC (<[ dst := WSealRange false p g b e a ]ᵣ> regs) = Some regs' →
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_failure :
      Subseg_failure regs dst src1 src2 regs' →
      Subseg_spec regs dst src1 src2 regs' FailedV.

  Lemma wp_Subseg Ep pc_p pc_g pc_b pc_e pc_a w dst src1 src2 regs :
    decodeInstrW w = Subseg dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [ [Hr Hsr] Hm] Hst] /=". destruct σ1 as [ [ [r sr] m] st]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [H'dst Hdst]]; first by set_solver+.

    rewrite /exec /= Hdst /= in Hstep.

    destruct (is_mutable_range wdst) eqn:Hwdst.
     2: { (* Failure: wdst is not of the right type *)
       unfold is_mutable_range in Hwdst.
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       { destruct wdst as [ | [t p b e a | ] | | ]; try by inversion Hwdst.
         all: try by simplify_pair_eq.
         all: repeat destruct (addr_of_argument r _); cbn in *; simplify_pair_eq; auto. }
       iFailWP "Hφ" Subseg_fail_allowed. }

    (* Both supported forms read the integer operands before conversion. *)
    assert (Hz1 : z_of_argument regs src1 = z_of_argument r src1).
    { destruct src1 as [n | rn]; first done.
      destruct (Hri rn) as [wv [Hwv Hwv']]; first (unfold regs_of_argument; set_solver+).
      by rewrite /z_of_argument Hwv Hwv'. }
    assert (Hz2 : z_of_argument regs src2 = z_of_argument r src2).
    { destruct src2 as [n | rn]; first done.
      destruct (Hri rn) as [wv [Hwv Hwv']]; first (unfold regs_of_argument; set_solver+).
      by rewrite /z_of_argument Hwv Hwv'. }
    destruct (z_of_argument regs src1) as [n1 |] eqn:Hn1.
    2: { assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
         { destruct_word wdst; cbn in Hwdst; try discriminate;
           rewrite -Hz1 /= in Hstep; by simplify_pair_eq. }
         iFailWP "Hφ" Subseg_fail_src1_nonz. }
    destruct (z_of_argument regs src2) as [n2 |] eqn:Hn2.
    2: { assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
         { destruct_word wdst; cbn in Hwdst; try discriminate;
           rewrite -Hz1 -Hz2 /= in Hstep; by simplify_pair_eq. }
         iFailWP "Hφ" Subseg_fail_src2_nonz. }

    assert (∃ w',
        (∀ regs', incrementPC (<[dst := w']ᵣ> regs) = Some regs' →
          Subseg_spec regs dst src1 src2 regs' NextIV) ∧
        (incrementPC (<[dst := w']ᵣ> regs) = None →
          Subseg_failure regs dst src1 src2 regs) ∧
        (match updatePC (update_reg (r, sr, m, st) dst w') with
         | Some conf => conf | None => (Failed, (r, sr, m, st)) end) = (c, σ2)) as (w' & Hsuccess & Hfailure & Hupdate).
    { destruct wdst as [ | [t p g b e a | t p g b e a] | | ];
        try discriminate Hwdst.
      - rewrite -Hz1 -Hz2 /= in Hstep.
        destruct (z_to_addr n1) as [a1 |] eqn:Ha1;
          destruct (z_to_addr n2) as [a2 |] eqn:Ha2;
          eexists; (split; [|split; [|exact Hstep]]); intros.
        all: first [solve [eapply Subseg_spec_success_cap; eauto]
                    | solve [eapply Subseg_spec_unrepresentable_cap; eauto]
                    | solve [eapply Subseg_fail_incrPC_cap; eauto]
                    | solve [eapply Subseg_fail_incrPC_unrepresentable_cap; eauto]].
      - rewrite -Hz1 -Hz2 /= in Hstep.
        destruct (z_to_otype n1) as [a1 |] eqn:Ha1;
          destruct (z_to_otype n2) as [a2 |] eqn:Ha2;
          eexists; (split; [|split; [|exact Hstep]]); intros.
        all: first [solve [eapply Subseg_spec_success_sr; eauto]
                    | solve [eapply Subseg_spec_unrepresentable_sr; eauto]
                    | solve [eapply Subseg_fail_incrPC_sr; eauto]
                    | solve [eapply Subseg_fail_incrPC_unrepresentable_sr; eauto]]. }
    clear Hstep. rename Hupdate into Hstep.
    rewrite /update_reg /= in Hstep.
    destruct (incrementPC (<[ dst := w' ]ᵣ> regs)) as [regs' |] eqn:Hregs'.
    2: { assert (incrementPC (<[ dst := w' ]ᵣ> r) = None) as HH.
         { eapply incrementPC_overflow_mono; first exact Hregs'.
           - by rewrite lookup_insert_is_Some'; eauto.
           - by apply insert_mono. }
         apply (incrementPC_fail_updatePC _ sr m st) in HH.
         rewrite HH in Hstep. inversion Hstep; subst c σ2.
         iFailWP "Hφ" Hfailure. }
    eapply (incrementPC_success_updatePC _ sr m st) in Hregs'
      as (t' & p' & g' & b' & e' & a' & a_pc' & HPC' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl in HuPC; last by eapply insert_mono.
    rewrite HuPC in Hstep. inversion Hstep; subst c σ2. cbn.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ dst) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame.
    iPureIntro. apply Hsuccess. reflexivity.
    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success E pc_p pc_g pc_b pc_e pc_a w dst r1 r2 (t : bool) p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ WInt n1
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WCap t p g a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' Hcnull Hcnull' Hcnull'' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_same E pc_p pc_g pc_b pc_e pc_a w dst r1 (t : bool) p g b e a n1 a1 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ dst ↦ᵣ WCap t p g a1 a1 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_l E pc_p pc_g pc_b pc_e pc_a w dst r2 (t : bool) p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WCap t p g a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_r E pc_p pc_g pc_b pc_e pc_a w dst r1 (t : bool) p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ dst ↦ᵣ WCap t p g a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_lr E pc_p pc_g pc_b pc_e pc_a w dst (t : bool) p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WCap t p g a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc E pc_p pc_g pc_b pc_e pc_a w r1 r2 n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg PC (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WInt n1
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a2 pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ r2 ↦ᵣ WInt n2
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite !insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_same E pc_p pc_g pc_b pc_e pc_a w r1 n1 a1 pc_a' :
    decodeInstrW w = Subseg PC (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a1 pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hwb Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_l E pc_p pc_g pc_b pc_e pc_a w r2 n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg PC (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a2 pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ WInt n2
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC r2) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_r E pc_p pc_g pc_b pc_e pc_a w r1 n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg PC (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a2 pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_lr E pc_p pc_g pc_b pc_e pc_a w n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg PC (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a2 pc_a'
          ∗ pc_a ↦ₐ w
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ϕ) "(>HPC & >Hpc_a) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold addr_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite !insert_insert_eq.
    iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

  Lemma wp_subseg_success_sr E pc_p pc_g pc_b pc_e pc_a w dst r1 r2 (t : bool) p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ WInt n1
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ??? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold otype_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_same_sr E pc_p pc_g pc_b pc_e pc_a w dst r1 (t : bool) p g b e a n1 a1 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ dst ↦ᵣ WSealRange t p g a1 a1 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold otype_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_l_sr E pc_p pc_g pc_b pc_e pc_a w dst r2 (t : bool) p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r2 ↦ᵣ WInt n2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ WInt n2
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold otype_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_r_sr E pc_p pc_g pc_b pc_e pc_a w dst r1 (t : bool) p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ WInt n1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold otype_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_lr_sr E pc_p pc_g pc_b pc_e pc_a w dst (t : bool) p g b e a n1 n2 a1 a2 pc_a' :
    decodeInstrW w = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold z_of_argument in *; simplify_map_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_map_eq; eauto. congruence. }
    all: unfold z_of_argument in *; simplify_map_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
    unfold otype_of_argument, z_of_argument in *. simplify_map_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (* Internal proof lemmas over maps. Public outcome rules below expose
     each required register explicitly. *)
  Local Lemma subseg_invalidated_map_cap E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 a1 a2 :
    decodeInstrW w = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ᵣ dst = Some (WCap t p g b e a) →
    z_of_argument regs src1 = Some n1 →
    z_of_argument regs src2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = false →
    incrementPC (<[ dst := WCap false p g a1 a2 a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hn1 Hn2 Hwithin Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: repeat match goal with
    | H : context [_ && isWithin _ _ _ _] |- _ =>
      rewrite Hwithin andb_false_r in H
    end.
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  Local Lemma subseg_unrepresentable_map_cap E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 :
    decodeInstrW w = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ᵣ dst = Some (WCap t p g b e a) →
    z_of_argument regs src1 = Some n1 →
    z_of_argument regs src2 = Some n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    incrementPC (<[ dst := WCap false p g b e a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hover Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try (destruct Hover; congruence).
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  Local Lemma subseg_invalidated_map_sr E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 a1 a2 :
    decodeInstrW w = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ᵣ dst = Some (WSealRange t p g b e a) →
    z_of_argument regs src1 = Some n1 →
    z_of_argument regs src2 = Some n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    incrementPC (<[ dst := WSealRange false p g a1 a2 a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hn1 Hn2 Hwithin Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: repeat match goal with
    | H : context [_ && isWithin _ _ _ _] |- _ =>
      rewrite Hwithin andb_false_r in H
    end.
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  Local Lemma subseg_unrepresentable_map_sr E pc_p pc_g pc_b pc_e pc_a
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 :
    decodeInstrW w = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ᵣ dst = Some (WSealRange t p g b e a) →
    z_of_argument regs src1 = Some n1 →
    z_of_argument regs src2 = Some n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    incrementPC (<[ dst := WSealRange false p g b e a ]ᵣ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hover Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try (destruct Hover; congruence).
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  (* Subseg: operand layouts follow the ordinary success rules. *)
  Lemma wp_subseg_invalidated_lr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2 a1 a2 :
    decodeInstrW w = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WCap false p g a1 a2 a]> (∅ : Reg))) t p g b e a n1 n2 a1 a2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_lr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2 :
    decodeInstrW w = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WCap false p g b e a]> (∅ : Reg))) t p g b e a n1 n2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_l E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2 r2
      (w2 : Word) a1 a2 :
    decodeInstrW w = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WCap false p g a1 a2 a]> (<[r2 := w2]> (∅ : Reg)))) t p g b e a n1 n2 a1
        a2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable_l E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1
      n2 r2 (w2 : Word) :
    decodeInstrW w = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WCap false p g b e a]> (<[r2 := w2]> (∅ : Reg)))) t p g b e a n1 n2
        with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated_r E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2 r1
      (w1 : Word) a1 a2 :
    decodeInstrW w = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WCap false p g a1 a2 a]> (<[r1 := w1]> (∅ : Reg)))) t p g b e a n1 n2 a1
        a2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable_r E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1
      n2 r1 (w1 : Word) :
    decodeInstrW w = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WCap false p g b e a]> (<[r1 := w1]> (∅ : Reg)))) t p g b e a n1 n2
        with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2 r1
      (w1 : Word) r2 (w2 : Word) a1 a2 :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WCap false p g a1 a2 a]> (<[r1 := w1]> (<[r2 := w2]> (∅ : Reg))))) t p g b
        e a n1 n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : Word) r2 (w2 : Word) :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WCap false p g b e a]> (<[r1 := w1]> (<[r2 := w2]> (∅ : Reg))))) t p
        g b e a n1 n2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 r1
      (w1 : Word) a1 :
    decodeInstrW w = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a1 a
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WCap false p g a1 a1 a]> (<[r1 := w1]> (∅ : Reg)))) t p g b e a n1 n1 a1
        a1 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable_same E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a
      n1 r1 (w1 : Word) :
    decodeInstrW w = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n1 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WCap false p g b e a]> (<[r1 := w1]> (∅ : Reg)))) t p g b e a n1 n1
        with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated_lr_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2 a1 a2 :
    decodeInstrW w = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WSealRange false p g a1 a2 a]> (∅ : Reg))) t p g b e a n1 n2 a1 a2 with
        "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_lr_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2 :
    decodeInstrW w = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WSealRange false p g b e a]> (∅ : Reg))) t p g b e a n1 n2 with
        "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_l_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2
      r2 (w2 : Word) a1 a2 :
    decodeInstrW w = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WSealRange false p g a1 a2 a]> (<[r2 := w2]> (∅ : Reg)))) t p g b e a n1
        n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable_l_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a
      n1 n2 r2 (w2 : Word) :
    decodeInstrW w = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WSealRange false p g b e a]> (<[r2 := w2]> (∅ : Reg)))) t p g b e a
        n1 n2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated_r_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : Word) a1 a2 :
    decodeInstrW w = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WSealRange false p g a1 a2 a]> (<[r1 := w1]> (∅ : Reg)))) t p g b e a n1
        n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable_r_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a
      n1 n2 r1 (w1 : Word) :
    decodeInstrW w = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WSealRange false p g b e a]> (<[r1 := w1]> (∅ : Reg)))) t p g b e a
        n1 n2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : Word) r2 (w2 : Word) a1 a2 :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WSealRange false p g a1 a2 a]> (<[r1 := w1]> (<[r2 := w2]> (∅ : Reg))))) t
        p g b e a n1 n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1
      n2 r1 (w1 : Word) r2 (w2 : Word) :
    decodeInstrW w = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WSealRange false p g b e a]> (<[r1 := w1]> (<[r2 := w2]> (∅ :
        Reg))))) t p g b e a n1 n2 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated_same_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e a n1
      r1 (w1 : Word) a1 :
    decodeInstrW w = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    z_to_otype n1 = Some a1 →
    isWithin a1 a1 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a1 a
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e
        pc_a']> (<[dst := WSealRange false p g a1 a1 a]> (<[r1 := w1]> (∅ : Reg)))) t p g b e a n1
        n1 a1 a1 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable_same_sr E pc_p pc_g pc_b pc_e pc_a pc_a' w dst (t : bool) p g b e
      a n1 r1 (w1 : Word) :
    decodeInstrW w = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (z_to_otype n1 = None ∨ z_to_otype n1 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b
        pc_e pc_a']> (<[dst := WSealRange false p g b e a]> (<[r1 := w1]> (∅ : Reg)))) t p g b e a
        n1 n1 with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated_pc_lr E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 n2 a1 a2 :
    decodeInstrW w = Subseg PC (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a2 pc_a'
        ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a2
        pc_a']> (∅ : Reg)) true pc_p pc_g pc_b pc_e pc_a n1 n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_1 with "Hmap").
  Qed.

  Lemma wp_subseg_unrepresentable_pc_lr E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 n2 :
    decodeInstrW w = Subseg PC (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hover φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b
        pc_e pc_a']> (∅ : Reg)) true pc_p pc_g pc_b pc_e pc_a n1 n2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_1 with "Hmap").
  Qed.

  Lemma wp_subseg_invalidated_pc_l E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 n2 r2 (w2 : Word) a1 a2 :
    decodeInstrW w = Subseg PC (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a2 pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a2
        pc_a']> (<[r2 := w2]> (∅ : Reg))) true pc_p pc_g pc_b pc_e pc_a n1 n2 a1 a2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_pc_l E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 n2 r2 (w2 : Word) :
    decodeInstrW w = Subseg PC (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread2 Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b
        pc_e pc_a']> (<[r2 := w2]> (∅ : Reg))) true pc_p pc_g pc_b pc_e pc_a n1 n2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_pc_r E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 n2 r1 (w1 : Word) a1 a2 :
    decodeInstrW w = Subseg PC (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a2 pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a2
        pc_a']> (<[r1 := w1]> (∅ : Reg))) true pc_p pc_g pc_b pc_e pc_a n1 n2 a1 a2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_pc_r E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 n2 r1 (w1 : Word) :
    decodeInstrW w = Subseg PC (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b
        pc_e pc_a']> (<[r1 := w1]> (∅ : Reg))) true pc_p pc_g pc_b pc_e pc_a n1 n2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_pc E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 n2 r1 (w1 : Word) r2 (w2 :
      Word) a1 a2 :
    decodeInstrW w = Subseg PC (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a2 pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a2
        pc_a']> (<[r1 := w1]> (<[r2 := w2]> (∅ : Reg)))) true pc_p pc_g pc_b pc_e pc_a n1 n2 a1 a2
        with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_unrepresentable_pc E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 n2 r1 (w1 : Word) r2 (w2 : Word) :
    decodeInstrW w = Subseg PC (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b
        pc_e pc_a']> (<[r1 := w1]> (<[r2 := w2]> (∅ : Reg)))) true pc_p pc_g pc_b pc_e pc_a n1 n2
        with "[$Hmem $Hmap]"); eauto;
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

  Lemma wp_subseg_invalidated_pc_same E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 r1 (w1 : Word) a1 :
    decodeInstrW w = Subseg PC (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 pc_b pc_e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a1 pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hconvert1 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a1
        pc_a']> (<[r1 := w1]> (∅ : Reg))) true pc_p pc_g pc_b pc_e pc_a n1 n1 a1 a1 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_pc_same E pc_p pc_g pc_b pc_e pc_a pc_a' w n1 r1 (w1 : Word) :
    decodeInstrW w = Subseg PC (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n1 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a'
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b
        pc_e pc_a']> (<[r1 := w1]> (∅ : Reg))) true pc_p pc_g pc_b pc_e pc_a n1 n1 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /z_of_argument /lookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /insert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.
End instruction_outcomes.
