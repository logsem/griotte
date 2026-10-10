From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.

(* Discharges the pure premise of the generic rule for the variants. *)
Ltac solve_subseg_root_free :=
  let Hd := fresh "Hd" in let Ha1 := fresh "Ha1" in let Ha2 := fresh "Ha2" in
  let Ht := fresh "Ht" in let Hlt := fresh "Hlt" in
  intros ? ? ? ? ? ? ? ? Hd Ha1 Ha2 Ht Hlt;
  rewrite /laddr_of_argument /lz_of_argument ?/llookup_reg in Ha1, Ha2, Hd;
  simplify_map_eq;
  first [ done | solve_addr | congruence
        | match goal with H : None = None → _ |- _ => by apply H end ].

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  Inductive Subseg_failure  (regs : LReg) (dst: RegName) (src1 src2: Z + RegName) : LReg → Prop :=
  | Subseg_fail_allowed w :
      regs !!ₗ dst = Some w →
      is_mutable_range w.(lw) = false →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_src1_nonz :
      lz_of_argument regs src1 = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_src2_nonz :
      lz_of_argument regs src2 = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC_cap (t : bool) p g b e a π n1 n2 a1 a2 :
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      z_to_addr n1 = Some a1 →
      z_to_addr n2 = Some a2 →
      incrementPC (<[ dst := WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π ]ₗ> regs) = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC_unrepresentable_cap (t : bool) p g b e a π n1 n2 :
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
      incrementPC (<[ dst := WCap false p g b e a @@? π ]ₗ> regs) = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC_sr (t : bool) p g b e a π n1 n2 a1 a2 :
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      z_to_otype n1 = Some a1 →
      z_to_otype n2 = Some a2 →
      incrementPC (<[ dst := WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a @@? π ]ₗ> regs) = None →
      Subseg_failure regs dst src1 src2 regs
  | Subseg_fail_incrPC_unrepresentable_sr (t : bool) p g b e a π n1 n2 :
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
      incrementPC (<[ dst := WSealRange false p g b e a @@? π ]ₗ> regs) = None →
      Subseg_failure regs dst src1 src2 regs.

  (* Both operands must be integers. If either endpoint cannot be represented,
     the instruction clears the tag and preserves both original endpoints.
     The result keeps the identifier of the source. *)
  Inductive Subseg_spec (regs : LReg) (dst : RegName)
      (src1 src2 : Z + RegName) (regs' : LReg) : griotte_lang.val → Prop :=
  | Subseg_spec_success_cap (t : bool) p g b e a π n1 n2 a1 a2 :
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      z_to_addr n1 = Some a1 →
      z_to_addr n2 = Some a2 →
      incrementPC (<[ dst := WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π ]ₗ> regs) = Some regs' →
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_unrepresentable_cap (t : bool) p g b e a π n1 n2 :
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
      incrementPC (<[ dst := WCap false p g b e a @@? π ]ₗ> regs) = Some regs' →
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_success_sr (t : bool) p g b e a π n1 n2 a1 a2 :
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      z_to_otype n1 = Some a1 →
      z_to_otype n2 = Some a2 →
      incrementPC (<[ dst := WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a @@? π ]ₗ> regs) = Some regs' →
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_unrepresentable_sr (t : bool) p g b e a π n1 n2 :
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
      incrementPC (<[ dst := WSealRange false p g b e a @@? π ]ₗ> regs) = Some regs' →
      Subseg_spec regs dst src1 src2 regs' NextIV
  | Subseg_spec_failure :
      Subseg_failure regs dst src1 src2 regs' →
      Subseg_spec regs dst src1 src2 regs' FailedV.

  (** The premise of the generic rule (§4.4). An identifier-less source that
      would give a tagged, non-empty heap result needs its new base to be a
      heap root. Otherwise (the source has an identifier, or the result is
      untagged, empty or not in the heap) nothing is needed: this is the pure
      branch, the one the FTLR and the switcher use. *)
  Definition subseg_root_free (regs : LReg) dst src1 src2 : Prop :=
    ∀ t p g b e a a1 a2,
      regs !!ₗ dst = Some (WCap t p g b e a @@? None) →
      laddr_of_argument regs src1 = Some a1 →
      laddr_of_argument regs src2 = Some a2 →
      (t && isWithin a1 a2 b e && (a1 <=? a2)%a) = true →
      (a1 < a2)%a →
      is_heap_address a1 = false.

  (** [oa = None] is the pure branch; [oa = Some a1] gives the heap root. *)
  Definition subseg_root_ok (regs : LReg) dst src1 src2 (oa : option Addr) : iProp Σ :=
    match oa with
    | None => ⌜subseg_root_free regs dst src1 src2⌝
    | Some a1 => ⌜laddr_of_argument regs src1 = Some a1⌝ ∗ addr_alloc a1 HeapRoot
    end.

  Lemma wp_Subseg Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs oa :
    decodeInstrW w.(lw) = Subseg dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ subseg_root_ok regs dst src1 src2 oa ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        subseg_root_ok regs dst src1 src2 oa ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hroot & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [Hdst _]]; first by set_solver+.
    assert (r !!ᵣ dst = Some wdst.(lw)) as Hdst'.
    { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase Hdst. }
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ Her Hlregs Hdst) as Hokdst.
    pose proof (lz_of_argument_phys regs r src1 Hregs ltac:(intros ? ->; set_solver)) as Hz1.
    pose proof (lz_of_argument_phys regs r src2 Hregs ltac:(intros ? ->; set_solver)) as Hz2.
    (* The heap-root fact for the new base, when needed. *)
    iAssert (⌜∀ a1, laddr_of_argument regs src1 = Some a1 →
               ¬ subseg_root_free regs dst src1 src2 → C !! a1 = Some HeapRoot⌝)%I
      as %Hrootc.
    { destruct oa as [a1'|]; cbn.
      - iDestruct "Hroot" as "(%Ha1' & Ha1)".
        iDestruct (addr_alloc_lookup with "HC Ha1") as %HCa1.
        iPureIntro. intros a1 Ha1 _. rewrite Ha1 in Ha1'. by simplify_eq.
      - iDestruct "Hroot" as %Hfree.
        iPureIntro. intros ? ? Hn. by exfalso. }
    iAssert (∀ regs' retv, ⌜Subseg_spec regs dst src1 src2 regs' retv⌝ -∗
               ([∗ map] k↦y ∈ regs', k ↦ᵣ y) -∗ φ retv)%I
      with "[Hφ Hpc_a Hroot]" as "Hφ".
    { iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame. }
    destruct wdst as [wd π].
    destruct (is_mutable_range wd) eqn:Hwdst.
    2: { (* Failure: wdst is not of the right type *)
      assert (c = Failed ∧ σ' = (r, sr, m, st)) as (-> & ->).
      { cbn in Hdst', Hstep. rewrite Hdst' /= in Hstep.
        destruct wd as [ | [t p b e a | ] | | ]; try by inversion Hwdst.
        all: cbn in Hstep; by simplify_pair_eq. }
      iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
      iIntros "Hmap". iApply ("Hφ" with "[%] Hmap").
      constructor. by eapply (Subseg_fail_allowed _ _ _ _ (wd @@? π)). }
    cbn in Hdst', Hstep. rewrite Hdst' /= in Hstep.
    destruct (lz_of_argument regs src1) as [n1 |] eqn:Hn1.
    2: { assert (c = Failed ∧ σ' = (r, sr, m, st)) as (-> & ->).
         { destruct_word wd; cbn in Hwdst; try discriminate;
           rewrite Hz1 /= in Hstep; by simplify_pair_eq. }
         iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
         iIntros "Hmap". iApply ("Hφ" with "[%] Hmap").
         constructor. by apply Subseg_fail_src1_nonz. }
    destruct (lz_of_argument regs src2) as [n2 |] eqn:Hn2.
    2: { assert (c = Failed ∧ σ' = (r, sr, m, st)) as (-> & ->).
         { destruct_word wd; cbn in Hwdst; try discriminate;
           rewrite Hz1 Hz2 /= in Hstep; by simplify_pair_eq. }
         iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
         iIntros "Hmap". iApply ("Hφ" with "[%] Hmap").
         constructor. by apply Subseg_fail_src2_nonz. }
    assert (∃ w',
        reg_word_ok R C w' ∧
        (∀ regs', incrementPC (<[dst := w']ₗ> regs) = Some regs' →
          Subseg_spec regs dst src1 src2 regs' NextIV) ∧
        (incrementPC (<[dst := w']ₗ> regs) = None →
          Subseg_spec regs dst src1 src2 regs FailedV) ∧
        (match updatePC (update_reg (r, sr, m, st) dst w'.(lw)) with
         | Some conf => conf | None => (Failed, (r, sr, m, st)) end) = (c, σ'))
      as (w' & Hok' & Hsuccess & Hfailure & Hupdate).
    { destruct wd as [ | [t p g b e a | t p g b e a] | | ];
        try discriminate Hwdst.
      - rewrite Hz1 Hz2 /= in Hstep.
        destruct (z_to_addr n1) as [a1 |] eqn:Ha1;
          destruct (z_to_addr n2) as [a2 |] eqn:Ha2.
        1: exists (WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π).
        2-4: exists (WCap false p g b e a @@? π).
        all: split_and!; [ | intros | intros | exact Hstep ].
        all: try solve [eapply Subseg_spec_success_cap; eauto
                       | eapply Subseg_spec_unrepresentable_cap; eauto
                       | constructor; eapply Subseg_fail_incrPC_cap; eauto
                       | constructor; eapply Subseg_fail_incrPC_unrepresentable_cap; eauto].
        2-4: by apply reg_word_ok_untagged.
        eapply reg_word_ok_subseg; [apply Her | exact Hokdst | |].
        + intros Ht. apply andb_prop in Ht as [Ht Hle]. apply andb_prop in Ht as [-> Hw].
          apply isWithin_implies in Hw. split; first done. solve_addr.
        + intros Ht Hlt Hheap ->. apply Hrootc.
          * by rewrite /laddr_of_argument Hn1.
          * intros Hfree. specialize (Hfree t p g b e a a1 a2 Hdst).
            rewrite /laddr_of_argument Hn1 Hn2 in Hfree. rewrite Hfree in Hheap; done.
      - rewrite Hz1 Hz2 /= in Hstep.
        destruct (z_to_otype n1) as [a1 |] eqn:Ha1;
          destruct (z_to_otype n2) as [a2 |] eqn:Ha2.
        1: exists (WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a @@? π).
        2-4: exists (WSealRange false p g b e a @@? π).
        all: split_and!; [ | intros | intros | exact Hstep ].
        all: try solve [eapply Subseg_spec_success_sr; eauto
                       | eapply Subseg_spec_unrepresentable_sr; eauto
                       | constructor; eapply Subseg_fail_incrPC_sr; eauto
                       | constructor; eapply Subseg_fail_incrPC_unrepresentable_sr; eauto].
        all: apply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π));
          [by right | cbn; intros; by destruct t | exact Hokdst]. }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst w' _ _ _
      (λ regs' retv, Subseg_spec regs dst src1 src2 regs' retv)
      with "Hr Hsr Hm Hst HR HC Hmap Hφ").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
    { exact Hok'. } { exact Hupdate. } { exact Hsuccess. } { exact Hfailure. }
  Qed.

  (** The generic rule on its pure branch. *)
  Lemma wp_Subseg_pure Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs :
    decodeInstrW w.(lw) = Subseg dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    subseg_root_free regs dst src1 src2 →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Subseg_spec regs dst src1 src2 regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hfree φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_Subseg _ _ _ _ _ _ _ _ _ _ _ _ None with "[$Hpc_a $Hmap]"); eauto.
    iNext. iIntros (regs' retv) "(Hspec & Hpc_a & _ & Hmap)". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 (t : bool) p g b e a w1 n1 w2 n2 a1 a2 pc_a' π :
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    (π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' Hcnull Hcnull' Hcnull'' ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_same E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 (t : bool) p g b e a w1 n1 a1 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WCap t p g a1 a1 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    assert (Hle' : (a1 <=? a1)%a = true) by solve_addr.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_l E pc_p pc_g pc_b pc_e pc_a pc_π w dst r2 (t : bool) p g b e a n1 w2 n2 a1 a2 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    (π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw2 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_r E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 (t : bool) p g b e a w1 n1 n2 a1 a2 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    (π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_lr E pc_p pc_g pc_b pc_e pc_a pc_π w dst (t : bool) p g b e a n1 n2 a1 a2 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    (π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc E pc_p pc_g pc_b pc_e pc_a pc_π w r1 r2 w1 n1 w2 n2 a1 a2 pc_a' :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = true →
    (a1 <= a2)%a →
    (pc_π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a2 pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite !insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_same E pc_p pc_g pc_b pc_e pc_a pc_π w r1 w1 n1 a1 pc_a' :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inr r1) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 pc_b pc_e = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a1 pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hwb Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    assert (Hle' : (a1 <=? a1)%a = true) by solve_addr.
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_l E pc_p pc_g pc_b pc_e pc_a pc_π w r2 n1 w2 n2 a1 a2 pc_a' :
    decodeInstrW w.(lw) = Subseg PC (inl n1) (inr r2) →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = true →
    (a1 <= a2)%a →
    (pc_π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a2 pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ w2
      }}}.
  Proof.
    iIntros (Hinstr Hw2 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC r2) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_r E pc_p pc_g pc_b pc_e pc_a pc_π w r1 w1 n1 n2 a1 a2 pc_a' :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inl n2) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = true →
    (a1 <= a2)%a →
    (pc_π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a2 pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_pc_lr E pc_p pc_g pc_b pc_e pc_a pc_π w n1 n2 a1 a2 pc_a' :
    decodeInstrW w.(lw) = Subseg PC (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e = true →
    (a1 <= a2)%a →
    (pc_π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g a1 a2 pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ϕ) "(>HPC & >Hpc_a) Hφ".
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold laddr_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite !insert_insert_eq.
    iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

  Lemma wp_subseg_success_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 (t : bool) p g b e a w1 n1 w2 n2 a1 a2 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hpc_a' ??? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold lotype_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_same_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 (t : bool) p g b e a w1 n1 a1 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WSealRange t p g a1 a1 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold lotype_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_l_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst r2 (t : bool) p g b e a n1 w2 n2 a1 a2 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw2 Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_3 with "HPC Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold lotype_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_r_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 (t : bool) p g b e a w1 n1 n2 a1 a2 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold lotype_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
            (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  Lemma wp_subseg_success_lr_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst (t : bool) p g b e a n1 n2 a1 a2 pc_a'  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ? ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iApply (wp_Subseg_pure with "[$Hmap Hpc_a]"); eauto; try solve_subseg_root_free; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    unfold lotype_of_argument, lz_of_argument in *. simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq insert_insert_ne // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame.

    Unshelve. all: auto.
  Qed.

  (** * Allocator-only rules *)

  (** Case 3: an identifier-less source narrowed to a tagged, non-empty heap
      result. The new base must be a heap root. *)
  Lemma wp_subseg_success_root E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 (t : bool) p g b e a w1 n1 w2 n2 a1 a2 pc_a' :
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? None
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2
        ∗ ▷ addr_alloc a1 HeapRoot }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? None
          ∗ addr_alloc a1 HeapRoot
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hpc_a' Hcnull Hcnull' Hcnull'' ϕ)
      "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2 & >Hroot) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    iApply (wp_Subseg _ _ _ _ _ _ _ _ _ _ _ _ (Some a1) with "[$Hmap $Hpc_a Hroot]");
      eauto; simplify_lmap_eq; eauto.
    { by unfold regs_of; rewrite !dom_insert; set_solver+. }
    { iFrame. iPureIntro. rewrite /laddr_of_argument /lz_of_argument.
      simplify_lmap_eq. done. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & [_ Hroot] & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      incrementPC_inv; simplify_lmap_eq; eauto. congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite Hwb Hle' ?andb_true_r in Hincr.
    iApply "Hφ". iFrame. incrementPC_inv; simplify_lmap_eq.
    rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
            (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
    iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame.
  Qed.

  (** Case 4, the rebase: an identifier-less source narrowed to exactly the
      range of a non-dead identifier [ι] takes [ι]. The allocate step
      ([rules_registry]) gives [alloc_obj] and the status token. *)
  Lemma wp_subseg_rebase E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 p g b e a w1 n1 w2 n2 a1 a2 pc_a'
      ι q s :
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    s ≠ ADead →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? None
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2
        ∗ alloc_obj ι a1 a2
        ∗ ι ↦st{q} s }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ (WCap true p g a1 a2 a) @@ ι
          ∗ alloc_obj ι a1 a2
          ∗ ι ↦st{q} s
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hs Hpc_a' Hcnull Hcnull' Hcnull'' ϕ)
      "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2 & #Hobj & Htok) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hdst") as "[Hmap (%&%&%&%&%&%)]".
    set (regs := <[PC:=WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π]>
                   (<[r1:=WInt n1 @@? π1]>
                      (<[r2:=WInt n2 @@? π2]>
                         (<[dst:=WCap true p g b e a @@? None]> ∅)))).
    set (v := WCap true p g a1 a2 a @@ ι).
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    { by rewrite /regs lookup_insert_eq. }
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    iDestruct (reg_lookup_obj with "HR Hobj") as %(γ & s' & HRι).
    iDestruct (reg_lookup_own with "HR Htok") as %(b' & e' & γ' & HRι').
    rewrite HRι in HRι'. simplify_eq.
    assert (r !! dst = Some (WCap true p g b e a)) as Hdst'.
    { eapply lookup_weaken; last exact Hregs.
      rewrite lookup_lregs_erase /regs. by simplify_map_eq. }
    assert (r !! r1 = Some (WInt n1)) as Hr1'.
    { eapply lookup_weaken; last exact Hregs.
      rewrite lookup_lregs_erase /regs. by simplify_map_eq. }
    assert (r !! r2 = Some (WInt n2)) as Hr2'.
    { eapply lookup_weaken; last exact Hregs.
      rewrite lookup_lregs_erase /regs. by simplify_map_eq. }
    assert (exec_opt (Subseg dst (inr r1) (inr r2)) pc_p (r, sr, m, st) =
              updatePC (update_reg (r, sr, m, st) dst v.(lw))) as HH.
    { rewrite /exec_opt /= /lookup_reg Hdst' Hr1' Hr2' /=.
      rewrite !decide_False //= Hn1 Hn2 Hwb Hle' /=. done. }
    rewrite Hinstr /exec HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst v _ _ _
      (λ regs' retv, (retv = NextIV ∧ incrementPC (<[dst := v]ₗ> regs) = Some regs') ∨
                     (retv = FailedV ∧ incrementPC (<[dst := v]ₗ> regs) = None))
      with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a Htok]").
    { exact Her. } { exact Hlregs. } { rewrite /regs. set_solver+. }
    { by rewrite /regs lookup_insert_eq. }
    { by eapply reg_word_ok_rebase. } { exact Hstep. }
    { intros. by left. } { intros. by right. }
    iIntros (regs' retv [[-> Hincr] | [-> Hincr]]) "Hmap"; subst regs v.
    - iApply "Hφ". iFrame "∗#". incrementPC_inv.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r2 dst) //
              (insert_insert_ne _ r1 dst) // (insert_insert_ne _ PC dst) // insert_insert_eq.
      iDestruct (regs_of_map_4 with "Hmap") as "(?&?&?&?)"; eauto; iFrame.
    - exfalso. incrementPC_inv; simplify_lmap_eq; eauto. congruence.
  Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (* Internal proof lemmas over maps. Public outcome rules below expose
     each required register explicitly. *)
  Local Lemma subseg_invalidated_map_cap E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 →
    lz_of_argument regs src2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    incrementPC (<[ dst := WCap false p g a1 a2 a @@? π ]ₗ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hn1 Hn2 Hwithin Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$Hpc_a $Hmap]"); eauto.
    { intros ? ? ? ? ? ? ? ? Hd Ha1 Ha2 Ht Hlt.
      rewrite Hdst in Hd. simplify_eq.
      rewrite /laddr_of_argument Hsrc1 Hn1 in Ha1.
      rewrite /laddr_of_argument Hsrc2 Hn2 in Ha2. simplify_eq.
      by rewrite -andb_assoc Hwithin andb_false_r in Ht. }
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: repeat match goal with
    | H : context [_ && isWithin _ _ _ _ && _] |- _ =>
      rewrite -andb_assoc Hwithin andb_false_r in H
    end.
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  Local Lemma subseg_unrepresentable_map_cap E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2  π:
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 →
    lz_of_argument regs src2 = Some n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    incrementPC (<[ dst := WCap false p g b e a @@? π ]ₗ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hover Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$Hpc_a $Hmap]"); eauto.
    { intros ? ? ? ? ? ? ? ? Hd Ha1 Ha2 Ht Hlt.
      rewrite /laddr_of_argument Hsrc1 in Ha1.
      rewrite /laddr_of_argument Hsrc2 in Ha2.
      destruct Hover; congruence. }
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try (destruct Hover; congruence).
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  Local Lemma subseg_invalidated_map_sr E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2 a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 →
    lz_of_argument regs src2 = Some n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    incrementPC (<[ dst := WSealRange false p g a1 a2 a @@? π ]ₗ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hn1 Hn2 Hwithin Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$Hpc_a $Hmap]"); eauto.
    { intros ? ? ? ? ? ? ? ? Hd. by rewrite Hdst in Hd. }
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

  Local Lemma subseg_unrepresentable_map_sr E pc_p pc_g pc_b pc_e pc_a pc_π
      w dst src1 src2 regs regs' (t : bool) p g b e a n1 n2  π:
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 →
    lz_of_argument regs src2 = Some n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    incrementPC (<[ dst := WSealRange false p g b e a @@? π ]ₗ> regs) = Some regs' →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hdst Hsrc1 Hsrc2 Hover Hincr φ) "(Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$Hpc_a $Hmap]"); eauto.
    { intros ? ? ? ? ? ? ? ? Hd. by rewrite Hdst in Hd. }
    iNext. iIntros (regs'' retv) "(%Hspec & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try (destruct Hover; congruence).
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  (* Subseg: operand layouts follow the ordinary success rules. *)
  Lemma wp_subseg_invalidated_lr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g a1 a2 a @@? π]> (∅ : LReg))) t p g b e a n1 n2 a1 a2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_lr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g b e a @@? π]> (∅ : LReg))) t p g b e a n1 n2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_l E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 r2
      (w2 : LWord) a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a @@? π
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g a1 a2 a @@? π]> (<[r2 := w2 @@? π2]> (∅ : LReg)))) t p g b e a n1 n2 a1
        a2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_l E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1
      n2 r2 (w2 : LWord)  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g b e a @@? π]> (<[r2 := w2 @@? π2]> (∅ : LReg)))) t p g b e a n1 n2
        with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_r E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 r1
      (w1 : LWord) a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g a1 a2 a @@? π]> (<[r1 := w1 @@? π1]> (∅ : LReg)))) t p g b e a n1 n2 a1
        a2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_r E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1
      n2 r1 (w1 : LWord)  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g b e a @@? π]> (<[r1 := w1 @@? π1]> (∅ : LReg)))) t p g b e a n1 n2
        with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 r1
      (w1 : LWord) r2 (w2 : LWord) a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a @@? π
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g a1 a2 a @@? π]> (<[r1 := w1 @@? π1]> (<[r2 := w2 @@? π2]> (∅ : LReg))))) t p g b
        e a n1 n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_4 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : LWord) r2 (w2 : LWord)  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g b e a @@? π]> (<[r1 := w1 @@? π1]> (<[r2 := w2 @@? π2]> (∅ : LReg))))) t p
        g b e a n1 n2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_4 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 r1
      (w1 : LWord) a1  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g a1 a1 a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g a1 a1 a @@? π]> (<[r1 := w1 @@? π1]> (∅ : LReg)))) t p g b e a n1 n1 a1
        a1 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [by rewrite Hreject].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a
      n1 r1 (w1 : LWord)  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n1 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WCap false p g b e a @@? π]> (<[r1 := w1 @@? π1]> (∅ : LReg)))) t p g b e a n1 n1
        with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_lr_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g a1 a2 a @@? π]> (∅ : LReg))) t p g b e a n1 n2 a1 a2 with
        "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_lr_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g b e a @@? π]> (∅ : LReg))) t p g b e a n1 n2 with
        "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_l_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2
      r2 (w2 : LWord) a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a @@? π
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g a1 a2 a @@? π]> (<[r2 := w2 @@? π2]> (∅ : LReg)))) t p g b e a n1
        n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_l_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a
      n1 n2 r2 (w2 : LWord)  π:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g b e a @@? π]> (<[r2 := w2 @@? π2]> (∅ : LReg)))) t p g b e a
        n1 n2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_r_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : LWord) a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g a1 a2 a @@? π]> (<[r1 := w1 @@? π1]> (∅ : LReg)))) t p g b e a n1
        n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_r_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a
      n1 n2 r1 (w1 : LWord)  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g b e a @@? π]> (<[r1 := w1 @@? π1]> (∅ : LReg)))) t p g b e a
        n1 n2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : LWord) r2 (w2 : LWord) a1 a2  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a @@? π
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g a1 a2 a @@? π]> (<[r1 := w1 @@? π1]> (<[r2 := w2 @@? π2]> (∅ : LReg))))) t
        p g b e a n1 n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_4 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1
      n2 r1 (w1 : LWord) r2 (w2 : LWord)  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_4 with "HPC Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ? & ? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g b e a @@? π]> (<[r1 := w1 @@? π1]> (<[r2 := w2 @@? π2]> (∅ :
        LReg))))) t p g b e a n1 n2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_4 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_same_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1
      r1 (w1 : LWord) a1  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_otype n1 = Some a1 →
    isWithin a1 a1 b e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g a1 a1 a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g a1 a1 a @@? π]> (<[r1 := w1 @@? π1]> (∅ : LReg)))) t p g b e a n1
        n1 a1 a1 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_same_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e
      a n1 r1 (w1 : LWord)  π:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_otype n1 = None ∨ z_to_otype n1 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[dst := WSealRange false p g b e a @@? π]> (<[r1 := w1 @@? π1]> (∅ : LReg)))) t p g b e a
        n1 n1 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_pc_lr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 n2 a1 a2 :
    decodeInstrW w.(lw) = Subseg PC (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a2 pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a2 pc_a' @@? pc_π]> (∅ : LReg)) true pc_p pc_g pc_b pc_e pc_a n1 n2 a1 a2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_1 with "Hmap").
  Qed.

  Lemma wp_subseg_unrepresentable_pc_lr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 n2 :
    decodeInstrW w.(lw) = Subseg PC (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hover φ) "(>HPC & >Hmem) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (∅ : LReg)) true pc_p pc_g pc_b pc_e pc_a n1 n2 with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_1 with "Hmap").
  Qed.

  Lemma wp_subseg_invalidated_pc_l E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 n2 r2 (w2 : LWord) a1 a2 :
    decodeInstrW w.(lw) = Subseg PC (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a2 pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a2 pc_a' @@? pc_π]> (<[r2 := w2 @@? π2]> (∅ : LReg))) true pc_p pc_g pc_b pc_e pc_a n1 n2 a1 a2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_pc_l E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 n2 r2 (w2 : LWord) :
    decodeInstrW w.(lw) = Subseg PC (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread2 Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r2 := w2 @@? π2]> (∅ : LReg))) true pc_p pc_g pc_b pc_e pc_a n1 n2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_pc_r E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 n2 r1 (w1 : LWord) a1 a2 :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a2 pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a2 pc_a' @@? pc_π]> (<[r1 := w1 @@? π1]> (∅ : LReg))) true pc_p pc_g pc_b pc_e pc_a n1 n2 a1 a2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_pc_r E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 n2 r1 (w1 : LWord) :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := w1 @@? π1]> (∅ : LReg))) true pc_p pc_g pc_b pc_e pc_a n1 n2 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_pc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 n2 r1 (w1 : LWord) r2 (w2 :
      LWord) a1 a2 :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 pc_b pc_e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a2 pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a2 pc_a' @@? pc_π]> (<[r1 := w1 @@? π1]> (<[r2 := w2 @@? π2]> (∅ : LReg)))) true pc_p pc_g pc_b pc_e pc_a n1 n2 a1 a2
        with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_pc E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 n2 r1 (w1 : LWord) r2 (w2 : LWord) :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := w1 @@? π1]> (<[r2 := w2 @@? π2]> (∅ : LReg)))) true pc_p pc_g pc_b pc_e pc_a n1 n2
        with "[$Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_3 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_invalidated_pc_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 r1 (w1 : LWord) a1 :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 pc_b pc_e = false →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g a1 a1 pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hconvert1 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g a1 a1 pc_a' @@? pc_π]> (<[r1 := w1 @@? π1]> (∅ : LReg))) true pc_p pc_g pc_b pc_e pc_a n1 n1 a1 a1 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [by rewrite Hreject].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.

  Lemma wp_subseg_unrepresentable_pc_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w n1 r1 (w1 : LWord) :
    decodeInstrW w.(lw) = Subseg PC (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n1 = None) →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hread1 Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ w _ _ _ _ (<[PC := WCap false pc_p pc_g pc_b pc_e pc_a' @@? pc_π]> (<[r1 := w1 @@? π1]> (∅ : LReg))) true pc_p pc_g pc_b pc_e pc_a n1 n1 with "[$Hmem
        $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument !dom_insert dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    - rewrite /incrementPC /incrementPC_gen /linsert_reg ?lookup_insert.
      repeat case_decide; simplify_eq; cbn; rewrite Hincr;
      apply f_equal; apply map_eq; intros;
      rewrite !lookup_insert; repeat case_decide; simplify_eq; done.
    - iNext. iIntros "[Hmem Hmap]". iApply "Hφ". iFrame "Hmem".
      iApply (regs_of_map_2 with "Hmap"); eauto.
  Qed.
End instruction_outcomes.
