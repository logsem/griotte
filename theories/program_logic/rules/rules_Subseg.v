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

  Inductive Subseg_failure (lpc : LWord) (regs : LReg) (dst: RegName) (src1 src2: Z + RegName) :
    LWord → LReg → Prop :=
  | Subseg_fail_allowed w :
      regs !!ₗ dst = Some w →
      is_mutable_range w.(lw) = false →
      Subseg_failure lpc regs dst src1 src2 lpc regs
  | Subseg_fail_src1_nonz :
      lz_of_argument regs src1 = None →
      Subseg_failure lpc regs dst src1 src2 lpc regs
  | Subseg_fail_src2_nonz :
      lz_of_argument regs src2 = None →
      Subseg_failure lpc regs dst src1 src2 lpc regs
  | Subseg_fail_incrPC_cap (t : bool) p g b e a π n1 n2 a1 a2 :
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      z_to_addr n1 = Some a1 →
      z_to_addr n2 = Some a2 →
      incrementPC lpc = None →
      Subseg_failure lpc regs dst src1 src2 lpc regs
  | Subseg_fail_incrPC_unrepresentable_cap (t : bool) p g b e a π n1 n2 :
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
      incrementPC lpc = None →
      Subseg_failure lpc regs dst src1 src2 lpc regs
  | Subseg_fail_incrPC_sr (t : bool) p g b e a π n1 n2 a1 a2 :
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      z_to_otype n1 = Some a1 →
      z_to_otype n2 = Some a2 →
      incrementPC lpc = None →
      Subseg_failure lpc regs dst src1 src2 lpc regs
  | Subseg_fail_incrPC_unrepresentable_sr (t : bool) p g b e a π n1 n2 :
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
      incrementPC lpc = None →
      Subseg_failure lpc regs dst src1 src2 lpc regs.

  (* Both operands must be integers. If either endpoint cannot be represented,
     the instruction clears the tag and preserves both original endpoints.
     The result keeps the identifier of the source. *)
  Inductive Subseg_spec (lpc : LWord) (regs : LReg) (dst : RegName)
      (src1 src2 : Z + RegName) (lpc' : LWord) (regs' : LReg) : griotte_lang.val → Prop :=
  | Subseg_spec_success_cap (t : bool) p g b e a π n1 n2 a1 a2 :
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      z_to_addr n1 = Some a1 →
      z_to_addr n2 = Some a2 →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π ]ₗ> regs →
      Subseg_spec lpc regs dst src1 src2 lpc' regs' NextIV
  | Subseg_spec_unrepresentable_cap (t : bool) p g b e a π n1 n2 :
      regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WCap false p g b e a @@? π ]ₗ> regs →
      Subseg_spec lpc regs dst src1 src2 lpc' regs' NextIV
  | Subseg_spec_success_sr (t : bool) p g b e a π n1 n2 a1 a2 :
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      z_to_otype n1 = Some a1 →
      z_to_otype n2 = Some a2 →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a @@? π ]ₗ> regs →
      Subseg_spec lpc regs dst src1 src2 lpc' regs' NextIV
  | Subseg_spec_unrepresentable_sr (t : bool) p g b e a π n1 n2 :
      regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
      lz_of_argument regs src1 = Some n1 →
      lz_of_argument regs src2 = Some n2 →
      (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
      incrementPC lpc = Some lpc' →
      regs' = <[ dst := WSealRange false p g b e a @@? π ]ₗ> regs →
      Subseg_spec lpc regs dst src1 src2 lpc' regs' NextIV
  | Subseg_spec_failure :
      Subseg_failure lpc regs dst src1 src2 lpc' regs' →
      Subseg_spec lpc regs dst src1 src2 lpc' regs' FailedV.

  (** The premise of the generic rule. An identifier-less source that
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

  Lemma wp_Subseg Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs oa dq :
    decodeInstrW w.(lw) = Subseg dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ subseg_root_ok regs dst src1 src2 oa ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Subseg_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        subseg_root_ok regs dst src1 src2 oa ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hroot & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri dst) as [wdst [Hdst _]]; first by set_solver+.
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hdst) as (s & Hdst' & Hrel).
    pose proof (erasure_llookup_reg_word _ _ _ _ _ _ _ _ _ Her Hlregs Hdst) as Hokdst.
    pose proof (lz_of_argument_phys R regs r src1 Hregs ltac:(intros ? ->; set_solver)) as Hz1.
    pose proof (lz_of_argument_phys R regs r src2 Hregs ltac:(intros ? ->; set_solver)) as Hz2.
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
    destruct wdst as [wd π].
    destruct (is_mutable_range wd) eqn:Hwdst.
    2: { (* Failure: wdst is not of the right type *)
      assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as (-> & ->).
      { cbn in Hdst', Hstep. rewrite Hdst' /= in Hstep.
        destruct wd as [ | [t p b e a | ] | | ]; try by inversion Hwdst.
        all: cbn in Hstep; by simplify_pair_eq. }
      instr_fail_close. constructor. by eapply (Subseg_fail_allowed _ _ _ _ _ (wd @@? π)). }
    cbn in Hdst', Hstep. rewrite Hdst' /= in Hstep.
    destruct (lz_of_argument regs src1) as [n1 |] eqn:Hn1.
    2: { assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as (-> & ->).
         { destruct_word wd; cbn in Hwdst; try discriminate;
           rewrite Hz1 /= in Hstep; by simplify_pair_eq. }
         instr_fail_close. constructor. by apply Subseg_fail_src1_nonz. }
    destruct (lz_of_argument regs src2) as [n2 |] eqn:Hn2.
    2: { assert (c = Failed ∧ σ' = (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) as (-> & ->).
         { destruct_word wd; cbn in Hwdst; try discriminate;
           rewrite Hz1 Hz2 /= in Hstep; by simplify_pair_eq. }
         instr_fail_close. constructor. by apply Subseg_fail_src2_nonz. }
    assert (∃ w' pw,
        reg_word_ok R C w' ∧
        reg_phys R w' pw ∧
        (∀ lpc', incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
          Subseg_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' (<[dst := w']ₗ> regs) NextIV) ∧
        (incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None →
          Subseg_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs FailedV) ∧
        (match updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst pw) with
         | Some conf => conf | None => (Failed, (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st)) end) = (c, σ'))
      as (w' & pw & Hok' & Hpw & Hsuccess & Hfailure & Hupdate).
    { destruct wd as [ | [t p g b e a | t p g b e a] | | ];
        try discriminate Hwdst.
      - rewrite Hz1 Hz2 /= in Hstep.
        destruct (z_to_addr n1) as [a1 |] eqn:Ha1;
          destruct (z_to_addr n2) as [a2 |] eqn:Ha2.
        1: exists (WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π).
        2-4: exists (WCap false p g b e a @@? π).
        all: eexists; split_and!; [ | | intros | intros | exact Hstep ].
        all: try solve [eapply Subseg_spec_success_cap; eauto
                       | eapply Subseg_spec_unrepresentable_cap; eauto
                       | constructor; eapply Subseg_fail_incrPC_cap; eauto
                       | constructor; eapply Subseg_fail_incrPC_unrepresentable_cap; eauto].
        3-8: first [by apply reg_word_ok_untagged | by apply reg_phys_untagged].
        2: { assert (s && t && isWithin a1 a2 b e && (a1 <=? a2)%a =
                       s && (t && isWithin a1 a2 b e && (a1 <=? a2)%a)) as -> by (by destruct s).
             eapply reg_phys_subseg; [apply Her | exact Hokdst | exact Hrel |].
             intros Ht. apply andb_prop in Ht as [Ht Hle]. apply andb_prop in Ht as [-> Hw].
             apply isWithin_implies in Hw. apply Z.leb_le in Hle.
             split; first done. solve_addr. }
        eapply reg_word_ok_subseg; [apply Her | exact Hokdst | |].
        + intros Ht. apply andb_prop in Ht as [Ht Hle]. apply andb_prop in Ht as [-> Hw].
          apply isWithin_implies in Hw. apply Z.leb_le in Hle.
          split; first done. solve_addr.
        + intros Ht Hlt Hheap ->. apply Hrootc.
          * by rewrite /laddr_of_argument Hn1.
          * intros Hfree. specialize (Hfree t p g b e a a1 a2 Hdst).
            rewrite /laddr_of_argument Hn1 Hn2 in Hfree. rewrite Hfree in Hheap; done.
      - rewrite Hz1 Hz2 /= in Hstep.
        destruct (z_to_otype n1) as [a1 |] eqn:Ha1;
          destruct (z_to_otype n2) as [a2 |] eqn:Ha2.
        1: exists (WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a @@? π).
        2-4: exists (WSealRange false p g b e a @@? π).
        all: eexists; split_and!; [ | | intros | intros | exact Hstep ].
        all: try solve [by apply reg_phys_untagged
                       | eapply (reg_phys_derive_eq _ (WSealRange t p g b e a @@? π) s);
                         [exact Hrel | done | cbn; intros; by destruct t | by destruct s] ].
        all: try solve [eapply Subseg_spec_success_sr; eauto
                       | eapply Subseg_spec_unrepresentable_sr; eauto
                       | constructor; eapply Subseg_fail_incrPC_sr; eauto
                       | constructor; eapply Subseg_fail_incrPC_unrepresentable_sr; eauto].
        all: apply (reg_word_ok_derive _ _ (WSealRange t p g b e a @@? π));
          [by right | cbn; intros; by destruct t | done | exact Hokdst]. }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst w' pw _ _ _
      (λ lpc' regs' retv, Subseg_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Hroot]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. }
    { exact Hok'. } { exact Hupdate. } { exact Hpw. } { exact Hsuccess. } { exact Hfailure. }
    iIntros (lpc' regs' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (** The generic rule on its pure branch. *)
  Lemma wp_Subseg_pure Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs dq :
    decodeInstrW w.(lw) = Subseg dst src1 src2 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    subseg_root_free regs dst src1 src2 →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ Subseg_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst src1 src2 lpc' regs' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hfree φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_Subseg _ _ _ _ _ _ _ _ _ _ _ _ None with "[$HPC $Hpc_a $Hmap]"); eauto.
    iNext. iIntros (lpc' regs' retv) "(Hspec & HPC & Hpc_a & _ & Hmap)". iApply "Hφ". iFrame.
  Qed.

  (** A Subseg of a capability, with representable bounds and a PC that
      increments, has one outcome. *)
  Lemma Subseg_spec_cap_next lpc regs dst src1 src2 lpc' regs' retv
      (t : bool) p g b e a π n1 n2 a1 a2 lpc0 :
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 → lz_of_argument regs src2 = Some n2 →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    incrementPC lpc = Some lpc0 →
    Subseg_spec lpc regs dst src1 src2 lpc' regs' retv →
    retv = NextIV ∧ lpc' = lpc0 ∧
    regs' = <[dst := WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π]ₗ> regs.
  Proof.
    intros Hd H1 H2 Ha1 Ha2 Hinc Hspec.
    destruct Hspec as [* Hd' H1' H2' Ha1' Ha2' Hinc' ->
                      | * Hd' H1' H2' Hbad
                      | * Hd'
                      | * Hd'
                      | Hfail].
    - rewrite Hd in Hd'. simplify_eq. done.
    - rewrite Hd in Hd'. simplify_eq. destruct Hbad; congruence.
    - rewrite Hd in Hd'. simplify_eq.
    - rewrite Hd in Hd'. simplify_eq.
    - destruct Hfail; simplify_eq; try congruence.
  Qed.

  (** The same for a sealing range. *)
  Lemma Subseg_spec_sr_next lpc regs dst src1 src2 lpc' regs' retv
      (t : bool) p g b e a π n1 n2 a1 a2 lpc0 :
    regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 → lz_of_argument regs src2 = Some n2 →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    incrementPC lpc = Some lpc0 →
    Subseg_spec lpc regs dst src1 src2 lpc' regs' retv →
    retv = NextIV ∧ lpc' = lpc0 ∧
    regs' = <[dst := WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a @@? π]ₗ> regs.
  Proof.
    intros Hd H1 H2 Ha1 Ha2 Hinc Hspec.
    destruct Hspec as [* Hd'
                      | * Hd'
                      | * Hd' H1' H2' Ha1' Ha2' Hinc' ->
                      | * Hd' H1' H2' Hbad
                      | Hfail].
    - rewrite Hd in Hd'. simplify_eq.
    - rewrite Hd in Hd'. simplify_eq.
    - rewrite Hd in Hd'. simplify_eq. done.
    - rewrite Hd in Hd'. simplify_eq. destruct Hbad; congruence.
    - destruct Hfail; simplify_eq; try congruence.
  Qed.

  (** The map-form success rules on a capability and on a sealing range, from
      which the register-shaped ones follow. *)
  Lemma wp_subseg_next E pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs
      (t : bool) p g b e a π n1 n2 a1 a2 lpc' dq :
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    subseg_root_free regs dst src1 src2 →
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 → lz_of_argument regs src2 = Some n2 →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[dst := WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π]ₗ> regs,
          k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs Hfree Hd H1 H2 Ha1 Ha2 Hinc φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$HPC $Hpc_a $Hmap]"); [done..|].
    iIntros "!>" (lpc0 regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct (Subseg_spec_cap_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hd H1 H2 Ha1 Ha2 Hinc Hspec) as (-> & -> & ->).
    iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_subseg_next_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst src1 src2 regs
      (t : bool) p g b e a π n1 n2 a1 a2 lpc' dq :
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    subseg_root_free regs dst src1 src2 →
    regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 → lz_of_argument regs src2 = Some n2 →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[dst := WSealRange (t && isWithin a1 a2 b e) p g a1 a2 a @@? π]ₗ> regs,
          k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs Hfree Hd H1 H2 Ha1 Ha2 Hinc φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$HPC $Hpc_a $Hmap]"); [done..|].
    iIntros "!>" (lpc0 regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct (Subseg_spec_sr_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hd H1 H2 Ha1 Ha2 Hinc Hspec) as (-> & -> & ->).
    iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_subseg_success E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 (t : bool) p g b e a w1 n1 w2 n2 a1 a2 pc_a' π dq :
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

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' Hcnull Hcnull' Hcnull'' ϕ) "(HPC & Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_subseg_next with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    rewrite Hwb Hle' !andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success_same E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 (t : bool) p g b e a w1 n1 a1 pc_a'  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WCap t p g a1 a1 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hwb Hpc_a' ?? ϕ) "(HPC & Hpc_a & >Hdst & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    iDestruct (map_of_regs_2 with "Hr1 Hdst") as "[Hmap %]".
    iApply (wp_subseg_next with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    assert ((a1 <=? a1)%a = true) as Hle' by solve_addr.
    rewrite Hwb Hle' !andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success_l E pc_p pc_g pc_b pc_e pc_a pc_π w dst r2 (t : bool) p g b e a n1 w2 n2 a1 a2 pc_a'  π dq:
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

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw2 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ?? ϕ) "(HPC & Hpc_a & >Hdst & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_2 with "Hr2 Hdst") as "[Hmap %]".
    iApply (wp_subseg_next with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    rewrite Hwb Hle' !andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success_r E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 (t : bool) p g b e a w1 n1 n2 a1 a2 pc_a'  π dq:
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

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ?? ϕ) "(HPC & Hpc_a & >Hdst & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    iDestruct (map_of_regs_2 with "Hr1 Hdst") as "[Hmap %]".
    iApply (wp_subseg_next with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    rewrite Hwb Hle' !andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success_lr E pc_p pc_g pc_b pc_e pc_a pc_π w dst (t : bool) p g b e a n1 n2 a1 a2 pc_a'  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    (π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ WCap t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hle Hroot Hpc_a' ? ϕ) "(HPC & Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_subseg_next with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    rewrite Hwb Hle' !andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

   (* Similar rules in case we have a SealRange instead of a capability, where some cases are impossible, because a SealRange is not a valid PC *)

  Lemma wp_subseg_success_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 (t : bool) p g b e a w1 n1 w2 n2 a1 a2 pc_a'  π dq:
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

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hpc_a' ??? ϕ) "(HPC & Hpc_a & >Hdst & >Hr1 & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_subseg_next_sr with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    rewrite Hwb andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success_same_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 (t : bool) p g b e a w1 n1 a1 pc_a'  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 →
    isWithin a1 a1 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WSealRange t p g a1 a1 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hwb Hpc_a' ?? ϕ) "(HPC & Hpc_a & >Hdst & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    iDestruct (map_of_regs_2 with "Hr1 Hdst") as "[Hmap %]".
    iApply (wp_subseg_next_sr with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    rewrite Hwb andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success_l_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst r2 (t : bool) p g b e a n1 w2 n2 a1 a2 pc_a'  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw2 Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(HPC & Hpc_a & >Hdst & >Hr2) Hφ".
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    iDestruct (map_of_regs_2 with "Hr2 Hdst") as "[Hmap %]".
    iApply (wp_subseg_next_sr with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    rewrite Hwb andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success_r_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 (t : bool) p g b e a w1 n1 n2 a1 a2 pc_a'  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    IsLInt w1 n1 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hvpc Hn1 Hn2 Hwb Hpc_a' ?? ϕ) "(HPC & Hpc_a & >Hdst & >Hr1) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    iDestruct (map_of_regs_2 with "Hr1 Hdst") as "[Hmap %]".
    iApply (wp_subseg_next_sr with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    rewrite Hwb andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  Lemma wp_subseg_success_lr_sr E pc_p pc_g pc_b pc_e pc_a pc_π w dst (t : bool) p g b e a n1 n2 a1 a2 pc_a'  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_otype n1 = Some a1 → z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ dst ↦ᵣ WSealRange t p g a1 a2 a @@? π
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hn1 Hn2 Hwb Hpc_a' ? ϕ) "(HPC & Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_subseg_next_sr with "[$HPC $Hpc_a $Hmap]");
      try solve_next_side; try solve_subseg_root_free.
    iIntros "!> (HPC & Hpc_a & Hmap)".
    rewrite Hwb andb_true_r linsert_reg_not_cnull //.
    iRegsMap "Hmap". iApply "Hφ". iFrame.
  Qed.

  (** * Allocator-only rules *)

  (** Case 3: an identifier-less source narrowed to a tagged, non-empty heap
      result. The new base must be a heap root. *)
  Lemma wp_subseg_success_root E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 (t : bool) p g b e a w1 n1 w2 n2 a1 a2 pc_a' dq :
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

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? None
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2
        ∗ ▷ addr_alloc a1 HeapRoot }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
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
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Subseg _ _ _ _ _ _ _ _ _ _ _ _ (Some a1) with "[$HPC $Hmap $Hpc_a Hroot]");
      eauto; simplify_lmap_eq; eauto.
    all: try (by unfold regs_of; rewrite ?dom_insert ?dom_singleton_L; set_solver+).
    { iFrame. iPureIntro. rewrite /laddr_of_argument /lz_of_argument.
      simplify_lmap_eq. done. }
    iNext. iIntros (lpc' regs' retv) "(#Hspec & HPC & Hpc_a & [_ Hroot] & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | * Hdst Hz1 Hz2 Ha1 Ha2 Hincr
                      | * Hdst Hz1 Hz2 Hbounds Hincr
                      | Hfail].
    5: { destruct Hfail; unfold lz_of_argument in *; simplify_lmap_eq.
      all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
        destruct Hbad; congruence
      end.
      all: try match goal with Hincr : incrementPC _ = None |- _ =>
        rewrite Hwb Hle' ?andb_true_r in Hincr
      end.
      all: try incrementPC_inv; simplify_lmap_eq; eauto; try congruence. }
    all: unfold lz_of_argument in *; simplify_lmap_eq.
    all: try match goal with Hbad : _ = None ∨ _ = None |- _ =>
      destruct Hbad; congruence
    end.
    rewrite ?Hwb ?Hle' ?andb_true_r.
    iApply "Hφ". iFrame. try incrementPC_inv; simplify_lmap_eq.
    iRegsMap "Hmap"; eauto; iFrame.
  Qed.

  (** Case 4, the rebase: an identifier-less source narrowed to exactly the
      range of a non-dead identifier [ι] takes [ι]. The source is not
      executable, since an identified word never is. The allocate step
      ([rules_registry]) gives [alloc_obj] and the status token. *)
  Lemma wp_subseg_rebase E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 p g b e a w1 n1 w2 n2 a1 a2 pc_a'
      ι q s dq :
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    s = ALive ∨ s = APainting →
    executeAllowed p = false →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap true p g b e a @@? None
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2
        ∗ alloc_obj ι a1 a2
        ∗ ι ↦st{q} s }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ (WCap true p g a1 a2 a) @@ ι
          ∗ alloc_obj ι a1 a2
          ∗ ι ↦st{q} s
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hs Hpx Hpc_a' Hcnull Hcnull' Hcnull'' ϕ)
      "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2 & #Hobj & Htok) Hφ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert (Hle' : (a1 <=? a2)%a = true) by solve_addr.
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%&%&%)]".
    set (regs := <[r1:=WInt n1 @@? π1]>
                   (<[r2:=WInt n2 @@? π2]>
                      (<[dst:=WCap true p g b e a @@? None]> (∅ : LReg)))).
    set (v := WCap true p g a1 a2 a @@ ι).
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    iDestruct (reg_lookup_obj with "HR Hobj") as %(γ & s' & HRι).
    iDestruct (reg_lookup_own with "HR Htok") as %(b' & e' & γ' & HRι').
    rewrite HRι in HRι'. simplify_eq.
    assert (regs !!ₗ dst = Some (WCap true p g b e a @@? None)) as Hd.
    { rewrite /regs llookup_reg_not_cnull //. by simplify_map_eq. }
    assert (regs !!ₗ r1 = Some (WInt n1 @@? π1)) as Hd1.
    { rewrite /regs llookup_reg_not_cnull //. by simplify_map_eq. }
    assert (regs !!ₗ r2 = Some (WInt n2 @@? π2)) as Hd2.
    { rewrite /regs llookup_reg_not_cnull //. by simplify_map_eq. }
    destruct (llookup_reg_phys _ _ _ _ _ Hregs Hd) as (sd & Hdst' & Hreld).
    pose proof (llookup_reg_phys_int _ _ _ _ _ _ Hregs Hd1) as Hr1'.
    pose proof (llookup_reg_phys_int _ _ _ _ _ _ Hregs Hd2) as Hr2'.
    assert (exec_opt (Subseg dst (inr r1) (inr r2)) pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
              updatePC (update_reg (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) dst
                (WCap sd p g b' e' a))) as HH.
    { rewrite /exec_opt /= Hdst' Hr1' Hr2' /=.
      rewrite Hn1 Hn2 Hwb Hle' /= !andb_true_r. done. }
    rewrite Hinstr /exec HH in Hstep.
    (* The physical result is a copy of [v]: exact, or untagged when the
       source is an empty heap capability without authority. *)
    assert (reg_phys R v (WCap sd p g b' e' a)) as Hpv.
    { destruct sd.
      - apply reg_phys_exact. intros ι' x Ha Hι Hx. rewrite /v /= in Hι. simplify_eq.
        cbn. by intros [-> | ->]; destruct Hs.
      - destruct Hreld as [[Heq | [_ [[(? & ? & ? & _) _] | [Hna [base Hh]]]]] _];
          cbn in *; try discriminate.
        split; last done. right. split; first done. right.
        assert (is_heap_address b = true) as Hbh.
        { rewrite /heap_cap_base /= in Hh. by destruct (is_heap_address b). }
        assert (¬ (b < e)%a) as Hnlt.
        { intros Hlt. apply Hna. split; first done. exists b.
          apply heap_authority_base_memory_cap_bounds. eauto. }
        apply isWithin_implies in Hwb.
        assert (b' = b) as -> by solve_addr. assert (e' = b) as -> by solve_addr.
        split.
        + intros [_ [b' Hab]]. apply heap_authority_base_memory_cap_bounds in Hab as (? & [= <- <-] & ? & _).
          solve_addr.
        + rewrite /heap_cap_base /= Hbh. eauto. }
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ _ _ dst v _ _ _ _
      (λ lpc' regs' retv,
         (retv = NextIV ∧ incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧ regs' = <[dst := v]ₗ> regs) ∨
         (retv = FailedV ∧ incrementPC (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None))
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a Htok]").
    { exact Her. } { exact Hlregs. } { rewrite /regs. set_solver+. }
    { eapply reg_word_ok_rebase; eauto. by destruct Hs as [-> | ->]. } { exact Hstep. }
    { exact Hpv. }
    { intros. by left. } { intros. by right. }
    iIntros (lpc' regs' retv [(-> & Hincr & ->) | [-> Hincr]]) "HPC Hmap"; subst regs v.
    - iApply "Hφ". iFrame "∗#". try incrementPC_inv; simplify_map_eq.
      try rewrite /linsert_reg; try (rewrite decide_False; [|done]).
      iRegsMap "Hmap"; eauto; iFrame.
    - exfalso. try incrementPC_inv; simplify_lmap_eq; eauto; try congruence.
  Qed.

End griotte_lang_rules.

Section instruction_outcomes.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (* Internal proof lemmas over maps. Public outcome rules below expose
     each required register explicitly. *)
  #[local] Lemma subseg_invalidated_map_cap E pc_p pc_g pc_b pc_e pc_a pc_π
      pc_a' w dst src1 src2 regs (t : bool) p g b e a n1 n2 a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 →
    lz_of_argument regs src2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[ dst := WCap false p g a1 a2 a @@? π ]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hdst Hsrc1 Hsrc2 Hn1 Hn2 Hwithin Hpca' φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$HPC $Hpc_a $Hmap]"); eauto.
    { intros ? ? ? ? ? ? ? ? Hd Ha1 Ha2 Ht Hlt.
      rewrite Hdst in Hd. simplify_eq.
      rewrite /laddr_of_argument Hsrc1 Hn1 in Ha1.
      rewrite /laddr_of_argument Hsrc2 Hn2 in Ha2. simplify_eq.
      by rewrite -andb_assoc Hwithin andb_false_r in Ht. }
    iNext. iIntros (lpc' regs'' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try incrementPC_inv; simplify_eq.
    all: repeat match goal with
    | H : context [_ && isWithin _ _ _ _ && _] |- _ =>
      rewrite -andb_assoc Hwithin andb_false_r in H
    end.
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: try (rewrite -andb_assoc Hwithin andb_false_r); try (rewrite Hwithin andb_false_r).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  #[local] Lemma subseg_unrepresentable_map_cap E pc_p pc_g pc_b pc_e pc_a pc_π
      pc_a' w dst src1 src2 regs (t : bool) p g b e a n1 n2  π dq:
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 →
    lz_of_argument regs src2 = Some n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[ dst := WCap false p g b e a @@? π ]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hdst Hsrc1 Hsrc2 Hover Hpca' φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$HPC $Hpc_a $Hmap]"); eauto.
    { intros ? ? ? ? ? ? ? ? Hd Ha1 Ha2 Ht Hlt.
      rewrite /laddr_of_argument Hsrc1 in Ha1.
      rewrite /laddr_of_argument Hsrc2 in Ha2.
      destruct Hover; congruence. }
    iNext. iIntros (lpc' regs'' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try incrementPC_inv; simplify_eq.
    all: try (destruct Hover; congruence).
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: try (rewrite -andb_assoc Hwithin andb_false_r); try (rewrite Hwithin andb_false_r).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  #[local] Lemma subseg_invalidated_map_sr E pc_p pc_g pc_b pc_e pc_a pc_π
      pc_a' w dst src1 src2 regs (t : bool) p g b e a n1 n2 a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 →
    lz_of_argument regs src2 = Some n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[ dst := WSealRange false p g a1 a2 a @@? π ]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hdst Hsrc1 Hsrc2 Hn1 Hn2 Hwithin Hpca' φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$HPC $Hpc_a $Hmap]"); eauto.
    { intros ? ? ? ? ? ? ? ? Hd. by rewrite Hdst in Hd. }
    iNext. iIntros (lpc' regs'' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try incrementPC_inv; simplify_eq.
    all: repeat match goal with
    | H : context [_ && isWithin _ _ _ _] |- _ =>
      rewrite Hwithin andb_false_r in H
    end.
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: try (rewrite -andb_assoc Hwithin andb_false_r); try (rewrite Hwithin andb_false_r).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  #[local] Lemma subseg_unrepresentable_map_sr E pc_p pc_g pc_b pc_e pc_a pc_π
      pc_a' w dst src1 src2 regs (t : bool) p g b e a n1 n2  π dq:
    decodeInstrW w.(lw) = Subseg dst src1 src2 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Subseg dst src1 src2) ⊆ dom regs →
    regs !!ₗ dst = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs src1 = Some n1 →
    lz_of_argument regs src2 = Some n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    (pc_a + 1)%a = Some pc_a' →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[ dst := WSealRange false p g b e a @@? π ]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs Hdst Hsrc1 Hsrc2 Hover Hpca' φ) "(HPC & Hpc_a & Hmap) Hφ".
    iApply (wp_Subseg_pure with "[$HPC $Hpc_a $Hmap]"); eauto.
    { intros ? ? ? ? ? ? ? ? Hd. by rewrite Hdst in Hd. }
    iNext. iIntros (lpc' regs'' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [ | | | | Hfail]; simplify_eq.
    all: try (destruct Hfail; simplify_eq).
    all: try incrementPC_inv; simplify_eq.
    all: try (destruct Hover; congruence).
    all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
    all: try (cbn in *; congruence).
    all: try (rewrite -andb_assoc Hwithin andb_false_r); try (rewrite Hwithin andb_false_r).
    all: simplify_eq; iApply "Hφ"; iFrame.
  Qed.

  (* Subseg: operand layouts follow the ordinary success rules. *)
  Lemma wp_subseg_invalidated_lr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 a1 a2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_lr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_l E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 r2
      (w2 : LWord) a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a @@? π
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 a1 a2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_l E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1
      n2 r2 (w2 : LWord)  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_r E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 r1
      (w1 : LWord) a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 a1 a2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_r E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1
      n2 r1 (w1 : LWord)  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 r1
      (w1 : LWord) r2 (w2 : LWord) a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e && (a1 <=? a2)%a = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g a1 a2 a @@? π
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 a1 a2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : LWord) r2 (w2 : LWord)  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_addr n1 = None ∨ z_to_addr n2 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 r1
      (w1 : LWord) a1  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 b e = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g a1 a1 a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n1 a1 a1 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto];
      try solve [by rewrite Hreject].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_same E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a
      n1 r1 (w1 : LWord)  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_addr n1 = None ∨ z_to_addr n1 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WCap t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WCap false p g b e a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_cap E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n1 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_lr_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2 a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 a1 a2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_lr_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hover φ) "(>HPC & >Hmem & >Hr1) Hφ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_l_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2
      r2 (w2 : LWord) a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a @@? π
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 a1 a2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_l_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a
      n1 n2 r2 (w2 : LWord)  π dq:
    decodeInstrW w.(lw) = Subseg dst (inl n1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_r_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : LWord) a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 a1 a2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_r_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a
      n1 n2 r1 (w1 : LWord)  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inl n2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1 n2
      r1 (w1 : LWord) r2 (w2 : LWord) a1 a2  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    z_to_otype n1 = Some a1 →
    z_to_otype n2 = Some a2 →
    isWithin a1 a2 b e = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g a1 a2 a @@? π
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hconvert1 Hconvert2 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 a1 a2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1
      n2 r1 (w1 : LWord) r2 (w2 : LWord)  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r2) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (if decide (r2 = cnull) then WInt 0 else w2.(lw)) = WInt n2 →
    (z_to_otype n1 = None ∨ z_to_otype n2 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π
        ∗ r1 ↦ᵣ w1
        ∗ r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hread2 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2 & >Hr3) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1. destruct w2 as [w2 π2]; cbn in Hread2.
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap %Hne]".
    destruct Hne as (? & ? & ?).
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n2 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_invalidated_same_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e a n1
      r1 (w1 : LWord) a1  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    z_to_otype n1 = Some a1 →
    isWithin a1 a1 b e = false →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g a1 a1 a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hconvert1 Hreject φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_invalidated_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n1 a1 a1 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

  Lemma wp_subseg_unrepresentable_same_sr E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst (t : bool) p g b e
      a n1 r1 (w1 : LWord)  π dq:
    decodeInstrW w.(lw) = Subseg dst (inr r1) (inr r1) →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    (if decide (r1 = cnull) then WInt 0 else w1.(lw)) = WInt n1 →
    (z_to_otype n1 = None ∨ z_to_otype n1 = None) →
    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ WSealRange t p g b e a @@? π
        ∗ ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
        ∗ pc_a ↦ₐ{dq} w
        ∗ dst ↦ᵣ WSealRange false p g b e a @@? π
        ∗ r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hinstr Hpc Hincr Hnull Hread1 Hover φ) "(>HPC & >Hmem & >Hr1 & >Hr2) Hφ".
    destruct w1 as [w1 π1]; cbn in Hread1.
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    iApply (subseg_unrepresentable_map_sr E _ _ _ _ _ _ pc_a' w _ _ _ _ t p g b e a n1 n1 with "[$HPC $Hmem $Hmap]"); eauto;
      try solve [rewrite /regs_of /regs_of_argument ?dom_insert ?dom_singleton_L ?dom_empty_L; set_solver];
      try solve [rewrite /lz_of_argument /llookup_reg ?lookup_insert;
                 repeat case_decide; simplify_eq; cbn; eauto].
    iNext. iIntros "(HPC & Hmem & Hmap)". iApply "Hφ". iFrame "HPC Hmem".
    rewrite /linsert_reg; try (rewrite decide_False; [|done]).
    iRegsMap "Hmap"; iFrame.
  Qed.

End instruction_outcomes.
