From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From cap_machine Require Export rules_base.

Section cap_lang_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types c : cap_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : cap_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Inductive Jnz_failure (regs: Reg) (rimm: Z + RegName) (rcond : RegName) :=
  | Jnz_fail_PC_overflow_next cond:
      regs !! rcond = Some cond →
      nonZero cond = false →
      incrementPC regs = None →
      Jnz_failure regs rimm rcond
  | Jnz_fail_PC_overflow_jmp imm cond:
      regs !! rcond = Some cond →
      nonZero cond = true →
      incrementPC_gen regs imm = None →
      Jnz_failure regs rimm rcond
  | Jnz_fail_no_imm cond:
      regs !! rcond = Some cond →
      nonZero cond = true →
      z_of_argument regs rimm = None →
      Jnz_failure regs rimm rcond.

  Inductive Jnz_spec (regs: Reg) (rimm: Z + RegName) (rcond : RegName) : Reg → cap_lang.val → Prop :=
  | Jnz_spec_success_next regs' cond :
      regs !! rcond = Some cond →
      nonZero cond = false →
      incrementPC regs = Some regs' →
      Jnz_spec regs rimm rcond regs' NextIV
  | Jnz_spec_success_jmp regs' imm cond :
      regs !! rcond = Some cond →
      nonZero cond = true →
      z_of_argument regs rimm = Some imm →
      incrementPC_gen regs imm = Some regs' →
      Jnz_spec regs rimm rcond regs' NextIV
  | Jnz_spec_failure:
      Jnz_failure regs rimm rcond →
      Jnz_spec regs rimm rcond regs FailedV.

  Lemma wp_Jnz Ep pc_p pc_g pc_b pc_e pc_a w rimm rcond regs :
    decodeInstrW w = Jnz rimm rcond ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jnz rimm rcond) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Jnz_spec regs rimm rcond regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr Hsr] Hm ] /=". destruct σ1 as [ [r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR. by iPureIntro; apply normal_always_base_reducible.
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.
    destruct (Hri rcond) as [wrcond [H'rcond Hrcond]]; first by set_solver+.
    unfold exec in Hstep; cbn in Hstep.
    rewrite Hrcond /= in Hstep.

    destruct (nonZero wrcond) eqn:Hnz; pose proof Hnz as H'nz; cbn in Hstep.
    - destruct (z_of_argument regs rimm) as [imm|] eqn:Himm
      ; pose proof Himm as H'imm
      ; cycle 1.
      { (* Failure: argument is not a constant (z_of_argument regs arg = None) *)
        unfold z_of_argument in Himm, Hstep.
        destruct rimm as [| rimm]; [ congruence |].
        odestruct (Hri rimm) as [rimmv [Hrimm' Hrimm]].
        { unfold regs_of_argument. set_solver+. }
        rewrite Hrimm Hrimm' in Himm Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
        { destruct_word rimmv; cbn in Hstep; try congruence; by simplify_pair_eq. }
        iFailWP "Hφ" Jnz_fail_no_imm. }
      apply (z_of_arg_mono _ r) in Himm; auto.
      rewrite Himm in Hstep; simpl in Hstep.

      destruct (incrementPC_gen regs imm) eqn:Hregs';
        pose proof Hregs' as H'regs'; cycle 1.
      {
        assert (incrementPC_gen r imm = None) as HH.
        { eapply incrementPC_gen_overflow_mono; first eapply Hregs' ; eauto. }
        apply (incrementPC_gen_fail_updatePC_gen _ sr m) in HH. rewrite HH in Hstep.
        assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->) by (inversion Hstep; auto).
        iFailWP "Hφ" Jnz_fail_PC_overflow_jmp. }

      eapply (incrementPC_gen_success_updatePC_gen _ sr m _ imm) in Hregs'
          as (p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_gen_success_incl with (sregs':=sr) (m':=m) in HuPC; eauto.
      rewrite HuPC in Hstep.
      eassert ((c, σ2) = (NextI, _)) as HH.
      { cbn in *; eauto. }
      simplify_pair_eq.

      iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame.
      iApply "Hφ". iFrame. iPureIntro.
      eapply Jnz_spec_success_jmp; eauto.
    - destruct (incrementPC regs) eqn:HX; pose proof HX as H'X; cycle 1.
      { apply incrementPC_fail_updatePC with (sregs:=sr) (m:=m) in HX.
        eapply updatePC_fail_incl with (sregs':=sr) (m':=m) in HX; eauto.
        rewrite HX in Hstep. inv Hstep.
        iFailWP "Hφ" Jnz_fail_PC_overflow_next. }

      destruct (incrementPC_success_updatePC _ sr m _ HX)
        as (p' & g' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
      eapply updatePC_success_incl with (sregs':=sr) (m':=m) in HuPC; eauto. rewrite HuPC in Hstep.
      simplify_pair_eq.
      iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
      iFrame. iApply "Hφ". iFrame. iPureIntro.
      eapply Jnz_spec_success_next; eauto.
  Qed.

  (* TODO fix the instantiated rules *)
  (* Lemma wp_jnz_success_jmp E r1 r2 pc_p pc_g pc_b pc_e pc_a w w1 w2 : *)
  (*   decodeInstrW w = Jnz r1 r2 → *)
  (*   isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) → *)
  (*   w2 ≠ WInt 0%Z → *)

  (*   {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a *)
  (*       ∗ ▷ pc_a ↦ₐ w *)
  (*       ∗ ▷ r1 ↦ᵣ w1 *)
  (*       ∗ ▷ r2 ↦ᵣ w2 }}} *)
  (*     Instr Executable @ E *)
  (*     {{{ RET NextIV; *)
  (*         PC ↦ᵣ updatePcPerm w1 *)
  (*         ∗ pc_a ↦ₐ w *)
  (*         ∗ r1 ↦ᵣ w1 *)
  (*         ∗ r2 ↦ᵣ w2 }}}. *)
  (* Proof. *)
  (*   iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ". *)
  (*   iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]". *)
  (*   iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   assert (nonZero w2 = true). *)
  (*   { unfold nonZero, Zneq_bool in *. *)
  (*     repeat case_match; try congruence; subst. exfalso. *)
  (*     apply Hne. f_equal. by apply Z.compare_eq. } *)

  (*  destruct Hspec as [ | | ]. *)
  (*  { exfalso. simplify_map_eq. congruence. } *)
  (*  { exfalso. simplify_map_eq. congruence. } *)
  (*  { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert. *)
  (*    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. } *)
  (* Qed. *)

  (* Lemma wp_jnz_success_jmp2 E r2 pc_p pc_g pc_b pc_e pc_a w w2 : *)
  (*   decodeInstrW w = Jnz r2 r2 → *)
  (*   isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) → *)
  (*   w2 ≠ WInt 0%Z → *)

  (*   {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a *)
  (*       ∗ ▷ pc_a ↦ₐ w *)
  (*       ∗ ▷ r2 ↦ᵣ w2 }}} *)
  (*     Instr Executable @ E *)
  (*     {{{ RET NextIV; *)
  (*         PC ↦ᵣ updatePcPerm w2 *)
  (*         ∗ pc_a ↦ₐ w *)
  (*         ∗ r2 ↦ᵣ w2 }}}. *)
  (* Proof. *)
  (*   iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]". *)
  (*   iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   assert (nonZero w2 = true). *)
  (*   { unfold nonZero, Zneq_bool in *. *)
  (*     repeat case_match; try congruence; subst. exfalso. *)
  (*     apply Hne. f_equal. by apply Z.compare_eq. } *)

  (*  destruct Hspec as [ | | ]. *)
  (*  { exfalso. simplify_map_eq. congruence. } *)
  (*  { exfalso. simplify_map_eq. congruence. } *)
  (*  { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert. *)
  (*    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
  (* Qed. *)

  (* Lemma wp_jnz_success_jmpPC E pc_p pc_g pc_b pc_e pc_a w : *)
  (*   decodeInstrW w = Jnz PC PC → *)
  (*   isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) → *)

  (*   {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a *)
  (*       ∗ ▷ pc_a ↦ₐ w }}} *)
  (*     Instr Executable @ E *)
  (*     {{{ RET NextIV; *)
  (*         PC ↦ᵣ updatePcPerm (WCap pc_p pc_g pc_b pc_e pc_a) *)
  (*         ∗ pc_a ↦ₐ w }}}. *)
  (* Proof. *)
  (*   iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a) Hφ". *)
  (*   iDestruct (map_of_regs_1 with "HPC") as "Hmap". *)
  (*   iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*  destruct Hspec as [ | | ]; [ by simplify_map_eq .. | ]. *)
  (*  { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert. *)
  (*    iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame. } *)
  (* Qed. *)

  (* Lemma wp_jnz_success_jmpPC1 E r2 pc_p pc_g pc_b pc_e pc_a w w2 : *)
  (*   decodeInstrW w = Jnz PC r2 → *)
  (*   isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) → *)
  (*   w2 ≠ WInt 0%Z → *)

  (*   {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a *)
  (*       ∗ ▷ pc_a ↦ₐ w *)
  (*       ∗ ▷ r2 ↦ᵣ w2 }}} *)
  (*     Instr Executable @ E *)
  (*     {{{ RET NextIV; *)
  (*         PC ↦ᵣ updatePcPerm (WCap pc_p pc_g pc_b pc_e pc_a) *)
  (*         ∗ pc_a ↦ₐ w *)
  (*         ∗ r2 ↦ᵣ w2 }}}. *)
  (* Proof. *)
  (*   iIntros (Hinstr Hvpc Hne ϕ) "(>HPC & >Hpc_a & >Hr2) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]". *)
  (*   iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*   assert (nonZero w2 = true). *)
  (*   { unfold nonZero, Zneq_bool in *. *)
  (*     repeat case_match; try congruence; subst. exfalso. *)
  (*     apply Hne. f_equal. by apply Z.compare_eq. } *)

  (*  destruct Hspec as [ | | ]. *)
  (*  { exfalso. simplify_map_eq. congruence. } *)
  (*  { exfalso. simplify_map_eq. congruence. } *)
  (*  { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert. *)
  (*    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
  (* Qed. *)

  (* Lemma wp_jnz_success_jmpPC2 E r1 pc_p pc_g pc_b pc_e pc_a w w1 : *)
  (*   decodeInstrW w = Jnz r1 PC → *)
  (*   isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) → *)

  (*   {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a *)
  (*       ∗ ▷ pc_a ↦ₐ w *)
  (*       ∗ ▷ r1 ↦ᵣ w1 }}} *)
  (*     Instr Executable @ E *)
  (*     {{{ RET NextIV; *)
  (*         PC ↦ᵣ updatePcPerm w1 *)
  (*         ∗ pc_a ↦ₐ w *)
  (*         ∗ r1 ↦ᵣ w1 }}}. *)
  (* Proof. *)
  (*   iIntros (Hinstr Hvpc ϕ) "(>HPC & >Hpc_a & >Hr1) Hφ". *)
  (*   iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]". *)
  (*   iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*  destruct Hspec as [ | | ]; [ by simplify_map_eq .. | ]. *)
  (*  { iApply "Hφ". iFrame. simplify_map_eq. rewrite insert_insert. *)
  (*    iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. } *)
  (* Qed. *)

  (* Lemma wp_jnz_success_next E r1 r2 pc_p pc_g pc_b pc_e pc_a pc_a' w w1 : *)
  (*   decodeInstrW w = Jnz r1 r2 → *)
  (*   isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) → *)
  (*   (pc_a + 1)%a = Some pc_a' → *)

  (*   {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a *)
  (*       ∗ ▷ pc_a ↦ₐ w *)
  (*       ∗ ▷ r1 ↦ᵣ w1 *)
  (*       ∗ ▷ r2 ↦ᵣ WInt 0%Z }}} *)
  (*     Instr Executable @ E *)
  (*     {{{ RET NextIV; *)
  (*         PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a' *)
  (*         ∗ pc_a ↦ₐ w *)
  (*         ∗ r1 ↦ᵣ w1 *)
  (*         ∗ r2 ↦ᵣ WInt 0%Z }}}. *)
  (* Proof. *)
  (*   iIntros (Hinstr Hvpc Hpc_a' ϕ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) Hφ". *)
  (*   iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]". *)
  (*   iApply (wp_Jnz with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto. *)
  (*   by unfold regs_of; rewrite !dom_insert; set_solver+. *)
  (*   iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec. *)

  (*  destruct Hspec as [ | | ]; try incrementPC_inv; simplify_map_eq; eauto. *)
  (*  { congruence. } *)
  (*  { iApply "Hφ". iFrame. rewrite insert_insert. *)
  (*    iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. } *)
  (* Qed. *)

End cap_lang_rules.
