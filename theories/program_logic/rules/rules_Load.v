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
  Implicit Types c : griotte_lang.expr.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types v : griotte_lang.val.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Definition reg_allows_load_imm (regs : Reg) (r : RegName) (imm : Z) p g b e a ea :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    (a + imm)%a = Some ea ∧ readAllowed p = true ∧ withinBounds b e ea = true.

  Inductive Load_failure_imm (regs: Reg) (r1 r2: RegName) (imm : Z) (mem : gmap Addr Word) :=
  | Load_fail_const_imm w:
      regs !!ᵣ r2 = Some w ->
      is_cap w = false →
      Load_failure_imm regs r1 r2 imm mem
  | Load_fail_tag_imm p g b e a:
      regs !!ᵣ r2 = Some (WCap false p g b e a) →
      Load_failure_imm regs r1 r2 imm mem
  | Load_fail_addr_imm p g b e a:
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = None →
      Load_failure_imm regs r1 r2 imm mem
  | Load_fail_bounds_imm p g b e a ea:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      (readAllowed p = false ∨ withinBounds b e ea = false) →
      Load_failure_imm regs r1 r2 imm mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC_imm p g b e a ea loadv:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      mem !! ea = Some loadv →
      incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs) = None ->
      Load_failure_imm regs r1 r2 imm mem
  .

  Inductive Load_spec_imm
    (regs: Reg) (r1 r2: RegName) (imm : Z)
    (regs': Reg) (mem : gmap Addr Word) : griotte_lang.val → Prop
  :=
  | Load_spec_success_imm p g b e a ea loadv :
    reg_allows_load_imm regs r2 imm p g b e a ea →
    mem !! ea = Some loadv →
    incrementPC
      (<[ r1 := (load_word p loadv) ]ᵣ> regs) = Some regs' ->
    Load_spec_imm regs r1 r2 imm regs' mem NextIV

  | Load_spec_failure_imm :
    Load_failure_imm regs r1 r2 imm mem ->
    Load_spec_imm regs r1 r2 imm regs' mem FailedV.

  Definition allow_load_map_or_true_imm r (imm : Z) (regs : Reg) (mem : gmap Addr Word):=
    ∃ t p g b e a, read_reg_inr regs r t p g b e a ∧
      match (a + imm)%a with
      | None => True
      | Some ea => if decide (reg_allows_load_imm regs r imm p g b e a ea) then
        ∃ w, mem !! ea = Some w
      else True
      end.

  Lemma allow_load_implies_loadv_imm r2 imm mem regs p g b e a ea :
    allow_load_map_or_true_imm r2 imm regs mem →
    reg_allows_load_imm regs r2 imm p g b e a ea →
    ∃ loadv, mem !! ea = Some loadv.
  Proof.
    intros (t & p0 & g0 & b0 & e0 & a0 & Hsrc & Hmem) Hallow.
    destruct Hallow as (Hreg & Hadd & Hra & Hwb).
    assert (r2 ≠ cnull).
    { intros ->. simplify_map_eq. destruct (regs !! cnull); cbn in *; done. }
    unfold read_reg_inr in Hsrc. simpl_map_regs by eauto.
    rewrite Hreg in Hsrc. inversion Hsrc; subst.
    unfold reg_allows_load_imm in Hmem. rewrite Hadd in Hmem. case_decide as Hdec; first done.
    exfalso. apply Hdec. repeat split; auto. by simplify_map_eq.
  Qed.

  Lemma wp_load_general_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs :
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec_imm regs r1 r2 imm regs' mem retv⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq φ) "(>Hmem & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr Hsr] Hm ] /=". destruct σ1 as [ [r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.

    (* Derive necessary register values in r *)
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r2) as [r2v [Hr'2 Hr2]]; first by set_solver+.
    odestruct (Hri r1) as [r1v [Hr'1 _]]; first by set_solver+.
    clear Hri.
    (* Derive the PC in memory *)
    assert (is_Some (dfracs !! pc_a)) as [dq Hdq].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! pc_a = Some (dq,w)) as Hmem_dpc.
    { rewrite lookup_merge Hmem_pc Hdq //. }
    iDestruct (gen_mem_valid_inSepM_general (prod_merge dfracs mem) m with "Hm Hmem") as %Hma; eauto.

    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.

    rewrite /exec /= Hr2 /= in Hstep.

     (* Now we start splitting on the different cases in the Load spec, and prove them one at a time *)
     destruct (is_cap r2v) eqn:Hr2v.
     2:{ (* Failure: r2 is not a capability *)
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
       {
         unfold is_cap in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" Load_fail_const_imm.
     }
     destruct r2v as [ | [t p g b e a | ] | | ]; try inversion Hr2v. clear Hr2v.
     destruct t.
     2: {
       inversion Hstep; subst c σ2.
       iFailWP "Hφ" Load_fail_tag_imm.
     }

    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { inversion Hstep; subst c σ2. iFailWP "Hφ" Load_fail_addr_imm. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iFailWP "Hφ" Load_fail_bounds_imm.
    }
    apply andb_true_iff in HRA; destruct HRA as (Hra & Hwb).

    (* Prove that a is in the memory map now, otherwise we cannot continue *)
    assert (reg_allows_load_imm regs r2 imm p g b e a ea) as Hallow.
    { repeat split; auto. }
    destruct (allow_load_implies_loadv_imm r2 imm mem regs p g b e a ea HaLoad Hallow) as (loadv & Hmema).

    assert (is_Some (dfracs !! ea)) as [dq' Hdq'].
    { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom;eauto. }
    assert (prod_merge dfracs mem !! ea = Some (dq',loadv)) as Hmemadq.
    { rewrite lookup_merge Hmema Hdq' //. }
    iDestruct (gen_mem_valid_inSepM_general (prod_merge dfracs mem) m ea loadv with "Hm Hmem" ) as %Hma' ; eauto.

    rewrite Hma' /= in Hstep.
    destruct (incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
    2: { (* Failure: the PC could not be incremented correctly *)
      assert (incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> r) = None).
      { eapply incrementPC_overflow_mono; first eapply Hregs'.
          + simplify_map_eq; by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto. }

      rewrite incrementPC_fail_updatePC /= in Hstep; auto.
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
      iFailWP "Hφ" Load_fail_invalid_PC_imm.
    }

    (* Success *)
    rewrite /update_reg /= in Hstep.
    eapply (incrementPC_success_updatePC _ sr m) in Hregs'
      as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame.
    iPureIntro. eapply Load_spec_success_imm; auto.
    * exact Hallow.
    * exact Hmema.
    * rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
      Unshelve. all: auto.
  Qed.

  Lemma wp_load_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem regs dq :
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec_imm regs r1 r2 imm regs' mem retv⌝ ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "[Hmem Hreg] Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general_imm with "[$Hmem $Hreg]");eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ?) "(?&Hmem&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  Definition reg_allows_load (regs : Reg) (r : RegName) p g b e a  :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  Inductive Load_failure (regs: Reg) (r1 r2: RegName) (mem : gmap Addr Word) :=
  | Load_fail_const w:
      regs !!ᵣ r2 = Some w ->
      is_cap w = false →
      Load_failure regs r1 r2 mem
  | Load_fail_tag p g b e a:
      regs !!ᵣ r2 = Some (WCap false p g b e a) →
      Load_failure regs r1 r2 mem
  | Load_fail_bounds p g b e a:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (readAllowed p = false ∨ withinBounds b e a = false) →
      Load_failure regs r1 r2 mem
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC p g b e a loadv:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      mem !! a = Some loadv →
      incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs) = None ->
      Load_failure regs r1 r2 mem
  .

  Inductive Load_spec
    (regs: Reg) (r1 r2: RegName)
    (regs': Reg) (mem : gmap Addr Word) : griotte_lang.val → Prop
  :=
  | Load_spec_success p g b e a loadv :
    reg_allows_load regs r2 p g b e a →
    mem !! a = Some loadv →
    incrementPC
      (<[ r1 := (load_word p loadv) ]ᵣ> regs) = Some regs' ->
    Load_spec regs r1 r2 regs' mem NextIV

  | Load_spec_failure :
    Load_failure regs r1 r2 mem ->
    Load_spec regs r1 r2 regs' mem FailedV.

  Definition allow_load_map_or_true r (regs : Reg) (mem : gmap Addr Word):=
    ∃ t p g b e a, read_reg_inr regs r t p g b e a ∧
      if decide (reg_allows_load regs r p g b e a) then
        ∃ w, mem !! a = Some w
      else True.

  Lemma reg_allows_load_imm_zero regs r p g b e a ea :
    reg_allows_load_imm regs r 0 p g b e a ea ↔
    ea = a ∧ reg_allows_load regs r p g b e a.
  Proof. unfold reg_allows_load_imm, reg_allows_load. rewrite finz_add_0. naive_solver. Qed.

  Lemma allow_load_map_or_true_imm_zero r regs mem :
    allow_load_map_or_true_imm r 0 regs mem ↔ allow_load_map_or_true r regs mem.
  Proof.
    unfold allow_load_map_or_true_imm, allow_load_map_or_true.
    unfold reg_allows_load_imm, reg_allows_load.
    setoid_rewrite finz_add_0.
    split; intros (t & p & g & b & e & a & Hr & Hmem);
      exists t,p,g,b,e,a; split; try done.
    all: cbn in Hmem |- *; repeat case_decide; pose proof (finz_add_0 MemNum a); naive_solver.
  Qed.

  Definition Load_failure_imm_zero regs r1 r2 mem :
    Load_failure_imm regs r1 r2 0 mem → Load_failure regs r1 r2 mem.
  Proof.
    intros H; destruct H.
    all: try match goal with H : (_ + 0)%a = _ |- _ => rewrite finz_add_0 in H; simplify_eq end.
    - eapply Load_fail_const; eauto.
    - eapply Load_fail_tag; eauto.
    - eapply Load_fail_bounds; eauto.
    - eapply Load_fail_invalid_PC; eauto.
  Defined.

  Definition Load_failure_zero_imm regs r1 r2 mem :
    Load_failure regs r1 r2 mem → Load_failure_imm regs r1 r2 0 mem.
  Proof.
    intros H; destruct H.
    - eapply Load_fail_const_imm; eauto.
    - eapply Load_fail_tag_imm; eauto.
    - eapply Load_fail_bounds_imm; eauto. by rewrite finz_add_0.
    - eapply Load_fail_invalid_PC_imm; eauto. by rewrite finz_add_0.
  Defined.

  Lemma Load_spec_imm_zero regs r1 r2 regs' mem retv :
    Load_spec_imm regs r1 r2 0 regs' mem retv ↔ Load_spec regs r1 r2 regs' mem retv.
  Proof.
    split; intros H; destruct H.
    - apply reg_allows_load_imm_zero in H as [-> H]. econstructor; eauto.
    - constructor. by apply Load_failure_imm_zero.
    - econstructor; eauto. apply reg_allows_load_imm_zero. done.
    - constructor. by apply Load_failure_zero_imm.
  Qed.

  Lemma allow_load_implies_loadv:
    ∀ (r2 : RegName) (mem0 : gmap Addr Word) (r : Reg) (p : Perm)
      (g : Locality) (b e a : Addr),
      allow_load_map_or_true r2 r mem0
      → r !!ᵣ r2 = Some (WCap true p g b e a)
      → readAllowed p = true
      → withinBounds b e a = true
      → ∃ (loadv : Word),
          mem0 !! a = Some loadv.
  Proof.
    intros r2 mem0 r p g b e a HaLoad Hr2v Hra Hwb.
    unfold allow_load_map_or_true, read_reg_inr in HaLoad.
    destruct HaLoad as (t&?&?&?&?&?& Hrinr & Hmem).
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (r !! cnull); cbn in * ; done.
    }
    simpl_map_regs by eauto.
    rewrite Hr2v in Hrinr. inversion Hrinr; subst.
    case_decide as Hrega.
    - exact Hmem.
    - assert (r !!ᵣ r2 = Some (WCap true x x0 x1 x2 x3)); eauto.
      { by simplify_map_eq. }
      contradiction Hrega. done.
  Qed.

  Lemma mem_eq_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (w : Word) p g b e a,
      mem = <[a:=w]> ∅
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 w p g b e a Hmem Hrr2.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a; split.
    - unfold read_reg_inr. by rewrite Hrr2.
    - case_decide; last done.
      exists w. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a,
      a ≠ pc_a
      → mem = <[pc_a:=w]> (<[a:=w']> ∅)
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a H4 Hrr2 Hreg2.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a; split.
    - unfold read_reg_inr. by rewrite Hreg2.
    - case_decide; last done.
      exists w'. simplify_map_eq. auto.
  Qed.

  Lemma mem_implies_allow_load_map:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a,
      (if (a =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[a:=w']> ∅))
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → allow_load_map_or_true r2 regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a H4 Hrr2.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    destruct (a =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst a. eapply mem_eq_implies_allow_load_map; eauto.
        by simplify_map_eq.
      + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_load_map; eauto.
        2: by simplify_map_eq.
        congruence.
  Qed.

  Lemma mem_eq_implies_allow_load_map_imm:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (w : Word) p g b e a ea (imm : Z),
      mem = <[ea:=w]> ∅
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 w p g b e a ea imm Hmem Hrr2 Hadd.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a; split.
    - unfold read_reg_inr. by rewrite Hrr2.
    - unfold reg_allows_load_imm. rewrite Hadd. case_decide; last done.
      exists w. simplify_map_eq. auto.
  Qed.

  Lemma mem_neq_implies_allow_load_map_imm:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a ea (imm : Z),
      ea ≠ pc_a
      → mem = <[pc_a:=w]> (<[ea:=w']> ∅)
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a ea imm H4 Hrr2 Hreg2 Hadd.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    exists true,p,g,b,e,a; split.
    - unfold read_reg_inr. by rewrite Hreg2.
    - unfold reg_allows_load_imm. rewrite Hadd. case_decide; last done.
      exists w'. simplify_map_eq. auto.
  Qed.

  Lemma mem_implies_allow_load_map_imm:
    ∀ (regs : Reg)(mem : gmap Addr Word)(r2 : RegName) (pc_a : Addr)
      (w w' : Word) p g b e a ea (imm : Z),
      (if (ea =? pc_a)%a
       then mem = <[pc_a:=w]> ∅
       else mem = <[pc_a:=w]> (<[ea:=w']> ∅))
      → regs !!ᵣ r2 = Some (WCap true p g b e a)
      → (a + imm)%a = Some ea
      → allow_load_map_or_true_imm r2 imm regs mem.
  Proof.
    intros regs mem r2 pc_a w w' p g b e a ea imm H4 Hrr2 Hadd.
    assert (r2 ≠ cnull).
    { intros -> ; simplify_map_eq.
      destruct (regs !! cnull); cbn in * ; done.
    }
    simplify_map_eq.
    destruct (ea =? pc_a)%a eqn:Heq.
      + apply Z.eqb_eq, finz_to_z_eq in Heq. subst ea. eapply mem_eq_implies_allow_load_map_imm; eauto.
        by simplify_map_eq.
      + apply Z.eqb_neq in Heq. eapply mem_neq_implies_allow_load_map_imm; eauto.
        2: by simplify_map_eq.
        congruence.
  Qed.

  Lemma mem_implies_loadv:
    ∀ (pc_a : Addr) (w w' : Word) (a0 : Addr)
      (mem0 : gmap Addr Word) (loadv : Word),
      (if (a0 =? pc_a)%a
       then mem0 = <[pc_a:=w]> ∅
       else mem0 = <[pc_a:=w]> (<[a0:=w']> ∅))→
      mem0 !! a0 = Some loadv →
      loadv = (if (a0 =? pc_a)%a then w else w').
  Proof.
    intros pc_a w w' a0 mem0 loadv H4 H6.
    destruct (a0 =? pc_a)%a eqn:Heq; rewrite H4 in H6.
    + apply Z.eqb_eq, finz_to_z_eq in Heq; subst a0. by simplify_map_eq.
    + apply Z.eqb_neq in Heq. rewrite lookup_insert_ne in H6; last congruence. by simplify_map_eq.
  Qed.

  Lemma wp_load_general Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs :
   decodeInstrW w = Load r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true r2 regs mem →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 regs' mem retv⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem HaLoad Hdom φ) "Hres Hφ".
    iApply (wp_load_general_imm with "Hres"); eauto.
    { by apply allow_load_map_or_true_imm_zero. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hregs)".
    iApply "Hφ". iFrame. iPureIntro. by apply Load_spec_imm_zero.
  Qed.

  Lemma wp_load Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem regs dq :
   decodeInstrW w = Load r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true r2 regs mem →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 regs' mem retv⌝ ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "[Hmem Hreg] Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general with "[$Hmem $Hreg]");eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ?) "(?&Hmem&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  Lemma wp_load_success E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ (if (eqb_addr a pc_a) then emp else ▷ a ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ (if (eqb_addr a pc_a) then (load_word p w) else (load_word p w'))
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ (if (eqb_addr a pc_a) then emp else a ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    { destruct (a =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iApply "Hφ". iFrame.
       by destruct (a0 =? x4)%Z.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; [destruct o|].
       all: congruence.
     }
  Qed.

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ ▷ a ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ a ↦ₐ{dq'} w' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha)".
    destruct (a =? pc_a)%Z eqn:Ha.
    - rewrite (_: a = pc_a); cycle 1.
      { apply Z.eqb_eq in Ha. solve_addr. }
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst a. auto. }
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst a.
        by assert (pc_a =? pc_a = true)%Z as -> by (apply Z.eqb_refl).
      }
      iNext. iIntros "(? & ? & ? & ? & ?)".
      iApply "Hφ".
      assert (pc_a =? pc_a = true)%Z as -> by (apply Z.eqb_refl).
      iFrame.
    - iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2 Ha]"); eauto.
      { rewrite Ha. iFrame. }
      iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
      iApply "Hφ". iFrame.
      Unshelve.
      + apply DfracDiscarded.
      + apply (WInt 0).
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e pc_a' dq :
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e pc_a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e pc_a }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2)".
    iIntros "Hφ". iApply (wp_load_success with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_same E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a
          ∗ (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ (if (a =? pc_a)%a then load_word p w else load_word p w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (a =? pc_a)%a then emp else a ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc Hra Hwb Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (a =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map; eauto. by simplify_map_eq. }
    { destruct (a =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by destruct (a0 =? x4)%Z.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto; [ destruct o |]; congruence. }
    Qed.

  Lemma wp_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a
          ∗ ▷ a ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ a ↦ₐ{dq'} w' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Ha)".
    destruct (a =? pc_a)%a eqn:Ha.
    { assert (a = pc_a) as Heqa.
      { apply Z.eqb_eq in Ha. solve_addr. }
      rewrite Heqa. subst a.
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto.
      { rewrite Ha; done. }
      iNext. iIntros "(? & ? & ? & ?)".
      iApply "Hφ". iFrame. rewrite Ha. iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]"); eauto.
    { rewrite Ha. iFrame. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame.
    Unshelve.
    + apply (WInt 0).
    + apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_same_frominstr E r1 pc_p pc_g pc_b pc_e pc_a w p g b e pc_a' dq :
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e pc_a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w
             ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1)".
    iIntros "Hφ". iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a (t : bool) p' g' b' e' a' a'' :
    decodeInstrW w = Load PC r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ ▷ a ↦ₐ WCap t p' g' b' e' a' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ load_word p (WCap t p' g' b' e' a'')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ a ↦ₐ WCap t p' g' b' e' a' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map with (a := a) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H1 as [Hrr2 _]. simplify_map_eq.
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto.
       iFrame.
       by destruct p0; destruct dro,dl; rewrite /load_word in H1 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail.
       + simplify_map_eq; eauto.
       + simplify_map_eq; eauto.
       + simplify_map_eq; eauto.
         destruct o ; congruence.
       + simplify_map_eq; eauto.
         rewrite /load_word in e3 |- *.
         destruct (isDRO p0) eqn:HDRO, (isDL p0) eqn:HDL; cbn.
         all: try incrementPC_inv; simplify_map_eq; eauto.
         all: try congruence.
     }
  Qed.

  Lemma wp_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' dq :
    decodeInstrW w = Load r1 PC 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w'' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r1 ↦ᵣ load_word pc_p w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iApply (wp_load with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_eq_implies_allow_load_map with (a := pc_a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as [Hrr2 _]. simplify_map_eq.
       rewrite -memMap_resource_1_dq.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_ne //= insert_insert_eq insert_insert_ne //= insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto.
       + apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
         destruct o; apply Is_true_false in H0; try congruence. done.
       + congruence.
     }
  Qed.

  Lemma wp_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ ▷ a ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w'
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ a ↦ₐ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_success_same_alt E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a pc_a' :
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a
          ∗ ▷ a ↦ₐ w'}}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w'
             ∗ pc_a ↦ₐ w
             ∗ a ↦ₐ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ".
    iAssert (⌜(a =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_same with "[$HPC $Hpc_a $Hr1 Ha]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_fail_not_cap E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' wsrc :
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc = false ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ wsrc
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
     iIntros (Hdecode Hvpc Hbounds φ) "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite memMap_resource_1_dq.
     iApply (wp_load with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true.
       destruct_word wsrc; cbn in *; try done.
       all: eexists true, RO, Global, za, za, za. (* dummy values *)
       all: split; rewrite /read_reg_inr; first by simplify_map_eq.
       all: rewrite /reg_allows_load; simplify_map_eq.
       all: rewrite decide_False; first done.
       all: intros (?&_&_); try done;  simplify_map_eq.
       all: destruct (decide (r2 = cnull)); done.
     }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [| Hfail].
     {
       rewrite /reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & _ & ?); simplify_eq.
       destruct (decide (r2 = cnull)); first done.
       simplify_eq.
     }
     by iApply "Hφ".
  Qed.

  Lemma wp_load_fail_not_ra E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a :
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
     iIntros (Hdecode Hvpc Hbounds Hcnull φ) "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite memMap_resource_1_dq.
     iApply (wp_load with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load; simplify_map_eq.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&?&_); done.
     }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [| Hfail].
     {
       rewrite /reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & ? & ?); simplify_eq.
       by rewrite H5 in Hbounds.
     }
     by iApply "Hφ".
  Qed.

  Lemma wp_load_fail_not_withinbounds E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a :
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = false →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
     iIntros (Hdecode Hvpc Hbounds Hcnull φ) "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite memMap_resource_1_dq.
     iApply (wp_load with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load; simplify_map_eq.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&?); done.
     }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [| Hfail].
     {
       rewrite /reg_allows_load in H2; simplify_map_eq.
       destruct H2 as (? & _ & ?); simplify_eq.
       by rewrite H5 in Hbounds.
     }
     by iApply "Hφ".
  Qed.

  (* Untagged authority fails before reading the target memory. *)
  Lemma wp_load_fail_tag E pc_p pc_g pc_b pc_e pc_a
      w dst src regs wa :
    decodeInstrW w = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    get_tag wa = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hsrc Htag φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[Hr Hsr] Hm] /=".
    destruct σ1 as [[r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
    { destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
        by simplify_pair_eq. }
    cbn; iFrame; iApply "Hφ"; iFrame. done.
  Qed.

  Lemma wp_load_success_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' dq dq' :
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ (if (eqb_addr ea pc_a) then emp else ▷ ea ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ (if (eqb_addr ea pc_a) then (load_word p w) else (load_word p w'))
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ (if (eqb_addr ea pc_a) then emp else ea ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iApply (wp_load_general_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       (* FIXME: fragile *)
       destruct H2 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       { iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H3) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_3 with "[$Hmap]") as "[HPC [Hr1 Hr2] ]"; eauto.
       iApply "Hφ". iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma wp_load_success_same_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' dq dq' :
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a
          ∗ (if (ea =? pc_a)%a then emp else ▷ ea ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ (if (ea =? pc_a)%a then load_word p w else load_word p w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (ea =? pc_a)%a then emp else ea ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma wp_load_success_notinstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' dq dq' :
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ ▷ ea ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ ea ↦ₐ{dq'} w' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha)".
    destruct (ea =? pc_a)%Z eqn:Ha.
    - rewrite (_: ea = pc_a); cycle 1.
      { apply Z.eqb_eq in Ha. solve_addr. }
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst ea. by rewrite Z.eqb_refl. }
      iNext. iIntros "(? & ? & ? & ? & ?)".
      iApply "Hφ".
      rewrite Ha.
      iFrame.
    - iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2 Ha]"); eauto.
      { rewrite Ha. iFrame. }
      iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
      iApply "Hφ". iFrame.
      Unshelve.
      + apply DfracDiscarded.
      + apply (WInt 0).
  Qed.

  Lemma wp_load_success_frominstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e a (imm : Z) pc_a' dq :
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w
             ∗ pc_a ↦ₐ{dq} w
             ∗ r2 ↦ᵣ WCap true p g b e a }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2)".
    iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_same_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' dq dq' :
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a
          ∗ ▷ ea ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ ea ↦ₐ{dq'} w' }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Ha)".
    destruct (ea =? pc_a)%a eqn:Ha.
    { assert (ea = pc_a) as Heqa.
      { apply Z.eqb_eq in Ha. solve_addr. }
      rewrite Heqa. subst ea.
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1]"); eauto.
      { rewrite Ha; done. }
      iNext. iIntros "(? & ? & ? & ?)".
      iApply "Hφ". iFrame. rewrite Ha. iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1 Ha]"); eauto.
    { rewrite Ha. iFrame. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame.
    Unshelve.
    + apply (WInt 0).
    + apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_same_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w p g b e a (imm : Z) pc_a' dq :
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true →
    withinBounds b e pc_a = true →
    (a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w
             ∗ pc_a ↦ₐ{dq} w }}}.
  Proof.
    intros. iIntros "(>HPC & >Hpc_a & >Hr1)".
    iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_alt_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' :
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ ▷ ea ↦ₐ w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w'
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ ea ↦ₐ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_imm with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_success_same_alt_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' :
    decodeInstrW w = Load r1 r1 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ WCap true p g b e a
          ∗ ▷ ea ↦ₐ w'}}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word p w'
             ∗ pc_a ↦ₐ w
             ∗ ea ↦ₐ w' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Ha Hpc_a") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1 Ha]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_fail_tag_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs wa :
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    get_tag wa = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hsrc Htag φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[Hr Hsr] Hm] /=".
    destruct σ1 as [[r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
    { destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
        by simplify_pair_eq. }
    cbn; iFrame; iApply "Hφ"; iFrame. done.
  Qed.

  Lemma wp_load_fail_not_ra_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a (imm : Z) :
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = false ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
     iIntros (Hdecode Hvpc Hbounds Hcnull φ) "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite memMap_resource_1_dq.
     iApply (wp_load_imm with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true_imm.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load_imm; simplify_map_eq.
         destruct (a + imm)%a; cbn; last done.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&?&_); done.
     }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [| Hfail].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. congruence.
     }
     by iApply "Hφ".
  Qed.

  Lemma wp_load_fail_not_withinbounds_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) :
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e ea = false →
    (a + imm)%a = Some ea →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
     iIntros (Hdecode Hvpc Hbounds Hadd Hcnull φ) "(>HPC & >Hi & >Hsrc & >Hdst) Hφ".
     iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
     rewrite memMap_resource_1_dq.
     iApply (wp_load_imm with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto.
     { by rewrite !dom_insert; set_solver+. }
     { rewrite /allow_load_map_or_true_imm.
       exists true, p, g, b, e, a.
       split.
       + rewrite /read_reg_inr; by simplify_map_eq.
       + rewrite /reg_allows_load_imm; simplify_map_eq.
         try rewrite Hadd.
         rewrite decide_False; first done.
         rewrite Hbounds.
         intros (_&_&_&?); done.
     }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.
     destruct Hspec as [| Hfail].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq). congruence.
     }
     by iApply "Hφ".
  Qed.

  Lemma wp_load_success_PC_imm E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    decodeInstrW w = Load PC r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e ea = true →
    (a + imm)%a = Some ea →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ ▷ ea ↦ₐ WCap t p' g' b' e' a' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ load_word p (WCap t p' g' b' e' a'')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ ea ↦ₐ WCap t p' g' b' e' a' }}}.
  Proof.
    iIntros (Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map_imm with (a := a) (ea := ea) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H1 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite insert_insert_eq insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr2]"; eauto.
       iFrame.
       by destruct p0; destruct dro,dl; rewrite /load_word in H1 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
       all: match goal with H : incrementPC _ = None |- _ =>
         rewrite /load_word in H end.
       all: destruct (isDRO p0) eqn:HDRO, (isDL p0) eqn:HDL; cbn.
       all: try incrementPC_inv; simplify_map_eq; eauto; try congruence.
     }
  Qed.

  Lemma wp_load_fail_addr_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs p g b e a :
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some (WCap true p g b e a) →
    (a + imm)%a = None →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hsrc Hadd φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[Hr Hsr] Hm] /=".
    destruct σ1 as [[r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
    { rewrite Hadd /= in Hstep. by simplify_pair_eq. }
    cbn; iFrame; iApply "Hφ"; iFrame. done.
  Qed.

  Lemma wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a
      w dst src (imm : Z) regs wa :
    decodeInstrW w = Load dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !!ᵣ src = Some wa →
    is_cap wa = false →
    {{{ ▷ pc_a ↦ₐ w ∗ ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET FailedV; pc_a ↦ₐ w ∗ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Hsrc Htag φ) "(>Hpc_a & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[Hr Hsr] Hm] /=".
    destruct σ1 as [[r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->).
    { destruct wa as [| [t p g b e a|] | |]; cbn in Htag;
        by simplify_pair_eq. }
    cbn; iFrame; iApply "Hφ"; iFrame. done.
  Qed.

  Lemma wp_load_fail_not_cap_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' wsrc (imm : Z) :
    decodeInstrW w = Load r1 r2 imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    is_cap wsrc = false ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ r2 ↦ᵣ wsrc
    }}}
       Instr Executable @ E
       {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hcap φ) "(>HPC & >Hi & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hdst Hsrc") as "[Hmap (%&%&%)]".
    iApply (wp_load_fail_const_imm E pc_p pc_g pc_b pc_e pc_a w r1 r2 imm _ (if decide (r2 = cnull) then WInt 0 else wsrc) with "[$Hi $Hmap]"); eauto; simplify_map_eq; eauto.
    { case_decide; done. }
    iNext. iIntros "_". by iApply "Hφ".
  Qed.

  Lemma wp_load_success_fromPC_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' ea (imm : Z) pc_a' dq dq' :
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ (if (ea =? pc_a)%a then emp else ▷ ea ↦ₐ{dq'} w') }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ (if (ea =? pc_a)%a then load_word pc_p w else load_word pc_p w')
             ∗ pc_a ↦ₐ{dq} w
             ∗ (if (ea =? pc_a)%a then emp else ea ↦ₐ{dq'} w') }}}.
  Proof.
    iIntros (Hinstr Hvpc Hwb Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    assert (readAllowed pc_p = true) as Hra.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc. apply andb_prop_elim in Hpc as [Hra _]. by apply Is_true_true. }
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hpc_a Ha]".
       {iExists mem,dfracs; iSplitL; auto. }
       incrementPC_inv.
       pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem H1) as Hloadv; eauto.
       simplify_map_eq.
       rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
       iDestruct (regs_of_map_2 with "[$Hmap]") as "[HPC Hr1]"; eauto. iFrame.
       by repeat case_match.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
     }
  Qed.

  Lemma wp_load_success_PC_PC_imm E pc_p pc_g pc_b pc_e pc_a w
        ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    decodeInstrW w = Load PC PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (a' + 1)%a = Some a'' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ ea ↦ₐ WCap t p' g' b' e' a' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ load_word pc_p (WCap t p' g' b' e' a'')
             ∗ pc_a ↦ₐ w
             ∗ ea ↦ₐ WCap t p' g' b' e' a' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hwb Hadd Hpca' φ)
            "(>HPC & >Hi & >Hr2a) Hφ".
    assert (readAllowed pc_p = true) as Hra.
    { apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra _]. by apply Is_true_true. }
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { eapply mem_neq_implies_allow_load_map_imm with (a := pc_a) (ea := ea) (pc_a := pc_a); eauto.
    }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | * Hfail ].
     { (* Success *)
       iApply "Hφ".
       destruct H0 as (Hrr2 & Hea & _). simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq).
       iDestruct (memMap_resource_2ne with "Hmem") as "[Hpc_a Ha]";auto.
       incrementPC_inv.
       simplify_map_eq.
       rewrite !insert_insert_eq.
       iDestruct (regs_of_map_1 with "Hmap") as "HPC".
       iFrame.
       by destruct p; destruct dro,dl; rewrite /load_word in H0 |- *; cbn in *; simplify_eq.
     }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; try congruence.
       all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
       all: match goal with H : incrementPC _ = None |- _ =>
         rewrite /load_word in H end.
       all: destruct (isDRO p) eqn:HDRO, (isDL p) eqn:HDL; cbn.
       all: try incrementPC_inv; simplify_map_eq; eauto; try congruence.
     }
  Qed.

  Lemma wp_load_success_fromPC_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' ea (imm : Z) pc_a' dq dq' :
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds pc_b pc_e ea = true →
    (pc_a + imm)%a = Some ea →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ ea ↦ₐ{dq'} w' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ r1 ↦ᵣ load_word pc_p w'
             ∗ pc_a ↦ₐ{dq} w
             ∗ ea ↦ₐ{dq'} w' }}}.
  Proof.
    iIntros (Hinstr Hvpc Hwb Hadd Hincr Hnull φ) "(>HPC & >Hi & >Hr & >Hm) Hφ".
    destruct (ea =? pc_a)%a eqn:Heq.
    - apply Z.eqb_eq, finz_to_z_eq in Heq. subst ea.
      iDestruct (pointsto_agree with "Hi Hm") as %->.
      iApply (wp_load_success_fromPC_imm with "[$HPC $Hi $Hr]"); eauto.
      { rewrite Z.eqb_refl. done. }
      iNext. iIntros "(HPC & Hr & Hi & _)". rewrite Z.eqb_refl.
      iApply "Hφ". iFrame.
    - iApply (wp_load_success_fromPC_imm with "[$HPC $Hi $Hr Hm]"); eauto.
      { rewrite Heq. iFrame. }
      iNext. iIntros "(HPC & Hr & Hi & Hm)". rewrite Heq.
      iApply "Hφ". iFrame.
    Unshelve. all: first [exact (WInt 0) | exact DfracDiscarded].
  Qed.

  Lemma wp_load_success_fromPC_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' dq (imm : Z) :
    decodeInstrW w = Load r1 PC imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + imm)%a = Some pc_a →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w'' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r1 ↦ᵣ load_word pc_p w }}}.
  Proof.
    iIntros (Hinstr Hvpc Hadd Hincr Hnull φ) "(>HPC & >Hi & >Hr) Hφ".
    assert (withinBounds pc_b pc_e pc_a = true) as Hwb.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc.
      apply andb_prop_elim in Hpc as [_ Hwb]. by apply Is_true_true. }
    iApply (wp_load_success_fromPC_imm with "[$HPC $Hi $Hr]"); eauto.
    { rewrite Z.eqb_refl. done. }
    iNext. iIntros "(HPC & Hr & Hi & _)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame.
    Unshelve. all: first [exact (WInt 0) | exact DfracDiscarded].
  Qed.

End griotte_lang_rules.
