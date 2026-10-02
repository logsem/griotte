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

  Definition reg_allows_load (regs : Reg) (r : RegName) p g b e a  :=
    regs !!ᵣ r = Some (WCap true p g b e a) ∧
    readAllowed p = true ∧ withinBounds b e a = true.

  Inductive Load_failure_spec (regs: Reg) (r1 r2: RegName) (imm : Z)
    (mem : gmap Addr Word) (shadow : ShadowTbl) :=
  | Load_fail_const w:
      regs !!ᵣ r2 = Some w ->
      is_cap w = false →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_tag p g b e a:
      regs !!ᵣ r2 = Some (WCap false p g b e a) →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_bounds p g b e a:
      imm = 0%Z →
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (readAllowed p = false ∨ withinBounds b e a = false) →
      Load_failure_spec regs r1 r2 imm mem shadow
  (* Loading a non-capability into PC also makes incrementPC fail. *)
  | Load_fail_invalid_PC p g b e a loadv:
      imm = 0%Z →
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      is_shadow_address a = false →
      mem !! a = Some loadv →
      incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs) = None ->
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_invalid_PC_shadow p g b e a heap_a revoked:
      imm = 0%Z →
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      is_shadow_address a = true →
      shadow_to_heap a = Some heap_a →
      shadow !! heap_a = Some revoked →
      incrementPC (<[ r1 := WInt (encodeAllocStatus revoked) ]ᵣ> regs) = None →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_invalid_PC_revoked p g b e a raw base:
      imm = 0%Z →
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      is_shadow_address a = false →
      mem !! a = Some raw →
      heap_cap_base raw = Some base →
      shadow !! base ≠ Some ShadowLive →
      incrementPC (<[ r1 := clear_tag (load_word p raw) ]ᵣ> regs) = None →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_missing_shadow p g b e a raw base:
      imm = 0%Z →
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      is_shadow_address a = false →
      mem !! a = Some raw →
      heap_cap_base raw = Some base →
      shadow !! base = None →
      Load_failure_spec regs r1 r2 imm mem shadow
    | Load_fail_const_imm w:
      regs !!ᵣ r2 = Some w ->
      is_cap w = false →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_tag_imm p g b e a:
      regs !!ᵣ r2 = Some (WCap false p g b e a) →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_addr_imm p g b e a:
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = None →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_bounds_imm p g b e a ea:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      (readAllowed p = false ∨ withinBounds b e ea = false) →
      Load_failure_spec regs r1 r2 imm mem shadow
  (* Notice how the None below also includes all cases where we read an inl value into the PC, because then incrementing it will fail *)
  | Load_fail_invalid_PC_imm p g b e a ea loadv:
      regs !!ᵣ r2 = Some (WCap true p g b e a) ->
      (a + imm)%a = Some ea →
      is_shadow_address ea = false →
      mem !! ea = Some loadv →
      incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs) = None ->
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_invalid_PC_shadow_imm p g b e a ea heap_a revoked:
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = Some ea →
      is_shadow_address ea = true →
      shadow_to_heap ea = Some heap_a →
      shadow !! heap_a = Some revoked →
      incrementPC (<[r1 := WInt (encodeAllocStatus revoked)]ᵣ> regs) = None →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_invalid_PC_revoked_imm p g b e a ea raw base:
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = Some ea →
      is_shadow_address ea = false →
      mem !! ea = Some raw →
      heap_cap_base raw = Some base →
      shadow !! base ≠ Some ShadowLive →
      incrementPC (<[r1 := clear_tag (load_word p raw)]ᵣ> regs) = None →
      Load_failure_spec regs r1 r2 imm mem shadow
  | Load_fail_missing_shadow_imm p g b e a ea raw base:
      regs !!ᵣ r2 = Some (WCap true p g b e a) →
      (a + imm)%a = Some ea →
      is_shadow_address ea = false →
      mem !! ea = Some raw →
      heap_cap_base raw = Some base →
      shadow !! base = None →
      Load_failure_spec regs r1 r2 imm mem shadow
  .

  Definition reg_allows_load_offset (regs : Reg) (r : RegName)
      (imm : Z) p g b e (ea : Addr) : Prop :=
    match imm with
    | 0%Z => reg_allows_load regs r p g b e ea
    | _ => ∃ a, reg_allows_load_imm regs r imm p g b e a ea
    end.

  Lemma reg_allows_load_offset_imm regs r imm p g b e ea :
    reg_allows_load_offset regs r imm p g b e ea →
    ∃ a, reg_allows_load_imm regs r imm p g b e a ea.
  Proof.
    destruct imm as [|imm|imm]; simpl.
    - intros (Hreg & Hra & Hwb). exists ea. repeat split; auto.
      by rewrite finz_add_0.
    - exact (λ H, H).
    - exact (λ H, H).
  Qed.

  Lemma reg_allows_load_imm_offset regs r imm p g b e a ea :
    reg_allows_load_imm regs r imm p g b e a ea →
    reg_allows_load_offset regs r imm p g b e ea.
  Proof.
    destruct imm as [|imm|imm]; simpl; intros Hallow;
      try (by exists a).
    destruct Hallow as (Hreg & Hadd & Hra & Hwb).
    rewrite finz_add_0 in Hadd. inversion Hadd; subst ea.
    repeat split; auto.
  Qed.

  Inductive Load_spec
    (regs: Reg) (r1 r2: RegName) (imm : Z)
    (regs': Reg) (mem : gmap Addr Word) (shadow : ShadowTbl) : griotte_lang.val → Prop
  :=
  | Load_spec_success p g b e a loadv :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = false →
    mem !! a = Some loadv →
    is_heap_cap loadv = false →
    incrementPC
      (<[ r1 := (load_word p loadv) ]ᵣ> regs) = Some regs' ->
    Load_spec regs r1 r2 imm regs' mem shadow NextIV

  | Load_spec_success_cap_nonheap p g b e a (t' : bool) p' g' b' e' a' :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = false →
    mem !! a = Some (WCap t' p' g' b' e' a') →
    is_heap_address b' = false →
    incrementPC
      (<[ r1 := (load_word p (WCap t' p' g' b' e' a')) ]ᵣ> regs) = Some regs' →
    Load_spec regs r1 r2 imm regs' mem shadow NextIV

  | Load_spec_success_cap_heap p g b e a raw base :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = false →
    mem !! a = Some raw →
    heap_cap_base raw = Some base →
    shadow !! base ≠ Some ShadowQuarantined →
    incrementPC
      (<[ r1 := (load_word p raw) ]ᵣ> regs) = Some regs' →
    Load_spec regs r1 r2 imm regs' mem shadow NextIV

  | Load_spec_success_cap_revoked p g b e a raw base :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = false →
    mem !! a = Some raw →
    heap_cap_base raw = Some base →
    shadow !! base ≠ Some ShadowLive →
    incrementPC (<[ r1 := clear_tag (load_word p raw) ]ᵣ> regs) = Some regs' →
    Load_spec regs r1 r2 imm regs' mem shadow NextIV

  | Load_spec_success_shadow p g b e a heap_a revoked :
    reg_allows_load_offset regs r2 imm p g b e a →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some revoked →
    incrementPC
      (<[ r1 := WInt (encodeAllocStatus revoked) ]ᵣ> regs) = Some regs' →
    Load_spec regs r1 r2 imm regs' mem shadow NextIV

  | Load_spec_failure :
    Load_failure_spec regs r1 r2 imm mem shadow ->
    Load_spec regs r1 r2 imm regs' mem shadow FailedV.

  Lemma Load_spec_success_imm regs r1 r2 imm regs' mem p g b e a ea loadv :
    reg_allows_load_imm regs r2 imm p g b e a ea →
    mem !! ea = Some loadv →
    incrementPC
      (<[ r1 := (load_word p loadv) ]ᵣ> regs) = Some regs' ->
    ((∃ p g b e a ea loadv,
      NextIV = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (<[r1 := load_word p loadv]ᵣ> regs) = Some regs') ∨
    (NextIV = FailedV ∧ ∃ fail : Load_failure_spec regs r1 r2 imm mem ∅, True)).
  Proof.
    intros Hallow Hmem Hincr. left.
    exists p, g, b, e, a, ea, loadv.
    exact (conj eq_refl (conj Hallow (conj Hmem Hincr))).
  Qed.

  Lemma Load_spec_failure_imm regs r1 r2 imm regs' mem :
    Load_failure_spec regs r1 r2 imm mem ∅ ->
    ((∃ p g b e a ea loadv,
      FailedV = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (<[r1 := load_word p loadv]ᵣ> regs) = Some regs') ∨
    (FailedV = FailedV ∧ ∃ fail : Load_failure_spec regs r1 r2 imm mem ∅, True)).
  Proof. intros Hfail. right. split; first done. by exists Hfail. Qed.

  Ltac iFailLoadImm Hcont fail_case_name :=
    by (cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
      eapply Load_spec_failure_imm; eapply fail_case_name; eauto).

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
   (∀ p g b e a ea loadv,
      reg_allows_load_imm regs r2 imm p g b e a ea → mem !! ea = Some loadv →
      is_shadow_address ea = false ∧ is_heap_cap loadv = false) →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (<[r1 := load_word p loadv]ᵣ> regs) = Some regs') ∨
    (retv = FailedV ∧ ∃ fail : Load_failure_spec regs r1 r2 imm mem ∅, True))⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hordinary Hdomeq φ) "(>Hmem & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[[[Hr Hsr] Hm] Hst] Hmmio] /=". destruct σ1 as [ [ [r sr] m] st]; cbn.
    iDestruct "Hmmio" as %Hmmio.
    iAssert (⌜mem_avoids_mmio m⌝)%I as "-#Hmmio"; first by iPureIntro.
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
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       {
         unfold is_cap in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailLoadImm "Hφ" Load_fail_const_imm.
     }
     destruct r2v as [ | [t p g b e a | ] | | ]; try inversion Hr2v. clear Hr2v.
     destruct t.
     2: {
       inversion Hstep; subst c σ2.
       iFailLoadImm "Hφ" Load_fail_tag_imm.
     }

    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { inversion Hstep; subst c σ2. iFailLoadImm "Hφ" Load_fail_addr_imm. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iFailLoadImm "Hφ" Load_fail_bounds_imm.
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

    destruct (Hordinary p g b e a ea loadv Hallow Hmema) as [Hshadow Hheap].
    rewrite Hshadow (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hma') Hma' /= in Hstep.
    assert (Hstep' :
      (match updatePC (update_reg (r, sr, m, st) r1 (load_word p loadv)) with
       | Some conf => conf | None => (Failed, (r, sr, m, st)) end) = (c, σ2)).
    { unfold is_heap_cap in Hheap.
      destruct (heap_cap_base loadv) as [base|] eqn:Hbase; cbn in Hheap;
        first discriminate.
      exact Hstep. }
    clear Hstep. rename Hstep' into Hstep.
    destruct (incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
    2: { (* Failure: the PC could not be incremented correctly *)
      assert (incrementPC (<[ r1 := (load_word p loadv) ]ᵣ> r) = None).
      { eapply incrementPC_overflow_mono; first eapply Hregs'.
          + simplify_map_eq; by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto. }

      rewrite incrementPC_fail_updatePC /= in Hstep; auto.
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
      iFailLoadImm "Hφ" Load_fail_invalid_PC_imm.
    }

    (* Success *)
    rewrite /update_reg /= in Hstep.
    eapply (incrementPC_success_updatePC _ sr m st) in Hregs'
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
   (∀ p g b e a ea loadv,
      reg_allows_load_imm regs r2 imm p g b e a ea → mem !! ea = Some loadv →
      is_shadow_address ea = false ∧ is_heap_cap loadv = false) →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs r2 imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (<[r1 := load_word p loadv]ᵣ> regs) = Some regs') ∨
    (retv = FailedV ∧ ∃ fail : Load_failure_spec regs r1 r2 imm mem ∅, True))⌝ ∗
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

  Definition allow_load_map_or_true r (regs : Reg) (mem : gmap Addr Word):=
    ∃ t p g b e a, read_reg_inr regs r t p g b e a ∧
      if decide (reg_allows_load regs r p g b e a) then
        ∃ w, mem !! a = Some w
      else True.

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

  (* Own the source location. Revocation entries may be untracked: a tracked
     bit rules out the opposite result, while an untracked bit allows either
     result or failure if the concrete entry is missing. *)
  Definition allow_load_mem_or_shadow (r : RegName) (regs : Reg)
    (mem : Mem) (shadow : ShadowTbl) :=
    ∀ p g b e a,
      reg_allows_load regs r p g b e a →
      if is_shadow_address a then
        ∃ heap_a, shadow_to_heap a = Some heap_a ∧ is_Some (shadow !! heap_a)
      else ∃ loadv, mem !! a = Some loadv.

  Definition load_word_unrevoked (shadow : ShadowTbl) (loadv : Word) : Prop :=
    match heap_cap_base loadv with
    | Some base => shadow !! base = Some ShadowLive
    | None => True
    end.

  Lemma not_heap_cap_load_word_unrevoked shadow loadv :
    is_heap_cap loadv = false → load_word_unrevoked shadow loadv.
  Proof.
    rewrite /is_heap_cap /load_word_unrevoked.
    by destruct (heap_cap_base loadv).
  Qed.

  Lemma decode_load_not_heap_cap_imm w dst src imm :
    decodeInstrW w = Load dst src imm → is_heap_cap w = false.
  Proof. destruct w; cbn; try discriminate; done. Qed.

  Lemma decode_load_not_heap_cap w dst src :
    decodeInstrW w = Load dst src 0 → is_heap_cap w = false.
  Proof. exact (decode_load_not_heap_cap_imm w dst src 0). Qed.

  Lemma decode_load_unrevoked shadow w dst src :
    decodeInstrW w = Load dst src 0 → load_word_unrevoked shadow w.
  Proof. destruct w; cbn; try discriminate; done. Qed.

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

  Lemma wp_load_success_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w') = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull' φ)
            "(>HPC & >Hi & >Hr1 & >Hr2 & Hr2a) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr2a") as (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hdfracs].

    iApply (wp_load_general_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0.
      simplify_map_eq.
      split; first done.
      pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem Hlookup0) as ->. exact Hheap. }
    { destruct (ea =? pc_a)%a; simplify_eq. all: rewrite !dom_insert_L;set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H2 & H3 & Hinc0) | (-> & (Hfail & _))].
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
       all: try (match goal with H : (_ + 0)%a = None |- _ =>
         rewrite finz_add_0 in H; discriminate end).
       all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
         rewrite finz_add_0 in H; simplify_eq end).
       all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
       1: { pose proof (mem_implies_loadv pc_a w w' ea mem raw Hmem e4) as Hraw.
         subst raw. unfold is_heap_cap in Hheap.
         rewrite e5 in Hheap. discriminate. }
       pose proof (mem_implies_loadv pc_a w w' ea mem raw Hmem e4) as Hraw.
       subst raw. unfold is_heap_cap in Hheap.
       rewrite e5 in Hheap. discriminate.
     }
  Qed.

  Lemma wp_load_success_same_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w') = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc Hra Hwb Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & Hr1a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Hr1a") as
        (mem dfracs) "[>Hmem Hmem']".
    iDestruct "Hmem'" as %[Hmem Hfracs].

    iApply (wp_load_general_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { destruct (ea =? pc_a)%a; by simplify_map_eq. }
    { eapply mem_implies_allow_load_map_imm; eauto. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0.
      simplify_map_eq. split; first done.
      pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem Hlookup0) as ->. exact Hheap. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H0 & H1 & Hinc0) | (-> & (Hfail & _))].
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
       all: try (match goal with H : (_ + 0)%a = None |- _ =>
         rewrite finz_add_0 in H; discriminate end).
       all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
         rewrite finz_add_0 in H; simplify_eq end).
       all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
       1: { pose proof (mem_implies_loadv pc_a w w' ea mem raw Hmem e4) as Hraw.
         subst raw. unfold is_heap_cap in Hheap.
         rewrite e5 in Hheap. discriminate. }
       pose proof (mem_implies_loadv pc_a w w' ea mem raw Hmem e4) as Hraw.
       subst raw. unfold is_heap_cap in Hheap.
       rewrite e5 in Hheap. discriminate.
     }
  Qed.

  Lemma wp_load_success_notinstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap w' = false →
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
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Ha)".
    destruct (ea =? pc_a)%Z eqn:Ha.
    - rewrite (_: ea = pc_a); cycle 1.
      { apply Z.eqb_eq in Ha. solve_addr. }
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
      { apply Z.eqb_eq,finz_to_z_eq in Ha. subst ea. by rewrite Z.eqb_refl. }
      { by rewrite Ha. }
      iNext. iIntros "(? & ? & ? & ? & ?)".
      iApply "Hφ".
      rewrite Ha.
      iFrame.
    - iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2 Ha]"); eauto.
      { by rewrite Ha. }
      { rewrite Ha. iFrame. }
      iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Ha.
      iApply "Hφ". iFrame.
      Unshelve.
      + apply DfracDiscarded.
      + apply (WInt 0).
  Qed.

  Lemma wp_load_success_frominstr_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e a (imm : Z) pc_a' dq :
    is_shadow_address pc_a = false →
    is_heap_cap w = false →
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
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Hr2)".
    iIntros "Hφ". iApply (wp_load_success_imm with "[$HPC $Hpc_a $Hr1 $Hr2]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    { by rewrite Z.eqb_refl. }
    iNext. iIntros "(? & ? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_same_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap w' = false →
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
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1 & >Ha)".
    destruct (ea =? pc_a)%a eqn:Ha.
    { assert (ea = pc_a) as Heqa.
      { apply Z.eqb_eq in Ha. solve_addr. }
      rewrite Heqa. subst ea.
      iDestruct (pointsto_agree with "Hpc_a Ha") as %->.
      iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1]"); eauto.
      { rewrite Ha; done. }
      { by rewrite Ha. }
      iNext. iIntros "(? & ? & ? & ?)".
      iApply "Hφ". iFrame. rewrite Ha. iFrame.
    }
    iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1 Ha]"); eauto.
    { by rewrite Ha. }
    { rewrite Ha. iFrame. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Ha.
    iApply "Hφ". iFrame.
    Unshelve.
    + apply (WInt 0).
    + apply DfracDiscarded.
  Qed.

  Lemma wp_load_success_same_frominstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w p g b e a (imm : Z) pc_a' dq :
    is_shadow_address pc_a = false →
    is_heap_cap w = false →
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
    intros Hshadow Hheap. intros. iIntros "(>HPC & >Hpc_a & >Hr1)".
    iIntros "Hφ". iApply (wp_load_success_same_imm with "[$HPC $Hpc_a $Hr1]"); eauto.
    { rewrite Z.eqb_refl. eauto. }
    { by rewrite Z.eqb_refl. }
    iNext. iIntros "(? & ? & ? & ?)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame. Unshelve. all: eauto.
  Qed.

  Lemma wp_load_success_alt_imm E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a ea (imm : Z) pc_a' :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w') = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull Hcnull' φ) "(>HPC & >Hi & >Hr1 & >Hr2 & >Hr2a) Hφ".
    iAssert (⌜(ea =? pc_a)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iDestruct (address_neq with "Hr2a Hi") as %Hneq. iIntros (->%finz_to_z_eq). done. }
    iApply (wp_load_success_imm with "[$HPC $Hi $Hr1 $Hr2 Hr2a]");eauto;rewrite Hfalse;iFrame.
  Qed.

  Lemma wp_load_success_same_alt_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a ea (imm : Z) pc_a' :
    is_shadow_address ea = false →
    is_heap_cap (if (ea =? pc_a)%a then w else w') = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull φ) "(>HPC & >Hpc_a & >Hr1 & >Ha) Hφ".
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
    iIntros (σ1 ns l1 l2 nt) "[[[[Hr Hsr] Hm] Hst] Hmmio] /=".
    destruct σ1 as [[[r sr] m] st]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
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
     iApply (wp_load_imm with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto;
       try solve [intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & Hra0 & Hwb0) Hlookup0;
         simplify_map_eq; congruence].
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
     destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H2 & Hmem0 & Hinc0) | (-> & (Hfail & _))].
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
     iApply (wp_load_imm with "[$Hmap $Hi]"); eauto; simplify_map_eq; eauto;
       try solve [intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & Hra0 & Hwb0) Hlookup0;
         simplify_map_eq; congruence].
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
     destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H2 & Hmem0 & Hinc0) | (-> & (Hfail & _))].
     {
       destruct H2 as (Hreg & Hea & Hra & Hwb).
       simplify_map_eq. try (rewrite Hadd in Hea; simplify_eq). congruence.
     }
     by iApply "Hφ".
  Qed.

  Lemma wp_load_success_PC_imm E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    is_shadow_address ea = false →
    is_heap_cap (WCap t p' g' b' e' a') = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hadd Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0;
        simplify_map_eq; split; assumption].
    { by rewrite !dom_insert; set_solver+. }
    { eapply mem_neq_implies_allow_load_map_imm with (a := a) (ea := ea) (pc_a := pc_a); eauto.
      by simplify_map_eq. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H1 & Hmem0 & Hinc0) | (-> & (Hfail & _))].
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
       all: try (match goal with H : (_ + 0)%a = None |- _ =>
         rewrite finz_add_0 in H; discriminate end).
       all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
         rewrite finz_add_0 in H; simplify_eq end).
       all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
       all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
       all: try (match goal with H : incrementPC _ = None |- _ =>
         rewrite /load_word in H end).
       all: destruct (isDRO p0) eqn:HDRO, (isDL p0) eqn:HDL; cbn.
       all: try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       all: try (unfold is_heap_cap in Hheap;
         match goal with Hbase : heap_cap_base _ = Some _ |- _ =>
           rewrite Hbase in Hheap end; discriminate).
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
    iIntros (σ1 ns l1 l2 nt) "[[[[Hr Hsr] Hm] Hst] Hmmio] /=".
    destruct σ1 as [[[r sr] m] st]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
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
    iIntros (σ1 ns l1 l2 nt) "[[[[Hr Hsr] Hm] Hst] Hmmio] /=".
    destruct σ1 as [[[r sr] m] st]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    have Hsrc' := lookup_reg_weaken _ _ _ _ Hsrc Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_". iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hsrc' /= in Hstep.
    assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
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
    is_shadow_address ea = false →
    is_heap_cap w' = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc Hwb Hadd Hpca' Hcnull φ)
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
    { intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0.
      simplify_map_eq. split; first done.
      pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem Hlookup0) as ->.
      case_match; last exact Hheap.
      destruct w; cbn in Hinstr |- *; try discriminate; done. }
    { destruct (ea =? pc_a)%a; by set_solver. }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p0 & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H0 & H1 & Hinc0) | (-> & (Hfail & _))].
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
       all: try (match goal with H : (_ + 0)%a = None |- _ =>
         rewrite finz_add_0 in H; discriminate end).
       all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
         rewrite finz_add_0 in H; simplify_eq end).
       all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
       all: try incrementPC_inv; simplify_map_eq; eauto.
       all: try congruence.
       all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
       1: { pose proof (mem_implies_loadv _ _ _ _ _ _ Hmem e3) as Hraw.
         rewrite Z.eqb_refl in Hraw. subst raw.
         pose proof (decode_load_not_heap_cap w r1 PC Hinstr) as Hwi.
         unfold is_heap_cap in Hwi. rewrite e4 in Hwi. discriminate. }
       pose proof (mem_implies_loadv a w w' ea mem raw Hmem e3) as Hraw.
       subst raw. destruct (ea =? a)%a eqn:Heq.
       - pose proof (decode_load_not_heap_cap_imm w r1 PC imm Hinstr) as Hwi.
         unfold is_heap_cap in Hwi. rewrite e4 in Hwi. discriminate.
       - unfold is_heap_cap in Hheap. rewrite e4 in Hheap. discriminate.
     }
  Qed.

  Lemma wp_load_success_PC_PC_imm E pc_p pc_g pc_b pc_e pc_a w
        ea (imm : Z) (t : bool) p' g' b' e' a' a'' :
    is_shadow_address ea = false →
    is_heap_cap (WCap t p' g' b' e' a') = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc Hwb Hadd Hpca' φ)
            "(>HPC & >Hi & >Hr2a) Hφ".
    assert (readAllowed pc_p = true) as Hra.
    { apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra _]. by apply Is_true_true. }
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iApply (wp_load_imm with "[$Hmap $Hmem]"); eauto; simplify_map_eq; eauto;
      try solve [intros p0 g0 b0 e0 a0 ea0 v0 (Hsrc0 & Hadd0 & _) Hlookup0;
        simplify_map_eq; split; assumption].
    { eapply mem_neq_implies_allow_load_map_imm with (a := pc_a) (ea := ea) (pc_a := pc_a); eauto.
    }
    iNext. iIntros (regs' retv) "(#Hspec & Hmem & Hmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [(p & g0 & b0 & e0 & a0 & ea0 & loadv & -> & H0 & Hmem0 & Hinc0) | (-> & (Hfail & _))].
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
       all: try (match goal with H : (_ + 0)%a = None |- _ =>
         rewrite finz_add_0 in H; discriminate end).
       all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
         rewrite finz_add_0 in H; simplify_eq end).
       all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
       all: try match goal with H : _ ∨ _ |- _ => destruct H; congruence end.
       all: try (match goal with H : incrementPC _ = None |- _ =>
         rewrite /load_word in H end).
       all: destruct (isDRO p) eqn:HDRO, (isDL p) eqn:HDL; cbn.
       all: try incrementPC_inv; simplify_map_eq; eauto; try congruence.
       all: try (unfold is_heap_cap in Hheap;
         match goal with Hbase : heap_cap_base _ = Some _ |- _ =>
           rewrite Hbase in Hheap end; discriminate).
     }
  Qed.

  Lemma wp_load_success_fromPC_notinstr_imm E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' ea (imm : Z) pc_a' dq dq' :
    is_shadow_address ea = false →
    is_heap_cap w' = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc Hwb Hadd Hincr Hnull φ) "(>HPC & >Hi & >Hr & >Hm) Hφ".
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
    is_shadow_address pc_a = false →
    is_heap_cap w = false →
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
    iIntros (Hshadow Hheap Hinstr Hvpc Hadd Hincr Hnull φ) "(>HPC & >Hi & >Hr) Hφ".
    assert (withinBounds pc_b pc_e pc_a = true) as Hwb.
    { pose proof (isCorrectPC_ra_wb _ _ _ _ _ _ Hvpc) as Hpc.
      apply andb_prop_elim in Hpc as [_ Hwb]. by apply Is_true_true. }
    iApply (wp_load_success_fromPC_imm with "[$HPC $Hi $Hr]"); eauto.
    { rewrite Z.eqb_refl. done. }
    iNext. iIntros "(HPC & Hr & Hi & _)". rewrite Z.eqb_refl.
    iApply "Hφ". iFrame.
    Unshelve. all: first [exact (WInt 0) | exact DfracDiscarded].
  Qed.

  Definition allow_load_mem_or_shadow_offset (r : RegName) (imm : Z)
      (regs : Reg) (mem : Mem) (shadow : ShadowTbl) :=
    ∀ p g b e ea,
      reg_allows_load_offset regs r imm p g b e ea →
      if is_shadow_address ea then
        ∃ heap_a, shadow_to_heap ea = Some heap_a ∧ is_Some (shadow !! heap_a)
      else ∃ loadv, mem !! ea = Some loadv.

  Lemma allow_load_mem_or_shadow_offset_zero r regs mem shadow :
    allow_load_mem_or_shadow r regs mem shadow →
    allow_load_mem_or_shadow_offset r 0 regs mem shadow.
  Proof. exact (λ H, H). Qed.

  Ltac iFailLoadOffset Hcont fail_case_name :=
    by (cbn; iFrame; iApply Hcont; iFrame; iPureIntro;
      eapply Load_spec_failure; eapply fail_case_name; eauto).

  Lemma wp_load_general_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs shadow sdq :
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_mem_or_shadow_offset r2 imm regs mem shadow →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 imm regs' mem shadow retv⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq φ)
      "(>Hmem & >Hshadow & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [ [ [Hr Hsr] Hm ] Hst ] Hmmio ] /=".
    destruct σ1 as [ [ [r sr] m] st]; cbn.
    iDestruct "Hmmio" as %Hmmio.
    iAssert (⌜mem_avoids_mmio m⌝)%I as "-#Hmmio"; first by iPureIntro.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    pose proof (lookup_weaken _ _ _ _ HPC Hregs) as HPCr.
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.
    odestruct (Hri r2) as [r2v [Hr'2 Hr2]]; first by set_solver+.
    odestruct (Hri r1) as [r1v [Hr'1 _]]; first by set_solver+.
    clear Hri.
    iAssert (⌜∀ a loadv, mem !! a = Some loadv → m !! a = Some loadv⌝)%I as %Hmem_valid.
    { iIntros (a loadv Hlookup).
      assert (is_Some (dfracs !! a)) as [dq Hdq].
      { apply elem_of_dom. rewrite -Hdomeq. apply elem_of_dom; eauto. }
      iApply (gen_mem_valid_inSepM_general (prod_merge dfracs mem) with "Hm Hmem").
      by rewrite lookup_merge Hlookup Hdq. }
    iAssert (⌜∀ a revoked, shadow !! a = Some revoked → st !! a = Some revoked⌝)%I as %Hshadow_valid.
    { iIntros (a revoked Hlookup).
      iDestruct (big_sepM_lookup with "Hshadow") as "Ha"; first exact Hlookup.
      iApply (gen_heap_valid with "Hst Ha"). }
    pose proof (Hmem_valid _ _ Hmem_pc) as Hma.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= Hr2 /= in Hstep.
    destruct (is_cap r2v) eqn:Hr2v.
    2: {
      assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
      { unfold is_cap in Hr2v. destruct_word r2v; by simplify_pair_eq. }
      iFailLoadOffset "Hφ" Load_fail_const.
    }
    destruct r2v as [ | [t p g b e a | ] | | ]; try inversion Hr2v. clear Hr2v.
    destruct t.
    2: { inversion Hstep; subst c σ2. iFailLoadOffset "Hφ" Load_fail_tag. }
    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { inversion Hstep; subst c σ2. iFailLoadOffset "Hφ" Load_fail_addr_imm. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2: {
      simplify_pair_eq. apply andb_false_iff in HRA.
      iFailLoadOffset "Hφ" Load_fail_bounds_imm.
    }
    apply andb_true_iff in HRA as [Hra Hwb].
    assert (Hallow : reg_allows_load_offset regs r2 imm p g b e ea).
    { apply reg_allows_load_imm_offset with (a := a). repeat split; auto. }
    specialize (HaLoad p g b e ea Hallow).

    (* Classify the read before performing the shared register update. *)
    assert (Hread :
      (c = Failed ∧ σ2 = (r, sr, m, st) ∧
        Load_spec regs r1 r2 imm regs mem shadow FailedV) ∨
      ∃ loadv,
        (match updatePC (update_reg (r, sr, m, st) r1 loadv) with
         | Some conf => conf
         | None => (Failed, (r, sr, m, st))
         end = (c, σ2)) ∧
        (∀ regs', incrementPC (<[r1:=loadv]ᵣ> regs) = Some regs' →
          Load_spec regs r1 r2 imm regs' mem shadow NextIV) ∧
        (incrementPC (<[r1:=loadv]ᵣ> regs) = None →
          Load_spec regs r1 r2 imm regs mem shadow FailedV)).
    {
      destruct (is_shadow_address ea) eqn:Hshadow.
      - destruct HaLoad as (heap_a & Htranslate & revoked & Hlookup).
        rewrite Htranslate /= in Hstep.
        rewrite (Hshadow_valid _ _ Hlookup) /= in Hstep.
        right. exists (WInt (encodeAllocStatus revoked)).
        repeat split; eauto 12 using Load_spec_failure, Load_spec_success_shadow, Load_fail_invalid_PC_shadow_imm.
      - destruct HaLoad as (loadv & Hlookup).
        rewrite (mem_avoids_mmio_not_revoker _ _ _ Hmmio (Hmem_valid _ _ Hlookup)) in Hstep.
        rewrite (Hmem_valid _ _ Hlookup) /= in Hstep.
        destruct (heap_cap_base loadv) as [base|] eqn:Hbase.
        + destruct (st !! base) as [status|] eqn:Hlookup_shadow; cbn in Hstep.
            2: {
              assert (shadow !! base = None) as Hmissing.
              { destruct (shadow !! base) as [status|] eqn:Hbit; last done.
                pose proof (Hshadow_valid _ _ Hbit). congruence. }
              left. simplify_pair_eq. repeat split.
              eauto using Load_spec_failure, Load_fail_missing_shadow_imm.
            }
            destruct status.
            -- assert (shadow !! base ≠ Some ShadowQuarantined) as Hbit.
               { intros Hbit. pose proof (Hshadow_valid _ _ Hbit). congruence. }
               right. exists (load_word p loadv).
               repeat split; eauto 12 using Load_spec_failure, Load_spec_success_cap_heap, Load_fail_invalid_PC_imm.
            -- assert (shadow !! base ≠ Some ShadowLive) as Hbit.
               { intros Hbit. pose proof (Hshadow_valid _ _ Hbit). congruence. }
               right. exists (clear_tag (load_word p loadv)).
               repeat split; eauto 12 using Load_spec_failure, Load_spec_success_cap_revoked, Load_fail_invalid_PC_revoked_imm.
        + right. exists (load_word p loadv).
          assert (Hnonheap : is_heap_cap loadv = false).
          { by rewrite /is_heap_cap Hbase. }
          repeat split; eauto 12 using Load_spec_failure, Load_spec_success, Load_fail_invalid_PC_imm.
    }

    destruct Hread as [(-> & -> & Hfailure)|(loadv & Hloadstep & Hsuccess & Hfailure)].
    { cbn; iFrame. iApply "Hφ". iFrame. done. }
    clear Hstep. rename Hloadstep into Hstep.
    rewrite /update_reg /= in Hstep.
    destruct (incrementPC (<[r1:=loadv]ᵣ> regs)) as [regs'|] eqn:Hregs'.
    2: {
      assert (incrementPC (<[r1:=loadv]ᵣ> r) = None) as Hfail.
      { eapply incrementPC_overflow_mono; first exact Hregs'.
        - simplify_map_eq; by rewrite lookup_insert_is_Some'; eauto.
        - by apply insert_mono. }
      rewrite incrementPC_fail_updatePC /= in Hstep; auto.
      simplify_pair_eq. cbn; iFrame. iApply "Hφ". iFrame.
      iPureIntro. by apply Hfailure.
    }
    pose proof (Hsuccess _ eq_refl) as Hspec.
    eapply (incrementPC_success_updatePC _ sr m st) in Hregs'
      as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl with (sregs':=sr) (m':=m) (shadow':=st) in HuPC.
    2: by eapply insert_mono.
    rewrite HuPC in Hstep. simplify_pair_eq. cbn.
    iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame. done.
  Qed.

  Lemma wp_load_general Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 w mem (dfracs : gmap Addr dfrac) regs shadow sdq :
   decodeInstrW w = Load r1 r2 0 →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 0) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_mem_or_shadow r2 regs mem shadow →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ Load_spec regs r1 r2 0 regs' mem shadow retv⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hdomeq.
    eapply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a
      r1 r2 0 w mem dfracs regs shadow sdq); eauto.
  Qed.

  (* A load from ordinary memory without ownership of the revocation bit.
     A missing shadow entry may fail; a successful read returns either the
     ordinary loaded word or its tag-cleared form. *)
  Lemma wp_load Ep pc_p pc_g pc_b pc_e pc_a
    dst src w mem regs dq :
    decodeInstrW w = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Load dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    allow_load_map_or_true src regs mem →
    (∀ p g b e a, reg_allows_load regs src p g b e a →
      is_shadow_address a = false) →
    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜(match retv with
    | NextIV => ∃ p g b e a loadv actualv,
        reg_allows_load regs src p g b e a ∧
        mem !! a = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end)⌝ ∗
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hnonshadow φ)
      "(Hmem & Hmap) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general_shadow_imm Ep pc_p pc_g pc_b pc_e pc_a dst src 0 w
      mem _ regs ∅ DfracDiscarded with "[$Hmem $Hmap]"); eauto.
    { intros p g b e a Hallow. rewrite (Hnonshadow _ _ _ _ _ Hallow).
      destruct Hallow as (Hsrc & Hra & Hwb).
      eapply allow_load_implies_loadv; eauto. }
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & _ & Hmap)".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply "Hφ". iFrame. iPureIntro.
    inversion Hspec; subst; simplify_map_eq; eauto 12.
  Qed.

  (* Ordinary-memory loads consult the shadow table only for heap capabilities. *)
  Lemma wp_load_success_mem E pc_p pc_g pc_b pc_e pc_a
    dst src w regs regs' mem dfracs shadow sdq p g b e a loadv :
    decodeInstrW w = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Load dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load regs src p g b e a →
    is_shadow_address a = false →
    mem !! a = Some loadv →
    load_word_unrevoked shadow loadv →
    dom mem = dom dfracs →
    incrementPC (<[dst:=load_word p loadv]ᵣ> regs) = Some regs' →
    {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem Hallow Hshadow Hlookup Hrev Hdom Hinc φ)
      "(>Hmem & >Hshadow & >Hmap) Hφ".
    iApply (wp_load_general with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      destruct Hallow as (Hsrc & _). simplify_eq.
      rewrite Hshadow. by exists loadv. }
    iNext. iIntros (regs0 retv) "(%Hspec & Hmem & Hshadow & Hmap)".
    destruct Hallow as (Hsrc & Hra & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 v0 (Hsrc0 & _) Hshadow0 Hlookup0 Hcap Hinc0
      |p0 g0 b0 e0 a0 t1 p1 g1 b1 e1 a1 (Hsrc0 & _) Hshadow0 Hlookup0 Hheap Hinc0
      |p0 g0 b0 e0 a0 raw base (Hsrc0 & _) Hshadow0 Hlookup0 Hheap Hbit Hinc0
      |p0 g0 b0 e0 a0 raw base (Hsrc0 & _) Hshadow0 Hlookup0 Hheap Hbit Hinc0
      |p0 g0 b0 e0 a0 heap_a0 revoked (Hsrc0 & _) Hshadow0
      |Hfail]; simplify_eq; try congruence.
    1-3: iApply "Hφ"; iFrame.
    { unfold load_word_unrevoked in Hrev. rewrite Hheap in Hrev.
      congruence. }
    destruct Hfail; simplify_eq; try congruence.
    all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
    all: try (match goal with H : (_ + 0)%a = None |- _ =>
      rewrite finz_add_0 in H; discriminate end).
    all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
      rewrite finz_add_0 in H; simplify_eq end).
    all: try (unfold load_word_unrevoked, is_heap_cap in Hrev;
      match goal with Hbase : heap_cap_base _ = Some _ |- _ =>
        rewrite Hbase in Hrev end; congruence).
    all: try congruence.
    all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
  Qed.

  (* Loads that do not require shadow-table ownership. *)
  Lemma wp_load_success E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    is_shadow_address a = false →
    is_heap_cap (if (a =? pc_a)%a then w else w') = false →
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
    intros Hshadow Hheap Hinstr Hvpc Hbounds Hpc Hdst Hsrc.
    eapply wp_load_success_imm; eauto.
    by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_notinstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    is_shadow_address a = false →
    is_heap_cap w' = false →
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
    intros.
    eapply wp_load_success_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (** Without shadow ownership, a load may fail or clear the loaded tag,
      in addition to the permission transformation performed by [load_word]. *)
  Lemma wp_load_preserve_or_clear E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src wi wd p g b e a raw :
    readAllowed p = true ->
    is_shadow_address a = false ->
    decodeInstrW wi = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true p g b e a ∗ a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ retv, RET retv; ⌜retv = FailedV⌝ ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗
        ⌜actual = load_word p raw ∨
          (is_heap_cap raw = true ∧ actual = clear_tag (load_word p raw))⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true p g b e a ∗ a ↦ₐ raw }}}.
  Proof.
    iIntros (Hread Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    destruct (is_heap_cap raw) eqn:Hheap; cycle 1.
    { iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply "Hφ". iRight. iExists (load_word p raw). iFrame.
      iPureIntro. split; first done. by left. }
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load E pc_p pc_g pc_b pc_e pc_a dst src wi with "[$Hmap $Hmem]");
      eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { exists true, p, g, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - case_decide; last done. exists raw. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      simpl_map_regs by eauto. simplify_map_eq. done. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct retv; simpl in Hspec; [contradiction|iApply "Hφ"; by iLeft|].
    destruct Hspec as (p0 & g0 & b0 & e0 & a0 & loadv & actual &
      Hallow & Hlookup & Hactual & Hinc).
    destruct Hallow as (Hsrc0 & _). simpl_map_regs by eauto. simplify_map_eq.
    unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
    rewrite (insert_insert_ne _ dst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iApply "Hφ". iRight. iExists actual. iFrame.
    iPureIntro. split; first done.
    destruct Hactual as [-> | ->]; [by left|right; done].
  Qed.

  Lemma wp_load_success_frominstr E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'' p g b e pc_a' dq :
    is_shadow_address pc_a = false →
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
    intros.
    eapply wp_load_success_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    is_shadow_address a = false →
    is_heap_cap (if (a =? pc_a)%a then w else w') = false →
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
    intros.
    eapply wp_load_success_same_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_notinstr E r1 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' dq dq' :
    is_shadow_address a = false →
    is_heap_cap w' = false →
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
    intros.
    eapply wp_load_success_same_notinstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma wp_load_success_same_frominstr E r1 pc_p pc_g pc_b pc_e pc_a w p g b e pc_a' dq :
    is_shadow_address pc_a = false →
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
    intros.
    eapply wp_load_success_same_frominstr_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (* If a points to a capability, the load into PC success if its address can be incr *)
  Lemma wp_load_success_PC E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a (t' : bool) p' g' b' e' a' a'' :
    is_shadow_address a = false →
    is_heap_address b' = false →
    decodeInstrW w = Load PC r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ ▷ a ↦ₐ WCap t' p' g' b' e' a' }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ load_word p (WCap t' p' g' b' e' a'')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ a ↦ₐ WCap t' p' g' b' e' a' }}}.
  Proof.
    intros.
    eapply wp_load_success_PC_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
    all: try by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    all: try (destruct (a =? pc_a)%a; eauto using decode_load_not_heap_cap).
    all: by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= H0.
  Qed.

  Lemma wp_load_success_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' dq :
    is_shadow_address pc_a = false →
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
    iIntros (Hshadow Hinstr Hvpc Hpc Hnull Φ) "(>HPC & >Hi & >Hr1) HΦ".
    iApply (wp_load_success_fromPC_imm E r1 pc_p pc_g pc_b pc_e pc_a
      w w w'' pc_a 0 pc_a' dq dq with "[$HPC $Hi $Hr1]"); eauto.
    - exact (decode_load_not_heap_cap w r1 PC Hinstr).
    - apply isCorrectPC_ra_wb in Hvpc.
      apply andb_prop_elim in Hvpc as [_ Hwb].
      apply Is_true_eq_true in Hwb. apply andb_true_iff in Hwb as [Hle Hlt].
      apply withinBounds_true_iff. solve_addr.
    - by rewrite finz_add_0.
    - by rewrite Z.eqb_refl.
    - iNext. iIntros "(HPC & Hr1 & Hi & _)".
      rewrite Z.eqb_refl. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_success_alt E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' w'' p g b e a pc_a' :
    is_shadow_address a = false →
    is_heap_cap w' = false →
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
    intros.
    eapply wp_load_success_alt_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
    all: try by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    all: try (destruct (a =? pc_a)%a; eauto using decode_load_not_heap_cap).
  Qed.

  Lemma wp_load_success_same_alt E r1 pc_p pc_g pc_b pc_e pc_a w w' p g b e a pc_a' :
    is_shadow_address a = false →
    is_heap_cap w' = false →
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
    intros.
    eapply wp_load_success_same_alt_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
    all: try by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
    all: try (destruct (a =? pc_a)%a; eauto using decode_load_not_heap_cap).
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
    intros.
    eapply wp_load_fail_not_cap_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
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
    intros.
    eapply wp_load_fail_not_ra_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
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
    intros.
    eapply wp_load_fail_not_withinbounds_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  (* Reading a shadow-table entry returns its Boolean value as an integer. *)
  Lemma wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a
    dst src w regs regs' mem dq shadow sdq p g b e a heap_a revoked :
    decodeInstrW w = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Load dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load regs src p g b e a →
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    shadow !! heap_a = Some revoked →
    incrementPC (<[dst:=WInt (encodeAllocStatus revoked)]ᵣ> regs) = Some regs' →
    {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
        ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem Hallow Hshadow Htranslate Hlookup Hinc φ)
      "(>Hmem & >Hshadow & >Hmap) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_general with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      destruct Hallow as (Hsrc & _). simplify_eq.
      rewrite Hshadow. exists heap_a. split; first done. by eexists. }
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (regs0 retv) "(%Hspec & Hmem & Hshadow & Hmap)".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    destruct Hallow as (Hsrc & Hra & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 v0 (Hsrc0 & _) Hshadow0
      |p0 g0 b0 e0 a0 t1 p1 g1 b1 e1 a1 (Hsrc0 & _) Hshadow0
      |p0 g0 b0 e0 a0 raw base (Hsrc0 & _) Hshadow0
      |p0 g0 b0 e0 a0 raw base (Hsrc0 & _) Hshadow0
      |p0 g0 b0 e0 a0 heap_a0 revoked0 (Hsrc0 & _) Hshadow0 Htranslate0 Hlookup0 Hinc0
      |Hfail]; simplify_eq; try congruence.
    - rewrite Hlookup in Hlookup0. simplify_eq. iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; try congruence.
      all: try (match goal with H : (_ + 0)%a = None |- _ =>
        rewrite finz_add_0 in H; discriminate end).
      all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
        rewrite finz_add_0 in H; simplify_eq end).
      all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
      all: try (match goal with H : ?tbl !! _ = Some _ |- _ =>
        rewrite Hlookup in H; simplify_eq end).
      all: try congruence.
  Qed.

  Lemma wp_load_success_from_shadow E r1 r2 pc_p pc_g pc_b pc_e pc_a w w' p g b e a pc_a' heap_a revoked dq sdq :
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ WCap true p g b e a
        ∗ ▷ heap_a ↦ₛ{sdq} revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ r1 ↦ᵣ WInt (encodeAllocStatus revoked)
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ WCap true p g b e a
        ∗ heap_a ↦ₛ{sdq} revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    rewrite memMap_resource_1_dq.
    iAssert ([∗ map] a0↦bit ∈ {[heap_a:=revoked]}, a0 ↦ₛ{sdq} bit)%I
      with "[Ha]" as "Hshadow"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a r1 r2 w _ _ _ dq _ sdq p g b e a heap_a revoked
      with "[$Hi $Hmap $Hshadow]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hi & Ha & Hmap)".
    rewrite -memMap_resource_1_dq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hr1 & Hr2)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_from_shadow_same E r1 pc_p pc_g pc_b pc_e pc_a w p g b e a pc_a' heap_a revoked dq sdq :
    is_shadow_address a = true →
    shadow_to_heap a = Some heap_a →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ{dq} w

        ∗ ▷ r1 ↦ᵣ WCap true p g b e a
        ∗ ▷ heap_a ↦ₛ{sdq} revoked }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ r1 ↦ᵣ WInt (encodeAllocStatus revoked)
        ∗ pc_a ↦ₐ{dq} w

        ∗ heap_a ↦ₛ{sdq} revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc [Hra Hwb] Hpca' Hcnull φ)
      "(>HPC & >Hi & >Hr1 & >Ha) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iAssert ([∗ map] a0↦bit ∈ {[heap_a:=revoked]}, a0 ↦ₛ{sdq} bit)%I
      with "[Ha]" as "Hshadow"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a r1 r1 w _ _ _ dq _ sdq p g b e a heap_a revoked
      with "[$Hi $Hmap $Hshadow]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hi & Ha & Hmap)".
    rewrite -memMap_resource_1_dq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(HPC & Hr1)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  (* Non-revoked heap capabilities use the usual load_word transformation. *)
  Lemma wp_load_success_heap E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'
    p g b e a (t' : bool) p' g' b' e' a' pc_a' dq dq' sdq :
    is_shadow_address a = false →
    is_heap_address b' = true →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ WCap true p g b e a
        ∗ ▷ a ↦ₐ{dq'} WCap t' p' g' b' e' a'
        ∗ ▷ b' ↦ₛ{sdq} ShadowLive }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ r1 ↦ᵣ load_word p (WCap t' p' g' b' e' a')
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ WCap true p g b e a
        ∗ a ↦ₐ{dq'} WCap t' p' g' b' e' a'
        ∗ b' ↦ₛ{sdq} ShadowLive }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha & >Hs) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    destruct (a =? pc_a)%a eqn:Heq.
    { apply Z.eqb_eq, finz_to_z_eq in Heq. subst a.
      iDestruct (pointsto_agree with "Hi Ha") as %->. discriminate. }
    iAssert (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} WCap t' p' g' b' e' a')%I
      with "[Ha]" as "Ha"; first by rewrite Heq; iFrame.
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Ha") as (mem dfracs) "[>Hmem %Hmaps]".
    destruct Hmaps as [Hmem Hdfracs].
    iAssert ([∗ map] a0↦bit ∈ {[b':=ShadowLive]}, a0 ↦ₛ{sdq} bit)%I
      with "[Hs]" as "Hs"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_mem E pc_p pc_g pc_b pc_e pc_a r1 r2 w _ _ mem dfracs
      {[b':=ShadowLive]} sdq p g b e a (WCap t' p' g' b' e' a')
      with "[$Hmap $Hmem $Hs]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { rewrite Heq in Hmem. by simplify_map_eq. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { rewrite Heq in Hmem. simplify_map_eq.
      rewrite lookup_insert_ne; last by intros ->; rewrite Z.eqb_refl in Heq.
      by simplify_map_eq. }
    { rewrite /load_word_unrevoked /heap_cap_base /memory_cap_base /= Hheap.
      by simplify_map_eq. }
    { rewrite Heq in Hmem, Hdfracs. simplify_eq. rewrite !dom_insert_L; set_solver+. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hs & Hmap)".
    iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hi Ha]".
    { iExists mem, dfracs; iSplitL; auto. }
    rewrite Heq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hr1 & Hr2)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_heap_same E r1 pc_p pc_g pc_b pc_e pc_a w
    p g b e a (t' : bool) p' g' b' e' a' pc_a' dq dq' sdq :
    is_shadow_address a = false →
    is_heap_address b' = true →
    decodeInstrW w = Load r1 r1 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ{dq} w

        ∗ ▷ r1 ↦ᵣ WCap true p g b e a
        ∗ ▷ a ↦ₐ{dq'} WCap t' p' g' b' e' a'
        ∗ ▷ b' ↦ₛ{sdq} ShadowLive }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ r1 ↦ᵣ load_word p (WCap t' p' g' b' e' a')
        ∗ pc_a ↦ₐ{dq} w

        ∗ a ↦ₐ{dq'} WCap t' p' g' b' e' a'
        ∗ b' ↦ₛ{sdq} ShadowLive }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull φ)
      "(>HPC & >Hi & >Hr1 & >Ha & >Hs) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    destruct (a =? pc_a)%a eqn:Heq.
    { apply Z.eqb_eq, finz_to_z_eq in Heq. subst a.
      iDestruct (pointsto_agree with "Hi Ha") as %->. discriminate. }
    iAssert (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} WCap t' p' g' b' e' a')%I
      with "[Ha]" as "Ha"; first by rewrite Heq; iFrame.
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Ha") as (mem dfracs) "[>Hmem %Hmaps]".
    destruct Hmaps as [Hmem Hdfracs].
    iAssert ([∗ map] a0↦bit ∈ {[b':=ShadowLive]}, a0 ↦ₛ{sdq} bit)%I
      with "[Hs]" as "Hs"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_mem E pc_p pc_g pc_b pc_e pc_a r1 r1 w _ _ mem dfracs
      {[b':=ShadowLive]} sdq p g b e a (WCap t' p' g' b' e' a')
      with "[$Hmap $Hmem $Hs]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { rewrite Heq in Hmem. by simplify_map_eq. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { rewrite Heq in Hmem. simplify_map_eq.
      rewrite lookup_insert_ne; last by intros ->; rewrite Z.eqb_refl in Heq.
      by simplify_map_eq. }
    { rewrite /load_word_unrevoked /heap_cap_base /memory_cap_base /= Hheap.
      by simplify_map_eq. }
    { rewrite Heq in Hmem, Hdfracs. simplify_eq. rewrite !dom_insert_L; set_solver+. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hs & Hmap)".
    iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hi Ha]".
    { iExists mem, dfracs; iSplitL; auto. }
    rewrite Heq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "(HPC & Hr1)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_heap_PC E r2 pc_p pc_g pc_b pc_e pc_a w
        p g b e a (t' : bool) p' g' b' e' a' a'' sdq :
    is_shadow_address a = false →
    is_heap_address b' = true →
    decodeInstrW w = Load PC r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (a' + 1)%a = Some a'' →
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ w
          ∗ ▷ r2 ↦ᵣ WCap true p g b e a
          ∗ ▷ a ↦ₐ WCap t' p' g' b' e' a'
          ∗ ▷ b' ↦ₛ{sdq} ShadowLive }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ load_word p (WCap t' p' g' b' e' a'')
             ∗ pc_a ↦ₐ w
             ∗ r2 ↦ᵣ WCap true p g b e a
             ∗ a ↦ₐ WCap t' p' g' b' e' a'
             ∗ b' ↦ₛ{sdq} ShadowLive }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr2 & >Hr2a & >Hs) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr2") as "[Hmap %]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hr2a") as "[Hmem %]"; auto.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iAssert ([∗ map] a0↦bit ∈ {[b':=ShadowLive]}, a0 ↦ₛ{sdq} bit)%I
      with "[Hs]" as "Hs"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_mem E pc_p pc_g pc_b pc_e pc_a PC r2 w _ (<[PC:=load_word p (WCap t' p' g' b' e' a'')]> (<[r2:=WCap true p g b e a]> ∅)) _ _ {[b':=ShadowLive]} sdq p g b e a (WCap t' p' g' b' e' a')
      with "[$Hmap $Hmem $Hs]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_load. split; first by simplify_map_eq.
      auto. }
    { rewrite /load_word_unrevoked /heap_cap_base /memory_cap_base /= Hheap.
      by simplify_map_eq. }
    { rewrite create_gmap_default_dom list_to_set_elements_L. done. }
    { rewrite /incrementPC /incrementPC_gen /load_word.
      destruct (isDRO p), (isDL p); cbn; simplify_map_eq; by rewrite !insert_insert_eq. }
    iNext. iIntros "(Hmem & Hs & Hmap)".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hr]"; eauto.
    rewrite big_sepM_singleton. iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_from_shadow_fromPC E r1 pc_p pc_g pc_b pc_e pc_a pc_a' w w'' heap_a revoked dq sdq :
    is_shadow_address pc_a = true →
    shadow_to_heap pc_a = Some heap_a →
    decodeInstrW w = Load r1 PC 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
          ∗ ▷ pc_a ↦ₐ{dq} w
          ∗ ▷ r1 ↦ᵣ w''
          ∗ ▷ heap_a ↦ₛ{sdq} revoked }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
             ∗ pc_a ↦ₐ{dq} w
             ∗ r1 ↦ᵣ WInt (encodeAllocStatus revoked)
             ∗ heap_a ↦ₛ{sdq} revoked }}}.
  Proof.
    iIntros (Hshadow Htranslate Hinstr Hvpc Hpca' Hcnull φ)
            "(>HPC & >Hi & >Hr1 & >Hs) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hr1") as "[Hmap %]".
    rewrite memMap_resource_1_dq.
    iAssert ([∗ map] a0↦bit ∈ {[heap_a:=revoked]}, a0 ↦ₛ{sdq} bit)%I
      with "[Hs]" as "Hs"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_shadow E pc_p pc_g pc_b pc_e pc_a r1 PC w _ _ _ dq _ sdq pc_p pc_g pc_b pc_e pc_a heap_a revoked
      with "[$Hmap $Hi $Hs]"); eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { unfold reg_allows_load. split; first by simplify_map_eq.
      apply isCorrectPC_ra_wb in Hvpc. apply andb_prop_elim in Hvpc as [Hra Hwb].
      split; by apply Is_true_true. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hi & Hs & Hmap)".
    rewrite -memMap_resource_1_dq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_2 with "Hmap") as "[HPC Hr]"; eauto.
    iApply "Hφ". iFrame.
  Qed.


  (* Revocation clears the validity tag after the ordinary load transformation. *)
  Lemma wp_load_success_mem_revoked E pc_p pc_g pc_b pc_e pc_a
    dst src w regs regs' mem dfracs shadow sdq p g b e a (t' : bool) p' g' b' e' a' :
    decodeInstrW w = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Load dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load regs src p g b e a →
    is_shadow_address a = false →
    mem !! a = Some (WCap t' p' g' b' e' a') →
    is_heap_address b' = true →
    shadow !! b' = Some ShadowQuarantined →
    dom mem = dom dfracs →
    incrementPC (<[dst:=clear_tag (load_word p (WCap t' p' g' b' e' a'))]ᵣ> regs) = Some regs' →
    {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem Hallow Hshadow Hlookup Hheap Hbit Hdom Hinc φ)
      "(>Hmem & >Hshadow & >Hmap) Hφ".
    iApply (wp_load_general with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      destruct Hallow as (Hsrc & _). simplify_eq.
      rewrite Hshadow. by exists (WCap t' p' g' b' e' a'). }
    iNext. iIntros (regs0 retv) "(%Hspec & Hmem & Hshadow & Hmap)".
    destruct Hallow as (Hsrc & Hra & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 v0 (Hsrc0 & _) Hshadow0 Hlookup0 Hcap Hinc0
      |p0 g0 b0 e0 a0 t1 p1 g1 b1 e1 a1 (Hsrc0 & _) Hshadow0 Hlookup0 Hheap0 Hinc0
      |p0 g0 b0 e0 a0 raw base (Hsrc0 & _) Hshadow0 Hlookup0 Hheap0 Hbit0 Hinc0
      |p0 g0 b0 e0 a0 raw base (Hsrc0 & _) Hshadow0 Hlookup0 Hheap0 Hbit0 Hinc0
      |p0 g0 b0 e0 a0 heap_a0 revoked (Hsrc0 & _) Hshadow0
      |Hfail]; simplify_eq; try congruence.
    - rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hheap in Hcap.
      discriminate.
    - rewrite /heap_cap_base /memory_cap_base /= Hheap in Hheap0.
      simplify_eq.
    - iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; try congruence.
      all: try (match goal with H : (_ + 0)%a = None |- _ =>
        rewrite finz_add_0 in H; discriminate end).
      all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
        rewrite finz_add_0 in H; simplify_eq end).
      all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
      all: try (match goal with H : heap_cap_base _ = Some _ |- _ =>
        rewrite /heap_cap_base /memory_cap_base /= Hheap in H;
        simplify_eq end).
      all: try (match goal with H : ?tbl !! ?addr = None |- _ =>
        rewrite Hbit in H; discriminate end).
      all: try (match goal with H : incrementPC _ = None |- _ =>
        unfold incrementPC, incrementPC_gen in Hinc, H;
        destruct (decide (dst = PC)) as [->|Hdst]; simplify_map_eq;
        [destruct (load_word p (WCap t' p' g' b' e' a')) as
          [z|[t0 p0 g0 b0 e0 a0|t0 p0 g0 b0 e0 a0]|ot sb|i];
          cbn in Hinc, H; try discriminate;
          destruct (a0 + 1)%a; discriminate
        |destruct (pc_a + 1)%a; discriminate] end).
      all: try congruence.
  Qed.

  Lemma wp_load_success_heap_revoked E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'
    p g b e a (t' : bool) p' g' b' e' a' pc_a' dq dq' sdq :
    is_shadow_address a = false →
    is_heap_address b' = true →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ WCap true p g b e a
        ∗ ▷ a ↦ₐ{dq'} WCap t' p' g' b' e' a'
        ∗ ▷ b' ↦ₛ{sdq} ShadowQuarantined }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ r1 ↦ᵣ clear_tag (load_word p (WCap t' p' g' b' e' a'))
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ WCap true p g b e a
        ∗ a ↦ₐ{dq'} WCap t' p' g' b' e' a'
        ∗ b' ↦ₛ{sdq} ShadowQuarantined }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha & >Hs) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    destruct (a =? pc_a)%a eqn:Heq.
    { apply Z.eqb_eq, finz_to_z_eq in Heq. subst a.
      iDestruct (pointsto_agree with "Hi Ha") as %->. discriminate. }
    iAssert (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} WCap t' p' g' b' e' a')%I
      with "[Ha]" as "Ha"; first by rewrite Heq; iFrame.
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Ha") as (mem dfracs) "[>Hmem %Hmaps]".
    destruct Hmaps as [Hmem Hdfracs].
    iAssert ([∗ map] a0↦bit ∈ {[b':=ShadowQuarantined]}, a0 ↦ₛ{sdq} bit)%I
      with "[Hs]" as "Hs"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_mem_revoked E pc_p pc_g pc_b pc_e pc_a r1 r2 w _ _ mem dfracs
      {[b':=ShadowQuarantined]} sdq p g b e a (t' : bool) p' g' b' e' a'
      with "[$Hmap $Hmem $Hs]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { rewrite Heq in Hmem. by simplify_map_eq. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { rewrite Heq in Hmem. simplify_map_eq.
      rewrite lookup_insert_ne; last by intros ->; rewrite Z.eqb_refl in Heq.
      by simplify_map_eq. }
    { by simplify_map_eq. }
    { rewrite Heq in Hmem, Hdfracs. simplify_eq. rewrite !dom_insert_L; set_solver+. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hs & Hmap)".
    iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hi Ha]".
    { iExists mem, dfracs; iSplitL; auto. }
    rewrite Heq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hr1 & Hr2)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_heap_word E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'
    p g b e a (raw : Word) (base : Addr) pc_a' dq dq' sdq :
    is_shadow_address a = false →
    heap_cap_base raw = Some base →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ WCap true p g b e a
        ∗ ▷ a ↦ₐ{dq'} raw
        ∗ ▷ base ↦ₛ{sdq} ShadowLive }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ r1 ↦ᵣ load_word p raw
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ WCap true p g b e a
        ∗ a ↦ₐ{dq'} raw
        ∗ base ↦ₛ{sdq} ShadowLive }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha & >Hs) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    destruct (a =? pc_a)%a eqn:Heq.
    { apply Z.eqb_eq, finz_to_z_eq in Heq. subst a.
      iDestruct (pointsto_agree with "Hi Ha") as %->.
      destruct raw as [z | sb | ot sb | ins]; try discriminate.
      all: by inversion Hinstr. }
    iAssert (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} raw)%I
      with "[Ha]" as "Ha"; first by rewrite Heq; iFrame.
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Ha") as (mem dfracs) "[>Hmem %Hmaps]".
    destruct Hmaps as [Hmem Hdfracs].
    iAssert ([∗ map] a0↦bit ∈ {[base:=ShadowLive]}, a0 ↦ₛ{sdq} bit)%I
      with "[Hs]" as "Hs"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_mem E pc_p pc_g pc_b pc_e pc_a r1 r2 w _ _ mem dfracs
      {[base:=ShadowLive]} sdq p g b e a raw
      with "[$Hmap $Hmem $Hs]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { rewrite Heq in Hmem. by simplify_map_eq. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { rewrite Heq in Hmem. simplify_map_eq.
      rewrite lookup_insert_ne; last by intros ->; rewrite Z.eqb_refl in Heq.
      by simplify_map_eq. }
    { rewrite /load_word_unrevoked Hheap.
      by simplify_map_eq. }
    { rewrite Heq in Hmem, Hdfracs. simplify_eq. rewrite !dom_insert_L; set_solver+. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hs & Hmap)".
    iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hi Ha]".
    { iExists mem, dfracs; iSplitL; auto. }
    rewrite Heq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hr1 & Hr2)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

  Lemma wp_load_success_mem_word_revoked E pc_p pc_g pc_b pc_e pc_a
    dst src w regs regs' mem dfracs shadow sdq p g b e a raw base :
    decodeInstrW w = Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Load dst src 0) ⊆ dom regs →
    mem !! pc_a = Some w →
    reg_allows_load regs src p g b e a →
    is_shadow_address a = false →
    mem !! a = Some raw →
    heap_cap_base raw = Some base →
    shadow !! base = Some ShadowQuarantined →
    dom mem = dom dfracs →
    incrementPC (<[dst:=clear_tag (load_word p raw)]ᵣ> regs) = Some regs' →
    {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        (▷ [∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
        ([∗ map] a↦revoked ∈ shadow, a ↦ₛ{sdq} revoked) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem Hallow Hshadow Hlookup Hheap Hbit Hdom Hinc φ)
      "(>Hmem & >Hshadow & >Hmap) Hφ".
    iApply (wp_load_general with "[$Hmem $Hshadow $Hmap]"); eauto.
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      destruct Hallow as (Hsrc & _). simplify_eq.
      rewrite Hshadow. by exists raw. }
    iNext. iIntros (regs0 retv) "(%Hspec & Hmem & Hshadow & Hmap)".
    destruct Hallow as (Hsrc & Hra & Hwb).
    destruct Hspec as
      [p0 g0 b0 e0 a0 v0 (Hsrc0 & _) Hshadow0 Hlookup0 Hcap Hinc0
      |p0 g0 b0 e0 a0 t1 p1 g1 b1 e1 a1 (Hsrc0 & _) Hshadow0 Hlookup0 Hheap0 Hinc0
      |p0 g0 b0 e0 a0 raw0 base0 (Hsrc0 & _) Hshadow0 Hlookup0 Hheap0 Hbit0 Hinc0
      |p0 g0 b0 e0 a0 raw0 base0 (Hsrc0 & _) Hshadow0 Hlookup0 Hheap0 Hbit0 Hinc0
      |p0 g0 b0 e0 a0 heap_a0 revoked (Hsrc0 & _) Hshadow0
      |Hfail]; simplify_eq; try congruence.
    - rewrite /is_heap_cap Hheap in Hcap.
      discriminate.
    - rewrite /heap_cap_base /memory_cap_base /= Hheap0 in Hheap.
      discriminate.
    - iApply "Hφ". iFrame.
    - destruct Hfail; simplify_eq; try congruence.
      all: try (match goal with H : (_ + 0)%a = None |- _ =>
        rewrite finz_add_0 in H; discriminate end).
      all: try (match goal with H : (_ + 0)%a = Some _ |- _ =>
        rewrite finz_add_0 in H; simplify_eq end).
      all: try (match goal with H : _ ∨ _ |- _ => destruct H; congruence end).
      all: try (match goal with H : ?tbl !! ?addr = None |- _ =>
        rewrite Hbit in H; discriminate end).
      all: try (match goal with H : incrementPC _ = None |- _ =>
        unfold incrementPC, incrementPC_gen in Hinc, H;
        destruct (decide (dst = PC)) as [->|Hdst]; simplify_map_eq;
        [destruct (load_word p raw) as
          [z|[t0 p0 g0 b0 e0 a0|t0 p0 g0 b0 e0 a0]|ot sb|i];
          cbn in Hinc, H; try discriminate;
          destruct (a0 + 1)%a; discriminate
        |destruct (pc_a + 1)%a; discriminate] end).
      all: try congruence.
  Qed.

  Lemma wp_load_success_heap_word_revoked E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'
    p g b e a (raw : Word) (base : Addr) pc_a' dq dq' sdq :
    is_shadow_address a = false →
    heap_cap_base raw = Some base →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ WCap true p g b e a
        ∗ ▷ a ↦ₐ{dq'} raw
        ∗ ▷ base ↦ₛ{sdq} ShadowQuarantined }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ r1 ↦ᵣ clear_tag (load_word p raw)
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ WCap true p g b e a
        ∗ a ↦ₐ{dq'} raw
        ∗ base ↦ₛ{sdq} ShadowQuarantined }}}.
  Proof.
    iIntros (Hshadow Hheap Hinstr Hvpc [Hra Hwb] Hpca' Hcnull Hcnull' φ)
      "(>HPC & >Hi & >Hr1 & >Hr2 & >Ha & >Hs) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    destruct (a =? pc_a)%a eqn:Heq.
    { apply Z.eqb_eq, finz_to_z_eq in Heq. subst a.
      iDestruct (pointsto_agree with "Hi Ha") as %->.
      destruct raw as [z | sb | ot sb | ins]; try discriminate.
      all: by inversion Hinstr. }
    iAssert (if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} raw)%I
      with "[Ha]" as "Ha"; first by rewrite Heq; iFrame.
    iDestruct (memMap_resource_2gen_clater_dq _ _ _ _ _ _ (λ a dq w, a ↦ₐ{dq} w)%I with "Hi Ha") as (mem dfracs) "[>Hmem %Hmaps]".
    destruct Hmaps as [Hmem Hdfracs].
    iAssert ([∗ map] a0↦bit ∈ {[base:=ShadowQuarantined]}, a0 ↦ₛ{sdq} bit)%I
      with "[Hs]" as "Hs"; first by rewrite big_sepM_singleton.
    iApply (wp_load_success_mem_word_revoked E pc_p pc_g pc_b pc_e pc_a r1 r2 w _ _ mem dfracs
      {[base:=ShadowQuarantined]} sdq p g b e a raw base
      with "[$Hmap $Hmem $Hs]"); eauto.
    { by simplify_map_eq. }
    { by rewrite !dom_insert; set_solver+. }
    { rewrite Heq in Hmem. by simplify_map_eq. }
    { unfold reg_allows_load. split; first by simplify_map_eq. auto. }
    { rewrite Heq in Hmem. simplify_map_eq.
      rewrite lookup_insert_ne; last by intros ->; rewrite Z.eqb_refl in Heq.
      by simplify_map_eq. }
    { by simplify_map_eq. }
    { rewrite Heq in Hmem, Hdfracs. simplify_eq. rewrite !dom_insert_L; set_solver+. }
    { by rewrite /incrementPC /incrementPC_gen; simplify_map_eq. }
    iNext. iIntros "(Hmem & Hs & Hmap)".
    iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hi Ha]".
    { iExists mem, dfracs; iSplitL; auto. }
    rewrite Heq big_sepM_singleton.
    rewrite (insert_insert_ne _ PC r1) // insert_insert_eq (insert_insert_ne _ r1 PC) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hr1 & Hr2)"; eauto.
    iApply "Hφ". iFrame.
  Qed.

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
    intros.
    eapply wp_load_fail_tag_imm; eauto using decode_load_not_heap_cap.
    all: try by rewrite finz_add_0.
  Qed.

  Lemma Load_memory_success_imm regs dst src imm regs' (mem : Mem)
      p g b e a ea loadv actualv :
    reg_allows_load_imm regs src imm p g b e a ea →
    mem !! ea = Some loadv →
    (actualv = load_word p loadv ∨
     actualv = clear_tag (load_word p loadv)) →
    incrementPC (<[dst := actualv]ᵣ> regs) = Some regs' →
    (match NextIV with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof.
    intros Hallow Hmem Hactual Hincr.
    exists p, g, b, e, a, ea, loadv, actualv.
    exact (conj Hallow (conj Hmem (conj Hactual Hincr))).
  Qed.

  Lemma Load_memory_failure_imm regs dst src imm regs' (mem : Mem) :
    (match FailedV with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof. exact I. Qed.

  Definition load_memory_shadow_observation
      (shadow : ShadowTbl) p loadv actualv : Prop :=
    match heap_cap_base loadv with
    | None => actualv = load_word p loadv
    | Some base => ∀ status, shadow !! base = Some status →
        actualv = match status with
                  | ShadowLive => load_word p loadv
                  | ShadowQuarantined => clear_tag (load_word p loadv)
                  end
    end.

  Lemma Load_memory_shadow_success_imm regs dst src imm regs' (mem : Mem) shadow
      p g b e a ea loadv actualv :
    reg_allows_load_imm regs src imm p g b e a ea →
    mem !! ea = Some loadv →
    (actualv = load_word p loadv ∨
     actualv = clear_tag (load_word p loadv)) →
    load_memory_shadow_observation shadow p loadv actualv →
    incrementPC (<[dst := actualv]ᵣ> regs) = Some regs' →
    (match NextIV with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        load_memory_shadow_observation shadow p loadv actualv ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof.
    intros Hallow Hmem Hactual Hobservation Hincr.
    exists p, g, b, e, a, ea, loadv, actualv.
    exact (conj Hallow (conj Hmem (conj Hactual
      (conj Hobservation Hincr)))).
  Qed.

  Lemma Load_memory_shadow_failure_imm regs dst src imm regs' (mem : Mem) shadow :
    (match FailedV with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        load_memory_shadow_observation shadow p loadv actualv ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof. exact I. Qed.

  Lemma load_memory_shadow_spec_imm_erase regs dst src imm regs' (mem : Mem) shadow retv :
    (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        load_memory_shadow_observation shadow p loadv actualv ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end) →
    (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof.
    intros Hspec. destruct retv; simpl in Hspec; [contradiction|done|].
    destruct Hspec as (p & g & b & e & a & ea & loadv & actualv &
      Hallow & Hmem & Hactual & _ & Hincr).
    eapply Load_memory_success_imm; eauto.
  Qed.

  Lemma load_spec_offset_to_memory_shadow_imm
      regs dst src imm regs' mem shadow retv :
    (∀ p g b e ea,
      reg_allows_load_offset regs src imm p g b e ea →
      is_shadow_address ea = false) →
    Load_spec regs dst src imm regs' mem shadow retv →
    (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        load_memory_shadow_observation shadow p loadv actualv ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof.
    intros Hordinary Hspec.
    destruct Hspec as
      [p g b e ea loadv Hallow Hshadow Hmem Hheap Hincr
      |p g b e ea t' p' g' b' e' a' Hallow Hshadow Hmem Hnonheap Hincr
      |p g b e ea raw base Hallow Hshadow Hmem Hbase Hbit Hincr
      |p g b e ea raw base Hallow Hshadow Hmem Hbase Hbit Hincr
      |p g b e ea heap_a revoked Hallow Hshadow Htranslate Hlookup Hincr
      |Hfail]; last exact I.
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow)
        as (a & Hallowimm).
      eapply Load_memory_shadow_success_imm with
        (a := a) (ea := ea) (loadv := loadv)
        (actualv := load_word p loadv);
        [exact Hallowimm|exact Hmem| | |exact Hincr].
      + by left.
      + unfold load_memory_shadow_observation, is_heap_cap in *.
        by destruct (heap_cap_base loadv).
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow)
        as (a & Hallowimm).
      eapply Load_memory_shadow_success_imm with
        (a := a) (ea := ea) (loadv := WCap t' p' g' b' e' a')
        (actualv := load_word p (WCap t' p' g' b' e' a'));
        [exact Hallowimm|exact Hmem| | |exact Hincr].
      + by left.
      + by rewrite /load_memory_shadow_observation /heap_cap_base
          /memory_cap_base /= Hnonheap.
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow)
        as (a & Hallowimm).
      eapply Load_memory_shadow_success_imm with
        (a := a) (ea := ea) (loadv := raw)
        (actualv := load_word p raw);
        [exact Hallowimm|exact Hmem| | |exact Hincr].
      + by left.
      + rewrite /load_memory_shadow_observation Hbase.
        intros status Hlookup. destruct status; auto.
        exfalso. apply Hbit. exact Hlookup.
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow)
        as (a & Hallowimm).
      eapply Load_memory_shadow_success_imm with
        (a := a) (ea := ea) (loadv := raw)
        (actualv := clear_tag (load_word p raw));
        [exact Hallowimm|exact Hmem| | |exact Hincr].
      + by right.
      + rewrite /load_memory_shadow_observation Hbase.
        intros status Hlookup. destruct status; auto.
        exfalso. apply Hbit. exact Hlookup.
    - rewrite (Hordinary _ _ _ _ _ Hallow) in Hshadow.
      discriminate.
  Qed.

  Lemma load_spec_offset_to_memory_imm
      regs dst src imm regs' mem shadow retv :
    (∀ p g b e ea,
      reg_allows_load_offset regs src imm p g b e ea →
      is_shadow_address ea = false) →
    Load_spec regs dst src imm regs' mem shadow retv →
    (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof.
    intros Hordinary Hspec.
    eapply (load_memory_shadow_spec_imm_erase _ _ _ _ _ _ shadow).
    exact (load_spec_offset_to_memory_shadow_imm
      _ _ _ _ _ _ _ _ Hordinary Hspec).
  Qed.

  Lemma load_spec_offset_to_spec_imm
      regs dst src imm regs' mem retv :
    (∀ p g b e ea,
      reg_allows_load_offset regs src imm p g b e ea →
      is_shadow_address ea = false) →
    (∀ p g b e ea loadv,
      reg_allows_load_offset regs src imm p g b e ea →
      mem !! ea = Some loadv → is_heap_cap loadv = false) →
    Load_spec regs dst src imm regs' mem ∅ retv →
    ((∃ p g b e a ea loadv,
      retv = NextIV ∧
      reg_allows_load_imm regs src imm p g b e a ea ∧
      mem !! ea = Some loadv ∧
      incrementPC (<[dst := load_word p loadv]ᵣ> regs) = Some regs') ∨
    (retv = FailedV ∧ ∃ fail : Load_failure_spec regs dst src imm mem ∅, True)).
  Proof.
    intros Hordinary Hnonheap Hspec.
    destruct Hspec as
      [p g b e ea loadv Hallow Hshadow Hmem Hheap Hincr
      |p g b e ea t' p' g' b' e' a' Hallow Hshadow Hmem Hheap Hincr
      |p g b e ea raw base Hallow Hshadow Hmem Hbase Hbit Hincr
      |p g b e ea raw base Hallow Hshadow Hmem Hbase Hbit Hincr
      |p g b e ea heap_a revoked Hallow Hshadow Htranslate Hlookup Hincr
      |Hfail].
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow)
        as (a & Hallowimm).
      eapply Load_spec_success_imm with
        (a := a) (ea := ea) (loadv := loadv);
        [exact Hallowimm|exact Hmem|exact Hincr].
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow)
        as (a & Hallowimm).
      eapply Load_spec_success_imm with
        (a := a) (ea := ea) (loadv := WCap t' p' g' b' e' a');
        [exact Hallowimm|exact Hmem|exact Hincr].
    - pose proof (Hnonheap _ _ _ _ _ _ Hallow Hmem) as Hnotheap.
      unfold is_heap_cap in Hnotheap. rewrite Hbase in Hnotheap.
      discriminate.
    - pose proof (Hnonheap _ _ _ _ _ _ Hallow Hmem) as Hnotheap.
      unfold is_heap_cap in Hnotheap. rewrite Hbase in Hnotheap.
      discriminate.
    - rewrite (Hordinary _ _ _ _ _ Hallow) in Hshadow.
      discriminate.
    - apply Load_spec_failure_imm. exact Hfail.
  Qed.

  Lemma load_memory_spec_imm_zero regs dst src regs' (mem : Mem) retv :
    (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs src 0 p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end) →
    (match retv with
    | NextIV => ∃ p g b e a loadv actualv,
        reg_allows_load regs src p g b e a ∧
        mem !! a = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof.
    intros Hspec. destruct retv; simpl in *; [contradiction|done|].
    destruct Hspec as (p & g & b & e & a & ea & loadv & actualv &
      (Hreg & Hadd & Hra & Hwb) & Hmem & Hactual & Hincr).
    rewrite finz_add_0 in Hadd. inversion Hadd; subst ea.
    exists p, g, b, e, a, loadv, actualv.
    exact (conj (conj Hreg (conj Hra Hwb))
      (conj Hmem (conj Hactual Hincr))).
  Qed.

  Lemma load_spec_offset_to_memory_zero
      regs dst src regs' mem shadow retv :
    (∀ p g b e a,
      reg_allows_load regs src p g b e a →
      is_shadow_address a = false) →
    Load_spec regs dst src 0 regs' mem shadow retv →
    (match retv with
    | NextIV => ∃ p g b e a loadv actualv,
        reg_allows_load regs src p g b e a ∧
        mem !! a = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[dst := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end).
  Proof.
    intros Hordinary Hspec.
    apply load_memory_spec_imm_zero.
    eapply load_spec_offset_to_memory_imm; eauto.
  Qed.

  Lemma wp_load_memory_general_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs shadow sdq :
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea,
      reg_allows_load_imm regs r2 imm p g b e a ea →
      is_shadow_address ea = false) →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       (▷ [∗ map] a↦status ∈ shadow, a ↦ₛ{sdq} status) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs r2 imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        load_memory_shadow_observation shadow p loadv actualv ∧
        incrementPC (<[r1 := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end)⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         ([∗ map] a↦status ∈ shadow, a ↦ₛ{sdq} status) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hordinary Hdomeq φ) "(>Hmem & >Hshadow & >Hmap) Hφ".
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[[[[Hr Hsr] Hm] Hst] Hmmio] /=". destruct σ1 as [ [ [r sr] m] st]; cbn.
    iDestruct "Hmmio" as %Hmmio.
    iAssert (⌜mem_avoids_mmio m⌝)%I as "-#Hmmio"; first by iPureIntro.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    iAssert (⌜∀ a status, shadow !! a = Some status → st !! a = Some status⌝)%I
      as %Hshadow_valid.
    { iIntros (a status Hlookup).
      iDestruct (big_sepM_lookup with "Hshadow") as "Ha"; first exact Hlookup.
      iApply (gen_heap_valid with "Hst Ha"). }

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
       assert (c = Failed ∧ σ2 = (r, sr, m, st)) as (-> & ->).
       {
         unfold is_cap in Hr2v.
         destruct_word r2v; by simplify_pair_eq.
       }
        iFailWP "Hφ" Load_memory_shadow_failure_imm.
     }
     destruct r2v as [ | [t p g b e a | ] | | ]; try inversion Hr2v. clear Hr2v.
     destruct t.
     2: {
       inversion Hstep; subst c σ2.
       iFailWP "Hφ" Load_memory_shadow_failure_imm.
     }

    destruct (a + imm)%a as [ea|] eqn:Hadd; cbn in Hstep.
    2: { inversion Hstep; subst c σ2. iFailWP "Hφ" Load_memory_shadow_failure_imm. }
    destruct (readAllowed p && withinBounds b e ea) eqn:HRA.
    2 : { (* Failure: r2 is either not within bounds or doesnt allow reading *)
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
      apply andb_false_iff in HRA.
      iFailWP "Hφ" Load_memory_shadow_failure_imm.
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

    rewrite (Hordinary p g b e a ea Hallow) (mem_avoids_mmio_not_revoker _ _ _ Hmmio Hma') Hma' /= in Hstep.
    assert (Hread : (c = Failed ∧ σ2 = (r, sr, m, st)) ∨
      ∃ actualv,
        (match updatePC (update_reg (r, sr, m, st) r1 actualv) with
         | Some conf => conf | None => (Failed, (r, sr, m, st)) end) = (c, σ2) ∧
        (actualv = load_word p loadv ∨ actualv = clear_tag (load_word p loadv)) ∧
        load_memory_shadow_observation shadow p loadv actualv).
    { destruct (heap_cap_base loadv) as [base|] eqn:Hheap.
      - destruct (st !! base) as [status|] eqn:Hbit; cbn in Hstep.
        + destruct status; right; eexists; split; [exact Hstep | | exact Hstep |].
          * split; first by left. rewrite /load_memory_shadow_observation Hheap.
            intros status Hlookup. specialize (Hshadow_valid _ _ Hlookup).
            rewrite Hbit in Hshadow_valid. by simplify_eq.
          * split; first by right. rewrite /load_memory_shadow_observation Hheap.
            intros status Hlookup. specialize (Hshadow_valid _ _ Hlookup).
            rewrite Hbit in Hshadow_valid. by simplify_eq.
        + left. by simplify_pair_eq.
      - right; eexists; split; [exact Hstep |].
        split; first by left. by rewrite /load_memory_shadow_observation Hheap. }
    destruct Hread as [(-> & ->) | (actualv & Hread & Hactual & Hobserved)].
    { iFailWP "Hφ" Load_memory_shadow_failure_imm. }
    clear Hstep. rename Hread into Hstep.
    destruct (incrementPC (<[ r1 := actualv ]ᵣ> regs)) as  [ regs' |] eqn:Hregs'.
    2: { (* Failure: the PC could not be incremented correctly *)
      assert (incrementPC (<[ r1 := actualv ]ᵣ> r) = None).
      { eapply incrementPC_overflow_mono; first eapply Hregs'.
          + simplify_map_eq; by rewrite lookup_insert_is_Some'; eauto.
          + by apply insert_mono; eauto. }

      rewrite incrementPC_fail_updatePC /= in Hstep; auto.
      symmetry in Hstep; inversion Hstep; clear Hstep. subst c σ2.
       (* Update the heap resource, using the resource for r2 *)
      iFailWP "Hφ" Load_memory_shadow_failure_imm.
    }

    (* Success *)
    rewrite /update_reg /= in Hstep.
    eapply (incrementPC_success_updatePC _ sr m st) in Hregs'
      as (t1 & p1 & g1 & b1 & e1 & a1 & a_pc1 & HPC'' & Ha_pc' & HuPC & ->).
    eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono.
    rewrite HuPC in Hstep; clear HuPC; inversion Hstep; clear Hstep; subst c σ2. cbn.
    iFrame.
    iMod ((gen_heap_update_inSepM _ _ r1) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    { apply is_Some_lookup_reg; done. }
    iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
    iFrame. iModIntro. iApply "Hφ". iFrame.
    iPureIntro. eapply Load_memory_shadow_success_imm with (loadv := loadv) (actualv := actualv); eauto.
    * rewrite /incrementPC /incrementPC_gen. by rewrite HPC'' Ha_pc'.
      Unshelve. all: auto.
  Qed.

  Lemma wp_load_memory_general_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem (dfracs : gmap Addr dfrac) regs :
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea,
      reg_allows_load_imm regs r2 imm p g b e a ea →
      is_shadow_address ea = false) →
   dom mem = dom dfracs →

   {{{ (▷ [∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs r2 imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[r1 := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end)⌝ ∗
         ([∗ map] a↦dw ∈ prod_merge dfracs mem, a ↦ₐ{dw.1} dw.2) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hmem_pc HaLoad Hordinary Hdomeq φ)
      "[Hmem Hmap] Hφ".
    iApply (wp_load_memory_general_shadow_imm Ep _ _ _ _ _ _ _ _ _ _ _ _ ∅ (DfracOwn 1)
      with "[Hmem Hmap]"); eauto.
    { iFrame. iNext. done. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & _ & Hmap)".
    iApply "Hφ". iFrame. iPureIntro.
    exact (load_memory_shadow_spec_imm_erase _ _ _ _ _ _ _ _ Hspec).
  Qed.

  Lemma wp_load_memory_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem regs dq :
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea,
      reg_allows_load_imm regs r2 imm p g b e a ea →
      is_shadow_address ea = false) →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs r2 imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        incrementPC (<[r1 := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end)⌝ ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "[Hmem Hreg] Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_memory_general_imm with "[$Hmem $Hreg]");eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ?) "(?&Hmem&?)". iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

  Lemma wp_load_memory_shadow_imm Ep
     pc_p pc_g pc_b pc_e pc_a
     r1 r2 (imm : Z) w mem regs dq shadow sdq :
   decodeInstrW w = Load r1 r2 imm →
   isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a) →
   regs_of (Load r1 r2 imm) ⊆ dom regs →
   mem !! pc_a = Some w →
   allow_load_map_or_true_imm r2 imm regs mem →
   (∀ p g b e a ea,
      reg_allows_load_imm regs r2 imm p g b e a ea →
      is_shadow_address ea = false) →
   {{{ (▷ [∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
       (▷ [∗ map] a↦status ∈ shadow, a ↦ₛ{sdq} status) ∗
       ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
     Instr Executable @ Ep
   {{{ regs' retv, RET retv;
       ⌜ (match retv with
    | NextIV => ∃ p g b e a ea loadv actualv,
        reg_allows_load_imm regs r2 imm p g b e a ea ∧
        mem !! ea = Some loadv ∧
        (actualv = load_word p loadv ∨
         actualv = clear_tag (load_word p loadv)) ∧
        load_memory_shadow_observation shadow p loadv actualv ∧
        incrementPC (<[r1 := actualv]ᵣ> regs) = Some regs'
    | FailedV => True
    | _ => False
    end)⌝ ∗
         ([∗ map] a↦w ∈ mem, a ↦ₐ{dq} w) ∗
         ([∗ map] a↦status ∈ shadow, a ↦ₛ{sdq} status) ∗
         [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    intros. iIntros "(Hmem & Hshadow & Hreg) Hφ".
    iDestruct (mem_remove_dq with "Hmem") as "Hmem".
    iApply (wp_load_memory_general_shadow_imm with "[$Hmem $Hshadow $Hreg]"); eauto.
    { rewrite create_gmap_default_dom list_to_set_elements_L. auto. }
    iNext. iIntros (? ?) "(? & Hmem & ? & ?)".
    iApply "Hφ". iFrame.
    iDestruct (mem_remove_dq with "Hmem") as "Hmem". iFrame.
  Qed.

End griotte_lang_rules.
