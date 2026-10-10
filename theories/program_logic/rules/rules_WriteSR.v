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
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types sreg : gmap SRegName Word.
  Implicit Types ms : gmap Addr LWord.

  (* System registers hold identifier-less words: a successful write stores the
     physical word of an identifier-less register word. *)
  Inductive WriteSR_failure (regs: LReg) (sregs : SReg) (dst: SRegName) (src: RegName) :=
  | WriteSR_fail_nonxrs p g b e a π:
      regs !! PC = Some (WCap true p g b e a @@? π) →
      has_sreg_access p = false ->
      WriteSR_failure regs sregs dst src
  | WriteSR_fail_incrPC p g b e a π w:
      regs !! PC = Some (WCap true p g b e a @@? π) →
      regs !!ₗ src = Some w →
      incrementPC regs = None →
      WriteSR_failure regs sregs dst src
  .

  Inductive WriteSR_spec
    (regs regs': LReg) (sregs sregs': SReg) (dst: SRegName) (src: RegName)
    : griotte_lang.val -> Prop :=
  | WriteSR_spec_success p g b e a π w:
    regs !! PC = Some (WCap true p g b e a @@? π) →
    has_sreg_access p = true ->
    regs !!ₗ src = Some w →
    incrementPC regs = Some regs' →
    sregs' = (<[dst := w.(lw)]> sregs) →
    WriteSR_spec regs regs' sregs sregs' dst src NextIV
  | WriteSR_spec_failure:
    sregs = sregs' ->
    WriteSR_failure regs sregs dst src →
    WriteSR_spec regs regs' sregs sregs' dst src FailedV.

  (* An identifier-less register word is a valid system register word. *)
  Lemma reg_word_ok_no_id R C (v : LWord) :
    v.(lprov) = None → reg_word_ok R C v → reg_word_ok R C (lword_of_word v.(lw)).
  Proof. destruct v as [w' π]; cbn. by intros ->. Qed.

  Lemma wp_WriteSR Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs sregs :
    decodeInstrW w.(lw) = WriteSR dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (WriteSR dst src) ⊆ dom regs →
    (if (has_sreg_access pc_p)
    then sregs_of (WriteSR dst src) ⊆ dom sregs
    else True) →
    (has_sreg_access pc_p = true → ∀ (v : LWord), regs !!ₗ src = Some v → v.(lprov) = None) →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}
      Instr Executable @ Ep
    {{{ regs' sregs' retv, RET retv;
        ⌜ WriteSR_spec regs regs' sregs sregs' dst src retv ⌝ ∗
        pc_a ↦ₐ w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        ([∗ map] k↦y ∈ sregs', k ↦ₛᵣ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Dsregs Hnoid φ) "(>Hpc_a & >Hmap & >Hsmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    iDestruct (gen_heap_valid_inclSepM with "Hsr Hsmap") as %Hsregs.
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    destruct (Hri src) as [wsrc [H'src _]]; first by set_solver+.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. simplify_eq.
      iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
      iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
      econstructor; first done. by eapply WriteSR_fail_nonxrs. }
    specialize (indom_sregs_incl _ _ _ Dsregs Hsregs) as Hsri. unfold sregs_of in Hsri.
    destruct (Hsri dst) as [wdst [H'dst Hdst]]; first by set_solver+.
    assert (lookup_reg src r = Some wsrc.(lw)) as Hsrc.
    { eapply lookup_reg_weaken; last exact Hregs. by rewrite lookup_reg_erase H'src. }
    assert (exec_opt (WriteSR dst src) pc_p (r, sr, m, st) =
              updatePC (update_sreg (r, sr, m, st) dst wsrc.(lw))) as HH.
    { by cbn; rewrite Hsrc Hxsr /=. }
    rewrite HH /update_sreg /= in Hstep.
    pose proof (Hnoid eq_refl _ H'src) as Hπ.
    assert (reg_word_ok R C (lword_of_word wsrc.(lw))) as Hok.
    { apply reg_word_ok_no_id; first done. by eapply erasure_llookup_reg_word. }
    pose proof (erasure_insert_sreg _ _ _ _ _ _ _ _ dst _ Her Hok) as Her1.
    destruct (incrementPC regs) as [regs'|] eqn:Hi.
    - destruct (erasure_incrementPC _ _ _ _ _ _ _ _ _ _ Her1 Hlregs Hi)
        as (t & p & g & b & e & a & a' & π & HPC1 & Ha' & -> & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      iMod (gen_heap_update_inSepM _ _ PC (WCap true pc_p pc_g pc_b pc_e a' @@? pc_π)
        with "Hr Hmap") as "[Hr Hmap]"; first eauto.
      iMod (gen_heap_update_inSepM _ _ dst wsrc.(lw) with "Hsr Hsmap") as "[Hsr Hsmap]"; first eauto.
      iModIntro. iSplitR "Hφ Hmap Hsmap Hpc_a".
      + iExists _, lmem, R, C. iFrame. iPureIntro. exact Her2.
      + iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
    - rewrite (incrementPC_fail_updatePC regs r (<[dst:=wsrc.(lw)]> sr) m st) in Hstep;
        [| done | by eexists | done].
      simplify_eq.
      iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
      iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
      econstructor; first done. by eapply WriteSR_fail_incrPC.
  Qed.

  Lemma wp_writesr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst src (wsrc : Word) :
    decodeInstrW w.(lw) = WriteSR dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ₛᵣ wdst
        ∗ ▷ src ↦ᵣ lword_of_word wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ₛᵣ wsrc
          ∗ src ↦ᵣ lword_of_word wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' ? ϕ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hsrc") as "[Hmap %]".
    iDestruct (map_of_sregs_1 with "Hdst") as "Hsmap".
    iApply (wp_WriteSR with "[$Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    - by unfold regs_of; rewrite !dom_insert; set_solver+.
    - by unfold sregs_of; rewrite Hxsr !dom_insert; set_solver+.
    - intros _ v Hv; simplify_eq; done.
    - iNext. iIntros (regs' sregs' retv) "(#Hspec & Hpc_a & Hmap & Hsmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| -> Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC src) // insert_insert_eq (insert_insert_ne _ PC src) // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(?&?&?)"; eauto; iFrame.
      iDestruct (sregs_of_map_1 with "Hsmap") as "?"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      - simplify_map_eq; eauto; congruence.
      - incrementPC_inv; simplify_map_eq; eauto.
        congruence.
    }
  Qed.

  Lemma wp_writesr_success_fromPC E pc_p pc_g pc_b pc_e pc_a pc_a' w dst wdst :
    decodeInstrW w.(lw) = WriteSR dst PC →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? None
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ₛᵣ wdst }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? None
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ₛᵣ WCap true pc_p pc_g pc_b pc_e pc_a }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' ϕ) "(>HPC & >Hpc_a & >Hdst) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hdst") as "Hsmap".
    iApply (wp_WriteSR with "[$Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold sregs_of; rewrite Hxsr !dom_insert; set_solver+. }
    { intros _ v Hv; simplify_eq; done. }
    iNext. iIntros (regs' sregs' retv) "(#Hspec & Hpc_a & Hmap & Hsmap)".
    iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| -> Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite !insert_insert_eq.
      iDestruct (regs_of_map_1 with "Hmap") as "?"; eauto; iFrame.
      iDestruct (sregs_of_map_1 with "Hsmap") as "?"; eauto; iFrame.
    }
    { (* Failure (contradiction) *)
      destruct Hfail.
      - simplify_map_eq; eauto; congruence.
      - incrementPC_inv; simplify_map_eq; eauto.
        congruence.
    }
  Qed.

End griotte_lang_rules.
