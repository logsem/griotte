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

  (* System registers hold identifier-less words: a read gives identifier [None]. *)
  Inductive ReadSR_failure (regs: LReg) (sregs : SReg) (dst: RegName) (src: SRegName) :=
  | ReadSR_fail_nonxrs p g b e a π:
      regs !! PC = Some (WCap true p g b e a @@? π) →
      has_sreg_access p = false ->
      ReadSR_failure regs sregs dst src
  | ReadSR_fail_incrPC p g b e a π (w : Word):
      regs !! PC = Some (WCap true p g b e a @@? π) →
      sregs !! src = Some w →
      incrementPC (<[ dst := lword_of_word w ]ₗ> regs) = None →
      ReadSR_failure regs sregs dst src
  .

  Inductive ReadSR_spec
  (regs: LReg) (sregs: SReg) (dst: RegName) (src: SRegName) (regs': LReg)
    : griotte_lang.val -> Prop :=
  | ReadSR_spec_success p g b e a π (w : Word):
      regs !! PC = Some (WCap true p g b e a @@? π) →
      has_sreg_access p = true ->
      sregs !! src = Some w →
      incrementPC (<[ dst := lword_of_word w ]ₗ> regs) = Some regs' →
      ReadSR_spec regs sregs dst src regs' NextIV
  | ReadSR_spec_failure:
      ReadSR_failure regs sregs dst src →
      ReadSR_spec regs sregs dst src regs' FailedV.

  Lemma wp_ReadSR Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs sregs :
    decodeInstrW w.(lw) = ReadSR dst src ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (ReadSR dst src) ⊆ dom regs →
    (if (has_sreg_access pc_p)
    then sregs_of (ReadSR dst src) ⊆ dom sregs
    else True) →
    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        ▷ ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ ReadSR_spec regs sregs dst src regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        ([∗ map] k↦y ∈ sregs, k ↦ₛᵣ y)
    }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Dsregs φ) "(>Hpc_a & >Hmap & >Hsmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    iDestruct (gen_heap_valid_inclSepM with "Hsr Hsmap") as %Hsregs.
    rewrite Hinstr /exec in Hstep.
    specialize (indom_lregs_incl _ _ _ Dregs Hlregs) as Hri. unfold regs_of in Hri.
    destruct (has_sreg_access pc_p) eqn:Hxsr; cycle 1.
    { cbn in Hstep. rewrite Hxsr in Hstep. simplify_eq.
      iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first done.
      iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro.
      econstructor. by eapply ReadSR_fail_nonxrs. }
    specialize (indom_sregs_incl _ _ _ Dsregs Hsregs) as Hsri. unfold sregs_of in Hsri.
    destruct (Hsri src) as [wsrc [H'src Hsrc]]; first by set_solver+.
    assert (exec_opt (ReadSR dst src) pc_p (r, sr, m, st) =
              updatePC (update_reg (r, sr, m, st) dst (lword_of_word wsrc).(lw))) as HH.
    { by cbn; rewrite Hsrc Hxsr /=. }
    rewrite HH in Hstep.
    iApply (instr_close_reg_update _ _ _ _ _ _ _ _ _ dst (lword_of_word wsrc) _ _ _
      (λ regs' retv, ReadSR_spec regs sregs dst src regs' retv)
      with "Hr Hsr Hm Hst HR HC Hmap [Hφ Hpc_a Hsmap]").
    { exact Her. } { exact Hlregs. } { apply Dregs. set_solver+. } { by eexists. }
    { by eapply (er_sreg_words _ _ _ _ _ Her src). } { exact Hstep. }
    { intros. by econstructor. }
    { intros. econstructor. by eapply ReadSR_fail_incrPC. }
    iIntros (regs' retv Hspec) "Hmap". iApply "Hφ". by iFrame.
  Qed.

  Lemma wp_readsr_success E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dst wdst src (wsrc : Word) :
    decodeInstrW w.(lw) = ReadSR dst src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ dst ↦ᵣ wdst
        ∗ ▷ src ↦ₛᵣ wsrc }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ dst ↦ᵣ lword_of_word wsrc
          ∗ src ↦ₛᵣ wsrc }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hdst & >Hsrc) Hφ".
    iDestruct (map_of_regs_2 with "HPC Hdst") as "[Hmap %]".
    iDestruct (map_of_sregs_1 with "Hsrc") as "Hsmap".
    iApply (wp_ReadSR with "[$Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    - by unfold regs_of; rewrite !dom_insert; set_solver+.
    - by unfold sregs_of; rewrite Hxsr !dom_insert; set_solver+.
    - iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap & Hsmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [| Hfail].
    { (* Success *)
      iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ PC dst) // insert_insert_eq.
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

  Lemma wp_readsr_success_toPC E pc_p pc_g pc_b pc_e pc_a pc_π w src (t : bool) p g b e a a':
    decodeInstrW w.(lw) = ReadSR PC src →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (a + 1)%a = Some a' →

    {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ w
        ∗ ▷ src ↦ₛᵣ WCap t p g b e a }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap t p g b e a' @@? None
          ∗ pc_a ↦ₐ w
          ∗ src ↦ₛᵣ WCap t p g b e a }}}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' ϕ) "(>HPC & >Hpc_a & >Hsrc) Hφ".
    iDestruct (map_of_regs_1 with "HPC") as "Hmap".
    iDestruct (map_of_sregs_1 with "Hsrc") as "Hsmap".
    iApply (wp_ReadSR with "[$Hmap $Hsmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by unfold sregs_of; rewrite Hxsr !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap & Hsmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [|Hfail].
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
