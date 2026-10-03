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
  Implicit Types ms : gmap Addr LWord.

  Inductive Jmp_failure (regs : LReg) (rimm: Z + RegName) :=
  | Jmp_fail_no_imm:
      lz_of_argument regs rimm = None →
      Jmp_failure regs rimm
  | Jmp_fail_PC_overflow imm:
      lz_of_argument regs rimm = Some imm →
      incrementPC_gen regs imm = None →
      Jmp_failure regs rimm.

  Inductive Jmp_spec (regs : LReg) (rimm: Z + RegName) : LReg → griotte_lang.val → Prop :=
  | Jmp_spec_success regs' imm :
      lz_of_argument regs rimm = Some imm →
      incrementPC_gen regs imm = Some regs' →
      Jmp_spec regs rimm regs' NextIV
  | Jmp_spec_failure:
      Jmp_failure regs rimm →
      Jmp_spec regs rimm regs FailedV.

  Lemma wp_Jmp Ep pc_p pc_g pc_b pc_e pc_a pc_π w rimm regs :
    decodeInstrW w.(lw) = Jmp rimm ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) →
    regs_of (Jmp rimm) ⊆ dom regs →

    {{{ ▷ pc_a ↦ₐ w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ regs' retv, RET retv;
        ⌜ Jmp_spec regs rimm regs' retv ⌝ ∗
        pc_a ↦ₐ w ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs φ) "(>Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "Hpc_a Hmap"); eauto.
    iNext. iIntros (r sr m st lreg lmem R C c σ' Her Hlregs Hregs Hpc_a Hstep)
      "Hr Hsr Hm Hst HR HC Hpc_a Hmap".
    rewrite Hinstr /exec /= in Hstep.
    unfold regs_of in Dregs.
    assert (∀ x, rimm = inr x → x ∈ dom regs) as Hdomr.
    { intros x ->. apply Dregs. set_solver+. }
    rewrite (lz_of_argument_phys regs r rimm Hregs Hdomr) in Hstep.
    destruct (lz_of_argument regs rimm) as [imm|] eqn:Himm.
    2: { cbn in Hstep. simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first exact Her.
         iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro. by constructor; constructor. }
    cbn in Hstep.
    destruct (incrementPC_gen regs imm) as [regs'|] eqn:Hregs'.
    2: { rewrite (incrementPC_gen_fail_updatePC_gen regs r sr m st imm) in Hstep; auto.
         simplify_eq. iApply (instr_close_fail with "Hr Hsr Hm Hst HR HC Hmap"); first exact Her.
         iIntros "Hmap". iApply "Hφ". iFrame. iPureIntro. constructor. by eapply Jmp_fail_PC_overflow. }
    destruct (erasure_incrementPC_gen _ _ _ _ _ _ _ _ _ _ _ Her Hlregs Hregs')
      as (t & p & g & b & e & a & a' & π & HPC1 & Ha' & -> & Hu & Her2).
    rewrite Hu in Hstep. simplify_eq.
    iMod (gen_heap_update_inSepM _ _ PC (WCap true pc_p pc_g pc_b pc_e a' @@? pc_π)
      with "Hr Hmap") as "[Hr Hmap]"; first eauto.
    iModIntro. iSplitR "Hφ Hmap Hpc_a".
    - iExists _, lmem, R, C. iFrame. iPureIntro. exact Her2.
    - iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

   Lemma wp_jmp_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm :
     decodeInstrW w.(lw) = Jmp (inl imm) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + imm)%a = Some pc_a' →
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w
     }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
         ∗ pc_a ↦ₐ w
     }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hφ".
     iDestruct (map_of_regs_1 with "HPC") as "Hmap".
     iApply (wp_Jmp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     { set_solver+. }
     iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [| * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_map_eq.
       rewrite insert_insert_eq //.
       iDestruct (regs_of_map_1 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try (unfold llookup_reg in * ); simplify_map_eq; eauto; try congruence.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto ; congruence.
     }
   Qed.

   Lemma wp_jmp_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rimm imm:
     decodeInstrW w.(lw) = Jmp (inr rimm) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + imm)%a = Some pc_a' →
     rimm ≠ cnull ->
     {{{ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ rimm ↦ᵣ WInt imm
     }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
         ∗ pc_a ↦ₐ w
         ∗ rimm ↦ᵣ WInt imm
     }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrimm) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrimm") as "[Hmap %]".
     iApply (wp_Jmp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     { set_solver+. }
     iNext. iIntros (regs' retv) "(%Hspec & Hpc_a & Hmap)".
     assert (lz_of_argument (<[PC:=WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π]>
               (<[rimm:=WInt imm @@? None]> ∅)) (inr rimm) = Some imm) as Hz0.
     { rewrite /lz_of_argument /llookup_reg lookup_insert_ne // lookup_insert_eq /=.
       by case_decide. }

     destruct Hspec as [regs' imm' Hz Hinc | Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. rewrite Hz0 in Hz. simplify_eq.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_map_eq.
       rewrite insert_insert_eq //.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail as [Hz | imm' Hz Hinc]; first congruence.
       rewrite Hz0 in Hz. simplify_eq.
       eapply incrementPC_gen_None_inv in Hinc; last by rewrite lookup_insert_eq.
       congruence.
     }
   Qed.


End griotte_lang_rules.
