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

  Inductive Jmp_failure (lpc : LWord) (regs : LReg) (rimm: Z + RegName) :=
  | Jmp_fail_PC_overflow imm:
      lz_of_argument regs rimm = Some imm →
      incrementPC_gen lpc imm = None →
      Jmp_failure lpc regs rimm.

  Inductive Jmp_spec (lpc : LWord) (regs : LReg) (rimm: Z + RegName) : LWord → griotte_lang.val → Prop :=
  | Jmp_spec_success lpc' imm :
      lz_of_argument regs rimm = Some imm →
      incrementPC_gen lpc imm = Some lpc' →
      Jmp_spec lpc regs rimm lpc' NextIV
  | Jmp_spec_failure:
      Jmp_failure lpc regs rimm →
      Jmp_spec lpc regs rimm lpc FailedV.

  Lemma wp_Jmp Ep pc_p pc_g pc_b pc_e pc_a pc_π w rimm regs dq :
    decodeInstrW w.(lw) = Jmp rimm ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    regs_of (Jmp rimm) ⊆ dom regs →

    {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' retv, RET retv;
        ⌜ Jmp_spec (WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs rimm lpc' retv ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hinstr Hvpc Dregs φ) "(>HPC & >Hpc_a & >Hmap) Hφ".
    iApply (wp_instr_step with "HPC Hpc_a Hmap"); eauto.
    iNext; iIntros (r sr m st lreg lmem R C c σ') "@".
    rewrite Hinstr /exec in Hstep.
    unfold regs_of in Dregs.
    assert (∀ x, rimm = inr x → x ∈ dom regs) as Hdomr.
    { intros x ->. apply Dregs. set_solver+. }
    assert (exec_opt (Jmp rimm) pc_p (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) =
              (imm ← lz_of_argument regs rimm;
               updatePC_gen (WCap true pc_p pc_g pc_b pc_e pc_a, r, sr, m, st) imm)) as HH.
    { rewrite -(lz_of_argument_phys R regs r rimm Hregs Hdomr). done. }
    rewrite HH in Hstep. clear HH.
    destruct (lz_of_argument_dom regs rimm Hdomr) as [imm Himm].
    rewrite Himm in Hstep. cbn [mbind option_bind] in Hstep.
    iApply (instr_close_pc_update _ _ _ _ _ _ _ _ _ _ _ imm _ _ _
      (λ lpc' retv, Jmp_spec _ regs rimm lpc' retv)
      with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hpc_a]"); first done; first done.
    { intros. by eapply Jmp_spec_success. }
    { intros. constructor. by eapply Jmp_fail_PC_overflow. }
    iIntros (lpc' retv Hspec) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

   Lemma wp_jmp_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w imm dq :
     decodeInstrW w.(lw) = Jmp (inl imm) →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + imm)%a = Some pc_a' →
     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ{dq} w
     }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
         ∗ pc_a ↦ₐ{dq} w
     }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' ϕ) "(>HPC & >Hpc_a) Hφ".
     iPoseProof map_of_regs_0 as "-#Hmap".
     iApply (wp_Jmp with "[$HPC $Hmap $Hpc_a]"); eauto; simplify_map_eq; eauto.
     iNext. iIntros (lpc' retv) "(#Hspec & HPC & Hpc_a & Hmap)".
     iDestruct "Hspec" as %Hspec.

     destruct Hspec as [| Hfail].
     { (* Success *)
       iApply "Hφ". iFrame.
       try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_map_eq.
       iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; try (unfold llookup_reg in * ); simplify_map_eq; eauto; try congruence.
     }
   Qed.

   Lemma wp_jmp_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w rimm wimm imm dq:
     decodeInstrW w.(lw) = Jmp (inr rimm) →
     IsLInt wimm imm →
     isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + imm)%a = Some pc_a' →
     rimm ≠ cnull ->
     {{{ ▷ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
         ∗ ▷ pc_a ↦ₐ{dq} w
         ∗ ▷ rimm ↦ᵣ wimm
     }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
         ∗ pc_a ↦ₐ{dq} w
         ∗ rimm ↦ᵣ wimm
     }}}.
   Proof.
     iIntros (Hinstr Hwimm Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrimm) Hφ".
     destruct (IsLInt_inv _ _ Hwimm) as [πimm ->].
     iDestruct (map_of_regs_1 with "Hrimm") as "Hmap".
     iApply (wp_Jmp with "[$HPC $Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     { set_solver+. }
     iNext. iIntros (lpc' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
     assert (lz_of_argument {[rimm:=WInt imm @@? πimm]} (inr rimm) = Some imm) as Hz0.
     { rewrite /lz_of_argument /llookup_reg lookup_singleton_eq /=.
       by case_decide. }

     destruct Hspec as [lpc' imm' Hz Hinc | Hfail].
     { (* Success *)
       iApply "Hφ". iFrame. rewrite Hz0 in Hz. simplify_eq.
       try incrementPC_inv as (?&?&?&?&?&?&?&?&?&?&?); simplify_map_eq.
       iRegsMap "Hmap"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail as [imm' Hz Hinc].
       rewrite Hz0 in Hz. simplify_eq.
       eapply incrementPC_gen_None_inv in Hinc; last done.
       all: try congruence.
     }
   Qed.


End griotte_lang_rules.
