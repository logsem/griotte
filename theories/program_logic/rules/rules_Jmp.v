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

  Inductive Jmp_failure (regs: Reg) (rimm: Z + RegName) :=
  | Jmp_fail_no_imm:
      z_of_argument regs rimm = None →
      Jmp_failure regs rimm
  | Jmp_fail_PC_overflow imm:
      z_of_argument regs rimm = Some imm →
      incrementPC_gen regs imm = None →
      Jmp_failure regs rimm.

  Inductive Jmp_spec (regs: Reg) (rimm: Z + RegName) : Reg → cap_lang.val → Prop :=
  | Jmp_spec_success regs' imm :
      z_of_argument regs rimm = Some imm →
      incrementPC_gen regs imm = Some regs' →
      Jmp_spec regs rimm regs' NextIV
  | Jmp_spec_failure:
      Jmp_failure regs rimm →
      Jmp_spec regs rimm regs FailedV.

  Lemma wp_Jmp Ep pc_p pc_g pc_b pc_e pc_a w rimm regs :
    decodeInstrW w = Jmp rimm ->
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    regs !! PC = Some (WCap pc_p pc_g pc_b pc_e pc_a) →
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
    iApply wp_lift_atomic_base_step_no_fork; auto.
    iIntros (σ1 ns l1 l2 nt) "[ [Hr Hsr] Hm ] /=". destruct σ1 as [ [r sr] m]; cbn.
    iDestruct (gen_heap_valid_inclSepM with "Hr Hmap") as %Hregs.
    have ? := lookup_weaken _ _ _ _ HPC Hregs.
    iDestruct (@gen_heap_valid with "Hm Hpc_a") as %Hpc_a; auto.
    iModIntro. iSplitR; first (by iPureIntro; apply normal_always_base_reducible).
    iNext. iIntros (e2 σ2 efs Hpstep).
    apply prim_step_exec_inv in Hpstep as (-> & -> & (c & -> & Hstep)).
    iIntros "_".
    iSplitR; auto. eapply step_exec_inv in Hstep; eauto.
    rewrite /exec /= in Hstep.

    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri.
    unfold regs_of in Hri, Dregs.

    destruct (z_of_argument regs rimm) as [imm|] eqn:Himm
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
       iFailWP "Hφ" Jmp_fail_no_imm. }
     apply (z_of_arg_mono _ r) in Himm; auto.
     rewrite Himm in Hstep; simpl in Hstep.


     destruct (incrementPC_gen regs imm) eqn:Hregs';
       pose proof Hregs' as H'regs'; cycle 1.
     {
       assert (incrementPC_gen r imm = None) as HH.
       { eapply incrementPC_gen_overflow_mono; first eapply Hregs' ; eauto.
       }
       apply (incrementPC_gen_fail_updatePC_gen _ sr m) in HH. rewrite HH in Hstep.
       assert (c = Failed ∧ σ2 = (r, sr, m)) as (-> & ->) by (inversion Hstep; auto).
       iFailWP "Hφ" Jmp_fail_PC_overflow. }

       eapply (incrementPC_gen_success_updatePC_gen _ sr m _ imm) in Hregs'
         as (p'' & g'' & b' & e' & a'' & a''' & a_pc' & HPC'' & HuPC & ->).
       eapply updatePC_gen_success_incl with (sregs':=sr) (m':=m) in HuPC; eauto.
       rewrite HuPC in Hstep.
       eassert ((c, σ2) = (NextI, _)) as HH.
       { cbn in *; eauto. }
       simplify_pair_eq.

       iMod ((gen_heap_update_inSepM _ _ PC) with "Hr Hmap") as "[Hr Hmap]"; eauto.
       iFrame.
       iApply "Hφ". iFrame. iPureIntro. econstructor; eauto.
  Qed.

   Lemma wp_jmp_success_z Ep pc_p pc_g pc_b pc_e pc_a pc_a' w imm :
     decodeInstrW w = Jmp (inl imm) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + imm)%a = Some pc_a' →
     {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
     }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
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
       incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
       rewrite insert_insert //.
       iDestruct (regs_of_map_1 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto ; congruence.
     }
   Qed.

   Lemma wp_jmp_success_reg Ep pc_p pc_g pc_b pc_e pc_a pc_a' w rimm imm:
     decodeInstrW w = Jmp (inr rimm) →
     isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
     (pc_a + imm)%a = Some pc_a' →
     rimm ≠ cnull ->
     {{{ ▷ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
         ∗ ▷ pc_a ↦ₐ w
         ∗ ▷ rimm ↦ᵣ WInt imm
     }}}
       Instr Executable @ Ep
     {{{ RET NextIV;
         PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
         ∗ pc_a ↦ₐ w
         ∗ rimm ↦ᵣ WInt imm
     }}}.
   Proof.
     iIntros (Hinstr Hvpc Hpca' Hcnull ϕ) "(>HPC & >Hpc_a & >Hrimm) Hφ".
     iDestruct (map_of_regs_2 with "HPC Hrimm") as "[Hmap %]".
     iApply (wp_Jmp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
     { set_solver+. }
     iNext. iIntros (regs' retv) "(%Hspec & Hpc_a & Hmap)".

     destruct Hspec as [| * Hfail].
     { (* Success *)
       iApply "Hφ". iFrame.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq.
       rewrite insert_insert //.
       iDestruct (regs_of_map_2 with "Hmap") as "(?&?)"; eauto; iFrame. }
     { (* Failure (contradiction) *)
       destruct Hfail; simplify_map_eq; eauto; try congruence.
       incrementPC_inv as (?&?&?&?&?&?&?&?&?); simplify_map_eq; eauto ; congruence.
     }
   Qed.


End cap_lang_rules.
