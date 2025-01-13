From cap_machine Require Export rules_PromoteU rules_binary_base.
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import frac.


Section cap_lang_spec_rules.
  Context `{cfgSG Σ, MachineParameters, invG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : cap_lang.state.
  Implicit Types a b : Addr.
  Implicit Types r : RegName.
  Implicit Types w : Word.
  Implicit Types reg : gmap RegName Word.
  Implicit Types ms : gmap Addr Word.

  Lemma step_PromoteU Ep K pc_p pc_g pc_b pc_e pc_a dst w regs :
   decodeInstrW w = PromoteU dst →
   isCorrectPC (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs !! PC = Some (inr ((pc_p, pc_g), pc_b, pc_e, pc_a)) →
   regs_of (PromoteU dst) ⊆ dom _ regs →

   nclose specN ⊆ Ep →

   spec_ctx ∗ ⤇ fill K (Instr Executable) ∗ ▷ pc_a ↣ₐ w ∗ (▷ [∗ map] k↦y ∈ regs, k ↣ᵣ y)
   ={Ep}=∗ ∃ retv regs', ⤇ fill K (of_val retv) ∗ ⌜PromoteU_spec regs dst regs' retv ⌝ ∗ pc_a ↣ₐ w ∗ ([∗ map] k↦y ∈ regs', k ↣ᵣ y).
  Proof.
    iIntros (Hinstr Hvpc HPC Dregs Hnclose) "(#Hinv & Hj & >Hpc_a & >Hmap)".
    iDestruct "Hinv" as (ρ) "Hinv". rewrite /spec_inv.
    iInv specN as ">Hinv'" "Hclose". iDestruct "Hinv'" as (e [σr σm]) "[Hown %] /=".
    iDestruct (regspec_heap_valid_inclSepM with "Hown Hmap") as %Hregs.
    iDestruct (spec_expr_valid with "[$Hown $Hj]") as %Heq; subst e.

    pose proof (regs_lookup_eq _ _ _ HPC) as HPC'.
    pose proof (lookup_weaken _ _ _ _ HPC Hregs).
    iDestruct (spec_heap_valid with "[$Hown $Hpc_a]") as %Hpc_a.

    specialize (normal_always_step (σr,σm)) as [c [ σ2 Hstep]].
    eapply step_exec_inv in Hstep; eauto. assert (Hstep':=Hstep).
    specialize (indom_regs_incl _ _ _ Dregs Hregs) as Hri. unfold regs_of in Hri.

    feed destruct (Hri dst) as [rdstv [Hdst' Hdst]]. by set_solver+.
    pose proof (regs_lookup_eq _ _ _ Hdst) as Hrdst'.
    cbn in Hstep. rewrite Hrdst' in Hstep. Local Opaque exec.
    destruct rdstv as [| (([[p g] b] & e) & a) ] eqn:Hdstv.
    { (* Failure: dst is not a capability *)
      inv Hstep.
      iFailStep PromoteU_fail_const. }

    destruct (perm_eq_dec p E).
    { subst p. inv Hstep.
      iFailStep PromoteU_fail_E. }

     destruct (incrementPC (<[ dst := inr ((promote_perm p, g), b, addr_reg.min a e, a) ]> regs)) as [ regs' |] eqn:Hregs'; cycle 1.
     { assert (incrementPC (<[ dst := inr ((promote_perm p, g, b, addr_reg.min a e, a))]> σr) = None).
       { eapply incrementPC_overflow_mono; first eapply Hregs'.
         by rewrite lookup_insert_is_Some'; eauto.
         by apply insert_mono; eauto. }
       rewrite incrementPC_fail_updatePC //= in Hstep; inversion Hstep; subst.
       iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
       iFailStep PromoteU_fail_incrementPC. }

     generalize Hregs'; intros HH.
     eapply (incrementPC_success_updatePC _ σm) in Hregs'
       as (p' & g' & b' & e' & a'' & a_pc' & HPC'' & Ha_pc' & HuPC & -> & ?).
     eapply updatePC_success_incl in HuPC. 2: by eapply insert_mono; eauto.
     rewrite HuPC in Hstep; clear HuPC; inversion Hstep. subst c σ2. cbn.
     iFrame.
     iMod ((regspec_heap_update_inSepM _ _ _ dst) with "Hown Hmap") as "[Hown Hmap]"; eauto.
     iMod ((regspec_heap_update_inSepM _ _ _ PC) with "Hown Hmap") as "[Hown Hmap]"; eauto.
     iMod (exprspec_mapsto_update _ _ (fill K (Instr NextI)) with "Hown Hj") as "[Hown Hj]".
     iExists NextIV,_. iFrame.
     iMod ("Hclose" with "[Hown]") as "_".
     { iNext. iExists _,_;iFrame. iPureIntro. eapply rtc_r;eauto. prim_step_from_exec. }
     iModIntro. iPureIntro. econstructor; eauto.
     Unshelve. auto.
  Qed.

End cap_lang_spec_rules.
