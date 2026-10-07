From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode_binary.
From griotte Require Export clear_stack.

(** * Clearing the stack in both runs

    Binary (lockstep) counterpart of the specification of the stack clearing
    macro: both runs execute the same macro, with the same stack pointer, on
    their own stack memory. *)

Section ClearStackMacro.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {specg: specG Σ} `{MP: MachineParameters}.

  Lemma clear_stack_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (csp_g : Locality) (csp_b csp_e csp_a : Addr)
    (r1 r2 : RegName) (ws ws' : list Word)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs r1 r2))%a ->
    (csp_b <= csp_a)%a -> (csp_a <= csp_e)%a ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    ( spec_ctx
      ∗ ⤇ Seq (Instr Executable)
      ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ csp ↦ᵣ WCap RWL csp_g csp_b csp_e csp_a
      ∗ csp ↣ᵣ WCap RWL csp_g csp_b csp_e csp_a
      ∗ r1 ↦ᵣ WInt csp_e ∗ r2 ↦ᵣ WInt csp_a
      ∗ r1 ↣ᵣ WInt csp_e ∗ r2 ↣ᵣ WInt csp_a
      ∗ codefrag pc_a (clear_stack_instrs r1 r2)
      ∗ spec_codefrag pc_a (clear_stack_instrs r1 r2)
      ∗ ([[ csp_a , csp_e ]] ↦ₐ [[ ws ]])
      ∗ ([[ csp_a , csp_e ]] ↣ₐ [[ ws' ]])
      ∗ ▷ ( (⤇ Seq (Instr Executable)
             ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a
             ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a
             ∗ csp ↦ᵣ WCap RWL csp_g csp_b csp_e csp_a
             ∗ csp ↣ᵣ WCap RWL csp_g csp_b csp_e csp_a
             ∗ r1 ↦ᵣ WInt 0 ∗ r2 ↦ᵣ WCap RWL csp_g csp_b csp_e csp_e
             ∗ r1 ↣ᵣ WInt 0 ∗ r2 ↣ᵣ WCap RWL csp_g csp_b csp_e csp_e
             ∗ codefrag pc_a (clear_stack_instrs r1 r2)
             ∗ spec_codefrag pc_a (clear_stack_instrs r1 r2)
             ∗ ([[ csp_a , csp_e ]] ↦ₐ [[region_addrs_zeroes csp_a csp_e]])
             ∗ ([[ csp_a , csp_e ]] ↣ₐ [[region_addrs_zeroes csp_a csp_e]]))
        -∗ WP Seq (Instr Executable) {{ φ }})
    )
      ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hbounds1 Hbounds2 Hr1cnull Hr2cnull)
      "(#Hctx & Hj & HPC & HsPC & Hcsp & Hscsp & Hr1 & Hr2 & Hsr1 & Hsr2
        & Hcode & Hscode & Hstack & Hsstack & Hφ)".
    codefrag_facts "Hcode".

    (* Sub r1 r2 r1 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Mov r2 csp *)
    iInstr_lockstep "Hscode" "Hcode".

    remember (WCap RWL csp_g csp_b csp_e csp_a) as sp.
    iAssert (r2 ↦ᵣ WCap RWL csp_g csp_b csp_e csp_a)%I with "[Hr2]" as "Hr2"; first by rewrite Heqsp.
    iAssert (r2 ↣ᵣ WCap RWL csp_g csp_b csp_e csp_a)%I with "[Hsr2]" as "Hsr2"; first by rewrite Heqsp.
    clear Heqsp.
    iAssert (⌜(csp_b <= csp_a)%a ⌝)%I as "-#Hbounds1"; first done.
    iAssert (⌜(csp_a <= csp_e)%a ⌝)%I as "-#Hbounds2"; first done.
    clear Hbounds1 Hbounds2.
    iLöb as "IH" forall (csp_a ws ws').
    iDestruct "Hbounds1" as "%Hbounds1".
    iDestruct "Hbounds2" as "%Hbounds2".
    iDestruct (big_sepL2_length with "Hstack") as "%Hlen_stk".
    iDestruct (big_sepL2_length with "Hsstack") as "%Hlen_sstk".

    destruct (decide (csp_a = csp_e)).
    - (* the loop has ended *)
      replace (csp_a - csp_e)%Z with 0%Z by solve_addr.
      (* Jnz 2 r1 *)
      iInstr_lockstep "Hscode" "Hcode".
      (* Jmp 5 *)
      iInstr_lockstep "Hscode" "Hcode".
      iApply "Hφ". subst. iFrame.
      rewrite /region_pointsto /spec_region_pointsto finz_seq_between_empty; last solve_addr+.
      rewrite /region_addrs_zeroes finz_dist_0; last solve_addr+.
      by iSplit.
    - (* another iteration *)
      (* Jnz 2 r1 *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: intros Hcontr; inversion Hcontr; solve_addr.

      rewrite finz_seq_between_cons in Hlen_stk; last solve_addr.
      rewrite finz_seq_between_cons in Hlen_sstk; last solve_addr.
      destruct ws as [|wa ws]; simplify_eq.
      destruct ws' as [|wa' ws']; simplify_eq.
      rewrite (region_pointsto_cons _ (csp_a ^+ 1)%a); [| solve_addr | solve_addr].
      rewrite (spec_region_pointsto_cons _ (csp_a ^+ 1)%a); [| solve_addr | solve_addr].
      iDestruct "Hstack" as "[Ha Hstack]".
      iDestruct "Hsstack" as "[Hsa Hsstack]".
      (* Store r2 0 *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: apply withinBounds_true_iff; solve_addr.

      (* Lea r2 1 *)
      destruct (csp_a + 1)%a eqn:Ha;cycle 1.
      { solve_addr. }
      iInstr_lockstep "Hscode" "Hcode".

      (* Add r1 r1 1 *)
      iInstr_lockstep "Hscode" "Hcode".

      (* Jmp -5 *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: instantiate (1:=(pc_a ^+ 2)%a); solve_addr.

      replace (csp_a - csp_e + 1)%Z with (f - csp_e)%Z by solve_addr.
      replace f with (csp_a ^+1)%a by solve_addr.
      iApply ("IH" $! (csp_a ^+1)%a ws ws' with
               "Hstack Hsstack [Ha Hsa Hφ] Hsr1 Hr1 Hscode HsPC Hscsp Hj Hcode HPC Hcsp Hr2 Hsr2 [] []").
      { iIntros "(?&?&?&?&?&?&?&?&?&?&?&Hstk&Hsstk)".
        iApply "Hφ"; iFrame.
        iDestruct ( region_pointsto_cons with "[$Ha $Hstk]" ) as "Hstk"; [solve_addr|solve_addr|].
        iDestruct ( spec_region_pointsto_cons with "[$Hsa $Hsstk]" ) as "Hsstk"; [solve_addr|solve_addr|].
        rewrite /region_addrs_zeroes.
        rewrite (finz_dist_S csp_a); last solve_addr.
        by iFrame.
      }
      { iPureIntro ; solve_addr. }
      { iPureIntro ; solve_addr. }
  Qed.

End ClearStackMacro.
