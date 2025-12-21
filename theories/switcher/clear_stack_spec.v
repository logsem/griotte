From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import memory_region rules proofmode.
From cap_machine Require Export clear_stack.

Section ClearStackMacro.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  Lemma clear_stack_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (csp_g : Locality) (csp_b csp_e csp_a : Addr)
    (r1 r2 : RegName) (ws : list Word)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs r1 r2))%a ->
    (csp_b <= csp_a)%a -> (csp_a <= csp_e)%a ->
    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ csp ↦ᵣ WCap RWL csp_g csp_b csp_e csp_a
      ∗ r1 ↦ᵣ WInt csp_e ∗ r2 ↦ᵣ WInt csp_a
      ∗ codefrag pc_a (clear_stack_instrs r1 r2)
      ∗ ([[ csp_a , csp_e ]] ↦ₐ [[ ws ]])
      ∗ ▷ ( (PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a
             ∗ csp ↦ᵣ WCap RWL csp_g csp_b csp_e csp_a
             ∗ r1 ↦ᵣ WInt 0 ∗ r2 ↦ᵣ WCap RWL csp_g csp_b csp_e csp_e
             ∗ codefrag pc_a (clear_stack_instrs r1 r2)
             ∗ ([[ csp_a , csp_e ]] ↦ₐ [[region_addrs_zeroes csp_a csp_e]]))
        -∗ WP Seq (Instr Executable) {{ φ }})
      ∗ ▷ φ FailedV
    )
      ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hbounds1 Hbounds2)
      "(HPC & Hcsp & Hr1 & Hr2 & Hcode & Hstack & Hφ & Hfail)".
    codefrag_facts "Hcode".

    (* --- Sub r1 r2 r1 --- *)
    iInstr "Hcode".

    (* --- Mov r2 csp --- *)
    iInstr "Hcode".

    remember (WCap RWL csp_g csp_b csp_e csp_a) as sp.
    rewrite{2} Heqsp. clear Heqsp.
    iAssert (⌜(csp_b <= csp_a)%a ⌝)%I as "-#Hbounds1"; first done.
    iAssert (⌜(csp_a <= csp_e)%a ⌝)%I as "-#Hbounds2"; first done.
    clear Hbounds1 Hbounds2.
    iLöb as "IH" forall (csp_a ws).
    iDestruct "Hbounds1" as "%Hbounds1".
    iDestruct "Hbounds2" as "%Hbounds2".
    iDestruct (big_sepL2_length with "Hstack") as "%Hlen_stk".

    destruct (decide (csp_a = csp_e)).
    - (* csp_a = csp_2 ==> loop has ended *)
      replace (csp_a - csp_e)%Z with 0%Z by solve_addr.
      (* --- Jnz 2 r1 --- *)
      iInstr "Hcode".
      (* --- Jmp 5 ---- *)
      iInstr "Hcode".
      iApply "Hφ". subst. iFrame.
      rewrite /region_pointsto finz_seq_between_empty; last solve_addr+.
      rewrite /region_addrs_zeroes finz_dist_0; last solve_addr+.
      done.
    - (* csp_a ≠ csp_2 ==> another iteration (or failure) *)
      (* --- Jnz 2 r1 --- *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hr1]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; solve_addr. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").

      (* --- Store r2 0%Z --- *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      rewrite finz_seq_between_cons in Hlen_stk; last solve_addr.
      destruct ws as [|wa ws]; simplify_eq.
      rewrite (region_pointsto_cons _ (csp_a ^+ 1)%a); [| solve_addr | solve_addr].
      iDestruct "Hstack" as "[Ha Hstack]".
      iApply (wp_store_success_z with "[$HPC $Hi $Hr2 $Ha]"); try solve_pure.
      { apply withinBounds_true_iff; solve_addr. }
      iIntros "!> (HPC & Hi & Hr2 & Ha)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").

      (* --- Lea r2 1 --- *)
      destruct (csp_a + 1)%a eqn:Ha;cycle 1.
      { iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hr2]")
        ; try solve_pure
        ; eauto.
        iIntros "!> _". wp_pure. wp_end. iFrame. }
      iInstr "Hcode".

      (* --- Add r1 r1 1 --- *)
      iInstr "Hcode".

      (* --- Jmp -5 --- *)
      iInstr "Hcode".
      { instantiate (1:=(pc_a ^+ 2)%a). solve_addr. }

      (* IH *)
      replace (csp_a - csp_e + 1)%Z with (f - csp_e)%Z by solve_addr.
      replace f with (csp_a ^+1)%a by solve_addr.
      iApply ("IH" $! (csp_a ^+1)%a ws with
               "[$Hstack] [Ha Hφ] [$Hfail] [$Hct2] [$Hcode] [$HPC] [$Hr2] [$Hcsp] [] []").
      { iIntros "(?&?&?&?&?&Hstk)".
        iApply "Hφ"; iFrame.
        iDestruct ( region_pointsto_cons with "[$Ha $Hstk]" ) as "Hstk"; [solve_addr|solve_addr|].
        rewrite /region_addrs_zeroes.
        rewrite (finz_dist_S csp_a); last solve_addr.
        by cbn.
      }
      { iPureIntro ; solve_addr. }
      { iPureIntro ; solve_addr. }
  Qed.

End ClearStackMacro.
