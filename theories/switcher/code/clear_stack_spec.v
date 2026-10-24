From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export clear_stack.

Section ClearStackMacro.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (** Zero the words [[a_lo, a_hi)] through the capability in [rbase], whose
      cursor is at [a_lo], up to the address [a_hi] in [rtop]. *)
  Lemma clear_stack_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (g : Locality) (b e a_lo a_hi : Addr)
    (rbase rtop : RegName) (ws : list LWord)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs rbase rtop))%a ->
    (b <= a_lo)%a -> (a_lo <= a_hi)%a -> (a_hi <= e)%a ->
    disjoint_from_shadow b e →
    rbase ≠ cnull ->
    rtop ≠ cnull ->

    ( PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
      ∗ rbase ↦ᵣ WCap true RWL g b e a_lo
      ∗ rtop ↦ᵣ WInt a_hi
      ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
      ∗ ([[ a_lo , a_hi ]] ↦ₐ [[ ws ]])
      ∗ ▷ ( (PC ↦ₚ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs rbase rtop))%a
             ∗ rbase ↦ᵣ WCap true RWL g b e a_hi
             ∗ rtop ↦ᵣ WInt 0
             ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
             ∗ ([[ a_lo , a_hi ]] ↦ₐ [[region_addrs_zeroes a_lo a_hi]]))
        -∗ WP Seq (Instr Executable) {{ φ }})
    )
      ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hb Hlo Hhi Hdisjoint Hrbase_cnull Hrtop_cnull)
      "(HPC & Hrbase & Hrtop & #Hcode & Hstack & Hφ)".
    codefrag_facts "Hcode".

    (* Sub rtop rbase rtop *)
    iInstr "Hcode".
    iEval (cbn) in "Hrtop".

    iAssert (⌜(b <= a_lo)%a ⌝)%I as "-#Hb"; first done.
    iAssert (⌜(a_lo <= a_hi)%a ⌝)%I as "-#Hlo"; first done.
    clear Hb Hlo.
    iLöb as "IH" forall (a_lo ws).
    iDestruct "Hb" as "%Hb".
    iDestruct "Hlo" as "%Hlo".
    iDestruct (big_sepL2_length with "Hstack") as "%Hlen_stk".

    destruct (decide (a_lo = a_hi)) as [<- | Hne].
    - (* The loop ends *)
      replace (a_lo - a_lo)%Z with 0%Z by lia.
      (* Jne 2 rtop 0 *)
      iInstr "Hcode".
      (* Jmp 5 *)
      iInstr "Hcode".
      iApply "Hφ". iFrame "∗ #".
      rewrite /region_pointsto finz_seq_between_empty; last solve_addr+.
      rewrite /region_addrs_zeroes finz_dist_0; last solve_addr+.
      done.
    - (* Another iteration *)
      (* Jne 2 rtop 0 *)
      iInstrApply "Hcode" wp_jnez_success_jmp_z with "[$HPC $Hrtop]" as "(HPC & Hrtop)".
      { apply negb_true_iff, Z.eqb_neq. intros Hcontr; cbn in Hcontr; solve_addr. }

      rewrite finz_seq_between_cons in Hlen_stk; last solve_addr.
      destruct ws as [|wa ws]; simplify_eq.
      rewrite (region_pointsto_cons _ (a_lo ^+ 1)%a); [| solve_addr | solve_addr].
      iDestruct "Hstack" as "[Ha Hstack]".
      (* Store rbase 0 0 *)
      iInstr "Hcode".
      { eapply disjoint_from_shadow_not_in; first exact Hdisjoint.
        apply withinBounds_true_iff; solve_addr. }
      { apply withinBounds_true_iff; solve_addr. }

      destruct (a_lo + 1)%a as [a_lo1|] eqn:Ha; cycle 1.
      { iInstr_lookup "Hcode" as "Hi" "Hcode".
        solve_addr.
      }
      (* Lea rbase rbase 1 *)
      iInstr "Hcode".

      (* Add rtop rtop 1 *)
      iInstr "Hcode".

      (* Jmp -5 *)
      iInstr "Hcode".
      { instantiate (1:=(pc_a ^+ 1)%a). solve_addr. }

      (* IH *)
      replace (a_lo - a_hi + 1)%Z with (a_lo1 - a_hi)%Z by solve_addr.
      replace a_lo1 with (a_lo ^+1)%a by solve_addr.
      iApply ("IH" $! (a_lo ^+1)%a ws with
               "[$Hstack] [Ha Hφ] [$HPC] [$Hrbase] [$Hrtop] [] []").
      { iIntros "(HPC & Hrbase & Hrtop & _ & Hstk)".
        iApply "Hφ"; iFrame "∗ #".
        iDestruct ( region_pointsto_cons with "[$Ha $Hstk]" ) as "Hstk"; [solve_addr|solve_addr|].
        rewrite /region_addrs_zeroes.
        rewrite (finz_dist_S a_lo); last solve_addr.
        by cbn.
      }
      { iPureIntro ; solve_addr. }
      { iPureIntro ; solve_addr. }
  Qed.

End ClearStackMacro.
