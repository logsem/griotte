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
             ∗ rtop ↦ᵣ WInt a_hi
             ∗ codefrag_pers pc_a (clear_stack_instrs rbase rtop)
             ∗ ([[ a_lo , a_hi ]] ↦ₐ [[region_addrs_zeroes a_lo a_hi]]))
        -∗ WP Seq (Instr Executable) {{ φ }})
    )
      ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hb Hlo Hhi Hdisjoint Hrbase_cnull Hrtop_cnull)
      "(HPC & Hrbase & Hrtop & #Hcode & Hstack & Hφ)".
    codefrag_facts "Hcode".
    destruct (decide (a_lo = a_hi)) as [<- | Hne].
    { (* Jle 4 rtop rbase *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hrtop $Hrbase]"
        as "(HPC & Hrtop & Hrbase)".
      { cbn; lia. }
      iApply "Hφ". iFrame "∗ #".
      rewrite /region_pointsto finz_seq_between_empty; last solve_addr+.
      rewrite /region_addrs_zeroes finz_dist_0; last solve_addr+.
      done. }
    (* Jle 4 rtop rbase *)
    iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hrtop $Hrbase]"
      as "(HPC & Hrtop & Hrbase)".
    { cbn; apply Z.leb_gt; solve_addr. }
    iAssert (⌜(b <= a_lo)%a ⌝)%I as "-#Hb"; first done.
    iAssert (⌜(a_lo < a_hi)%a ⌝)%I as "-#Hlo"; first (iPureIntro; solve_addr).
    clear Hb Hlo Hne.
    iLöb as "IH" forall (a_lo ws).
    iDestruct "Hb" as "%Hb".
    iDestruct "Hlo" as "%Hlo".
    iDestruct (big_sepL2_length with "Hstack") as "%Hlen_stk".
    rewrite finz_seq_between_cons in Hlen_stk; last solve_addr.
    destruct ws as [|wa ws]; simplify_eq.
    rewrite (region_pointsto_cons _ (a_lo ^+ 1)%a); [| solve_addr | solve_addr].
    iDestruct "Hstack" as "[Ha Hstack]".
    (* Store rbase 0 0 *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact Hdisjoint.
      apply withinBounds_true_iff; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    (* Lea rbase rbase 1 *)
    iInstr "Hcode".
    { instantiate (1 := (a_lo ^+ 1)%a); solve_addr. }
    destruct (decide ((a_lo ^+ 1)%a = a_hi)) as [Hend | Hne].
    - (* Jlt -2 rbase rtop *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hrbase $Hrtop]"
        as "(HPC & Hrbase & Hrtop)".
      { cbn; apply Z.ltb_ge; solve_addr. }
      rewrite Hend finz_seq_between_empty in Hlen_stk; last solve_addr.
      destruct ws; last done.
      iApply "Hφ".
      iDestruct (region_pointsto_cons with "[$Ha $Hstack]") as "Hstk"; [solve_addr|solve_addr|].
      rewrite Hend.
      iFrame "∗ #".
      rewrite /region_addrs_zeroes (finz_dist_S a_lo); last solve_addr.
      rewrite -Hend finz_dist_0; last solve_addr.
      done.
    - (* Jlt -2 rbase rtop *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hrbase $Hrtop]"
        as "(HPC & Hrbase & Hrtop)".
      { cbn; apply Z.ltb_lt; solve_addr. }
      { instantiate (1 := (pc_a ^+ 1)%a). solve_addr. }
      iApply ("IH" $! (a_lo ^+ 1)%a ws with
               "[$Hstack] [Ha Hφ] [$HPC] [$Hrtop] [$Hrbase] [] []").
      { iIntros "(HPC & Hrbase & Hrtop & _ & Hstk)".
        iApply "Hφ"; iFrame "∗ #".
        iDestruct (region_pointsto_cons with "[$Ha $Hstk]") as "Hstk"; [solve_addr|solve_addr|].
        rewrite /region_addrs_zeroes (finz_dist_S a_lo); last solve_addr.
        by cbn. }
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
  Qed.

End ClearStackMacro.
