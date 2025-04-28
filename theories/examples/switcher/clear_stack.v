From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import addr_reg_sample rules proofmode.

Section ClearStackMacro.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (* Expects r1 := e_stk ; r2 := a_stk *)
  Definition clear_stack_instrs (r1 r2 : RegName) : list Word :=
    encodeInstrsW [
        Sub r1 r2 r1;
        Mov r2 csp;
        Jnz 2%Z r1;
        Jmp 5%Z;
        Store r2 0%Z;
        Lea r2 1%Z;
        Add r1 r1 1%Z;
        Jmp (-5)%Z
      ].


  (* Lemma clear_stack_spec_iter *)
  (*   (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr) *)
  (*   (csp_b csp_e csp_a : Addr) *)
  (*   (r1 r2 : RegName) (ws : list Word) *)
  (*   φ : *)
  (*   executeAllowed pc_p = true -> *)
  (*   SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs r1 r2))%a -> *)
  (*   (csp_b <= csp_a)%a -> (csp_a <= csp_e)%a -> *)
  (*   length ws = finz.dist csp_a csp_e -> *)
  (*   ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ 2)%a *)
  (*     ∗ r1 ↦ᵣ WInt (csp_a - csp_e)%Z ∗ r2 ↦ᵣ WCap RWL Local csp_b csp_e csp_a *)
  (*     ∗ codefrag pc_a (clear_stack_instrs r1 r2) *)
  (*     ∗ ([[ csp_a , csp_e ]] ↦ₐ [[ ws ]]) *)
  (*     ∗ ▷ ( (PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a *)
  (*            ∗ ([[ csp_a , csp_e ]] ↦ₐ [[region_addrs_zeroes csp_a csp_e]]) *)
  (*            ∗ (∃ csp_a, r2 ↦ᵣ WCap RWL Local csp_b csp_e csp_a *)
  (*                        ∗ r1 ↦ᵣ WInt (csp_a - csp_e)%Z ∗ ⌜ (csp_a - csp_e)%Z = 0 ⌝ *)
  (*              ) *)
  (*            ∗ codefrag pc_a (clear_stack_instrs r1 r2)) *)
  (*       -∗ WP Seq (Instr Executable) {{ φ }}) *)
  (*   ) *)
  (*     ⊢ WP Seq (Instr Executable) {{ φ }}%I. *)
  (* Proof. *)
  (*   iIntros (Hpc_exec Hbounds Hstk_bounds1 Hstk_bounds2 Hlen_stack) *)
  (*     "(HPC & Hr1 & Hr2 & Hcode & Hstack & Hφ)". *)
  (*   codefrag_facts "Hcode". *)

  (*   iRevert (Hlen_stack Hstk_bounds1 Hstk_bounds2). *)
  (*   iLöb as "IH" forall (csp_a ws); iIntros (Hlen_stack Hstl_bounds1 Hstk_bounds2). *)
  (*   destruct (decide (csp_a = csp_e) )%Z as [Heq|Hneq]. *)
  (*   - subst csp_a. *)
  (*     rewrite (_: csp_e - csp_e = 0)%Z; last lia. *)
  (*     (* Jnz 2%Z r1; *) *)
  (*     iInstr "Hcode". *)
  (*     (* Jmp 5%Z; *) *)
  (*     iInstr "Hcode". *)
  (*     iApply "Hφ". *)
  (*     iFrame. *)
  (*     rewrite (_: csp_e - csp_e = 0)%Z; last lia. *)
  (*     iFrame. iSplit ; last done. *)
  (*     rewrite /region_pointsto. *)
  (*     rewrite finz_seq_between_empty; last done. *)
  (*     rewrite /region_addrs_zeroes finz_dist_0; last done. *)
  (*     done. *)
  (*   - assert (csp_a < csp_e)%a as Hstk_bounds2' by solve_addr. *)
  (*     (* Jnz 2%Z r1; *) *)
  (*     iInstr "Hcode". *)
  (*     { assert (csp_a - csp_e ≠ 0)%Z by solve_addr. congruence. } *)
  (*     (* Store r2 0%Z; *) *)
  (*     rewrite finz_dist_S in Hlen_stack; last done. *)
  (*     destruct ws as [|w' ws]; first by cbn in *. *)
  (*     iDestruct (region_pointsto_cons with "Hstack") as "[Hcsp_a Hstack]". *)
  (*     { transitivity (Some (csp_a ^+ 1)%a); solve_addr. } *)
  (*     { solve_addr. } *)
  (*     iInstr "Hcode". *)
  (*     { solve_addr. } *)
  (*     (* Lea r2 1%Z; *) *)
  (*     iInstr_lookup "Hcode" as "Hi" "Hcont". *)
  (*     wp_instr. *)
  (*     iApply (wp_lea_success_z with "[HPC Hr2 Hi]"); try iFrame; try solve_pure. *)
  (*     { transitivity (Some (csp_a ^+ 1)%a); solve_addr. } *)
  (*     iNext. *)
  (*     iIntros "(HPC & Hi & Hr2)". *)
  (*     iDestruct ("Hcont" with "Hi") as "Hcode"; wp_pure. *)

  (*     (* Add r1 r1 1%Z; *) *)
  (*     iInstr "Hcode". *)
  (*     (* Jmp (-5)%Z; *) *)
  (*     iInstr "Hcode". *)
  (*     { transitivity (Some (pc_a ^+2)%a); solve_addr. } *)
  (*     replace (csp_a - csp_e + 1)%Z with ((csp_a ^+ 1)%a - csp_e)%Z by solve_addr. *)
  (*     iApply ("IH" with "[$] [$] [$] [$] [$] [Hφ]"). *)
  (*     + iNext. iIntros "(HPC & Hstack & H & Hcode)". *)
  (*       iApply "Hφ"; iFrame. *)
  (*     + iPureIntro. cbn in Hlen_stack; lia. *)
  (*     + iPureIntro ; solve_addr. *)
  (*     + iPureIntro ; solve_addr. *)
  (* Qed. *)


  Lemma clear_stack_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (csp_b csp_e csp_a : Addr)
    (r1 r2 : RegName) (ws : list Word)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs r1 r2))%a ->
    (csp_b <= csp_a)%a -> (csp_a <= csp_e)%a ->
    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_a
      ∗ r1 ↦ᵣ WInt csp_e ∗ r2 ↦ᵣ WInt csp_a
      ∗ codefrag pc_a (clear_stack_instrs r1 r2)
      ∗ ([[ csp_a , csp_e ]] ↦ₐ [[ ws ]])
      ∗ ▷ ( (PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a
             ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_a
             ∗ r1 ↦ᵣ WInt 0 ∗ r2 ↦ᵣ WCap RWL Local csp_b csp_e csp_a
             ∗ codefrag pc_a (clear_stack_instrs r1 r2)
             ∗ ([[ csp_a , csp_e ]] ↦ₐ [[region_addrs_zeroes csp_a csp_e]]))
        -∗ WP Seq (Instr Executable) {{ φ }})
    )
      ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    (* iIntros (Hpc_exec Hbounds Hstk_bounds1 Hstk_bounds2) *)
    (*   "(HPC & Hcsp & Hr1 & Hr2 & Hcode & Hstack & Hφ)". *)
    (* iDestruct (big_sepL2_length with "Hstack") as "%Hlen_stk". *)
    (* codefrag_facts "Hcode". *)

    (* (* Sub r1 r2 r1; *) *)
    (* iInstr "Hcode". *)
    (* (* Mov r2 csp; *) *)
    (* iInstr "Hcode". *)
    (* iApply (clear_stack_spec_iter with "[Hcsp Hφ $HPC $Hcode $Hr1 $Hr2 $Hstack]"); eauto. *)
    (* iNext. *)
    (* iIntros "(HPC & H & Hcode)". *)
    (* iDestruct "H" as (cps_a0) "(Hr2 & Hr1 & %Hprogress & Hstack)". *)
    (* rewrite Hprogress. *)
    (* iApply "Hφ"; iFrame. *)

    (* iRevert (Hlen_stack Hstk_bounds1 Hstk_bounds2). *)
    (* iLöb as "IH" forall (csp_a ws); iIntros (Hlen_stack Hstl_bounds1 Hstk_bounds2). *)
    (* destruct (decide (csp_a = csp_e) )%Z as [Heq|Hneq]. *)
    (* - subst csp_a. rewrite (_: csp_e - csp_e = 0)%Z; last lia. *)
    (*   (* Jnz 2%Z r1; *) *)
    (*   iInstr "Hcode". *)
    (*   (* Jmp 5%Z; *) *)
    (*   iInstr "Hcode". *)
    (*   iApply "Hφ". *)
    (*   iFrame. *)
    (*   rewrite /region_pointsto. *)
    (*   rewrite finz_seq_between_empty; last done. *)
    (*   rewrite /region_addrs_zeroes finz_dist_0; last done. *)
    (*   done. *)
    (* - assert (csp_a < csp_e)%a as Hstk_bounds2' by solve_addr. *)
    (*   (* Jnz 2%Z r1; *) *)
    (*   iInstr "Hcode". *)
    (*   { assert (csp_a - csp_e ≠ 0)%Z by solve_addr. congruence. } *)
    (*   (* Store r2 0%Z; *) *)
    (*   rewrite finz_dist_S in Hlen_stack; last done. *)
    (*   destruct ws as [|w' ws]; first by cbn in *. *)
    (*   iDestruct (region_pointsto_cons with "Hstack") as "[Hcsp_a Hstack]". *)
    (*   { transitivity (Some (csp_a ^+ 1)%a); solve_addr. } *)
    (*   { solve_addr. } *)
    (*   iInstr "Hcode". *)
    (*   { solve_addr. } *)
    (*   (* Lea r2 1%Z; *) *)
    (*   iInstr_lookup "Hcode" as "Hi" "Hcont". *)
    (*   wp_instr. *)
    (*   iApply (wp_lea_success_z with "[HPC Hr2 Hi]"); try iFrame; try solve_pure. *)
    (*   { transitivity (Some (csp_a ^+ 1)%a); solve_addr. } *)
    (*   iNext. *)
    (*   iIntros "(HPC & Hi & Hr2)". *)
    (*   iDestruct ("Hcont" with "Hi") as "Hcode"; wp_pure. *)

    (*   (* Add r1 r1 1%Z; *) *)
    (*   iInstr "Hcode". *)
    (*   (* Jmp (-5)%Z; *) *)
    (*   iInstr "Hcode". *)
    (*   { transitivity (Some (pc_a ^+2)%a); solve_addr. } *)
    (*   replace (csp_a - csp_e + 1)%Z with ((csp_a ^+ 1)%a - csp_e)%Z by solve_addr. *)
    (*   iApply ("IH" with "[$] [] [$] [$] [$] [$] [Hcsp]"). *)
    (*   + admit. *)
    (*   + *)
    (*   + admit. *)
    (*   + admit. *)
    (*   + admit. *)
  Admitted.

End ClearStackMacro.
