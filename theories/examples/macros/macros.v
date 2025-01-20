From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine.proofmode Require Import tactics_helpers map_simpl solve_pure.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.
From cap_machine Require Export malloc assert fetch rclear mclear reqperm.

Section macros.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- ASSERT ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  Definition assert_instrs f_a :=
    fetch_instrs f_a ++
    [move_r r_t2 r_t0;
     move_r r_t0 PC;
     lea_z r_t0 3;
     jmp r_t1;
     move_r r_t0 r_t2;
     move_z r_t1 0;
     move_z r_t2 0].

  Definition assert a f_a :=
    ([∗ list] a_i;w_i ∈ a;(assert_instrs f_a), a_i ↦ₐ w_i)%I.

  (* Spec for assertion success *)
  (* Since we are not jumping to the failure subroutine, we do not need any assumptions
     about the failure subroutine *)
  Lemma assert_success a f_a pc_p pc_b pc_e a_first a_last
        b_link e_link a_link a_entry w0 w1 w2 w3 n1 n2
        ba a_flag ea assertN EN φ :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    (* linking table assumptions *)
    withinBounds b_link e_link a_entry = true →
    (a_link + f_a)%a = Some a_entry →
    ↑assertN ⊆ EN →
    (* condition for assertion success *)
    (n1 = n2) →

    ▷ assert a f_a
    ∗ na_inv logrel_nais assertN (assert_inv ba a_flag ea)
    ∗ na_own logrel_nais EN
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E ba ea ba
    ∗ ▷ r_t0 ↦ᵣ w0
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_t4 ↦ᵣ WInt n1
    ∗ ▷ r_t5 ↦ᵣ WInt n2
    ∗ ▷ (r_t0 ↦ᵣ w0 ∗
         r_t1 ↦ᵣ WInt 0%Z ∗ r_t2 ↦ᵣ WInt 0%Z ∗ r_t3 ↦ᵣ WInt 0%Z
         ∗ r_t4 ↦ᵣ WInt 0%Z ∗ r_t5 ↦ᵣ WInt 0%Z
         ∗ PC ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ assert a f_a
         ∗ na_own logrel_nais EN
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link ∗ a_entry ↦ₐ WCap E ba ea ba
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Htable HN Hsuccess)
            "(>Hprog & #Hinv & Hna & >HPC & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & >Hr_t5 & Hφ)".
     (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iApply (fetch_spec with "[- $HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b]");
      [|apply Hcont_fetch|apply Hwb|apply Htable|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a0 l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst a0.
    (* move r_t2 r_t0 *)
    destruct l';[inversion Hlength_rest|]. subst n2.
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t2 $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|].
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t0)"; iCombine "Hfetch" "Hi" as "Hprog_done".
    (* move r_t0 PC *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 3 *)
    destruct l';[inversion Hlength_rest|].
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    assert (pc_p ≠ E).
    { assert (isCorrectPC (WCap pc_p pc_b pc_e a_first)) as HH.
      { apply Hvpc. split. solve_addr.
        apply contiguous_between_length in Hcont.
        rewrite Heqapp length_app /= in Hcont. solve_addr. }
      destruct pc_p; inversion HH; destruct_or?; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|..].
    { iContiguous_next Hcont_rest 2. }
    { eapply (contiguous_between_incr_addr_middle' _ _ _ 1%nat 3).
      apply Hcont_rest. 2: done. 2: done. cbn. lia. } auto.
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jmp r_t1 *)
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* assert routine *)
    iApply (assert_success_spec with "[- $Hinv $Hna $HPC $Hr_t0 $Hr_t4 $Hr_t5]"); auto.
    iNext. iIntros "(Hna & HPC & Hr_t0 & Hr_t4 & Hr_t5)".
    rewrite updatePcPerm_cap_non_E//.
    (* move r_t0 r_t2 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 4|].
    iEpilogue "(HPC & Hi & Hr_t0 & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 0 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 5|].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    destruct l';[|inversion Hlength_rest].
    apply contiguous_between_last with (ai:=f4) in Hcont_rest as Hlink';[|auto].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlink'|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* Continuation *)
    iApply "Hφ". iFrame.
    rewrite Heqapp /=. iDestruct "Hprog_done" as "(?&?&?&?&?&?&?&?)". iFrame. done.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- MALLOC ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* malloc stores the result in r_t1, rather than a user chosen destination.
     f_m is the offset of the malloc capability *)
  Definition malloc_instrs f_m size :=
    fetch_instrs f_m ++
    [move_r r_t5 r_t0;
    move_r r_t3 r_t1;
    move_z r_t1 size;
    move_r r_t0 PC;
    lea_z r_t0 3;
    jmp r_t3;
    move_r r_t0 r_t5;
    move_z r_t5 0].

  Definition malloc f_m size a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(malloc_instrs f_m size), a_i ↦ₐ w_i)%I.

  (* malloc spec *)
  Lemma malloc_spec φ size cont a pc_p pc_b pc_e a_first a_last
        b_link e_link a_link f_m a_entry mallocN b_m e_m EN rmap :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    size > 0 →

    (* malloc program and subroutine *)
    ▷ malloc f_m size a
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ malloc f_m size a
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ WCap RWX b e b
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=WInt 0%Z]>
                               (<[r_t3:=WInt 0%Z]>
                                (<[r_t4:=WInt 0%Z]>
                                 (<[r_t5:=WInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *)
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iApply (fetch_spec with "[- $HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b]");
      [|apply Hcont_fetch|apply Hwb|apply Ha_entry|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst.
    (* move r_t5 r_t0 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t5 $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_t5 & Hr_t0)". iCombine "Hprog_done" "Hfetch" as "Hprog_done".
    (* move r_t3 r_t1 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 size *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t0 PC *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 3|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 3 *)
    destruct l';[inversion Hlength_rest|]. destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    assert ((f1 + 3)%a = Some f4) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 3 3 f1 f4) in Hcont_rest; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | -> ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jmp r_t3 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|].
    iEpilogue "(HPC & Hi & Hr_t3) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* we are now ready to use the malloc subroutine spec. For this we prepare the registers *)
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      by rewrite lookup_delete_ne // lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete_ne // lookup_delete_ne // lookup_delete.
    map_simpl "Hregs".
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      by simplify_map_eq. map_simpl "Hregs".
    iApply (wp_wand with "[-]").
    iApply (simple_malloc_subroutine_spec with "[- $Hmalloc $Hna $Hregs $Hr_t0 $HPC $Hr_t1]"); auto.
    { rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      rewrite !difference_difference_l_L !singleton_union_difference_L !all_registers_union_l.
      f_equal. }
    (* { lia. } *)
    iNext.
    rewrite updatePcPerm_cap_non_E.
    2: { eapply isCorrectPC_range_perm_non_E; eauto.
         generalize (contiguous_between_length _ _ _ Hcont_rest). cbn.
         clear; solve_addr. }
    iIntros "((Hna & Hregs) & Hr_t0 & HPC & Hbe) /=".
    iDestruct "Hbe" as (b e size' Hsize' Hbe) "(Hr_t1 & Hbe)". inversion Hsize'; subst size'.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]".
      by rewrite lookup_insert_ne // lookup_insert //.
      rewrite delete_insert_ne // delete_insert_delete.
      repeat (rewrite delete_insert_ne //;[]). rewrite delete_insert_delete.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]".
      by (repeat (rewrite lookup_insert_ne //;[]); rewrite lookup_insert //).
      repeat (rewrite delete_insert_ne //;[]). rewrite delete_insert_delete.
    (* move r_t0 r_t5 *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 6|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0 & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t5 0 *)
    destruct l';[| by inversion Hlength_rest].
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=f5) in Hcont_rest as Hlast;[|auto].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ". 2: auto.
    iFrame "HPC". iSplitL "Hprog_done".
    { rewrite Heqapp. repeat (iDestruct "Hprog_done" as "[$ Hprog_done]"). iFrame. done. }
    iFrame.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      simplify_map_eq. auto.
    repeat (rewrite (insert_commute _ r_t5) //;[]).
    map_simpl "Hregs". rewrite (insert_commute _ r_t2 r_t3); auto.
  Qed.

  (* malloc spec - alternative formulation *)
  Lemma malloc_spec_alt φ ψ size cont a pc_p pc_b pc_e a_first a_last
        b_link e_link a_link f_m a_entry mallocN b_m e_m EN rmap :
    isCorrectPC_range pc_p pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    withinBounds b_link e_link a_entry = true →
    (a_link + f_m)%a = Some a_entry →
    dom rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    size > 0 →

    (* malloc program and subroutine *)
    ▷ malloc f_m size a
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ WCap RO b_link e_link a_link
    ∗ ▷ a_entry ↦ₐ WCap E b_m e_m b_m
    (* register state *)
    ∗ ▷ PC ↦ᵣ WCap pc_p pc_b pc_e a_first
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* failure/continuation *)
    ∗ ▷ (∀ v, ψ v -∗ φ v)
    ∗ ▷ (ψ FailedV)
    ∗ ▷ (PC ↦ᵣ WCap pc_p pc_b pc_e a_last ∗ malloc f_m size a
         ∗ pc_b ↦ₐ WCap RO b_link e_link a_link
         ∗ a_entry ↦ₐ WCap E b_m e_m b_m
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ WCap RWX b e b
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=WInt 0%Z]>
                               (<[r_t3:=WInt 0%Z]>
                                (<[r_t4:=WInt 0%Z]>
                                 (<[r_t5:=WInt 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (finz.seq_between b e)⌝ *)
         -∗ WP Seq (Instr Executable) {{ ψ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hψ & Hφfailed & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite -elem_of_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]". by rewrite !lookup_delete_ne //.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iApply (fetch_spec with "[- $HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b]");
      [|apply Hcont_fetch|apply Hwb|apply Ha_entry|].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst.
    (* move r_t5 r_t0 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t5 $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 0|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_t5 & Hr_t0)". iCombine "Hprog_done" "Hfetch" as "Hprog_done".
    (* move r_t3 r_t1 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 size *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t0 PC *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 3|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t0 3 *)
    destruct l';[inversion Hlength_rest|]. destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    assert ((f1 + 3)%a = Some f4) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 3 3 f1 f4) in Hcont_rest; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | -> ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jmp r_t3 *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|].
    iEpilogue "(HPC & Hi & Hr_t3) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* we are now ready to use the malloc subroutine spec. For this we prepare the registers *)
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      by rewrite lookup_delete_ne // lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t2 with "[$Hregs $Hr_t2]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete_ne // lookup_delete_ne // lookup_delete.
    rewrite -(delete_insert_ne _ r_t5 r_t3) // insert_delete_insert.
    rewrite -(delete_insert_ne _ r_t5 r_t2) //.
    rewrite (insert_commute ((delete r_t2 _)) r_t2 r_t3) //.
    rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      by rewrite lookup_delete. rewrite insert_delete_insert.
    iApply (wp_wand with "[- Hφfailed Hψ]").
    iApply (simple_malloc_subroutine_spec with "[- $Hmalloc $Hna $Hregs $Hr_t0 $HPC $Hr_t1]"); auto.
    { rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      rewrite !difference_difference_l_L !singleton_union_difference_L !all_registers_union_l.
      f_equal. }
    (* { lia. } *)
    iNext.
    rewrite updatePcPerm_cap_non_E.
    2: { eapply isCorrectPC_range_perm_non_E; eauto.
         generalize (contiguous_between_length _ _ _ Hcont_rest). cbn.
         clear; solve_addr. }
    iIntros "((Hna & Hregs) & Hr_t0 & HPC & Hbe) /=".
    iDestruct "Hbe" as (b e size' Hsize' Hbe) "(Hr_t1 & Hbe)". inversion Hsize';subst size'.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]".
      by rewrite lookup_insert_ne // lookup_insert //.
      rewrite delete_insert_ne // delete_insert_delete.
      repeat (rewrite delete_insert_ne //;[]). rewrite delete_insert_delete.
    iDestruct (big_sepM_delete _ _ r_t5 with "Hregs") as "[Hr_t5 Hregs]".
      by (repeat (rewrite lookup_insert_ne //;[]); rewrite lookup_insert //).
      repeat (rewrite delete_insert_ne //;[]). rewrite delete_insert_delete.
    (* move r_t0 r_t5 *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 6|auto|..].
    iEpilogue "(HPC & Hi & Hr_t0 & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t5 0 *)
    destruct l';[| by inversion Hlength_rest].
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=f5) in Hcont_rest as Hlast;[|auto].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ". 2: iIntros (v) "[Hφ|Hφ] /="; iApply "Hψ"; iSimplifyEq; iFrame.
    iFrame "HPC". iSplitL "Hprog_done".
    { rewrite Heqapp. repeat (iDestruct "Hprog_done" as "[$ Hprog_done]"). iFrame. done. }
    iFrame.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      repeat (rewrite lookup_insert_ne //;[]).
      rewrite lookup_delete_ne // lookup_delete //.
    repeat (rewrite (insert_commute _ r_t5) //;[]).
    rewrite insert_delete_insert -(delete_insert_ne _ _ r_t5) //.
    rewrite (insert_commute _ r_t5 r_t2) // (delete_insert_ne _ r_t3 r_t2)//.
    rewrite (insert_commute _ r_t4 r_t2) // insert_insert.
    rewrite (insert_commute _ r_t3 r_t2) //.
    rewrite -(delete_insert_ne _ r_t3) // insert_delete_insert.
    iFrame.
    auto.
  Qed.

End macros.
