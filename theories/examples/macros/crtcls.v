From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel.
From cap_machine Require Export addr_reg_sample region_macros contiguous stack_macros_helpers malloc fetch
     awkward_example_helpers.
From cap_machine.rules Require Import rules_StoreU_derived rules_LoadU_derived.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

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
  Lemma malloc_spec W size cont a pc_p pc_g pc_b pc_e a_first a_last
        b_link e_link a_link f_m a_entry mallocN b_m e_m EN rmap φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0 ]} →
    ↑mallocN ⊆ EN →
    size > 0 →

    (* malloc program and subroutine *)
    ▷ malloc f_m size a
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset f_m *)
    ∗ ▷ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ inr (E,Global,b_m,e_m,b_m)
    (* register state *)
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* current world *)
    ∗ ▷ region W
    ∗ ▷ sts_full_world W
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ malloc f_m size a
         ∗ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link)
         ∗ a_entry ↦ₐ inr (E,Global,b_m,e_m,b_m)
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr),
            ⌜(b + size)%a = Some e⌝
            ∗ r_t1 ↦ᵣ inr (RWX,Global,b,e,b)
            ∗ [[b,e]] ↦ₐ [[region_addrs_zeroes b e]])
         ∗ r_t0 ↦ᵣ cont
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ (<[r_t2:=inl 0%Z]>
                               (<[r_t3:=inl 0%Z]>
                                (<[r_t4:=inl 0%Z]>
                                 (<[r_t5:=inl 0%Z]> (delete r_t1 rmap))))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (region_addrs b e)⌝ *)
         ∗ region W
         ∗ sts_full_world W
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom HmallocN Hsize)
            "(>Hprog & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >HPC & >Hr_t0 & >Hregs & Hr & Hsts & Hφ)".
    (* extract necessary registers from regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t1)) as [rv1 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t2)) as [rv2 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]". by rewrite lookup_delete_ne //.
    assert (is_Some (rmap !! r_t3)) as [rv3 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]". by rewrite !lookup_delete_ne //.
    assert (is_Some (rmap !! r_t5)) as [rv5 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
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
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
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
    assert ((a1 + 3)%a = Some a4) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 3 3 a1 a4) in Hcont_rest; auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | [-> | ->] ]; auto. }
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | [-> | ->] ]; auto. }
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
    rewrite -(delete_insert_ne _ r_t5 r_t3) // insert_delete.
    rewrite -(delete_insert_ne _ r_t5 r_t2) // (insert_commute _ r_t2 r_t3) //.
    rewrite insert_delete.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      by rewrite lookup_delete. rewrite insert_delete.
    iApply (wp_wand with "[-]").
    iApply (simple_malloc_subroutine_spec with "[- $Hmalloc $Hna $Hregs $Hr_t0 $HPC $Hr_t1]"); auto.
    { rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      rewrite !difference_difference_L !singleton_union_difference_L !all_registers_union_l.
      f_equal. set_solver-. }
    iNext.
    rewrite updatePcPerm_cap_non_E.
    2: { eapply isCorrectPC_range_npE; eauto.
         generalize (contiguous_between_length _ _ _ Hcont_rest). cbn.
         clear; solve_addr. }
    iIntros "((Hna & Hregs) & Hr_t0 & HPC & Hbe) /=".
    iDestruct "Hbe" as (b e z Hbe Hbounds Hpos Hsizebe) "(Hr_t1 & Hbe)". inversion Hbe; subst z.
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
    apply contiguous_between_last with (ai:=a5) in Hcont_rest as Hlast;[|auto]. 
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t5]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t5)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame "HPC". iSplitL "Hprog_done".
    { rewrite Heqapp. repeat (iDestruct "Hprog_done" as "[$ Hprog_done]"). iFrame. done. }
    iFrame.
    iDestruct (big_sepM_insert _ _ r_t5 with "[$Hregs $Hr_t5]") as "Hregs".
      repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete.
    iDestruct (big_sepM_insert _ _ r_t3 with "[$Hregs $Hr_t3]") as "Hregs".
      repeat (rewrite lookup_insert_ne //;[]).
      rewrite lookup_delete_ne // lookup_delete //.
    repeat (rewrite (insert_commute _ r_t5) //;[]).
    rewrite insert_delete -(delete_insert_ne _ _ r_t5) //.
    rewrite (insert_commute _ r_t5 r_t2) // (delete_insert_ne _ r_t3 r_t2)//.
    rewrite (insert_commute _ r_t4 r_t2) // insert_insert.
    rewrite (insert_commute _ r_t3 r_t2) //.
    rewrite -(delete_insert_ne _ r_t3) // insert_delete.
    iFrame.
    iExists b,e. iFrame. auto. auto.
  Qed.

  (* ---------------------------------------- CRTCLS ------------------------------------ *)
  (* The following macro creates a closure with one variable. A more general create closure would 
     allow for more than one variable in the closure, but this is so far not necessary for our 
     examples. The closure allocates a new region with a capability to the closure code, the closure 
     variable, and the closure activation *)

  (* encodings of closure activation code *)
  Definition v1 := encodeInstr (Mov r_t1 (inr PC)).
  Definition v2 := encodeInstr (Lea r_t1 (inl 7%Z)).
  Definition v3 := encodeInstr (Load r_env r_t1).
  Definition v4 := encodeInstr (Lea r_t1 (inl (-1)%Z)).
  Definition v5 := encodeInstr (Load r_t1 r_t1).
  Definition v6 := encodeInstr (Jmp r_t1).

  (* crtcls instructions *)
  (* f_m denotes the offset to the malloc capability in the lookup table *)
  (* crtcls assumes that the code lies in register r_t1 and the variable lies in r_t2 *)
  Definition crtcls_instrs f_m :=
    [move_r r_t6 r_t1;
    move_r r_t7 r_t2] ++
    malloc_instrs f_m 8%nat ++
    [store_z r_t1 v1;
    lea_z r_t1 1;
    store_z r_t1 v2;
    lea_z r_t1 1;
    store_z r_t1 v3;
    lea_z r_t1 1;
    store_z r_t1 v4;
    lea_z r_t1 1;
    store_z r_t1 v5;
    lea_z r_t1 1;
    store_z r_t1 v6;
    lea_z r_t1 1;
    store_r r_t1 r_t6;
    move_z r_t6 0;
    lea_z r_t1 1;
    store_r r_t1 r_t7;
    move_z r_t7 0;
    lea_z r_t1 (-7)%Z;
    restrict_z r_t1 global_e].

  Definition crtcls f_m a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(crtcls_instrs f_m), a_i ↦ₐ w_i)%I.

  (* crtcls spec *)
  Lemma crtcls_spec W f_m wvar wcode a pc_p pc_g pc_b pc_e
        a_first a_last b_link a_link e_link a_entry b_m e_m mallocN EN rmap cont φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_m)%a = Some a_entry →
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_t0; r_t1; r_t2 ]} →
    isLocalWord wcode = false → (* the closure must be a Global Word! *)
    isLocalWord wvar = false → (* the closure must be a Global Word! *)
    ↑mallocN ⊆ EN →

      ▷ crtcls f_m a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ na_own logrel_nais EN
    (* we need to assume that the malloc capability is in the linking table at offset 0 *)
    ∗ ▷ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ inr (E,Global,b_m,e_m,b_m)
    (* register state *)
    ∗ ▷ r_t0 ↦ᵣ cont
    ∗ ▷ r_t1 ↦ᵣ wcode
    ∗ ▷ r_t2 ↦ᵣ wvar
    ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
    (* current world *)
    ∗ ▷ region W
    ∗ ▷ sts_full_world W
    (* continuation *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ crtcls f_m a
         ∗ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link)
         ∗ a_entry ↦ₐ inr (E,Global,b_m,e_m,b_m)
         (* the newly allocated region *)
         ∗ (∃ (b e : Addr), ⌜(b + 8)%a = Some e⌝ ∧ r_t1 ↦ᵣ inr (E,Global,b,e,b)
         ∗ [[b,e]] ↦ₐ [[ [inl v1;inl v2;inl v3;inl v4;inl v5;inl v6;wcode;wvar] ]]
         ∗ r_t0 ↦ᵣ cont
         ∗ r_t2 ↦ᵣ inl 0%Z
         ∗ na_own logrel_nais EN
         ∗ ([∗ map] r_i↦w_i ∈ <[r_t3:=inl 0%Z]>
                               (<[r_t4:=inl 0%Z]>
                                (<[r_t5:=inl 0%Z]>
                                 (<[r_t6:=inl 0%Z]>
                                  (<[r_t7:=inl 0%Z]> rmap)))), r_i ↦ᵣ w_i)
         (* the newly allocated region is fresh in the current world *)
         (* ∗ ⌜Forall (λ a, a ∉ dom (gset Addr) (std W)) (region_addrs b e)⌝ *)
         ∗ region W
         ∗ sts_full_world W)
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Ha_entry Hrmap_dom Hlocal Hlocal' HmallocN)
            "(>Hprog & >HPC & #Hmalloc & Hna & >Hpc_b & >Ha_entry & >Hr_t0 & >Hr_t1 & >Hr_t2 & >Hregs & Hr & Hsts & Hφ)".
    (* get some registers out of regs *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    assert (is_Some (rmap !! r_t6)) as [rv6 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]"; eauto.
    assert (is_Some (rmap !! r_t7)) as [rv7 ?]. by rewrite elem_of_gmap_dom Hrmap_dom; set_solver.
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]". by rewrite lookup_delete_ne //.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* move r_t6 r_t1 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t6 $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|].
    iEpilogue "(HPC & Hprog_done & Hr_t6 & Hr_t1)".
    (* move r_t7 r_t2 *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t7 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 1|].
    iEpilogue "(HPC & Hi & Hr_t7 & Hr_t2)"; iCombine "Hi Hprog_done" as "Hprog_done".
    assert (contiguous_between (a0 :: l) a0 a_last) as Hcont'.
    { apply contiguous_between_cons_inv in Hcont as [_ (? & ? & Hcont)].
      apply contiguous_between_cons_inv in Hcont as [_ (? & ? & Hcont)].
      pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). subst. apply Hcont. }
    (* malloc 8 *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (malloc_prog rest link) "(Hmalloc_prog & Hprog & #Hcont)";[apply Hcont'|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    (* we start by putting the registers back together *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs".
      by rewrite lookup_delete_ne // lookup_delete.
      rewrite delete_commute // insert_delete.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs".
      by rewrite lookup_insert_ne // lookup_delete.
      rewrite insert_commute // insert_delete.
    assert (∀ (r:RegName), r ∈ ({[PC;r_t0;r_t1;r_t2]} : gset RegName) → rmap !! r = None) as Hnotin_rmap.
    { intros r Hr. eapply (@not_elem_of_dom _ _ (gset RegName)). typeclasses eauto.
      rewrite Hrmap_dom. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs".
      by rewrite !lookup_insert_ne //; apply Hnotin_rmap; set_solver.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs".
      by rewrite !lookup_insert_ne //; apply Hnotin_rmap; set_solver.
    (* apply the malloc spec *)
    rewrite -/(malloc _ _ _ _).
    iApply (malloc_spec with "[- $HPC $Hmalloc $Hna $Hpc_b $Ha_entry $Hr_t0 $Hregs $Hr $Hsts $Hmalloc_prog]");
      [|apply Hcont_fetch|apply Hwb|apply Ha_entry| |auto|lia|..].
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest.
      apply contiguous_between_incr_addr with (i:=2) (ai:=a0) in Hcont;auto.
      revert Hcont Hcont_rest Hmid; clear. solve_addr. }
    { rewrite !dom_insert_L. rewrite Hrmap_dom.
      repeat (rewrite singleton_union_difference_L all_registers_union_l).
      f_equal. clear; set_solver. }
    iNext. iIntros "(HPC & Hmalloc_prog & Hpc_b & Ha_entry & Hbe & Hr_t0 & Hna & Hregs & Hr & Hsts)".
    iDestruct "Hbe" as (b e Hbe) "(Hr_t1 & Hbe)".
    rewrite delete_insert_delete.
    rewrite (delete_insert_ne _ r_t1 r_t2) //.
    repeat (rewrite (insert_commute _ _ r_t2) //;[]).
    rewrite insert_insert.
    (* we now want to infer a list of contiguous addresses between b and e *)
    assert (b < e)%a as Hlt;[solve_addr|]. 
    assert (contiguous (region_addrs b e)) as Hcontbe';[apply region_addrs_contiguous|].
    apply contiguous_iff_contiguous_between in Hcontbe'. destruct Hcontbe' as [b' [e' Hcontbe] ].
    assert (exists l, l = region_addrs b e) as [h Heqh];[eauto|].
    rewrite -Heqh in Hcontbe.
    rewrite /region_mapsto /region_addrs_zeroes -Heqh.
    assert (region_size b e = 8) as ->.
    { rewrite /region_size. revert Hbe; clear; solve_addr. }
    simpl.
    (* prepare the execution of the rest of the program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_incr_addr with (i:=2) (ai:=a0) in Hcont;auto.
      revert Hcont Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a1 l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst link. 
    iDestruct (big_sepL2_length with "Hbe") as %Hlengthbe. 
    destruct h;[inversion Hlengthbe|]. 
    apply region_addrs_first in Hlt as Hfirst. rewrite -Heqh in Hfirst; inversion Hfirst. subst a2.
    apply contiguous_between_cons_inv_first in Hcontbe as Heq. subst b'. 
    assert (∀ i a', (b :: h) !! i = Some a' -> withinBounds (RWX, Global, b, e, a') = true) as Hwbbe.
    { intros i a' Hsome. apply andb_true_intro.
      apply contiguous_between_incr_addr with (i:=i) (ai:=a') in Hcontbe;[|congruence].
      apply lookup_lt_Some in Hsome. rewrite Heqh region_addrs_length in Hsome. 
      revert Hsome Hcontbe Hbe. rewrite /region_size. clear; intros. split;[apply Z.leb_le|apply Z.ltb_lt];solve_addr.
    }
    iCombine "Hmalloc_prog" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v1 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 0|..].
    { split;auto. apply Hwbbe with 0. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Heb)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 1|iContiguous_next Hcontbe 0|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v2 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 2|..].
    { split;auto. apply Hwbbe with 1. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 3|iContiguous_next Hcontbe 1|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v3 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 4|..].
    { split;auto. apply Hwbbe with 2. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 5|iContiguous_next Hcontbe 2|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v4 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 6|..].
    { split;auto. apply Hwbbe with 3. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 7|iContiguous_next Hcontbe 3|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v5 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 8|..].
    { split;auto. apply Hwbbe with 4. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 9|iContiguous_next Hcontbe 4|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 v6 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hb]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 10|..].
    { split;auto. apply Hwbbe with 5. auto. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb". 
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 11|iContiguous_next Hcontbe 5|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 r_t6 *)
    (* first we must extract r_t6 *)
    iDestruct (big_sepM_delete _ _ r_t6 with "Hregs") as "[Hr_t6 Hregs]".
      by rewrite !lookup_insert_ne // lookup_delete_ne // lookup_insert //.
    (* then we can store *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t6 $Hr_t1 $Hb]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 12|..].
    { split;auto. apply Hwbbe with 6. auto. }
    { destruct wcode;auto. destruct c,p,p,p,p,l0;auto;inversion Hlocal'. }

    iEpilogue "(HPC & Hi & Hr_t6 & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb".
    (* move r_t6 0 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t6]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 13|auto..].
    iEpilogue "(HPC & Hi & Hr_t6)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 1 *)
    destruct l';[inversion Hlength_rest|].
    destruct h;[inversion Hlengthbe|]. 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 14|iContiguous_next Hcontbe 6|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* store r_t1 r_t7 *)
    (* first we must extract r_t7 *)
    iDestruct (big_sepM_delete _ _ r_t7 with "Hregs") as "[Hr_t7 Hregs]".
      rewrite lookup_delete_ne // !lookup_insert_ne // lookup_delete_ne //
              lookup_insert_ne // lookup_insert //.
    (* then we can store *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iDestruct "Hbe" as "[Hb Hbe]". 
    iApply (wp_store_success_reg with "[$HPC $Hi $Hr_t7 $Hr_t1 $Hb]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 15|..].
    { split;auto. apply Hwbbe with 7. auto. }
    { destruct wvar;auto. destruct c,p,p,p,p,l0;auto;inversion Hlocal. }
    iEpilogue "(HPC & Hi & Hr_t7 & Hr_t1 & Hb)"; iCombine "Hi" "Hprog_done" as "Hprog_done"; iCombine "Hb" "Heb" as "Heb".
    (* move r_t7 0 *)
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog". 
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t7]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 16|auto..].
    iEpilogue "(HPC & Hi & Hr_t7)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* put r_t6 and r_t7 back *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t7]") as "Hregs". by rewrite lookup_delete.
    rewrite insert_delete.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t6]") as "Hregs". by rewrite lookup_insert_ne // lookup_delete.
    rewrite -(delete_insert_ne _ r_t6) // insert_delete.
    iClear "Hbe".
    (* lea r_t1 -7 *)
    destruct h;[|inversion Hlengthbe]. 
    destruct l';[inversion Hlength_rest|]. 
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=a23) in Hcontbe as Hnext; auto.
    assert ((a23 + (-7))%a = Some b) as Hlea.
    { apply contiguous_between_length in Hcontbe. revert Hbe Hnext Hcontbe; clear. solve_addr. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|iContiguous_next Hcont_rest 17|apply Hlea|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* restrict r_t1 (Global,E) *)
    destruct l';[|inversion Hlength_rest].
    apply contiguous_between_last with (ai:=a26) in Hcont_rest as Hlast; auto.
    iPrologue "Hprog". iClear "Hprog". 
    iApply (wp_restrict_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a1 a_last|apply Hlast|auto..].
    { rewrite decode_encode_permPair_inv. auto. }
    rewrite decode_encode_permPair_inv.
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame "HPC Hpc_b Ha_entry". iSplitL "Hprog_done".
    { rewrite Heqapp.
      do 22 iDestruct "Hprog_done" as "[$ Hprog_done]". iFrame. done. 
    }
    iExists b,e. iSplitR;auto.
    iFrame "Hr_t1 Hr_t0".
    iSplitL "Heb".
    { rewrite -Heqh. do 7 iDestruct "Heb" as "[$ Heb]". iFrame. done. }
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]".
      by do 2 (rewrite lookup_insert_ne //); rewrite lookup_insert //.
    iFrame "Hr Hsts Hr_t2 Hna".
    repeat (rewrite delete_insert_ne //; []). rewrite delete_insert_delete.
    rewrite !delete_insert_ne // !delete_notin; [| apply Hnotin_rmap; set_solver ..].
    repeat (rewrite (insert_commute _ r_t6) //;[]). rewrite insert_insert.
    repeat (rewrite (insert_commute _ r_t7) //;[]). rewrite insert_insert. eauto.
  Qed.

  (* ------------------------------- Closure Activation --------------------------------- *)

  Lemma closure_activation_spec pc_p pc_g b_cls e_cls r1v renvv wcode wenv φ :
    readAllowed pc_p = true →
    isCorrectPC_range pc_p pc_g b_cls e_cls b_cls e_cls →
    pc_p ≠ E →
    PC ↦ᵣ inr (pc_p, pc_g, b_cls, e_cls, b_cls)
    ∗ r_t1 ↦ᵣ r1v
    ∗ r_env ↦ᵣ renvv
    ∗ [[b_cls, e_cls]]↦ₐ[[ [inl v1; inl v2; inl v3; inl v4; inl v5; inl v6; wcode; wenv] ]]
    ∗ (  PC ↦ᵣ updatePcPerm wcode
       ∗ r_t1 ↦ᵣ wcode
       ∗ r_env ↦ᵣ wenv
       ∗ [[b_cls, e_cls]]↦ₐ[[ [inl v1; inl v2; inl v3; inl v4; inl v5; inl v6; wcode; wenv] ]]
       -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hrpc Hvpc HnpcE) "(HPC & Hr1 & Hrenv & Hcode & Hcont)".
    rewrite /region_mapsto.
    iDestruct (big_sepL2_length with "Hcode") as %Hcls_len. simpl in Hcls_len.
    assert (b_cls + 8 = Some e_cls)%a as Hbe.
    { rewrite region_addrs_length /region_size in Hcls_len.
      revert Hcls_len; clear; solve_addr. }
    assert (contiguous_between (region_addrs b_cls e_cls) b_cls e_cls) as Hcont_cls.
    { apply contiguous_between_of_region_addrs; auto. revert Hbe; clear; solve_addr. }
    pose proof (region_addrs_NoDup b_cls e_cls) as Hcls_nodup.
    iDestruct (big_sepL2_split_at 6 with "Hcode") as "[Hprog Hcls_data]".
    cbn [take drop].
    destruct (region_addrs b_cls e_cls) as [| ? ll]; [by inversion Hcls_len|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_cls). subst.
    do 7 (destruct ll as [| ? ll]; [by inversion Hcls_len|]).
    destruct ll;[| by inversion Hcls_len]. cbn [take drop].
    iDestruct "Hcls_data" as "(Hcls_ptr & Hcls_env & _)".
    (* move r_t1 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|  iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 0 |  ..].
    iEpilogue "(HPC & Hprog_done & Hr1)".
    (* lea r_t1 7 *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 1 | | done | ..].
    { eapply contiguous_between_incr_addr_middle' with (i:=0); eauto.
      cbn. clear. lia. }
    { destruct pc_p; simpl in *; try discriminate; auto. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi Hprog_done" as "Hprog_done".
    (* load r_env r_t1 *)
    iPrologue "Hprog".
    (* FIXME: tedious & fragile *)
    assert ((a5 =? a0)%a = false) as H_5_0.
    { apply Z.eqb_neq. intros Heqb. assert (a5 = a0) as ->. revert Heqb; clear; solve_addr.
      exfalso. by pose proof (NoDup_lookup _ 2 7 _ Hcls_nodup eq_refl eq_refl). }
    iApply (wp_load_success with "[$HPC $Hi $Hrenv $Hr1 Hcls_env]");
      [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls |
       split;[done|] | iContiguous_next Hcont_cls 2 | ..].
    { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?].
      by eapply le_addr_withinBounds; eauto. repeat constructor. }
    { rewrite H_5_0. iFrame. }
    iEpilogue "(HPC & Hrenv & Hi & Hr1 & Hcls_env)". rewrite H_5_0.
    iCombine "Hi Hprog_done" as "Hprog_done".
    (* lea r_t1 (-1) *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls |
       iContiguous_next Hcont_cls 3 | | done | ..].
    { assert ((a4 + 1)%a = Some a5) as HH. by iContiguous_next Hcont_cls 6.
      instantiate (1 := a4). revert HH. clear; solve_addr. }
    { destruct pc_p; simpl in *; try discriminate; auto. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    iPrologue "Hprog".
    (* FIXME: tedious & fragile *)
    assert ((a4 =? a2)%a = false) as H_4_2.
    { apply Z.eqb_neq. intros Heqb. assert (a4 = a2) as ->. revert Heqb; clear; solve_addr.
      exfalso. by pose proof (NoDup_lookup _ 4 6 _ Hcls_nodup eq_refl eq_refl). }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr1 Hcls_ptr]");
      [(* FIXME *) auto | apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls |
       auto | | iContiguous_next Hcont_cls 4 | ..].
    { eapply contiguous_between_middle_bounds' in Hcont_cls as [? ?].
      by eapply le_addr_withinBounds; eauto. repeat constructor. }
    { rewrite H_4_2. iFrame. }
    iEpilogue "(HPC & Hr1 & Hi & Hcls_ptr)". rewrite H_4_2.
    iCombine "Hi Hprog_done" as "Hprog_done".
    (* jmp r_t1 *)
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv | iCorrectPC b_cls e_cls | .. ].
    iEpilogue "(HPC & Hi & Hr1)".

    iApply "Hcont". do 4 (iDestruct "Hprog_done" as "(? & Hprog_done)"). iFrame.
  Qed.

End stack_macros.
