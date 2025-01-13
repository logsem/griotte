From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export addr_reg_sample region_macros contiguous stack_macros_helpers.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (* --------------------------------------------------------------------------------- *)
  (* ---------------------------------- REQINT --------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition reqint_instrs r r1 r2 :=
    [is_ptr r2 r; (* if r -> 0, we want to continue, o/w we want to crash *)
    sub_r_z r2 r2 1; (* we flip the bit for the jnz*)
    move_r r1 PC;
    lea_z r1 4;
    jnz r1 r2;
    fail_end;
    move_z r1 0;
    move_z r2 0].

  Definition reqint a r r1 r2 : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqint_instrs r r1 r2), a_i ↦ₐ w_i)%I.

  (* reqint spec *)
  Lemma reqint_spec a r r1 r2 pc_p pc_g pc_b pc_e a_first a_last φ w w1 w2 :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ reqint a r r1 r2
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ r ↦ᵣ w
    (* if the input is an int, we want to be able to continue *)
    (* if w is not an int, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ φ FailedV
    ∗ ▷ ((∃ z, ⌜w = inl z⌝) ∗ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ reqint a r r1 r2
            ∗ r ↦ᵣ w ∗ r1 ↦ᵣ inl 0%Z ∗ r2 ↦ᵣ inl 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr1 & >Hr2 & >Hr & Hfailed & Hcont)".
    (* argument prep *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    destruct_addr_list a.
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iAssert (⌜r1 ≠ PC⌝)%I as %Hne'.
    { destruct (decide (r1 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr1") as %Hcontr. done. }
    iAssert (⌜r2 ≠ PC⌝)%I as %Hne2.
    { destruct (decide (r2 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr2") as %Hcontr. done. }
    pose proof (pc_range_perm _ _ _ _ _ _ _ Hvpc Hcont) as Hperms.
    (* is_ptr r2 r *)
    iPrologue "Hprog".
    iApply (wp_IsPtr_success with "[$HPC $Hi $Hr $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|].
    iEpilogue "(HPC & Hprog_done & Hr & Hr2)".
    (* sub r2 r2 1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC a_first a_last|].
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done". iSimpl in "Hr2".
    (* move r1 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r1 4 *)
    assert (a1 + 4 = Some a5)%a as Hlea.
    apply contiguous_between_incr_addr_middle with (i:=2) (j:=4) (ai:=a1) (aj:=a5) in Hcont;auto.
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hlea|auto..].
    { destruct Hperms as [-> | [-> | ->] ];auto. }
    { destruct Hperms as [-> | [-> | ->] ];auto. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r2 r *)
    (* we now need to branch on the two cases, based on w *)
    destruct (is_cap w) eqn:Hiscap.
    - (* if w is a capability, we must fail *)
      rewrite Z.sub_diag.
      (* jnz r1 r2 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr1 $Hr2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|].
      iEpilogue "(HPC & Hi & Hr1 & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* fail_end *)
      iPrologue "Hprog".
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iEpilogue "(HPC & Hi)". iApply wp_value. iFrame.
    - (* otherwise we cleanup the temp register and continue *)
      (* jnz r1 r2 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr1 $Hr2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|done|].
      iEpilogue "(HPC & Hi & Hr1 & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      iDestruct "Hprog" as "[Hi Hprog]". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r1 0 *)
      rewrite updatePcPerm_cap_non_E;[|destruct Hperms as [-> | [-> | ->] ];auto].
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|].
      iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r2 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|eapply contiguous_between_last;eauto|].
      iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* Hcont *)
      iApply "Hcont".
      iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$)".
      destruct w;inversion Hiscap. eauto.
  Qed.


  (* --------------------------------------------------------------------------------- *)
  (* -------------------------------- CHECKINTS -------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  (* we will first need a preamble that lowers the bounds of the input capability *)
  (* PRE: r points to a capability with at least RO permission *)
  Definition leabound_instrs r r1 r2 :=
    [getb r1 r;
    geta r2 r;
    sub_r_r r1 r1 r2;
    lea_r r r1;
    move_z r1 0;
    move_z r2 0].

  Definition leabound a r r1 r2 : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(leabound_instrs r r1 r2), a_i ↦ₐ w_i)%I.

  Lemma leabound_spec addrs r r1 r2 pc_p pc_g pc_b pc_e a_first a_last φ w1 w2 p g b e a :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between addrs a_first a_last ->
    readAllowed p = true ->

      ▷ leabound addrs r r1 r2
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ r ↦ᵣ inr (p,g,b,e,a)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ leabound addrs r r1 r2
            ∗ r ↦ᵣ inr (p,g,b,e,b) ∗ r1 ↦ᵣ inl 0%Z ∗ r2 ↦ᵣ inl 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hra) "(>Hprog & >HPC & >Hr1 & >Hr2 & >Hr & Hcont)".
    (* argument prep *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    destruct_addr_list addrs.
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst addrs.
    pose proof (pc_range_perm _ _ _ _ _ _ _ Hvpc Hcont) as Hperms.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iAssert (⌜r1 ≠ PC⌝)%I as %Hne'.
    { destruct (decide (r1 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr1") as %Hcontr. done. }
    iAssert (⌜r2 ≠ PC⌝)%I as %Hne2.
    { destruct (decide (r2 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr2") as %Hcontr. done. }
    (* getb r1 r *)
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr1 $Hr]");
      [apply decode_encode_instrW_inv|eauto|iCorrectPC a_first a_last|iContiguous_next_a Hcont|auto..].
    iEpilogue "(HPC & Hprog_done & Hr & Hr1) /=".
    (* geta r2 r *)
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr2 $Hr]");
      [apply decode_encode_instrW_inv|eauto|iCorrectPC a_first a_last|iContiguous_next_a Hcont|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr2) /=". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub r1 r2 r1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr2 $Hr1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC a_first a_last|].
    iEpilogue "(HPC & Hi & Hr2 & Hr1) /=". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r r1 *)
    assert ((a + (b - a)%Z)%a = Some b) as Hlea;[solve_addr|].
    iPrologue "Hprog".
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr $Hr1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hlea|auto|destruct p;auto;inversion Hra..|].
    { destruct p;auto;inversion Hr. }
    iEpilogue "(HPC & Hi & Hr1 & Hr) /=". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r1 0 *)
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r2 0 *)
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|eapply contiguous_between_last;eauto|].
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* Hcont *)
    iApply "Hcont".
    iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$)".
    done.
  Qed.


  (* next we want to look through each address in the bounds of the ra capability in r *)
  (* PRE: r points to a capability with at least RO permission *)
  Definition checkintsloop_instrs r r1 r2 r3 :=
    [load_r r1 r] ++
    reqint_instrs r1 r2 r3 ++
    [geta r1 r;
    add_r_z r1 r1 1;
    gete r2 r;
    lt_r_r r1 r1 r2;
     (* if r1 -> 0 then a + 1 >= e, and we continue,
        otherwise we jump back to the beginning of the loop *)
    move_r r2 PC;
    lea_z r2 (-1 * (length (reqint_instrs r1 r2 r3) + 5));
    lea_z r 1;
    jnz r2 r1].

  Definition checkintsloop a r r1 r2 r3 : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(checkintsloop_instrs r r1 r2 r3), a_i ↦ₐ w_i)%I.

  Lemma checkintsloop_spec addrs r r1 r2 r3 pc_p pc_g pc_b pc_e a_first a_last φ p g b e a ws :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between addrs a_first a_last ->
    readAllowed p = true ->
    withinBounds (p,g,b,e,a) = true →

    ▷ checkintsloop addrs r r1 r2 r3
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ (∃ w1, r1 ↦ᵣ w1)
    ∗ ▷ (∃ w1, r2 ↦ᵣ w1)
    ∗ ▷ (∃ w1, r3 ↦ᵣ w1)
    ∗ ▷ r ↦ᵣ inr (p,g,b,e,a)
    ∗ ▷ ([∗ list] a;w∈(region_addrs a e);ws, a ↦ₐ w)
    (* if a points to an int, we want to be able to continue *)
    (* if not, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ checkintsloop addrs r r1 r2 r3
            ∗ r ↦ᵣ inr (p,g,b,e,e) ∗ (∃ w, r1 ↦ᵣ w) ∗ (∃ w, r2 ↦ᵣ w) ∗ (∃ w, r3 ↦ᵣ w) ∗ ([∗ list] a;w∈(region_addrs a e);ws, a ↦ₐ w) ∗ ⌜Forall (λ w, ∃ z, w = inl z) ws⌝
            -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hra Hwb) "(>Hprog & >HPC & >Hr1 & >Hr2 & >Hr3 & >Hr & >Hae & Hcont)".
    iLöb as "IH" forall (a ws Hwb).
    iDestruct "Hr1" as (w1) "Hr1".
    iDestruct "Hr2" as (w2) "Hr2".
    iDestruct "Hr3" as (w3) "Hr3".
    (* prepare the range *)
    iDestruct (big_sepL2_length with "Hae") as %Hlengthae.
    assert (Hwb':=Hwb).
    apply andb_true_iff in Hwb' as [Hle%Z.leb_le Hlt%Z.ltb_lt].
    destruct ws as [|w wps].
    { exfalso. rewrite region_addrs_length /= in Hlengthae.
      rewrite /region_size in Hlengthae. solve_addr. }
    assert (is_Some (a + 1)%a) as [a' Ha'];[destruct (a + 1)%a eqn:hsome;eauto;solve_addr|].
    rewrite region_addrs_cons// Ha' /=.
    iDestruct "Hae" as "[Ha Hae]".
    (* prepare the program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
    destruct addrs as [|a0 addrs];[inversion Hlength_prog|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst a0.
    pose proof (pc_range_perm _ _ _ _ _ _ _ Hvpc Hcont) as Hperms.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iAssert (⌜r1 ≠ PC⌝)%I as %Hne'.
    { destruct (decide (r1 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr1") as %Hcontr. done. }
    iAssert (⌜r2 ≠ PC⌝)%I as %Hne2.
    { destruct (decide (r2 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr2") as %Hcontr. done. }
    iAssert (⌜r3 ≠ PC⌝)%I as %Hne3.
    { destruct (decide (r3 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr3") as %Hcontr. done. }
    (* load r1 r *)
    destruct addrs as [|a0 addrs];[inversion Hlength_prog|].
    iPrologue "Hprog".
    iAssert (⌜(a =? a_first)%a = false⌝)%I as %Hfalse.
    { rewrite Z.eqb_neq. iIntros (->%z_of_eq). iDestruct (addr_dupl_false with "Hi Ha") as "Bot";auto. }
    iApply (wp_load_success with "[$HPC $Hi $Hr1 $Hr Ha]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|iContiguous_next_a Hcont|rewrite Hfalse..].
    { iFrame. }
    iEpilogue "(HPC & Hr1 & Hprog_done & Hr & Ha)".
    (* reqint r1 r2 r3 *)
    assert (a_first + 1 = Some a0)%a as Ha_first;[iContiguous_next_a Hcont|].
    apply contiguous_between_weak in Hcont.
    apply isCorrectPC_range_monotone with (a':=a0) (a'':=a_last) in Hvpc; [|solve_addr..].
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iApply (reqint_spec with "[- $HPC $Hcode $Hr1 $Hr2 $Hr3]");[eauto..].
    iSplitR. { iNext. by iRight. }
    iNext. iIntros "(#Heq & HPC & Hreqint & Hr1 & Hr2 & Hr3)". iDestruct "Heq" as %[z Heqz].
    destruct_addr_list l_rest. apply contiguous_between_cons_inv_first in Hcont as Heq. subst l_rest.
    (* geta r1 r *)
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr1]");
      [apply decode_encode_instrW_inv|eauto|iCorrectPC link a_last|iContiguous_next_a Hcont|auto..].
    iEpilogue "(HPC & Hrest_done & Hr & Hr1)". iSimpl in "Hr1".
    (* add r1 r1 1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC link a_last|].
    iEpilogue "(HPC & Hi & Hr1)";iCombine "Hi" "Hrest_done" as "Hrest_done". iSimpl in "Hr1".
    (* gete r2 r *)
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr2]");
      [apply decode_encode_instrW_inv|eauto|iCorrectPC link a_last|iContiguous_next_a Hcont|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr2)";iCombine "Hi" "Hrest_done" as "Hrest_done". iSimpl in "Hr2".
    (* lt r1 r1 r2 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr2 $Hr1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC link a_last|].
    iEpilogue "(HPC & Hi & Hr2 & Hr1)";iCombine "Hi" "Hrest_done" as "Hrest_done". iSimpl in "Hr1".
    (* move r2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next_a Hcont|].
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hrest_done" as "Hrest_done".
    (* lea r2 -(5 + length reqint) *)
    assert (a4 + (-1*(length (reqint_instrs r1 r2 r3)+5)) = Some a_first)%a as Hlea.
    { eapply contiguous_between_incr_addr with (i:=4) (ai:=a4) in Hcont;auto. simpl. clear -Ha_first Hcont Hlink. solve_addr. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next_a Hcont|apply Hlea|auto..].
    { destruct Hperms as [-> | [-> | ->] ];auto. }
    { destruct Hperms as [-> | [-> | ->] ];auto. }
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hrest_done" as "Hrest_done".
    (* lea r 1 *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next_a Hcont|apply Ha'|auto..].
    { destruct p;auto;inversion Hra. }
    { destruct p;auto;inversion Hra. }
    iEpilogue "(HPC & Hi & Hr)". iCombine "Hi" "Hrest_done" as "Hrest_done".
    (* we must now branch: either we are done, and we must show that a' = e,
       or we will jump back and we must apply the IH *)
    destruct ((a + 1 <? e)%Z) eqn:Hcond.
    - (* if a' < e, we must redo the loop *)
      iSimpl in "Hr1".
      (* jnz r2 r1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr2 $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|done|].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hrest_done" as "Hrest_done".
      rewrite updatePcPerm_cap_non_E;[|destruct Hperms as [-> | [-> | ->] ];auto].
      iApply ("IH" with "[] [Hrest_done Hprog_done Hreqint] HPC [Hr1] [Hr2] [Hr3] Hr Hae [-]");eauto.
      { iPureIntro. apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. clear -Hcond Ha' Hle Hlt. apply Z.ltb_lt in Hcond. solve_addr. }
      { iFrame. iDestruct "Hrest_done" as "($&$&$&$&$&$&$&$)". done. }
      { iNext. iIntros "(HPC & Hprog_done & Hr & Hr1 & Hr2 & Hr3 & Hae & #Hforall)".
        iApply "Hcont". iFrame.
        iDestruct "Hforall" as %Hforall'. iPureIntro.
        apply Forall_cons. split;eauto. }
    - (* otherwise, we are done and we must show that a' = e, and that ws = [w] *)
      iSimpl in "Hr1".
      (* jnz r2 r1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr2 $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|eapply contiguous_between_last;eauto|].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hrest_done" as "Hrest_done".
      (* φ *)
      assert (a' = e) as ->.
      { clear - Ha' Hcond Hle Hlt. apply Z.ltb_ge in Hcond. solve_addr. }
      iDestruct (big_sepL2_length with "Hae") as %Hlengthws.
      rewrite region_addrs_length in Hlengthws. rewrite region_size_0 in Hlengthws;[|clear;solve_addr].
      destruct wps;[|inversion Hlengthws].
      iApply "Hcont". iFrame. iDestruct "Hrest_done" as "($&$&$&$&$&$&$&$)".
      iSplitL "Hr1";[eauto|]. iSplitL "Hr2";[eauto|]. iSplitL "Hr3";[eauto|].
      iPureIntro. apply Forall_singleton. eauto.
  Qed.


  (* The full checkints macro: if the region size is at least 1, the macro
     moves the address to the lower bound, and checks that each content is an int. *)
  Definition checkints_instrs r r1 r2 r3 :=
    leabound_instrs r r1 r2 ++
    [getb r1 r;
    gete r2 r;
    move_r r3 PC;
    lea_z r3 (5 + length (checkintsloop_instrs r r1 r2 r3));
    lt_r_r r1 r1 r2;
    sub_r_z r1 r1 1; (* invert result for the jump *)
    jnz r3 r1] ++
    checkintsloop_instrs r r1 r2 r3 ++
    [move_z r1 0;
    move_z r2 0;
    move_z r3 0].

  Definition checkints a r r1 r2 r3 : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(checkints_instrs r r1 r2 r3), a_i ↦ₐ w_i)%I.

  Lemma checkints_spec addrs r r1 r2 r3 pc_p pc_g pc_b pc_e a_first a_last φ p g b e a wps w1 w2 w3 :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between addrs a_first a_last ->
    readAllowed p = true ->

    ▷ checkints addrs r r1 r2 r3
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r1 ↦ᵣ w1
    ∗ ▷ r2 ↦ᵣ w2
    ∗ ▷ r3 ↦ᵣ w3
    ∗ ▷ r ↦ᵣ inr (p,g,b,e,a)
    ∗ ▷ ([∗ list] a;wp∈(region_addrs b e);wps, a ↦ₐ wp)
    (* if a points to an int, we want to be able to continue *)
    (* if not, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ checkints addrs r r1 r2 r3
            ∗ r ↦ᵣ inr (p,g,b,e,addr_reg.max b e) ∗ r1 ↦ᵣ inl 0%Z ∗ r2 ↦ᵣ inl 0%Z ∗ r3 ↦ᵣ inl 0%Z
            ∗ ([∗ list] a;wp∈(region_addrs b e);wps, a ↦ₐ wp) ∗ ⌜Forall (λ w, ∃ z, w = inl z) wps⌝
            -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
    ⊢
      WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}.
  Proof.
    iIntros (Hvpc Hcont Hra) "(>Hprog & >HPC & >Hr1 & >Hr2 & >Hr3 & >Hr & >Hae & Hcont)".
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iRename "Hcode" into "Hleab".
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iRename "Hcode" into "Hpre".
    iPrologue_multi "Hprog" Hcont Hvpc link1.
    iDestruct (big_sepL2_length with "Hpre") as %Hlength_pre.
    destruct_addr_list l_code0.
    apply contiguous_between_cons_inv_first in Hcont_code0 as Heq. subst l_code0.
    pose proof (pc_range_perm _ _ _ _ _ _ _ Hvpc_code0 Hcont_code0) as Hperms.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iAssert (⌜r1 ≠ PC⌝)%I as %Hne'.
    { destruct (decide (r1 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr1") as %Hcontr. done. }
    iAssert (⌜r2 ≠ PC⌝)%I as %Hne2.
    { destruct (decide (r2 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr2") as %Hcontr. done. }
    iAssert (⌜r3 ≠ PC⌝)%I as %Hne3.
    { destruct (decide (r3 = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr3") as %Hcontr. done. }
    (* leabounds macro *)
    iApply (leabound_spec with "[- $HPC $Hleab $Hr1 $Hr2 $Hr]");eauto.
    iNext. iIntros "(HPC & Hleab & Hr & Hr1 & Hr2)".
    (* getb r1 r *)
    iPrologue "Hpre".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr1]");
      [apply decode_encode_instrW_inv|eauto|iCorrectPC link link0|iContiguous_next_a Hcont_code0|auto..].
    iEpilogue "(HPC & Hprog_done & Hr & Hr1)". iSimpl in "Hr1".
    (* gete r2 r *)
    iPrologue "Hpre".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr2]");
      [apply decode_encode_instrW_inv|eauto|iCorrectPC link link0|iContiguous_next_a Hcont_code0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr2)". iSimpl in "Hr2". iCombine "Hprog_done" "Hi" as "Hprog_done".
    (* move r3 PC *)
    iPrologue "Hpre".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr3]");
      [apply decode_encode_instrW_inv|iCorrectPC link link0|iContiguous_next_a Hcont_code0|].
    iEpilogue "(HPC & Hi & Hr3)". iCombine "Hprog_done" "Hi" as "Hprog_done". rewrite -bi.sep_assoc.
    (* lea r3 (5 + len checkintsloop) *)
    assert (a1 + (5 + length (checkintsloop_instrs r r1 r2 r3)) = Some link1)%a as Hlea.
    { simpl. apply contiguous_between_middle_to_end with (i:=2) (ai:=a1) (k:=5) in Hcont_code0;auto.
      apply contiguous_between_length in Hcont_code1. rewrite app_length Hlength1 in Hlength0.
      clear -Hcont_code0 Hcont_code1 Hlength0. solve_addr. }
    iPrologue "Hpre".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr3]");
      [apply decode_encode_instrW_inv|iCorrectPC link link0|iContiguous_next_a Hcont_code0|apply Hlea|auto..].
    { destruct Hperms as [-> | [-> | ->] ];auto. }
    { destruct Hperms as [-> | [-> | ->] ];auto. }
    iEpilogue "(HPC & Hi & Hr3)". iCombine "Hprog_done" "Hi" as "Hprog_done". rewrite -2!bi.sep_assoc.
    (* lt r1 r1 r2 *)
    iPrologue "Hpre".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr2 $Hr1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont_code0|iCorrectPC link link0|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hprog_done" "Hi" as "Hprog_done". rewrite -3!bi.sep_assoc.
    (* sub r1 r1 1 *)
    iPrologue "Hpre".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont_code0|iCorrectPC link link0|..].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hprog_done" "Hi" as "Hprog_done". rewrite -4!bi.sep_assoc.

    (* we now need to branch: if the range is already 0, we do not need to check anything, and we jump to the end *)
    iSimpl in "Hr1".
    destruct (b <? e)%Z eqn:Hz.
    - (* if the range is non 0, we need to check its content *)
      (* jnz r3 r1 *)
      iPrologue "Hpre".
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr3 $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC link link0|apply contiguous_between_last with (ai:=a5) in Hcont_code0;eauto|..].
      iEpilogue "(HPC & Hi & Hr3 & Hr1)". iCombine "Hprog_done" "Hi" as "Hprog_done". rewrite -5!bi.sep_assoc.
      (* checkintsloop spec *)
      iApply (checkintsloop_spec with "[- $HPC $Hcode $Hr $Hae]");eauto.
      { apply andb_true_iff. rewrite Z.leb_le Z.ltb_lt. revert Hz. clear. rewrite Z.ltb_lt =>Hz. lia. }
      iSplitL "Hr1";[eauto|]. iSplitL "Hr2";[eauto|]. iSplitL "Hr3";[eauto|].
      iNext. iIntros "(HPC & Hcheckints & Hr & Hr1 & Hr2 & Hr3 & Hbe & #Hforall)".
      (* register cleanup *)
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      destruct_addr_list l_rest1.
      apply contiguous_between_cons_inv_first in Hcont as Heq. subst l_rest1.
      (* move r1 0 *)
      iDestruct "Hr1" as (w1') "Hr1".
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi1 & Hr1)".
      (* move r2 0 *)
      iDestruct "Hr2" as (w2') "Hr2".
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr2]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi2 & Hr2)".
      (* move r3 0 *)
      iDestruct "Hr3" as (w3') "Hr3".
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr3]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|apply contiguous_between_last with (ai:=a7) in Hcont;eauto|..].
      iEpilogue "(HPC & Hi3 & Hr3)".
      (* cont *)
      iApply "Hcont". iFrame. iFrame "Hforall".
      assert (addr_reg.max b e = e) as ->;[|iFrame].
      clear -Hz. revert Hz; rewrite Z.ltb_lt =>Hz. solve_addr.
    - (* otherwise we are done and we go straight to cleanup*)
      (* jnz r3 r1 *)
      iPrologue "Hpre".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr3 $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC link link0|..].
      { revert Hz;clear. rewrite Z.ltb_ge /=. done. }
      iEpilogue "(HPC & Hi & Hr3 & Hr1)". iCombine "Hprog_done" "Hi" as "Hprog_done". rewrite -5!bi.sep_assoc.
      (* register cleanup *)
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog.
      destruct_addr_list l_rest1.
      apply contiguous_between_cons_inv_first in Hcont as Heq. subst l_rest1.
      rewrite updatePcPerm_cap_non_E;[|destruct Hperms as [-> | [-> | ->] ];auto].
      (* move r1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr1]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi1 & Hr1)".
      (* move r2 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr2]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi2 & Hr2)".
      (* move r3 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr3]");
        [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|apply contiguous_between_last with (ai:=a7) in Hcont;eauto|..].
      iEpilogue "(HPC & Hi3 & Hr3)".
      (* cont *)
      iApply "Hcont". iDestruct (big_sepL2_length with "Hae") as %Hlength_ws. iFrame.
      assert (addr_reg.max b e = b) as ->;[|iFrame].
      clear -Hz. revert Hz; rewrite Z.ltb_ge =>Hz. solve_addr.
      iPureIntro. rewrite region_addrs_length /region_size in Hlength_ws. revert Hz; rewrite Z.ltb_ge =>Hz.
      destruct wps;[by apply Forall_nil|]. exfalso. clear -Hlength_ws Hz. simpl in Hlength_ws. lia.
  Qed.

End stack_macros.
