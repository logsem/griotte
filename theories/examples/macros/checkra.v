From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers req.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.


  (* -------------------------------------- CHECKRA --------------------------------------- *)
  (* the following macro checks that the input is a capability with at least RO permission  *)

  Definition checkra_instrs_pre r off_to_blockU :=
    [move_r r_t3 PC;
    lea_z r_t3 (off_to_blockU);
    getp r_t1 r;
    sub_r_z r_t2 r_t1 (encodePerm RO);
    move_r r_t4 PC;
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not RO, we must continue and skip the following jmp *)
    jmp r_t3;
    sub_r_z r_t2 r_t1 (encodePerm RX);
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not RX, we must continue and skip the following jmp *)
    jmp r_t3;
    sub_r_z r_t2 r_t1 (encodePerm RW);
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not RW, we must continue and skip the following jmp *)
    jmp r_t3;
    sub_r_z r_t2 r_t1 (encodePerm RWL);
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not RWL, we must continue and skip the following jmp *)
    jmp r_t3;
    sub_r_z r_t2 r_t1 (encodePerm RWX);
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not RWX, we must continue and skip the following jmp *)
    jmp r_t3;
    sub_r_z r_t2 r_t1 (encodePerm RWLX);
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* finally if the permission is not RWLX, we must continue and skip the following jmp, and fail *)
    jmp r_t3;
    fail_end].

  Local Definition off_to_blockU := length (checkra_instrs_pre r_t0 0).

  Definition checkra_instrs r := checkra_instrs_pre r off_to_blockU ++ [move_z r_t1 0; move_z r_t2 0; move_z r_t3 0; move_z r_t4 0].

  Definition checkra_pre r a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(checkra_instrs_pre r off_to_blockU), a_i ↦ₐ w_i)%I.
  Definition checkra r a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(checkra_instrs r), a_i ↦ₐ w_i)%I.

  Lemma branchperm_pre_spec r a w pc_p pc_g pc_b pc_e a_first a_last φ w1 w2 w3 w4 :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ checkra_pre r a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_t4 ↦ᵣ w4
    ∗ ▷ (if is_cap w then
           ∃ l p b e a', ⌜w = inr (p,l,b,e,a')⌝ ∧
           if readAllowed p then
             (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ checkra_pre r a ∗
                 r ↦ᵣ inr (p,l,b,e,a') ∗ (∃ w, r_t1 ↦ᵣ w) ∗ (∃ w, r_t2 ↦ᵣ w) ∗ (∃ w, r_t3 ↦ᵣ w) ∗ (∃ w, r_t4 ↦ᵣ w)
                 -∗ WP Seq (Instr Executable) {{ φ }})
           else
             φ FailedV
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    prep_addr_list_full a Hcont.
    assert (pc_p ≠ E) as Hnp.
    { eapply pc_range_not_E;eauto. }
    pose proof (pc_range_perm _ _ _ _ _ _ _ Hvpc Hcont) as Hperms.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    (* move_r r_t3 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$Hi $HPC $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|..].
    iEpilogue "(HPC & Hprog_done & Hr_t3)".
    (* lea r_t3 off1 *)
    assert (a_first + off_to_blockU = Some a_last)%a as Hoff.
    { apply contiguous_between_length in Hcont. auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$Hi $HPC $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hoff|auto..].
    { destruct Hperms as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* getp r_t1 r *)
    iPrologue "Hprog".
    destruct w.
    { (* if w is an integer, the getL will fail *)
      iApply (wp_Get_fail with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|..].
      iEpilogue "_ /=".
      iApply wp_value. done. }
    destruct c,p,p,p.
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next_a Hcont|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    iSimpl in "Hr_t1".
    (* sub r_t2 r_t1 URW *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t4 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$Hi $HPC $Hr_t4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|..].
    iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t4 4 *)
    assert (a3 + 4 = Some a7)%a as Hlea.
    { apply contiguous_between_incr_addr_middle with (i:=4) (j:=4) (ai:=a3) (aj:=a7) in Hcont;auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$Hi $HPC $Hr_t4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hlea|auto..].
    { destruct Hperms as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t4 r_t2 *)
    iPrologue "Hprog". iSimpl in "Hr_t2".
    destruct (decide (encodePerm p - encodePerm RO = 0)%Z).
    { (* if the permission is URW we are done and will jump to the last block *)
      rewrite e.
      iApply (wp_jnz_success_next with "[$Hi $HPC $Hr_t4 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t3 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$Hi $Hr_t3 $HPC]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|..].
      iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* Hφ *)
      assert (p = RO);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
      iDestruct "Hcont" as (l0 p b e0 a' Heq) "Hφ". simplify_eq. iSimpl in "Hφ".
      iApply "Hφ". rewrite updatePcPerm_cap_non_E//. iFrame "HPC Hr".
      iSplitL "Hprog Hprog_done".
      { iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$)". }
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    }
    (* otherwise we keep checking *)
    iApply (wp_jnz_success_jmp with "[$Hi $HPC $Hr_t4 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|intros;congruence|..].
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub r_t2 r_t1 URWL *)
    rewrite updatePcPerm_cap_non_E//.
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t4 4 *)
    assert (a7 + 4 = Some a11)%a as Hlea'.
    { apply contiguous_between_incr_addr_middle with (i:=8) (j:=4) (ai:=a7) (aj:=a11) in Hcont;auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$Hi $HPC $Hr_t4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hlea'|auto..].
    { destruct Hperms as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t4 r_t2 *)
    iPrologue "Hprog". iSimpl in "Hr_t2".
    destruct (decide (encodePerm p - encodePerm RX = 0)%Z).
    { (* if the permission is URW we are done and will jump to the last block *)
      rewrite e.
      iApply (wp_jnz_success_next with "[$Hi $HPC $Hr_t4 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t3 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$Hi $Hr_t3 $HPC]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|..].
      iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* Hφ *)
      assert (p = RX);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
      iDestruct "Hcont" as (l0 p b e0 a' Heq) "Hφ". simplify_eq. iSimpl in "Hφ".
      iApply "Hφ". rewrite updatePcPerm_cap_non_E//. iFrame "HPC Hr".
      iSplitL "Hprog Hprog_done".
      { iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$)". }
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    }
    (* otherwise we keep checking *)
    iApply (wp_jnz_success_jmp with "[$Hi $HPC $Hr_t4 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|intros;congruence|..].
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done".
    rewrite updatePcPerm_cap_non_E//.
    (* sub r_t2 r_t1 URWL *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t4 4 *)
    assert (a11 + 4 = Some a15)%a as Hlea''.
    { apply contiguous_between_incr_addr_middle with (i:=12) (j:=4) (ai:=a11) (aj:=a15) in Hcont;auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$Hi $HPC $Hr_t4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hlea''|auto..].
    { destruct Hperms as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t4 r_t2 *)
    iPrologue "Hprog". iSimpl in "Hr_t2".
    destruct (decide (encodePerm p - encodePerm RW = 0)%Z).
    { (* if the permission is URW we are done and will jump to the last block *)
      rewrite e.
      iApply (wp_jnz_success_next with "[$Hi $HPC $Hr_t4 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t3 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$Hi $Hr_t3 $HPC]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|..].
      iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* Hφ *)
      assert (p = RW);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
      iDestruct "Hcont" as (l0 p b e0 a' Heq) "Hφ". simplify_eq. iSimpl in "Hφ".
      iApply "Hφ". rewrite updatePcPerm_cap_non_E//. iFrame "HPC Hr".
      iSplitL "Hprog Hprog_done".
      { iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$)". }
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    }
    (* otherwise we keep checking *)
    iApply (wp_jnz_success_jmp with "[$Hi $HPC $Hr_t4 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|intros;congruence|..].
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done".
    rewrite updatePcPerm_cap_non_E//.
    (* sub r_t2 r_t1 URWL *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t4 4 *)
    assert (a15 + 4 = Some a19)%a as Hlea'''.
    { apply contiguous_between_incr_addr_middle with (i:=16) (j:=4) (ai:=a15) (aj:=a19) in Hcont;auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$Hi $HPC $Hr_t4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hlea'''|auto..].
    { destruct Hperms as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t4 r_t2 *)
    iPrologue "Hprog". iSimpl in "Hr_t2".
    destruct (decide (encodePerm p - encodePerm RWL = 0)%Z).
    { (* if the permission is URW we are done and will jump to the last block *)
      rewrite e.
      iApply (wp_jnz_success_next with "[$Hi $HPC $Hr_t4 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t3 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$Hi $Hr_t3 $HPC]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|..].
      iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* Hφ *)
      assert (p = RWL);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
      iDestruct "Hcont" as (l0 p b e0 a' Heq) "Hφ". simplify_eq. iSimpl in "Hφ".
      iApply "Hφ". rewrite updatePcPerm_cap_non_E//. iFrame "HPC Hr".
      iSplitL "Hprog Hprog_done".
      { iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$)". }
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    }
    (* otherwise we keep checking *)
    iApply (wp_jnz_success_jmp with "[$Hi $HPC $Hr_t4 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|intros;congruence|..].
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done".
    rewrite updatePcPerm_cap_non_E//.
    (* sub r_t2 r_t1 URWL *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t4 4 *)
    assert (a19 + 4 = Some a23)%a as Hlea''''.
    { apply contiguous_between_incr_addr_middle with (i:=20) (j:=4) (ai:=a19) (aj:=a23) in Hcont;auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$Hi $HPC $Hr_t4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hlea''''|auto..].
    { destruct Hperms as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t4 r_t2 *)
    iPrologue "Hprog". iSimpl in "Hr_t2".
    destruct (decide (encodePerm p - encodePerm RWX = 0)%Z).
    { (* if the permission is URW we are done and will jump to the last block *)
      rewrite e.
      iApply (wp_jnz_success_next with "[$Hi $HPC $Hr_t4 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t3 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$Hi $Hr_t3 $HPC]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|..].
      iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* Hφ *)
      assert (p = RWX);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
      iDestruct "Hcont" as (l0 p b e0 a' Heq) "Hφ". simplify_eq. iSimpl in "Hφ".
      iApply "Hφ". rewrite updatePcPerm_cap_non_E//. iFrame "HPC Hr".
      iSplitL "Hprog Hprog_done".
      { iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$)". }
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    }
    (* otherwise we keep checking *)
    iApply (wp_jnz_success_jmp with "[$Hi $HPC $Hr_t4 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|intros;congruence|..].
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done".
    rewrite updatePcPerm_cap_non_E//.
    (* sub r_t2 r_t1 URWL *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_z with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t4 4 *)
    assert (a23 + 4 = Some a27)%a as Hleaend.
    { apply contiguous_between_incr_addr_middle with (i:=24) (j:=4) (ai:=a23) (aj:=a27) in Hcont;auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$Hi $HPC $Hr_t4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hleaend|auto..].
    { destruct Hperms as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t4 r_t2 *)
    iPrologue "Hprog". iSimpl in "Hr_t2".
    destruct (decide (encodePerm p - encodePerm RWLX = 0)%Z).
    { (* if the permission is URW we are done and will jump to the last block *)
      rewrite e.
      iApply (wp_jnz_success_next with "[$Hi $HPC $Hr_t4 $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|..].
      iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t3 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$Hi $Hr_t3 $HPC]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|..].
      iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* Hφ *)
      assert (p = RWLX);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
      iDestruct "Hcont" as (l0 p b e0 a' Heq) "Hφ". simplify_eq. iSimpl in "Hφ".
      iApply "Hφ". rewrite updatePcPerm_cap_non_E//. iFrame "HPC Hr".
      iSplitL "Hprog Hprog_done".
      { iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$)". }
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    }
    (* otherwise we go to the first block *)
    iApply (wp_jnz_success_jmp with "[$Hi $HPC $Hr_t4 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|intros;congruence|..].
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done".
    rewrite updatePcPerm_cap_non_E//.
    (* fail_end *)
    iPrologue "Hprog".
    iApply (wp_fail with "[$HPC $Hi]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
    iEpilogue "(HPC & Hi)". iApply wp_value.
    (* Hφ *)
    iSimpl in "Hcont".
    iDestruct "Hcont" as (l0 p0 b e a' Heq) "Hcont".
    simplify_eq.
    assert (readAllowed p0 = false) as ->.
    { destruct p0;auto;exfalso;[apply n|apply n1|apply n2|apply n0|apply n3|apply n4]; clear;lia. }
    iApply "Hcont".
  Qed.


  Lemma checkra_spec r a w pc_p pc_g pc_b pc_e a_first a_last φ w1 w2 w3 w4 :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ checkra r a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    ∗ ▷ r_t4 ↦ᵣ w4
    ∗ ▷ (if is_cap w then
           ∃ l p b e a', ⌜w = inr (p,l,b,e,a')⌝ ∧
           if readAllowed p then
             (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ checkra r a ∗
                 r ↦ᵣ inr (p,l,b,e,a') ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z ∗ r_t4 ↦ᵣ inl 0%Z
                 -∗ WP Seq (Instr Executable) {{ φ }})
           else
             φ FailedV
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    (* check block *)
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iRename "Hcode" into "Hcode_first".
    iApply (branchperm_pre_spec with "[- $HPC $Hcode_first $Hr $Hr_t1 $Hr_t2 $Hr_t3 $Hr_t4]"); [apply Hvpc_code|apply Hcont_code|].
    iNext. destruct (is_cap w) eqn:Hcap;[|simpl;iFrame].
    destruct w;inversion Hcap. destruct c,p,p,p.
    destruct (readAllowed p) eqn:Hra.
    - iDestruct "Hcont" as (l' p' b e a' Heq) "Hcont". simplify_eq. rewrite Hra.
      iExists _,_,_,_,_. iSplit;eauto. rewrite Hra. iIntros "(HPC & Hcheckra & Hr & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4)".
      iDestruct "Hr_t1" as (w1') "Hr_t1".
      iDestruct "Hr_t2" as (w2') "Hr_t2".
      iDestruct "Hr_t3" as (w3') "Hr_t3".
      iDestruct "Hr_t4" as (w4') "Hr_t4".
      prep_addr_list_full l_rest Hcont.
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next_a Hcont|].
      iEpilogue "(HPC & Hi1 & Hr_t1)".
      (* move r_t2 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next_a Hcont|].
      iEpilogue "(HPC & Hi2 & Hr_t2)".
      (* move r_t3 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next_a Hcont|].
      iEpilogue "(HPC & Hi3 & Hr_t3)".
      (* move r_t4 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t4]");
        [apply decode_encode_instrW_inv|iCorrectPC link a_last|..].
      { eapply contiguous_between_last;eauto. }
      iEpilogue "(HPC & Hi4 & Hr_t4)".
      (* Hcont *)
      iApply "Hcont".
      iFrame.
    - iDestruct "Hcont" as (l' p' b e a' Heq) "Hcont". simplify_eq. rewrite Hra.
      iExists _,_,_,_,_. iSplit;eauto. rewrite Hra. iFrame.
  Qed.


End stack_macros.
