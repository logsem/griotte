From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers req.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.


  (* -------------------------------------- CHECKBELOW ------------------------------------ *)
  (* the following macro checks that the upper read bound of one capability is below the lower
     bound of another capability *)
  (* the macro branches based on the U of the capability *)

  Definition branchperm_instrs_pre r off_to_blockU off_to_skip_blockU :=
    [move_r r_t3 PC;
    lea_z r_t3 (off_to_blockU + off_to_skip_blockU);
    getp r_t1 r;
    sub_r_z r_t2 r_t1 (encodePerm URW);
    move_r r_t4 PC;
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not URW, we must continue and skip the following jmp *)
    jmp r_t3;
    sub_r_z r_t2 r_t1 (encodePerm URWL);
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not URWL, we must continue and skip the following jmp *)
    jmp r_t3;
    sub_r_z r_t2 r_t1 (encodePerm URWX);
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not URWX, we must continue and skip the following jmp *)
    jmp r_t3;
    sub_r_z r_t2 r_t1 (encodePerm URWLX);
    lea_z r_t4 4;
    jnz r_t4 r_t2; (* if the permission is not URWLX, we must continue and skip the following jmp *)
    jmp r_t3].

  (* after the above macro, the PC will either point to the instruction right after, or the instruction
     skipping an offset *)

  Local Definition off_to_blockU := length (branchperm_instrs_pre r_t0 0 0).

  Definition branchperm_instrs r off_to_skip_blockU := branchperm_instrs_pre r off_to_blockU off_to_skip_blockU.

  Definition branchperm r off_to_skip_blockU a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(branchperm_instrs r off_to_skip_blockU), a_i ↦ₐ w_i)%I.

  Definition isU_word (w : Word) :=
    match w with
    | inl _ => false
    | inr (p,_,_,_,_) => isU p
    end.

  Lemma branchperm_spec r a w pc_p pc_g pc_b pc_e a_first a_last a_blockU off_to_skip_blockU φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->
    (a_first + (off_to_blockU + off_to_skip_blockU))%a = Some a_blockU →

      ▷ branchperm r off_to_skip_blockU a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t3 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t4 ↦ᵣ w)
    ∗ ▷ (if is_cap w then
           ∃ l p b e a', ⌜w = inr (p,l,b,e,a')⌝ ∧
           if isU p then
             (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_blockU) ∗ branchperm r off_to_skip_blockU a ∗
                 r ↦ᵣ inr (p,l,b,e,a') ∗ (∃ w, r_t1 ↦ᵣ w) ∗ (∃ w, r_t2 ↦ᵣ w) ∗ (∃ w, r_t3 ↦ᵣ w) ∗ (∃ w, r_t4 ↦ᵣ w)
                 -∗ WP Seq (Instr Executable) {{ φ }})
           else
             (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ branchperm r off_to_skip_blockU a ∗
                 r ↦ᵣ inr (p,l,b,e,a') ∗ (∃ w, r_t1 ↦ᵣ w) ∗ (∃ w, r_t2 ↦ᵣ w) ∗ (∃ w, r_t3 ↦ᵣ w) ∗ (∃ w, r_t4 ↦ᵣ w)
                 -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hoff) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hr_t3 & Hr_t4 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iDestruct ("Hr_t1") as (w1) "Hr_t1".
    iDestruct ("Hr_t2") as (w2) "Hr_t2".
    iDestruct ("Hr_t3") as (w3) "Hr_t3".
    iDestruct ("Hr_t4") as (w4) "Hr_t4".
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
    (* lea r_t3 (off1 + off2) *)
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
    destruct (decide (encodePerm p - encodePerm URW = 0)%Z).
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
      assert (p = URW);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
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
    destruct (decide (encodePerm p - encodePerm URWL = 0)%Z).
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
      assert (p = URWL);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
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
    destruct (decide (encodePerm p - encodePerm URWX = 0)%Z).
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
      assert (p = URWX);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
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
    assert (a15 + 4 = Some a_last)%a as Hlea'''.
    { apply contiguous_between_middle_to_end with (i:=16) (k:=4) (ai:=a15) in Hcont;auto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$Hi $HPC $Hr_t4]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next_a Hcont|apply Hlea'''|auto..].
    { destruct Hperms as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t4 r_t2 *)
    iPrologue "Hprog". iSimpl in "Hr_t2".
    destruct (decide (encodePerm p - encodePerm URWLX = 0)%Z).
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
      assert (p = URWLX);[apply encodePerm_inj;lia|subst p]. iSimpl in "Hcont".
      iDestruct "Hcont" as (l0 p b e0 a' Heq) "Hφ". simplify_eq. iSimpl in "Hφ".
      iApply "Hφ". rewrite updatePcPerm_cap_non_E//. iFrame "HPC Hr".
      iSplitL "Hprog Hprog_done".
      { iFrame. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$)". }
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
    }
    (* otherwise we go to the first block *)
    iApply (wp_jnz_success_jmp with "[$Hi $HPC $Hr_t4 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|intros;congruence|..].
    iEpilogue "(HPC & Hi & Hr_t4 & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
    iDestruct "Hprog" as "[Hi Hprog]";iCombine "Hi" "Hprog_done" as "Hprog_done".
    rewrite updatePcPerm_cap_non_E//.
    (* Hφ *)
    iSimpl in "Hcont".
    iDestruct "Hcont" as (l0 p0 b e a' Heq) "Hcont".
    simplify_eq.
    assert (isU p0 = false) as ->.
    { destruct p0;auto;exfalso;[apply n|apply n0|apply n1|apply n2];clear;lia. }
    iApply "Hcont".
    iFrame "Hr HPC".
    iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$)".
    iSplit;auto. iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";eauto.
  Qed.


  Definition checkbelow_notU_block_instrs r rown off_skip_block :=
    [(* we must first check whether the permission is O *)
    getp r_t1 r;
    sub_r_z r_t1 r_t1 (encodePerm O);
    move_r r_t2 PC;
    lea_z r_t2 4;
    jnz r_t2 r_t1;
    fail_end;
    (* then we can compare the bounds *)
    gete r_t1 r;
    getb r_t2 rown;
    lt_r_r r_t1 r_t1 r_t2;
    move_r r_t2 PC;
    lea_z r_t2 4;
    jnz r_t2 r_t1; (* if zero we go to failure *)
    fail_end;
    move_r r_t2 PC;
    lea_z r_t2 (3 + off_skip_block);
    jmp r_t2].

  Definition checkbelow_U_block_instrs r rown :=
    [geta r_t1 r;
    getb r_t2 rown;
    lt_r_r r_t1 r_t1 r_t2;
    move_r r_t2 PC;
    lea_z r_t2 4;
    jnz r_t2 r_t1; (* if zero we go to failure *)
    fail_end].

  Definition checkbelow_instrs r rown :=
    branchperm_instrs r (length (checkbelow_notU_block_instrs r rown 0)) ++
    checkbelow_notU_block_instrs r rown (length (checkbelow_U_block_instrs r rown)) ++
    checkbelow_U_block_instrs r rown ++
    [move_z r_t1 0;
    move_z r_t2 0;
    move_z r_t3 0;
    move_z r_t4 0].

  Definition checkbelow r rown a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(checkbelow_instrs r rown), a_i ↦ₐ w_i)%I.

  Definition isO p :=
    match p with
    | O => true
    | _ => false
    end.
  Definition isO_word (w:Word):=
    match w with
    | inl _ => false
    | inr (p,_,_,_,_) => isO p
    end.

  Lemma checkbelow_spec r rown a w p g b e a' pc_p pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ checkbelow r rown a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ rown ↦ᵣ inr (p,g,b,e,a')
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t3 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t4 ↦ᵣ w)
    ∗ ▷ (if (is_cap w && (canReadUpTo w <? b) && (negb (isO_word w)))%a then
           (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ checkbelow r rown a ∗
               r ↦ᵣ w ∗ rown ↦ᵣ inr (p,g,b,e,a') ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z ∗ r_t4 ↦ᵣ inl 0%Z
               -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hrown & >Hr_t1 & >Hr_t2 & >Hr_t3 & >Hr_t4 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    (* check block *)
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    iAssert (⌜rown ≠ PC⌝)%I as %Hne'.
    { destruct (decide (rown = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hrown") as %Hcontr. done. }
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iRename "Hcode" into "Hcode_first".
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    assert ((a_first + (20%nat + 16%nat))%a = Some link0) as Hoff.
    { clear -Hlink Hlink0. solve_addr. }
    iApply (branchperm_spec with "[- $HPC $Hcode_first $Hr $Hr_t1 $Hr_t2 $Hr_t3 $Hr_t4]"); [apply Hvpc_code|apply Hcont_code|eauto|].
    iNext. destruct (is_cap w) eqn:Hcap;[|simpl;iFrame].
    destruct w;inversion Hcap. destruct c,p0,p0,p0.
    iExists _,_,_,_,_. iSplit;eauto.
    destruct (isU p0) eqn:HU.
    - iIntros "(HPC & Hprog_done & Hr & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4)".
      iDestruct "Hr_t1" as (w1) "Hr_t1".
      iDestruct "Hr_t2" as (w2) "Hr_t2".
      iDestruct "Hr_t3" as (w3) "Hr_t3".
      iDestruct "Hr_t4" as (w4) "Hr_t4".
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog. simpl in *.
      prep_addr_list_full l_rest0 Hcont.
      assert (pc_p ≠ E) as Hnp.
      { eapply pc_range_not_E;eauto. }
      pose proof (pc_range_perm _ _ _ _ _ _ _ Hvpc Hcont) as Hperms.
      (* geta r_t1 r *)
      iPrologue "Hprog".
      iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC link0 a_last|iContiguous_next_a Hcont|auto..].
      iEpilogue "(HPC & Hi & Hr & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* getb r_t2 rown *)
      iPrologue "Hprog".
      iApply (wp_Get_success with "[$HPC $Hi $Hrown $Hr_t2]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC link0 a_last|iContiguous_next_a Hcont|auto..].
      iEpilogue "(HPC & Hi & Hrown & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lt r_t1 r_t1 r_t2 *)
      iPrologue "Hprog".
      iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC link0 a_last|auto..].
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next_a Hcont|auto..].
      iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea r_t2 4 *)
      assert (a5 + 4 = Some a9)%a as Hlea.
      { apply contiguous_between_incr_addr_middle with (i:=3) (j:=4) (ai:=a5) (aj:=a9) in Hcont;auto. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next_a Hcont|apply Hlea|auto..].
      { destruct Hperms as [-> | [-> | ->] ]; auto. }
      iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jnz r_t1 r_t2 *)
      iPrologue "Hprog". iSimpl in "Hr_t1".
      destruct (decide ((Z.b2z (a0 <? b)%Z) = 0)).
      + rewrite e0.
        iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next_a Hcont|auto..].
        iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* fail *)
        iPrologue "Hprog".
        iApply (wp_fail with "[$HPC $Hi]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|..].
        iEpilogue "(HPC & Hi)". iApply wp_value.
        assert (match p0 with
                | O => 0
                | URW | URWL | URWX | URWLX => a0
                | _ => a1
                end = a0)%a as ->.
        { destruct p0;auto;inversion HU. }
        destruct (a0 <? b)%Z eqn:Hbool;[inversion e0|].
        assert (a0 <? b = false)%a as ->;[clear -Hbool;solve_addr|].
        iFrame.
      + iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|auto..].
        { intros Hcontr; inversion Hcontr. done. }
        iEpilogue "(HPC & Hi & Hr_t2 &  Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* move r_t1 0 *)
        rewrite updatePcPerm_cap_non_E //.
        iPrologue "Hprog".
        iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next_a Hcont|].
        iEpilogue "(HPC & Hi & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* move r_t2 0 *)
        iPrologue "Hprog".
        iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next_a Hcont|].
        iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* move r_t3 0 *)
        iPrologue "Hprog".
        iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next_a Hcont|].
        iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* move r_t4 0 *)
        iPrologue "Hprog".
        iApply (wp_move_success_z with "[$HPC $Hi $Hr_t4]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|eapply contiguous_between_last;[apply Hcont|auto]|].
        iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* cont *)
        assert (match p0 with
                | O => 0
                | URW | URWL | URWX | URWLX => a0
                | _ => a1
                end = a0)%a as ->.
        { destruct p0;auto;inversion HU. }
        destruct (a0 <? b)%Z eqn:Hbool;[|contradiction].
        assert (a0 <? b = true)%a as ->;[clear -Hbool;solve_addr|].
        assert (negb (isO p0) = true) as ->;[destruct p0;auto|].
        iApply "Hcont". iFrame "HPC Hr Hr_t1 Hr_t2 Hr_t3 Hr_t4 Hrown Hcode".
        iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&?)". iFrame.
    - iIntros "(HPC & Hprog_done & Hr & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4)".
      iDestruct "Hr_t1" as (w1) "Hr_t1".
      iDestruct "Hr_t2" as (w2) "Hr_t2".
      iDestruct "Hr_t3" as (w3) "Hr_t3".
      iDestruct "Hr_t4" as (w4) "Hr_t4".
      iRename "Hprog" into "Hskipped". iRename "Hcode" into "Hprog".
      rename link0 into linkskipped. rename link into link0.
      rename Hcont into Hcont_skipped. rename Hcont_code0 into Hcont.
      rename Hvpc into Hvpc_skipped. rename Hvpc_code0 into Hvpc.
      iDestruct (big_sepL2_length with "Hprog") as %Hlength_prog. simpl in *.
      prep_addr_list_full l_code0 Hcont.
      assert (pc_p ≠ E) as Hnp.
      { eapply pc_range_not_E;[apply Hvpc|]. eauto. }
      pose proof (pc_range_perm _ _ _ _ _ _ _ Hvpc Hcont) as Hperms.
      (* getp r_t1 r *)
      iPrologue "Hprog".
      iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|auto..].
      iEpilogue "(HPC & Hi & Hr & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      iSimpl in "Hr_t1".
      (* sub r_t1 r_t1 O *)
      iPrologue "Hprog".
      iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC link0 linkskipped|..].
      iEpilogue "(HPC & Hi & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|auto..].
      iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea r_t2 4 *)
      assert (a4 + 4 = Some a8)%a as Hlea.
      { apply contiguous_between_incr_addr_middle with (i:=2) (j:=4) (ai:=a4) (aj:=a8) in Hcont;auto. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|apply Hlea|auto..].
      { destruct Hperms as [-> | [-> | ->] ]; auto. }
      iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jnz r_t2 r_t1 *)
      iPrologue "Hprog". iSimpl in "Hr_t1".
      destruct (decide (encodePerm p0 - encodePerm O = 0)%Z).
      { (* the permission is O, we can simply fail since jumping to an O cap will fail anyways *)
        rewrite e0.
        iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|auto..].
        iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* fail *)
        iPrologue "Hprog".
        iApply (wp_fail with "[$HPC $Hi]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|..].
        iEpilogue "(HPC & Hi)". iApply wp_value.
        assert (p0 = O) as ->;[apply encodePerm_inj;lia|]. rewrite andb_false_r. iFrame.
      }
      (* now we know that p0 is not O *)
      assert (p0 ≠ O) as HnO;[intros Hcontr;subst;lia|].
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|auto..].
      { intros Hcontr; inversion Hcontr. done. }
      iEpilogue "(HPC & Hi & Hr_t2 &  Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* gete r_t1 r *)
      rewrite updatePcPerm_cap_non_E //.
      iPrologue "Hprog".
      iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|auto..].
      iEpilogue "(HPC & Hi & Hr & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* getb r_t2 rown *)
      iPrologue "Hprog".
      iApply (wp_Get_success with "[$HPC $Hi $Hrown $Hr_t2]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|auto..].
      iEpilogue "(HPC & Hi & Hrown & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lt r_t1 r_t1 r_t2 *)
      iPrologue "Hprog".
      iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont|iCorrectPC link0 linkskipped|auto..].
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|auto..].
      iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea r_t2 4 *)
      assert (a11 + 4 = Some a15)%a as Hlea'.
      { apply contiguous_between_incr_addr_middle with (i:=9) (j:=4) (ai:=a11) (aj:=a15) in Hcont;auto. }
      iPrologue "Hprog".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|apply Hlea'|auto..].
      { destruct Hperms as [-> | [-> | ->] ]; auto. }
      iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jnz r_t1 r_t2 *)
      iPrologue "Hprog". iSimpl in "Hr_t1".
      destruct (decide ((Z.b2z (a1 <? b)%Z) = 0)).
      + rewrite e0.
        iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|auto..].
        iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* fail *)
        iPrologue "Hprog".
        iApply (wp_fail with "[$HPC $Hi]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|..].
        iEpilogue "(HPC & Hi)". iApply wp_value.
        assert (match p0 with
                | O => 0
                | URW | URWL | URWX | URWLX => a0
                | _ => a1
                end = a1)%a as ->.
        { destruct p0;auto;inversion HU. contradiction. }
        destruct (a1 <? b)%Z eqn:Hbool;[inversion e0|].
        assert (a1 <? b = false)%a as ->;[clear -Hbool;solve_addr|].
        iFrame.
      + iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|auto..].
        { intros Hcontr; inversion Hcontr. done. }
        iEpilogue "(HPC & Hi & Hr_t2 &  Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* move r_t2 PC *)
        iPrologue "Hprog". rewrite updatePcPerm_cap_non_E //.
        iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|auto..].
        iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* lea r_t2 10 *)
        iDestruct (big_sepL2_length with "Hskipped") as %Hlength_skipped. simpl in *.
        prep_addr_list_full l_rest0 Hcont_skipped.
        assert (a15 + 10 = Some a24)%a as Hlea''.
        { apply contiguous_between_incr_addr_middle with (i:=0) (j:=7) (ai:=linkskipped) (aj:=a24) in Hcont_skipped;auto.
          apply contiguous_between_middle_to_end with (i:=13) (ai:=a15) (k:=3) in Hcont;auto.
          clear -Hcont Hcont_skipped. solve_addr. }
        iPrologue "Hprog".
        iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|iContiguous_next_a Hcont|apply Hlea''|auto..].
        { destruct Hperms as [-> | [-> | ->] ]; auto. }
        iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* jmp r_t2 *)
        iPrologue "Hprog".
        iApply (wp_jmp_success with "[$HPC $Hi $Hr_t2]");
          [apply decode_encode_instrW_inv|iCorrectPC link0 linkskipped|..].
        iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        rewrite updatePcPerm_cap_non_E //.
        do 7 (iDestruct "Hskipped" as "[Hi Hskipped]"; iCombine "Hi" "Hprog_done" as "Hprog_done").
        (* move r_t1 0 *)
        iClear "Hprog". iRename "Hskipped" into "Hprog".
        iPrologue "Hprog".
        iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
          [apply decode_encode_instrW_inv|iCorrectPC linkskipped a_last|iContiguous_next_a Hcont_skipped|].
        iEpilogue "(HPC & Hi & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* move r_t2 0 *)
        iPrologue "Hprog".
        iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
          [apply decode_encode_instrW_inv|iCorrectPC linkskipped a_last|iContiguous_next_a Hcont_skipped|].
        iEpilogue "(HPC & Hi & Hr_t2)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* move r_t3 0 *)
        iPrologue "Hprog".
        iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
          [apply decode_encode_instrW_inv|iCorrectPC linkskipped a_last|iContiguous_next_a Hcont_skipped|].
        iEpilogue "(HPC & Hi & Hr_t3)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* move r_t4 0 *)
        iPrologue "Hprog".
        iApply (wp_move_success_z with "[$HPC $Hi $Hr_t4]");
          [apply decode_encode_instrW_inv|iCorrectPC linkskipped a_last|eapply contiguous_between_last;[apply Hcont_skipped|auto]|].
        iEpilogue "(HPC & Hi & Hr_t4)";iCombine "Hi" "Hprog_done" as "Hprog_done".
        (* cont *)
        assert (match p0 with
                | O => 0
                | URW | URWL | URWX | URWLX => a0
                | _ => a1
                end = a1)%a as ->.
        { destruct p0;auto;inversion HU. contradiction. }
        destruct (a1 <? b)%Z eqn:Hbool;[|contradiction].
        assert (a1 <? b = true)%a as ->;[clear -Hbool;solve_addr|].
        assert (negb (isO p0) = true) as ->;[destruct p0;auto|].
        iApply "Hcont". iFrame "HPC Hr Hr_t1 Hr_t2 Hr_t3 Hr_t4 Hrown".
        iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$&$)".
        done.
  Qed.


End stack_macros.
