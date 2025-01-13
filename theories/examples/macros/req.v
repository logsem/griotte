From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export addr_reg_sample region_macros contiguous stack_macros_helpers.
From cap_machine.rules Require Import rules_StoreU_derived rules_LoadU_derived.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (* -------------------------------------- REQGLOB ----------------------------------- *)
  (* the following macro requires that a given registers contains a global capability. If 
     this is not the case, the macro goes to fail, otherwise it continues               *)

  Definition reqglob_instrs r :=
    [getl r_t1 r;
    sub_r_z r_t1 r_t1 (encodeLoc Global);
    move_r r_t2 PC;
    lea_z r_t2 6;
    jnz r_t2 r_t1;
    move_r r_t2 PC;
    lea_z r_t2 4;
    jmp r_t2;
    fail_end;
    move_z r_t1 0;
    move_z r_t2 0].

  (* TODO: move this to the rules_Get.v file. small issue with the spec of failure: it does not actually 
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)
  Lemma wp_Get_fail E get_i dst src pc_p pc_g pc_b pc_e pc_a w zsrc wdst :
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →

    {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
      ∗ ▷ pc_a ↦ₐ w
      ∗ ▷ dst ↦ᵣ wdst
      ∗ ▷ src ↦ᵣ inl zsrc }}}
      Instr Executable @ E
      {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hinstr Hvpc φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_Get with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  (* ------------------------------- *)

  Definition reqglob r a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqglob_instrs r), a_i ↦ₐ w_i)%I.

  Lemma reqglob_spec r a w pc_p pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ reqglob r a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (if isGlobalWord w then
           ∃ g b e a', ⌜w = inr (g,Global,b,e,a')⌝ ∧
          (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ reqglob r a ∗
            r ↦ᵣ inr (g,Global,b,e,a') ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iDestruct ("Hr_t1") as (w1) "Hr_t1".
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    prep_addr_list_full a Hcont.
    iPrologue "Hprog".
    destruct w. 
    { (* if w is an integer, the getL will fail *)
      iApply (wp_Get_fail with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|..].
      iEpilogue "_ /=". 
      iApply wp_value. done. 
    }
    (* if w is a capability, the getL will succeed *)
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1)". iRename "Hi" into "Hprog_done".
    destruct c,p,p,p. iSimpl in "Hr_t1". 
    (* sub r_t1 r_t1 (encodeLoc Global) *)
    iPrologue "Hprog". 
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 1|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done". 
    iSimpl in "Hr_t1".
    (* move r_t2 PC *)
    iPrologue "Hprog".
    iDestruct "Hr_t2" as (w2) "Hr_t2". 
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t2 6 *)
    assert ((a1 + 6)%a = Some a7) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 2 6 a1 a7) in Hcont; auto. }
    assert (pc_p ≠ E) as HneE.
    { eapply pc_range_not_E;eauto. }
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|apply Hlea|auto..].
    { apply isCorrectPC_range_perm in Hvpc as [Heq | [Heq | Heq] ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto. }
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    destruct (decide (encodeLoc l - encodeLoc Global = 0))%Z.
    - (* l is Global *)
      rewrite e. assert (l = Global);[apply encodeLoc_inj;lia|subst]. 
      iSimpl in "Hcont". iDestruct "Hcont" as (g b e0 a' Heq) "Hφ". inversion Heq; subst.
      iPrologue "Hprog". 
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|..].
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move_r r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* lea r_t2 3 *)
      assert ((a4 + 4)%a = Some a8) as Hlea'. 
      { apply (contiguous_between_incr_addr_middle _ _ _ 5 4 a4 a8) in Hcont; auto. }
      iPrologue "Hprog". 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hlea'|auto..].
      { apply isCorrectPC_range_perm in Hvpc as [Heq' | [Heq' | Heq'] ]; subst; auto.
        apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto. }
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* jmp r_t2 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      rewrite updatePcPerm_cap_non_E//.
      iDestruct "Hprog" as "[Hi Hprog]". iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]"); 
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 9|auto|..].
      iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move r_t2 0 *)
      iPrologue "Hprog".
      apply contiguous_between_last with (ai:=a9) in Hcont as Hnext;[|auto]. 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]"); 
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hnext|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      iApply "Hφ". iFrame "HPC Hr Hr_t1 Hr_t2".
      iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$)".
      done.
    - destruct l;[lia|iSimpl in "Hcont"..].
      (* jnz r_t2 r_t1 *)
      all: iPrologue "Hprog".
      all: iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      1,3: intros Hcontr; inversion Hcontr; done. 
      all: iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      all: do 3 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done"). 
      (* fail *)
      all: iPrologue "Hprog".
      all: rewrite updatePcPerm_cap_non_E//.
      all: iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      all: iEpilogue "(HPC & Hi)"; iApply wp_value; iApply "Hcont". 
  Qed.

  (* -------------------------------------- REQPERM ----------------------------------- *)
  (* the following macro requires that a given registers contains a capability with a
     given (encoded) permission. If this is not the case, the macro goes to fail,
     otherwise it continues *)

  Definition reqperm_instrs r z :=
    [getp r_t1 r;
    sub_r_z r_t1 r_t1 z;
    move_r r_t2 PC;
    lea_z r_t2 6;
    jnz r_t2 r_t1;
    move_r r_t2 PC;
    lea_z r_t2 4;
    jmp r_t2;
    fail_end;
    move_z r_t1 0;
    move_z r_t2 0].


  (* ------------------------------- *)

  Definition reqperm r z a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqperm_instrs r z), a_i ↦ₐ w_i)%I.

  Lemma reqperm_spec r perm a w pc_p pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ reqperm r (encodePerm perm) a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (if isPermWord w perm then
           ∃ l b e a', ⌜w = inr (perm,l,b,e,a')⌝ ∧
          (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ reqperm r (encodePerm perm) a ∗
            r ↦ᵣ inr (perm,l,b,e,a') ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z
            -∗ WP Seq (Instr Executable) {{ φ }})
        else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iDestruct ("Hr_t1") as (w1) "Hr_t1".
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    prep_addr_list_full a Hcont.
    iPrologue "Hprog".
    destruct w.
    { (* if w is an integer, the getL will fail *)
      iApply (wp_Get_fail with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|..].
      iEpilogue "_ /=".
      iApply wp_value. done.
    }
    (* if w is a capability, the getL will succeed *)
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1)". iRename "Hi" into "Hprog_done".
    destruct c,p,p,p. iSimpl in "Hr_t1". 
    (* sub r_t1 r_t1 (encodeLoc Global) *)
    iPrologue "Hprog". 
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 1|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done" as "Hprog_done". 
    iSimpl in "Hr_t1".
    (* move r_t2 PC *)
    iPrologue "Hprog".
    iDestruct "Hr_t2" as (w2) "Hr_t2". 
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t2 6 *)
    assert ((a1 + 6)%a = Some a7) as Hlea. 
    { apply (contiguous_between_incr_addr_middle _ _ _ 2 6 a1 a7) in Hcont; auto. }
    assert (pc_p ≠ E) as HneE.
    { eapply pc_range_not_E;eauto. } 
    iPrologue "Hprog". 
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|apply Hlea|auto..].
    { apply isCorrectPC_range_perm in Hvpc as [Heq | [Heq | Heq] ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto.  }
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    destruct (decide (encodePerm p - encodePerm perm = 0))%Z.
    - (* p is perm *)
      rewrite e. assert (p = perm);[apply encodePerm_inj;lia|subst]. 
      iSimpl in "Hcont". rewrite isPerm_refl. iDestruct "Hcont" as (l' b e0 a' Heq) "Hφ". inversion Heq; subst.
      iPrologue "Hprog". 
      iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|..].
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)";iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move_r r_t2 PC *)
      iPrologue "Hprog".
      iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* lea r_t2 3 *)
      assert ((a4 + 4)%a = Some a8) as Hlea'. 
      { apply (contiguous_between_incr_addr_middle _ _ _ 5 4 a4 a8) in Hcont; auto. }
      iPrologue "Hprog". 
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hlea'|auto..].
      { apply isCorrectPC_range_perm in Hvpc as [Heq' | [Heq' | Heq'] ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto.  }
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* jmp r_t2 *)
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t2]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      rewrite updatePcPerm_cap_non_E//.
      iDestruct "Hprog" as "[Hi Hprog]". iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move r_t1 0 *)
      iPrologue "Hprog".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]"); 
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 9|auto|..].
      iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      (* move r_t2 0 *)
      iPrologue "Hprog".
      apply contiguous_between_last with (ai:=a9) in Hcont as Hnext;[|auto]. 
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]"); 
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hnext|auto|..].
      iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      iApply "Hφ". iFrame "HPC Hr Hr_t1 Hr_t2".
      iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$&$)". done.
    - assert (p ≠ perm) as HneP.
      { intros Hcontr. subst. lia. }
      iSimpl in "Hcont". rewrite isPerm_ne;[|auto]. 
      (* jnz r_t2 r_t1 *)
      iPrologue "Hprog".
      iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t2 $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      { intros Hcontr. inversion Hcontr. done. }
      iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done". 
      do 3 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done"). 
      (* fail *)
      iPrologue "Hprog".
      rewrite updatePcPerm_cap_non_E//.
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|].
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont". 
  Qed.

  (* --------------------------------------- REQSIZE ----------------------------------- *)
  (* This macro checks that the capability in r covers a memory range of size
     (i.e. e-b) greater than [minsize]. *)

  Definition reqsize_instrs r (minsize: Z) :=
    [getb r_t1 r;
     gete r_t2 r;
     sub_r_r r_t1 r_t2 r_t1;
     lt_z_r r_t1 minsize r_t1;
     move_r r_t2 PC;
     lea_z r_t2 4;
     jnz r_t2 r_t1;
     fail_end].

  Definition reqsize r minsize a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqsize_instrs r minsize), a_i ↦ₐ w_i)%I.

  Lemma reqsize_spec r minsize a pc_p pc_g pc_b pc_e a_first a_last r_p r_g r_b r_e r_a w1 w2 φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →

      ▷ reqsize r minsize a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ inr (r_p, r_g, r_b, r_e, r_a)
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ (if (minsize <? (r_e - r_b)%a)%Z then
           (∃ w1 w2,
            reqsize r minsize a
            ∗ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last)
            ∗ r ↦ᵣ inr (r_p, r_g, r_b, r_e, r_a)
            ∗ r_t1 ↦ᵣ w1
            ∗ r_t2 ↦ᵣ w2)
           -∗ WP Seq (Instr Executable) {{ φ }}
        else φ FailedV)
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr1 & >Hr2 & Hcont)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { iIntros (->). iApply (regname_dupl_false with "HPC Hr"). }
    prep_addr_list_full a Hcont.
    assert (pc_p ≠ E).
    { eapply pc_range_not_E;eauto. }
    (* getb r_t1 r *)
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..];
      simpl.
    iEpilogue "(HPC & Hi & Hr & Hr1)". iRename "Hi" into "Hprog_done".
    (* gete r_t2 r *)
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr2]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..];
      simpl.
    iEpilogue "(HPC & Hi & Hr & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub_r_r r_t1 r_t2 r_t1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_r_dst with "[$HPC $Hi $Hr2 $Hr1]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 2|iCorrectPC a_first a_last|..];
      simpl.
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lt_z_r r_t1 minsize r_t1 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_z_dst with "[$HPC $Hi $Hr1]");
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 3|iCorrectPC a_first a_last|..];
      simpl.
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t2 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|auto..].
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t2 4 *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|try done..].
    { change 4%Z with (Z.of_nat (4%nat)).
      (* FIXME: a bit annoying to have to specify the index manually *)
      eapply (contiguous_between_middle_to_end _ _ _ 4); eauto. }
    { assert (isCorrectPC (inr (pc_p, pc_g, pc_b, pc_e, a_first))) as HH.
      iCorrectPC a_first a_last. inversion HH; subst.
      repeat match goal with H: _ ∨ _ |- _ => destruct H end; subst; auto. }
    iEpilogue "(HPC & Hi & Hr2)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t2 r_t1 *)
    iPrologue "Hprog".
    destruct (minsize <? r_e - r_b)%Z eqn:Htest; simpl.
    { iApply (wp_jnz_success_jmp with "[$HPC $Hr2 $Hr1 $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|done|..].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iApply "Hcont". iExists _,_.
      rewrite updatePcPerm_cap_non_E //. iFrame.
      iDestruct "Hprog_done" as "(?&?&?&?&?&?)". simpl. iFrame. }
    { iApply (wp_jnz_success_next with "[$HPC $Hr2 $Hr1 $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|..].
      iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* fail_end *)
      iPrologue "Hprog".
      iApply (wp_fail with "[$HPC $Hi]");
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|..].
      iEpilogue "(HPC & Hi)". iApply wp_value. iApply "Hcont". }
  Qed.

End stack_macros.
