From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel stack_macros_helpers.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.
From cap_machine Require Import macros.
From cap_machine.binary_model.rules_binary Require Import rules_binary rules_binary_StoreU_derived.


Ltac iPrologue_s prog :=
  (try iPrologue_pre);
  iDestruct prog as "[Hi Hprog]".

Ltac iEpilogue_s :=
   iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj";auto;
   iSimpl in "Hj".

Section macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MP: MachineParameters}.

  Lemma step_Get_fail E K get_i dst src pc_p pc_g pc_b pc_e pc_a w zsrc wdst :
    decodeInstrW w = get_i →
    is_Get get_i dst src →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ fill K (Instr Executable)
      ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
      ∗ ▷ pc_a ↣ₐ w
      ∗ ▷ dst ↣ᵣ wdst
      ∗ ▷ src ↣ᵣ inl zsrc
    ={E}=∗
        ⤇ fill K (Instr Failed).
  Proof.
    iIntros (Hdecode Hinstr Hvpc Hnclose) "(#Hspec & Hj & >HPC & >Hpc_a & >Hsrc & >Hdst)".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iMod (step_Get with "[$Hmap Hpc_a $Hj $Hspec]") as (retv regs') "(Hj & Hspec' & Hmap & Hpc_a)"; eauto; simplify_map_eq; eauto.
      by erewrite regs_of_is_Get; eauto; rewrite !dom_insert; set_solver+.
    iDestruct "Hspec'" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. }
    { (* Failure, done *) by iFrame. }
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* --------------------------------------- REQ ------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  (* -------------------------------------- REQPERM ----------------------------------- *)
  (* the following macro requires that a given registers contains a capability with a
     given (encoded) permission. If this is not the case, the macro goes to fail,
     otherwise it continues *)

  Definition reqperm_s r z a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqperm_instrs r z), a_i ↣ₐ w_i)%I.

  Lemma reqperm_spec E r perm a w pc_p pc_g pc_b pc_e a_first a_last :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ reqperm_s r (encodePerm perm) a
    ∗ ▷ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↣ᵣ w
    ∗ ▷ (∃ w, r_t1 ↣ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↣ᵣ w)
    ={E}=∗
         (if isPermWord w perm then
             ∃ l b e a', ⌜w = inr (perm,l,b,e,a')⌝ ∧
                         ⤇ Seq (Instr Executable)
                           ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ reqperm_s r (encodePerm perm) a ∗
                           r ↣ᵣ inr (perm,l,b,e,a') ∗ r_t1 ↣ᵣ inl 0%Z ∗ r_t2 ↣ᵣ inl 0%Z
           else ⤇ Seq (Instr Failed)).
  Proof.
    iIntros (Hvpc Hcont Hnclose) "(#Hspec & Hj & >Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iDestruct ("Hr_t1") as (w1) "Hr_t1".
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    prep_addr_list_full a Hcont.
    iPrologue_s "Hprog".
    destruct w.
    { (* if w is an integer, the getL will fail *)
      iMod (step_Get_fail _ [SeqCtx] with "[$HPC $Hi $Hr_t1 $Hr $Hspec $Hj]");
        [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|auto..]. }
    (* if w is a capability, the getL will succeed *)
    iMod (step_Get_success _ [SeqCtx] with "[$HPC $Hi $Hr $Hr_t1 $Hspec $Hj]") as "(Hj & HPC & Hi & Hr & Hr_t1)";
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..].
    iRename "Hi" into "Hprog_done".
    destruct c,p,p,p. iSimpl in "Hr_t1".
    iEpilogue_s.
    (* sub r_t1 r_t1 (encodeLoc Global) *)
    iPrologue_s "Hprog". 
    iMod (step_add_sub_lt_success_dst_z _ [SeqCtx] with "[$HPC $Hi $Hr_t1 $Hspec $Hj]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 1|iCorrectPC a_first a_last|auto..].
    iEpilogue_s. iCombine "Hi" "Hprog_done" as "Hprog_done".
    iSimpl in "Hr_t1".
    (* move r_t2 PC *)
    iPrologue_s "Hprog".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$HPC $Hi $Hr_t2 $Hspec $Hj]")
      as "(Hj & HPC & Hi & Hr_t2)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto|..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t2 6 *)
    assert ((a1 + 6)%a = Some a7) as Hlea.
    { apply (contiguous_between_incr_addr_middle _ _ _ 2 6 a1 a7) in Hcont; auto. }
    assert (pc_p ≠ machine_base.E) as HneE.
    { eapply pc_range_not_E;eauto. }
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$HPC $Hi $Hr_t2 $Hj $Hspec]")
      as "(Hj & HPC & Hi & Hr_t2)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 3|apply Hlea|auto..].
    { apply isCorrectPC_range_perm in Hvpc as [Heq | [Heq | Heq] ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto.  }
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    destruct (decide (encodePerm p - encodePerm perm = 0))%Z.
    - (* p is perm *)
      rewrite e. assert (p = perm);[apply encodePerm_inj;lia|subst].
      iPrologue_s "Hprog".
      iMod (step_jnz_success_next _ [SeqCtx] with "[$HPC $Hi $Hr_t2 $Hr_t1 $Hspec $Hj]")
        as "(Hj & HPC & Hi & Hr_t2 & Hr_t1)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|auto..].
      iEpilogue_s;iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move_r r_t2 PC *)
      iPrologue_s "Hprog".
      iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$HPC $Hi $Hr_t2 $Hspec $Hj]")
        as "(Hj & HPC & Hi & Hr_t2)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|auto|..].
      iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* lea r_t2 3 *)
      assert ((a4 + 4)%a = Some a8) as Hlea'.
      { apply (contiguous_between_incr_addr_middle _ _ _ 5 4 a4 a8) in Hcont; auto. }
      iPrologue_s "Hprog".
      iMod (step_lea_success_z _ [SeqCtx] with "[$HPC $Hi $Hr_t2 $Hj $Hspec]")
        as "(Hj & HPC & Hi & Hr_t2)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hlea'|auto..].
      { apply isCorrectPC_range_perm in Hvpc as [Heq' | [Heq' | Heq'] ]; subst; auto.
      apply (contiguous_between_middle_bounds _ 0 a_first) in Hcont as [_ Hlt]; auto.  }
      iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* jmp r_t2 *)
      iPrologue_s "Hprog".
      iMod (step_jmp_success _ [SeqCtx] with "[$HPC $Hi $Hr_t2 $Hspec $Hj]")
        as "(Hj & HPC & Hi & Hr_t2)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto..].
      iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
      rewrite updatePcPerm_cap_non_E//.
      iDestruct "Hprog" as "[Hi Hprog]". iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t1 0 *)
      iPrologue_s "Hprog".
      iMod (step_move_success_z _ [SeqCtx] with "[$HPC $Hi $Hr_t1 $Hspec $Hj]")
        as "(Hj & HPC & Hi & Hr_t1)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 9|auto|..].
      iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* move r_t2 0 *)
      iPrologue_s "Hprog".
      apply contiguous_between_last with (ai:=a9) in Hcont as Hnext;[|auto].
      iMod (step_move_success_z _ [SeqCtx] with "[$HPC $Hi $Hr_t2 $Hspec $Hj]")
        as "(Hj & HPC & Hi & Hr_t2)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|apply Hnext|auto|..].
      iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
      simpl. assert (isPerm perm perm = true) as ->;[rewrite /isPerm /= /bool_decide decide_True//|].
      iModIntro. iExists _,_,_,_. iSplit;eauto. iFrame.
      iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$&$)". done.
    - assert (p ≠ perm) as HneP.
      { intros Hcontr. subst. lia. }
      simpl. rewrite isPerm_ne//.
      iPrologue_s "Hprog".
      iMod (step_jnz_success_jmp _ [SeqCtx] with "[$HPC $Hi $Hr_t2 $Hr_t1 $Hspec $Hj]")
        as "(Hj & HPC & Hi & Hr_t2 & Hr_t1)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto..].
      { intros Hcontr. inversion Hcontr. done. }
      iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
      do 3 (iDestruct "Hprog" as "[Hi Hprog]"; iCombine "Hi" "Hprog_done" as "Hprog_done").
      (* fail *)
      iPrologue_s "Hprog".
      rewrite updatePcPerm_cap_non_E//.
      iMod (step_fail _ [SeqCtx] with "[$HPC $Hi $Hspec $Hj]") as "(Hj & HPC & Hi)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto..].
  Qed.

  (* --------------------------------------- REQSIZE ----------------------------------- *)
  (* This macro checks that the capability in r covers a memory range of size
     (i.e. e-b) greater than [minsize]. *)

  Definition reqsize_s r minsize a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(reqsize_instrs r minsize), a_i ↣ₐ w_i)%I.

  Lemma reqsize_spec E r minsize a pc_p pc_g pc_b pc_e a_first a_last r_p r_g r_b r_e r_a w1 w2 :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ reqsize_s r minsize a
    ∗ ▷ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↣ᵣ inr (r_p, r_g, r_b, r_e, r_a)
    ∗ ▷ r_t1 ↣ᵣ w1
    ∗ ▷ r_t2 ↣ᵣ w2
    ={E}=∗
         (if (minsize <? (r_e - r_b)%a)%Z then
           (∃ w1 w2,
               ⤇ Seq (Instr Executable)
            ∗ reqsize_s r minsize a
            ∗ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last)
            ∗ r ↣ᵣ inr (r_p, r_g, r_b, r_e, r_a)
            ∗ r_t1 ↣ᵣ w1
            ∗ r_t2 ↣ᵣ w2)
           else ⤇ Seq (Instr Failed)).
  Proof.
    iIntros (Hvpc Hcont Hnclose) "(#Hspec & Hj & >Hprog & >HPC & >Hr & >Hr1 & >Hr2)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { iIntros (->). iApply (regname_dupl_false with "HPC Hr"). }
    prep_addr_list_full a Hcont.
    assert (pc_p ≠ machine_base.E).
    { eapply pc_range_not_E;eauto. }
    (* getb r_t1 r *)
    iPrologue_s "Hprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hj $Hspec $HPC $Hi $Hr $Hr1]") as "(Hj & HPC & Hi & Hr & Hr1)";
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto..];
      simpl.
    iEpilogue_s. iRename "Hi" into "Hprog_done".
    (* gete r_t2 r *)
    iPrologue_s "Hprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hj $Hspec $HPC $Hi $Hr $Hr2]") as "(Hj & HPC & Hi & Hr & Hr2)";
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..];
      simpl.
    iEpilogue_s. iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub_r_r r_t1 r_t2 r_t1 *)
    iPrologue_s "Hprog".
    iMod (step_add_sub_lt_success_r_dst _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr2 $Hr1]")
      as "(Hj & HPC & Hi & Hr2 & Hr1)";
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 2|iCorrectPC a_first a_last|auto..];
      simpl.
    iEpilogue_s. iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lt_z_r r_t1 minsize r_t1 *)
    iPrologue_s "Hprog".
    iMod (step_add_sub_lt_success_z_dst _ [SeqCtx] with "[$Hj $Hspec $HPC $Hi $Hr1]")
      as "(Hj & HPC & Hi & Hr1)";
      [apply decode_encode_instrW_inv|done|iContiguous_next Hcont 3|iCorrectPC a_first a_last|auto..];
      simpl.
    iEpilogue_s. iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t2 PC *)
    iPrologue_s "Hprog".
    iMod (step_move_success_reg_fromPC _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr2]")
      as "(Hj & HPC & Hi & Hr2)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|auto..].
    iEpilogue_s. iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t2 4 *)
    iPrologue_s "Hprog".
    iMod (step_lea_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr2]")
      as "(Hj & HPC & Hi & Hr2)";
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 5|try done..].
    { change 4%Z with (Z.of_nat (4%nat)).
      (* FIXME: a bit annoying to have to specify the index manually *)
      eapply (contiguous_between_middle_to_end _ _ _ 4); eauto. }
    { assert (isCorrectPC (inr (pc_p, pc_g, pc_b, pc_e, a_first))) as HH.
      iCorrectPC a_first a_last. inversion HH; subst.
      repeat match goal with H: _ ∨ _ |- _ => destruct H end; subst; auto. }
    iEpilogue_s. iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* jnz r_t2 r_t1 *)
    iPrologue_s "Hprog".
    destruct (minsize <? r_e - r_b)%Z eqn:Htest; simpl.
    { iMod (step_jnz_success_jmp _ [SeqCtx] with "[$Hspec $Hj $HPC $Hr2 $Hr1 $Hi]")
        as "(Hj & HPC & Hi & Hr2 & Hr1)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|done|auto..].
      iEpilogue_s. iExists _,_. iModIntro.
      rewrite updatePcPerm_cap_non_E //. iFrame.
      iDestruct "Hprog_done" as "(?&?&?&?&?&?)". simpl. iFrame. }
    { iMod (step_jnz_success_next _ [SeqCtx] with "[$Hspec $Hj $HPC $Hr2 $Hr1 $Hi]")
        as "(Hj & HPC & Hi & Hr2 & Hr1)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|auto..].
      iEpilogue_s. iCombine "Hi" "Hprog_done" as "Hprog_done".
      (* fail_end *)
      iPrologue_s "Hprog".
      iMod (step_fail _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi]")
        as "(Hj & HPC & Hi)";
        [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto..].
    }
  Qed.

End macros.
