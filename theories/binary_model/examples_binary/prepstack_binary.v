From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import stack_macros_helpers.
From cap_machine Require Export iris_extra addr_reg_sample contiguous.
From cap_machine Require Import macros.
From cap_machine.binary_model.rules_binary Require Import rules_binary rules_binary_StoreU_derived.
From cap_machine.binary_model.examples_binary Require Import req_binary.

Ltac iPrologue_s prog :=
  (try iPrologue_pre);
  iDestruct prog as "[Hi Hprog]".

Ltac iEpilogue_s :=
   iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj";auto;
   iSimpl in "Hj".

Section macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {cfg : cfgSG Σ}
          `{MP: MachineParameters}.

  (* TODO: move this to the rules_binary_Lea.v file. small issue with the spec of failure: it does not actually
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)
  Lemma step_Lea_fail_U E K pc_p pc_g pc_b pc_e pc_a w r1 rv p g b e a z a' :
    decodeInstrW w = Lea r1 (inr rv) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (a + z)%a = Some a' ->
     (match p with
      | URW | URWL | URWX | URWLX => (a < a')%a
      | _ => False
      end) ->
     nclose specN ⊆ E →

     spec_ctx ∗ ⤇ fill K (Instr Executable)
              ∗ ▷ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
              ∗ ▷ pc_a ↣ₐ w
              ∗ ▷ r1 ↣ᵣ inr ((p,g),b,e,a)
              ∗ ▷ rv ↣ᵣ inl z
     ={E}=∗
         ⤇ fill K (Instr Failed).
  Proof.
    iIntros (Hdecode Hvpc Hz Hp Hnclose) "(#Hspec & Hj & >HPC & >Hpc_a & >Hsrc & >Hdst)".
    iDestruct (rules_binary_base.map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iMod (step_lea with "[$Hmap Hpc_a $Hspec $Hj]") as (regs' retv) "(Hj & #Hspec' & Hpc_a & Hmap)"; eauto; simplify_map_eq; eauto.
      by rewrite !dom_insert; set_solver+.
    iDestruct "Hspec'" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. destruct p0; try done; revert Hp H5;clear;solve_addr. }
    { (* Failure, done *) iFrame. done. }
  Qed.

  Definition prepstackU_s r minsize paramsize a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(prepstackU_instrs r minsize paramsize), a_i ↣ₐ w_i)%I.

  Lemma prepstackU_s_spec E r minsize paramsize a w pc_p pc_g pc_b pc_e a_first a_last :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->
    nclose specN ⊆ E →

    spec_ctx ∗ ⤇ Seq (Instr Executable)
    ∗ ▷ prepstackU_s r minsize paramsize a
    ∗ ▷ PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↣ᵣ w
    ∗ ▷ (∃ w, r_t1 ↣ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↣ᵣ w)
    ={E}=∗ (if isPermWord w URWLX then
           ∃ l b e a', ⌜w = inr (URWLX,l,b,e,a')⌝ ∗
           if (minsize + paramsize <? e - b)%Z then
             if ((b + paramsize) <=? a')%Z then
               (∃ a_param, ⌜(b + paramsize)%a = Some a_param⌝ ∧
                   ⤇ Seq (Instr Executable) ∗
                   PC ↣ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ prepstackU_s r minsize paramsize a ∗
                   r ↣ᵣ inr (URWLX,l,b,e,a_param) ∗ r_t1 ↣ᵣ inl 0%Z ∗ r_t2 ↣ᵣ inl 0%Z)
             else ⤇ Seq (Instr Failed)
           else ⤇ Seq (Instr Failed)
         else ⤇ Seq (Instr Failed)).
  Proof.
    iIntros (Hvpc Hcont Hnclose) "(#Hspec & Hj & >Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    (* reqperm *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iMod (reqperm_spec with "[- $HPC $Hcode $Hr $Hr_t1 $Hr_t2 Hprog $Hspec $Hj]") as "Hcond"; [apply Hvpc_code|apply Hcont_code|auto..].
    destruct (isPermWord w URWLX); auto.
    iDestruct "Hcond" as (l b e a' Heq) "Hφ".
    subst. iExists l,b,e,a'. iSplitR; auto.
    iDestruct "Hφ" as  "(Hj & HPC & Hprog_done & Hr & Hr_t1 & Hr_t2)".
    (* reqsize *)
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iMod (reqsize_spec with "[$HPC $Hcode $Hr $Hr_t1 $Hr_t2 $Hspec $Hj]") as "Hφ";
      [apply Hvpc_code0|eauto|auto..].
    destruct (minsize + paramsize <? e - b)%Z eqn:Hsize; auto.
    iDestruct "Hφ" as (w1 w2) "(Hj & Hreqsize & HPC & Hr & Hr_t1 & Hr_t2)".
    (* getb r_t1 r *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength'.
    prep_addr_list_full l_rest0 Hcont.
    iPrologue_s "Hprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr $Hr_t1]")
      as "(Hj & HPC & Hi & Hr & Hr_t1) /=";
      [apply decode_encode_instrW_inv|auto|iCorrectPC link0 a_last|iContiguous_next Hcont 0|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* geta r_t2 r *)
    iPrologue_s "Hprog".
    iMod (step_Get_success _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr $Hr_t2]")
      as "(Hj & HPC & Hi & Hr & Hr_t2) /=";
      [apply decode_encode_instrW_inv|auto|iCorrectPC link0 a_last|iContiguous_next Hcont 1|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* add r_t2 r_t2 paramsize *)
    iPrologue_s "Hprog".
    iMod (step_add_sub_lt_success_dst_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t2]")
      as "(Hj & HPC & Hi & Hr_t2) /=";
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 2|iCorrectPC link0 a_last|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub r_t1 r_t1 r_t2 *)
    iPrologue_s "Hprog".
    iMod (step_add_sub_lt_success_dst_r _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t2 $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t2 & Hr_t1) /=";
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 3|iCorrectPC link0 a_last|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* we need to distinguish between the case where the capability is stuck, or usable *)
    assert (∃ a_param, (b + paramsize)%a = Some a_param) as [a_param Ha_param].
    { destruct (b + paramsize)%a eqn:Hnone;eauto. exfalso. clear -Hnone Hsize. apply Z.ltb_lt in Hsize. solve_addr. }
    assert ((a' + (b - (a' - paramsize)))%a = Some a_param) as Hlea;[clear -Ha_param; solve_addr|].
    destruct (decide (a_param <= a')%a).
    2: { (* lea fail *)
      iPrologue_s "Hprog".
      iMod (step_Lea_fail_U _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Hr]")
        as "Hj";
        [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|apply Hlea|auto..].
      { simpl. solve_addr. }
      assert (b + paramsize <=? a' = false)%Z as ->;[apply Z.leb_gt;solve_addr|].
      iFrame. done. }
    (* lea r r_t1 *)
    iPrologue_s "Hprog".
    iMod (step_lea_success_reg _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1 $Hr]")
      as "(Hj & HPC & Hi & Hr_t1 & Hr)";
      [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next Hcont 4|apply Hlea|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 0 *)
    iPrologue_s "Hprog".
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t1]")
      as "(Hj & HPC & Hi & Hr_t1)";
      [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next Hcont 5|auto..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    iPrologue_s "Hprog".
    apply contiguous_between_last with (ai:=a5) in Hcont as Hlast;[|auto].
    iMod (step_move_success_z _ [SeqCtx] with "[$Hspec $Hj $HPC $Hi $Hr_t2]")
      as "(Hj & HPC & Hi & Hr_t2)";
      [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|apply Hlast|auto|..].
    iEpilogue_s; iCombine "Hi" "Hprog_done" as "Hprog_done".
    assert (b + paramsize <=? a' = true)%Z as ->;[apply Zle_is_le_bool;auto;clear -Ha_param l0;solve_addr|].
    iExists a_param. iSplitR;auto. iFrame.
    repeat (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi").
    iFrame "Hprog_done". done.
  Qed.

End macros.
