From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export addr_reg_sample region_macros contiguous stack_macros_helpers.
From cap_machine Require Export req.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (* TODO: move this to the rules_Lea.v file. small issue with the spec of failure: it does not actually
     require/leave a trace on dst! It would be good if req_regs of a failing get does not include dst (if possible) *)
  Lemma wp_Lea_fail_U Ep pc_p pc_g pc_b pc_e pc_a w r1 rv p g b e a z a' :
    decodeInstrW w = Lea r1 (inr rv) →
    isCorrectPC (inr ((pc_p,pc_g),pc_b,pc_e,pc_a)) →
    (a + z)%a = Some a' ->
     (match p with
      | URW | URWL | URWX | URWLX => (a < a')%a
      | _ => False
      end) ->

     {{{ ▷ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,pc_a)
           ∗ ▷ pc_a ↦ₐ w
           ∗ ▷ r1 ↦ᵣ inr ((p,g),b,e,a)
           ∗ ▷ rv ↦ᵣ inl z }}}
       Instr Executable @ Ep
     {{{ RET FailedV; True }}}.
  Proof.
    iIntros (Hdecode Hvpc Hz Hp φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_lea with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
      by rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)".
    iDestruct "Hspec" as %Hspec.
    destruct Hspec as [* Hsucc |].
    { (* Success (contradiction) *) simplify_map_eq. destruct p0; try done; revert Hp H5;clear;solve_addr. }
    { (* Failure, done *) by iApply "Hφ". }
  Qed.

  Definition prepstackU_instrs r (minsize paramsize: nat) :=
    reqperm_instrs r (encodePerm URWLX) ++
    reqsize_instrs r (minsize + paramsize) ++
    [getb r_t1 r;
    geta r_t2 r;
    sub_r_z r_t2 r_t2 paramsize;
    sub_r_r r_t1 r_t1 r_t2;
    lea_r r r_t1;
    move_z r_t1 0;
    move_z r_t2 0].

  Definition prepstackU r minsize paramsize a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(prepstackU_instrs r minsize paramsize), a_i ↦ₐ w_i)%I.

  Lemma prepstackU_spec r minsize paramsize a w pc_p pc_g pc_b pc_e a_first a_last φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->

      ▷ prepstackU r minsize paramsize a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ r ↦ᵣ w
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (if isPermWord w URWLX then
           ∃ l b e a', ⌜w = inr (URWLX,l,b,e,a')⌝ ∧
           if (minsize + paramsize <? e - b)%Z then
             if ((b + paramsize) <=? a')%Z then
               ((∃ a_param, ⌜(b + paramsize)%a = Some a_param⌝ ∧
                   PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ prepstackU r minsize paramsize a ∗
                   r ↦ᵣ inr (URWLX,l,b,e,a_param) ∗ r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z)
                   -∗ WP Seq (Instr Executable) {{ φ }})
             else φ FailedV
           else φ FailedV
         else φ FailedV)
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont) "(>Hprog & >HPC & >Hr & >Hr_t1 & >Hr_t2 & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength. simpl in *.
    iAssert (⌜r ≠ PC⌝)%I as %Hne.
    { destruct (decide (r = PC)); auto; subst. iDestruct (regname_dupl_false with "HPC Hr") as %Hcontr. done. }
    (* reqperm *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iApply (reqperm_spec with "[$HPC $Hcode $Hr $Hr_t1 $Hr_t2 Hφ Hprog]"); [apply Hvpc_code|apply Hcont_code|].
    iNext. destruct (isPermWord w URWLX); auto.
    iDestruct "Hφ" as (l b e a' Heq) "Hφ".
    subst. iExists l,b,e,a'. iSplit; auto.
    iIntros "(HPC & Hprog_done & Hr & Hr_t1 & Hr_t2)".
    (* reqsize *)
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iApply (reqsize_spec with "[- $HPC $Hcode $Hr $Hr_t1 $Hr_t2]");
      [apply Hvpc_code0|eauto|].
    iNext. destruct (minsize + paramsize <? e - b)%Z eqn:Hsize; auto.
    iIntros "H". iDestruct "H" as (w1 w2) "(Hreqsize & HPC & Hr & Hr_t1 & Hr_t2)".
    (* getb r_t1 r *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength'.
    prep_addr_list_full l_rest0 Hcont.
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC link0 a_last|iContiguous_next Hcont 0|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* geta r_t2 r *)
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr $Hr_t2]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC link0 a_last|iContiguous_next Hcont 1|auto..].
    iEpilogue "(HPC & Hi & Hr & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* add r_t2 r_t2 paramsize *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 2|iCorrectPC link0 a_last|..].
    iEpilogue "(HPC & Hi & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* sub r_t1 r_t1 r_t2 *)
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 3|iCorrectPC link0 a_last|..].
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* we need to distinguish between the case where the capability is stuck, or usable *)
    assert (∃ a_param, (b + paramsize)%a = Some a_param) as [a_param Ha_param].
    { destruct (b + paramsize)%a eqn:Hnone;eauto. exfalso. clear -Hnone Hsize. apply Z.ltb_lt in Hsize. solve_addr. }
    assert ((a' + (b - (a' - paramsize)))%a = Some a_param) as Hlea;[clear -Ha_param; solve_addr|].
    destruct (decide (a_param <= a')%a).
    2: { (* lea fail *)
      iPrologue "Hprog".
      iApply (wp_Lea_fail_U with "[$HPC $Hi $Hr_t1 $Hr]");
        [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|apply Hlea|..].
      { simpl. solve_addr. }
      iEpilogue "_ /=". assert (b + paramsize <=? a' = false)%Z as ->;[apply Z.leb_gt;solve_addr|].
      iApply wp_value. iApply "Hφ". }
    (* lea r r_t1 *)
    iPrologue "Hprog".
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next Hcont 4|apply Hlea|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 0 *)
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|iContiguous_next Hcont 5|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    iPrologue "Hprog".
    apply contiguous_between_last with (ai:=a5) in Hcont as Hlast;[|auto].
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC link0 a_last|apply Hlast|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    assert (b + paramsize <=? a' = true)%Z as ->;[apply Zle_is_le_bool;auto;clear -Ha_param l0;solve_addr|].
    iApply "Hφ". iFrame. iExists a_param. iSplit;auto. iFrame.
    repeat (iDestruct "Hprog_done" as "[Hi Hprog_done]"; iFrame "Hi").
    iFrame "Hprog_done". done.
  Qed.

End stack_macros.
