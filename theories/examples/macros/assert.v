From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers fetch.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- ASSERT ------------------------------------ *)
  (* --------------------------------------------------------------------------------- *)

  (* The assert macro relies on a convention for the failure flag. This file contains the 
     failure subroutine *)

  (* The convention for the failure flag: one address after the last instruction of the failure subroutine *)
  (* failing the assert will set the flag to 1 and then crash the program to a Failed configuration. The flag 
     capability is at one address after the instructions *)
  Definition assert_fail_instrs :=
    [move_r r_t1 PC;
    lea_z r_t1 6;
    load_r r_t1 r_t1;
    store_z r_t1 1;
    move_z r_t1 0;
    fail_end].

  Definition assert_fail a :=
    ([∗ list] a_i;w_i ∈ a;(assert_fail_instrs), a_i ↦ₐ w_i)%I.

  (* f_a is the offset of the failure subroutine in the linking table *)
  (* assert r z asserts that the register r contains the integer z *)
  (* r is assumed not to be r_t1 *)
  Definition assert_r_z_instrs f_a r z :=
    fetch_instrs f_a ++
    [sub_r_z r r z;
    jnz r_t1 r;
    move_z r_t1 0].

  Definition assert_r_z a f_a r z :=
    ([∗ list] a_i;w_i ∈ a;(assert_r_z_instrs f_a r z), a_i ↦ₐ w_i)%I.

  (* Spec for assertion success *)
  (* Since we are not jumping to the failure subroutine, we do not need any assumptions
     about the failure subroutine *)
  Lemma assert_r_z_success a f_a r z pc_p pc_g pc_b pc_e a_first a_last
        b_link e_link a_link a_entry fail_cap w_r φ :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    (* linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->
    (* condition for assertion success *)
    (w_r = inl z) ->

    ▷ assert_r_z a f_a r z
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link)
    ∗ ▷ a_entry ↦ₐ fail_cap
    ∗ ▷ r ↦ᵣ w_r
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t3 ↦ᵣ w)
    ∗ ▷ (r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z ∗ r ↦ᵣ inl 0%Z
         ∗ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ assert_r_z a f_a r z
         ∗ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ fail_cap
         -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
    WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Htable Hsuccess)
            "(>Hprog & >HPC & >Hpc_b & >Ha_entry & >Hr & >Hr_t1 & >Hr_t2 & >Hr_t3 & Hφ)".
     (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iDestruct "Hr_t1" as (w1) "Hr_t1".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3". 
    iApply (fetch_spec with "[$HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b Hφ Hprog Hr]");
      [|apply Hcont_fetch|apply Hwb|apply Htable|]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a0 l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst a0.
    (* sub_r_z r r z *)
    destruct l';[inversion Hlength_rest|].
    inversion Hsuccess. subst w_r.  
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr]");
      [apply decode_encode_instrW_inv|right;left;eauto|iContiguous_next Hcont_rest 0|iCorrectPC link a_last|..].
    iEpilogue "(HPC & Hi & Hr)"; iCombine "Hfetch" "Hi" as "Hprog_done". 
    (* jnz r_t1 r *)
    rewrite /= Z.sub_diag. 
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_jnz_success_next with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|iContiguous_next Hcont_rest 1|].
    iEpilogue "(HPC & Hinstr & Hr_t1 & Hr)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".  
    (* move r_t1 0 *)
    destruct l';[|inversion Hlength_rest].
    apply contiguous_between_last with (ai:=a1) in Hcont_rest as Hlink';[|auto].
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|apply Hlink'|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* Continuation *)
    iApply "Hφ". iFrame.
    rewrite Heqapp /=. iDestruct "Hprog_done" as "(?&?&?&?)". iFrame. done.
  Qed.

  (* Spec for assertion failure *)
  (* When the assertion fails, the program jumps to the failure subroutine, sets the 
     flag (which by convention is one address after subroutine) and Fails *)
  Lemma assert_r_z_fail a f_a r z pc_p pc_g pc_b pc_e a_first a_last z_r
        b_link e_link a_link a_entry
        f_b f_e f_a_first f_a_last a' a_env (* fail subroutine *)
        flag_p flag_b flag_e flag_a (* flag capability *) :
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last →
    contiguous_between a a_first a_last →
    (* linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->
    (* failure subroutine assumptions *)
    isCorrectPC_range RX Global f_b f_e f_a_first f_a_last →
    contiguous_between a' f_a_first f_a_last →
    (f_a_first + (length a'))%a = Some a_env ->
    withinBounds (RX,Global,f_b,f_e,a_env) = true ->
    (* flag assumptions *)
    withinBounds (flag_p,Global,flag_b,flag_e,flag_a) = true ∧ writeAllowed flag_p = true ->
    (* condition for assertion success *)
    (z_r ≠ z) ->

    (* the assert and assert failure subroutine programs *)
    {{{ ▷ assert_r_z a f_a r z
    ∗ ▷ assert_fail a'
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    (* linking table and assertion flag *)
    ∗ ▷ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link) (* the linking table capability *)
    ∗ ▷ a_entry ↦ₐ inr (E,Global,f_b,f_e,f_a_first) (* the capability to the failure subroutine *)
    ∗ ▷ a_env ↦ₐ inr (flag_p,Global,flag_b,flag_e,flag_a) (* the assertion flag capability *)
    ∗ ▷ (∃ w, flag_a ↦ₐ w) (* the assertion flag *)
    (* registers *)
    ∗ ▷ r ↦ᵣ inl z_r
    ∗ ▷ (∃ w, r_t1 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t2 ↦ᵣ w)
    ∗ ▷ (∃ w, r_t3 ↦ᵣ w) }}}
      Seq (Instr Executable)
    {{{ RET FailedV; r_t1 ↦ᵣ inl 0%Z ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z ∗ (∃ z, r ↦ᵣ inl z ∧ ⌜z ≠ 0⌝)
         ∗ PC ↦ᵣ inr (RX, Global, f_b, f_e,^(f_a_last + (-1))%a)
         ∗ assert_r_z a f_a r z ∗ assert_fail a'
         ∗ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ inr (E,Global,f_b,f_e,f_a_first)
         ∗ a_env ↦ₐ inr (flag_p,Global,flag_b,flag_e,flag_a) ∗ flag_a ↦ₐinl 1%Z }}}. 
  Proof.
    iIntros (Hvpc Hcont Hwb Htable Hvpc' Hcont' Henv Henvwb [Hwb' Hwa] Hfailure φ) 
            "(>Hprog & >Hprog' & >HPC & >Hpc_b & >Ha_entry & >Ha_env & >Hflag & >Hr & >Hr_t1 & >Hr_t2 & >Hr_t3) Hφ".
    iDestruct "Hflag" as (flag_w) "Hflag". 
    (* fetch f *)
    iDestruct (contiguous_between_program_split with "Hprog") as (fetch_prog rest link)
                                                                   "(Hfetch & Hprog & #Hcont)";[apply Hcont|].
    iDestruct "Hcont" as %(Hcont_fetch & Hcont_rest & Heqapp & Hlink).
    iDestruct "Hr_t1" as (w1) "Hr_t1".
    iDestruct "Hr_t2" as (w2) "Hr_t2".
    iDestruct "Hr_t3" as (w3) "Hr_t3". 
    iApply (fetch_spec with "[$HPC $Hfetch $Hr_t1 $Hr_t2 $Hr_t3 $Ha_entry $Hpc_b Hφ Hprog Hr Hprog' Ha_env Hflag]");
      [|apply Hcont_fetch|apply Hwb|apply Htable|]. 
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto.
      apply contiguous_between_bounds in Hcont_rest. revert Hcont_rest Hmid; clear. solve_addr. }
    iNext. iIntros "(HPC & Hfetch& Hr_t1 & Hr_t2 & Hr_t3 & Hpc_b & Ha_entry)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    assert (isCorrectPC_range pc_p pc_g pc_b pc_e link a_last) as Hvpc_rest.
    { intros mid Hmid. apply isCorrectPC_inrange with a_first a_last; auto. revert Hmid Hlink;clear. solve_addr. }
    destruct rest as [|a0 l'];[inversion Hlength_rest|].
    apply contiguous_between_cons_inv_first in Hcont_rest as Heq. subst a0.
    (* sub_r_z r r z *)
    destruct l';[inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr]");
      [apply decode_encode_instrW_inv|right;left;eauto|iContiguous_next Hcont_rest 0|iCorrectPC link a_last|..].
    iEpilogue "(HPC & Hi & Hr)"; iCombine "Hi" "Hfetch" as "Hprog_done". 
    (* jnz r_t1 r *)
    iPrologue "Hprog".
    iApply (wp_jnz_success_jmp with "[$HPC $Hi $Hr_t1 $Hr]");
      [apply decode_encode_instrW_inv|iCorrectPC link a_last|simpl;revert Hfailure;clear;intros Hne Hcontr;simplify_eq;lia|..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr)"; iSimpl in "HPC"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    iCombine "Hprog" "Hprog_done" as "Hprog_done".
    (* FAILURE SUBROUTINE *)
    iDestruct (big_sepL2_length with "Hprog'") as %Hlength'. 
    destruct a';[inversion Hlength'|].
    apply contiguous_between_cons_inv_first in Hcont' as Heq. subst a1.
    (* move r_t1 PC *)
    destruct a';[inversion Hlength'|].
    iAssert (⌜r_t1 ≠ PC⌝)%I as %Hne. 
    { iIntros (Hcontr). rewrite Hcontr. iDestruct (regname_dupl_false with "Hr_t1 HPC") as "H". done. }
    iPrologue "Hprog'".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC f_a_first f_a_last|iContiguous_next Hcont' 0|auto|..].
    iEpilogue "(HPC & Hi & Hr_t1)". iRename "Hi" into "Hprog_done'". 
    (* lea r_t1 5 *)
    destruct a';[inversion Hlength'|].
    iPrologue "Hprog'".
    assert ((f_a_first + 6)%a = Some a_env) as Hlea.
    { simpl in Henv. inversion Hlength' as [Heq]. rewrite Heq in Henv. auto. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC f_a_first f_a_last|iContiguous_next Hcont' 1|apply Hlea|auto..].
    { simpl; auto. }
    iEpilogue "(HPC & Hi & Hr_t1)". iCombine "Hi" "Hprog_done'" as "Hprog_done'".
    (* load r_t1 r_t1 *)
    destruct a';[inversion Hlength'|].
    iPrologue "Hprog'".
    iAssert (⌜(a_env =? a2)%a = false⌝)%I as %Hne'.
    { destruct (decide (a_env = a2)%Z); [subst|iPureIntro;apply Z.eqb_neq,neq_z_of;auto].
      iDestruct (addr_dupl_false with "Hi Ha_env") as "H";auto. }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_t1 Ha_env]");
      [|apply decode_encode_instrW_inv|iCorrectPC f_a_first f_a_last|auto| |iContiguous_next Hcont' 2|
       rewrite Hne';iFrame|rewrite Hne'];auto. 
    iEpilogue "(HPC & Hr_t1 & Hi & Ha_env)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* store r_t1 1 *)
    destruct a';[inversion Hlength'|].
    iPrologue "Hprog'".
    iApply (wp_store_success_z with "[$HPC $Hi $Hr_t1 $Hflag]");
      [apply decode_encode_instrW_inv|iCorrectPC f_a_first f_a_last|iContiguous_next Hcont' 3|
       split;auto|].
    iEpilogue "(HPC & Hi & Hr_t1 & Hflag)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t1 0 *)
    destruct a';[inversion Hlength'|].
    iPrologue "Hprog'".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC f_a_first f_a_last|iContiguous_next Hcont' 4|auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* Halt *)
    destruct a';[|inversion Hlength'].
    apply contiguous_between_last with (ai:=a5) in Hcont' as Hlink';[|auto].
    iPrologue "Hprog'".
    iApply (wp_fail with "[$HPC $Hi]");
      [apply decode_encode_instrW_inv|iCorrectPC f_a_first f_a_last|].
    iEpilogue "(HPC & Hi)".
    iApply wp_value. iApply "Hφ".
    iFrame. iSplitL "Hr".
    { simpl. iExists _. iFrame. iPureIntro. revert Hfailure. clear. lia. }
    assert ((f_a_last + (-1))%a = Some a5) as ->;[|simpl].
    { eapply contiguous_between_last in Hcont';[|eauto]. revert Hlink' Hcont'. clear. solve_addr. }
    iFrame. rewrite Heqapp. iDestruct "Hprog_done'" as "(?&?)". iDestruct "Hprog_done" as "(?&?&?&?&?&?&?)".
    iFrame.
  Qed.


End stack_macros.
