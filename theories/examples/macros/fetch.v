From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers.

Section stack_macros.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          `{MP: MachineParameters}.


  (* --------------------------------------------------------------------------------- *)
  (* ------------------------------------- FETCH ------------------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Definition fetch_instrs (f : Z) :=
    [move_r r_t1 PC;
    getb r_t2 r_t1;
    geta r_t3 r_t1;
    sub_r_r r_t2 r_t2 r_t3;
    lea_r r_t1 r_t2;
    load_r r_t1 r_t1;
    lea_z r_t1 f;
    move_z r_t2 0;
    move_z r_t3 0;
    load_r r_t1 r_t1]. 

  Definition fetch f a : iProp Σ :=
    ([∗ list] a_i;w_i ∈ a;(fetch_instrs f), a_i ↦ₐ w_i)%I. 

  (* fetch spec *)
  Lemma fetch_spec f a pc_p pc_g pc_b pc_e a_first a_last b_link e_link a_link entry_a wentry φ w1 w2 w3:
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->
    contiguous_between a a_first a_last ->
    withinBounds (RW, Global, b_link, e_link, entry_a) = true ->
    (a_link + f)%a = Some entry_a ->

      ▷ fetch f a
    ∗ ▷ PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_first)
    ∗ ▷ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link)
    ∗ ▷ entry_a ↦ₐ wentry
    ∗ ▷ r_t1 ↦ᵣ w1
    ∗ ▷ r_t2 ↦ᵣ w2
    ∗ ▷ r_t3 ↦ᵣ w3
    (* if the capability is global, we want to be able to continue *)
    (* if w is not a global capability, we will fail, and must now show that Phi holds at failV *)
    ∗ ▷ (PC ↦ᵣ inr (pc_p,pc_g,pc_b,pc_e,a_last) ∗ fetch f a
            (* the newly allocated region *)
            ∗ r_t1 ↦ᵣ wentry ∗ r_t2 ↦ᵣ inl 0%Z ∗ r_t3 ↦ᵣ inl 0%Z
            ∗ pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link)
            ∗ entry_a ↦ₐ wentry
            -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢
      WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hvpc Hcont Hwb Hentry) "(>Hprog & >HPC & >Hpc_b & >Ha_entry & >Hr_t1 & >Hr_t2 & >Hr_t3 & Hφ)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    destruct a as [|a l];[inversion Hlength|].
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst.
    (* move r_t1 PC *)
    destruct l;[inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 0|auto|..].
    iEpilogue "(HPC & Hprog_done & Hr_t1)".
    (* getb r_t2 r_t1 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t2 $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 1|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* geta r_t3 r_t1 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t3 $Hr_t1]");
      [apply decode_encode_instrW_inv|auto|iCorrectPC a_first a_last|iContiguous_next Hcont 2|auto..].
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t3) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* sub r_t2 r_t2 r_t3 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_add_sub_lt_success_dst_r with "[$HPC $Hi $Hr_t3 $Hr_t2]");
      [apply decode_encode_instrW_inv|auto|iContiguous_next Hcont 3|iCorrectPC a_first a_last|..].
    iEpilogue "(HPC & Hi & Hr_t3 & Hr_t2) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* lea r_t1 r_t2 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    assert ((a_first + (pc_b - a_first))%a = Some pc_b) as Hlea;[solve_addr|]. 
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 4|apply Hlea|auto..].
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | [-> | ->] ]; auto. }
    { apply contiguous_between_length in Hcont.
      assert (a_first < a_last)%Z as Hlt;[simpl in Hcont;solve_addr|].
      apply isCorrectPC_inrange with (a:=a_first) in Hvpc;[|lia].
      destruct pc_p;auto;inversion Hvpc;solve_addr. }
    iEpilogue "(HPC & Hi & Hr_t2 & Hr_t1) /="; iCombine "Hi" "Hprog_done" as "Hprog_done". 
    (* load r_t1 r_t1 *)
    destruct l;[inversion Hlength|].
    assert (readAllowed pc_p = true) as Hra.
    { eapply pc_range_readA;eauto. }
    iPrologue "Hprog".
    iAssert (⌜(pc_b ≠ a3)%Z⌝)%I as %Hneq.
    { iIntros (Hcontr);subst.
      iDestruct (addr_dupl_false with "Hi Hpc_b") as %Hne; auto. }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_t1 Hpc_b]");
      [|apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto| |iContiguous_next Hcont 5|..].
    { exact (inr (RW, Global, b_link, e_link, a_link)). }
    { apply contiguous_between_length in Hcont as Hlen.
      assert (pc_b < pc_e)%Z as Hle.
      { eapply isCorrectPC_contiguous_range in Hvpc as Hwb';[|eauto|apply elem_of_cons;left;eauto].
        inversion Hwb'. solve_addr. }
      apply isCorrectPC_range_perm in Hvpc as Heq; [|revert Hlen; clear; solve_addr].
      apply andb_true_intro. split;[apply Z.leb_le;solve_addr|apply Z.ltb_lt;auto].
    }
    { destruct (pc_b =? a3)%a; [done|iFrame]. }
    destruct ((pc_b =? a3)%a) eqn:Hcontr;[apply Z.eqb_eq in Hcontr;apply z_of_eq in Hcontr;congruence|clear Hcontr]. 
    iEpilogue "(HPC & Hr_t1 & Hi & Hpc_b)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea r_t1 f *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 6|apply Hentry|simpl;auto..].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t2 0 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 7|auto|..].
    iEpilogue "(HPC & Hi & Hr_t2)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move r_t3 0 *)
    destruct l;[inversion Hlength|]. 
    iPrologue "Hprog".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t3]");
      [apply decode_encode_instrW_inv|iCorrectPC a_first a_last|iContiguous_next Hcont 8|auto|..].
    iEpilogue "(HPC & Hi & Hr_t3)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* load r_t1 r_t1 *)
    destruct l;[|inversion Hlength].
    apply contiguous_between_last with (ai:=a7) in Hcont as Hlink;[|auto]. 
    iPrologue "Hprog".
    iAssert (⌜(entry_a ≠ a7)%Z⌝)%I as %Hneq'.
    { iIntros (Hcontr);subst.
      iDestruct (addr_dupl_false with "Hi Ha_entry") as %Hne; auto. }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_t1 Ha_entry]");
      [exact wentry|apply decode_encode_instrW_inv|iCorrectPC a_first a_last|auto|auto|apply Hlink|..].
    { destruct (entry_a =? a7)%a; auto. }
    destruct ((entry_a =? a7)%a) eqn:Hcontr;[apply Z.eqb_eq in Hcontr;apply z_of_eq in Hcontr;congruence|clear Hcontr]. 
    iEpilogue "(HPC & Hr_t1 & Hi & Hentry_a)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* continuation *)
    iApply "Hφ".
    iFrame. 
    iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&$)".
  Qed.


End stack_macros.
