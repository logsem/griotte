From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static.
From cap_machine.examples Require Import region_macros macros
     awkward_example_helpers stack_object.
From stdpp Require Import countable.

Section stack_object_preamble.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* [offset_to_obj] is the offset between the [move_r r_t1 PC] instruction
  and the code of the awkward example *)
  Definition stack_object_preamble_instrs (offset_to_obj: Z) :=
    [move_r r_t1 PC;
    lea_z r_t1 offset_to_obj;
    restrict_z r_t1 global_e;
    jmp r_t0].

  Definition stack_object_preamble offset_to_lse ai :=
    ([∗ list] a_i;w_i ∈ ai;(stack_object_preamble_instrs offset_to_lse), a_i ↦ₐ w_i)%I.

  (* Compute the offset from the start of the program to the move_r r_t1 PC
     instruction. Will be used later to compute [offset_to_lse]. *)
  (* This is somewhat overengineered, but could be easily generalized to compute
     offsets for other programs if needed. *)
  Definition stack_object_preamble_instrs_length : Z :=
    Eval cbv in (length (stack_object_preamble_instrs 0)).
  Definition stack_object_preamble_move_offset : Z :=
    stack_object_preamble_instrs_length.

  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end.

  Definition objN : namespace := nroot .@ "objN".
  Definition obj_invN : namespace := objN .@ "inv".
  Definition obj_codeN : namespace := objN .@ "code".
  Definition obj_clsN : namespace := objN .@ "cls".
  Definition obj_env : namespace := objN .@ "env".

  Lemma stack_object_preamble_spec (f_m f_a offset_to_stack_object: Z) (r: Reg) W pc_p pc_b pc_e
        ai a_first a_end b_link e_link a_link a_entry'
        fail_cap ai_obj obj_first obj_end stack_obj :

    isCorrectPC_range pc_p Global pc_b pc_e a_first a_end →
    contiguous_between ai a_first a_end →
    withinBounds (RW, Global, b_link, e_link, a_entry') = true →
    (a_link + f_a)%a = Some a_entry' →
    (a_first + offset_to_stack_object)%a = Some obj_first →
    isCorrectPC_range pc_p Global pc_b pc_e obj_first obj_end →
    contiguous_between ai_obj obj_first obj_end →

    (* Code of the preamble *)
    stack_object_preamble offset_to_stack_object ai

    (* Code of the example itself *)
    ∗ stack_object_passing ai_obj stack_obj f_a

    (*** Resources for fail ***)
    (* assume that a pointer to the linking table (where the malloc capa is) is at offset 0 of PC *)
    ∗ pc_b ↦ₐ (inr (RO, Global, b_link, e_link, a_link))
    ∗ a_entry' ↦ₐ fail_cap

    -∗
    interp_expr interp r W (inr (pc_p, Global, pc_b, pc_e, a_first)).
  Proof.
    rewrite /interp_expr /=.
    iIntros (Hvpc Hcont Hwb_assert Ha_entry' Ha_lea Hvpc_awk Hcont_awk)
            "(Hprog & Hawk & Hpc_b & Ha_entry')
             ([#Hr_full #Hr_valid] & Hregs & Hr & Hsts & HnaI)".
    iDestruct "Hr_full" as %Hr_full.
    rewrite /full_map.
    iSplitR; auto. rewrite /interp_conf.

    (* put the code for the awkward example in an invariant *)
    iDestruct (na_inv_alloc logrel_nais _ obj_codeN with "Hawk") as ">#Hawk".

    rewrite /registers_mapsto.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]".
      by rewrite lookup_insert //. rewrite delete_insert_delete //.
    destruct (Hr_full r_t0) as [r0 Hr0].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr0 Hregs]". by rewrite !lookup_delete_ne//.
    destruct (Hr_full r_t1) as [r1 Hr1].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]". by rewrite !lookup_delete_ne//.
    pose proof (regmap_full_dom _ Hr_full) as Hdom_r.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.

    assert (pc_p ≠ E).
    { eapply isCorrectPC_range_npE. eapply Hvpc.
      pose proof (contiguous_between_length _ _ _ Hcont) as HH. rewrite Hlength /= in HH.
      revert HH; clear; solve_addr. }

    destruct_addr_list ai.
    apply contiguous_between_cons_inv_first in Hcont as Heq. subst ai.

    (* move r_t1 PC *)
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_first a_end|iContiguous_next_a Hcont|..].
    iEpilogue "(HPC & Hdone1 & Hr_t1)".
    (* lea r_t1 offset_to_stack_object *)
    iPrologue "Hprog".
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_first a_end|iContiguous_next_a Hcont|apply Ha_lea|auto|..].
    { destruct (isCorrectPC_range_perm _ _ _ _ _ _ Hvpc) as [-> | [-> | ->] ]; auto.
      generalize (contiguous_between_middle_bounds _ 3 a1 _ _ Hcont). simpl.
      intros Hres. destruct Hres as [? ?]. auto. solve_addr. }
    iEpilogue "(HPC & Hdone2 & Hr_t1)".
    (* restrict r_t1 global_e *)
    iPrologue "Hprog".
    iApply (wp_restrict_success_z with "[$HPC $Hi $Hr_t1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_first a_end|iContiguous_next_a Hcont|auto..].
    { rewrite decode_encode_permPair_inv.
      destruct (isCorrectPC_range_perm _ _ _ _ _ _ Hvpc) as [-> | [-> | ->] ]; auto.
      generalize (contiguous_between_middle_bounds _ 3 a1 _ _ Hcont). simpl.
      intros Hres. destruct Hres as [? ?]. auto. solve_addr. }
    iEpilogue "(HPC & Hdone3 & Hr_t1)".
    rewrite decode_encode_permPair_inv.

    assert (r_t0 ≠ PC) as Hne;auto.
    iDestruct ("Hr_valid" $! r_t0 Hne) as "#Hr0valid".
    rewrite /RegLocate Hr0.
    iDestruct (jmp_or_fail_spec with "Hr0valid") as "Hjmp".

    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";
      [rewrite lookup_delete//| rewrite insert_delete -!delete_insert_ne//].

    (* jmp r_t0 *)
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_first a_end|..].
    destruct (decide (isCorrectPC (updatePcPerm r0))).
    2: { iEpilogue "(HPC & Hdone4 & Hr_t0)". iApply "Hjmp". iFrame.
         iIntros (Hcontr). inversion Hcontr. }
    iDestruct "Hjmp" as (p g b e start Heq) "Hjmp". inv Heq.
    set (r' := <[PC:=inl 0%Z]> (<[r_t1:=inr (E, Global, pc_b, pc_e, obj_first)]> r)).
    iAssert (future_world g e W W) as "#Hfuture".
    { destruct g. all: iPureIntro. 1,2: apply related_sts_priv_refl_world.
      apply related_sts_a_refl_world. }
    iDestruct ("Hjmp" $! r' with "Hfuture") as "Hcont".
    iEpilogue "(HPC & Hdone4 & Hr_t1)".

    iDestruct (big_sepM_delete with "[$Hregs $Hr_t1]") as "Hregs".
    { rewrite lookup_delete_ne// lookup_insert_ne//. }
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
    { apply lookup_delete. } rewrite insert_delete -(insert_insert _ PC _ (inl 0%Z)).

    (* we allocate a non atomic invariant for the environment table *)
    iMod (na_inv_alloc logrel_nais _ obj_env
                       (pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link) ∗ a_entry' ↦ₐ fail_cap)%I
            with "[$Ha_entry' $Hpc_b]") as "#Henv".

    iDestruct ("Hcont" with "[$Hsts $Hr $HnaI $Hregs]") as "[_ Hwp]".
    { iSplit.
      - iPureIntro. intros x. rewrite /= /r'.
        destruct (decide (x = PC));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        destruct (decide (x = r_t1));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
      - iIntros (r0 Hne').
        iSpecialize ("Hr_valid" $! r0 Hne').
        rewrite /r' /RegLocate lookup_insert_ne//.
        destruct (decide (r0 = r_t1)).
        { subst. rewrite lookup_insert.
          iApply fixpoint_interp1_eq. iSimpl.
          iModIntro. iIntros (W' rr Hrelated). iNext.
          iSimpl. iIntros "([#Hr_full' #Hr_valid'] & Hregs & Hr & Hsts & HnaI)".
          iSplit;[auto|].
          iDestruct "Hr_full'" as %Hr_full'.

          destruct Hr_full' with r_stk as [wstk Hwstk].
          destruct Hr_full' with r_adv as [wadv Hwadv].
          iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]";
            [rewrite lookup_insert//|rewrite delete_insert_delete].
          iDestruct (big_sepM_delete _ _ r_stk with "Hregs") as "[Hr_stk Hregs]";
            [rewrite !lookup_delete_ne//|].
          iDestruct (big_sepM_delete _ _ r_adv with "Hregs") as "[Hr_adv Hregs]";
            [rewrite !lookup_delete_ne//|].
          iDestruct ("Hr_valid'" $! r_stk _) as "Hstack_valid". Unshelve. 2:auto.
          iDestruct ("Hr_valid'" $! r_adv _) as "Hadv_valid". Unshelve. 2:auto.
          rewrite /RegLocate Hwstk Hwadv.

          iApply (stack_object_spec with "[$Hr $Hsts $HnaI $HPC $Hr_stk $Hr_adv $Hregs $Hstack_valid
                                           $Hadv_valid $Hawk $Henv]");eauto.
          { intros mid Hmid. split;[|auto].
            apply Hvpc_awk in Hmid. inv Hmid;auto. }
          { rewrite !dom_delete_L. apply regmap_full_dom in Hr_full' as ->. clear. set_solver. }
          { solve_ndisj. }
          iNext. iIntros (v) "Hcond". iIntros (Hval).
          iDestruct ("Hcond" $! Hval) as (r0 W0) "(?&?&%&?&?&?)".
          iExists _,_. iFrame. iPureIntro. auto. }
        rewrite lookup_insert_ne//. }
    iSimpl in "Hwp".
    iFrame.
  Qed.

End stack_object_preamble.
