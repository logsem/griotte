From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel stack_macros_helpers push_pop rclear.
From cap_machine.rules Require Import rules_StoreU_derived rules_LoadU_derived rules_PromoteU_derived.

Section scall.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MP: MachineParameters}.

  (* Macro for stack calling when the stack capability is uninitialized.
     Note that the prologue and epilogue does not include storing and loading
     private state on the stack. *)

  (* helper lemma for the length of the registers *)
  Ltac iRegNotEq Hne :=
    repeat (apply not_elem_of_cons in Hne;
            (let Hneq := fresh "Hneq" in destruct Hne as [Hneq Hne])); auto.

  Definition scallU_prologue_instrs r1 params :=
    (* push activation code *)
    [pushU_z_instr r_stk w_1;
    pushU_z_instr r_stk w_2_U;
    pushU_z_instr r_stk w_3;
    pushU_z_instr r_stk w_4a;
    pushU_z_instr r_stk w_4b_U; (* Note that there is one fewer instruction here than in the non-initialized case, cause we store with an offset *)
    (* push old pc *)
    move_r r_t1 PC;
    lea_z r_t1 (length (list_difference all_registers (params ++ [PC;r_stk;r_t0;r1])) + 11 + (2 + (2 * length (params))))%nat;
    pushU_r_instr r_stk r_t1;
    (* push stack pointer *)
    pushU_r_instr r_stk r_stk; (* Note that the stored r_stk will not be able to read itself, but that should not be a problem. *)
    (* set up protected return pointer *)
    (* since a URWLX capability cannot be made into an E, we have to promote r_t0 first *)
    move_r r_t0 r_stk;
    promoteU r_t0;
    lea_z r_t0 (-7)%Z;
    restrict_z r_t0 (monotone_e);
    (* restrict stack capability *)
    geta r_t1 r_stk;
    gete r_t2 r_stk;
    subseg_r_r r_stk r_t1 r_t2] ++
    (* don't clear the unused part of the stack - just clear the registers *)
    rclear_instrs (list_difference all_registers (params ++ [PC;r_stk;r_t0;r1])).

  Definition scallU_prologue (a : list Addr) r1 params :=
    ([∗ list] a_i;w_i ∈ a;(scallU_prologue_instrs r1 params), a_i ↦ₐ w_i)%I.

  Lemma single_instr_extract a i j instr prog :
    contiguous_between a i j →
    ([∗ list] a_i;w_i ∈ a; (instr :: prog), a_i ↦ₐ w_i) -∗
    ∃ a' a_rest,
      (( i ↦ₐ instr) ∗
       [∗ list] a_i;w_i ∈ a'; prog, a_i ↦ₐ w_i) ∗
       ⌜ a = i :: a'
         ∧ (i + 1 = Some a_rest)%a
         ∧ contiguous_between a' a_rest j ⌝.
  Proof.
    intros. iIntros "HH".
    iDestruct (big_sepL2_length with "HH") as %Hlength.
    destruct a; [ by inversion Hlength |].
    rewrite big_sepL2_cons.
    set (H' := H). apply contiguous_between_cons_inv_first in H'; subst i.
    apply contiguous_between_cons_inv in H as (_ & (a' & (Hpp & H))).
    iExists a0, a'; auto.
  Qed.

  Ltac iPush_z prog :=
    let cont := fresh "cont" in
    let a_rest := fresh "a_rest" in
    let Ha1 := fresh "Ha1" in
    let Ha := fresh "Ha" in
    iDestruct (single_instr_extract with prog) as (a_rest cont)
      "((Hpush & Hprog) & #Hcont)"; eauto;
    iDestruct "Hcont" as %(-> & Ha1 & Ha);
    iApply (pushU_z_spec with "[-]"); last iFrame "Hpush HPC Hr_stk Ha"; eauto;
    clear Ha1; last iRename "Hprog" into prog.

  Ltac iContiguous_bounds i j :=
    eapply contiguous_between_middle_bounds' with (a0 := i) (an := j);
    [ eauto | cbn; solve [ repeat constructor ] ].
  Ltac iContiguous_bounds_withinBounds a0 an :=
    apply isWithinBounds_bounds_alt' with a0 an; auto; [];
    iContiguous_bounds a0 an.

  Ltac iEpilogue_combine ptrn instr prog :=
    iEpilogue ptrn;iCombine instr prog as prog.

  Lemma rclear_length l :
    length (rclear_instrs l) = length l.
  Proof. induction l;auto. simpl. rewrite IHl. done. Qed.

  Lemma scallU_prologue_spec
        (* adress arithmetic *) a_r_adv b_r_adv a_cont a_next
        (* scall parameters *) a a_first r1
        (* program counter *) p g b e
        (* stack capability *) b_r e_r a_r
        (* continuation *) φ
        (* register contents *) rmap
        (* local stack *) ws_own
        (* function parameters *) params :

    isCorrectPC_range p g b e a_first a_cont →
    withinBounds ((URWLX, Local), b_r, e_r, a_r) = true ->
    withinBounds ((URWLX, Local), b_r, e_r, b_r_adv) = true →
    contiguous_between a a_first a_cont →
    isDirected g = false →
    r1 ∉ [PC;r_stk;r_t0;r_t1;r_t2;r_t3;r_t4;r_t5;r_t6] → (* the jump destination will not be overwritten/cleared *)
    params ## [PC;r_stk;r_t0;r_t1; r_t2; r_t3; r_t4; r_t5; r_t6] → (* the parameters will not be overwritten/cleared *)
    dom (gset RegName) rmap = all_registers_s ∖ {[ PC; r_stk; r1; r_t0]} ∖ (list_to_set params) →

    (a_r + 6)%a = Some a_r_adv →
    (a_r + 7)%a = Some b_r_adv →
    (a_cont + (2 + (2 * length (params))))%a = Some a_next →

    (▷ scallU_prologue a r1 params
   ∗ ▷ PC ↦ᵣ inr ((p,g),b,e,a_first)
   ∗ ▷ r_stk ↦ᵣ inr ((URWLX,Directed),b_r,e_r,a_r)
   ∗ ▷ (∃ w, r_t0 ↦ᵣ w)
   ∗ ▷ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
   ∗ ▷ ([[a_r, b_r_adv]]↦ₐ[[ws_own]]) (* local stack - note that the perm here is NOT unitialized,
                                               as the definition of interp1 has a promote_permission in there *)
   (* No ownership of adversarial stack here; no clearing required *)
   ∗ ▷ (PC ↦ᵣ inr (p,g,b,e,a_cont)
            ∗ r_stk ↦ᵣ inr ((URWLX,Directed),b_r_adv,e_r,b_r_adv)
            ∗ r_t0 ↦ᵣ inr ((E,Directed),b_r,b_r_adv,a_r) (* Note that this capbility does not grant permissions up to the end of the stack anymore *)
            ∗ (∃ rmap', ⌜dom (gset RegName) rmap = dom (gset RegName) rmap' ∧ ∀ r w, rmap' !! r = Some w → w = inl 0%Z⌝
                                                    ∗ [∗ map] r_i↦w_i ∈ rmap', r_i ↦ᵣ w_i)
            ∗ [[ a_r, b_r_adv ]]↦ₐ[[ [inl w_1;
                                             inl w_2_U;
                                             inl w_3;
                                             inl w_4a;
                                             inl w_4b_U;
                                             inr (p,g,b,e,a_next);
                                             inr (URWLX,Directed,b_r,e_r,a_r_adv)] ]] (* local stack *)
            ∗ scallU_prologue a r1 params -∗
            WP Seq (Instr Executable) {{ φ }})
   ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc1 Hwb1 Hwb2 Ha Hmono Hne Hdisj Hrmap Hadva Hadvb Hcont)
            "(>Hprog & >HPC & >Hr_stk & >Hr_t0 & >Hregs & >Hgen_reg & Hφ)".
    assert (withinBounds ((RWLX, Local), b_r, e_r, a_r_adv) = true) as Hwb3.
    { apply andb_true_iff.
      apply andb_true_iff in Hwb2 as [Hba Hae]. apply andb_true_iff in Hwb1 as [Hbact Hacte].
      revert Hae Hba Hbact Hacte; repeat rewrite Z.leb_le Z.ltb_lt; intros Hae Hba Hbact Hacte.
      assert (a_r_adv ≤ b_r_adv)%Z as Hle;[apply incr_addr_le with a_r 6 7;auto;lia|].
      assert (a_r ≤ a_r_adv)%Z as Hle';[apply next_le_i with 6;auto;lia|]. lia.
    }
    assert (Hin_rmap: ∀ r, r ∈ [r_t1; r_t2; r_t3; r_t4; r_t5; r_t6] → is_Some (rmap !! r)).
    { intros r Hr. rewrite elem_of_gmap_dom Hrmap !elem_of_difference.
      split; [split;[apply all_registers_s_correct|]|]. rewrite !not_elem_of_union !not_elem_of_singleton.
      rewrite !elem_of_cons elem_of_nil in Hr |- * => Hr. repeat split; try naive_solver.
      intros <-. apply Hne. rewrite !elem_of_cons elem_of_nil. repeat destruct Hr as [|Hr]; tauto.
      intros Hin%elem_of_list_to_set. apply Hdisj in Hin. apply Hin. do 3 constructor. auto.
    }

    iDestruct (big_sepL2_length with "Hgen_reg") as %Hlength'.
    assert ((a_r <= b_r_adv)%a) as Hle_stack;[clear -Hadva Hadvb;solve_addr|].
    pose proof (contiguous_between_region_addrs a_r b_r_adv Hle_stack) as Hcontiguous.
    set l:=region_addrs a_r b_r_adv. rewrite -/l in Hcontiguous,Hlength'. rewrite -/l.
    assert (length l = 7) as Hllen.
    { rewrite /l region_addrs_length /region_size. clear -Hadvb Hadva;solve_addr. }
    rewrite /region_mapsto -/l.
    destruct_addr_list l.

    (* The following length assumptions will let us destruct the stack/program *)
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.
    apply contiguous_between_cons_inv_first in Hcontiguous as Heq. subst l.
    (* PUSH ACTIVATION RECORD *)
    (* push w_1 *)
    destruct ws_own as [|w ws_own];[inversion Hlength'|]; iDestruct "Hgen_reg" as "[Ha Hstack_own]".
    iPush_z "Hprog"; [| iContiguous_next Hcontiguous 0|].
    { iCorrectPC a_first a_cont. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iRename "Hpush" into "Hi". iRename "Ha" into "Hw1".
    (* push w_2_U *)
    destruct ws_own as [|w1 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog"; [| |iContiguous_next Hcontiguous 1|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hw1" as "Hact_frame".
    (* push w_3 *)
    destruct ws_own as [|w2 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 2|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    (* push w_4a *)
    destruct ws_own as [|w3 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 3|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    (* push w_4b_U *)
    destruct ws_own as [|w4 ws_own];[inversion Hlength'|]; iDestruct "Hstack_own" as "[Ha Hstack_own]".
    iPush_z "Hprog";[| |iContiguous_next Hcontiguous 4|].
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    iNext. iIntros "(HPC & Hpush & Hr_stk & Ha)".
    iCombine "Hpush" "Hi" as "Hi". iCombine "Ha" "Hact_frame" as "Hact_frame".
    clear Ha4 Ha3 Ha0.
    (* PUSH OLD PC *)
    (* some general purpose registers *)
    iDestruct "Hr_t0" as (w0) "Hr_t0".
    assert (is_Some (rmap !! r_t1)) as [rv1 ?] by (apply Hin_rmap; repeat constructor).
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hrt1 Hregs]";[eauto|].
    (* move r_t1 PC *)
    do 2 (destruct a_rest; [inversion Hlength|]).
    match goal with H: contiguous_between (?a' :: _) ?a _ |- _ =>
      generalize (contiguous_between_cons_inv_first _ a a' _ H); intro; subst a end.
    iDestruct "Hprog" as "[Hinstr Hprog]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_move_success_reg_fromPC with "[$Hinstr $Hrt1 $HPC]");
      [apply decode_encode_instrW_inv| |iContiguous_next Ha 5|].
    { iCorrectPC a_first a_cont. }
    iEpilogue_combine "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hi".
    (* lea r_t1 epilogue_off *)
    iRename "Hi" into "Hpushes".
    destruct a_rest; [inversion Hlength|].
    iPrologue "Hprog".
    (* we first need to make some assertions about the increase of the address a *)
    assert ((a + (length (list_difference all_registers (params ++ [PC;r_stk;r_t0;r1])) + 11)%nat)%a = Some a_cont) as Hepilogue.
    { apply contiguous_between_middle_to_end with (i:=5) (ai:=a)
            (k:=(length (list_difference all_registers (params ++ [PC; r_stk; r_t0; r1])) + 11)%nat) in Ha;eauto.
      rewrite Hlength. rewrite /scallU_prologue_instrs. rewrite app_length rclear_length.
      set v := (length (list_difference all_registers (params ++ [PC; r_stk; r_t0; r1]))). simpl.
      clear. lia. }
    assert (a + (length (list_difference all_registers (params ++ [PC; r_stk; r_t0; r1])) + 11 +
                 (2 + 2* length params))%nat = Some a_next)%a as Hepilogue'.
    { clear -Hepilogue Hcont. revert Hepilogue.
      set (l := (length (list_difference all_registers (params ++ [PC; r_stk; r_t0; r1])) + 11)%nat).
      intros Hl. pose proof (incr_addr_trans a a_cont a_next l (2 + 2 * length params)%Z Hl Hcont).
      rewrite -H. f_equiv. lia. }
    iApply (wp_lea_success_z with "[$Hi $Hr_t1 $HPC]");
      [apply decode_encode_instrW_inv| |iContiguous_next Ha 6|apply Hepilogue'|auto|..].
    { iCorrectPC a_first a_cont. }
    { eapply isCorrectPC_range_npE; eauto. iContiguous_bounds a_first a_cont. }
    { apply contiguous_between_length in Ha.
      apply isCorrectPC_range_perm in Hvpc1; [|revert Ha; clear; solve_addr].
      destruct Hvpc1 as [-> | [-> | ->] ]; auto. }
    iEpilogue "(HPC & Hprog_done & Hr_t1)".
    (* PUSH R_T1 *)
    (* pushU r_stk r_t1 *)
    destruct ws_own;[inversion Hlength'|].
    destruct a_rest; [inversion Hlength|].
    iDestruct "Hstack_own" as "[Ha6 Hstk_own]".
    iDestruct "Hprog" as "[Hi Hprog]".
    iApply (pushU_r_spec with "[-]"); last iFrame "Hi Ha6 HPC Hr_stk Hr_t1"; eauto.
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    { iContiguous_next Ha 7. }
    { iContiguous_next Hcontiguous 5. }
    { intros Hmono'. destruct g;inversion Hmono;inversion Hmono'. }
    iNext. iIntros "(HPC & Hinstr & Hr_stk & Hr_t1 & Ha6)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
    iCombine "Ha6" "Hact_frame" as "Hact_frame".
    (* STORE OLD SP *)
    (* pushU r_stk r_stk *)
    destruct ws_own;[inversion Hlength'|].
    destruct a_rest; [inversion Hlength|].
    iDestruct "Hstk_own" as "[Ha7 Hstk_own]".
    iDestruct "Hprog" as "[Hi Hprog]".
    iApply (pushU_r_spec_same with "[-]"); last iFrame "Hi Ha7 HPC Hr_stk"; eauto.
    { iCorrectPC a_first a_cont. }
    { iContiguous_bounds_withinBounds a_r b_r_adv. }
    { iContiguous_next Ha 8. }
    { eapply contiguous_between_last. exact Hcontiguous. auto. }
    iNext. iIntros "(HPC & Hinstr & Hr_stk & Ha7)". iCombine "Hinstr" "Hprog_done" as "Hprog_done".
    iCombine "Ha7" "Hact_frame" as "Hact_frame".
    (* PREPARE RETURN CAP *)
    (* move r_t0 r_stk *)
    destruct a_rest; [inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_t0 $Hr_stk]");
      [apply decode_encode_instrW_inv| |iContiguous_next Ha 9|].
    { iCorrectPC a_first a_cont. }
    iEpilogue_combine "(HPC & Hinstr & Hr_t0 & Hr_stk)" "Hinstr" "Hprog_done".
    (* promoteU r_t0 *)
    destruct a_rest; [inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_promoteU_success with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv| |auto |iContiguous_next Ha 10|].
    { iCorrectPC a_first a_cont. }
    iEpilogue_combine "(HPC & Hinstr & Hr_t0)" "Hinstr" "Hprog_done".
    assert ((addr_reg.min b_r_adv e_r) = b_r_adv) as ->.
    { apply withinBounds_le_addr in Hwb2 as [_ Hlt].
      unfold addr_reg.min. destruct (Addr_le_dec b_r_adv e_r); auto. destruct n.
      apply Z.lt_le_incl; auto.
    }
    (* lea r_t0 -7 *)
    (* assert that the activation frame starts at a_r *)
    destruct a_rest; [inversion Hlength|].
    iPrologue "Hprog".
    generalize (contiguous_between_last _ _ _ _ Hcontiguous eq_refl).
    match goal with |- (?a + _)%a = _ -> _ =>
      intro HH; assert (a = a_r_adv); [ revert HH Hadva Hadvb; clear; solve_addr |];
      subst a end.
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv| |iContiguous_next Ha 11| |auto..].
    { iCorrectPC a_first a_cont. }
    { eapply invert_incr_addr in Hadvb. done.  }
    { by cbn. }
    iEpilogue_combine "(HPC & Hinstr & Hr_t0)" "Hinstr" "Hprog_done".
    (* restrict r_t0 (Local,E) *)
    destruct a_rest; [inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_restrict_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv| |iContiguous_next Ha 12| |auto|auto|].
    { iCorrectPC a_first a_cont. }
    { rewrite decode_encode_permPair_inv. auto. }
    iEpilogue_combine "(HPC & Hinstr & Hr_t0)" "Hinstr" "Hprog_done".
    (* RESTRICT STACK CAP *)
    (* geta r_t1 r_stk *)
    destruct a_rest; [inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi Hr_t1 Hr_stk]");
      [apply decode_encode_instrW_inv|eauto| |iContiguous_next Ha 13|iSimpl|]; eauto.
    { iCorrectPC a_first a_cont. } { iFrame. }
    iEpilogue_combine "(HPC & Hinstr & Hr_stk & Hr_t1)" "Hinstr" "Hprog_done".
    (* gete r_t2 r_stk *)
    assert (is_Some (rmap !! r_t2)) as [rv2 ?] by (apply Hin_rmap; repeat constructor).
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]".
      by rewrite !lookup_delete_ne //.
    destruct a_rest; [inversion Hlength|].
    iPrologue "Hprog".
    iApply (wp_Get_success with "[$HPC $Hi Hr_t2 Hr_stk]");
      [apply decode_encode_instrW_inv| eauto |  |iContiguous_next Ha 14|iSimpl|]; eauto.
    { iCorrectPC a_first a_cont. } { iFrame. }
    iEpilogue_combine "(HPC & Hinstr & Hr_stk & Hr_t2)" "Hinstr" "Hprog_done".
    (* subseg r_stk r_t1 r_t2 *)
    assert (z_to_addr b_r_adv = Some b_r_adv) as Hb_r_adv.
    { destruct b_r_adv; rewrite /z_to_addr /=. destruct (Z_le_dec z MemNum); [|elim n; eapply Z.leb_le; auto].
      destruct (Z_le_dec 0 z); [|elim n; eapply Z.leb_le; auto].
      f_equal; by apply z_of_eq. }
    assert (z_to_addr e_r = Some e_r) as He_r.
    { destruct e_r; rewrite /z_to_addr /=. destruct (Z_le_dec z MemNum); [|elim n; eapply Z.leb_le; auto].
      destruct (Z_le_dec 0 z); [|elim n; eapply Z.leb_le; auto].
      f_equal; by apply z_of_eq. }

    (* Annoying exception here: the Prologue does not resolve automatically, as the length definition
       does not get unfolded automatically, which is in turn caused by the fact that coq cannot derive
       that the map over the list of registers that need to be cleared at the end is not empty. ->
       inversion on Hlength does not work *)
    iDestruct (contiguous_between_program_split with "[Hprog]") as (subseg_addrs rclear_addrs rclear_first) "(Hmclear & Hrclear & #Hcont)".
    { eapply contiguous_between_app with (k := a14)(a2 := (a14 :: a_rest)) in Ha as [_ Ha]. exact Ha.
      * simpl. do 15 (instantiate (1:= cons _ _)). instantiate (1 := []). simpl; eauto.
      * cbn.  eapply (contiguous_between_incr_addr _ 15); eauto.
    }
    { instantiate(2:= [_]). unfold app; auto. }
    iDestruct "Hcont" as %(Hcont21 & Hcont22 & Happeq' & Hlink').
    assert (a14 <= rclear_first)%a as Harcl. by eapply contiguous_between_bounds;eauto.
    destruct subseg_addrs.
    { inversion Hcont21. rewrite H3 in Hlink'. cbn in Hlink'. destruct rclear_first. unfold incr_addr in Hlink'. simpl in Hlink'.
      destruct (Z_le_dec (z + 1%nat)%Z MemNum); last by inversion Hlink'. inversion Hlink'. done. }
    apply contiguous_between_cons_inv_first in Hcont21; subst a15.

    iDestruct (big_sepL2_length with "Hmclear") as %Hlen.
    destruct subseg_addrs. 2: {cbn in Hlen. discriminate. } clear Hlen.

    iDestruct "Hmclear" as "[Hinstr _]".
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_subseg_success with "[$HPC $Hinstr $Hr_stk $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv| |eauto|auto|auto|..].
    { iCorrectPC a_first a_cont. }
    { rewrite !andb_true_iff !Z.leb_le. repeat split; try lia.
      eapply withinBounds_le_addr; eauto. }
    { exact Hlink'. }
    iEpilogue_combine "(HPC & Hinstr & Hr_t1 & Hr_t2 & Hr_stk)" "Hinstr" "Hprog_done".

    (* RCLEAR *)
    iDestruct (big_sepL2_length with "Hrclear") as %Hrclear_length.
    rewrite rclear_length in Hrclear_length. rewrite list_difference_app in Hrclear_length.
    rewrite list_difference_app.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs".
      repeat (rewrite lookup_delete_ne //;[]); apply lookup_delete.
      repeat (rewrite -delete_insert_ne //;[]); rewrite insert_delete.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs".
      repeat (rewrite lookup_delete_ne //;[]); apply lookup_delete.
      repeat (rewrite -delete_insert_ne //;[]); rewrite insert_delete.
    assert (r_t1 ∈ list_difference (list_difference all_registers params) [PC; r_stk; r_t0; r1]) as Hin_test.
    { apply elem_of_list_difference. split;[|clear -Hne;set_solver].
      apply elem_of_list_difference. split;[|clear -Hdisj;set_solver].
      apply all_registers_correct. }
    iApply (rclear_spec with "[- $Hregs]"); last (iFrame "HPC Hrclear").
    { eauto. }
    { apply not_elem_of_list; apply elem_of_cons; by left. }
    { destruct rclear_addrs; inversion Hcont22; eauto.
      destruct (list_difference (list_difference all_registers params) [PC; r_stk; r_t0; r1]);inversion Hrclear_length.
      inversion Hin_test. }
    { intros a' [Ha'1 Ha'2]. eapply Hvpc1. split; [| by auto].
      have: (a_first <= a14)%a by iContiguous_bounds a_first a_cont.
      have: (a14 <= rclear_first)%a by auto.
      revert Ha'1; clear; solve_addr. }
    { rewrite !dom_insert_L !list_to_set_difference -/all_registers_s.
      rewrite Hrmap !difference_difference_L !singleton_union_difference_L
              !all_registers_union_l.
      f_equal. clear -Hne Hdisj. set_solver. }
    iNext. iIntros "(HPC & Hregs & Hrclear)".
    iApply "Hφ". rewrite decode_encode_permPair_inv. iFrame "HPC Hr_stk Hr_t0".
    iSplitL "Hregs".
    { iExists (create_gmap_default (elements (dom (gset RegName) rmap)) (inl 0%Z)).
      iSplit;[iPureIntro|].
      - rewrite Hrmap create_gmap_default_dom. split;[clear;set_solver|].
        intros r w' Hin. apply create_gmap_default_lookup_is_Some in Hin as [? ->]. auto.
      - iApply big_sepM_to_create_gmap_default; last iFrame "Hregs".
        rewrite /= !dom_insert_L. clear -Hin_rmap.
        assert (r_t2 ∈ dom (gset RegName) rmap) as Hin2.
        { apply elem_of_gmap_dom. apply Hin_rmap. repeat constructor. }
        assert (r_t1 ∈ dom (gset RegName) rmap) as Hin1.
        { apply elem_of_gmap_dom. apply Hin_rmap. repeat constructor. }
        set_solver.
    }
    iSplitL "Hact_frame".
    { iDestruct "Hact_frame" as "(?&?&?&?&?&?&?)". by iFrame. }
    { rewrite Happeq'. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$&?)".
      iDestruct "Hpushes" as "($&$&$&$&$&$)".
      iFrame. rewrite -list_difference_app. iFrame. }
    Unshelve. apply _.
  Qed.

  Lemma scallU_epilogue_spec stack_own_b stack_own_e s_last rt1w rstkw
        (* reinstated PC *) pc_p pc_g pc_b pc_e pc_cont pc_next
        (* reinstated stack *) p_r g_r b_r e_r
        (* current PC *) p g φ :

    isCorrectPC_range p g b_r stack_own_e stack_own_b stack_own_e →
    withinBounds ((p_r, g_r), b_r, e_r, s_last) = true -> (* Extra hypothesis to anchor the value of s_last vs e_r,
                                                            when we load through the stack pointer -
                                                            TODO: this could be avoided by loading through the PC instead,
                                                            but I reused the legacy code for now *)
    isU p_r = true → (* Stack capability is uninitialized *)
    (pc_cont + 1)%a = Some pc_next ->
    (s_last + 1)%a = Some stack_own_e ->
    isCorrectPC (inr (pc_p, pc_g, pc_b, pc_e, pc_next)) ->

    (▷ PC ↦ᵣ inr (p, g, b_r, stack_own_e, stack_own_b) (* only permission up to adv frame, i.e. stack_own_e *)
       ∗ ▷ r_t1 ↦ᵣ rt1w
       ∗ ▷ r_stk ↦ᵣ rstkw
       ∗ ▷ ([[stack_own_b,stack_own_e]]↦ₐ[[
                [inl w_1; inl w_2_U; inl w_3; inl w_4a; inl w_4b_U;
                 inr (pc_p, pc_g, pc_b, pc_e, pc_cont);
                 inr (p_r, g_r, b_r, e_r, s_last)]
            ]]) (* activation frame *)
       ∗ ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, pc_next)
               ∗ r_stk ↦ᵣ inr (p_r, g_r, b_r, e_r, s_last)
               ∗ (∃ rt1w, r_t1 ↦ᵣ rt1w)
               ∗ [[stack_own_b,stack_own_e]]↦ₐ[[
                    [inl w_1; inl w_2_U; inl w_3; inl w_4a; inl w_4b_U;
                     inr (pc_p, pc_g, pc_b, pc_e, pc_cont);
                     inr (p_r, g_r, b_r, e_r, s_last)]
                 ]] (* activation frame *) -∗
               WP Seq (Instr Executable) {{ φ }})
       ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    iIntros (Hvpc Hwb HUstk Hstack1 Hstack2 HX) "(>HPC & >Hr_t1 & >Hr_stk & >Hframe & Hφ)".
    rewrite /region_mapsto.
    iDestruct (big_sepL2_length with "Hframe") as %Hframe_length.
    set (l := region_addrs stack_own_b stack_own_e) in *.
    simpl in Hframe_length.
    assert (contiguous_between l stack_own_b stack_own_e) as Hcont.
    { eapply contiguous_between_of_region_addrs; eauto.
      rewrite region_addrs_length /region_size // in Hframe_length. solve_addr. }
    assert (stack_own_b + 7 = Some stack_own_e)%a as Hstack_bounds.
    { generalize (contiguous_between_length _ _ _ Hcont). cbn. by rewrite Hframe_length. }

    destruct_addr_list l.
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont). subst l.
    (* move r_t1 PC *)
    iPrologue "Hframe".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 0|].
    { iCorrectPC stack_own_b stack_own_e. }
    iAssert (emp)%I as "-#Hframe_past";[done|].
    iEpilogue_combine "(HPC & Hi & Hr_t1)" "Hi" "Hframe_past".
    (* lea r_t1 6 *)
    iPrologue "Hframe".
    assert ((stack_own_b + 6)%a = Some s_last) as Hincr.
    { revert Hstack_bounds Hframe_length Hstack2; clear; solve_addr. }
    iApply (wp_lea_success_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv| |iContiguous_next Hcont 1|apply Hincr|auto|..].
    { iCorrectPC stack_own_b stack_own_e. }
    { eapply isCorrectPC_range_npE; eauto. iContiguous_bounds stack_own_b stack_own_e. }
    { apply contiguous_between_length in Hcont.
      apply isCorrectPC_range_perm in Hvpc; [|revert Hcont; clear; solve_addr].
      destruct Hvpc as [-> | [-> | ->] ]; auto. }
    iEpilogue_combine "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hframe_past".
    (* load r_stk r_t1 *)
    iPrologue "Hframe".
    iDestruct "Hframe" as "(Hinstr1 & Hinstr2 & Hinstr3 & Hlast & _)".
    (* fixme: tedious *)
    assert (a4 = s_last) as ->.
    { generalize (contiguous_between_last _ _ _ _ Hcont eq_refl).
      revert Hstack2; clear; solve_addr. }
    (* assert (a3 = stack_new) as ->. *)
    (* { generalize (contiguous_between_incr_addr_middle _ _ _ 5 1 _ _ Hcont eq_refl eq_refl). *)
    (*   revert Hstack1 Hstack2; clear; solve_addr. } *)

    assert ((s_last =? a0)%a = false) as Hne.
    { assert ((a0 + 4)%a = Some s_last) as Hincr'.
      { pose proof (contiguous_between_last _ _ _ _ Hcont eq_refl) as HH5.
        eapply (contiguous_between_incr_addr_middle _ _ _ 2 4 _ _ Hcont); auto. }
      apply Z.eqb_neq. revert Hincr'; clear; solve_addr. }
    iApply (wp_load_success with "[$HPC $Hi $Hr_stk $Hr_t1 Hlast]").
    apply decode_encode_instrW_inv.
    iCorrectPC stack_own_b stack_own_e.
    { split.
      - unshelve epose proof (isCorrectPC_range_perm _ _ _ _ _ _ Hvpc _)
          as [ ? | [?|?] ]; [| destruct p; cbn; congruence ..].
        iContiguous_bounds stack_own_b stack_own_e.
      - eapply isCorrectPC_withinBounds. apply Hvpc.
        iContiguous_bounds stack_own_b stack_own_e. }
    { iContiguous_next Hcont 2. }
    rewrite Hne; iFrame.
    iEpilogue_combine "(HPC & Hr_stk & Hinstr & Hr_t1 & Hlast)" "Hinstr" "Hframe_past".
    (* sub r_t1 0 (2 + i) *)
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_add_sub_lt_success_z_z with "[$HPC Hr_t1 $Hinstr1]");
      [apply decode_encode_instrW_inv| | | | iFrame;eauto|..]; eauto.
    assert ((a1 + 1)%a = Some a2) as ->;[iContiguous_next Hcont 3|]. eauto.
    { iCorrectPC stack_own_b stack_own_e. }
    iEpilogue_combine "(HPC & Hinstr & Hr_t1)" "Hinstr" "Hframe_past".
    (* loadu PC r_stk r_t1 *)
    iApply (wp_bind (fill [SeqCtx])).
      rewrite Hne. simpl.
    iApply ( wp_loadU_success_reg_to_PC with "[$HPC $Hr_t1 $Hr_stk $Hinstr2 $Hinstr3]");
      [apply decode_encode_instrW_inv| | apply HUstk | | ..];eauto.
    { iCorrectPC stack_own_b stack_own_e. }
    { rewrite /withinBounds. rewrite /withinBounds in Hwb. rewrite andb_true_iff. apply andb_true_iff in Hwb as [Hle Hlt]. split.
      * assert ((stack_own_b + 5)%a = Some a3) as Hso.
        { apply contiguous_between_incr_addr with (i:=5) (ai:=a3) in Hcont;auto. }
        apply next_le_i in Hso; last done.
        assert (( b_r <=? stack_own_b)%a).
        { assert (isCorrectPC (inr (p, g, b_r, stack_own_e, stack_own_b))) as HPCownb. iCorrectPC stack_own_b stack_own_e.  eapply isCorrectPC_withinBounds in HPCownb. rewrite /withinBounds in HPCownb. apply andb_true_iff in HPCownb; destruct HPCownb as [Hr1 _]. auto. }
        unfold leb_addr in *. rewrite Z.leb_le. apply Is_true_eq_true in H. apply Z.leb_le in H. eapply Z.le_trans; eauto.
      * apply (contiguous_between_middle_bounds' _ a3) in Hcont;[|repeat constructor].
        revert Hlt Hle; rewrite !Z.ltb_lt !Z.leb_le =>Hlt Hle. solve_addr. }
    { iContiguous_next_a Hcont. }
    iEpilogue_combine "(HPC & Hinstr & Hr_stk & Hr_t1 & Hsn)" "Hinstr" "Hframe_past".
    iDestruct "Hframe_past" as "(Ha2 & Ha1 & Ha0 & Ha & Hstack_own_b & _)".
    iApply "Hφ". iFrame. eauto.
    Unshelve. all: auto.
  Qed.

End scall.
