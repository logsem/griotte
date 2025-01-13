From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
Require Import Eqdep_dec.
From cap_machine Require Import
     rules logrel fundamental region_invariants
     region_invariants_revocation region_invariants_static.
From cap_machine.examples Require Import region_macros macros
     awkward_example_helpers downwards_lse.
From stdpp Require Import countable.

Section downwards_lse_preamble.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  (* [f_m] is the offset of the malloc capability *)
  (* [offset_to_awkward] is the offset between the [move_r r_t1 PC] instruction
  and the code of the awkward example *)
  Definition downwards_lse_preamble_instrs (f_m offset_to_lse: Z) :=
    malloc_instrs f_m 1%nat ++
    [store_z r_t1 2;
     move_r r_t2 r_t1;
     move_r r_t1 PC;
     lea_z r_t1 offset_to_lse] ++
    crtcls_instrs f_m ++
    [jmp r_t0].

  Definition downwards_lse_preamble f_m offset_to_lse ai :=
    ([∗ list] a_i;w_i ∈ ai;(downwards_lse_preamble_instrs f_m offset_to_lse), a_i ↦ₐ w_i)%I.

  (* Compute the offset from the start of the program to the move_r r_t1 PC
     instruction. Will be used later to compute [offset_to_lse]. *)
  (* This is somewhat overengineered, but could be easily generalized to compute
     offsets for other programs if needed. *)
  Definition downwards_lse_preamble_move_offset_ : Z.
  Proof.
    unshelve refine (let x := _ : Z in _). {
      set instrs := downwards_lse_preamble_instrs 0 0.
      assert (sig (λ l1, ∃ l2, instrs = l1 ++ l2)) as [l1 _]; [do 2 eexists | exact (length l1)].

      assert (forall A (l1 l2 l3 l4: list A), l2 = l3 ++ l4 → l1 ++ l2 = (l1 ++ l3) ++ l4) as step_app.
      { intros * ->. by rewrite app_assoc. }
      assert (forall A (l1 l2 l3: list A) x, l1 = l2 ++ l3 → x :: l1 = (x :: l2) ++ l3) as step_cons.
      { intros * ->. reflexivity. }
      assert (forall A (l1 l2: list A) x, x :: l1 = l2 → x :: l1 = l2) as prepare_cons.
      { auto. }
      assert (forall A (l: list A), l = [] ++ l) as stop.
      { reflexivity. }

      unfold instrs, downwards_lse_preamble_instrs.
      (* Program-specific part *)
      eapply step_app.
      repeat (eapply prepare_cons;
              lazymatch goal with
              | |- move_r r_t1 PC :: _ = _ => fail
              | _ => eapply step_cons end).
      eapply stop.
    }
    exact x.
  Defined.

  Definition downwards_lse_preamble_move_offset : Z :=
    Eval cbv in downwards_lse_preamble_move_offset_.

  Definition downwards_lse_preamble_instrs_length : Z :=
    Eval cbv in (length (downwards_lse_preamble_instrs 0 0)).

  Ltac middle_lt prev index :=
    match goal with
    | Ha_first : ?a !! 0 = Some ?a_first |- _
    => apply Z.lt_trans with prev; auto; apply incr_list_lt_succ with a index; auto
    end.

  Definition lseN : namespace := nroot .@ "lseN".
  Definition lse_invN : namespace := lseN .@ "inv".
  Definition lse_codeN : namespace := lseN .@ "code".
  Definition lse_clsN : namespace := lseN .@ "cls".
  Definition lse_env : namespace := lseN .@ "env".

  Lemma downwards_lse_preamble_spec (f_m f_a offset_to_downwards_lse: Z) (r: Reg) W pc_p pc_b pc_e
        ai a_first a_end b_link e_link a_link a_entry a_entry'
        mallocN b_m e_m fail_cap ai_lse lse_first lse_end a_move:

    isCorrectPC_range pc_p Global pc_b pc_e a_first a_end →
    contiguous_between ai a_first a_end →
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    withinBounds (RW, Global, b_link, e_link, a_entry') = true →
    (a_link + f_m)%a = Some a_entry →
    (a_link + f_a)%a = Some a_entry' →
    (a_first + downwards_lse_preamble_move_offset)%a = Some a_move →
    (a_move + offset_to_downwards_lse)%a = Some lse_first →
    isCorrectPC_range pc_p Global pc_b pc_e lse_first lse_end →
    contiguous_between ai_lse lse_first lse_end →

    (* Code of the preamble *)
    downwards_lse_preamble f_m offset_to_downwards_lse ai

    (* Code of the awkward example itself *)
    ∗ lse ai_lse f_a

    (*** Resources for malloc ***)
    (* assume that a pointer to the linking table (where the malloc capa is) is at offset 0 of PC *)
    ∗ na_inv logrel_nais mallocN (malloc_inv b_m e_m)
    ∗ pc_b ↦ₐ (inr (RO, Global, b_link, e_link, a_link))
    ∗ a_entry ↦ₐ (inr (E, Global, b_m, e_m, b_m))
    ∗ a_entry' ↦ₐ fail_cap

    -∗
    interp_expr interp r W (inr (pc_p, Global, pc_b, pc_e, a_first)).
  Proof.
    rewrite /interp_expr /=.
    iIntros (Hvpc Hcont Hwb_malloc Hwb_assert Ha_entry Ha_entry' Ha_lea H_awk_offset Hvpc_awk Hcont_awk)
            "(Hprog & Hawk & #Hinv_malloc & Hpc_b & Ha_entry & Ha_entry')
             ([#Hr_full #Hr_valid] & Hregs & Hr & Hsts & HnaI)".
    iDestruct "Hr_full" as %Hr_full.
    rewrite /full_map.
    iSplitR; auto. rewrite /interp_conf.

    (* put the code for the awkward example in an invariant *)
    iDestruct (na_inv_alloc logrel_nais _ lse_codeN with "Hawk") as ">#Hawk".

    rewrite /registers_mapsto.
    iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]".
      by rewrite lookup_insert //. rewrite delete_insert_delete //.
    destruct (Hr_full r_t0) as [r0 Hr0].
    iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr0 Hregs]". by rewrite !lookup_delete_ne//.
    pose proof (regmap_full_dom _ Hr_full) as Hdom_r.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength.

    assert (pc_p ≠ E).
    { eapply isCorrectPC_range_npE. eapply Hvpc.
      pose proof (contiguous_between_length _ _ _ Hcont) as HH. rewrite Hlength /= in HH.
      revert HH; clear; solve_addr. }

    (* malloc 1 *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_malloc ai_rest a_malloc_end) "(Hmalloc & Hprog & #Hcont)"; [apply Hcont|].
    iDestruct "Hcont" as %(Hcont_malloc & Hcont_rest & Heqapp & Hlink).
    iDestruct (big_sepL2_length with "Hmalloc") as %Hai_malloc_len.
    assert (isCorrectPC_range pc_p Global pc_b pc_e a_first a_malloc_end) as Hvpc1.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_rest). clear; solve_addr. }
    assert (isCorrectPC_range pc_p Global pc_b pc_e a_malloc_end a_end) as Hvpc2.
    { eapply isCorrectPC_range_restrict. apply Hvpc.
      generalize (contiguous_between_bounds _ _ _ Hcont_malloc). clear; solve_addr. }
    rewrite -/(malloc _ _ _ _).
    iApply (wp_wand with "[-]").
    iApply (malloc_spec with "[- $HPC $Hmalloc $Hpc_b $Ha_entry $Hr0 $Hregs $Hr $Hsts $Hinv_malloc $HnaI]");
      [apply Hvpc1|eapply Hcont_malloc|eapply Hwb_malloc|eapply Ha_entry| |auto|lia|..].
    { rewrite !dom_delete_L Hdom_r difference_difference_L //. }
    iNext. iIntros "(HPC & Hmalloc & Hpc_b & Ha_entry & HH & Hr0 & HnaI & Hregs & Hr & Hsts)".
    iDestruct "HH" as (b_cell e_cell Hbe_cell) "(Hr1 & Hcell)".
    iDestruct (region_mapsto_single with "Hcell") as (cellv) "(Hcell & _)". revert Hbe_cell; clear; solve_addr.
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest.
    2: { iIntros (?) "[HH | ->]". iApply "HH". iIntros (Hv). inversion Hv. }

    destruct ai_rest as [| a l]; [by inversion Hlength|].
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest) as ->.
    (* store_z r_t1 0 *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_store_success_z with "[$HPC $Hr1 $Hi $Hcell]");
      [apply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|
       iContiguous_next Hcont_rest 0|..].
    { split; auto. apply le_addr_withinBounds; revert Hbe_cell; clear; solve_addr. }
    iEpilogue "(HPC & Hprog_done & Hr1 & Hb_cell)". iCombine "Hprog_done" "Hmalloc" as "Hprog_done".
    (* move_r r_t2 r_t1 *)
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr2 Hregs]".
      by rewrite lookup_insert. rewrite delete_insert_delete.
    destruct l as [| a_move' l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg _ _ _ _ _ _ _ _ r_t2 _ r_t1 with "[$HPC $Hi $Hr1 $Hr2]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 1|..].
    iEpilogue "(HPC & Hi & Hr2 & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* move_r r_t1 PC *)
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_move_success_reg_fromPC with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 2|..].
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* lea_z r_t1 offset_to_awkward *)
    assert (a_move' = a_move) as ->.
    { assert ((a_first + (length ai_malloc + 2))%a = Some a_move') as HH.
      { rewrite Hai_malloc_len /= in Hlink |- *.
        generalize (contiguous_between_incr_addr_middle _ _ _ 0 2 _ _ Hcont_rest eq_refl eq_refl).
        revert Hlink; clear; solve_addr. }
      revert HH Ha_lea. rewrite Hai_malloc_len. cbn. clear.
      unfold downwards_lse_preamble_move_offset. solve_addr. }
    destruct l as [| ? l]; [by inversion Hlength_rest|].
    iPrologue "Hprog".
    iApply (wp_lea_success_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lse_first with "[$HPC $Hi $Hr1]");
      [eapply decode_encode_instrW_inv|iCorrectPC a_malloc_end a_end|iContiguous_next Hcont_rest 3
       |assumption|done|..].
    { destruct (isCorrectPC_range_perm _ _ _ _ _ _ Hvpc) as [-> | [-> | ->] ]; auto.
      generalize (contiguous_between_middle_bounds _ (length ai_malloc) a_malloc_end _ _ Hcont ltac:(subst ai; rewrite list_lookup_middle; auto)). clear. solve_addr. }
    iEpilogue "(HPC & Hi & Hr1)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    (* crtcls *)
    iDestruct (contiguous_between_program_split with "Hprog") as
        (ai_crtcls ai_rest a_crtcls_end) "(Hcrtcls & Hprog & #Hcont)".
    { epose proof (contiguous_between_incr_addr _ 4%nat _ _ _ Hcont_rest eq_refl).
      eapply contiguous_between_app with (a1:=[_;_;_;_]). 2: eapply Hcont_rest.
      all: eauto. }
    iDestruct "Hcont" as %(Hcont_crtcls & Hcont_rest' & Heqapp' & Hlink').
    assert (a_malloc_end <= a1)%a as Ha1_after_malloc.
    { eapply contiguous_between_middle_bounds'. apply Hcont_rest. repeat constructor. }
    iApply (wp_wand with "[-]").
    iApply (crtcls_spec with "[- $HPC $Hcrtcls $Hpc_b $Ha_entry $Hr0 $Hregs $Hr1 $Hr2 $Hr $Hsts $HnaI $Hinv_malloc]");
      [|apply Hcont_crtcls|apply Hwb_malloc|apply Ha_entry| |done|done|auto|..].
    { eapply isCorrectPC_range_restrict. apply Hvpc2. split; auto.
      eapply contiguous_between_bounds. apply Hcont_rest'. }
    { rewrite dom_delete_L !dom_insert_L !dom_delete_L Hdom_r.
      rewrite !difference_difference_L singleton_union_difference_L all_registers_union_l.
      rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
      f_equal. set_solver-. }
    2: { iIntros (?) "[ H | -> ]". iApply "H". iIntros (HC). congruence. }
    iNext. iIntros "(HPC & Hcrtcls & Hpc_b & Ha_entry & HH)".
    iDestruct "HH" as (b_cls e_cls Hbe_cls) "(Hr1 & Hbe_cls & Hr0 & Hr2 & HnaI & Hregs & Hr & Hsts)".
    iDestruct (big_sepL2_length with "Hprog") as %Hlength_rest'.
    iDestruct (na_inv_alloc logrel_nais _ lse_clsN with "Hbe_cls") as ">#Hcls_inv".
    (* in preparation of jumping, we allocate the new awkward invariant *)
    iDestruct (inv_alloc lseN _ (lse_inv b_cell) with "[Hb_cell]") as ">#Hawk_inv".
    { iNext. rewrite /lse_inv. iFrame. }
    (* we also allocate a non atomic invariant for the environment table *)
    iMod (na_inv_alloc logrel_nais _ lse_env
                       (pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link) ∗ a_entry' ↦ₐ fail_cap)%I
            with "[$Ha_entry' $Hpc_b]") as "#Henv".
    (* call the resulting world W2 *)
    match goal with |- context [ sts_full_world ?W ] => set W2 := W end.
    (* jmp *)
    destruct ai_rest as [| ? l']; [by inversion Hlength_rest'|].
    destruct l'; [|by inversion Hlength_rest'].
    iPrologue "Hprog".
    pose proof (contiguous_between_cons_inv_first _ _ _ _ Hcont_rest') as ->.
    iApply (wp_jmp_success with "[$HPC $Hi $Hr0]");
      [apply decode_encode_instrW_inv|..].
    { apply Hvpc2.
      generalize (contiguous_between_middle_bounds'
        _ a_crtcls_end _ _ Hcont_rest' ltac:(repeat constructor)).
      generalize (contiguous_between_bounds _ _ _ Hcont_rest').
      revert Ha1_after_malloc Hlink'. clear; solve_addr. }

    (* the current state of registers is valid *)
    iAssert (interp W2 (inr (E, Global, b_cls, e_cls, b_cls)))%I as "#Hvalid_cls".
    { rewrite /interp fixpoint_interp1_eq. iModIntro. rewrite /enter_cond.
      iIntros (r' W3 HW3) "". iNext. rewrite /interp_expr /=.
      iIntros "([Hr'_full #Hr'_valid] & Hregs' & Hr & Hsts & HnaI)". iDestruct "Hr'_full" as %Hr'_full.
      pose proof (regmap_full_dom _ Hr'_full) as Hdom_r'.
      iSplitR; [auto|]. rewrite /interp_conf.

      iDestruct (na_inv_acc with "Hcls_inv HnaI") as ">(>Hcls & Hna & Hcls_close)";
        [auto..|].

      rewrite /registers_mapsto.
      rewrite -insert_delete.
      iDestruct (big_sepM_insert with "Hregs'") as "[HPC Hregs']". by apply lookup_delete. 
      destruct (Hr'_full r_t1) as [r1v ?].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hregs'") as "[Hr1 Hregs']".
        by rewrite lookup_delete_ne //.
      destruct (Hr'_full r_env) as [renvv ?].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs'") as "[Hrenv Hregs']".
        by rewrite !lookup_delete_ne //.
      (* Run the closure activation code *)
      iApply (closure_activation_spec with "[- $HPC $Hr1 $Hrenv $Hcls]");
        [done| |done|..].
      { intros ? [? ?]. constructor; try split; auto. }
      rewrite updatePcPerm_cap_non_E //;[].
      iIntros "(HPC & Hr1 & Hrenv & Hcls)".
      (* close the invariant for the closure *)
      iDestruct ("Hcls_close" with "[Hcls $Hna]") as ">Hna".
      { repeat iDestruct "Hprog_done" as "(?&Hprog_done)". iNext. iFrame. }

      iDestruct (big_sepM_insert with "[$Hregs' $Hr1]") as "Hregs'".
        by rewrite lookup_delete_ne // lookup_delete //.
        rewrite -delete_insert_ne // insert_delete.
      destruct (Hr'_full r_stk) as [rstkv Hrstkv].
      iDestruct (big_sepM_delete _ _ r_stk with "Hregs'") as "[Hrstk Hregs']".
        by rewrite !lookup_delete_ne // lookup_insert_ne // lookup_delete_ne //.

      iApply (lse_spec with "[$HPC $Hrenv $Hrstk $Hregs' $Hna $Hsts $Hr $Henv $Hawk]");
        [apply Hvpc_awk|apply Hcont_awk|auto..|].
      { rewrite !dom_delete_L !dom_insert_L !dom_delete_L Hdom_r'.
        rewrite !singleton_union_difference_L !all_registers_union_l !difference_difference_L.
        f_equal. clear. set_solver. }
      { solve_ndisj. }
      iSplitL. iExists lseN; iApply "Hawk_inv".
      { unshelve iSpecialize ("Hr'_valid" $! r_stk _); [done|].
        rewrite /(RegLocate r' r_stk) Hrstkv. iApply "Hr'_valid". }
      iNext. iIntros (?) "HH". iIntros (->). iApply "HH". eauto.
    }

    unshelve iPoseProof ("Hr_valid" $! r_t0 _) as "#Hr0_valid". done.
    rewrite /(RegLocate _ r_t0) Hr0.

    iAssert (((fixpoint interp1) W2) r0) as "#Hr0_valid2".
    { iApply (interp_monotone with "[] Hr0_valid"). iPureIntro. apply related_sts_pub_refl_world. }
    set r' : gmap RegName Word :=
      <[r_t0  := r0]>
      (<[r_t1 := inr (E, Global, b_cls, e_cls, b_cls)]>
       (create_gmap_default (list_difference all_registers [r_t0;r_t1]) (inl 0%Z))).

    (* either we fail, or we use the continuation in rt0 *)
    iDestruct (jmp_or_fail_spec with "Hr0_valid2") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm r0))).
    2 : { iEpilogue "(HPC & Hi & Hr0)". iApply "Hcont". iFrame "HPC". iIntros (Hcontr);done. }
    iDestruct "Hcont" as (p g b e a3 Heq) "#Hcont".
    simplify_eq.

    iAssert (future_world g e W2 W2) as "#Hfuture".
    { destruct g; iPureIntro. 1,2:apply related_sts_priv_refl_world. apply related_sts_a_refl_world. }
    iAssert (∀ r, ▷ ((interp_expr interp r) W2 (updatePcPerm (inr (p, g, b, e, a3)))))%I with "[Hcont]" as "Hcont'".
    { iIntros. iApply "Hcont". iApply "Hfuture". }

    (* prepare the continuation *)
    iEpilogue "(HPC & Hi & Hr0)". iCombine "Hi" "Hprog_done" as "Hprog_done".

    (* Put the registers back in the map *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr2]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete //. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr1]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). apply lookup_delete. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr0]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne // lookup_delete //. }
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
    { repeat (rewrite lookup_insert_ne //;[]). rewrite lookup_delete_ne //.
      repeat (rewrite lookup_insert_ne //;[]). do 2 rewrite lookup_delete_ne //.
      apply lookup_delete. }
    repeat (rewrite -(delete_insert_ne _ r_t2) //;[]). rewrite insert_delete.
    repeat (rewrite -(delete_insert_ne _ r_t1) //;[]). rewrite insert_delete.
    repeat (rewrite -(delete_insert_ne _ r_t0) //;[]). rewrite insert_delete.
    repeat (rewrite -(delete_insert_ne _ PC) //;[]). rewrite insert_delete.
    rewrite -(insert_insert _ PC _ (inl 0%Z)).
    match goal with |- context [ ([∗ map] k↦y ∈ <[PC:=_]> ?r, _)%I ] => set r'' := r end.
    iAssert (full_map r'') as %Hr''_full.
    { rewrite /full_map. iIntros (rr). iPureIntro. rewrite elem_of_gmap_dom /r''.
      rewrite 12!dom_insert_L regmap_full_dom //.
      generalize (all_registers_s_correct rr). clear; set_solver. }
    assert (related_sts_pub_world W W2) as Hfuture2.
    { apply related_sts_pub_refl_world; auto. }
    iSpecialize ("Hcont'" $! r'' with "[Hsts Hr Hregs HnaI]").
    { iFrame.
      rewrite /interp_reg. iSplit; [iPureIntro; apply Hr''_full|].
      iIntros (rr Hrr).
      assert (is_Some (r'' !! rr)) as [rrv Hrrv] by apply Hr''_full.
      rewrite /RegLocate Hrrv. rewrite /r'' in Hrrv.
      rewrite lookup_insert_Some in Hrrv |- *. move=> [ [? ?] | [_ Hrrv] ].
      { subst rr. by exfalso. }
      rewrite lookup_insert_Some in Hrrv |- *. move=> [ [? ?] | [? Hrrv] ].
      { subst rr rrv. iApply "Hr0_valid2". }
      rewrite lookup_insert_Some in Hrrv |- *. move=> [ [? ?] | [? Hrrv] ].
      { subst rr rrv. iApply "Hvalid_cls". }
      do 9 (
        rewrite lookup_insert_Some in Hrrv |- *; move=> [ [? ?] | [? Hrrv] ];
        [subst; by rewrite (fixpoint_interp1_eq W2 (inl 0%Z)) |]
      ).
      unshelve iSpecialize ("Hr_valid" $! rr _). by auto. rewrite Hrrv.
      iApply (interp_monotone with "[] Hr_valid"). auto. }
    (* apply the continuation *)
    iDestruct "Hcont'" as "[_ Hcallback_now]".
    iApply wp_wand_l. iFrame "Hcallback_now".
    iIntros (v) "Hφ". iIntros (Hne).
    iDestruct ("Hφ" $! Hne) as (r0 W') "(Hfull & Hregs & #Hrelated & Hna & Hsts & Hr)".
    iExists r0,W'. iFrame.
    iDestruct "Hrelated" as %Hrelated. iPureIntro.
    eapply related_sts_pub_priv_trans_world;[|eauto].
    apply related_sts_pub_refl_world; auto.
  Qed.

End downwards_lse_preamble.
