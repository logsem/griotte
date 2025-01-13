From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules logrel fundamental region_invariants_batch_uninitialized.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers macros.

Section lse.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.


  Definition lse_instrs f_a :=
    prepstackU_instrs r_stk 1 1 ++
    [loadU_r_z r_t0 r_stk (-1); (* since parameters are passer on the stack, no need to check that the input is below the stack bound *)
    pushU_r_instr r_stk r_env;
    load_r r_env r_env] ++
    assert_r_z_instrs f_a r_env 2 ++
    rclear_instrs (list_difference all_registers [PC;r_t0]) ++
    [jmp r_t0].

  Definition lse a f_a :=
    ([∗ list] a_i;w_i ∈ a;(lse_instrs f_a), a_i ↦ₐ w_i)%I.

  Definition lse_inv d : iProp Σ := d ↦ₐ inl 2%Z.


  Lemma lse_spec W pc_p pc_g pc_b pc_e (* PC *)
        lse_addrs (* program addresses *)
        d d' (* dynamically allocated memory given by preamble, connected to invariant i *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        wstk (* stack *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between lse_addrs a_first a_last ->

    (* Linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* malloc'ed memory assumption *)
    (d + 1)%a = Some d' ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_env]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    {{{ r_stk ↦ᵣ wstk
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (lse_inv d))
      (* stack *)
      ∗ interp W wstk
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (lse lse_addrs f_a)
      (* linking table *)
      ∗ na_inv logrel_nais ι2 (pc_b ↦ₐ inr (RO,Global,b_link,e_link,a_link) ∗ a_entry ↦ₐ fail_cap)
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
                    ∃ r W', full_map r ∧ registers_mapsto r
                         ∗ ⌜related_sts_priv_world W W'⌝
                         ∗ na_own logrel_nais ⊤
                         ∗ sts_full_world W'
                         ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hcont Hlt_wb Hlt_link Hdoff Hdom Hndisj φ).
    iIntros "(Hr_stk & HPC & Hr_env & Hregs & #Hdinv & #Hwstk_valid & Hown & #Hlse_prog & #Htable & Hsts & Hr) Hφ".
    iMod (na_inv_acc with "Hlse_prog Hown") as "(>Hprog & Hown & Hcls)";auto.
    (* get some general purpose registers *)
    assert (is_Some (rmap !! r_t0)) as [w0 Hw0];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t2)) as [w2 Hw2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t3)) as [w3 Hw3];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t4)) as [w4 Hw4];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t0 Hregs]";[apply Hw0|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[rewrite lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    (* prepstack *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iApply (prepstackU_spec with "[- $HPC $Hcode $Hr_stk]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|].
    iNext. destruct (isPermWord wstk URWLX) eqn:Hperm;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    (* cleanup of stack information *)
    destruct wstk as [| [ [ [ [p_stk l_stk] b_stk] e_stk] a_stk] ];[inversion Hperm|]. iExists l_stk,b_stk, e_stk, a_stk.
    destruct p_stk;inversion Hperm. iSplit;auto.
    destruct (1%nat + 1%nat <? e_stk - b_stk)%Z eqn:Hsize;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct (b_stk + 1%nat <=? a_stk)%Z eqn:Hle;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iDestruct (writeLocalAllowedU_implies_local with "Hwstk_valid") as %Hmonotone;auto. destruct l_stk;inversion Hmonotone.
    iIntros "Hstack".
    iDestruct "Hstack" as (a Ha) "(HPC & Hprepstack & Hr_stk & Hr_t1 & Hr_t2)".
    apply Z.leb_le in Hle. apply Z.ltb_lt in Hsize.
    (* pop r_stk r_t0 *)
    (* in order to pop, we must first open the region at b_stk *)
    iDestruct (writeLocalAllowedU_valid_cap_below_implies _ _ _ _ _ _ b_stk with "Hwstk_valid") as %Ha_param_W;[auto|..].
    { clear -Hle Hsize Ha. rewrite andb_true_iff Z.leb_le Z.ltb_lt. solve_addr. }
    { clear -Hle;solve_addr. }
    iDestruct (read_allowedU_inv _ b_stk with "Hwstk_valid") as  "Hrel";[clear -Hsize;solve_addr|auto|]. 
    iDestruct (region_open_monotemp with "[$Hr $Hsts $Hrel]") as (wret) "(Hr & Hsts & Hstate & Hb_stk & #Hmono & #Hwret_valid)";auto.
    iSimpl in "Hwret_valid".
    (* loadU r_t0 r_stk -1 *)
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength1. destruct_addr_list l_code0.
    iPrologue "Hcode". apply contiguous_between_cons_inv_first in Hcont_code0 as Heq. subst link.
    iApply (rules_LoadU_derived.wp_loadU_success with "[$HPC $Hi $Hr_t0 $Hr_stk $Hb_stk]");
      [apply decode_encode_instrW_inv|iCorrectPC l_code0 link0|auto..].
    { clear -Hle Hsize Ha. rewrite andb_true_iff Z.leb_le Z.ltb_lt. solve_addr. }
    { iContiguous_next_a Hcont_code0. }
    iEpilogue "(HPC & Hr_t0 & Hprog_done & Hr_stk & Hb_stk)".
    (* we can close the world again *)
    iDestruct (region_close_monotemp with "[$Hstate $Hb_stk $Hr $Hrel $Hmono $Hwret_valid]") as "Hr";auto.

    (* pushu r_stk r_env *)
    (* we have reached a part of the code which will require us to make a pub^b_stk change to the world *)
    (* we will therefore first uninitialize all addresses at or above b_stk *)
    iMod (uninitialize_region _ b_stk with "[$Hsts $Hr]") as (m Hmcond) "[Hsts Hr]".
    (* next we can open the region at b_stk, which we will first assert is in m *)
    iDestruct (valid_uninitialized_condition _ m with "Hwstk_valid") as %Hstk_cond;auto.
    (* next we can open the world at a *)
    assert (b_stk <= a < e_stk)%a as Hstk_bounds.
    { split;[clear -Ha;solve_addr|]. clear -Hsize Ha. solve_addr. }
    pose proof (Hstk_cond a Hstk_bounds) as [w Hw].
    iDestruct (read_allowedU_inv _ a with "Hwstk_valid") as "Hrel'";[clear -Hsize Ha;solve_addr|auto|].
    iDestruct (region_open_uninitialized with "[$Hrel' $Hr $Hsts]") as "(Hr & Hsts & Hstate & Ha)";[eauto|..].
    (* and we are ready to push a new value b_stk *)
    assert (is_Some (a + 1))%a as [b_stk1 Hb_next].
    { clear -Hstk_bounds. destruct (a + 1)%a eqn:Hsome;eauto. exfalso. solve_addr. }
    iDestruct "Hcode" as "[HpushU Hcode]".
    iApply (pushU_r_spec with "[- $HPC $HpushU $Hr_stk $Hr_env $Ha]");
      [iCorrectPC l_code0 link0| |iContiguous_next_a Hcont_code0|apply Hb_next|..].
    { apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];clear -Hstk_bounds;solve_addr. }
    { intros Hcontr;inversion Hcontr. }
    iNext. iIntros "(HPC & HpushU & Hr_stk & Hr_env & Hb_stk)".
    (* we can now close the world again *)
    pose proof (uninitialized_condition _ _ _ Hmcond) as Hmcond_alt.
    iMod (uninitialize_open_region_change _ _ a with "[$Hb_stk $Hrel' $Hsts $Hr $Hstate]") as "[Hr Hsts]";
      [clear;solve_addr|auto|].
    { intros. apply Hmcond_alt. clear -H0 Ha. solve_addr. }

    (* and we can now finish executing the instructions without more changes to W *)
    iPrologue "Hcode".
    iDestruct "Hdinv" as (ι) "Hdinv". iInv ι as ">Hd" "Hcls'". rewrite /lse_inv.
    iAssert (⌜(d =? a1)%a = false⌝)%I as %Heq_false.
    { rewrite Z.eqb_neq. iIntros (->%z_of_eq). iDestruct (addr_dupl_false with "Hi Hd") as "Hbot";[auto..|done]. }
    iApply (wp_load_success_same with "[$HPC $Hi $Hr_env Hd]");
      [auto|apply decode_encode_instrW_inv|iCorrectPC l_code0 link0|..];auto.
    { clear -Hdoff. apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];solve_addr. }
    { eapply contiguous_between_last. apply Hcont_code0. auto. }
    { rewrite Heq_false. iFrame. }
    rewrite Heq_false.
    iNext. iIntros "(HPC & Hr_env & Hi & Hd)". iCombine "Hi" "Hprog_done" as "Hprog_done".
    iMod ("Hcls'" with "[$Hd]") as "_".
    iModIntro. iApply wp_pure_step_later;auto. iNext.
    iClear "Hcode".

    (* assert r_env 2 *)
    iPrologue_multi "Hprog" Hcont Hvpc link2.
    iMod (na_inv_acc with "Htable Hown") as "(>[Hpc_b Ha_entry] & Hown & Hcls'')";[auto|solve_ndisj|].
    iApply (assert_r_z_success with "[- $HPC $Hcode $Hr_env $Hpc_b $Ha_entry]");
      [apply Hvpc_code1|apply Hcont_code1|auto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|].
    iNext. iIntros "(Hr_t1 & Hr_t2 & Hr_t3 & Hr_env & HPC & Hassert & Hpc_b & Ha_entry)".
    iMod ("Hcls''" with "[$Hown $Hpc_b $Ha_entry]") as "Hown".

    (* rclear RegName/{PC;r_t0} *)
    iPrologue_multi "Hprog" Hcont Hvpc link3.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_stk]") as "Hregs".
    { rewrite lookup_insert_ne// lookup_delete_ne// !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom. set_solver-. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_env]") as "Hregs".
    { simplify_map_eq. apply not_elem_of_dom. rewrite Hdom. set_solver-. }
    iApply (rclear_spec_gmap with "[- $HPC $Hcode $Hregs]");[eauto..|].
    { apply not_elem_of_list. constructor. }
    { assert (length l_code2 = 31) as Hlength4. clear -Hlength2 Hlength3. rewrite app_length Hlength3 in Hlength2. lia.
      destruct l_code2;inversion Hlength4. apply contiguous_between_cons_inv_first in Hcont_code2 as ->. auto. }
    { clear -Hdom. rewrite !dom_insert_L !dom_delete_L !dom_insert_L Hdom list_to_set_difference -/all_registers_s /=. clear. set_solver. }
    iNext. iIntros "[HPC [Hdom Hrclear]]".
    iDestruct "Hdom" as (rmap') "[Hregs #Hregs_cond]". iDestruct "Hregs_cond" as %[Hdom' Hzeroes].

    (* jmp r_t0 *)
    prep_addr_list_full l_rest2 Hcont.
    iPrologue "Hprog".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 a_last|].

    (* first we will update the varilidy of wret to the new world *)
    set (W' := (<s[a:=Uninitialized (inr (RWX, Global, d, d', d))]s>(uninitialize W m))).
    assert (related_sts_a_world W W' b_stk) as Hrelated.
    { eapply related_sts_a_trans_world;[apply uninitialize_related_pub_a|];eauto.
      apply related_sts_a_uninitialized. clear -Ha; solve_addr. apply Hstk_cond. auto. }
    iDestruct ("Hmono" $! _ _ Hrelated with "Hwret_valid") as "Hwret_valid'". iSimpl in "Hwret_valid'".
    iDestruct (jmp_or_fail_spec with "Hwret_valid'") as "Hcond". destruct (decide (isCorrectPC (updatePcPerm wret))).
    2: { iEpilogue "(HPC & _)". iApply "Hcond". iFrame. iApply "Hφ". iIntros (Hcontr). inversion Hcontr. }
    iDestruct "Hcond" as (p g b e a' Heq) "Hcond". rewrite Heq.
    iSpecialize ("Hcond" $! (<[PC:=inl 0%Z]> (<[r_t0:=wret]> rmap')) W' with "[]").
    { destruct g;iPureIntro.
      apply related_sts_priv_refl_world. apply related_sts_priv_refl_world. apply related_sts_a_refl_world. }

    (* we can now establish the continuation *)
    iEpilogue "(HPC & Hi & Hr_t0)".

    (* first we will close the program invariant *)
    iMod ("Hcls" with "[Hprepstack HpushU Hprog_done Hassert Hrclear Hi $Hown]") as "Hown".
    { iNext. iFrame. iDestruct "Hprog_done" as "($&$)". simpl. done. }

    (* next we must establish that the current register state is valid *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs".
    { apply not_elem_of_dom. rewrite Hdom'. set_solver-. }
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
    { rewrite lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom'. set_solver-. }
    iDestruct ("Hcond" with "[$Hown $Hr $Hsts Hregs]") as "[_ Hconf]".
    {  rewrite -(insert_insert _ PC _ (inl 0%Z)) Heq. iFrame "Hregs". iSplit;[iPureIntro|].
      - simpl. intros x. apply elem_of_gmap_dom. rewrite !dom_insert_L Hdom' list_to_set_difference. clear.
        pose proof (all_registers_s_correct x). set_solver.
      - iIntros (r HPC). rewrite /RegLocate. rewrite lookup_insert_ne//.
        destruct (decide (r_t0 = r));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne;auto].
        rewrite Hzeroes. rewrite !fixpoint_interp1_eq. done.
        rewrite Hdom'. clear -HPC n. pose proof (all_registers_s_correct r).
        rewrite list_to_set_difference. set_solver. }
    iApply (wp_wand with "Hconf").
    iIntros (v). iIntros "Hcond'". iApply "Hφ".
    iIntros (Hhalted). iDestruct ("Hcond'" $! Hhalted) as (r W'') "(?&?&%&?&?&?)".
    iExists _,_;iFrame.
    iPureIntro. eapply related_sts_a_priv_trans_world;eauto.
  Qed.

End lse.
