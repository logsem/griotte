From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules rules_LoadU_derived logrel fundamental region_invariants_revocation region_invariants_static region_invariants_batch_uninitialized stack_object_helpers.
From cap_machine Require Export iris_extra addr_reg_sample region_macros contiguous stack_macros_helpers macros.

Section stack_object.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Definition r_adv := r_t29.
  Definition r_param1 := r_t16.
  Definition r_param2 := r_t17.

  Definition stack_object_passing_instrs stack_obj f_a :=
    (* we check that the function pointer is global *)
    reqglob_instrs r_adv ++
    (* prepare the stack *)
    prepstackU_instrs r_stk 12 2 ++
    (* load parameter 1 into register *)
    [loadU_r_z r_param1 r_stk (-1)] ++
    (* we must do some dynamic checks on the input object, which can be a stack object *)
    checkra_instrs r_param1 ++
    checkints_instrs r_param1 r_t1 r_t2 r_t3 ++
    (* we can begin the function *)
    (* push some local state *)
    [pushU_z_instr r_stk 2;
    (* we create a stack object *)
    pushU_z_instr r_stk stack_obj;
    move_r r_param2 r_stk;
    getb r_t1 r_stk;
    gete r_t2 r_stk;
    add_r_z r_t1 r_t1 3;
    subseg_r_r r_param2 r_t1 r_t2;
    promoteU r_param2] ++
    (* call r_adv *)
    scallU_prologue_instrs r_adv [r_param1;r_param2] ++
    (* we push the parameters onto the new restricted adversary stack *)
    [pushU_r_instr r_stk r_param1;
    pushU_r_instr r_stk r_param2;
    pushU_r_instr r_stk r_t0;
    move_z r_param1 0; (* these three cleanup steps are not necessary, but practical *)
    move_z r_param2 0;
    move_z r_t0 0;
    (* jump to the ardversary callee *)
    jmp r_adv;
    (* restore local state *)
    lea_z r_stk (-6)] ++
    (* we assert that the local state is still 2. If the return pointer has been leaked,
       then the caller can alter the local state, jump to the return pointer and make
       the following assertion fail *)
    [loadU_r_z r_adv r_stk (-2)] ++
    assert_r_z_instrs f_a r_adv 2 ++
    [loadU_r_z r_t1 r_stk (-4)] ++
    (* we leave everything on the stack, but clear registers before returning *)
    rclear_instrs (list_difference all_registers [PC;r_t1]) ++
    [jmp r_t1].

  Definition stack_object_passing a stack_obj f_a :=
    ([∗ list] a_i;w_i ∈ a;(stack_object_passing_instrs stack_obj f_a), a_i ↦ₐ w_i)%I.


  Lemma stack_object_spec W pc_p pc_g pc_b pc_e (* PC *)
        stack_object_passing_addrs (* program addresses *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        stack_obj advw (* input *)
        wstk (* stack *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between stack_object_passing_addrs a_first a_last ->

    (* Linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* the monotonicity of the PC is not monotone *)
    isDirected pc_g = false →

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_adv]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    {{{ r_stk ↦ᵣ wstk
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* adv *)
      ∗ r_adv ↦ᵣ advw
      ∗ interp W advw
      (* stack *)
      ∗ interp W wstk
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (stack_object_passing stack_object_passing_addrs stack_obj f_a)
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
    iIntros (Hvpc Hcont Hlt_wb Hlt_link Hpcmono Hdom Hndisj φ).
    iIntros "(Hr_stk & HPC & Hregs & Hr_adv & #Hadv_valid & #Hwstk_valid & Hown & #Hlse_prog & #Htable & Hsts & Hr) Hφ".
    iMod (na_inv_acc with "Hlse_prog Hown") as "(>Hprog & Hown & Hcls)";auto.

    (* get some general purpose registers *)
    assert (is_Some (rmap !! r_t0)) as [w0 Hw0];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t2)) as [w2 Hw2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t3)) as [w3 Hw3];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_t4)) as [w4 Hw4];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_param1)) as [wp1 Hwp1];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    assert (is_Some (rmap !! r_param2)) as [wp2 Hwp2];[apply elem_of_gmap_dom;rewrite Hdom;set_solver+|].
    iDestruct (big_sepM_delete with "Hregs") as "[Hr_t0 Hregs]";[apply Hw0|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]";[rewrite lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t4 with "Hregs") as "[Hr_t4 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_param1 with "Hregs") as "[Hr_param1 Hregs]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_param2 with "Hregs") as "[Hr_param2 Hregs]";[rewrite !lookup_delete_ne//;eauto|].

    (* reqglob  *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code.
    iApply (reqglob_spec with "[- $HPC $Hcode $Hr_adv]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|].
    iNext. destruct (isGlobalWord advw) eqn:Hglob;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct advw as [c | [ [ [ [g l] b] e] a'] ];[inversion Hglob|]. destruct l;[|inversion Hglob..].
    iExists _,_,_,_. iSplit;[eauto|].
    iIntros "(HPC & Hreqglob & Hr_adv & Hr_t1 & Hr_t2)".

    (* prepstack *)
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code0.
    iApply (prepstackU_spec with "[- $HPC $Hcode $Hr_stk]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|].
    iNext. destruct (isPermWord wstk URWLX) eqn:Hperm;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct wstk as [c | [ [ [ [gstk lstk] bstk] estk] astk] ];[inversion Hperm|]. destruct gstk;inversion Hperm.
    iExists _,_,_,_. iSplit;[eauto|].
    destruct ((12%nat + 2%nat <? estk - bstk)%Z) eqn:Hsize;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct ((bstk + 2%nat <=? astk)%Z) eqn:Hbounds;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iIntros "Hcont". iDestruct "Hcont" as (a_param Ha_param) "(HPC & HprepstackU & Hr_stk & Hr_t1 & Hr_t2)".
    apply Z.ltb_lt in Hsize. apply Z.leb_le in Hbounds.

    (* we can extract the validity of the parameters passed on the stack *)
    (* we only need the validity of the stack object parameter, not need for the return pointer yet *)
    destruct (bstk + 1)%a eqn:Hsome;[|exfalso;clear -Ha_param Hsome;solve_addr].
    iDestruct (read_allowedU_inv _ a with "Hwstk_valid") as "Hcond2";[clear -Hbounds Hsize Hsome;solve_addr|auto|].
    iDestruct (writeLocalAllowedU_valid_cap_below_implies _ _ _ _ _ _ a with "Hwstk_valid") as %Hmono2;
      [auto|apply le_addr_withinBounds|..];[clear -Hbounds Hsize Hsome;solve_addr..|].

    (* loadU r_param1 r_stk -1 *)
    iPrologue_multi "Hprog" Hcont Hvpc link1.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code1.
    destruct_addr_list l_code1.
    iDestruct (region_open_monotemp with "[$Hcond2 $Hr $Hsts]") as
        (wsecret) "(Hr & Hsts & Hstate & Ha & #Hmono & #Hwsecret_valid)";[auto..|].
    iPrologue "Hcode". apply contiguous_between_cons_inv_first in Hcont_code1 as Heq. subst l_code1.
    iApply (wp_loadU_success with "[$HPC $Hi $Hr_param1 $Hr_stk $Ha]");
      [apply decode_encode_instrW_inv|iCorrectPC link0 link1|auto..].
    { clear -Hsome Ha_param Hbounds Hsize. apply le_addr_withinBounds;solve_addr. }
    { apply Hlink1. }
    { clear -Hsome Ha_param Hbounds Hsize. solve_addr. }
    iEpilogue "(HPC & Hr_param1 & Hprog_done & Hr_stk & Ha)".
    iDestruct (region_close_monotemp with "[$Hstate $Hr $Ha $Hcond2]") as "Hr";auto. iClear "Hcode".

    (* check the passed object is RA *)
    iPrologue_multi "Hprog" Hcont Hvpc link2.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code2.
    iApply (checkra_spec with "[- $HPC $Hcode $Hr_param1 $Hr_t1 $Hr_t2 $Hr_t3 $Hr_t4]");[eauto..|].
    iNext. destruct (is_cap wsecret) eqn:Hiscap;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct wsecret as [c | [ [ [ [l p] bsec] esec] asec] ];[inversion Hiscap|].
    iExists _,_,_,_,_;iSplit;[eauto|].
    destruct (readAllowed l) eqn:Hra;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iIntros "(HPC & Hcheckra & Hr_param1 & Hr_t1 & Hr_t2 & Hr_t3 & Hr_t4)".

    (* we must now dynamically check that the object in param1 is of the correct type *)
    (* we must therefore extract the object from W *)
    (* we will thereafter need to freeze the full world, before reinstating the object after the check *)

    (* extract region information of [bsec,esec] from W *)
    iDestruct (state_unused_stack with "Hwstk_valid") as %Hstack_state;[apply Hbounds|apply Ha_param|].
    iDestruct (input_stack_disjoint _ _ a_param estk with "[$Hwsecret_valid $Hmono]") as %Hdisj;
      [clear -Hbounds Hsize Hsome Ha_param;solve_addr|auto|auto|].
    iDestruct (readAllowed_implies_region_conditions with "Hwsecret_valid") as "Hsecret_cond";auto.

    (* uninitialize the full stack *)
    iMod (uninitialize_region_keep _ addr_reg.za with "[$Hsts $Hr]") as (m Hmcond) "[Hsts [Hr #Hvalids] ]".
    (* next we can open the region at b_stk, which we will first assert is in m *)
    iDestruct (valid_uninitialized_condition_weak _ m with "Hwstk_valid") as %Hstk_cond;eauto. clear. solve_addr.
    iSimpl in "Hwsecret_valid". iDestruct (valid_readAllowed_condition_weak _ m with "Hwsecret_valid") as %Hsec_cond;eauto. clear. solve_addr.
    iDestruct (pers_res_to_sec_res with "Hvalids []") as "Hsec_res";[auto|iNext;iFrame "Hsecret_cond"|].

    (* opening [bsec,esec] while remembering the words in case of uninitialized state in (uninit m W) *)
    iDestruct (open_stack_object with "[$Hsts $Hr]") as "(Hsts & Hws)";eauto.
    { iApply big_sepL_forall. iIntros (k x Hx).
      assert (x ∈ region_addrs bsec esec) as Hinx;[apply elem_of_list_lookup;eauto|].
      iDestruct (read_allowed_inv with "Hwsecret_valid") as "Hasw".
      apply elem_of_region_addrs in Hinx. eauto. eauto.
      destruct (writeAllowed l).
      iExists interp. iSplit;[iPureIntro;apply _|]. iSplit. iFrame "Hasw". rewrite /rcond.
      iSplit;[auto|]. iNext. iModIntro. iIntros (W1 W2 z) "_". iClear "#". rewrite fixpoint_interp1_eq;done.
      iDestruct "Hasw" as (P) "(?&?&?)". iExists P;iFrame "#". }
    iDestruct "Hws" as (wps) "(Hbesec & Hcls' & #Hsecret_states)".
    iDestruct (big_sepL2_length with "Hbesec") as %Hbesec_length.
    iDestruct "Hsecret_states" as %Hsecret_states.

    (* Now we are ready to apply the checkints macro *)
    iPrologue_multi "Hprog" Hcont Hvpc link3.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code3.
    iApply (wp_wand with "[- Hφ]").
    2: { iIntros (v) "Hφ'". iApply "Hφ". iExact "Hφ'". }
    iApply (wp_wand with "[-]").
    iApply (checkints_spec with "[- $HPC $Hcode $Hr_param1 $Hbesec $Hr_t1 $Hr_t2 $Hr_t3]");[eauto..|].
    2: { iSimpl. iIntros (v) "[Hφ | Hfailed]". iExact "Hφ". iIntros "Hcontr". iSimplifyEq. }
    iNext. iIntros "(HPC & Hcheckints & Hr_param1 & Hr_t1 & Hr_t2 & Hr_t3 & Hbesec & #Hints)".
    iDestruct "Hints" as %Hints.
    (* we now have enough information to close the region again *)
    iDestruct ("Hcls'" with "Hbesec") as "Hr".

    (* for the next part of the code, we will need to manipulate our local stack frame *)
    (* for that, we begin by revoking the local stack frame from W which we will use to store the local state and activation record*)
    assert (∃ frame_end, a_param + 12 = Some frame_end)%a as [frame_end Hframe_delim].
    { clear -Hbounds Ha_param Hsome Hsize. destruct (a_param + 12)%a eqn:HH;eauto. exfalso. solve_addr. }
    (* first we must know that a fully uninitialized world satisfies the revoke condition *)
    apply uninitialize_revoke_condition in Hmcond as Hrevoked.
    (* next we may revoke it *)
    iMod (uninitialize_to_revoked_cond (region_addrs a_param frame_end) _ _ (λ Wv, interp Wv.1 Wv.2) with "[$Hr $Hsts]") as "(Hr & Hsts & Hframe)";[auto|apply region_addrs_NoDup|..].
    { apply Forall_forall. intros x Hin%elem_of_region_addrs. apply Hstk_cond. clear -Hbounds Ha_param Hsome Hsize Hframe_delim Hin. solve_addr. }
    { iApply big_sepL_forall. iIntros (k x Hlookup).
      assert (x ∈ (region_addrs a_param frame_end)) as Hin;[apply elem_of_list_lookup;eauto|].
      apply elem_of_region_addrs in Hin.
      iDestruct (read_allowedU_inv _ x with "Hwstk_valid") as "Hcond".
      clear -Hin Hframe_delim Ha_param Hsome Hsize Hbounds. solve_addr.
      auto. iFrame "Hcond". }

    (* finally we clean up our resources a bit *)
    iAssert (∃ ws,[[a_param,frame_end]]↦ₐ[[ws]])%I with "[Hframe]" as (wsstk) "Hframe".
    { iDestruct (region_addrs_exists with "Hframe") as (ws) "Hframe".
      iExists ws. iApply (big_sepL2_mono with "Hframe"). iIntros (k y1 y2 Hin1 Hin2) "H". iFrame. }
    iDestruct (big_sepL2_length with "Hframe") as %Hframe_length.
    rewrite region_addrs_length in Hframe_length.
    apply (incr_addr_region_size_iff _ _ 12)in Hframe_delim as Hframe_det.
    destruct Hframe_det as [Hframe_le Hframe_size]. rewrite Hframe_size in Hframe_length.

    (* we can now continue with the execution of instructions *)
    iPrologue_multi "Hprog" Hcont Hvpc link4.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code4.
    destruct_addr_list l_code3.
    iDestruct (writeLocalAllowedU_implies_local with "Hwstk_valid") as %Hmono;auto.
    destruct lstk;inversion Hmono;clear Hmono.

    (* pushU r_stk 2 *)
    assert (is_Some (a_param + 1)%a) as [af2 Haf2].
    { destruct (a_param + 1)%a eqn:Hcontr;eauto;exfalso;clear -Hframe_delim Hcontr;solve_addr. }
    destruct wsstk as [|wf1 wsstk];[inversion Hframe_length|].
    iDestruct (region_mapsto_cons with "Hframe") as "[Hf1 Hframe]";
      [apply Haf2|clear -Haf2 Hframe_delim;solve_addr|..].
    iDestruct "Hcode" as "[Hi Hcode]".
    apply contiguous_between_cons_inv_first in Hcont_code4 as Heq. subst l_code3.
    iApply (pushU_z_spec with "[- $HPC $Hf1 $Hr_stk $Hi]");
      [iCorrectPC link3 link4|auto|iContiguous_next_a Hcont_code4|apply Haf2|].
    { clear -Hbounds Ha_param Hsize Hframe_delim. apply le_addr_withinBounds; solve_addr. }
    iNext. iIntros "(HPC & Hprog_done2 & Hr_stk & Hf1)".

    (* pushU r_stk stack_obj *)
    assert (is_Some (af2 + 1)%a) as [af3 Haf3].
    { destruct (af2 + 1)%a eqn:Hcontr;eauto;exfalso;clear -Hframe_delim Hcontr Haf2;solve_addr. }
    destruct wsstk as [|wf2 wsstk];[inversion Hframe_length|].
    iDestruct (region_mapsto_cons with "Hframe") as "[Hf2 Hframe]";
      [apply Haf3|clear -Haf2 Haf3 Hframe_delim;solve_addr|..].
    iDestruct "Hcode" as "[Hi Hcode]".
    iApply (pushU_z_spec with "[- $HPC $Hf2 $Hr_stk $Hi]");
      [iCorrectPC link3 link4|auto|iContiguous_next_a Hcont_code4|apply Haf3|].
    { clear -Hbounds Ha_param Hsize Hframe_delim Haf2 Haf3.
      apply le_addr_withinBounds; solve_addr. }
    iNext. iIntros "(HPC & Hi & Hr_stk & Hf2)". iCombine "Hi" "Hprog_done2" as "Hprog_done2".

    (* move r_param2 r_stk *)
    iPrologue "Hcode".
    iApply (wp_move_success_reg with "[$HPC $Hi $Hr_param2 $Hr_stk]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 link4|iContiguous_next_a Hcont_code4|].
    iEpilogue "(HPC & Hi & Hr_param2 & Hr_stk)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    (* getb r_t1 r_stk *)
    iPrologue "Hcode".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t1 $Hr_stk]");
      [apply decode_encode_instrW_inv|eauto|iCorrectPC link3 link4|iContiguous_next_a Hcont_code4|auto..|].
    iEpilogue "(HPC & Hi & Hr_stk & Hr_t1)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    iSimpl in "Hr_t1".
    (* gete r_t2 r_stk *)
    iPrologue "Hcode".
    iApply (wp_Get_success with "[$HPC $Hi $Hr_t2 $Hr_stk]");
      [apply decode_encode_instrW_inv|eauto|iCorrectPC link3 link4|iContiguous_next_a Hcont_code4|auto..|].
    iEpilogue "(HPC & Hi & Hr_stk & Hr_t2)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    iSimpl in "Hr_t2".
    (* add r_t1 r_t1 3 *)
    iPrologue "Hcode".
    iApply (wp_add_sub_lt_success_dst_z with "[$HPC $Hi $Hr_t1]");
      [apply decode_encode_instrW_inv|eauto|iContiguous_next_a Hcont_code4|iCorrectPC link3 link4|].
    iEpilogue "(HPC & Hi & Hr_t1)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    iSimpl in "Hr_t1".
    (* subseg r_param2 r_t1 r_t2 *)
    iPrologue "Hcode".
    iApply (wp_subseg_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ af2 estk with "[$HPC $Hi $Hr_param2 $Hr_t1 $Hr_t2]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 link4| |auto| |iContiguous_next_a Hcont_code4|].
    { split;[|apply z_to_addr_z_of]. clear -Haf2 Ha_param. assert (bstk + 3 = Some af2)%a;[solve_addr|].
      apply incr_addr_of_z_i in H as Heq. rewrite Heq. apply z_to_addr_z_of. }
    { rewrite /isWithin. apply andb_true_iff. rewrite !Z.leb_le. clear -Ha_param Haf2. solve_addr. }
    iEpilogue "(HPC & Hi & Hr_t1 & Hr_t2 & Hr_param2)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    (* promoteU r_param2 *)
    iPrologue "Hcode".
    iApply (rules_PromoteU_derived.wp_promoteU_success with "[$HPC $Hi $Hr_param2]");
      [apply decode_encode_instrW_inv|iCorrectPC link3 link4|auto|..].
    { eapply contiguous_between_last. apply Hcont_code4. auto. }
    iEpilogue "(HPC & Hi & Hr_param2)"; iCombine "Hi" "Hprog_done2" as "Hprog_done2".
    iSimpl in "Hr_param2". assert (addr_reg.min af3 estk = af3) as ->;[clear -Hbounds Hsize Ha_param Haf2 Haf3;solve_addr|].

    (* we are now ready to apply the calling convention *)
    (* split up the stack frame into activation and parameter part *)
    assert (∃ a_r_adv, (af3 + 6)%a = Some a_r_adv) as [a_r_adv Ha_r_adv];
      [clear -Hbounds Hframe_delim Haf2 Haf3;destruct (af3 + 6)%a eqn:hsome;eauto;exfalso;solve_addr|].
    assert (∃ b_r_adv, (af3 + 7)%a = Some b_r_adv) as [b_r_adv Hb_r_adv];
      [clear -Hbounds Hframe_delim Haf2 Haf3;destruct (af3 + 7)%a eqn:hsome;eauto;exfalso;solve_addr|].
    assert (∃ wact wparams, wsstk = wact ++ wparams ∧ length wact = 7) as (wact & wparams & Hframe_eqapp & Hact_size).
    { clear -Hframe_length. repeat (destruct wsstk;[by inversion Hframe_length|]). destruct wsstk;inversion Hframe_length.
      exists [w;w0;w1;w2;w3;w4;w5]. eauto. }
    rewrite Hframe_eqapp. iDestruct (region_mapsto_split _ _ b_r_adv with "Hframe") as "[Hact Hparams]";auto.
    { clear -Ha_r_adv Hframe_delim Haf2 Haf3 Hb_r_adv. solve_addr. }
    { rewrite /region_size Hact_size. clear -Hb_r_adv Hframe_delim Haf2 Haf3. solve_addr. }
    iClear "Hcode". iPrologue_multi "Hprog" Hcont Hvpc link5.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code5.
    (* reconstruct registers except r_param1 r_param2 *)
    rewrite -!(delete_commute _ r_t4).
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t4]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
    rewrite -!(delete_commute _ r_t3) -!delete_insert_ne//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
    rewrite -!(delete_commute _ r_t2) -!delete_insert_ne//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
    rewrite -!(delete_commute _ r_t1) -!delete_insert_ne//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].

    assert (length wparams = 3) as Hparams_length.
    { rewrite Hframe_eqapp in Hframe_length. rewrite /= app_length Hact_size in Hframe_length. inversion Hframe_length. auto. }
    iRename "Hcode" into "Hscall".
    iPrologue_multi "Hprog" Hcont Hvpc link6.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code6.
    destruct_addr_list l_code4.
    apply contiguous_between_cons_inv_first in Hcont_code6 as Heq. subst l_code4.

    iApply (scallU_prologue_spec with "[- $HPC $Hact $Hscall $Hregs $Hr_stk]");
      [apply Hvpc_code5| | |apply Hcont_code5|auto..|apply Ha_r_adv|apply Hb_r_adv| |].
    { clear -Ha_param Haf3 Hbounds Hsize Hframe_delim Haf2. apply le_addr_withinBounds;solve_addr. }
    { clear -Ha_param Haf3 Hbounds Hsize Hframe_delim Haf2 Hb_r_adv. apply le_addr_withinBounds;solve_addr. }
    { repeat (apply not_elem_of_cons; split;auto). apply not_elem_of_nil. }
    { clear. set_solver. }
    { rewrite dom_insert_L !dom_delete_L !dom_insert_L Hdom. clear. simpl. set_solver. }
    { simpl. assert ((2 + 2 * 2%nat)%Z = 6%Z) as ->;[auto|].
      apply (contiguous_between_incr_addr _ 6 link5 a12) in Hcont_code6;auto. apply Hcont_code6. }
    iSplitL "Hr_t0";[eauto|].
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hregs & Hact & HscallU_prologue)".
    iDestruct "Hregs" as (rmap' [Hdom' Hcond]) "Hregs".

    (* pushU r_stk r_param1 *)
    destruct wparams;[inversion Hparams_length|].
    destruct (b_r_adv + 1)%a eqn:Hparam1;[|exfalso;clear -Hb_r_adv Haf3 Haf2 Ha_param Hparam1 Hframe_delim;solve_addr].
    iDestruct (region_mapsto_cons with "Hparams") as "[Hp1 Hparams]";[apply Hparam1|clear -Hb_r_adv Haf3 Haf2 Ha_param Hparam1 Hframe_delim;solve_addr|].
    iDestruct "Hcode" as "[Hi Hcode]".
    iApply (pushU_r_or_fail_spec with "[- $HPC $Hi $Hr_param1 $Hr_stk $Hp1]");
      [iCorrectPC link5 link6|auto|iContiguous_next_a Hcont_code6|apply Hparam1|].
    { clear -Hbounds Ha_param Hsize Hframe_delim Haf2 Haf3 Hparam1 Hb_r_adv Ha_r_adv.
      apply le_addr_withinBounds; solve_addr. }
    iSplitR;[iNext;by iRight|].
    iNext. iIntros "(Hmonocond & HPC & Hprog_done3 & Hr_stk & Hr_param1 & Hp1)".
    iDestruct "Hmonocond" as %Hmonocond.

    (* pushU r_stk r_param2 *)
    destruct wparams;[inversion Hparams_length|].
    destruct (a14 + 1)%a eqn:Hparam2;[|exfalso;clear -Hb_r_adv Haf3 Haf2 Ha_param Hparam1 Hparam2 Hframe_delim;solve_addr].
    iDestruct (region_mapsto_cons with "Hparams") as "[Hp2 Hparams]";[apply Hparam2|clear -Hb_r_adv Haf3 Haf2 Ha_param Hparam1 Hparam2 Hframe_delim;solve_addr|].
    iDestruct "Hcode" as "[Hi Hcode]".
    iApply (pushU_r_spec with "[- $HPC $Hi $Hr_param2 $Hr_stk $Hp2]");
      [iCorrectPC link5 link6|auto|iContiguous_next_a Hcont_code6|apply Hparam2|..].
    { clear -Hbounds Ha_param Hsize Hframe_delim Haf2 Haf3 Hparam1 Hb_r_adv Ha_r_adv.
      apply le_addr_withinBounds; solve_addr. }
    { simpl. intros _. clear -Hb_r_adv Hparam1. rewrite Z.leb_le. solve_addr. }
    iNext. iIntros "(HPC & Hi & Hr_stk & Hr_param2 & Hp2)". iCombine "Hi" "Hprog_done3" as "Hprog_done3".

    (* pushU r_stk r_t0 *)
    destruct wparams;[inversion Hparams_length|].
    destruct (a15 + 1)%a eqn:Hparam3;[|exfalso;clear -Hb_r_adv Haf3 Haf2 Ha_param Hparam1 Hparam2 Hparam3 Hframe_delim;solve_addr].
    iDestruct (region_mapsto_cons with "Hparams") as "[Hp3 Hparams]";[apply Hparam3|clear -Hb_r_adv Haf3 Haf2 Ha_param Hparam1 Hparam2 Hparam3 Hframe_delim;solve_addr|].
    iDestruct "Hcode" as "[Hi Hcode]".
    iApply (pushU_r_spec with "[- $HPC $Hi $Hr_t0 $Hr_stk $Hp3]");
      [iCorrectPC link5 link6|auto|iContiguous_next_a Hcont_code6|apply Hparam3|..].
    { clear -Hbounds Ha_param Hsize Hframe_delim Haf2 Haf3 Hparam1 Hparam2 Hparam3 Hb_r_adv Ha_r_adv.
      apply le_addr_withinBounds; solve_addr. }
    { simpl. intros _. clear -Hb_r_adv Hparam1 Hparam2. rewrite Z.leb_le. solve_addr. }
    iNext. iIntros "(HPC & Hi & Hr_stk & Hr_t0 & Hp3)". iCombine "Hi" "Hprog_done3" as "Hprog_done3".

    (* move r_param1 0 *)
    iPrologue "Hcode".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_param1]");
      [apply decode_encode_instrW_inv|iCorrectPC link5 link6|iContiguous_next_a Hcont_code6|].
    iEpilogue "(HPC & Hi & Hr_param1)"; iCombine "Hi" "Hprog_done3" as "Hprog_done3".
    (* move r_param2 0 *)
    iPrologue "Hcode".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_param2]");
      [apply decode_encode_instrW_inv|iCorrectPC link5 link6|iContiguous_next_a Hcont_code6|].
    iEpilogue "(HPC & Hi & Hr_param2)"; iCombine "Hi" "Hprog_done3" as "Hprog_done3".
    (* move r_t0 0 *)
    iPrologue "Hcode".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link5 link6|iContiguous_next_a Hcont_code6|].
    iEpilogue "(HPC & Hi & Hr_t0)"; iCombine "Hi" "Hprog_done3" as "Hprog_done3".
    (* jmp r_adv *)
    iPrologue "Hcode".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_adv]");
      [apply decode_encode_instrW_inv|iCorrectPC link5 link6|].

    (* prepare to use the ftlr by reconstructoring the register state *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_param2]") as "Hregs".
    { apply not_elem_of_dom. rewrite -Hdom'. clear. rewrite dom_insert_L !dom_delete_L !dom_insert_L. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_param1]") as "Hregs".
    { rewrite lookup_insert_ne//. apply not_elem_of_dom. rewrite -Hdom'. clear. rewrite dom_insert_L !dom_delete_L !dom_insert_L. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs".
    { rewrite !lookup_insert_ne//. apply not_elem_of_dom. rewrite -Hdom'. clear. rewrite dom_insert_L !dom_delete_L !dom_insert_L. set_solver. }

    match goal with |- context [ ([∗ map] k↦y ∈ ?r, k ↦ᵣ y)%I ] =>
                    set rmap2 := r
    end.

    set rmap3 := <[PC:=updatePcPerm (inr (g, Global, b, e, a'))]>
                 (<[PC:=inl 0%Z]>
                  (<[r_stk:=inr (URWLX, Directed, b_r_adv, estk, frame_end)]>
                   (<[r_adv:=inr (g, Global, b, e, a')]> rmap2))).
    match goal with |- context [ [[af3,b_r_adv]]↦ₐ[[?act]]%I ] =>
                    set actw := act
    end.
    set lframe : gmap Addr Word := list_to_map (zip (a_param :: (region_addrs af3 b_r_adv)) (inl 2%Z :: actw)).
    set W2 := <s[a15:=Monotemporary]s>
              (<s[a14:=Monotemporary]s>
               (<s[af2:=Monotemporary]s>
                (<s[b_r_adv:=Monotemporary]s>
                 (initialize_list (region_addrs bsec esec) (std_update_multiple (std_update_multiple (uninitialize W m) (a_param :: region_addrs af3 b_r_adv) (Monostatic lframe)) (af2 :: region_addrs b_r_adv frame_end) Revoked))))).

    destruct wparams;[|inversion Hparams_length]. iClear "Hparams".
    assert (a16 = frame_end) as ->.
    { clear -Hframe_delim Hb_r_adv Hparam1 Hparam2 Hparam3 Haf2 Haf3. solve_addr. }
    iAssert (⌜∀ x : Addr, (bsec <= x < esec)%a → W.1 !! x = Some Permanent ∨ W.1 !! x = Some Monotemporary⌝)%I
      as %Hsec_cond'.
    { iIntros (x Hin%elem_of_region_addrs). iRevert "Hsecret_cond". iClear "∗ #". iIntros "#Hregion_cond".
      iDestruct (big_sepL_elem_of with "Hregion_cond") as "Hx";[apply Hin|].
      iDestruct "Hx" as "[_ Hcond]".
      rewrite /region_state_pwl_mono /region_state_nwl /=. destruct (pwl l). iRight;auto.
      destruct p;auto. 1,2:iLeft;auto. iDestruct "Hcond" as "[Hcond | Hcond]";[iRight|iLeft];auto. }

    assert (related_sts_priv_world W W2) as Hrelatedpriv.
    { eapply related_sts_priv1;eauto. }

    iDestruct (jmp_or_fail_spec with "Hadv_valid") as "Hcont".
    destruct (decide (isCorrectPC (updatePcPerm (inr (g, Global, b, e, a'))))).
    2: { iRevert "Hcont". iClear "∗ #". iIntros "H". rewrite decide_False;auto.
         iEpilogue "(HPC & _)". iApply "H". iFrame. auto. }
    rewrite decide_True;[|auto]. iDestruct "Hcont" as (p' g' b' e' a'' Heq) "Hcont"; inversion Heq;subst.
    iDestruct ("Hcont" $! rmap3 W2 with "[]") as "Hexpr_now".
    { iSimpl. iPureIntro. apply Hrelatedpriv. }
    iEpilogue "(HPC & Hi & Hr_adv)"; iCombine "Hi" "Hprog_done3" as "Hprog_done3".

    (* setup the map for the frozen local stack frame *)
    (* Notice that we are not freezing the stack object! *)
    assert (NoDup (a_param :: region_addrs af3 b_r_adv)) as Hnodup.
    { apply NoDup_cons. split;try apply region_addrs_NoDup.
      intros Hin1%elem_of_region_addrs.
      clear -Hsome Haf2 Haf3 Hin1. exfalso. solve_addr. }

    (* Freeze the local stack frame *)
    iMod (region_revoked_cond_to_static _ lframe with "[Hf1 Hact $Hr $Hsts]") as "[Hsts Hr]".
    { apply revoke_condition_std_multiple_updates;auto. }
    { iApply big_sepL2_to_big_sepM. apply Hnodup.
      iSimpl.
      iDestruct (read_allowedU_inv _ a_param with "Hwstk_valid") as "Hcond3";
        [clear -Hbounds Hsize Ha_param Haf2;solve_addr|auto|].
      iSplitL "Hf1".
      { iExists (λ Wv, interp Wv.1 Wv.2). repeat iSplit;auto. iPureIntro. apply _. }
      iDestruct (read_allowedU_inv_range _ _ _ _ _ _ af3 b_r_adv with "Hwstk_valid") as "Hconds";auto.
      { clear -Hsome Haf2 Haf3 Hb_r_adv Hsize Hbounds Ha_param. solve_addr. }
      iDestruct (big_sepL2_length with "Hact") as %Hact_length.
      iDestruct (big_sepL2_to_big_sepL_l _ _ actw with "Hconds") as "Hconds'";auto.
      iDestruct (big_sepL2_sep with "[Hconds' Hact]") as "Hact";[iSplitL;[iFrame "Hact"|iFrame "Hconds'"]|].
      iApply (big_sepL2_mono with "Hact").
      iIntros (k y1 y2 Hin1 Hin2) "[Hy Hy1] /=".
      iDestruct "Hy1" as "Hcond". iExists _;iFrame.
      iPureIntro. apply _. }

    (* a bit of world cleanup: This part is quite tedious, and could maybe be delegated to lemma! *)
    assert (region_addrs a_param frame_end = a_param :: af2 :: region_addrs af3 b_r_adv ++ region_addrs b_r_adv frame_end) as Heqapp2.
    { rewrite region_addrs_cons;[rewrite Haf2|clear -Hframe_delim Haf2 Ha_param;solve_addr]. f_equiv. simpl.
      rewrite region_addrs_cons;[rewrite Haf3|clear -Hframe_delim Haf2 Ha_param;solve_addr]. f_equiv. simpl.
      apply region_addrs_split. clear -Hb_r_adv Haf2 Haf3 Hparam1 Hparam2 Hparam3;solve_addr. }
    rewrite Heqapp2.
    erewrite std_update_multiple_permutation.
    2: { apply elements_dom_list_to_map_zip;auto. apply _. simpl. rewrite region_addrs_length.
         clear -Hb_r_adv. rewrite /region_size. solve_addr. }
    assert (a_param :: af2 :: region_addrs af3 b_r_adv ++ region_addrs b_r_adv frame_end ≡ₚ
                    ((af2 :: region_addrs b_r_adv frame_end) ++ (a_param :: region_addrs af3 b_r_adv))) as Hperm'.
    { rewrite Permutation_app_comm. rewrite -(Permutation_middle _ _ a_param). simpl. auto. }
    erewrite (std_update_multiple_permutation _ _ _ Revoked);[|apply Hperm'].
    rewrite (std_update_multiple_app _ _ _ Revoked). rewrite std_update_multiple_overlap.
    rewrite std_update_multiple_disjoint.
    2: { assert (af2 :: region_addrs b_r_adv frame_end = [af2] ++ region_addrs b_r_adv frame_end) as ->;auto.
         assert (a_param :: region_addrs af3 b_r_adv = [a_param] ++ region_addrs af3 b_r_adv) as ->;auto.
         rewrite -(region_addrs_single a_param af2)//.  apply region_addrs_disjoint_skip_middle. auto. clear -Hb_r_adv. solve_addr. }

    (* we are ready to close the parts of the world that must stay valid: the two stack objects *)
    iAssert (⌜if pwl l then p = Directed else True⌝)%I as %Hmono.
    { destruct (pwl l) eqn:Hpwl. iDestruct (writeLocalAllowed_implies_local with "Hwsecret_valid") as %HH;auto.
      iPureIntro. destruct p;inversion HH;auto. auto. }
    iMod (close_stack_object with "Hsecret_cond Hsec_res Hsts Hr") as "(Hsts & Hr & #Hvalid)";
      [apply Hmono|auto|apply Hbesec_length|apply Hints|apply Hsecret_states|auto..].
    { clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim . apply elem_of_disjoint. intros x Hin.
      apply elem_of_disjoint in Hdisj. apply Hdisj in Hin as Hnin.
      apply not_elem_of_cons. split.
      { intros ->. apply Hnin. apply elem_of_region_addrs. solve_addr. }
      apply not_elem_of_app. split.
      { intros Hcontr%elem_of_region_addrs. apply Hnin. apply elem_of_region_addrs. solve_addr. }
      apply not_elem_of_cons. split.
      { intros ->. apply Hnin. apply elem_of_region_addrs. solve_addr. }
      intros Hcontr%elem_of_region_addrs. apply Hnin. apply elem_of_region_addrs. solve_addr. }

    match goal with |- context [ region ?W ] =>
                    set W1 := W
    end.

    (* we close the first parameter *)
    iDestruct (read_allowedU_inv _ b_r_adv with "Hwstk_valid") as "#Hb_r_adv_rel";[|auto|].
    { clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim. solve_addr. }
    iDestruct "Hb_r_adv_rel" as "Hb_r_adv_rel".
    iMod (update_region_revoked_monotemp with "[] Hsts Hr Hp1 [] Hb_r_adv_rel") as "[Hr Hsts]";[|auto|auto|..].
    { rewrite /W1 /= initialize_list_nin. rewrite lookup_insert_ne. rewrite std_sta_update_multiple_lookup_in_i//.
      apply elem_of_region_addrs. all: clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim Hdisj. 1,2: solve_addr.
      apply elem_of_disjoint in Hdisj. intros Hcontr. apply Hdisj in Hcontr.
      apply Hcontr. apply elem_of_region_addrs. solve_addr. }
    { iAlways. iIntros (W0 W' Hrelated) "Hv /=". destruct p.
      iApply (interp_monotone_nm with "[] [] Hv");auto. iPureIntro.
      clear -Hrelated. apply related_sts_pub_plus_priv_world. eapply related_sts_a_pub_plus_world. eauto.
      iApply (interp_monotone_nm with "[] [] Hv");auto. iPureIntro.
      clear -Hrelated. apply related_sts_pub_plus_priv_world. eapply related_sts_a_pub_plus_world. eauto.
      iApply (interp_monotone_a with "[] Hv"). iPureIntro.
      clear -Hmonocond Hmono2 Hmono Hrelated Hra. simpl in *.
      assert (isU l = false) as ->;[destruct l;auto;inversion Hra|].
      eapply related_sts_a_weak_world;[|eauto]. revert Hmonocond; rewrite Z.leb_le =>Hmonocond.
      destruct l;inversion Hra;apply Hmonocond;auto. }

    (* our new stack object at addess af2: we go from Revoked to Monotemporary *)
    iDestruct (read_allowedU_inv _ af2 with "Hwstk_valid") as "#Hf2_rel";[|auto|].
    { clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim. solve_addr. }
    iMod (update_region_revoked_monotemp with "[] Hsts Hr Hf2 [] Hf2_rel") as "[Hr Hsts]";[|auto|auto|..].
    { rewrite lookup_insert_ne. 2: clear -Hb_r_adv Haf3;solve_addr. rewrite /W1 /= initialize_list_nin. rewrite lookup_insert//.
      apply elem_of_disjoint in Hdisj. intros Hcontr. apply Hdisj in Hcontr.
      apply Hcontr. apply elem_of_region_addrs. clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim. solve_addr. }
    { iAlways. iIntros (W0 W' _) "_ /=". rewrite !fixpoint_interp1_eq. eauto. }
    { iSimpl. rewrite !fixpoint_interp1_eq. eauto. }

    (* we close the second parameter *)
    iDestruct (read_allowedU_inv _ a14 with "Hwstk_valid") as "#Ha14_rel";[|auto|].
    { clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim Hparam1. solve_addr. }
    iMod (update_region_revoked_monotemp with "[] Hsts Hr Hp2 [] Ha14_rel") as "[Hr Hsts]";[|auto|auto|..].
    { rewrite lookup_insert_ne;[|clear -Hb_r_adv Hparam1 Haf3;solve_addr].
      rewrite lookup_insert_ne;[|clear -Hb_r_adv Hparam1;solve_addr].
      rewrite /W1 /= initialize_list_nin. rewrite lookup_insert_ne. rewrite std_sta_update_multiple_lookup_in_i//.
      apply elem_of_region_addrs. all: clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim Hdisj Hparam1. 1,2: solve_addr.
      apply elem_of_disjoint in Hdisj. intros Hcontr. apply Hdisj in Hcontr.
      apply Hcontr. apply elem_of_region_addrs. solve_addr. }
    { iModIntro. iIntros (W0 W' Hrelated) "Hv /=".
      iApply (interp_monotone_a with "[] Hv"). iPureIntro.
      clear -Hparam1 Hb_r_adv Hrelated.
      eapply related_sts_a_weak_world;[|eauto]. solve_addr. }
    { iSimpl. rewrite !fixpoint_interp1_eq. iSimpl. rewrite region_addrs_single;auto. iSimpl.
      iSplit;auto. iFrame "Hf2_rel". rewrite /region_state_pwl_mono. rewrite lookup_insert. auto. }

    (* We are almost ready to apply the expression relation of the adversary *)
    (* We have two remaining steps: first we must show that the continuation is in the value relation *)
    (* Next we must close the final parameter and apply the relation on the almost empty register state, where in particular
       we must show the validity of the current stack register *)

    (* In order to begin with step one, we must first close our open invariants *)
    iMod ("Hcls" with "[$Hown Hreqglob HprepstackU Hprog_done Hcheckra Hcheckints
                        Hprog_done2 HscallU_prologue Hprog_done3 Hcode Hprog]")
      as "Hown".
    { iNext. iApply (big_sepL2_app with "Hreqglob").
      iApply (big_sepL2_app with "HprepstackU").
      iApply (big_sepL2_app with "[Hprog_done]"). iFrame. done.
      iApply (big_sepL2_app with "Hcheckra").
      iApply (big_sepL2_app with "Hcheckints").
      iApply (big_sepL2_app with "[Hprog_done2]"). iDestruct "Hprog_done2" as "($&$&$&$&$&$&$&$)". done.
      iApply (big_sepL2_app with "HscallU_prologue").
      iApply (big_sepL2_app with "[Hprog_done3 Hcode]"). iDestruct "Hprog_done3" as "($&$&$&$&$&$&$)". done.
      iFrame. }

    (* Let's close the final stack parameter address *)
    iDestruct (read_allowedU_inv _ a15 with "Hwstk_valid") as "#Ha15_rel";[|auto|].
    { clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim Hparam1 Hparam2. solve_addr. }
    iMod (update_region_revoked_monotemp_updated with "[] Hsts Hr Hp3 [] Ha15_rel") as "[Hr Hsts]";[|auto|auto|..].
    { rewrite lookup_insert_ne;[|clear -Hb_r_adv Hparam1 Hparam2 Haf3;solve_addr].
      rewrite lookup_insert_ne;[|clear -Hb_r_adv Hparam1 Hparam2 Haf3;solve_addr].
      rewrite lookup_insert_ne;[|clear -Hb_r_adv Hparam1 Hparam2;solve_addr].
      rewrite /W1 /= initialize_list_nin. rewrite lookup_insert_ne. rewrite std_sta_update_multiple_lookup_in_i//.
      apply elem_of_region_addrs. all: clear -Hdisj Hsize Hbounds Hb_r_adv Ha_param Haf2 Haf3 Hframe_delim Hdisj Hparam1 Hparam2. 1,2: solve_addr.
      apply elem_of_disjoint in Hdisj. intros Hcontr. apply Hdisj in Hcontr.
      apply Hcontr. apply elem_of_region_addrs. solve_addr. }
    { iModIntro. iIntros (W0 W' Hrelated) "Hv /=".
      iApply (interp_monotone_a with "[] Hv"). iPureIntro.
      clear -Hparam1 Hparam2 Hb_r_adv Hrelated.
      eapply related_sts_a_weak_world;[|eauto]. solve_addr. }
    { (* We have now come to the interesting
         part: we must show that the callback
         is valid in a monotone future world
         with respect to b_r_dv. Note that we
         are showing it is valid in a world
         where the parameter is not yet monotemporary,
         this is fine in this case since we do not
         care about it anymore *)
      iSimpl. rewrite (fixpoint_interp1_eq _ (inr (E, Directed, bstk, b_r_adv, af3))). iModIntro.
      iIntros (r' W' Hrelated). iNext.
      iIntros "(#[Hall Hregs_valid] & Hregs & Hr & Hsts & Hown)".
      iSplit;auto. iDestruct "Hall" as %Hr_all. iClear "Hall".
      (* extract some registers *)
      iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]"; [rewrite lookup_insert;eauto|].
      rewrite delete_insert_delete.
      (* we will first have to go through the activation record *)
      (* let's open the static region of W' *)
      (* we must therefore first attest that the local stack frame is still static in W' *)
      assert (std W' !! af3 = Some (Monostatic lframe)) as Hlframe'.
      { eapply related_sts_pub_a_world_static. 3: apply Hrelated.
        - clear -Hsize Hb_r_adv Haf2 Haf3 Ha_param Hframe_delim Hparam1 Hparam2 Hparam3 Hdisj.
          repeat (rewrite lookup_insert_ne;[|solve_addr]). apply elem_of_disjoint in Hdisj.
          rewrite initialize_list_nin /=. rewrite lookup_insert_ne;[|clear -Haf3;solve_addr].
          rewrite std_sta_update_multiple_lookup_same_i. rewrite lookup_insert_ne;[|clear -Haf3 Haf2;solve_addr].
          apply std_sta_update_multiple_lookup_in_i. 1,2: rewrite elem_of_region_addrs.
          1,2:clear -Hb_r_adv;solve_addr. intros Hcontr%Hdisj. apply Hcontr, elem_of_region_addrs. solve_addr.
        - clear -Hb_r_adv. solve_addr. }
      (* in order to be able to uninitialize the frozen world, it is conveninent to first
         uninitialize the region above the lowest address of the frame *)
      iDestruct (full_sts_monostatic_all with "Hsts Hr") as %Hall_mono;[apply Hlframe'|].
      iMod (uninitialize_region_keep _ bstk with "[$Hsts $Hr]") as (m' Hmcond') "[Hsts [Hr #Hvalids'] ]".

      (* then we can open the static region *)
      iMod (region_open_monostatic _ _ af3 with "[$Hr $Hsts]") as "(Hr & Hsts & Hstates & Hframe & %)".
      { rewrite uninitialize_std_sta_not_elem_of_lookup. apply Hlframe'. intros Hcontr%elem_of_gmap_dom%Hmcond'.
        destruct Hcontr as [Hcontr _]. rewrite Hlframe' in Hcontr. done. }
      rewrite /static_resources.
      (* cleanup the resources *)
      iAssert (a_param ↦ₐ inl 2%Z ∗ [[af3,b_r_adv]]↦ₐ[[ actw ]])%I with "[Hframe]" as "[Ha_param Hact]".
      { iDestruct (read_allowedU_inv_range _ _ _ _ _ _ af3 b_r_adv with "Hwstk_valid") as "Hconds";[|auto|].
        { clear -Hsize Hb_r_adv Haf2 Haf3 Ha_param. solve_addr. }
        iDestruct (big_sepM_to_big_sepL2 with "Hframe") as "Hframe".
        { apply NoDup_cons. split;[|apply region_addrs_NoDup]. rewrite elem_of_region_addrs.
          clear -Haf2 Haf3. solve_addr. }
        { rewrite /= region_addrs_length /region_size. clear -Hb_r_adv. solve_addr. }
        iDestruct "Hframe" as "[Ha Hframe]". iSplitL "Ha".
        - iDestruct "Ha" as (φ') "[#Hrel Ha]".
          iDestruct (read_allowedU_inv _ a_param with "Hwstk_valid") as "Hrel_a_param";[|auto|].
          { clear -Ha_param Hsize. solve_addr. } auto.
        - iDestruct (big_sepL2_to_big_sepL_l _ _ actw with "Hconds") as "Hconds'".
          { rewrite /= region_addrs_length /region_size. clear -Hb_r_adv. solve_addr. }
          iDestruct (big_sepL2_sep with "[$Hframe $Hconds']") as "Hframe".
          iApply (big_sepL2_mono with "Hframe").
          iIntros (k y1 y2 Hy1 Hy2) "[Hrel1 Hrel2]".
          iDestruct "Hrel1" as (φ0) "[#Hrel1 Ha]". iFrame. }
      (* apply the activation record *)
      specialize (Hr_all r_t1) as Hr_t1; specialize (Hr_all r_stk) as Hr_stk;
        destruct Hr_t1 as [w1' Hr_t1]; destruct Hr_stk as [wstk' Hr_stk].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; [rewrite lookup_delete_ne//|].
      iDestruct (big_sepM_delete _ _ r_stk with "Hregs") as "[Hr_stk Hregs]"; [rewrite !lookup_delete_ne//|].
      iApply (scallU_epilogue_spec with "[- $HPC $Hact $Hr_t1 $Hr_stk]");[| |auto..].
      { intros mid Hmid. constructor;auto. clear -Hmid Ha_param Haf2 Haf3 Hb_r_adv. solve_addr. }
      { clear -Ha_param Haf2 Haf3 Hb_r_adv Ha_r_adv Hsize. apply le_addr_withinBounds;solve_addr. }
      { iContiguous_next_a Hcont_code6. }
      { clear -Ha_r_adv Hb_r_adv. solve_addr. }
      { eapply (isCorrectPC_contiguous_range _ _ _ _ _ _ _ _ Hvpc_code6); eauto. repeat econstructor. }
      iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hact)".
      iDestruct "Hr_t1" as (rt1w) "Hr_t1".

      (* Next we continue the execution of the callback *)
      (* first we must open the invariant containing the program *)
      iMod (na_inv_acc with "Hlse_prog Hown") as "(>Hprog & Hown & Hcls)";auto.
      rewrite /stack_object_passing /stack_object_passing_instrs.
      match goal with |- context [ ([∗ list] a_i;w_i ∈ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5 ++ ?l6 ++ ?l7 ++ ?l8 ++ l_rest6);(?i1 ++ ?i2 ++ ?i3 ++ ?i4 ++ ?i5 ++ ?i6 ++ ?i7 ++ ?i8 ++ ?i_rest),_)%I ] =>
                      set lprev := (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7); set lcur := l8;
                      set iprev := (i1 ++ i2 ++ i3 ++ i4 ++ i5 ++ i6 ++ i7); set icur := i8; set irest := i_rest
      end.
      match goal with |- context [ ([∗ list] a_i;w_i ∈ ?l_addrs;?i_instrs, _)%I ] =>
                      set laddrs := l_addrs; set instrs := i_instrs
      end.
      assert (laddrs = lprev ++ (lcur ++ l_rest6)) as ->;[rewrite /laddrs /lprev /lcur;repeat rewrite -app_assoc //|].
      assert (instrs = iprev ++ (icur ++ irest)) as ->;[rewrite /instrs /iprev /lcur /irest;repeat rewrite -app_assoc //|].
      iDestruct (big_sepL2_app' with "Hprog") as "[Hprog_done Hprog]".
      { by rewrite /lprev /iprev /= !app_length /= !app_length /=
                   Hlength_code Hlength_code0 Hlength_code2 Hlength_code3 Hlength_code5 /=. }
      iDestruct (big_sepL2_app' with "Hprog") as "[Hcode Hprog]".
      { by rewrite /lcur /icur /=. }
      do 7 (iDestruct "Hcode" as "[Hi Hcode]";iCombine "Hi" "Hprog_done" as "Hprog_done").

      (* lea r_stk -6 *)
      assert (a_r_adv + (-6) = Some af3)%a as Hlea;[clear -Ha_r_adv;solve_addr|].
      iPrologue "Hcode".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_stk]");
        [apply decode_encode_instrW_inv|iCorrectPC link5 link6| |apply Hlea|auto..].
      { eapply contiguous_between_last;[apply Hcont_code6|auto]. }
      { simpl. clear -Ha_r_adv. solve_addr. }
      iEpilogue "(HPC & Hi & Hr_stk)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      iClear "Hcode".

      (* loadU r_t1 r_stk -2 *)
      iPrologue_multi "Hprog" Hcont Hvpc link7.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code7.
      destruct_addr_list l_code4.
      iPrologue "Hcode". iClear "Hcode". clear Heq.
      apply contiguous_between_cons_inv_first in Hcont_code7 as Heq. subst l_code4.
      specialize (Hr_all r_adv) as Hr_adv;destruct Hr_adv as [wadv Hr_adv].
      iDestruct (big_sepM_delete _ _ r_adv with "Hregs") as "[Hr_adv Hregs]"; [rewrite !lookup_delete_ne//|].
      iApply (wp_loadU_success_any with "[$HPC $Hi $Hr_adv $Hr_stk $Ha_param]");
        [apply decode_encode_instrW_inv|iCorrectPC link6 link7|auto..|clear;lia|].
      { clear -Hsize Ha_param Haf3 Haf2. solve_addr. }
      { clear -Hsize Ha_param Haf3 Haf2. apply le_addr_withinBounds;solve_addr. }
      { eapply contiguous_between_last. apply Hcont_code7. auto. }
      { clear -Hsize Ha_param Haf3 Haf2. solve_addr. }
      iEpilogue "(HPC & Hr_adv & Hprog_done0 & Hr_stk & Ha_param)".

      (* assert r_t1 2 *)
      iPrologue_multi "Hprog" Hcont Hvpc link8.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code8.
      iMod (na_inv_acc with "Htable Hown") as "([Hpc_b Ha_entry] & Hcls' & Hown)";[auto|solve_ndisj|].
      specialize (Hr_all r_t2) as Hr_t2; specialize (Hr_all r_t3) as Hr_t3;
        destruct Hr_t2 as [w2' Hr_t2]; destruct Hr_t3 as [w3' Hr_t3].
      iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]"; [rewrite !lookup_delete_ne//|].
      iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]"; [rewrite !lookup_delete_ne//|].
      iApply (assert_r_z_success with "[- $HPC $Hcode $Hpc_b $Ha_entry $Hr_adv]");
        [apply Hvpc_code8|apply Hcont_code8|auto..|eauto|].
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|].
      iNext. iIntros "(Hr_t1 & Hr_t2 & Hr_t3 & Hr_adv & HPC & Hassert & Hpc_b & Ha_entry)".
      iMod ("Hown" with "[$Hcls' $Hpc_b $Ha_entry]") as "Hown".

      (* let's close the frozen stack frame to an uninitialized state *)
      iMod (region_close_monostatic_to_uninitialized with "[$Hsts $Hr Hact $Hstates Ha_param]") as "[Hsts Hr]".
      { intros x y [Hx%list_to_map_lookup_is_Some Hle].
        rewrite fst_zip in Hx. 2: { simpl. rewrite region_addrs_length /region_size. clear -Hb_r_adv. solve_addr. }
        clear -Hmcond' Hx Hle Haf3 Haf2 Ha_param. destruct (m' !! y) eqn:Hsome.
        - destruct Hmcond' with y as [ [Hmono Hle'] _];eauto.
          rewrite (uninitialize_std_sta_lookup_in _ _ _ w);auto.
        - rewrite uninitialize_std_sta_None_lookup//. intros Hcontr.
          destruct Hmcond' with y as [_ [Hmono Hle'] ];eauto;[|congruence].
          split;auto. apply elem_of_cons in Hx as [-> | Hx%elem_of_region_addrs];auto;solve_addr. }
      { iApply big_sepL2_to_big_sepM. auto. iSimpl. iSplitL "Ha_param".
        - iDestruct (read_allowedU_inv _ a_param with "Hwstk_valid")
            as  "Hrel_a_param";[|auto|].
          { clear -Ha_param Hsize. solve_addr. } iExists _.
          iFrame "Ha_param Hrel_a_param". iPureIntro. apply _.
        - iDestruct (read_allowedU_inv_range _ _ _ _ _ _ af3 b_r_adv with "Hwstk_valid") as "Hconds";[|auto|].
        { clear -Hsize Hb_r_adv Haf2 Haf3 Ha_param. solve_addr. }
        iDestruct (big_sepL2_to_big_sepL_l _ _ actw with "Hconds") as "Hconds'".
        { rewrite /= region_addrs_length /region_size. clear -Hb_r_adv. solve_addr. }
        iDestruct (big_sepL2_sep with "[$Hact $Hconds']") as "Hframe".
        iApply (big_sepL2_mono with "Hframe").
        iIntros (k y1 y2 Hy1 Hy2) "(Hy & Hconds)".
        iExists  _. iFrame. iPureIntro. apply _. }


      (* once the assertion has succeeded, the final step is to return to the caller *)

      (* multiple steps is required: we must clear all registers so that no pointers are leaked,
         and we must load the return pointer from the stack *)

      (* in order to load the return pointer, we have to assert that the address that stores it
         is uninitialized, and that either the word it points to was valid in W, or it is valid in W'
         We must then prove that it is still valid in Wfinal *)

      (* in either case, we should be able to infer validity of the word it contains, and that it is
         monotone with respect to the address it is stored in *)

      (* Note an added difficulty: unlike the rest of the frame, the stack object parameter may overlap
         with the address of the return pointer *)
      iDestruct (open_parameter lframe with "Hwstk_valid Hvalids Hvalids'") as (wret Hwret_in) "Hret_val";
        [| |apply Hdisj|apply Hsize|apply Hbounds|apply Ha_param|
         apply Haf2|apply Haf3|apply Hb_r_adv|apply Hparam1|
         apply Hparam2| |apply Hmcond|apply Hmcond'|apply Hrelated|]. eauto. eauto.
      { simpl. rewrite region_addrs_length /region_size. clear -Hb_r_adv. solve_addr. }

      iDestruct (read_allowedU_inv _ bstk with "Hwstk_valid") as "#Hbstk_rel";[|auto..|].
      { clear -Hsize. solve_addr. }
      iDestruct (region_open_uninitialized with "[$Hbstk_rel $Hr $Hsts]") as "(Hr & Hsts & Hstate & Hbstk)";
        [apply Hwret_in|..].

      iPrologue_multi "Hprog" Hcont Hvpc link9.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code9.
      destruct_addr_list l_code5. apply contiguous_between_cons_inv_first in Hcont_code9 as Heq. subst l_code5.

      iPrologue "Hcode". iClear "Hcode".
      iApply (wp_loadU_success_any with "[$HPC $Hi $Hr_t1 $Hr_stk $Hbstk]");
        [apply decode_encode_instrW_inv|iCorrectPC link8 link9|auto| | |apply Hlink9|..].
      { clear -Ha_param Haf2 Haf3 Hsize. solve_addr. }
      { clear -Ha_param Haf2 Haf3 Hsize. apply le_addr_withinBounds;solve_addr. }
      { clear -Ha_param Haf2 Haf3 Hsize. solve_addr. }
      { clear. lia. }
      iEpilogue "(HPC & Hr_t1 & Hprog_done1 & Hr_stk & Hbstk)".

      iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -delete_insert_ne//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -!(delete_insert_ne _ r_adv)//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_adv]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -!(delete_insert_ne _ r_stk)//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_stk]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete.

      iPrologue_multi "Hprog" Hcont Hvpc link10.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code10.
      iApply (rclear_spec_gmap with "[- $HPC $Hcode $Hregs]");
      [apply Hcont_code10|apply not_elem_of_list; constructor|
       |apply Hvpc_code10| |].
      { clear -Hlength_code10 Hcont_code10. rewrite rclear_length in Hlength_code10.
        assert (r_t2 ∈ (list_difference all_registers [PC; r_t1])) as Hin.
        { apply elem_of_list_difference. split;[apply all_registers_correct|set_solver]. }
        destruct l_code5.
        { simpl in Hlength_code10. by rewrite (nil_length_inv (list_difference all_registers [PC; r_t1])) in Hin;auto. }
        apply contiguous_between_cons_inv_first in Hcont_code10. subst;auto. }
      { clear - Hr_all. rewrite !dom_insert_L !dom_delete_L. apply regmap_full_dom in Hr_all as ->. set_solver. }
      iNext. iIntros "(HPC & Hrmap & Hrclear)".
      iDestruct "Hrmap" as (rmap4) "(Hregs & #Heq & #Hreg_spec)".
      iDestruct "Heq" as %Hdom''. iDestruct "Hreg_spec" as %Hreg_spec.

      (* extract the validity of wret from the persistent information of m'.
         we here need to distinguish between the two cases:
         1) the return capability did not change
         2) the return capability was changed but is valid in the new world (no need to reinstate invariants) *)

      destruct_addr_list l_rest10. apply contiguous_between_cons_inv_first in Hcont as Heq. subst l_rest10.
      iPrologue "Hprog". iClear "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t1]");
        [apply decode_encode_instrW_inv|iCorrectPC link10 a_last|].

      assert (related_sts_a_world W' (override_uninitialize lframe (uninitialize W' m')) bstk) as Hrelated'.
      { eapply related_sts_a_trans_world; [|eapply related_sts_pub_world_monostatic_to_uninitialized].
        - apply uninitialize_related_pub_a;auto.
        - intros x Hin%elem_of_gmap_dom. apply Hall_mono in Hin. rewrite /monostatic in Hin.
          destruct (W'.1 !! x) eqn:Hin';inversion Hin;subst r.
          rewrite uninitialize_std_sta_spec Hin'. destruct (m' !! x);auto.
        - clear -Hb_r_adv Ha_param Haf2 Haf3. intros a' Hx%list_to_map_lookup_is_Some.
          rewrite fst_zip in Hx. apply elem_of_cons in Hx as [-> | [Hx Hx']%elem_of_region_addrs]. 1,2: solve_addr.
          simpl. rewrite region_addrs_length /region_size. solve_addr. }

      iDestruct "Hret_val" as "[Hret_val | Hret_val]".
      - set (maddrs := (filter (λ a, a < bstk)%a (elements (dom (gset Addr) m)))).
        set (Wfinal := initialize_list maddrs (override_uninitialize lframe (uninitialize W' m'))).
        assert (related_sts_a_world W Wfinal bstk) as Hrelated2.
        { eapply related_sts_pub_a1;eauto. }
        iDestruct ("Hret_val" $! Wfinal with "[]") as "Hret_val_final".
        { iPureIntro. apply Hrelated2. }
        iDestruct (jmp_or_fail_spec with "Hret_val_final") as "Hcont'".
        destruct (decide (isCorrectPC (updatePcPerm wret))).
        2: { iEpilogue "(HPC & Hi & Hr_t1)". iApply "Hcont'". iFrame "HPC". iIntros (Hcontr);inversion Hcontr. }
        iDestruct ("Hcont'") as (pret gret bret eret aret ->) "Hcont'".
        iDestruct ("Hcont'" $! (<[PC:=inl 0%Z]> (<[r_t1 := inr (pret, gret, bret, eret, aret)]> rmap4))
                           Wfinal with "[]") as "Hcont_final".
        { iClear "#". clear.
          destruct gret;simpl;iPureIntro;
            [apply related_sts_priv_refl_world..|
                   apply related_sts_a_refl_world]. }
        iEpilogue "(HPC & Hi & Hr_t1)".
        iMod ("Hcls" with "[$Hown Hprog_done Hprog_done0 Hassert Hprog_done1 Hrclear Hi]") as "Hown".
        { iNext. rewrite /lcur /icur. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$)". iSplitR;[auto|].
          iFrame. auto. }
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs".
        { apply not_elem_of_dom. rewrite Hdom''. rewrite elem_of_list_to_set. apply not_elem_of_list. repeat constructor. }
        iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
        { rewrite lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom''. rewrite elem_of_list_to_set.
          apply not_elem_of_list. repeat constructor. }
        rewrite -(insert_insert _ PC (updatePcPerm _) (inl 0%Z)).
        iDestruct (region_close_uninit with "[$Hstate $Hr $Hbstk $Hbstk_rel]") as "Hr". auto.
        iMod (initialize_list_region _ maddrs with "[$Hsts $Hr]") as "[Hsts Hr]".
        { iApply big_sepL_forall.
          iIntros (k x Hin). iModIntro. assert (x ∈ maddrs) as Hin';[apply elem_of_list_lookup;eauto|].
          apply elem_of_list_filter in Hin' as [Hle Hin'].
          apply elem_of_elements,elem_of_gmap_dom in Hin' as [v Hv].
          iDestruct (big_sepM_lookup with "Hvalids") as (φ' Hpers') "[Hx Hrelx]";[apply Hv|].
          iExists φ',v. iDestruct "Hx" as "[Hmonox Hφx]". iFrame "#".
          destruct Hmcond with x as [ [Hmonox _] _];[eauto|].
          iSplit.
          { iPureIntro. clear -Hle Hv Hmonox Hrelated Hrelated' Ha_param Haf2 Haf3
                                     Hb_r_adv Hmcond Hmcond' Hparam1 Hparam2 Hparam3.
              assert (lframe !! x = None) as Hnone.
              { apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_cons.
                rewrite elem_of_region_addrs. 2: rewrite /= region_addrs_length /region_size.
                split. all: clear -Hle Ha_param Haf2 Haf3 Hb_r_adv; solve_addr. }
              destruct (decide (x ∈ region_addrs bsec esec)).
              - assert (W1.1 !! x = Some Monotemporary) as Hin'.
                { rewrite /W1. apply initialize_list_in with v;auto.
                  rewrite lookup_insert_ne;[|solve_addr].
                  rewrite std_sta_update_multiple_lookup_same_i;[|rewrite elem_of_region_addrs;solve_addr].
                  rewrite lookup_insert_ne;[|solve_addr].
                  rewrite std_sta_update_multiple_lookup_same_i;[|rewrite elem_of_region_addrs;solve_addr].
                  rewrite (uninitialize_std_sta_lookup_in _ _ _ v);auto. }
                apply related_sts_pub_a_world_monotemporary with (i:=x) in Hrelated.
                rewrite override_uninitialize_std_sta_lookup_none;auto.
                rewrite (uninitialize_std_sta_None_lookup);auto.
                apply eq_None_not_Some. intros [_ Hcontr]%Hmcond'. clear -Hcontr Hle. solve_addr.
                clear -Hin'. rewrite /std_update /=.
                destruct (decide (a15 = x));[subst;rewrite lookup_insert//|rewrite lookup_insert_ne//].
                destruct (decide (a14 = x));[subst;rewrite lookup_insert//|rewrite lookup_insert_ne//].
                destruct (decide (af2 = x));[subst;rewrite lookup_insert//|rewrite lookup_insert_ne//].
                destruct (decide (b_r_adv = x));[subst;rewrite lookup_insert//|rewrite lookup_insert_ne//].
                clear -Hle Ha_param Haf2 Haf3 Hb_r_adv;solve_addr.
              - assert (W1.1 !! x = Some (Uninitialized v)) as Hin'.
                { rewrite /W1. rewrite initialize_list_nin;auto.
                  rewrite lookup_insert_ne;[|solve_addr].
                  rewrite std_sta_update_multiple_lookup_same_i;[|rewrite elem_of_region_addrs;solve_addr].
                  rewrite lookup_insert_ne;[|solve_addr].
                  rewrite std_sta_update_multiple_lookup_same_i;[|rewrite elem_of_region_addrs;solve_addr].
                  rewrite (uninitialize_std_sta_lookup_in _ _ _ v);auto. }
                apply related_sts_pub_a_world_uninitialized with (i:=x) (w:=v) in Hrelated.
                rewrite override_uninitialize_std_sta_lookup_none;auto.
                2: { clear -Hle Ha_param Haf2 Haf3 Hb_r_adv Hparam1 Hparam2 Hparam3 Hin'.
                     repeat (rewrite lookup_insert_ne;[|solve_addr]). auto. }
                rewrite (uninitialize_std_sta_None_lookup);[destruct Hrelated;auto|].
                apply eq_None_not_Some. intros [_ Hcontr]%Hmcond'. clear -Hcontr Hle. solve_addr.
                clear -Hle Ha_param Haf2 Haf3 Hb_r_adv;solve_addr. }
          repeat iSplit;auto.
          all: iApply ("Hmonox" with "[] Hφx").
          all: iPureIntro.

          apply related_sts_a_weak_world with bstk. clear -Hle;solve_addr. apply Hrelated2.
        }
        iDestruct ("Hcont_final" with "[$Hr $Hsts $Hown $Hregs]") as "[_ Hφ]".
        { iSplit.
          - iPureIntro. clear -Hdom''. intros x. simpl.
            destruct (decide (x = PC));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
            destruct (decide (x = r_t1));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
            apply elem_of_gmap_dom. rewrite Hdom'' elem_of_list_to_set.
            apply elem_of_list_difference. split;[apply all_registers_correct|set_solver].
          - iIntros (r Hne). rewrite /RegLocate. rewrite lookup_insert_ne//.
            destruct (decide (r = r_t1));[subst;rewrite lookup_insert|]. iFrame "Hret_val_final".
            rewrite lookup_insert_ne// Hreg_spec. iClear "#". rewrite fixpoint_interp1_eq. done.
            rewrite Hdom'' elem_of_list_to_set.
            apply elem_of_list_difference. split;[apply all_registers_correct|clear -Hne n;set_solver]. }
        iApply (wp_wand with "Hφ").
        iIntros (v) "Hv". iIntros (Hv).
        iDestruct ("Hv" $! Hv) as (r W'') "(Hregval & Hregs & #Hrelated & Hown & Hsts & Hr)".
        iExists r,W''. iFrame. iDestruct "Hrelated" as %Hrelated''. iPureIntro.
        eapply related_sts_a_priv_trans_world. 2: apply Hrelated''.
        eapply related_sts_a_trans_world;[|apply related_sts_pub_a_world;apply initialize_list_related_pub].
        apply Hrelated'.
      - iDestruct ("Hret_val" $! (override_uninitialize lframe (uninitialize W' m')) with "[]") as "Hret_val_final".
        { iPureIntro. apply Hrelated'. }
        iDestruct (jmp_or_fail_spec with "Hret_val_final") as "Hcont'".
        destruct (decide (isCorrectPC (updatePcPerm wret))).
        2: { iEpilogue "(HPC & Hi & Hr_t1)". iApply "Hcont'". iFrame "HPC". iIntros (Hcontr);inversion Hcontr. }
        iDestruct ("Hcont'") as (pret gret bret eret aret ->) "Hcont'".
        iDestruct ("Hcont'" $! (<[PC:=inl 0%Z]> (<[r_t1 := inr (pret, gret, bret, eret, aret)]> rmap4))
                           (override_uninitialize lframe (uninitialize W' m')) with "[]") as "Hcont_final".
        { iClear "#". clear.
          destruct gret;simpl;iPureIntro;
            [apply related_sts_priv_refl_world..|
                   apply related_sts_a_refl_world]. }
        iEpilogue "(HPC & Hi & Hr_t1)".
        iMod ("Hcls" with "[$Hown Hprog_done Hprog_done0 Hassert Hprog_done1 Hrclear Hi]") as "Hown".
        { iNext. rewrite /lcur /icur. iDestruct "Hprog_done" as "($&$&$&$&$&$&$&$&$)". iSplitR;[auto|].
          iFrame. auto. }
        iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs".
        { apply not_elem_of_dom. rewrite Hdom''. rewrite elem_of_list_to_set. apply not_elem_of_list. repeat constructor. }
        iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
        { rewrite lookup_insert_ne//. apply not_elem_of_dom. rewrite Hdom''. rewrite elem_of_list_to_set.
          apply not_elem_of_list. repeat constructor. }
        rewrite -(insert_insert _ PC (updatePcPerm _) (inl 0%Z)).
        iDestruct ("Hcont_final" with "[Hr $Hsts $Hown $Hregs Hstate Hbstk]") as "[_ Hφ]".
        { iDestruct (region_close_uninit with "[$Hstate $Hr $Hbstk $Hbstk_rel]") as "Hr". auto. iFrame "Hr".
          iSplit.
          - iPureIntro. clear -Hdom''. intros x. simpl.
            destruct (decide (x = PC));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
            destruct (decide (x = r_t1));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
            apply elem_of_gmap_dom. rewrite Hdom'' elem_of_list_to_set.
            apply elem_of_list_difference. split;[apply all_registers_correct|set_solver].
          - iIntros (r Hne). rewrite /RegLocate. rewrite lookup_insert_ne//.
            destruct (decide (r = r_t1));[subst;rewrite lookup_insert|]. iFrame "Hret_val_final".
            rewrite lookup_insert_ne// Hreg_spec. iClear "#". rewrite fixpoint_interp1_eq. done.
            rewrite Hdom'' elem_of_list_to_set.
            apply elem_of_list_difference. split;[apply all_registers_correct|clear -Hne n;set_solver]. }
        iApply (wp_wand with "Hφ").
        iIntros (v) "Hv". iIntros (Hv).
        iDestruct ("Hv" $! Hv) as (r W'') "(Hregval & Hregs & #Hrelated & Hown & Hsts & Hr)".
        iExists r,W''. iFrame. iDestruct "Hrelated" as %Hrelated''. iPureIntro.
        eapply related_sts_a_priv_trans_world. apply Hrelated'. apply Hrelated''.
    }

    iDestruct (big_sepM_insert with "[$Hregs $Hr_adv]") as "Hregs".
    { rewrite /rmap2 !lookup_insert_ne//. apply not_elem_of_dom. rewrite -Hdom'.
      rewrite !dom_insert_L !dom_delete_L !dom_insert_L Hdom. clear. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_stk]") as "Hregs".
    { rewrite /rmap2 !lookup_insert_ne//. apply not_elem_of_dom. rewrite -Hdom'.
      rewrite !dom_insert_L !dom_delete_L !dom_insert_L Hdom. clear. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
    { rewrite /rmap2 !lookup_insert_ne//. apply not_elem_of_dom. rewrite -Hdom'.
      rewrite !dom_insert_L !dom_delete_L !dom_insert_L Hdom. clear. set_solver. }

    rewrite -(insert_insert _ PC _ (inl 0%Z)).

    iDestruct ("Hexpr_now" with "[$Hr $Hsts $Hown Hregs]") as "[_ Hφ]".
    { rewrite /registers_mapsto /rmap3.
      rewrite (insert_insert _ _ _ (updatePcPerm (inr (p', Global, b', e', a'')))). iFrame.
      iSplit.
      - iPureIntro. intros x. simpl. rewrite /rmap2.

        repeat (match goal with
          |-  context [ <[?r := _]> _ ] => destruct (decide (x = r));[subst;rewrite lookup_insert;eauto|
                                                                    rewrite lookup_insert_ne//]
                end).
        apply elem_of_gmap_dom. rewrite -Hdom'. rewrite dom_insert_L !dom_delete_L !dom_insert_L Hdom.
        clear -n n1 n2 n3 n4 n5. pose proof (all_registers_s_correct x). set_solver.

      - iIntros (r Hne). rewrite /RegLocate. rewrite lookup_insert_ne// lookup_insert_ne//.
        destruct (decide (r = r_stk)).
        { subst. rewrite lookup_insert. iRevert "Hwstk_valid". iClear "#". iIntros "Hwstk_valid".
          rewrite (fixpoint_interp1_eq W2) /=.
          assert (addr_reg.min frame_end estk = frame_end) as ->.
          { clear -Ha_param Hsize Hb_r_adv Haf2 Haf3 Hparam1 Hparam2 Hparam3. solve_addr. }
          assert (addr_reg.max b_r_adv frame_end = frame_end) as ->.
          { clear -Ha_param Hsize Hb_r_adv Haf2 Haf3 Hparam1 Hparam2 Hparam3. solve_addr. }
          iSplit.
          + iApply big_sepL_forall. iIntros (k x Hin).
            assert (x ∈ region_addrs b_r_adv frame_end) as Hin'%elem_of_region_addrs.
            { apply elem_of_list_lookup;eauto. }
            iDestruct (read_allowedU_inv _ x with "Hwstk_valid") as "Hrel".
            { clear -Ha_param Hsize Hb_r_adv Haf2 Haf3 Hparam1 Hparam2 Hparam3 Hin'. solve_addr. }
            { auto. }
            iFrame "Hrel".
            rewrite /region_state_pwl_mono. iPureIntro. eapply stack_state_W2_params;eauto.
            apply elem_of_region_addrs. auto.
          + iApply big_sepL_forall. iIntros (k x Hin).
            assert (x ∈ region_addrs frame_end estk) as Hin'%elem_of_region_addrs.
            { apply elem_of_list_lookup;eauto. }
            iDestruct (read_allowedU_inv _ x with "Hwstk_valid") as "Hrel".
            { clear -Ha_param Hsize Hb_r_adv Haf2 Haf3 Hparam1 Hparam2 Hparam3 Hin'. solve_addr. }
            { auto. }
            iFrame "Hrel".
            rewrite /region_state_U_pwl_mono. iPureIntro. eapply stack_state_W2;eauto.
            apply elem_of_region_addrs. auto.
        }

        rewrite lookup_insert_ne//.
        destruct (decide (r = r_adv)).
        { subst. rewrite lookup_insert. iApply interp_monotone_nm;auto. }
        rewrite lookup_insert_ne//.
        rewrite /rmap2.
        repeat (match goal with
          |-  context [ <[?r1 := _]> _ ] => destruct (decide (r = r1));[subst;rewrite lookup_insert;iClear "#";rewrite fixpoint_interp1_eq;eauto|
                                                                    rewrite lookup_insert_ne//]
                end).

        destruct (rmap' !! r) eqn:Hsome';[|iClear "#";rewrite Hsome' fixpoint_interp1_eq;eauto].
        rewrite Hsome'. apply Hcond in Hsome'. subst w7. iClear "#";rewrite fixpoint_interp1_eq;eauto.
    }

    iApply (wp_wand with "Hφ").
    iClear "#". iIntros (v) "Hv". iLeft. iIntros (Hhalted).
    iDestruct ("Hv" $! Hhalted) as (r W') "(Hfull & Hregs & Hrelated & Hown & Hsts & Hr)".
    iExists r , W'. iFrame. iDestruct "Hrelated" as %Hrelated'. iPureIntro.
    apply related_sts_priv_trans_world with W2;auto.
  Qed.

End stack_object.
