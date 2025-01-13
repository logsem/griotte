From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From cap_machine Require Import
     rules logrel fundamental region_invariants rules_LoadU_derived
     region_invariants_revocation region_invariants_static region_invariants_batch_uninitialized.
From cap_machine.examples Require Import region_macros macros stack_macros_helpers
     awkward_example_helpers stack_object_helpers awkward_example_extra.
From stdpp Require Import countable.

Section awkward_example.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* choose a special register for the environment and adv pointer *)
  (* note that we are here simplifying the environment to simply point to one location *)
   Definition r_env : RegName := r_t30.
   Definition r_adv : RegName := r_t28.

  (* assume r1 contains an executable pointer to adversarial code *)
  (* f_a is the offset to the failure subroutine in the environment table *)
  (* by convention a pointer to the linking table is at the bottom address of the PC *)
  Definition awkward_instrs f_a (r1 : RegName) :=
     reqglob_instrs r1 ++
     prepstackU_instrs r_stk 10 1 ++
     [store_z r_env 0] ++
     [pushU_r_instr r_stk r_env;
     pushU_r_instr r_stk r1] ++
     scallU_prologue_instrs r1 [] ++
     [pushU_r_instr r_stk r_t0;
     move_z r_t0 0;
     jmp r1;
     lea_z r_stk (-6)] ++
     popU_instrs r_stk r1 ++
     popU_instrs r_stk r_env ++
     [store_z r_env 1;
     pushU_r_instr r_stk r_env] ++
     scallU_prologue_instrs r1 [] ++
     [pushU_r_instr r_stk r_t0;
     move_z r_t0 0;
     jmp r1;
     lea_z r_stk (-6)] ++
     popU_instrs r_stk r_env ++
     [loadU_r_z r_t0 r_stk (-1);
     (* assert that the cap in r_env points to 1 *)
     load_r r1 r_env] ++
     assert_r_z_instrs f_a r1 1 ++
     (* in this version, we clear only the registers before returning *)
     rclear_instrs (list_difference all_registers [PC;r_t0]) ++
     [jmp r_t0].

   Definition awkward_instrs_length : Z :=
     Eval cbv in (length (awkward_instrs 0 r_adv)).

   Definition awkward_example (a : list Addr) f_a (r1 : RegName) : iProp Σ :=
     ([∗ list] a_i;w_i ∈ a;(awkward_instrs f_a r1), a_i ↦ₐ w_i)%I.

  (* Notation for overriding W with a map *)
   Notation "m1 >> W" := (override_uninitialize m1 W) (at level 40, left associativity).

   Ltac isWithinBounds := rewrite /withinBounds; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; simpl; auto.

 (* the following spec is for the f4 subroutine of the awkward example, jumped to after activating the closure *)
  Lemma f4_spec W pc_p pc_g pc_b pc_e (* PC *)
        wadv (* b e a *) (* adv *)
        f4_addrs (* f2 *)
        d d' i (* dynamically allocated memory given by preamble, connected to invariant i *)
        a_first a_last (* special adresses *)
        f_a b_link e_link a_link a_entry fail_cap (* linking table variables *)
        wstk (* stack *)
        rmap (* registers *)
        ι1 ι2 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between f4_addrs a_first a_last ->

    (* Linking table assumptions *)
    withinBounds (RW, Global, b_link, e_link, a_entry) = true →
    (a_link + f_a)%a = Some a_entry ->

    (* the monotonicity of the PC is not monotone *)
    isDirected pc_g = false →

    (* malloc'ed memory assumption *)
    (d + 1)%a = Some d' ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk;r_adv;r_env]} →

    (* The two invariants have different names *)
    (up_close (B:=coPset) ι2 ## ↑ι1) ->

    {{{ r_stk ↦ᵣ wstk
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ r_adv ↦ᵣ wadv
      ∗ r_env ↦ᵣ inr (RWX,Global,d,d',d)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      (* invariant for d *)
      ∗ (∃ ι, inv ι (awk_inv i d))
      ∗ sts_rel_loc (A:=Addr) i awk_rel_pub awk_rel_pub awk_rel_priv
      (* stack *)
      ∗ interp W wstk
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* adv code *)
      ∗ interp W wadv
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (awkward_example f4_addrs f_a r_adv)
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
    iIntros (Hvpc Hcont Hwb_table Hlink_table Hpc_g_mono Hd Hrmap_dom Hne φ)
            "(Hr_stk & HPC & Hr_adv & Hr_env & Hgen_reg & #Hι & #Hrel & #Hstack_val
            & Hna & #Hadv_val & #Hf4 & #Htable & Hsts & Hr) Hφ".
    iMod (na_inv_acc with "Hf4 Hna") as "(>Hprog & Hna & Hcls)";[auto..|].
    iDestruct (big_sepL2_length with "Hprog") as %Hprog_length.
    (* destruct (f4_addrs);[inversion Hprog_length|]. *)
    iDestruct "Hι" as (ι) "Hinv".
    (* We get some general purpose registers *)
    iAssert ((∃ w0, r_t0 ↦ᵣ w0) ∗
             (∃ w1, r_t1 ↦ᵣ w1) ∗
             (∃ w2, r_t2 ↦ᵣ w2) ∗ [∗ map] r_i↦w_i ∈ delete r_t2 (delete r_t1 (delete r_t0 rmap)), r_i ↦ᵣ w_i)%I
      with "[Hgen_reg]" as "(Hr_t0 & Hr_t1 & Hr_t2 & Hgen_reg)".
    { assert (is_Some (rmap !! r_t0)) as [w0 Hrt0].
      { apply elem_of_gmap_dom. rewrite Hrmap_dom. set_solver. }
      assert (is_Some (delete r_t0 rmap !! r_t1)) as [w1 Hrt1].
      { apply elem_of_gmap_dom. rewrite dom_delete_L Hrmap_dom. set_solver. }
      assert (is_Some (delete r_t1 (delete r_t0 rmap) !! r_t2)) as [w2 Hrt2].
      { apply elem_of_gmap_dom. rewrite !dom_delete_L Hrmap_dom. set_solver. }
      iDestruct (big_sepM_delete _ _ r_t0 with "Hgen_reg") as "[Hr_t0 Hgen_reg]";[eauto|].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hgen_reg") as "[Hr_t1 Hgen_reg]";[eauto|].
      iDestruct (big_sepM_delete _ _ r_t2 with "Hgen_reg") as "[Hr_t2 Hgen_reg]";[eauto|].
      iSplitL "Hr_t0";[eauto|]. iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iFrame.
    }

    (* reqglob  *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code.
    iApply (reqglob_spec with "[- $HPC $Hcode $Hr_adv]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|].
    iNext. destruct (isGlobalWord wadv) eqn:Hglob;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct wadv as [c | [ [ [ [g l] b] e] a'] ];[inversion Hglob|]. destruct l;[|inversion Hglob..].
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
    destruct ((10%nat + 1%nat <? estk - bstk)%Z) eqn:Hsize;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct ((bstk + 1%nat <=? astk)%Z) eqn:Hbounds;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iIntros "Hcont". iDestruct "Hcont" as (a_param Ha_param) "(HPC & HprepstackU & Hr_stk & Hr_t1 & Hr_t2)".
    apply Z.ltb_lt in Hsize. apply Z.leb_le in Hbounds.

    (* we can extract the validity of the parameters passed on the stack *)
    (* the return pointer is now passed on the stack. this parameter will be frozen
       during adversary call, but only loaded during the final callback *)
    iDestruct (read_allowedU_inv _ bstk with "Hstack_val") as "Hcond2";[clear -Hbounds Hsize;solve_addr|auto|].
    iDestruct (writeLocalAllowedU_valid_cap_below_implies _ _ _ _ _ _ bstk with "Hstack_val") as %Hmono2;
      [auto|apply le_addr_withinBounds|..];[clear -Hbounds Hsize;solve_addr..|].

    (* for the next part of the code, we will need to manipulate our local stack frame *)
    (* for that, we begin by revoking the local stack frame from W which we will use to
       store the local state and activation record *)
    (* uninitialize the full stack *)
    iMod (uninitialize_region_keep _ addr_reg.za with "[$Hsts $Hr]") as (m Hmcond) "[Hsts [Hr #Hvalids] ]".
    (* next we can open the region at b_stk, which we will first assert is in m *)
    iDestruct (valid_uninitialized_condition_weak _ m with "Hstack_val") as %Hstk_cond;eauto. clear. solve_addr.
    assert (∃ frame_end, a_param + 10 = Some frame_end)%a as [frame_end Hframe_delim].
    { clear -Hbounds Ha_param Hsize. destruct (a_param + 10)%a eqn:HH;eauto. exfalso. solve_addr. }
    (* first we must know that a fully uninitialized world satisfies the revoke condition *)
    apply uninitialize_revoke_condition in Hmcond as Hrevoked.
    (* next we may revoke it *)

    (* first we will revoke bstk specifically to remember its valid state *)
    destruct Hstk_cond with bstk as [wret Hwret].
    { clear -Hsize. solve_addr. }
    iMod (uninitialize_to_revoked_cond_param bstk with "[$Hr $Hsts]") as "(Hr & Hsts & Hbstk)";[eauto..|].
    (* next we will revoke the full frame *)
    iMod (uninitialize_to_revoked_cond (region_addrs a_param frame_end) _ _ interpC with "[$Hr $Hsts]") as "(Hr & Hsts & Hframe)";[|apply region_addrs_NoDup|..].
    { intros a. destruct (decide (bstk = a));[subst;rewrite lookup_insert;auto|rewrite lookup_insert_ne//]. }
    { apply Forall_forall. intros x Hin%elem_of_region_addrs.
      rewrite lookup_insert_ne. apply Hstk_cond.
      clear -Hbounds Ha_param Hsize Hframe_delim Hin. solve_addr.
      clear -Ha_param Hin. solve_addr. }
    { iApply big_sepL_forall. iIntros (k x Hlookup).
      assert (x ∈ (region_addrs a_param frame_end)) as Hin;[apply elem_of_list_lookup;eauto|].
      apply elem_of_region_addrs in Hin.
      iDestruct (read_allowedU_inv _ x with "Hstack_val") as "Hcond".
      clear -Hin Hframe_delim Ha_param Hsize Hbounds. solve_addr.
      auto. iFrame "Hcond". } rewrite /uninitialized_resources.

    (* finally we clean up our resources a bit *)
    iAssert (∃ ws,[[a_param,frame_end]]↦ₐ[[ws]])%I with "[Hframe]" as (wsstk) "Hframe".
    { iDestruct (region_addrs_exists with "Hframe") as (ws) "Hframe".
      iExists ws. iApply (big_sepL2_mono with "Hframe"). iIntros (k y1 y2 Hin1 Hin2) "H". iFrame. }
    iDestruct (big_sepL2_length with "Hframe") as %Hframe_length.
    rewrite region_addrs_length in Hframe_length.
    apply (incr_addr_region_size_iff _ _ 10)in Hframe_delim as Hframe_det.
    destruct Hframe_det as [Hframe_le Hframe_size]. rewrite Hframe_size in Hframe_length.
    iDestruct (writeLocalAllowedU_implies_local with "Hstack_val") as %Hmono;auto.
    destruct lstk;inversion Hmono.

    match goal with |- context [ region ?W ] =>
                    set (W' := W)
    end.
    assert (revoke_condition W') as Hrevoked_2.
    { rewrite /W'. intros a. destruct (decide (a ∈ (region_addrs a_param frame_end))).
      rewrite std_sta_update_multiple_lookup_in_i;auto.
      rewrite std_sta_update_multiple_lookup_same_i;auto.
      destruct (decide (a = bstk));[subst;rewrite lookup_insert;auto|rewrite lookup_insert_ne//]. }
    assert (related_sts_priv_world W W') as HrelatedWW'.
    { rewrite /W'.
      eapply related_sts_priv_trans_world.
      apply related_sts_pub_plus_priv_world.
      apply (related_sts_a_pub_plus_world _ _ addr_reg.za).
      apply uninitialize_related_pub_a. eauto.
      apply related_sts_priv_world_std_update_multiple_Uninit_to_Rev_cond
        with (l:=bstk::region_addrs a_param frame_end) in Hrevoked.
      simpl in Hrevoked. rewrite std_update_multiple_insert_commute;auto.
      apply not_elem_of_region_addrs. clear -Ha_param. solve_addr.
      apply Forall_forall. intros a Ha. apply Hstk_cond.
      apply elem_of_cons in Ha as [-> | Ha%elem_of_region_addrs];
        [clear -Hsize;solve_addr|clear -Ha_param Hsize Ha Hframe_delim;solve_addr]. }

    (* For later use it will be useful to know that W contains i *)
    (* Now we may do any private transitions to our local invariants.
       since we don't know which case we are in, we can generalize and
       say that there exists some private future world such that
       the store succeeded, after which the state at i is false
     *)
    iPrologue_multi "Hprog" Hcont Hvpc link1.
    assert (withinBounds (RWX, Global, d, d', d) = true) as Hwb.
    { isWithinBounds;[lia|]. revert Hd; clear. solve_addr. }
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code1.
    destruct_addr_list l_code1. apply contiguous_between_cons_inv_first in Hcont_code1 as Heq. subst link0.
    iPrologue "Hcode". iClear "Hcode".
    iAssert (▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, link1)
              ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
              ∗ l_code1 ↦ₐ store_z r_env 0
              ∗ ⌜(∃ b : bool, W.2.1 !! i = Some (encode b))
                ∧ W.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝ ∧
                ⌜related_sts_priv_world W' (W'.1,(<[i:=encode false]> W.2.1,W.2.2))⌝ ∧
                region (W'.1,(<[i:=encode false]> W.2.1,W.2.2))
                       ∗ sts_full_world (W'.1,(<[i:=encode false]> W.2.1,W.2.2))
                       -∗ WP Seq (Instr Executable) {{ v, φ v }})
        -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
      with "[HPC Hi Hr_env Hr Hsts]" as "Hstore_step".
    { iIntros "Hcont".
      (* store r_env 0 *)
      iInv ι as (x) "[>Hstate Hb]" "Hcls".
      destruct x; iDestruct "Hb" as ">Hb".
      - iApply (wp_store_success_z with "[$HPC $Hi $Hr_env $Hb]");
          [apply decode_encode_instrW_inv|iCorrectPC l_code1 link1| |auto..].
        { eapply contiguous_between_last. apply Hcont_code1. auto. }
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* we assert that updating the local state d to 0 is a private transition *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.
        assert ((W'.1, (<[i:=encode false]> W'.2.1, W'.2.2)) = (W'.1, (<[i:=encode false]> W.2.1, W.2.2))) as HeqW.
        { f_equiv. rewrite /W' std_update_multiple_loc_rel std_update_multiple_loc_sta /uninitialize /loc /=; auto. }
        assert (related_sts_priv_world W' (W'.1,(<[i:=encode false]> W.2.1,W.2.2))) as Hrelated.
        { apply related_priv_local_1 in Hlookup;auto. rewrite -HeqW. auto. }
        (* first we can update region privately since it is revoked *)
        iAssert (sts_full_world W'
               ∗ region (W'.1, (<[i:=encode false]> W'.2.1, W'.2.2)))%I with "[Hsts Hr]" as "[Hsts Hr]".
        { rewrite region_eq /region_def.
          iDestruct "Hr" as (M Mρ) "(HM & % & % & Hr)".
          iDestruct (monotone_revoke_cond_region_def_mono_same $! _ Hrelated with "Hsts Hr") as "[Hsts Hr]".
          iFrame. iExists M, Mρ. iFrame. rewrite HeqW. iFrame. iPureIntro. auto. }
        (* we must update the local state of d to false *)
        iMod (sts_update_loc _ _ _ false with "Hsts Hstate") as "[Hsts Hstate]".
        iMod ("Hcls" with "[Hstate Hd]") as "_".
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        rewrite std_update_multiple_loc_sta.
        rewrite std_update_multiple_loc_rel.
        iFrame "Hsts Hr". iSimpl.
        iPureIntro.
        rewrite /W' std_update_multiple_loc_sta /uninitialize /loc /= in Hlookup; auto.
        rewrite /W' std_update_multiple_loc_rel /uninitialize /loc /= in Hrel; auto.
        split;auto. split;auto. eauto.
      - iApply (wp_store_success_z with "[$HPC $Hi $Hr_env $Hb]");
          [apply decode_encode_instrW_inv|iCorrectPC l_code1 link1| |auto..].
        { eapply contiguous_between_last. apply Hcont_code1. auto. }
        iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
        (* use sts_state to assert that the current state of i is false *)
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.
        rewrite /W' std_update_multiple_loc_sta /uninitialize /loc /= in Hlookup; auto.
        rewrite /W' std_update_multiple_loc_rel /uninitialize /loc /= in Hrel; auto.
        (* No need to update the world, since we did not change state *)
        iMod ("Hcls" with "[Hstate Hd]") as "_".
        { iNext. iExists false. iFrame. }
        iModIntro. iApply wp_pure_step_later;auto;iNext.
        iApply "Hcont". iFrame "HPC Hr_env Hinstr".
        rewrite insert_id /=;auto.
        assert ((W'.1, (W'.2.1, W'.2.2)) = (W'.1, (W.2.1, W.2.2))) as HeqW.
        { f_equiv. rewrite /W' std_update_multiple_loc_rel std_update_multiple_loc_sta /uninitialize /loc /=; auto. }
        rewrite -HeqW. iSplit;[|iSplit]. 3: destruct W' as [? [? ?] ];simpl; iFrame "Hsts Hr".
        all: iPureIntro.
        eauto. destruct W' as [? [? ?] ]; simpl; apply related_sts_priv_refl_world.
    }
    iApply "Hstore_step".
    iNext. iIntros "(HPC & Hr_env & Hprog_done & HW')".
    iDestruct "HW'" as ([Hawki Hawk] HrelatedW'Wi) "(Hr & Hsts)".
    assert (is_Some (a_param + 1)%a) as [a_param2 Ha_param2].
    { destruct (a_param + 1)%a eqn:Hsome;[eauto|clear -Ha_param Hsize Hsome;solve_addr]. }
    assert (is_Some (a_param2 + 1)%a) as [a_param3 Ha_param3].
    { destruct (a_param2 + 1)%a eqn:Hsome;[eauto|clear -Ha_param Ha_param2 Hsize Hsome;solve_addr]. }
    destruct wsstk;[inversion Hframe_length|].
    destruct wsstk;[inversion Hframe_length|].
    iDestruct (region_mapsto_cons with "Hframe") as "[Ha1 Hframe]";
      [eauto|clear -Hframe_size Ha_param Ha_param2;rewrite /region_size in Hframe_size;solve_addr|].
    iDestruct (region_mapsto_cons with "Hframe") as "[Ha2 Hframe]";
      [eauto|clear -Hframe_size Ha_param Ha_param2 Ha_param3;rewrite /region_size in Hframe_size;solve_addr|].

    iPrologue_multi "Hprog" Hcont Hvpc link2.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code2.
    destruct_addr_list l_code2. apply contiguous_between_cons_inv_first in Hcont_code2 as Heq. subst link1.
    iDestruct "Hcode" as "(Hpush1 & Hpush2 & _)".
    (* push r_stk r_env *)
    iApply (pushU_r_spec); [..|iFrame "HPC Hpush1 Hr_stk Hr_env Ha1"];
      [iCorrectPC l_code2 link2| |iContiguous_next_a Hcont_code2|apply Ha_param2|by simpl|].
    { clear -Ha_param Hsize. apply le_addr_withinBounds; solve_addr. }
    iNext. iIntros "(HPC & Hpush1 & Hr_stk & Hr_env & Ha1)".
    (* push r_stk r_adv *)
    iApply (pushU_r_spec); [..|iFrame "HPC Hpush2 Hr_stk Hr_adv Ha2"];
      [iCorrectPC l_code2 link2| | |apply Ha_param3|by simpl|].
    { clear -Ha_param Ha_param2 Hsize. apply le_addr_withinBounds; solve_addr. }
    { eapply contiguous_between_last. apply Hcont_code2. auto. }
    iNext. iIntros "(HPC & Hpush2 & Hr_stk & Hr_adv & Ha2)".

    (* prepare the activation record *)
    rewrite /region_size in Hframe_size.
    assert (is_Some (a_param3 + 6)%a) as [a_act_final Ha_act_final].
    { destruct (a_param3 + 6)%a eqn:Hsome;
        [eauto|clear -Hframe_size Hsome Ha_param Ha_param2 Ha_param3;solve_addr]. }
    assert (is_Some (a_param3 + 7)%a) as [a_act_end Ha_act_end].
    { destruct (a_param3 + 7)%a eqn:Hsome;
        [eauto|clear -Hframe_size Hsome Ha_param Ha_param2 Ha_param3;solve_addr]. }
    assert (a_act_final + 1 = Some a_act_end)%a as Hact_boundary.
    { clear -Ha_act_final Ha_act_end. solve_addr. }
    assert (a_act_end + 1 = Some frame_end)%a as Ha_act_end_next.
    { clear -Ha_act_end Hframe_size Ha_param Ha_param2 Ha_param3;solve_addr. }
    rewrite /region_mapsto.
    rewrite (region_addrs_split a_param3 a_act_end);
      [|clear -Hframe_size Ha_act_end Ha_param Ha_param2 Ha_param3;solve_addr].
    assert (∃ wsstk' w, wsstk = wsstk' ++ [w] ∧ length wsstk' = 7) as [wsstk' [wend [-> Hact_length] ] ].
    { repeat (destruct wsstk;[by inversion Hframe_length|]);destruct wsstk;[|inversion Hframe_length].
      exists [w1; w2; w3; w4; w5; w6; w7],w8. split;eauto. }
    rewrite (region_addrs_single a_act_end)//.
    iDestruct (mapsto_decomposition with "Hframe") as "[Hact [Hparam _] ]".
    { rewrite Hact_length region_addrs_length /region_size. clear -Ha_act_end. solve_addr. }

    (* reconstruct registers *)
    iDestruct (big_sepM_insert with "[$Hgen_reg $Hr_t2]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
    rewrite -delete_insert_ne//.
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert with "[$Hregs $Hr_env]") as "Hregs".
    { rewrite !lookup_insert_ne// !lookup_delete_ne//. apply not_elem_of_dom. rewrite Hrmap_dom. clear. set_solver. }

    (* apply calling convention *)
    iPrologue_multi "Hprog" Hcont Hvpc link3. iRename "Hcode" into "Hscall".
    iPrologue_multi "Hprog" Hcont Hvpc link4.
    iDestruct (big_sepL2_length with "Hscall") as %Hlength_code3.
    iDestruct (big_sepL2_length with "Hcode") as %Hlength_code4.
    destruct_addr_list l_code4. apply contiguous_between_cons_inv_first in Hcont_code4 as Heq. subst link3.
    iApply (scallU_prologue_spec with "[- $HPC $Hact $Hscall $Hregs $Hr_stk $Hr_t0]");
      [apply Hvpc_code3| | |apply Hcont_code3|auto..|apply Ha_act_final|apply Ha_act_end| |].
    { clear -Ha_param Ha_param2 Ha_param3 Hsize. apply le_addr_withinBounds;solve_addr. }
    { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Hsize. apply le_addr_withinBounds;solve_addr. }
    { repeat (apply not_elem_of_cons; split;auto). apply not_elem_of_nil. }
    { clear. set_solver. }
    { rewrite !dom_insert_L !dom_delete_L Hrmap_dom. clear. simpl. set_solver. }
    { simpl. assert ((2 + 2 * 0%nat)%Z = 2%Z) as ->;[auto|].
      apply (contiguous_between_incr_addr _ 2 l_code4 a1) in Hcont_code4;auto. apply Hcont_code4. }
    iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hrmap & Hact & Hscall)".
    iDestruct "Hrmap" as (rmap' [Hrmap_dom' Hrmap_spec']) "Hrmap".

    (* push the return capability parameter onto stack *)
    iDestruct "Hcode" as "[Hpush3 Hcode]".
    iApply (pushU_r_spec); [..|iFrame "HPC Hpush3 Hr_stk Hr_t0 Hparam"];
      [iCorrectPC l_code4 link4| |iContiguous_next_a Hcont_code4|..].
    { clear -Ha_param Hsize Ha_param2 Ha_param3 Ha_act_end Ha_act_final. apply le_addr_withinBounds; solve_addr. }
    { apply Ha_act_end_next. }
    { simpl. clear. rewrite Z.leb_le. solve_addr. }
    iNext. iIntros "(HPC & Hpush3 & Hr_stk & Hr_t0 & Hparam)".
    iPrologue "Hcode".
    iApply (wp_move_success_z with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC l_code4 link4|iContiguous_next_a Hcont_code4|].
    iEpilogue "(HPC & Hprog_done0 & Hr_t0)".

    (* freeze the local stack frame *)
    match goal with |- context [ [[a_param3,a_act_end]]↦ₐ[[ ?activation ]]%I ] =>
                    set (actw := activation)
    end.
    set lframe : gmap Addr Word :=
      list_to_map (zip (region_addrs bstk a_act_end)
                       (wret :: inr (RWX, Global, d, d', d) :: inr (g, Global, b, e, a') :: actw)).
    iDestruct (read_allowedU_inv_range _ _ _ _ _ _ bstk a_act_end with "Hstack_val") as "Hstack_conditions".
    { clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final. solve_addr. }
    { auto. }
    iMod (region_revoked_cond_to_static _ lframe with "[Hbstk Hact Ha1 Ha2 $Hr $Hsts]") as "[Hsts Hr]";[auto|..].
    { iApply big_sepL2_to_big_sepM. apply region_addrs_NoDup.
      iSimpl.
      rewrite region_addrs_cons;[|clear -Ha_param Hsize Ha_param2 Ha_param3 Ha_act_end;solve_addr].
      rewrite Ha_param /=. iDestruct "Hstack_conditions" as "[Hbstk_rel Hconds]". iSplitL "Hbstk".
      iExists interpC. iFrame "∗ #". iPureIntro;apply _.
      rewrite region_addrs_cons;[|clear -Ha_param Hsize Ha_param2 Ha_param3 Ha_act_end;solve_addr].
      rewrite Ha_param2 /=. iDestruct "Hconds" as "[Ha2_rel Hconds]". iSplitL "Ha1".
      iExists interpC. iFrame "∗ #". iPureIntro;apply _.
      rewrite region_addrs_cons;[|clear -Ha_param Hsize Ha_param2 Ha_param3 Ha_act_end;solve_addr].
      rewrite Ha_param3 /=. iDestruct "Hconds" as "[Ha3_rel Hconds]". iSplitL "Ha2".
      iExists interpC. iFrame "∗ #". iPureIntro;apply _.
      iDestruct (big_sepL2_to_big_sepL_l _ _ actw with "Hconds") as "Hconds'".
      { rewrite /= region_addrs_length /region_size. clear -Ha_act_end. solve_addr. }
      iDestruct (big_sepL2_sep with "[$Hact $Hconds']") as "Hact".
      iApply (big_sepL2_mono with "Hact").
      iIntros (k y1 y2 Hin1 Hin2) "[Hy Hy1] /=".
      iExists interpC. iFrame.
      iPureIntro. apply _. }

    match goal with |- context [ region ?W ] =>
                    set (W1 := W)
    end.
    set W2 := <s[a_act_end := Monotemporary]s> W1.

    assert (related_sts_priv_world (W'.1, (<[i:=encode false]> W.2.1, W.2.2)) W1) as HrelationWiW1.
    { rewrite /W1 /lframe. apply related_sts_priv_world_static.
      apply Forall_forall. intros x Hx%elem_of_elements%elem_of_gmap_dom%list_to_map_lookup_is_Some.
      rewrite fst_zip in Hx.
      2: { rewrite /= region_addrs_length /region_size.
           clear -Hsize Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final. solve_addr. }
      apply elem_of_region_addrs in Hx. rewrite /std /W' /=.
      assert (std_update_multiple (<s[bstk:=Revoked]s>(uninitialize W m)) (region_addrs a_param frame_end) Revoked
              = std_update_multiple (uninitialize W m) (bstk :: region_addrs a_param frame_end) Revoked) as ->.
      { apply std_update_multiple_insert_commute. apply not_elem_of_region_addrs. clear -Ha_param. solve_addr. }
      apply std_sta_update_multiple_lookup_in_i.
      assert (a_param = ^(bstk + 1)%a) as Heq;[rewrite Ha_param;auto|].
      rewrite Heq -region_addrs_cons;[|clear -Ha_param Hframe_delim;solve_addr].
      apply elem_of_region_addrs. clear -Hx Ha_param Hframe_delim Hsize Ha_param2 Ha_param3 Ha_act_end Ha_act_final.
      solve_addr. }
    assert (related_sts_pub_world W1 W2) as HrelatedW1W2.
    { rewrite /W2. apply related_sts_pub_world_revoked_monotemp. left.
      rewrite /std /W1 /=. rewrite std_sta_update_multiple_lookup_same_i.
      rewrite /std /W' /=. apply std_sta_update_multiple_lookup_in_i.
      apply elem_of_region_addrs. clear -Ha_param Hframe_delim Hsize Ha_param2 Ha_param3 Ha_act_end Ha_act_final.
      solve_addr. intros Hx%elem_of_elements%elem_of_gmap_dom%list_to_map_lookup_is_Some.
      rewrite fst_zip in Hx.
      2: { rewrite /= region_addrs_length /region_size.
           clear -Hsize Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final. solve_addr. }
      apply elem_of_region_addrs in Hx. clear -Hx. solve_addr. }
    assert (related_sts_priv_world W W2) as HrelatedWW2.
    { eapply related_sts_priv_pub_trans_world. 2: apply HrelatedW1W2.
      eapply related_sts_priv_trans_world. 2: apply HrelationWiW1.
      eapply related_sts_priv_trans_world. apply HrelatedWW'. auto. }

    iDestruct (big_sepM_insert with "[$Hrmap $Hr_t0]") as "Hregs".
    { apply not_elem_of_dom. rewrite -Hrmap_dom'. rewrite !dom_insert_L dom_delete_L. clear. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_stk]") as "Hregs".
    { rewrite !lookup_insert_ne//.
      apply not_elem_of_dom. rewrite -Hrmap_dom'. rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      clear. set_solver. }

    iDestruct (jmp_or_fail_spec with "Hadv_val") as "Hcall".
    (* jmp r_adv *)
    iPrologue "Hcode".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_adv]");
      [apply decode_encode_instrW_inv|iCorrectPC l_code4 link4|].
    destruct (decide (isCorrectPC (updatePcPerm (inr (g, Global, b, e, a'))))).
    2: { rewrite decide_False//. iEpilogue "(HPC & Hi & Hr_adv)".
         iApply "Hcall". iFrame. iApply "Hφ". iIntros (Hcontr). inversion Hcontr. }
    rewrite decide_True//.
    iDestruct "Hcall" as (p g0 b0 e0 a3 Heq) "Hcall".
    inversion Heq. subst p g0 b0 e0 a3.
    match goal with |- context [ ([∗ map] k↦y ∈ ?reg, k ↦ᵣ y)%I ] =>
                    set (rmap2 := reg)
    end.
    iSpecialize ("Hcall" $! (<[PC:=inl 0%Z]> (<[r_adv:=inr (g, Global, b, e, a')]> rmap2)) W2 HrelatedWW2).
    iEpilogue "(HPC & Hi & Hr_adv)".

    (* reconstruct registers and close program invariant *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_adv]") as "Hregs".
    { rewrite !lookup_insert_ne//.
      apply not_elem_of_dom. rewrite -Hrmap_dom'. rewrite !dom_insert_L dom_delete_L Hrmap_dom.
      clear. set_solver. }
    iMod ("Hcls" with "[$Hna $Hreqglob $HprepstackU $Hprog_done $Hpush1 $Hpush2
                        $Hcode $Hprog $Hscall $Hpush3 $Hprog_done0 $Hi]") as "Hna".
    { iNext. iSplit;done. }

    (* the adversary stack is valid in W2 *)
    iAssert (interp W2 (inr (URWLX, Directed, a_act_end, estk, frame_end))) as "#Hadv_stack_val".
    { iClear "∗". iApply fixpoint_interp1_eq.
      iSimpl.
      assert (addr_reg.min frame_end estk = frame_end) as ->.
      { clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim. solve_addr. }
      assert (addr_reg.max a_act_end frame_end = frame_end) as ->.
      { clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim. solve_addr. }
      iSplit. all: iApply big_sepL_forall. all: iIntros (k x Hx).
      assert (x ∈ region_addrs a_act_end frame_end) as Hin%elem_of_region_addrs;
        [apply elem_of_list_lookup;eauto|].
      2: assert (x ∈ region_addrs frame_end estk) as Hin%elem_of_region_addrs;
        [apply elem_of_list_lookup;eauto|].
      all: (iDestruct (read_allowedU_inv _ x with "Hstack_val") as "$";
        [clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim Hin;solve_addr|auto|]).
      all: iPureIntro.
      - assert (x = a_act_end) as ->.
        clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim Hin;solve_addr.
        rewrite /W2 /region_state_pwl_mono lookup_insert //.
      - assert (x ≠ a_act_end) as Hnex.
        clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim Hin;solve_addr.
        rewrite /W2 /region_state_U_pwl_mono lookup_insert_ne// /W1.
        right. rewrite std_sta_update_multiple_lookup_same_i /= /W'.
        rewrite std_sta_update_multiple_lookup_same_i. rewrite lookup_insert_ne.
        apply Hstk_cond. 4: rewrite elem_of_elements /lframe.
        4: rewrite not_elem_of_dom -not_elem_of_list_to_map fst_zip.
        3,4: apply not_elem_of_region_addrs.
        5: rewrite /= region_addrs_length /region_size.
        all: clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim Hin Hnex;solve_addr. }

    (* rmap2 is a valid register state *)
    iAssert (interp_reg interp W2 (<[PC:=inl 0%Z]> (<[r_adv:=inr (g, Global, b, e, a')]> rmap2))) as "#Hadv_reg_val".
    { iSplit.
      - iPureIntro. intros r. rewrite /= /rmap2. clear -Hrmap_dom Hrmap_dom'.
        destruct (decide (r = PC));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        destruct (decide (r = r_adv));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        destruct (decide (r = r_stk));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        destruct (decide (r = r_t0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        apply elem_of_gmap_dom. rewrite -Hrmap_dom'. rewrite !dom_insert_L dom_delete_L Hrmap_dom.
        pose proof (all_registers_s_correct r). clear Hrmap_dom Hrmap_dom'.
        set_solver.
      - iIntros (r Hner). rewrite /RegLocate lookup_insert_ne//.
        rewrite /= /rmap2.
        destruct (decide (r = r_adv));[subst;rewrite lookup_insert|rewrite lookup_insert_ne//].
        iApply interp_monotone_nm. eauto. auto. iFrame "Hadv_val".
        destruct (decide (r = r_stk));[subst;rewrite lookup_insert|rewrite lookup_insert_ne//].
        iFrame "Hadv_stack_val".
        destruct (decide (r = r_t0));[subst;rewrite lookup_insert|rewrite lookup_insert_ne//].
        iClear "∗ #". rewrite fixpoint_interp1_eq. eauto.
        destruct (rmap' !! r) eqn:Hsome;rewrite Hsome.
        apply Hrmap_spec' in Hsome. inv Hsome. all: iClear "∗ #"; rewrite fixpoint_interp1_eq; eauto. }

    iDestruct (read_allowedU_inv _ a_act_end with "Hstack_val") as "Ha_act_end_rel";[|auto|].
    { clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr. }

    (* we must now finally prove the validity of the callback *)
    iMod (update_region_revoked_monotemp_updated with "[] Hsts Hr Hparam [] Ha_act_end_rel") as "[Hr Hsts]".
    { rewrite /W1 std_sta_update_multiple_lookup_same_i /W' /=. apply std_sta_update_multiple_lookup_in_i.
      2: rewrite elem_of_elements not_elem_of_dom -not_elem_of_list_to_map fst_zip.
      1,2: rewrite elem_of_region_addrs.
      3: rewrite /= region_addrs_length /region_size.
      all: clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim;solve_addr. }
    { iClear "#". iModIntro. iIntros (W1' W2' Hrelated'') "Hval /=".
      iApply (interp_monotone_a with "[] Hval"). auto. }
    { iSimpl. iApply fixpoint_interp1_eq. iModIntro. iIntros (rmap3 Wmid HrelatedW2Wmid).
      iNext.
      iIntros "(#[Hall Hregs_valid] & Hregs & Hr & Hsts & Hown)".
      iSplit;auto. iDestruct "Hall" as %Hr_all. iClear "Hall".
      (* extract some registers *)
      iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]"; [rewrite lookup_insert;eauto|].
      rewrite delete_insert_delete.

      (* we will first have to go through the activation record *)
      (* let's open the static region of W' *)
      (* we must therefore first attest that the local stack frame is still static in Wmid *)
      assert (std Wmid !! bstk = Some (Monostatic lframe)) as Hlframe'.
      { eapply related_sts_pub_a_world_static. 3: apply HrelatedW2Wmid.
        - rewrite lookup_insert_ne.
          apply std_sta_update_multiple_lookup_in_i.
          rewrite elem_of_elements -elem_of_gmap_dom list_to_map_lookup_is_Some fst_zip.
          apply elem_of_region_addrs. 2: rewrite /= region_addrs_length /region_size.
          all: clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr.
        - clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr. }

      (* since we will need to change the static state, it is conveninent to first
         uninitialize the full stack, so we can revoke the local stack frame *)
      iDestruct (full_sts_monostatic_all with "Hsts Hr") as %Hall_mono;[apply Hlframe'|].
      iMod (uninitialize_region_keep _ addr_reg.za with "[$Hsts $Hr]") as (m' Hmcond') "[Hsts [Hr #Hvalids'] ]".
      apply uninitialize_revoke_condition in Hmcond' as Hrevoked'.

      (* then we can open the static region *)
      iMod (region_open_monostatic _ _ bstk with "[$Hr $Hsts]") as "(Hr & Hsts & Hstates & Hframe & %)".
      { rewrite uninitialize_std_sta_not_elem_of_lookup. apply Hlframe'. intros Hcontr%elem_of_gmap_dom%Hmcond'.
        destruct Hcontr as [Hcontr _]. rewrite Hlframe' in Hcontr. done. }
      rewrite /static_resources.
      (* cleanup the resources *)
      iAssert (bstk ↦ₐ wret ∗ a_param ↦ₐ inr (RWX, Global, d, d', d) ∗ a_param2 ↦ₐ inr (g, Global, b, e, a')
            ∗ [[a_param3,a_act_end]]↦ₐ[[ actw ]])%I with "[Hframe]" as "[Hbstk [Ha_param [Ha_param2 Hact]]]".
      { iDestruct (big_sepM_to_big_sepL2 with "Hframe") as "Hframe".
        { apply region_addrs_NoDup. }
        { rewrite /= region_addrs_length /region_size.
          clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr. }
        do 3 (rewrite region_addrs_cons;[|clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr]).
        rewrite Ha_param Ha_param2 Ha_param3.
        iDestruct "Hframe" as "(Hbstk & Ha_param & Ha_param2 & Hframe)".
        iDestruct "Hbstk" as (?) "[_ $]".
        iDestruct "Ha_param" as (?) "[_ $]".
        iDestruct "Ha_param2" as (?) "[_ $]".
        iApply (big_sepL2_mono with "Hframe").
        iIntros (k y1 y2 Hin1 Hin2) "H". iDestruct "H" as (?) "[_ $]". }

      (* apply the activation record *)
      specialize (Hr_all r_t1) as Hr_t1; specialize (Hr_all r_stk) as Hr_stk;
        destruct Hr_t1 as [w1' Hr_t1]; destruct Hr_stk as [wstk' Hr_stk].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; [rewrite lookup_delete_ne//|].
      iDestruct (big_sepM_delete _ _ r_stk with "Hregs") as "[Hr_stk Hregs]"; [rewrite !lookup_delete_ne//|].
      iApply (scallU_epilogue_spec with "[- $HPC $Hact $Hr_t1 $Hr_stk]");[| |auto..].
      { intros mid Hmid. constructor;auto. clear -Hmid Ha_param Ha_param2 Ha_param3 Ha_act_end. solve_addr. }
      { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize. apply le_addr_withinBounds;solve_addr. }
      { iContiguous_next_a Hcont_code4. }
      { eapply (isCorrectPC_contiguous_range _ _ _ _ _ _ _ _ Hvpc_code4); eauto. repeat econstructor. }
      iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hact)".
      iDestruct "Hr_t1" as (rt1w) "Hr_t1".

      (* Next we continue the execution of the callback *)
      (* first we must open the invariant containing the program *)
      iMod (na_inv_acc with "Hf4 Hown") as "(>Hprog & Hown & Hcls)";auto.
      rewrite /awkward_example /awkward_instrs.
      match goal with |- context [ ([∗ list] a_i;w_i ∈ (?l1 ++ ?l2 ++ ?l3 ++ ?l4 ++ ?l5 ++ ?l6 ++ l_rest4);
                                   (?i1 ++ ?i2 ++ ?i3 ++ ?i4 ++ ?i5 ++ ?i6 ++ ?i_rest),_)%I ] =>
                      set lprev := (l1 ++ l2 ++ l3 ++ l4 ++ l5); set lcur := l6;
                      set iprev := (i1 ++ i2 ++ i3 ++ i4 ++ i5); set icur := i6; set irest := i_rest
      end.
      match goal with |- context [ ([∗ list] a_i;w_i ∈ ?l_addrs;?i_instrs, _)%I ] =>
                      set laddrs := l_addrs; set instrs := i_instrs
      end.
      assert (laddrs = lprev ++ (lcur ++ l_rest4)) as ->;[rewrite /laddrs /lprev /lcur;repeat rewrite -app_assoc //|].
      assert (instrs = iprev ++ (icur ++ irest)) as ->;[rewrite /instrs /iprev /lcur /irest;repeat rewrite -app_assoc //|].
      iDestruct (big_sepL2_app' with "Hprog") as "[Hprog_done Hprog]".
      { by rewrite /lprev /iprev /= !app_length /= Hlength_code Hlength_code0 Hlength_code3 /=. }
      iDestruct (big_sepL2_app' with "Hprog") as "[Hcode Hprog]".
      { by rewrite /lcur /icur /=. }
      do 3 (iDestruct "Hcode" as "[Hi Hcode]";iCombine "Hi" "Hprog_done" as "Hprog_done").

      (* lea r_stk -6 *)
      assert (a_act_final + (-6) = Some a_param3)%a as Hlea;[clear -Ha_act_final;solve_addr|].
      iPrologue "Hcode".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_stk]");
        [apply decode_encode_instrW_inv|iCorrectPC l_code4 link4| |apply Hlea|auto..].
      { eapply contiguous_between_last;[apply Hcont_code4|auto]. }
      { simpl. clear -Ha_act_end Ha_act_final. solve_addr. }
      iEpilogue "(HPC & Hi & Hr_stk)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      iClear "Hcode".

      iPrologue_multi "Hprog" Hcont Hvpc link5.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code5.
      destruct_addr_list l_code5. clear Heq.
      apply contiguous_between_cons_inv_first in Hcont_code5 as Heq. subst link4.

      (* pop r_adv *)
      specialize (Hr_all r_adv) as Hr_adv; destruct Hr_adv as [wadv' Hr_adv].
      iDestruct (big_sepM_delete _ _ r_adv with "Hregs") as "[Hr_adv Hregs]"; [rewrite !lookup_delete_ne//|].
      iApply (popU_spec with "[- $HPC $Hcode $Hr_stk $Hr_adv $Ha_param2 $Hr_t1]");
        [split;[|split];iCorrectPC l_code5 link5| |auto|iContiguous_next_a Hcont_code5|
         iContiguous_next_a Hcont_code5| |apply Ha_param3|].
      { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize. apply le_addr_withinBounds;solve_addr. }
      { eapply contiguous_between_last. apply Hcont_code5. auto. }
      iNext. iIntros "(HPC & Hpop1 & Hr_adv & Ha_param2 & Hr_stk & Hr_t1)".

      iPrologue_multi "Hprog" Hcont Hvpc link6.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code6.
      destruct_addr_list l_code6.
      apply contiguous_between_cons_inv_first in Hcont_code6 as Heq. subst link5.

      (* pop r_env *)
      specialize (Hr_all r_env) as Hr_env; destruct Hr_env as [wenv' Hr_env].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]"; [rewrite !lookup_delete_ne//|].
      iApply (popU_spec with "[- $HPC $Hcode $Hr_stk $Hr_env $Ha_param $Hr_t1]");
        [split;[|split];iCorrectPC l_code6 link6| |auto|iContiguous_next_a Hcont_code6|
         iContiguous_next_a Hcont_code6| |apply Ha_param2|].
      { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize. apply le_addr_withinBounds;solve_addr. }
      { eapply contiguous_between_last. apply Hcont_code6. auto. }
      iNext. iIntros "(HPC & Hpop2 & Hr_env & Ha_param & Hr_stk & Hr_t1)".

      (* before we continue, we will want to revoke the local stack frame, so that we can freeze
         it to a new state *)
      (* first we turn it uninitialized *)
      iMod (region_close_monostatic_to_uninitialized with "[$Hsts $Hr Hact Hbstk Ha_param Ha_param2 $Hstates]")
        as "[Hsts Hr]".
      { intros x1 x2 [Hin Hle]. apply Hrevoked'. }
      { iClear "Hstack_conditions". rewrite /lframe.
        iApply (big_sepL2_to_big_sepM).
        { apply region_addrs_NoDup. }
        do 3 (rewrite region_addrs_cons;[|clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr]).
        rewrite Ha_param Ha_param2 Ha_param3. iSimpl. iSplitL "Hbstk";[|iSplitL "Ha_param";[|iSplitL "Ha_param2"] ].
        1,2,3: iExists interpC;iFrame;iSplit;[iPureIntro;apply _|];iFrame "#".
        1,2:(iDestruct (read_allowedU_inv with "Hstack_val") as "$";auto).
        1,2: clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
        iDestruct (read_allowedU_inv_range _ _ _ _ _ _ a_param3 a_act_end with "Hstack_val") as "Hrange";[|auto|].
        { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr. }
        iDestruct (big_sepL2_to_big_sepL_l _ _ actw with "Hrange") as "Hrange2".
        { rewrite /= region_addrs_length /region_size.
          clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr. }
        iDestruct (big_sepL2_sep with "[$Hact $Hrange2]") as "Hact".
        iApply (big_sepL2_mono with "Hact").
        iIntros (k y1 y2 Hy1 Hy2) "[? ?]".
        iExists interpC. iFrame. iPureIntro. apply _. }
      assert (revoke_condition (lframe >> uninitialize Wmid m')) as Hrevoked_2'.
      { intros x. destruct (lframe !! x) eqn:Hsome.
        rewrite (override_uninitialize_std_sta_lookup_some _ _ _ w1)//.
        rewrite override_uninitialize_std_sta_lookup_none//. }
      assert (lframe !! bstk = Some wret) as Hlframebstk.
      { apply elem_of_list_to_map_1'.
        all: (rewrite region_addrs_cons;[|clear -Ha_param Ha_param2 Ha_param3 Hsize
                                                          Ha_act_end Ha_act_final;solve_addr]).
        - intros y Hin. apply elem_of_cons in Hin as [Heq|Hin];[inv Heq;auto|].
          apply elem_of_zip_l in Hin. rewrite Ha_param /= in Hin.
          apply elem_of_region_addrs in Hin. clear -Hin Ha_param. solve_addr.
        - constructor. }
      assert ((lframe >> uninitialize Wmid m').1 !! bstk = Some (Uninitialized wret)) as HWbstk.
      { apply override_uninitialize_std_sta_lookup_some;auto. }
      (* first we will revoke bstk specifically to remember its valid state *)
      iMod (uninitialize_to_revoked_cond_param bstk with "[$Hr $Hsts]") as "(Hr & Hsts & Hbstk)";[eauto..|].
      (* next we will revoke the full frame *)
      iMod (uninitialize_to_revoked_cond (region_addrs a_param a_act_end) _ _ interpC with "[$Hr $Hsts]") as "(Hr & Hsts & Hframe)";[|apply region_addrs_NoDup|..].
      { intros x. destruct (decide (bstk = x));[subst;rewrite lookup_insert;auto|rewrite lookup_insert_ne//]. }
      { apply Forall_forall. intros x Hin%elem_of_region_addrs.
        rewrite lookup_insert_ne.
        assert (is_Some (lframe !! x)) as [w' Hin'].
        { apply list_to_map_lookup_is_Some. rewrite fst_zip. apply elem_of_region_addrs.
          2: rewrite /= region_addrs_length /region_size.
          1,2: clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hin;solve_addr. }
        rewrite (override_uninitialize_std_sta_lookup_some _ _ _ w');auto. eauto.
        clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hin;solve_addr. }
      { iApply big_sepL_forall. iIntros (k x Hlookup).
        assert (x ∈ (region_addrs a_param a_act_end)) as Hin;[apply elem_of_list_lookup;eauto|].
        apply elem_of_region_addrs in Hin.
        iDestruct (read_allowedU_inv _ x with "Hstack_val") as "Hcond".
        clear -Hin Hframe_delim Ha_param2 Ha_param3 Ha_act_end Ha_act_final Ha_param Hsize Hbounds. solve_addr.
        auto. iFrame "Hcond". }

      (* finally we clean up our resources a bit *)
      iAssert (∃ ws,[[a_param,a_act_end]]↦ₐ[[ws]])%I with "[Hframe]" as (wsstk) "Hframe".
      { iDestruct (region_addrs_exists with "Hframe") as (ws) "Hframe".
        iExists ws. iApply (big_sepL2_mono with "Hframe"). iIntros (k y1 y2 Hin1 Hin2) "H". iFrame. }
      iDestruct (big_sepL2_length with "Hframe") as %Hframe_length'.
      rewrite region_addrs_length in Hframe_length'.
      assert ((a_param + 9)%a = Some a_act_end) as Hframe_delim'.
      { clear -Ha_param2 Ha_param3 Ha_act_end Ha_act_final Ha_param. solve_addr. }
      apply (incr_addr_region_size_iff _ _ 9)in Hframe_delim' as Hframe_det.
      destruct Hframe_det as [Hframe_le' Hframe_size']. rewrite Hframe_size' in Hframe_length'.

      match goal with |- context [ region ?W ] =>
                    set (W3 := W)
      end.

      iPrologue_multi "Hprog" Hcont Hvpc link7.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code7.
      destruct_addr_list l_code7.
      apply contiguous_between_cons_inv_first in Hcont_code7 as Heq. subst link6.

      (* store r_env 1 *)
      iPrologue "Hcode".
      (* Storing 1 will always constitute a public future world of
           (uninitialize Wmid m') *)
      iAssert (∀ φ, ▷ (PC ↦ᵣ inr (pc_p, pc_g, pc_b, pc_e, a7)
                          ∗ r_env ↦ᵣ inr (RWX, Global, d, d', d)
                          ∗ l_code7 ↦ₐ store_z r_env 1
                          ∗ sts_full_world (W3.1, (<[i:=encode true]> W3.2.1,W3.2.2))
                          ∗ region (W3.1, (<[i:=encode true]> W3.2.1,W3.2.2))
                          ∗ ⌜(∃ y : bool, W3.2.1 !! i = Some (encode y)) ∧ W3.2.2 !! i = Some (convert_rel awk_rel_pub, convert_rel awk_rel_pub, convert_rel awk_rel_priv)⌝
                                -∗ WP Seq (Instr Executable) {{ v, φ v }})
                      -∗ WP Instr Executable {{ v, WP fill [SeqCtx] (of_val v) {{ v, φ v }} }})%I
        with "[HPC Hi Hr_env Hr Hsts]" as "Hstore_step".
      { iIntros (φ') "Hφ".
        iInv ι as (y) "[>Hstate Hb]" "Hcls".
        iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hlookup.
        iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrellookup.
        rewrite std_update_multiple_loc_sta in Hlookup.
        rewrite std_update_multiple_loc_rel in Hrellookup.
        destruct y; iDestruct "Hb" as ">Hb".
        - iApply (wp_store_success_z with "[$HPC $Hi $Hr_env $Hb]");
            [apply decode_encode_instrW_inv|iCorrectPC l_code7 link7|
             iContiguous_next_a Hcont_code7|auto|].
          iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
          iMod ("Hcls" with "[Hstate Hd]") as "_".
          { iNext. iExists true. iFrame. } iSimpl.
          iDestruct ("Hφ" with "[$HPC $Hr_env $Hinstr Hr Hsts]") as "Hφ".
          { rewrite /override_uninitialize /= in Hlookup.
            rewrite /override_uninitialize /= in Hrellookup.
            rewrite (insert_id _ i);[|rewrite /W3 /override_uninitialize std_update_multiple_loc_sta /= //].
            iSplitL "Hsts";[|iSplitL;[|rewrite /W3 /override_uninitialize std_update_multiple_loc_sta std_update_multiple_loc_rel /= //;eauto] ].
            all: destruct W3 as [W3_std [W3_loc_pub W3_lo_priv] ]; iFrame. }
          iModIntro. iApply wp_pure_step_later;auto;iNext.
        - iApply (wp_store_success_z with "[$HPC $Hi $Hr_env $Hb]");
            [apply decode_encode_instrW_inv|iCorrectPC l_code7 link7|
             iContiguous_next_a Hcont_code7|auto|].
          iNext. iIntros "(HPC & Hinstr & Hr_env & Hd)".
          iMod (sts_update_loc _ _ _ true with "Hsts Hstate") as "[Hsts Hstate]".
          iMod ("Hcls" with "[Hstate Hd]") as "_".
          { iNext. iExists true. iFrame. }
          iModIntro. iApply wp_pure_step_later;auto;iNext. iApply "Hφ".
          rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel std_update_multiple_proj_eq.
          iFrame.
          iSplitL;[|eauto]. iSimpl. iApply (region_monotone with "Hr").
          + rewrite /revoke /std /loc /=. erewrite std_update_multiple_std_sta_eq. eauto.
          + apply std_update_mutiple_related_monotone.
            split;[apply related_sts_std_pub_refl|].
            rewrite /= /loc. apply related_pub_local_1 with false; auto.
      }
      iApply "Hstore_step". iNext. iIntros "(HPC & Hr_env & Hinstr & Hr & Hsts & #HW3lookup)".
      iDestruct "HW3lookup" as %[HW3lookup Hw3rel].
      iCombine "Hinstr" "Hprog_done" as "Hprog_done".

      destruct wsstk;[inversion Hframe_length'|].
      iDestruct (region_mapsto_cons a_param a_param2 with "Hframe") as "[Ha_param Hframe]";auto.
      { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end. solve_addr. }
      assert (is_Some (a_param2 + 6)%a) as [a_act_end' Ha_act_end'].
      { destruct (a_param2 + 6)%a eqn:Hsome;eauto. clear -Ha_act_end Hsome Ha_param2 Ha_param3. solve_addr. }
      rewrite /region_mapsto.
      assert (a_act_end' + 1 = Some a_act_final)%a as Ha_act_end_next'.
      { clear -Ha_act_end Ha_act_end' Ha_param Ha_param2 Ha_param3 Ha_act_final. solve_addr. }
      rewrite (region_addrs_split a_param2 a_act_final a_act_end).
      2: clear -Ha_act_end' Ha_act_end Ha_act_final Ha_param2 Ha_param Ha_param3;solve_addr.

      assert (∃ wsstk' w1, wsstk = wsstk' ++ [w1] ∧ length wsstk' = 7) as [wsstk'' [wend1 [-> Hact_length'] ] ].
      { repeat (destruct wsstk;[by inversion Hframe_length'|]);destruct wsstk;[|inversion Hframe_length'].
        exists [w2; w3; w4; w5; w6; w7; w8],w9. split;eauto. }
      rewrite (region_addrs_cons a_act_final).
      2: clear -Ha_act_end' Ha_act_end Ha_act_final Ha_param2 Ha_param Ha_param3;solve_addr.
      rewrite Hact_boundary (region_addrs_empty a_act_end);[|clear;solve_addr].
      iDestruct (big_sepL2_app' with "Hframe") as "[Hact [Hp1 _] ]".
      { rewrite /= app_length /= in Hframe_length'.
        assert (length wsstk'' = 7) as Heqlen. clear -Hframe_length';lia.
        rewrite Heqlen region_addrs_length /region_size. clear -Ha_act_final Ha_act_end Ha_param3;solve_addr. }

      (* push r_stk r_env *)
      iDestruct "Hcode" as "[Hi _]".
      iApply (pushU_r_spec with "[- $Hi $Ha_param $Hr_stk $Hr_env $HPC]");
        [iCorrectPC l_code7 link7| | |apply Ha_param2| |].
      { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Hframe_delim Hsize.
        apply le_addr_withinBounds;solve_addr. }
      { eapply contiguous_between_last. apply Hcont_code7. auto. }
      { simpl. intros Hcontr; inversion Hcontr. }
      iNext. iIntros "(HPC & Hpush1 & Hr_stk & Hr_env & Ha_param)".

      (* reconstruct registers *)
      iDestruct (big_sepM_insert with "[$Hregs $Hr_env]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
      rewrite -!(delete_insert_ne _ _ r_env)// !(delete_commute _ _ r_t1)//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs"; [apply lookup_delete|rewrite insert_delete].
      assert (is_Some (rmap3 !! r_t0)) as [w0' Hw0'];[apply Hr_all|].
      iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr_t0 Hregs]".
      { rewrite lookup_insert_ne// !lookup_delete_ne// lookup_insert_ne//. }

      (* apply calling convention *)
      iPrologue_multi "Hprog" Hcont Hvpc link8. iRename "Hcode" into "Hscall".
      iPrologue_multi "Hprog" Hcont Hvpc link9.
      iDestruct (big_sepL2_length with "Hscall") as %Hlength_code8.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code9.
      destruct_addr_list l_code9. apply contiguous_between_cons_inv_first in Hcont_code9 as Heq. subst link8.
      iApply (scallU_prologue_spec with "[- $HPC $Hact $Hscall $Hregs $Hr_stk]");
        [apply Hvpc_code8| | |apply Hcont_code8|apply Hpc_g_mono|
        |clear; set_solver| |apply Ha_act_end'|clear -Ha_act_end' Ha_act_end_next'; solve_addr|..].
      { clear -Ha_act_end' Ha_act_end Ha_act_final Ha_param2 Ha_param Ha_param3 Hsize.
        apply le_addr_withinBounds; solve_addr. }
      { clear -Ha_act_end' Ha_act_end Ha_act_final Ha_param2 Ha_param Ha_param3 Hsize.
        apply le_addr_withinBounds; solve_addr. }
      { repeat (apply not_elem_of_cons; split;auto). apply not_elem_of_nil. }
      { rewrite dom_delete_L dom_insert_L !dom_delete_L dom_insert_L. apply regmap_full_dom in Hr_all as ->.
        clear. set_solver. }
      { rewrite /=. eapply (contiguous_between_incr_addr _ (2 + 2 * 0%nat) l_code9);eauto. }
      iSplitL "Hr_t0";[eauto|]. iNext. iIntros "(HPC & Hr_stk & Hr_t0 & Hregs & Hact & Hscall)".
      iDestruct "Hregs" as (rmap4 [Hrmap_dom'' Hrmap_spec'']) "Hregs".

      iDestruct "Hcode" as "[Hi Hcode]".
      iApply (pushU_r_spec with "[- $Hi $Hp1 $Hr_stk $Hr_t0 $HPC]");
        [iCorrectPC l_code9 link9| | |apply Hact_boundary| |].
      { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Hframe_delim Hsize Hact_boundary.
        apply le_addr_withinBounds;solve_addr. }
      { iContiguous_next_a Hcont_code9. }
      { simpl. intros Hcontr. rewrite Z.leb_le. clear. solve_addr. }
      iNext. iIntros "(HPC & Hpush2 & Hr_stk & Hr_t0 & Ha_act_final)".
      iPrologue "Hcode".
      iApply (wp_move_success_z with "[$HPC $Hi $Hr_t0]");
        [apply decode_encode_instrW_inv|iCorrectPC l_code9 link9|iContiguous_next_a Hcont_code9|].
      iEpilogue "(HPC & Hprog_done0 & Hr_t0)".

      (* freeze the local stack frame *)
      match goal with |- context [ [[a_param2,a_act_final]]↦ₐ[[ ?activation ]]%I ] =>
                      set (actw' := activation)
      end.
      set lframe' : gmap Addr Word :=
        list_to_map (zip (region_addrs bstk a_act_final)
                         (wret :: inr (RWX, Global, d, d', d) :: actw')).
      assert (revoke_condition (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2))) as Hrevoked_3.
      { clear -Hrevoked_2'. intros a. rewrite /W3 /=. destruct (decide (a ∈ (region_addrs a_param a_act_end))).
        rewrite std_sta_update_multiple_lookup_in_i;auto.
        rewrite std_sta_update_multiple_lookup_same_i//.
        destruct (decide (bstk = a));[subst;rewrite lookup_insert//|rewrite lookup_insert_ne//]. }
      iClear "Hstack_conditions".
      iDestruct (read_allowedU_inv_range _ _ _ _ _ _ bstk a_act_final with "Hstack_val") as "Hstack_conditions".
      { clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final. solve_addr. }
      { auto. }
      iMod (region_revoked_cond_to_static _ lframe' with "[Hbstk Hact Ha_param $Hr $Hsts]") as "[Hsts Hr]";[auto|..].
      { iApply big_sepL2_to_big_sepM. apply region_addrs_NoDup.
        iSimpl.
        rewrite region_addrs_cons;[|clear -Ha_param Hsize Ha_param2 Ha_param3 Ha_act_end
                                                  Ha_act_final Ha_act_end_next;solve_addr].
        rewrite Ha_param /=. iDestruct "Hstack_conditions" as "[Hbstk_rel Hconds]". iSplitL "Hbstk".
        iExists interpC. iFrame "∗ #". iPureIntro;apply _.
        rewrite (region_addrs_cons a_param);[|clear -Ha_param Hsize Ha_param2 Ha_param3 Ha_act_end
                                                  Ha_act_final Ha_act_end_next;solve_addr].
        rewrite Ha_param2 /=. iDestruct "Hconds" as "[Ha2_rel Hconds]". iSplitL "Ha_param".
        iExists interpC. iFrame "∗ #". iPureIntro;apply _.
        iDestruct (big_sepL2_to_big_sepL_l _ _ actw' with "Hconds") as "Hconds'".
        { rewrite /= region_addrs_length /region_size. clear -Ha_act_end' Ha_act_end_next'. solve_addr. }
        iDestruct (big_sepL2_sep with "[$Hact $Hconds']") as "Hact".
        iApply (big_sepL2_mono with "Hact").
        iIntros (k y1 y2 Hin1 Hin2) "[Hy Hy1] /=".
        iExists interpC. iFrame.
        iPureIntro. apply _. }

      match goal with |- context [ region ?W ] =>
                      set (W4 := W)
      end.
      set W5 := <s[a_act_final := Monotemporary]s> W4.

      assert (∀ a', (bstk <= a' < estk)%a → ∃ w, (lframe >> uninitialize Wmid m').1 !! a' = Some (Uninitialized w))
        as Hstk_cond'.
      { intros x Hx.
        destruct (lframe !! x) eqn:Hsome.
        rewrite /override_uninitialize /=.
        erewrite override_uninitialize_std_sta_lookup_some;eauto.
        rewrite override_uninitialize_std_sta_lookup_none;auto.
        destruct (m' !! x) eqn:Hsome'. rewrite /uninitialize /=.
        erewrite uninitialize_std_sta_lookup_in;eauto.
        destruct Hmcond' with x as [ [Hmono' Hle] _];eauto.
        rewrite uninitialize_std_sta_None_lookup//.
        apply not_elem_of_list_to_map in Hsome.
        rewrite fst_zip in Hsome.
        2: rewrite /= region_addrs_length /region_size;clear -Ha_act_end Ha_param Ha_param2 Ha_param3;solve_addr.
        apply not_elem_of_region_addrs in Hsome.
        destruct Hsome as [Hcontr | Hle];[clear -Hcontr Hx;solve_addr|].
        apply Hstk_cond in Hx as [w2 Hw2].
        destruct (decide (x = a_act_end)).
        { subst x.
          apply related_sts_pub_a_world_monotemporary_le with (i:=a_act_end)
            in HrelatedW2Wmid as [Hcontr | HH];eauto.
          2: rewrite lookup_insert;auto.
          exfalso. clear -Hsome' Hcontr Hmcond'.
          assert (is_Some (m' !! a_act_end)) as [? ?];[apply Hmcond';split;auto;solve_addr|congruence]. }

        apply related_sts_pub_a_world_uninitialized_le with (i:=x) (w:=w2)
            in HrelatedW2Wmid as [Hcontr | HH];eauto.
        exfalso. clear -Hsome' Hcontr Hmcond'.
        assert (is_Some (m' !! x)) as [? ?];[apply Hmcond';split;auto;solve_addr|congruence].
        rewrite lookup_insert_ne// std_sta_update_multiple_lookup_same_i//.
        simpl. rewrite /W'. rewrite std_sta_update_multiple_lookup_same_i.
        rewrite lookup_insert_ne. auto.
        3: rewrite elem_of_elements;apply not_elem_of_dom, not_elem_of_list_to_map; rewrite fst_zip.
        2,3: apply not_elem_of_region_addrs.
        4: rewrite /= region_addrs_length /region_size.
        all: clear -Hle Ha_param Ha_param2 Ha_param3 Hframe_delim Ha_act_end_next
                        Ha_act_end Hsize Hle n;try solve_addr. }

      assert ((std_update_multiple (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2))
                                   (elements (dom (gset Addr) lframe'))
                                   (Monostatic lframe')).1 !! a_act_final = Some Revoked) as Hw2.
      { rewrite std_sta_update_multiple_lookup_same_i /W3 /=.
        rewrite std_sta_update_multiple_lookup_in_i /=. auto.
        2: rewrite elem_of_elements;apply not_elem_of_dom, not_elem_of_list_to_map; rewrite fst_zip.
        3: rewrite /= region_addrs_length /region_size.
        1,2: rewrite elem_of_region_addrs.
        all: clear -Ha_param Ha_param2 Ha_param3 Hframe_delim Ha_act_end_next
                        Ha_act_end Hsize Ha_act_final Ha_act_end' Ha_act_end_next';try solve_addr. }

      assert (Forall (λ a11, ∃ ρ, std (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2)) !! a11 = Some ρ ∧ ρ ≠ Permanent)
                     (elements (dom (gset Addr) lframe'))) as Hlframe'_forall.
      { apply Forall_forall. intros x Hx. rewrite /W3 /=.
        destruct (decide (x ∈ (region_addrs a_param a_act_end))).
        { rewrite std_sta_update_multiple_lookup_in_i//. eauto. }
        rewrite std_sta_update_multiple_lookup_same_i//.
        destruct (decide (x = bstk)).
        { subst. rewrite lookup_insert. eauto. }
        rewrite lookup_insert_ne//. destruct Hstk_cond' with x;eauto.
        revert Hx; rewrite elem_of_elements =>Hx. apply elem_of_gmap_dom in Hx.
        apply list_to_map_lookup_is_Some in Hx. rewrite fst_zip in Hx.
        apply elem_of_region_addrs in Hx.
        2: rewrite /= region_addrs_length /region_size.
        revert Hx.
        all: clear -Ha_param Ha_param2 Ha_param3 Hframe_delim Ha_act_end_next
                             Ha_act_end Hsize Ha_act_final;try solve_addr. }

      assert (related_sts_priv_world W3 W5) as HrelationW3W5.
      { rewrite /W5 /W4.
        apply related_sts_priv_pub_trans_world with
            (std_update_multiple (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2))
                                 (elements (dom (gset Addr) lframe')) (Monostatic lframe')).
        - apply related_sts_pub_priv_trans_world with (W3.1, (<[i:=encode true]> W3.2.1, W3.2.2)).
          { split;[apply related_sts_std_pub_refl|simpl].
            destruct HW3lookup as [y Hy].
            apply related_pub_local_1 with y; auto. }
          apply related_sts_priv_world_static2. auto.
        - apply related_sts_pub_world_revoked_monotemp;auto. }

      assert (related_sts_priv_world Wmid W3) as HrelationWmidW3.
      { rewrite /W3. apply related_sts_priv_trans_world with (<s[bstk:=Revoked]s>(lframe >> uninitialize Wmid m')).
        { apply related_sts_priv_trans_world with (lframe >> uninitialize Wmid m').
          apply related_sts_a_priv_trans_world with (uninitialize Wmid m') addr_reg.za.
          - apply uninitialize_related_pub_a;auto.
          - apply related_sts_pub_plus_priv_world. apply related_sts_a_pub_plus_world with addr_reg.za.
            eapply related_sts_pub_world_monostatic_to_uninitialized.
            + intros x Hx%elem_of_gmap_dom%Hall_mono.
              rewrite uninitialize_std_sta_None_lookup.
              rewrite /monostatic in Hx. destruct (Wmid.1 !! x) eqn:Hsome;inversion Hx;subst;eauto.
              apply eq_None_not_Some. intros [Hsome _]%Hmcond'.
              rewrite /monostatic Hsome in Hx. inv Hx.
            + intros. clear. solve_addr.
          - eapply related_sts_priv_world_Uninitialized_to_Revoked. eauto. }
        apply related_sts_priv_world_std_update_multiple_Uninit_to_Rev_cond.
        - intros x. destruct (decide (bstk = x)).
          + subst. rewrite lookup_insert. auto.
          + rewrite lookup_insert_ne//.
        - apply Forall_forall. intros x Hx%elem_of_region_addrs.
          rewrite lookup_insert_ne. apply Hstk_cond'.
          all: clear -Hx Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;try solve_addr. }

    assert (related_sts_priv_world Wmid W5) as HrelatedWmidW5.
    { eapply related_sts_priv_trans_world. apply HrelationWmidW3. auto. }

    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs".
    { apply not_elem_of_dom. rewrite -Hrmap_dom''. rewrite dom_delete_L dom_insert_L !dom_delete_L dom_insert_L.
      apply regmap_full_dom in Hr_all as ->. clear. set_solver. }
    iDestruct (big_sepM_insert with "[$Hregs $Hr_stk]") as "Hregs".
    { rewrite !lookup_insert_ne//.
      apply not_elem_of_dom. rewrite -Hrmap_dom''. rewrite dom_delete_L dom_insert_L !dom_delete_L dom_insert_L.
      apply regmap_full_dom in Hr_all as ->. clear. set_solver. }

    iDestruct (jmp_or_fail_spec with "Hadv_val") as "Hcall_2".
    (* jmp r_adv *)
    iPrologue "Hcode".
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_adv]");
      [apply decode_encode_instrW_inv|iCorrectPC l_code9 link9|].
    rewrite decide_True//.
    iDestruct "Hcall_2" as (p g0 b0 e0 a11 Heq) "Hcall_2".
    inversion Heq. subst p g0 b0 e0 a11.
    match goal with |- context [ ([∗ map] k↦y ∈ ?reg, k ↦ᵣ y)%I ] =>
                    set (rmap5 := reg)
    end.
    assert (related_sts_priv_world W W5) as HrelatedWW5.
    { eapply related_sts_priv_trans_world. apply HrelatedWW2.
      eapply related_sts_a_priv_trans_world. apply HrelatedW2Wmid. auto. }
    iSpecialize ("Hcall_2" $! (<[PC:=inl 0%Z]> (<[r_adv:=inr (g, Global, b, e, a')]> rmap5)) W5 HrelatedWW5).
    iEpilogue "(HPC & Hi & Hr_adv)".

    (* reconstruct registers and close program invariant *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_adv]") as "Hregs".
    { rewrite !lookup_insert_ne//.
      apply not_elem_of_dom. rewrite -Hrmap_dom''. rewrite dom_delete_L dom_insert_L !dom_delete_L dom_insert_L.
      apply regmap_full_dom in Hr_all as ->. clear. set_solver. }
    iMod ("Hcls" with "[$Hown Hprog_done $Hpop1 $Hpop2 $Hpush1 $Hcode $Hprog $Hscall
                        $Hpush2 $Hprog_done0 $Hi]") as "Hna".
    { iNext. iDestruct "Hprog_done" as "($&$&$&$&$&$)". iSplit;done. }

    (* the adversary stack is valid in W2 *)
    iAssert (interp W5 (inr (URWLX, Directed, a_act_final, estk, a_act_end))) as "#Hadv_stack_val_2".
    { iClear "∗". iApply fixpoint_interp1_eq.
      iSimpl.
      assert (addr_reg.min a_act_end estk = a_act_end) as ->.
      { clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim. solve_addr. }
      assert (addr_reg.max a_act_final a_act_end = a_act_end) as ->.
      { clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim. solve_addr. }
      iSplit. all: iApply big_sepL_forall. all: iIntros (k x Hx).
      assert (x ∈ region_addrs a_act_final a_act_end) as Hin%elem_of_region_addrs;
        [apply elem_of_list_lookup;eauto|].
      2: assert (x ∈ region_addrs a_act_end estk) as Hin%elem_of_region_addrs;
        [apply elem_of_list_lookup;eauto|].
      all: (iDestruct (read_allowedU_inv _ x with "Hstack_val") as "$";
        [clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim Hin;solve_addr|auto|]).
      all: iPureIntro.
      - assert (x = a_act_final) as ->.
        clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim Hin;solve_addr.
        rewrite /W5 /region_state_pwl_mono lookup_insert //.
      - assert (x ≠ a_act_final) as Hnex.
        clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim Hin;solve_addr.
        rewrite /W5 /region_state_U_pwl_mono lookup_insert_ne//.
        right. rewrite std_sta_update_multiple_lookup_same_i /=.
        rewrite std_sta_update_multiple_lookup_same_i. rewrite lookup_insert_ne.
        apply Hstk_cond'. 4: rewrite elem_of_elements /lframe.
        4: rewrite not_elem_of_dom -not_elem_of_list_to_map fst_zip.
        3,4: apply not_elem_of_region_addrs.
        5: rewrite /= region_addrs_length /region_size.
        all: clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final Hframe_delim Hin Hnex;solve_addr. }

    (* rmap5 is a valid register state *)
    iAssert (interp_reg interp W5 (<[PC:=inl 0%Z]> (<[r_adv:=inr (g, Global, b, e, a')]> rmap5))) as "#Hadv_reg_val_2".
    { iSplit.
      - iPureIntro. intros r. rewrite /= /rmap2. clear -Hr_all Hrmap_dom''.
        destruct (decide (r = PC));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        destruct (decide (r = r_adv));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        destruct (decide (r = r_stk));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        destruct (decide (r = r_t0));[subst;rewrite lookup_insert;eauto|rewrite lookup_insert_ne//].
        apply elem_of_gmap_dom. rewrite -Hrmap_dom''.
        rewrite dom_delete_L dom_insert_L !dom_delete_L dom_insert_L.
        apply regmap_full_dom in Hr_all as ->.
        pose proof (all_registers_s_correct r). clear Hrmap_dom''.
        set_solver.
      - iIntros (r Hner). rewrite /RegLocate lookup_insert_ne//.
        rewrite /= /rmap5.
        destruct (decide (r = r_adv));[subst;rewrite lookup_insert|rewrite lookup_insert_ne//].
        iApply interp_monotone_nm. eauto. auto. iFrame "Hadv_val".
        destruct (decide (r = r_stk));[subst;rewrite lookup_insert|rewrite lookup_insert_ne//].
        iFrame "Hadv_stack_val_2".
        destruct (decide (r = r_t0));[subst;rewrite lookup_insert|rewrite lookup_insert_ne//].
        iClear "∗ #". rewrite fixpoint_interp1_eq. eauto.
        destruct (rmap4 !! r) eqn:Hsome;rewrite Hsome.
        apply Hrmap_spec'' in Hsome. inv Hsome. all: iClear "∗ #"; rewrite fixpoint_interp1_eq; eauto. }

    iDestruct (read_allowedU_inv _ a_act_final with "Hstack_val") as "Ha_act_final_rel";[|auto|].
    { clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr. }

    (* for convenience we remember the awkward sts relation for W4 *)
    iDestruct (sts_full_rel_loc with "Hsts Hrel") as %Hrel.

    (* we must now finally prove the validity of the callback *)
    iMod (update_region_revoked_monotemp_updated with "[] Hsts Hr Ha_act_final [] Ha_act_final_rel") as "[Hr Hsts]".
    { auto. }
    { iClear "#". iModIntro. iIntros (W1' W2' Hrelated') "Hr". iApply interp_monotone_a. eauto. iFrame. }
    { iSimpl. iApply fixpoint_interp1_eq. iModIntro. iIntros (rmap6 Wmid2 HrelatedW5Wmid2).
      iNext.
      iIntros "(#[Hall Hregs_valid_2] & Hregs & Hr & Hsts & Hown)".
      iSplit;auto. iDestruct "Hall" as %Hr_all'. iClear "Hall".
      (* extract some registers *)
      iDestruct (big_sepM_delete _ _ PC with "Hregs") as "[HPC Hregs]"; [rewrite lookup_insert;eauto|].
      rewrite delete_insert_delete.

      (* we will first have to go through the activation record *)
      (* let's open the static region of W' *)
      (* we must therefore first attest that the local stack frame is still static in Wmid *)
      assert (std Wmid2 !! bstk = Some (Monostatic lframe')) as Hlframe2.
      { eapply related_sts_pub_a_world_static. 3: apply HrelatedW5Wmid2.
        - rewrite lookup_insert_ne.
          apply std_sta_update_multiple_lookup_in_i.
          rewrite elem_of_elements -elem_of_gmap_dom list_to_map_lookup_is_Some fst_zip.
          apply elem_of_region_addrs. 2: rewrite /= region_addrs_length /region_size.
          all: clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr.
        - clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr. }

      (* since we will need to change the static state, it is conveninent to first
         uninitialize the full stack, so we can revoke the local stack frame *)
      iDestruct (full_sts_monostatic_all with "Hsts Hr") as %Hall_mono';[apply Hlframe2|].
      iMod (uninitialize_region_keep _ bstk with "[$Hsts $Hr]") as (m2 Hmcond2) "[Hsts [Hr #Hvalids2] ]".

      (* then we can open the static region *)
      iMod (region_open_monostatic _ _ bstk with "[$Hr $Hsts]") as "(Hr & Hsts & Hstates & Hframe & %)".
      { rewrite uninitialize_std_sta_not_elem_of_lookup. apply Hlframe2. intros Hcontr%elem_of_gmap_dom%Hmcond2.
        destruct Hcontr as [Hcontr _]. rewrite Hlframe2 in Hcontr. done. }
      rewrite /static_resources.
      (* cleanup the resources *)
      iAssert (bstk ↦ₐ wret ∗ a_param ↦ₐ inr (RWX, Global, d, d', d)
            ∗ [[a_param2,a_act_final]]↦ₐ[[ actw' ]])%I with "[Hframe]" as "[Hbstk [Ha_param Hact]]".
      { iDestruct (big_sepM_to_big_sepL2 with "Hframe") as "Hframe".
        { apply region_addrs_NoDup. }
        { rewrite /= region_addrs_length /region_size.
          clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr. }
        do 2 (rewrite region_addrs_cons;[|clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr]).
        rewrite Ha_param Ha_param2.
        iDestruct "Hframe" as "(Hbstk & Ha_param & Hframe)".
        iDestruct "Hbstk" as (?) "[_ $]".
        iDestruct "Ha_param" as (?) "[_ $]".
        iApply (big_sepL2_mono with "Hframe").
        iIntros (k y1 y2 Hin1 Hin2) "H". iDestruct "H" as (?) "[_ $]". }

      (* apply the activation record *)
      specialize (Hr_all' r_t1) as Hr_t1'; specialize (Hr_all' r_stk) as Hr_stk';
        destruct Hr_t1' as [w1'' Hr_t1']; destruct Hr_stk' as [wstk'' Hr_stk'].
      iDestruct (big_sepM_delete _ _ r_t1 with "Hregs") as "[Hr_t1 Hregs]"; [rewrite lookup_delete_ne//|].
      iDestruct (big_sepM_delete _ _ r_stk with "Hregs") as "[Hr_stk Hregs]"; [rewrite !lookup_delete_ne//|].
      iApply (scallU_epilogue_spec with "[- $HPC $Hact $Hr_t1 $Hr_stk]");[| |auto..].
      { intros mid Hmid. constructor;auto. clear -Hmid Ha_param Ha_param2 Ha_param3 Ha_act_end. solve_addr. }
      { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Ha_act_end_next' Hsize. apply le_addr_withinBounds;solve_addr. }
      { iContiguous_next_a Hcont_code9. }
      { eapply (isCorrectPC_contiguous_range _ _ _ _ _ _ _ _ Hvpc_code9); eauto. repeat econstructor. }
      iNext. iIntros "(HPC & Hr_stk & Hr_t1 & Hact)".
      iDestruct "Hr_t1" as (rt1w') "Hr_t1".

      (* Next we continue the execution of the callback *)
      (* first we must open the invariant containing the program *)
      iMod (na_inv_acc with "Hf4 Hown") as "(>Hprog & Hown & Hcls)";auto.
      rewrite /awkward_example /awkward_instrs /irest.
      match goal with |- context [ ([∗ list] a_i;w_i ∈ (lprev ++ lcur ++ ?l3 ++ ?l4 ++ ?l5 ++ ?l6 ++ ?l7 ++ l_rest9);
                                   (iprev ++ icur ++ ?i3 ++ ?i4 ++ ?i5 ++ ?i6 ++ ?i7 ++ ?i_rest),_)%I ] =>
                      set lprev2 := (l3 ++ l4 ++ l5 ++ l6); set lcur2 := l7;
                      set iprev2 := (i3 ++ i4 ++ i5 ++ i6); set icur2 := i7; set irest2 := i_rest
      end.
      match goal with |- context [ ([∗ list] a_i;w_i ∈ ?l_addrs;?i_instrs, _)%I ] =>
                      set laddrs2 := l_addrs; set instrs2 := i_instrs
      end.
      assert (laddrs2 = (lprev ++ lcur ++ lprev2) ++ (lcur2 ++ l_rest9)) as ->;[rewrite /laddrs2 /lprev2 /lcur2;repeat rewrite -app_assoc //|].
      assert (instrs2 = (iprev ++ icur ++ iprev2) ++ (icur2 ++ irest2)) as ->;[rewrite /instrs2 /iprev2 /lcur2 /irest2;repeat rewrite -app_assoc //|].
      iDestruct (big_sepL2_app' with "Hprog") as "[Hprog_done Hprog]".
      { by rewrite /lprev /iprev /lcur /icur /lprev2 /iprev2 /= !app_length /= Hlength_code Hlength_code0 Hlength_code3 Hlength_code8 /=. }
      iDestruct (big_sepL2_app' with "Hprog") as "[Hcode Hprog]".
      { by rewrite /lcur2 /icur2 /=. }
      do 3 (iDestruct "Hcode" as "[Hi Hcode]";iCombine "Hi" "Hprog_done" as "Hprog_done").

      (* lea r_stk -6 *)
      assert (a_act_end' + (-6) = Some a_param2)%a as Hlea';[clear -Ha_act_end';solve_addr|].
      iPrologue "Hcode".
      iApply (wp_lea_success_z with "[$HPC $Hi $Hr_stk]");
        [apply decode_encode_instrW_inv|iCorrectPC l_code9 link9| |apply Hlea'|auto..].
      { eapply contiguous_between_last;[apply Hcont_code9|auto]. }
      { simpl. clear -Ha_act_end' Ha_act_final. solve_addr. }
      iEpilogue "(HPC & Hi & Hr_stk)"; iCombine "Hi" "Hprog_done" as "Hprog_done".
      iClear "Hcode".

      iPrologue_multi "Hprog" Hcont Hvpc link10.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code10.
      destruct_addr_list l_code10. clear Heq.
      apply contiguous_between_cons_inv_first in Hcont_code10 as Heq. subst link9.

      (* pop r_adv *)
      specialize (Hr_all' r_env) as Hr_env'; destruct Hr_env' as [wenv'' Hr_env'].
      iDestruct (big_sepM_delete _ _ r_env with "Hregs") as "[Hr_env Hregs]"; [rewrite !lookup_delete_ne//|].
      iApply (popU_spec with "[- $HPC $Hcode $Hr_stk $Hr_env $Ha_param $Hr_t1]").
      { split;[|split];iCorrectPC l_code10 link10. }
      { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize. apply le_addr_withinBounds;solve_addr. }
      { auto. }
      { iContiguous_next_a Hcont_code10. }
      { iContiguous_next_a Hcont_code10. }
      { eapply contiguous_between_last. apply Hcont_code10. auto. }
      { apply Ha_param2. }
      iNext. iIntros "(HPC & Hpop1 & Hr_env & Ha_param & Hr_stk & Hr_t1)".

      (* loadU r_t0 r_stk -1 *)
      specialize (Hr_all' r_t0) as Hr_t0'; destruct Hr_t0' as [w0'' Hr_t0'];
        iDestruct (big_sepM_delete _ _ r_t0 with "Hregs") as "[Hr_t0 Hregs]"; [rewrite !lookup_delete_ne//|].
      iPrologue_multi "Hprog" Hcont Hvpc link11.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code11.
      destruct_addr_list l_code11.
      apply contiguous_between_cons_inv_first in Hcont_code11 as Heq. subst link10.
      iPrologue "Hcode".
      iApply (wp_loadU_success with "[$HPC $Hi $Hr_t0 $Hr_stk $Hbstk]");
        [apply decode_encode_instrW_inv|iCorrectPC l_code11 link11|auto|
         |iContiguous_next_a Hcont_code11|apply Ha_param|].
      { clear -Hsize. apply le_addr_withinBounds;solve_addr. }
      iEpilogue "(HPC & Hr_t0 & Hprog_done0 & Hr_stk & Hbstk)".

      (* lets uninitialize the local stack frame *)
      iMod (region_close_monostatic_to_uninitialized with "[$Hsts $Hr Hact Hbstk Ha_param $Hstates]")
        as "[Hsts Hr]".
      { intros x1 x2 [Hin%list_to_map_lookup_is_Some Hle].
        destruct (m2 !! x2) eqn:Hsome.
        - assert (is_Some (m2 !! x2)) as [Htemp Hlex]%Hmcond2;[eauto|].
          rewrite (uninitialize_std_sta_lookup_in _ _ _ w2)//.
        - intros Hcontr. apply eq_None_not_Some in Hsome as Hnsome. apply Hnsome.
          rewrite uninitialize_std_sta_None_lookup// in Hcontr. apply Hmcond2.
          split;auto.
          rewrite fst_zip in Hin. apply elem_of_region_addrs in Hin. clear -Hle Hin. solve_addr.
          rewrite /= region_addrs_length /region_size.
          clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final. solve_addr. }
      { iClear "Hstack_conditions". rewrite /lframe'.
        iApply (big_sepL2_to_big_sepM).
        { apply region_addrs_NoDup. }
        do 2 (rewrite region_addrs_cons;[|clear -Ha_param Ha_param2 Ha_param3 Hsize Ha_act_end Ha_act_final;solve_addr]).
        rewrite Ha_param Ha_param2. iSimpl. iSplitL "Hbstk";[|iSplitL "Ha_param"].
        1,2: iExists interpC;iFrame;iSplit;[iPureIntro;apply _|];iFrame "#".
        1:(iDestruct (read_allowedU_inv with "Hstack_val") as "$";auto).
        1: clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr.
        iDestruct (read_allowedU_inv_range _ _ _ _ _ _ a_param2 a_act_final with "Hstack_val") as "Hrange";[|auto|].
        { clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr. }
        iDestruct (big_sepL2_to_big_sepL_l _ _ actw' with "Hrange") as "Hrange2".
        { rewrite /= region_addrs_length /region_size.
          clear -Ha_param Ha_param2 Ha_param3 Ha_act_end Ha_act_final Hsize;solve_addr. }
        iDestruct (big_sepL2_sep with "[$Hact $Hrange2]") as "Hact".
        iApply (big_sepL2_mono with "Hact").
        iIntros (k y1 y2 Hy1 Hy2) "[? ?]".
        iExists interpC. iFrame. iPureIntro. apply _. }

      (* load r_adv r_env *)
      specialize (Hr_all' r_adv) as Hr_adv'; destruct Hr_adv' as [wadv'' Hr_adv'];
        iDestruct (big_sepM_delete _ _ r_adv with "Hregs") as "[Hr_adv Hregs]"; [rewrite !lookup_delete_ne//|].
      iPrologue "Hcode".
      iInv ι as (y) "[>Hstate Hval]" "Hcls'".
      (* since we are in a public future world, we can assert that y is true *)
      iDestruct (sts_full_state_loc with "Hsts Hstate") as %Hstate.
      assert (y = true) as Hy.
      { destruct HrelatedW5Wmid2 as [_ [Hdom1 [Hdom2 Htrans] ] ].
        destruct HrelatedW2Wmid as [_ [Hdom1' [Hdom2' Htrans'] ] ].
        assert (is_Some (Wmid2.2.2 !! i)) as [r' Hr'].
        { apply elem_of_gmap_dom. apply elem_of_subseteq in Hdom2. apply Hdom2.
          apply elem_of_subseteq in Hdom2'.
          rewrite /W4 std_update_multiple_loc /= std_update_multiple_loc /=.
          apply Hdom2', elem_of_gmap_dom. rewrite /W1 /= std_update_multiple_loc /=. eauto. }
        destruct r' as [(r1' & r2') r3'].
        specialize (Htrans i _ _ _ _ _ _ Hrel Hr') as [Heq1 [Heq2 [Heq3 Htrans] ] ].
        subst r1' r2' r3'.
        assert ((<s[a_act_final:=Monotemporary]s>W4).2.1 !! i = Some (encode true)) as Hi.
        { rewrite /W4 /= std_update_multiple_loc /= lookup_insert//. }
        rewrite /override_uninitialize /= in Hstate.
        specialize (Htrans _ _ Hi Hstate).
        apply rtc_rel_pub'. eapply rtc_implies. 2: apply Htrans. simpl. intros r q [Hrq | Hrq];eauto. }
      subst y. iDestruct "Hval" as ">Hval".
      iApply (wp_load_success_notinstr with "[$HPC $Hi $Hr_adv $Hr_env $Hval]");
        [apply decode_encode_instrW_inv|iCorrectPC l_code11 link11|..].
      { split;auto. }
      { eapply contiguous_between_last. apply Hcont_code11. auto. }
      iNext. iIntros "(HPC & Hr_adv & Hi & Hr_env & Hd)".
      iMod ("Hcls'" with "[Hd Hstate]") as "_".
      { iExists true. iFrame. }
      iModIntro. iApply wp_pure_step_later;auto;iNext.
      iCombine "Hi" "Hprog_done0" as "Hprog_done0".

      (* now we know the following assert will succeed *)
      iClear "Hcode".
      iPrologue_multi "Hprog" Hcont Hvpc link12.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code12.

      specialize (Hr_all' r_t2) as Hr_t2'; destruct Hr_t2' as [w2'' Hr_t2'];
        iDestruct (big_sepM_delete _ _ r_t2 with "Hregs") as "[Hr_t2 Hregs]"; [rewrite !lookup_delete_ne//|].
      specialize (Hr_all' r_t3) as Hr_t3'; destruct Hr_t3' as [w3'' Hr_t3'];
        iDestruct (big_sepM_delete _ _ r_t3 with "Hregs") as "[Hr_t3 Hregs]"; [rewrite !lookup_delete_ne//|].

      iMod (na_inv_acc with "Htable Hown") as "([Hpc_b Ha_entry] & Hown & Hcls')". auto. solve_ndisj.
      iApply (assert_r_z_success with "[- $HPC $Hcode $Hr_adv $Hpc_b $Ha_entry]");
        [apply Hvpc_code12|apply Hcont_code12|auto|auto|auto|].
      iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|]. iSplitL "Hr_t3";[eauto|].
      iNext. iIntros "(Hr_t1 & Hr_t2 & Hr_t3 & Hr_adv & HPC & Hassert & Hpc_b & Ha_entry)".
      iMod ("Hcls'" with "[$Hown $Hpc_b $Ha_entry]") as "Hown".

      (* finally we will clear the register state *)
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t3]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -!(delete_insert_ne _ _ r_t3)//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t2]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -!(delete_insert_ne _ _ r_t2)//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_adv]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -!(delete_insert_ne _ _ r_adv)//. rewrite !(delete_commute _ r_t0)//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_env]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -!(delete_insert_ne _ _ r_env)//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_stk]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -!(delete_insert_ne _ _ r_stk)//.
      iDestruct (big_sepM_insert with "[$Hregs $Hr_t1]") as "Hregs";[apply lookup_delete|].
      rewrite insert_delete -!(delete_insert_ne _ _ r_t1)//.

      iPrologue_multi "Hprog" Hcont Hvpc link13.
      iDestruct (big_sepL2_length with "Hcode") as %Hlength_code13.
      (* destruct l_code13;[inversion Hlength_code13|]. *)
      (* apply contiguous_between_cons_inv_first in Hcont_code13 as Heq. subst a14. *)

      iApply (rclear_spec_gmap with "[- $HPC $Hcode $Hregs]");
        [apply Hcont_code13|clear;set_solver| |apply Hvpc_code13|..].
      { clear -Hlength_code13 Hcont_code13. rewrite rclear_length in Hlength_code13.
        assert (r_t2 ∈ (list_difference all_registers [PC; r_t1])) as Hin.
        { apply elem_of_list_difference. split;[apply all_registers_correct|set_solver]. }
        destruct l_code13.
        { simpl in Hlength_code13. by rewrite (nil_length_inv (list_difference all_registers [PC; r_t1])) in Hin;auto. }
        apply contiguous_between_cons_inv_first in Hcont_code13. clear -Hcont_code13. subst;auto. }
      { rewrite !dom_delete_L !dom_insert_L. apply regmap_full_dom in Hr_all' as ->. clear. set_solver. }

      (* we are reaching the end of the program, in which we return to the caller *)
      (* let's begin by extracting the validity of wret in W *)
      iAssert (▷ (interp W wret ∗ future_pub_a_mono bstk interpC wret))%I as "#(Hret_val & Hret_mono)".
      { assert (m !! bstk = Some wret) as Hsomewret.
        { assert (is_Some (m !! bstk)) as [wret' Hmbstk].
          apply Hmcond. split;auto. clear;solve_addr.
          rewrite (uninitialize_std_sta_lookup_in _ _ _ wret')// in Hwret. inv Hwret. auto. }
        iDestruct (big_sepM_lookup with "Hvalids") as "Hwret". apply Hsomewret.
        iDestruct "Hwret" as (φ' Hpersφ') "((#Hmono & #Hwret_valid) & #Hrelwret)".
        iDestruct (rel_agree _ interpC φ' with "[$Hrelwret $Hcond2]") as "Heq". iNext.
        iSplit. iSpecialize ("Heq" $! (W,wret)). iSimpl in "Heq". rewrite /interp. iSimpl. iRewrite "Heq".
        iFrame "Hwret_valid".
        iModIntro. iIntros (W1' W2' Hrelated') "#Hval". iDestruct ("Heq" $! (W2',wret)) as "Heq1". iRewrite "Heq1".
        iApply "Hmono". eauto. iDestruct ("Heq" $! (W1',wret)) as "Heq2". iRewrite -"Heq2". iFrame "Hval". }

      iNext. iIntros "(HPC & Hrmap & Hrclear)".
      iDestruct "Hrmap" as (rmap7) "(Hregs & Hspec)".
      iDestruct "Hspec" as %(Hrmap_dom2 & Hrmap_spec2).

      set (maddrs := (filter (λ a, a < bstk)%a (elements (dom (gset Addr) m) ++ elements (dom (gset Addr) m')))).
      set (Wfinal := initialize_list maddrs (override_uninitialize lframe' (uninitialize Wmid2 m2))).
      assert (∀ a14 : Addr, a14 ∈ dom (gset Addr) lframe → Wmid.1 !! a14 = Some (Monostatic lframe)).
      { intros x Hx. apply Hall_mono in Hx. rewrite /monostatic in Hx.
        destruct (Wmid.1 !! x) eqn:Hsome;[|inversion Hx]. subst r. auto. }
      assert (∀ a14 : Addr, a14 ∈ dom (gset Addr) lframe' → Wmid2.1 !! a14 = Some (Monostatic lframe')).
      { intros x Hx. apply Hall_mono' in Hx. rewrite /monostatic in Hx.
        destruct (Wmid2.1 !! x) eqn:Hsome;[|inversion Hx]. subst r. auto. }
      assert (related_sts_a_world W Wfinal bstk) as HrelatedWWfinal.
      { eapply (awkward_world_reconstruct W W' W1 W2 Wmid W3 W4 W5 Wmid2 Wfinal m m' m2
                 maddrs lframe' lframe bstk estk a_param a_param2 a_param3 frame_end a_act_final
                 a_act_end a_act_end' i). all: auto. }
      assert (related_sts_a_world Wmid Wfinal bstk) as HrelatedWmidWfinal.
      { eapply (awkward_world_reconstruct_mid W W' W1 W2 Wmid W3 W4 W5 Wmid2 Wfinal m m' m2
                 maddrs lframe' lframe bstk estk a_param a_param2 a_param3 frame_end a_act_final
                 a_act_end a_act_end' i). all: auto. }

      iDestruct (big_sepL2_length with "Hprog") as %Hprog_length14.
      destruct_addr_list l_rest13.
      apply contiguous_between_cons_inv_first in Hcont as Heq. subst l_rest13.
      iPrologue "Hprog".
      iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
        [apply decode_encode_instrW_inv|iCorrectPC link13 a_last|].

      iDestruct ("Hret_mono" $! W Wfinal HrelatedWWfinal with "Hret_val") as "Hret_val_final".
      iDestruct (jmp_or_fail_spec with "Hret_val_final") as "Hcont'".
      iSimpl in "Hcont'".
      destruct (decide (isCorrectPC (updatePcPerm wret))).
      2: { iEpilogue "(HPC & Hi & Hr_t1)". iApply "Hcont'". iFrame "HPC". iIntros (Hcontr);inversion Hcontr. }
      iDestruct ("Hcont'") as (pret gret bret eret aret ->) "Hcont'".
      iDestruct ("Hcont'" $! (<[PC:=inl 0%Z]> (<[r_t0 := inr (pret, gret, bret, eret, aret)]> rmap7))
                          Wfinal with "[]") as "Hcont_final".
      { iClear "#". clear.
        destruct gret;simpl;iPureIntro;
          [apply related_sts_priv_refl_world..|
                 apply related_sts_a_refl_world]. }
      iEpilogue "(HPC & Hi & Hr_t0)".

      iMod ("Hcls" with "[Hown Hprog_done Hpop1 Hprog_done0 Hassert Hrclear Hi]") as "Hown".
      { iSplitR "Hown". 2: iFrame. iNext.
        rewrite /iprev2 /icur2 /irest2. iDestruct "Hprog_done" as "(H1&H2&H3&H4&H5)".
        iSplitL "H5". iFrame. rewrite /lcur2. iFrame "H4 H3 H2 H1". iSplit;[done|].
        iFrame "Hpop1". iDestruct "Hprog_done0" as "($&$&$)". iFrame "Hassert Hrclear Hi". iSplit;done. }
      iClear "Hprog Hcont'".

      iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs".
      { apply not_elem_of_dom. rewrite Hrmap_dom2. rewrite elem_of_list_to_set. apply not_elem_of_list. repeat constructor. }
      iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
      { rewrite lookup_insert_ne//. apply not_elem_of_dom. rewrite Hrmap_dom2. rewrite elem_of_list_to_set.
        apply not_elem_of_list. repeat constructor. }
      rewrite -(insert_insert _ PC (updatePcPerm _) (inl 0%Z)).

      iMod (initialize_list_region _ maddrs with "[$Hsts $Hr]") as "[Hsts Hr]".
      { iApply big_sepL_forall.
        iIntros (k x Hin). iModIntro. assert (x ∈ maddrs) as Hin';[apply elem_of_list_lookup;eauto|].
        assert (∀ x, (x < bstk)%a → lframe' !! x = None
                                    ∧ m2 !! x = None
                                    ∧ lframe !! x = None
                                    ∧ bstk ≠ x) as Hxcond.
        { intros y Hlt. split;[|split;[|split ] ].
          - apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_region_addrs.
            clear -Hlt;solve_addr. rewrite /= region_addrs_length /region_size.
            clear -Ha_param Ha_param2 Ha_param3 Ha_act_final;solve_addr.
          - apply eq_None_not_Some. intros [_ Hcontr]%Hmcond2. clear -Hlt Hcontr. solve_addr.
          - apply not_elem_of_list_to_map. rewrite fst_zip. apply not_elem_of_region_addrs.
            clear -Hlt;solve_addr. rewrite /= region_addrs_length /region_size.
            clear -Ha_param Ha_param2 Ha_param3 Ha_act_end;solve_addr.
          - clear -Hlt;solve_addr. }
        assert (∀ x, (x < bstk)%a → x ∉ region_addrs a_param a_act_end
                                    ∧ a_act_final ≠ x
                                    ∧ (x < a_act_final)%a) as Hxcond1.
        { intros y Hlt. split;[|split].
          - apply not_elem_of_region_addrs. clear -Ha_param Hlt. solve_addr.
          - clear -Hlt Ha_param Ha_param2 Ha_param3 Ha_act_final;solve_addr.
          - clear -Hlt Ha_param Ha_param2 Ha_param3 Ha_act_final;solve_addr. }
        assert (∀ x, (x < bstk)%a → x ∉ region_addrs a_param frame_end
                                    ∧ a_act_end ≠ x
                                    ∧ (x < a_act_end)%a) as Hxcond2.
        { intros y Hlt. split;[|split].
          - apply not_elem_of_region_addrs. clear -Ha_param Hlt. solve_addr.
          - clear -Hlt Ha_param Ha_param2 Ha_param3 Ha_act_end;solve_addr.
          - clear -Hlt Ha_param Ha_param2 Ha_param3 Ha_act_end;solve_addr. }

        rewrite /maddrs filter_app in Hin'.
        destruct (decide (x ∈ filter (λ a : Addr, (a < bstk)%a) (elements (dom (gset Addr) m')))).
        - apply elem_of_list_filter in e0 as [Hlt Hin0%elem_of_elements%elem_of_gmap_dom].
          apply Hmcond' in Hin0 as Hcond. destruct Hcond as [Htemp _].
          destruct Hin0 as [ww Hww].
          destruct Hxcond with x as (?&?&?&?);auto. destruct Hxcond1 with x as (?&?&?);auto.
          iDestruct (big_sepM_lookup with "Hvalids'") as "#Hww". apply Hww.
          assert (W5.1 !! x = Some (Uninitialized ww)) as Hww5.
          { rewrite lookup_insert_ne// std_sta_update_multiple_lookup_same_i.
            2: rewrite elem_of_elements -elem_of_gmap_dom;apply eq_None_not_Some;auto.
            rewrite std_sta_update_multiple_lookup_same_i// lookup_insert_ne//
                    override_uninitialize_std_sta_lookup_none//
                    (uninitialize_std_sta_lookup_in _ _ _ ww)//. }
          apply related_sts_pub_a_world_uninitialized with (i:=x) (w:=ww) in HrelatedW5Wmid2;auto.
          iDestruct "Hww" as (φ0 Hpers0) "[Hmonotemp Hrelx]".
          iExists φ0,ww. iFrame "Hrelx". iSplit.
          rewrite override_uninitialize_std_sta_lookup_none// uninitialize_std_sta_None_lookup//.
          destruct HrelatedW5Wmid2 as [Htempx | Huninit];auto.
          iSplit;[auto|]. iDestruct "Hmonotemp" as "[Hpub Hφ]". iFrame "Hpub".
          iApply "Hpub". iPureIntro. apply related_sts_a_weak_world with bstk. clear -Hlt;solve_addr.
          apply HrelatedWmidWfinal. iFrame "Hφ".
        - apply elem_of_app in Hin'
          as [ [Hlt Hin'%elem_of_elements%elem_of_gmap_dom]%elem_of_list_filter
             | Hcontr];[|congruence].
          apply Hmcond in Hin' as Hcond. destruct Hcond as [Htemp _].
          destruct Hin' as [ww Hww].
          destruct Hxcond with x as (?&?&?&?);[auto|]. destruct Hxcond2 with x as (?&?&?);[auto|].
          assert (W2.1 !! x = Some (Uninitialized ww)) as Hww2.
          { rewrite lookup_insert_ne// std_sta_update_multiple_lookup_same_i.
            2: rewrite elem_of_elements -elem_of_gmap_dom;apply eq_None_not_Some;auto.
            rewrite std_sta_update_multiple_lookup_same_i// lookup_insert_ne//
                    (uninitialize_std_sta_lookup_in _ _ _ ww)//. }
          apply related_sts_pub_a_world_uninitialized with (i:=x) (w:=ww) in HrelatedW2Wmid;[|auto..].
          destruct HrelatedW2Wmid as [Htempx | Huninit].
          + assert (is_Some (m' !! x)) as [vv Hvv].
            { apply Hmcond'. split;auto. clear;solve_addr. }
            destruct Hxcond1 with x as (?&?&?);[auto|].
            assert (W5.1 !! x = Some (Uninitialized vv)) as Hww5.
            { rewrite lookup_insert_ne// std_sta_update_multiple_lookup_same_i.
              2: rewrite elem_of_elements -elem_of_gmap_dom;apply eq_None_not_Some;auto.
              rewrite std_sta_update_multiple_lookup_same_i// lookup_insert_ne//
                      override_uninitialize_std_sta_lookup_none//
                      (uninitialize_std_sta_lookup_in _ _ _ vv)//. }
            iDestruct (big_sepM_lookup with "Hvalids'") as "#Hww". apply Hvv.
            apply related_sts_pub_a_world_uninitialized with (i:=x) (w:=vv) in HrelatedW5Wmid2;[|auto..].
            iDestruct "Hww" as (φ0 Hpers0) "[Hmonotemp Hrelx]".
            iExists φ0,vv. iFrame "Hrelx". iSplit.
            rewrite override_uninitialize_std_sta_lookup_none// uninitialize_std_sta_None_lookup//.
            destruct HrelatedW5Wmid2 as [Htempx' | Huninit];auto.
            iSplit;[auto|]. iDestruct "Hmonotemp" as "[Hpub Hφ]". iFrame "Hpub".
            iApply "Hpub". iPureIntro. apply related_sts_a_weak_world with bstk. clear -Hlt;solve_addr.
            apply HrelatedWmidWfinal. iFrame "Hφ".
          + destruct Hxcond1 with x as (?&?&?);[auto|].
            assert (m' !! x = None) as Hnone.
            { apply eq_None_not_Some. intros [Hcontr _]%Hmcond'. congruence. }
            assert (W5.1 !! x = Some (Uninitialized ww)) as Hww5.
            { rewrite lookup_insert_ne// std_sta_update_multiple_lookup_same_i.
              2: rewrite elem_of_elements -elem_of_gmap_dom;apply eq_None_not_Some;auto.
              rewrite std_sta_update_multiple_lookup_same_i// lookup_insert_ne//
                      override_uninitialize_std_sta_lookup_none//
                      uninitialize_std_sta_None_lookup//. }
            iDestruct (big_sepM_lookup with "Hvalids") as "#Hww". apply Hww.
            apply related_sts_pub_a_world_uninitialized with (i:=x) (w:=ww) in HrelatedW5Wmid2;[|auto..].
            iDestruct "Hww" as (φ0 Hpers0) "[Hmonotemp Hrelx]".
            iExists φ0,ww. iFrame "Hrelx". iSplit.
            rewrite override_uninitialize_std_sta_lookup_none// uninitialize_std_sta_None_lookup//.
            destruct HrelatedW5Wmid2 as [Htempx' | Huninit'];auto.
            iSplit;[auto|]. iDestruct "Hmonotemp" as "[Hpub Hφ]". iFrame "Hpub".
            iApply "Hpub". iPureIntro. apply related_sts_a_weak_world with bstk. clear -Hlt;solve_addr.
            apply HrelatedWWfinal. iFrame "Hφ". }

      iDestruct ("Hcont_final" with "[$Hr $Hsts $Hown $Hregs]") as "[_ Hφ]".
      { iSplit.
        - iPureIntro. intros x. apply elem_of_gmap_dom. rewrite /= !dom_insert_L.
          rewrite Hrmap_dom2. clear. pose proof (all_registers_correct x). set_solver.
        - iIntros (r Hne'). rewrite /RegLocate. rewrite lookup_insert_ne//.
          destruct (decide (r = r_t0));[subst;rewrite lookup_insert|]. iFrame "Hret_val_final".
          rewrite lookup_insert_ne;[|auto]. rewrite Hrmap_spec2. iClear "#". rewrite fixpoint_interp1_eq. done.
          rewrite Hrmap_dom2 elem_of_list_to_set.
          apply elem_of_list_difference. split;[apply all_registers_correct|clear -Hne' n;set_solver]. }
      iApply (wp_wand with "Hφ").
      iIntros (v) "Hv". iIntros (Hv).
      iDestruct ("Hv" $! Hv) as (r W'') "(Hregval & Hregs & #Hrelated & Hown & Hsts & Hr)".
      iExists r,W''. iFrame. iDestruct "Hrelated" as %Hrelated''. iPureIntro.
      apply related_sts_priv_trans_world with Wfinal;auto.
      rewrite /Wfinal. apply uninitialize_related_pub_a in Hmcond2 as Hrelated'.
      eapply related_sts_a_priv_trans_world. apply Hrelated'.
      eapply related_sts_a_priv_trans_world with (a:=bstk).
      apply related_sts_pub_world_monostatic_to_uninitialized with lframe'.
      3: apply related_sts_pub_priv_world,initialize_list_related_pub.
      { intros x Hx%elem_of_gmap_dom%Hall_mono'.
        rewrite /monostatic in Hx. destruct (Wmid2.1 !! x) eqn:Hsome;[|inversion Hx].
        subst r0.
        assert (m2 !! x = None) as Hnone.
        { apply eq_None_not_Some. intros [Hcontr _]%Hmcond2. rewrite Hsome in Hcontr. done. }
        rewrite uninitialize_std_sta_None_lookup//. }
      { intros x Hx%list_to_map_lookup_is_Some. rewrite fst_zip in Hx.
        apply elem_of_region_addrs in Hx as [? ?];auto.
        rewrite /= region_addrs_length /region_size. clear -Ha_param Ha_param2 Ha_param3 Ha_act_final. solve_addr. }
    }

    iDestruct ("Hcall_2" with "[$Hna $Hr $Hsts $Hadv_reg_val_2 HPC Hregs]") as "[_ Hwp]".
    { rewrite /rmap5. rewrite insert_insert. iApply big_sepM_insert. 2: iFrame.
      apply not_elem_of_dom. rewrite !dom_insert_L -Hrmap_dom'' dom_delete_L dom_insert_L !dom_delete_L dom_insert_L. apply regmap_full_dom in Hr_all as ->. clear. set_solver. }
    iApply (wp_wand with "Hwp"). iIntros (v) "Hcond". iIntros (Hv).
    iDestruct ("Hcond" $! Hv) as (r Wfinal) "(?&?&%&?&?&?)".
    iExists _,_. iFrame. iPureIntro. eapply related_sts_priv_trans_world. apply HrelatedWmidW5. auto. }

    iDestruct ("Hcall" with "[$Hna $Hr $Hsts $Hadv_reg_val HPC Hregs]") as "[_ Hwp]".
    { rewrite /rmap2. rewrite insert_insert. iApply big_sepM_insert. 2: iFrame.
      apply not_elem_of_dom. rewrite !dom_insert_L -Hrmap_dom' !dom_insert_L !dom_delete_L Hrmap_dom.
      clear. set_solver. }
    iApply (wp_wand with "Hwp"). iIntros (v) "Hcond". iApply "Hφ". iIntros (Hv).
    iDestruct ("Hcond" $! Hv) as (r Wfinal) "(?&?&%&?&?&?)".
    iExists _,_. iFrame. iPureIntro. eapply related_sts_priv_trans_world. apply HrelatedWW2. auto.
    Unshelve. apply Hrevoked_2. all: try apply _. auto.
  Qed.

End awkward_example.
