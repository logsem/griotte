From iris.algebra Require Import frac.
From iris.proofmode Require Import tactics.
Require Import Eqdep_dec List.
From cap_machine Require Import rules rules_LoadU_derived.
From cap_machine Require Import rules_binary rules_binary_LoadU_derived.
From cap_machine Require Export iris_extra addr_reg_sample contiguous stack_macros_helpers.
From cap_machine.binary_model.examples_binary Require Import macros_binary.
From cap_machine Require Import macros.

From cap_machine.binary_model Require Import logrel_binary fundamental_binary region_invariants_batch_uninitialized_binary.

Ltac iPrologue_s prog :=
  let str_destr := constr:(("(Hsi & " ++ prog ++ ")")%string) in
  iDestruct prog as str_destr.

Ltac iEpilogue_s :=
   iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj";auto;
   iSimpl in "Hj".

Section conf.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ} {cfg : cfgSG Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_invariants_binary.region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Definition conf_instrs z :=
    prepstackU_instrs r_stk 1 1 ++
    [loadU_r_z r_t0 r_stk (-1); (* since parameters are passer on the stack, no need to check that the input is below the stack bound *)
    pushU_z_instr r_stk z] ++
    rclear_instrs (list_difference all_registers [PC;r_t0]) ++
    [jmp r_t0].


  Definition conf1 a z1 :=
    ([∗ list] a_i;w_i ∈ a;(conf_instrs z1), a_i ↦ₐ w_i)%I.
  Definition conf2 a z2:=
    ([∗ list] a_i;w_i ∈ a;(conf_instrs z2), a_i ↣ₐ w_i)%I.


  Lemma conf_spec_12 z1 z2 (* stack values *)
        W pc_p pc_g pc_b pc_e (* PC *)
        conf_addrs (* program addresses: same for implementation and specification *)
        a_first a_last (* special adresses *)
        wstk wstk' (* stack *)
        rmap rmap' (* registers *)
        ι1 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between conf_addrs a_first a_last ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk]} →
    dom (gset RegName) rmap' = all_registers_s ∖ {[PC;r_stk]} →

    {{{ spec_ctx ∗ ⤇ Seq (Instr Executable)
      ∗ r_stk ↦ᵣ wstk
      ∗ r_stk ↣ᵣ wstk'
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      ∗ ([∗ map] r_i↦w_i ∈ rmap', r_i ↣ᵣ w_i)
      (* stack *)
      ∗ interp W (wstk,wstk')
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (conf1 conf_addrs z1 ∗ conf2 conf_addrs z2)
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
             ∃ r W', ⤇ of_val HaltedV
                   ∗ full_map r
                   ∗ registers_mapsto r.1
                   ∗ spec_registers_mapsto r.2
                   ∗ ⌜related_sts_priv_world W W'⌝
                   ∗ na_own logrel_nais ⊤
                   ∗ sts_full_world W'
                   ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hcont Hrdom Hsdom φ) "(#Hspec & Hj & Hr_stk & Hs_stk & HPC & HsPC & Hrmap
    & Hsmap & #Hstk_valid & Hown & #Hconfprogs & Hsts & Hr) Hφ".
    iDestruct (interp_eq with "Hstk_valid") as %<-.
    iMod (na_inv_acc with "Hconfprogs Hown") as "([>Hprog >Hsprog] & Hown & Hcls)";auto.
    (* Get registers from implementation and specification side of the code *)
    assert (is_Some (rmap !! r_t0)) as [w0 Hw0];[apply elem_of_gmap_dom;rewrite Hrdom;set_solver+|].
    assert (is_Some (rmap !! r_t1)) as [w1 Hw1];[apply elem_of_gmap_dom;rewrite Hrdom;set_solver+|].
    assert (is_Some (rmap !! r_t2)) as [w2 Hw2];[apply elem_of_gmap_dom;rewrite Hrdom;set_solver+|].
    assert (is_Some (rmap' !! r_t0)) as [w0' Hsw0];[apply elem_of_gmap_dom;rewrite Hsdom;set_solver+|].
    assert (is_Some (rmap' !! r_t1)) as [w1' Hsw1];[apply elem_of_gmap_dom;rewrite Hsdom;set_solver+|].
    assert (is_Some (rmap' !! r_t2)) as [w2' Hsw2];[apply elem_of_gmap_dom;rewrite Hsdom;set_solver+|].
    iDestruct (big_sepM_delete with "Hrmap") as "[Hr_t0 Hrmap]";[apply Hw0|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hrmap") as "[Hr_t1 Hrmap]";[rewrite lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hrmap") as "[Hr_t2 Hrmap]";[rewrite !lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete with "Hsmap") as "[Hs_t0 Hsmap]";[apply Hsw0|].
    iDestruct (big_sepM_delete _ _ r_t1 with "Hsmap") as "[Hs_t1 Hsmap]";[rewrite lookup_delete_ne//;eauto|].
    iDestruct (big_sepM_delete _ _ r_t2 with "Hsmap") as "[Hs_t2 Hsmap]";[rewrite !lookup_delete_ne//;eauto|].
    (* prepstackU *)
    iPrologue_multi "Hprog" Hcont Hvpc link.
    iDestruct (big_sepL2_length with "Hcode") as %Hcode_length.
    iDestruct (big_sepL2_app' with "Hsprog") as "[Hscode Hsprog]";auto.
    iMod (prepstackU_s_spec with "[$HsPC $Hscode $Hs_stk $Hspec $Hj Hs_t1 Hs_t2 ]") as "H";[eauto..|].
    { iSplitL "Hs_t1";eauto. }
    iApply (prepstackU_spec with "[- $HPC $Hcode $Hr_stk]");[eauto..|].
    iSplitL "Hr_t1";[eauto|]. iSplitL "Hr_t2";[eauto|].
    iNext. destruct (isPermWord wstk URWLX) eqn:Hperm;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    (* cleanup of stack information *)
    destruct wstk as [| [ [ [ [p_stk l_stk] b_stk] e_stk] a_stk] ];[inversion Hperm|]. iExists l_stk,b_stk, e_stk, a_stk.
    destruct p_stk;inversion Hperm. iSplit;auto.
    iDestruct "H" as (l b e a' Heq) "H". inversion Heq. subst l b e a'.
    destruct (1%nat + 1%nat <? e_stk - b_stk)%Z eqn:Hsize;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    destruct (b_stk + 1%nat <=? a_stk)%Z eqn:Hle;[|(* Failure *) iApply "Hφ";iIntros (Hcontr);inversion Hcontr].
    iDestruct (writeLocalAllowedU_implies_local with "Hstk_valid") as %Hmonotone;auto. destruct l_stk;inversion Hmonotone.
    iIntros "Hstack".
    iDestruct "Hstack" as (a Ha) "(HPC & Hprepstack & Hr_stk & Hr_t1 & Hr_t2)".
    iDestruct "H" as (a' Ha') "(Hj & HsPC & Hsprepstack & Hs_stk & Hs_t1 & Hs_t2)".
    clear Heq. assert (a = a') as Heq;[clear -Ha Ha';solve_addr|subst a';clear Ha'].
    revert Hsize Hle; rewrite Z.ltb_lt Z.leb_le =>Hsize Hle.

    (* pop r_stk r_t0 *)
    (* in order to pop, we must first open the region at b_stk *)
    iDestruct (writeLocalAllowedU_valid_cap_below_implies _ _ _ _ _ _ b_stk with "Hstk_valid") as %Ha_param_W;[auto|..].
    { clear -Hle Hsize Ha. rewrite andb_true_iff Z.leb_le Z.ltb_lt. solve_addr. }
    { clear -Hle. solve_addr. }
    iDestruct (read_allowedU_inv _ b_stk with "Hstk_valid") as  "Hrel";[clear -Hsize;solve_addr|auto|].
    iDestruct (region_open_monotemp with "[$Hr $Hsts $Hrel]") as (wret wret') "(Hr & Hsts & Hstate & Hb_stk & Hb_stk' & #Hmono & #Hwret_valid)";auto.
    iSimpl in "Hwret_valid".
    iAssert (▷ ⌜wret = wret'⌝)%I as "#><-".
    { iNext. iDestruct (interp_eq with "Hwret_valid") as %->. auto. }
    (* loadU r_t0 r_stk -1 *)
    iPrologue_multi "Hprog" Hcont Hvpc link0.
    iDestruct (big_sepL2_length with "Hcode") as %Hcode_length0.
    iDestruct (big_sepL2_app' with "Hsprog") as "[Hscode Hsprog]";auto.
    destruct_addr_list l_code0.
    iPrologue "Hcode". apply contiguous_between_cons_inv_first in Hcont_code0 as Heq. subst link.
    iApply (rules_LoadU_derived.wp_loadU_success with "[$HPC $Hi $Hr_t0 $Hr_stk $Hb_stk]");
      [apply decode_encode_instrW_inv|iCorrectPC l_code0 link0|auto..].
    { clear -Hle Hsize Ha. rewrite andb_true_iff Z.leb_le Z.ltb_lt. solve_addr. }
    { iContiguous_next_a Hcont_code0. }
    iEpilogue "(HPC & Hr_t0 & Hprog_done & Hr_stk & Hb_stk)".
    iPrologue_s "Hscode".
    iMod (step_loadU_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0 $Hs_stk $Hb_stk']")
      as "(Hj & HsPC & Hs_t0 & Hsprog_done & Hs_stk & Hb_stk')";
      [apply decode_encode_instrW_inv|iCorrectPC l_code0 link0|auto..].
    { clear -Hle Hsize Ha. rewrite andb_true_iff Z.leb_le Z.ltb_lt. solve_addr. }
    { iContiguous_next_a Hcont_code0. }
    iEpilogue_s.
    (* we can close the world again *)
    iDestruct (region_close_monotemp with "[$Hstate $Hb_stk $Hb_stk' $Hr $Hrel $Hmono $Hwret_valid]") as "Hr";auto.

    (* pushu r_stk r_env *)
    (* we have reached a part of the code which will require us to make a pub^b_stk change to the world *)
    (* we will therefore first uninitialize all addresses at or above b_stk *)
    iMod (uninitialize_region _ b_stk with "[$Hsts $Hr]") as (m Hmcond) "[Hsts Hr]".
    (* next we can open the region at b_stk, which we will first assert is in m *)
    iDestruct (valid_uninitialized_condition _ m with "Hstk_valid") as %Hstk_cond;auto.
    (* next we can open the world at a *)
    assert (b_stk <= a < e_stk)%a as Hstk_bounds.
    { split;[clear -Ha;solve_addr|]. clear -Hsize Ha. solve_addr. }
    pose proof (Hstk_cond a Hstk_bounds) as [ [v1 v2] Hw].
    iDestruct (read_allowedU_inv _ a with "Hstk_valid") as "Hrel'";[clear -Hsize Ha;solve_addr|auto|].
    iDestruct (region_open_uninitialized with "[$Hrel' $Hr $Hsts]") as "(Hr & Hsts & Hstate & Ha & Ha')";[eauto|..].
    (* and we are ready to push a new value b_stk *)
    assert (is_Some (a + 1))%a as [b_stk1 Hb_next].
    { clear -Hstk_bounds. destruct (a + 1)%a eqn:Hsome;eauto. exfalso. solve_addr. }
    iDestruct "Hcode" as "[HpushU _]".
    iDestruct "Hscode" as "[HspushU _]".
    assert ((a0 + 1)%a = Some link0) as Hlast.
    { eapply contiguous_between_last;eauto. }
    iApply (pushU_z_spec with "[- $HPC $HpushU $Hr_stk $Ha]");
      [iCorrectPC l_code0 link0| |apply Hlast|apply Hb_next|..].
    { apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];clear -Hstk_bounds;solve_addr. }
    iNext. iIntros "(HPC & HpushU & Hr_stk & Hb_stk)".
    iMod (push_pop_binary.pushU_z_spec with "[$Hspec $Hj $HsPC $HspushU $Hs_stk $Ha']")
      as "(Hj & HsPC & HspushU & Hs_stk & Hb_stk')";
      [iCorrectPC l_code0 link0| |apply Hlast|apply Hb_next|auto..].
    { apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];clear -Hstk_bounds;solve_addr. }
    (* we can now close the world again *)
    pose proof (uninitialized_condition _ _ _ Hmcond) as Hmcond_alt.
    iMod (uninitialize_open_region_change _ _ a with "[$Hb_stk $Hb_stk' $Hrel' $Hsts $Hr $Hstate]") as "[Hr Hsts]";
      [clear;solve_addr|auto|].
    { intros. apply Hmcond_alt. clear -H0 Ha. solve_addr. }

    (* and we can now finish executing the instructions without more changes to W *)
    (* rclear RegName/{PC;r_t0} *)
    iPrologue_multi "Hprog" Hcont Hvpc link1.
    iDestruct (big_sepL2_length with "Hcode") as %Hcode_length1.
    iDestruct (big_sepL2_app' with "Hsprog") as "[Hscode Hsprog]";auto.

    iDestruct (big_sepM_insert with "[$Hrmap $Hr_t2]") as "Hrmap";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hrmap $Hr_t1]") as "Hrmap";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert with "[$Hrmap $Hr_stk]") as "Hrmap".
    { rewrite lookup_insert_ne// lookup_delete_ne// !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hrdom. set_solver-. }

    iDestruct (big_sepM_insert with "[$Hsmap $Hs_t2]") as "Hsmap";[apply lookup_delete|rewrite insert_delete -!delete_insert_ne//].
    iDestruct (big_sepM_insert with "[$Hsmap $Hs_t1]") as "Hsmap";[apply lookup_delete|rewrite insert_delete].
    iDestruct (big_sepM_insert with "[$Hsmap $Hs_stk]") as "Hsmap".
    { rewrite lookup_insert_ne// lookup_delete_ne// !lookup_insert_ne//. apply not_elem_of_dom. rewrite Hsdom. set_solver-. }

    iApply (rclear_spec_gmap with "[- $HPC $Hcode $Hrmap]");[eauto..|].
    { apply not_elem_of_list. constructor. }
    { assert (length l_code1 = 31) as Hlength4.
      clear -Hlength Hlength0 Hlength1. rewrite app_length Hlength1 in Hlength0. lia.
      destruct l_code1;inversion Hlength4. apply contiguous_between_cons_inv_first in Hcont_code1 as ->.
      auto. }
    { clear -Hrdom. rewrite !dom_delete_L !dom_insert_L Hrdom list_to_set_difference -/all_registers_s /=. clear. set_solver. }
    iNext. iIntros "[HPC [Hdom Hrclear]]".
    iDestruct "Hdom" as (rmap1) "[Hregs #Hregs_cond]". iDestruct "Hregs_cond" as %[Hrdom1 Hzeroes].
    iMod (rclear_s_spec_gmap with "[$Hspec $Hj $HsPC $Hscode $Hsmap]") as "(Hj & HsPC & Hdom & Hsrclear)";[eauto..|].
    { apply not_elem_of_list. constructor. }
    { assert (length l_code1 = 31) as Hlength4.
      clear -Hlength Hlength0 Hlength1. rewrite app_length Hlength1 in Hlength0. lia.
      destruct l_code1;inversion Hlength4. apply contiguous_between_cons_inv_first in Hcont_code1 as ->.
      auto. }
    { clear -Hsdom. rewrite !dom_insert_L !dom_delete_L !dom_insert_L Hsdom list_to_set_difference -/all_registers_s /=. clear. set_solver. }
    iDestruct "Hdom" as (rmap2) "[Hsregs #Hsegs_cond]". iDestruct "Hsegs_cond" as %[Hrdom2 Hzeroes2].

    (* jmp r_t0 *)
    prep_addr_list_full l_rest1 Hcont.
    iPrologue "Hprog".
    iPrologue_s "Hsprog".
    iMod (step_jmp_success _ [SeqCtx] with "[$Hspec $Hj $HsPC $Hsi $Hs_t0]")
      as "(Hj & HsPC & Hsi & Hs_t0)";
      [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|auto..].
    iApply (wp_jmp_success with "[$HPC $Hi $Hr_t0]");
      [apply decode_encode_instrW_inv|iCorrectPC link1 a_last|].

    (* first we will update the varilidy of wret to the new world *)
    set (W' := (<s[a:=Uninitialized (inl z1, inl z2)]s>(uninitialize W m))).
    assert (related_sts_a_world W W' b_stk) as Hrelated.
    { eapply related_sts_a_trans_world;[apply uninitialize_related_pub_a|];eauto.
      apply related_sts_a_uninitialized. clear -Ha; solve_addr. apply Hstk_cond. auto. }
    iDestruct ("Hmono" $! _ _ Hrelated with "Hwret_valid") as "Hwret_valid'". iSimpl in "Hwret_valid'".
    iDestruct (jmp_or_fail_binary_spec with "Hspec Hwret_valid'") as "Hcond".
    destruct (decide (isCorrectPC (updatePcPerm wret))).
    2: { iEpilogue "(HPC & _)". iApply "Hcond". iFrame. iApply "Hφ". iIntros (Hcontr). inversion Hcontr. }
    iDestruct "Hcond" as (p g b e a' Heq) "Hcond". rewrite Heq.
    iSpecialize ("Hcond" $! (<[PC:=inl 0%Z]> (<[r_t0:=wret]> rmap1),<[PC:=inl 0%Z]> (<[r_t0:=wret]> rmap2)) W' with "[]").
    { destruct g;iPureIntro.
      apply related_sts_priv_refl_world. apply related_sts_priv_refl_world. apply related_sts_a_refl_world. }

    (* we can now establish the continuation *)
    iEpilogue "(HPC & Hi & Hr_t0)".
    iEpilogue_s.

    (* first we will close the program invariant *)
    iMod ("Hcls" with "[Hprepstack Hsprepstack Hprog_done Hsprog_done
                        Hrclear Hsrclear Hi Hsi HpushU HspushU $Hown]") as "Hown".
    { iNext. iFrame. simpl. done. }

    (* next we must establish that the current register state is valid *)
    iDestruct (big_sepM_insert with "[$Hregs $Hr_t0]") as "Hregs".
    { apply not_elem_of_dom. rewrite Hrdom1. set_solver-. }
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs".
    { rewrite lookup_insert_ne//. apply not_elem_of_dom. rewrite Hrdom1. set_solver-. }
    iDestruct (big_sepM_insert with "[$Hsregs $Hs_t0]") as "Hsregs".
    { apply not_elem_of_dom. rewrite Hrdom2. set_solver-. }
    iDestruct (big_sepM_insert with "[$Hsregs $HsPC]") as "Hsregs".
    { rewrite lookup_insert_ne//. apply not_elem_of_dom. rewrite Hrdom2. set_solver-. }
    iDestruct ("Hcond" with "[$Hown $Hr $Hsts $Hj Hregs Hsregs]") as "[_ Hconf]".
    {  rewrite -(insert_insert (<[_:=_]> rmap1) PC _ (inl 0%Z)) -(insert_insert (<[_:=_]> rmap2) PC _ (inl 0%Z)) Heq /=.
       iFrame "Hsregs Hregs". iSplit;[iPureIntro|].
       - simpl. intros x. split. all: apply elem_of_gmap_dom.
         rewrite !dom_insert_L Hrdom1 list_to_set_difference.
         2: rewrite !dom_insert_L Hrdom2 list_to_set_difference.
         all: clear.
         all: pose proof (all_registers_s_correct x). all: set_solver.
       - iIntros (r HPC). rewrite /RegLocate. rewrite lookup_insert_ne// (lookup_insert_ne _ PC)//.
         destruct (decide (r_t0 = r));[subst;rewrite !lookup_insert;eauto|rewrite !lookup_insert_ne;auto].
         rewrite Hzeroes. rewrite Hzeroes2. rewrite !fixpoint_interp1_eq. done.
         rewrite Hrdom2. 2: rewrite Hrdom1. all: clear -HPC n. all: pose proof (all_registers_s_correct r).
         all: rewrite list_to_set_difference. all: set_solver. }
    iApply (wp_wand with "Hconf").
    iIntros (v). iIntros "Hcond'". iApply "Hφ".
    iIntros (Hhalted). iDestruct ("Hcond'" $! Hhalted) as (r W'') "(?&?&?&?&%&?&?&?)".
    iExists _,_;iFrame.
    iPureIntro. eapply related_sts_a_priv_trans_world;eauto.
  Qed.


  (* --------------------------------------------------------------------------------------------------- *)
  (* ------------------------------------ left to right refinement ------------------------------------- *)
  (* --------------------------------------------------------------------------------------------------- *)

  Definition confL a := conf1 a 2.
  Definition confR a := conf2 a 3.

  Lemma conf_spec_LR W pc_p pc_g pc_b pc_e (* PC *)
        conf_addrs (* program addresses: same for implementation and specification *)
        a_first a_last (* special adresses *)
        wstk wstk' (* stack *)
        rmap rmap' (* registers *)
        ι1 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between conf_addrs a_first a_last ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk]} →
    dom (gset RegName) rmap' = all_registers_s ∖ {[PC;r_stk]} →

    {{{ spec_ctx ∗ ⤇ Seq (Instr Executable)
      ∗ r_stk ↦ᵣ wstk
      ∗ r_stk ↣ᵣ wstk'
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      ∗ ([∗ map] r_i↦w_i ∈ rmap', r_i ↣ᵣ w_i)
      (* stack *)
      ∗ interp W (wstk,wstk')
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (confL conf_addrs ∗ confR conf_addrs)
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
             ∃ r W', ⤇ of_val HaltedV
                   ∗ full_map r
                   ∗ registers_mapsto r.1
                   ∗ spec_registers_mapsto r.2
                   ∗ ⌜related_sts_priv_world W W'⌝
                   ∗ na_own logrel_nais ⊤
                   ∗ sts_full_world W'
                   ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hcont Hrdom Hsdom φ) "(#Hspec & Hj & Hr_stk & Hs_stk & HPC & HsPC & Hrmap
    & Hsmap & #Hstk_valid & Hown & #Hconfprogs & Hsts & Hr) Hφ".
    iDestruct (conf_spec_12 with "[$Hspec $Hj $Hr_stk $Hs_stk $HPC $HsPC $Hrmap $Hsmap
    $Hstk_valid $Hown $Hconfprogs $Hsts $Hr] Hφ") as "$";eauto.
  Qed.

  (* --------------------------------------------------------------------------------------------------- *)
  (* ------------------------------------ right to left refinement ------------------------------------- *)
  (* --------------------------------------------------------------------------------------------------- *)

  Definition confL' a := conf2 a 2.
  Definition confR' a := conf1 a 3.

  Lemma conf_spec_RL W pc_p pc_g pc_b pc_e (* PC *)
        conf_addrs (* program addresses: same for implementation and specification *)
        a_first a_last (* special adresses *)
        wstk wstk' (* stack *)
        rmap rmap' (* registers *)
        ι1 (* invariant names *) :

    (* PC assumptions *)
    isCorrectPC_range pc_p pc_g pc_b pc_e a_first a_last ->

    (* Program adresses assumptions *)
    contiguous_between conf_addrs a_first a_last ->

    (* footprint of the register map *)
    dom (gset RegName) rmap = all_registers_s ∖ {[PC;r_stk]} →
    dom (gset RegName) rmap' = all_registers_s ∖ {[PC;r_stk]} →

    {{{ spec_ctx ∗ ⤇ Seq (Instr Executable)
      ∗ r_stk ↦ᵣ wstk
      ∗ r_stk ↣ᵣ wstk'
      ∗ PC ↦ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ PC ↣ᵣ inr ((pc_p,pc_g),pc_b,pc_e,a_first)
      ∗ ([∗ map] r_i↦w_i ∈ rmap, r_i ↦ᵣ w_i)
      ∗ ([∗ map] r_i↦w_i ∈ rmap', r_i ↣ᵣ w_i)
      (* stack *)
      ∗ interp W (wstk,wstk')
      (* token which states all non atomic invariants are closed *)
      ∗ na_own logrel_nais ⊤
      (* trusted code *)
      ∗ na_inv logrel_nais ι1 (confR' conf_addrs ∗ confL' conf_addrs)
      (* we start out with arbitrary sts *)
      ∗ sts_full_world W
      ∗ region W
    }}}
      Seq (Instr Executable)
      {{{ v, RET v; ⌜v = HaltedV⌝ →
             ∃ r W', ⤇ of_val HaltedV
                   ∗ full_map r
                   ∗ registers_mapsto r.1
                   ∗ spec_registers_mapsto r.2
                   ∗ ⌜related_sts_priv_world W W'⌝
                   ∗ na_own logrel_nais ⊤
                   ∗ sts_full_world W'
                   ∗ region W' }}}.
  Proof.
    iIntros (Hvpc Hcont Hrdom Hsdom φ) "(#Hspec & Hj & Hr_stk & Hs_stk & HPC & HsPC & Hrmap
    & Hsmap & #Hstk_valid & Hown & #Hconfprogs & Hsts & Hr) Hφ".
    iDestruct (conf_spec_12 with "[$Hspec $Hj $Hr_stk $Hs_stk $HPC $HsPC $Hrmap $Hsmap
    $Hstk_valid $Hown $Hconfprogs $Hsts $Hr] Hφ") as "$";eauto.
  Qed.

End conf.
