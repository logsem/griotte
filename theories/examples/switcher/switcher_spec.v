From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel fundamental interp_weakening addr_reg_sample rules proofmode.
From cap_machine Require Import multiple_updates region_invariants_revocation region_invariants_allocation.
From cap_machine Require Import switcher.



Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {tframeg : TFRAMEG Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation TFRAME := (leibnizO nat).
  Notation WORLD := ( prodO (prodO STS_STD STS) TFRAME) .
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition export_tableN (C : CmptName) : namespace := nroot .@ "export_tableN" .@ C.
  Definition export_table_PCCN (C : CmptName) : namespace := (export_tableN C) .@ "PCC".
  Definition export_table_CGPN (C : CmptName) : namespace := (export_tableN C) .@ "CGP".
  Definition export_table_entryN (C : CmptName) (a : Addr) : namespace :=
    (export_tableN C) .@ "entry" .@ a.

  Program Definition execute_entry_point_register (wpcc wcgp : Word) :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ) :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO Reg),
      (full_map reg ∧
       ⌜ reg !! PC = Some wpcc ⌝ ∧
       ⌜ reg !! cgp = Some wcgp ⌝ ∧
       (∀ (wstk : Word), (⌜reg !! csp = Some wstk⌝ → interp W C wstk)) ∧
       (∀ (wret : Word), (⌜reg !! cra = Some wret⌝ → interp W C wret)) ∧
       (∀ (r : RegName) (v : Word), (⌜r ∈ dom_arg_rmap⌝ → ⌜reg !! r = Some v⌝ → interp W C v)) ∧
       (∀ (r : RegName),
          (⌜r ∉ (dom_arg_rmap ∪ {[PC; cra; cgp; csp]})⌝ →  ⌜reg !! r = Some (WInt 0)⌝)))%I.
  Solve All Obligations with solve_proper.

  Program Definition execute_entry_point (wpcc wcgp : Word) (regs : Reg) : (WORLD -n> (leibnizO CmptName) -n> iPropO Σ) :=
    (λne (W : WORLD) (C : CmptName),
       ( (execute_entry_point_register wpcc wcgp W C regs)
         ∗ registers_pointsto regs
         ∗ region W C
         ∗ sts_full_world W C
         ∗ tframe_frag (frm W)
         ∗ na_own logrel_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  Program Definition ot_switcher_prop :
    (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ):=
    λne (W : WORLD) (C : CmptName) (w : Word),
       (∃ (g_tbl : Locality) (b_tbl e_tbl a_tbl : Addr)
          (bpcc epcc : Addr)
          (bcgp ecgp : Addr)
          (nargs off : Z),
           ⌜ w = WCap RO g_tbl b_tbl e_tbl a_tbl ⌝
           ∗ ⌜ (b_tbl <= a_tbl < e_tbl)%a ⌝
           ∗ ⌜ (b_tbl < (b_tbl ^+1))%a ⌝
           ∗ ⌜ ((b_tbl ^+1) < a_tbl)%a ⌝
           ∗ ⌜ (0 <= nargs <= 7 )%Z ⌝
           ∗ inv (export_table_PCCN C) ( b_tbl ↦ₐ WCap RX Global bpcc epcc bpcc)
           ∗ inv (export_table_CGPN C) ( (b_tbl ^+ 1)%a ↦ₐ WCap RW Global bcgp ecgp bcgp)
           ∗ inv (export_table_entryN C a_tbl) ( a_tbl ↦ₐ WInt (encode_entry_point nargs off))
           ∗ □ ( ∀ W' regs, ⌜related_sts_priv_world W W'⌝ →
                   ▷ (execute_entry_point
                            (WCap RX Global bpcc epcc (bpcc ^+ off)%a)
                            (WCap RW Global bcgp ecgp bcgp)
                            regs W' C))
      )%I.
  Solve All Obligations with solve_proper.

  Definition ot_switcher_propC : (WORLD * CmptName * Word) -> iPropI Σ :=
    safeC ot_switcher_prop.

  Lemma persistent_cond_ot_switcher :
    persistent_cond ot_switcher_prop.
  Proof. intros [ [] ] ; cbn ; apply _. Qed.

  Lemma mono_priv_ot_switcher (C : CmptName) (w : Word) :
    ⊢ future_priv_mono C ot_switcher_propC w.
  Proof.
    iIntros (W W' Hrelated_W_W').
    iModIntro.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iDestruct "Hot_switcher" as
      (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs off ->
       Hatbl Hbtbl Hbtbl1 Hnargs) "(Hinvpcc & Hinvcgp & Hinventry & #Hcont)".
    iFrame "Hinvpcc Hinvcgp Hinventry".
    iExists _,_.
    repeat (iSplit ; first done).
    iModIntro.
    iIntros (W'' regs Hrelated_W'_W'').
    iSpecialize ("Hcont" $! W'' regs).
    iApply "Hcont".
    iPureIntro.
    by eapply related_sts_priv_trans_world.
  Qed.

  Definition switcher_inv
    (b_switcher e_switcher a_switcher_cc b_tstk e_tstk : Addr)
    (ot_switcher : OType) : iProp Σ :=
    ∃ (a_tstk : Addr) (d : nat) (tstk_next : list Word),
     mtdc ↦ₛᵣ WCap RWL Local b_tstk e_tstk a_tstk
     ∗ ⌜ SubBounds
         b_switcher e_switcher
         a_switcher_cc (a_switcher_cc ^+ length switcher_instrs)%a ⌝
     ∗ ⌜ (ot_switcher < (ot_switcher ^+1) )%ot ⌝
     ∗ codefrag a_switcher_cc switcher_instrs
     ∗ b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher
     ∗ [[ (a_tstk ^+1)%a, e_tstk ]] ↦ₐ [[ tstk_next ]]
     ∗ tframe_full d ∗ ⌜ (b_tstk + d)%a = Some a_tstk  ⌝
     ∗ seal_pred ot_switcher ot_switcher_propC.

   Definition frame_inv (C : CmptName) (i : positive) (P : iProp Σ) :=
     (∃ x:bool, sts_state_loc C i x ∗ if x then P else emp)%I.
   Definition frame_rel_pub := λ (a b : bool), False.
   Definition frame_rel_priv := λ (a b : bool), True.
   Definition frame_W (W : WORLD) : WORLD :=
     let ι := fresh_cus_name W in
      <l[ ι := true , ( frame_rel_pub, (frame_rel_pub, frame_rel_priv)) ]l> W.

   Lemma frame_W_related_sts_pub_world (W : WORLD) : related_sts_pub_world W (frame_W W).
   Proof.
     rewrite /frame_W.
     destruct W as [ [Wstd [fs fr] ] Wfrm ] .
     assert (fresh (dom fs ∪ dom fr) ∉ (dom fs ∪ dom fr)) as Hfresh by apply is_fresh.
     apply related_sts_pub_world_fresh_loc; set_solver.
   Qed.

   Set Nested Proofs Allowed.

  Lemma frame_W_lookup_std (W : WORLD) (a : Addr) :
    std (frame_W W) !! a = (std W) !!a.
  Proof.
    rewrite /frame_W.
    by cbn.
  Qed.

  Lemma frame_W_lookup_loc (W : WORLD) (ι : positive) :
    ι ≠ fresh_cus_name W ->
    loc (frame_W W) !! ι = (loc W) !! ι.
  Proof.
    intros Hι.
    rewrite /frame_W /= lookup_insert_ne //.
  Qed.
  Lemma frame_W_lookup_rel (W : WORLD) (ι : positive) :
    ι ≠ fresh_cus_name W ->
    wrel (frame_W W) !! ι = (wrel W) !! ι.
  Proof.
    intros Hι.
    rewrite /frame_W /= lookup_insert_ne //.
  Qed.
  Lemma frame_W_lookup_frm (W : WORLD) : frm (frame_W W) = (frm W).
  Proof. by cbn. Qed.

  Lemma ι0_in_Wloc_helper (W0 : WORLD) (ι0 : positive) (callee_stk_frm_addr : list Addr) :
    ι0 ∈ (dom (loc (std_update_multiple
                       (<l[ι0:=false]l>(revoke W0))
                       callee_stk_frm_addr Temporary))).
  Proof.
    rewrite std_update_multiple_loc_sta dom_insert_L; set_solver.
  Qed.

  Lemma ι0_isnot_fresh (W0 : WORLD) (ι0 : positive) (callee_stk_frm_addr : list Addr) :
    ι0 ≠ fresh_cus_name (std_update_multiple
                           (<l[ι0:=false]l>(revoke W0))
                           callee_stk_frm_addr Temporary).
  Proof.
    apply fresh_name_notin. left.
    apply ι0_in_Wloc_helper.
  Qed.

  Definition switcher_world_pre_frame (W_init : WORLD) (callee_stk_frm_addr : list Addr) :=
    (std_update_multiple (<d[ frm W_init + 1]d>(revoke W_init)) callee_stk_frm_addr Temporary).

  Definition switcher_world_upon_jmp (W_init : WORLD)
    (a_local_args callee_stk_frm_addr : list Addr) :=
    std_update_multiple
      (frame_W (switcher_world_pre_frame W_init callee_stk_frm_addr))
      a_local_args Temporary.

  Lemma related_sts_priv_world_switcher_pre_frame
    (W : WORLD) (callee_stk_frm_addr : list Addr) :
    Forall (fun a => std W !! a = Some Revoked) callee_stk_frm_addr ->
    related_sts_priv_world W (switcher_world_pre_frame W callee_stk_frm_addr).
  Proof.
    intros Ha_local_args.
    rewrite /switcher_world_pre_frame.
    eapply related_sts_priv_trans_world; cycle 1.
    { apply related_sts_pub_priv_world.
      apply related_sts_pub_update_multiple_temp.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by apply revoke_lookup_Revoked.
    }
    eapply related_sts_priv_trans_world; cycle 1.
    { apply sts.related_sts_priv_world_update_frm. }
    apply revoke_related_sts_priv_world.
  Qed.

  Lemma switcher_world_pre_frame_local_revoked
    (W : WORLD) (callee_stk_frm_addr : list Addr) (a : Addr) :
    a ∉ callee_stk_frm_addr ->
    std W !! a = Some Revoked ->
    std (switcher_world_pre_frame W callee_stk_frm_addr) !! a = Some Revoked.
  Proof.
    intros Ha_notin Ha.
    rewrite /switcher_world_pre_frame.
    rewrite std_sta_update_multiple_lookup_same_i; last done.
    cbn.
    by apply revoke_lookup_Revoked.
  Qed.

  Lemma related_sts_priv_world_switcher_upon_jmp
    (W : WORLD) (a_local_args callee_stk_frm_addr : list Addr) :
    Forall (fun a => std W !! a = Some Revoked) a_local_args ->
    Forall (fun a => std W !! a = Some Revoked) callee_stk_frm_addr ->
    a_local_args ## callee_stk_frm_addr ->
    related_sts_priv_world W (switcher_world_upon_jmp W a_local_args callee_stk_frm_addr).
  Proof.
    intros Ha_local_args Hcallee_stk_frm_addr Hdis.
    rewrite /switcher_world_upon_jmp.
    eapply related_sts_priv_trans_world; cycle 1.
    { apply related_sts_pub_priv_world.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall.
      intros a Ha; cbn in *.
      assert (a ∉ callee_stk_frm_addr) as Ha'.
      { rewrite elem_of_disjoint in Hdis.
        intro Hcontra; eapply Hdis; eauto.
      }
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [k Ha].
      eapply Forall_lookup_1 in Ha; eauto; cbn in Ha.
      apply switcher_world_pre_frame_local_revoked; auto.
    }
    eapply related_sts_priv_trans_world; cycle 1.
    {
      apply related_sts_pub_priv_world.
      apply frame_W_related_sts_pub_world.
    }
    apply related_sts_priv_world_switcher_pre_frame; auto.
  Qed.


  Lemma helper_switcher_final_pub
    (W0 WF : WORLD) (ltemp_unknown a_local_args : list Addr)
    (a_stk e_stk : Addr) :
    let callee_stk_frm_addr :=
      finz.seq_between (a_stk ^+ 4)%a e_stk
    in
    let W1 := switcher_world_upon_jmp W0 a_local_args callee_stk_frm_addr in
    let ι :=
      fresh_cus_name (switcher_world_pre_frame W0 callee_stk_frm_addr)
    in

    (a_stk ^+ 4 < e_stk)%a ->

    NoDup ltemp_unknown ->
    NoDup a_local_args ->
    ltemp_unknown ## a_local_args ->
    ltemp_unknown ## finz.seq_between a_stk e_stk ->
    a_local_args ## finz.seq_between a_stk e_stk ->
    (∀ a : Addr, std W0 !! a = Some Temporary ↔ a ∈ ltemp_unknown) ->
    related_sts_pub_world W1 WF ->
    loc WF !! ι = Some (encode true) ->
    wrel WF !! ι =
    Some (convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv) ->

    Forall (λ a : Addr, std WF !! a = Some Temporary)
      (finz.seq_between (a_stk ^+ 4)%a e_stk) ->
    Forall (λ a : Addr, std WF !! a = Some Temporary) a_local_args ->
    Forall (λ a : Addr , std WF !! a = Some Revoked ) ltemp_unknown ->
    Forall (λ a : Addr, (std W0) !! a = Some Revoked) a_local_args ->
    Forall (λ a : Addr, (std W0) !! a = Some Revoked) (finz.seq_between a_stk e_stk) ->

    related_sts_pub_world W0
      (close_list ltemp_unknown (<d[ frm W0 ]d>(<l[ι:=false]l>(revoke WF)))).
  Proof.
    intros callee_stk_frm_addr W1 ι
      Haestk HNoDup_temp_unknown HNoDup_local_args Hdis_unkw_locals Hdis_unkw_stk Hdis_locals_stk W_temps
      Hrelated_W1_WF Hι_loc_WF Hι_rel_WF Hcallee_frame_WF_temporary Hlocal_args_WF_temporary
      (* Hunknown_WF_revoked Hlocal_notin_W0. *)
      Hunknown_WF_revoked Hlocal_W0_revoked Hcalle_frame_W0_temporary.
    destruct W0 as [ [Wstd0 [ Wloc0 Wrel0 ] ] Wfrm0 ]; cbn in *.
    destruct WF as [ [WstdF [ WlocF WrelF ] ] WfrmF ]; cbn in *.
    split ; [split|] ; cycle 1; cbn.

    (* --- CUSTOM WORLD ---*)
    - (* Show that the custom world is a public transition*)
      (* rewrite std_update_multiple_loc_sta std_update_multiple_loc_rel /=. *)
      split;[|split].
      + assert (dom Wloc0 ⊆ dom (loc W1)) as Hdom_loc_W0_W1.
        { subst W1.
          rewrite std_update_multiple_loc_sta dom_insert_L.
          rewrite std_update_multiple_loc_sta.
          set_solver.
        }
        assert (dom (loc W1) ⊆ dom (<[ι:=encode false]> WlocF))
          as Hdom_loc_W0_WF.
        { rewrite dom_insert_L.
          destruct Hrelated_W1_WF as [ [? [Hdom ?] ] ?] ; cbn in *.
          set_solver+Hdom.
        }
        set_solver.
      + assert (dom Wrel0 ⊆ dom (wrel W1)) as Hdom_rel_W0_W1.
        { subst W1.
          rewrite std_update_multiple_loc_rel dom_insert_L.
          rewrite std_update_multiple_loc_rel.
          set_solver.
        }
        assert (dom (wrel W1) ⊆ dom WrelF) as Hdom_rel_W0_WF.
        {
          destruct Hrelated_W1_WF as [ [? [? [Hdom ?] ] ] ?] ; cbn in *.
          set_solver+Hdom.
        }
        set_solver.
      + intros ι' r1 r2 r1' r2' r3 r3' HWrel0_ι' HWrelF_ι'.
        assert (ι' ≠ ι) as Hι_ι'.
        { apply fresh_name_notin.
          right.
          rewrite std_update_multiple_loc_rel.
          simplify_map_eq; by rewrite elem_of_dom.
        }
        assert ((wrel W1) !! ι' = Some (r1, r2, r3)) as HWrel1_ι'.
        { subst W1.
          rewrite std_update_multiple_loc_rel.
          rewrite lookup_insert_ne //.
          rewrite std_update_multiple_loc_rel.
          simplify_map_eq; done.
        }
        destruct Hrelated_W1_WF as [ [_ [_ [_ Hrelated_rel_W1_WF] ] ] _] ; cbn in *.
        specialize (Hrelated_rel_W1_WF _ _ _ _ _ _ _ HWrel1_ι' HWrelF_ι').
        destruct Hrelated_rel_W1_WF as (-> & -> & -> & Hrtc).
        repeat (split ; first done).

        intros b0 bF Hloc0_ι' HlocF_ι'.
        assert ((loc W1) !! ι' = Some b0) as HWloc1_ι'.
        { subst W1.
          rewrite std_update_multiple_loc_sta.
          rewrite lookup_insert_ne //.
          rewrite std_update_multiple_loc_sta.
          simplify_map_eq; try done.
        }
        rewrite lookup_insert_ne // in HlocF_ι'.
        by apply Hrtc.

    (* --- CUSTOM WORLD ---*)
    - apply related_tframe_pub_refl.

    (* --- STANDARD WORLD ---*)
    - assert ( dom Wstd0 ⊆ dom (std W1) ) as Hdom_std_W0_W1.
      { subst W1.
        etransitivity ; last apply std_update_multiple_sta_dom_subseteq.
        cbn.
        etransitivity ; last apply std_update_multiple_sta_dom_subseteq.
        cbn.
        by rewrite -revoke_dom_eq.
      }
      split.
      + (* monotonic domains *)
        rewrite -close_list_dom_eq.
        cbn.
        rewrite -revoke_dom_eq.
        destruct Hrelated_W1_WF as [ [ [? _] _] _] ; cbn in *.
        set_solver.
      + (* each address has public transition*)
        clear Hι_loc_WF Hι_rel_WF.
        intros a ρ0 ρF Hstd0_a HstdF_a.

        assert (is_Some (std W1 !! a)) as [ρ1 Hstd1_a].
        {
          rewrite -elem_of_dom.
          apply Hdom_std_W0_W1.
          by rewrite elem_of_dom.
        }
        assert (is_Some (WstdF !! a)) as [ρ2 HstdF'_a].
        {
          destruct Hrelated_W1_WF as [ [Hdom _] _] ; cbn in *.
          rewrite -elem_of_dom.
          apply Hdom.
          by rewrite elem_of_dom.
        }

        destruct (decide (a ∈ ltemp_unknown)) as [Ha_temps_unknown | Ha_temps_unknown].
        { rewrite close_list_std_sta_revoked in HstdF_a; eauto.
          + simplify_eq.
            specialize (W_temps a).
            destruct W_temps as [_ W_temps].
            ospecialize (W_temps _); first set_solver.
            rewrite Hstd0_a in W_temps; simplify_eq.
            by apply rtc_refl.
          + assert ( (std W1) !! a = Some Revoked) as Hstd1'_a.
            {
              subst W1.
              rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
              { eapply elem_of_disjoint in Ha_temps_unknown; eauto. }
              cbn.
              rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
              { intro Hcontra; eapply (elem_of_disjoint ltemp_unknown); eauto.
                rewrite (finz_seq_between_split a_stk (a_stk ^+ 4)%a); last by solve_addr.
                apply elem_of_app; naive_solver.
              }
              cbn.
              apply revoke_lookup_Monotemp.
              by apply W_temps.
            }
            apply revoke_lookup_Revoked; cbn.
            apply elem_of_list_lookup_1 in Ha_temps_unknown.
            destruct Ha_temps_unknown as [? ?].
            eapply Forall_lookup_1 in Hunknown_WF_revoked; eauto.
        }

        rewrite -close_list_std_sta_same in HstdF_a; last done.
        destruct (decide (a ∈ (finz.seq_between a_stk e_stk))) as [Ha_stk | Ha_stk].
        {
          rewrite elem_of_list_lookup in Ha_stk.
          destruct Ha_stk as [k Ha_stk].
          eapply Forall_lookup in Hcalle_frame_W0_temporary; eauto.
          rewrite Hcalle_frame_W0_temporary in Hstd0_a; simplify_eq.

          destruct (decide (a ∈ (finz.seq_between (a_stk ^+ 4)%a e_stk))) as [Ha4_stk | Ha4_stk].
          - rewrite revoke_lookup_Monotemp in HstdF_a ; simplify_eq.
            { apply rtc_refl. }
            eapply Forall_forall in Hcallee_frame_WF_temporary; eauto.
          - assert (std W1 !! a = Some Revoked) as Hstd1'_a.
            { subst W1.
              rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
              { intro Ha'.
                rewrite elem_of_disjoint in Hdis_locals_stk.
                apply (Hdis_locals_stk a); eauto.
                rewrite elem_of_list_lookup; eexists; eauto.
              }
              rewrite frame_W_lookup_std.
              rewrite std_sta_update_multiple_lookup_same_i; simplify_eq; auto.
              cbn.
              by apply revoke_lookup_Revoked.
            }
            eapply region_state_Revoked_monotone in Hstd1'_a; eauto.
            destruct Hstd1'_a as [Hstd1'_a | [ Hstd1'_a | Hstd1'_a] ]; cbn in Hstd1'_a.
            + apply revoke_lookup_Revoked in Hstd1'_a.
              rewrite Hstd1'_a in HstdF_a; simplify_eq.
              apply rtc_refl.
            + apply revoke_lookup_Monotemp in Hstd1'_a.
              rewrite Hstd1'_a in HstdF_a; simplify_eq.
              apply rtc_refl.
            + apply revoke_lookup_Perm in Hstd1'_a.
              rewrite Hstd1'_a in HstdF_a; simplify_eq.
              apply rtc_once; cbn; constructor.
        }

        destruct (decide (a ∈ a_local_args)) as [Ha_local_args | Ha_local_args].
        { replace ρ0 with Revoked; cycle 1.
          { apply elem_of_list_lookup_1 in Ha_local_args.
            destruct Ha_local_args as [ ? ? ].
            eapply Forall_lookup_1 in Hlocal_W0_revoked; eauto.
            by rewrite Hlocal_W0_revoked in Hstd0_a ; simplify_eq.
          }
          assert ( (std W1) !! a = Some Temporary) as Hstd1'_a.
          {
            subst W1.
            rewrite std_sta_update_multiple_lookup_in_i; auto .
          }
          rewrite revoke_lookup_Monotemp in HstdF_a; simplify_eq; first by apply rtc_refl.
          replace WstdF with (std (WstdF, (WlocF, WrelF), WfrmF)); last by cbn.
          eapply region_state_pub_temp; eauto.
        }

        destruct ρ0.
        * (* Case ρ0 = Temporary --- not possible *)
          apply W_temps in Hstd0_a.
          set_solver.
        * (* Case ρ0 = Permanent --- ρF Permanent *)
          destruct Hrelated_W1_WF as [ [ [_ Hrelated] _] _] ; cbn in *.
          specialize (Hrelated _ _ _ Hstd1_a HstdF'_a).
          subst W1.
          rewrite std_sta_update_multiple_lookup_same_i in Hstd1_a; last done.
          cbn in Hstd1_a.
          rewrite std_sta_update_multiple_lookup_same_i in Hstd1_a.
          2: {
            rewrite (finz_seq_between_split  a_stk (a_stk ^+ 4)%a)
            in Ha_stk ; last by solve_addr.
            apply not_elem_of_app in Ha_stk; naive_solver.
          }
          cbn in Hstd1_a.
          rewrite revoke_lookup_Perm in Hstd1_a ; eauto; simplify_eq.
          eapply std_rel_pub_rtc_Permanent in Hrelated; eauto; simplify_eq.
          rewrite revoke_lookup_Perm in HstdF_a ; eauto; simplify_eq.
          apply rtc_refl.
        * (* Case ρ0 = Revoked --- ρF Revoked *)
          destruct Hrelated_W1_WF as [ [ [_ Hrelated] _] _] ; cbn in *.
          specialize (Hrelated _ _ _ Hstd1_a HstdF'_a).
          subst W1.
          rewrite std_sta_update_multiple_lookup_same_i in Hstd1_a; last done.
          cbn in Hstd1_a.
          rewrite std_sta_update_multiple_lookup_same_i in Hstd1_a.
          2: {
            rewrite (finz_seq_between_split  a_stk (a_stk ^+ 4)%a)
            in Ha_stk ; last by solve_addr.
            apply not_elem_of_app in Ha_stk; naive_solver.
          }
          cbn in Hstd1_a.
          rewrite revoke_lookup_Revoked in Hstd1_a ; eauto; simplify_eq.
          eapply std_rel_pub_rtc_Revoked in Hrelated; eauto; simplify_eq.
          destruct Hrelated as [ -> | [  -> | -> ] ].
          ** rewrite revoke_lookup_Perm in HstdF_a ; eauto; simplify_eq.
             apply rtc_once; constructor.
          ** rewrite revoke_lookup_Monotemp in HstdF_a ; eauto; simplify_eq.
             apply rtc_refl.
          ** rewrite revoke_lookup_Revoked in HstdF_a ; eauto; simplify_eq.
             apply rtc_refl.
  Qed.

  Lemma switcher_ret_specification
    (Nswitcher Nframes : namespace)
    (W0 : WORLD)
    (C : CmptName)
    (b_switcher e_switcher a_switcher_cc : Addr)
    (b_stk e_stk a_stk : Addr)
    (ot_switcher : OType)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (ltemp_unknown : list Addr)
    (b_tstk a_tstk e_tstk a_jmp : Addr )
    (tstk_a1 : Word)
    (a_local_args : list Addr)
    (φ : val -> iPropI Σ) :

    let stk_caller_save_area :=
      [wcs0_caller;wcs1_caller;wcra_caller;wcgp_caller]
    in
    let callee_stk_frm_addr :=
      finz.seq_between (a_stk ^+ 4)%a e_stk
    in

    let W1 := switcher_world_upon_jmp W0 a_local_args callee_stk_frm_addr in
    let Hφ : iPropI Σ :=
      ((∃ W2 (rmap' : Reg), ⌜related_sts_pub_world W0 W2⌝ ∗
        ⌜dom rmap' = all_registers_s ∖ {[PC; cgp; cra; csp; ca0; ca1]}⌝ ∗
        na_own logrel_nais ⊤ ∗ sts_full_world W2 C ∗
        region W2 C ∗ tframe_frag W2.2 ∗
        ([∗ list] a ∈ (finz.seq_between a_stk e_stk), rel C a RWL interpC ∗ ⌜ std W2 !! a = Some Revoked ⌝ ) ∗
        PC ↦ᵣ updatePcPerm wcra_caller ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller ∗
        csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        (∃ warg0 : Word, ca0 ↦ᵣ warg0) ∗
        (∃ warg1 : Word, ca1 ↦ᵣ warg1) ∗
        ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) ∗
        ([∗ list] a ∈ a_local_args, ∃ w : Word, a ↦ₐ w) ∗
        [[a_stk,e_stk]]↦ₐ[[region_addrs_zeroes a_stk e_stk]]) -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I
    in
    let htemp_unknown :=
     ([∗ list] x ∈ ltemp_unknown, (∃ (x0 : Perm) (x1 : WORLD * CmptName * Word → iPropI Σ),
                                    ⌜∀ Wv : WORLD * CmptName * Word, Persistent (x1 Wv)⌝ ∗ temp_resources W0 C x1 x x0 ∗
                                    rel C x x0 x1) ∗ ⌜std (revoke W0) !! x = Some Revoked⌝)%I
    in
    let Pframe :=
     (Hφ ∗ (a_tstk ^+ 1)%a ↦ₐ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
     [[a_stk,(a_stk ^+ 4)%a]]↦ₐ[[stk_caller_save_area]] ∗ htemp_unknown)%I
    in
    let ι := fresh_cus_name (switcher_world_pre_frame W0 callee_stk_frm_addr)
    in

    Nswitcher ## Nframes ->
    (a_switcher_cc + 79%nat)%a = Some a_jmp ->
    (a_stk ^+ 4 < e_stk)%a ->
    (b_stk <= a_stk)%a ->
    (a_tstk ^+ 2 < e_tstk)%a ->
    (b_tstk <= a_tstk)%a ->
    (b_tstk + frm W0)%a = Some a_tstk ->
    NoDup ltemp_unknown ->
    NoDup a_local_args ->
    ltemp_unknown ## a_local_args ->
    ltemp_unknown ## finz.seq_between a_stk e_stk ->
    a_local_args ## finz.seq_between a_stk e_stk ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary ↔ a ∈ ltemp_unknown) ->
    Forall (λ a : Addr, (std W0) !! a = Some Revoked) a_local_args ->
    Forall (λ a : Addr, (std W0) !! a = Some Revoked) (finz.seq_between a_stk e_stk) ->

    ( na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher )
      ∗ ([∗ list] y ∈ finz.seq_between a_stk (a_stk ^+ 4)%a, rel C y RWL interpC)
      ∗ ([∗ list] y ∈ finz.seq_between (a_stk ^+ 4)%a e_stk, rel C y RWL interpC)
      ∗ ([∗ list] x ∈ finz.seq_between a_stk e_stk, ⌜std (revoke W0) !! x = Some Revoked⌝)
      ∗ sts_rel_loc C ι frame_rel_pub frame_rel_pub frame_rel_priv
      ∗ na_inv logrel_nais (Nframes.@ι) (frame_inv C ι Pframe)
      -∗ interp W1 C (WSentry XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a)
    ).
  Proof.
    intros stk_caller_save_area callee_stk_frm_addr W1 Hφ htemp_unknown Pframe ι
      HN Ha_jmp Hstk_ae Hstk_ba Htstk_ae Htstk_ba Hatstk
      HNoDup_temp_unknown HNoDup_local_args Hdis_unkw_locals Hdis_unkw_stk Hdis_local_stk W_temps
      Ha_args_locals_revoked Hstk_revoked.
    iIntros "#(Hinv_switcher & Hrel_reg_saved & Hrel_callee_frm
    & Htemp_opened_revoked & Hsts_rel_ι & #Hinv_frame)".

    iEval (rewrite fixpoint_interp1_eq //=).
    iModIntro; iIntros (rmap' W2 Hrelated_W1_W2).
    iAssert (interp_expr interp rmap' W2 C
               (WCap XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a))
              as "Hinterp_expr" ; last iFrame "Hinterp_expr".

    iIntros "([%Hfull_rmap #Hinterp_rmap] & Hrmap & Hregion & Hworld & Htframe_frag & Hna)".
    rewrite /interp_conf /registers_pointsto.
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by rewrite lookup_insert.
    rewrite delete_insert_delete.

    (* extract register points-to *)
    assert (exists wcra, rmap' !! cra = Some wcra)
      as [wcra Hwcra] by (by specialize (Hfull_rmap cra)).
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    assert (exists wcsp, rmap' !! csp = Some wcsp)
      as [wcsp Hwcsp] by (by specialize (Hfull_rmap csp)).
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    assert (exists wcgp, rmap' !! cgp = Some wcgp)
      as [wcgp Hwcgp] by (by specialize (Hfull_rmap cgp)).
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    assert (exists wca0, rmap' !! ca0 = Some wca0)
      as [wca0 Hwca0] by (by specialize (Hfull_rmap ca0)).
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert (exists wca1, rmap' !! ca1 = Some wca1)
      as [wca1 Hwca1] by (by specialize (Hfull_rmap ca1)).
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap' !! ctp = Some wctp)
      as [wctp Hwctp] by (by specialize (Hfull_rmap ctp)).
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    assert (exists wca2, rmap' !! ca2 = Some wca2)
      as [wca2 Hwca2] by (by specialize (Hfull_rmap ca2)).
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs1, rmap' !! cs1 = Some wcs1)
      as [wcs1 Hwcs1] by (by specialize (Hfull_rmap cs1)).
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs0, rmap' !! cs0 = Some wcs0)
      as [wcs0 Hwcs0] by (by specialize (Hfull_rmap cs0)).
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert (exists wct0, rmap' !! ct0 = Some wct0)
      as [wct0 Hwct0] by (by specialize (Hfull_rmap ct0)).
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert (exists wct1, rmap' !! ct1 = Some wct1)
      as [wct1 Hwct1] by (by specialize (Hfull_rmap ct1)).
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.

    (* open frame invariant *)
    iMod (na_inv_acc with "Hinv_frame Hna")
      as "(Hframe & Hna & Hclose_frame_inv)" ; auto.
    iEval (rewrite /frame_inv) in "Hframe".
    iDestruct "Hframe" as (ι_state) "[Hι_loc Hframe]".

    (* open switcher invariant *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    { solve_ndisj. }
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk' d tstk_next')
           "(>Hmtdc & >%Hbounds & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & Htframe_full & >%H_tstk_frame & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region; clear H0.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.
    focus_block_nochangePC 5 "Hcode" as a5 Ha5 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a5 = a_jmp) by solve_addr ; simplify_eq.

    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
    { done. }

    (* TODO extract as lemma about frame_W *)
    iDestruct (sts_full_state_loc with "[$] [$Hι_loc]") as "%Hι_state".
    iDestruct (sts_full_rel_loc with "[$] [$Hsts_rel_ι]") as "%Hι_rel".
    assert (ι_state = true) as ->.
    {
      assert ( loc W1 !! ι = Some (encode true))
        by (by rewrite /W1 std_update_multiple_loc_sta /frame_W /ι lookup_insert).
      assert ( wrel W1 !! ι = Some ( convert_rel frame_rel_pub, convert_rel frame_rel_pub, convert_rel frame_rel_priv))
        by (by rewrite /W1 std_update_multiple_loc_rel /frame_W /ι lookup_insert).
      assert (related_sts_pub_world W1 W2) as Hrelated by done.

      destruct Hrelated as [ [ _ [_ [_ Hrelated ] ] ] _].
      specialize (Hrelated ι _ _ _ _ _ _ H2 Hι_rel).
      destruct Hrelated as (_ & _ & _ & Hrelated).
      specialize (Hrelated _ _ H1 Hι_state).
      rewrite /convert_rel /frame_rel_pub /= in Hrelated.
      apply rtc_inv in Hrelated.
      destruct Hrelated.
      + by inv H3.
      + destruct H3 as (? & (? & ? & Hcontra) & _).
        naive_solver.
    }

    iDestruct "Hframe" as "(Hφ & tstk & Hsaved_register_area & Htemp_unknown)".
    iDestruct (tframe_agree with "[$] [$]") as "->".
    assert ( frm W2 = frm W0 + 1 ) as Hfrm_W2.
    { admit. (* NOTE true, because W2 pub of W1, where (frm W1) = (frm W0 +1) *)
    }
    rewrite !Hfrm_W2 in H_tstk_frame |- *.
    rewrite /stk_caller_save_area.
    iDestruct (region_pointsto_cons with "Hsaved_register_area") as "[Ha0_stk Hsaved_register_area]".
    { transitivity (Some (a_stk ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hsaved_register_area") as "[Ha1_stk Hsaved_register_area]".
    { transitivity (Some (a_stk ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hsaved_register_area") as "[Ha2_stk Hsaved_register_area]".
    { transitivity (Some (a_stk ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hsaved_register_area") as "[Ha3_stk _]".
    { transitivity (Some (a_stk ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }
    replace a_tstk' with ( (a_tstk ^+ 1)%a ) by ( solve_addr+H_tstk_frame Htstk_ae Htstk_ba Hatstk ).

    (* Load csp ctp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }

    (* Lea ctp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_tstk); solve_addr. }
    (* WriteSR mtdc ctp *)
    iInstr "Hcode".
    { done. }
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 3)%a); solve_addr. }
    (* Load cgp csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcgp".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 2)%a); solve_addr. }
    (* Load ca2 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hca2".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 1)%a); solve_addr. }
    (* Load cs1 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcs1".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk); solve_addr. }
    (* Load cs0 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcs0".
    (* GetE ct0 csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    assert (Forall (fun a => (std W2) !! a = Some Temporary) (finz.seq_between (a_stk ^+4)%a e_stk ))
      as Hcallee_stk_temporary.
    { clear -W1 Hrelated_W1_W2.
      apply Forall_forall.
      intros a Ha.
      eapply region_state_pub_temp; eauto.
      subst W1.
      cbn.
      destruct (decide (a ∈ a_local_args)).
      - by apply std_sta_update_multiple_lookup_in_i.
      - rewrite std_sta_update_multiple_lookup_same_i; last done.
        rewrite frame_W_lookup_std.
        by apply std_sta_update_multiple_lookup_in_i.
    }
    assert (Forall (fun a => (std W2) !! a = Some Temporary) a_local_args)
      as Hlocal_args_temporary.
    { clear -W1 Hrelated_W1_W2.
      apply Forall_forall.
      intros a Ha.
      eapply region_state_pub_temp; eauto.
      subst W1.
      by apply std_sta_update_multiple_lookup_in_i.
    }

    iMod ( revoked_by_revoked_resources with "[$Hworld $Hregion $Htemp_unknown]")
      as "(Hworld & Hregion & Htemp_unknown & %Hstd2_unknown)".
    { apply Forall_forall.
      intros a Ha.
      (* NOTE: true because a ∈ ltemp_unknown, and so it's Temporary in WO *)
      admit. }

    iMod ( monotone_revoke_keep _ _
             ( (finz.seq_between (a_stk ^+ 4)%a e_stk) ++ a_local_args)
           with "[ $Hworld $Hregion ]") as "(Hworld & Hregion & Hstk)".
    { apply NoDup_app.
      split ; [|split]; auto; first by apply finz_seq_between_NoDup.
      intros a Ha.
      intro Ha'.
      eapply elem_of_disjoint; eauto.
      rewrite (finz_seq_between_split a_stk (a_stk ^+ 4)%a); last by solve_addr.
      apply elem_of_app; naive_solver.
    }
    { iApply big_sepL_pure; iPureIntro.
      intros k a Ha.
      apply lookup_app_Some in Ha.
      destruct Ha as [ Ha | [ _ Ha] ].
      - eapply Forall_lookup_1 in Hcallee_stk_temporary; eauto.
      - eapply Forall_lookup_1 in Hlocal_args_temporary; eauto.
    }
    iEval (rewrite big_sepL_sep) in "Hstk"
    ; iDestruct "Hstk" as "[Hstk %Htemporary_revoked]".
    iEval (rewrite region_addrs_exists) in "Hstk"; iDestruct "Hstk" as (pl) "Hstk".
    iEval (rewrite region_addrs_exists2) in "Hstk"; iDestruct "Hstk" as (φl) "[%Hlen Hstk]".
    iEval (rewrite big_sepL2_sep) in "Hstk"
    ; iDestruct "Hstk" as "[_ Htemp_res]".
    iEval (rewrite big_sepL2_sep) in "Htemp_res"
    ; iDestruct "Htemp_res" as "[Htemp_res _]".
    iEval (rewrite /temp_resources) in "Htemp_res".
    iEval (rewrite big_sepL2_later_2) in "Htemp_res".
    iEval (rewrite region_addrs_exists2) in "Htemp_res"; iDestruct "Htemp_res" as (wl) "[>%Hlen2 Htemp_res]".
    iEval (rewrite big_sepL2_sep) in "Htemp_res"
    ; iDestruct "Htemp_res" as "[_ Htemp_res]".
    iEval (rewrite big_sepL2_sep) in "Htemp_res"
    ; iDestruct "Htemp_res" as "[>Htemp_res _]".

    rewrite (big_sepL2_zip_snd_2 _ (zip pl φl) wl (λ a w, a ↦ₐ w)%I); last done.
    iEval (rewrite big_sepL2_app_inv_l) in "Htemp_res"
    ; iDestruct "Htemp_res" as (stk arg_locals) "(%Hwl & Hstk & Hargs_locals)".
    rewrite -/(region_pointsto (a_stk ^+ 4)%a e_stk stk).
    iDestruct (region_pointsto_cons with "[$Ha3_stk $Hstk]") as "Hstk".
    { solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "[$Ha2_stk $Hstk]") as "Hstk".
    { solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "[$Ha1_stk $Hstk]") as "Hstk".
    { solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "[$Ha0_stk $Hstk]") as "Hstk".
    { solve_addr. }
    { solve_addr. }

    focus_block 6 "Hcode" as a6 Ha6 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 7 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cra ca2 *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 8 "Hcode" as a8 Ha8 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct1]") as "Hrmap".
    rewrite -delete_insert_ne //.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct0]") as "Hrmap".
    do 2 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs0]") as "Hrmap".
    do 3 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs1]") as "Hrmap".
    do 4 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca2]") as "Hrmap".
    do 5 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hctp]") as "Hrmap".

    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]"); try solve_pure.
    { clear -Hfull_rmap.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hfull_rmap.
      rewrite Hfull_rmap.
      set_solver.
    }
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Harg_rmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 9 "Hcode" as a9 Ha9 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* close switcher invariant *)
    iDestruct (tframe_update _ _ (frm W0) with "Htframe_full Htframe_frag")
                as ">[Htframe_full Htframe_frag]".
    iDestruct (region_pointsto_cons with "[$tstk $Htstk]") as "Htstk".
    { solve_addr. }
    { solve_addr. }
    iMod ("Hclose_switcher_inv" with
           "[$Hna $Hmtdc $Hcode $Hb_switcher $Htstk $Htframe_full $Hp_ot_switcher]")
      as "Hna"; first done.

    iMod (sts_update_loc _ _ _ _ false with "[$Hworld] [$Hι_loc]") as "[Hworld Hι_loc]".
    iMod ("Hclose_frame_inv" with "[$Hna $Hι_loc]") as "Hna".
    iMod (update_region_revoked_update_loc with "[$] [$]") as "[Hregion Hworld]".
    { rewrite /revoke_condition.
      simpl; apply revoke_conditions_sat.
    }
    { by cbn. }
    { admit. (* NOTE by definition of Hι_sts *) }

    iDestruct (sts_update_frm _ _ (frm W0) with "Hworld") as ">Hworld".
    iMod (update_region_revoked_update_loc with "[$] [$]") as "[Hregion Hworld]".
    { apply revoke_conditions_sat. }
    { by cbn. }
    { apply related_sts_priv_world_update_frm. }

    iDestruct (big_sepL_app _ (finz.seq_between a_stk (a_stk ^+ 4)%a)
                           (finz.seq_between (a_stk ^+ 4)%a e_stk)
                with "[$Hrel_reg_saved $Hrel_callee_frm]")
      as "Hrel_stk".
    rewrite -finz_seq_between_split; last solve_addr.

    iDestruct (big_sepL_sep with "Htemp_unknown") as "[Htemp_unknown %Hunknown_revoked]".
    iMod (monotone_close_list_region W0 _ _ ltemp_unknown
                with "[] [$Hworld $Hregion $Htemp_unknown]") as "[Hworld Hregion]".
    { iPureIntro; eapply helper_switcher_final_pub; eauto. }

    iApply ("Hφ" with "[-]"); iFrame "∗#".
    iSplit.
    { iPureIntro; eapply helper_switcher_final_pub; eauto. }
    iSplit.
    { by rewrite Harg_rmap'. }
    iSplitR "Hargs_locals".
    { rewrite big_sepL_sep; iFrame "#".
      iPureIntro. intros k' a' Ha'; cbn.
      rewrite -close_list_std_sta_same; cycle 1.
      { admit. (* NOTE disjoint by Hdis_unkw_stk *) }
      admit. (* NOTE true, because by Ha',
                either it was Revoked (register_save_area),
                or it was Temporary *)
    }
    { rewrite region_addrs_exists; iFrame. }
  Admitted.



  (* TODO:
     - How to encode the number of registers to pass as arguments?
       A possibility is to use a resource that encodes it.
   *)
  Lemma switcher_cc_specification
    (Nswitcher Nframe : namespace)
    (W0 : WORLD)
    (C : CmptName)
    (b_switcher e_switcher a_switcher_cc : Addr)
    (b_stk e_stk a_stk : Addr)
    (ot_switcher : OType)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (w_entry_point : Sealable)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (a_local_args : list Addr) (p_local_args : list Perm)
    (b_tstk e_tstk : Addr)
    (φ : val -> iPropI Σ) :

    (* ct1 must contain the target entry points, which needs to be sealed with ot_switcher *)
    let wct1_caller := WSealed ot_switcher w_entry_point in
    (* the state of the stack before the jump  *)
    let stk_caller_save_area :=
      [wcs0_caller;wcs1_caller;wcra_caller;wcgp_caller]
    in
    let stk_callee_frame_pre_jmp :=
        (region_addrs_zeroes (a_stk ^+4)%a e_stk)
    in
    let stk_pre_jmp :=
     stk_caller_save_area ++ stk_callee_frame_pre_jmp
    in
    let callee_stk_frm_addr := (finz.seq_between (a_stk ^+ 4)%a e_stk) in

    let W0' := frame_W (switcher_world_pre_frame W0 callee_stk_frm_addr) in
    let W1 := switcher_world_upon_jmp W0 a_local_args callee_stk_frm_addr in

    Nswitcher ## Nframe ->
    is_arg_rmap arg_rmap ->
    dom rmap = all_registers_s ∖ ((dom arg_rmap) ∪ {[ PC ; cgp ; cra ; csp ; cs0 ; cs1 ; ct1 ]} ) ->
    Forall (λ a : Addr, (std W0) !! a = Some Revoked) a_local_args ->

    ( na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher )

      (* PRE-CONDITION *)
      ∗ na_own logrel_nais ⊤
      (* Registers *)
      ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_cc
      ∗ cgp ↦ᵣ wcgp_caller
      ∗ cra ↦ᵣ wcra_caller
      (* Stack register *)
      ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
      (* Entry point of the target compartment *)
      ∗ ct1 ↦ᵣ wct1_caller ∗ interp W1 C wct1_caller
      ∗ cs0 ↦ᵣ wcs0_caller
      ∗ cs1 ↦ᵣ wcs1_caller
      (* Argument registers, need to be safe-to-share *)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W1 C warg )
      (* All the points-to predicate of the addresses shared as local argument have to be passed by the user,
         via the list a_local_args; and they have to not be in the domain
       *)
      ∗ ([∗ list] a ∈ a_local_args, ∃ w, a ↦ₐ w )
      (* ∗ ([∗ list] a;p ∈ a_local_args;p_local_args, rel C a p interpC *)
      (*                                              ∗ sts_state_std C a Revoked *)
      (*                                              ∗ ⌜ isWL p = false⌝) *)
      (* All the other registers *)
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* Stack frame *)
      ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

      (* Interpretation of the world, at the moment of the switcher_call *)
      ∗ sts_full_world W0 C
      (* region W0 C *)
      ∗ region W0 C
      ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), rel C a RWL interpC ∗ ⌜ std W0 !! a = Some Revoked ⌝ )
      ∗ tframe_frag (frm W0)


      (* Transformation of the world, before the jump to the adversary *)
      ∗ (region W0' C ∗ sts_full_world W0' C
          ∗ ([∗ list] a ∈ a_local_args, ∃ w : Word, a ↦ₐ w )
          ==∗
          region W1 C ∗ sts_full_world W1 C)


      (* POST-CONDITION *)
      ∗ ▷ ( (∃ (W2 : WORLD) (rmap' : Reg),
                (* We receive a public future world of the world pre switcher call *)
                ⌜ related_sts_pub_world W0 W2 ⌝
                ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ]} ⌝
                ∗ na_own logrel_nais ⊤
                (* Interpretation of the world *)
                ∗ sts_full_world W2 C
                ∗ region W2 C
                ∗ tframe_frag (frm W2)
                ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), rel C a RWL interpC ∗ ⌜ std W2 !! a = Some Revoked ⌝ )
                ∗ PC ↦ᵣ updatePcPerm wcra_caller
                (* cgp is restored, cra points to the next  *)
                ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller
                ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
                ∗ (∃ warg0, ca0 ↦ᵣ warg0)
                ∗ (∃ warg1, ca1 ↦ᵣ warg1)
                ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
                ∗ ([∗ list] a ∈ a_local_args, ∃ w, a ↦ₐ w )
                ∗ [[ a_stk , e_stk ]] ↦ₐ [[ region_addrs_zeroes a_stk e_stk ]])
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})
    )
    ⊢ WP Seq (Instr Executable)
       {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    intros Hwct1_caller Hstk_caller_save_area Hstk_caller_frm_pre  Hstk_pre_jmp Hcallee_stk_frm_addr W0' W1
      HN Harg_map Hrmap Hlocal_args_revoked.
    iIntros "(#Hinv_switcher & Hna
           & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Hinterp_ct1 & Hcs0 & Hcs1
           & Hargmap & Hlocal_args & Hrmap & Hstk & Hworld & Hregion
           & Hstd_stk & Htframe_frag & Hnext_world & Hφ)".
    iEval (rewrite big_sepL_sep) in "Hstd_stk".
    iDestruct "Hstd_stk" as "[#Hrel_stk Hstd_state_stk]".

    (* ------------------------------------------------ *)
    (* -------- Prepare resources for the proof ------- *)
    (* ------------------------------------------------ *)

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk d tstk_next)
           "(>Hmtdc & >%Hbounds & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & Htframe_full & >%H_tstk_frame & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region; clear H0.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iHide "Hφ" as hφ.

    (* --- Extract scratch registers ct2 ctp --- *)
    assert (exists wct2, rmap !! ct2 = Some wct2) as [wct2 Hwct2].
    { admit. (* NOTE easy but tedious *) }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap !! ctp = Some wctp) as [wctp Hwctp].
    { admit. (* NOTE easy but tedious *) }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    (* ------------------------------------------------ *)
    (* ----- Start the proof of the switcher here ----- *)
    (* ------------------------------------------------ *)

    (* --- First, we destruct cases where it will quickly fail ---  *)
    destruct (decide ((a_stk ^+ 4) < e_stk))%a as [Hstk_ae|Hstk_ae]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    destruct (decide (b_stk <= a_stk))%a as [Hstk_ba|Hstk_ba]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }

    iAssert (⌜ a_local_args ## (finz.seq_between a_stk e_stk) ⌝)%I
      with "[ Hlocal_args Hstk]" as "%Hdisjoint_locals_stk".
    { rewrite /region_pointsto.
      rewrite region_addrs_exists.
      iDestruct "Hlocal_args" as (ws) "Hlocal_args".
      iClear "#"; clear.
      iApply big_sepL2_disjoint; eauto; iFrame.
    }
    iAssert (⌜ NoDup a_local_args ⌝)%I
      with "[Hlocal_args]" as "%HNoDup_locals".
    { rewrite region_addrs_exists.
      iDestruct "Hlocal_args" as (ws) "Hlocal_args".
      by iApply big_sepL2_nodup. }

    iDestruct (big_sepL2_length with "Hstk") as %Hlen_stk.
    iAssert (⌜ exists stk_wa stk_wa1 stk_wa2 stk_wa3 stk_mem',
                 (stk_mem = stk_wa :: stk_wa1 :: stk_wa2 :: stk_wa3 :: stk_mem')⌝)%I
      as %(stk_wa & stk_wa1 & stk_wa2 & stk_wa3 & stk_mem' & ->).
    { iEval (rewrite /region_pointsto) in "Hstk".
      iPureIntro.
      assert (length (finz.seq_between a_stk e_stk) > 4) as Hlen_stk_ae.
      { rewrite finz_seq_between_length.
        assert (a_stk^+4 < e_stk)%a by solve_addr.
        do 5 (rewrite finz_dist_S; last solve_addr); lia.
      }
      destruct stk_mem as [|stk_wa stk_mem0]; first (cbn in Hlen_stk; lia).
      destruct stk_mem0 as [|stk_wa1 stk_mem1]; first (cbn in Hlen_stk; lia).
      destruct stk_mem1 as [|stk_wa2 stk_mem2]; first (cbn in Hlen_stk; lia).
      destruct stk_mem2 as [|stk_wa3 stk_mem3]; first (cbn in Hlen_stk; lia).
      destruct stk_mem3 as [|stk_wa4 stk_mem4]; first (cbn in Hlen_stk; lia).
      eexists _,_,_,_,_; done.
    }

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.

    (* ---- store csp cs0 ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha1_stk Hstk]".
    { transitivity (Some (a_stk ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 1%Z)%a); auto;solve_addr. }

    (* ---- store csp cs1 ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha2_stk Hstk]".
    { transitivity (Some (a_stk ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 2%Z)%a); auto;solve_addr. }

    (* ---- store csp cra ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha3_stk Hstk]".
    { transitivity (Some (a_stk ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 3%Z)%a); auto;solve_addr. }

    (* ---- store csp cgp ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha4_stk Hstk]".
    { transitivity (Some (a_stk ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 4%Z)%a); auto;solve_addr. }

    (* --- getp ct2 csp --- *)
    iInstr "Hcode".

    (* --- mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".

    (* --- sub ct2 ct2 ctp --- *)
    iInstr "Hcode".
    replace ((encodePerm RWL - encodePerm RWL)%Z) with 0%Z by lia.

    (* --- jnz 2 ct2 --- *)
    iInstr "Hcode".

    (* --- jmp 2 --- *)
    iInstr "Hcode".

    (* --- readsr ct2 mtdc --- *)
    iInstr "Hcode".
    { done. (* TODO add to solve_pure *) }

    destruct (decide ((a_tstk ^+ 2) < e_tstk))%a as [Htstk_ae|Htstk_ae]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    destruct (decide (b_tstk <= a_tstk))%a as [Htstk_ba|Htstk_ba]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    iAssert (⌜ exists tstk_a1 tstk_next', (tstk_next = tstk_a1 :: tstk_next')⌝)%I
      as %(tstk_a1 & tstk_next' & ->).
    { iEval (rewrite /region_pointsto) in "Htstk".
      iDestruct (big_sepL2_length with "Htstk") as %Hlen_tstk.
      iPureIntro.
      assert (1 < length (finz.seq_between (a_tstk ^+ 1)%a e_tstk)) as Hlen_tstk_ae.
      { rewrite finz_seq_between_length.
        assert (a_tstk^+2 < e_tstk)%a by solve_addr.
        rewrite finz_dist_S; last solve_addr.
        rewrite finz_dist_S; last solve_addr; lia.
      }
      destruct tstk_next as [|stk_a1 tstk_next]; first (cbn in Hlen_tstk; lia).
      exists stk_a1, tstk_next; done.
    }
    iDestruct (region_pointsto_cons with "Htstk") as "[Ha1_tstk Htstk]".
    { transitivity (Some (a_tstk ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Lea ct2 1%Z; *)
    iInstr "Hcode".
    {  transitivity (Some (a_tstk ^+1)%a); solve_addr. }

    (* Store ct2 csp; *)
    iInstr "Hcode".
    { rewrite /withinBounds andb_true_iff; solve_addr. }

    (* WriteSR mtdc ct2; *)
    iInstr "Hcode".
    { done. (* TODO add to solve_pure *) }

    (* Zero out the callee's stack frame *)
    (* GetE cs0 csp; *)
    iInstr "Hcode".

    (* GetA cs1 csp; *)
    iInstr "Hcode".

    (* Subseg csp cs1 cs0 *)
    iInstr "Hcode" with "Hlc".
    { rewrite /isWithin andb_true_iff; solve_addr. }

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 1 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hcs0 $Hcs1 $Hcode $Hstk]"); eauto.
    { done. }
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    iHide "Hcode" as hcode.
    iHide "Hφ" as hφ.

    iDestruct "Hstd_state_stk" as "%Hstk_revoked".


    (* UPDATING THE WORLD NOW *)
    opose proof ( extract_temps W0 ) as (ltemp_unknown & HNoDup_unk & W_temps).
    (* 1) revoke the world *)
    iMod ( monotone_revoke_keep _ C ltemp_unknown with "[$Hworld $Hregion]") as "(Hworld & Hregion & Htemp_unknown)".
    { by cbn. }
    { iPureIntro.
      intros k' a' Hk'; cbn.
      apply W_temps.
      apply elem_of_list_lookup.
      by eexists.
    }
    rewrite revoke_resources_later
    ; iMod (lc_fupd_elim_later with "Hlc Htemp_unknown") as "Htemp_unknown".

    iAssert (⌜ ltemp_unknown ## a_local_args  ⌝)%I as "%Hdis_unk_locals".
    {
      rewrite revoked_resources_pointsto.
      iDestruct "Htemp_unknown" as (ws) "[%Hlen_ltemp Hltemp_unknown]".
      iDestruct (region_addrs_exists with "Hlocal_args") as (lw_args) "Hlocal_args".
      iApply big_sepL2_disjoint; iFrame.
    }

    iAssert (⌜ ltemp_unknown ## finz.seq_between a_stk e_stk⌝)%I as "%Hdis_unk_stk".
    {
      rewrite revoked_resources_pointsto.
      iDestruct "Htemp_unknown" as (ws) "[%Hlen_ltemp Hltemp_unknown]".
      iDestruct (big_sepL2_disjoint_pointsto with "[$Hltemp_unknown $Ha1_stk]") as "%Ha1_stk".
      iDestruct (big_sepL2_disjoint_pointsto with "[$Hltemp_unknown $Ha2_stk]") as "%Ha2_stk".
      iDestruct (big_sepL2_disjoint_pointsto with "[$Hltemp_unknown $Ha3_stk]") as "%Ha3_stk".
      iDestruct (big_sepL2_disjoint_pointsto with "[$Hltemp_unknown $Ha4_stk]") as "%Ha4_stk".
      iDestruct (big_sepL2_disjoint with "[$Hltemp_unknown $Hstk]") as "%Hstk"; iFrame.
      iPureIntro.
      clear -Ha1_stk Ha2_stk Ha3_stk Ha4_stk Hstk Hstk_ae Hstk_ba.
      do 4 (rewrite finz_seq_between_cons; last solve_addr).
      intros a Ha Ha'.
      rewrite elem_of_cons in Ha'; destruct Ha' as [-> | Ha']; first set_solver.
      rewrite elem_of_cons in Ha'; destruct Ha' as [-> | Ha']; first set_solver.
      replace ((a_stk ^+ 1) ^+1)%a with (a_stk ^+ 2)%a in Ha'; last solve_addr.
      rewrite elem_of_cons in Ha'; destruct Ha' as [-> | Ha']; first set_solver.
      replace ((a_stk ^+ 2) ^+1)%a with (a_stk ^+ 3)%a in Ha'; last solve_addr.
      rewrite elem_of_cons in Ha'; destruct Ha' as [-> | Ha']; first set_solver.
      replace ((a_stk ^+ 3) ^+1)%a with (a_stk ^+ 4)%a in Ha'; last solve_addr.
      set_solver.
    }

    (* 2) update the frame number *)
    iDestruct (tframe_agree with "Htframe_full Htframe_frag") as "->".
    iDestruct (tframe_update _ _ ((frm W0) + 1) with "Htframe_full Htframe_frag")
                as ">[Htframe_full Htframe_frag]".
    iDestruct (sts_update_frm _ _ (W0.2 + 1) with "Hworld") as ">Hworld".
    iMod (update_region_revoked_update_loc with "[$] [$]") as "[Hworld Hregion]".
    { apply revoke_conditions_sat. }
    { by cbn. }
    { apply related_sts_priv_world_update_frm. }

    (* 3) update the callee stack frame as Temporary *)
    rewrite {1}(finz_seq_between_split _ (a_stk^+4)%a e_stk) ; last solve_addr.
    rewrite big_sepL_app;
    iDestruct "Hrel_stk" as "[Hrel_reg_saved Hrel_callee_frm]".
    subst W0'.
    set ( callee_stk_frm_addr := finz.seq_between (a_stk ^+ 4)%a e_stk ).

    iMod (update_region_revoked_temp_pwl_multiple ⊤ _ _
                 callee_stk_frm_addr (region_addrs_zeroes (a_stk ^+ 4)%a e_stk) RWL interpC
                with "[$] [$] [Hstk]") as "[Hregion Hworld]".
    { done. }
    { done. }
    { apply finz_seq_between_NoDup. }
    { admit. (* NOTE easy, but tedious -- see what was done in the return *) }

    (* 4) add the custom sts for the frame *)
    iMod ( sts_alloc_loc _ C true frame_rel_pub frame_rel_pub frame_rel_priv with "Hworld")
      as "(Hworld & %Hfresh_ι & %Hfresh_ι' & Hsts_loc_ι & #Hsts_rel_ι)".
    rewrite -/(frame_W (std_update_multiple (<d[W0.2 + 1]d>(revoke W0)) callee_stk_frm_addr Temporary)).

    set (W0' := (frame_W (std_update_multiple (<d[W0.2 + 1]d>(revoke W0)) callee_stk_frm_addr Temporary))).
    set (ι := fresh_cus_name (std_update_multiple (<d[W0.2 + 1]d>(revoke W0)) callee_stk_frm_addr Temporary)).

    iDestruct (region_monotone _ _ W0' with "Hregion") as "Hregion".
    { subst W0'. rewrite /frame_W //=. }
    { apply frame_W_related_sts_pub_world. }

    (* 5) make all local_arg Temporary *)
    iMod ("Hnext_world" with "[$Hregion $Hworld $Hlocal_args]") as "[Hregion Hworld]".
    subst hcode.


    focus_block 2 "Hcode" as a_unseal Ha_unseal "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* GetB cs1 PC *)
    iInstr "Hcode".

    (* GetA cs0 PC *)
    iInstr "Hcode".

    (* Sub cs1 cs1 cs0 *)
    iInstr "Hcode".
    (* Mov cs0 PC *)
    iInstr "Hcode".
    (* Lea cs0 cs1 *)
    assert ( (a_unseal ^+ 3 + (b_switcher - (a_unseal ^+ 1)))%a = Some ( (b_switcher ^+ 2%Z)%a ))
    as ?.
    { solve_addr. }
    iInstr "Hcode".

    (* Lea cs0 (-2)%Z *)
    iInstr "Hcode".
    { transitivity (Some b_switcher); solve_addr. }

    iEval (rewrite fixpoint_interp1_eq /= /interp_sb) in "Hinterp_ct1".
    iDestruct "Hinterp_ct1"
      as (Pct1 Hpers_Pct1) "(HmonoReq & Hseal_pred_Pct1 & HPct1 & HPct1_borrow)".
    iDestruct (seal_pred_agree with "Hseal_pred_Pct1 Hp_ot_switcher") as "Hot_switcher_agree".
    iSpecialize ("Hot_switcher_agree" $! (W1,C,WSealable w_entry_point)).

    (* Load cs0 cs0 *)
    iInstr "Hcode".
    iEval (cbn) in "Hcs0".

    rewrite /ot_switcher_prop.
    iEval (rewrite /safeC /=) in "Hot_switcher_agree".
    iRewrite "Hot_switcher_agree" in "HPct1".
    rewrite /ot_switcher_propC /ot_switcher_prop.
    iDestruct "HPct1" as (g_tbl b_tbl e_tbl a_tbl
                         bpcc epcc bcgp ecgp nargs off_entry
                            Heq_entry_point Hatbl Hbtbl Hbtbl1 Hnargs)
                           "(#Hinv_pcc_B & #Hinv_cgp_B & #Hinv_entry_B_f & #Hjmp_callee_pc)".
    iClear "Hot_switcher_agree".
    cbn in Heq_entry_point.
    rewrite !Heq_entry_point.

    (* UnSeal ct1 cs0 ct1 *)
    assert ( ot_switcher < (ot_switcher ^+1) )%ot as Hot_switcher.
    { admit. (* TODO add hyp *) }

    subst Hwct1_caller.
    iInstr "Hcode".
    { done. (* TODO solve_pure *) }
    { apply withinBounds_true_iff; solve_addr. (* TODO solve_pure *) }
    rewrite Heq_entry_point.


    (* Load cs0 ct1 *)
    wp_instr.
    iInv "Hinv_entry_B_f" as ">Hatbl" "Hcls_atbl".
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr. }
    iEval (cbn) in "Hcs0".
    iMod ("Hcls_atbl" with "Hatbl") as "_"; iModIntro.
    wp_pure.

    (* LAnd ct2 cs0 7%Z *)
    iInstr "Hcode".

    (* ShiftR cs0 cs0 3%Z *)
    iInstr "Hcode".

    replace ( (Z.land (encode_entry_point nargs off_entry) 7)) with nargs by admit.
    replace ( (encode_entry_point nargs off_entry ≫ 3)%Z) with off_entry by admit.
    (* TODO unclear why the above are true: should be properties of encode_entry_point *)
    (* GetB cgp ct1 *)
    iInstr "Hcode".

    (* GetA cs1 ct1 *)
    iInstr "Hcode".

    (* Sub cs1 cgp cs1 *)
    iInstr "Hcode".

    (* Lea ct1 cs1 *)
    iInstr "Hcode".
    { transitivity (Some b_tbl); solve_addr. }

    (* Load cra ct1 *)
    wp_instr.
    iInv "Hinv_pcc_B" as ">Hbtbl" "Hcls_btbl".
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr. }
    iEval (cbn) in "Hcra".
    iMod ("Hcls_btbl" with "Hbtbl") as "_"; iModIntro.
    wp_pure.

    (* Lea ct1 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (b_tbl ^+ 1)%a); solve_addr. }

    (* Load cgp ct1 *)
    wp_instr.
    iInv "Hinv_cgp_B" as ">Hbtbl1" "Hcls_btbl1".
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr. }
    iEval (cbn) in "Hcra".
    iMod ("Hcls_btbl1" with "Hbtbl1") as "_"; iModIntro.
    wp_pure.

    (* Lea cra cs0 *)
    iInstr "Hcode".
    { transitivity (Some (bpcc ^+ off_entry)%a); last solve_addr. admit. }
    (* TODO actually, it's fine if the offset fail, the machine fails...
       we just need not to use iInstr, but instead manually choose the wp rule
     *)

    (* Add ct2 ct2 1%Z *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 3 "Hcode" as a_clear_pre_reg1 Ha_clear_pre_reg1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_registers_pre_call_skip_spec with "[- $HPC $Hargmap $Hct2 $Hcode]"); try solve_pure.
    { solve_addr. }
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Hct2 & Harg_rmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 4 "Hcode" as a_clear_pre_reg2 Ha_clear_pre_reg2 "Hcode" "Hcont"; iHide "Hcont" as hcont.

    iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.

    iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap".
    { simplify_map_eq. apply not_elem_of_dom.
      rewrite Hrmap; set_solver+.
    }
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { simplify_map_eq. apply not_elem_of_dom.
      rewrite Hrmap; set_solver+.
    }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { simplify_map_eq. apply not_elem_of_dom.
      rewrite Hrmap; set_solver+.
    }
    iApply (clear_registers_pre_call_spec with "[- $HPC $Hrmap $Hcode]"); try solve_pure.
    { clear -Harg_map Hrmap.
      rewrite !dom_insert_L.
      rewrite Hrmap.

      rewrite -difference_difference_l_L.
      do 4 rewrite union_assoc_L.
      rewrite union_comm_L.
      replace {[cs1; cs0; ct1; ct2; ctp]}
        with ({[cs1; cs0; ct1]} ∪ {[ct2; ctp]} : gset _) by set_solver.
      replace ( (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]})
                 ∪ ({[cs1; cs0; ct1]} ∪ {[ct2; ctp]}))
        with ( (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]}
                  ∪ {[cs1; cs0; ct1]}) ∪ {[ct2; ctp]}) by set_solver.
      rewrite union_comm_L.
      replace (
         (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]} ∪ {[cs1; cs0; ct1]})
        )
        with (
         all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp]}
        ).
      2:{
        replace {[PC; cgp; cra; csp; cs0; cs1; ct1]}
        with ( {[PC; cgp; cra; csp]} ∪ {[cs1; cs0; ct1]} : gset _)
             by set_solver.
      rewrite -(difference_difference_l_L  _ _ {[cs1; cs0; ct1]}).
      rewrite difference_union_L.
      set_solver.
      }
      rewrite subseteq_union_1_L; set_solver.
    }
    iNext; iIntros "H".
    iDestruct "H" as (rmap') "(%Hrmap' & HPC & Hrmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 5 "Hcode" as a_jmp Ha_jmp "Hcode" "Hcont"; iHide "Hcont" as hcont.
    set (
        rmap'' :=
       <[PC:=WCap RX Global bpcc epcc (bpcc ^+ off_entry)%a]>
      (<[csp:=WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a]>
         (<[cra:=WSentry XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a]>
            (<[cgp:=WCap RW Global bcgp ecgp bcgp]> (arg_rmap' ∪ rmap'))))
      ).
    iSpecialize ("Hjmp_callee_pc" $! W1 rmap'' (related_sts_priv_refl_world W1)).

    (* Jalr cra cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.
    iEval (cbn) in "Hcgp".

    (* show that csp in safe-to-share *)
    iAssert ( interp W1 C (WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a)) as "Hinterp_csp".
    { iEval (rewrite fixpoint_interp1_eq); cbn.
      subst callee_stk_frm_addr.
      iApply big_sepL_intro.
      iModIntro. iIntros (? astk Hastk).
      assert ( (std W1) !! astk = Some Temporary) as Hastk_temporary.
      { apply (monotone.region_state_pub_temp W0').
        + subst W1 W0'; cbn.
          apply related_sts_pub_update_multiple_temp.
          apply Forall_forall.
          intros a' Ha'.
          rewrite frame_W_lookup_std.
          rewrite std_sta_update_multiple_lookup_same_i.
          2: { intro Hcontra.
               clear -Ha' Hcontra Hdisjoint_locals_stk.
               rewrite /disjoint /set_disjoint_instance in Hdisjoint_locals_stk.
               eapply Hdisjoint_locals_stk; eauto.
               apply elem_of_finz_seq_between in Hcontra.
               apply elem_of_finz_seq_between.
               solve_addr.
          }
          cbn.
          apply revoke_lookup_Revoked.
          rewrite elem_of_list_lookup in Ha'.
          destruct Ha' as [k' Ha'].
          by eapply Forall_lookup in Ha'; eauto; cbn in Ha'.
        + eapply std_update_multiple_lookup; eauto.
      }
      iExists RWL, interp; cbn.
      iSplit; first done.
      iSplit; first (iPureIntro; apply persistent_cond_interp).
      iSplit; first (iDestruct (big_sepL_lookup with "Hrel_callee_frm") as "?"; eauto).
      iSplit; first (iNext; iApply zcond_interp).
      iSplit; first (iNext; iApply rcond_interp).
      iSplit; first (iNext; iApply wcond_interp).
      iSplit; first (iApply monoReq_interp; done).
      by rewrite /region_state_pwl.
    }

    (* allocate frame invariant *)
    (* rewrite tstack_frag_combine_cons. *)
    iHide "Htemp_unknown" as htemp_unknown.

    set (Pframe := (hφ0
                    ∗ (a_tstk ^+ 1)%a ↦ₐ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a
                    ∗ [[a_stk,(a_stk ^+ 4)%a]]↦ₐ[[Hstk_caller_save_area]]
                    ∗ htemp_unknown
                   )%I).
    iMod (na_inv_alloc
            logrel_nais
            ⊤ (Nframe .@ ι)
            (frame_inv C ι Pframe)
           with "[$Hsts_loc_ι $Ha1_tstk $Hφ $Htemp_unknown Ha1_stk Ha2_stk Ha3_stk Ha4_stk ]") as "#Hinv_frame".
    { iNext; iFrame.
      rewrite /Hstk_caller_save_area.
      admit. (* NOTE just iris manipulation *)
    }

    (* close switcher invariant *)
    iMod ("Hclose_switcher_inv" with
           "[$Hna Hmtdc Hcode Hb_switcher Htstk Htframe_full]")
      as "Hna"
    .
    { iNext; iFrame "Hmtdc".
      iExists (frm W0 + 1),tstk_next'.
      iSplit; first done.
      iSplit; first done.
      iFrame.
      replace ((a_tstk ^+ 1) ^+ 1)%a with (a_tstk ^+ 2)%a by solve_addr+Htstk_ae.
      iFrame "∗#".
      iPureIntro.
      clear -H_tstk_frame Htstk_ba Htstk_ae.
      replace a_tstk with (b_tstk ^+ frm W0)%a; solve_addr.
    }

    iAssert (interp W1 C (WSentry XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a)) as "Hinterp_return".
    { shelve. }

    iDestruct (big_sepM_sep with "Harg_rmap'") as "[Harg_rmap' #Harg_rmap'_interp]".
    iDestruct (big_sepM_sep with "Hrmap'") as "[Hrmap' %Hrmap'_zero]".
    iCombine "Harg_rmap' Hrmap'" as "Hrmap'".

    rewrite -(big_sepM_union _ arg_rmap' rmap').
    2: {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      apply map_disjoint_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap' $Hcgp]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap' $Hcra]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ csp with "[$Hrmap' $Hcsp]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      do 2 rewrite lookup_insert_ne //.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ PC with "[$Hrmap' $HPC]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      do 3 rewrite lookup_insert_ne //.
      apply not_elem_of_dom.
      set_solver.
    }

    match goal with
    | _ : _ |- context [<[PC:=?w]> ?m] =>
        subst rmap'' ; set (rmap'' := <[PC:=w]> m)
    end.
    (* rewrite -(insert_id rmap'' PC (WCap RX Global bpcc epcc (bpcc ^+ off_entry)%a)). *)
    (* 2: { by subst rmap'' ; rewrite lookup_insert. } *)
    iApply "Hjmp_callee_pc"; iFrame.
    iSplitR "Htframe_frag"; cycle 1.
    { subst W1. rewrite std_update_multiple_frm frame_W_lookup_frm std_update_multiple_frm //=. }
    { rewrite /execute_entry_point_register; cbn.
      iSplitR.
      {
        clear -Hrmap' Harg_rmap'.
        subst hinv_switcher hφ0 htemp_unknown Pframe.
        iPureIntro.
        intros r; cbn.
        destruct (decide (r = PC)) as [Hrpc | Hrpc]; simplify_eq; first by rewrite lookup_insert.
        rewrite lookup_insert_ne //.
        destruct (decide (r = csp)) as [Hrcsp | Hrcsp]; simplify_eq; first by rewrite lookup_insert.
        rewrite lookup_insert_ne //.
        destruct (decide (r = cra)) as [Hrcra | Hrcra]; simplify_eq; first by rewrite lookup_insert.
        rewrite lookup_insert_ne //.
        destruct (decide (r = cgp)) as [Hrcgp | Hrcgp]; simplify_eq; first by rewrite lookup_insert.
        rewrite lookup_insert_ne //.
        apply elem_of_dom.
        rewrite dom_union.
        rewrite elem_of_union.
        destruct (decide (r ∈ dom arg_rmap')); first by left.
        right.
        rewrite Harg_rmap' in n.
        assert (r ∉ ({[PC; cra; cgp; csp]} : gset RegName)).
        { set_solver.  }
        rewrite Hrmap'.
        rewrite elem_of_difference.
        split; first by apply all_registers_s_correct.
        set_solver.
      }
      iSplitR.
      { iPureIntro. by rewrite lookup_insert. }
      iSplitR.
      { iPureIntro.
        subst rmap''.
        do 3 (rewrite lookup_insert_ne //).
        by rewrite lookup_insert.
      }
      iSplitR.
      { iIntros (wstk Hcsp).
        subst rmap''.
        rewrite lookup_insert_ne // in Hcsp.
        rewrite lookup_insert in Hcsp; simplify_eq.
        iFrame "#".
      }
      iSplitR.
      { iIntros (wret Hcra).
        subst rmap''.
        do 2 (rewrite lookup_insert_ne // in Hcra).
        rewrite lookup_insert in Hcra; simplify_eq.
        iFrame "#".
      }
      iSplitR.
      { iIntros (r wr Hr_arg Hr).
        subst rmap''.
        iClear "Hjmp_callee_pc Hp_ot_switcher".
        clear -Hr_arg Hr Harg_rmap' Hrmap'.

        rewrite /dom_arg_rmap in Hr_arg.
        destruct (decide (r = PC)) as [Hrpc|Hrpc]
        ; first (exfalso ; set_solver+Hr_arg Hrpc).
        destruct (decide (r = csp)) as [Hrcsp|Hrcsp]
        ; first (exfalso ; set_solver+Hr_arg Hrcsp).
        destruct (decide (r = cra)) as [Hrcra|Hrcra]
        ; first (exfalso ; set_solver+Hr_arg Hrcra).
        destruct (decide (r = cgp)) as [Hrcgp|Hrcgp]
        ; first (exfalso ; set_solver+Hr_arg Hrcgp).
        do 4 (rewrite lookup_insert_ne // in Hr).
        rewrite lookup_union in Hr.
        rewrite union_Some in Hr.
        destruct Hr as [Hr | Hr]; cycle 1.
        { exfalso.
          destruct Hr as [Hcontra _].
          rewrite /is_arg_rmap /dom_arg_rmap in Harg_rmap'.
          rewrite -Harg_rmap' in Hr_arg.
          apply lookup_lookup_total_dom in Hr_arg.
          congruence.
        }
        rewrite big_sepM_lookup; eauto.
      }
      {
        iIntros (r Hr); iPureIntro.
        clear -Hr Harg_rmap' Hrmap' Hrmap'_zero.

        rewrite not_elem_of_union in Hr.
        destruct Hr as [Hr1 Hr2].
        repeat (rewrite not_elem_of_union in Hr2).
        repeat (rewrite not_elem_of_singleton in Hr2).
        destruct Hr2 as [ [ [Hrpc Hrcra ] Hrcgp] Hrcsp] .
        do 4 (rewrite lookup_insert_ne //).
        rewrite lookup_union.
        rewrite union_Some.
        right.
        split.
        {
        rewrite /is_arg_rmap in Harg_rmap'.
        rewrite -Harg_rmap' not_elem_of_dom in Hr1.
        done.
        }
        assert (is_Some (rmap' !! r)) as [wr Hr].
        { rewrite -elem_of_dom.
          rewrite Hrmap'.
          rewrite elem_of_difference.
          split ; first apply all_registers_s_correct.
          set_solver.
        }
        eapply map_Forall_lookup_1 in Hrmap'_zero; eauto.
        by simplify_eq.
    }

    (* Proof of the return *)
    Unshelve.

    iClear "Hp_ot_switcher HmonoReq Hseal_pred_Pct1
    HPct1_borrow Hjmp_callee_pc Hinterp_csp".
    clear
      (* Ha_jmp a_jmp *)
      Hrmap' Harg_rmap'
      Ha_clear_pre_reg2 a_clear_pre_reg2
      Ha_clear_pre_reg1 a_clear_pre_reg1
      H1 Ha_unseal a_unseal
      Ha_clear_stk1 a_clear_stk1.
    clear Hwctp Hwct2 Hrmap rmap rmap' rmap''.
    subst hclose_switcher_inv hφ.
    clear Hstk_pre_jmp.
    cbn in Ha_jmp.
    clear Harg_map.
    clear Hnargs arg_rmap' Hot_switcher.
    clear Hatbl Hbtbl Hbtbl1.
    clear Hlen_stk wct2 wctp stk_wa stk_wa1 stk_wa2 stk_wa3 stk_mem' tstk_next'.
    subst W0' ; cbn.

    iApply switcher_ret_specification ; eauto.
    { apply Forall_forall.
      intros a Ha.
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [k Ha].
      by apply Hstk_revoked in Ha.
    }
    iFrame "#".
    { iPureIntro. intros k a Ha; cbn.
      apply revoke_lookup_Revoked.
      by apply Hstk_revoked in Ha.
    }
  Admitted.


  Lemma switcher_interp (W : WORLD) (C : CmptName) (N : namespace)
    (b_switcher e_switcher a_switcher_cc b_tstk e_tstk : Addr) (ot_switcher : OType) :
    na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher) -∗
    interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_cc).
  Proof.
  Admitted.

  Lemma future_priv_mono_interp_switcher (C : CmptName) (Nswitcher : namespace)
    (b_switcher e_switcher a_switcher_cc b_tstk e_tstk : Addr) (ot_switcher : OType) :
    na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher) -∗
    future_priv_mono C interpC (WSentry XSRW_ Local b_switcher e_switcher a_switcher_cc).
  Proof.
  Admitted.


End Switcher.
