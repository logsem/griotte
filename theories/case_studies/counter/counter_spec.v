From iris.proofmode Require Import proofmode.
From griotte Require Import logrel.
From griotte Require Import monotone.
From griotte Require Import rules.
From griotte Require Import interp_weakening.
From griotte Require Import fetch_spec.
From griotte Require Import switcher_spec_call.
From griotte Require Import counter.
From griotte Require Import switcher_spec_return.
From griotte Require Import world_interp_stack.
From griotte Require Import proofmode.
From griotte Require Import allocator_resources.
From griotte Require Import heap_region.

Section Counter.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Context {C : CmptName}.

  Lemma related_pub_W0_Wfixed (W0 W2 : WORLD) (csp_b csp_e : Addr ) (l : list Addr):
    let W1 := revoke W0 in
    let W3 := revoke W2 in
    (∀ a : finz MemNum, std W0 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e) ->
    Forall (λ a : finz MemNum, std W3 !! a = Some Revoked) (l++finz.seq_between csp_b csp_e) ->
    related_sts_pub_world W1 W2 ->
    related_sts_pub_world W0 (close_list (l ++ finz.seq_between csp_b csp_e) W3).
  Proof.
    intros * Htemporaries_W0 Hrevoked_W3 Hrelated_pub_W1_W2.

    destruct W0 as [ [ [W0_std W0_cus] W0_seals] W_heap0 ],
               W2 as [ [ [W2_std W2_cus] W2_seals] W_heap2 ]; cbn.
    destruct Hrelated_pub_W1_W2 as (HW1_W2_std & HW1_W2_cus & HW1_W2_seals & HW1_W2_heap).
    split;[|split];cbn; cycle 1.
    { eapply related_sts_pub_trans; eauto; eapply related_sts_pub_refl. }
    { split; [exact HW1_W2_seals | exact HW1_W2_heap]. }
    destruct HW1_W2_std as [HW1_W2_std_dom HW1_W2_std_t].
    cbn in *.
    split.
    {
      intros a Ha.
      rewrite elem_of_dom -close_list_std_sta_is_Some -revoke_std_sta_lookup_Some -elem_of_dom.
      apply HW1_W2_std_dom.
      by rewrite elem_of_dom -revoke_std_sta_lookup_Some -elem_of_dom.
    }
    intros a ρ0 ρ2 Ha0 Ha2.
    destruct ρ0; cycle 1.
    - (* the initial a was in the Permanent state *)
      assert (a ∉ l ++ finz.seq_between csp_b csp_e) as Ha_notin.
      { destruct (Htemporaries_W0 a) as [_ ?].
        intro Hcontra; apply H in Hcontra. by rewrite Ha0 in Hcontra.
      }
      apply revoke_lookup_Perm in Ha0.
      assert (std (revoke ((W0_std, W0_cus, W0_seals, W_heap0))) !! a = Some Permanent) as Ha0' by done.
      rewrite -(std_sta_update_multiple_lookup_same_i _ (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary)
        in Ha0'.
      2: {
        intro Hcontra; apply Ha_notin.
        rewrite elem_of_app; right.
        rewrite !elem_of_finz_seq_between in Hcontra |- *.
        solve_addr.
      }
      rewrite -close_list_std_sta_same in Ha2; last done.
      destruct ρ2.
      + by apply revoke_std_sta_lookup_non_temp in Ha2.
      + done.
      + apply anti_revoke_lookup_Revoked in Ha2.
        destruct Ha2 as [Ha2|Ha2]; first eapply HW1_W2_std_t in Ha0; eauto.
        eapply HW1_W2_std_t in Ha0; last eauto.
        inversion Ha0 as [|??? Hcontra]; simplify_eq.
        inversion Hcontra.
    - (* the initial a was in the Revoked state *)
      destruct ρ2; last apply rtc_refl; apply rtc_once; constructor.
    - (* the initial a was in the Temporary state *)
      assert (a ∈ l ++ finz.seq_between csp_b csp_e) as Ha_in.
      { destruct (Htemporaries_W0 a) as [? _]; by apply Htemporaries_W0. }
      apply revoke_lookup_Monotemp in Ha0.
      assert (std (revoke ((W0_std, W0_cus, W0_seals, W_heap0))) !! a = Some Revoked) as Ha0' by done.
      assert (
          std ((std_update_multiple (revoke (W0_std, W0_cus, W0_seals, W_heap0)) (finz.seq_between (csp_b ^+ 4)%a csp_e)
                  Temporary)) !! a =
          Some (if (decide (a ∈ (finz.seq_between (csp_b ^+ 4)%a csp_e)))
                then Temporary
                else Revoked
        )).
      {
        destruct (decide (a ∈ (finz.seq_between (csp_b ^+ 4)%a csp_e))) as [Ha_in_stk | Ha_in_stk].
        + apply std_sta_update_multiple_lookup_in_i; eauto.
        + rewrite std_sta_update_multiple_lookup_same_i; eauto.
      }
      pose proof Ha_in as Ha_in'.
      rewrite Forall_forall in Hrevoked_W3.
      eapply Hrevoked_W3 in Ha_in;eauto.
      eapply close_list_std_sta_revoked in Ha_in; last apply Ha_in'.
      rewrite Ha_in in Ha2; simplify_eq.
      apply rtc_refl.
  Qed.

  Lemma counter_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)
    (csp_content : list Word)
    (C_f : Sealable)

    (W0 : WORLD)
    (cstk : CSTK)
    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nswitcher Ncounter : namespace)

    :

    let imports := counter_main_imports C_f in

    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_shadow_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    Nswitcher ## Ncounter ->
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp ; cra]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length counter_main_code)%a ->

    (cgp_b + length counter_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    is_heap_cap (WSealed ot_switcher C_f) = false ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->

    (
      allocator_ctx ∗ na_inv cerise_nais Nswitcher switcher_inv
      (* initial memory layout *)
      ∗ na_inv cerise_nais Ncounter
          ( ∃ (cnt : Z),
            [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
            ∗ codefrag pc_a counter_main_code
            ∗ [[ cgp_b, cgp_e ]] ↦ₐ [[ [WInt cnt] ]]
            ∗ ⌜ (0 <= cnt)%Z ⌝
          )
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
      ∗ cra ↦ᵣ WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      ∗ world_interp W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
      ∗ interp W0 C (WCap true RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hcgp_shadow Hcgp_nonheap HNswitcher_counter Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hsealed_nonheap Hframe_match Hcsp_sync
            )
      "(#Halloc & #Hswitcher & #Hmem & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f & #Hentry_C_f
      & #Hinterp_W0_csp
      )".
    iMod (na_inv_acc with "Hmem Hna")
      as "(( %cnt & >Himports_main & >Hcode_main & >Hcgp_main & >%Hcnt) & Hna & Hmem_close)"; auto.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous ; clear H0.

    (* --- Extract registers ca0  --- *)
    assert ( is_Some (rmap !! cs0) ) as [wcs0 Hwcs0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs1) ) as [wcs1 Hwcs1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.

    (* Extract the addresses of b and a *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }


    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜std W0 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_shadow Hstk_heap]; first done.
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_interp_C]")
        as (l) "(%Hl_unk & Hworld_interp_C & #Hstack_revoked_W0 & >%Hrevoked_W0 & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)


    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Load cs0 cgp 0. *)
    iInstr_success "Hcode".
    { reflexivity. }
    { split; [done | solve_addr]. }

    (* Add cs0 cs0 1%Z. *)
    iInstr_success "Hcode".

    (* Store cgp cs0 0. *)
    iInstr "Hcode".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    assert (Forall (fun x : Addr => x ∈ dom (std W1)) l) as Hdom_l.
    { apply Forall_forall. intros x Hx. subst W1. rewrite -revoke_dom_eq.
      rewrite elem_of_dom. exists Temporary. destruct Hl_unk as [_ Htemp].
      apply Htemp. apply elem_of_app. by left. }
    iEval (rewrite world_interp_eq /world_interp_def) in "Hworld_interp_C".
    iDestruct "Hworld_interp_C" as "(Hr & Hsts & Hseals)".
    iDestruct (region_cells_status_some W1 C l Hdom_l with "Hr") as "[Hr %Hstatuses_l]".
    rewrite /W1 revoke_heap in Hstatuses_l.
    destruct (heap_status_partition (heap_std W0) l Hstatuses_l)
      as (l_live & l_q & Hperm_l & Hlive_l & Hq_l).
    iAssert (world_interp W1 C) with "[Hr Hsts Hseals]" as "Hworld_interp_C".
    { rewrite world_interp_eq /world_interp_def. iFrame. }
    iEval (rewrite Hperm_l RevokedResources_app) in "Hrevoked_l".
    iDestruct "Hrevoked_l" as "[Hrevoked_live Hrevoked_q]".
    set (W1q := close_list l_q W1).
    assert (Forall (fun a => heap_cell_status (heap_std W1q) a = Some AllocObjectQuarantined) l_q) as Hq_W1q.
    { rewrite /W1q close_list_heap /W1 revoke_heap. exact Hq_l. }
    iAssert (RevokedResources W1q C l_q) with "[Hrevoked_q]" as "Hrevoked_q'".
    { rewrite (RevokedResources_quarantined W1q C l_q Hq_W1q)
        (RevokedResources_quarantined W0 C l_q Hq_l). iExact "Hrevoked_q". }
    iMod (world_interp_restore W1 C l_q with "[$Hworld_interp_C $Hrevoked_q']")
      as "Hworld_interp_C".
    assert (related_sts_priv_world W0 W1q) as Hpriv_W0_W1q.
    { eapply related_sts_priv_trans_world; [exact Hrelared_priv_W0_W1 |].
      apply related_sts_pub_priv_world, close_list_related_sts_pub. }
    assert (l_q ## finz.seq_between csp_b csp_e) as Hq_stack.
    { destruct Hl_unk as [Hnd _]. apply NoDup_app in Hnd.
      destruct Hnd as (_ & Hdisj & _).
      intros x Hx Hxs. apply (Hdisj x);
        [rewrite Hperm_l; apply elem_of_app; right; exact Hx | exact Hxs]. }
    assert (revoked_addresses W1q (finz.seq_between csp_b csp_e)) as Hrevoked_stk_W1q.
    { apply Forall_forall. intros x Hx.
      rewrite /W1q /close_list /= -close_list_std_sta_same;
        [|set_solver+Hq_stack Hx].
      rewrite /revoked_addresses Forall_forall in Hrevoked_W0.
      by apply Hrevoked_W0. }

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec _ _ _ _ _ _ _ _ _
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call) with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]").
    { reflexivity. }
    { exact H0. }
    { solve_addr. }
    { exact Hpc_shadow. }
    { exact switcher_call_sentry_not_heap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcs0 $Hcs1 $Hcode $Himport_C_f]").
    { reflexivity. }
    { exact H0. }
    { solve_addr. }
    { exact Hpc_shadow. }
    { exact Hsealed_nonheap. }
    { done. }
    { done. }
    { done. }
    iNext ; iIntros "(HPC & Hct1 & Hcs0 & Hcs1 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cs0 cra. *)
    iInstr "Hcode".

    (* Jalr cra ct0. *)
    iInstr "Hcode".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Close the memory invariant before using the switcher's spec*)

    iMod ("Hmem_close" with "[$Hna Himport_switcher Himport_C_f Himports_main $Hcode_main Hcgp_b Hcgp_main]") as "Hna".
    { iExists (cnt+1)%Z.
      iDestruct (region_pointsto_cons with "[$Hcgp_b $Hcgp_main]") as "$" ; [solve_addr|solve_addr|].
      iSplit ; last (iPureIntro;lia).
      iDestruct (region_pointsto_cons with "[$Himport_C_f $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }
    clear dependent cnt.

    (* -- separate argument registers -- *)
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca2) ) as [wca2 Hwca2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca3) ) as [wca3 Hwca3].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca4) ) as [wca4 Hwca4].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca5) ) as [wca5 Hwca5].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    set ( rmap_arg :=
           {[ ca0 := wca0;
              ca1 := wca1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).

    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 0)
                                             then interp W1q C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W1q C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    (* Show that the entry point to C_f is still safe in W1q *)
    iAssert (interp W1q C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply (interp_monotone_sd_same_heap with "[] [$]"); eauto. }
    iClear "Hinterp_W0_C_f".

    (* Prepare the closing resources for the switcher call spec *)
    iDestruct (StackRevokedResources_mono_priv _ W1q with "Hstack_revoked_W0") as "Hstack_revoked_W1"; auto.
    iAssert (⌜ revoked_addresses W1 l ⌝)%I as "%Hrevoked_l_W".
    {
      iPureIntro; apply Forall_forall; intros a Ha.
      rewrite /revoked_addresses Forall_forall in Hrevoked_l.
      by apply Hrevoked_l in Ha.
    }

    iApply (switcher_cc_specification _ _ _ _ _ _ _ _ _ _ _ _ rmap_arg _ _ _ _ _
       with
             "[- $Halloc $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W1 $Hcstk_frag
              $Hinterp_W1_C_f $Hentry_C_f $HK]"); eauto; last iFrame "∗%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap . }

    iNext. subst rmap'; clear stk_mem.
    iIntros (W2 rmap' stk_mem l' rcgp rcra rcs0 rcs1)
      "( %Hl_unk' & Hrevoked_l' & %Hrevoked_l'_W2 & %Hrelated_pub_2ext_W2 & Hrel_stk_C' & %Hdom_rmap & Hstack_revoked_W2 & %Hstack_revoked_W2
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & Hrcs1).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= switcher_base_not_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcs1; [|cbn; eauto].
    subst rcgp rcra rcs0 rcs1.
    iEval (cbn) in "HPC".

    assert (related_sts_pub_world W1q W2) as Hrelated_pub_W1q_W2.
    {
      eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros a Ha.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stk_W1q.
      apply Hrevoked_stk_W1q.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
    }

    assert (Forall (fun a => std W1q !! a = Some Temporary) l_q) as Hq_temp_W1q.
    { apply Forall_forall. intros a Ha. rewrite /W1q /close_list /=.
      apply close_list_std_sta_revoked; first exact Ha.
      rewrite Forall_forall in Hrevoked_l. apply Hrevoked_l.
      rewrite Hperm_l. apply elem_of_app. right. exact Ha. }
    assert (Forall (fun a => std W2 !! a = Some Temporary) l_q) as Hq_temp_W2.
    { apply Forall_forall. intros a Ha.
      eapply region_state_pub_temp; [exact Hrelated_pub_W1q_W2 |].
      rewrite Forall_forall in Hq_temp_W1q. by apply Hq_temp_W1q. }

    set (W3 := revoke W2).
    assert (Forall (fun a => a ∈ dom (std W3)) l_live) as Hdom_live_W3.
    { apply Forall_forall; intros a Ha.
      subst W3. rewrite -revoke_dom_eq.
      eapply elem_of_mono_pub; eauto.
      rewrite /W1q -close_list_dom_eq /W1 -revoke_dom_eq.
      rewrite elem_of_dom. exists Temporary.
      destruct Hl_unk as [_ Htemp]. apply Htemp.
      rewrite Hperm_l. apply elem_of_app. left.
      apply elem_of_app. by left. }
    iEval (rewrite world_interp_eq /world_interp_def) in "Hworld_interp_C".
    iDestruct "Hworld_interp_C" as "(Hr & Hsts & Hseals)".
    iDestruct (region_cells_status_some W3 C l_live Hdom_live_W3 with "Hr")
      as "[Hr %Hstatuses_live_W3]".
    iAssert (world_interp W3 C) with "[Hr Hsts Hseals]" as "Hworld_interp_C".
    { rewrite world_interp_eq /world_interp_def. iFrame. }
    iMod (counter_framed_resources_live W0 W3 C l_live Hlive_l Hstatuses_live_W3
      with "[$Halloc $Hworld_interp_C $Hrevoked_live]")
      as "(#Halloc2 & Hworld_interp_C & Hrevoked_live & %Hlive_W3)".
    iMod (world_interp_revoked_by_separation_many_with_RevokedResources
      W0 W3 C l_live Hlive_l Hlive_W3 Hdom_live_W3
      with "[$Hworld_interp_C $Hrevoked_live]")
      as "(Hworld_interp_C & Hrevoked_live & %Hrevoked_live_W3)".

    iMod (world_interp_revoked_by_separation_many with "[$Hworld_interp_C $Hstk]")
      as "(Hworld_interp_C & Hstk & %Hrevoked_stk_W3)".
    { apply Forall_forall; intros x Hx.
      rewrite revoke_heap. apply heap_cell_live_nonheap.
      apply not_true_is_false. intro Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hstk_heap.
      eapply Hstk_heap; [exact Hx|].
      apply elem_of_finz_seq_between.
      by apply withinBounds_true_iff in Hheap. }
    { apply Forall_forall; intros x Hx.
      subst W3. rewrite -revoke_dom_eq.
      eapply elem_of_mono_pub; eauto.
      rewrite /W1q -close_list_dom_eq /W1 -revoke_dom_eq.
      rewrite elem_of_dom. exists Temporary.
      destruct Hl_unk as [_ Htemp]. apply Htemp.
      apply elem_of_app. by right. }

    assert (l_q ⊆ l') as Hq_in_l'.
    { intros x Hx.
      rewrite Forall_forall in Hq_temp_W2.
      pose proof (Hq_temp_W2 x Hx) as Hx_temp.
      destruct Hl_unk' as [_ Htemp2]. apply Htemp2 in Hx_temp.
      apply elem_of_app in Hx_temp as [Hxl'|Hxtail]; first exact Hxl'.
      exfalso. apply (Hq_stack x Hx).
      apply elem_of_finz_seq_between in Hxtail.
      apply elem_of_finz_seq_between. solve_addr+Hxtail Hcsp_bounds. }
    assert (l_live ## l_q) as Hlive_q_disjoint.
    { destruct Hl_unk as [Hnd _]. rewrite Hperm_l in Hnd.
      apply NoDup_app in Hnd as [Hnd_l _].
      apply NoDup_app in Hnd_l as (_ & Hdisj & _). exact Hdisj. }
    assert (l_live ## finz.seq_between csp_b csp_e) as Hlive_stack.
    { destruct Hl_unk as [Hnd _]. apply NoDup_app in Hnd as (_ & Hdisj & _).
      intros x Hx Hxs. apply (Hdisj x);
        [rewrite Hperm_l; apply elem_of_app; by left | exact Hxs]. }
    assert (Forall (fun a => std W3 !! a = Some Revoked) l_q) as Hrevoked_q_W3.
    { apply Forall_forall. intros x Hx. subst W3.
      apply revoke_lookup_Monotemp.
      rewrite Forall_forall in Hq_temp_W2. by apply Hq_temp_W2. }
    assert (Forall (fun a => std W3 !! a = Some Revoked)
      (l ++ finz.seq_between csp_b csp_e)) as Hrevoked_initial_W3.
    { apply Forall_forall. intros x Hx. apply elem_of_app in Hx as [Hx|Hx].
      - rewrite Hperm_l in Hx. apply elem_of_app in Hx as [Hx|Hx].
        + rewrite Forall_forall in Hrevoked_live_W3. by apply Hrevoked_live_W3.
        + rewrite Forall_forall in Hrevoked_q_W3. by apply Hrevoked_q_W3.
      - rewrite Forall_forall in Hrevoked_stk_W3. by apply Hrevoked_stk_W3. }

    set (l'_fresh := filter
      (fun a => a ∉ l_live ∧ a ∉ finz.seq_between csp_b csp_e) l').
    set (closing_revoked := l_live ++ l'_fresh).
    set (closing := closing_revoked ++ finz.seq_between csp_b csp_e).
    assert (l ⊆ closing_revoked) as Hinitial_in_closing.
    { intros x Hx. subst closing_revoked. apply elem_of_app.
      rewrite Hperm_l in Hx. apply elem_of_app in Hx as [Hlive|Hq]; first by left.
      right. subst l'_fresh. apply list_elem_of_filter. split.
      - split.
        + intros Hlive. apply (Hlive_q_disjoint x Hlive Hq).
        + intros Hstack. apply (Hq_stack x Hq Hstack).
      - by apply Hq_in_l'. }
    assert (l' ++ finz.seq_between (csp_b ^+ 4)%a csp_e ⊆ closing)
      as Hreturned_in_closing.
    { intros x Hx. subst closing closing_revoked.
      apply elem_of_app in Hx as [Hxl'|Hxtail].
      - destruct (decide (x ∈ finz.seq_between csp_b csp_e)) as [Hstack|Hnotstack].
        + apply elem_of_app. by right.
        + apply elem_of_app. left. apply elem_of_app.
          destruct (decide (x ∈ l_live)) as [Hlive|Hnotlive]; first by left.
          right. subst l'_fresh. apply list_elem_of_filter.
          split; [split; assumption|assumption].
      - apply elem_of_app. right.
        apply elem_of_finz_seq_between in Hxtail.
        apply elem_of_finz_seq_between. solve_addr+Hxtail Hcsp_bounds. }
    assert (NoDup closing) as Hclosing_nodup.
    { subst closing closing_revoked. apply NoDup_app. split; [|split].
      - apply NoDup_app. split; [|split].
        + destruct Hl_unk as [Hnd _]. rewrite Hperm_l in Hnd.
          apply NoDup_app in Hnd as [Hnd_l _].
          apply NoDup_app in Hnd_l as [Hnd_live _]. exact Hnd_live.
        + intros x Hlive Hfresh. subst l'_fresh.
          apply list_elem_of_filter in Hfresh as [Hpred _].
          destruct Hpred as [Hnotlive _]. contradiction.
        + subst l'_fresh. apply NoDup_filter.
          destruct Hl_unk' as [Hnd _]. apply NoDup_app in Hnd as [Hnd_l' _]. exact Hnd_l'.
      - intros x Hx Hstack. apply elem_of_app in Hx as [Hlive|Hfresh].
        + by apply (Hlive_stack x Hlive Hstack).
        + subst l'_fresh. apply list_elem_of_filter in Hfresh as [Hpred _].
          destruct Hpred as [_ Hnotstack]. contradiction.
      - apply finz_seq_between_NoDup. }
    assert (∀ x, std W0 !! x = Some Temporary -> x ∈ closing) as Htemp0_cover.
    { intros x Hx. destruct Hl_unk as [_ Htemp]. apply Htemp in Hx.
      apply elem_of_app in Hx as [Hxl|Hxstack].
      - subst closing. apply elem_of_app. left. by apply Hinitial_in_closing.
      - subst closing. apply elem_of_app. by right. }

    set (Wfixed := close_list closing W3).
    assert (related_sts_pub_world W2 Wfixed) as Hpub2.
    { subst Wfixed W3.
      destruct W2 as [ [ [W2std W2cus] W2seals] W2heap ]; cbn.
      split; [|split]; cbn.
      - split.
        + setoid_rewrite <- close_list_dom_eq.
          setoid_rewrite <- revoke_dom_eq. done.
        + intros x ρ2 ρf Hx2 Hxf.
          destruct ρ2.
          * assert (x ∈ l' ++ finz.seq_between (csp_b ^+ 4)%a csp_e) as Hx_close.
            { destruct Hl_unk' as [_ Htemp]. apply Htemp. exact Hx2. }
            rewrite close_list_std_sta_revoked in Hxf; auto.
            { simplify_eq; apply rtc_refl. }
            by apply revoke_lookup_Monotemp.
          * apply revoke_lookup_Perm in Hx2.
            rewrite -close_list_std_sta_same_alt in Hxf; [|intro];
              simplify_eq; apply rtc_refl.
          * destruct ρf; try apply rtc_refl; apply rtc_once; econstructor.
      - apply related_sts_pub_refl.
      - split; [apply related_sts_seals_std_refl|apply related_sts_heap_std_refl]. }
    assert (related_sts_priv_world W0 W2) as Hpriv02.
    { eapply related_sts_priv_pub_trans_world; eauto. }
    assert (related_sts_pub_world W0 Wfixed) as Hpub0.
    { subst Wfixed W3.
      destruct W0 as [ [ [W0std W0cus] W0seals] W0heap ].
      destruct W2 as [ [ [W2std W2cus] W2seals] W2heap ]. cbn in *.
      split; [|split]; cbn.
      - split.
        + destruct Hpriv02 as ((Hdom02 & _) & _ & _ & _).
          setoid_rewrite <- close_list_dom_eq.
          setoid_rewrite <- revoke_dom_eq. exact Hdom02.
        + intros x ρ0 ρf Hx0 Hxf.
          destruct ρ0.
          * assert (x ∈ l ++ finz.seq_between csp_b csp_e) as Hx_close.
            { destruct Hl_unk as [_ Htemp]. apply Htemp. exact Hx0. }
            rewrite close_list_std_sta_revoked in Hxf; auto.
            { simplify_eq; apply rtc_refl. }
            rewrite Forall_forall in Hrevoked_initial_W3.
            by apply Hrevoked_initial_W3.
          * assert (std (W2std, W2cus, W2seals, W2heap) !! x = Some Permanent) as Hx2.
            { eapply region_state_priv_perm; [exact Hpriv02|exact Hx0]. }
            apply revoke_lookup_Perm in Hx2.
            rewrite -close_list_std_sta_same_alt in Hxf;
              [|intro Hcontra]; cbn; simplify_eq.
            { rewrite Hx2 in Hxf; simplify_eq; apply rtc_refl. }
            rewrite Hx2 in Hcontra; done.
          * destruct ρf; try apply rtc_refl; apply rtc_once; econstructor.
      - destruct Hpriv_W0_W1q as (_ & Hcus01 & _).
        destruct Hrelated_pub_W1q_W2 as (_ & Hcus12 & _).
        eapply related_sts_pub_trans; eauto.
        apply related_sts_pub_refl.
      - destruct Hpriv02 as (_ & _ & Hseals02 & Hheap02).
        split; assumption. }

    set (l'_dropped := filter
      (fun a => ¬(a ∉ l_live ∧ a ∉ finz.seq_between csp_b csp_e)) l').
    assert (l' ≡ₚ l'_fresh ++ l'_dropped) as Hl'_partition.
    { subst l'_fresh l'_dropped. apply filter_complement_list. }
    iAssert (RevokedResources W2 C (l'_fresh ++ l'_dropped))%I
      with "[Hrevoked_l']" as "Hrevoked_parts".
    { rewrite -Hl'_partition. iExact "Hrevoked_l'". }
    iDestruct (RevokedResources_app with "Hrevoked_parts")
      as "[Hrevoked_fresh Hrevoked_dropped]".
    iClear "Hrevoked_dropped".
    iDestruct (wp_rules_interp.world_interp_heap_wf with "Hworld_interp_C")
      as %Hheap_wf3.
    assert (heap_wf (heap_std Wfixed)) as Hheap_wf_fixed.
    { subst Wfixed. rewrite close_list_heap. exact Hheap_wf3. }
    iDestruct (RevokedResources_mono_pub W0 Wfixed C l_live [] Hheap_wf_fixed Hpub0
      with "Hrevoked_live") as "Hrevoked_live_fixed".
    iDestruct (RevokedResources_mono_pub W2 Wfixed C l'_fresh [] Hheap_wf_fixed Hpub2
      with "Hrevoked_fresh") as "Hrevoked_fresh_fixed".
    iAssert (RevokedResources Wfixed C closing_revoked)%I
      with "[Hrevoked_live_fixed Hrevoked_fresh_fixed]" as "Hclosing_resources".
    { subst closing_revoked. rewrite RevokedResources_app. iFrame. }

    (* simplify the knowledge about the new rmap *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero".
    assert (∀ r : RegName, r ∈ dom rmap' → rmap' !! r = Some (WInt 0)) as Hrmap_init'.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: RETURN ----------------- *)
    (* --------------------------------------------------- *)

    iMod (na_inv_acc with "Hmem Hna")
      as "(( %cnt & >Himports_main & >Hcode_main & >Hcgp_main & >%Hcnt) & Hna & Hmem_close)"; auto.

    rewrite /counter_main_code.
    focus_block 4 "Hcode_main" as a_ret Ha_ret "Hcode" "Hcont"; iHide "Hcont" as hcont.

    assert ( rmap' !! cnull = Some (WInt 0) ) as Hwcnull''.
    { apply Hrmap_init'. rewrite Hdom_rmap. clear -Hdom_rmap.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cnull with "Hrmap") as "[Hcnull Hrmap]"; first by simplify_map_eq.
    (* Mov cra cs0. *)
    iInstr "Hcode".
    (* Mov ca0 0%Z. *)
    iInstr "Hcode".
    (* Mov ca1 0%Z. *)
    iInstr "Hcode".
    (* Mov cs0 0%Z. *)
    iInstr "Hcode".
    (* Mov cs1 0%Z. *)
    iInstr "Hcode".
    (* Jalr cnull cra. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Close the memory invariant *)
    iMod ("Hmem_close" with "[$Hna $Himports_main $Hcode_main $Hcgp_main]") as "Hna"; first done.

    (* Put all the registers under the same map *)
    iDestruct (big_sepM_insert _ _ cnull with "[$Hrmap $Hcnull]") as "Hrmap".
    { by simplify_map_eq. }
    rewrite insert_delete_id //.
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap ; set_solver+. }

    clear dependent wcs0 wcs1 wct0 wct1 a_fetch1 a_fetch2 a_callB a_ret.
    iClear "Hmem Hentry_C_f".

    iApply (switcher_ret_specification _ W0 W3
             with
             "[ $Halloc $Hswitcher $Hstk $Hcstk_frag $HK $Hworld_interp_C $Hna $HPC $Hclosing_resources
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ).
    { exact Hpub0. }
    { repeat (rewrite dom_insert_L); rewrite Hdom_rmap;
      clear -Hdom_rmap; set_solver+. }
    { exact Hframe_match. }
    { exact Hcsp_sync. }
    { exact Hclosing_nodup. }
    { exact Htemp0_cover. }
    { iSplit; iApply interp_int. }
  Qed.

  Lemma counter_spec_entry_point

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (C_f : Sealable)

    (W0 : WORLD)

    (csp_content : list Word)

    (Nswitcher Ncounter : namespace)
    :

    let imports := counter_main_imports C_f in

    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_shadow_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    Nswitcher ## Ncounter ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length counter_main_code)%a ->
    (cgp_b + length counter_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    is_heap_cap (WSealed ot_switcher C_f) = false ->
    na_inv cerise_nais Nswitcher switcher_inv
    (* initial memory layout *)
    ∗ na_inv cerise_nais Ncounter
        ( ∃ (cnt : Z),
            [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
            ∗ codefrag pc_a counter_main_code
            ∗ [[ cgp_b, cgp_e ]] ↦ₐ [[ [WInt cnt] ]]
            ∗ ⌜ (0 <= cnt)%Z ⌝
        )
    ∗ interp W0 C (WSealed ot_switcher C_f)
    ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
    ⊢ execute_entry_point
      (WCap true RX Global pc_b pc_e pc_a) (WCap true RW Global cgp_b cgp_e cgp_b) 0 W0 C.
  Proof.
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hcgp_shadow Hcgp_nonheap HNswitcher_counter HsubBounds
               Hcgp_contiguous Himports_contiguous Hsealed_nonheap)
      "(#Hswitcher & #Hmain & #Hinterp_C_f & #HentryC_f)
      % % % % % % #Halloc
      (HK & %Hframe_match & Hregister_state & Hrmap & Hworld_interp_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as "(%Hfullrmap & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_csp & Hinterp_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

    iApply counter_spec; last iFrame "∗#"; eauto.
    { repeat (rewrite dom_delete_L).
      apply regmap_full_dom in Hfullrmap; rewrite Hfullrmap.
      set_solver.
    }
    { intros r Hr.
      repeat (rewrite dom_delete_L in Hr).
      repeat (rewrite lookup_delete_ne; last set_solver).
      set_solver.
    }
    destruct Hsync_csp as [ Hsync_csp <- ]; done.
  Qed.

End Counter.
