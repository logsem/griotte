From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import logrel logrel_extra rules proofmode.
From cap_machine Require Import fetch assert switcher_spec_call deep_locality.

Section DLE.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Context {C : CmptName}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma dle_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports :=
     dle_main_imports b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp ; cra]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code)%a ->

    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W0) ->
    (cgp_b ^+1 )%a ∉ dom (std W0) ->

    frame_match Ws Cs cstk W0 C ->
    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher switcher_inv
      ∗ na_own logrel_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ (∃ wcra, cra ↦ᵣ wcra)
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a dle_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ dle_main_data ]]

      ∗ region W0 C ∗ sts_full_world W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W0 C (WCap RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_a Hframe_match
            )
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & [%wcra Hcra] & Hrmap
      & Himports_main & Hcode_main & Hcgp_main
      & Hr_C & Hsts_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      )".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    (* --- Extract registers ca0 ct0 ct1 ct2 ct3 cs0 cs1 --- *)
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct2) ) as [wct2 Hwct2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct3) ) as [wct3 Hwct3].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs0) ) as [wcs0 Hwcs0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs1) ) as [wcs1 Hwcs1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.

    (* Extract the addresses of b and a *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_a _]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f _]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }


    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l) "(%Hl_unk & Hsts_C & Hr_C & Hfrm_close_W0 & >[%stk_mem Hstk] & Hrevoked_l)".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_b]") as "%Hcgp_b_stk".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_a]") as "%Hcgp_a_stk".

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W1 := W')
    end.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.

    (* Store cgp 42%Z; *)
    iInstr "Hcode".
    { solve_addr. }
    (* Mov ct0 cgp; *)
    iInstr "Hcode".

    (* GetB ct1 cgp; *)
    iInstr "Hcode".
    (* Add ct2 ct1 1%Z; *)
    iInstr "Hcode".
    (* Subseg ct0 ct1 ct2; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

    (* Lea cgp 1%Z; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    (* Store cgp ct0; *)
    (* NOTE for some reason, iInstr doesnt work here lol *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg with "[$HPC $Hi $Hct0 $Hcgp $Hcgp_a]") ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hcgp_a)".
    iDestruct ("Hcode" with "Hi") as "Hcode".
    wp_pure.

    (* Mov ca0 cgp; *)
    iInstr "Hcode".
    (* Lea cgp (-1)%Z; *)
    iInstr "Hcode".
    { transitivity (Some cgp_b); auto; solve_addr. }
    (* Add ct1 ct2 1%Z; *)
    iInstr "Hcode".
    (* Subseg ca0 ct2 ct1; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    (* Restrict ca0 rw_dl *)
    iInstr "Hcode".
    { by rewrite decode_encode_permPair_inv. }
    { solve_pure. }
    { solve_pure. }

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hct1 $Hct2 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hct1 & Hct2 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct2 $Hct3 $Hcode $Himport_C_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 3.1: CALL B ---------------- *)
    (* --------------------------------------------------- *)

    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cs0 ct0; *)
    iInstr "Hcode".
    (* Mov cs1 ct1; *)
    iInstr "Hcode" with "Hlc".

    (* Jalr cra ct0; *)
    iInstr "Hcode" with "Hlc'".

    (* -- Update the world and prove interp of the the argument in `ca0` -- *)

    (* First, extend the world such that `cgp_b` is interp with RW_DL access *)
    iMod (extend_region_temp _ _ _ _ _ RW_DL interpC
        with "[] [$Hsts_C] [$Hr_C] [$Hcgp_b] []")
      as "(Hr_C & #Hrel_cgp_b & Hsts_C)"; auto.
    { by rewrite -revoke_dom_eq. }
    { iApply future_pub_mono_interp_z. }
    { rewrite /interpC /safeC; iApply interp_int. }
    match goal with
    | _ : _ |- context [ region ?W' ] => set (W2 := W')
    end.

    (* And prove that the RW_DL capability pointing to it is safe *)
    iAssert (interp W2 C (WCap RW_DL Local cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_cgp_b".
    { iEval (rewrite fixpoint_interp1_eq); iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RW_DL, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit; first iApply zcond_interp.
      iSplit; first iApply rcond_interp.
      iSplit; first iApply wcond_interp.
      iSplit; first iApply monoReq_interp.
      + by simplify_map_eq.
      + by intro.
      + by iPureIntro; right; simplify_map_eq.
    }

    (* Second, extend the world such that `cgp_b+1` is interp_dl with RW_DL access *)
    iMod (extend_region_temp _ _ _ _ _ RW_DL (safeC interp_dl)
        with "[] [$Hsts_C] [$Hr_C] [$Hcgp_a] []")
      as "(Hr_C & Hrel_cgp_a & Hsts_C)";auto.
    { subst W2.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; solve_addr+Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }
    { iApply future_pub_mono_interp_dl. }
    match goal with
    | _ : _ |- context [ region ?W' ] => set (W3 := W')
    end.

    (* And prove that the RW_DL capability pointing to it is safe *)
    iAssert (interp W3 C (WCap RW_DL Local (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a)) as "#Hinterp_W3_cgp_a".
    { iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RW_DL, interp_dl.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro; apply persistent_cond_interp_dl).
      iSplit; first iFrame "Hrel_cgp_a".
      iSplit; first iApply zcond_interp_dl.
      iSplit; first (iApply rcond_interp_dl; auto).
      iSplit; first iApply wcond_interp_dl.
      iSplit; last (by iPureIntro; right; rewrite lookup_insert).
      rewrite /monoReq; rewrite lookup_insert; cbn.
      iApply mono_pub_interp_dl.
    }

    assert (related_sts_priv_world W0 W3) as Hrelated_priv_W0_W3.
    { eapply related_sts_priv_trans_world with (W' := W1) ; eauto
      ; first eapply revoke_related_sts_priv_world.
      eapply related_sts_pub_priv_trans_world with (W' := W2) ; eauto.
      { eapply related_sts_pub_world_revoked_temporary'.
        by rewrite -revoke_lookup_None -not_elem_of_dom.
      }
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_world_revoked_temporary'.
      rewrite lookup_insert_ne; last solve_addr.
      by rewrite -revoke_lookup_None -not_elem_of_dom.
    }

    (* -- separate argument registers -- *)
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
           {[ ca0 := WCap RW_DL Local (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a;
              ca1 := wca1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    rewrite !(delete_commute _ _ ct2).
    iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    rewrite !(delete_commute _ _ ct3).
    iDestruct (big_sepM_insert _ _ ct3 with "[$Hrmap $Hct3]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).

    set (rmap' := (delete ca5 _)).

    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W3 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W3 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }


    (* Show that the entry point to C_f is still safe in W3 *)
    iAssert (interp W3 C (WSealed ot_switcher C_f)) as "#Hinterp_W3_C_f".
    { iApply interp_monotone_sd; eauto. }
    iClear "Hinterp_W0_C_f".

    (* Prepare the closing resources for the switcher call spec *)
    iAssert (
        ([∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W3 C a ∗
                                                    ⌜W3.1 !! a = Some Revoked⌝)
      )%I with "[Hfrm_close_W0]" as "Hfrm_close_W3".
    {
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a Ha) "[Hclose %Hrev]".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
      iPureIntro.
      pose proof (elem_of_list_lookup_2 _ _ _ Ha) as Ha'.
      rewrite lookup_insert_ne; last (set_solver+Ha' Hcgp_a_stk).
      rewrite lookup_insert_ne; last (set_solver+Ha' Hcgp_b_stk).
      done.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W3 $Hcstk_frag
              $Hinterp_W3_C_f $HentryC_f $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    clear dependent wca1 wca2 wca3 wca4 wca5 rmap.
    iNext.
    iIntros (W4 rmap)
      "(%Hrelated_pub_W3ext_W4 & %Hdom_rmap
      & Hna & #Hinterp_W4_csp & %Hcsp_bounds
      & Hsts_C & Hr_C & Hfrm_close_W3 & Hfrm_close_W4
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn) in "HPC".


    (* TODO see whether I can make this a lemma *)
    iEval (rewrite <- (app_nil_r (finz.seq_between (csp_b ^+ 4)%a csp_e))) in "Hr_C".
    rewrite (region_addrs_zeroes_split _ (csp_b ^+4)%a).
    2: { split; solve_addr+Hcsp_bounds. }
    set (lv := region_addrs_zeroes (csp_b ^+4)%a csp_e).
    iDestruct (region_pointsto_split _ _ (csp_b ^+4)%a with "Hstk") as "[Hstk' Hstk]".
    { split; solve_addr+Hcsp_bounds. }
    { by rewrite length_replicate. }
    iAssert (
       [∗ list] a ; v ∈ finz.seq_between (csp_b ^+ 4)%a csp_e ; lv, a ↦ₐ v ∗ closing_resources interp W4 C a v
      )%I with "[Hfrm_close_W4 Hstk]" as "Hfrm_close_W4".
    { rewrite /region_pointsto.
      iDestruct (big_sepL2_sep_sepL_l  with "[$Hfrm_close_W4 $Hstk]") as "H".
      iApply (big_sepL2_impl with "H").
      iIntros "!> % % % % % [? $]"; iFrame.
      subst lv; apply lookup_replicate in H2 as [-> _]; done.
    }
    iDestruct (
        ftlr_switcher_return.region_close_list_interp_gen
          with "[$Hr_C $Hfrm_close_W4]"
      ) as "Hr_C".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { subst lv; by rewrite length_replicate finz_seq_between_length. }
    rewrite -region_open_nil.

    assert ( cgp_b ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_b_stk'.
    { clear -Hcgp_b_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_b_stk.
      destruct Hcgp_b_stk; [left|right]; solve_addr.
    }
    assert ( (cgp_b ^+1)%a  ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_a_stk'.
    { clear -Hcgp_a_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_a_stk.
      destruct Hcgp_a_stk; [left|right]; solve_addr.
    }
    assert (related_sts_pub_world W3 W4) as Hrelated_pub_W3_W4.
    {
      eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros a Ha.
      rewrite lookup_insert_ne;[|intro Hcontra; subst a; set_solver+Ha Hcgp_a_stk'].
      rewrite lookup_insert_ne;[|intro Hcontra; subst a; set_solver+Ha Hcgp_b_stk'].
      cbn.
      eapply revoke_lookup_Monotemp.
      destruct Hl_unk as [_ Htemp]; apply Htemp.
      apply elem_of_app; right.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
    }

    iMod (revoked_by_separation_many with "[$Hr_C $Hsts_C $Hstk']")
      as "(Hr_C & Hsts_C & Hstk' & %Hstk'_revoked)".
    {
      assert ( cgp_b ∉ finz.seq_between csp_b (csp_b ^+ 4)%a ) as Hcgp_b_stk''.
      { apply not_elem_of_finz_seq_between.
        apply not_elem_of_finz_seq_between in Hcgp_b_stk.
        destruct Hcgp_b_stk; [left|right]; solve_addr.
      }
      assert ( (cgp_b ^+1)%a ∉ finz.seq_between csp_b (csp_b ^+ 4)%a ) as Hcgp_a_stk''.
      { apply not_elem_of_finz_seq_between.
        apply not_elem_of_finz_seq_between in Hcgp_a_stk.
        destruct Hcgp_a_stk; [left|right]; solve_addr.
      }
      apply Forall_forall; intros a Ha.
      eapply elem_of_mono_pub;eauto.
      rewrite elem_of_dom.
      rewrite lookup_insert_ne.
      2:{ intro Hcontra; subst a; set_solver +Ha Hcgp_a_stk''. }
      rewrite lookup_insert_ne.
      2:{ intro Hcontra; subst a; set_solver +Ha Hcgp_b_stk''. }
      rewrite revoke_lookup_Monotemp; first done.
      destruct Hl_unk as [_ H_lunk].
      pose proof (H_lunk a) as [_ Ha']; apply Ha'.
      apply elem_of_app; right.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha Hcsp_bounds.
    }
    rewrite Forall_forall in Hstk'_revoked.

    clear stk_mem.
    iMod (monotone_revoke_stack_alt with "[$Hinterp_W4_csp $Hsts_C $Hr_C]")
        as (l') "(%Hl_unk' & Hsts_C & Hr_C & Hfrm_close_W4 & >[%stk_mem Hstk] & Hrevoked_l')".
    iDestruct (region_pointsto_split with "[$Hstk' $Hstk]") as "Hstk"; auto.
    { by rewrite length_replicate. }
    set (W5 := revoke W4).
    (* TODO up to here *)

    (* TODO lemma again *)
    (* -- extract cgp_b out of the revoked -- *)
    assert (cgp_b ∈ l') as Hcgp_in_l'.
    {
      assert ( W4.1 !! cgp_b = Some Temporary ) as HW4.
      { eapply region_state_pub_temp; eauto.
        rewrite lookup_insert_ne; last solve_addr.
        by rewrite lookup_insert.
      }
      destruct Hl_unk' as [_ Hl_unk'].
      pose proof (Hl_unk' cgp_b) as [Hl_unk'_cgp _].
      apply Hl_unk'_cgp in HW4.
      apply elem_of_app in HW4 as [?|?]; try done.
    }
    iAssert
      ( ∃ l'',
          ⌜ l' ≡ₚ cgp_b::l'' ⌝
          ∗ ([∗ list] a ∈ l'', (∃ (p' : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
                                             ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝ ∗ ▷ temp_resources W4 C φ a p' ∗
                                             rel C a p' φ) ∗ ⌜(revoke W4).1 !! a = Some Revoked⌝)
          ∗ (▷ (∃ v, cgp_b ↦ₐ v)))%I with "[Hrevoked_l']"
      as (l'') "(%Hl_unk'' & Hrevoked_l'' & >[%wcgpb Hcgp_b])".
    { destruct Hl_unk' as [Hnodup ?].
      apply NoDup_app in Hnodup as (Hnodup_l_unk & ? & ?).
      apply elem_of_Permutation in Hcgp_in_l' as [l_unk'' Hl_unk''].
      iExists l_unk''; iFrame "%".
      iEval (setoid_rewrite Hl_unk'') in "Hrevoked_l'".
      iDestruct "Hrevoked_l'" as "[ [Hv _] $]".
      iDestruct "Hv" as (? ? ?) "[Hv _]".
      iNext.
      rewrite /temp_resources.
      iDestruct "Hv" as (??) "[$ _]".
    }

    (* simplify the knowledge about the new rmap *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero".
    assert (∀ r : RegName, r ∈ dom rmap → rmap !! r = Some (WInt 0)) as Hrmap_init.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    assert ( rmap !! ct0 = Some (WInt 0) ) as Hwct0'.
    { apply Hrmap_init. rewrite Hdom_rmap.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct1 = Some (WInt 0) ) as Hwct1'.
    { apply Hrmap_init. rewrite Hdom_rmap.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.


    (* --------------------------------------------------- *)
    (* ------------- BLOCK 3.2: CALL B again -------------- *)
    (* --------------------------------------------------- *)

    (* Store cgp 42%Z; *)
    iInstr "Hcode".
    { solve_addr+Hcgp_contiguous. }
    (* Mov ca0 0%Z; *)
    iInstr "Hcode".
    (* Mov ct0 cs0; *)
    iInstr "Hcode".
    (* Mov ct1 cs1; *)
    iInstr "Hcode".
    (* Jalr cra ct0; *)
    iInstr "Hcode".

    (* -- separate argument registers -- *)
    assert ( is_Some (rmap !! ca2) ) as [wca2 Hwca2].
    { exists (WInt 0); apply Hrmap_init; rewrite Hdom_rmap ; done. }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca3) ) as [wca3 Hwca3].
    { exists (WInt 0); apply Hrmap_init; rewrite Hdom_rmap ; done. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca4) ) as [wca4 Hwca4].
    { exists (WInt 0); apply Hrmap_init; rewrite Hdom_rmap ; done. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca5) ) as [wca5 Hwca5].
    { exists (WInt 0); apply Hrmap_init; rewrite Hdom_rmap ; done. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    set ( rmap_arg :=
           {[ ca0 := WInt 0;
              ca1 := warg1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).
    set (rmap' := (delete ca5 _)).

    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W5 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W5 C (WInt 0)) as "Hinterp_0"; first by iApply interp_int.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    assert (related_sts_priv_world W4 W5) as Hrelated_priv_W4_W5 by apply revoke_related_sts_priv_world.

    (* Show that the entry point to C_f is still safe in W5 *)
    iAssert (interp W5 C (WSealed ot_switcher C_f)) as "#Hinterp_W5_C_f".
    { iApply monotone.interp_monotone_sd; eauto.
      iApply monotone.interp_monotone_sd; eauto.
      iPureIntro; apply related_sts_pub_priv_world; auto.
    }
    iClear "Hinterp_W3_C_f".

    (* Prepare the closing resources for the switcher call spec *)
    iAssert (
        ([∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W5 C a ∗
                                                    ⌜W5.1 !! a = Some Revoked⌝)
      )%I with "[Hfrm_close_W3 Hfrm_close_W4]" as "Hfrm_close_W5".
    { rewrite !big_sepL_sep.
     rewrite (finz_seq_between_split csp_b (csp_b ^+ 4)%a csp_e); last solve_addr.
      iDestruct "Hfrm_close_W3" as "[Hclose_W3 Hrev_W3]".
      iDestruct "Hfrm_close_W4" as "[Hclose_W4 Hrev_W4]".
      iSplitL "Hclose_W3 Hclose_W4".
      - rewrite big_sepL_app.
        iSplitL "Hclose_W3".
        + iApply (big_sepL_impl with "Hclose_W3").
          iModIntro; iIntros (k a Ha) "Hclose'".
          iApply mono_priv_closing_revoked_resources; eauto.
          iApply mono_priv_closing_revoked_resources; eauto.
          by apply related_sts_pub_priv_world.
        + iApply (big_sepL_impl with "Hclose_W4").
          iModIntro; iIntros (k a Ha) "Hclose_".
          iApply mono_priv_closing_revoked_resources; eauto.
      - rewrite big_sepL_app.
        iFrame.
        iApply (big_sepL_impl with "Hrev_W3").
        iModIntro; iIntros (k a Ha) "%Hrev_W3".
        iDestruct (big_sepL_pure_1 with "Hstk_frm_tmp_W0") as "%Hstk_frm_tmp_W0".
        iPureIntro.
        apply revoke_lookup_Revoked.
        eapply Hstk'_revoked.
        apply elem_of_list_lookup.
        eexists; done.
    }

    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W5 $Hcstk_frag
              $Hinterp_W5_C_f $HentryC_f $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hdom_rmap.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    iNext. subst rmap'.
    clear dependent warg0 warg1 rmap.
    iIntros (W6 rmap)
      "(%Hrelated_pub_W5_W6 & %Hdom_rmap
      & Hna & #Hinterp_W6_csp & _
      & Hsts_C & Hr_C & Hfrm_close_W5 & Hfrm_close_W6
      & Hcstk_frag & Hrel_stk_C'
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hcsp_stk & HK)".
    iEval (cbn) in "HPC".

    (* -- simplify our knowledge about rmap -- *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero'".
    assert (∀ r : RegName, r ∈ dom rmap → rmap !! r = Some (WInt 0)) as Hrmap_init.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    assert ( rmap !! ct0 = Some (WInt 0) ) as Hwct0.
    { apply Hrmap_init. rewrite Hdom_rmap.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct1 = Some (WInt 0) ) as Hwct1.
    { apply Hrmap_init. rewrite Hdom_rmap.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct2 = Some (WInt 0) ) as Hwct2.
    { apply Hrmap_init. rewrite Hdom_rmap.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct3 = Some (WInt 0) ) as Hwct3.
    { apply Hrmap_init. rewrite Hdom_rmap.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct4 = Some (WInt 0) ) as Hwct4.
    { apply Hrmap_init. rewrite Hdom_rmap.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct4 with "Hrmap") as "[Hct4 Hrmap]"; first by simplify_map_eq.

    (* Load ct0 cgp  *)
    iInstr "Hcode".
    { split; [done| solve_addr]. }
    (* Mov ct1 42  *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ------------------ BLOCK 5: HALT ------------------ *)
    (* --------------------------------------------------- *)
    focus_block 5 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* JmpCap cra *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.
  Qed.

End DLE.
