From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening.
From cap_machine Require Import logrel logrel_extra rules.
From cap_machine Require Import fetch_spec assert_spec switcher_spec_call deep_immutability.
From cap_machine Require Import proofmode.

Section DROE.
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

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma droe_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports :=
     droe_main_imports b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length droe_main_code)%a ->

    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W_init_C) ->
    (cgp_b ^+1 )%a ∉ dom (std W_init_C) ->

    frame_match Ws Cs cstk W_init_C C ->
    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher switcher_inv
      ∗ na_own logrel_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a droe_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ droe_main_data ]]

      ∗ region W_init_C C ∗ sts_full_world W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W_init_C C (WCap RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_a Hframe_match
            )
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main
      & HWreg_C & HWstd_full_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_C_g
      & #HentryC_g
      & #Hinterp_Winit_C_csp
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
    assert ( is_Some (rmap !! cra) ) as [wcra Hwcra].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

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
    (* Restrict ca0 ro_dro *)
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
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cs0 cra; *)
    iInstr "Hcode".

    (* Jalr cra ct0; *)
    iInstr "Hcode" with "Hlc".

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
           {[ ca0 := WCap RO_DRO Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a;
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

    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W_init_C.1 !! a = Some Temporary⌝)%I as "Hstack_temporary".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_Winit_C_csp"); eauto. }

    iMod (monotone_revoke_stack with "[$Hinterp_Winit_C_csp $HWstd_full_C $HWreg_C]")
        as (l_unk) "(%Hl_unk & HWstd_full_C & HWreg_C & Hstk' & Hrevoked_rest)".
    iAssert (
        |={⊤}=>
          ([∗ list] a ∈ finz.seq_between csp_b csp_e,
             closing_revoked_resources W_init_C C a
             ∗ ⌜(revoke W_init_C).1 !! a = Some Revoked⌝
             ∗ ∃ v, a ↦ₐ v
          )
      )%I with "[Hstk' Hlc]" as ">Hstk'".
    {
      rewrite !big_sepL_sep.
      iDestruct "Hstk'" as "[Hstk' $]".
      iDestruct (big_sepL_later_2 with "Hstk'") as "Hstk'".
      iDestruct (lc_fupd_elim_later with "[$] [$Hstk']") as ">Hstk'".
      iModIntro.
      rewrite -big_sepL_sep.
      iApply (big_sepL_impl with "Hstk'").
      iModIntro; iIntros (k a Hx) "Hrev".
      iDestruct (close_revoked_resources with "Hrev") as (v) "[$ $]".
    }
    iAssert (
        ∃ stk_mem,
         ([∗ list] a ∈ finz.seq_between csp_b csp_e,
          closing_revoked_resources W_init_C C a ∗ ⌜(revoke W_init_C).1 !! a = Some Revoked⌝)
         ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      )%I with "[Hstk']" as (stk_mem) "[Hclose_res Hcsp_stk]".
    { rewrite !big_sepL_sep.
      iDestruct "Hstk'" as "(Hclose & Hrev & Hv)".
      iDestruct (big_sepL_sep with "[$Hclose $Hrev]") as "$".
      by iApply region_addrs_exists.
    }
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_b]") as "%Hcgp_b_stk".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_a]") as "%Hcgp_a_stk".

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W0 := W')
    end.

    iMod (extend_region_perm _ _ _ _ _ RO_DRO (safeC (interp_dro_eq (WInt 42)))
        with "[] [$HWstd_full_C] [$HWreg_C] [$Hcgp_b] []")
      as "(HWreg_C & #Hrel_cgp_b & HWstd_full_C)".
    { done. }
    { subst W0.
      by rewrite -revoke_dom_eq.
    }
    { rewrite /future_priv_mono.
      iIntros "!>" (W W' Hrelared) "[% H]"; cbn.
      iSplitR; [done | by rewrite !fixpoint_interp1_eq].
    }
    { cbn.
      iSplitR; [done | by rewrite !fixpoint_interp1_eq].
    }

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W1 := W')
    end.

    iAssert (interp W1 C (WCap RO_DRO Global cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_cgp_b".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RO_DRO, (interp_dro_eq _).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z) "[-> H]".
        rewrite /interp_dro_eq /=.
        iSplitR; [done | by rewrite !fixpoint_interp1_eq].
      }
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (w') "[-> H]".
        done.
      }
      iSplit; first done.
      subst W0.
      iSplit.
      + rewrite /monoReq; simplify_map_eq.
        iIntros (?) "%Hcontra"; rewrite /canStore in Hcontra.
        destruct (isLocalWord w); done.
      + iPureIntro.
        by rewrite lookup_insert.
    }

    iMod (extend_region_perm _ _ _ _ _ RO_DRO (safeC (interp_dro_eq (WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b)))
        with "[] [$HWstd_full_C] [$HWreg_C] [$Hcgp_a] []")
      as "(HWreg_C & Hrel_cgp_a & HWstd_full_C)".
    { done. }
    { subst W1.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; solve_addr+Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }
    { rewrite /future_priv_mono.
      iIntros "!>" (W W' Hrelared) "[% H]"; cbn.
      iSplitR; [done |].
      iApply monotone.interp_monotone_nl; eauto.
    }
    { cbn. iSplit; done. }

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W2 := W')
    end.

    assert (related_sts_priv_world W_init_C W2) as HWinit_privC_W2.
    { subst W2.
      eapply related_sts_priv_trans_world with (W' := W0) ; eauto; first eapply revoke_related_sts_priv_world.
      eapply related_sts_priv_trans_world with (W' := W1) ; eauto; apply related_sts_priv_world_fresh_Permanent.
    }

    iAssert (interp W2 C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply monotone.interp_monotone_sd; eauto. }

    iAssert (interp W2 C (WCap RO_DRO Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a)) as "#Hinterp_W1_C_a".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RO_DRO, (interp_dro_eq _).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_a".
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z) "[% H]"; done.
      }
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (w') "[-> H]".
        done.
      }
      iSplit; first done.
      subst W1.
      iSplit.
      + rewrite /monoReq; simplify_map_eq.
        iIntros (?) "%Hcontra"; rewrite /canStore in Hcontra.
        destruct (isLocalWord w); done.
      + iPureIntro.
        by rewrite lookup_insert.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W2 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W2 C (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    iEval (cbn) in "Hct1".
    iApply (switcher_cc_specification _ W2 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $HWreg_C $HWstd_full_C $Hcstk_frag
              $Hinterp_W1_C_f $HentryC_g $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }
    iSplitL "Hclose_res".
    { rewrite !big_sepL_sep.
      iDestruct "Hclose_res" as "[Hclose Hrev]".
      iSplitL "Hclose".
      - iApply (big_sepL_impl with "Hclose").
        iModIntro; iIntros (k a Ha) "Hclose".
        rewrite /closing_revoked_resources.
        iDestruct "Hclose" as (???) "(?&?&#Hmono&#Hzcond&#Hrcond&#Hwcond&?)".
        iExists φ,p,Hpers; iFrame "∗#".
        iApply "Hzcond"; done.
      - iApply (big_sepL_impl with "Hrev").
        iModIntro; iIntros (k a Ha) "Hrev".
        iDestruct (big_sepL_pure_1 with "Hstack_temporary") as "%Hstack_temporary".
        subst W2 W1 W0.
        iPureIntro.
        pose proof (elem_of_list_lookup_2 _ _ _ Ha) as Ha'.
        rewrite lookup_insert_ne; last (set_solver+Ha' Hcgp_a_stk).
        rewrite lookup_insert_ne; last (set_solver+Ha' Hcgp_b_stk).
        destruct W_init_C as [WC ?]; cbn.
        apply revoke_lookup_Monotemp.
        eapply Hstack_temporary; eauto.
    }

    iNext. subst rmap'.
    clear stk_mem.
    iIntros (W2_B rmap' stk_mem l)
      "( _ & _
      & %HW1_pubB_W2 & Hrel_stk_B & %Hdom_rmap' & Hclose_reg_B
      & Hna & %Hcsp_bounds
      & HWstd_full_B & HWreg_B
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)" ; clear l.
    iEval (cbn) in "HPC".

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

    (* ---- extract the needed registers ct0 ct1 ct2 ct3 ct4 ----  *)
    assert ( rmap' !! ct0 = Some (WInt 0) ) as Hwct0'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct1 = Some (WInt 0) ) as Hwct1'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct2 = Some (WInt 0) ) as Hwct2'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct3 = Some (WInt 0) ) as Hwct3'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct4 = Some (WInt 0) ) as Hwct4'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct4 with "Hrmap") as "[Hct4 Hrmap]"; first by simplify_map_eq.

    assert ( cgp_b ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_b_stk'.
    { clear -Hcgp_b_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_b_stk.
      destruct Hcgp_b_stk; [left|right]; solve_addr.
    }
    iDestruct (
       region_open_perm with "[$Hrel_cgp_b $HWreg_B $HWstd_full_B]"
      ) as (v) "(HWreg_B & HWstd_full_B & Hstd_cgp_b & Hcgp_b & %Hp & Hmono & Hφ_cgp_b)"; auto.
    {
      eapply (monotone.region_state_priv_perm W2_B); eauto.
      { eapply revoke_related_sts_priv_world. }
      eapply monotone.region_state_pub_perm; eauto.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      subst W2 W1.
      rewrite lookup_insert_ne; last solve_addr+Hcgp_contiguous.
      by rewrite lookup_insert.
    }

    (* Mov cs0 cra; *)
    iInstr "Hcode".
    cbn; iDestruct "Hφ_cgp_b" as "[-> Hinterp_cgp_b']".

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
    (* Mov ca0 0; *)
    iInstr "Hcode".
    (* Mov ca1 0; *)
    iInstr "Hcode".
    (* JmpCap cra *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.

  Qed.

End DROE.
