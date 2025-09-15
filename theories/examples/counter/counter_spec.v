From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening.
From cap_machine Require Import logrel rules proofmode.
From cap_machine Require Import fetch switcher_spec_call counter.

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

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma counter_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (C_f : Sealable)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (Nswitcher Ncounter : namespace)

    (cstk : CSTK)
    :

    let imports := counter_main_imports b_switcher e_switcher a_switcher_call ot_switcher C_f in

    Nswitcher ## Ncounter ->
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp ; cra]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length counter_main_code)%a ->

    (cgp_b + length counter_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    frame_match Ws Cs cstk W_init_C C ->
    (
      na_inv logrel_nais Nswitcher switcher_inv
      (* initial memory layout *)
      ∗ na_inv logrel_nais Ncounter
          ( ∃ (cnt : Z),
            [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
            ∗ codefrag pc_a counter_main_code
            ∗ [[ cgp_b, cgp_e ]] ↦ₐ [[ [WInt cnt] ]]
            ∗ ⌜ (0 <= cnt)%Z ⌝
          )
      ∗ na_own logrel_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ cra ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      ∗ region W_init_C C ∗ sts_full_world W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
      ∗ interp W_init_C C (WCap RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_counter Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hframe_match
            )
      "(#Hswitcher & #Hmem & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & HWreg_C & HWstd_full_C
      & HK
      & Hcstk_frag
      & #Hinterp_C_f & #Hentry_C_f
      & #Hinterp_Winit_C_csp
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
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W_init_C.1 !! a = Some Temporary⌝)%I as "Hstack_temporary".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_Winit_C_csp"); eauto. }

    iMod (monotone_revoke_stack with "[$Hinterp_Winit_C_csp $HWstd_full_C $HWreg_C]")
        as "(HWstd_full_C & HWreg_C & Hstk)".
    iAssert (
        |={⊤}=>
          ▷ ([∗ list] a ∈ finz.seq_between csp_b csp_e,
             closing_revoked_resources W_init_C C a
             ∗ ⌜(revoke W_init_C).1 !! a = Some Revoked⌝
             ∗ ∃ v, a ↦ₐ v
          )
      )%I with "[Hstk]" as ">Hstk".
    {
      rewrite !big_sepL_sep.
      iDestruct "Hstk" as "[Hstk $]".
      iDestruct (big_sepL_later_2 with "Hstk") as "Hstk".
      iIntros "!>!>".
      rewrite -big_sepL_sep.
      iApply (big_sepL_impl with "Hstk").
      iModIntro; iIntros (k a Hx) "Hrev".
      iDestruct (close_revoked_resources with "Hrev") as (v) "[$ $]".
    }
    iAssert (
        ▷
        (∃ stk_mem,
         ([∗ list] a ∈ finz.seq_between csp_b csp_e,
          closing_revoked_resources W_init_C C a ∗ ⌜(revoke W_init_C).1 !! a = Some Revoked⌝)
         ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]])
      )%I with "[Hstk]" as (stk_mem) "[Hclose_res >Hcsp_stk]".
    { iNext.
      rewrite !big_sepL_sep.
      iDestruct "Hstk" as "(Hclose & Hrev & Hv)".
      iDestruct (big_sepL_sep with "[$Hclose $Hrev]") as "$".
      by iApply region_addrs_exists.
    }
    set (W1 := revoke W_init_C).

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)


    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Load ca0 cgp; *)
    iInstr "Hcode".
    { split; first done. apply withinBounds_true_iff; solve_addr. }

    (* Add ca0 ca0 1%Z; *)
    iInstr "Hcode".

    (* Store cgp ca0; *)
    (* NOTE for some reason, iInstr doesnt work here lol *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg with "[$HPC $Hi $Hcs0 $Hcgp $Hcgp_b]") ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    { done. }
    iIntros "!> (HPC & Hi & Hcs0 & Hcgp & Hcgp_b)".
    iDestruct ("Hcode" with "Hi") as "Hcode".
    wp_pure.

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcs0 $Hcs1 $Hcode $Himport_C_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hcs0 & Hcs1 & Hcode & Himport_C_f)".
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

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

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
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).

    assert (related_sts_priv_world W_init_C W1) as HWinit_privC_W1.
    { subst W1; eapply revoke_related_sts_priv_world. }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 0)
                                             then interp W1 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W1 C (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]); done.
    }

    iAssert (interp W1 C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply monotone.interp_monotone_sd; eauto. }

    iApply (switcher_cc_specification _ W1 _ _ _ _ _ _ _ _ _ _ rmap_arg with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap
              $Hcsp_stk $HWreg_C $HWstd_full_C $Hcstk_frag
              $Hinterp_W1_C_f $Hentry_C_f $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap . }
    iSplitL "Hrmap_arg"; first done.
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
        subst W1.
        iPureIntro.
        apply revoke_lookup_Monotemp.
        eapply Hstack_temporary; eauto.
    }

    iNext. subst rmap'.
    iIntros (W2 rmap')
      "(%HW1_pubB_W2 & %Hdom_rmap'
      & Hna & HWstd_full_B & HWreg_B & Hclose_reg_B
      & Hcstk_frag & Hrel_stk_B
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hcsp_stk & HK)".
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

    iMod (na_inv_acc with "Hmem Hna")
      as "(( %cnt & >Himports_main & >Hcode_main & >Hcgp_main & >%Hcnt) & Hna & Hmem_close)"; auto.

    rewrite /counter_main_code.
    focus_block 4 "Hcode_main" as a_ret Ha_ret "Hcode" "Hcont"; iHide "Hcont" as hcont.

    iGo "Hcode".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Close the memory invariant *)
    iMod ("Hmem_close" with "[$Hna $Himports_main $Hcode_main $Hcgp_main]") as "Hna"; first done.

    (* Put all the registers under the same map *)
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap'; set_solver+. }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap'; set_solver+. }
    iDestruct (big_sepM_insert _ _ ca0 with "[$Hrmap $Hca0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap'; set_solver+. }
    iDestruct (big_sepM_insert _ _ ca1 with "[$Hrmap $Hca1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap'; set_solver+. }

    (* TODO Apply the switcher's return specification *)

  Admitted.

  Lemma counter_spec_entry_point

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rmap : Reg)

    (C_f : Sealable)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (Nswitcher Ncounter : namespace)

    (cstk : CSTK)
    :

    let imports := counter_main_imports b_switcher e_switcher a_switcher_call ot_switcher C_f in

    Nswitcher ## Ncounter ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length counter_main_code)%a ->
    (cgp_b + length counter_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    na_inv logrel_nais Nswitcher switcher_inv
    (* initial memory layout *)
    ∗ na_inv logrel_nais Ncounter
        ( ∃ (cnt : Z),
            [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
            ∗ codefrag pc_a counter_main_code
            ∗ [[ cgp_b, cgp_e ]] ↦ₐ [[ [WInt cnt] ]]
            ∗ ⌜ (0 <= cnt)%Z ⌝
        )
    ∗ interp W_init_C C (WSealed ot_switcher C_f)
    ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
    ⊢ execute_entry_point
      (WCap RX Global pc_b pc_e pc_a) (WCap RW Global cgp_b cgp_e cgp_b) rmap
      cstk Ws Cs W_init_C C.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_counter HsubBounds
               Hcgp_contiguous Himports_contiguous)
      "(#Hswitcher & #Hmain & #Hinterp_C_f & #HentryC_f)
      (HK & %Hframe_match & Hregister_state & Hrmap & HWreg_C & HWstd_full_C & Hcstk & Hna)".
    iDestruct "Hregister_state" as "(%Hfullrmap & %HPC & %Hcgp & %Hcra & Hcsp & Hinterp_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    pose proof (Hfullrmap csp) as [wcsp Hwcsp].
    iDestruct ("Hcsp" $! wcsp Hwcsp) as "[H Hinterp_csp]"; iDestruct "H" as (??) "->".
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.

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
  Qed.
