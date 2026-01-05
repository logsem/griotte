From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import rules logrel logrel_extra monotone proofmode register_tactics.
From cap_machine Require Import fetch_spec assert_spec checkints checkra check_no_overlap_spec.
From cap_machine Require Import
  switcher interp_switcher_call switcher_spec_call switcher_spec_return.
From cap_machine Require Import stack_object.
From cap_machine Require Import proofmode.

Section SO.

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

  (** Steps of the proofs:
      - 1) Revoke the world, obtain [l] the unknown addresses being revoked.
      - 2) Check that the passed stack object [wca0] has read permission,
         and that it does not overlap with our stack frame.
      - 3) Knowing that [wca0] is a safe capability with read permission,
         we know that all addresses must be in the world,
         either Temporary or Permanent.
      - 4) Filter [l] to separate the addresses of [wca0]'s region
         that are Temporary, and the others.
         We know that they are in [l] because if Temporary
         they must either be in [l] or in our stack frame.
         That way, we can get the points-to predicates for
         the Temporary addresses of [wca0].
      - 5) Open the world and get the points-to predicates
         of the Permanent addresses of [wca0].
      - 6) We know have all the points-to predicate of [wca0]'s region,
         we can apply [checkints_spec].
      - 7) We can close the world with the Permanent addresses,
         and we can re-introduce the Temporary ones (via [close_list]).
         They respect their associated validity predicate because [wca0] is interp,
         so their associated predicate must be [zcond],
         and they contain integers.
      - 8) Allocate a new stack object [a_stk1] from our stack frame,
         update the world with its address.
      - 9) Show the arguments to be safe.
         The passed SO is safe because it was safe in the initial world,
         and we re-introduced the Temporary addresses
         (which had been revoked in the initial revocation)
         manually.
         The allocated SO [a_stk1] is safe because we updated the world accordingly.
      - 10) Call the adversary. We obtain a new public future world that is revoked.
          The unknown addresses are [l''].
      - 11) We know that [a_stk1] is in [l'']
          and that the Temporary addresses of `wca0` also are in [l''].
      - 12) We fix the world by closing the world with [l] and [l''],
          but some addresses are redundant.
          It's mostly a game of filtering the addresses.
      - 13) Note that the addresses of [l] are revoked in the initial world,
          but the ones of [l''] are revoked in the final world.
          That's why we need the generalised version of the switcher's return specification.
   *)

  Lemma stack_object_f_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_so_exp_tbl e_so_exp_tbl : Addr)
    (g_so_exp_tbl : Locality)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nso SON : namespace)

    :

    let imports :=
     so_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nso ->
    Nassert ## Nso ->
    (b_so_exp_tbl <= b_so_exp_tbl ^+ 2 < e_so_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length so_main_data)%a = Some cgp_e ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nso
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a so_main_code)
    ∗ inv (export_table_PCCN SON) (b_so_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN SON) ((b_so_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN SON (b_so_exp_tbl ^+ 2)%a)
        ((b_so_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 2 (length (imports ++ SO_main_code_run))))
    ∗ WSealed ot_switcher (SCap RO g_so_exp_tbl b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)
        ↦□ₑ 2
    ∗ seal_pred ot_switcher ot_switcher_propC
      -∗
    ot_switcher_prop W C (WCap RO g_so_exp_tbl b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a).
  Proof.
    intros imports.
    iIntros (Hswitcher_assert HNswitcher_so HNassert_so
               Hso_exp_tbl_size Hso_size_code Hso_imports Hcgp_size)
      "(#Hassert & #Hswitcher
      & #Hso_code
      & #Hso_exp_PCC
      & #Hso_exp_CGP
      & #Hso_exp_awkward
      & #Hentry_SO & #Hot_switcher)".
    iExists g_so_exp_tbl, b_so_exp_tbl, e_so_exp_tbl, (b_so_exp_tbl ^+ 2)%a,
    pc_b, pc_e, cgp_b, cgp_e, 2, _, SON.
    iFrame "#".
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hr_C & Hsts_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

    iMod (na_inv_acc with "Hso_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* --- Extract registers ca0  --- *)
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs0) ) as [wcs0 Hwcs0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs1) ) as [wcs1 Hwcs1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f Himports_main]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }

    iAssert (interp W0 C wca0) as "#Hinterp_wca0_W0".
    { iApply "Hinterp_rmap"; eauto.
      cbn; set_solver+.
    }

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    rewrite /so_main_code /SO_main_code_run.
    rewrite -!app_assoc.
    rewrite /SO_main_code_f.
    assert (SubBounds pc_b pc_e (pc_a ^+ length SO_main_code_run)%a
              (pc_a ^+ length so_main_code)%a).
    { solve_addr. }
    focus_block_nochangePC 3 "Hcode_main" as a_f Ha_f "Hcode" "Hcont"; iHide "Hcont" as hcont.
    replace (pc_b ^+ 23%nat)%a with a_f by solve_addr.

    (* Mov ct1 ca1 *)
    iInstr "Hcode" with "Hlc".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ----------------------------------------------- *)
    (* ------------- BLOCK 4 : CHECKRA --------------- *)
    (* ----------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_checkra Ha_checkra "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_f.
    iApply (checkra_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    iSplitL; last ( iModIntro; iNext ; iIntros (?); done).
    iNext ; iIntros "H"; iDestruct "H" as (p g b e a) "([%Hp ->] & HPC & Hca0 & Hcs0 & Hcs1 & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ------------------------------------------------------ *)
    (* ------------- BLOCK 5:  CHECK_NO_OVERLAP ------------- *)
    (* ------------------------------------------------------ *)
    focus_block 5 "Hcode_main" as a_check_overlap Ha_check_overlap "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_checkra.
    iApply (check_no_overlap_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcsp $Hcode]"); eauto.
    iSplitL; last ( iNext ; iIntros (?); done).
    iNext ; iIntros "(HPC & Hca0 & Hcsp & Hcs1 & Hcs0 & %Hno_overlap & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ------------------------------------------------------- *)
    (* ----------------- BLOCK 6:  CHECKINTS ----------------- *)
    (* ------------------------------------------------------- *)
    focus_block 6 "Hcode_main" as a_checkints Ha_checkints "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_overlap.

    (* Revoke the world to get the stack frame *)
    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l_revoked_W0) "([%Hl_revoked_W0_nodup %Hl_revoked_W0_temporaries]
                 & Hsts_C & Hr_C
                 & #Hfrm_close_W0 & >%Hfrm_close_W0 & >[%stk_mem Hstk]
                 & [Hl_revoked_W0 %Hl_revoked_W0])".

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as
      Hrelated_priv_W0_W1 by eapply revoke_related_sts_priv_world.

    (* Because the passed object has read permission,
       all the addresses must be in the world, either Temporary or Permanent *)
    iAssert ( ⌜ Forall (fun a => std W0 !! a = Some Permanent ∨ std W0 !! a = Some Temporary)
                (finz.seq_between b e) ⌝)%I
    as "%Hstd_state_be_W0".
    { iDestruct (readAllowed_valid_cap with "Hinterp_wca0_W0" ) as "%Hbe_revoked"; auto.
      iPureIntro.
      clear -Hbe_revoked.
      eapply Forall_impl; eauto; cbn.
      intros a Ha.
      destruct Ha as (ρ & Ha & Hρ).
      destruct ρ; [ right | left |]; done.
    }

    (* Filter the addresses that are in Temporary state in [la_be_temporaries]
       and the ones that are in Permanent state in [la_be_permanents] *)
    set (la_be_temporaries := filter (fun a => std W0 !! a = Some Temporary) (finz.seq_between b e)).
    set (la_be_permanents := filter (fun a => std W0 !! a = Some Permanent) (finz.seq_between b e)).
    assert ( (finz.seq_between b e) ≡ₚ la_be_permanents ++ la_be_temporaries ) as Hwca0_range.
    { clear - Hstd_state_be_W0 Hstd_state_be_W0.
      subst la_be_permanents la_be_temporaries.
      generalize (finz.seq_between b e), Hstd_state_be_W0.
      clear Hstd_state_be_W0 b e .
      induction l; intros Hl; cbn; first done.
      apply Forall_cons in Hl as [Ha Hl]
      ; apply IHl in Hl
      ; destruct Ha as [Ha | Ha]
      ; [ assert (W0.1 !! a ≠ Some Temporary) as Ha' by (intro ; simplify_map_eq)
        | assert (W0.1 !! a ≠ Some Permanent) as Ha' by (intro ; simplify_map_eq) ]
      ; rewrite (decide_True _ _ Ha); auto; rewrite (decide_False _ _ Ha'); auto
      ; cbn ; [|rewrite -Permutation_middle] ; rewrite -Hl; done.
    }

    (* Filter out of [l_revoked_W0] the addresses that are [la_be_temporaries]
       and those that are not. *)
    set (l_revoked_W0_no_be := filter (fun a => a ∉ la_be_temporaries) l_revoked_W0).
    assert (
       la_be_temporaries ≡ₚ filter (fun a => a ∈ la_be_temporaries) l_revoked_W0
      ) as Hla_be_temporaries_l.
    {
      clear -Hl_revoked_W0_nodup Hl_revoked_W0_temporaries Hno_overlap.
      assert (la_be_temporaries ⊆ l_revoked_W0).
      {
        intros a Ha.
        subst la_be_temporaries.
        apply elem_of_list_filter in Ha as [Ha Ha_be].
        apply (Hl_revoked_W0_temporaries a) in Ha.
        apply elem_of_app in Ha as [Ha|Ha]; first done.
        rewrite elem_of_disjoint in Hno_overlap.
        exfalso; eapply Hno_overlap; eauto.
      }
      apply NoDup_app in Hl_revoked_W0_nodup as (Hnodup_l & _ & _).
      assert (NoDup la_be_temporaries) as Hnodup_la_be_temporaries.
      { subst la_be_temporaries. apply NoDup_filter, finz_seq_between_NoDup. }
      (* can the proofs below be a lemma instead? *)
      generalize la_be_temporaries, H, Hnodup_la_be_temporaries; intros l' Hl' Hnodup_l'.
      clear -Hl' Hnodup_l Hnodup_l'.
      generalize dependent l'.
      induction l_revoked_W0 as [|a l_revoked_W0]; intros l' Hl' Hnodup_l'.
      + destruct l' ; last set_solver.
        done.
      + cbn.
        apply NoDup_cons in Hnodup_l as [Ha_l Hnodup_l].
        destruct (decide (a ∈ l')) as [Ha_l' | Ha_l'].
        * apply elem_of_Permutation in Ha_l' as [l0 Ha_l'].
          setoid_rewrite Ha_l' in Hnodup_l'.
          apply NoDup_cons in Hnodup_l' as [Ha_l0 Hnodup_l0].
          setoid_rewrite Ha_l' in Hl'.
          setoid_rewrite Ha_l' at 1.
          assert (l0 ⊆ l_revoked_W0).
          { clear -Ha_l Hl' Ha_l0.
            intros x Hx.
            assert (x ≠ a) by (intro; simplify_eq; done).
            apply (elem_of_list_further _ a) in Hx.
            apply Hl' in Hx.
            apply elem_of_cons in Hx as [Hx|Hx]; auto.
            done.
          }
          eapply (IHl_revoked_W0) in H; eauto.
          apply Permutation_cons; first done.
          rewrite H.
          clear -Hnodup_l Ha_l' Ha_l.
          induction l_revoked_W0; cbn; first done.
          apply not_elem_of_cons in Ha_l as [Ha_a0 Ha_l].
          apply NoDup_cons in Hnodup_l as [_ Hnodup_l].
          destruct ( decide (a0 ∈ l0) ) as [Ha0|Ha0].
          ** apply (elem_of_list_further _ a) in Ha0.
             setoid_rewrite <- Ha_l' in Ha0.
             rewrite decide_True; last done.
             rewrite IHl_revoked_W0; auto.
          ** rewrite decide_False; first (rewrite IHl_revoked_W0; auto).
             intros Ha0'.
             setoid_rewrite Ha_l' in Ha0'.
             apply elem_of_cons in Ha0' as [Ha0'|?]; auto.
        * eapply IHl_revoked_W0; auto.
          clear -Hl' Ha_l Ha_l'.
          intros x Hx.
          assert (x ≠ a) by (intro; simplify_eq; done).
          apply Hl' in Hx.
          apply elem_of_cons in Hx as [Hx|Hx]; auto.
          done.
    }
    assert ( l_revoked_W0 ≡ₚ la_be_temporaries ∪ l_revoked_W0_no_be) as Hl_wca0_l'.
    { subst l_revoked_W0_no_be.
      rewrite {1}Hla_be_temporaries_l.
      apply filter_complement_list.
    }
    (* Eliminate the later of [close_list_resources] *)
    iAssert (▷ (close_list_resources C W0 l_revoked_W0 false))%I with "[Hl_revoked_W0]" as "Hl_revoked_W0".
    { rewrite /close_list_resources /close_addr_resources.
      iNext; done.
    }
    iDestruct (lc_fupd_elim_later with "[$] [$Hl_revoked_W0]") as ">Hl_revoked_W0".
    rewrite /close_list_resources.
    iEval (setoid_rewrite Hl_wca0_l') in "Hl_revoked_W0".
    iDestruct (big_sepL_app with "Hl_revoked_W0") as "[Hrevoked_la_be_temporaries Hrevoked_l_revoked_W0_no_be]".

    (* Open the world for the Permanent addresses [la_be_permanents]:
     - get the list of predicates [φs] and [rel] from the validity predicate of [wca0]
     - open the world
     - change the shape of the resources obtained from the open world in a more usable way
     *)
    rewrite region_open_nil.
    iDestruct (read_allowed_inv_full_cap with "Hinterp_wca0_W0") as "Hinterp_wca0_invs"; auto.
    iAssert (
        ∃ (wca0_invs : list (finz MemNum * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type)),
          ⌜ (λ '(a, _, _, _), a) <$> wca0_invs = la_be_permanents ⌝ ∗
          ⌜ Forall (λ '(a, _, _, ρ), std W0 !! a = Some ρ ∧ ρ = Permanent) wca0_invs ⌝ ∗
          ([∗ list] '(a, p, φ, _) ∈ wca0_invs, rel C a p φ) ∗
          ⌜ Forall (λ '(_, _, φ, _), ∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)) wca0_invs⌝
      )%I as "(%wca0_invs & %Hwca0_invs_perma & %Hwca0_invs_std_perma & Hrels_wca0 & %Hpers_wca0_invs)".
    {
      iDestruct "Hinterp_wca0_invs" as "-#Hinterp_wca0_invs".
      iClear "#".
      setoid_rewrite Hwca0_range.
      iDestruct (big_sepL_app with "Hinterp_wca0_invs") as "[H _]".
      iDestruct "H" as "#H".
      assert (Forall (λ a : finz MemNum, W0.1 !! a = Some Permanent) la_be_permanents) as Hla_be_permanents.
      { subst la_be_permanents.
        clear.
        induction (finz.seq_between b e); first done.
        cbn.
        destruct ( decide (W0.1 !! a = Some Permanent) ); last done.
        apply Forall_cons; split ;auto.
      }
      generalize la_be_permanents, Hla_be_permanents.
      clear; intros l Hl.
      iInduction (l) as [|a l] "IH".
      + iExists []; cbn.
        repeat (iSplit; iPureIntro; done).
      + apply Forall_cons in Hl as [Ha Hl].
        cbn.
        iDestruct "H" as "[ (%p'& %P' & %Hpermflow & %HpersP
                              & HrelP & Hzcond & Hrcond & Hwcond & Hmono) H ]".
        iDestruct ("IH" with "[%] [$]") as "(%invs & %Hl_ & %Hperma & #Hrels & %Hpers )"; auto.
        iExists (( (a,p',safeC P'), Permanent)::invs).
        iSplit; first iPureIntro.
        { cbn; by rewrite Hl_. }
        iSplit; first iPureIntro.
        { apply Forall_cons; split; auto. }
        iSplit; first cbn; iFrame "#".
        iPureIntro.
        apply Forall_cons; split; auto.
    }
    iDestruct (region_open_list with "[$Hrels_wca0 $Hr_C $Hsts_C]") as
      "(%wca0_lv_perma & Hr_C & Hsts_C & Hsts_std_wca0 & Hla_be_permanents_lv & Hwca0_mono & Hwca0_φs
     & %Hlength_wca0_lv & Hwca0_pO)".
    { rewrite Hwca0_invs_perma.
      subst la_be_permanents.
      apply NoDup_filter, finz_seq_between_NoDup.
    }
    { rewrite Hwca0_invs_perma; set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [  ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [_ ->]; done.
    }
    { cbn in *.
      rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [  ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [Hx ->].
      by apply revoke_lookup_Perm.
    }
    iAssert ( [∗ list] a;v ∈ la_be_permanents ; wca0_lv_perma, a ↦ₐ v )%I with "[Hla_be_permanents_lv]"
      as "Hla_be_permanents_lv".
    { iClear "#". clear -Hwca0_invs_perma.
      iStopProof.
      rewrite -Hwca0_invs_perma big_sepL2_fmap_l.
      generalize dependent la_be_permanents; intros l Hl.
      generalize dependent wca0_invs.
      generalize dependent wca0_lv_perma.
      induction l; iIntros (lv linvs Hl) "Hl".
      + apply fmap_nil_inv in Hl; simplify_eq; done.
      + apply fmap_cons_inv in Hl; simplify_eq.
        destruct Hl as ( apφρ & l' & Ha & Hl' & Hl); cbn in *.
        destruct apφρ as [ [ [] ] ]; simplify_eq; cbn.
        iDestruct (big_sepL2_length with "Hl") as "%Hlen"
        ; destruct lv ; simplify_eq.
        cbn.
        iDestruct "Hl" as "[$ Hl]".
        iApply IHl; eauto.
    }
    assert (Forall (λ a : finz MemNum, (revoke W0).1 !! a = Some Revoked) la_be_temporaries) as
      Hrevoked_la_be_temporaries.
    { clear - Hl_wca0_l' Hl_revoked_W0.
      setoid_rewrite Hl_wca0_l' in Hl_revoked_W0.
      apply Forall_app in Hl_revoked_W0 as [? ?].
      auto.
    }

    (* Get the list of permissions, predicates and words for the [la_be_temporaries] *)
    iAssert (
        ∃ (lp : list Perm)
          (lφ : list (WORLD * CmptName * Word → iPropI Σ) )
          (lv : list Word),
          ⌜ length lp = length la_be_temporaries ⌝
          ∗ ⌜ length lφ = length la_be_temporaries ⌝
          ∗ ⌜ length lv = length la_be_temporaries ⌝
          ∗ ([∗ list] φ ∈ lφ, ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝)
          ∗ ([∗ list] a;pφ ∈ la_be_temporaries;(zip lp lφ), rel C a pφ.1 pφ.2)
          ∗ ([∗ list] p ∈ lp, ⌜isO p = false⌝)
          ∗ ([∗ list] a;v ∈ la_be_temporaries;lv, a ↦ₐ v)
          ∗ ([∗ list] lpφ;v ∈ (zip lp lφ);lv,
               (if isWL lpφ.1
                then future_pub_mono C lpφ.2 v
                else (if isDL lpφ.1 then future_pub_mono C lpφ.2 v else future_priv_mono C lpφ.2 v))
            )
          ∗ ([∗ list] φ;v ∈ lφ;lv, φ (W0,C,v)))%I
      with "[Hrevoked_la_be_temporaries]"
      as (lp lφ wca0_lv_temps)
           "(%Hlen_lp & %Hlen_lφ & %Hlen_lv & Hlφ_pers & #Hlpφ_rels & HlpO & Hla_be_temporaries_lv & Hlpφ_mono & Hlφ_lv)".
    { iClear "#".
      generalize la_be_temporaries.
      clear; intros l.
      iInduction (l) as [| a l]; first (iExists [],[],[]; cbn; done).
      iDestruct "Hrevoked_la_be_temporaries" as "[Ha Hl]".
      iDestruct ("IHl" with "Hl") as "Hl".
      iDestruct "Ha" as (p P HpersP) "[Ha Hrel_a]".
      iDestruct "Ha" as (v) "(HpO & Hv & Hmono & HP)".
      iDestruct "Hl" as (lp lP lv) "(% & % & % & %Hpers_lP & Hrels & HpOs & Hvs & Hmonos & HPs)".
      iExists (p::lp), (P::lP), (v::lv).
      iFrame.
      iFrame "%".
      iPureIntro.
      cbn; lia.
    }
    iDestruct (big_sepL2_app with "Hla_be_permanents_lv Hla_be_temporaries_lv") as "Hwca0_lvs".

    (* Apply the checkint specification*)
    iApply (checkints_spec with "[- $HPC $Hca0 $Hcs1 $Hcs0 $Hwca0_lvs $Hcode]"); eauto.
    { symmetry; auto. }
    iSplitL; last ( iModIntro; iNext ; iIntros (?); done).
    iNext ; iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hwca0_lvs & %Hwca0_lvs_ints & Hcode & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Close the world from the opened addresses [la_be_permanents] *)
    iDestruct (big_sepL2_app' with "Hwca0_lvs") as "[Hla_be_permanents_lv Hla_be_temporaries_lv]".
    { by rewrite Hlength_wca0_lv Hwca0_invs_perma. }
    iAssert ( [∗ list] '(a0, _, _, _);v ∈ wca0_invs;wca0_lv_perma, a0 ↦ₐ v )%I with "[Hla_be_permanents_lv]"
      as "Hla_be_permanents_lv".
    { iClear "#". clear -Hwca0_invs_perma.
      iStopProof.
      rewrite -Hwca0_invs_perma big_sepL2_fmap_l.
      generalize dependent la_be_permanents; intros l Hl.
      generalize dependent wca0_invs.
      generalize dependent wca0_lv_perma.
      induction l; iIntros (lv linvs Hl) "Hl".
      + apply fmap_nil_inv in Hl; simplify_eq; done.
      + apply fmap_cons_inv in Hl; simplify_eq.
        destruct Hl as ( apφρ & l' & Ha & Hl' & Hl); cbn in *.
        destruct apφρ as [ [ [] ] ]; simplify_eq; cbn.
        iDestruct (big_sepL2_length with "Hl") as "%Hlen"
        ; destruct lv ; simplify_eq.
        cbn.
        iDestruct "Hl" as "[$ Hl]".
        iApply IHl; eauto.
    }
    iDestruct (region_close_list W1 C wca0_invs [] with
             "[$Hr_C $Hsts_std_wca0 $Hla_be_permanents_lv $Hwca0_mono $Hwca0_φs $Hrels_wca0 $Hwca0_pO]"
      ) as "Hr_C".
    { by rewrite Hlength_wca0_lv length_fmap. }
    { rewrite Hwca0_invs_perma. apply NoDup_filter, finz_seq_between_NoDup. }
    { set_solver+. }
    { rewrite !Forall_forall in Hwca0_invs_std_perma |- *.
      intros [ [ [  ] ] ] Hx; cbn in *; simplify_eq.
      apply Hwca0_invs_std_perma in Hx.
      destruct Hx as [_ ->]; done.
    }
    { auto. }
    rewrite -region_open_nil.

    (* Update the world and insert [la_be_temporaries].
       It means that we need to prove that they are safe to share in the revoked world.
       It's fine because they contain only integers.
     *)
    iAssert (▷ [∗ list] φ ∈ lφ, zcond (safeUC φ) C)%I as "#Hzcond_lφ".
    { iClear "∗".
      iDestruct "Hlpφ_rels" as "-#Hrels".
      iDestruct "Hinterp_wca0_invs" as "-#Hinterp".
      iClear "#".
      setoid_rewrite Hwca0_range.
      iDestruct (big_sepL_app with "Hinterp") as "[_ #Hinterp]".
      generalize la_be_temporaries, Hlen_lp, Hlen_lφ.
      clear.
      intros l Hlen_lp Hlen_lφ.
      iInduction (l) as [|a l] "IH" forall (lp lφ Hlen_lp Hlen_lφ).
      all: destruct lφ; simplify_eq.
      all: destruct lp; simplify_eq.
      + done.
      + cbn.
        iDestruct "Hinterp" as "[(%p' & %P' & _ & _ & Hrel' & Hzcond & _) Hinterp]".
        iDestruct "Hrels" as "[Hrel #Hrels]".
        iDestruct (rel_agree  with "[$Hrel $Hrel']") as "[_ #Heq]".
        iSplitL "Heq"; last iApply "IH"; eauto.
        iNext.
        iIntros (???) "!> H"; cbn.
        iDestruct ("Heq" $! (W1, C, WInt z)) as "-#Heq0".
        iDestruct ("Heq" $! (W2, C, WInt z)) as "-#Heq1".
        (* FIXME: for some reason, I cant rewrite Heq0 and Heq1... *)
        iDestruct (internal_eq_iff with "Heq1") as "[_ Heq1]".
        iDestruct (internal_eq_iff with "Heq0") as "[Heq0 _]".
        iApply "Heq1".
        iDestruct ("Heq0" with "H") as "H".
        iApply "Hzcond"; eauto.
    }
    iDestruct "Hlc" as "[Hlc' Hlc]".
    iDestruct (lc_fupd_elim_later with "[$Hlc'] [$Hzcond_lφ]") as ">Hzcond_lφ'".
    iAssert (
        [∗ list] φ;v ∈ lφ;wca0_lv_temps, φ (W1, C, v)
      )%I with "[Hlφ_lv Hzcond_lφ']" as "Hlφ_lv".
    { iClear "#".
      apply Forall_app in Hwca0_lvs_ints as [_ Hl].
      generalize wca0_lv_temps, Hl, Hlen_lv.
      generalize la_be_temporaries, Hlen_lp, Hlen_lφ.
      clear.
      intros la Hlen_lp Hlen_lφ lv Hl_ints Hlen_lv.
      iInduction (la) as [|a la] "IH" forall (lp lφ lv Hlen_lp Hlen_lφ Hlen_lv Hl_ints).
      all: destruct lφ; simplify_eq.
      all: destruct lp; simplify_eq.
      all: destruct lv; simplify_eq.
      + done.
      + cbn.
        iDestruct "Hlφ_lv" as "[Hb Hlb]".
        iDestruct "Hzcond_lφ'" as "[#Hz Hzl]".
        apply Forall_cons in Hl_ints as [ [z ->] Hl_ints].
        iSplitL "Hb Hz"; last (iApply ("IH" with "[] [] [] [] [$] [$]") ; eauto).
        rewrite /zcond.
        iSpecialize ("Hz" $! W0 W1 z).
        cbn.
        iApply "Hz"; auto.
    }
    iDestruct (big_sepL2_disjoint with "[$Hstk $Hla_be_temporaries_lv]") as "%".
    iAssert (
        ([∗ list] a ∈ la_be_temporaries,
           ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ temp_resources W1 C φ a p ∗ rel C a p φ)
      )%I with "[Hlφ_pers HlpO Hlpφ_mono Hla_be_temporaries_lv Hlφ_lv]" as "Hla_be_temporaries_closing_resources".
    { iDestruct "Hlpφ_rels" as "-#Hlpφ_rels".
      iClear "#".
      assert (Forall (λ w : Word, ∃ z : Z, w = WInt z) wca0_lv_temps) as Hlvs_temp_int.
      { clear -Hwca0_lvs_ints.
        by apply Forall_app in Hwca0_lvs_ints as [??].
      }
      clear -Hlen_lp Hlen_lφ Hlen_lv.
      generalize dependent la_be_temporaries; intros l Hlen_lp Hlen_lφ Hlen_lv.
      generalize wca0_lv_temps Hlen_lv; intros lv.
      clear Hlen_lv wca0_lv_temps; intros Hlen_lv.
      iRename "Hla_be_temporaries_lv" into "Hlv".
      iInduction (l) as [|a l] "IH" forall (lφ lp lv Hlen_lp Hlen_lφ Hlen_lv); first done.
      destruct lv as [|v lv]; cbn in Hlen_lv; simplify_eq.
      destruct lφ as [|φ lφ]; cbn in Hlen_lφ; simplify_eq.
      destruct lp as [|p lp]; cbn in Hlen_lp; simplify_eq.
      cbn in *.
      iDestruct "Hlφ_pers" as "[Hlφ_pers_a Hlφ_pers]".
      iDestruct "HlpO" as "[HlpO_a HlpO]".
      iDestruct "Hlpφ_mono" as "[Hlpφ_mono_a Hlpφ_mono]".
      iDestruct "Hlv" as "[Hlv_a Hlv]".
      iDestruct "Hlφ_lv" as "[Hlφ_lv_a Hlφ_lv]".
      iDestruct "Hlpφ_rels" as "[Hlpφ_rels_a Hlpφ_rels]".
      iFrame.
      iApply ("IH" $! lφ lp lv with "[%] [%] [%] [$] [$] [$] [$] [$] [$]"); eauto.
    }
    iMod (monotone_close_list_region W1 W1 C la_be_temporaries with
      "[] [$Hsts_C $Hr_C $Hla_be_temporaries_closing_resources]") as "[Hsts_C Hr_C]".
    { iPureIntro; apply close_list_related_sts_pub. }
    set ( W2 := (close_list la_be_temporaries W1)).

    (* The passed object is safe to share in the world [W2] *)
    iAssert (interp W2 C (WCap p g b e (finz.max b e)))%I as "#Hinterp_wca0_W2".
    {
      iEval (rewrite fixpoint_interp1_eq interp1_eq).
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_wca0_W0".
      destruct (isO p); first done.
      destruct (has_sreg_access p); first done.
      iDestruct "Hinterp_wca0_W0" as "[ Hinterp $ ]".
      iClear "∗".
      iApply (big_sepL_impl with "Hinterp").
      iModIntro.
      iIntros (k x Hx) "(%px & %Px & %Hpx_flow & %Hpers_Px & Hrelx
                             & Hzcondx & Hrcondx & Hwcondx & Hmonox & %Hstatex)".
      iFrame "∗%".
      apply elem_of_list_lookup_2 in Hx.
      rewrite Forall_forall in Hstd_state_be_W0.
      assert (std W0 !! x = std W2 !! x) as Hxeq.
      { destruct (Hstd_state_be_W0 x Hx) as [Hx' | Hx']; rewrite Hx'; symmetry.
        * rewrite close_list_lookup_not_in.
          { cbn.
            by apply revoke_lookup_Perm.
          }
          intro Hcontra.
          apply elem_of_list_filter in Hcontra as [ hcontra _ ].
          by rewrite hcontra in Hx'.
        * apply close_list_lookup_in; auto; last (apply elem_of_list_filter; split; done).
          cbn; apply revoke_lookup_Monotemp; auto.
      }
      iSplitL "Hmonox".
      + rewrite /monoReq.
        by rewrite Hxeq.
      + iPureIntro.
        destruct (isWL p); rewrite !/region_state_nwl !/region_state_pwl in Hstatex |- *
        ; rewrite -Hxeq; done.
    }


    (* ------------------------------------------------------- *)
    (* ------------------ BLOCK 7: ALLOC_SO ------------------ *)
    (* ------------------------------------------------------- *)
    focus_block 7 "Hcode_main" as a_alloc_so Ha_alloc_so "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_checkints.

    (* Store csp so_secret; *)
    destruct ( decide ((csp_b < csp_e)%a) ) as [Hcsp_size|Hcsp_size]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_z with "[$HPC $Hi $Hcsp]"); try solve_pure.
      { rewrite /withinBounds; solve_addr+Hcsp_size. }
      iIntros "!> _".
      wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.
    rewrite finz_dist_S in Hstklen; last solve_addr+Hcsp_size.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    assert (is_Some (csp_b + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hcsp_size|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Hastk0 Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1. }
    iInstr "Hcode".
    { rewrite /withinBounds; solve_addr+Hcsp_size. }
    (* Lea csp 1; *)
    iInstr "Hcode".
    (* Mov ca1 csp; *)
    iInstr "Hcode".
    (* GetA cs0 ca1; *)
    iInstr "Hcode".
    (* Add cs1 cs0 1; *)
    iInstr "Hcode".
    (* Subseg ca1 cs0 cs1; *)
    destruct ( decide ((a_stk1 < csp_e)%a) ) as [Hcsp_size'|Hcsp_size']; cycle 1.
    {
      destruct (z_to_addr (a_stk1 + 1))%a as [a_stk2|] eqn:Hastk2; cycle 1.
      + iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_subseg_fail_src2_nonaddr with "[$HPC $Hi $Hca1 $Hcs0 $Hcs1]"); try solve_pure.
        iIntros "!> _".
        wp_pure; wp_end; iIntros (?); done.
      + iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_subseg_fail_not_iswithin_cap with "[$HPC $Hi $Hca1 $Hcs0 $Hcs1]"); try solve_pure.
        { eauto. }
        {
          assert (csp_e < a_stk2)%a as Hcsp_e_stk2 by solve_addr+Hastk1 Hcsp_size Hcsp_size' Hastk2.
          rewrite /isWithin.
          apply andb_false_iff.
          right.
          solve_addr+Hcsp_e_stk2.
        }
        iIntros "!> _".
        wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen'.
    rewrite finz_seq_between_length in Hstklen'.
    rewrite finz_dist_S in Hstklen'; last solve_addr+Hcsp_size'.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2];[solve_addr+Hcsp_size'|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Hastk1 Hstk]"; eauto.
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    iInstr "Hcode".
    { transitivity (Some (a_stk2)%a); auto.
      solve_addr+Hastk2.
    }
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* Store ca1 0; *)
    iInstr "Hcode".
    { solve_addr+Hcsp_size Hastk1 Hcsp_size' Hastk2. }
    (* Lea csp 1; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 8 : FETCH ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 8 "Hcode_main" as a_fetch Ha_fetch "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_alloc_so.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 9 : CALL ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 9 "Hcode_main" as a_call Ha_call "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_fetch.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov cs1 ct1 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode" with "Hl".


    (* and the hard part should be mostly done at that point *)

    (* -- separate argument registers -- *)
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
           {[ ca0 := WCap p g b e (finz.max b e);
              ca1 := WCap RWL Local a_stk1 a_stk2 a_stk1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).

    assert (related_sts_pub_world W1 W2) as Hrelated_pub_W1_W2.
    { apply close_list_related_sts_pub. }

    assert (related_sts_priv_world W0 W2) as Hrelated_priv_W0_W2.
    { eapply related_sts_priv_pub_trans_world; eauto. }
    assert (related_sts_priv_world W W2) as
      Hrelated_priv_W_W2 by (by eapply related_sts_priv_trans_world; eauto).

    (* Show that the arguments are safe, when necessary *)
    iAssert ( ⌜ wca2 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca3 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca4 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert ( ⌜ wca5 = WInt 0 ⌝ )%I as "->".
    { iApply "Hzeroed_rmap"; eauto.
      set_solver+.
    }
    iAssert (
        |={⊤}=> ([∗ list] a ∈ [a_stk1],
           ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝ ∗ temp_resources W2 C φ a p ∗ rel C a p φ)
      )%I with "[Hastk1 Hlc]" as ">Hastk1_closing_resources".
    { cbn.
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp_W0_csp")
        as "(%pastk1 & %Pastk1 &
      %Hpastk1_rwl & %Hpers_Pastk1 & #Hrel_astk1
      & Hzcond_Pastk1 & Hrcond_Pastk1 & Hwcond_Pastk1 & Hmono_Pastk1
      )";auto.
      { solve_addr+Hastk1 Hcsp_size'. }
      replace (writeAllowed pastk1) with true.
      2:{ symmetry; eapply writeAllowed_flowsto; eauto. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hwcond_Pastk1]") as ">#Hwcond_Pastk1'".
      assert (isWL pastk1 = true) as Hpastk1_wl by (apply isWL_flowsto in Hpastk1_rwl;done).
      iModIntro.
      iSplitL; last done.
      iExists pastk1, (safeC Pastk1).
      iSplit; first iPureIntro.
      { intros Wcv; apply Hpers_Pastk1. }
      iSplit; last iFrame "#".
      iFrame "Hastk1".
      iSplit; first iPureIntro.
      { by apply isWL_nonO. }
      rewrite /monoReq !Hpastk1_wl.
      iSplit.
      + replace (W0.1 !! a_stk1) with (Some Temporary); first iApply "Hmono_Pastk1".
        assert (a_stk1 ∈ finz.seq_between csp_b csp_e) as Hastk1_range.
        { rewrite elem_of_finz_seq_between.
          solve_addr+Hastk1 Hcsp_size' Hcsp_size.
        }
        clear -Hl_revoked_W0_nodup Hl_revoked_W0_temporaries Hastk1_range.
        assert ( a_stk1 ∈ l_revoked_W0 ++ finz.seq_between csp_b csp_e ) as Ha.
        { apply elem_of_app; right; done. }
        by specialize (Hl_revoked_W0_temporaries a_stk1); apply Hl_revoked_W0_temporaries in Ha.
      + (* apply Hwcond_Pastk1, but remove the later... *)
        rewrite /safeC /=.
        iApply "Hwcond_Pastk1'".
        iApply interp_int.
    }

    (* Insert the allocated SO [a_stk1] in the world *)
    iMod (monotone_close_list_region W2 W2 C [a_stk1] with
      "[] [$Hsts_C $Hr_C $Hastk1_closing_resources]") as "[Hsts_C Hr_C]".
    { iPureIntro; apply close_list_related_sts_pub. }
    set (W3 := close_list _ W2).
    assert (related_sts_pub_world W2 W3) as Hrelated_pub_W2_W3.
    { apply close_list_related_sts_pub. }
    assert (related_sts_priv_world W0 W3) as Hrelated_priv_W0_W3.
    { eapply related_sts_priv_pub_trans_world; eauto. }

    assert (W0.1 !! a_stk1 = Some Temporary) as Ha_stk1_W0.
    { apply Hl_revoked_W0_temporaries.
      apply elem_of_app; right.
      apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
    }
    assert (W3.1 !! a_stk1 = Some Temporary) as Ha_stk1_W3.
    {
      apply close_list_lookup_in; last set_solver+.
      rewrite close_list_lookup_not_in.
      * cbn; apply revoke_lookup_Monotemp; done.
      * subst la_be_temporaries.
        intro Ha'.
        rewrite elem_of_disjoint in H0; eapply H0; eauto.
        apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
    }
    (* And show that the allocated SO is safe to share *)
    iAssert (interp W3 C (WCap RWL Local a_stk1 a_stk2 a_stk1))%I
      as "#Hinterp_W2_wca1".
    {
      iEval (rewrite fixpoint_interp1_eq interp1_eq).
      cbn.
      iSplit; last done.
      rewrite (finz_seq_between_singleton a_stk1 a_stk2);last solve_addr+Hastk1 Hastk2 Hcsp_size.
      cbn.
      iSplit; last done.
      iClear "∗".
      iDestruct "Hinterp_W0_csp" as "-#Hinterp"; iClear "#".
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp")
        as "(%px & %Px & %Hpx_flow & %HPx_pers & Hrelx & Hzcondx & Hrcondx & Hwcondx & Hmonox)"; auto
      ; first solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
      iFrame "∗%".
      apply readAllowed_flowsto in Hpx_flow; last done.
      rewrite Hpx_flow; iFrame.
      rewrite /monoReq.
      rewrite Ha_stk1_W0 Ha_stk1_W3; done.
    }
    iDestruct (interp_monotone with "[] Hinterp_wca0_W2") as "Hinterp_wca0_W3"; eauto.

    iAssert (if is_sealed_with_o wca1 ot_switcher
             then (interp W3 C wca1)
             else True)%I as "#Hinterp_W3_wct1".
    { destruct (is_sealed_with_o wca1 ot_switcher) eqn:His_sealed_wct1; last done.
      destruct wca1 as [| [|] | |]; try discriminate.
      iApply (interp_monotone_sd W0 W3); eauto.
      iApply "Hinterp_rmap"; eauto.
      iPureIntro ; set_solver.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg , rarg ↦ᵣ warg ∗ interp W3 C warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W3 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      iAssert (interp W3 C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call)) as
        "Hinterp_sw_call"; first iApply interp_switcher_call; auto.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    rewrite (finz_seq_between_cons csp_b csp_e); last solve_addr+Hcsp_size.
    iEval (cbn) in "Hfrm_close_W0".
    iDestruct "Hfrm_close_W0" as "[Hfrm_close_W0_a_stk1 Hfrm_close_W0]".
    rewrite (finz_seq_between_cons ((csp_b ^+ 1)%a) csp_e)
    ; last solve_addr+Hcsp_size Hcsp_size' Hastk1.
    iEval (cbn) in "Hfrm_close_W0".
    iDestruct "Hfrm_close_W0" as "[Hfrm_close_W0_a_stk2 Hfrm_close_W0]".
    (* Prepare the closing resources for the switcher call spec *)
    assert (
        Forall (λ k : finz MemNum, W3.1 !! k = Some Revoked) (finz.seq_between a_stk2 csp_e)
      ) as HW3_revoked_callee_frm.
    {
      apply Forall_forall; intros x Hx.
      subst W3 W2 W1.
      rewrite close_list_lookup_not_in.
      2: { intros Hx'; apply elem_of_list_singleton in Hx'; simplify_eq.
           apply elem_of_finz_seq_between in Hx.
           solve_addr+Hx Hastk2 Hcsp_size'.
      }
      rewrite close_list_lookup_not_in.
      2: { intro Hx'.
           apply H0 in Hx'; first done.
           apply elem_of_finz_seq_between in Hx.
           apply elem_of_finz_seq_between.
           solve_addr+Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
      }
      apply revoke_lookup_Monotemp.
      clear -Hl_revoked_W0_nodup Hl_revoked_W0_temporaries Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
      specialize (Hl_revoked_W0_temporaries x) ; apply Hl_revoked_W0_temporaries.
      apply elem_of_app; right.
      apply elem_of_finz_seq_between in Hx.
      apply elem_of_finz_seq_between.
      solve_addr+Hx Hastk2 Hcsp_size' Hastk1 Hcsp_size.
    }
    iAssert (
        ([∗ list] a ∈ finz.seq_between a_stk2 csp_e, closing_revoked_resources W3 C a)
      )%I with "[Hfrm_close_W0]" as "Hfrm_close_W3".
    { replace (((csp_b ^+ 1) ^+ 1)%a)
        with a_stk2%a by solve_addr+Hastk2 Hastk1 Hcsp_size'.
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a' Ha') "Hclose".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hso_code_close" with "[$Hna Himport_assert Himport_switcher Himport_C_f Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_C_f $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification_alt with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W3 $Hcstk
              $Hinterp_W3_wct1 $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hrmap_init.
      rewrite /dom_arg_rmap Hrmap_init.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    iClear "Hinterp_rmap Hzeroed_rmap".
    clear dependent wct1 wct0 wcs0 wcs1 rmap stk_mem.
    iNext.
    iIntros (W4 rmap stk_mem l_revoked_W4)
      "( [%Hl_revoked_W4_nodup %Hl_revoked_W4_temporaries] & Hl_revoked_W4 & %Hl_revoked_W4
      & %Hrelated_pub_2ext_W4 & Hrel_stk_C' & %Hdom_rmap & Hfrm_close_W4 & %Hfrm_close_W4
      & Hna & %Hcsp_bounds
      & Hsts_C & Hr_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn) in "HPC".

    assert (related_sts_pub_world W3 W4) as Hrelated_pub_W3_W4.
    {
      eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros x Hx.
      rewrite Forall_forall in HW3_revoked_callee_frm.
      apply HW3_revoked_callee_frm.
      rewrite !elem_of_finz_seq_between in Hx |- *; solve_addr+Hx.
    }
    set (W5 := revoke W4).

    (* Derive a bunch of disjointness properties that will be necessary later *)
    iMod (revoked_by_separation_close_list_resources with "[$Hrevoked_l_revoked_W0_no_be $Hr_C $Hsts_C]")
      as "(Hr_C & Hsts_C & Hrevoked_l_revoked_W0_no_be & %Hrevoked_l_revoked_W0_no_be_W5)".
    { apply Forall_forall.
      intros x Hx.
      subst l_revoked_W0_no_be.
      apply elem_of_list_filter in Hx as [_ Hl].
      rewrite -revoke_dom_eq.
      eapply elem_of_mono_pub; eauto.
      rewrite -!close_list_dom_eq.
      rewrite -revoke_dom_eq.
      assert ( std W0 !! x = Some Temporary).
      { apply Hl_revoked_W0_temporaries; apply elem_of_app ; by left. }
      rewrite elem_of_dom; done.
    }
    iMod (revoked_by_separation_close_list_resources with "[$Hl_revoked_W4 $Hr_C $Hsts_C]")
      as "(Hr_C & Hsts_C & Hl_revoked_W4 & %Hrevoked_l_revoked_W4_W5)".
    { apply Forall_forall.
      intros x Hx.
      rewrite -revoke_dom_eq.
      assert ( std W4 !! x = Some Temporary).
      { apply Hl_revoked_W4_temporaries; apply elem_of_app ; by left. }
      rewrite elem_of_dom; done.
    }
    iMod (revoked_by_separation_many with "[$Hstk $Hr_C $Hsts_C]")
      as "(Hr_C & Hsts_C & Hstk & %Hstk_W5)".
    { eapply Forall_impl; eauto; cbn.
      intros x Hx.
      rewrite elem_of_dom; done.
    }
    iMod (revoked_by_separation with "[$Hastk0 $Hr_C $Hsts_C]")
      as "(Hr_C & Hsts_C & Hastk0 & %Hastk0_W5)".
    {
      rewrite -revoke_dom_eq.
      eapply elem_of_mono_pub; eauto.
      rewrite -!close_list_dom_eq.
      rewrite -revoke_dom_eq.
      assert ( std W0 !! csp_b = Some Temporary).
      { apply Hl_revoked_W0_temporaries; apply elem_of_app ; right.
        apply elem_of_finz_seq_between; done.
      }
      rewrite elem_of_dom; done.
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
    iExtractList "Hrmap" [ct0;ct1] as ["Hct0"; "Hct1"].

    iMod (na_inv_acc with "Hso_code Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hso_code_close)"; auto.
    clear Hpc_contiguous.
    codefrag_facts "Hcode_main" ; rename H into Hpc_contiguous; clear H0.

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    focus_block 10 "Hcode_main" as a_assert_prep Ha_assert_prep "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_call.

    (* Lea csp (-2)%Z *)
    iInstr "Hcode".
    { transitivity (Some csp_b); auto.
      solve_addr+Hastk1 Hastk2 Hcsp_size Hcsp_size'.
    }
    (* Load ct0 csp *)
    iInstr "Hcode".
    { split;auto; solve_addr+Hcsp_size. }
    (* Mov ct1 so_secret *)
    iInstr "Hcode".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 11: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 11 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_assert_prep.
    iExtractList "Hrmap" [ct2;ct3;ct4;cnull] as ["Hct2"; "Hct3";"Hct4";"Hcnull"].
    iApply (assert_success_spec
             with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra $Hcnull
              $Hcode $Himport_assert]") ; auto.
    { apply withinBounds_true_iff; solve_addr. }
    { solve_ndisj. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 12: RETURN ----------------- *)
    (* --------------------------------------------------- *)
    focus_block 12 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_assert_c.
    (* Mov cra cs0; *)
    iInstr "Hcode".
    (* Mov ca0 0%Z; *)
    iInstr "Hcode".
    (* Mov ca1 0%Z; *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hso_code_close" with "[$Hna Himport_switcher Himport_assert Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Put all the registers under the same map *)
    iInsertList "Hrmap" [cnull;ct4;ct3;ct2;ct1;ct0].
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap ; set_solver+. }

    assert (a_stk1 ∈ l_revoked_W4) as Hastk1_l_revoked_W4.
    { assert (a_stk1 ∉ finz.seq_between (a_stk2 ^+ 4)%a csp_e).
      {
        apply not_elem_of_finz_seq_between.
        solve_addr+Hcsp_bounds Hastk1 Hastk2 Hcsp_size' Hcsp_size.
      }
      clear -Hl_revoked_W4_temporaries Hrelated_pub_2ext_W4 H Ha_stk1_W3 H1.
      assert (std W4 !! a_stk1 = Some Temporary) as Htemp.
      { eapply region_state_pub_temp; eauto.
        rewrite std_sta_update_multiple_lookup_same_i; auto.
      }
      apply Hl_revoked_W4_temporaries in Htemp.
      apply elem_of_app in Htemp as [?|?]; done.
    }

    assert (∀ a, a ∈ l_revoked_W0 ++ finz.seq_between csp_b csp_e -> std (revoke W4) !! a = Some Revoked) as
    Ha_5.
    { clear a ; intros a Ha.
      apply elem_of_app in Ha as [Ha|Ha]; cycle 1.
      - rewrite finz_seq_between_cons in Ha; last solve_addr+Hcsp_size' Hastk1.
        replace (csp_b ^+1)%a with a_stk1 in Ha by solve_addr+Hcsp_size' Hastk2 Hastk1 Hcsp_bounds.
        rewrite finz_seq_between_cons in Ha; last solve_addr+Hcsp_size' Hastk1 Hcsp_bounds.
        replace (a_stk1 ^+1)%a with a_stk2 in Ha by solve_addr+Hcsp_size' Hastk2 Hastk1 Hcsp_bounds.
        apply elem_of_cons in Ha as [Ha | Ha]; simplify_eq; first auto.
        apply elem_of_cons in Ha as [Ha | Ha]; simplify_eq.
        { rewrite Forall_forall in Hl_revoked_W4; apply Hl_revoked_W4 in Hastk1_l_revoked_W4; auto. }
        rewrite Forall_forall in Hstk_W5; apply Hstk_W5 in Ha; auto.
      - setoid_rewrite Hl_wca0_l' in Ha.
        apply elem_of_app in Ha as [Ha|Ha]; cycle 1.
        + rewrite Forall_forall in Hrevoked_l_revoked_W0_no_be_W5; apply Hrevoked_l_revoked_W0_no_be_W5 in Ha; auto.
        + apply revoke_lookup_Monotemp.
          eapply region_state_pub_temp; eauto.
          rewrite close_list_lookup_not_in; auto.
          * rewrite close_list_lookup_in; auto.
            rewrite Forall_forall in Hrevoked_la_be_temporaries; apply Hrevoked_la_be_temporaries; auto.
          * intro Ha' ; apply elem_of_list_singleton in Ha'; simplify_eq.
            apply elem_of_list_filter in Ha as [_ Ha].
            rewrite elem_of_disjoint in Hno_overlap; eapply Hno_overlap; eauto.
            apply elem_of_finz_seq_between; subst csp_b; solve_addr+Hastk1 Hcsp_size'.
    }

    (* To fix the world, we need to close the world with the addresses from
       [l_revoked_W0] and [l_revoked_W4], but they have some overlap.
       So we need to separe them into disjoint lists.
     *)
    rewrite -/(close_list_resources C W0 l_revoked_W0_no_be false).
    iDestruct (close_list_resources_separation_many_alt with "[$Hrevoked_l_revoked_W0_no_be $Hl_revoked_W4]") as "%Hdisjoint_l_revoked_W0_no_be_l_revoked_W4".
    assert (∃ l_revoked_W4_no_astk1, l_revoked_W4 ≡ₚ a_stk1::l_revoked_W4_no_astk1 ∧ a_stk1 ∉ l_revoked_W4_no_astk1) as (l_revoked_W4_no_astk1 & Hl_revoked_W4_astk1 & Ha_stk1_l_revoked_W4_no_astk1).
    {
      clear -Hastk1_l_revoked_W4 Hl_revoked_W4_nodup.
      apply elem_of_Permutation in Hastk1_l_revoked_W4.
      destruct Hastk1_l_revoked_W4 as [l_revoked_W4_no_astk1 Hl_revoked_W4_no_astk1].
      exists l_revoked_W4_no_astk1; split; first done.
      setoid_rewrite Hl_revoked_W4_no_astk1 in Hl_revoked_W4_nodup.
      apply NoDup_app in Hl_revoked_W4_nodup; destruct Hl_revoked_W4_nodup as (Hnodup & _ & _).
      apply NoDup_cons in Hnodup; destruct Hnodup as [? _]; done.
    }
    iAssert (
       close_list_resources C W4 l_revoked_W4_no_astk1 false
       ∗ close_addr_resources C W4 a_stk1 false
      )%I with "[Hl_revoked_W4]" as "[Hl_revoked_W4 Ha_stk1]".
    { rewrite /close_list_resources.
      setoid_rewrite Hl_revoked_W4_astk1.
      iDestruct "Hl_revoked_W4" as "[$ $]".
    }
    set (l_revoked_W4_no_astk1_no_wca0 := filter (fun a => a ∉ la_be_temporaries) l_revoked_W4_no_astk1).
    set (l_revoked_W4_no_astk1_wca0 := filter (fun a => a ∈ la_be_temporaries) l_revoked_W4_no_astk1).
    assert (l_revoked_W4_no_astk1 ≡ₚ l_revoked_W4_no_astk1_wca0 ∪ l_revoked_W4_no_astk1_no_wca0) as Hl_revoked_W4_no_astk1_p.
    { clear.
      subst l_revoked_W4_no_astk1_wca0 l_revoked_W4_no_astk1_no_wca0.
      apply filter_complement_list.
    }
    assert ( l_revoked_W0 ≡ₚ l_revoked_W0_no_be ∪ l_revoked_W4_no_astk1_wca0) as Hl_l_revoked_W4_no_astk1_wca0.
    { subst l_revoked_W0_no_be l_revoked_W4_no_astk1_wca0 l_revoked_W4_no_astk1_no_wca0.
      apply NoDup_app in Hl_revoked_W0_nodup as (Hnodup_l&?&?).
      apply NoDup_app in Hl_revoked_W4_nodup as (Hl_revoked_W4_nodup&?&?).
      eapply NoDup_Permutation; eauto.
      { apply NoDup_app.
        split;[|split]; try (apply NoDup_filter); auto; cycle 1.
        + apply (NoDup_cons_1_2 a_stk1).
          setoid_rewrite <- Hl_revoked_W4_astk1; auto.
        + intros x Hx Hx'.
          apply elem_of_list_filter in Hx as [Hx _].
          apply elem_of_list_filter in Hx' as [Hx' _].
          done.
      }
      intros x; split; intros Hx.
      + apply elem_of_app.
        destruct (decide (x ∈ la_be_temporaries)) as [Hx_temp|Hx_temp]; [right|left]; cycle 1.
        * apply elem_of_list_filter; split; auto.
        * apply elem_of_list_filter; split; auto.
          assert (std W4 !! x = Some Temporary) as Hx_W4.
          { eapply region_state_pub_temp; eauto.
            destruct (decide (x ∈ [a_stk1])) as [Hx'|Hx'].
            + rewrite elem_of_list_singleton in Hx'; simplify_eq; done.
            + rewrite close_list_lookup_not_in; eauto.
              apply close_list_lookup_in; eauto.
              rewrite Forall_forall in Hl_revoked_W0; apply Hl_revoked_W0; auto.
          }
          apply elem_of_list_filter in Hx_temp as [Hx_temp_W0 Hx_temp].
          subst la_be_temporaries.
          apply Hl_revoked_W4_temporaries in Hx_W4.
          apply elem_of_app in Hx_W4 as [Hx_W4|Hx_W4].
          { setoid_rewrite Hl_revoked_W4_astk1 in Hx_W4.
            apply elem_of_cons in Hx_W4 as [Hx_W4|Hx_W4]; last done; simplify_eq.
            assert (a_stk1 ∈ finz.seq_between csp_b csp_e)
              by (apply elem_of_finz_seq_between; solve_addr+Hastk1 Hcsp_size').
            exfalso; rewrite elem_of_disjoint in Hno_overlap ; eapply Hno_overlap; eauto.
          }
          { apply elem_of_finz_seq_between in Hx_W4.
            assert (x ∈ finz.seq_between csp_b csp_e)
              by (apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_size' Hx_W4).
            exfalso; rewrite elem_of_disjoint in Hno_overlap ; eapply Hno_overlap; eauto.
          }
      + apply elem_of_app in Hx as [Hx | Hx]
        ; apply elem_of_list_filter in Hx as [Hx Hx']; first done.
        assert (x ∈ finz.seq_between b e)
          as Hx_be by (by apply elem_of_list_filter in Hx as [_ ?]).
        assert ( W0.1 !! x = Some Temporary )
          as Hx_W0 by (by apply elem_of_list_filter in Hx as [? _]).
        apply Hl_revoked_W0_temporaries in Hx_W0.
        apply elem_of_app in Hx_W0 as [Hx_W0|Hx_W0]; auto.
            exfalso; rewrite elem_of_disjoint in Hno_overlap ; eapply Hno_overlap; eauto.
    }

    (* [closing_list_revoked_addresses] is the addresses revoked from [W0] and from [W4],
       but without duplication *)
    set (closing_list_revoked_addresses := l_revoked_W0++l_revoked_W4_no_astk1_no_wca0).
    set (closing_list := (closing_list_revoked_addresses ++ finz.seq_between csp_b csp_e)).
    (* Show that fixing the world [W4] with [closing_list] is public future world... *)
    assert (related_sts_pub_world W4 (close_list closing_list W5)) as Hrelated_pub_W4_Wfixed.
    { subst W5.
      assert ( l_revoked_W4 ++ finz.seq_between (a_stk2 ^+ 4)%a csp_e ⊆ closing_list ).
      { clear a.
        intros a Ha.
        apply elem_of_app in Ha as [Ha|Ha]; cycle 1.
        { apply elem_of_app; right.
          apply elem_of_finz_seq_between in Ha;
          apply elem_of_finz_seq_between.
          solve_addr+Ha Hcsp_bounds Hastk1 Hastk2.
        }
        setoid_rewrite Hl_revoked_W4_astk1 in Ha.
        apply elem_of_cons in Ha as [Ha|Ha]; simplify_eq; cycle 1.
        + apply elem_of_app; left.
          subst closing_list_revoked_addresses.
          setoid_rewrite Hl_l_revoked_W4_no_astk1_wca0.
          rewrite -app_assoc.
          setoid_rewrite <- Hl_revoked_W4_no_astk1_p.
          apply elem_of_app; right.
          done.
        + apply elem_of_app; right.
          rewrite elem_of_finz_seq_between; solve_addr+Hcsp_size' Hastk1.
      }
      destruct W4 as [W4std W4cus]; cbn.
      split; cbn; last apply related_sts_pub_refl.
      split; first (by setoid_rewrite <- close_list_dom_eq; setoid_rewrite <- revoke_dom_eq).
      clear a.
      intros a ρ4 ρ5 Ha_4 Ha_6.
      destruct ρ4.
      - (* Temporary in W4 *)
        assert ( a ∈  l_revoked_W4 ++ finz.seq_between (a_stk2 ^+ 4)%a csp_e ) as Ha_closing.
        { apply Hl_revoked_W4_temporaries; auto. }
        rewrite close_list_std_sta_revoked in Ha_6; auto.
        + simplify_eq; apply rtc_refl.
        + by apply revoke_lookup_Monotemp.
      - (* Permanent in W4 *)
        apply revoke_lookup_Perm in Ha_4.
        rewrite -close_list_std_sta_same_alt in Ha_6; [|intro]; simplify_eq.
        apply rtc_refl.
     - (* Revoked in W4 *)
       destruct ρ5; try apply rtc_refl ; apply rtc_once; econstructor.
    }
    (* ... and use it for showing that we can close the resources of [l_revoked_W4_no_astk1] *)
    iAssert (close_list_resources_gen C W5 closing_list l_revoked_W4_no_astk1 false) with "[Hl_revoked_W4]" as "Hl_revoked_W4".
    { iApply close_list_resources_gen_eq; eauto. }

    (* Show that fixing the world [W0] with [closing_list] is public future world... *)
    assert (related_sts_pub_world W0 (close_list closing_list W5)) as Hrelated_pub_W0_Wfixed.
    { subst W5.
      assert ( l_revoked_W0 ++ finz.seq_between csp_b csp_e ⊆ closing_list ).
      { clear a.
        intros a Ha.
        apply elem_of_app in Ha as [Ha|Ha]; last (by apply elem_of_app; right).
         by do 2 (apply elem_of_app; left).
      }
      destruct W0 as [W0std W0cus]; cbn.
      destruct W4 as [W4std W4cus]; cbn.
      split; cbn; cycle 1.
      { destruct Hrelated_priv_W0_W3 as [_ H_W0_W3].
        destruct Hrelated_pub_W3_W4 as [_ H_W3_W4].
        clear -H_W0_W3 H_W3_W4.
        cbn in *.
        eapply related_sts_pub_trans; eauto.
        apply related_sts_pub_refl.
      }
      split.
      {
        destruct Hrelated_priv_W0_W3 as [ [H_W0_W3 _] _].
        destruct Hrelated_pub_W3_W4 as [ [H_W3_W4 _] _].
        clear -H_W0_W3 H_W3_W4.
        setoid_rewrite <- close_list_dom_eq; setoid_rewrite <- revoke_dom_eq.
        set_solver.
      }
      clear a.
      intros a ρ0 ρ5 Ha_0 Ha_6.
      destruct ρ0.
      - (* Temporary in W0 *)
        assert ( a ∈  l_revoked_W0 ++ finz.seq_between csp_b csp_e ) as Ha_closing.
        { apply Hl_revoked_W0_temporaries; auto. }
        assert (std W1 !! a = Some Revoked)
          as Ha_1 by (by apply revoke_lookup_Monotemp).
        specialize (Ha_5 a Ha_closing).
        apply H in Ha_closing.
        rewrite close_list_std_sta_revoked in Ha_6; auto.
        simplify_eq; apply rtc_refl.
      - (* Permanent in W0 *)
        assert (std W3 !! a = Some Permanent) as Ha_3.
        { eapply region_state_priv_perm; eauto. }
        assert (std (W4std, W4cus) !! a = Some Permanent) as Ha_4.
        { eapply region_state_priv_perm; eauto.
          by apply related_sts_pub_priv_world.
        }
        apply revoke_lookup_Perm in Ha_4.
        rewrite -close_list_std_sta_same_alt in Ha_6; [|intro Hcontra]; cbn; simplify_eq.
        + rewrite Ha_4 in Ha_6; simplify_eq; apply rtc_refl.
        + rewrite Ha_4 in Hcontra; done.
      - (* Revoked in W0 *)
        destruct ρ5; try apply rtc_refl ; apply rtc_once; econstructor.
    }
    (* ... and use it for showing that we can close the resources of [l_revoked_W0_no_be] *)
    iAssert (close_list_resources_gen C W5 closing_list l_revoked_W0_no_be false) with "[Hrevoked_l_revoked_W0_no_be]" as "Hrevoked_l_revoked_W0_no_be".
    { iApply close_list_resources_gen_eq; eauto. }

    (* Derive some separation properties that will be requires later *)
    iAssert (
       close_list_resources_gen C W5 closing_list l_revoked_W4_no_astk1_no_wca0 false
       ∗ close_list_resources_gen C W5 closing_list l_revoked_W4_no_astk1_wca0 false
      )%I with "[Hl_revoked_W4]" as "[Hl_revoked_W4_no_wca0 Hl_revoked_W4_wca0]".
    { rewrite /close_list_resources_gen.
      setoid_rewrite Hl_revoked_W4_no_astk1_p.
      iDestruct (big_sepL_app with "Hl_revoked_W4") as "[$ $]".
    }
    iDestruct (close_list_resources_gen_separation with "[$Hastk0] [$Hl_revoked_W4_no_wca0]") as "%Hcsp_b_notin_l_revoked_W4_no_astk1_no_wca0".
    iDestruct (close_addr_list_gen_resources_separation with "[$Ha_stk1] [$Hl_revoked_W4_no_wca0]") as "%Hastk_1_notin_l_revoked_W4_no_astk1_no_wca0".
    iDestruct (close_list_resources_gen_separation_many
                 with "[$Hstk] [$Hl_revoked_W4_no_wca0]") as "%Hfrm_notin_l_revoked_W4_no_astk1_no_wca0".
    (* Combine all the revoked addresses [closing_list_revoked_addresses] that will
     be used to fix the world *)
    iAssert (close_list_resources_gen C W5 closing_list l_revoked_W0 false)
      with "[Hrevoked_l_revoked_W0_no_be Hl_revoked_W4_wca0]" as "Hrevoked_l_revoked_W0_no_be".
    { rewrite /close_list_resources_gen.
      setoid_rewrite Hl_l_revoked_W4_no_astk1_wca0.
      iApply big_sepL_app; iFrame.
    }
    iAssert (close_list_resources_gen C W5 closing_list closing_list_revoked_addresses false)
      with "[Hrevoked_l_revoked_W0_no_be Hl_revoked_W4_no_wca0]" as "Hrevoked".
    { rewrite /close_list_resources_gen; iApply big_sepL_app; iFrame. }

    (* Reconstruct the stack region *)
    rewrite /close_addr_resources.
    iDestruct "Ha_stk1" as (???) "[Ha_stk1 _]".
    iEval (cbn) in "Ha_stk1".
    iDestruct "Ha_stk1" as (?) "(_ & Ha_stk1 & _)".
    iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; auto.
    { solve_addr+Hcsp_size' Hastk2. }
    iDestruct (region_pointsto_cons with "[$Hastk0 $Hstk]") as "Hstk"; auto.
    { solve_addr+Hcsp_size Hastk1. }

    (* Apply the generalised version of the return to switcher specification *)
    iApply (switcher_ret_specification_gen _ W0 W5
             with
             "[ $Hswitcher $Hstk $Hcstk_frag $HK $Hsts_C $Hna $HPC $Hr_C
             $Hrmap $Hca0 $Hca1 $Hcsp $Hrevoked]"
           ); eauto.
    { repeat (rewrite dom_insert_L); rewrite Hdom_rmap; set_solver+. }
    { subst csp_b.
      clear -Hsync_csp.
      destruct Hsync_csp as [].
      rewrite -H0; auto.
    }
    {
      apply NoDup_app.
      split;[|split]; cycle -1.
      - apply finz_seq_between_NoDup.
      - subst closing_list_revoked_addresses.
        setoid_rewrite Hl_l_revoked_W4_no_astk1_wca0.
        subst l_revoked_W0_no_be.
        rewrite /union /Union_list.
        apply NoDup_app.
        split;[|split]; cycle -1.
        + subst l_revoked_W4_no_astk1_no_wca0.
          apply NoDup_filter.
          clear -Hl_revoked_W4_nodup Hl_revoked_W4_astk1.
          apply NoDup_app in Hl_revoked_W4_nodup as (Hnodup&_&_).
          setoid_rewrite Hl_revoked_W4_astk1 in Hnodup.
          apply NoDup_cons in Hnodup as [_ Hnodup].
          done.
        + apply NoDup_app.
          split;[|split]; cycle -1.
          * subst l_revoked_W4_no_astk1_wca0.
            apply NoDup_filter.
            clear -Hl_revoked_W4_nodup Hl_revoked_W4_astk1.
            apply NoDup_app in Hl_revoked_W4_nodup as (Hnodup&_&_).
            setoid_rewrite Hl_revoked_W4_astk1 in Hnodup.
            apply NoDup_cons in Hnodup as [_ Hnodup].
            done.
          * apply NoDup_filter.
            clear -Hl_revoked_W0_nodup Hl_revoked_W0_temporaries.
            apply NoDup_app in Hl_revoked_W0_nodup as (Hl_revoked_W0_nodup&_&_).
            done.
          * cbn; intros x Hx.
            clear -Hx.
            apply elem_of_list_filter in Hx as [Hx _].
            subst l_revoked_W4_no_astk1_wca0.
            intros Hx'.
            apply elem_of_list_filter in Hx' as [Hx' _].
            done.
        + cbn; intros x Hx.
          intros Hx'.
          subst l_revoked_W4_no_astk1_no_wca0.
          apply elem_of_list_filter in Hx' as [Hx_no_la_be_temporaries Hx'].
          apply elem_of_app in Hx as [Hx|Hx].
          * apply elem_of_list_filter in Hx as [_ Hx].
            apply (elem_of_list_further _ a_stk1) in Hx'.
            setoid_rewrite <- Hl_revoked_W4_astk1 in Hx'.
            setoid_rewrite Hl_wca0_l' in Hx.
            clear -Hx Hx_no_la_be_temporaries Hx' Hdisjoint_l_revoked_W0_no_be_l_revoked_W4.
            rewrite elem_of_disjoint in Hdisjoint_l_revoked_W0_no_be_l_revoked_W4.
            apply elem_of_app in Hx as [Hx|Hx]; first done.
            apply (Hdisjoint_l_revoked_W0_no_be_l_revoked_W4 x); eauto.
          * subst l_revoked_W4_no_astk1_wca0.
            apply elem_of_list_filter in Hx as [Hx _].
            done.
      - cbn; intros x Hx.
        apply elem_of_app in Hx as [Hx|Hx].
        + clear -Hx Hl_revoked_W0_nodup Hl_revoked_W0_temporaries.
          apply NoDup_app in Hl_revoked_W0_nodup as (_&Hl_revoked_W0_nodup&_).
          by apply Hl_revoked_W0_nodup.
        + rewrite finz_seq_between_cons; last solve_addr+Hcsp_bounds Hastk1 Hastk2.
          apply not_elem_of_cons; split.
          { intros ->; done. }
          replace (csp_b ^+ 1)%a with a_stk1; last solve_addr+Hcsp_bounds Hastk1 Hastk2.
          rewrite finz_seq_between_cons; last solve_addr+Hcsp_bounds Hastk1 Hastk2.
          apply not_elem_of_cons; split.
          { intros ->; done. }
          replace (a_stk1 ^+ 1)%a with a_stk2; last solve_addr+Hcsp_bounds Hastk1 Hastk2.
          intro Hx'.
          rewrite elem_of_disjoint in Hfrm_notin_l_revoked_W4_no_astk1_no_wca0.
          eapply Hfrm_notin_l_revoked_W4_no_astk1_no_wca0; eauto.
    }
    { intros x Hx.
      specialize (Hl_revoked_W0_temporaries x); apply Hl_revoked_W0_temporaries in Hx.
      apply elem_of_app in Hx as [Hx | Hx].
      + apply elem_of_app; left.
        apply elem_of_app; left; done.
      + apply elem_of_app; right; done.
    }
    { iSplit; iApply interp_int. }
  Qed.


  Lemma stack_object_f_spec_safe

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_so_exp_tbl e_so_exp_tbl : Addr)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nso SON : namespace)

    :

    let imports :=
     so_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nso ->
    Nassert ## Nso ->
    (b_so_exp_tbl <= b_so_exp_tbl ^+ 2 < e_so_exp_tbl)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length so_main_code)%a ->
    (pc_b + length imports)%a = Some pc_a ->
    (cgp_b + length so_main_data)%a = Some cgp_e ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nso
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a so_main_code)
    ∗ inv (export_table_PCCN SON) (b_so_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN SON) ((b_so_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN SON (b_so_exp_tbl ^+ 2)%a)
        ((b_so_exp_tbl ^+ 2)%a ↦ₐ WInt (encode_entry_point 2 (length (imports ++ SO_main_code_run))))
    ∗ WSealed ot_switcher (SCap RO Global b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)
        ↦□ₑ 2
    ∗ WSealed ot_switcher (SCap RO Local b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)
        ↦□ₑ 2
    ∗ seal_pred ot_switcher ot_switcher_propC
      -∗
    interp W C
      (WSealed ot_switcher (SCap RO Global b_so_exp_tbl e_so_exp_tbl (b_so_exp_tbl ^+ 2)%a)).
  Proof.
    intros imports.
    iIntros (Hswitcher_assert HNswitcher_so HNassert_so
               Hso_exp_tbl_size Hso_size_code Hso_imports Hcgp_size)
      "(#Hassert & #Hswitcher
      & #Hso_code
      & #Hso_exp_PCC
      & #Hso_exp_CGP
      & #Hso_exp_awkward
      & #Hentry_SO & #Hentry_SO' & #Hot_switcher)".
    iEval (rewrite fixpoint_interp1_eq /=).
    rewrite /interp_sb.
    iFrame "Hot_switcher".
    iSplit; [iPureIntro; apply persistent_cond_ot_switcher |].
    iSplit; [iIntros (w); iApply mono_priv_ot_switcher|].
    iSplit; iNext ; iApply stack_object_f_spec; try iFrame "#"; eauto.
  Qed.

End SO.
