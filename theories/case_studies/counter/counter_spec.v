From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening.
From cap_machine Require Import logrel logrel_extra rules proofmode.
From cap_machine Require Import fetch switcher_spec_call counter.
From cap_machine Require Import switcher_spec_return.

Section Counter.
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

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Context {C : CmptName}.

  (* TODO move *)
  Lemma revoked_by_separation_with_temp_resources W W' B a :
    a ∈ dom (std W') ->
    (∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
        ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                         ∗ temp_resources W B φ a p  ∗ rel C a p φ)
    ∗ sts_full_world W' B
    ∗ region W' B
    ==∗
    (∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
        ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                         ∗ temp_resources W B φ a p ∗ rel C a p φ)
    ∗ sts_full_world W' B
    ∗ region W' B
    ∗ ⌜ std W' !! a = Some Revoked ⌝.
  Proof.
    iIntros (Hin) "( (%&%&%& (%&%&Hv&Hmono&Hφ) &Hrel) & Hsts & Hr )".
    rewrite elem_of_dom in Hin; destruct Hin as [? Hin].
    iMod (revoked_by_separation with "[$Hsts $Hr $Hv]") as "(Hsts & Hr & Hv & %H')"; eauto.
    simplify_eq.
    iModIntro.
    iFrame "∗%".
  Qed.

  Lemma revoked_by_separation_many_with_temp_resources W W' B la :
    Forall (λ a, a ∈ dom (std W')) la →
    ([∗ list] a ∈ la, (∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
                          ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                                           ∗ temp_resources W B φ a p  ∗ rel C a p φ)
                      ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
    ∗ sts_full_world W' B
    ∗ region W' B
    ==∗
    ([∗ list] a ∈ la, (∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
                          ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                                           ∗ temp_resources W B φ a p  ∗ rel C a p φ)
                      ∗ ⌜(std (revoke W)) !! a = Some Revoked⌝)
    ∗ sts_full_world W' B
    ∗ region W' B
    ∗ ⌜ Forall (λ a, std W' !! a = Some Revoked) la⌝.
  Proof.
    induction la; iIntros (Hin) "(Hl & Hsts & Hr)"; cbn.
    - iModIntro; iFrame. by iPureIntro; apply Forall_nil.
    - iDestruct "Hl" as "[ [Hl %] IHl]".
      apply Forall_cons in Hin as [Hin_a Hin].
      iMod (revoked_by_separation_with_temp_resources with "[$Hl $Hsts $Hr]")
        as "(Hl & Hsts & Hr & %)"; first done.
      iMod (IHla with "[$IHl $Hsts $Hr]") as "(IHl & Hsts & Hr & %)"; first done.
      iModIntro.
      iFrame "∗%".
      by iPureIntro; apply Forall_cons.
  Qed.

  Lemma related_pub_W0_Wfixed (W0 W2 : WORLD  ) (csp_b csp_e : Addr ) (l : list Addr):
    (∀ a : finz MemNum, W0.1 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e)
    → related_sts_priv_world W0 (revoke W0)
    → related_sts_pub_world (std_update_multiple (revoke W0) (finz.seq_between (csp_b ^+ 4)%a csp_e) Temporary) W2
    -> related_sts_pub_world (revoke W0) W2
    → Forall (λ a : finz MemNum, W2.1 !! a = Some Revoked) l
    -> Forall (λ a : finz MemNum, W2.1 !! a = Some Revoked) (finz.seq_between csp_b (csp_b ^+ 4)%a)
    -> finz.seq_between csp_b csp_e = finz.seq_between csp_b (csp_b ^+ 4)%a ++ finz.seq_between (csp_b ^+ 4)%a csp_e
    → related_sts_pub_world W0
        (close_list (l ++ finz.seq_between csp_b csp_e) (revoke W2)).
  Proof.
    intros Htemporaries_W0 Hrelared_priv_W0_W1 Hrelated_pub_1ext_W2 Hrelated_pub_W1_W2 HW2_revoked_l
      Hrevoked_stk_l Hsplit_csp.

    destruct W0 as [W0_std W0_cus], W2 as [W2_std W2_cus]; cbn.
    destruct Hrelated_pub_W1_W2 as [HW1_W2_std HW1_W2_cus].
    split; cbn; cycle 1.
    { eapply related_sts_pub_trans; eauto; eapply related_sts_pub_refl. }
    destruct Hrelated_pub_1ext_W2 as [ [HW1ext_W2_dom HW1ext_W2_t] _].
    cbn in *.
    split.
    {
      intros a Ha.
      rewrite elem_of_dom -close_list_std_sta_is_Some -revoke_std_sta_lookup_Some -elem_of_dom.
      apply HW1ext_W2_dom.
      rewrite elem_of_dom; apply std_sta_update_multiple_is_Some.
      cbn.
      by rewrite -revoke_std_sta_lookup_Some -elem_of_dom.
    }
    intros a ρ0 ρ2 Ha0 Ha2.
    destruct ρ0; cycle 1.
    - (* the initial a was in the Permanent state *)
      assert (a ∉ l ++ finz.seq_between csp_b csp_e) as Ha_notin.
      { destruct (Htemporaries_W0 a) as [_ ?].
        intro Hcontra; apply H in Hcontra. by rewrite Ha0 in Hcontra.
      }
      apply revoke_lookup_Perm in Ha0.
      assert (std (revoke ((W0_std, W0_cus))) !! a = Some Permanent) as Ha0' by done.
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
        destruct Ha2 as [Ha2|Ha2]; first (eapply (HW1ext_W2_t _ _ Revoked) in Ha0'; auto).
        eapply (HW1ext_W2_t _ _ Temporary) in Ha0'; auto.
        inversion Ha0' as [|??? Hcontra]; simplify_eq.
        inversion Hcontra.
    - (* the initial a was in the Revoked state *)
      destruct ρ2; last apply rtc_refl; apply rtc_once; constructor.
    - (* the initial a was in the Temporary state *)
      assert (a ∈ l ++ finz.seq_between csp_b csp_e) as Ha_in.
      { destruct (Htemporaries_W0 a) as [? _]; by apply Htemporaries_W0. }
      apply revoke_lookup_Monotemp in Ha0.
      assert (std (revoke ((W0_std, W0_cus))) !! a = Some Revoked) as Ha0' by done.
      assert (
          std ((std_update_multiple (revoke (W0_std, W0_cus)) (finz.seq_between (csp_b ^+ 4)%a csp_e)
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
      assert (is_Some (W2_std !! a)) as [ρ2' Ha2'].
      { rewrite -elem_of_dom. apply HW1ext_W2_dom. by rewrite elem_of_dom. }
      pose proof (HW1ext_W2_t a _ ρ2' H Ha2') as Hρ2'.
      pose proof Ha_in as Ha_in'.
      rewrite Hsplit_csp app_assoc elem_of_app in Ha_in'.

      destruct (decide (a ∈ finz.seq_between (csp_b ^+ 4)%a csp_e)) as [Ha_in''|Ha_in''].
      { eapply std_rel_pub_rtc_Temporary in Hρ2'; auto; simplify_eq.
        apply revoke_lookup_Monotemp in Ha2'.
        assert (std (revoke ((W2_std, W2_cus))) !! a = Some Revoked) as Ha2'' by done.
        eapply close_list_std_sta_revoked in Ha2''; last apply Ha_in.
        rewrite Ha2 in Ha2''; simplify_eq.
        apply rtc_refl.
      }

      destruct Ha_in' as [Ha_in'|Ha_in']; last set_solver+Ha_in'' Ha_in'.
      assert (ρ2' = Revoked) as ->.
      { rewrite elem_of_app in Ha_in'.
        destruct Ha_in' as [Ha_in'|Ha_in'].
        + rewrite Forall_forall in HW2_revoked_l.
          eapply HW2_revoked_l in Ha_in';eauto.
          by rewrite Ha_in' in Ha2'; simplify_eq.
        + rewrite Forall_forall in Hrevoked_stk_l.
          eapply Hrevoked_stk_l in Ha_in'; eauto.
          by rewrite Ha_in' in Ha2'; simplify_eq.
      }
      eapply revoke_lookup_Revoked in Ha2'.
      assert (std (revoke ((W2_std, W2_cus))) !! a = Some Revoked) as Ha2'' by done.
      eapply close_list_std_sta_revoked in Ha2''; last apply Ha_in.
      rewrite Ha2 in Ha2''; simplify_eq.
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

    let imports := counter_main_imports b_switcher e_switcher a_switcher_call ot_switcher C_f in

    Nswitcher ## Ncounter ->
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp ; cra]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length counter_main_code)%a ->

    (cgp_b + length counter_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->

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

      ∗ region W0 C ∗ sts_full_world W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
      ∗ interp W0 C (WCap RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_counter Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hframe_match Hcsp_sync
            )
      "(#Hswitcher & #Hmem & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Hr_C & Hsts_C
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
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l) "(%Hl_unk & Hsts_C & Hr_C & #Hfrm_close_W0 & >[%stk_mem Hstk] & Hrevoked_l)".
    (* iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_b]") as "%Hcgp_b_stk". *)

    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.


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
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).

    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 0)
                                             then interp W1 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W1 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    (* Show that the entry point to C_f is still safe in W1 *)
    iAssert (interp W1 C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply monotone.interp_monotone_sd; eauto. }
    iClear "Hinterp_W0_C_f".

    (* Prepare the closing resources for the switcher call spec *)
    iAssert (
        ([∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W1 C a ∗
                                                    ⌜W1.1 !! a = Some Revoked⌝)
      )%I with "[Hfrm_close_W0]" as "Hfrm_close_W1".
    {
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a Ha) "[Hclose %Hrev]".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
    }

    iApply (switcher_cc_specification _ _ _ _ _ _ _ _ _ _ _ _ rmap_arg with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W1 $Hcstk_frag
              $Hinterp_W1_C_f $Hentry_C_f $HK]"); eauto; last iFrame.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap . }

    iNext. subst rmap'; clear stk_mem.
    iIntros (W2 rmap' stk_mem_l stk_mem_h)
      "(%Hrelated_pub_1ext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds
      & Hsts_C & Hr_C & Hfrm_close_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk_l & Hstk_h & HK)".
    iEval (cbn) in "HPC".

    (* TODO see whether I can make this a lemma *)
    iEval (rewrite <- (app_nil_r (finz.seq_between (csp_b ^+ 4)%a csp_e))) in "Hr_C".

    iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
    iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".

    iAssert (
       [∗ list] a ; v ∈ finz.seq_between (csp_b ^+ 4)%a csp_e ; stk_mem_h, a ↦ₐ v ∗ closing_resources interp W2 C a v
      )%I with "[Hfrm_close_W2 Hstk_h]" as "Hfrm_close_W2".
    { rewrite /region_pointsto.
      iDestruct (big_sepL2_sep  with "[$Hstk_h $Hfrm_close_W2]") as "$".
    }
    iDestruct (region_close_list_interp_gen with "[$Hr_C $Hfrm_close_W2]"
      ) as "Hr_C"; auto.
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    clear dependent stk_mem_h.
    rewrite -region_open_nil.

    assert (related_sts_pub_world W1 W2) as Hrelated_pub_W1_W2.
    {
      eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros a Ha.
      eapply revoke_lookup_Monotemp.
      destruct Hl_unk as [_ Htemp]; apply Htemp.
      apply elem_of_app; right.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
    }

    iAssert (⌜ Forall (λ a : finz MemNum, a ∈ dom W1.1) l ⌝)%I as "%Hrevoked_l_W".
    {
      iDestruct (big_sepL_sep with "Hrevoked_l") as "[_ %Hrevoked_l]".
      iPureIntro; apply Forall_forall; intros a Ha.
      apply elem_of_list_lookup in Ha as [k Hk].
      apply Hrevoked_l in Hk.
      by rewrite elem_of_dom.
    }
    iMod (
       revoked_by_separation_many_with_temp_resources with "[$Hsts_C $Hr_C $Hrevoked_l]"
      ) as "(Hrevoked_l & Hsts_C & Hr_C & %HW2_revoked_l)".
    { apply Forall_forall; intros a Ha.
      rewrite Forall_forall in Hrevoked_l_W.
      apply Hrevoked_l_W in Ha.
      destruct Hrelated_pub_W1_W2 as [ [Hdom _ ] _].
      by apply Hdom.
    }

    iDestruct (big_sepL_sep with "Hfrm_close_W0") as "[_ %Hrevoked_stk]".
    iMod (
       revoked_by_separation_many with "[$Hsts_C $Hr_C $Hstk_l]"
      ) as "(Hsts_C & Hr_C & Hstk_l & %Hrevoked_stk_l)".
    { apply Forall_forall; intros x Hx.
      destruct Hrelated_pub_W1_W2 as [ [Hdom _ ] _].
      apply Hdom.
      subst W1.
      rewrite elem_of_dom.
      assert (x ∈ finz.seq_between csp_b csp_e) as Hx'.
      { rewrite !elem_of_finz_seq_between in Hx |- *.
        solve_addr+Hcsp_bounds Hx.
      }
      apply elem_of_list_lookup in Hx' as [? Hx'].
      eexists; eapply Hrevoked_stk; eauto.
    }


    (* Revoke the world again to get the points-to of the stack *)
    iMod (monotone_revoke_stack_alt with "[$Hinterp_W2_csp $Hsts_C $Hr_C]")
        as (l') "(%Hl_unk' & Hsts_C & Hr_C & Hfrm_close_W2 & >[%stk_mem Hstk] & Hrevoked_l')".
    iDestruct (region_pointsto_split with "[$Hstk_l $Hstk]") as "Hstk"; auto.
    { solve_addr+Hcsp_bounds. }
    { by rewrite finz_seq_between_length in Hlen_stk_l. }
    set (W3 := revoke W2).

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

    iGo "Hcode".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Close the memory invariant *)
    iMod ("Hmem_close" with "[$Hna $Himports_main $Hcode_main $Hcgp_main]") as "Hna"; first done.

    (* Put all the registers under the same map *)
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap; set_solver+. }

    clear dependent wcs0 wcs1 wct0 wct1 a_fetch1 a_fetch2 a_callB a_ret.
    iClear "Hmem Hentry_C_f".
    subst W3.

    destruct Hl_unk.
    iApply (switcher_ret_specification _ W0 (revoke W2)
             with
             "[ $Hswitcher $Hstk $Hcstk_frag $HK $Hsts_C $Hna $HPC $Hr_C $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ); auto.
    { apply related_pub_W0_Wfixed; eauto.
      apply finz_seq_between_split; solve_addr+Hcsp_bounds.
    }
    { repeat (rewrite dom_insert_L); rewrite Hdom_rmap; set_solver+. }
    { iSplit; iApply interp_int. }

  Qed.

  Lemma counter_spec_entry_point

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rmap : Reg)

    (C_f : Sealable)

    (W0 : WORLD)

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
    ∗ interp W0 C (WSealed ot_switcher C_f)
    ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
    ⊢ execute_entry_point
      (WCap RX Global pc_b pc_e pc_a) (WCap RW Global cgp_b cgp_e cgp_b) rmap
      cstk Ws Cs W0 C.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_counter HsubBounds
               Hcgp_contiguous Himports_contiguous)
      "(#Hswitcher & #Hmain & #Hinterp_C_f & #HentryC_f)
      % % (HK & %Hframe_match & Hregister_state & Hrmap & Hr_C & Hsts_C & %Hsync_csp & Hcstk & Hna)".
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
