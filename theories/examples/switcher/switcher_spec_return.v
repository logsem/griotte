From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine.ftlr Require Import ftlr_base interp_weakening ftlr_switcher_return.
From cap_machine Require Import logrel fundamental interp_weakening addr_reg_sample rules proofmode monotone.
From cap_machine Require Import multiple_updates region_invariants_revocation region_invariants_allocation.
From cap_machine Require Import switcher switcher_preamble.
From stdpp Require Import base.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.
From cap_machine Require Export logrel_extra.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma switcher_ret_specification
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : Reg)
    (csp_e csp_b cgp_e: Addr)
    (l : list Addr)
    (stk_mem : list Word)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : Word)
    :
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->
    NoDup (l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, W0.1 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e) ->

    (* Switcher Invariant *)
    na_inv logrel_nais Nswitcher switcher_inv
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ sts_full_world (revoke Wcur) C
    ∗ na_own logrel_nais ⊤
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ region (revoke Wcur) C
    ∗ ([∗ list] a ∈ l,
          (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ),
              ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝
              ∗ temp_resources W0 C P a p
              ∗ rel C a p P)
          ∗ ⌜(std (revoke W0)) !! a = Some Revoked⌝)
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    iIntros (Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & Hstk & Hcstk & HK & Hsts & Hna
    & HPC & Hr & Hrevoked & Hrmap & Hca0 & Hca1 & Hcsp)".

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".

    set (Hret := switcher_return_entry_point).
    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    rewrite {2}/switcher_instrs.
    assert (SubBounds b_switcher e_switcher a_switcher_return (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.

    codefrag_facts "Hcode".
    rewrite /switcher_instrs /switcher_call_instrs /switcher_return_instrs.
    rewrite -!app_assoc.
    focus_block_nochangePC 6 "Hcode" as a_ret Ha_ret "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.
    replace a_switcher_return with a_ret by solve_addr.

    assert (is_Some (rmap !! cra)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cra as "Hcra".
    assert (is_Some (rmap !! cgp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cgp as "Hcgp".
    assert (is_Some (rmap !! ctp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ctp as "Hctp".
    assert (is_Some (rmap !! ca2)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ca2 as "Hca2".
    assert (is_Some (rmap !! cs1)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cs1 as "Hcs1".
    assert (is_Some (rmap !! cs0)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cs0 as "Hcs0".
    assert (is_Some (rmap !! ct0)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ct0 as "Hct0".
    assert (is_Some (rmap !! ct1)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ct1 as "Hct1".

    (* --- ReadSR ctp mtdc --- *)
    iInstr "Hcode"; try solve_pure.

    (* --- Load csp ctp --- *)
    destruct (decide (a_tstk < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Load.wp_load_fail_not_withinbounds with "[HPC Hi Hctp Hcsp]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds.
        apply andb_false_iff; right.
        solve_addr+Htstk_ae.
      }
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }

    iDestruct (cstack_agree with "Hcstk_full [$]") as %Heq; subst cstk'.

    destruct cstk as [|frm cstk]; iEval (cbn) in "Hstk_interp"; cbn in Hlen_cstk.
    { (* no caller, return subroutine fails *)
      replace a_tstk with (b_trusted_stack)%a by solve_addr.
      iInstr "Hcode".
      { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
      (* Lea ctp (-1)%Z *)
      destruct (decide (b_trusted_stack <= (b_trusted_stack ^+ -1))%a) as [Hb_trusted_stack1'|Hb_trusted_stack1'].
      {
        assert ((b_trusted_stack + -1) = None)%a by solve_addr+Hb_trusted_stack1'.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (rules_Lea.wp_Lea_fail_none_z with "[HPC Hi Hctp]")
        ; try iFrame
        ; try solve_pure.
        iNext; iIntros "_".
        wp_pure; wp_end ; by iIntros (?).
      }
      assert (is_Some (b_trusted_stack + -1))%a as [b_trusted_stack1 Hb_trusted_stack1] by solve_addr+Hb_trusted_stack1'.
      clear Hb_trusted_stack1'.
      iInstr "Hcode".
      (* WriteSR mtdc ctp *)
      iInstr "Hcode".
      (* Lea csp (-1)%Z *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Lea.wp_Lea_fail_integer with "[HPC Hi Hcsp]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }

    destruct Ws,Cs;try done. simpl in Hframe.
    destruct Hframe as [<- [<- Hframe] ].

    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as (wtstk4) "[Ha_tstk Hcframe_interp]".
    destruct wstk; try done.
    destruct sb; try done.
    destruct p; try done.
    destruct rx; try done.
    destruct w; try done.
    destruct dl; try done.
    destruct dro; try done.
    destruct g; try done.
    rename a into a_stk; rename b into b_stk; rename e into e_stk.
    iDestruct "Hcframe_interp" as "(%HWF & -> & Hcframe_interp)".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    cbn in Hcsp_sync; destruct Hcsp_sync as [ Ha He ]; simplify_eq.
    set (a_stk := (csp_b ^+ -4)%a).

    iDestruct "HK" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".

    rewrite -/(interp_cont).

    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }

    (* --- Lea ctp -1 --- *)
    destruct (decide (a_tstk <= (a_tstk ^+ -1))%a) as [Ha_tstk1'|Ha_tstk1'].
    {
      assert ((a_tstk + -1) = None)%a by solve_addr+Ha_tstk1'.
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Lea.wp_Lea_fail_none_z with "[HPC Hi Hctp]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }
    assert (is_Some (a_tstk + -1))%a as [a_tstk1 Ha_tstk1] by solve_addr+Ha_tstk1'.
    iInstr "Hcode".
    replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.

    (* --- WriteSR mtdc ctp --- *)
    iInstr "Hcode".

    (* --- Lea csp -1 --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 3)%a); subst a_stk; solve_addr+Ha_stk4. }

    set (stk_len := finz.dist (a_stk ^+ 4)%a csp_e).
    set (stk_ws := repeat (WInt 0) stk_len).
    simpl.

    (* NOTE in the case of untrusted code calling,
       it means that the addresses (astk, astk+4) are stored in the world,
       but remember that we revoked the world,
       so the callee needs to pass the revoked addresses!
     *)
    iAssert (
        ∃ wastk wastk1 wastk2 wastk3,
          (* let la := (if is_untrusted_caller then True else (finz.seq_between (csp_b ^+ 4)%a csp_e)) in *)
          (* let lv := (if is_untrusted_caller then [wastk;wastk1;wastk2;wastk3] ++ stk_ws *)
          (*            else stk_ws) in *)
          a_stk ↦ₐ wastk
          ∗ (a_stk ^+ 1)%a ↦ₐ wastk1
          ∗ (a_stk ^+ 2)%a ↦ₐ wastk2
          ∗ (a_stk ^+ 3)%a ↦ₐ wastk3
          (* ∗ ▷ ([∗ list] a ; v ∈ la ; lv, ▷ closing_resources interp W C a v) *)
          ∗ (⌜if is_untrusted_caller then True else (wastk = wcs0 ∧ wastk1 = wcs1 ∧ wastk2 = wret ∧ wastk3 = wcgp)⌝)
          ∗ ( if is_untrusted_caller
              then
                ( ∃ l',
                    ⌜ l ≡ₚ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a]++l' ⌝
                    ∗ ([∗ list] a ∈ l', (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ),
                                       ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝ ∗
                                                                        temp_resources W0 C P a p ∗ rel C a p P) ∗
                                   ⌜(revoke W0).1 !! a = Some Revoked⌝)
                    (* ∗ ([∗ list] a ∈ l', (∃ (p' : Perm) (φ : WORLD * CmptName * Word → iPropI Σ), *)
                    (*                          ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝ ∗ ▷ temp_resources W4 C φ a p' ∗ *)
                    (*                                                           rel C a p' φ) ∗ ⌜(revoke W4).1 !! a = Some Revoked⌝) *)
                )
              else
                ([∗ list] a ∈ l, (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ),
                                     ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝ ∗
                                                                      temp_resources W0 C P a p ∗ rel C a p P) ∗
                                 ⌜(revoke W0).1 !! a = Some Revoked⌝
                )
            )
      )%I
      with "[Hcframe_interp Hrevoked]" as "Hcframe_interp"
    ; [|iDestruct "Hcframe_interp" as
        (wastk wastk1 wastk2 wastk3
        ) "(Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & %Hwastks & Hrevoked)"
      ].
    { admit. }
    (* { *)
    (*   destruct is_untrusted_caller; cycle 1. *)
    (*   * iExists wcs0, wcs1, wret, wcgp. *)
    (*     iDestruct "Hcframe_interp" as "($&$&$&$)". iFrame. *)
    (*     done. *)
    (*   * cbn. *)
    (*     iAssert *)
    (*       (⌜ ∀ (a : Addr), a ∈ (finz.seq_between b_stk csp_e) → (std W0 !! a) = Some Temporary ⌝)%I *)
    (*       as "%Hstk_tmp". *)
    (*     { *)
    (*       iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_callee_wstk") as "%Hstk_tmp" ; auto. *)
    (*       iPureIntro ; intros a Ha. *)
    (*       apply elem_of_list_lookup_1 in Ha as [k Ha]. *)
    (*       by eapply Hstk_tmp. *)
    (*     } *)

    (*     iAssert ( ⌜ a_stk ∈ l ⌝)%I as "%Hastk_unk". *)
    (*     { *)
    (*       opose proof (Hstk_tmp a_stk _) as Hastk_tmp. *)
    (*       { rewrite elem_of_finz_seq_between; subst a_stk; solve_addr+Hb_a4 He_a1 Ha_stk4. } *)
    (*       apply Htemp_revoked in Hastk_tmp. *)
    (*       apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done. *)
    (*       rewrite elem_of_finz_seq_between in Hcontra. *)
    (*       subst a_stk. *)
    (*       solve_addr+Hcontra. *)
    (*     } *)
    (*     iAssert ( ⌜ (a_stk ^+1)%a ∈ l ⌝)%I as "%Hastk1_unk". *)
    (*     { *)
    (*       opose proof (Hstk_tmp (a_stk ^+1)%a _) as Hastk_tmp. *)
    (*       { rewrite elem_of_finz_seq_between; subst a_stk; solve_addr+Hb_a4 He_a1 Ha_stk4. } *)
    (*       apply Htemp_revoked in Hastk_tmp. *)
    (*       apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done. *)
    (*       rewrite elem_of_finz_seq_between in Hcontra. *)
    (*       subst a_stk. *)
    (*       solve_addr+Hcontra. *)
    (*     } *)
    (*     iAssert ( ⌜ (a_stk ^+2)%a ∈ l ⌝)%I as "%Hastk2_unk". *)
    (*     { *)
    (*       opose proof (Hstk_tmp (a_stk ^+2)%a _) as Hastk_tmp. *)
    (*       { rewrite elem_of_finz_seq_between; subst a_stk; solve_addr+Hb_a4 He_a1 Ha_stk4. } *)
    (*       apply Htemp_revoked in Hastk_tmp. *)
    (*       apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done. *)
    (*       rewrite elem_of_finz_seq_between in Hcontra. *)
    (*       subst a_stk. *)
    (*       solve_addr+Hcontra. *)
    (*     } *)
    (*     iAssert ( ⌜ (a_stk ^+3)%a ∈ l ⌝)%I as "%Hastk3_unk". *)
    (*     { *)
    (*       opose proof (Hstk_tmp (a_stk ^+3)%a _) as Hastk_tmp. *)
    (*       { rewrite elem_of_finz_seq_between; subst a_stk; solve_addr+Hb_a4 He_a1 Ha_stk4. } *)
    (*       apply Htemp_revoked in Hastk_tmp. *)
    (*       apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done. *)
    (*       rewrite elem_of_finz_seq_between in Hcontra. *)
    (*       subst a_stk. *)
    (*       solve_addr+Hcontra. *)
    (*     } *)
    (*     iAssert *)
    (*       ( ∃ l', *)
    (*           ⌜ l ≡ₚ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a]++l' ⌝ *)
    (*           ∗ ([∗ list] a ∈ l', (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ), *)
    (*                                   ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝ ∗ *)
    (*                                                                    temp_resources W0 C P a p ∗ rel C a p P) ∗ *)
    (*                               ⌜(revoke W0).1 !! a = Some Revoked⌝) *)
    (*           ∗ (∃ wastk wastk1 wastk2 wastk3, *)
    (*                 a_stk ↦ₐ wastk *)
    (*                 ∗ (a_stk ^+ 1)%a ↦ₐ wastk1 *)
    (*                 ∗ (a_stk ^+ 2)%a ↦ₐ wastk2 *)
    (*                 ∗ (a_stk ^+ 3)%a ↦ₐ wastk3 *)
    (*             ) *)
    (*       )%I with "[Hrevoked]" *)
    (*       as (l') "(%Hl_unk'' & Hrevoked_l'' & H)". *)
    (* { apply NoDup_app in Hnodup_revoked as (Hnodup_revoked & ? & ?). *)
    (*   apply elem_of_Permutation in Hastk_unk as [l0 Hl0]. *)
    (*   rewrite Hl0 in Hastk1_unk,Hastk2_unk,Hastk3_unk. *)
    (*   apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (subst a_stk;solve_addr+Hcontra He_a1). *)
    (*   apply elem_of_cons in Hastk2_unk as [Hcontra | Hastk2_unk]; first (subst a_stk;solve_addr+Hcontra He_a1). *)
    (*   apply elem_of_cons in Hastk1_unk as [Hcontra | Hastk1_unk]; first (subst a_stk;solve_addr+Hcontra He_a1). *)

    (*   apply elem_of_Permutation in Hastk1_unk as [l1 Hl1]. *)
    (*   rewrite Hl1 in Hastk2_unk,Hastk3_unk. *)
    (*   apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (subst a_stk;solve_addr+Hcontra He_a1). *)
    (*   apply elem_of_cons in Hastk2_unk as [Hcontra | Hastk2_unk]; first (subst a_stk;solve_addr+Hcontra He_a1). *)

    (*   apply elem_of_Permutation in Hastk2_unk as [l2 Hl2]. *)
    (*   rewrite Hl2 in Hastk3_unk. *)
    (*   apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (subst a_stk;solve_addr+Hcontra He_a1). *)

    (*   apply elem_of_Permutation in Hastk3_unk as [l3 Hl3]. *)

    (*   rewrite Hl3 in Hl2; rewrite Hl2 in Hl1; rewrite Hl1 in Hl0. *)
    (*   clear Hl3 Hl2 Hl1. *)

    (*   iExists l3; iFrame "%". *)
    (*   iEval (setoid_rewrite Hl0) in "Hrevoked". *)
    (*   cbn. *)
    (*   iDestruct "Hrevoked" as "( [Hv0 _] & [Hv1 _] & [Hv2 _] & [Hv3 _] & $)". *)
    (*   iDestruct "Hv0" as (? ? ?) "[Hv0 _]". *)
    (*   iDestruct "Hv1" as (? ? ?) "[Hv1 _]". *)
    (*   iDestruct "Hv2" as (? ? ?) "[Hv2 _]". *)
    (*   iDestruct "Hv3" as (? ? ?) "[Hv3 _]". *)
    (*   rewrite /temp_resources. *)
    (*   iDestruct "Hv0" as (??) "[$ _]". *)
    (*   iDestruct "Hv1" as (??) "[$ _]". *)
    (*   iDestruct "Hv2" as (??) "[$ _]". *)
    (*   iDestruct "Hv3" as (??) "[$ _]". *)
    (* } *)
    (* iDestruct "H" as (????) "($&$&$&$)". *)
    (* by iFrame. *)
    (* } *)

    (* --- Load cgp csp --- *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcgp".

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 2)%a); subst a_stk; solve_addr+Ha_stk4. }
    replace ((csp_b ^+ -4) ^+ 3)%a with (a_stk ^+ 3)%a by (subst a_stk; solve_addr+Ha_stk4).
    replace ((csp_b ^+ -4) ^+ 2)%a with (a_stk ^+ 2)%a by (subst a_stk; solve_addr+Ha_stk4).

    (* Load ca2 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hca2".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 1)%a); subst a_stk; solve_addr+Ha_stk4. }
    (* Load cs1 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcs1".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk); subst a_stk; solve_addr. }
    (* Load cs0 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcs0".
    (* GetE ct0 csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* -------- CLEAR STACK --------- *)
    focus_block 7 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iAssert ([[ a_stk , csp_e ]] ↦ₐ [[wastk :: wastk1 :: wastk2 :: wastk3 :: stk_mem]])%I
      with "[Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hstk]" as "Hstk".
    {
      iAssert ([[ (a_stk ^+ 4)%a , csp_e ]] ↦ₐ [[ stk_mem ]])%I with "[Hstk]" as "Hstk".
      { replace (a_stk ^+ 4)%a with csp_b; first done. subst a_stk;solve_addr+Ha_stk4. }
      subst a_stk.
      iDestruct (region_pointsto_cons with "[$Ha_stk3 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk2 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iFrame.
    }

    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto; [solve_addr|].
    iSplitL; cycle 1.
    { iIntros "!> %"; simplify_eq. }
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 8 "Hcode" as a8 Ha8 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cra ca2 *)
    iInstr "Hcode" with "Hlc".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* -------- CLEAR REGISTERS --------- *)
    focus_block 9 "Hcode" as a9 Ha9 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct1]") as "Hrmap".
    rewrite -delete_insert_ne //.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct0]") as "Hrmap".
    do 2 (rewrite (delete_commute _ _ ca2); auto).
    do 2 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca2]") as "Hrmap".
    do 2 (rewrite (delete_commute _ _ ctp); auto).
    do 3 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hctp]") as "Hrmap".

    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]"); try solve_pure.
    { clear -Hrmap.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      rewrite Hrmap.
      set_solver.
    }
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Hrmap & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    focus_block 10 "Hcode" as a10 Ha10 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* JmpCap cra *)
    iInstr "Hcode" with "Hlc".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    iHide "Hcode" as hcode.
    subst a_stk; set (a_stk := (csp_b ^+ -4)%a).
    (* rewrite (region_addrs_zeroes_split _ (a_stk ^+ 4)%a); last (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1). *)
    (* rewrite (region_pointsto_split _ _ (a_stk ^+ 4)%a) *)
    (* ; [| subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1 | by rewrite /region_addrs_zeroes length_replicate]. *)
    (* iDestruct "Hstk" as "[Hstk_register_save Hstk]". *)


    (* Update the call-stack: depop the topmost frame *)
    iDestruct (cstack_update _ _ cstk with "[$] [$]") as ">[Hcstk_full Hcstk_frag]".

    (* Close the switcher's invariant *)
    iDestruct (region_pointsto_cons with "[$Ha_tstk $Htstk]") as "Htstk"; [solve_addr| solve_addr| ].
    iMod ("Hclose_switcher_inv"
           with "[Hstk_interp_next $Hna $Hmtdc $Hcode $Hb_switcher Htstk $Hcstk_full $Hp_ot_switcher]")
      as "Hna".
    {
      replace (a_tstk1 ^+ 1)%a with a_tstk by solve_addr.
      replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.
      iFrame.
      iNext.
      iSplit; first (iPureIntro; done).
      iSplit; first (iPureIntro; solve_addr+Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Ha_tstk1).
      iPureIntro; solve_addr+Hbounds_tstk_b  Hlen_cstk Ha_tstk1.
    }

    (* TODO need to fix the world *)


    destruct is_untrusted_caller; cycle 1.
    - (* Case where caller is trusted, we use the continuation *)
      destruct Hwastks as (-> & -> & -> & ->).
      (* TODO need open the world *)
      (* iEval (rewrite app_nil_r) in "Hr". *)
      (* iAssert ([[a_stk,e_stk]] ↦ₐ [[region_addrs_zeroes a_stk e_stk%a]])%I with "[Hstk_register_save Hstk]" as "Hstk". *)
      (* { *)
      (*   rewrite (region_addrs_zeroes_split a_stk (a_stk ^+4)%a e_stk); last solve_addr+Ha_stk4 He_a1 Hb_a4. *)
      (*   rewrite region_pointsto_split; first iFrame. *)
      (*   solve_addr+Ha_stk4 He_a1 Hb_a4. *)
      (*   by rewrite /region_addrs_zeroes length_replicate. *)
      (* } *)
      (* iAssert (([∗ list] a ∈ finz.seq_between (a_stk ^+ 4)%a e_stk, closing_resources interp W C a (WInt 0)))%I *)
      (*   with "[Hres]" as "Hres". *)
      (* { iClear "#". *)
      (*   clear -Hlen_lv. *)
      (*   iStopProof. *)
      (*   revert Hlen_lv. *)
      (*   generalize dependent lv. *)
      (*   generalize (finz.seq_between (a_stk ^+ 4)%a e_stk) as la. *)
      (*   induction la; iIntros (lv Hlen) "H"; destruct lv as [|v lv]; simplify_eq; cbn; first done. *)
      (*   iDestruct "H" as "[Ha H]". *)
      (*   iDestruct (closing_resources_zeroed with "Ha") as "$". *)
      (*   by iApply (IHla with "H"). *)
      (* } *)

      (* here I'm supposed to have fixed the world, so (revoke Wcur) should be fixed *)
      iAssert (interp (revoke Wcur) C wca0)%I as "#Hinterp_wca0".
      { admit. (* hypothesis *) }
      iAssert (interp (revoke Wcur) C wca1)%I as "#Hinterp_wca1".
      { admit. (* hypothesis *) }
      iApply ("Hexec_topmost_frm" with
               "[] [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_wca0 $Hinterp_wca1
      $Hrmap $Hstk Hr $Hsts $Hcont_K $Hcstk_frag $Hna]").
      { admit. (* hypothesis *) }
      iSplitR.
      { iPureIntro;rewrite Harg_rmap'; set_solver. }
      iSplit; first done.
      iSplit; first done.
      admit. (* follows from opening the world *)

    - (* Case where caller is untrusted, we use the IH *)

      (* I should know that wastk,... , are interp, because of interp_callee_wstk
       and fixed world is public *)

  Admitted.



End Switcher.
