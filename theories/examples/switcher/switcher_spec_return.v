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
    let Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) (revoke Wcur)) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->
    NoDup (l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, W0.1 !! a = Some Temporary ↔ a ∈ l ++ finz.seq_between csp_b csp_e) ->

    (* Switcher Invariant *)
    na_inv logrel_nais Nswitcher switcher_inv
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
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
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hcstk & HK & Hsts & Hna
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
    iInstr "Hcode" with "Hlc".
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
        |={⊤}=>
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
          ∗ (if is_untrusted_caller
             then (
                 (interp Wfixed C wastk)
                 ∗ (interp Wfixed C wastk1)
                 ∗ (interp Wfixed C wastk2)
                 ∗ (interp Wfixed C wastk3)
               )
             else True
            )
          ∗ ( if is_untrusted_caller
              then
                ( ∃ l',
                    ⌜ l ≡ₚ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a]++l' ⌝
                    ∗ ([∗ list] a ∈ l', (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ),
                                       ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝ ∗
                                                                        temp_resources W0 C P a p ∗ rel C a p P) ∗
                                   ⌜(revoke W0).1 !! a = Some Revoked⌝)
                    ∗ ([∗ list] a ∈ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a],
                       ∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
                         ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                                          ∗ (⌜isO p = false⌝
                                                             ∗ (if isWL p
                                                                then future_pub_mono C φ (WInt 0)
                                                                else if isDL p then future_pub_mono C φ (WInt 0) else future_priv_mono C φ (WInt 0)
                                                               )
                                                             ∗ φ (W0, C, WInt 0))
                                                          ∗ rel C a p φ
                      )
                )
              else
                ([∗ list] a ∈ l, (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ),
                                     ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝ ∗
                                                                      temp_resources W0 C P a p ∗ rel C a p P) ∗
                                 ⌜(revoke W0).1 !! a = Some Revoked⌝
                )
            )
      )%I
      with "[Hcframe_interp Hrevoked Hlc]" as ">Hcframe_interp"
    ; [|iDestruct "Hcframe_interp" as
        (wastk wastk1 wastk2 wastk3
        ) "(Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & %Hwastks & #Hinterp_wfrm & Hrevoked)"
      ].
    {
      destruct is_untrusted_caller; cycle 1.
      * iExists wcs0, wcs1, wret, wcgp.
        iDestruct "Hcframe_interp" as "($&$&$&$)". iFrame.
        done.
      * cbn.
        iAssert
          (⌜ ∀ (a : Addr), a ∈ (finz.seq_between b_stk csp_e) → (std W0 !! a) = Some Temporary ⌝)%I
          as "%Hstk_tmp".
        {
          iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_callee_wstk") as "%Hstk_tmp" ; auto.
          iPureIntro ; intros a Ha.
          apply elem_of_list_lookup_1 in Ha as [k Ha].
          by eapply Hstk_tmp.
        }

        iAssert ( ⌜ a_stk ∈ l ⌝)%I as "%Hastk_unk".
        {
          opose proof (Hstk_tmp a_stk _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; subst a_stk; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          rewrite elem_of_finz_seq_between in Hcontra.
          subst a_stk.
          solve_addr+Hcontra.
        }
        iAssert ( ⌜ (a_stk ^+1)%a ∈ l ⌝)%I as "%Hastk1_unk".
        {
          opose proof (Hstk_tmp (a_stk ^+1)%a _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; subst a_stk; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          rewrite elem_of_finz_seq_between in Hcontra.
          subst a_stk.
          solve_addr+Hcontra.
        }
        iAssert ( ⌜ (a_stk ^+2)%a ∈ l ⌝)%I as "%Hastk2_unk".
        {
          opose proof (Hstk_tmp (a_stk ^+2)%a _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; subst a_stk; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          rewrite elem_of_finz_seq_between in Hcontra.
          subst a_stk.
          solve_addr+Hcontra.
        }
        iAssert ( ⌜ (a_stk ^+3)%a ∈ l ⌝)%I as "%Hastk3_unk".
        {
          opose proof (Hstk_tmp (a_stk ^+3)%a _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; subst a_stk; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          rewrite elem_of_finz_seq_between in Hcontra.
          subst a_stk.
          solve_addr+Hcontra.
        }
        iDestruct (write_allowed_inv _ _ a_stk with "Hinterp_callee_wstk")
          as (p_astk0 φ_astk0) "(%Hp_astk0 & _ &  Hrel_astk0 & _ & Hwcond_astk0 & Hrcond_astk0 & _)"
        ; auto.
        { subst a_stk; solve_addr+Hb_a4 He_a1. }
        iDestruct (write_allowed_inv _ _ (a_stk ^+1)%a with "Hinterp_callee_wstk")
          as (p_astk1 φ_astk1) "(%Hp_astk1 & _ &  Hrel_astk1 & _ & Hwcond_astk1 & Hrcond_astk1 & _)"
        ; auto.
        { subst a_stk; solve_addr+Hb_a4 He_a1. }
        iDestruct (write_allowed_inv _ _ (a_stk ^+2)%a with "Hinterp_callee_wstk")
          as (p_astk2 φ_astk2) "(%Hp_astk2 & _ &  Hrel_astk2 & _ & Hwcond_astk2 & Hrcond_astk2 & _)"
        ; auto.
        { subst a_stk; solve_addr+Hb_a4 He_a1. }
        iDestruct (write_allowed_inv _ _ (a_stk ^+3)%a with "Hinterp_callee_wstk")
          as (p_astk3 φ_astk3) "(%Hp_astk3 & _ &  Hrel_astk3 & _ & Hwcond_astk3 & Hrcond_astk3 & _)"
        ; auto.
        { subst a_stk; solve_addr+Hb_a4 He_a1. }

        iAssert
          ( ▷ (∃ l',
              ⌜ l ≡ₚ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a]++l' ⌝
              ∗ ([∗ list] a ∈ l', (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ),
                                      ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝ ∗
                                                                       temp_resources W0 C P a p ∗ rel C a p P) ∗
                                  ⌜(revoke W0).1 !! a = Some Revoked⌝)
              ∗ (∃ wastk wastk1 wastk2 wastk3,
                    a_stk ↦ₐ wastk
                    ∗ (a_stk ^+ 1)%a ↦ₐ wastk1
                    ∗ (a_stk ^+ 2)%a ↦ₐ wastk2
                    ∗ (a_stk ^+ 3)%a ↦ₐ wastk3
                    ∗ (interp W0 C wastk)
                    ∗ (interp W0 C wastk1)
                    ∗ (interp W0 C wastk2)
                    ∗ (interp W0 C wastk3)
                )
              ∗ ([∗ list] a ∈ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a],
                   ∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
                     ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                                      ∗ (⌜isO p = false⌝
                                                         ∗ (if isWL p
                                                            then future_pub_mono C φ (WInt 0)
                                                            else if isDL p then future_pub_mono C φ (WInt 0) else future_priv_mono C φ (WInt 0)
                                                           )
                                                         ∗ φ (W0, C, WInt 0))
                                                      ∗ rel C a p φ
                )
          ))%I with "[Hrevoked]" as "H".
    { apply NoDup_app in Hnodup_revoked as (Hnodup_revoked & ? & ?).
      apply elem_of_Permutation in Hastk_unk as [l0 Hl0].
      rewrite Hl0 in Hastk1_unk,Hastk2_unk,Hastk3_unk.
      apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (subst a_stk;solve_addr+Hcontra He_a1).
      apply elem_of_cons in Hastk2_unk as [Hcontra | Hastk2_unk]; first (subst a_stk;solve_addr+Hcontra He_a1).
      apply elem_of_cons in Hastk1_unk as [Hcontra | Hastk1_unk]; first (subst a_stk;solve_addr+Hcontra He_a1).

      apply elem_of_Permutation in Hastk1_unk as [l1 Hl1].
      rewrite Hl1 in Hastk2_unk,Hastk3_unk.
      apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (subst a_stk;solve_addr+Hcontra He_a1).
      apply elem_of_cons in Hastk2_unk as [Hcontra | Hastk2_unk]; first (subst a_stk;solve_addr+Hcontra He_a1).

      apply elem_of_Permutation in Hastk2_unk as [l2 Hl2].
      rewrite Hl2 in Hastk3_unk.
      apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (subst a_stk;solve_addr+Hcontra He_a1).

      apply elem_of_Permutation in Hastk3_unk as [l3 Hl3].

      rewrite Hl3 in Hl2; rewrite Hl2 in Hl1; rewrite Hl1 in Hl0.
      clear Hl3 Hl2 Hl1.

      iExists l3; iFrame "%".
      iEval (setoid_rewrite Hl0) in "Hrevoked".
      cbn.
      iDestruct "Hrevoked" as "( [Hv0 _] & [Hv1 _] & [Hv2 _] & [Hv3 _] & $)".
      iDestruct "Hv0" as (? P0 ?) "[Hv0 #Hrel0]".
      iDestruct "Hv1" as (? P1 ?) "[Hv1 #Hrel1]".
      iDestruct "Hv2" as (? P2 ?) "[Hv2 #Hrel2]".
      iDestruct "Hv3" as (? P3 ?) "[Hv3 #Hrel3]".
      iClear "Hinterp_Wfixed_wca0 Hinterp_Wfixed_wca1 Hinterp_callee_wstk".
      iFrame "#".
      iDestruct "Hv0" as (v0 ?) "[$ [#H0 H0']]".
      iDestruct "Hv1" as (v1 ?) "[$ [#H1 H1']]".
      iDestruct "Hv2" as (v2 ?) "[$ [#H2 H2']]".
      iDestruct "Hv3" as (v3 ?) "[$ [#H3 H3']]".
      iFrame "%".
      iDestruct (rel_agree _ _ (safeC φ_astk0) P0 with "[$Hrel_astk0 $Hrel0]") as "[<- HP0]".
      iDestruct (rel_agree _ _ (safeC φ_astk1) P1 with "[$Hrel_astk1 $Hrel1]") as "[<- HP1]".
      iDestruct (rel_agree _ _ (safeC φ_astk2) P2 with "[$Hrel_astk2 $Hrel2]") as "[<- HP2]".
      iDestruct (rel_agree _ _ (safeC φ_astk3) P3 with "[$Hrel_astk3 $Hrel3]") as "[<- HP3]".
      rewrite (readAllowed_flowsto RWL p_astk0); auto.
      rewrite (readAllowed_flowsto RWL p_astk1); auto.
      rewrite (readAllowed_flowsto RWL p_astk2); auto.
      rewrite (readAllowed_flowsto RWL p_astk3); auto.
      rewrite (isWL_flowsto RWL p_astk0); auto.
      rewrite (isWL_flowsto RWL p_astk1); auto.
      rewrite (isWL_flowsto RWL p_astk2); auto.
      rewrite (isWL_flowsto RWL p_astk3); auto.
      iNext.
      iRewrite - ("HP0" $! (W0,C,v0)) in "H0'".
      iRewrite - ("HP1" $! (W0,C,v1)) in "H1'".
      iRewrite - ("HP2" $! (W0,C,v2)) in "H2'".
      iRewrite - ("HP3" $! (W0,C,v3)) in "H3'".
      iDestruct ("Hrcond_astk0" with "H0'") as "#Hinterp0"; cbn.
      iDestruct ("Hrcond_astk1" with "H1'") as "#Hinterp1"; cbn.
      iDestruct ("Hrcond_astk2" with "H2'") as "#Hinterp2"; cbn.
      iDestruct ("Hrcond_astk3" with "H3'") as "#Hinterp3"; cbn.
      iSplitR ; cycle 1.
      iSplitL "H0 H0'".
      { iSplitR "H0'"; cycle 1.
        + iRewrite - ("HP0" $! (W0,C,WInt 0)).
          iApply "Hwcond_astk0"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP0" $! (W',C,WInt 0)).
          iApply "Hwcond_astk0"; iApply interp_int.
      }
      iSplitL "H1 H1'".
      { iSplitR "H1'"; cycle 1.
        + iRewrite - ("HP1" $! (W0,C,WInt 0)).
          iApply "Hwcond_astk1"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP1" $! (W',C,WInt 0)).
          iApply "Hwcond_astk1"; iApply interp_int.
      }
      iSplitL "H2 H2'".
      { iSplitR "H2'"; cycle 1.
        + iRewrite - ("HP2" $! (W0,C,WInt 0)).
          iApply "Hwcond_astk2"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP2" $! (W',C,WInt 0)).
          iApply "Hwcond_astk2"; iApply interp_int.
      }
      { iSplitR "H3'"; cycle 1.
        + iRewrite - ("HP3" $! (W0,C,WInt 0)).
          iApply "Hwcond_astk3"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP3" $! (W',C,WInt 0)).
          iApply "Hwcond_astk3"; iApply interp_int.
      }

      rewrite /load_word.
      rewrite (notisDRO_flowsfrom RWL p_astk0); eauto.
      rewrite (notisDRO_flowsfrom RWL p_astk1); eauto.
      rewrite (notisDRO_flowsfrom RWL p_astk2); eauto.
      rewrite (notisDRO_flowsfrom RWL p_astk3); eauto.
      rewrite (notisDL_flowsfrom RWL p_astk0); eauto.
      rewrite (notisDL_flowsfrom RWL p_astk1); eauto.
      rewrite (notisDL_flowsfrom RWL p_astk2); eauto.
      rewrite (notisDL_flowsfrom RWL p_astk3); eauto.
    }

    iDestruct (lc_fupd_elim_later with "[$] [$H]") as ">H".
    iModIntro.
    iDestruct "H" as (l') "($ & $ & (%&%&%&%& $&$&$&$&H0&H1&H2&H3) & ($&$&$&?))".
    iDestruct (interp_monotone W0 Wfixed with "[] H0") as "$"; first done.
    iDestruct (interp_monotone W0 Wfixed with "[] H1") as "$"; first done.
    iDestruct (interp_monotone W0 Wfixed with "[] H2") as "$"; first done.
    iDestruct (interp_monotone W0 Wfixed with "[] H3") as "$"; first done.
    iFrame.
    rewrite big_sepL_singleton; iFrame.
    }

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
    iInstr "Hcode" with "Hlc'".

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


    iAssert
      ([[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]] ∗ [[a_stk4,csp_e]]↦ₐ[[region_addrs_zeroes a_stk4 csp_e]]
      )%I with "[Hstk]" as "[Hstk' Hstk]".
    {
      rewrite (region_addrs_zeroes_split _ a_stk4); last (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      rewrite (region_pointsto_split _ _ a_stk4)
      ; [| subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1 | by rewrite /region_addrs_zeroes length_replicate].
      done.
    }
    set (closing_region := finz.seq_between csp_b csp_e).


    (* Fix the world! *)
    iAssert (
        |==>
          sts_full_world Wfixed C
          ∗ region Wfixed C
          ∗ (if is_untrusted_caller
             then True
             else [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]]
            )
      )%I with "[Hsts Hr Hstk' Hstk Hrevoked]" as ">(Hsts & Hr & Hstk')".
    { destruct is_untrusted_caller.
      - (* caller is untrusted, we need to re-instate the whole stack frame *)
        iMod (monotone_close_list_region W0 _ _ (l++closing_region) with
               "[] [$Hr $Hsts Hrevoked Hstk Hstk']") as "[Hsts Hr]"; first done; last by iFrame.
        iDestruct "Hrevoked" as (l') "(%Hl & Hrevoked & (Hrev0 & Hrev1 & Hrev2 & Hrev3 & _) )".
        rewrite Hl.
        rewrite big_sepL_app.
        rewrite big_sepL_app.
        iSplitR "Hstk"; cycle 1.
        { subst closing_region.
          replace a_stk4 with csp_b by solve_addr+Ha_stk4 Hb_a4 He_a1.
          (* I should be able to obtain all the information I need from Hinterp_callee_wstk *)
          admit.
        }
        iSplitR "Hrevoked"; cycle 1.
        { iApply (big_sepL_impl with "Hrevoked"); iIntros "!> % % %Hk [$ _]". }
        cbn in *.
        replace a_stk4 with (a_stk ^+4)%a by (subst a_stk; solve_addr+Ha_stk4 He_a1).
        rewrite /region_addrs_zeroes.
        replace (finz.dist a_stk (a_stk ^+ 4)%a) with 4; first cbn.
        2: { do 4 (rewrite finz_dist_S; last (subst a_stk; solve_addr+Ha_stk4)).
             rewrite finz_dist_0; last (subst a_stk; solve_addr+Ha_stk4).
             done.
        }
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk0 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 1)%a ); subst a_stk; solve_addr+Ha_stk4
          | subst a_stk; solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk1 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 2)%a ); subst a_stk; solve_addr+Ha_stk4
          | subst a_stk; solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk2 Hstk']"
        ; [ transitivity ( Some (a_stk ^+ 3)%a ); subst a_stk; solve_addr+Ha_stk4
          | subst a_stk; solve_addr+Ha_stk4 He_a1
          |].
        iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk3 _]"
        ; [ transitivity ( Some (a_stk ^+ 4)%a ); subst a_stk; solve_addr+Ha_stk4
          | subst a_stk; solve_addr+Ha_stk4 He_a1
          |].
        iFrame.

      - (* caller is trusted, we need only need re-instate callee's stack frame *)
        iFrame "Hstk'".
        iMod (monotone_close_list_region W0 _ _ (l++closing_region) with
               "[] [$Hr $Hsts Hrevoked Hstk]") as "[Hsts Hr]"; first done; last by iFrame.
        rewrite big_sepL_app.
        iSplitL "Hrevoked".
        { iApply (big_sepL_impl with "Hrevoked"); iIntros "!> % % %Hk [$ _]". }
        subst closing_region.
        replace a_stk4 with csp_b by solve_addr+Ha_stk4 Hb_a4 He_a1.
        admit.
        (* I should be able to obtain all the information I need from Hinterp_callee_wstk *)
    }

    iDestruct (interp_monotone with "[] [$Hinterp_callee_wstk]") as "Hinterp_callee_wstk'" ; first done.


    destruct is_untrusted_caller; cycle 1.
    - (* Case where caller is trusted, we use the continuation *)
      destruct Hwastks as (-> & -> & -> & ->).

    iEval (rewrite region_open_nil) in "Hr".
    iDestruct (region_open_list_interp_gen _ _ (finz.seq_between a_stk4 csp_e) []
                with "[$Hinterp_callee_wstk' $Hr $Hsts]")
      as "(Hr & Hsts & Hres)"; auto.
    { apply finz_seq_between_NoDup. }
    { apply Forall_forall; intros y Hy.
      rewrite elem_of_finz_seq_between in Hy.
      subst a_stk.
      solve_addr+Ha_stk4 Hb_a4 He_a1 Hy.
    }
    { set_solver+. }

      iAssert (∃ (lv : list Word),
                  ⌜ length lv = length (finz.seq_between a_stk4 csp_e) ⌝
                  ∗ ▷ ([∗ list] a ; v ∈ (finz.seq_between a_stk4 csp_e) ; lv, closing_resources interp Wfixed C a v)
                  ∗ ([∗ list] a ; v ∈ (finz.seq_between a_stk4 csp_e)  ; lv, a ↦ₐ v)
              )%I
        with "[Hres]"
        as (lv Hlen_lv) "[Hres Hstk]".
      {
        replace a_stk4 with csp_b by solve_addr+Ha_stk4 Hb_a4 He_a1.
        replace (a_stk ^+ 4)%a with csp_b by (subst a_stk;solve_addr+Ha_stk4 Hb_a4 He_a1).
        iClear "#"; clear.
        iStopProof.
        generalize Wfixed; clear; intros W.
        generalize (finz.seq_between csp_b csp_e).
        induction l; cbn; iIntros "Hres".
        - iExists []; cbn; done.
        - iDestruct "Hres" as "[Ha Hres]".
          iDestruct (IHl with "Hres") as (lv) "(%Hlen & Hres & Hlv)".
          iDestruct ( opening_closing_resources with "Ha" ) as (va) "[Hres_a Ha]".
          iExists (va::lv).
          iFrame.
          iPureIntro ; cbn ; lia.
      }
      rewrite app_nil_r.
      replace a_stk4 with csp_b by solve_addr+Ha_stk4 Hb_a4 He_a1.
      replace csp_b with (a_stk ^+ 4)%a by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      iDestruct (lc_fupd_elim_later with "[$] [$Hres]") as ">Hres".


      iApply ("Hexec_topmost_frm" with
               "[] [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_Wfixed_wca0 $Hinterp_Wfixed_wca1
      $Hrmap $Hr $Hstk $Hstk' $Hsts $Hres $Hcont_K $Hcstk_frag $Hna]"); first done.

      iSplitR.
      { iPureIntro;rewrite Harg_rmap'; set_solver. }
      iSplit; done.

    - (* Case where caller is untrusted, we use the IH *)

      iDestruct "Hinterp_wfrm" as "#(Hinterp_wstk0 & Hinterp_wstk1 & Hinterp_wstk2 & Hinterp_wstk3)".
      iClear "Hexec_topmost_frm".

      (* TODO apply the FTLR here, should be fine *)
      (* BUT!!! I can't prove `frame_match Wfixed` because what I have is `frame_match W0` !!!! *)

      (* iDestruct (fundamental _ cstk Ws Cs _ _ (WCap RWL Local b_stk csp_e a_stk) with "[$] Hinterp_wstk2") as "Hcont'". *)
      (* rewrite /interp_expression /=. *)
      (* iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hrmap_zeroes]". *)

      (* iDestruct (big_sepM_insert with "[$Hrmap $Hca0]") as "Hrmap". *)
      (* { apply not_elem_of_dom; rewrite Harg_rmap'; set_solver+. } *)
      (* iDestruct (big_sepM_insert with "[$Hrmap $Hca1]") as "Hrmap". *)
      (* { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. } *)
      (* iDestruct (big_sepM_insert with "[$Hrmap $Hcs0]") as "Hrmap". *)
      (* { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. } *)
      (* iDestruct (big_sepM_insert with "[$Hrmap $Hcs1]") as "Hrmap". *)
      (* { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. } *)
      (* iDestruct (big_sepM_insert with "[$Hrmap $Hcgp]") as "Hrmap". *)
      (* { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. } *)
      (* iDestruct (big_sepM_insert with "[$Hrmap $Hcra]") as "Hrmap". *)
      (* { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. } *)
      (* iDestruct (big_sepM_insert with "[$Hrmap $Hcsp]") as "Hrmap". *)
      (* { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. } *)
      (* iClear "Hlc Hlc' Hstk'". *)

      (* set (regs := <[csp := _]> _ ). *)
      (* set (regs' := <[PC := WInt 0]> regs). *)
      (* iApply ("Hcont'" $! regs'); iFrame. *)
      (* iSplit. *)
      (* { iSplit. *)
      (*   + iIntros (r); iPureIntro. *)
      (*     rewrite -elem_of_dom. *)
      (*     subst regs regs'. *)
      (*     repeat (rewrite dom_insert_L). *)
      (*     rewrite Harg_rmap'. *)
      (*     set_solver+. *)
      (*   + iIntros (r v) "%HrPC %Hr". *)
      (*     subst regs' regs. *)
      (*     clear -Hr HrPC Hrmap_zeroes. *)
      (*     simplify_map_eq. *)
      (*     destruct (decide (r = csp)); simplify_map_eq; first done. *)
      (*     destruct (decide (r = cra)); simplify_map_eq; first done. *)
      (*     destruct (decide (r = cgp)); simplify_map_eq; first done. *)
      (*     destruct (decide (r = cs1)); simplify_map_eq; first done. *)
      (*     destruct (decide (r = cs0)); simplify_map_eq; first done. *)
      (*     destruct (decide (r = ca1)); simplify_map_eq; first done. *)
      (*     destruct (decide (r = ca0)); simplify_map_eq; first done. *)
      (*     eapply map_Forall_lookup_1 in Hr; eauto; cbn in Hr; simplify_eq. *)
      (*     iApply interp_int. *)
      (* } *)
      (* iSplit. *)
      (* {  rewrite /registers_pointsto. *)
      (*    subst regs'. *)
      (*   admit. } *)
      (* iSplit. *)
      (* { *)

      (* } *)
      (* last (iPureIntro; apply Hframe). *)

  Admitted.

End Switcher.
