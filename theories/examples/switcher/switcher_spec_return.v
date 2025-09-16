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
    (W0 W : WORLD)
    (C : CmptName)
    (rmap : Reg)
    (csp_e csp_b cgp_b cgp_e: Addr)
    (l_unk : list Addr)
    (stk_mem : list Word)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : Word)
    :
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    NoDup (l_unk ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, (std W0) !! a = Some Temporary ↔ a ∈ l_unk ++ finz.seq_between csp_b csp_e) ->


    (* Switcher Invariant *)
    na_inv logrel_nais Nswitcher switcher_inv
    ∗ ([∗ list] a ∈ finz.seq_between (csp_b ^+ 4)%a csp_e, closing_resources interp W C a (WInt 0))
    ∗ ([∗ list] a ∈ finz.seq_between (csp_b ^+ 4)%a csp_e, ⌜W.1 !! a = Some Temporary⌝)
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ sts_full_world W C
    ∗ na_own logrel_nais ⊤
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ open_region_many W C (finz.seq_between (csp_b ^+ 4)%a csp_e)
    ∗ ([∗ list] a ∈ l_unk,
          (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ),
              ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝
              ∗ temp_resources W0 C P a p
              ∗ rel C a p P)
          ∗ ⌜(std W) !! a = Some Revoked⌝)
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    iIntros (Hrmap Hframe Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & Hcls_stk & #Hstktemp & Hstk & Hcstk & Hcont & Hsts & Hna
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

    focus_block_nochangePC 1 "Hcode" as a_ret Ha_ret "Hcode" "Hcls". iHide "Hcls" as hcont.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.
    replace a_ret with a_switcher_return by solve_addr.
    codefrag_facts "Hcode".

    assert (is_Some (rmap !! ctp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ctp as "Hctp".
    assert (is_Some (rmap !! cgp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cgp as "Hcgp".

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

    iDestruct "Hcont" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".

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
    { by transitivity (Some (a_stk ^+ 3)%a); solve_addr+Ha_stk4. }

    set (stk_len := finz.dist (csp_b ^+ 4)%a csp_e).
    set (stk_ws := repeat (WInt 0) stk_len).

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
          ∗ ([∗ list] a ∈ l_unk, (∃ (p : Perm) (P : WORLD * CmptName * Word → iPropI Σ),
                                      ⌜∀ Wv : WORLD * CmptName * Word, Persistent (P Wv)⌝ ∗
                                      temp_resources W0 C P a p ∗ rel C a p P) ∗
               ⌜W.1 !! a = Some Revoked⌝)
      )%I
      with "[Hcframe_interp Hcls_stk Hrevoked]" as "Hcframe_interp"
    ; [|iDestruct "Hcframe_interp" as
        (wastk wastk1 wastk2 wastk3
        ) "(Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & %Hwastks & Hrevoked)"
      ].
    {
      destruct is_untrusted_caller; cycle 1.
      * iExists wcs0, wcs1, wret, wcgp.
        iDestruct "Hcframe_interp" as "($&$&$&$)". iFrame.
        cbn.
        done.
        (* iSplit;done. *)
        (* iNext. *)
        (* iApply (big_sepL2_mono (λ _ a _, closing_resources interp W C a (WInt 0))). *)
        (* { iIntros (???? ->%elem_of_list_lookup_2%elem_of_list_In%repeat_spec) "HH". *)
        (*   iFrame. } *)
        (* iApply big_sepL2_const_sepL_l. iFrame. iPureIntro. *)
        (* rewrite repeat_length finz_seq_between_length//. *)
      * cbn.
        iAssert
          (⌜ ∀ (a : Addr), a ∈ (finz.seq_between b_stk e_stk) → (std W0 !! a) = Some Temporary ⌝)%I
          as "%Hstk_tmp".
        {
          iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_callee_wstk") as "%Hstk_tmp" ; auto.
          iPureIntro ; intros a Ha.
          apply elem_of_list_lookup_1 in Ha as [k Ha].
          by eapply Hstk_tmp.
        }

        iAssert ( ⌜ a_stk ∈ l_unk ⌝)%I as "%Hastk_unk".
        {
          opose proof (Hstk_tmp a_stk _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          (* TODO it should be that a_stk is (csp_b+4) *)
          admit.
        }
  Admitted.
  (*       } *)
  (*       do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1). *)
  (*       rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+. *)
  (*       cbn. *)
  (*       replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4. *)
  (*       replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4. *)
  (*       cbn. *)
  (*       iDestruct "Hres" as "(Hres0 & Hres1 & Hres2 & Hres3 & _)". *)
  (*       iDestruct (opening_closing_resources with "Hres0") as (wastk) "[Hres0 $]". *)
  (*       iDestruct (opening_closing_resources with "Hres1") as (wastk1) "[Hres1 $]". *)
  (*       iDestruct (opening_closing_resources with "Hres2") as (wastk2) "[Hres2 $]". *)
  (*       iDestruct (opening_closing_resources with "Hres3") as (wastk3) "[Hres3 $]". *)
  (*       iFrame. *)
  (*   } *)

  (*   (* --- Load cgp csp --- *) *)
  (*   iInstr "Hcode". *)
  (*   { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. } *)
  (*   iEval (cbn) in "Hcgp". *)

  (*   (* --- Lea csp (-1)%Z --- *) *)
  (*   iInstr "Hcode". *)
  (*   { by transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. } *)

  (*   (* Load ca2 csp *) *)
  (*   iInstr "Hcode". *)
  (*   { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. } *)
  (*   iEval (cbn) in "Hca2". *)
  (*   (* Lea csp (-1)%Z *) *)
  (*   iInstr "Hcode". *)
  (*   { by transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. } *)
  (*   (* Load cs1 csp *) *)
  (*   iInstr "Hcode". *)
  (*   { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. } *)
  (*   iEval (cbn) in "Hcs1". *)
  (*   (* Lea csp (-1)%Z *) *)
  (*   iInstr "Hcode". *)
  (*   { by transitivity (Some a_stk); solve_addr. } *)
  (*   (* Load cs0 csp *) *)
  (*   iInstr "Hcode". *)
  (*   { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. } *)
  (*   iEval (cbn) in "Hcs0". *)
  (*   (* GetE ct0 csp *) *)
  (*   iInstr "Hcode". *)
  (*   (* GetA ct1 csp *) *)
  (*   iInstr "Hcode". *)

  (*   unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont. *)

  (*   { i} *)

  (*   iAssert ( *)
  (*       ∃ wastk wastk1 wastk2 wastk3, *)
  (*       let la := (if is_untrusted_caller then finz.seq_between a_stk (a_stk ^+ 4)%a else []) in *)
  (*       let lv := (if is_untrusted_caller then [wastk;wastk1;wastk2;wastk3] else []) in *)
  (*         a_stk ↦ₐ wastk *)
  (*         ∗ (a_stk ^+ 1)%a ↦ₐ wastk1 *)
  (*         ∗ (a_stk ^+ 2)%a ↦ₐ wastk2 *)
  (*         ∗ (a_stk ^+ 3)%a ↦ₐ wastk3 *)
  (*         ∗ ▷ ([∗ list] a ; v ∈ la ; lv, ▷ closing_resources interp W C a v) *)
  (*         ∗ ⌜if is_untrusted_caller then True else (wastk = wcs2 ∧ wastk1 = wcs3 ∧ wastk2 = wret ∧ wastk3 = wcgp0)⌝ *)
  (*         ∗ open_region_many W C la *)
  (*         ∗ sts_full_world W C *)
  (*     )%I *)
  (*     with "[Hcframe_interp Hr Hsts]" as "Hcframe_interp" *)
  (*   ; [|iDestruct "Hcframe_interp" as *)
  (*       (wastk wastk1 wastk2 wastk3) "(Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hclose_res & %Hwastks & Hr & Hsts)" *)
  (*     ]. *)


  (*   iInstr "Hcode"; try solve_pure. *)


  (*   [WriteSR mtdc ctp; Lea csp (-1)%Z; Load cgp csp; *)
  (*    Lea csp (-1)%Z; Load ca2 csp; Lea csp (-1)%Z; Load cs1 csp; Lea csp (-1)%Z; Load cs0 csp; *)
  (*    GetE ct0 csp; GetA ct1 csp] ++ *)
  (* clear_stack_instrs ct0 ct1 ++ *)
  (* encodeInstrsW [Mov cra ca2] ++ clear_registers_post_call_instrs ++ encodeInstrsW [JmpCap cra] *)




End Switcher.
