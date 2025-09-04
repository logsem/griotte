From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_JmpCap.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.

Section fundamental.
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

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).


  Lemma region_open_list_interp_gen (W : WORLD) (C : CmptName)
    (la la' : list Addr) (p : Perm) (g : Locality) (b e a : Addr) :
    NoDup la ->
    readAllowed p = true →
    Forall (fun a' : Addr => (b <= a' < e)%a ) la ->
    la ## la' ->

    interp W C (WCap p g b e a)
    ∗ open_region_many W C la'
    ∗ sts_full_world W C -∗

    ∃ (l : list (Word * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type)),
      open_region_many W C (la++la')
      ∗ sts_full_world W C
      ∗ ([∗ list] a ; '(v,p,φ,ρ) ∈ la ; l, sts_state_std C a ρ)
      ∗ ([∗ list] a ; '(v,p,φ,ρ) ∈ la ; l, a ↦ₐ v)
      ∗ ▷ ([∗ list] '(v,p,φ,ρ) ∈ l, monotonicity_guarantees_region C φ p v ρ)
      ∗ ▷ ([∗ list] '(v,p,φ,ρ) ∈ l, φ (W, C, v))
      ∗ ▷ ([∗ list] '(v,p,φ,ρ) ∈ l, rcond (safeUC φ) C p interp)
      ∗ ([∗ list] a ; '(v,p,φ,ρ) ∈ la ; l, rel C a p φ)
      ∗ ⌜ length l = length la ⌝
  .
  Proof.
    induction la; intros Hnodup Hp Hin Hdis ;
      iIntros "(#Hinterp & Hr & Hsts)"; cbn in * |- *.
    - iExists []; cbn in *.
      by iFrame.
    - apply Forall_cons in Hin; destruct Hin as [Hin_a0 Hin].
      apply list.NoDup_cons in Hnodup; destruct Hnodup as [Hnotin Hnodup].
      pose proof (disjoint_cons _ _ _ Hdis) as Ha_notin_l'.
      eapply disjoint_weak in Hdis.
      iDestruct (IHla with "[$Hinterp $Hr $Hsts]") as "IH"; eauto.
      iDestruct "IH" as (lv) "(Hr & Hsts & Hsts_stds & Hlv & Hmono & Hlφ & Hrcond & Hrel & %Hlen)".
      iDestruct (read_allowed_inv _ _ a0 with "Hinterp")
        as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hrcond_P & Hwcond_P & HmonoV)"
      ; auto.
      iDestruct (readAllowed_valid_cap_implies with "Hinterp") as (ρ) "[%HWa %Hρ]"; auto.
      { by eapply withinBounds_true_iff. }
      iDestruct (region_open_next with "[$Hr $Hrel_P $Hsts]") as "Ha"; eauto.
      {
        intros Hcontra.
        apply elem_of_app in Hcontra. destruct Hcontra as [Hcontra|Hcontra]
        ; [set_solver+Hcontra Hnotin|set_solver+Hcontra Ha_notin_l'].
      }
      iDestruct "Ha" as (va) "(Hsts & Hsts_std_a & Hr & Hv_a & Hmono_a & Hφ_a & %Hp_a)".
      iExists ((va, p', safeC P, ρ)::lv).
      iFrame "∗#".
      iPureIntro ; cbn ; lia.
  Qed.

  Lemma region_open_list_interp (W : WORLD) (C : CmptName)
    (la' : list Addr) (p : Perm) (g : Locality) (b e a : Addr) :
    let la := finz.seq_between b e in
    readAllowed p = true →
    la ## la' ->

    interp W C (WCap p g b e a)
    ∗ open_region_many W C la'
    ∗ sts_full_world W C -∗

    ∃ (l : list (Word * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type)),
      open_region_many W C (la++la')
      ∗ sts_full_world W C
      ∗ ([∗ list] a ; '(v,p,φ,ρ) ∈ la ; l, sts_state_std C a ρ)
      ∗ ([∗ list] a ; '(v,p,φ,ρ) ∈ la ; l, a ↦ₐ v)
      ∗ ▷ ([∗ list] '(v,p,φ,ρ) ∈ l, monotonicity_guarantees_region C φ p v ρ)
      ∗ ▷ ([∗ list] '(v,p,φ,ρ) ∈ l, φ (W,C,v))
      ∗ ▷ ([∗ list] '(v,p,φ,ρ) ∈ l, rcond (safeUC φ) C p interp)
      ∗ ([∗ list] a ; '(v,p,φ,ρ) ∈ la ; l, rel C a p φ)
      ∗ ⌜ length l = length la ⌝
  .
  Proof.
    iIntros (la Hp Hdis).
    iApply region_open_list_interp_gen; eauto; subst la.
    - apply finz_seq_between_NoDup.
    - apply Forall_forall ; intros.
      by apply elem_of_finz_seq_between.
  Qed.

  Definition closing_resources W C a w : iProp Σ :=
    ∃ φ p ρ,
      (sts_state_std C a ρ
       ∗ (φ (W, C, w))
       ∗ (monotonicity_guarantees_region C φ p w ρ)
       ∗ rcond (safeUC φ) C p interp
       ∗ rel C a p φ)%I.

  Lemma closing_resources_interp W C a w :
    closing_resources W C a w -∗ interp W C w.
    iIntros "H".
    iDestruct "H" as (???) "(Hstd&Hφ&Hmono&Hrcond&Hrel)".
    destruct p.
    destruct dl,dro; by iApply "Hrcond".
  Qed.

  Lemma switcher_return_ftlr (W : WORLD) (C : CmptName) (rmap : leibnizO Reg)
    (cstk : CSTK) (wstk : Word)
    (Nswitcher : namespace)
    :
    (∀ x, is_Some (rmap !! x)) ->
    rmap !! csp = Some wstk ->
    ftlr_IH -∗
    (∀ (r : RegName) (v : leibnizO Word) , ⌜r ≠ PC⌝ → ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    na_inv logrel_nais Nswitcher switcher_inv -∗
    interp_continuation cstk W C -∗
    sts_full_world W C -∗
    na_own logrel_nais ⊤ -∗
    cstack_frag cstk -∗
    ([∗ map] k↦y ∈ <[PC:=WCap XSRW_ Local b_switcher e_switcher a_switcher_return]> rmap , k ↦ᵣ y) -∗
    region W C -∗
    ▷ (£ 1 -∗ WP Seq (Instr Executable) {{ v0, ⌜v0 = HaltedV⌝ → na_own logrel_nais ⊤ }}).
  Proof.
    iIntros (Hfull_rmap Hwstk) "#IH #Hrmap_interp #Hinv_switcher Hcont_K Hsts Hna Hcstk Hrmap Hr".
    iNext; iIntros "_".

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    (* --- Extract scratch registers ct2 ctp --- *)
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    rewrite delete_insert_delete.
    assert (exists wcra, rmap !! cra = Some wcra)
      as [wcra Hwcra] by (by specialize (Hfull_rmap cra)).
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    assert (exists wcsp, rmap !! csp = Some wcsp)
      as [wcsp Hwcsp] by (by specialize (Hfull_rmap csp)).
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    assert (exists wcgp, rmap !! cgp = Some wcgp)
      as [wcgp Hwcgp] by (by specialize (Hfull_rmap cgp)).
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    assert (exists wca0, rmap !! ca0 = Some wca0)
      as [wca0 Hwca0] by (by specialize (Hfull_rmap ca0)).
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert (exists wca1, rmap !! ca1 = Some wca1)
      as [wca1 Hwca1] by (by specialize (Hfull_rmap ca1)).
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap !! ctp = Some wctp)
      as [wctp Hwctp] by (by specialize (Hfull_rmap ctp)).
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    assert (exists wca2, rmap !! ca2 = Some wca2)
      as [wca2 Hwca2] by (by specialize (Hfull_rmap ca2)).
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs1, rmap !! cs1 = Some wcs1)
      as [wcs1 Hwcs1] by (by specialize (Hfull_rmap cs1)).
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs0, rmap !! cs0 = Some wcs0)
      as [wcs0 Hwcs0] by (by specialize (Hfull_rmap cs0)).
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert (exists wct0, rmap !! ct0 = Some wct0)
      as [wct0 Hwct0] by (by specialize (Hfull_rmap ct0)).
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert (exists wct1, rmap !! ct1 = Some wct1)
      as [wct1 Hwct1] by (by specialize (Hfull_rmap ct1)).
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.


    (* ------------------------------------------------ *)
    (* ----- Start the proof of the switcher here ----- *)
    (* ------------------------------------------------ *)
    iAssert (interp W C wcsp) as "#Hinterp_wcsp".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wcs0) as "#Hinterp_wcs0".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wcs1) as "#Hinterp_wcs1".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wcra) as "#Hinterp_wcra".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wcgp) as "#Hinterp_wcgp".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wct1) as "#Hinterp_wct1".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wca0) as "#Hinterp_wca0".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wca1) as "#Hinterp_wca1".
    { iApply "Hrmap_interp"; eauto; done. }

    rewrite /switcher_instrs /switcher_call_instrs /switcher_return_instrs.
    rewrite -!app_assoc.

    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }
    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.
    focus_block_nochangePC 6 "Hcode" as a5 Ha5 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a5 = a_switcher_return); [|simplify_eq].
    { cbn in Ha5.
      clear -Ha5.
      pose proof switcher_return_entry_point as Hret; cbn in Hret.
      pose proof switcher_call_entry_point as Hcall; cbn in Hcall.
      solve_addr.
    }

    rewrite /interp_continuation /interp_cont.
    (* ReadSR ctp mtdc *)
    iInstr "Hcode" with "Hlc".

    iDestruct (cstack_agree with "[$] [$]") as "%"; simplify_eq.
    destruct cstk as [|frm cstk]; iEval (cbn) in "Hstk_interp"; cbn in Hlen_cstk.
    replace a_tstk with (b_trusted_stack ^+ (-1))%a by solve_addr.
    { (* the stack is empty, it will fail *)
      admit. (* Loading fails *)
    }
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp & %Ha_tstk1)".
    destruct Ha_tstk1 as [a_tstk1 Ha_tstk1].
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as (wtstk4) "[Ha_tstk Hcframe_interp]".
    destruct wstk0; try done.
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

    iDestruct "Hcont_K" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".
    iEval (cbn) in "Hinterp_callee_wstk".
    iDestruct (lc_fupd_elim_later with "[$] [$Hinterp_callee_wstk]") as ">#Hinterp_callee_wstk'".
    iClear "Hinterp_callee_wstk" ; iRename "Hinterp_callee_wstk'" into "Hinterp_callee_wstk".

    iAssert (
        ∃ wastk wastk1 wastk2 wastk3,
          a_stk ↦ₐ wastk
          ∗ (a_stk ^+ 1)%a ↦ₐ wastk1
          ∗ (a_stk ^+ 2)%a ↦ₐ wastk2
          ∗ (a_stk ^+ 3)%a ↦ₐ wastk3
          ∗ (if is_untrusted_caller
             then
               ▷ (closing_resources W C a_stk wastk
               ∗ closing_resources W C (a_stk ^+ 1)%a wastk1
               ∗ closing_resources W C (a_stk ^+ 2)%a wastk2
               ∗ closing_resources W C (a_stk ^+ 3)%a wastk3)
             else (⌜ wastk = wcs2 ⌝ ∗ ⌜ wastk1 = wcs3 ⌝ ∗ ⌜ wastk2 = wret ⌝ ∗ ⌜ wastk3 = wcgp0 ⌝)
            )
          ∗ open_region_many W C (if is_untrusted_caller then [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a] else [])
          ∗ sts_full_world W C
      )%I
      with "[Hcframe_interp Hr Hsts]" as "Hcframe_interp"
    ; [|iDestruct "Hcframe_interp" as
        (wastk wastk1 wastk2 wastk3) "(Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hwstk & Hr & Hsts)"
      ].
    {
      destruct is_untrusted_caller; cycle 1.
      * iExists wcs2, wcs3, wret, wcgp0.
        rewrite region_open_nil; iFrame "Hr Hsts".
        by iDestruct "Hcframe_interp" as "($&$&$&$)".
      * rewrite region_open_nil.


        iDestruct (region_open_list_interp_gen _ _ (finz.seq_between a_stk (a_stk^+4)%a)
                    with "[$Hinterp_callee_wstk $Hr $Hsts]")
          as (l) "(Hr & Hsts & Hstd & Hv & Hmono & Hφ & Hrcond & Hrel & %Hlen_l)"; auto.
        { eapply finz_seq_between_NoDup. }
        { clear-He_a1 ; apply Forall_forall; intros a' Ha'.
          apply elem_of_finz_seq_between in Ha'; solve_addr.
        }
        { set_solver. }
        cbn in Hlen_l.
        do 4 (rewrite finz_seq_between_cons in Hlen_l; last solve_addr+He_a1).
        rewrite finz_seq_between_empty in Hlen_l; last solve_addr+.
        cbn in Hlen_l.
        destruct l as [| [ [ [wastk0 p0] φ0] ρ0] l]; first (by cbn in Hlen_l).
        destruct l as [| [ [ [wastk1 p1] φ1] ρ1] l]; first (by cbn in Hlen_l).
        destruct l as [| [ [ [wastk2 p2] φ2] ρ2] l]; first (by cbn in Hlen_l).
        destruct l as [| [ [ [wastk3 p3] φ3] ρ3] l]; first (by cbn in Hlen_l).
        destruct l as [|]; last (by cbn in Hlen_l).
        do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1).
        rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+.
        cbn.
        replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4.
        replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4.
        iDestruct "Hv" as "($&$&$&$&_)".
        iFrame.
        iDestruct "Hrcond" as "(Hrcond_0 & Hrcond_1 & Hrcond_2 & Hrcond_3 & _)".
        iDestruct "Hrel" as "(Hrel_0 & Hrel_1 & Hrel_2 & Hrel_3 & _)".
        iDestruct "Hφ" as "(Hφ_0 & Hφ_1 & Hφ_2 & Hφ_3 & _)".
        iDestruct "Hmono" as "(Hmono_0 & Hmono_1 & Hmono_2 & Hmono_3 & _)".
        iDestruct "Hstd" as "(Hstd_0 & Hstd_1 & Hstd_2 & Hstd_3 & _)".
        rewrite /closing_resources.
        iFrame.
    }

    destruct (decide (a_tstk < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    (* Load csp ctp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    rewrite -/(interp_cont).
    iEval (cbn) in "Hinterp_callee_wstk".

    (* Lea ctp (-1)%Z *)
    iInstr "Hcode".
    (* WriteSR mtdc ctp *)
    iInstr "Hcode".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 3)%a); solve_addr+Ha_stk4. }
    (* Load cgp csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcgp".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. }
    (* Load ca2 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hca2".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. }
    (* Load cs1 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcs1".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk); solve_addr. }
    (* Load cs0 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcs0".
    (* GetE ct0 csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.



    iDestruct (region_open_list_interp_gen _ _ (finz.seq_between (a_stk^+4)%a e_stk)
                with "[$Hinterp_callee_wstk $Hr $Hsts]")
      as (l) "(Hr & Hsts & Hstd & Hv & Hmono & Hφ & Hrcond & Hrel & %Hlen_l)"; auto.
    { eapply finz_seq_between_NoDup. }
    { clear-He_a1 ; apply Forall_forall; intros a' Ha'.
      apply elem_of_finz_seq_between in Ha'.
      destruct is_untrusted_caller; solve_addr.
    }
    {
      destruct is_untrusted_caller; last set_solver.
      set (la := finz.seq_between (a_stk ^+ 4)%a e_stk).
      assert ( a_stk ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 1)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 2)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 3)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      set_solver.
    }
    set (lv := map (fun x => let '(v, _, _, _) := x in v) l).

    iAssert ([[ a_stk , e_stk ]] ↦ₐ [[wastk :: wastk1 :: wastk2 :: wastk3 :: lv]])%I
      with "[Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hv]" as "Hstk".
    {
      iAssert ([[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ lv ]])%I with "[Hv]" as "Hstk".
      { admit. (* should be fairly easy, just projections *) }
      iDestruct (region_pointsto_cons with "[$Ha_stk3 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk2 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iFrame.
    }
    focus_block 7 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto; [solve_addr|].
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 8 "Hcode" as a8 Ha8 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cra ca2 *)
    iInstr "Hcode" with "Hlc".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

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

    focus_block 10 "Hcode" as a10 Ha10 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* JmpCap cra *)
    iInstr "Hcode" with "Hlc".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* TODO close the region *)

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
      clear -Hot_bounds Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Ha_tstk1.
      repeat (iSplit ;[iPureIntro; try solve_addr|]); [|iPureIntro; try solve_addr].
      split; last solve_addr.
      admit. (* TODO is this true? *)
    }

    (* Use the continuation *)
    pose proof (related_sts_pub_refl_world W) as Hpub_W.
    iSpecialize ("Hexec_topmost_frm" $! W Hpub_W).
    rewrite /interp_cont_exec.
    iEval (cbn) in "Hexec_topmost_frm".
    iAssert ([∗ map] r↦w ∈ arg_rmap', r ↦ᵣ WInt 0)%I with "[Harg_rmap']" as "Hrmap".
    { admit. (* easy *) }

    destruct is_untrusted_caller.
    - (* Case where caller is untrusted, we use the IH *)

      destruct ( decide (isCorrectPC (updatePcPerm wastk2))) as [HcorrectWret|HcorrectWret]; cycle 1.
      { (* The PC is not correct, the execution will crash *)
            iApply (wp_bind (fill [SeqCtx])).
            iApply (wp_notCorrectPC with "HPC"); first done.
            iNext; iIntros "HPC /=".
            iApply wp_pure_step_later; auto; iNext; iIntros "_".
            iApply wp_value; iIntros; discriminate.
      }
      (* The PC is correct, we can use the continuation*)
      iDestruct "Hlc" as "[Hlc Hlc']".
      iDestruct (lc_fupd_elim_later with "[$Hlc'] [$Hwstk]") as ">Hwstk".
      iDestruct "Hwstk" as "(Hclose_wastk & Hclose_wastk1 & Hclose_wastk2 & Hclose_wastk3)".

      iDestruct (closing_resources_interp with "Hclose_wastk") as "#Hinterp_wastk".
      iDestruct (closing_resources_interp with "Hclose_wastk1") as "#Hinterp_wastk1".
      iDestruct (closing_resources_interp with "Hclose_wastk2") as "#Hinterp_wastk2".
      iDestruct (closing_resources_interp with "Hclose_wastk3") as "#Hinterp_wastk3".

      iAssert (
          ∃ rmap', ⌜ dom rmap' = dom arg_rmap' ⌝ ∗ ([∗ map] r↦w ∈ rmap', r ↦ᵣ w)
                   ∗ (∀ (r : RegName) (v : leibnizO Word), ⌜r ≠ PC⌝ → ⌜rmap' !! r = Some v⌝ → interp W C v)
        )%I with "[Hrmap]" as (rmap') "(%Hdom_rmap' & Hrmap & #Hrmap_interp')".
      {
        iExists (fmap (fun v => WInt 0) arg_rmap').
        iSplit ; [iPureIntro; apply dom_fmap_L|].
        iSplitL.
        { admit. (* this clearly holds *) }
        iIntros (r w HrPC Hr).
        rewrite lookup_fmap_Some in Hr.
        destruct Hr as (? & <- & Hr').
        iEval (rewrite fixpoint_interp1_eq); done.
      }

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cra m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcra]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cgp m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcgp]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete ca0 m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca0]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete ca1 m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca1]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cs0 m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs0]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cs1 m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs1]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete csp m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcsp]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete PC m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $HPC]") as "Hrmap".

      destruct wastk2 as [ z | [p g b e a|]  | p g b e a | ot sb ] ; iEval (cbn) in "Hrmap".
      all: cbn in HcorrectWret.
      all: inversion HcorrectWret; simplify_eq.
      + (* wret was a regular capability: apply the IH *)
        iApply ("IH" with "[] [] [$] [] [Hr] [$Hsts] [$Hcont_K] [$Hna] [$Hcstk_frag] [$]").
        { admit. (* easy *) }
        {
          iIntros (r rv HrPC Hr).
          destruct (decide (r = csp)); simplify_map_eq.
          { admit. (* doable, but tedious *) }
          destruct (decide (r = cs1)); simplify_map_eq; first done.
          destruct (decide (r = cs0)); simplify_map_eq; first done.
          destruct (decide (r = ca1)); simplify_map_eq; first done.
          destruct (decide (r = ca0)); simplify_map_eq; first done.
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          iApply "Hrmap_interp'"; eauto.
          iPureIntro.
          rewrite lookup_delete_ne; eauto.
        }
        { iPureIntro; simplify_map_eq; done. }
        { admit. (* just close the region *) }

      + (* wret was a sentry capability: apply the def of safe for sentry *)
        iAssert (interp W C (WSentry p g b e a)) as "#Hinterp_wret'" ; first done.
        iEval (rewrite fixpoint_interp1_eq /=) in "Hinterp_wastk2".
        destruct ( is_switcher_entry_point p g b e a ) eqn:Hwret_is_switcher_entry_point.
        (* The caller had changed the `wret` into one of the switcher's entry point.... *)
        * admit. (* TODO I need an inductive case *)
        * iDestruct "Hinterp_wastk2" as "#Hinterp_wret".
          rewrite /enter_cond.
          iAssert (future_world g W W) as "-#Hfuture".
          { destruct g; cbn; iPureIntro
            ; [apply related_sts_priv_refl_world| apply related_sts_pub_refl_world].
          }
          iSpecialize ("Hinterp_wret" $! cstk (WCap RWL Local b_stk e_stk a_stk) W with "[$]").
          iDestruct "Hinterp_wret" as "[Hinterp_wret _]".
          iDestruct (lc_fupd_elim_later with "[$] [$Hinterp_wret]") as ">Hinterp_wret".
          rewrite /interp_expr /=.
          iDestruct ("Hinterp_wret" with "[$Hcont_K $Hrmap Hr $Hsts $Hcstk_frag $Hna]") as "HA"; eauto.
          iSplitR.
          { iSplit.
            - admit. (* easy *)
            -
              iIntros (r rv HrPC Hr).
              destruct (decide (r = csp)); simplify_map_eq.
              { admit. (* doable, but tedious *) }
              destruct (decide (r = cs1)); simplify_map_eq; first done.
              destruct (decide (r = cs0)); simplify_map_eq; first done.
              destruct (decide (r = ca1)); simplify_map_eq; first done.
              destruct (decide (r = ca0)); simplify_map_eq; first done.
              destruct (decide (r = cgp)); simplify_map_eq; first done.
              destruct (decide (r = cra)); simplify_map_eq; first done.
              iApply "Hrmap_interp'"; eauto.
              iPureIntro.
              rewrite lookup_delete_ne; eauto.
          }
          iSplitR.
          { iPureIntro; simplify_map_eq; done. }
          { admit. (* just close the region *) }

    - (* Case where caller is trusted, we use the continuation *)
      iDestruct "Hwstk" as "(-> & -> & -> & ->)".
      iApply ("Hexec_topmost_frm" with
               "[$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_wca0 $Hinterp_wca1
      $Hrmap Hr $Hsts $Hcont_K $Hcstk_frag $Hna]").
      iSplitL;[iPureIntro|].
      rewrite Harg_rmap'; set_solver.
      (* Should be done with closing the region *)
      admit.

  Admitted.


End fundamental.
