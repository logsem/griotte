From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import logrel logrel_extra.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From cap_machine Require Export world_ghost_theory world_ghost_theory_interface.
From cap_machine Require Import switcher_preamble.

Section switcher_helper.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* TODO Move the lemmas into a helper file for switcher spec *)

  (* TODO the following seems like it's always used in sequence with
    [decompose_opening_to_closing_resources],
    so maybe they should be put together somehow!! *)
  Lemma open_world_interp_opening_resources (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) la ->
    la ## la' ->

    interp W C (WCap RWL g b e a)
    ∗ world_interp_open W C la'
      -∗

    world_interp_open W C (la++la')
    ∗ ([∗ list] a ∈ la, opening_resources interp W C a)
  .
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "(#Hinterp & [Hr Hsts] )"; cbn in * |- *.
    iDestruct (region_open_list_interp_gen _ _ _ _
                with "[$Hinterp $Hr $Hsts]") as "[$ $]"; eauto.
  Qed.

  Lemma close_world_interp_opening_resources (W : WORLD) (C : CmptName)
  (lv : list Word)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    world_interp_open W C (la++la')
    ∗ ([∗ list] a ; v ∈ la ; lv, a ↦ₐ v ∗ closing_resources interp W C a v)
    -∗ world_interp_open W C la'.
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "([Hr Hsts] & Hres )"; cbn in * |- *.
    iDestruct (region_close_list_interp_gen with "[$Hres $Hr]") as "$"; eauto.
  Qed.

  Lemma world_interp_reinstate_stack  E W C la lv :
    NoDup la →
    Forall (eq (WInt 0)) lv ->

    world_interp W C -∗
    ([∗ list] a;v ∈ la;lv ,
       (closing_revoked_resources W C a
        ∗ ⌜(std W) !! a = Some Revoked ⌝)
       ∗ a ↦ₐ v
    )

    ={E}=∗

    world_interp (std_update_multiple W la Temporary) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (??) "[Hr Hsts] Hres".
    iMod (update_region_revoked_temp_pwl_multiple'
           with "Hsts Hr [$Hres]") as "[ $ $ ]"; eauto.
  Qed.

  (* TODO This theorem is essentially [revoke_world], but with different RevokedResources *)
  Lemma world_interp_revoke_keep W C l :
    NoDup l ->
    ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝)
    ∗ world_interp W C
    ==∗
    world_interp (revoke W) C
    ∗ close_list_resources C W l true
    ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (Hdup) "(Hl & [Hr Hsts] )".
    iMod ( monotone_revoke_keep _ _ l with "[$Hr $Hsts Hl]") as
      "($ & $ & $ & $)"; auto.
  Qed.

  (* TODO This theorem is essentially [reinstate_world], but with different RevokedResources *)
  Lemma reinstate_close_list_gen W C (l : list Addr) :
    ⊢ world_interp W C
    ∗ close_list_resources_gen C W l l false
    ==∗
    world_interp (reinstate W l) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "([Hr Hsts] & Htemp)".
    iMod (monotone_close_list_region_gen W W _ l with "[$Hr $Hsts $Htemp]") as "[Hsts Hr]"; iFrame.
    done.
  Qed.

  (* TODO USED IN INTERP RETURN *)
  Lemma open_world_interp_cframe
    (W : WORLD) (C : CmptName) (b_stk e_stk a_stk a_stk4 : Addr)
    (wret wcgp0 wcs2 wcs3 : Word) (ccrel : caller_callee_relation)
    :
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->
    (a_stk + 4)%a = Some a_stk4 ->

    interp W C (WCap RWL Local (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) e_stk a_stk) ∗
    cframe_stk_own {|
        wret := wret;
        wcgp := wcgp0;
        wcs0 := wcs2;
        wcs1 := wcs3;
        b_stk := b_stk;
        a_stk := a_stk;
        e_stk := e_stk;
        ccrel := ccrel
      |}
    ∗ world_interp W C
      -∗
    ∃ wastk wastk1 wastk2 wastk3,
      let la := (if (is_untrusted_caller ccrel) then finz.seq_between a_stk (a_stk ^+ 4)%a else []) in
      let lv := (if (is_untrusted_caller ccrel) then [wastk;wastk1;wastk2;wastk3] else []) in
      a_stk ↦ₐ wastk
      ∗ (a_stk ^+ 1)%a ↦ₐ wastk1
      ∗ (a_stk ^+ 2)%a ↦ₐ wastk2
      ∗ (a_stk ^+ 3)%a ↦ₐ wastk3
      ∗ ▷ ([∗ list] a ; v ∈ la ; lv, ▷ closing_resources interp W C a v)
      ∗ ⌜if (is_untrusted_caller ccrel) then True else (wastk = wcs2 ∧ wastk1 = wcs3 ∧ wastk2 = wret ∧ wastk3 = wcgp0)⌝
                                                    ∗ world_interp_open W C la.
  Proof.
    iIntros (Hb_a4 He_a1 Ha_stk4) "(#Hinterp_callee_wstk & Hcframe_interp & Hworld_interp)".

    rewrite /cframe_stk_own /= /is_untrusted_caller_frm; cbn.
    destruct (is_untrusted_caller ccrel); cycle 1.
    * iExists wcs2, wcs3, wret, wcgp0.
      iEval (rewrite -open_empty) in "Hworld_interp"; iFrame "Hworld_interp".
      iDestruct "Hcframe_interp" as "($&$&$&$)".
      cbn.
      iSplit;first done.
      iPureIntro.
      repeat (split;auto).
    * iEval (rewrite -open_empty) in "Hworld_interp".
      iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between a_stk (a_stk^+4)%a)
                  with "[$Hinterp_callee_wstk $Hworld_interp]")
        as "(Hworld_interp & Hres)"; auto.
      { eapply finz_seq_between_NoDup. }
      { clear- Hb_a4 He_a1 ; apply Forall_forall; intros a' Ha'.
        apply elem_of_finz_seq_between in Ha'; solve_addr.
      }
      { set_solver. }
      do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1).
      rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+.
      cbn.
      replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4.
      replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4.
      cbn.
      iDestruct "Hres" as "(Hres0 & Hres1 & Hres2 & Hres3 & _)".
      iDestruct (opening_closing_resources with "Hres0") as (wastk) "[Hres0 $]".
      iDestruct (opening_closing_resources with "Hres1") as (wastk1) "[Hres1 $]".
      iDestruct (opening_closing_resources with "Hres2") as (wastk2) "[Hres2 $]".
      iDestruct (opening_closing_resources with "Hres3") as (wastk3) "[Hres3 $]".
      iFrame.
  Qed.

  Lemma decompose_opening_to_closing_resources W C la :
    ([∗ list] a ∈ la, opening_resources interp W C a) -∗
    (∃ (lv : list Word),
        ⌜ length lv = length la ⌝
        ∗ ▷ ([∗ list] a ; v ∈ la; lv, closing_resources interp W C a v)
        ∗ ([∗ list] a ; v ∈  la ; lv, a ↦ₐ v)
    ).
  Proof.
    induction la; cbn; iIntros "Hres".
    - iExists []; cbn; done.
    - iDestruct "Hres" as "[Ha Hres]".
      iDestruct (IHla with "Hres") as (lv) "(%Hlen & Hres & Hlv)".
      iDestruct ( opening_closing_resources with "Ha" ) as (va) "[Hres_a Ha]".
      iExists (va::lv).
      iFrame.
      iPureIntro ; cbn ; lia.
  Qed.

  (* TODO any way to generalize? Or would it be worth re-inlining?? *)
  (* TODO isn't it JUST open_world_interp_opening_resources + decompose_opening_to_closing_resources ?? *)

  Lemma open_world_interp_callee_stack (W : WORLD) (C : CmptName) (b_stk e_stk a_stk a_stk4 : Addr)
    ccrel
    :
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->
    (a_stk + 4)%a = Some a_stk4 ->
    let l_register_save_area :=
      (if is_untrusted_caller ccrel
       then finz.seq_between a_stk (a_stk ^+ 4)%a
       else [])
    in
    let l_callee_stack_frame := finz.seq_between (a_stk ^+ 4)%a e_stk in

    interp W C (WCap RWL Local (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) e_stk a_stk) ∗
    world_interp_open W C l_register_save_area
    -∗

    world_interp_open W C (l_callee_stack_frame ++ l_register_save_area) ∗
    (∃ (lv : list Word),
        ⌜ length lv = length l_callee_stack_frame ⌝
        ∗ ([∗ list] a ; v ∈ l_callee_stack_frame ; lv, a ↦ₐ v)
        (* TODO following resources is (only) used by closing_resources_zeros,
           and in closing_resources_zeros' + close_world_interp_opening_resources,
           and is (essentially!) generated from open_world_interp_opening_resources...
           Any ways to makes that look better ??
         *)
        ∗ ▷ ([∗ list] a ; v ∈ l_callee_stack_frame ; lv, closing_resources interp W C a v)
    )
  .
  Proof.
    iIntros (Hb_a4 He_a1 Ha_stk4)
      "(Hinterp_callee_wstk & Hworld_interp)".
    iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between (a_stk^+4)%a e_stk)
                with "[$Hinterp_callee_wstk $Hworld_interp]")
      as "($ & Hres)"; auto.
    { eapply finz_seq_between_NoDup. }
    { clear- Hb_a4 He_a1 ; apply Forall_forall; intros a' Ha'.
      apply elem_of_finz_seq_between in Ha'.
      rewrite /is_untrusted_caller_frm; cbn.
      destruct (is_untrusted_caller ccrel); solve_addr.
    }
    {
      destruct (is_untrusted_caller ccrel); last set_solver.
      set (la := finz.seq_between (a_stk ^+ 4)%a e_stk).
      assert ( a_stk ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 1)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 2)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 3)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1).
      rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+.
      replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4.
      replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4.
      set_solver.
    }
    iDestruct (decompose_opening_to_closing_resources with "Hres") as "(%&$&$&$)".
  Qed.


  (* TODO The result matches the excepted shape for E_K *)
  Lemma closing_resources_zeros (W : WORLD) (C : CmptName) (b e : Addr) (lv : list Word) :
    let lv' := region_addrs_zeroes b e in
    length lv = length (finz.seq_between b e) ->
    Forall (λ y : Word, y = WInt 0) lv' ->
    ([∗ list] a;v ∈ finz.seq_between b e;lv, closing_resources interp W C a v) -∗
    ([∗ list] a;v ∈ finz.seq_between b e;lv', closing_resources interp W C a v)
  .
    intros lv'.
    iIntros (Hlen_lv Hlv') "Hres".
    iAssert (([∗ list] a ∈ finz.seq_between b e, closing_resources interp W C a (WInt 0)))%I
      with "[Hres]" as "Hres".
    {
      iClear "#".
      clear -Hlen_lv.
      iStopProof.
      revert Hlen_lv.
      generalize dependent lv.
      generalize (finz.seq_between b e) as la.
      induction la; iIntros (lv Hlen) "H"; destruct lv as [|v lv]; simplify_eq; cbn; first done.
      iDestruct "H" as "[Ha H]".
      iDestruct (closing_resources_zeroed with "Ha") as "$".
      by iApply (IHla with "H").
    }
    rewrite /region_pointsto.
    iApply big_sepL2_replicate_r; auto.
    by rewrite finz_seq_between_length.
  Qed.

  (* TODO note the slight difference from above: contains a ↦ₐ v *)
  Lemma closing_resources_zeros' (W : WORLD) (C : CmptName) (b e : Addr) (lv : list Word) :
    let lv' := region_addrs_zeroes b e in
    length lv = length (finz.seq_between b e) ->
    Forall (λ y : Word, y = WInt 0) lv' ->
    ([∗ list] a;v ∈ finz.seq_between b e;lv, closing_resources interp W C a v) ∗
    [[b,e]]↦ₐ[[lv']]
    -∗
    ([∗ list] a;v ∈ finz.seq_between b e;lv', a ↦ₐ v ∗ closing_resources interp W C a v)
  .
    intros lv'.
    iIntros (Hlen_lv Hlv') "(Hres & Hstk)".
    rewrite /region_pointsto.
    iStopProof.
    assert (length lv' = length (finz.seq_between b e)) as Hlen_lv'.
    { subst lv'. by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }
    revert Hlen_lv Hlen_lv' Hlv'.
    generalize dependent lv.
    generalize dependent lv'.
    generalize (finz.seq_between b e) as la.
    induction la; iIntros (lv' lv Hlen' Hlen Hlv') "H"
    ; destruct lv as [|v lv]; simplify_eq; cbn
    ; destruct lv' as [|v' lv']; simplify_eq; cbn
    ; first done.
    iDestruct "H" as "[ [Hclose Hres] [Ha H] ]"; iFrame.
    apply Forall_cons in Hlv' ; destruct Hlv' as [-> Hlv'].
    iDestruct (closing_resources_zeroed with "Hclose") as "$".
    iApply (IHla with "[Hres H]"); last iFrame; eauto.
  Qed.


End switcher_helper.
