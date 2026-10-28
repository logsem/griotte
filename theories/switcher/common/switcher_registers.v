From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode.
From griotte Require Import map_simpl register_tactics.

(** * Register sets

    Splitting a register file into a fixed list of registers and the rest,
    and putting them back. The lemmas are proved once, in a small context,
    so that the switcher's proofs do not compute on register maps. *)

Section Switcher_Registers.
  Context {Σ:gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread}.

  (** ** Any list of registers *)

  (** The registers of a register file out of a list [rs] of registers, in
      order, and the rest of the file. *)
  Lemma big_sepM_extract_list (m : LReg) (rs : list RegName) :
    NoDup rs →
    (∀ r, r ∈ rs → is_Some (m !! r)) →
    (regs[th] m) ⊢
      ([∗ list] r ∈ rs, r ↦ᵣ[th] (m !!! r)) ∗ regs[th] foldr delete m rs.
  Proof.
    induction rs as [|r rs IH]; intros Hnd Hsome; first by iIntros "$".
    apply NoDup_cons in Hnd as [Hr Hnd].
    iIntros "Hm".
    iDestruct (IH with "Hm") as "[Hrs Hrest]"; [done | set_solver |].
    destruct (Hsome r ltac:(set_solver)) as [w Hw].
    iDestruct (big_sepM_delete _ _ r w with "Hrest") as "[Hr Hrest]".
    { by rewrite lookup_foldr_delete_not_elem_of. }
    rewrite big_sepL_cons (lookup_total_correct _ _ _ Hw).
    iFrame "Hr Hrs Hrest".
  Qed.

  (** ** The fifteen registers of the exception path *)

  (** The register file, after the path took fifteen registers out of
      [rmap] and gives them back. *)
  Definition regs_rebuild (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord)
    : LReg :=
    <[ca1 := wca1]> (<[ca0 := wca0]> (<[ca5 := wca5]> (<[ca4 := wca4]> (<[ca3 := wca3]>
    (<[ca2 := wca2]> (<[cs1 := wcs1]> (<[cs0 := wcs0]> (<[ct2 := wct2]> (<[ct1 := wct1]>
    (<[ct0 := wct0]> (<[ctp := wctp]> (<[cgp := wcgp]> (<[csp := wcsp]>
    (<[cra := wcra]> rmap)))))))))))))).

  Lemma regs_rebuild_full (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ r, is_Some (rmap !! r)) →
    ∀ r, is_Some (regs_rebuild rmap wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1
                    wca0 wca1 wca2 wca3 wca4 wca5 !! r).
  Proof.
    intros Hfull r. rewrite /regs_rebuild.
    repeat (rewrite lookup_insert_is_Some'; right). apply Hfull.
  Qed.

  Lemma regs_rebuild_pointsto (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (regs[th] delete ca5 (delete ca4 (delete ca3 (delete ca2 (delete ca1 (delete ca0 (delete cs1 (delete cs0 (delete ct2 (delete ct1 (delete ct0 (delete ctp (delete cgp (delete csp (delete cra rmap))))))))))))))) -∗
    cra ↦ᵣ[th] wcra -∗
    csp ↦ᵣ[th] wcsp -∗
    cgp ↦ᵣ[th] wcgp -∗
    ctp ↦ᵣ[th] wctp -∗
    ct0 ↦ᵣ[th] wct0 -∗
    ct1 ↦ᵣ[th] wct1 -∗
    ct2 ↦ᵣ[th] wct2 -∗
    cs0 ↦ᵣ[th] wcs0 -∗
    cs1 ↦ᵣ[th] wcs1 -∗
    ca0 ↦ᵣ[th] wca0 -∗
    ca1 ↦ᵣ[th] wca1 -∗
    ca2 ↦ᵣ[th] wca2 -∗
    ca3 ↦ᵣ[th] wca3 -∗
    ca4 ↦ᵣ[th] wca4 -∗
    ca5 ↦ᵣ[th] wca5 -∗
    registers_pointsto (regs_rebuild rmap wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1
                          wca0 wca1 wca2 wca3 wca4 wca5).
  Proof.
    iIntros "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
    iInsertList "Hrmap" [cra;csp;cgp;ctp;ct0;ct1;ct2;cs0;cs1;ca2;ca3;ca4;ca5;ca0;ca1].
    rewrite /registers_pointsto /regs_rebuild. iFrame.
  Qed.

  (** The fifteen registers of [error_state_regs], out of a register file
      [rmap] that maps them to [wcra], ..., [wca5]. *)
  Lemma regs_extract (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    rmap !! cra = Some wcra → rmap !! csp = Some wcsp → rmap !! cgp = Some wcgp →
    rmap !! ctp = Some wctp → rmap !! ct0 = Some wct0 → rmap !! ct1 = Some wct1 →
    rmap !! ct2 = Some wct2 → rmap !! cs0 = Some wcs0 → rmap !! cs1 = Some wcs1 →
    rmap !! ca0 = Some wca0 → rmap !! ca1 = Some wca1 → rmap !! ca2 = Some wca2 →
    rmap !! ca3 = Some wca3 → rmap !! ca4 = Some wca4 → rmap !! ca5 = Some wca5 →
    registers_pointsto rmap ⊢
      cra ↦ᵣ[th] wcra ∗
      csp ↦ᵣ[th] wcsp ∗
      cgp ↦ᵣ[th] wcgp ∗
      ctp ↦ᵣ[th] wctp ∗
      ct0 ↦ᵣ[th] wct0 ∗
      ct1 ↦ᵣ[th] wct1 ∗
      ct2 ↦ᵣ[th] wct2 ∗
      cs0 ↦ᵣ[th] wcs0 ∗
      cs1 ↦ᵣ[th] wcs1 ∗
      ca0 ↦ᵣ[th] wca0 ∗
      ca1 ↦ᵣ[th] wca1 ∗
      ca2 ↦ᵣ[th] wca2 ∗
      ca3 ↦ᵣ[th] wca3 ∗
      ca4 ↦ᵣ[th] wca4 ∗
      ca5 ↦ᵣ[th] wca5 ∗
      regs[th] delete ca5 (delete ca4 (delete ca3 (delete ca2 (delete ca1 (delete ca0 (delete cs1 (delete cs0 (delete ct2 (delete ct1 (delete ct0 (delete ctp (delete cgp (delete csp (delete cra rmap)))))))))))))).
  Proof.
    intros Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5.
    iIntros "Hrmap".
    iDestruct (big_sepM_extract_list _
                 [ca5; ca4; ca3; ca2; ca1; ca0; cs1; cs0; ct2; ct1; ct0; ctp; cgp; csp; cra]
                with "Hrmap") as "[Hregs $]".
    { by apply (bool_decide_unpack _). }
    { intros r Hr. rewrite !elem_of_cons elem_of_nil in Hr.
      repeat destruct Hr as [-> | Hr]; try done; eauto. }
    iDestruct "Hregs" as
      "(Hca5 & Hca4 & Hca3 & Hca2 & Hca1 & Hca0 & Hcs1 & Hcs0 & Hct2 & Hct1 & Hct0 & Hctp
       & Hcgp & Hcsp & Hcra & _)".
    rewrite (lookup_total_correct _ _ _ Hcra) (lookup_total_correct _ _ _ Hcsp)
      (lookup_total_correct _ _ _ Hcgp) (lookup_total_correct _ _ _ Hctp)
      (lookup_total_correct _ _ _ Hct0) (lookup_total_correct _ _ _ Hct1)
      (lookup_total_correct _ _ _ Hct2) (lookup_total_correct _ _ _ Hcs0)
      (lookup_total_correct _ _ _ Hcs1) (lookup_total_correct _ _ _ Hca0)
      (lookup_total_correct _ _ _ Hca1) (lookup_total_correct _ _ _ Hca2)
      (lookup_total_correct _ _ _ Hca3) (lookup_total_correct _ _ _ Hca4)
      (lookup_total_correct _ _ _ Hca5).
    iFrame "Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
  Qed.

  (** The register file [rmap] back from these registers, with the return
      values [w0] and [w1] in [ca0] and [ca1]. *)
  Lemma regs_insert_return_values (rmap : LReg)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca2 wca3 wca4 wca5 w0 w1 : LWord) :
    rmap !! cra = Some wcra → rmap !! csp = Some wcsp → rmap !! cgp = Some wcgp →
    rmap !! ctp = Some wctp → rmap !! ct0 = Some wct0 → rmap !! ct1 = Some wct1 →
    rmap !! ct2 = Some wct2 → rmap !! cs0 = Some wcs0 → rmap !! cs1 = Some wcs1 →
    rmap !! ca2 = Some wca2 → rmap !! ca3 = Some wca3 → rmap !! ca4 = Some wca4 →
    rmap !! ca5 = Some wca5 →
    (regs[th] delete ca5 (delete ca4 (delete ca3 (delete ca2 (delete ca1 (delete ca0 (delete cs1 (delete cs0 (delete ct2 (delete ct1 (delete ct0 (delete ctp (delete cgp (delete csp (delete cra rmap))))))))))))))) -∗
    cra ↦ᵣ[th] wcra -∗
    csp ↦ᵣ[th] wcsp -∗
    cgp ↦ᵣ[th] wcgp -∗
    ctp ↦ᵣ[th] wctp -∗
    ct0 ↦ᵣ[th] wct0 -∗
    ct1 ↦ᵣ[th] wct1 -∗
    ct2 ↦ᵣ[th] wct2 -∗
    cs0 ↦ᵣ[th] wcs0 -∗
    cs1 ↦ᵣ[th] wcs1 -∗
    ca0 ↦ᵣ[th] w0 -∗
    ca1 ↦ᵣ[th] w1 -∗
    ca2 ↦ᵣ[th] wca2 -∗
    ca3 ↦ᵣ[th] wca3 -∗
    ca4 ↦ᵣ[th] wca4 -∗
    ca5 ↦ᵣ[th] wca5 -∗
    registers_pointsto (<[ca1 := w1]> (<[ca0 := w0]> rmap)).
  Proof.
    intros Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca2 Hca3 Hca4 Hca5.
    iIntros "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
    iDestruct (regs_rebuild_pointsto with
                "Hrmap Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5")
      as "Hrmap".
    rewrite /regs_rebuild (insert_id _ _ _ Hcra) (insert_id _ _ _ Hcsp) (insert_id _ _ _ Hcgp)
      (insert_id _ _ _ Hctp) (insert_id _ _ _ Hct0) (insert_id _ _ _ Hct1)
      (insert_id _ _ _ Hct2) (insert_id _ _ _ Hcs0) (insert_id _ _ _ Hcs1)
      (insert_id _ _ _ Hca2) (insert_id _ _ _ Hca3) (insert_id _ _ _ Hca4)
      (insert_id _ _ _ Hca5).
    iExact "Hrmap".
  Qed.

  (** ** The eight registers of the call path *)

  (** The call path uses [csp], [ct2], [ctp], [cs0], [cs1], [cra], [cgp]
      and [ct1]: the register file without them, ... *)
  Definition call_regs_without (regs : LReg) : LReg :=
    delete ct1 (delete cgp (delete cra (delete cs1 (delete cs0 (delete ctp (delete ct2
      (delete csp regs))))))).

  (** ... and with them set to the given words. *)
  Definition call_regs_with (regs : LReg)
    (wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 : LWord) : LReg :=
    <[ct1 := wct1]> (<[cgp := wcgp]> (<[cra := wcra]> (<[cs1 := wcs1]> (<[cs0 := wcs0]>
      (<[ctp := wctp]> (<[ct2 := wct2]> (<[csp := wcsp]> regs))))))).

  Lemma call_regs_with_full (regs : LReg)
    (wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 : LWord) :
    (∀ r, is_Some (regs !! r)) →
    ∀ r, is_Some (call_regs_with regs wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 !! r).
  Proof.
    intros Hfull r. rewrite /call_regs_with.
    repeat (rewrite lookup_insert_is_Some'; right). apply Hfull.
  Qed.

  (** Setting the registers of the call path to their own words, except for
      [ct2] and [ctp]. *)
  Lemma call_regs_with_id (regs : LReg)
    (wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 : LWord) :
    regs !! csp = Some wcsp → regs !! cs0 = Some wcs0 → regs !! cs1 = Some wcs1 →
    regs !! cra = Some wcra → regs !! cgp = Some wcgp → regs !! ct1 = Some wct1 →
    call_regs_with regs wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 =
      <[ctp := wctp]> (<[ct2 := wct2]> regs).
  Proof.
    intros Hcsp Hcs0 Hcs1 Hcra Hcgp Hct1.
    apply map_eq; intros r. rewrite /call_regs_with.
    destruct (decide (r = ct1)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = cgp)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = cra)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = cs1)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = cs0)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = ctp)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = ct2)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = csp)) as [->|]; first by simplify_map_eq.
    by simplify_map_eq.
  Qed.

  (** Take the registers of the call path out of a register file. *)
  Lemma call_regs_extract (regs : LReg)
    (wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 : LWord) :
    regs !! csp = Some wcsp → regs !! ct2 = Some wct2 → regs !! ctp = Some wctp →
    regs !! cs0 = Some wcs0 → regs !! cs1 = Some wcs1 → regs !! cra = Some wcra →
    regs !! cgp = Some wcgp → regs !! ct1 = Some wct1 →
    registers_pointsto regs ⊢
      csp ↦ᵣ[th] wcsp ∗
      ct2 ↦ᵣ[th] wct2 ∗
      ctp ↦ᵣ[th] wctp ∗
      cs0 ↦ᵣ[th] wcs0 ∗
      cs1 ↦ᵣ[th] wcs1 ∗
      cra ↦ᵣ[th] wcra ∗
      cgp ↦ᵣ[th] wcgp ∗
      ct1 ↦ᵣ[th] wct1 ∗
      regs[th] call_regs_without regs.
  Proof.
    intros Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1.
    iIntros "Hregs".
    iDestruct (big_sepM_extract_list _ [ct1; cgp; cra; cs1; cs0; ctp; ct2; csp]
                with "Hregs") as "[Hl $]".
    { by apply (bool_decide_unpack _). }
    { intros r Hr. rewrite !elem_of_cons elem_of_nil in Hr.
      repeat destruct Hr as [-> | Hr]; try done; eauto. }
    iDestruct "Hl" as "(Hct1 & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct2 & Hcsp & _)".
    rewrite (lookup_total_correct _ _ _ Hcsp) (lookup_total_correct _ _ _ Hct2)
      (lookup_total_correct _ _ _ Hctp) (lookup_total_correct _ _ _ Hcs0)
      (lookup_total_correct _ _ _ Hcs1) (lookup_total_correct _ _ _ Hcra)
      (lookup_total_correct _ _ _ Hcgp) (lookup_total_correct _ _ _ Hct1).
    iFrame "Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1".
  Qed.

  (** Setting the registers of the call path does not depend on their
      former words. *)
  Lemma call_regs_with_without (regs : LReg)
    (wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 : LWord) :
    call_regs_with (call_regs_without regs) wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 =
      call_regs_with regs wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1.
  Proof.
    apply map_eq; intros r. rewrite /call_regs_with /call_regs_without.
    destruct (decide (r = ct1)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = cgp)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = cra)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = cs1)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = cs0)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = ctp)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = ct2)) as [->|]; first by simplify_map_eq.
    destruct (decide (r = csp)) as [->|]; first by simplify_map_eq.
    by simplify_map_eq.
  Qed.

  (** Put the registers of the call path back, with any words. *)
  Lemma call_regs_insert (regs : LReg)
    (wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1 : LWord) :
    (regs[th] call_regs_without regs) -∗
    csp ↦ᵣ[th] wcsp -∗
    ct2 ↦ᵣ[th] wct2 -∗
    ctp ↦ᵣ[th] wctp -∗
    cs0 ↦ᵣ[th] wcs0 -∗
    cs1 ↦ᵣ[th] wcs1 -∗
    cra ↦ᵣ[th] wcra -∗
    cgp ↦ᵣ[th] wcgp -∗
    ct1 ↦ᵣ[th] wct1 -∗
    registers_pointsto (call_regs_with regs wcsp wct2 wctp wcs0 wcs1 wcra wcgp wct1).
  Proof.
    iIntros "Hregs Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1".
    rewrite -call_regs_with_without /registers_pointsto /call_regs_with.
    iApply (big_sepM_insert_2 (λ k y, k ↦ᵣ y)%I with "Hct1").
    iApply (big_sepM_insert_2 (λ k y, k ↦ᵣ y)%I with "Hcgp").
    iApply (big_sepM_insert_2 (λ k y, k ↦ᵣ y)%I with "Hcra").
    iApply (big_sepM_insert_2 (λ k y, k ↦ᵣ y)%I with "Hcs1").
    iApply (big_sepM_insert_2 (λ k y, k ↦ᵣ y)%I with "Hcs0").
    iApply (big_sepM_insert_2 (λ k y, k ↦ᵣ y)%I with "Hctp").
    iApply (big_sepM_insert_2 (λ k y, k ↦ᵣ y)%I with "Hct2").
    iApply (big_sepM_insert_2 (λ k y, k ↦ᵣ y)%I with "Hcsp").
    iExact "Hregs".
  Qed.

  (** ** Registers out of a register file of known domain *)

  Lemma dom_foldr_delete (m : LReg) (rs : list RegName) :
    dom (foldr delete m rs) = dom m ∖ list_to_set rs.
  Proof.
    induction rs as [|r rs IH]; cbn; first set_solver.
    rewrite dom_delete_L IH. set_solver.
  Qed.

  (** The registers [rs] out of a register file of domain [X], with some
      words, and the rest of the file, of domain [X ∖ rs]. *)
  Lemma big_sepM_extract_dom (m : LReg) (rs : list RegName) (X : gset RegName) :
    NoDup rs →
    dom m = X →
    (∀ r, r ∈ rs → r ∈ X) →
    (regs[th] m) ⊢
      ([∗ list] r ∈ rs, ∃ w, r ↦ᵣ[th] w) ∗
      ∃ m', ⌜ dom m' = X ∖ list_to_set rs ⌝ ∗ regs[th] m'.
  Proof.
    intros Hnd Hdom Hin.
    iIntros "Hm".
    iDestruct (big_sepM_extract_list m rs with "Hm") as "[Hrs Hm]"; first done.
    { intros r Hr. apply elem_of_dom. rewrite Hdom. by apply Hin. }
    iSplitL "Hrs".
    { iApply (big_sepL_mono with "Hrs"). iIntros (k r _) "Hr". by iExists _. }
    iExists _; iFrame "Hm".
    iPureIntro. by rewrite dom_foldr_delete Hdom.
  Qed.

  (** ** The registers of the return routine *)

  (** The callee-save registers, out of a register file without the stack
      pointer and the return values. *)
  Lemma ret_callee_saved_extract (rmap : LReg) :
    dom rmap = all_registers_s ∖ {[ csp ; ca0 ; ca1 ]} →
    (regs[th] rmap) ⊢
      (∃ w, cgp ↦ᵣ[th] w) ∗
      (∃ w, cra ↦ᵣ[th] w) ∗
      (∃ w, cs0 ↦ᵣ[th] w) ∗
      (∃ w, cs1 ↦ᵣ[th] w) ∗
      ∃ rmap', ⌜ dom rmap' = all_registers_s ∖ {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        regs[th] rmap'.
  Proof.
    intros Hdom.
    iIntros "Hrmap".
    iDestruct (big_sepM_extract_dom _ [cgp; cra; cs0; cs1] with "Hrmap")
      as "[(Hcgp & Hcra & Hcs0 & Hcs1 & _) (%rmap' & %Hdom' & Hrmap)]"; [|done| |].
    { by apply (bool_decide_unpack _). }
    { intros r Hr. rewrite !elem_of_cons elem_of_nil in Hr.
      repeat destruct Hr as [-> | Hr]; try done; set_solver. }
    iFrame "Hcgp Hcra Hcs0 Hcs1 Hrmap".
    iPureIntro. rewrite Hdom'. cbn. set_solver.
  Qed.

  (** The return values, the stack pointer and the callee-save registers,
      out of a full register file. *)
  Lemma ret_regs_extract_full (rmap : LReg) (wca0 wca1 : LWord) :
    (∀ r, is_Some (rmap !! r)) →
    rmap !! ca0 = Some wca0 →
    rmap !! ca1 = Some wca1 →
    registers_pointsto rmap ⊢
      ca0 ↦ᵣ[th] wca0 ∗
      ca1 ↦ᵣ[th] wca1 ∗
      (∃ w, csp ↦ᵣ[th] w) ∗
      (∃ w, cgp ↦ᵣ[th] w) ∗
      (∃ w, cra ↦ᵣ[th] w) ∗
      (∃ w, cs0 ↦ᵣ[th] w) ∗
      (∃ w, cs1 ↦ᵣ[th] w) ∗
      ∃ rmap', ⌜ dom rmap' = all_registers_s ∖ {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        regs[th] rmap'.
  Proof.
    intros Hfull Hca0 Hca1.
    iIntros "Hrmap".
    iDestruct (big_sepM_extract_list _ [ca0; ca1] with "Hrmap")
      as "[(Hca0 & Hca1 & _) Hrmap]".
    { by apply (bool_decide_unpack _). }
    { intros r _. apply Hfull. }
    rewrite (lookup_total_correct _ _ _ Hca0) (lookup_total_correct _ _ _ Hca1).
    iDestruct (big_sepM_extract_dom _ [csp; cgp; cra; cs0; cs1] (all_registers_s ∖ {[ ca0 ; ca1 ]})
                with "Hrmap")
      as "[(Hcsp & Hcgp & Hcra & Hcs0 & Hcs1 & _) (%rmap' & %Hdom' & Hrmap)]".
    { by apply (bool_decide_unpack _). }
    { rewrite dom_foldr_delete (lregmap_full_dom _ Hfull). cbn. set_solver. }
    { intros r Hr. rewrite !elem_of_cons elem_of_nil in Hr.
      repeat destruct Hr as [-> | Hr]; try done; set_solver. }
    iFrame "Hca0 Hca1 Hcsp Hcgp Hcra Hcs0 Hcs1 Hrmap".
    iPureIntro. rewrite Hdom'. cbn. set_solver.
  Qed.

  (** The registers that the return routine uses, out of a register file
      without the callee-save registers, the stack pointer and the return
      values. *)
  Lemma ret_regs_extract (rmap : LReg) :
    dom rmap = all_registers_s ∖ {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} →
    (regs[th] rmap) ⊢
      (∃ w, ctp ↦ᵣ[th] w) ∗
      (∃ w, ct0 ↦ᵣ[th] w) ∗
      (∃ w, ct1 ↦ᵣ[th] w) ∗
      (∃ w, ct2 ↦ᵣ[th] w) ∗
      (∃ w, ca2 ↦ᵣ[th] w) ∗
      ∃ rmap', ⌜ dom rmap' = all_registers_s ∖
                   {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ; ct2 ]} ⌝ ∗
        regs[th] rmap'.
  Proof.
    intros Hdom.
    iIntros "Hrmap".
    iDestruct (big_sepM_extract_dom _ [ctp; ct0; ct1; ct2; ca2] with "Hrmap")
      as "[(Hctp & Hct0 & Hct1 & Hct2 & Hca2 & _) (%rmap' & %Hdom' & Hrmap)]"; [|done| |].
    { by apply (bool_decide_unpack _). }
    { intros r Hr. rewrite !elem_of_cons elem_of_nil in Hr.
      repeat destruct Hr as [-> | Hr]; try done; set_solver. }
    iFrame "Hctp Hct0 Hct1 Hct2 Hca2 Hrmap".
    iPureIntro. rewrite Hdom'. cbn. set_solver.
  Qed.

End Switcher_Registers.
