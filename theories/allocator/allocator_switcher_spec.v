From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import switcher_spec_KtK register_tactics map_simpl region_keys.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec.

(** The public specifications of [malloc] and [free]: calls through the
    switcher from a known caller (§4.8). They take the same ghost resources as
    the functional specifications, with generic resources only. The argument
    is in [ca0] (D36). The callers carry no register condition: the
    switcher-entry facts (the non-argument registers are zero, the stack and
    return capabilities carry no identifier) discharge the allocator-entry
    condition of the functional [free] (D23). *)

Section AllocatorSwitcherSpec.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {FA : FreeAuth Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}.

  (** The results of [malloc n]: exhaustion, or a fresh object [ι ∉ S] of
      [n] zeroed cells. *)
  Definition allocator_malloc_result (S : gset AId) (n : Z) (w0 w1 : LWord) : iProp Σ :=
    (⌜w0 = WInt ALLOC_NO_MEMORY ∧ w1 = WInt 0⌝ ∨
     (∃ (ι : AId) (b e : Addr),
       ⌜(heap_b < b /\ b < e /\ e <= heap_e)%a ∧ (e - b = n)%Z⌝ ∗
       ⌜ι ∉ S⌝ ∗
       ⌜w0 = WCap true RW Global b e b @@ ι ∧ w1 = WInt 0⌝ ∗
       alloc_obj ι b e ∗
       free_auth_held ι ∗
       [[b, e]] ↦ₕ[ι] [[region_addrs_zeroes b e]]))%I.

  Lemma allocator_malloc_switcher_spec
    (S : gset AId) (n : Z)
    (wcgp wcra wcs0 wcs1 : LWord)
    (b_stk e_stk a_stk : Addr) (arg_rmap : LReg) (cstk : CSTK) :
    (0 < n)%Z ->
    arg_rmap !! ca0 = Some (lword_of_word (WInt n)) ->
    allocator_service_ctx ⊢
    switcher_cc_specification_known_to_known_function
      emp (allocator_malloc_result S n) wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk arg_rmap cstk allocator_malloc_nargs ⊤
      allocator_pcc_b allocator_pcc_e allocator_cgp_b allocator_cgp_e
      allocator_malloc_pcc_off.
  Proof.
    iIntros (Hn Harg) "#Hservice".
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros (arg_rmap' rmap')
      "(%Hargdom & %Hrmapdom & Hna & HPC & Hcgp & Hcra & Hcsp
        & Hargs & Hrmap & Hstk & Hcstk & _ & Hpost)".
    iEval (cbn) in "HPC".
    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0] as
      ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
       "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";
       "[Hct0 %Hwct0]"].
    iClear "Hargs".
    rewrite Harg in Hwca0. simplify_eq.
    iExtractList "Hrmap" [ct1;ct2;ct3;ct4;ctp;cnull] as
      ["Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    iDestruct "Hct1" as "[Hct1 %Hct1]".
    iDestruct "Hct2" as "[Hct2 %Hct2]".
    iDestruct "Hct3" as "[Hct3 %Hct3]".
    iDestruct "Hct4" as "[Hct4 %Hct4]".
    iDestruct "Hctp" as "[Hctp %Hctp]".
    iDestruct "Hcnull" as "[Hcnull %Hcnull]".
    simplify_eq.
    iApply (allocator_malloc_valid_correct S ⊤ n None _ with
      "[- $Hservice $Hna $HPC $Hcgp $Hcra
       $Hca0 $Hca1 $Hca2 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hcnull]");
      eauto.
    iNext.
    iIntros "(Hna & HPC & Hcgp & Hcra & Hca2 & Hct0 & Hct1 & Hct2
      & Hct3 & Hct4 & Hctp & Hcnull & Hres)".
    iEval (cbn) in "HPC".
    iExtractList "Hrmap" [cs0;cs1] as
      ["[Hcs0 %Hcs0]";"[Hcs1 %Hcs1]"].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iDestruct "Hca2" as (wca2_ret) "Hca2".
    iDestruct "Hct0" as (wct0_ret) "Hct0".
    iDestruct "Hct1" as (wct1_ret) "Hct1".
    iDestruct "Hct2" as (wct2_ret) "Hct2".
    iDestruct "Hct3" as (wct3_ret) "Hct3".
    iDestruct "Hct4" as (wct4_ret) "Hct4".
    iDestruct "Hctp" as (wctp_ret) "Hctp".
    iInsertList "Hrmap" [ca2;ca3;ca4;ca5;ct0;ct1;ct2;ct3;ct4;ctp;cnull].
    set (rmap_ret := <[cnull:=lword_of_word (WInt 0)]>
      (<[ctp:=wctp_ret]> (<[ct4:=wct4_ret]> (<[ct3:=wct3_ret]>
      (<[ct2:=wct2_ret]> (<[ct1:=wct1_ret]> (<[ct0:=wct0_ret]>
      (<[ca5:=lword_of_word (WInt 0)]> (<[ca4:=lword_of_word (WInt 0)]>
      (<[ca3:=lword_of_word (WInt 0)]>
      (<[ca2:=wca2_ret]> (delete cs1 (delete cs0 rmap'))))))))))))).
    assert (dom rmap_ret =
      all_registers_s ∖ {[PC; csp; cgp; cra; cs0; cs1; ca0; ca1]})
      as Hdom_ret.
    { subst rmap_ret. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmapdom /dom_arg_rmap /allocator_malloc_nargs /=.
      set_solver+. }
    iDestruct "Hres" as "[[Hca0 Hca1] | Hres]".
    - iApply ("Hpost" $! (lword_of_word (WInt ALLOC_NO_MEMORY))
        (lword_of_word (WInt 0)) rmap_ret
        (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
      iSplit; first (iPureIntro; exact Hdom_ret).
      iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hstk Hcstk".
      iLeft. iPureIntro. auto.
    - iDestruct "Hres" as (ι b e)
        "(%Hbounds & %Hfresh & Hca0 & Hca1 & #Hobj & Hheld & Hzero)".
      iApply ("Hpost" $! (WCap true RW Global b e b @@ ι) (lword_of_word (WInt 0))
        rmap_ret (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
      iSplit; first (iPureIntro; exact Hdom_ret).
      iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hstk Hcstk".
      iRight. iExists ι,b,e. iFrame "Hobj Hheld Hzero".
      iPureIntro. split; [exact Hbounds|done].
  Qed.

  (** The result of [free]: only [ι ⊒ AQuar] (D12). *)
  Definition allocator_free_result (ι : AId) (w0 w1 : LWord) : iProp Σ :=
    (ι ⊒ AQuar ∗ ⌜w0 = WInt ALLOC_OK ∧ w1 = WInt 0⌝)%I.

  Lemma allocator_free_switcher_spec
    (wcgp wcra wcs0 wcs1 : LWord)
    (b_stk e_stk a_stk b e a : Addr) (arg_rmap : LReg) (cstk : CSTK)
    (p : Perm) (g : Locality) (ι : AId) (ws : list LWord) :
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    length ws = length (finz.seq_between b e) ->
    arg_rmap !! ca0 = Some (WCap true p g b e a @@ ι) ->
    allocator_service_ctx ⊢
    switcher_cc_specification_known_to_known_function
      (alloc_obj ι b e ∗
       free_auth_held ι ∗
       [[b,e]] ↦ₕ[ι] [[ws]])
      (allocator_free_result ι) wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk arg_rmap cstk allocator_free_nargs ⊤
      allocator_pcc_b allocator_pcc_e allocator_cgp_b allocator_cgp_e
      allocator_free_pcc_off%I.
  Proof.
    iIntros (Hbounds Hlen Harg) "#Hservice".
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros (arg_rmap' rmap')
      "(%Hargdom & %Hrmapdom & Hna & HPC & Hcgp & Hcra & Hcsp
        & Hargs & Hrmap & Hstk & Hcstk & (#Hobj & Hheld & Hmem) & Hpost)".
    iEval (cbn) in "HPC".
    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0] as
      ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
       "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";
       "[Hct0 %Hwct0]"].
    iClear "Hargs".
    rewrite Harg in Hwca0. simplify_eq.
    iExtractList "Hrmap" [ct1;ct2;ct3;ct4;ctp;cnull] as
      ["Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    iDestruct "Hct1" as "[Hct1 %Hct1]".
    iDestruct "Hct2" as "[Hct2 %Hct2]".
    iDestruct "Hct3" as "[Hct3 %Hct3]".
    iDestruct "Hct4" as "[Hct4 %Hct4]".
    iDestruct "Hctp" as "[Hctp %Hctp]".
    iDestruct "Hcnull" as "[Hcnull %Hcnull]".
    simplify_eq.
    (* The registers framed by [free] hold zero or the stack capability:
       none carries an identifier (D23). *)
    set (rmap0 := delete cnull (delete ctp (delete ct4 (delete ct3
      (delete ct2 (delete ct1 rmap')))))).
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap #Hzero]".
    iDestruct (big_sepM_pure_1 with "Hzero") as %Hzero.
    iClear "Hzero".
    set (rframe := <[csp := lword_of_word (WCap true RWL Local
        (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a)]>
      (<[ca5 := lword_of_word (WInt 0)]> (<[ca4 := lword_of_word (WInt 0)]>
      (<[ca3 := lword_of_word (WInt 0)]> rmap0)))).
    iAssert ([∗ map] r↦w ∈ rframe, r ↦ᵣ w)%I
      with "[Hrmap Hca3 Hca4 Hca5 Hcsp]" as "Hframe".
    { subst rframe rmap0.
      iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ w)%I with "Hcsp").
      iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ w)%I with "Hca5").
      iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ w)%I with "Hca4").
      iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ w)%I with "Hca3").
      iExact "Hrmap". }
    iApply (allocator_free_valid_correct ⊤ p g ι b e a ws _ rframe with
      "[- $Hservice $Hna $Hobj $Hheld $HPC $Hcgp $Hcra
       $Hca0 $Hca1 $Hca2 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hcnull $Hframe $Hmem]");
      eauto.
    { subst rframe rmap0. rewrite !dom_insert_L !dom_delete_L Hrmapdom
        /dom_arg_rmap /=. set_solver+. }
    { intros r w Hr _. subst rframe.
      rewrite !lookup_insert_Some in Hr.
      destruct Hr as [ [_ <-]|[_ [ [_ <-]|[_ [ [_ <-]|[_ [ [_ <-]|[_ Hr] ] ] ] ] ] ] ];
        try done.
      by rewrite (Hzero _ _ Hr). }
    iNext.
    iIntros "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1
      & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hframe & #Hq & _)".
    iEval (cbn) in "HPC".
    subst rframe.
    iDestruct (big_sepM_insert with "Hframe") as "[Hcsp Hframe]".
    { rewrite !lookup_insert_ne //. subst rmap0. apply not_elem_of_dom.
      rewrite !dom_delete_L Hrmapdom. set_solver+. }
    subst rmap0.
    iExtractList "Hframe" [cs0;cs1] as ["Hcs0";"Hcs1"].
    iDestruct "Hca2" as (wca2_ret) "Hca2".
    iDestruct "Hct0" as (wct0_ret) "Hct0".
    iDestruct "Hct1" as (wct1_ret) "Hct1".
    iDestruct "Hct2" as (wct2_ret) "Hct2".
    iDestruct "Hct3" as (wct3_ret) "Hct3".
    iDestruct "Hct4" as (wct4_ret) "Hct4".
    iDestruct "Hctp" as (wctp_ret) "Hctp".
    iInsertList "Hframe" [ca2;ct0;ct1;ct2;ct3;ct4;ctp;cnull].
    iApply ("Hpost" $! (lword_of_word (WInt ALLOC_OK)) (lword_of_word (WInt 0)) _
      (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
    iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hframe Hstk Hcstk".
    rewrite /allocator_free_result. iFrame "Hq".
    iPureIntro. split; last done.
    repeat (rewrite dom_insert_L || rewrite dom_delete_L).
    rewrite Hrmapdom /dom_arg_rmap /=.
    set_solver+.
  Qed.

End AllocatorSwitcherSpec.
