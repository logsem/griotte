From iris.proofmode Require Import proofmode.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import region_invariants_revocation.
From griotte Require Export world_ghost_theory world_interp_stack.
From griotte Require Import switcher_preamble.
From griotte Require Import map_simpl.

Section switcher_helpers_cframe.

  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma temp_resources_mono_pub W W' C φ a p :
    related_sts_pub_world W W' ->
    temp_resources W C φ a p -∗
    temp_resources W' C φ a p.
  Proof.
    iIntros (Hrelated) "Htemp".
    iDestruct "Htemp" as (v) "(%Hp & Ha & #Hmono & Hφ)".
    iExists v. iFrame "Ha Hmono %".
    destruct (isWL p); last destruct (isDL p);
      iApply ("Hmono" with "[] Hφ").
    all: try (iPureIntro; exact Hrelated).
    iPureIntro. by apply related_sts_pub_priv_world.
  Qed.

  Lemma world_interp_close_resources_to_RevokedResources Wcur Wsrc C lfull l :
    related_sts_pub_world Wsrc (close_list lfull Wcur) ->
    world_interp Wcur C -∗
    close_list_resources C Wsrc l false -∗
    world_interp Wcur C ∗
    RevokedResources (close_list lfull Wcur) C l.
  Proof.
    iIntros (Hrelated) "Hworld Hres".
    iSplitL "Hworld"; first done.
    iAssert (RevokedResources Wsrc C l) with "[Hres]" as "Hres".
    { rewrite (RevokedResources_eq_all Wsrc C l). iExact "Hres". }
    iApply (RevokedResources_mono_pub Wsrc (close_list lfull Wcur) C l l
      with "Hres").
    exact Hrelated.
  Qed.

  (** Helper lemmas for switcher. The lemmas with the suffix [_aux] are
      stated on the literal layout of the spill area, at [s], below the
      cursor of the caller; the others on the stack layout of
      [call_stack.v], with the spill area at [stk_spill_a a_stk] for a
      caller whose cursor is [a_stk]. *)
  #[local] Lemma open_world_interp_cframe_aux
    (W : WORLD) (C : CmptName) (b_stk e_stk s s4 hi cur : Addr)
    (wret wcgp0 wcs2 wcs3 : LWord) (ccrel : caller_callee_relation)
    :
    (b_stk <= s)%a ->
    (s ^+ (SpillSlot_size - 1) < e_stk)%a ->
    (s + SpillSlot_size)%a = Some s4 ->

    interp W C (Cap RWL Local b_stk (if is_untrusted_caller ccrel then e_stk else hi) cur) ∗
    cframe_stk_own s {|
        cs_cra := wret;
        cs_cgp := wcgp0;
        cs_cs0 := wcs2;
        cs_cs1 := wcs3
           |} ccrel
    ∗ world_interp W C
      -∗
    ∃ wastk wastk1 wastk2 wastk3,
      let la := (if (is_untrusted_caller ccrel) then finz.seq_between s (s ^+ SpillSlot_size) else []) in
      let lv := (if (is_untrusted_caller ccrel) then [wastk;wastk1;wastk2;wastk3] else []) in
      ([[ s , s ^+ SpillSlot_size ]] ↦ₐ [[ [wastk;wastk1;wastk2;wastk3] ]])
      ∗ ▷ StackOpenWorldResources interp W C la lv
      ∗ (⌜if (is_untrusted_caller ccrel)
         then True
         else (wastk = wcs2 ∧ wastk1 = wcs3 ∧ wastk2 = wcgp0 ∧ wastk3 = wret)⌝)
      ∗ world_interp_open W C (LNonHeap <$> la).
  Proof.
    iIntros (Hb_s He_s3 Hs4) "(#Hinterp_callee_wstk & Hcframe_interp & Hworld_interp)".
    unfold SpillSlot_size in *. change (4 - 1)%Z with 3%Z in He_s3.

    rewrite /cframe_stk_own /= /is_untrusted_caller_frm; cbn.
    destruct (is_untrusted_caller ccrel); cycle 1.
    * iExists wcs2, wcs3, wcgp0, wret.
      iEval (rewrite open_world_interp_empty) in "Hworld_interp"; iFrame "Hworld_interp".
      rewrite /StackOpenWorldResources /StackWorldResources.
      iSplitL "Hcframe_interp"; auto.
      iDestruct "Hcframe_interp" as "(?&?&?&?)".
      iApply (region_pointsto_cons _ (s ^+ 1)); [solve_addr+Hs4|solve_addr+Hs4|]; iFrame.
      iApply (region_pointsto_cons _ (s ^+ 2)); [solve_addr+Hs4|solve_addr+Hs4|]; iFrame.
      iApply (region_pointsto_cons _ (s ^+ 3)); [solve_addr+Hs4|solve_addr+Hs4|]; iFrame.
      iApply (region_pointsto_cons _ (s ^+ 4)); [solve_addr+Hs4|solve_addr+Hs4|]; iFrame.
      by rewrite /region_pointsto finz_seq_between_empty.
    * iEval (rewrite open_world_interp_empty -(fmap_nil LNonHeap)) in "Hworld_interp".
      iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between s (s ^+4)) []
                  with "[$Hinterp_callee_wstk $Hworld_interp]")
        as "(Hworld_interp & Hres)"; auto.
      { eapply finz_seq_between_NoDup. }
      { clear- Hb_s He_s3 Hs4; apply Forall_forall; intros a' Ha'.
        apply elem_of_finz_seq_between in Ha'; solve_addr.
      }
      { set_solver. }
      do 4 (rewrite (finz_seq_between_cons _ (s ^+ 4)); last solve_addr+Hs4).
      rewrite (finz_seq_between_empty _ (s ^+ 4)); last solve_addr+.
      cbn.
      replace ((s ^+ 1) ^+ 1) with (s ^+ 2) by solve_addr+Hs4.
      replace ((s ^+ 2) ^+ 1) with (s ^+ 3) by solve_addr+Hs4.
      iFrame "Hworld_interp".
      iDestruct "Hres" as "(%lv & [Hlv Hres])".
      iDestruct (big_sepL2_length with "Hlv") as "%Hlv_len".
      destruct lv as [|w [|w0 [|w1 [|w2 [|] ] ] ] ]; try done.
      iExists w, w0, w1, w2.
      iFrame "Hres".
      replace ( [s; (s ^+ 1); (s ^+ 2); (s ^+ 3)] )
        with (finz.seq_between s (s ^+4)); first done.
      repeat (rewrite finz_seq_between_cons; last solve_addr+Hs4).
      replace ( (s ^+ 1) ^+ 1 ) with ((s ^+ 2))%a by solve_addr+Hs4.
      replace ( (s ^+ 2) ^+ 1 ) with ((s ^+ 3))%a by solve_addr+Hs4.
      replace ( (s ^+ 3) ^+ 1 ) with ((s ^+ 4))%a by solve_addr+Hs4.
      rewrite finz_seq_between_empty; last solve_addr+Hs4.
      done.
  Qed.

  #[local] Lemma open_world_interp_callee_stack_aux (W : WORLD) (C : CmptName)
    (b_stk e_stk s s4 cur : Addr) ccrel
    :
    let l_register_save_area :=
      (if is_untrusted_caller ccrel
       then finz.seq_between s (s ^+ SpillSlot_size)
       else [])
    in
    let l_callee_stack_frame := finz.seq_between b_stk s in

    (b_stk <= s)%a ->
    (s ^+ (SpillSlot_size - 1) < e_stk)%a ->
    (s + SpillSlot_size)%a = Some s4 ->

    interp W C (Cap RWL Local b_stk (if is_untrusted_caller ccrel then e_stk else s) cur) ∗
    world_interp_open W C (LNonHeap <$> l_register_save_area)
    -∗

    world_interp_open W C (LNonHeap <$> (l_callee_stack_frame ++ l_register_save_area)) ∗
    (∃ (lv : list LWord),
        ([∗ list] a ; v ∈ l_callee_stack_frame ; lv, a ↦ₐ v)
        ∗ ▷ StackOpenWorldResources interp W C l_callee_stack_frame lv
    )
  .
  Proof.
    intros l_register_save_area l_callee_stack_frame;
    subst l_register_save_area l_callee_stack_frame.
    iIntros (Hb_s He_s3 Hs4)
      "(Hinterp_callee_wstk & Hworld_interp)".
    unfold SpillSlot_size in *. change (4 - 1)%Z with 3%Z in He_s3.
    iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between b_stk s)
                with "[$Hinterp_callee_wstk $Hworld_interp]")
      as "($ & Hres)"; auto.
    { eapply finz_seq_between_NoDup. }
    { clear- Hb_s He_s3 Hs4; apply Forall_forall; intros a' Ha'.
      apply elem_of_finz_seq_between in Ha'.
      destruct (is_untrusted_caller ccrel); solve_addr.
    }
    {
      destruct (is_untrusted_caller ccrel); last set_solver.
      set (la := finz.seq_between b_stk s).
      assert ( s ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (s ^+ 1) ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+Hs4).
      assert ( (s ^+ 2) ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+Hs4).
      assert ( (s ^+ 3) ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+Hs4).
      do 4 (rewrite (finz_seq_between_cons _ (s ^+ 4)); last solve_addr+Hs4).
      rewrite (finz_seq_between_empty _ (s ^+ 4)); last solve_addr+.
      replace ((s ^+ 1) ^+ 1) with (s ^+ 2) by solve_addr+Hs4.
      replace ((s ^+ 2) ^+ 1) with (s ^+ 3) by solve_addr+Hs4.
      set_solver.
    }
  Qed.



  (** Open the spill area of a frame whose caller's cursor is [a_stk]. *)
  Lemma open_world_interp_cframe
    (W : WORLD) (C : CmptName) (b_stk e_stk a_stk : Addr)
    (wret wcgp0 wcs2 wcs3 : LWord) (ccrel : caller_callee_relation)
    :
    let s := stk_spill_a a_stk in
    switcher_stk_bounds b_stk e_stk a_stk ->

    interp W C (Cap RWL Local
                  (if is_untrusted_caller ccrel then b_stk else stk_callee_b b_stk a_stk)
                  (if is_untrusted_caller ccrel then e_stk else stk_callee_e e_stk a_stk)
                  a_stk) ∗
    cframe_stk_own s {|
        cs_cra := wret;
        cs_cgp := wcgp0;
        cs_cs0 := wcs2;
        cs_cs1 := wcs3
           |} ccrel
    ∗ world_interp W C
      -∗
    ∃ wastk wastk1 wastk2 wastk3,
      let la := (if (is_untrusted_caller ccrel) then finz.seq_between s (s ^+ SpillSlot_size) else []) in
      let lv := (if (is_untrusted_caller ccrel) then [wastk;wastk1;wastk2;wastk3] else []) in
      ([[ s , s ^+ SpillSlot_size ]] ↦ₐ [[ [wastk;wastk1;wastk2;wastk3] ]])
      ∗ ▷ StackOpenWorldResources interp W C la lv
      ∗ (⌜if (is_untrusted_caller ccrel)
         then True
         else (wastk = wcs2 ∧ wastk1 = wcs3 ∧ wastk2 = wcgp0 ∧ wastk3 = wret)⌝)
      ∗ world_interp_open W C (LNonHeap <$> la).
  Proof.
    intros s Hbounds; subst s.
    destruct Hbounds as (Hb & Hb3 & Ha4).
    stk_unfold. change (4 - 1)%Z with 3%Z in Hb3.
    replace (if is_untrusted_caller ccrel then b_stk else b_stk) with b_stk
      by (by destruct (is_untrusted_caller ccrel)).
    apply (open_world_interp_cframe_aux W C b_stk e_stk (stk_spill_a a_stk) a_stk);
      [done | stk_unfold; solve_addr+Hb3 Ha4 | stk_unfold; solve_addr+Ha4].
  Qed.

  (** Open the callee's stack, below the spill area. *)
  Lemma open_world_interp_callee_stack (W : WORLD) (C : CmptName) (b_stk e_stk a_stk : Addr)
    ccrel
    :
    let s := stk_spill_a a_stk in
    let l_register_save_area :=
      (if is_untrusted_caller ccrel
       then finz.seq_between s (s ^+ SpillSlot_size)
       else [])
    in
    let l_callee_stack_frame := callee_stk_region b_stk e_stk a_stk in

    switcher_stk_bounds b_stk e_stk a_stk ->

    interp W C (Cap RWL Local
                  (if is_untrusted_caller ccrel then b_stk else stk_callee_b b_stk a_stk)
                  (if is_untrusted_caller ccrel then e_stk else stk_callee_e e_stk a_stk)
                  a_stk) ∗
    world_interp_open W C (LNonHeap <$> l_register_save_area)
    -∗

    world_interp_open W C (LNonHeap <$> (l_callee_stack_frame ++ l_register_save_area)) ∗
    (∃ (lv : list LWord),
        ([∗ list] a ; v ∈ l_callee_stack_frame ; lv, a ↦ₐ v)
        ∗ ▷ StackOpenWorldResources interp W C l_callee_stack_frame lv
    )
  .
  Proof.
    intros s l_register_save_area l_callee_stack_frame Hbounds;
      subst s l_register_save_area l_callee_stack_frame.
    destruct Hbounds as (Hb & Hb3 & Ha4).
    stk_unfold. change (4 - 1)%Z with 3%Z in Hb3.
    replace (if is_untrusted_caller ccrel then b_stk else b_stk) with b_stk
      by (by destruct (is_untrusted_caller ccrel)).
    apply (open_world_interp_callee_stack_aux W C b_stk e_stk (stk_spill_a a_stk) a_stk);
      [done | stk_unfold; solve_addr+Hb3 Ha4 | stk_unfold; solve_addr+Ha4].
  Qed.


  Definition CloseRes (Wfixed : WORLD) (C : CmptName)
    (a_stk : Addr) (l : list LAddr ) ccrel : iProp Σ :=
    ( if (is_untrusted_caller ccrel)
      then
        ( ∃ l',
            ⌜ l ≡ₚ (LNonHeap <$> [a_stk;(a_stk ^+ 1);(a_stk ^+ 2);(a_stk ^+ 3)])++l' ⌝
            ∗ RevokedResources Wfixed C l'
            ∗ ([∗ list] a ∈ [a_stk;(a_stk ^+ 1);(a_stk ^+ 2);(a_stk ^+ 3)],
                 ∃ (p : Perm) (φ : WORLD * CmptName * LWord → iPropI Σ),
                   ⌜∀ Wv : WORLD * CmptName * LWord, Persistent (φ Wv)⌝
                                                    ∗ (⌜isO p = false⌝
                                                       ∗ (if isWL p
                                                          then future_pub_mono C φ (WInt 0)
                                                          else if isDL p then future_pub_mono C φ (WInt 0) else future_priv_mono C φ (WInt 0)
                                                         )
                                                       ∗ (∃ W0', ⌜ related_sts_pub_world W0' Wfixed⌝ ∗ φ (W0', C, lword_of_word (WInt 0))))
                                                    ∗ rel C (LNonHeap a) p φ
              )
        )
      else
        (RevokedResources Wfixed C l)
    )%I.

    #[local] Lemma open_world_interp_cframe_gen_aux
    (W0 Wcur : WORLD) (C : CmptName) (b_stk e_stk a_stk a_stk4 cur : Addr) (l : list LAddr)
    (wret wcgp wcs0 wcs1 : LWord) (ccrel : caller_callee_relation)
    :
      let Wfixed := close_list (l ++ (LNonHeap <$> finz.seq_between b_stk a_stk)) Wcur in

      (b_stk <= a_stk)%a ->
      (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->
      (a_stk + SpillSlot_size)%a = Some a_stk4 ->

      (∀ a : LAddr, std W0 !! a = Some Temporary → a ∈ l ++ (LNonHeap <$> finz.seq_between b_stk a_stk)) ->
      NoDup (l ++ (LNonHeap <$> finz.seq_between b_stk a_stk)) ->
      related_sts_pub_world W0 Wfixed ->
      disjoint_from_heap b_stk e_stk ->

      interp W0 C (Cap RWL Local b_stk (if is_untrusted_caller ccrel then e_stk else a_stk) cur) -∗
      cframe_stk_own a_stk
        {|
          cs_cra := wret;
          cs_cgp := wcgp;
          cs_cs0 := wcs0;
          cs_cs1 := wcs1
           |} ccrel
        -∗
        RevokedResources Wfixed C l -∗
        £ 1
      -∗
      (
        |={⊤}=>
          ∃ wastk wastk1 wastk2 wastk3,
          a_stk ↦ₐ wastk
          ∗ (a_stk ^+ 1) ↦ₐ wastk1
          ∗ (a_stk ^+ 2) ↦ₐ wastk2
          ∗ (a_stk ^+ 3) ↦ₐ wastk3
          ∗ (⌜if (is_untrusted_caller ccrel)
             then True
             else (wastk = wcs0 ∧ wastk1 = wcs1 ∧ wastk2 = wcgp ∧ wastk3 = wret)⌝)
          ∗ (if (is_untrusted_caller ccrel)
             then (
                 (interp_in_mem RWL Wfixed C wastk)
                 ∗ (interp_in_mem RWL Wfixed C wastk1)
                 ∗ (interp_in_mem RWL Wfixed C wastk2)
                 ∗ (interp_in_mem RWL Wfixed C wastk3)
               )
             else True
            )
          ∗ CloseRes Wfixed C a_stk l ccrel
      )
    .
    Proof.
      intros Wfixed.
      iIntros (Hb_a4 He_a1 Ha_stk4 Htemp_revoked Hnodup_revoked Hrelated_pub_W0_Wfixed Hstk_heap)
        "#Hinterp_callee_wstk Hcframe_interp Hclose_list_res Hlc".
      rewrite /SpillSlot_size in He_a1 Ha_stk4. change (4 - 1)%Z with 3%Z in He_a1.
      rewrite /cframe_stk_own /= /is_untrusted_caller_frm; cbn.
      rewrite /CloseRes.
      destruct (is_untrusted_caller ccrel); cycle 1.
      * iExists wcs0, wcs1, wcgp, wret.
        iDestruct "Hcframe_interp" as "($&$&$&$)". iFrame.
        done.
      * cbn.
        iAssert
          (⌜ ∀ (a : Addr), a ∈ (finz.seq_between b_stk e_stk) → (std W0 !! LNonHeap a) = Some Temporary ⌝)%I
          as "%Hstk_tmp".
        {
          iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_callee_wstk") as "%Hstk_tmp" ; auto.
          iPureIntro ; intros a Ha.
          apply list_elem_of_lookup_1 in Ha as [k Ha].
          by eapply Hstk_tmp.
        }

        iAssert ( ⌜ LNonHeap a_stk ∈ l ⌝)%I as "%Hastk_unk".
        {
          opose proof (Hstk_tmp a_stk _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          rewrite elem_of_LNonHeap_fmap elem_of_finz_seq_between in Hcontra.
          solve_addr+Hcontra Ha_stk4.
        }
        iAssert ( ⌜ LNonHeap (a_stk ^+1) ∈ l ⌝)%I as "%Hastk1_unk".
        {
          opose proof (Hstk_tmp (a_stk ^+1) _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          rewrite elem_of_LNonHeap_fmap elem_of_finz_seq_between in Hcontra.
          solve_addr+Hcontra Ha_stk4.
        }
        iAssert ( ⌜ LNonHeap (a_stk ^+2) ∈ l ⌝)%I as "%Hastk2_unk".
        {
          opose proof (Hstk_tmp (a_stk ^+2) _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          rewrite elem_of_LNonHeap_fmap elem_of_finz_seq_between in Hcontra.
          solve_addr+Hcontra Ha_stk4.
        }
        iAssert ( ⌜ LNonHeap (a_stk ^+3) ∈ l ⌝)%I as "%Hastk3_unk".
        {
          opose proof (Hstk_tmp (a_stk ^+3) _) as Hastk_tmp.
          { rewrite elem_of_finz_seq_between; solve_addr+Hb_a4 He_a1 Ha_stk4. }
          apply Htemp_revoked in Hastk_tmp.
          apply elem_of_app in Hastk_tmp as [?|Hcontra]; first done.
          rewrite elem_of_LNonHeap_fmap elem_of_finz_seq_between in Hcontra.
          solve_addr+Hcontra Ha_stk4.
        }
        assert (a_stk ∈ₐ [b_stk, e_stk)) as Hbound0
          by solve_addr+Hb_a4 He_a1.
        iDestruct (write_allowed_inv W0 C a_stk cur b_stk e_stk RWL Local None
          Hbound0 I with "Hinterp_callee_wstk")
          as (p_astk0 φ_astk0) "(%Hp_astk0 & _ & Hrel_astk0 & _ & Hwcond_astk0 & Hrcond_astk0 & _)".
        assert (addr_key None a_stk = LNonHeap a_stk) as Hkey_astk0 by done.
        rewrite Hkey_astk0.
        assert ((a_stk ^+1) ∈ₐ [b_stk, e_stk)) as Hbound1
          by solve_addr+Hb_a4 He_a1.
        iDestruct (write_allowed_inv W0 C (a_stk ^+1) cur b_stk e_stk RWL Local None
          Hbound1 I with "Hinterp_callee_wstk")
          as (p_astk1 φ_astk1) "(%Hp_astk1 & _ & Hrel_astk1 & _ & Hwcond_astk1 & Hrcond_astk1 & _)".
        assert (addr_key None (a_stk ^+1) = LNonHeap (a_stk ^+1)) as Hkey_astk1 by done.
        rewrite Hkey_astk1.
        assert ((a_stk ^+2) ∈ₐ [b_stk, e_stk)) as Hbound2
          by solve_addr+Hb_a4 He_a1.
        iDestruct (write_allowed_inv W0 C (a_stk ^+2) cur b_stk e_stk RWL Local None
          Hbound2 I with "Hinterp_callee_wstk")
          as (p_astk2 φ_astk2) "(%Hp_astk2 & _ & Hrel_astk2 & _ & Hwcond_astk2 & Hrcond_astk2 & _)".
        assert (addr_key None (a_stk ^+2) = LNonHeap (a_stk ^+2)) as Hkey_astk2 by done.
        rewrite Hkey_astk2.
        assert ((a_stk ^+3) ∈ₐ [b_stk, e_stk)) as Hbound3
          by solve_addr+Hb_a4 He_a1.
        iDestruct (write_allowed_inv W0 C (a_stk ^+3) cur b_stk e_stk RWL Local None
          Hbound3 I with "Hinterp_callee_wstk")
          as (p_astk3 φ_astk3) "(%Hp_astk3 & _ & Hrel_astk3 & _ & Hwcond_astk3 & Hrcond_astk3 & _)".
        assert (addr_key None (a_stk ^+3) = LNonHeap (a_stk ^+3)) as Hkey_astk3 by done.
        rewrite Hkey_astk3.

        iAssert
          ( ▷ (∃ l',
              ⌜ l ≡ₚ (LNonHeap <$> [a_stk;(a_stk ^+ 1);(a_stk ^+ 2);(a_stk ^+ 3)])++l' ⌝
              ∗ RevokedResources Wfixed C l'
              ∗ (∃ wastk wastk1 wastk2 wastk3,
                    a_stk ↦ₐ wastk
                    ∗ (a_stk ^+ 1) ↦ₐ wastk1
                    ∗ (a_stk ^+ 2) ↦ₐ wastk2
                    ∗ (a_stk ^+ 3) ↦ₐ wastk3
                    ∗ (∃ W0', ⌜ related_sts_pub_world W0' Wfixed⌝ ∗ (interp_in_mem RWL W0' C wastk))
                    ∗ (∃ W1', ⌜ related_sts_pub_world W1' Wfixed⌝ ∗ (interp_in_mem RWL W1' C wastk1))
                    ∗ (∃ W2', ⌜ related_sts_pub_world W2' Wfixed⌝ ∗ (interp_in_mem RWL W2' C wastk2))
                    ∗ (∃ W3', ⌜ related_sts_pub_world W3' Wfixed⌝ ∗ (interp_in_mem RWL W3' C wastk3))
                )
              ∗ ([∗ list] a ∈ [a_stk;(a_stk ^+ 1);(a_stk ^+ 2);(a_stk ^+ 3)],
                   ∃ (p : Perm) (φ : WORLD * CmptName * LWord → iPropI Σ),
                     ⌜∀ Wv : WORLD * CmptName * LWord, Persistent (φ Wv)⌝
                                                      ∗ (⌜isO p = false⌝
                                                         ∗ (if isWL p
                                                            then future_pub_mono C φ (WInt 0)
                                                            else if isDL p then future_pub_mono C φ (WInt 0) else future_priv_mono C φ (WInt 0)
                                                           )
                                                         ∗ (∃ W0', ⌜ related_sts_pub_world W0' Wfixed⌝ ∗ φ (W0', C, lword_of_word (WInt 0)))
                                                        )
                                                      ∗ rel C (LNonHeap a) p φ
                )
          ))%I with "[Hclose_list_res]" as "H".
    { apply NoDup_app in Hnodup_revoked as (Hnodup_revoked & ? & ?).
      apply elem_of_Permutation in Hastk_unk as [l0 Hl0].
      rewrite Hl0 in Hastk1_unk,Hastk2_unk,Hastk3_unk.
      apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (injection Hcontra as Hcontra; exfalso; clear -Hcontra Ha_stk4; solve_addr).
      apply elem_of_cons in Hastk2_unk as [Hcontra | Hastk2_unk]; first (injection Hcontra as Hcontra; exfalso; clear -Hcontra Ha_stk4; solve_addr).
      apply elem_of_cons in Hastk1_unk as [Hcontra | Hastk1_unk]; first (injection Hcontra as Hcontra; exfalso; clear -Hcontra Ha_stk4; solve_addr).

      apply elem_of_Permutation in Hastk1_unk as [l1 Hl1].
      rewrite Hl1 in Hastk2_unk,Hastk3_unk.
      apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (injection Hcontra as Hcontra; exfalso; clear -Hcontra Ha_stk4; solve_addr).
      apply elem_of_cons in Hastk2_unk as [Hcontra | Hastk2_unk]; first (injection Hcontra as Hcontra; exfalso; clear -Hcontra Ha_stk4; solve_addr).

      apply elem_of_Permutation in Hastk2_unk as [l2 Hl2].
      rewrite Hl2 in Hastk3_unk.
      apply elem_of_cons in Hastk3_unk as [Hcontra | Hastk3_unk]; first (injection Hcontra as Hcontra; exfalso; clear -Hcontra Ha_stk4; solve_addr).

      apply elem_of_Permutation in Hastk3_unk as [l3 Hl3].

      rewrite Hl3 in Hl2; rewrite Hl2 in Hl1; rewrite Hl1 in Hl0.
      clear Hl3 Hl2 Hl1.

      iExists l3.
      iSplit; first (iPureIntro; exact Hl0).
      rewrite /RevokedResources.
      iDestruct (big_opL_permutation with "Hclose_list_res") as "Hclose_list_res"; first (symmetry; done).
      iDestruct (big_sepL_app _ (LNonHeap <$> [a_stk; (a_stk ^+ 1); (a_stk ^+ 2); (a_stk ^+ 3)]) l3 with "Hclose_list_res") as "[Hframe $]".
      assert (Forall (λ a, is_heap_address a = false)
        [a_stk; (a_stk ^+ 1); (a_stk ^+ 2); (a_stk ^+ 3)]) as Hnonheap.
      { apply Forall_forall. intros a Ha.
        apply not_true_is_false. intros Hheap.
        apply withinBounds_true_iff in Hheap.
        rewrite /disjoint_from_heap elem_of_disjoint in Hstk_heap.
        eapply (Hstk_heap a); [apply elem_of_finz_seq_between|by apply elem_of_finz_seq_between].
        rewrite !elem_of_cons elem_of_nil in Ha.
        repeat (destruct Ha as [->|Ha]); try contradiction;
          solve_addr+Hb_a4 He_a1 Ha_stk4.
      }
      apply Forall_cons in Hnonheap as [Hnonheap0 Hnonheap].
      apply Forall_cons in Hnonheap as [Hnonheap1 Hnonheap].
      apply Forall_cons in Hnonheap as [Hnonheap2 Hnonheap].
      apply Forall_cons in Hnonheap as [Hnonheap3 _].
      cbn.
      iDestruct "Hframe" as "(Hv0 & Hv1 & Hv2 & Hv3 & _)".
      iDestruct "Hv0" as (p_v0 P0 Hpers_P0) "(#Hrel0 & Hv0)".
      iDestruct "Hv1" as (p_v1 P1 Hpers_P1) "(#Hrel1 & Hv1)".
      iDestruct "Hv2" as (p_v2 P2 Hpers_P2) "(#Hrel2 & Hv2)".
      iDestruct "Hv3" as (p_v3 P3 Hpers_P3) "(#Hrel3 & Hv3)".
      iClear "Hinterp_callee_wstk".
      iFrame "Hrel0". iFrame "Hrel1". iFrame "Hrel2". iFrame "Hrel3".
      iDestruct "Hv0" as (v0) "(%Hnot_O0 & $ & H0' & #H0)".
      iDestruct "Hv1" as (v1) "(%Hnot_O1 & $ & H1' & #H1)".
      iDestruct "Hv2" as (v2) "(%Hnot_O2 & $ & H2' & #H2)".
      iDestruct "Hv3" as (v3) "(%Hnot_O3 & $ & H3' & #H3)".
      iEval (rewrite !mono_temporary_eq) in "H0 H1 H2 H3".
      pose (W0' := Wfixed). pose (W1' := Wfixed).
      pose (W2' := Wfixed). pose (W3' := Wfixed).
      assert (related_sts_pub_world W0' Wfixed) as HW0' by apply related_sts_pub_refl_world.
      assert (related_sts_pub_world W1' Wfixed) as HW1' by apply related_sts_pub_refl_world.
      assert (related_sts_pub_world W2' Wfixed) as HW2' by apply related_sts_pub_refl_world.
      assert (related_sts_pub_world W3' Wfixed) as HW3' by apply related_sts_pub_refl_world.
      iDestruct (rel_agree _ _ (safeC φ_astk0) P0 with "[$Hrel_astk0 $Hrel0]") as "[<- HP0]".
      iDestruct (rel_agree _ _ (safeC φ_astk1) P1 with "[$Hrel_astk1 $Hrel1]") as "[<- HP1]".
      iDestruct (rel_agree _ _ (safeC φ_astk2) P2 with "[$Hrel_astk2 $Hrel2]") as "[<- HP2]".
      iDestruct (rel_agree _ _ (safeC φ_astk3) P3 with "[$Hrel_astk3 $Hrel3]") as "[<- HP3]".
      rewrite (readAllowed_flowsto RWL p_astk0 Hp_astk0 eq_refl)
        (readAllowed_flowsto RWL p_astk1 Hp_astk1 eq_refl)
        (readAllowed_flowsto RWL p_astk2 Hp_astk2 eq_refl)
        (readAllowed_flowsto RWL p_astk3 Hp_astk3 eq_refl)
        (isWL_flowsto RWL p_astk0 Hp_astk0 eq_refl)
        (isWL_flowsto RWL p_astk1 Hp_astk1 eq_refl)
        (isWL_flowsto RWL p_astk2 Hp_astk2 eq_refl)
        (isWL_flowsto RWL p_astk3 Hp_astk3 eq_refl).
      iNext.
      iRewrite - ("HP0" $! (Wfixed,C,v0)) in "H0'".
      iRewrite - ("HP1" $! (Wfixed,C,v1)) in "H1'".
      iRewrite - ("HP2" $! (Wfixed,C,v2)) in "H2'".
      iRewrite - ("HP3" $! (Wfixed,C,v3)) in "H3'".
      iDestruct ("Hrcond_astk0" with "H0'") as "#Hinterp0"; cbn.
      iDestruct ("Hrcond_astk1" with "H1'") as "#Hinterp1"; cbn.
      iDestruct ("Hrcond_astk2" with "H2'") as "#Hinterp2"; cbn.
      iDestruct ("Hrcond_astk3" with "H3'") as "#Hinterp3"; cbn.
      iSplitR.
      {
        assert (∀ p (v : LWord), PermFlowsTo RWL p → lload_word p v = v) as Hll.
        { intros p [w π] Hp.
          rewrite /lload_word /lift_word /= /load_word (notisDRO_flowsfrom RWL p Hp eq_refl)
            (notisDL_flowsfrom RWL p Hp eq_refl) //. }
        rewrite /interp_in_mem_pre !(Hll RWL) //.
        rewrite (Hll _ _ Hp_astk0) (Hll _ _ Hp_astk1) (Hll _ _ Hp_astk2) (Hll _ _ Hp_astk3).
        iFrame "Hinterp0 Hinterp1 Hinterp2 Hinterp3".
        iPureIntro; split_and!; apply related_sts_pub_refl_world.
      }
      iSplitL "H0 H0'".
      { iSplitR "H0'"; first (iPureIntro; exact Hpers_P0).
        iSplitR "H0'"; first (iPureIntro; exact Hnot_O0).
        iSplitR "H0'"; cycle 1.
        + iExists W0'; iSplitR; first (iPureIntro; exact HW0').
          iRewrite - ("HP0" $! (W0',C,WInt 0 @@? None)).
          iApply "Hwcond_astk0"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP0" $! (W',C,WInt 0 @@? None)).
          iApply "Hwcond_astk0"; iApply interp_int.
      }
      iSplitL "H1 H1'".
      { iSplitR "H1'"; first (iPureIntro; exact Hpers_P1).
        iSplitR "H1'"; first (iPureIntro; exact Hnot_O1).
        iSplitR "H1'"; cycle 1.
        + iExists W1'; iSplitR; first (iPureIntro; exact HW1').
          iRewrite - ("HP1" $! (W1',C,WInt 0 @@? None)).
          iApply "Hwcond_astk1"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP1" $! (W',C,WInt 0 @@? None)).
          iApply "Hwcond_astk1"; iApply interp_int.
      }
      iSplitL "H2 H2'".
      { iSplitR "H2'"; first (iPureIntro; exact Hpers_P2).
        iSplitR "H2'"; first (iPureIntro; exact Hnot_O2).
        iSplitR "H2'"; cycle 1.
        + iExists W2'; iSplitR; first (iPureIntro; exact HW2').
          iRewrite - ("HP2" $! (W2',C,WInt 0 @@? None)).
          iApply "Hwcond_astk2"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP2" $! (W',C,WInt 0 @@? None)).
          iApply "Hwcond_astk2"; iApply interp_int.
      }
      { iSplitR "H3'"; first (iPureIntro; exact Hpers_P3).
        iSplitR "H3'"; first (iPureIntro; exact Hnot_O3).
        iSplitR "H3'"; cycle 1.
        + iExists W3'; iSplitR; first (iPureIntro; exact HW3').
          iRewrite - ("HP3" $! (W3',C,WInt 0 @@? None)).
          iApply "Hwcond_astk3"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP3" $! (W',C,WInt 0 @@? None)).
          iApply "Hwcond_astk3"; iApply interp_int.
      }
    }

    iDestruct (lc_fupd_elim_later with "[$] [$H]") as ">H".
    iModIntro.
    iDestruct "H" as (l') "(%Hl & Hrest & Hvals & Hzero)".
    iDestruct "Hvals" as (v0 v1 v2 v3) "(Ha0 & Ha1 & Ha2 & Ha3 & H0 & H1 & H2 & H3)".
    iExists v0, v1, v2, v3. iFrame "Ha0 Ha1 Ha2 Ha3".
    iSplitR; first done.
    iSplitL "H0 H1 H2 H3".
    { iDestruct "H0" as (W0' HW0') "H0".
      iDestruct "H1" as (W1' HW1') "H1".
      iDestruct "H2" as (W2' HW2') "H2".
      iDestruct "H3" as (W3' HW3') "H3".
      iDestruct (interp_in_mem_monotone W0' Wfixed with "H0") as "$"; [done|].
      iDestruct (interp_in_mem_monotone W1' Wfixed with "H1") as "$"; [done|].
      iDestruct (interp_in_mem_monotone W2' Wfixed with "H2") as "$"; [done|].
      iApply (interp_in_mem_monotone W3' Wfixed with "H3"); done.
    }
    iExists l'. iFrame "Hrest Hzero". done.
    Qed.

  (** Open the spill area of the topmost frame at the return, whose caller's
      cursor is [a_stk], with the world fixed on the callee's stack. *)
  Lemma open_world_interp_cframe_gen
    (W0 Wcur : WORLD) (C : CmptName) (b_stk e_stk a_stk : Addr) (l : list LAddr)
    (wret wcgp wcs0 wcs1 : LWord) (ccrel : caller_callee_relation)
    :
      let Wfixed := close_list (l ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) Wcur in
      let s := stk_spill_a a_stk in

      switcher_stk_bounds b_stk e_stk a_stk ->
      (∀ a : LAddr, std W0 !! a = Some Temporary →
                    a ∈ l ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) ->
      NoDup (l ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) ->
      related_sts_pub_world W0 Wfixed ->
      disjoint_from_heap b_stk e_stk ->

      interp W0 C (Cap RWL Local
                   (if is_untrusted_caller ccrel then b_stk else stk_callee_b b_stk a_stk)
                   (if is_untrusted_caller ccrel then e_stk else stk_callee_e e_stk a_stk)
                   a_stk) -∗
      cframe_stk_own s
        {|
          cs_cra := wret;
          cs_cgp := wcgp;
          cs_cs0 := wcs0;
          cs_cs1 := wcs1
           |} ccrel
        -∗
        RevokedResources Wfixed C l -∗
        £ 1
      -∗
      (
        |={⊤}=>
          ∃ wastk wastk1 wastk2 wastk3,
          s ↦ₐ wastk
          ∗ (s ^+ 1) ↦ₐ wastk1
          ∗ (s ^+ 2) ↦ₐ wastk2
          ∗ (s ^+ 3) ↦ₐ wastk3
          ∗ (⌜if (is_untrusted_caller ccrel)
             then True
             else (wastk = wcs0 ∧ wastk1 = wcs1 ∧ wastk2 = wcgp ∧ wastk3 = wret)⌝)
          ∗ (if (is_untrusted_caller ccrel)
             then (
                 (interp_in_mem RWL Wfixed C wastk)
                 ∗ (interp_in_mem RWL Wfixed C wastk1)
                 ∗ (interp_in_mem RWL Wfixed C wastk2)
                 ∗ (interp_in_mem RWL Wfixed C wastk3)
               )
             else True
            )
          ∗ CloseRes Wfixed C s l ccrel
      )
    .
  Proof.
    intros Wfixed s Hbounds; subst Wfixed s.
    destruct Hbounds as (Hb & Hb3 & Ha4).
    stk_unfold. change (4 - 1)%Z with 3%Z in Hb3.
    replace (if is_untrusted_caller ccrel then b_stk else b_stk) with b_stk
      by (by destruct (is_untrusted_caller ccrel)).
    intros Htemp Hnodup Hrelated Hheap.
    apply (open_world_interp_cframe_gen_aux W0 Wcur C b_stk e_stk (stk_spill_a a_stk) a_stk);
      [done | stk_unfold; solve_addr+Hb3 Ha4 | stk_unfold; solve_addr+Ha4 | done..].
  Qed.

End switcher_helpers_cframe.
