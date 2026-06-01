From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel monotone interp_weakening fundamental.
From cap_machine Require Import region_invariants_revocation.
From cap_machine Require Export world_ghost_theory world_interp_stack.
From cap_machine Require Import switcher_preamble.

Section switcher_helper.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
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

  (* This lemma is a more general version of [world_interp_restore_world]. *)
  Lemma reinstate_close_list_gen W C (l : list Addr) :
    ⊢ world_interp W C
    ∗ close_list_resources_gen C W l l false
    ==∗
    world_interp (reinstate W l) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "([Hr [Hsts Hseals] ] & Htemp)".
    iMod (monotone_close_list_region_gen W W _ l with "[$Hr $Hsts $Htemp]") as "[Hsts Hr]"; iFrame.
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    apply close_list_related_sts_pub; done.
  Qed.

  (** Helper lemmas for switcher. *)
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
      ([[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ [wastk;wastk1;wastk2;wastk3] ]])
      ∗ ▷ StackOpenWorldResources interp W C la lv
      ∗ (⌜if (is_untrusted_caller ccrel)
         then True
         else (wastk = wcs2 ∧ wastk1 = wcs3 ∧ wastk2 = wret ∧ wastk3 = wcgp0)⌝)
      ∗ world_interp_open W C la.
  Proof.
    iIntros (Hb_a4 He_a1 Ha_stk4) "(#Hinterp_callee_wstk & Hcframe_interp & Hworld_interp)".

    rewrite /cframe_stk_own /= /is_untrusted_caller_frm; cbn.
    destruct (is_untrusted_caller ccrel); cycle 1.
    * iExists wcs2, wcs3, wret, wcgp0.
      iEval (rewrite open_world_interp_empty) in "Hworld_interp"; iFrame "Hworld_interp".
      rewrite /StackOpenWorldResources /StackWorldResources.
      iSplitL "Hcframe_interp"; auto.
      iDestruct "Hcframe_interp" as "(?&?&?&?)".
      iApply (region_pointsto_cons _ (a_stk ^+ 1)%a); [solve_addr+Ha_stk4|solve_addr+He_a1|]; iFrame.
      iApply (region_pointsto_cons _ (a_stk ^+ 2)%a); [solve_addr+Ha_stk4|solve_addr+He_a1|]; iFrame.
      iApply (region_pointsto_cons _ (a_stk ^+ 3)%a); [solve_addr+Ha_stk4|solve_addr+He_a1|]; iFrame.
      iApply (region_pointsto_cons _ (a_stk ^+ 4)%a); [solve_addr+Ha_stk4|solve_addr+He_a1|]; iFrame.
      by rewrite /region_pointsto finz_seq_between_empty.
    * iEval (rewrite open_world_interp_empty) in "Hworld_interp".
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
      iFrame.
      iDestruct "Hres" as "(%lv & [Hlv Hres])".
      iDestruct (big_sepL2_length with "Hlv") as "%Hlv_len".
      repeat (destruct lv; try done).
      iExists w, w0, w1, w2.
      iFrame.
      iSplitL "Hlv".
      - replace ( [a_stk; (a_stk ^+ 1)%a; (a_stk ^+ 2)%a; (a_stk ^+ 3)%a] )
        with (finz.seq_between a_stk (a_stk ^+4)%a); first done.
        repeat (rewrite finz_seq_between_cons; last solve_addr+He_a1).
        replace ( ((a_stk ^+ 1) ^+ 1)%a ) with ((a_stk ^+ 2))%a by solve_addr+He_a1.
        replace ( ((a_stk ^+ 2) ^+ 1)%a ) with ((a_stk ^+ 3))%a by solve_addr+He_a1.
        replace ( ((a_stk ^+ 3) ^+ 1)%a ) with ((a_stk ^+ 4))%a by solve_addr+He_a1.
        rewrite finz_seq_between_empty; last solve_addr+He_a1.
        done.
      - iNext.
        rewrite /StackOpenWorldResources.
        iDestruct "Hres" as "[Hres $]".
        rewrite /StackWorldResources.
        repeat (iDestruct (big_sepL2_cons with "Hres") as "[$ Hres]").
  Qed.

  Lemma open_world_interp_callee_stack (W : WORLD) (C : CmptName) (b_stk e_stk a_stk a_stk4 : Addr)
    ccrel
    :
    let l_register_save_area :=
      (if is_untrusted_caller ccrel
       then finz.seq_between a_stk (a_stk ^+ 4)%a
       else [])
    in
    let l_callee_stack_frame := finz.seq_between (a_stk ^+ 4)%a e_stk in

    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->
    (a_stk + 4)%a = Some a_stk4 ->

    interp W C (WCap RWL Local (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) e_stk a_stk) ∗
    world_interp_open W C l_register_save_area
    -∗

    world_interp_open W C (l_callee_stack_frame ++ l_register_save_area) ∗
    (∃ (lv : list Word),
        ([∗ list] a ; v ∈ l_callee_stack_frame ; lv, a ↦ₐ v)
        ∗ ▷ StackOpenWorldResources interp W C l_callee_stack_frame lv
    )
  .
  Proof.
    intros l_register_save_area l_callee_stack_frame;
    subst l_register_save_area l_callee_stack_frame.
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
  Qed.


  Definition CloseRes_gen (Wcur Wfixed : WORLD) (C : CmptName)
    (csp_b csp_e a_stk : Addr) (l : list Addr ) ccrel : iProp Σ :=
    ( if (is_untrusted_caller ccrel)
      then
        ( ∃ l',
            ⌜ l ≡ₚ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a]++l' ⌝
            ∗ close_list_resources_gen C Wcur (l ++ finz.seq_between csp_b csp_e) l' false
            ∗ ([∗ list] a ∈ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a],
                 ∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
                   ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                                    ∗ (⌜isO p = false⌝
                                                       ∗ (if isWL p
                                                          then future_pub_mono C φ (WInt 0)
                                                          else if isDL p then future_pub_mono C φ (WInt 0) else future_priv_mono C φ (WInt 0)
                                                         )
                                                       ∗ (∃ W0', ⌜ related_sts_pub_world W0' Wfixed⌝ ∗ φ (W0', C, WInt 0)))
                                                    ∗ rel C a p φ
              )
        )
      else
        (close_list_resources_gen C Wcur (l ++ finz.seq_between csp_b csp_e) l false)
    )%I.

    Lemma open_world_interp_cframe_gen
    (W0 Wcur : WORLD) (C : CmptName) (b_stk csp_b csp_e a_stk4 : Addr) (l : list Addr)
    (wret wcgp wcs0 wcs1 : Word) (ccrel : caller_callee_relation) :
      let Wfixed := close_list (l ++ finz.seq_between csp_b csp_e) Wcur in
      let a_stk := (csp_b ^+ -4)%a in

      (b_stk <= csp_b ^+ -4)%a ->
      ((csp_b ^+ -4) ^+ 3 < csp_e)%a ->
      (csp_b ^+ -4 + 4)%a = Some a_stk4 ->

      (∀ a : finz MemNum, std W0 !! a = Some Temporary → a ∈ l ++ finz.seq_between csp_b csp_e) ->
      NoDup (l ++ finz.seq_between csp_b csp_e) ->
      related_sts_pub_world W0 Wfixed ->

      interp W0 C (WCap RWL Local (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) csp_e a_stk) -∗
      cframe_stk_own
        {|
          wret := wret;
          wcgp := wcgp;
          wcs0 := wcs0;
          wcs1 := wcs1;
          b_stk := b_stk;
          a_stk := a_stk;
          e_stk := csp_e;
          ccrel := ccrel
        |}
        -∗
        close_list_resources_gen C Wcur (l ++ finz.seq_between csp_b csp_e) l false -∗
        £ 1
      -∗
      (
        |={⊤}=>
          ∃ wastk wastk1 wastk2 wastk3,
          a_stk ↦ₐ wastk
          ∗ (a_stk ^+ 1)%a ↦ₐ wastk1
          ∗ (a_stk ^+ 2)%a ↦ₐ wastk2
          ∗ (a_stk ^+ 3)%a ↦ₐ wastk3
          ∗ (⌜if (is_untrusted_caller ccrel)
             then True
             else (wastk = wcs0 ∧ wastk1 = wcs1 ∧ wastk2 = wret ∧ wastk3 = wcgp)⌝)
          ∗ (if (is_untrusted_caller ccrel)
             then (
                 (interp Wfixed C wastk)
                 ∗ (interp Wfixed C wastk1)
                 ∗ (interp Wfixed C wastk2)
                 ∗ (interp Wfixed C wastk3)
               )
             else True
            )
          ∗ CloseRes_gen Wcur Wfixed C csp_b csp_e a_stk l ccrel
      )
    .
    Proof.
      intros Wfixed a_stk.
      iIntros (Hb_a4 He_a1 Ha_stk4 Htemp_revoked Hnodup_revoked Hrelated_pub_W0_Wfixed)
        "#Hinterp_callee_wstk Hcframe_interp Hclose_list_res Hlc".
      rewrite /cframe_stk_own /= /is_untrusted_caller_frm; cbn.
      rewrite /CloseRes_gen.
      destruct (is_untrusted_caller ccrel); cycle 1.
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
          apply list_elem_of_lookup_1 in Ha as [k Ha].
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
              ∗ close_list_resources_gen C Wcur (l ++ finz.seq_between csp_b csp_e) l' false
              ∗ (∃ wastk wastk1 wastk2 wastk3,
                    a_stk ↦ₐ wastk
                    ∗ (a_stk ^+ 1)%a ↦ₐ wastk1
                    ∗ (a_stk ^+ 2)%a ↦ₐ wastk2
                    ∗ (a_stk ^+ 3)%a ↦ₐ wastk3
                    ∗ (∃ W0', ⌜ related_sts_pub_world W0' Wfixed⌝ ∗ (interp W0' C wastk))
                    ∗ (∃ W1', ⌜ related_sts_pub_world W1' Wfixed⌝ ∗ (interp W1' C wastk1))
                    ∗ (∃ W2', ⌜ related_sts_pub_world W2' Wfixed⌝ ∗ (interp W2' C wastk2))
                    ∗ (∃ W3', ⌜ related_sts_pub_world W3' Wfixed⌝ ∗ (interp W3' C wastk3))
                )
              ∗ ([∗ list] a ∈ [a_stk;(a_stk ^+ 1)%a;(a_stk ^+ 2)%a;(a_stk ^+ 3)%a],
                   ∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
                     ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
                                                      ∗ (⌜isO p = false⌝
                                                         ∗ (if isWL p
                                                            then future_pub_mono C φ (WInt 0)
                                                            else if isDL p then future_pub_mono C φ (WInt 0) else future_priv_mono C φ (WInt 0)
                                                           )
                                                         ∗ (∃ W0', ⌜ related_sts_pub_world W0' Wfixed⌝ ∗ φ (W0', C, WInt 0))
                                                        )
                                                      ∗ rel C a p φ
                )
          ))%I with "[Hclose_list_res]" as "H".
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

      iExists l3.
      iSplit; first iFrame "%".
      rewrite /close_list_resources_gen /close_addr_resources_gen.
      iDestruct (big_opL_permutation with "Hclose_list_res") as "Hclose_list_res"; first (symmetry; done).
      cbn.
      iDestruct "Hclose_list_res" as "( Hv0 & Hv1 & Hv2 & Hv3 & $)".
      iDestruct "Hv0" as (? P0 ?) "[Hv0 #Hrel0]".
      iDestruct "Hv1" as (? P1 ?) "[Hv1 #Hrel1]".
      iDestruct "Hv2" as (? P2 ?) "[Hv2 #Hrel2]".
      iDestruct "Hv3" as (? P3 ?) "[Hv3 #Hrel3]".
      iClear "Hinterp_callee_wstk".
      iFrame "#".
      iDestruct "Hv0" as (W0') "[%HW0' (%v0 & % & [$ [#H0 H0']])]".
      iDestruct "Hv1" as (W1') "[%HW1' (%v1 & % & [$ [#H1 H1']])]".
      iDestruct "Hv2" as (W2') "[%HW2' (%v2 & % & [$ [#H2 H2']])]".
      iDestruct "Hv3" as (W3') "[%HW3' (%v3 & % & [$ [#H3 H3']])]".
      (* iFrame "%". *)
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
      iRewrite - ("HP0" $! (W0',C,v0)) in "H0'".
      iRewrite - ("HP1" $! (W1',C,v1)) in "H1'".
      iRewrite - ("HP2" $! (W2',C,v2)) in "H2'".
      iRewrite - ("HP3" $! (W3',C,v3)) in "H3'".
      iDestruct ("Hrcond_astk0" with "H0'") as "#Hinterp0"; cbn.
      iDestruct ("Hrcond_astk1" with "H1'") as "#Hinterp1"; cbn.
      iDestruct ("Hrcond_astk2" with "H2'") as "#Hinterp2"; cbn.
      iDestruct ("Hrcond_astk3" with "H3'") as "#Hinterp3"; cbn.
      iSplitR.
      {
        rewrite /load_word.
        rewrite (notisDRO_flowsfrom RWL p_astk0); eauto.
        rewrite (notisDRO_flowsfrom RWL p_astk1); eauto.
        rewrite (notisDRO_flowsfrom RWL p_astk2); eauto.
        rewrite (notisDRO_flowsfrom RWL p_astk3); eauto.
        rewrite (notisDL_flowsfrom RWL p_astk0); eauto.
        rewrite (notisDL_flowsfrom RWL p_astk1); eauto.
        rewrite (notisDL_flowsfrom RWL p_astk2); eauto.
        rewrite (notisDL_flowsfrom RWL p_astk3); eauto.
        iFrame "#%".
      }
      iSplitL "H0 H0'".
      { iSplitR "H0'"; first iFrame "%".
        iSplitR "H0'"; first iFrame "%".
        iSplitR "H0'"; cycle 1.
        + iExists W0'; iFrame "%".
          iRewrite - ("HP0" $! (W0',C,WInt 0)).
          iApply "Hwcond_astk0"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP0" $! (W',C,WInt 0)).
          iApply "Hwcond_astk0"; iApply interp_int.
      }
      iSplitL "H1 H1'".
      { iSplitR "H1'"; first iFrame "%".
        iSplitR "H1'"; first iFrame "%".
        iSplitR "H1'"; cycle 1.
        + iExists W1'; iFrame "%".
          iRewrite - ("HP1" $! (W1',C,WInt 0)).
          iApply "Hwcond_astk1"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP1" $! (W',C,WInt 0)).
          iApply "Hwcond_astk1"; iApply interp_int.
      }
      iSplitL "H2 H2'".
      { iSplitR "H2'"; first iFrame "%".
        iSplitR "H2'"; first iFrame "%".
        iSplitR "H2'"; cycle 1.
        + iExists W2'; iFrame "%".
          iRewrite - ("HP2" $! (W2',C,WInt 0)).
          iApply "Hwcond_astk2"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP2" $! (W',C,WInt 0)).
          iApply "Hwcond_astk2"; iApply interp_int.
      }
      { iSplitR "H3'"; first iFrame "%".
        iSplitR "H3'"; first iFrame "%".
        iSplitR "H3'"; cycle 1.
        + iExists W3'; iFrame "%".
          iRewrite - ("HP3" $! (W3',C,WInt 0)).
          iApply "Hwcond_astk3"; iApply interp_int.
        + iIntros "!> % % % _".
          iRewrite - ("HP3" $! (W',C,WInt 0)).
          iApply "Hwcond_astk3"; iApply interp_int.
      }
    }

    iDestruct (lc_fupd_elim_later with "[$] [$H]") as ">H".
    iModIntro.
    iDestruct "H" as (l') "($ & $ & (%&%&%&%& $&$&$&$&(%W0'&%HW0'&H0)&(%W1'&%HW1'&H1)&(%W2'&%HW2'&H2)&(%W3'&%HW3'&H3)) & ($&$&$&?))".
    iDestruct (interp_monotone W0' Wfixed with "[] H0") as "$"; first done.
    iDestruct (interp_monotone W1' Wfixed with "[] H1") as "$"; first done.
    iDestruct (interp_monotone W2' Wfixed with "[] H2") as "$"; first done.
    iDestruct (interp_monotone W3' Wfixed with "[] H3") as "$"; first done.
    iFrame.
    Qed.

    Lemma world_interp_stack_fixing
      (Wcur W0 : WORLD) (C : CmptName)
      (a_stk4 b_stk csp_b csp_e : Addr) (l : list Addr)
      ccrel
      :

      let a_stk := (csp_b ^+ -4)%a in
      let Wfixed := close_list (l ++ finz.seq_between csp_b csp_e) Wcur in
      let closing_region := finz.seq_between csp_b csp_e in

      ((csp_b ^+ -4) ^+ 3 < csp_e)%a ->
      (b_stk <= csp_b ^+ -4)%a ->
      (csp_b ^+ -4 + 4)%a = Some a_stk4 ->

      related_sts_pub_world W0 Wfixed ->
      interp W0 C
        (WCap RWL Local
           (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) csp_e
           a_stk) -∗
      world_interp Wcur C -∗
      [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]] -∗
      [[a_stk4,csp_e]]↦ₐ[[region_addrs_zeroes a_stk4 csp_e]] -∗

      CloseRes_gen Wcur Wfixed C csp_b csp_e a_stk l ccrel -∗

      £ 1 -∗
      |={⊤}=>
            world_interp Wfixed C
            ∗ (if (is_untrusted_caller ccrel)
               then True
               else [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]]
              )
    .
    Proof.
      intros a_stk Wfixed closing_region.
      iIntros (He_a1 Hb_a4 Ha_stk4 Hrelated_pub_W0_Wfixed)
        "#Hinterp_callee_wstk Hworld_interp Hstk' Hstk Hrevoked Hlc''".

      iAssert ( ▷( close_list_resources_gen C Wcur (l++(finz.seq_between csp_b csp_e)) (finz.seq_between csp_b csp_e) false) )%I with "[Hstk]" as "Hstk".
      {
        replace a_stk4 with (a_stk ^+4)%a by (subst a_stk; solve_addr+Ha_stk4 He_a1).
        replace (a_stk ^+4)%a with csp_b by (subst a_stk; solve_addr+Ha_stk4 He_a1).
        iAssert (interp W0 C (WCap RWL Local csp_b csp_e a_stk)) as "Hvalid".
        {
          rewrite /is_untrusted_caller_frm /=; destruct (is_untrusted_caller ccrel); auto.
          iApply (interp_weakening _ _ _ _ _ _ b_stk csp_b with "[]Hinterp_callee_wstk"); auto.
          + subst a_stk; solve_addr+Ha_stk4 He_a1 Hb_a4.
          + subst a_stk; solve_addr+Ha_stk4 He_a1 Hb_a4.
          + iApply fundamental_ih.
        }

        iDestruct (write_allowed_inv_full_cap with "Hvalid") as "-#H"; auto.
        iClear "#";clear-Hrelated_pub_W0_Wfixed.
        rewrite /region_pointsto.
        rewrite big_sepL2_replicate_r; last by rewrite finz_seq_between_length.
        iDestruct (big_sepL_sep with "[$Hstk $H]") as "H".
        iNext.
        iApply (big_sepL_impl with "H").
        iIntros "!> %%% [Hv (%&%&%&%&Hrel&#Hzcond&#Hrcond&#Hwcond&Hmono)]".
        iExists x0, (safeC x1). iFrame.
        iSplit.
        { iPureIntro; intros W. rewrite /persistent_cond in H1.
          specialize (H1 W).
          apply _.
        }
        iFrame "%".
        iSplit; first (iPureIntro; eapply notisO_flowsfrom; eauto).
        iSplit.
        { erewrite isWL_flowsto;eauto.
          rewrite /future_pub_mono.
          iIntros "!> %%% H".
          iApply "Hzcond"; auto.
        }
        iApply "Hwcond"; iApply interp_int.
      }
      iDestruct (lc_fupd_elim_later with "[$] [$Hstk]") as ">Hstk".

      rewrite /CloseRes_gen.
      destruct (is_untrusted_caller ccrel).
      - (* caller is untrusted, we need to re-instate the whole stack frame *)
        iMod (reinstate_close_list_gen _ _ (l++closing_region) with
               "[$Hworld_interp Hrevoked Hstk Hstk']") as "Hworld_interp"; last by iFrame.
        iDestruct "Hrevoked" as (l') "(%Hl & Hclose_list_res & (Hrev0 & Hrev1 & Hrev2 & Hrev3 & _) )".
        rewrite /close_list_resources_gen.
        rewrite big_sepL_app.
        iSplitR "Hstk"; last done.
        iApply big_opL_permutation; first (symmetry; done).
        rewrite big_sepL_app.
        iFrame.
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
        rewrite /close_addr_resources_gen.
        iSplitL "Hrev0 Ha_stk0".
        { iFrame "Ha_stk0".
          iDestruct "Hrev0" as " (%p & %P & $ & ($ & $ & $) & $)".
        }
        iSplitL "Hrev1 Ha_stk1".
        { iFrame "Ha_stk1".
          iDestruct "Hrev1" as " (%p & %P & $ & ($ & $ & $) & $)".
        }
        iSplitL "Hrev2 Ha_stk2".
        { iFrame "Ha_stk2".
          iDestruct "Hrev2" as " (%p & %P & $ & ($ & $ & $) & $)".
        }
        iSplitL "Hrev3 Ha_stk3".
        { iFrame "Ha_stk3".
          iDestruct "Hrev3" as " (%p & %P & $ & ($ & $ & $) & $)".
        }
        done.

      - (* caller is trusted, we need only need re-instate callee's stack frame *)
        iFrame "Hstk'".
        iMod (reinstate_close_list_gen _ _ (l++closing_region) with
               "[$Hworld_interp Hrevoked Hstk]") as "Hworld_interp"; last by iFrame.
        rewrite /close_list_resources_gen big_sepL_app.
        iFrame.
    Qed.

End switcher_helper.
