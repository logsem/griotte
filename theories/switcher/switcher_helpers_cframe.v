From iris.proofmode Require Import proofmode.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import region_invariants_revocation.
From griotte Require Export world_ghost_theory world_interp_stack.
From griotte Require Import switcher_preamble.
From griotte Require Import map_simpl.

Section switcher_helpers_cframe.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
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
    iIntros "([Hr Hsts] & Htemp)".
    iMod (monotone_close_list_region_gen W W _ l with "[$Hr $Hsts $Htemp]") as "[Hsts Hr]"; iFrame.
    done.
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

  (** The four words of the register-save area below [csp_b] are in the
      list [l] of revoked addresses, so [l] can be permuted to put them
      first. *)
  Lemma stack_frame_in_revoked
    (W0 : WORLD) (b_stk csp_b csp_e a_stk4 : Addr) (l : list Addr) :
    (b_stk <= csp_b ^+ -4)%a ->
    ((csp_b ^+ -4) ^+ 3 < csp_e)%a ->
    (csp_b ^+ -4 + 4)%a = Some a_stk4 ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary → a ∈ l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : Addr, a ∈ finz.seq_between b_stk csp_e → std W0 !! a = Some Temporary) ->
    ∃ l', l ≡ₚ [(csp_b ^+ -4)%a; ((csp_b ^+ -4) ^+ 1)%a; ((csp_b ^+ -4) ^+ 2)%a; ((csp_b ^+ -4) ^+ 3)%a] ++ l'.
  Proof.
    intros Hb_a4 He_a1 Ha_stk4 Htemp_revoked Hstk_tmp.
    assert (Hin : ∀ a : Addr, (b_stk <= a)%a → (a < csp_b)%a → a ∈ l).
    { intros a Hba Hac.
      assert (Ha : a ∈ l ++ finz.seq_between csp_b csp_e).
      { apply Htemp_revoked, Hstk_tmp, elem_of_finz_seq_between; solve_addr. }
      apply elem_of_app in Ha as [?|Ha]; first done.
      apply elem_of_finz_seq_between in Ha; solve_addr. }
    set (a_stk := (csp_b ^+ -4)%a) in *.
    pose proof (Hin a_stk ltac:(subst a_stk; solve_addr) ltac:(subst a_stk; solve_addr)) as H0.
    pose proof (Hin (a_stk ^+ 1)%a ltac:(subst a_stk; solve_addr) ltac:(subst a_stk; solve_addr)) as H1.
    pose proof (Hin (a_stk ^+ 2)%a ltac:(subst a_stk; solve_addr) ltac:(subst a_stk; solve_addr)) as H2.
    pose proof (Hin (a_stk ^+ 3)%a ltac:(subst a_stk; solve_addr) ltac:(subst a_stk; solve_addr)) as H3.
    clear Hin Htemp_revoked Hstk_tmp.
    apply elem_of_Permutation in H0 as [l0 Hl0].
    rewrite Hl0 in H1,H2,H3.
    apply elem_of_cons in H3 as [Hcontra | H3]; first (subst a_stk; solve_addr).
    apply elem_of_cons in H2 as [Hcontra | H2]; first (subst a_stk; solve_addr).
    apply elem_of_cons in H1 as [Hcontra | H1]; first (subst a_stk; solve_addr).
    apply elem_of_Permutation in H1 as [l1 Hl1].
    rewrite Hl1 in H2,H3.
    apply elem_of_cons in H3 as [Hcontra | H3]; first (subst a_stk; solve_addr).
    apply elem_of_cons in H2 as [Hcontra | H2]; first (subst a_stk; solve_addr).
    apply elem_of_Permutation in H2 as [l2 Hl2].
    rewrite Hl2 in H3.
    apply elem_of_cons in H3 as [Hcontra | H3]; first (subst a_stk; solve_addr).
    apply elem_of_Permutation in H3 as [l3 Hl3].
    exists l3.
    by rewrite Hl0 Hl1 Hl2 Hl3.
  Qed.

  (** Opening one revoked address [a'] of a safe stack capability. *)
  Lemma open_revoked_stack_addr
    (W0 Wcur : WORLD) (C : CmptName) (b e a a' : Addr) (l : list Addr) :
    (b <= a')%a -> (a' < e)%a ->
    interp W0 C (WCap RWL Local b e a) -∗
    close_addr_resources_gen C Wcur l a' false -∗
    ▷ ((∃ w, a' ↦ₐ w ∗ (∃ W', ⌜related_sts_pub_world W' (close_list l Wcur)⌝ ∗ interp W' C w))
       ∗ (∃ (p : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
            ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝
            ∗ (⌜isO p = false⌝
               ∗ (if isWL p
                  then future_pub_mono C φ (WInt 0)
                  else if isDL p then future_pub_mono C φ (WInt 0) else future_priv_mono C φ (WInt 0))
               ∗ (∃ W0', ⌜related_sts_pub_world W0' (close_list l Wcur)⌝ ∗ φ (W0', C, WInt 0)))
            ∗ rel C a' p φ)).
  Proof.
    iIntros (Hba He) "#Hinterp Hv".
    iDestruct (write_allowed_inv _ _ a' with "Hinterp")
      as (p_a φ_a) "(%Hp_a & _ & Hrel_a & _ & Hwcond_a & Hrcond_a & _)"; auto.
    rewrite /close_addr_resources_gen.
    iDestruct "Hv" as (? P0 ?) "[Hv #Hrel0]".
    iDestruct "Hv" as (W0') "[%HW0' (%v0 & % & [Ha [#H0 H0']])]".
    iDestruct (rel_agree _ _ (safeC φ_a) P0 with "[$Hrel_a $Hrel0]") as "[<- HP0]".
    rewrite (readAllowed_flowsto RWL p_a Hp_a eq_refl).
    iNext.
    iRewrite - ("HP0" $! (W0',C,v0)) in "H0'".
    iDestruct ("Hrcond_a" with "H0'") as "#Hinterp0"; cbn.
    iSplitL "Ha".
    { iExists v0; iFrame "Ha".
      rewrite /load_word.
      rewrite (notisDRO_flowsfrom RWL p_a Hp_a eq_refl) (notisDL_flowsfrom RWL p_a Hp_a eq_refl).
      iExists W0'; iFrame "Hinterp0 %". }
    iExists p_a, P0; iFrame "Hrel0".
    rewrite (isWL_flowsto RWL p_a Hp_a eq_refl).
    iSplit; first iFrame "%".
    iSplit; first iFrame "%".
    iSplit.
    + iIntros "!> % % % _".
      iRewrite - ("HP0" $! (W',C,WInt 0)).
      iApply "Hwcond_a"; iApply interp_int.
    + iExists W0'; iFrame "%".
      iRewrite - ("HP0" $! (W0',C,WInt 0)).
      iApply "Hwcond_a"; iApply interp_int.
  Qed.

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

        destruct (stack_frame_in_revoked W0 b_stk csp_b csp_e a_stk4 l)
          as [l3 Hl0]; auto.
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
    { iExists l3.
      iSplit; first iFrame "%".
      rewrite /close_list_resources_gen.
      iDestruct (big_opL_permutation with "Hclose_list_res") as "Hclose_list_res"; first (symmetry; done).
      cbn.
      iDestruct "Hclose_list_res" as "(Hv0 & Hv1 & Hv2 & Hv3 & $)".
      iDestruct (open_revoked_stack_addr with "Hinterp_callee_wstk Hv0") as "H0";
        [subst a_stk; solve_addr+Hb_a4 He_a1..|].
      iDestruct (open_revoked_stack_addr with "Hinterp_callee_wstk Hv1") as "H1";
        [subst a_stk; solve_addr+Hb_a4 He_a1..|].
      iDestruct (open_revoked_stack_addr with "Hinterp_callee_wstk Hv2") as "H2";
        [subst a_stk; solve_addr+Hb_a4 He_a1..|].
      iDestruct (open_revoked_stack_addr with "Hinterp_callee_wstk Hv3") as "H3";
        [subst a_stk; solve_addr+Hb_a4 He_a1..|].
      iNext.
      iDestruct "H0" as "[(%v0 & Ha0 & Hw0) $]".
      iDestruct "H1" as "[(%v1 & Ha1 & Hw1) $]".
      iDestruct "H2" as "[(%v2 & Ha2 & Hw2) $]".
      iDestruct "H3" as "[(%v3 & Ha3 & Hw3) $]".
      iExists v0, v1, v2, v3; iFrame.
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

End switcher_helpers_cframe.
