From cap_machine.binary_model.ftlr_binary Require Export Mov_binary Jmp_binary Jnz_binary Load_binary Store_binary AddSubLt_binary Lea_binary Restrict_binary Subseg_binary IsPtr_binary Get_binary StoreU_binary LoadU_binary PromoteU_binary.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Export logrel_binary region_invariants_binary.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ} {cfgg : cfgSG Σ}
          `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := (WORLD -n> (prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types v : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types interp : (D).

  Lemma extract_r_ex r (reg : RegName) :
    (∃ w, r !! reg = Some w) →
    ⊢ (([∗ map] r0↦w ∈ r, r0 ↦ᵣ w) → ∃ w, reg ↦ᵣ w).
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w.
    iApply (big_sepM_lookup (λ reg' i, reg' ↦ᵣ i)%I r reg w); eauto.
  Qed.

  Lemma extract_r_ex_spec r (reg : RegName) :
    (∃ w, r !! reg = Some w) →
    ⊢ (([∗ map] r0↦w ∈ r, r0 ↣ᵣ w) → ∃ w, reg ↣ᵣ w).
  Proof.
    intros [w Hw].
    iIntros "Hmap". iExists w.
    iApply (big_sepM_lookup (λ reg' i, reg' ↣ᵣ i)%I r reg w); eauto.
  Qed.

  Lemma extract_r reg (r : RegName) w :
    reg !! r = Some w →
    ⊢ (([∗ map] r0↦w ∈ reg, r0 ↦ᵣ w) →
      (r ↦ᵣ w ∗ (∀ x', r ↦ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↦ᵣ y))).
  Proof.
    iIntros (Hw) "Hmap".
    iDestruct (big_sepM_lookup_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ (r : RegName) i, r ↦ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto.
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Lemma extract_r_spec reg (r : RegName) w :
    reg !! r = Some w →
    ⊢ (([∗ map] r0↦w ∈ reg, r0 ↣ᵣ w) →
      (r ↣ᵣ w ∗ (∀ x', r ↣ᵣ x' -∗ [∗ map] k↦y ∈ <[r := x']> reg, k ↣ᵣ y))).
  Proof.
    iIntros (Hw) "Hmap".
    iDestruct (big_sepM_lookup_acc (λ (r : RegName) i, r ↣ᵣ i)%I reg r w) as "Hr"; eauto.
    iSpecialize ("Hr" with "[Hmap]"); eauto. iDestruct "Hr" as "[Hw Hmap]".
    iDestruct (big_sepM_insert_acc (λ (r : RegName) i, r ↣ᵣ i)%I reg r w) as "Hupdate"; eauto.
    iSpecialize ("Hmap" with "[Hw]"); eauto.
    iSpecialize ("Hupdate" with "[Hmap]"); eauto.
  Qed.

  Instance addr_inhabited: Inhabited Addr := populate (A 0%Z eq_refl eq_refl).

  Global Instance ifcond_pers : Persistent (if writeAllowed p then read_write_cond a interp else ∃ P : D, ⌜∀ Wv : WORLD * (prodO (leibnizO Word) (leibnizO Word)), Persistent (P Wv.1 Wv.2)⌝ ∧ read_cond a P interp)%I.
  Proof. intros. destruct (writeAllowed p);apply _. Qed.
  Global Instance ifwcond_pers : Persistent (if decide (writeAllowed_in_r_a (<[PC:=inr (p, g, b, e, a)]> r) a) then wcond P interp else emp)%I.
  Proof. intros. case_decide;apply _. Qed.
  Global Instance if_pers (P: D) : Persistent (if decide (ρ = Monotemporary)
                                               then future_pub_a_mono a (λ Wv, P Wv.1 Wv.2) w1 w2
                                               else future_priv_mono (λ Wv, P Wv.1 Wv.2) w1 w2).
  Proof. intros. case_decide;apply _. Qed.

  Theorem fundamental_binary W r p g b e (a : Addr) :
    ⊢ ((⌜p = RX⌝ ∨ ⌜p = RWX⌝ ∨ ⌜p = RWLX ∧ g = Directed⌝) →
       spec_ctx →
       region_conditions W p g b e →
       interp_expression r W (inr ((p,g),b,e,a),inr ((p,g),b,e,a))).
  Proof.
    iIntros (Hp) "#Hspec #Hinv /=".
    iIntros "[Hregs [Hmreg [Hsreg [Hr [Hsts [Hown Hj]]]]]]".
    iSplit; eauto; simpl.
    iRevert (Hp) "Hinv".
    iLöb as "IH" forall (W r p g b e a).
    iAssert (⌜∀ w, <[PC:=w]> r.1 = <[PC:=w]> r.2⌝)%I as %Heqregs.
    { iIntros (w). iDestruct (interp_reg_eq _ _ _ w with "Hregs") as %Heqregs. auto. }
    iDestruct "Hregs" as "[Hfull Hreg]".
    iIntros (Hp) "#Hinv".
    rewrite -Heqregs.
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (inr ((p,g),b,e,a)))).
    - (* Correct PC *)
      assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
      { eapply in_range_is_correctPC; eauto.
        unfold le_addr; lia. }
      iDestruct (extract_from_region_inv_regs a a with "[Hmreg] Hinv") as (P Hpers) "(#Hinva & #Hrcond & #Hwcond)";auto;[|iFrame "# %"|].
      { destruct Hp as [-> | [-> | [? ->] ] ];auto. subst;auto. }
      iDestruct (extract_from_region_inv _ _ a with "Hinv") as "[_ Hstate_a]";auto.
      iDestruct "Hstate_a" as %Hstate_a.
      assert (∃ (ρ : region_type), (std W) !! a = Some ρ ∧ ρ ≠ Revoked
                                   ∧ (∀ g, ρ ≠ Monostatic g) ∧ (∀ w, ρ ≠ Uninitialized w))
        as [ρ [Hρ [Hne_rev [Hne_mono Hne_uninit] ] ] ].
      { destruct (machine_base.pwl p); [rewrite Hstate_a;eexists;eauto|].
        destruct g; [rewrite Hstate_a|rewrite Hstate_a|destruct Hstate_a as [-> | ->] ];eexists;eauto. }
      iDestruct (region_open W a with "[$Hinva $Hr $Hsts]")
        as (w1 w2) "(Hr & Hsts & Hstate & Ha & Ha' & #Hmono & Hw) /=";[|apply Hρ|..].
      { destruct ρ;auto;[done|by specialize (Hne_mono g0)|by specialize (Hne_uninit p0)]. }
      iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
        first apply (lookup_insert _ _ (inr (p, g, b, e, a))).
      iDestruct ((big_sepM_delete _ _ PC) with "Hsreg") as "[HsPC Hsmap]";
        first apply (lookup_insert _ _ (inr (p, g, b, e, a))).
      iAssert (▷ ⌜w1 = w2⌝)%I as "#>Heq".
      { iNext. iApply (interp_eq W). iDestruct "Hrcond" as "[Hrcond _]". iApply "Hrcond". iFrame. }
      iDestruct "Heq" as %<-.
      destruct (decodeInstrW w1) eqn:Hi. (* proof by cases on each instruction *)
      + (* Jmp *)
        iApply (jmp_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Jnz *)
        iApply (jnz_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Mov *)
        iApply (mov_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Load *)
        iApply (load_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Store *)
        iApply (store_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Lt *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Add *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Sub *)
        iApply (add_sub_lt_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Lea *)
        iApply (lea_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Restrict *)
        iApply (restrict_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Subseg *)
        iApply (subseg_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* IsPtr *)
        iApply (isptr_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* GetL *)
        iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetL _ _) with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* GetP *)
        iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetP _ _) with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* GetB *)
        iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetB _ _) with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* GetE *)
        iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetE _ _) with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* GetA *)
        iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetA _ _) with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]");
          try iAssumption; eauto.
      + (* Fail *)
        iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros (Hcontr); inversion Hcontr.
      + (* Halt *)
        iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
        iNext. iIntros "[HPC Ha] /=".
        iMod (step_halt _ [SeqCtx] with "[$HsPC $Ha' $Hj $Hspec]") as "(Hj & HsPC & Ha')";eauto.
        iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";auto.
        iDestruct (region_close _ _ _ _ _ ρ with "[$Hr $Ha $Ha' $Hstate $Hmono Hw]") as "Hr";[auto|iFrame "#"; auto|].
        { destruct ρ;auto;[|specialize (Hne_mono g0)|specialize (Hne_uninit p0)]; contradiction. }
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=".
        apply lookup_insert. rewrite delete_insert_delete. iFrame.
        rewrite insert_insert. iNext. iIntros (_).
        iExists (<[PC:=inr (p, g, b, e, a)]> r.1,<[PC:=inr (p, g, b, e, a)]> r.1),W. iFrame.
        iAssert (⌜related_sts_priv_world W W⌝)%I as "#Hrefl".
        { iPureIntro. apply related_sts_priv_refl_world. }
        iFrame "#".
        iPureIntro. intros r0. destruct (reg_eq_dec PC r0).
        * subst r0; rewrite lookup_insert; eauto.
        * rewrite lookup_insert_ne//. destruct H with r0;eauto.
      + (* LoadU *)
      iApply (loadU_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]"); try iAssumption; eauto.
      + (* StoreU *)
        iApply (storeU_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]"); try iAssumption; eauto.
      + (* PromoteU *)
        iApply (promoteU_case with "[] [] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [Ha'] [HPC] [Hmap] [HsPC] [Hsmap] [Hj]"); try iAssumption; eauto.
   - (* Not correct PC *)
     iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
       first apply (lookup_insert _ _ (inr (p, g, b, e, a))).
     iApply (wp_notCorrectPC with "HPC"); eauto.
     iNext. iIntros "HPC /=".
     iApply wp_pure_step_later; auto.
     iApply wp_value.
     iNext. iIntros (Hcontr); inversion Hcontr.
     Unshelve. apply _.
  Qed.

  (* the execute condition can be regained using the FTLR on read allowed permissions *)
  Lemma interp_exec_cond_binary W p g b e a :
    p = RX ∨ p = RWX ∨ p = RWLX ->
    spec_ctx -∗
    interp W (inr (p,g,b,e,a),inr (p,g,b,e,a)) -∗ exec_cond W b e g p b e g p interp.
  Proof.
    iIntros (Hra) "#Hspec #Hw".
    iIntros (a0 r W' Hin) "#Hfuture". iModIntro.
    destruct g.
    + iDestruct (interp_monotone_nm with "Hfuture [] Hw") as "Hw'";[auto|].
      iDestruct (readAllowed_implies_region_conditions with "Hw'") as "Hread_cond";[destruct Hra as [-> | [-> | ->] ];auto|].
      iApply fundamental_binary;[|iFrame "#"|eauto]. destruct Hra as [-> | [-> | ->] ];auto.
      rewrite fixpoint_interp1_eq /=. done.
    + iDestruct (interp_monotone_nm with "Hfuture [] Hw") as "Hw'";[auto|].
      iDestruct (readAllowed_implies_region_conditions with "Hw'") as "Hread_cond";[destruct Hra as [-> | [-> | ->] ];auto|].
      iApply fundamental_binary;[|iFrame "#"|eauto]. destruct Hra as [-> | [-> | ->] ];auto.
      rewrite fixpoint_interp1_eq /=. done.
    + iDestruct (interp_monotone_a with "[Hfuture] Hw") as "Hw'";[auto|].
      2: iDestruct (readAllowed_implies_region_conditions with "Hw'") as "Hread_cond";[destruct Hra as [-> | [-> | ->] ];auto|].
      2: iApply fundamental_binary;[|iFrame "#"|eauto];destruct Hra as [-> | [-> | ->] ];auto.
      simpl. destruct Hra as [-> | [-> | ->] ];auto.
  Qed.

  Lemma fundamental_binary_from_interp_correctPC W p g b e a r (w:Word) :
    p = RX ∨ p = RWX ∨ (p = RWLX ∧ g = Directed) →
    ⊢ spec_ctx -∗ interp W (inr (p, g, b, e, a),w) -∗
      interp_expression r W (inr (p,g,b,e,a),w).
  Proof.
    iIntros (Hp) "HV Hv". iDestruct (interp_eq with "Hv") as %<-.
    iApply (fundamental_binary with "[] HV"); auto.
    iApply (readAllowed_implies_region_conditions with "Hv").
    destruct Hp as [-> | [-> | [ -> -> ] ] ]; eauto.
  Qed.

  Lemma fundamental_binary_not_correctPC r W p g b e a :
    ⊢ ⌜¬ isCorrectPC (inr ((p,g),b,e,a))⌝ →
    interp_expression r W (inr ((p,g),b,e,a),inr ((p,g),b,e,a)).
  Proof.
    iIntros (Hnvpc). iIntros "(H1 & Hmreg & H3 & H4 & H5)".
    iSplit;auto. rewrite /interp_conf.
    iDestruct ((big_sepM_delete _ _ PC) with "Hmreg") as "[HPC Hmap]";
      first apply (lookup_insert _ _ (inr (p, g, b, e, a))).
    iApply (wp_bind (fill [SeqCtx])).
    iApply (wp_notCorrectPC with "HPC"); eauto.
    iNext. iIntros "HPC /=".
    iApply wp_pure_step_later; auto.
    iApply wp_value.
    iNext. iIntros (Hcontr); inversion Hcontr.
  Qed.

  Corollary fundamental_binary_from_interp r W p g b e a (w : Word) :
    spec_ctx -∗
    interp W (inr ((p,g),b,e,a),w) -∗
    interp_expression r W (inr ((p,g),b,e,a),w).
  Proof.
    iIntros "#Hspec #Hinterp".
    iDestruct (interp_eq with "Hinterp") as %<-.
    destruct (decide (isCorrectPC (inr ((p,g),b,e,a)))).
    - assert (p = RX ∨ p = RWX ∨ p = RWLX) as Hp;[inversion i;auto|].
      iAssert (⌜p = RWLX → g = Directed⌝)%I as %Hmono.
      { iIntros (->). iDestruct (writeLocalAllowed_implies_local with "Hinterp") as %Hmono;[auto|destruct g;auto]. }
      iApply (fundamental_binary_from_interp_correctPC with "Hspec Hinterp").
      destruct Hp as [-> | [-> | ->] ];auto.
    - iApply fundamental_binary_not_correctPC. auto.
  Qed.

  Lemma updatePcPerm_RX w g b e a :
    inr (RX, g, b, e, a) = updatePcPerm w ->
    w = inr (RX, g, b, e, a) ∨ w = inr (E, g, b, e, a).
  Proof.
    intros Hperm.
    destruct w;inversion Hperm.
    destruct c,p,p,p,p;simplify_eq;auto.
  Qed.

  Lemma exec_binary_wp W p g b e a :
    isCorrectPC (inr (p, g, b, e, a)) ->
    exec_cond W b e g p b e g p interp -∗
    ∀ r W', future_world g e W W' → ▷ ((interp_expr interp r) W') (inr (p, g, b, e, a),inr (p, g, b, e, a)).
  Proof.
    iIntros (Hvpc) "Hexec".
    rewrite /exec_cond /enter_cond.
    iIntros (r W'). rewrite /future_world.
    assert (a ∈ₐ[[b,e]])%I as Hin.
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    destruct g.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a r W' Hin Hrelated).
      iFrame.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a r W' Hin Hrelated).
      iFrame.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a r W' Hin Hrelated).
      iFrame.
  Qed.

  (* The following lemma is to assist with a pattern when jumping to unknown valid capablities *)
  Lemma jmp_or_fail_binary_spec W (w w' : Word) φ :
    spec_ctx
    -∗ (interp W (w,w')
    -∗ (if decide (isCorrectPC (updatePcPerm w)) then
          (∃ p g b e a, ⌜w = inr (p,g,b,e,a)⌝
          ∗ □ ∀ r W', future_world g e W W' → ▷ ((interp_expr interp r) W') (updatePcPerm w,updatePcPerm w'))
        else
          φ FailedV ∗ PC ↦ᵣ updatePcPerm w -∗ WP Seq (Instr Executable) {{ φ }} )).
  Proof.
    iIntros "#Hspec #Hw".
    iDestruct (interp_eq with "Hw") as %<-.
    destruct (decide (isCorrectPC (updatePcPerm w))).
    - inversion i.
      destruct w;inversion H. destruct c,p0,p0,p0; inversion H.
      destruct H1 as [-> | [-> | ->] ].
      + destruct p0; simpl in H; simplify_eq.
        * iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
          iDestruct (interp_exec_cond_binary with "Hspec Hw") as "Hexec";[auto|].
          iApply exec_binary_wp;auto.
        * iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
          rewrite /= fixpoint_interp1_eq /=.
          iDestruct "Hw" as "[_ Hw]".
          iExact "Hw".
      + destruct p0; simpl in H; simplify_eq.
        iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond_binary with "Hspec Hw") as "Hexec";[auto|].
        iApply exec_binary_wp;auto.
      + destruct p0; simpl in H; simplify_eq.
        iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond_binary with "Hspec Hw") as "Hexec";[auto|].
        iApply exec_binary_wp;auto.
    - iIntros "[Hfailed HPC]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC");eauto.
      iNext. iIntros "_". iApply wp_pure_step_later;auto.
      iNext. iApply wp_value. iFrame.
  Qed.


End fundamental.
