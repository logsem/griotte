From cap_machine.ftlr Require Export Jmp Jnz Mov Load Store AddSubLt Restrict
  Subseg Get Lea Seal UnSeal.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel register_tactics.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ} {sealsg: sealStoreG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Theorem fundamental_cap W regs p g b e (a : Addr) :
    ⊢ interp W (WCap p g b e a) →
      interp_expression regs W (WCap p g b e a).
  Proof.
    iIntros "#Hinv_interp /=".
    iIntros "[[Hfull Hreg] [Hmreg [Hr [Hsts Hown]]]]".

    assert ( readAllowed p = true \/ readAllowed p = false )
      as [Hread_p|Hread_p] by (destruct p ; naive_solver)
    ; cycle 1.
    { (* if p not readable, then execution will fail *)
      iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
      iApply (wp_bind (fill [SeqCtx])).
      rewrite /registers_pointsto.
      iExtract "Hmreg" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); eauto.
      intro Hcontra ; destruct p ; inv Hcontra; naive_solver.
      iNext. iIntros "HPC /=".
      iApply wp_pure_step_later; auto.
      iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    }
    clear Hread_p.

    iRevert "Hinv_interp".
    iLöb as "IH'" forall (W regs p g b e a).
    iAssert ftlr_IH as "IH" ; [|iClear "IH'"].
    { iModIntro; iNext.
      iIntros (W_ih r_ih p_ig g_ih b_ih e_ih a_ih) "%Hfull #Hregs Hmreg Hr Hsts Hown % Hrcond".
      iApply ("IH'" with "[%] [] [Hmreg] [$Hr] [$Hsts] [$Hown]"); eauto.
    }
    iIntros "#Hinv_interp".
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (WCap p g b e a))) as [i|] ; cycle 1.
    { (* Not correct PC *)
      rewrite /registers_pointsto.
      iExtract "Hmreg" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); eauto.
      iNext. iIntros "HPC /=".
      iApply wp_pure_step_later; auto.
      iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    }

    (* Correct PC *)
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }

    iAssert (⌜p = RX⌝ ∨ ⌜p = RWX⌝  ∨ ⌜(p = RWLX ∧ g = Local) ⌝)%I as "%Hp".
    { (* if not, contradiction by correctPC or validity *)
      inv i; subst; auto.
      inv H6; auto.
      inv H0; auto.
      iRight; iRight; iSplit; auto.
      destruct g; auto.
      rewrite fixpoint_interp1_eq //=.
    }

    assert (readAllowed p = true)
      as Hread_p by (destruct Hp as [ -> | [ -> | [ -> -> ] ] ]; done).
    iDestruct (readAllowed_implies_region_conditions with "Hinv_interp")
      as "#Hinv"; eauto.

    iDestruct (extract_from_region_inv_regs a a with "[Hmreg] Hinv") as (P Hpers) "(#Hinva & #Hrcond & #Hwcond)";auto;[iFrame "# %"|].
    iDestruct (extract_from_region_inv _ _ a with "Hinv") as "[_ Hstate_a]";auto.
    iDestruct "Hstate_a" as %Hstate_a.
    assert (∃ (ρ : region_type), (std W) !! a = Some ρ ∧ ρ ≠ Revoked
                                 ∧ (∀ g, ρ ≠ Monostatic g) )
      as [ρ [Hρ [Hne_rev Hne_mono  ] ] ].
    { destruct (pwl p); [rewrite Hstate_a;eexists;eauto|].
      destruct g; [rewrite Hstate_a|rewrite Hstate_a];eexists;eauto. }
    iDestruct (region_open W a with "[$Hinva $Hr $Hsts]")
      as (w) "(Hr & Hsts & Hstate & Ha & #Hmono & Hw) /=";[|apply Hρ|].
    { destruct ρ;auto;[done|by ospecialize (Hne_mono _)]. }
    rewrite /registers_pointsto ; iExtract "Hmreg" PC as "HPC".

    destruct (decodeInstrW w) eqn:Hi. (* proof by cases on each instruction *)
    + (* Jmp *)
      iApply (jmp_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Jnz *)
      iApply (jnz_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Mov *)
      iApply (mov_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Load *)
      iApply (load_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Store *)
      iApply (store_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Lt *)
      iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Add *)
      iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Sub *)
      iApply (add_sub_lt_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Lea *)
      iApply (lea_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Restrict *)
      iApply (restrict_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Subseg *)
      iApply (subseg_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* GetB *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetB _ _) with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* GetE *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetE _ _) with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* GetA *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetA _ _) with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* GetP *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetP _ _) with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* GetL *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetL _ _) with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* GetWType *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetWType _ _) with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* GetOType *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ (GetOType _ _) with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Seal *)
      iApply (seal_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* UsSeal *)
      iApply (unseal_case with "[] [] [] [] [Hmono] [] [] [Hw] [Hsts] [Hown] [Hr] [Hstate] [Ha] [HPC] [Hmreg]");
        try iAssumption; eauto.
    + (* Fail *)
      iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto; iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    + (* Halt *)
      iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iDestruct (region_close _ _ _ _ ρ with "[$Hr $Ha $Hstate $Hmono Hw]") as "Hr";[auto|iFrame "#"; auto|].
      { destruct ρ;auto;[|ospecialize (Hne_mono _)]; contradiction. }
      iApply wp_pure_step_later; auto; iNext ; iIntros "_".
      iApply wp_value.
      iInsert "Hmreg" PC.
      iIntros (_).
      iExists (<[PC:=WCap p g b e a]> regs),W. iFrame.
      iAssert (⌜related_sts_priv_world W W⌝)%I as "#Hrefl".
      { iPureIntro. apply related_sts_priv_refl_world. }
      iFrame "#".
      iAssert (∀ r0 : RegName, ⌜is_Some (<[PC:=WCap p g b e a]> regs !! r0)⌝)%I as "HA".
      { iIntros. destruct (reg_eq_dec PC r0).
        - subst r0; rewrite lookup_insert; eauto.
        - rewrite lookup_insert_ne; auto. }
      iExact "HA".
      Unshelve. apply _.
  Qed.

  Theorem fundamental W w regs :
    ⊢ interp W w -∗ interp_expression regs W w.
  Proof.
    iIntros "Hw". destruct w as [| [c | ] | ].
    2: { iApply fundamental_cap. done. }
    all: iClear "Hw"; iIntros "(? & Hreg & ?)"; unfold interp_conf.
    all: iApply (wp_wand with "[-]"); [ | iIntros (?) "H"; iApply "H"].
    all: iApply (wp_bind (fill [SeqCtx])); cbn.
    all: unfold registers_pointsto; rewrite -insert_delete_insert.
    all: iDestruct (big_sepM_insert with "Hreg") as "[HPC ?]"; first by rewrite lookup_delete.
    all: iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
    all: iNext; iIntros; cbn; iApply wp_pure_step_later; auto.
    all: iNext; iIntros "_"; iApply wp_value; iIntros (?); congruence.
  Qed.

  (* The fundamental theorem implies the exec_cond *)

  (* TODO fix the model *)
  Lemma interp_exec_cond W p g b e a :
    p ≠ E ->
    interp W (WCap p g b e a) -∗ exec_cond W b e g p interp.
  Proof.
    iIntros (Hp) "#Hw".
    iIntros (a0 r W' Hin) "#Hfuture". iModIntro.
    destruct g.
    + iDestruct (interp_monotone_nm_nl with "Hfuture [] Hw") as "Hw'";[auto|].
      iApply fundamental;eauto.
      destruct p ; rewrite !fixpoint_interp1_eq //=.
    (* + rewrite /future_world. *)
    (*   iDestruct (interp_monotone with "Hfuture Hw") as "Hw'";[auto|]. *)
    (*   iDestruct (readAllowed_implies_region_conditions with "Hw'") as "Hread_cond";[destruct Hra as [-> | [-> | ->] ];auto|]. *)
    (*   iApply fundamental;[|eauto]. destruct Hra as [-> | [-> | ->] ];auto. *)
    (*   rewrite fixpoint_interp1_eq /=. done. *)
    (* iApply fundamental. *)
    (* rewrite !fixpoint_interp1_eq /=. destruct p; try done. *)
  Admitted.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)

  Lemma exec_wp W p g b e a :
    isCorrectPC (WCap p g b e a) ->
    exec_cond W b e g p interp -∗
    ∀ r W', future_world g W W' → ▷ ((interp_expr interp r) W') (WCap p g b e a).
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
  Qed.

  (* updatePcPerm adds a later because of the case of E-capabilities, which
     unfold to ▷ interp_expr *)
  Lemma interp_updatePcPerm W w :
    ⊢ interp W w -∗ ▷ (∀ regs, interp_expression regs W (updatePcPerm w)).
  Proof.
    iIntros "#Hw".
    assert ((∃ g b e a, w = WCap E g b e a) ∨ updatePcPerm w = w) as [Hw | ->].
    { destruct w as [ | [ | ] | ]; eauto. unfold updatePcPerm.
      case_match; eauto; naive_solver.
    }
    { destruct Hw as [ g [b [e [a ->] ] ] ].
      rewrite fixpoint_interp1_eq /=.
      iIntros (rmap). iSpecialize ("Hw" $! rmap). iDestruct "Hw" as "#Hw".
      iPoseProof (futureworld_refl g W) as "Hfuture".
      iSpecialize ("Hw" $! W (futureworld_refl g W)).
      iNext. iIntros "(HPC & Hr & ?)".
      iApply "Hw"; eauto. iFrame.
    }
    { iNext. iIntros (rmap). iApply fundamental; eauto. }
  Qed.

  Lemma jmp_or_fail_spec W w φ :
    (interp W w
     -∗ (if decide (isCorrectPC (updatePcPerm w))
         then (∃ p g b e a,
                  ⌜w = WCap p g b e a⌝
                  ∗ □ ∀ regs W', future_world g W W'
                              → ▷ ((interp_expr interp regs) W') (updatePcPerm w))
         else φ FailedV ∗ PC ↦ᵣ updatePcPerm w
                          -∗ WP Seq (Instr Executable) {{ φ }} )).
  Proof.
    iIntros "#Hw".
    destruct (decide (isCorrectPC (updatePcPerm w))).
    - inversion i.
      destruct w;inv H. destruct sb; inv H3.
      destruct H1 as [-> | [-> | ->] ].
      + destruct p0; cbn in * ; simplify_eq.
        * iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
          iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|].
          iApply exec_wp;auto.
        * iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
          rewrite /= fixpoint_interp1_eq /=.
          iExact "Hw".
      + destruct p0; cbn in *; simplify_eq.
        iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|].
        iApply exec_wp;auto.
      + destruct p0; cbn in *; simplify_eq.
        iExists _,_,_,_,_; iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|].
        iApply exec_wp;auto.
    - iIntros "[Hfailed HPC]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC");eauto.
      iNext. iIntros "_". iApply wp_pure_step_later;auto.
      iNext; iIntros "_". iApply wp_value. iFrame.
  Qed.

End fundamental.
