From cap_machine.binary_model Require Export logrel_binary.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Import ftlr_base_binary monotone_binary.
From cap_machine.rules Require Import rules_base rules_Mov.
From cap_machine.binary_model.rules_binary Require Import rules_binary_Mov.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ} {cfgg : cfgSG Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := (WORLD -n> (prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types v : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types interp : (D).

  Lemma Mov_spec_determ r dst src regs regs' retv retv' :
    Mov_spec r dst src regs retv ->
    Mov_spec r dst src regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2;subst; simplify_eq.
    - split;auto.
    - split;auto.
  Qed.

  Lemma mov_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D):
    ftlr_instr W r p g b e a w (Mov dst src) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'. destruct Hsome with rr;eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    iMod (step_Mov _ [SeqCtx] with "[$Ha' $Hsmap $Hj $Hspec]") as (retv' regs'') "(Hs & #Hmovspec & Ha' & Hsmap) /=";eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'. destruct Hsome with rr;eauto. }
    iDestruct "Hmovspec" as %HSpec'.

    specialize (Mov_spec_determ _ _ _ _ _ _ _ HSpec HSpec') as [Hregs <-].

    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { (* TODO: it might be possible to refactor the proof below by using more simplify_map_eq *)
      (* TODO: use incrementPC_inv *)
      destruct Hregs as [<-|Hcontr];[|inversion Hcontr].
      match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs' & XX)
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      destruct (reg_eq_dec dst PC).
      { subst dst. rewrite lookup_insert in HPC. inv HPC.
        repeat rewrite insert_insert.
        destruct src; simpl in *; try discriminate.

        iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw $Ha']") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized p0)];contradiction. }
        destruct (reg_eq_dec PC r0).
        { subst r0. simplify_map_eq.
        iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.
        iApply ("IH" $! _ r with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [Hs]"); try iClear "IH"; eauto.
        rewrite -Heqregs. auto. }
        { iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.
          simplify_map_eq.
          assert (r.2 !! r0 = Some (inr (p'', g'', b'', e'', a''))) as H1.
          { rewrite -(lookup_insert_ne _ PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//. }
          rewrite /RegLocate. iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hr0". rewrite H0 H1.
          destruct (PermFlowsTo RX p'') eqn:Hpft.
          - iApply ("IH" $! _ r with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [Hs]"); try iClear "IH"; eauto.
            { rewrite -Heqregs. auto. }
            + destruct p''; simpl in Hpft; auto.
              repeat rewrite fixpoint_interp1_eq. simpl.
              destruct g''; auto.
            + iModIntro. rewrite /region_conditions.
              destruct p''; simpl in Hpft; try discriminate; repeat (rewrite fixpoint_interp1_eq);
                try (iDestruct "Hr0" as "[_ Hr0]"); simpl; auto.
              iApply (big_sepL_mono with "Hr0").
              intros. iIntros "H". iDestruct "H" as (P') "(?&?&?)".
              iApply bi.and_exist_r. iExists _. iFrame.
              destruct g''; auto.
              iDestruct "Hr0" as "[_ Hr0]". auto.
          - iApply (wp_bind (fill [SeqCtx])).
            iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
            iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p''; simpl in Hpft; try discriminate; eauto|].
            iNext. iIntros "HPC /=".
            iApply wp_pure_step_later; auto.
            iApply wp_value.
            iNext. iIntros. discriminate. } }
      { rewrite lookup_insert_ne in HPC; auto.
        rewrite lookup_insert in HPC. inv HPC.
        iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized p)];contradiction. }
        iApply ("IH" $! _ (<[dst:=w0]> _,<[dst:=w0]> _) with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); eauto.
        iSplit.
        - iPureIntro. intros; simpl.
          rewrite lookup_insert_is_Some.
          split. all: destruct (reg_eq_dec dst x0); auto; right; split; auto.
          all: rewrite lookup_insert_is_Some.
          all: destruct (reg_eq_dec PC x0); auto; right; split; destruct Hsome with x0;eauto.
        - iIntros (ri Hri).
          destruct (reg_eq_dec ri dst).
          + subst ri. rewrite /RegLocate lookup_insert.
            destruct src; simplify_map_eq.
            * repeat rewrite fixpoint_interp1_eq; auto.
            * destruct (reg_eq_dec PC r0).
              { subst r0.
                - simplify_map_eq.
                  rewrite (fixpoint_interp1_eq _ (inr (_, g'', b'', e'', a''),inr (_, g'', b'', e'', a''))) /=.
                destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; subst p''; try subst g'';
                  try (iFrame "Hexec"); try (iFrame "Hinv").
                iSplit;[auto|].
                iApply (big_sepL_mono with "Hinv").
                intros. iIntros "(H & ?)".
                simpl. iDestruct "H" as (P') "(?&?&?)".
                iExists _. iFrame. auto. auto.
              }
              simplify_map_eq.
              iDestruct ("Hreg" $! r0 ltac:(auto)) as "Hr0".
               assert (r.2 !! r0 = Some w0) as H1.
               { rewrite -(lookup_insert_ne _ PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//. }
              rewrite H0 H1. auto.
          + repeat rewrite /RegLocate lookup_insert_ne; auto.
            iDestruct ("Hreg" $! ri with "[]") as "HH"; auto.
            assert (r.1 !! ri = r.2 !! ri) as Heq;[|rewrite Heq;auto].
            rewrite -(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.
      }
    }
    Unshelve. all: auto.
  Qed.

End fundamental.
