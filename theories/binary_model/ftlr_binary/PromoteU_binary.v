From cap_machine.binary_model Require Export logrel_binary.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Import ftlr_base_binary interp_weakening_binary.
From cap_machine.rules Require Import rules_PromoteU.
From cap_machine.binary_model.rules_binary Require Import rules_binary_PromoteU.
From cap_machine Require Import stdpp_extra.

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

  Lemma PromoteU_spec_determ r dst regs regs' retv retv' :
    PromoteU_spec r dst regs retv →
    PromoteU_spec r dst regs' retv' →
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2;subst; simplify_eq.
    - split;auto.
    - inv H4;try congruence. rewrite H1 in H3;done.
    - inv H0;try congruence. rewrite H1 in H3;done.
    - split;auto.
  Qed.

  Lemma promote_interp W p g b e a (Hp: p <> E):
    IH -∗
    ((fixpoint interp1) W) (inr (p, g, b, e, a),inr (p, g, b, e, a)) -∗
    ((fixpoint interp1) W) (inr (promote_perm p, g, b, addr_reg.min a e, a),inr (promote_perm p, g, b, addr_reg.min a e, a)).
  Proof.
    iIntros "#IH A". destruct (isU p) eqn:HisU.
    - rewrite !fixpoint_interp1_eq /=. destruct p; simpl in *; try congruence; auto.
      all: try iSplit;auto.
      + destruct g.
        all: iDestruct "A" as "[_ A]".
        * (* iDestruct "A" as (p) "[% A]". *)
          (* iExists p; iSplit; [auto|]. *)
          iApply (big_sepL_submseteq with "A").
          destruct (Addr_le_dec b (addr_reg.min a e)).
          { rewrite (region_addrs_split b (addr_reg.min a e) e); [|solve_addr].
            eapply submseteq_inserts_r. auto. }
          { rewrite region_addrs_empty; [|solve_addr].
            eapply submseteq_nil_l. }
        * iDestruct "A" as "[A B]". auto.
        * iDestruct "A" as "[A B]". auto.
      + destruct g; auto. iDestruct "A" as "[_ [A B]]". auto.
      + destruct g.
        all: iDestruct "A" as "[_ A]".
        * iDestruct "A" as "#A".
          iApply (big_sepL_submseteq with "A").
          destruct (Addr_le_dec b (addr_reg.min a e)).
          { rewrite (region_addrs_split b (addr_reg.min a e) e); [|solve_addr].
            eapply submseteq_inserts_r. auto. }
          { rewrite region_addrs_empty; [|solve_addr].
            eapply submseteq_nil_l. }
        * iDestruct "A" as "[#A #B]". auto.
        * iDestruct "A" as "[#A #B]". auto.
      + destruct g; auto. iDestruct "A" as "[_ [A B]]". auto.
    - iApply (interp_weakening with "IH"); eauto; try solve_addr.
      + rewrite HisU; auto.
      + destruct p; simpl in HisU; simpl; auto; congruence.
      + destruct g; auto.
  Qed.

  Lemma promoteU_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (P:D) :
    ftlr_instr W r p g b e a w (PromoteU dst) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_PromoteU with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; destruct Hsome with rr; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    iMod (step_PromoteU _ [SeqCtx] with "[$Ha' $Hsmap $Hj $Hspec]") as (retv' regs'') "(Hj & Hspec' & Ha' & Hsmap)";eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; destruct Hsome with rr; eauto. }
    iDestruct "Hspec'" as %HSpec'.

    specialize (PromoteU_spec_determ _ _ _ _ _ _ HSpec HSpec') as [Heq <-].

    iAssert (interp_registers W (r.1, r.1)) as "#[_ Hreg']".
    { iApply interp_reg_dupl. iSplit;eauto. auto. }

    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { destruct Heq as [<- | Hcontr];[|inversion Hcontr].
      incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";auto.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;congruence. }
      iApply ("IH" $! _ (<[dst:=inr (promote_perm p0, g0, b0, addr_reg.min a0 e0, a0)]> (<[PC:=_]> r.1),<[dst:=inr (promote_perm p0, g0, b0, addr_reg.min a0 e0, a0)]> (<[PC:=_]> r.1)) with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hj]"); eauto.
      { iSplit. iPureIntro. intro. cbn. split; by repeat (rewrite lookup_insert_is_Some'; destruct Hsome with x5; right).
        iIntros (ri Hri). rewrite /(RegLocate _ ri) //; auto.
        destruct (reg_eq_dec dst ri).
        - subst ri. rewrite lookup_insert.
          destruct (reg_eq_dec dst PC); try congruence.
          iDestruct ("Hreg'" $! dst n) as "H".
          rewrite lookup_insert_ne in H1; auto.
          rewrite /RegLocate H1. iApply (promote_interp with "IH H"); auto.
        - rewrite !lookup_insert_ne; auto.
          iDestruct ("Hreg'" $! ri with "[]") as "HH"; auto. }
      { assert (x = p /\ x0 = g) as [-> ->].
        { destruct (reg_eq_dec PC dst).
          - subst dst. rewrite !lookup_insert in H1 H2. inv H1; inv H2.
            split; auto. destruct Hp as [-> | [-> | [-> ->] ] ]; auto.
          - rewrite lookup_insert_ne in H2; auto.
            rewrite lookup_insert in H2; inv H2; auto. }
        auto. }
      { iModIntro. destruct (reg_eq_dec PC dst).
        - subst dst. rewrite !lookup_insert in H1 H2. inv H2. inv H1.
          assert (promote_perm p0 = p0) as -> by (destruct Hp as [-> | [-> | [-> ->] ] ]; auto).
          rewrite /region_conditions (isWithin_region_addrs_decomposition x1 (addr_reg.min x3 e0) x1 e0); try solve_addr.
          rewrite !big_sepL_app. iDestruct "Hinv" as "[A1 [A2 A3]]". auto.
        - rewrite lookup_insert_ne in H2; auto. rewrite lookup_insert in H2.
          inv H2. auto. } }
  Qed.

 End fundamental.
