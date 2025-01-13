From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine.binary_model Require Export logrel_binary monotone_binary.
From cap_machine.binary_model Require Import ftlr_base_binary interp_weakening_binary.
From cap_machine.rules Require Import rules_StoreU.
From cap_machine.binary_model.rules_binary Require Import rules_binary_StoreU.
From cap_machine Require Import stdpp_extra.
Import uPred.

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


  Lemma StoreU_fail_succeed_exfalso p g b e a offs zoffs a' w dst r src regs' :
    StoreU_failure r dst offs src →
    word_of_argument r src = Some w →
    z_of_argument r offs = Some zoffs →
    (a + zoffs)%a = Some a' →
    reg_allows_storeU r dst p g b e a a' w →
    (if addr_eq_dec a a'
    then
      match (a + 1)%a with
      | Some a'' => incrementPC (<[dst:=inr (p, g, b, e, a'')]> r) = Some regs'
      | None => False
      end
     else incrementPC r = Some regs') →
    False.
  Proof.
    intros X H0 H1 H2 H3 H6.
    inv H3. destruct H5 as (?&?&?&?&?).
    inv X;try congruence.
    { rewrite H4 in H10. done. }
    { rewrite H4 in H10. inv H10. rewrite H1 in H12. inv H12.
      rewrite H0 in H11. inv H11. inv H13. rewrite H2 in H11.
      repeat (rewrite decide_True// in H11). inv H11. congruence. }
    { rewrite H4 in H10. inv H10. rewrite H1 in H12. inv H12.
      rewrite H0 in H11. inv H11. inv H13. rewrite H2 in H11.
      repeat (rewrite decide_True// in H11). }
    { rewrite H4 in H10. inv H10. rewrite H1 in H14. inv H14.
      rewrite H0 in H11. inv H11. inv H15. rewrite H2 in H11.
      repeat (rewrite decide_True// in H11). inv H11. solve_addr. }
    { rewrite H4 in H10. inv H10. rewrite H1 in H14. inv H14.
      rewrite H0 in H11. inv H11. inv H15. rewrite H2 in H11.
      repeat (rewrite decide_True// in H11). inv H11.
      destruct (addr_eq_dec a0 a'');subst.
      - rewrite H16 in H6. congruence.
      - rewrite /incrementPC in H17,H6.
        destruct (r !! PC) eqn:HPC;[|inversion H6].
        destruct s;[inversion H6|]. destruct p,p,p,p.
        destruct (decide (dst = PC)).
        + subst. rewrite H4 in HPC. inv HPC. rewrite lookup_insert in H17.
          destruct (a'0 + 1)%a eqn:Hsome;[inversion H17|].
          destruct (a + 1)%a eqn:Hsome';[|inversion H6]. destruct p; try congruence; inv H6.
          solve_addr.
        + rewrite lookup_insert_ne// HPC in H17. destruct (a+1)%a eqn:Hsome; destruct p; try congruence; inversion H6;inversion H17. }
    { rewrite H4 in H10. inv H10. rewrite H1 in H14. inv H14.
      rewrite H0 in H11. inv H11. inv H15. rewrite H2 in H11.
      repeat (rewrite decide_True// in H11). inv H11.
      rewrite decide_False// in H6. congruence. }
  Qed.

  Lemma StoreU_spec_determ r dst offs src regs regs' mem0 mem1 mem0' mem0'' retv retv' :
    (∀ a a' p g b e zoffs, r !! dst = Some (inr (p, g, b, e, a)) → z_of_argument r offs = Some zoffs
             → (a + zoffs)%a = Some a' → delete a' mem0 = delete a' mem1) →
    StoreU_spec r dst offs src regs mem0 mem0' retv →
    StoreU_spec r dst offs src regs' mem1 mem0'' retv' →
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv' /\ (mem0' = mem0'' ∨ retv = FailedV).
  Proof.
    intros Hcond Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; try congruence.
    - repeat split; auto. left. inv H11. inv H3. rewrite H5 in H8; simplify_eq.
      destruct (addr_eq_dec a a'); try congruence.
      destruct (a + 1)%a;try congruence. done.
      inv H11. inv H3. rewrite H5 in H8; simplify_eq.
      eapply Hcond in H2;eauto.
      rewrite -insert_delete H2 insert_delete. auto.
    - exfalso. eapply StoreU_fail_succeed_exfalso;eauto.
    - exfalso. eapply StoreU_fail_succeed_exfalso;eauto.
    - repeat split;auto.
  Qed.

  Lemma isU_inv:
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality) (w:Word),
      (b ≤ a' < addr_reg.min a e)%Z
      → isU p = true
      → ⊢ (interp W) (inr (p, g, b, e, a),w)
      → read_write_cond a' interp
                     ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                                            ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g) ∧ (∀ w, ρ ≠ Uninitialized w))⌝.
  Proof.
    intros. iIntros "H".
    iDestruct (interp_eq with "H") as %<-.
    rewrite /interp fixpoint_interp1_eq /=.
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H1; auto; congruence); simpl.
    - destruct g.
      all: iDestruct "H" as "[_ H]".
      + iDestruct (extract_from_region_inv with "H") as "[C %]";[|iFrame]. solve_addr.
        iPureIntro; auto. (* rewrite H1. *) eexists;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as "[D %]"; try (iFrame); auto.
        iPureIntro; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as "[D %]"; try (iFrame); auto.
        iPureIntro; auto. destruct H2 as [? | ?]; eexists;eauto.
    - destruct g; auto.
      iDestruct "H" as "[_ H]".
      iDestruct "H" as "[B C]".
      iDestruct (extract_from_region_inv with "B") as "[D %]"; try (iFrame); auto.
      iPureIntro. eexists;split;eauto.
    - destruct g.
      all: iDestruct "H" as "[_ H]".
      + iDestruct (extract_from_region_inv with "H") as "[D %]"; try (iFrame); auto; [solve_addr|].
        iPureIntro; auto. eexists; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as "[E %]"; try (iFrame); auto.
        iPureIntro; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "B") as  "[E %]"; try (iFrame); auto.
        iPureIntro; auto. destruct H2 as [? | ?]; eexists;eauto.
    - destruct g; auto.
      iDestruct "H" as "[_ [B C]]".
      iDestruct (extract_from_region_inv with "B") as "[D %]"; try (iFrame); auto.
      iPureIntro; simpl in H1; eexists;eauto.
  Qed.

  Lemma isU_inv_all :
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality) (w:Word),
      (b ≤ a' < e)%Z
      → isU p = true
      → ⊢ (interp W) (inr (p, g, b, e, a),w)
      → read_write_cond a' interp
        ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                               ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g))⌝.
  Proof.
    intros. iIntros "H".
    iDestruct (interp_eq with "H") as %<-.
    destruct (decide (a' < addr_reg.min a e))%a.
    { iDestruct (isU_inv _ a' with "H") as "(?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?&?).
      iFrame. iPureIntro;eauto. }
    assert (addr_reg.min a e <= a' < e)%a;[solve_addr|].
    rewrite /interp fixpoint_interp1_eq /=.
    assert (p = URW \/ p = URWL \/ p = URWX \/ p = URWLX) as [-> | [-> | [-> | ->] ] ] by (destruct p; simpl in H1; auto; congruence); simpl.
    - destruct g.
      all: iDestruct "H" as "[_ H]".
      + iDestruct (extract_from_region_inv with "H") as "[C %]";try (iFrame; auto);[solve_addr|].
        iPureIntro; auto. eexists;repeat split;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as "[D %]"; try (iFrame);[solve_addr|].
        iPureIntro; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as "[D %]"; try (iFrame); [solve_addr|].
        iPureIntro; auto. destruct H3 as [? | [? | [? ?] ] ];
                                         eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
    - destruct g; auto.
      iDestruct "H" as "[_ [B C]]".
      iDestruct (extract_from_region_inv with "C") as  "[D %]"; try (iFrame); [solve_addr|].
      iPureIntro; eauto. destruct H3 as [? | [? ?] ]; eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
    - destruct g.
      all: iDestruct "H" as "[_ H]".
      + iDestruct (extract_from_region_inv with "H") as "[D %]"; try (iFrame); auto.
        iPureIntro; auto. eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as "[E %]"; try (iFrame);[solve_addr|].
        iPureIntro; eauto.
      + iDestruct "H" as "[B C]".
        iDestruct (extract_from_region_inv with "C") as "[E %]"; try (iFrame); [solve_addr|].
        iPureIntro; auto. destruct H3 as [? | [? | [? ?] ] ];
                                         eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
    - destruct g; auto.
      iDestruct "H" as "[_ [B C]]".
      iDestruct (extract_from_region_inv with "C") as "[D %]"; try (iFrame); [solve_addr|].
      iPureIntro; destruct H3 as [? | [? ?] ]; eexists;repeat split;eauto;intros ? Hcontr;inversion Hcontr;eauto.
  Qed.

  Lemma isU_inv_boundary :
    ∀ (W : leibnizO WORLD) (a' a b e : Addr) (p : Perm) (g : Locality) (w:Word),
      (b <= a' < e)%Z → (a' ≤ addr_reg.min a e)%Z
      → isU p = true
      → ⊢ (interp W) (inr (p, g, b, e, a),w)
      → read_write_cond a' interp
        ∧ ⌜(∃ ρ : region_type, std W !! a' = Some ρ
                               ∧ ρ ≠ Revoked ∧ (∀ g, ρ ≠ Monostatic g) ∧
                               if (a' =? addr_reg.min a e)%Z
                               then True
                               else (∀ w, ρ ≠ Uninitialized w))⌝.
  Proof.
    intros. iIntros "H".
    destruct (a' =? addr_reg.min a e)%Z eqn:Heq.
    - iDestruct (isU_inv_all _ a' with "H") as "(?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?).
      iFrame. iPureIntro;eexists;eauto.
    - apply Z.eqb_neq in Heq. iDestruct (isU_inv _ a' with "H") as "(?&H)";[solve_addr|auto|]. iDestruct "H" as %(?&?&?&?&?).
      iFrame. iPureIntro;eexists;repeat split;eauto.
  Qed.

  Lemma execcPC_implies_interp W p g b e a0 :
    p = RX ∨ p = RWX ∨ p = RWLX ∧ g = Directed →
    region_conditions W p g b e  -∗
      ((fixpoint interp1) W) (inr (p, g, b, e, a0),inr (p,g,b,e,a0)).
  Proof.
    iIntros (Hp) "#HR".
    rewrite (fixpoint_interp1_eq _ (inr _,inr _)).
    (do 2 try destruct Hp as [ | Hp]). 3:destruct Hp.
    all:subst; iSplit; auto; simpl. rewrite /region_conditions /=.
    iApply (big_sepL_mono with "HR").
    intros. iIntros "H". iDestruct (and_exist_r with "H") as (P) "((?&?)&?)". iExists _;iFrame.
  Qed.

  (* The necessary resources to close the region again, except for the points to predicate, which we will store separately *)
  Definition region_open_resources W l ls φ (condb : bool): iProp Σ :=
    (∃ ρ,
        sts_state_std l ρ
    ∗ ⌜std W !! l = Some ρ⌝
    ∗ ⌜ρ ≠ Revoked⌝
    ∗ ⌜(∀ g, ρ ≠ Monostatic g)⌝
    ∗ ⌜if condb then True else (forall w, ρ ≠ Uninitialized w)⌝
    ∗ open_region_many (l :: ls) W
    ∗ rel l φ)%I.

  Lemma store_inr_eq {regs r p0 g0 b0 e0 a0 a' p1 g1 b1 e1 a1 storev}:
    reg_allows_storeU regs r p0 g0 b0 e0 a0 a' storev →
    read_reg_inr regs r p1 g1 b1 e1 a1 →
    p0 = p1 ∧ g0 = g1 ∧ b0 = b1 ∧ e0 = e1 ∧ a0 = a1.
  Proof.
      intros Hrar H3.
      pose (Hrar' := Hrar).
      destruct Hrar' as (Hinr0 & _). destruct H3 as [Hinr1 | Hinl1].
      * rewrite Hinr0 in Hinr1. inversion Hinr1.
        subst;auto.
      * destruct Hinl1 as [z Hinl1]. rewrite Hinl1 in Hinr0. by exfalso.
  Qed.

  (* Description of what the resources are supposed to look like after opening the region if we need to, but before closing the region up again*)
  Definition allow_store_res W r1 r2 offs (regs : Reg) pc_a :=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝ ∗ ⌜word_of_argument regs r2 = Some storev⌝ ∗
      match z_of_argument regs offs with
      | None => open_region pc_a W
      | Some zoffs =>
        match (a + zoffs)%a with
        | Some a' => (if decide (reg_allows_storeU regs r1 p g b e a a' storev) then
                       (if decide (a' ≠ pc_a) then
                          ∃ w1 w2, a' ↦ₐ w1  ∗ a' ↣ₐ w2 ∗ (region_open_resources W a' [pc_a] interpC (a' =? a)%Z)
                        else open_region pc_a W )
                     else open_region pc_a W)
        | None => open_region pc_a W
        end
      end)%I.

  Definition allow_store_mem W r1 r2 offs (regs : Reg) pc_a pc_w (mem1 mem2 : Mem):=
    (∃ p g b e a storev, ⌜read_reg_inr regs r1 p g b e a⌝ ∗ ⌜word_of_argument regs r2 = Some storev⌝ ∗
      match z_of_argument regs offs with
      | None => ⌜mem1 = <[pc_a:=pc_w]> ∅⌝ ∗ ⌜mem2 = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W
      | Some zoffs =>
        match (a + zoffs)%a with
        | Some a' => (if decide (reg_allows_storeU regs r1 p g b e a a' storev) then
                       (if decide (a' ≠ pc_a) then
                          ∃ w1 w2, ⌜mem1 = <[a':=w1]> (<[pc_a:=pc_w]> ∅)⌝
                             ∗ ⌜mem2 = <[a':=w2]> (<[pc_a:=pc_w]> ∅)⌝
                             ∗ (region_open_resources W a' [pc_a] interpC (a' =? a)%Z)
                        else ⌜mem1 = <[pc_a:=pc_w]> ∅⌝ ∗ ⌜mem2 = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W )
                     else ⌜mem1 = <[pc_a:=pc_w]> ∅⌝ ∗ ⌜mem2 = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W)
        | None => ⌜mem1 = <[pc_a:=pc_w]> ∅⌝ ∗ ⌜mem2 = <[pc_a:=pc_w]> ∅⌝ ∗ open_region pc_a W
        end
      end)%I.

  Lemma create_store_res:
    ∀ (W : WORLD) (r : leibnizO Reg) (p : Perm)
      (g : Locality) (b e a : Addr) (r1 : RegName) (offs r2 : Z + RegName) (p0 : Perm)
      (g0 : Locality) (b0 e0 a0 : Addr)(storev : Word)(P:D) E,
      read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r) r1 p0 g0 b0 e0 a0
      → isU p = false
      → word_of_argument (<[PC:=inr (p, g, b, e, a)]> r) r2 = Some storev
      → (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1,r !r! r1))
          -∗ rel a (λ Wv, P Wv.1 Wv.2)
          -∗ open_region a W
          -∗ sts_full_world W
          ={E}=∗ allow_store_res W r1 r2 offs (<[PC:=inr (p, g, b, e, a)]> r) a
          ∗ sts_full_world W.
  Proof.
    intros W r p g b e a r1 r2 offs p0 g0 b0 e0 a0 storev P E HVr1 Hnu Hwoa.
    iIntros "#Hreg #Hinva Hr Hsts".
    do 6 (iApply sep_exist_r; iExists _). iFrame "%".
    destruct (z_of_argument (<[PC:=inr (p, g, b, e, a)]> r) r2);[|iFrame].
    destruct (a0 + z)%a;[|iFrame].
    case_decide as Hallows.
    - case_decide as Haeq.
      + destruct Hallows as (Hrinr & Hra & Hwb1 & Hwb2 & Hwb3 & HLoc).
        assert (r1 ≠ PC) as n.
        { intros Heq;subst. destruct HVr1 as [?|[? ?] ]; simplify_map_eq;congruence. }
        simplify_map_eq.

        iDestruct ("Hreg" $! r1 n) as "Hvsrc".
        rewrite /RegLocate Hrinr.
        iDestruct (isU_inv_boundary _ a1 with "Hvsrc") as "[Hrel' %]";[solve_addr|solve_addr|auto|].
        rewrite /read_write_cond.
        iDestruct (region_open_prepare with "Hr") as "Hr".

        destruct H0 as (ρ & Hρ & Hnotrevoked & Hnotmonostatic & Hdec).
        assert (addr_reg.min a0 e0 = a0) as Heq;[solve_addr|]. rewrite Heq in Hdec.
        destruct ρ; try congruence.
        * iDestruct (region_open_next _ _ _ a1 RO Monotemporary with "[$Hrel' $Hr $Hsts]") as (w0 w1) "($ & Hstate' & Hr & Ha0 & Ha1 & Hfuture & #Hval)";
            auto;[intros [g1 Hcontr];done..| |].
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iAssert (▷ ⌜w0 = w1⌝)%I as "#>->".
          { iNext. iDestruct (interp_eq with "Hval") as %->. auto. }
          iExists _,_. iFrame. iModIntro. iExists Monotemporary. iFrame "∗ % #".
        * iDestruct (region_open_next _ _ _ a1 RO Permanent with "[$Hrel' $Hr $Hsts]") as (w0 w1) "($ & Hstate' & Hr & Ha0 & Ha1 & Hfuture & #Hval)";
            auto;[intros [g1 Hcontr];done..| |].
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iAssert (▷ ⌜w0 = w1⌝)%I as "#>->".
          { iNext. iDestruct (interp_eq with "Hval") as %->. auto. }
          iExists _,_. iFrame. iExists Permanent. iFrame "∗ % #". done.
        * destruct p1 as [w0 w1].
          iDestruct (region_open_next_monouninit_w _ w0 w1 _ a1 with "[$Hrel' $Hr $Hsts]") as "($ & $ & Hstate & Ha & Ha')";eauto.
          { apply not_elem_of_cons. split; auto. apply not_elem_of_nil. }
          iExists _,_;iFrame. iExists _;iFrame. iFrame "% #". done.
      + subst a1. iFrame. done.
    - iFrame. done.
    - done.
    - done.
  Qed.

  Lemma store_res_implies_mem_map:
    ∀ (W : WORLD) (r : leibnizO Reg)
       (a : Addr) (w : Word) (r1 : RegName) (offs r2 : Z + RegName),
      allow_store_res W r1 r2 offs r a
      -∗ a ↦ₐ w
      -∗ a ↣ₐ w
      -∗ ∃ mem0 mem1: Mem,
          allow_store_mem W r1 r2 offs r a w mem0 mem1
            ∗ ▷ (([∗ map] a0↦w ∈ mem0, a0 ↦ₐ w)
            ∗ ([∗ map] a0↦w ∈ mem1, a0 ↣ₐ w)).
  Proof.
    intros W r a w r1 r2 offs.
    iIntros "HStoreRes Ha Ha'".
    iDestruct "HStoreRes" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".
    destruct (z_of_argument r r2) eqn:Hz.
    2: { iExists _,_. iSplitL "HStoreRes".
         + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
           rewrite Hz. iFrame. eauto.
         + iNext. iSplitL "Ha"; try by iApply memMap_resource_1.
           rewrite big_sepM_insert;auto. }
    destruct (a1 + z)%a eqn:Hnext.
    2: { iExists _,_. iSplitL "HStoreRes".
         + iExists p1,g1,b1,e1,a1,storev. iFrame "%".
           rewrite Hz Hnext. iFrame. eauto.
         + iNext. rewrite !big_sepM_insert//;auto. iFrame. auto. }

    case_decide as Hallows.
    - case_decide as Haeq.
      ++ pose(Hallows' := Hallows). destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
         iDestruct "HStoreRes" as (w0 w1) "[HStoreCh [HStoreCh' HStoreRest]]".
         iExists _,_.
         iSplitL "HStoreRest".
        + iExists p1,g1,b1,e1,a1,storev. iFrame "%". rewrite Hz Hnext.
          case_decide; last by exfalso. case_decide; last by exfalso.
          iExists w0,w1. iSplitR; auto.
        + iNext. rewrite !big_sepM_insert//. iFrame. auto.
          all: rewrite lookup_insert_ne//.
      ++ iExists _,_.
         iSplitL "HStoreRes".
        + iExists p1,g1,b1,e1,a1,storev. iFrame "%". rewrite Hz Hnext.
          case_decide; last by exfalso. case_decide; first by exfalso.
          iFrame. auto.
        + iNext. rewrite !big_sepM_insert//. iFrame. auto.
    - iExists _,_.
      iSplitL "HStoreRes".
      + iExists p1,g1,b1,e1,a1,storev. iFrame "%". rewrite Hz Hnext.
        case_decide; first by exfalso. iFrame. auto.
      + iNext. rewrite !big_sepM_insert//. iFrame. auto.
    Qed.

  Lemma mem_map_implies_pure_conds:
    ∀ (W : WORLD) (r : leibnizO Reg) (p : Perm)
      (g : Locality) (b e a : Addr) (w : Word) (r1 : RegName) (offs r2 : Z + RegName)
      (mem0 mem1 : Mem),
        allow_store_mem W r1 r2 offs r a w mem0 mem1
        -∗ ⌜mem0 !! a = Some w⌝ ∗ ⌜mem1 !! a = Some w⌝
         ∗ ⌜allow_storeU_map_or_true r1 r2 offs r mem0⌝
         ∗ ⌜allow_storeU_map_or_true r1 r2 offs r mem1⌝
         ∗ ⌜(∀ a a' p g b e zoffs, r !! r1 = Some (inr (p, g, b, e, a)) → z_of_argument r offs = Some zoffs
             → (a + zoffs)%a = Some a' → delete a' mem0 = delete a' mem1)⌝.
  Proof.
    iIntros (W r p g b e a w r1 r2 offs mem0 mem1) "HStoreMem".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1 storev) "(% & % & HStoreRes)".
    rewrite /allow_storeU_map_or_true.
    destruct (z_of_argument r r2) eqn:Hz.
    2: { iDestruct "HStoreRes" as "[-> [-> HStoreRes] ]".
         repeat (iSplitR; [by rewrite lookup_insert|]).
         iSplit. 2: iSplit. 1,2: iExists p1,g1,b1,e1,a1,storev. 1,2: repeat iSplitR; auto.
         iIntros (a0 a' p0 g0 b0 e0 zoffs Hr Hcontr). inversion Hcontr.
    }
    destruct (a1 + z)%a eqn:Hnext.
    2: { iDestruct "HStoreRes" as "[-> [-> HStoreRes] ]".
         repeat (iSplitR; [by rewrite lookup_insert|]).
         iSplit. 2: iSplit. 1,2: iExists p1,g1,b1,e1,a1,storev. 1,2: repeat iSplitR; auto.
         1,2: rewrite Hnext. 1,2: auto.
         iIntros (a0 a' p0 g0 b0 e0 zoffs Hr Hz' Ha'). auto.
    }

    case_decide as Hallows.
    - case_decide as Haeq.
      + pose(Hallows' := Hallows). destruct Hallows' as (Hrinr & Hra & Hwb & HLoc).
        (* case_decide as Haeq. *)
        iDestruct "HStoreRes" as (w0 w1 -> ->) "_".
        iSplit;[|iSplit].
        1,2: rewrite lookup_insert_ne//. 1,2: by rewrite lookup_insert.
        iSplit. 2: iSplit. 1,2: iExists p1,g1,b1,e1,a1,storev.
        1,2: iPureIntro. 1,2: repeat split; auto. 1,2: rewrite Hnext.
        1,2: case_decide; last by exfalso.
        1: exists w0; simplify_map_eq; split;auto.
        1: exists w1; simplify_map_eq; split;auto.
        iPureIntro. intros. simplify_eq. rewrite Hrinr in H2. inv H2.
        rewrite Hnext in H4. inv H4. rewrite !delete_insert//.
        all: rewrite lookup_insert_ne//.
      + subst a. iDestruct "HStoreRes" as "[-> [-> HStoreRes] ]".
        iSplitR;[|iSplitR;[|iSplitR] ]. 1,2: by rewrite lookup_insert.
        2: iSplit. 1,2: iExists p1,g1,b1,e1,a1,storev;repeat iSplitR; auto;rewrite Hnext.
        1,2: case_decide as Hdec1; last by done.
        iExists w. 2: iExists w. 1,2: rewrite lookup_insert; auto.
        iPureIntro. intros. simplify_eq. destruct Hallows as (Hrinr & Hra & Hwb & HLoc).
        rewrite Hrinr in H2. inv H2.
        rewrite Hnext in H4. inv H4. rewrite !delete_insert//.
    - iDestruct "HStoreRes" as "[-> [-> HStoreRes] ]".
      iSplitR;[|iSplitR]. 1,2: by rewrite lookup_insert.
      iSplit. 2: iSplit. 1,2: iExists p1,g1,b1,e1,a1,storev. 1,2: repeat iSplitR; auto.
      1,2: rewrite Hnext.
      1,2: case_decide as Hdec1; last by done. 1,2: by exfalso.
      iPureIntro. intros. auto.
  Qed.

  (* TODO: prove this using interp_weakening *)
  Lemma isU_weak_addrs W p g b e a a' :
    isU p = true -> (a' <= a)%a →
    interp W (inr (p,g,b,e,a),inr (p,g,b,e,a)) -∗ interp W (inr (p,g,b,e,a'),inr (p,g,b,e,a')).
  Proof.
    iIntros (Hu Hle) "#Hv".
    iApply interp_weakeningEO;eauto.
    rewrite Hu;auto. 1,2,3,4: destruct p;auto;inversion Hu.
    solve_addr. solve_addr. apply Is_true_eq_left. apply PermFlows_refl.
    apply Is_true_eq_left. destruct g;auto.
  Qed.

  Lemma storev_interp_mono W (r : Reg) (r1 : RegName) (r2 : Z + RegName) p g b e a a' ρ storev:
    word_of_argument r r2 = Some storev
     → reg_allows_storeU r r1 p g b e a a' storev
     → std W !! a' = Some ρ
     → ((fixpoint interp1) W) (inr (p,g,b,e,a),inr (p,g,b,e,a))
       -∗ monotonicity_guarantees_region ρ a' storev storev interpC.
   Proof.
     iIntros (Hwoa Hras Hststd) "HInt".
     destruct Hras as (Hrir & Hwa & Hwb & Hwb1 & Hwb2 & Hloc).
     destruct storev as [z | cap].
     - iDestruct (isU_weak_addrs with "HInt") as "HInt";eauto.
       iApply (interp_monotone_generalZ with "HInt" );auto.
       { apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];solve_addr. }
     - iDestruct (isU_weak_addrs with "HInt") as "HInt";eauto.
       destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
       destruct_cap cap. cbn in Hwoa.
       destruct (r !! r0); inversion Hwoa; clear Hwoa; subst w.
       iApply (interp_monotone_generalUW with "HInt" ); eauto.
       apply andb_true_iff. split;[apply Z.leb_le|apply Z.ltb_lt];solve_addr.
   Qed.


   Definition new_worldU W (a0 : Addr) pc_p pc_g pc_b pc_e pc_a r offs :=
     match z_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) offs with
     | Some z =>
       match (a0 + z)%a with
       | Some a1 =>
         if (a1 =? a0)%Z
         then match std W !! a1 with
              | Some (Uninitialized _) => (<[a1:=Monotemporary]> W.1,W.2)
              | _ => W
              end
         else W
       | None => W
       end
     | None => W
     end.

   Lemma new_worldU_pub W a0 pc_p pc_g pc_b pc_e pc_a r offs :
     related_sts_pub_world W (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs).
   Proof.
     unfold new_worldU.
     destruct (z_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) offs);
       [|apply related_sts_pub_refl_world].
     destruct (a0 + z)%a eqn:Hnext;[|apply related_sts_pub_refl_world].
     destruct (a =? a0)%Z;[|apply related_sts_pub_refl_world].
     destruct (std W !! a) eqn:Hsome;[|apply related_sts_pub_refl_world].
     destruct r0;try apply related_sts_pub_refl_world.
     apply uninitialized_w_mono_related_sts_pub_world in Hsome;auto.
   Qed.

   Definition new_state ρ :=
     match ρ with
     | Uninitialized _ => Monotemporary
     | _ => ρ
     end.

   Lemma new_worldU_lookup W a0 pc_p pc_g pc_b pc_e pc_a r offs z a1 ρ :
     z_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) offs = Some z →
     (a0 + z)%a = Some a1 →
     W.1 !! a1 = Some ρ →
     (a1 =? a0)%Z = true →
     std (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs) !! a1 = Some (new_state ρ).
   Proof.
     intros Hzoff Hnext Hρ Hfalse.
     unfold new_worldU. rewrite Hzoff Hnext Hfalse Hρ.
     unfold new_state. destruct ρ;auto;
     simplify_map_eq;auto.
   Qed.


   Definition wcond' (P : D) p g b e a r : iProp Σ := (if decide (writeAllowed_in_r_a (<[PC:=inr (p, g, b, e, a)]> r) a) then □ (∀ W0 w, interp W0 w -∗ P W0 w) else emp)%I.
  Instance wcond'_pers : Persistent (wcond' P p g b e a r).
  Proof. intros. rewrite /wcond'. case_decide;apply _. Qed.
  (* Note that we turn in all information that we might have on the monotonicity of the current PC value, so that in the proof of the ftlr case itself, we do not have to worry about whether the PC was written to or not when we close the last location pc_a in the region *)
   Lemma mem_map_recover_res:
    ∀ (W : WORLD) (r : Reg)
       (pc_w : Word) (r1 : RegName) (r2 offs : Z + RegName) (offz : Z) (p0 pc_p : Perm)
       (g0 pc_g : Locality) (b0 e0 a0 a1 pc_b pc_e pc_a : Addr) (mem0 mem1 : Mem) (oldv storev : Word) (ρ : region_type) (P:D)
       (Hnotuninitialized : ∀ w, ρ ≠ Uninitialized w),
        word_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) r2 = Some storev
      → z_of_argument (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) offs = Some offz (* necessary for successful store *)
      → (a0 + offz)%a = Some a1 (* necessary for successful store *)
      → (pc_p = RX ∨ pc_p = RWX ∨ pc_p = RWLX)
      → reg_allows_storeU (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) r1 p0 g0 b0 e0 a0 a1 storev
      → std W !! pc_a = Some ρ
      → mem0 !! a1 = Some oldv (*?*)
      → (∀ Wv, Persistent (P Wv.1 Wv.2))
      → allow_store_mem W r1 r2 offs (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r) pc_a pc_w mem0 mem1
        -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1,r !r! r1))
        -∗ ((fixpoint interp1) W) (inr(pc_p, pc_g, pc_b, pc_e, pc_a),inr(pc_p, pc_g, pc_b, pc_e, pc_a))
        -∗ P W (pc_w,pc_w)
        -∗ □ (∀ W0 w, P W0 w -∗ interp W0 w)
        -∗ wcond' P pc_p pc_g pc_b pc_e pc_a r
        -∗ monotonicity_guarantees_region ρ pc_a pc_w pc_w (λ Wv, P Wv.1 Wv.2)
        -∗ future_pub_mono (λ Wv, P Wv.1 Wv.2) pc_w pc_w
        -∗ ([∗ map] a0↦w ∈ <[a1 := storev]> mem0, a0 ↦ₐ w)
        -∗ ([∗ map] a0↦w ∈ <[a1 := storev]> mem1, a0 ↣ₐ w)
        -∗ sts_full_world W
        ={⊤}=∗ ∃ (v:Word), open_region pc_a (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)
                            ∗ sts_full_world (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)
                            ∗ pc_a ↦ₐ v ∗ pc_a ↣ₐ v
                            ∗ P (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs) (v,v)
                            ∗ monotonicity_guarantees_region ρ pc_a v v (λ Wv, P Wv.1 Wv.2)
                            ∗ ⌜related_sts_pub_world W (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)⌝.
   Proof.
    intros W r pc_w r1 r2 offs offz p0 pc_p g0 pc_g b0 e0 a0 a1 pc_b pc_e pc_a mem0 mem1 oldv storev ρ P Hnotuninitialized
           Hwoa Hz Hnext Hpcperm Hras Hstdst Ha0 Hpers.
    iIntros "HStoreMem #Hreg #HVPCr Hpc_w #Hrcond #Hwcond Hpcmono #Hpubmono Hmem Hmem' Hsts".
    iDestruct "HStoreMem" as (p1 g1 b1 e1 a1' storev1) "[% [% HStoreRes] ]".
    assert (Persistent (P W (pc_w,pc_w))).
    { specialize (Hpers (W,(pc_w,pc_w))). auto. }
    iDestruct "Hpc_w" as "#Hpc_w".
    destruct (store_inr_eq Hras H0) as (<- & <- &<- &<- &<-).
    rewrite Hwoa in H1; inversion H1; simplify_eq.
    rewrite /new_worldU !Hz !Hnext.

    case_decide as Hallows.
    - iAssert (((fixpoint interp1) W) (inr (p0,g0,b0,e0,a0),inr (p0,g0,b0,e0,a0)))%I with "[HVPCr Hreg]" as "#HVr1".
      { destruct Hras as [Hreg _]. destruct (decide (r1 = PC)).
        - subst r1. rewrite lookup_insert in Hreg. inversion Hreg. subst.
          destruct Hallows as (_ & Hallows & _). destruct Hpcperm as [-> | [-> | -> ] ];inversion Hallows.
        - iSpecialize ("Hreg" $! r1 n). rewrite lookup_insert_ne in Hreg; last congruence. rewrite /RegLocate Hreg.
          auto.
      }
      iAssert (((fixpoint interp1) W) (storev1,storev1))%I with "[HVPCr Hreg]" as "#HVstorev1".
      { destruct storev1.
        - repeat rewrite fixpoint_interp1_eq. by cbn.
        - destruct r2. cbn in Hwoa; inversion Hwoa; by exfalso.
          destruct_cap c. cbn in Hwoa.
          destruct (<[PC:=inr (pc_p, pc_g, pc_b, pc_e, pc_a)]> r !! r0) eqn:Hrr0; inversion Hwoa; clear Hwoa; subst w.
          destruct (decide (r0 = PC)).
          + subst r0. rewrite lookup_insert in Hrr0. by inversion Hrr0.
          + iSpecialize ("Hreg" $! r0 n). rewrite lookup_insert_ne in Hrr0; last congruence. by rewrite /RegLocate Hrr0.
      }
      case_decide as Haeq.
      + iExists pc_w.
        destruct Hallows as [Hrinr [Hwa [Hwb Hloc] ] ].
        iDestruct "HStoreRes" as (w' w'') "[-> [-> HLoadRes]]".
        rewrite lookup_insert in Ha0; inversion Ha0; clear Ha0; subst.
        iDestruct "HLoadRes" as (ρ1) "(Hstate' & % & % & % & % & Hr & Hrel')".
        rewrite insert_insert. rewrite big_sepM_insert. 2: { rewrite lookup_insert_ne//. }
        rewrite big_sepM_insert;[|auto]. iDestruct "Hmem" as "(Ha1 & $ & _)".
        rewrite insert_insert. rewrite big_sepM_insert. 2: { rewrite lookup_insert_ne//. }
        rewrite big_sepM_insert;[|auto]. iDestruct "Hmem'" as "(Ha2 & $ & _)".
        iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
        destruct ((a1 =? a0)%Z) eqn:Heqa.
        assert (related_sts_pub_world W (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs)) as Hpub.
        { apply new_worldU_pub. }
        iDestruct (storev_interp_mono (new_worldU W a0 pc_p pc_g pc_b pc_e pc_a r offs) with "[HVr1]") as "Hr1Mono2";
          [eauto..|eapply new_worldU_lookup;eauto| |].
        { iApply interp_monotone;[|iFrame "#"]. iPureIntro. auto. }
        iDestruct ("Hpubmono" $! _ _ Hpub with "Hpc_w") as "Hpc_w'". iSimpl in "Hpc_w'".
        apply Z.eqb_eq,z_of_eq in Heqa as ->.
        * rewrite H1. iFrame.
          destruct (decide (ρ1 = Monotemporary ∨ ρ1 = Permanent)).
          ** iDestruct (region_close_next with "[$Hr $Ha1 $Ha2 $Hrel' $Hstate' $HVstorev1 $Hr1Mono]") as "Hr"; eauto;
               [intros [g Hcontr];destruct o as [o | o]; subst;try done..| |].
             { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
             destruct o as [-> | ->]; iDestruct (region_open_prepare with "Hr") as "$"; iFrame.
             all: iFrame "Hpc_w"; iPureIntro;apply related_sts_pub_refl_world.
          ** apply Decidable.not_or in n as [Hne1 n].
             destruct ρ1;try congruence.
             (* ρ1 = Uninitialized w *)
             unfold monotonicity_guarantees_region.
             iSimpl in "Hr1Mono2".
             iMod (region_close_next_mono_uninit_w with "[$Hr $Hsts $Ha1 $Ha2 $Hrel' $Hstate' $HVstorev1 $Hr1Mono2]") as "[Hr Hsts]";eauto.
             { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
             iModIntro. iDestruct (region_open_prepare with "Hr") as "$". iFrame. unfold new_worldU.
             rewrite Hz Hnext H1 Z.eqb_refl. iFrame "Hpc_w'".
             rewrite /new_worldU Hz Hnext H1 Z.eqb_refl in Hpub. auto.
        * iDestruct (region_close_next with "[$Hr $Ha1 $Ha2 $Hrel' $Hstate' $HVstorev1 $Hr1Mono]") as "Hr"; eauto.
          { intros [g Hcontr]. specialize (H4 g). done. }
          { intros [g Hcontr]. specialize (H5 g). done. }
          { apply not_elem_of_cons; split; [auto|apply not_elem_of_nil]. }
          iDestruct (region_open_prepare with "Hr") as "$". iFrame. iFrame "Hpc_w".
          iPureIntro. apply related_sts_pub_refl_world.
      + subst a1. inversion Hallows. iDestruct "HStoreRes" as "[-> [-> HStoreRes]]".
        rewrite insert_insert -memMap_resource_1.
        rewrite big_sepM_insert//. iDestruct "Hmem'" as "[Hmem' _]".
        rewrite lookup_insert in Ha0; inversion Ha0; simplify_eq.
        iExists storev1. iFrame.
        rewrite Hstdst.
        iDestruct (storev_interp_mono with "HVr1") as "Hr1Mono"; eauto.
        rewrite /wcond'. rewrite decide_True.
        2: { rewrite /writeAllowed_in_r_a. inversion Hallows. exists r1. rewrite /RegLocate H1. simpl.
               destruct H3 as (?&?&?&?&?). split;auto. destruct p0;inversion H3;auto. solve_addr. }
        destruct (pc_a =? a0)%Z eqn:Heqa0.
        * apply Z.eqb_eq,z_of_eq in Heqa0. subst a0.
          destruct ρ; iFrame "∗ #".
          all: try (iSplitR;[iApply "Hwcond";by iFrame "#"|]).
          all: try by (iPureIntro;apply related_sts_pub_refl_world).
          all: rewrite /monotonicity_guarantees_region.
          all: try (iModIntro;iSplit;[|iPureIntro;apply related_sts_pub_refl_world]).
          1,2: iModIntro;iIntros (W1 W2 Hrelated) "HP".
          1,2: iSimpl; iApply "Hwcond"; iApply "Hr1Mono";eauto;iApply "Hrcond";iFrame.
          exfalso. specialize (Hnotuninitialized p);done.
        * iModIntro. iFrame "∗ #".
          iSplitR. iApply "Hwcond". iFrame "#".
          rewrite /monotonicity_guarantees_region.
          destruct ρ;auto.
          all: (iSplit;[|iPureIntro;apply related_sts_pub_refl_world]);auto.
          all: iModIntro; iIntros (W1 W2 Hrelated) "H /=".
          all: iApply "Hwcond"; iApply "Hr1Mono";eauto.
          all: iApply "Hrcond";iFrame.
    - by exfalso.
   Qed.

   (* core lemma which will state that incrementing the address remains valid if world is initialized *)
   Lemma interp_initialize_limit W a' x x0 x1 x2 x3 r offs p0 g0 b0 e0 a0 zoffs w0 r1:
     related_sts_pub_world W (new_worldU W a' x x0 x1 x2 x3 r offs) →
     z_of_argument (<[PC:=inr (x, x0, x1, x2, x3)]> r) offs = Some zoffs →
     reg_allows_storeU (<[PC:=inr (x, x0, x1, x2, x3)]> r) r1 p0 g0 b0 e0 a' a' w0 →
     (a' + zoffs)%a = Some a' →
     (a' + 1)%a = Some a0 →
     fixpoint interp1 W (inr (p0, g0, b0, e0, a'),inr (p0, g0, b0, e0, a')) -∗
     fixpoint interp1 (new_worldU W a' x x0 x1 x2 x3 r offs) (inr (p0, g0, b0, e0, a0),inr (p0, g0, b0, e0, a0)).
   Proof.
     iIntros (Hpub Hzoff Hallows Ha' Hnext) "#Hvalid".
     destruct Hallows as [Hlookup [Hu (Hle1 & Hle2 & Hle3 & Hallows)] ].
     iDestruct (interp_monotone with "[] Hvalid") as "Hvalid'";[eauto|].
     iClear "Hvalid".
     destruct p0;inversion Hu;rewrite !fixpoint_interp1_eq /=;
       try (iDestruct "Hvalid'" as "[Heq Hvalid']";
       iDestruct "Heq" as %(->&->&->&->)); eauto.
     - destruct g0;iDestruct "Hvalid'" as "[Heq Hvalid']";
         try (iDestruct "Hvalid'" as "[Heq Hvalid']";
         iDestruct "Heq" as %(->&->&->));iSplit;auto;
         try done.
       + iDestruct "Hvalid'" as "[Hval1 Hval2]".
         assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
         assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
         rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
         rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
         assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
         rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
         iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
         assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
         assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
         assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
         assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
         rewrite (region_addrs_single a' a0);auto.
       + iDestruct "Hvalid'" as "[Hval1 Hval2]".
         assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
         assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
         rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
         rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
         assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
         rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
         iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
         assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
         assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
         assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
         assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
         rewrite (region_addrs_single a' a0);auto. simpl.
         iDestruct "Hval21" as "[Hval21 _]".
         iDestruct "Hval21" as "[Hrel %]".
         iSplit;auto. repeat iSplit;auto. iPureIntro.

         unfold region_state_U_mono in H3. destruct H3 as [-> | [ -> | [w Hstatic] ] ];auto.
         all: unfold new_worldU in Hstatic;rewrite Hzoff Ha' Z.eqb_refl in Hstatic.
         all: unfold new_worldU;rewrite Hzoff Ha' Z.eqb_refl.
         all: destruct (std W !! a') eqn:Hsome;[|congruence].
         all: destruct r0;inversion Hstatic; try congruence.
         all: simplify_map_eq.
     - destruct g0;try done; iDestruct "Hvalid'" as "[Heq Hvalid']";
         try (iDestruct "Hvalid'" as "[Heq Hvalid']";
         iDestruct "Heq" as %(->&->&->));iSplit;auto;
         try done.
       iDestruct "Hvalid'" as "[Hval1 Hval2]".
       assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
       assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
       rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
       rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
       assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
       rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
       iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
       assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
       assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
       assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
       assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
       rewrite (region_addrs_single a' a0);auto. simpl.
       iDestruct "Hval21" as "[Hval21 _]".
       iDestruct "Hval21" as "[Hrel %]".
       iSplit;auto. repeat iSplit;auto. iPureIntro.

       destruct H3 as [Hw | [w Hstatic] ];auto.
       unfold new_worldU in Hstatic. rewrite Hzoff Ha' Z.eqb_refl in Hstatic.
       unfold new_worldU. rewrite Hzoff Ha' Z.eqb_refl.
       destruct (std W !! a') eqn:Hsome;[|congruence].
       destruct r0;inversion Hstatic; try congruence.
       simplify_map_eq.
     - destruct g0;try done;iDestruct "Hvalid'" as "[Heq Hvalid']";
         try (iDestruct "Hvalid'" as "[Heq Hvalid']";
         iDestruct "Heq" as %(->&->&->));iSplit;auto;
         try done.
       + iDestruct "Hvalid'" as "[Hval1 Hval2]".
         assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
         assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
         rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
         rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
         assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
         rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
         iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
         assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
         assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
         assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
         assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
         rewrite (region_addrs_single a' a0);auto.
       + iDestruct "Hvalid'" as "[Hval1 Hval2]".
         assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
         assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
         rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
         rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
         assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
         rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
         iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
         assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
         assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
         assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
         assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
         rewrite (region_addrs_single a' a0);auto. simpl.
         iDestruct "Hval21" as "[Hval21 _]".
         iDestruct "Hval21" as "[Hrel %]".
         iSplit;auto. repeat iSplit;auto. iPureIntro.

         unfold region_state_U in H0. destruct H3 as [-> | [ -> | [w Hstatic] ] ];auto.
         all: unfold new_worldU in Hstatic;rewrite Hzoff Ha' Z.eqb_refl in Hstatic.
         all: unfold new_worldU;rewrite Hzoff Ha' Z.eqb_refl.
         all: destruct (std W !! a') eqn:Hsome;[|congruence].
         all: destruct r0;inversion Hstatic; try congruence.
         all: simplify_map_eq.
     - destruct g0;try done;iDestruct "Hvalid'" as "[Heq Hvalid']";
         try (iDestruct "Hvalid'" as "[Heq Hvalid']";
         iDestruct "Heq" as %(->&->&->));iSplit;auto;
         try done.
       iDestruct "Hvalid'" as "[Hval1 Hval2]".
       assert (addr_reg.min a' e0 <= addr_reg.min a0 e0)%Z;[solve_addr|].
       assert (b0 <= (addr_reg.min a' e0))%Z;[solve_addr|].
       rewrite (region_addrs_split b0 (addr_reg.min a' e0) (addr_reg.min a0 e0));[|solve_addr].
       rewrite big_sepL_app. rewrite bi.sep_comm. iFrame "Hval1".
       assert (addr_reg.max b0 a0 <= e0)%a;[solve_addr|].
       rewrite (region_addrs_split (addr_reg.max b0 a') (addr_reg.max b0 a0) e0);[|solve_addr].
       iDestruct (big_sepL_app with "Hval2") as "[Hval21 Hval22]". iFrame "Hval22".
       assert (addr_reg.min a' e0 = a') as ->;[solve_addr|].
       assert (addr_reg.min a0 e0 = a0) as ->;[solve_addr|].
       assert (addr_reg.max b0 a' = a') as ->;[solve_addr|].
       assert (addr_reg.max b0 a0 = a0) as ->;[solve_addr|].
       rewrite (region_addrs_single a' a0);auto. simpl.
       iDestruct "Hval21" as "[Hval21 _]".
       iDestruct "Hval21" as "[Hrel %]".
       iSplit;auto. repeat iSplit;auto. iPureIntro.

       unfold region_state_U in H0. destruct H3 as [Hw | [w Hstatic] ];auto.
       unfold new_worldU in Hstatic. rewrite Hzoff Ha' Z.eqb_refl in Hstatic.
       unfold new_worldU. rewrite Hzoff Ha' Z.eqb_refl.
       destruct (std W !! a') eqn:Hsome;[|congruence].
       destruct r0;inversion Hstatic; try congruence.
       simplify_map_eq.
   Qed.

   Lemma if_later {C} {eqdec: Decision C} (P:D) interp (Q Q' : iProp Σ) : (if (decide C) then ▷ Q else Q') -∗ ▷ (if (decide C) then Q else Q').
   Proof. iIntros "H". destruct (decide C);auto. Qed.

   Lemma storeU_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm) (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (rdst : RegName) (offs rsrc : Z + RegName) (P:D):
    ftlr_instr W r p g b e a w (StoreU rdst offs rsrc) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.

    (* To read out PC's name later, and needed when calling wp_load *)
    assert(∀ x : RegName, is_Some (<[PC:=inr (p, g, b, e, a)]> r.1 !! x)) as Hsome'.
    {
      intros. destruct (decide (x = PC)).
      rewrite e0 lookup_insert; unfold is_Some. by eexists.
        destruct Hsome with x; by rewrite lookup_insert_ne.
    }

    (* Initializing the names for the values of Hsrc now, to instantiate the existentials in step 1 *)
    assert (∃ p0 g0 b0 e0 a0 , read_reg_inr (<[PC:=inr (p, g, b, e, a)]> r.1) rdst p0 g0 b0 e0 a0) as [p0 [g0 [b0 [e0 [a0 HVdst] ] ] ] ].
    {
      specialize Hsome' with rdst as Hdst.
      destruct Hdst as [wdst Hsomedst].
      unfold read_reg_inr. destruct wdst. 2: destruct_cap c. all: repeat eexists.
      right. by exists z. by left.
    }

    assert (∃ storev, word_of_argument (<[PC:=inr (p, g, b, e, a)]> r.1) rsrc = Some storev) as [storev Hwoa].
    { destruct rsrc; cbn.
      - by exists (inl z).
      - specialize Hsome' with r0 as Hr0.
        destruct Hr0 as [wsrc Hsomer0].
        exists wsrc. by rewrite Hsomer0.
    }

    iAssert (interp_registers W (r.1, r.1)) as "#[_ Hreg']".
    { iApply interp_reg_dupl. iSplit;eauto. auto. }

    (* Step 1: open the region, if necessary, and store all the resources obtained from the region in allow_load_res *)
    iMod (create_store_res with "Hreg' Hinva Hr Hsts") as "[HStoreRes Hsts]"; eauto.
    { destruct Hp as [-> | [-> | [-> _] ] ];auto. }
    (* Clear helper values; they exist in the existential now *)
    clear HVdst p0 g0 b0 e0 a0 Hwoa storev.

    (* Step2: derive the concrete map of memory we need, and any spatial predicates holding over it *)
    iDestruct (store_res_implies_mem_map W  with "HStoreRes Ha Ha'") as (mem mem0) "[HStoreMem [HMemRes HMemRes'] ]".

    (* Step 3:  derive the non-spatial conditions over the memory map*)
    iDestruct (mem_map_implies_pure_conds _ _ _ _ _ _ _ _ _ offs with "HStoreMem") as %(HReadPC & HReadPC' & HStoreAP & HStoreAP' & Hdstcond); auto. simpl in *.

    iApply (wp_storeU_alt with "[$Hmap $HMemRes]");[apply Hi|eauto|auto..].
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; destruct Hsome with rr; eauto. }
    iDestruct (if_later with "Hwcond") as "Hwcond'";auto.
    iNext. iIntros (regs' mem' retv). iDestruct 1 as (HSpec) "[Hmem Hmap]".

    iMod (step_storeU_alt _ [SeqCtx] with "[$Hsmap $HMemRes' $Hj $Hspec]") as (retv' regs'' mem'') "(Hj & HSpec & Hmem' & Hsmap)";eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. rewrite lookup_insert_is_Some'; destruct Hsome with rr; eauto. }
    iDestruct "HSpec" as %HSpec'.

    specialize (StoreU_spec_determ _ _ _ _ _ _ _ _ _ _ _ _ Hdstcond HSpec HSpec') as (Heq1 & <- & Heq2).

    iAssert (future_pub_mono (λ Wv, P Wv.1 Wv.2) w w) as "#Hpubmono".
    { destruct ρ;simpl. all: iDestruct "Hmono" as "#Hmono"; iModIntro; simpl.
      all: iIntros (W1 W2 Hrelated) "Hp".
      all: iApply "Hmono";[|iFrame].
      1: iPureIntro; apply related_sts_pub_a_world;eauto.
      all: iPureIntro; apply related_sts_pub_priv_world;eauto. }

    destruct HSpec as [* ? ? ? ? ? -> Hincr|].
    { destruct Heq1 as [<- | Hcontr];[|inversion Hcontr].
      destruct Heq2 as [<- | Hcontr];[|inversion Hcontr].
      destruct (addr_eq_dec a0 a').
      - subst. destruct (a' + 1)%a eqn:Hincr';inversion Hincr.
        apply incrementPC_Some_inv in Hincr.

        destruct Hincr as (?&?&?&?&?&?&?&?&?&XYZ).
        iApply wp_pure_step_later; auto. iNext.
        (* From this, derive value relation for the current PC*)
        iDestruct (execcPC_implies_interp _ _ _ _ _ a with "Hinv") as "HVPC"; eauto.

        iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; [eauto..|].

        (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
        iDestruct "Hrcond" as "[Hrcond Hrcond']".
        assert (<[a':=w0]> mem = <[a':=w0]> mem0) as Hmemeq.
        { rewrite -insert_delete. erewrite Hdstcond;eauto. rewrite insert_delete;auto.
          inversion H3;eauto. }
        iMod (mem_map_recover_res with "HStoreMem Hreg' HVPC Hw Hrcond Hwcond' Hmono Hpubmono Hmem [Hmem'] Hsts") as (w') "(Hr & Hsts & Ha & Ha' & HSVInterp & Hmono & %)";eauto.
        { destruct Hp as [-> | [-> | [-> _] ] ];auto. }
        { rewrite Hmemeq. auto. }

        iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; auto.

        iDestruct (region_close with "[$Hstate HSVInterp $Hinva $Hr $Ha $Ha' $Hmono]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g1)|specialize (Hnotuninitialized p1)];try contradiction. }
        simplify_map_eq.

        iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";auto.
        iApply wp_wand_r.
        iSplitL. iApply ("IH" $! (new_worldU W a' p g b e a r.1 offs)
                              ((<[rdst:=inr (p0, g0, b0, e0, a0)]> (<[PC:=inr (p, g, b, e, a)]> r.1)),
                               (<[rdst:=inr (p0, g0, b0, e0, a0)]> (<[PC:=inr (p, g, b, e, a)]> r.1))) x x0 x1 x2 x4 with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hj]");simpl;auto.
        { iSplit. iPureIntro. cbn. intros x'. destruct (decide (rdst = x'));simplify_map_eq;eauto.
          iIntros (r1 Hne). destruct (decide (rdst = r1)).
          { subst. rewrite /RegLocate. assert (Hval:=H3).
            destruct H3 as [Hdst H3]. rewrite lookup_insert_ne// lookup_insert in H5. inv H5.
            iSpecialize ("Hreg'" $! r1 Hne). rewrite lookup_insert_ne// in Hdst. rewrite Hdst.
            simplify_map_eq.

            iDestruct (interp_initialize_limit with "Hreg'") as "HH";eauto.
          }
          { rewrite /RegLocate. simplify_map_eq. iSpecialize ("Hreg'" $! r1 Hne).
            destruct (r.1 !! r1) eqn:Hsomer;rewrite Hsomer.
            iApply (interp_monotone with "[] Hreg'"). auto.
            rewrite !fixpoint_interp1_eq. done.
          }
        }
        { iPureIntro. destruct (decide (rdst = PC));subst;[|simplify_map_eq;auto].
          unfold reg_allows_storeU in H3.
          rewrite /incrementPC in H6. simplify_map_eq. destruct H3 as [H3 _]. inversion H3;subst;auto. }
        { destruct (decide (rdst = PC));subst;simplify_map_eq;auto.
          - unfold reg_allows_storeU in H3.
            rewrite /incrementPC in H6. simplify_map_eq.
            destruct H3 as [H3 _]. inversion H3;subst;auto.
            iDestruct (interp_monotone with "[] HVPC") as "HVPC'";[iPureIntro;apply H9|].
            iClear "HVPC".
            rewrite fixpoint_interp1_eq /=.
            destruct Hp as [-> | [-> | [-> _] ] ]; try iDestruct "HVPC'" as "[_ HVPC']"; try (iFrame "HVPC'").
            rewrite /region_conditions /=.
            iApply (big_sepL_mono with "HVPC'"). intros.  iIntros "H". iApply and_exist_r.
            iDestruct "H" as (P0) "(?&?&?)". iExists _;iFrame.
            destruct x0; try done; iDestruct "HVPC'" as "[_ HVPC']"; iFrame "HVPC'".
          - iDestruct (interp_monotone with "[] HVPC") as "HVPC'";[iPureIntro;apply H9|].
            iClear "HVPC".
            rewrite fixpoint_interp1_eq /=.
            destruct Hp as [-> | [-> | [-> _] ] ]; try iDestruct "HVPC'" as "[_ HVPC']"; try iFrame "HVPC'".
            iApply (big_sepL_mono with "HVPC'"). intros.  iIntros "H". iApply and_exist_r.
            iDestruct "H" as (P0) "(?&?&?)". iExists _;iFrame.
            destruct x0; try done; try iDestruct "HVPC'" as "[_ HVPC']"; iFrame "HVPC'".
        }
        iIntros (v) "Hv". iIntros (Hhalted).
        iDestruct ("Hv" $! Hhalted) as (r0 W') "(Hj & Hfull & Hregs & Hregs' & % & Hown & sts & Hr)".
        iExists _,_. iFrame. iPureIntro. eapply related_sts_pub_priv_trans_world;eauto.
      - apply incrementPC_Some_inv in Hincr.

        destruct Hincr as (?&?&?&?&?&?&?&?&?&XYZ).
        iApply wp_pure_step_later; auto. iNext.
        iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hj /=";auto.

        (* From this, derive value relation for the current PC*)
        iDestruct (execcPC_implies_interp _ _ _ _ _ a  with "Hinv") as "HVPC"; eauto.

        iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; [eauto..|].

        assert (<[a':=w0]> mem = <[a':=w0]> mem0) as Hmemeq.
        { rewrite -insert_delete. erewrite Hdstcond;eauto. rewrite insert_delete;auto.
          inversion H3;eauto. }

        (* Step 4: return all the resources we had in order to close the second location in the region, in the cases where we need to *)
        iDestruct "Hrcond" as "[Hrcond Hrcond']".
        iMod (mem_map_recover_res with "HStoreMem Hreg' HVPC Hw Hrcond Hwcond' Hmono Hpubmono Hmem [Hmem'] Hsts") as (w') "(Hr & Hsts & Ha & Ha' & HSVInterp & Hmono & %)";eauto.
        { destruct Hp as [-> | [-> | [-> _] ] ];auto. }
        { rewrite Hmemeq. auto. }

        iDestruct (switch_monotonicity_formulation with "Hmono") as "Hmono"; auto.

        iDestruct (region_close with "[$Hstate $Hr HSVInterp $Hinva $Ha $Ha' $Hmono]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g1)|specialize (Hnotuninitialized p1)];try contradiction. }
        simplify_map_eq.

        iApply wp_wand_r.
        iSplitL. iApply ("IH" $! (new_worldU W a0 x x0 x1 x2 x3 r.1 offs)
                           (<[PC:=inr (x, x0, x1, x2, x3)]> r.1,
                            <[PC:=inr (x, x0, x1, x2, x3)]> r.1)
                           with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hj]"); simpl; auto.
        { iSplit. auto.
          iIntros (r1 Hne). destruct (decide (rdst = r1)).
          { subst. rewrite /RegLocate. assert (Hval:=H3).
            destruct H3 as [Hdst H3]. simplify_map_eq.
            iSpecialize ("Hreg'" $! r1 Hne). rewrite Hdst.
            iApply (interp_monotone with "[] Hreg'"). auto. }
          { rewrite /RegLocate. simplify_map_eq. iSpecialize ("Hreg'" $! r1 Hne).
            destruct (r.1 !! r1) eqn:Hsomer;rewrite Hsomer.
            iApply (interp_monotone with "[] Hreg'"). auto.
            rewrite !fixpoint_interp1_eq. done.
          }
        }
        { destruct (decide (rdst = PC));subst;simplify_map_eq;auto.
          - unfold reg_allows_storeU in H3.
            rewrite /incrementPC in H6. simplify_map_eq.
            destruct H3 as [H3 _]. inversion H3;subst;auto.
            iDestruct (interp_monotone with "[] HVPC") as "HVPC'";[iPureIntro;apply H8|].
            iClear "HVPC".
            rewrite (fixpoint_interp1_eq (new_worldU W a0 p0 g0 b0 e0 a0 r.1 offs)).
            destruct Hp as [-> | [-> | [-> _] ] ]; try iDestruct "HVPC'" as "[_ HVPC']"; try iFrame "HVPC'".
            iApply (big_sepL_mono with "HVPC'"). intros.  iIntros "H". iApply and_exist_r.
            iDestruct "H" as (P0) "(?&?&?)". iExists _;iFrame.
            destruct g0; try done; iDestruct "HVPC'" as "[_ HVPC']"; iFrame "HVPC'".
          - iDestruct (interp_monotone with "[] HVPC") as "HVPC'";[iPureIntro;apply H8|].
            iClear "HVPC".
            rewrite fixpoint_interp1_eq /=.
            destruct Hp as [-> | [-> | [-> _] ] ]; try iDestruct "HVPC'" as "[_ HVPC']"; try iFrame "HVPC'".
            iApply (big_sepL_mono with "HVPC'"). intros.  iIntros "H". iApply and_exist_r.
            iDestruct "H" as (P0) "(?&?&?)". iExists _;iFrame.
            destruct x0; try done; iDestruct "HVPC'" as "[_ HVPC']"; iFrame "HVPC'".
        }
        iIntros (v) "Hv". iIntros (Hhalted).
        iDestruct ("Hv" $! Hhalted) as (r0 W') "(Hj & Hfull & Hregs & Hregs' & % & Hown & sts & Hr)".
        iExists _,_. iFrame. iPureIntro. eapply related_sts_pub_priv_trans_world;eauto.
    }
    { iApply wp_pure_step_later; auto. iNext. iApply wp_value; auto. iIntros; discriminate. }
    Unshelve. all: auto.
  Qed.

End fundamental.
