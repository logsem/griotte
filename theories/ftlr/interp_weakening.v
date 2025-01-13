From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base monotone region.
From cap_machine Require Import addr_reg.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition IH: iProp Σ :=
    (□ ▷ (∀ (a0 : WORLD) (a1 : leibnizO Reg) (a2 : Perm) (a3 : Locality) (a4 a5 a6 : Addr),
              full_map a1
              -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → fixpoint interp1 a0 (a1 !r! r0))
                 -∗ registers_mapsto (<[PC:=inr (a2, a3, a4, a5, a6)]> a1)
                    -∗ region a0
                       -∗ sts_full_world a0
                          -∗ na_own logrel_nais ⊤
                             -∗ ⌜a2 = RX ∨ a2 = RWX ∨ a2 = RWLX ∧ a3 = Directed⌝
                                → □ region_conditions a0 a2 a3 a4 a5 -∗ interp_conf a0))%I.

  (* TODO: Move in monotone ? *)
  Lemma region_state_nwl_future W W' l l' p a a':
    (a < a')%a →
    LocalityFlowsTo l' l ->
    (if pwlU p then l = Directed else True) ->
    (@future_world Σ l' a' W W') -∗
    ⌜if pwlU p then region_state_pwl_mono W a else region_state_nwl W a l⌝ -∗
    ⌜region_state_nwl W' a l'⌝.
  Proof.
    intros Hlt Hlflows Hloc. iIntros "Hfuture %".
    destruct l'; simpl; iDestruct "Hfuture" as %Hf; iPureIntro.
    - assert (l = Global) as -> by (destruct l; simpl in Hlflows; tauto).
      destruct (pwlU p) eqn:HpwlU; try congruence.
      eapply region_state_nwl_monotone_nm_nl; eauto.
    - destruct (pwlU p).
      + subst l. inversion Hlflows.
      + eapply region_state_nwl_monotone_nm_nl; eauto.
        destruct l;inversion Hlflows;auto.
    - destruct (pwlU p).
      + subst l. simpl in *.
        left. eapply region_state_pwl_monotone_a;eauto.
      + destruct l.
        * right. eapply region_state_nwl_monotone_nm_nl;eauto.
          apply related_sts_pub_plus_priv_world.
          eapply related_sts_a_pub_plus_world;eauto.
        * right. eapply region_state_nwl_monotone_nm_nl;eauto.
          apply related_sts_pub_plus_priv_world.
          eapply related_sts_a_pub_plus_world;eauto.
        * destruct a0 as [a0 | a0].
          left. eapply region_state_pwl_monotone_a;eauto.
          right. eapply region_state_nwl_monotone_nm_nl;eauto.
          apply related_sts_pub_plus_priv_world.
          eapply related_sts_a_pub_plus_world;eauto.
  Qed.

  Lemma region_state_future W W' l l' p p' a a':
    (a < a')%a →
    PermFlowsTo p' p ->
    LocalityFlowsTo l' l ->
    (if pwlU p then l = Directed else True) ->
    (@future_world Σ l' a' W W') -∗
    ⌜if pwlU p then region_state_pwl_mono W a else region_state_nwl W a l⌝ -∗
    ⌜if pwlU p' then region_state_pwl_mono W' a else region_state_nwl W' a l'⌝.
  Proof.
    intros Hlt Hpflows Hlflows Hloc. iIntros "Hfuture %".
    case_eq (pwlU p'); intros.
    - assert (pwlU p = true) as Hpwl.
      { destruct p, p'; simpl in H; try congruence; simpl in Hpflows; try tauto. }
      rewrite Hpwl in a0, Hloc. subst l.
      destruct l'; simpl in Hlflows; try tauto.
      simpl; iDestruct "Hfuture" as "%"; iPureIntro.
      eapply region_state_pwl_monotone_a; eauto.
    - iApply (region_state_nwl_future with "Hfuture"); eauto.
  Qed.

  (* TODO: Move somewhere ?*)
  Lemma PermFlowsToPermFlows p p':
    PermFlowsTo p p' <-> PermFlows p p'.
  Proof.
    rewrite /PermFlows; split; intros; auto.
    destruct (Is_true_reflect (PermFlowsTo p p')); auto.
  Qed.

  Lemma localityflowsto_futureworld l l' W W' a a':
    LocalityFlowsTo l' l ->
    (a' <= a)%a →
    (@future_world Σ l' a W W' -∗
     @future_world Σ l a' W W').
  Proof.
    intros; destruct l, l'; auto.
    all: rewrite /future_world; iIntros "%".
    all: iPureIntro.
    1,2: eapply related_sts_pub_plus_priv_world; auto.
    1,2: eapply related_sts_a_pub_plus_world;eauto.
    eapply related_sts_a_weak_world;eauto.
  Qed.

  Lemma futureworld_refl l W a :
    ⊢ @future_world Σ l a W W.
  Proof.
    rewrite /future_world.
    destruct l.
    all: iPureIntro.
    apply related_sts_priv_refl_world.
    apply related_sts_priv_refl_world.
    apply related_sts_a_refl_world.
  Qed.

  Lemma promote_perm_flows_monotone p p':
    PermFlowsTo p p' ->
    PermFlowsTo (promote_perm p) (promote_perm p').
  Proof.
    destruct p, p'; simpl; tauto.
  Qed.

  Lemma promote_perm_flows p:
    PermFlowsTo p (promote_perm p).
  Proof.
    destruct p; simpl; tauto.
  Qed.

  Lemma promote_perm_pwl p:
    pwl (promote_perm p) = pwlU p.
  Proof.
    destruct p; reflexivity.
  Qed.

  Instance if_persistent (PROP: bi) (b: bool) (φ1 φ2: PROP) (H1: Persistent φ1) (H2: Persistent φ2):
    Persistent (if b then φ1 else φ2).
  Proof.
    destruct b; auto.
  Qed.

  Lemma rcond_interp : ⊢ rcond interp interp.
  Proof.
    iSplit;[auto|].
    iNext. iModIntro. iIntros (W1 W2 Hrelated) "_".
    rewrite fixpoint_interp1_eq. done.
  Qed.

  Lemma interp_weakeningEO W p p' l l' b b' e e' a a'
        (HU: if isU p then (a' <= a)%a else True):
    p <> E ->
    p ≠ O →
    p' ≠ E →
    p' ≠ O →
    (b <= b')%a ->
    (e' <= e)%a ->
    PermFlowsTo p' p ->
    LocalityFlowsTo l' l ->
    (fixpoint interp1) W (inr (p, l, b, e, a)) -∗
    (fixpoint interp1) W (inr (p', l', b', e', a')).
  Proof.
    intros HpnotE HpnotO HpnotE' HpnotO' Hb He Hp Hl. iIntros "HA".
    rewrite !fixpoint_interp1_eq !interp1_eq.
    destruct (perm_eq_dec p O);try congruence.
    destruct (perm_eq_dec p E);try congruence.
    destruct (perm_eq_dec p' O);try congruence.
    destruct (perm_eq_dec p' E);try congruence.
    iDestruct "HA" as "[#A [% #C]]".
    iSplit.
    { destruct (isU p') eqn:HisU'.
      { destruct (isU p) eqn:HisU.
        - destruct l; destruct l'; simpl.
          + destruct (Addr_le_dec b' e').
            { rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as "[#X %]".
              case_eq (pwlU p'); intros.
              + assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                assert (writeAllowed p || readAllowedU p = true) as ->.
                { destruct p;auto;inversion HP. }
                assert (writeAllowed p' || readAllowedU p' = true) as ->.
                { destruct p';auto;inversion H2. }
                iFrame "X".
                rewrite HP in H1. iPureIntro. auto.
              + assert (writeAllowed p || readAllowedU p = true) as ->.
                { destruct p;auto;inversion HP. }
                assert (writeAllowed p' || readAllowedU p' = true) as ->.
                { destruct p';auto;inversion H2. }
                iFrame "X".
                iAssert (future_world Global e' W W) as "Hfut".
                { iApply futureworld_refl. }
                iApply (region_state_nwl_future W W Global Global); eauto.
                assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);auto;destruct l;inversion H0;auto. }
            { rewrite (region_addrs_empty b' e'); auto. solve_addr. }
          + destruct (Addr_le_dec b' (min a' e')).
            { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as  "[#X %]".
              assert (writeAllowed p' || readAllowedU p' = true) as ->.
              { destruct p';auto;inversion HisU'. }
              assert (writeAllowed p || readAllowedU p = true) as ->.
              { destruct p';auto;inversion HisU';destruct p;inversion Hp;auto. }
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                rewrite HP in H1. iPureIntro. auto.
              * iApply (region_state_nwl_future W W Global Local _ _ (min a' e')); eauto.
                assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);inversion H0;auto.
                simpl. iPureIntro. eapply related_sts_priv_refl_world. }
            { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
          + destruct (Addr_le_dec b' (min a' e')).
            { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as  "[#X %]".
              assert (writeAllowed p' || readAllowedU p' = true) as ->.
              { destruct p';auto;inversion HisU'. }
              assert (writeAllowed p || readAllowedU p = true) as ->.
              { destruct p';auto;inversion HisU';destruct p;inversion Hp;auto. }
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                rewrite HP in H1. iPureIntro. auto.
              * iApply (region_state_nwl_future W W Global Directed _ _ (min a' e')); eauto.
                assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);inversion H0;auto.
                simpl. iPureIntro. eapply related_sts_a_refl_world. }
            { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
          + inversion Hl.
          + destruct (Addr_le_dec b' (min a' e')).
            { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b (min a e)). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as "[#X %]".
              assert (writeAllowed p || readAllowedU p = true) as ->.
              { destruct p;inversion HisU;auto. }
              assert (writeAllowed p' || readAllowedU p' = true) as ->.
              { destruct p';inversion HisU';auto. }
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                rewrite HP in H1. iPureIntro. auto.
              * iApply (region_state_nwl_future W W Local Local _ _ (min a' e')); eauto.
                assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);inversion H0;auto.
                iApply futureworld_refl. }
            { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
          + destruct (Addr_le_dec b' (min a' e')).
            { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b (min a e)). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as "[#X %]".
              assert (writeAllowed p || readAllowedU p = true) as ->.
              { destruct p;inversion HisU;auto. }
              assert (writeAllowed p' || readAllowedU p' = true) as ->.
              { destruct p';inversion HisU';auto. }
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                rewrite HP in H1. iPureIntro. auto.
              * iApply (region_state_nwl_future W W Local Directed _ _ (min a' e')); eauto.
                assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);inversion H0;auto.
                iApply futureworld_refl. }
            { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
          + inversion Hl.
          + inversion Hl.
          + destruct (Addr_le_dec b' (min a' e')).
            { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b (min a e)). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as "[#X %]".
              assert (writeAllowed p || readAllowedU p = true) as ->.
              { destruct p;inversion HisU;auto. }
              assert (writeAllowed p' || readAllowedU p' = true) as ->.
              { destruct p';inversion HisU';auto. }
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                rewrite HP in H1. iPureIntro. auto.
              * iApply (region_state_nwl_future W W Directed Directed _ _ (min a' e')); eauto.
                assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);inversion H0;auto.
                iApply futureworld_refl. }
            { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
        - simpl. destruct l'; simpl.
          { destruct (Addr_le_dec b' e').
            + rewrite (isWithin_region_addrs_decomposition b' e' b e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as "[#X %]".
              assert (writeAllowed p' || readAllowedU p' = true) as ->.
              { destruct p';inversion HisU';auto. }
              assert (writeAllowed p || readAllowedU p = true) as ->.
              { destruct p';inversion HisU';destruct p;inversion Hp;auto. }
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                rewrite HP in H1. iPureIntro. auto.
              * iApply (region_state_nwl_future W W l Global _ _ e'); eauto.
                assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);auto. destruct l;auto;inversion H0.
                iApply futureworld_refl.
            + rewrite (region_addrs_empty b' e'); auto. solve_addr. }
          { destruct (Addr_le_dec b' (min a' e')).
            + rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as "[#X %]".
              assert (writeAllowed p' || readAllowedU p' = true) as ->.
              { destruct p';inversion HisU';auto. }
              assert (writeAllowed p || readAllowedU p = true) as ->.
              { destruct p';inversion HisU';destruct p;inversion Hp;auto. }
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                rewrite HP in H1. iPureIntro. auto.
              * iApply (region_state_nwl_future W W l Local _ _ (min a' e')); eauto.
                assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);auto. destruct l;auto;inversion H0.
                iApply futureworld_refl.
            + rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
          { destruct (Addr_le_dec b' (min a' e')).
            + rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
              iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as "[#X %]".
              assert (writeAllowed p' || readAllowedU p' = true) as ->.
              { destruct p';inversion HisU';auto. }
              assert (writeAllowed p || readAllowedU p = true) as ->.
              { destruct p';inversion HisU';destruct p;inversion Hp;auto. }
              repeat iSplit; auto.
              case_eq (pwlU p'); intros.
              * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
                rewrite HP in H1. iPureIntro. auto.
              * iApply (region_state_nwl_future W W l Directed _ _ (min a' e')); eauto.
                assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs;
                  [apply elem_of_list_lookup;eauto|];auto.
                destruct (pwlU p);auto. destruct l;auto;inversion H0.
                iApply futureworld_refl.
            + rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. }
      }
      assert (HisU: isU p = false).
      { destruct p', p; simpl in *; try tauto; try congruence. }
      rewrite !HisU. simpl.
      destruct (Addr_le_dec b' e').
      - rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
        rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
        iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as "[#X %]".
        assert (readAllowedU p = false) as ->.
        { destruct p;auto;inversion HisU. }
        assert (readAllowedU p' = false) as ->.
        { destruct p';auto;inversion HisU'. }
        rewrite !orb_false_r.
        destruct (writeAllowed p') eqn:Hpw.
        { assert (writeAllowed p = true) as ->.
          { destruct p',p;inversion Hp;auto. }
          iSplitR; auto.
          case_eq (pwlU p'); intros.
          + assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
            rewrite HP in H1. iPureIntro. auto.
          + iApply (region_state_nwl_future _ _ _ _ _ x e'); eauto.
            assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs;
              [apply elem_of_list_lookup;eauto|];auto.
            destruct (pwlU p);auto. destruct l;auto;inversion H0.
            iApply futureworld_refl. }
        { destruct (writeAllowed p).
          - rewrite bi.and_exist_r. iExists interp. rewrite /read_cond. iFrame "X".
            iSplit;[iSplit;[iPureIntro;apply _|iApply rcond_interp]|].
            case_eq (pwlU p'); intros.
            + assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
              rewrite HP in H1. iPureIntro. auto.
            + iApply (region_state_nwl_future _ _ _ _ _ x e'); eauto.
              assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs;
                [apply elem_of_list_lookup;eauto|];auto.
              destruct (pwlU p);auto. destruct l;auto;inversion H0.
              iApply futureworld_refl.
          - rewrite bi.and_exist_r. iDestruct "X" as (P) "(?&?&?)".
            iExists P. iFrame "#".
            case_eq (pwlU p'); intros.
            + assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
              rewrite HP in H1. iPureIntro. auto.
            + iApply (region_state_nwl_future _ _ _ _ _ x e'); eauto.
              assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs;
                [apply elem_of_list_lookup;eauto|];auto.
              destruct (pwlU p);auto. destruct l;auto;inversion H0.
              iApply futureworld_refl. }
      - rewrite (region_addrs_empty b' e'); auto. solve_addr. }
    iSplit.
    { case_eq (pwlU p'); intros; auto.
      assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
      rewrite HP in H0. destruct l;inversion H0. destruct l'; simpl in Hl; try tauto. auto. }
    { case_eq (pwlU p'); intros; auto.
      - assert (pwlU p = true) as HP by (destruct p, p'; naive_solver).
        rewrite HP in H0; destruct l;inversion H0. destruct l'; simpl in Hl; try tauto.
        destruct (isU p') eqn:HisU'; auto. simpl.
        destruct (isU p) eqn:HisU; simpl.
        + destruct (Addr_le_dec (max b' a') e').
          * rewrite HP. destruct (Addr_lt_dec (max b' a') (max b a)).
            { destruct (Addr_le_dec (max b a) e').
              - rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b a) e). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]".
                rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b' a') e'). 2: solve_addr.
                rewrite !big_sepL_app. rewrite (region_addrs_empty e' e'); [simpl; iFrame "#"|solve_addr].
                assert (Heq: min a e = max b a) by solve_addr. rewrite Heq.
                rewrite (isWithin_region_addrs_decomposition (max b' a') (max b a) b (max b a)). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". iFrame "#".
                iApply (big_sepL_impl with "A2"); auto.
                iModIntro; iIntros (k x Hx) "Hw".
                iDestruct "Hw" as "[#X %]".
                assert (writeAllowed p || readAllowedU p = true) as ->.
                { destruct p;inversion HP;auto. } iFrame "X".
                iPureIntro. left; auto.
              - rewrite (isWithin_region_addrs_decomposition (max b' a') e' b (min a e)). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
                iApply (big_sepL_impl with "A2"); auto.
                iModIntro; iIntros (k x Hx) "Hw".
                iDestruct "Hw" as "[#X %]".
                assert (writeAllowed p || readAllowedU p = true) as ->.
                { destruct p;inversion HP;auto. } iFrame "X".
                iPureIntro. left; auto. }
            { rewrite (isWithin_region_addrs_decomposition (max b' a') e' (max b a) e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]".
              iApply (big_sepL_impl with "C2"); auto. }
          * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr.
        + destruct (Addr_le_dec (max b' a') e').
          * rewrite HP. rewrite (isWithin_region_addrs_decomposition (max b' a') e' b e). 2: solve_addr.
            rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
            iApply (big_sepL_impl with "A2"); auto.
            iModIntro; iIntros (k x Hx) "Hw".
            iDestruct "Hw" as  "[#X %]".
            assert (writeAllowed p || readAllowedU p = true) as ->.
            { destruct p;inversion HP;auto. } iFrame "X".
            iPureIntro. left; auto.
          * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr.
      - destruct (isU p') eqn:HisU'; simpl; auto.
        destruct (isLocal l') eqn:Hl'; auto.
        destruct (isU p && isLocal l) eqn:X.
        + destruct (Addr_le_dec (max b' a') e').
          * destruct (Addr_lt_dec (max b' a') (max b a)).
            { destruct (Addr_le_dec (max b a) e').
              - rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b a) e). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]".
                rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b' a') e'). 2: solve_addr.
                rewrite !big_sepL_app. rewrite (region_addrs_empty e' e'); [simpl; iFrame "#"|solve_addr].
                assert (Heq: min a e = max b a) by solve_addr. rewrite Heq.
                rewrite (isWithin_region_addrs_decomposition (max b' a') (max b a) b (max b a)). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
                iSplitR.
                + iApply (big_sepL_impl with "A2"); auto.
                  iModIntro; iIntros (k x Hx) "Hw".
                  iDestruct "Hw" as "[#X %]".
                  assert (writeAllowed p || readAllowedU p = true) as ->.
                  { destruct p;inversion H1;auto. } iFrame "X".
                  iPureIntro. destruct (pwlU p).
                  { destruct l';inversion Hl';destruct l;inversion H0;inversion Hl. left; auto. }
                  { destruct l; simpl in H1; auto.
                    - destruct l';auto. right; left; auto.
                    - destruct l';inversion Hl;auto. right;left;auto.
                    - destruct l';inversion Hl. destruct H2;[left;auto|right;left;auto]. }
                + iSplitL; auto. iApply (big_sepL_impl with "C2"); auto.
                  iModIntro; iIntros (k x Hx) "Hw".
                  iDestruct "Hw" as "[#X %]".
                  iFrame "X".
                  iPureIntro.
                  destruct (pwlU p).
                  { destruct l';inversion Hl';destruct l;inversion H0;inversion Hl.
                    destruct H2;[left;auto|right;right;auto]. }
                  { destruct l; simpl in H1; auto.
                    - destruct l';auto. right; left; auto.
                    - destruct l';inversion Hl;auto. right;left;auto.
                    - destruct l';inversion Hl. destruct H2;[left;auto|].
                      destruct H2;[right;left;auto|right;right;auto]. }
              - rewrite (isWithin_region_addrs_decomposition (max b' a') e' b (min a e)). 2: solve_addr.
                rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
                iApply (big_sepL_impl with "A2"); auto.
                iModIntro; iIntros (k x Hx) "Hw".
                iDestruct "Hw" as "[#X %]".
                assert (writeAllowed p || readAllowedU p = true) as ->.
                { apply andb_true_iff in X as [HisU Hlocal]. destruct p;inversion HisU;auto. }
                iFrame "#". iPureIntro. destruct (pwlU p).
                + destruct l,l'; inversion H0;inversion Hl. left; auto.
                + destruct l; simpl in H1; auto.
                  * destruct l';inversion Hl';[auto|right; left; auto].
                  * destruct l';inversion Hl;auto. right;left;auto.
                  * destruct l';inversion Hl. destruct H2;[left;auto|right;left;auto]. }
            { rewrite (isWithin_region_addrs_decomposition (max b' a') e' (max b a) e). 2: solve_addr.
              rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]". auto.
              iApply (big_sepL_impl with "C2"); auto.
              iModIntro; iIntros (k x Hx) "Hw".
              iDestruct "Hw" as "[#X %]".
              iFrame "X".
              iPureIntro.
              destruct (pwlU p);auto.
              + destruct l;inversion H0. destruct l';inversion Hl.
                destruct H2;[left;auto|right;right;auto].
              + apply andb_true_iff in X as [HisU Hll].
                destruct l',l;inversion Hll;inversion Hl'; inversion Hl;auto.
                right;left;auto. }
          * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr.
        + destruct (Addr_le_dec (max b' a') e').
          * rewrite (isWithin_region_addrs_decomposition (max b' a') e' b e). 2: solve_addr.
            rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
            iApply (big_sepL_impl with "A2"); auto.
            iModIntro; iIntros (k x Hx) "Hw".
            iDestruct "Hw" as "[#X %]".
            assert (writeAllowed p || readAllowedU p = true) as ->.
            { destruct p;auto;destruct p';inversion HisU';inversion Hp. }
            iFrame "#". iPureIntro. destruct (pwlU p).
            { destruct l;inversion H0. destruct l';inversion Hl. left; auto. }
            { destruct l; simpl in H2; auto.
              - destruct l'; try (right; left; auto);auto.
              - destruct l';inversion Hl;auto.
                right;left. auto.
              - destruct l';inversion Hl.
                destruct H2; [left|right;left]; auto. }
          * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr. }
  Qed.



  Lemma interp_weakening W p p' l l' b b' e e' a a'
        (HU: if isU p then (a' <= a)%a else True):
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo p' p ->
      LocalityFlowsTo l' l ->
      IH -∗
      (fixpoint interp1) W (inr (p, l, b, e, a)) -∗
      (fixpoint interp1) W (inr (p', l', b', e', a')).
  Proof.
    intros HpnotE Hb He Hp Hl. iIntros "#IH HA".
    destruct (perm_eq_dec p E); try congruence.
    destruct (perm_eq_dec p' O).
    { subst. rewrite !fixpoint_interp1_eq !interp1_eq. auto. }
    destruct (perm_eq_dec p O).
    { subst p; destruct p'; simpl in Hp; try tauto. }
    destruct (perm_eq_dec p' E).
    { rewrite !fixpoint_interp1_eq !interp1_eq.
      destruct (perm_eq_dec p' O);try congruence.
      destruct (perm_eq_dec p' E);try congruence.
      destruct (perm_eq_dec p O);try congruence.
      destruct (perm_eq_dec p E);try congruence.
      iDestruct "HA" as "[#A [% #C]]".
      (* p' = E *) subst p'. iModIntro.
      assert (HisU: isU p = false).
      { destruct p; simpl in Hp; simpl; auto; tauto. }
      rewrite !HisU /enter_cond /interp_expr /=.
      iIntros (r W') "#Hfuture". iNext.
      iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
      iSplitR; auto. rewrite /interp_conf.
      iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
      iModIntro. simpl. destruct (Addr_le_dec b' e').
      - rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr.
        rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
        iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as "[#X %]".
        simpl.
        destruct (writeAllowed p || readAllowedU p).
        { rewrite bi.and_exist_r. iExists interp.
          iFrame "#". iSplit;[iSplit;[iPureIntro;apply _|iApply rcond_interp]|].
          iApply (region_state_nwl_future with "Hfuture"); eauto.
          assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs;
            [apply elem_of_list_lookup;eauto|];auto.
          destruct (pwlU p);auto;destruct l;inversion H0;auto. }
        { rewrite bi.and_exist_r. iDestruct "X" as (P) "(? & ?)".
          iExists P;iFrame "#".
          iApply (region_state_nwl_future with "Hfuture"); eauto.
          assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs;
            [apply elem_of_list_lookup;eauto|];auto.
          destruct (pwlU p);auto;destruct l;inversion H0;auto. }
      - rewrite /region_conditions (region_addrs_empty b' e'); auto. solve_addr.
    }
    iApply interp_weakeningEO;eauto.
  Qed.

End fundamental.
