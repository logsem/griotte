From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine Require Import addr_reg region monotone.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


   (* TODO FIX *)
  Lemma interp_weakeningEO W p p' g g' b b' e e' a a' :
    p <> E ->
    p ≠ O →
    p' ≠ E →
    p' ≠ O →
    (b <= b')%a ->
    (e' <= e)%a ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    (fixpoint interp1) W (WCap p g b e a) -∗
    (fixpoint interp1) W (WCap p' g' b' e' a').
  Proof.
    (* intros HpnotE HpnotO HpnotE' HpnotO' Hb He Hp Hl. iIntros "HA". *)
    (* rewrite !fixpoint_interp1_eq !interp1_eq. *)
    (* destruct (perm_eq_dec p O);try congruence. *)
    (* destruct (perm_eq_dec p E);try congruence. *)
    (* destruct (perm_eq_dec p' O);try congruence. *)
    (* destruct (perm_eq_dec p' E);try congruence. *)
    (* iDestruct "HA" as "[#A [% #C]]". *)
    (* iSplit. *)
    (* { destruct (isU p') eqn:HisU'. *)
    (*   { destruct (isU p) eqn:HisU. *)
    (*     - destruct l; destruct l'; simpl. *)
    (*       + destruct (Addr_le_dec b' e'). *)
    (*         { rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as "[#X %]". *)
    (*           case_eq (pwlU p'); intros. *)
    (*           + assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*             { destruct p;auto;inversion HP. } *)
    (*             assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*             { destruct p';auto;inversion H2. } *)
    (*             iFrame "X". *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           + assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*             { destruct p;auto;inversion HP. } *)
    (*             assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*             { destruct p';auto;inversion H2. } *)
    (*             iFrame "X". *)
    (*             iAssert (future_world Global e' W W) as "Hfut". *)
    (*             { iApply futureworld_refl. } *)
    (*             iApply (region_state_nwl_future W W Global Global); eauto. *)
    (*             assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);auto;destruct l;inversion H0;auto. } *)
    (*         { rewrite (region_addrs_empty b' e'); auto. solve_addr. } *)
    (*       + destruct (Addr_le_dec b' (min a' e')). *)
    (*         { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as  "[#X %]". *)
    (*           assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*           { destruct p';auto;inversion HisU'. } *)
    (*           assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*           { destruct p';auto;inversion HisU';destruct p;inversion Hp;auto. } *)
    (*           repeat iSplit; auto. *)
    (*           case_eq (pwlU p'); intros. *)
    (*           * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           * iApply (region_state_nwl_future W W Global Local _ _ (min a' e')); eauto. *)
    (*             assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);inversion H0;auto. *)
    (*             simpl. iPureIntro. eapply related_sts_priv_refl_world. } *)
    (*         { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. } *)
    (*       + destruct (Addr_le_dec b' (min a' e')). *)
    (*         { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as  "[#X %]". *)
    (*           assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*           { destruct p';auto;inversion HisU'. } *)
    (*           assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*           { destruct p';auto;inversion HisU';destruct p;inversion Hp;auto. } *)
    (*           repeat iSplit; auto. *)
    (*           case_eq (pwlU p'); intros. *)
    (*           * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           * iApply (region_state_nwl_future W W Global Directed _ _ (min a' e')); eauto. *)
    (*             assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);inversion H0;auto. *)
    (*             simpl. iPureIntro. eapply related_sts_a_refl_world. } *)
    (*         { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. } *)
    (*       + inversion Hl. *)
    (*       + destruct (Addr_le_dec b' (min a' e')). *)
    (*         { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b (min a e)). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as "[#X %]". *)
    (*           assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*           { destruct p;inversion HisU;auto. } *)
    (*           assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*           { destruct p';inversion HisU';auto. } *)
    (*           repeat iSplit; auto. *)
    (*           case_eq (pwlU p'); intros. *)
    (*           * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           * iApply (region_state_nwl_future W W Local Local _ _ (min a' e')); eauto. *)
    (*             assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);inversion H0;auto. *)
    (*             iApply futureworld_refl. } *)
    (*         { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. } *)
    (*       + destruct (Addr_le_dec b' (min a' e')). *)
    (*         { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b (min a e)). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as "[#X %]". *)
    (*           assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*           { destruct p;inversion HisU;auto. } *)
    (*           assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*           { destruct p';inversion HisU';auto. } *)
    (*           repeat iSplit; auto. *)
    (*           case_eq (pwlU p'); intros. *)
    (*           * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           * iApply (region_state_nwl_future W W Local Directed _ _ (min a' e')); eauto. *)
    (*             assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);inversion H0;auto. *)
    (*             iApply futureworld_refl. } *)
    (*         { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. } *)
    (*       + inversion Hl. *)
    (*       + inversion Hl. *)
    (*       + destruct (Addr_le_dec b' (min a' e')). *)
    (*         { rewrite (isWithin_region_addrs_decomposition b' (min a' e') b (min a e)). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as "[#X %]". *)
    (*           assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*           { destruct p;inversion HisU;auto. } *)
    (*           assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*           { destruct p';inversion HisU';auto. } *)
    (*           repeat iSplit; auto. *)
    (*           case_eq (pwlU p'); intros. *)
    (*           * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           * iApply (region_state_nwl_future W W Directed Directed _ _ (min a' e')); eauto. *)
    (*             assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);inversion H0;auto. *)
    (*             iApply futureworld_refl. } *)
    (*         { rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. } *)
    (*     - simpl. destruct l'; simpl. *)
    (*       { destruct (Addr_le_dec b' e'). *)
    (*         + rewrite (isWithin_region_addrs_decomposition b' e' b e). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as "[#X %]". *)
    (*           assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*           { destruct p';inversion HisU';auto. } *)
    (*           assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*           { destruct p';inversion HisU';destruct p;inversion Hp;auto. } *)
    (*           repeat iSplit; auto. *)
    (*           case_eq (pwlU p'); intros. *)
    (*           * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           * iApply (region_state_nwl_future W W l Global _ _ e'); eauto. *)
    (*             assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);auto. destruct l;auto;inversion H0. *)
    (*             iApply futureworld_refl. *)
    (*         + rewrite (region_addrs_empty b' e'); auto. solve_addr. } *)
    (*       { destruct (Addr_le_dec b' (min a' e')). *)
    (*         + rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as "[#X %]". *)
    (*           assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*           { destruct p';inversion HisU';auto. } *)
    (*           assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*           { destruct p';inversion HisU';destruct p;inversion Hp;auto. } *)
    (*           repeat iSplit; auto. *)
    (*           case_eq (pwlU p'); intros. *)
    (*           * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           * iApply (region_state_nwl_future W W l Local _ _ (min a' e')); eauto. *)
    (*             assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);auto. destruct l;auto;inversion H0. *)
    (*             iApply futureworld_refl. *)
    (*         + rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. } *)
    (*       { destruct (Addr_le_dec b' (min a' e')). *)
    (*         + rewrite (isWithin_region_addrs_decomposition b' (min a' e') b e). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*           iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as "[#X %]". *)
    (*           assert (writeAllowed p' || readAllowedU p' = true) as ->. *)
    (*           { destruct p';inversion HisU';auto. } *)
    (*           assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*           { destruct p';inversion HisU';destruct p;inversion Hp;auto. } *)
    (*           repeat iSplit; auto. *)
    (*           case_eq (pwlU p'); intros. *)
    (*           * assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*             rewrite HP in H1. iPureIntro. auto. *)
    (*           * iApply (region_state_nwl_future W W l Directed _ _ (min a' e')); eauto. *)
    (*             assert (x ∈ region_addrs b' (min a' e')) as [_ Hin]%elem_of_region_addrs; *)
    (*               [apply elem_of_list_lookup;eauto|];auto. *)
    (*             destruct (pwlU p);auto. destruct l;auto;inversion H0. *)
    (*             iApply futureworld_refl. *)
    (*         + rewrite (region_addrs_empty b' (min a' e')); auto. solve_addr. } *)
    (*   } *)
    (*   assert (HisU: isU p = false). *)
    (*   { destruct p', p; simpl in *; try tauto; try congruence. } *)
    (*   rewrite !HisU. simpl. *)
    (*   destruct (Addr_le_dec b' e'). *)
    (*   - rewrite (isWithin_region_addrs_decomposition b' e' b e); try solve_addr. *)
    (*     rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*     iApply (big_sepL_impl with "A2"); auto. iModIntro; iIntros (k x Hx) "Hw". *)
    (*     iDestruct "Hw" as "[#X %]". *)
    (*     assert (readAllowedU p = false) as ->. *)
    (*     { destruct p;auto;inversion HisU. } *)
    (*     assert (readAllowedU p' = false) as ->. *)
    (*     { destruct p';auto;inversion HisU'. } *)
    (*     rewrite !orb_false_r. *)
    (*     destruct (writeAllowed p') eqn:Hpw. *)
    (*     { assert (writeAllowed p = true) as ->. *)
    (*       { destruct p',p;inversion Hp;auto. } *)
    (*       iSplitR; auto. *)
    (*       case_eq (pwlU p'); intros. *)
    (*       + assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*         rewrite HP in H1. iPureIntro. auto. *)
    (*       + iApply (region_state_nwl_future _ _ _ _ _ x e'); eauto. *)
    (*         assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs; *)
    (*           [apply elem_of_list_lookup;eauto|];auto. *)
    (*         destruct (pwlU p);auto. destruct l;auto;inversion H0. *)
    (*         iApply futureworld_refl. } *)
    (*     { destruct (writeAllowed p). *)
    (*       - rewrite bi.and_exist_r. iExists interp. rewrite /read_cond. iFrame "X". *)
    (*         iSplit;[iSplit;[iPureIntro;apply _|iApply rcond_interp]|]. *)
    (*         case_eq (pwlU p'); intros. *)
    (*         + assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*           rewrite HP in H1. iPureIntro. auto. *)
    (*         + iApply (region_state_nwl_future _ _ _ _ _ x e'); eauto. *)
    (*           assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs; *)
    (*             [apply elem_of_list_lookup;eauto|];auto. *)
    (*           destruct (pwlU p);auto. destruct l;auto;inversion H0. *)
    (*           iApply futureworld_refl. *)
    (*       - rewrite bi.and_exist_r. iDestruct "X" as (P) "(?&?&?)". *)
    (*         iExists P. iFrame "#". *)
    (*         case_eq (pwlU p'); intros. *)
    (*         + assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*           rewrite HP in H1. iPureIntro. auto. *)
    (*         + iApply (region_state_nwl_future _ _ _ _ _ x e'); eauto. *)
    (*           assert (x ∈ region_addrs b' e') as [_ Hin]%elem_of_region_addrs; *)
    (*             [apply elem_of_list_lookup;eauto|];auto. *)
    (*           destruct (pwlU p);auto. destruct l;auto;inversion H0. *)
    (*           iApply futureworld_refl. } *)
    (*   - rewrite (region_addrs_empty b' e'); auto. solve_addr. } *)
    (* iSplit. *)
    (* { case_eq (pwlU p'); intros; auto. *)
    (*   assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*   rewrite HP in H0. destruct l;inversion H0. destruct l'; simpl in Hl; try tauto. auto. } *)
    (* { case_eq (pwlU p'); intros; auto. *)
    (*   - assert (pwlU p = true) as HP by (destruct p, p'; naive_solver). *)
    (*     rewrite HP in H0; destruct l;inversion H0. destruct l'; simpl in Hl; try tauto. *)
    (*     destruct (isU p') eqn:HisU'; auto. simpl. *)
    (*     destruct (isU p) eqn:HisU; simpl. *)
    (*     + destruct (Addr_le_dec (max b' a') e'). *)
    (*       * rewrite HP. destruct (Addr_lt_dec (max b' a') (max b a)). *)
    (*         { destruct (Addr_le_dec (max b a) e'). *)
    (*           - rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b a) e). 2: solve_addr. *)
    (*             rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]". *)
    (*             rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b' a') e'). 2: solve_addr. *)
    (*             rewrite !big_sepL_app. rewrite (region_addrs_empty e' e'); [simpl; iFrame "#"|solve_addr]. *)
    (*             assert (Heq: min a e = max b a) by solve_addr. rewrite Heq. *)
    (*             rewrite (isWithin_region_addrs_decomposition (max b' a') (max b a) b (max b a)). 2: solve_addr. *)
    (*             rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". iFrame "#". *)
    (*             iApply (big_sepL_impl with "A2"); auto. *)
    (*             iModIntro; iIntros (k x Hx) "Hw". *)
    (*             iDestruct "Hw" as "[#X %]". *)
    (*             assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*             { destruct p;inversion HP;auto. } iFrame "X". *)
    (*             iPureIntro. left; auto. *)
    (*           - rewrite (isWithin_region_addrs_decomposition (max b' a') e' b (min a e)). 2: solve_addr. *)
    (*             rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*             iApply (big_sepL_impl with "A2"); auto. *)
    (*             iModIntro; iIntros (k x Hx) "Hw". *)
    (*             iDestruct "Hw" as "[#X %]". *)
    (*             assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*             { destruct p;inversion HP;auto. } iFrame "X". *)
    (*             iPureIntro. left; auto. } *)
    (*         { rewrite (isWithin_region_addrs_decomposition (max b' a') e' (max b a) e). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]". *)
    (*           iApply (big_sepL_impl with "C2"); auto. } *)
    (*       * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr. *)
    (*     + destruct (Addr_le_dec (max b' a') e'). *)
    (*       * rewrite HP. rewrite (isWithin_region_addrs_decomposition (max b' a') e' b e). 2: solve_addr. *)
    (*         rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*         iApply (big_sepL_impl with "A2"); auto. *)
    (*         iModIntro; iIntros (k x Hx) "Hw". *)
    (*         iDestruct "Hw" as  "[#X %]". *)
    (*         assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*         { destruct p;inversion HP;auto. } iFrame "X". *)
    (*         iPureIntro. left; auto. *)
    (*       * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr. *)
    (*   - destruct (isU p') eqn:HisU'; simpl; auto. *)
    (*     destruct (isLocal l') eqn:Hl'; auto. *)
    (*     destruct (isU p && isLocal l) eqn:X. *)
    (*     + destruct (Addr_le_dec (max b' a') e'). *)
    (*       * destruct (Addr_lt_dec (max b' a') (max b a)). *)
    (*         { destruct (Addr_le_dec (max b a) e'). *)
    (*           - rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b a) e). 2: solve_addr. *)
    (*             rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]". *)
    (*             rewrite (isWithin_region_addrs_decomposition (max b a) e' (max b' a') e'). 2: solve_addr. *)
    (*             rewrite !big_sepL_app. rewrite (region_addrs_empty e' e'); [simpl; iFrame "#"|solve_addr]. *)
    (*             assert (Heq: min a e = max b a) by solve_addr. rewrite Heq. *)
    (*             rewrite (isWithin_region_addrs_decomposition (max b' a') (max b a) b (max b a)). 2: solve_addr. *)
    (*             rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*             iSplitR. *)
    (*             + iApply (big_sepL_impl with "A2"); auto. *)
    (*               iModIntro; iIntros (k x Hx) "Hw". *)
    (*               iDestruct "Hw" as "[#X %]". *)
    (*               assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*               { destruct p;inversion H1;auto. } iFrame "X". *)
    (*               iPureIntro. destruct (pwlU p). *)
    (*               { destruct l';inversion Hl';destruct l;inversion H0;inversion Hl. left; auto. } *)
    (*               { destruct l; simpl in H1; auto. *)
    (*                 - destruct l';auto. right; left; auto. *)
    (*                 - destruct l';inversion Hl;auto. right;left;auto. *)
    (*                 - destruct l';inversion Hl. destruct H2;[left;auto|right;left;auto]. } *)
    (*             + iSplitL; auto. iApply (big_sepL_impl with "C2"); auto. *)
    (*               iModIntro; iIntros (k x Hx) "Hw". *)
    (*               iDestruct "Hw" as "[#X %]". *)
    (*               iFrame "X". *)
    (*               iPureIntro. *)
    (*               destruct (pwlU p). *)
    (*               { destruct l';inversion Hl';destruct l;inversion H0;inversion Hl. *)
    (*                 destruct H2;[left;auto|right;right;auto]. } *)
    (*               { destruct l; simpl in H1; auto. *)
    (*                 - destruct l';auto. right; left; auto. *)
    (*                 - destruct l';inversion Hl;auto. right;left;auto. *)
    (*                 - destruct l';inversion Hl. destruct H2;[left;auto|]. *)
    (*                   destruct H2;[right;left;auto|right;right;auto]. } *)
    (*           - rewrite (isWithin_region_addrs_decomposition (max b' a') e' b (min a e)). 2: solve_addr. *)
    (*             rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*             iApply (big_sepL_impl with "A2"); auto. *)
    (*             iModIntro; iIntros (k x Hx) "Hw". *)
    (*             iDestruct "Hw" as "[#X %]". *)
    (*             assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*             { apply andb_true_iff in X as [HisU Hlocal]. destruct p;inversion HisU;auto. } *)
    (*             iFrame "#". iPureIntro. destruct (pwlU p). *)
    (*             + destruct l,l'; inversion H0;inversion Hl. left; auto. *)
    (*             + destruct l; simpl in H1; auto. *)
    (*               * destruct l';inversion Hl';[auto|right; left; auto]. *)
    (*               * destruct l';inversion Hl;auto. right;left;auto. *)
    (*               * destruct l';inversion Hl. destruct H2;[left;auto|right;left;auto]. } *)
    (*         { rewrite (isWithin_region_addrs_decomposition (max b' a') e' (max b a) e). 2: solve_addr. *)
    (*           rewrite !big_sepL_app. iDestruct "C" as "[C1 [C2 C3]]". auto. *)
    (*           iApply (big_sepL_impl with "C2"); auto. *)
    (*           iModIntro; iIntros (k x Hx) "Hw". *)
    (*           iDestruct "Hw" as "[#X %]". *)
    (*           iFrame "X". *)
    (*           iPureIntro. *)
    (*           destruct (pwlU p);auto. *)
    (*           + destruct l;inversion H0. destruct l';inversion Hl. *)
    (*             destruct H2;[left;auto|right;right;auto]. *)
    (*           + apply andb_true_iff in X as [HisU Hll]. *)
    (*             destruct l',l;inversion Hll;inversion Hl'; inversion Hl;auto. *)
    (*             right;left;auto. } *)
    (*       * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr. *)
    (*     + destruct (Addr_le_dec (max b' a') e'). *)
    (*       * rewrite (isWithin_region_addrs_decomposition (max b' a') e' b e). 2: solve_addr. *)
    (*         rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]". *)
    (*         iApply (big_sepL_impl with "A2"); auto. *)
    (*         iModIntro; iIntros (k x Hx) "Hw". *)
    (*         iDestruct "Hw" as "[#X %]". *)
    (*         assert (writeAllowed p || readAllowedU p = true) as ->. *)
    (*         { destruct p;auto;destruct p';inversion HisU';inversion Hp. } *)
    (*         iFrame "#". iPureIntro. destruct (pwlU p). *)
    (*         { destruct l;inversion H0. destruct l';inversion Hl. left; auto. } *)
    (*         { destruct l; simpl in H2; auto. *)
    (*           - destruct l'; try (right; left; auto);auto. *)
    (*           - destruct l';inversion Hl;auto. *)
    (*             right;left. auto. *)
    (*           - destruct l';inversion Hl. *)
    (*             destruct H2; [left|right;left]; auto. } *)
    (*       * rewrite (region_addrs_empty (max b' a') e'); auto. solve_addr. } *)
  Admitted.

  Lemma interp_weakening W p p' g g' b b' e e' a a' :
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo p' p ->
      LocalityFlowsTo g' g ->
      ftlr_IH -∗
      (fixpoint interp1) W (WCap p g b e a) -∗
      (fixpoint interp1) W (WCap p' g' b' e' a').
  Proof.
    intros HpnotE Hb He Hp Hl. iIntros "#IH HA".
    destruct (perm_eq_dec p E); try congruence.
    destruct (perm_eq_dec p' O).
    { subst.
      rewrite !fixpoint_interp1_eq !interp1_eq. auto. }
    destruct (perm_eq_dec p O).
    { subst p; destruct p'; simpl in Hp; try tauto. }
    destruct (perm_eq_dec p' E).
    { rewrite !fixpoint_interp1_eq !interp1_eq.
      destruct (perm_eq_dec p' O);try congruence.
      destruct (perm_eq_dec p' E);try congruence.
      destruct (perm_eq_dec p O);try congruence.
      destruct (perm_eq_dec p E);try congruence.
      iDestruct "HA" as "[#A %]".
      (* p' = E *) subst p'. iModIntro.
      rewrite /enter_cond /interp_expr /=.
      iIntros (r W') "#Hfuture". iNext.
      iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
      rewrite /interp_conf.
      iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
      iModIntro. rewrite fixpoint_interp1_eq /=.
      simpl. destruct (decide (b' < e'))%a.
      - rewrite (isWithin_finz_seq_between_decomposition b' e' b e); try solve_addr.
        rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
        iApply (big_sepL_impl with "A2"); auto.
        iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p' Hflp') "[#X %]".
        assert (Hflows': PermFlows RX p').
        { eapply PermFlows_trans; eauto.
          destruct p; simpl in *; auto; try congruence; try tauto; reflexivity. }
        destruct (writeAllowed p).
        { iExists p',interp.
          iSplitR; auto.
          iSplitR; first (iPureIntro; by apply _).
          iFrame "X".
          iSplitR; first iApply rcond_interp.
          iApply (region_state_nwl_future with "Hfuture"); eauto.
        }
        { iDestruct "X" as (P HpersP) "X".
          iExists p',P.
          iSplitR; auto.
          iSplitR; first (iPureIntro; by apply _).
          iFrame "X".
          iApply (region_state_nwl_future with "Hfuture"); eauto.
        }
      - rewrite /region_conditions (finz_seq_between_empty b' e'); auto. solve_addr.
    }
    iApply (interp_weakeningEO _ p p' g g'); eauto.
  Qed.

  (* from cerise *)
  (* Lemma interp_weakening p p' b b' e e' a a': *)
  (*     p <> E -> *)
  (*     (b <= b')%a -> *)
  (*     (e' <= e)%a -> *)
  (*     PermFlowsTo p' p -> *)
  (*     IH -∗ *)
  (*     (fixpoint interp1) (WCap p b e a) -∗ *)
  (*     (fixpoint interp1) (WCap p' b' e' a'). *)
  (* Proof. *)
  (*   intros HpnotE Hb He Hp. iIntros "#IH #HA". *)
  (*   destruct (decide (b' <= e')%a). *)
  (*   2: { rewrite !fixpoint_interp1_eq. destruct p'; try done; try (by iClear "HA"; rewrite /= !finz_seq_between_empty;[|solve_addr]). *)
  (*        iIntros (r). iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hna)". *)
  (*        iApply ("IH" with "Hfull Hreg Hregs Hna"); auto. iModIntro. *)
  (*        iClear "HA". by rewrite !fixpoint_interp1_eq /= !finz_seq_between_empty;[|solve_addr]. *)
  (*   } *)
  (*   destruct p'. *)
  (*   - rewrite !fixpoint_interp1_eq. done. *)
  (*   - rewrite !fixpoint_interp1_eq. *)
  (*     destruct p;inversion Hp; *)
  (*     (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]); *)
  (*     rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#". *)
  (*     + iApply (big_sepL_mono with "A2"). *)
  (*       iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame. *)
  (*     + iApply (big_sepL_mono with "A2"). *)
  (*       iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame. *)
  (*   - rewrite !fixpoint_interp1_eq. *)
  (*     destruct p;inversion Hp; *)
  (*     (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]); *)
  (*     rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#". *)
  (*   - rewrite !fixpoint_interp1_eq. *)
  (*     destruct p;inversion Hp; *)
  (*     (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]); *)
  (*     rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#". *)
  (*     iApply (big_sepL_mono with "A2"). *)
  (*     iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame. *)
  (*   - rewrite !fixpoint_interp1_eq. iIntros (r). iNext. iModIntro. iIntros "([Hfull Hreg] & Hregs & Hna)". *)
  (*     iApply ("IH" with "Hfull Hreg Hregs Hna"); auto. iModIntro. *)
  (*     destruct p; inversion Hp; try contradiction. *)
  (*     + rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]. *)
  (*       rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]"; iFrame "#". *)
  (*     + rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]. *)
  (*       rewrite !fixpoint_interp1_eq !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]". *)
  (*       iApply (big_sepL_mono with "A2"). *)
  (*       iIntros (k y Hsome) "H". iDestruct "H" as (P) "(H1 & H2 & H3)". iExists P. iFrame. *)
  (*   - rewrite !fixpoint_interp1_eq. *)
  (*     destruct p;inversion Hp; *)
  (*     (rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr]); *)
  (*     rewrite !big_sepL_app; iDestruct "HA" as "[A1 [A2 A3]]";iFrame "#". *)
  (* Qed. *)

  Lemma safe_to_unseal_weakening b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_unseal (fixpoint interp1) b e -∗
    safe_to_unseal (fixpoint interp1) b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_unseal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma safe_to_seal_weakening b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_seal (fixpoint interp1) b e -∗
    safe_to_seal (fixpoint interp1) b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_seal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma interp_weakening_ot W p p' g g' b b' e e' a a':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    SealPermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    (fixpoint interp1) W (WSealRange p g b e a) -∗
    (fixpoint interp1) W (WSealRange p' g' b' e' a').
  Proof.
  intros Hb He Hp Hg. iIntros "#HA".
  rewrite !fixpoint_interp1_eq. cbn.
  destruct (permit_seal p') eqn:Hseal; [eapply (permit_seal_flowsto _ p) in Hseal as ->; auto | ].
  all: destruct (permit_unseal p') eqn:Hunseal; [eapply (permit_unseal_flowsto _ p) in Hunseal as ->; auto | ]; iDestruct "HA" as "[Hs Hus]".
  all: iSplitL "Hs";
  [try iApply (safe_to_seal_weakening with "Hs") | try iApply (safe_to_unseal_weakening with "Hus")]; auto.
  Qed.

End fundamental.
