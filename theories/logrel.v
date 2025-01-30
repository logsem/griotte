From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export cap_lang region seal_store region_invariants.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine.rules Require Import rules_base.
Import uPred.

Ltac auto_equiv :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _) in H
  | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

Class logrel_na_invs Σ :=
  {
    logrel_na_invG :: na_invG Σ;
    logrel_nais : na_inv_pool_name;
  }.

(** interp : is a unary logical relation. *)
Section logrel.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ} {sealsg: sealStoreG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
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

  (* -------------------------------------------------------------------------------- *)

  (* Future world relation *)
  Definition future_world g W W' : iProp Σ :=
    (match g with
    | Local => ⌜related_sts_pub_world W W'⌝
    | Global => ⌜related_sts_priv_world W W'⌝
     end)%I.

  Lemma localityflowsto_futureworld g g' W W':
    LocalityFlowsTo g' g ->
    (@future_world g' W W' -∗
     @future_world g  W W').
  Proof.
    intros; destruct g, g'; auto.
    rewrite /future_world; iIntros "%".
    iPureIntro. eapply related_sts_pub_priv_world; auto.
  Qed.

  Lemma futureworld_refl g W :
    ⊢ @future_world g W W.
  Proof.
    rewrite /future_world.
    destruct g; iPureIntro
    ; [apply related_sts_priv_refl_world
      | apply related_sts_pub_refl_world].
  Qed.

  Global Instance future_world_persistent g W W': Persistent (future_world g W W').
  Proof.
    unfold future_world. destruct g; apply bi.pure_persistent.
  Qed.


  (* interp expression definitions *)
  Definition registers_pointsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Program Definition interp_reg (interp : D) : R :=
   λne (W : WORLD) (reg : leibnizO Reg),
     (full_map reg ∧
      ∀ (r : RegName) (v : Word), (⌜r ≠ PC⌝ → ⌜reg !! r = Some v⌝ → interp W v))%I.
  Solve All Obligations with solve_proper.

  Definition interp_conf W : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ →
              ∃ r W', full_map r ∧ registers_pointsto r
                   ∗ ⌜related_sts_priv_world W W'⌝
                   ∗ na_own logrel_nais ⊤
                   ∗ sts_full_world W'
                   ∗ region W' }})%I.

Program Definition interp_expr (interp : D) r : D :=
    (λne W w, (interp_reg interp W r ∗ registers_pointsto (<[PC:=w]> r)
                                     ∗ region W
                                     ∗ sts_full_world W
                                     ∗ na_own logrel_nais ⊤ -∗
                                     interp_conf W))%I.
  Solve All Obligations with solve_proper.

  (* Condition definitions *)
  Definition zcond (P : D) : iProp Σ :=
    (□ ∀ (W1 W2: WORLD) (z : Z), P W1 (WInt z) -∗ P W2 (WInt z)).
  Global Instance zcond_ne n :
    Proper ((=) ==> dist n) zcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance zcond_contractive P :
    Contractive (λ interp, ▷ zcond P)%I.
  Proof. solve_contractive. Qed.

  Definition rcond (p : Perm) (P interp : D) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word), P W w -∗ interp W (load_word p w)).
  Global Instance rcond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) rcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance rcond_contractive p P :
    Contractive (λ interp, ▷ rcond p P interp)%I.
  Proof. solve_contractive. Qed.

  Definition wcond (P interp : D) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word), interp W w -∗ P W w).
  Global Instance wcond_ne n :
    Proper ((=) ==> dist n ==> dist n) wcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance wcond_contractive P :
    Contractive (λ interp, ▷ wcond P interp)%I.
  Proof. solve_contractive. Qed.


  Definition exec_cond W b e g p (interp : D) : iProp Σ :=
    (∀ a r W', ⌜a ∈ₐ [[ b , e ]]⌝ → future_world g W W' →
            ▷ interp_expr interp r W' (WCap p g b e a))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof. unfold exec_cond. solve_proper. Qed.
  Global Instance exec_cond_contractive W b e g p :
    Contractive (λ interp, exec_cond W b e g p interp).
  Proof. solve_contractive. Qed.

  Definition enter_cond W p g b e a (interp : D) : iProp Σ :=
    (∀ r W', future_world g W W' →
             (▷ interp_expr interp r W' (WCap p g b e a))
               ∗ (▷ interp_expr interp r W' (WCap p Local b e a))
    )%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. unfold enter_cond. solve_proper. Qed.
  Global Instance enter_cond_contractive W p g b e a :
    Contractive (λ interp, enter_cond W p g b e a interp).
  Proof.
    solve_contractive.
  Qed.

  Definition persistent_cond (P:D) := (∀ Wv, Persistent (P Wv.1 Wv.2)).

  (* interp definitions *)


  (*
      -------------------------------------------------------------
      |          |         nwl           |          pwl           |
      -------------------------------------------------------------
      | Local    |       {P,T}           |           {T}          |
      |-----------------------------------------------------------|
      | Global   |       {P}             |           N/A          |
      -------------------------------------------------------------

   *)

  Definition region_state_pwl W (a : Addr) : Prop :=
    (std W) !! a = Some Temporary.

  Definition region_state_nwl W (a : Addr) (l : Locality) : Prop :=
    match l with
     | Local => (std W) !! a = Some Permanent ∨ (std W) !! a = Some Temporary
     | Global => (std W) !! a = Some Permanent
    end.

  (* For simplicity we might want to have the following statement in valididy of caps.
     However, it is strictly not necessary since it can be derived form full_sts_world *)

  Definition safeC (P : D) :=
    (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2).

  Definition monoReq (W : WORLD) (a : Addr) (p : Perm) (P : D) :=
    match (std W) !! a with
    | Some Temporary =>
        (if pwl p
         then mono_pub (safeC P)
         else mono_priv (safeC P) p)
    | Some Permanent => mono_priv (safeC P) p
    | _ => True%I
    end.

  Definition interp_z : D := λne _ w, ⌜match w with WInt z => True | _ => False end⌝%I.
  Definition interp_cap_O : D := λne _ _, True%I.

  Program Definition interp_cap_E (interp : D) : D :=
    λne W w, (match w with
              | WCap E g b e a => (□ enter_cond W RX g b e a interp)
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap (interp : D) : D :=
    λne W w, (match w with
              | WCap E _ _ _ _
              | WCap (O _ _) _ _ _ _
              | WCap (BPerm _ WL _ _) Global _ _ _ => False
              | WCap p g b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo p p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond p' P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ monoReq W a p' P
                      ∧ ⌜ if pwl p then region_state_pwl W a else region_state_nwl W a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with auto;solve_proper.


  (* (un)seal permission definitions *)
  (* Note the asymmetry: to seal values, we need to know that we are using a persistent predicate to create a value, whereas we do not need this information when unsealing values (it is provided by the `interp_sb` case). *)
  Definition safe_to_seal (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : D,  ⌜∀ w W, Persistent (P W w)⌝ ∗ (∀ W, seal_pred a (P W)) ∗ ▷ wcond P interp)%I.
  Definition safe_to_unseal (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : D, (∀ W, seal_pred a (P W)) ∗ ▷ rcond RO P interp)%I.

  Program Definition interp_sr (interp : D) : D :=
    λne W w, (match w with
    | WSealRange p g b e a =>
    (if permit_seal p then safe_to_seal interp b e else True)
    ∗ (if permit_unseal p then safe_to_unseal interp b e else True)
    | _ => False end ) %I.
  Solve All Obligations with solve_proper.

  Program Definition interp_sb (o : OType) (w : Word) :=
    (∃ P : Word → iPropI Σ,  ⌜∀ w, Persistent (P w)⌝
                                   ∗ seal_pred o P
                                   ∗ ▷ P w
                                   ∗ ▷ P (borrow w)
    )%I.

  Definition interp_False : D := λne _ _, False%I.

  Program Definition interp1 (interp : D) : D :=
    (λne W w,
    match w return _ with
    | WInt _ => interp_z W w
    | WCap (O _ _) g b e a => interp_cap_O W w
    | WCap E g b e a => interp_cap_E interp W w
    | WCap _ g b e a => interp_cap interp W w
    | WSealRange p g b e a => interp_sr interp W w
    | WSealed o sb => interp_sb o (WSealable sb)
    end)%I.
  Solve All Obligations with solve_proper.

  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.

  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto. destruct_perm c; auto.
    all: solve_contractive.
  Qed.

  Global Instance interp_cap_contractive :
    Contractive (interp_cap).
  Proof.
    (* solve_proper_prepare. *)
    (* destruct_word x1; auto. *)
    (* destruct c ; auto. *)
    (* destruct rx,w,g; auto. *)
    (* par: solve_contractive. (* TODO how can I set -async-proofs-tac-j *) *)
  Admitted. (* TODO holds, but very loooong *)

  Global Instance interp_sr_contractive :
    Contractive (interp_sr).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct (permit_seal sr), (permit_unseal sr);
    rewrite /safe_to_seal /safe_to_unseal;
    solve_contractive.
  Qed.

  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
   (*  intros n x y Hdistn W w. *)
   (*  rewrite /interp1. *)
   (*  destruct_word w; [auto|..]. *)
   (*  + destruct c; first auto ; cycle 1. *)
   (*    - by apply interp_cap_E_contractive. *)
   (*    - destruct rx,w,dl,dro. *)
   (*      par: try (by apply interp_cap_O_contractive). *)
   (*      par: by apply interp_cap_contractive. *)
   (* + by apply interp_sr_contractive. *)
   (* + rewrite /interp_sb; solve_contractive. *)
  Admitted. (* TODO holds, but very loooong *)

  Lemma fixpoint_interp1_eq (W : WORLD) (x : leibnizO Word) :
    fixpoint (interp1) W x ≡ interp1 (fixpoint (interp1)) W x.
  Proof. exact: (fixpoint_unfold (interp1) W x). Qed.

  Program Definition interp : D := λne W w, (fixpoint (interp1)) W w.
  Solve All Obligations with solve_proper.
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent W w : Persistent (interp W w).
  Proof.
    (* intros. destruct_word w; simpl; rewrite fixpoint_interp1_eq; simpl. *)
    (* - apply _. *)
    (* - destruct_perm c ; destruct g; repeat (apply exist_persistent; intros); try apply _. *)
    (* - destruct (permit_seal sr), (permit_unseal sr); rewrite /safe_to_seal /safe_to_unseal; apply _ . *)
    (* - apply exist_persistent; intros P. *)
    (*   unfold Persistent. iIntros "(Hpers & #Hs & HP & HPborrowed)". *)
    (*   iDestruct "Hpers" as %Hpers. *)
    (*   (* use knowledge about persistence *) *)
    (*   iAssert (<pers> ▷ P (WSealable sb))%I with "[ HP ]" as "HP". *)
    (*   { iApply later_persistently_1. by iApply Hpers.  } *)
    (*   iAssert (<pers> ▷ P (borrow (WSealable sb)))%I with "[ HPborrowed ]" as "HPborrowed". *)
    (*   { iApply later_persistently_1. by iApply Hpers.  } *)
    (*   iApply persistently_sep_2; iSplitR; auto. *)
    (*   iApply persistently_sep_2; auto. *)
  Admitted. (* TODO holds, but very loooong *)

  (* Non-curried version of interp *)
  Definition interpC := safeC interp.

  Lemma interp1_eq interp (W: WORLD) p g b e a:
    ((interp1 interp W (WCap p g b e a)) ≡
       (if (isO p)
        then True
        else
          if (isSentry p)
          then □ enter_cond W RX g b e a interp
          else ([∗ list] a ∈ finz.seq_between b e,
                  ∃ (p' : Perm) (P:D),
                    ⌜PermFlowsTo p p'⌝
                    ∗ ⌜persistent_cond P⌝
                    ∗ rel a p' (safeC P)
                    ∗ ▷ zcond P
                    ∗ (if readAllowed p' then ▷ (rcond p' P interp) else True)
                    ∗ (if writeAllowed p' then ▷ (wcond P interp) else True)
                    ∗ monoReq W a p' P
                    ∗ ⌜ if pwl p then region_state_pwl W a else region_state_nwl W a g⌝)
               ∗ (⌜ if pwl p then g = Local else True⌝))%I).
  Proof.
    (* iSplit. *)
    (* { iIntros "HA". *)
    (*   destruct (isO p) eqn:HnotO; subst; auto. *)
    (*   destruct (isSentry p) eqn:Hsentry; subst; auto. *)
    (*   { destruct p ; cbn in *;auto; congruence. } *)
    (*   destruct p; cbn in Hsentry; try congruence; auto ; clear Hsentry. *)
    (*   cbn. *)
    (*   destruct rx ; destruct w ; try (cbn in HnotO ; congruence); auto. *)
    (*   all: destruct g ;auto ; try (iSplit;eauto). *)
    (*   all: try (iApply (big_sepL_mono with "HA"); intros k a' ?; iIntros "H"). *)
    (*   all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a')"). *)
    (*   all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)). *)
    (* } *)
    (* { iIntros "A". *)
    (*   destruct (isO p) eqn:HnotO; subst; auto. *)
    (*   { destruct_perm p ; cbn in *;auto;try congruence. } *)
    (*   destruct (isSentry p) eqn:Hsentry; subst; auto. *)
    (*   { destruct p ; cbn in *;auto;congruence. } *)

    (*   iDestruct "A" as "(A & %)". *)
    (*   destruct_perm p; cbn in HnotO,Hsentry; try congruence; auto ; clear Hsentry. *)
    (*   all: destruct g eqn:Hg; simplify_eq ; eauto ; cbn. *)
    (*   all: try (iApply (big_sepL_mono with "A"); intros; iIntros "H"). *)
    (*   all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a')"). *)
    (*   all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)). *)
    (*   all: try (iApply (big_sepL_mono with "A"); intros; iIntros "H"). *)
    (* } *)
  Admitted. (* TODO holds, but very long to compile *)


  (* Inversion lemmas about interp  *)
  Lemma read_allowed_inv W (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp W (WCap p g b e a)) →
    ∃ (p' : Perm) (P:D),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ rel a' p' (safeC P)
      ∗ ▷ zcond P
      ∗ ▷ rcond p' P interp
      ∗ (if writeAllowed p' then (▷ wcond P interp) else True)
      ∗ monoReq W a' p' P
  .
  Proof.
    iIntros (Hin Ra) "Hinterp".
    apply Is_true_eq_true in Ra.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply readAllowed_nonO in Ra ;done. }
    replace (isSentry p) with false.
    2: { eapply readAllowed_isnot_sentry in Ra ;done. }
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & _)";eauto.
    pose proof (readAllowed_flows _ _ Hfl' Ra) as Ra'.
    rewrite Ra'.
    iExists p',P'; iFrame "#∗%"; try done.
  Qed.


  Lemma write_allowed_inv W (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    writeAllowed p →
    ⊢ (interp W (WCap p g b e a)) →
    ∃ (p' : Perm) (P:D),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ rel a' p' (safeC P)
      ∗ ▷ zcond P
      ∗ ▷ wcond P interp
      ∗ (if readAllowed p' then (▷ rcond p' P interp) else True)
      ∗ monoReq W a' p' P
  .
  Proof.
    iIntros (Hin Ra) "Hinterp".
    apply Is_true_eq_true in Ra.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply writeAllowed_nonO in Ra ;done. }
    replace (isSentry p) with false.
    2: { eapply writeAllowed_isnot_sentry in Ra ;done. }
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & _)";eauto.
    pose proof (writeAllowed_flows _ _ Hfl' Ra) as Ra'.
    rewrite Ra'.
    iExists p',P'; iFrame "#∗%"; try done.
  Qed.

  Lemma readAllowed_valid_cap_implies W p g b e a:
    readAllowed p = true ->
    withinBounds b e a = true ->
    interp W (WCap p g b e a) -∗
           ⌜∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked ∧ (∀ m, ρ ≠ Frozen m)⌝.
  Proof.
    intros Hra Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply readAllowed_nonO in Hra ;done. }
    replace (isSentry p) with false.
    2: { eapply readAllowed_isnot_sentry in Hra ;done. }
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    iPureIntro.
    destruct (pwl p); simplify_eq.
    naive_solver.
    destruct g; naive_solver.
  Qed.

  Lemma writeAllowed_valid_cap_implies W p g b e a:
    writeAllowed p = true ->
    withinBounds b e a = true ->
    interp W (WCap p g b e a) -∗
           ⌜∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked ∧ (∀ m, ρ ≠ Frozen m)⌝.
  Proof.
    intros Hra Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply writeAllowed_nonO in Hra ;done. }
    replace (isSentry p) with false.
    2: { eapply writeAllowed_isnot_sentry in Hra ;done. }
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    iPureIntro.
    destruct (pwl p); simplify_eq.
    naive_solver.
    destruct g; naive_solver.
  Qed.

  Lemma writeLocalAllowed_implies_local W p g b e a:
    pwl p = true ->
    interp W (WCap p g b e a) -∗ ⌜ isLocal g = true ⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct_perm p; simpl in H; try congruence; destruct g; auto.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies W p g b e a:
    pwl p = true ->
    withinBounds b e a = true ->
    interp W (WCap p g b e a) -∗
           ⌜std W !! a = Some Temporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply pwl_nonO in Hp ;done. }
    replace (isSentry p) with false.
    2: { eapply pwl_isnot_sentry in Hp ;done. }
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    by rewrite Hp in Hstate.
  Qed.

  Lemma interp_in_registers
    W (regs : leibnizO Reg) (p : Perm) (g : Locality) (b e a : Addr):
      (∀ (r : RegName) (v : Word), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → fixpoint interp1 W v)%I
    -∗ (∃ (p' : Perm) (P : D),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel a p' (safeC P)
        ∗ ▷ zcond P
        ∗ (if readAllowed p' then ▷ rcond p' P interp else True)
        ∗ (if writeAllowed p' then ▷ wcond P interp else True)
        ∗ monoReq W a p' P
        ∗ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝
       )
    -∗ (∃ (p' : Perm) (P : D),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel a p' (safeC P)
        ∗ ▷ zcond P
        ∗ (if decide (readAllowed_in_r_a (<[PC:=WCap p g b e a]> regs) a)
            then ▷ (rcond p' P interp)
            else emp)
        ∗ (if decide (writeAllowed_in_r_a (<[PC:=WCap p g b e a]> regs) a)
            then ▷ wcond P interp
            else emp)
        ∗ monoReq W a p' P
        ∗ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝
       ).
  Proof.
    iIntros "#Hreg #H".
    iDestruct "H" as (p0 P0 Hflp0 Hperscond_P0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0 & HmonoR0 & %Hstate0)".
    iExists p0,P0.
    iFrame "%#".
    iSplit.
    - (* rcond *)
      destruct (decide (readAllowed_in_r_a (<[PC:=WCap p g b e a]> regs) a))
        as [Hra'|Hra']; auto.
      destruct (readAllowed p0) eqn:Hra; auto.
      destruct Hra' as (r & w & Hsome & Hrar & Hvw).
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert in Hsome; simplify_eq.
        eapply readAllowed_flows in Hrar; eauto.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      iDestruct ("Hreg" $! r w n Hsome) as "Hinterp_w".
      destruct_word w; cbn in * ; try done.
      destruct Hvw as [Hvw ->].
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_w".
      replace (isO c) with false.
      2: { eapply readAllowed_nonO in Hrar ;done. }
      replace (isSentry c) with false.
      2: { eapply readAllowed_isnot_sentry in Hrar ;done. }
      iDestruct "Hinterp_w" as "[Hinterp_w %Hc_cond ]".
      iDestruct (extract_from_region_inv with "Hinterp_w")
        as (p1 P1 Hflc1 Hperscond_P1) "(Hrel1 & Hzcond1 & Hrcond1 & Hwcond1 & HmonoR1 & %Hstate1)"
      ; eauto; iClear "Hinterp_w".
      apply readAllowed_flows in Hflc1; auto.
      iDestruct (rel_agree a0 _ _ p0 p1 with "[$Hrel0 $Hrel1]") as "(-> & Heq)".
      congruence.
    - (* wcond *)
      destruct (decide (writeAllowed_in_r_a (<[PC:=WCap p g b e a]> regs) a))
        as [Hwa'|Hwa']; auto.
      destruct (writeAllowed p0) eqn:Hwa; auto.
      destruct Hwa' as (r & w & Hsome & Hwaw & Hvw).
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert in Hsome; simplify_eq.
        eapply writeAllowed_flows in Hwaw; eauto.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      iDestruct ("Hreg" $! r w n Hsome) as "Hinterp_w".
      destruct_word w; cbn in * ; try done.
      destruct Hvw as [Hvw ->].
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_w".
      replace (isO c) with false.
      2: { eapply writeAllowed_nonO in Hwaw ;done. }
      replace (isSentry c) with false.
      2: { eapply writeAllowed_isnot_sentry in Hwaw ;done. }
      iDestruct "Hinterp_w" as "[Hinterp_w %Hc_cond ]".
      iDestruct (extract_from_region_inv with "Hinterp_w")
        as (p1 P1 Hflc1 Hperscond_P1) "(Hrel1 & Hzcond1 & Hrcond1 & Hwcond1 & HmonoR1 & %Hstate1)"
      ; eauto; iClear "Hinterp_w".
      apply writeAllowed_flows in Hflc1; auto.
      iDestruct (rel_agree a0 _ _ p0 p1 with "[$Hrel0 $Hrel1]") as "(-> & Heq)".
      congruence.
  Qed.

End logrel.
