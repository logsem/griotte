From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
(* From cap_machine.rules Require Export rules. *)
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
  (* condition definitions *)
  Program Definition read_write_cond a p (interp : D) : iProp Σ :=
    rel a p (λne Wv, interp Wv.1 Wv.2).
  Next Obligation.
  Proof. solve_proper. Qed.
  Global Instance read_write_cond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) read_write_cond.
  Proof.
    rewrite /read_write_cond rel_eq /rel. solve_proper_prepare.
    f_equiv =>γ. f_equiv.
    apply saved_anything_ne.
    solve_proper.
  Qed.

  Definition rcond (P interp : D) : iProp Σ :=
    (▷ □ ∀ (W: WORLD) (w : Word), P W w -∗ interp W w)
  ∗ (▷ □ ∀ (W1 W2: WORLD) (z : Z), P W1 (WInt z) -∗ P W2 (WInt z)).
  Program Definition read_cond a p (P : D) (interp : D) : iProp Σ :=
    rcond P interp ∗ rel a p (λne Wv, P Wv.1 Wv.2).
  Next Obligation.
  Proof. solve_proper. Qed.
  Global Instance read_cond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n ==> dist n) read_cond.
  Proof.
    rewrite /read_cond /rcond rel_eq /rel. solve_proper_prepare.
    apply sep_ne.
    - repeat f_equiv;auto.
    - solve_proper_prepare.
      f_equiv =>γ. f_equiv.
      apply saved_anything_ne.
      solve_proper.
  Qed.

  Definition wcond (P interp : D) : iProp Σ :=
    (▷ □ ∀ (W: WORLD) (w : Word), interp W w -∗ P W w).
  Global Instance wcond_ne n :
    Proper ((=) ==> dist n ==> dist n) wcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.

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

  Definition exec_cond W b e g p (interp : D) : iProp Σ :=
    (∀ a r W', ⌜a ∈ₐ [[ b , e ]]⌝ → future_world g W W' →
            ▷ interp_expr interp r W' (WCap p g b e a))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof. unfold exec_cond. solve_proper. Qed.

  Definition enter_cond W g b e a (interp : D) : iProp Σ :=
    (∀ r W', future_world g W W' →
        ▷ interp_expr interp r W' (WCap RX g b e a))%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. unfold enter_cond. solve_proper. Qed.

  (* interp definitions *)


  (* TODO update the table *)
  (*
      -------------------------------------------------------------
      |          |         nwl           |          pwl           |
      |          | - < a    |    a ≤ -   |  - < a    |    a ≤ -   |
      -------------------------------------------------------------
      | Directed | {M,P}    | {M,P,U}    |    {M}    |    {M,U}   |
      |-----------------------------------------------------------|
      | Local    |       {P}             |           N/A          |
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

  (* Definition region_state_U W (a : Addr) : Prop := *)
  (*   (std W) !! a = Some Permanent. *)

  (* Definition region_state_U_mono W (a : Addr) : Prop := *)
  (*   (std W) !! a = Some Temporary *)
  (*   \/ (std W) !! a = Some Permanent *)
  (*   ∨ (exists w, (std W) !! a = Some (Uninitialized w)). *)

  (* Definition region_state_U_pwl_mono W (a : Addr) : Prop := *)
  (*   (std W) !! a = Some Temporary *)
  (*   ∨ (exists w, (std W) !! a = Some (Uninitialized w)). *)

  (* For simplicity we might want to have the following statement in valididy of caps.
     However, it is strictly not necessary since it can be derived form full_sts_world *)
  (* Definition region_std W (a : Addr) : Prop := rel_is_std_i W (countable.encode a). *)


  Definition interp_z : D := λne _ w, ⌜match w with WInt z => True | _ => False end⌝%I.
  Definition interp_cap_O : D := λne _ _, True%I.

  Program Definition interp_cap_RO (interp : D) : D :=
    λne W w, (match w with
              | WCap RO g b e a =>
                [∗ list] a ∈ (finz.seq_between b e),
                  ∃ (p : Perm) (P:D),
                    ⌜PermFlows RO p⌝
                    ∧ ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
                    ∧ (read_cond a p P interp)
                    ∧ ⌜region_state_nwl W a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RW (interp : D) : D :=
    λne W w, (match w with
              | WCap RW g b e a =>
                [∗ list] a ∈ (finz.seq_between b e),
                  ∃ (p : Perm),
                    ⌜PermFlows RW p⌝
                    ∧ (read_write_cond a p interp) (* TODO should be wcond and rcond *)
                    ∧ ⌜region_state_nwl W a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne W w, (match w with
              | WCap RX g b e a =>
                ([∗ list] a ∈ (finz.seq_between b e),
                  ∃ (p : Perm) (P:D),
                    ⌜PermFlows RX p⌝
                    ∧ ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
                    ∧ (read_cond a p P interp)
                    ∧ ⌜region_state_nwl W a g⌝)
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_E (interp : D) : D :=
    λne W w, (match w with
              | WCap E g b e a => □ enter_cond W g b e a interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWX (interp : D) : D :=
    λne W w, (match w with
              | WCap RWX g b e a =>
                ([∗ list] a ∈ (finz.seq_between b e),
                  ∃ (p : Perm),
                    ⌜PermFlows RWX p⌝
                   ∧ (read_write_cond a p interp)
                   ∧ ⌜region_state_nwl W a g⌝)
              | _ => False end)%I.
  Solve All Obligations with solve_proper.

  (* Interp with WL *)
  Program Definition interp_cap_RWL (interp : D) : D :=
    λne W w, (match w with
              | WCap RWL Local b e a =>
                [∗ list] a ∈ (finz.seq_between b e),
                  ∃ p, ⌜PermFlows RWL p⌝
                       ∧ (read_write_cond a p interp)
                       ∧ ⌜region_state_pwl W a⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp_cap_RWLX (interp : D) : D :=
    λne W w, (match w with
              | WCap RWLX Local b e a =>
                [∗ list] a ∈ (finz.seq_between b e),
                  ∃ p, ⌜PermFlows RWLX p⌝
                       ∧ (read_write_cond a p interp)
                       ∧ ⌜region_state_pwl W a⌝
              | _ => False end)%I.
  Solve All Obligations with solve_proper.

  (* (un)seal permission definitions *)
  (* Note the asymmetry: to seal values, we need to know that we are using a persistent predicate to create a value, whereas we do not need this information when unsealing values (it is provided by the `interp_sb` case). *)
  Definition safe_to_seal (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : D,  ⌜∀ w W, Persistent (P W w)⌝ ∗ (∀ W, seal_pred a (P W)) ∗ wcond P interp)%I.
  Definition safe_to_unseal (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e), ∃ P : D, (∀ W, seal_pred a (P W)) ∗ rcond P interp)%I.

  Program Definition interp_sr (interp : D) : D :=
    λne W w, (match w with
    | WSealRange p g b e a =>
    (if permit_seal p then safe_to_seal interp b e else True)
    ∗ (if permit_unseal p then safe_to_unseal interp b e else True)
    | _ => False end ) %I.
  Solve All Obligations with solve_proper.

  Program Definition interp_sb (o : OType) (w : Word) :=
    (∃ P : Word → iPropI Σ,  ⌜∀ w, Persistent (P w)⌝ ∗ seal_pred o P ∗ ▷ P w)%I.

  Program Definition interp1 (interp : D) : D :=
    (λne W w,
    match w return _ with
    | WInt _ => interp_z W w
    | WCap O g b e a => interp_cap_O W w
    | WCap RO g b e a => interp_cap_RO interp W w
    | WCap RW g b e a => interp_cap_RW interp W w
    | WCap RX g b e a => interp_cap_RX interp W w
    | WCap E g b e a => interp_cap_E interp W w
    | WCap RWX g b e a => interp_cap_RWX interp W w
    | WCap RWL g b e a => interp_cap_RWL interp W w
    | WCap RWLX g b e a => interp_cap_RWLX interp W w
    | WSealRange p g b e a => interp_sr interp W w
    | WSealed o sb => interp_sb o (WSealable sb)
    end)%I.
  Solve All Obligations with solve_proper.

  Global Instance rcond_contractive P :
    Contractive (λ interp, rcond P interp).
  Proof. solve_contractive. Qed.

  Global Instance wcond_contractive P :
    Contractive (λ interp, wcond P interp).
  Proof. solve_contractive. Qed.

  Global Instance read_cond_contractive a p P :
    Contractive (λ interp, read_cond a p P interp).
  Proof. solve_contractive. Qed.

  Global Instance read_write_cond_contractive a p :
    Contractive (λ interp, read_write_cond a p interp).
  Proof.
    solve_proper_prepare.
    rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
    apply exist_ne =>γ. apply sep_ne; auto.
    f_equiv. solve_contractive.
  Qed.

  Global Instance exec_cond_contractive W b e g p :
    Contractive (λ interp, exec_cond W b e g p interp).
  Proof.
    solve_contractive.
  Qed.
  Global Instance enter_cond_contractive W b e a g :
    Contractive (λ interp, enter_cond W b e a g interp).
  Proof.
    solve_contractive.
  Qed.

  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.
  Global Instance interp_cap_RO_contractive :
    Contractive (interp_cap_RO).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto. destruct c; auto.
    solve_contractive.
  Qed.

  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto. destruct c; auto.
    solve_contractive.
  Qed.

  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto. destruct c, g; auto.
    solve_contractive.
  Qed.

  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto. destruct c; auto.
    solve_contractive.
  Qed.

  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto. destruct c; auto.
    solve_contractive.
  Qed.

  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto. destruct c,g; auto.
    all: solve_contractive.
  Qed.

  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto. destruct c,g; auto.
    all: solve_contractive.
  Qed.

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
    intros n x y Hdistn W w.
    rewrite /interp1.
    destruct_word w; [auto|..].
    + destruct c; first auto.
      - by apply interp_cap_RO_contractive.
      - by apply interp_cap_RW_contractive.
      - by apply interp_cap_RWL_contractive.
      - by apply interp_cap_RX_contractive.
      - by apply interp_cap_E_contractive.
      - by apply interp_cap_RWX_contractive.
      - by apply interp_cap_RWLX_contractive.
   + by apply interp_sr_contractive.
   + rewrite /interp_sb. solve_contractive.
  Qed.

  Lemma fixpoint_interp1_eq (W : WORLD) (x : leibnizO Word) :
    fixpoint (interp1) W x ≡ interp1 (fixpoint (interp1)) W x.
  Proof. exact: (fixpoint_unfold (interp1) W x). Qed.

  Program Definition interp : D := λne W w, (fixpoint (interp1)) W w.
  Solve All Obligations with solve_proper.
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent W w : Persistent (interp W w).
  Proof. intros. destruct_word w; simpl; rewrite fixpoint_interp1_eq; simpl.
         - apply _.
         - destruct c,g; repeat (apply exist_persistent; intros); try apply _.
         - destruct (permit_seal sr), (permit_unseal sr); rewrite /safe_to_seal /safe_to_unseal; apply _ .
         - apply exist_persistent; intros P.
           unfold Persistent. iIntros "(Hpers & #Hs & HP)".
           iDestruct "Hpers" as %Hpers.
           (* use knowledge about persistence *)
           iAssert (<pers> ▷ P (WSealable sb))%I with "[ HP ]" as "HP".
           { iApply later_persistently_1. by iApply Hpers.  }
           iApply persistently_sep_2; iSplitR; auto.
           iApply persistently_sep_2; auto.
  Qed.

  Global Instance ne_interpC : NonExpansive
                           (λ Wv : (WORLD * (leibnizO Word)), (interp Wv.1) Wv.2).
  Proof. intros. solve_proper. Qed.

  (* Non-curried version of interp *)
  Definition interpC :=
    (λne Wv : WORLD * (leibnizO Word), (interp Wv.1) Wv.2).

  Lemma interp_int W n : ⊢ interp W (WInt n).
  Proof. iIntros. rewrite /interp fixpoint_interp1_eq //. Qed.

  Lemma read_allowed_inv W (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp W (WCap p g b e a)) →
    ∃ (p' : Perm), ⌜ PermFlows p p'⌝
    ∗ (if writeAllowed p
      then read_write_cond a' p' interp
      else (∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∧ read_cond a' p' P interp)).
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p,g; try done;cbn.
    (* try (iDestruct "Hinterp" as "[Hinterp Hinterpe]"); *)
    all: try (iDestruct (extract_from_region_inv with "Hinterp") as (p P Hfl Hpers) "[Hinv _]"
              ; eauto ; iExists p,P; iFrame "%∗").
    all: try (iDestruct (extract_from_region_inv with "Hinterp") as (p Hfl) "[Hinv _]"
              ; eauto ; iExists p,P; iFrame "%∗").
  Qed.

  (* Lemma write_allowed_inv (a' a b e: Addr) p : *)
  (*   (b ≤ a' ∧ a' < e)%Z → *)
  (*   writeAllowed p → *)
  (*   ⊢ (interp (WCap p b e a) → *)
  (*     inv (logN .@ a') (interp_ref_inv a' interp))%I. *)
  (* Proof. *)
  (*   iIntros (Hin Wa) "Hinterp". *)
  (*   rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn. *)
  (*   destruct p; try contradiction. *)
  (*   - iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #[Hread Hwrite] ]";[eauto|]. *)
  (*     iApply (inv_iff with "Hinv"). *)
  (*     iNext. iModIntro. iSplit. *)
  (*     + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]". *)
  (*       iExists w. iFrame. iApply "Hread". iFrame. *)
  (*     + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]". *)
  (*       iExists w. iFrame. iApply "Hwrite". iFrame. *)
  (*   - iDestruct (extract_from_region_inv with "Hinterp") as (P) "[Hinv #[Hread Hwrite] ]";[eauto|]. *)
  (*     iApply (inv_iff with "Hinv"). *)
  (*     iNext. iModIntro. iSplit. *)
  (*     + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]". *)
  (*       iExists w. iFrame. iApply "Hread". iFrame. *)
  (*     + iIntros "HP". iDestruct "HP" as (w) "[Ha' HP]". *)
  (*       iExists w. iFrame. iApply "Hwrite". iFrame. *)
  (* Qed. *)


  Lemma writeLocalAllowed_implies_local W p g b e a:
    pwl p = true ->
    interp W (WCap p g b e a) -∗ ⌜ isLocal g = true ⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H; try congruence; destruct g; auto.
  Qed.

  Lemma readAllowed_valid_cap_implies W p g b e a:
    readAllowed p = true ->
    withinBounds b e a = true ->
    interp W (WCap p g b e a) -∗
           ⌜∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked ∧ (∀ m, ρ ≠ Frozen m)⌝.
  Proof.
    intros Hp Hb. iIntros "H".
    eapply withinBounds_le_addr in Hb.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in Hp; try congruence.
    - iDestruct (extract_from_region_inv with "H") as (p P Hfl Hpers) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro.
      destruct g; eauto;simpl in HH; destruct HH as [HH|HH]; eauto.
    - iDestruct (extract_from_region_inv with "H") as (p Hfl) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro.
      destruct g; eauto;simpl in HH; destruct HH as [HH|HH]; eauto.
    - destruct g; auto.
      iDestruct (extract_from_region_inv with "H") as (p Hpers) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. eauto.
    - iDestruct (extract_from_region_inv with "H") as (p P Hfl Hpers) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro.
      destruct g; eauto;simpl in HH; destruct HH as [HH|HH]; eauto.
    - iDestruct (extract_from_region_inv with "H") as (p Hfl) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro.
      destruct g; eauto;simpl in HH; destruct HH as [HH|HH]; eauto.
    - destruct g; eauto.
      iDestruct (extract_from_region_inv with "H") as (p Hfl) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. eauto.
  Qed.

  Definition region_conditions W p g b e:=
  ([∗ list] a ∈ (finz.seq_between b e),
     ∃ p', ⌜PermFlows p p'⌝
           ∗ (if writeAllowed p
              then read_write_cond a p' interp
              else (∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
                             ∧ read_cond a p' P interp))
           ∧ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝)%I.

  Global Instance region_conditions_persistent W p g b e : Persistent (region_conditions W p g b e).
  Proof.
    intros. rewrite /region_conditions. apply big_sepL_persistent. intros.
    destruct (writeAllowed p),(pwl p);apply _.
  Qed.

  Lemma readAllowed_implies_region_conditions W p g b e a:
    readAllowed p = true ->
    interp W (WCap p g b e a) -∗ region_conditions W p g b e.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    unfold region_conditions.
    destruct p; simpl in *; try congruence; destruct g; simpl; eauto.
    all:iApply (big_sepL_mono with "Hvalid");iIntros (k y Hin) "H".
    all: try (iDestruct "H" as (p P) "(%Hfl&%Hpers&[? ?]&?)"; iFrame "∗%").
    all: try (iDestruct "H" as (p) "(%Hfl&?&?)"; iFrame "∗%").
  Qed.

  Lemma execCond_implies_region_conditions W p g b e a:
    p = RX ∨ p = RWX ∨ (p = RWLX /\ g = Local) ->
    interp W (WCap p g b e a) -∗ region_conditions W p g b e.
  Proof.
    iIntros (Hp) "Hvalid".
    iApply readAllowed_implies_region_conditions; last done.
    destruct p; naive_solver.
  Qed.

  Lemma read_write_cond_implies_read_cond a p :
    read_write_cond a p interp -∗ ∃ P, read_cond a p P interp.
  Proof.
    iIntros "Hread". iExists interp. iFrame. rewrite /rcond. iSplit; auto.
    iNext. iModIntro. iIntros (W1 W2 z) "_". rewrite fixpoint_interp1_eq. done.
  Qed.

  Lemma rcond_interp : ⊢ rcond interp interp.
  Proof.
    iSplit;[auto|].
    iNext. iModIntro. iIntros (W1 W2 Hrelated) "_".
    rewrite fixpoint_interp1_eq. done.
  Qed.

  Lemma wcond_interp : ⊢ wcond interp interp.
  Proof.
    by iNext; iModIntro; iIntros (W1 w) "?".
  Qed.

  Lemma execcPC_implies_interp W p g b e a0:
    p = RX ∨ p = RWX ∨ p = RWLX ∧ g = Local →
    region_conditions W p g b e -∗ ((fixpoint interp1) W) (WCap p g b e a0).
  Proof.
    iIntros (Hp) "#HR".
    rewrite (fixpoint_interp1_eq _ (WCap _ _ _ _ _)).
    (do 2 try destruct Hp as [ | Hp]); [| |destruct Hp];subst; auto.
    all: rewrite /region_conditions /=.
    all: iApply (big_sepL_mono with "HR").
    all: intros;iIntros "H".
    iDestruct "H" as (p' Hfl) "[H %Hstate]" ;iDestruct "H" as (P) "[%Hpers ?]"; iFrame "%∗".
    all: iDestruct "H" as (p' Hfl) "[H %Hstate]"; iFrame "%∗".
  Qed.

  Lemma read_allowed_inv_regs (a' a b e: Addr) p g W r :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp_registers W r -∗
      interp W (WCap p g b e a) -∗
      (∃ (p' : Perm) (P : D),
          ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
          ∗ rel a' p' (λ Wv, P Wv.1 Wv.2)
          ∗ rcond P interp
          ∗ if decide (writeAllowed_in_r_a (<[PC:=(WCap p g b e a)]> r) a')
            then wcond P interp
            else emp))%I.
  Proof.
    iIntros (Hin Ra) "#Hregs #Hinterp".
    rewrite /interp_registers /interp_reg /=.
    iDestruct "Hregs" as "[Hfull Hregvalid]".
    case_decide as Hinra.
    - destruct Hinra as [reg (wa & Hra & Hwa & Ha) ].
      destruct (decide (reg = PC)).
      + simplify_map_eq.
        rewrite fixpoint_interp1_eq /=; cbn.
        destruct p,g
        ; try contradiction ; try done
        ; inversion Hwa; try done
        ; try (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv Hiff]"; eauto)
        ; try (iDestruct (extract_from_region_inv with "Hinterp") as (p) "[% [Hinv Hiff]]"; eauto).
        all: iExists p,interp;iFrame "%";try iFrame "Hinv".
        all: iSplitR;[iPureIntro;apply _|].
        all: iSplitR;[iApply rcond_interp|iApply wcond_interp].
      + simplify_map_eq.
        destruct wa; try inv Ha.
        destruct sb; try inv Ha.
        iSpecialize ("Hregvalid" $! _ _ n Hra).
        iClear "Hinterp".
        rewrite fixpoint_interp1_eq /=; cbn.
        destruct p0,g0; try contradiction; inversion Hwa; try done ; subst.
        all: iDestruct (extract_from_region_inv with "Hregvalid") as (p' Hflp') "[Hrwcond %Hstate]"; eauto.
        all: iExists p',interp; iFrame "Hrwcond".
        all: iSplitR;[iPureIntro;apply _|].
        all: iSplitR;[iApply rcond_interp|iApply wcond_interp].
    - rewrite fixpoint_interp1_eq /=; cbn.
      destruct p,g; try contradiction; try done.
      all: try (iDestruct (extract_from_region_inv with "Hinterp") as (p' Hflp') "[Hrwcond %Hstate]"; eauto).
      all: try (iDestruct (extract_from_region_inv with "Hinterp") as (p' P Hflp' Hpers) "[Hrwcond %Hstate]"; eauto).
      all: try (iDestruct "Hrwcond" as "[Hrcond Hrel]").
      all: try (iFrame "Hrel");try (iFrame "Hrwcond").
      all: iSplitR;[iPureIntro;apply _|auto].
      all: iSplitR;[iApply rcond_interp|auto].
  Qed.

  (* TODO fix if necessary *)
  Lemma extract_from_region_inv_regs a (a' b e : Addr) p g W r :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp_registers W r -∗
       region_conditions W p g b e -∗
      (∃ (p' : Perm) (P : D),
           ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
           ∗ rel a' p' (λ Wv, P Wv.1 Wv.2)
           ∗ rcond P interp
           ∗ if decide (writeAllowed_in_r_a (<[PC:=WCap p g b e a]> r) a')
             then wcond P interp
             else emp))%I.
  Proof.
    (* iIntros (Hin Ra) "#Hregs #Hinterp". *)
    (* rewrite /interp_registers /interp_reg /=. *)
    (* iDestruct "Hregs" as "[Hfull Hregvalid]". *)
    (* case_decide as Hinra. *)
    (* - destruct Hinra as [reg (wa & Hra & Hwa & Ha) ]. *)
    (*   destruct (decide (reg = PC)). *)
    (*   + simplify_map_eq. *)
    (*     rewrite /interp. *)
    (*     destruct p,g; try contradiction; inversion Hwa ; try done; subst. *)
    (*     all: iDestruct (extract_from_region_inv with "Hinterp") as (p' Hp') "[Hinv Hiff]"; eauto; cbn. *)
    (*     all: rewrite /read_write_cond ; iFrame "#%". *)
    (*     all: iSplitR;[iPureIntro;apply _|]. *)
    (*     all: iSplitR;[iApply rcond_interp | iApply wcond_interp ]. *)
    (*   + simplify_map_eq. *)
    (*     destruct wa; try inv Ha. *)
    (*     destruct sb; try inv Ha. *)
    (*     iSpecialize ("Hregvalid" $! _ _ n Hra). *)
    (*     iClear "Hinterp". *)
    (*     rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn. *)
    (*     destruct p0,g0; try contradiction; inversion Hwa; try done ; subst. *)
    (*     all: try (iDestruct (extract_from_region_inv with "Hregvalid") as (p' Hp') "[Hinv Hiff]" ;eauto;cbn). *)
    (*     all: rewrite /read_write_cond ; iFrame "#%". *)
    (*     iSplitL; [iPureIntro|]. destruct p,p' ; cbn in * ; inv Hp';try done. *)
    (*     rewrite /PermFlows //=. *)
    (*     all: iSplitR;[iPureIntro;apply _|]. *)
    (*     all: iSplitR;[iApply rcond_interp | iApply wcond_interp ]. *)
    (*     ;iExists p',interp;iFrame "Hinv";rewrite /rcond /wcond /=). *)
    (*     all: try (iSplitR;[iPureIntro;apply _|]). *)
    (*     all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z) "_";rewrite fixpoint_interp1_eq;auto). *)
    (*     all: iDestruct (extract_from_region_inv with "Hregvalid") as (p' Hp') "[Hinv Hiff]"; eauto *)
    (*     ;iExists interp;iFrame "Hinv";rewrite /rcond /wcond /=. *)
    (*     all: try (iSplitR;[iPureIntro;apply _|]). *)
    (*     all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z) "_";rewrite fixpoint_interp1_eq;auto). *)
    (* - rewrite /interp. cbn. *)
    (*   destruct p,g; try contradiction; try done. all: rewrite /region_conditions /=. *)
    (*   all: try (iDestruct (extract_from_region_inv with "Hinterp") as "[Ha _]"; eauto; iDestruct "Ha" as (P Hpers) "[Ha Hcond]";iExists P;iFrame "Ha Hcond"). *)
    (*   all: try (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv Hiff]";eauto;iExists interp;iFrame "Hinv";rewrite /rcond /wcond /=). *)
    (*   all: iSplitR;[iPureIntro;apply _|]. *)
    (*   all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z) "_";rewrite fixpoint_interp1_eq;auto). *)
  Admitted.

  Lemma writeLocalAllowed_valid_cap_implies W p g b e a:
    pwl p = true ->
    withinBounds b e a = true ->
    interp W (WCap p g b e a) -∗
           ⌜std W !! a = Some Temporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hvalid".
    eapply withinBounds_le_addr in Hb.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in Hp; try congruence; destruct g;try done.
    - iDestruct (extract_from_region_inv with "Hvalid") as (p' Hp') "[_ %]"; eauto.
    - iDestruct (extract_from_region_inv with "Hvalid") as (p' Hp') "[_ %]"; eauto.
  Qed.

  Lemma region_seal_pred_interp E W (b e a: OType) b1 b2 g :
    ([∗ list] o ∈ finz.seq_between b e, (∀ W, seal_pred o (interp W))) ={E}=∗
    interp W (WSealRange (b1,b2) g b e a).
  Proof.
    remember (finz.seq_between b e) as l eqn:Hgen. rewrite Hgen; revert Hgen.
    generalize b e. clear b e.
    induction l as [|hd tl IH].
    - iIntros (b e Hfinz) "_ !>".
      rewrite /interp fixpoint_interp1_eq /= /safe_to_seal /safe_to_unseal.
      rewrite -Hfinz. destruct b1, b2; iSplit; done.
    - iIntros (b e Hfinz).
      assert (b < e)%ot as Hlbe.
      {destruct (decide (b < e)%ot) as [|HF]; first auto. rewrite finz_seq_between_empty in Hfinz; [inversion Hfinz | solve_addr  ]. }
      apply finz_cons_tl in Hfinz as (b' & Hplus & Hfinz).
      specialize (IH b' e Hfinz). rewrite (finz_seq_between_split _ b' _).
      2 : split; solve_addr.
      iIntros "[#Hfirst Hca]".
      iMod (IH with "Hca") as "Hca". iModIntro.
      rewrite /interp !fixpoint_interp1_eq /= /safe_to_seal /safe_to_unseal.
      rewrite !(finz_seq_between_split b b' e). 2: { split ; solve_addr. }
      iDestruct "Hca" as "[Hseal Hunseal]".
      iSplitL "Hseal"; [destruct b1| destruct b2]; iFrame.
      all: iApply (big_sepL_mono with "Hfirst").
      all: iIntros (k a' Hk) "H"; cbn.
      all: iExists _; iFrame; auto.
      all: iSplit; auto.
      all: try (iPureIntro; apply _).
      rewrite /wcond;auto.
      iNext ; iModIntro; iIntros (? ? ?) "?"; rewrite !fixpoint_interp1_eq //=.
  Qed.


  (* Get the validity of sealing capabilities if we can allocate an arbitrary predicate,
     and can hence choose interp itself as the sealing predicate *)
  (* Lemma region_can_alloc_interp E W (b e a: OType) b1 b2 g: *)
  (*   ([∗ list] o ∈ finz.seq_between b e, can_alloc_pred o) ={E}=∗ *)
  (*   interp W (WSealRange (b1,b2) g b e a). *)
  (* Proof. *)
  (*   iIntros "Hca". *)
  (*   iDestruct (big_sepL_mono with "Hca") as "Hca". *)
  (*   iIntros (k a' Hk) "H". iDestruct (seal_store_update_alloc _ (interp W)  with "H") as "H". iExact "H". *)

  (*   iDestruct (big_sepL_bupd with "Hca") as "Hca". *)
  (*   iMod "Hca". *)
  (*   by iApply region_seal_pred_interp. *)
  (* Qed. *)

   Lemma interp1_eq interp (W: WORLD) p g b e a:
    ((interp1 interp W (WCap p g b e a)) ≡
             (if perm_eq_dec p O
              then True
              else
                if perm_eq_dec p E
                then □ enter_cond W g b e a interp
                else ([∗ list] a ∈ finz.seq_between b e,
                        ∃ p', ⌜PermFlows p p'⌝
                              ∗ (if writeAllowed p
                                 then read_write_cond a p' interp
                                 else (∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝
                                                ∧ read_cond a p' P interp))
                 ∗ ⌜ if pwl p then region_state_pwl W a else region_state_nwl W a g⌝)
                     ∗ (⌜ if pwl p then g = Local else True⌝))%I).
  Proof.
    iSplit.
    { iIntros "HA".
      destruct (perm_eq_dec p O); subst; auto.
      destruct (perm_eq_dec p E); subst; auto.
      destruct p; simpl; try congruence; auto
      ; destruct g ;auto
      ; try (iSplit;eauto)
      ; iApply (big_sepL_mono with "HA"); intros k a' ?; iIntros "H".
      - iDestruct "H" as (p' P Hflp' Hpers) "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' P Hflp' Hpers) "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' P Hflp' Hpers) "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' P Hflp' Hpers) "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
    }
    { iIntros "A".
      destruct (perm_eq_dec p O); subst; auto.
      destruct (perm_eq_dec p E); subst; auto.
      iDestruct "A" as "(A & %)".
      destruct p eqn:Hp; simpl in *; try congruence; subst; eauto; try (destruct g eqn:Hg); eauto.
      all: iApply (big_sepL_mono with "A"); intros; iIntros "H".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iDestruct "Hrcond" as (P Hpers) "Hrcond".
        iExists p',P ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iDestruct "Hrcond" as (P Hpers) "Hrcond".
        iExists p',P ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iDestruct "Hrcond" as (P Hpers) "Hrcond".
        iExists p',P ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iDestruct "Hrcond" as (P Hpers) "Hrcond".
        iExists p',P ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
      - iDestruct "H" as (p' Hflp') "[Hrcond %Hstate_a']".
        iExists p' ; iFrame "%#∗".
    }
  Qed.


End logrel.
