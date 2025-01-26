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

  Definition rcond (P interp : D) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word), P W w -∗ interp W w).
  Global Instance rcond_ne n :
    Proper ((=) ==> dist n ==> dist n) rcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance rcond_contractive P :
    Contractive (λ interp, ▷ rcond P interp)%I.
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
        ▷ interp_expr interp r W' (WCap p g b e a))%I.
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

  Definition interp_z : D := λne _ w, ⌜match w with WInt z => True | _ => False end⌝%I.
  Definition interp_cap_O : D := λne _ _, True%I.

  Program Definition interp_cap_E (interp : D) : D :=
    λne W w, (match w with
              | WCap E g b e a =>
                  □ enter_cond W RX g b e a interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_WO (interp : D) : D :=
    λne W w, (match w with
              | WCap WO g b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo WO p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ ⌜ region_state_nwl W a g ⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_WLO (interp : D) : D :=
    λne W w, (match w with
              | WCap WLO Local b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo WLO p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ ⌜ region_state_pwl W a ⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RO (interp : D) : D :=
    λne W w, (match w with
              | WCap RO g b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo RO p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ ⌜ region_state_nwl W a g ⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RW (interp : D) : D :=
    λne W w, (match w with
              | WCap RW g b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo RW p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ ⌜ region_state_nwl W a g ⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWL (interp : D) : D :=
    λne W w, (match w with
              | WCap RWL Local b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo RWL p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ ⌜ region_state_pwl W a ⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne W w, (match w with
              | WCap RX g b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo RX p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ ⌜ region_state_nwl W a g ⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWX (interp : D) : D :=
    λne W w, (match w with
              | WCap RWX g b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo RWX p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ ⌜ region_state_nwl W a g ⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWLX (interp : D) : D :=
    λne W w, (match w with
              | WCap RWLX Local b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo RWLX p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel a p' (λne Wv, P Wv.1 Wv.2)
                      ∧ ▷ zcond P
                      ∧ (if readAllowed p' then ▷ rcond P interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P interp else True)
                      ∧ ⌜ region_state_pwl W a ⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  (* (un)seal permission definitions *)
  (* Note the asymmetry: to seal values, we need to know that we are using a persistent predicate to create a value, whereas we do not need this information when unsealing values (it is provided by the `interp_sb` case). *)
  Definition safe_to_seal (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : D,  ⌜∀ w W, Persistent (P W w)⌝ ∗ (∀ W, seal_pred a (P W)) ∗ ▷ wcond P interp)%I.
  Definition safe_to_unseal (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e), ∃ P : D, (∀ W, seal_pred a (P W)) ∗ ▷ rcond P interp)%I.

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
    | WCap WO g b e a => interp_cap_WO interp W w
    | WCap WLO g b e a => interp_cap_WLO interp W w
    | WCap RO g b e a => interp_cap_RO interp W w
    | WCap RW g b e a => interp_cap_RW interp W w
    | WCap RWL g b e a => interp_cap_RWL interp W w
    | WCap RX g b e a => interp_cap_RX interp W w
    | WCap RWX g b e a => interp_cap_RWX interp W w
    | WCap RWLX g b e a => interp_cap_RWLX interp W w
    | WCap E g b e a => interp_cap_E interp W w
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

  Global Instance interp_cap_WO_contractive :
    Contractive (interp_cap_WO).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct_perm c ; auto ; solve_contractive.
  Qed.

  Global Instance interp_cap_WLO_contractive :
    Contractive (interp_cap_WLO).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct_perm c ; destruct g ; auto ; solve_contractive.
  Qed.

  Global Instance interp_cap_RO_contractive :
    Contractive (interp_cap_RO).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct_perm c ; auto ; solve_contractive.
  Qed.

  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct_perm c ; auto ; solve_contractive.
  Qed.

  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct_perm c ; destruct g ; auto ; solve_contractive.
  Qed.

  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct_perm c ; auto ; solve_contractive.
  Qed.

  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct_perm c ; auto ; solve_contractive.
  Qed.

  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    solve_proper_prepare.
    destruct_word x1; auto.
    destruct_perm c ; destruct g ; auto ; solve_contractive.
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
    + destruct c; first auto ; cycle 1.
      - by apply interp_cap_E_contractive.
      - destruct rx,w; first auto.
        * by apply interp_cap_WO_contractive.
        * by apply interp_cap_WLO_contractive.
        * by apply interp_cap_RO_contractive.
        * by apply interp_cap_RW_contractive.
        * by apply interp_cap_RWL_contractive.
        * by apply interp_cap_RX_contractive.
        * by apply interp_cap_RWX_contractive.
        * by apply interp_cap_RWLX_contractive.
   + by apply interp_sr_contractive.
   + rewrite /interp_sb; solve_contractive.
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
         - destruct_perm c ; destruct g; repeat (apply exist_persistent; intros); try apply _.
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

  (* Non-curried version of interp *)
  Definition safeC (P : D) :=
    (λ Wv : WORLD * (leibnizO Word), (P Wv.1) Wv.2).
  Definition interpC := safeC interp.

  (* TODO readAllow p or p'?
     On previous version, it was only based on p
     ; but in my paper, version, it is p'.
     Which one?
   *)
  Lemma interp1_eq interp (W: WORLD) p g b e a:
    ((interp1 interp W (WCap p g b e a)) ≡
       (if (decide (p=O))
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
                    ∗ (if readAllowed p' then ▷ (rcond P interp) else True)
                    ∗ (if writeAllowed p' then ▷ (wcond P interp) else True)
                    ∗ ⌜ if pwl p then region_state_pwl W a else region_state_nwl W a g⌝)
               ∗ (⌜ if pwl p then g = Local else True⌝))%I).
  Proof.
    iSplit.
    { iIntros "HA".
      destruct (decide (p=O)); subst; auto.
      destruct (isSentry p) eqn:Hsentry; subst; auto.
      { destruct p ; cbn in *;auto. congruence. }
      destruct p; cbn in Hsentry; try congruence; auto ; clear Hsentry.
      cbn.
      destruct rx
      ; destruct w ; try congruence ; auto
      ; destruct g ;auto
      ; try (iSplit;eauto).
      all: try (iApply (big_sepL_mono with "HA"); intros k a' ?; iIntros "H").
      all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate_a')").
      (* all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hpcond & %Hstate_a')"). *)
      all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)).
    }
    { iIntros "A".
      destruct (decide (p = O)); subst; auto.
      destruct (isSentry p) eqn:Hsentry; subst; auto.
      { destruct p ; cbn in *;auto. congruence. }
      iDestruct "A" as "(A & %)".
      destruct_perm p; cbn in Hsentry; try congruence; auto ; clear Hsentry.
      all: destruct g eqn:Hg; simplify_eq ; eauto ; cbn.
      all: try (iApply (big_sepL_mono with "A"); intros; iIntros "H").
      all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate_a')").
      all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)).
      all: try (iApply (big_sepL_mono with "A"); intros; iIntros "H").
    }
  Qed.

  Lemma interp_int W n : ⊢ interp W (WInt n).
  Proof. iIntros. rewrite /interp fixpoint_interp1_eq //. Qed.

  Lemma read_allowed_inv W (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp W (WCap p g b e a)) →
    ∃ (p' : Perm) (P:D),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ rel a' p' (safeC P)
      ∗ ▷ zcond P
      ∗ ▷ rcond P interp
      ∗ (if writeAllowed p' then (▷ wcond P interp) else True)
  .
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct g; try done;cbn.
    all: destruct_perm p; try done;cbn.
    all: try (iDestruct (extract_from_region_inv with "Hinterp")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & _)"); eauto.
    all: try (iExists p,P ; destruct_perm p; iFrame "#∗"; repeat (iSplit;[done|];done)).
    all: try done.
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
      ∗ (if readAllowed p' then (▷ rcond P interp) else True)
  .
  Proof.
    iIntros (Hin Ra) "Hinterp".
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct g; try done;cbn.
    all: destruct_perm p; try done;cbn.
    all: try (iDestruct (extract_from_region_inv with "Hinterp")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & _)"); eauto.
    all: try (iExists p,P ; destruct_perm p; iFrame "#∗"; repeat (iSplit;[done|];done)).
    all: try done.
  Qed.

  Lemma writeLocalAllowed_implies_local W p g b e a:
    pwl p = true ->
    interp W (WCap p g b e a) -∗ ⌜ isLocal g = true ⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct_perm p; simpl in H; try congruence; destruct g; auto.
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
    destruct_perm p; simpl in Hp; try congruence.
    all: try (iDestruct (extract_from_region_inv with "H")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & %Hstate)"); eauto.
    all: try (iDestruct (extract_from_region_inv with "H")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)"); eauto.
    all: try (destruct g ; auto;
             iDestruct (extract_from_region_inv with "H")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)"); eauto.
    all: iPureIntro.
    all: try (destruct g; eauto;simpl in Hstate; destruct Hstate as [Hstate|Hstate]; eauto).
  Qed.

  Lemma writeAllowed_valid_cap_implies W p g b e a:
    writeAllowed p = true ->
    withinBounds b e a = true ->
    interp W (WCap p g b e a) -∗
           ⌜∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked ∧ (∀ m, ρ ≠ Frozen m)⌝.
  Proof.
    intros Hp Hb. iIntros "H".
    eapply withinBounds_le_addr in Hb.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct_perm p; simpl in Hp; try congruence.
    all: try (iDestruct (extract_from_region_inv with "H")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & %Hstate)"); eauto.
    all: try (iDestruct (extract_from_region_inv with "H")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)"); eauto.
    all: try (destruct g ; auto;
             iDestruct (extract_from_region_inv with "H")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)"); eauto.
    all: try (destruct g ; auto;
             iDestruct (extract_from_region_inv with "H")
             as (p P Hfl Hpers) "(Hrel & Hzcond & Hwcond & %Hstate)"); eauto.
    all: iPureIntro.
    all: try (destruct g; eauto;simpl in Hstate; destruct Hstate as [Hstate|Hstate]; eauto).
  Qed.

  Lemma persistent_cond_interp : persistent_cond interp.
  Proof.
    intros W; apply _.
  Qed.

  Lemma zcond_interp : ⊢ zcond interp.
  Proof.
    by iModIntro; iIntros (W1 W2 w) "_"; iApply interp_int.
  Qed.

  Lemma rcond_interp : ⊢ rcond interp interp.
  Proof.
    by iModIntro; iIntros (W1 w) "?".
  Qed.

  Lemma wcond_interp : ⊢ wcond interp interp.
  Proof.
    by iModIntro; iIntros (W1 w) "?".
  Qed.

  (* Lemma read_allowed_inv_regs (a' a b e: Addr) p g W r : *)
  (*   (b ≤ a' ∧ a' < e)%Z → *)
  (*   readAllowed p → *)
  (*   ⊢ (interp_registers W r -∗ *)
  (*     interp W (WCap p g b e a) -∗ *)
  (*     (∃ (p' : Perm) (P : D), *)
  (*         ⌜persistent_cond P⌝ *)
  (*         ∗ rel a' p' (λ Wv, P Wv.1 Wv.2) *)
  (*         ∗ ▷ zcond P *)
  (*         ∗ (if decide (readAllowed_in_r_a (<[PC:=(WCap p g b e a)]> r) a') *)
  (*           then ▷ rcond P interp *)
  (*           else emp) *)
  (*         ∗ (if decide (writeAllowed_in_r_a (<[PC:=(WCap p g b e a)]> r) a') *)
  (*           then ▷ wcond P interp *)
  (*           else emp)))%I. *)
  (* Proof. *)
  (*   iIntros (Hin Ra) "#Hregs #Hinterp". *)
  (*   rewrite /interp_registers /interp_reg /=. *)
  (*   iDestruct "Hregs" as "[Hfull Hregvalid]". *)
  (*   case_decide as Hinra. *)
  (*   - destruct Hinra as [reg (wa & Hra & Hwa & Ha) ]. *)
  (*     destruct (decide (reg = PC)). *)
  (*     + simplify_map_eq. *)
  (*       rewrite fixpoint_interp1_eq /=; cbn. *)
  (*       destruct_perm p *)
  (*       ; destruct g *)
  (*       ; try contradiction ; try done *)
  (*       ; inversion Hwa; try done. *)
  (*       all: try (iDestruct (extract_from_region_inv with "Hinterp") *)
  (*         as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)" *)
  (*       ; eauto ; iClear "Hinterp Hregvalid"). *)
  (*       all: try (iDestruct (extract_from_region_inv with "Hinterp") *)
  (*         as (p P Hfl Hpers) "(Hrel & Hzcond & Hcond & %Hstate)" *)
  (*       ; eauto ; iClear "Hinterp Hregvalid"). *)
  (*       all: try (iExists p,P; iFrame "#"; done). *)
  (*     + simplify_map_eq. *)
  (*       destruct wa; try inv Ha. *)
  (*       destruct sb; try inv Ha. *)
  (*       iSpecialize ("Hregvalid" $! _ _ n Hra). *)
  (*       iClear "Hinterp". *)
  (*       rewrite fixpoint_interp1_eq /=; cbn. *)
  (*       destruct_perm p0 *)
  (*       ; cbn in Hwa *)
  (*       ; destruct g0 *)
  (*       ; try contradiction; inversion Hwa; try done ; subst. *)
  (*       all: try (iDestruct (extract_from_region_inv with "Hregvalid") *)
  (*         as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)" *)
  (*       ; eauto ; iClear "Hregvalid"). *)
  (*       all: try (iDestruct (extract_from_region_inv with "Hregvalid") *)
  (*         as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hwcond & %Hstate)" *)
  (*       ; eauto ; iClear "Hregvalid"). *)
  (*       all: iExists p',P'; iFrame "#"; done. *)
  (*   - rewrite fixpoint_interp1_eq /=; cbn. *)
  (*     destruct p,g; try contradiction; try done. *)
  (*     all: try (iDestruct (extract_from_region_inv with "Hinterp") *)
  (*              as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & %Hstate)" *)
  (*               ; eauto ; iClear "Hinterp Hregvalid"). *)
  (*     all: try (iDestruct (extract_from_region_inv with "Hinterp") *)
  (*              as (p P Hfl Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)" *)
  (*               ; eauto ; iClear "Hinterp Hregvalid"). *)
  (*     all: iExists p,P; iFrame "#"; done. *)
  (* Qed. *)

  Lemma write_allowed_implies_ra
    W (regs : leibnizO Reg) (p : Perm) (g : Locality) (b e a : Addr):
    readAllowed p = true
    -> (∀ (r : RegName) (v : Word), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → fixpoint interp1 W v)%I
    -∗ (∃ (p' : Perm) (P : D),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel a p' (λ Wv : prodO WORLD (leibnizO Word), P Wv.1 Wv.2)
        ∗ ▷ zcond P
        ∗ (if readAllowed p' then ▷ rcond P interp else True)
        ∗ (if writeAllowed p' then ▷ wcond P interp else True)
        ∗ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝
       )
    -∗ (∃ (p' : Perm) (P : D),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel a p' (λ Wv : prodO WORLD (leibnizO Word), P Wv.1 Wv.2)
        ∗ ▷ zcond P
        ∗ ▷ rcond P interp
        ∗ (if decide (writeAllowed_in_r_a (<[PC:=WCap p g b e a]> regs) a)
            then ▷ wcond P interp
            else emp)
        ∗ ⌜if pwl p then region_state_pwl W a else region_state_nwl W a g⌝
       ).
  Proof.
    intros Hrap.
    iIntros "#Hreg #H".
    iDestruct "H" as (p0 P0 Hflp0 Hperscond_P0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0 & %Hstate0)".
    destruct (readAllowed p0) eqn:Hrap'; cycle 1.
    { apply readAllowed_flows in Hflp0; auto; congruence.  }
    destruct (writeAllowed p0) eqn:Hwa.
    - iExists p0,P0.
      iSplit; first (iPureIntro ; apply Hflp0).
      iSplit; first (iPureIntro ; apply Hperscond_P0).
      iFrame "#".
      case_decide;auto.
    - assert (writeAllowed p = false) as Hwaw'.
      { destruct_perm p ; destruct_perm p0 ; cbn in * ; try done. }
      destruct (decide (writeAllowed_in_r_a (<[PC:=WCap p g b e a]> regs) a))
        as [Hwa'|Hwa']; cycle 1.
      { iExists p0, P0.
        iSplit; first (iPureIntro ; apply Hflp0).
        iSplit; first (iPureIntro ; apply Hperscond_P0).
        iFrame "#".
        auto.
      }

      destruct Hwa' as (r & w & Hsome & Hwaw & Hvw).
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert in Hsome; simplify_eq.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      iDestruct ("Hreg" $! r w n Hsome) as "Hinterp_w".
      destruct_word w; cbn in * ; try done.
      destruct Hvw as [Hvw ->].
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_w".
      destruct (decide (c = O)); first (subst; cbn in *;done).
      destruct (isSentry c) eqn:Henstry ; first (destruct_perm c; cbn in *; try done).
      iDestruct "Hinterp_w" as "[Hinterp_w %Hc_cond ]".
      iDestruct (extract_from_region_inv with "Hinterp_w")
        as (p1 P1 Hflc1 Hperscond_P1) "(Hrel1 & Hzcond1 & Hrcond1 & Hwcond1 & %Hstate1)"
      ; eauto; iClear "Hinterp_w".
      apply writeAllowed_flows in Hflc1; auto.
      iDestruct (rel_agree a0 _ _ p0 p1 with "[$Hrel0 $Hrel1]") as "(-> & Heq)".
      congruence.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies W p g b e a:
    pwl p = true ->
    withinBounds b e a = true ->
    interp W (WCap p g b e a) -∗
           ⌜std W !! a = Some Temporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hvalid".
    eapply withinBounds_le_addr in Hb.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct_perm p; simpl in Hp; try congruence; destruct g;try done.
    all:try (iDestruct (extract_from_region_inv with "Hvalid") as (????) "(_&_&_&_&%)"; eauto).
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
      iSplit;first (iPureIntro; apply _).
      iApply wcond_interp.
      iApply rcond_interp.
  Qed.

  Lemma monotonicity_guarantees_region_canStore
    (p : Perm) (w : Word) (P : D)
    (ρ : region_type) :
    canStore p w = true
    -> monotonicity_guarantees_regionFull ρ p (safeC P)
      -∗ monotonicity_guarantees_region ρ w p (safeC P).
  Proof.
    iIntros (HcanStore) "Hmono".
    destruct ρ; auto; cbn; [destruct (pwl p)|].
    all: iApply "Hmono"; auto.
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


End logrel.
