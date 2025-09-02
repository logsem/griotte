From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export cap_lang region seal_store region_invariants.
From iris.algebra Require Export gmap agree auth excl_auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine.rules Require Import rules_base.
From cap_machine Require Export switcher.
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

Definition tframeR := excl_authR (leibnizO (list (Word * Word))).
Definition tframeUR := excl_authUR (leibnizO (list (Word * Word))).

Class TFRAME_preG Σ :=
  { tframe_preG :: inG Σ tframeUR; }.

Class TFRAMEG Σ :=
  { tframe_inG :: inG Σ tframeUR;
    γtframe : gname;
  }.

Definition TFRAME_preΣ :=
  #[ GFunctor tframeUR ].

Instance subG_TFRAME_preΣ {Σ} :
  subG TFRAME_preΣ Σ → TFRAME_preG Σ.
Proof. solve_inG. Qed.

Section TStack.
  Context {Σ : gFunctors} {tframeg : TFRAMEG Σ} .

  Definition tframe_full (a : list (Word * Word)) : iProp Σ
    := own γtframe (●E (a : leibnizO (list (Word * Word))) : tframeUR).

  Definition tframe_frag (a : list (Word * Word)) : iProp Σ
    := own γtframe (◯E (a : leibnizO (list (Word * Word))) : tframeUR).

  Lemma tframe_agree a a' :
   tframe_full a -∗
   tframe_frag a' -∗
   ⌜ a = a' ⌝.
  Proof.
    iIntros "Hfull Hfrag".
    rewrite /tframe_full /tframe_frag.
    iCombine "Hfull Hfrag" as "H".
    iDestruct (own_valid with "H") as "%H".
    by apply excl_auth_agree_L in H.
  Qed.

  Lemma tframe_update a a' a'' :
   tframe_full a -∗
   tframe_frag a' ==∗
   tframe_full a'' ∗ tframe_frag a''.
  Proof.
    iIntros "Hfull Hfrag".
    rewrite /tframe_full /tframe_frag.
    iCombine "Hfull Hfrag" as "H".
    iMod ( own_update _ _ _  with "H" ) as "H".
    { apply excl_auth_update. }
    iDestruct "H" as "[? ?]".
    by iFrame.
  Qed.

End TStack.

Section pre_TFRAME.
  Context {Σ : gFunctors} {tframeg : TFRAME_preG Σ}.

  Lemma gen_tframe_init stk :
    ⊢ |==> (∃ (tframeg : TFRAMEG Σ), tframe_full stk ∗ tframe_frag stk).
  Proof.
    iMod (own_alloc (A:=tframeUR) (●E (stk : leibnizO _) ⋅ ◯E (stk : leibnizO _) )) as (γtframe) "Htframe"
    ; first by apply excl_auth_valid.
    iModIntro. iExists (Build_TFRAMEG _ _ γtframe).
    by rewrite own_op.
  Qed.

End pre_TFRAME.

(** interp : is a unary logical relation. *)
Section logrel.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {tframeg : TFRAMEG Σ}
    `{MP: MachineParameters}
    `{swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation STK := (leibnizO (list (Word * Word))).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (STK -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  (* -------------------------------------------------------------------------------- *)

  (* Future world relation *)
  Definition future_world (g : Locality) (W W' : WORLD) : iProp Σ :=
    (match g with
     | Local => ⌜related_sts_pub_world W W'⌝
     | Global => ⌜related_sts_priv_world W W'⌝
     end)%I.

  Lemma localityflowsto_futureworld (g g' : Locality) (W W' : WORLD):
    LocalityFlowsTo g' g ->
    (@future_world g' W W' -∗
     @future_world g  W W').
  Proof.
    intros Hflows.
    destruct g, g'; auto.
    rewrite /future_world; iIntros "%".
    iPureIntro. eapply related_sts_pub_priv_world; auto.
  Qed.

  Lemma futureworld_refl (g : Locality) (W : WORLD) :
    ⊢ @future_world g W W.
  Proof.
    rewrite /future_world.
    destruct g; iPureIntro
    ; [apply related_sts_priv_refl_world
      | apply related_sts_pub_refl_world].
  Qed.

  Global Instance future_world_persistent (g : Locality) (W W' : WORLD) :
    Persistent (future_world g W W').
  Proof.
    unfold future_world. destruct g; apply bi.pure_persistent.
  Qed.


  (* interp expression definitions *)
  Definition registers_pointsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition SP : RegName := r_t31.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Program Definition interp_reg (interp : V) : R :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO Reg),
      (full_map reg ∧
       ∀ (r : RegName) (v : Word), (⌜r ≠ PC⌝ → ⌜reg !! r = Some v⌝ → interp W C v))%I.
  Solve All Obligations with solve_proper.

  (* Definition interp_conf (W : WORLD) (C : CmptName) : iProp Σ := *)
  (*   (WP Seq (Instr Executable) *)
  (*      {{ v, ⌜v = HaltedV⌝ → *)
  (*            ∃ regs W', ∃ WC WC', *)
  (*           ⌜W !! C = Some WC⌝ ∧ ⌜W' !! C = Some WC'⌝ *)
  (*           ∧ full_map regs ∧ registers_pointsto regs *)
  (*           ∗ ⌜related_sts_priv_world WC WC'⌝ *)
  (*           ∗ na_own logrel_nais ⊤ *)
  (*           ∗ sts_full_world WC' *)
  (*           ∗ region W' C}} *)
  (*   )%I. *)
  Definition interp_conf (W : WORLD) (C : CmptName) : iProp Σ :=
    (WP Seq (Instr Executable)
       {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.

  Program Definition interp_expr (interp : V) (interp_cont : K) : E :=
    (λne (stk : STK) (W : WORLD) (C : CmptName) (wpc : Word) (wstk : Word),
       ∀ regs,
       ( interp_reg interp W C regs
        ∗ registers_pointsto (<[PC:=wpc]> (<[csp:=wstk]> regs))
        ∗ region W C
        ∗ sts_full_world W C
        ∗ interp_cont W C
        ∗ na_own logrel_nais ⊤
        ∗ tframe_frag stk
          -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  Global Instance interp_expr_ne n :
    Proper (dist n ==> dist n ==> dist n) (interp_expr).
  Proof.
    intros interp interp0 Heq K K0 HK.
    rewrite /interp_expr. intros ?????. simpl.
    do 10 f_equiv;[|apply HK].
    by repeat f_equiv.
  Qed.

  Program Fixpoint interp_cont (interp : V) (stk : STK) : K :=
    match stk with
    | [] => λne (W : WORLD) (C : leibnizO CmptName), True%I
    | (wret,wstk) :: stk' =>
        λne (W : WORLD) (C : leibnizO CmptName),
        (interp_cont interp stk' W C ∗
          (∀ W', ⌜related_sts_pub_world W W'⌝ -∗ ▷ interp_expr interp (interp_cont interp stk') stk' W' C wret wstk))%I
    end.
  Solve All Obligations with solve_proper.

  Global Instance interp_continuation_ne (* (interp : V) stk *) n :
    Proper (dist n ==> (=) ==> dist n ==> dist n) (interp_cont).
  Proof.
    intros interp interp0 Heq x y -> W W0 ->.
    generalize dependent W0. clear W.
    induction y;intros W0;[simpl;f_equiv|].
    destruct a. simpl. intros ?. simpl.
    f_equiv;[apply IHy|].
    do 13 f_equiv;[repeat f_equiv;auto|].
    intros ?. apply IHy.
  Qed.
  (* Global Instance interp_cont_contractive (interp : V) stk : *)
    (* Contractive (λ interp_cont', (interp_cont stk interp) interp_cont'). *)
  (* Proof. *)
  (*   solve_proper_prepare. *)
  (*   destruct p. *)
  (*   destruct p. *)
  (*   solve_contractive. *)
  (* Qed. *)

  (* Lemma fixpoint_interp_continuation_eq (interp : V) (stk : STK) (W : WORLD) (C : CmptName) (w : leibnizO Word) : *)
  (*   fixpoint (interp_continuation interp) stk W C ≡ interp_continuation interp (fixpoint (interp_continuation interp)) stk W C. *)
  (* Proof. exact: (fixpoint_unfold (interp_continuation interp) stk W C). Qed. *)

  (* Definition interp_cont (interp : V) := fixpoint (interp_continuation interp). *)
  (* Definition interp_expr (interp : V) := interp_expr' interp (interp_cont interp). *)

  (* Condition definitions *)
  Definition zcond (P : V) (C : CmptName) : iProp Σ :=
    (□ ∀ (W1 W2: WORLD) (z : Z), P W1 C (WInt z) -∗ P W2 C (WInt z)).
  Global Instance zcond_ne n :
    Proper ((=) ==> (=) ==> dist n) zcond.
  Proof. solve_proper_prepare.
         repeat f_equiv;auto. Qed.
  Global Instance zcond_contractive (P : V) (C : CmptName) :
    Contractive (λ interp, ▷ zcond P C)%I.
  Proof. solve_contractive. Qed.

  Definition rcond (P : V) (C : CmptName) (p : Perm) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word), P W C w -∗ interp W C (load_word p w)).
  Global Instance rcond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) rcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance rcond_contractive (P : V) (C : CmptName) (p : Perm) :
    Contractive (λ interp, ▷ rcond P C p interp)%I.
  Proof. solve_contractive. Qed.

  Definition wcond (P : V) (C : CmptName) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word), interp W C w -∗ P W C w).
  Global Instance wcond_ne n :
    Proper ((=) ==> (=)  ==> dist n ==> dist n) wcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance wcond_contractive (P : V) (C : CmptName) :
    Contractive (λ interp, ▷ wcond P C interp)%I.
  Proof. solve_contractive. Qed.


  (* Definition exec_cond *)
  (*   (stk : STK) *)
  (*   (W : WORLD) (C : CmptName) *)
  (*   (p : Perm) (g : Locality) (b e : Addr) *)
  (*   (interp : D) : iProp Σ := *)
  (*   (∀ a regs W', ⌜a ∈ₐ [[ b , e ]]⌝ *)
  (*              → future_world g W W' *)
  (*              → ▷ interp_expr interp regs stk W' C (WCap p g b e a))%I. *)
  (* Global Instance exec_cond_ne n : *)
  (*   Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond. *)
  (* Proof. unfold exec_cond. solve_proper. Qed. *)
  (* Global Instance exec_cond_contractive W C b e g p : *)
  (*   Contractive (λ interp, exec_cond W C b e g p interp). *)
  (* Proof. solve_contractive. Qed. *)

  Definition enter_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr)
    (interp : V) : iProp Σ :=
    (∀ stk wstk W', future_world g W W' →
             (▷ interp_expr interp (interp_cont interp stk) stk W' C (WCap p g b e a) wstk)
               ∗ (▷ interp_expr interp (interp_cont interp stk) stk W' C (WCap p Local b e a) wstk)
    )%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof.
    solve_proper_prepare.
    do 17 f_equiv;[by repeat f_equiv| |by repeat f_equiv|..].
    1,2: by apply interp_continuation_ne.
  Qed.

  Global Instance enter_cond_contractive W C p g b e a :
    Contractive (λ interp, enter_cond W C p g b e a interp).
  Proof.
    intros ????. rewrite /enter_cond.
    do 8 f_equiv.
    apply later_contractive.
    { inversion H. constructor. intros.
      apply dist_later_lt in H0.
      apply interp_expr_ne;auto. intros ?.
      apply interp_continuation_ne;auto. }
    apply later_contractive.
    inversion H. constructor. intros.
    apply dist_later_lt in H0.
    apply interp_expr_ne;auto. intros ?.
    apply interp_continuation_ne;auto.
  Qed.

  Definition persistent_cond (P:V) := (∀ WCv, Persistent (P WCv.1.1 WCv.1.2  WCv.2)).

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

  Definition region_state_pwl (W : WORLD) (a : Addr) : Prop :=
    (std W) !! a = Some Temporary.

  Definition region_state_nwl (W : WORLD) (a : Addr) (l : Locality) : Prop :=
    match l with
     | Local => (std W) !! a = Some Permanent ∨ (std W) !! a = Some Temporary
     | Global => (std W) !! a = Some Permanent
    end.

  (* For simplicity we might want to have the following statement in valididy of caps.
     However, it is strictly not necessary since it can be derived form full_sts_world *)

  Definition safeC (P : V) :=
    (λ WCv : WORLD * CmptName * (leibnizO Word), P WCv.1.1 WCv.1.2 WCv.2).

  Definition monoReq (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (P : V) :=
    (match (std W) !! a with
        | Some Temporary =>
            (if isWL p
             then mono_pub C (safeC P)
             else (if isDL p then mono_borrow C (safeC P) p else mono_priv C (safeC P) p))
        | Some Permanent => mono_priv C (safeC P) p
        | _ => True
        end)%I.

  Definition interp_z : V := λne _ _ w, ⌜match w with WInt z => True | _ => False end⌝%I.
  Definition interp_cap_O : V := λne _ _ _, True%I.

  Program Definition interp_sentry (interp : V) : V :=
    λne W C w, (match w with
                | WSentry p g b e a =>
                    if is_switcher_entry_point b e a
                    then True
                    else (□ enter_cond W C p g b e a interp)
                | _ => False
                end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap (interp : V) : V :=
    λne W C w, (match w with
              | WCap (O _ _) _ _ _ _
              | WCap (BPerm XSR _ _ _) _ _ _ _ (* XRS capabilities are never safe-to-share *)
              | WCap (BPerm _ WL _ _) Global _ _ _ (* WL Global capabilities are never safe-to-share *)
                => False
              | WCap p g b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:V),
                      ⌜PermFlowsTo p p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel C a p' (safeC P)
                      ∧ ▷ zcond P C
                      ∧ (if readAllowed p' then ▷ rcond P C p' interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P C interp else True)
                      ∧ monoReq W C a p' P
                      ∧ ⌜ if isWL p then region_state_pwl W a else region_state_nwl W a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with auto;solve_proper.

  (* (un)seal permission definitions *)
  (* Note the asymmetry: to seal values, we need to know that we are using a persistent predicate to create a value, whereas we do not need this information when unsealing values (it is provided by the `interp_sb` case). *)
  Definition safe_to_seal (W : WORLD) (C : CmptName) (interp : V) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : V, ⌜persistent_cond P⌝
                ∗ (∀ w, future_priv_mono C (safeC P) w)
                ∗ (seal_pred a (safeC P))
                ∗ ▷ wcond P C interp)%I.
  Definition safe_to_unseal (W : WORLD) (C : CmptName) (interp : V) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : V, (∀ w, future_priv_mono C (safeC P) w)
                ∗ (seal_pred a (safeC P))
                ∗ ▷ rcond P C RO interp)%I.

  Program Definition interp_sr (interp : V) : V :=
    λne W C w, (match w with
    | WSealRange p g b e a =>
    (if permit_seal p then safe_to_seal W C interp b e else True)
    ∗ (if permit_unseal p then safe_to_unseal W C interp b e else True)
    | _ => False end ) %I.
  Solve All Obligations with solve_proper.

  Program Definition interp_sb (W : WORLD) (C : CmptName) (o : OType) (w : Word) :=
    (∃ (P : V) ,
        ⌜persistent_cond P⌝
        ∗ (∀ w, future_priv_mono C (safeC P) w)
        ∗ seal_pred o (safeC P)
        ∗ ▷ P W C w
        ∗ ▷ P W C (borrow w)
    )%I.

  Definition interp_False : V := λne _ _ _, False%I.

  Program Definition interp1 (interp : V) : V :=
    (λne W C w,
    match w return _ with
    | WInt _ => interp_z W C w
    | WCap (O _ _) g b e a => interp_cap_O W C w
    | WCap _ g b e a => interp_cap interp W C w
    | WSentry p g b e a => interp_sentry interp W C w
    | WSealRange p g b e a => interp_sr interp W C w
    | WSealed o sb => interp_sb W C o (WSealable sb)
    end)%I.
  Solve All Obligations with solve_proper.

  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.

  Global Instance interp_sentry_contractive :
    Contractive (interp_sentry).
  Proof.
    solve_proper_prepare.
    destruct_word x2; auto.
    destruct sd ; auto.
    destruct rx,w,g; auto.
    all: solve_contractive.
  Qed.

  Global Instance interp_cap_contractive :
    Contractive (interp_cap).
  Proof.
    (* solve_proper_prepare. *)
    (* destruct_word x2; auto. *)
    (* destruct c ; auto. *)
    (* destruct rx,w,g; auto. *)
    (* par: solve_contractive. (* TODO how can I set -async-proofs-tac-j *) *)
  Admitted. (* TODO holds, but very loooong *)

  Global Instance interp_sr_contractive :
    Contractive (interp_sr).
  Proof.
    solve_proper_prepare.
    destruct_word x2; auto.
    destruct (permit_seal sr), (permit_unseal sr);
    rewrite /safe_to_seal /safe_to_unseal;
    solve_contractive.
  Qed.

  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    (* intros n x y Hdistn W C w. *)
    (* rewrite /interp1. *)
    (* destruct_word w; [auto|..]. *)
    (* + destruct c; first auto. *)
    (*   destruct rx,w,dl,dro. *)
    (*   par: try (by apply interp_cap_O_contractive). *)
    (*   par: by apply interp_cap_contractive. *)
    (* + by apply interp_sr_contractive. *)
    (* + by apply interp_sentry_contractive. *)
    (* + rewrite /interp_sb; solve_contractive. *)
  Admitted. (* TODO holds, but very loooong *)

  Lemma fixpoint_interp1_eq (W : WORLD) (C : CmptName) (w : leibnizO Word) :
    fixpoint (interp1) W C w ≡ interp1 (fixpoint (interp1)) W C w.
  Proof. exact: (fixpoint_unfold (interp1) W C w). Qed.

  Program Definition interp : V := (fixpoint (interp1)).
  Solve All Obligations with solve_proper.
  Definition interp_continuation (stk : STK) : K := interp_cont interp stk.
  Definition interp_expression : E :=
    λne stk, interp_expr interp (interp_continuation stk) stk.
  Definition interp_registers : R := interp_reg interp.

  Lemma interp_continuation_eq (stk : STK) (W : WORLD) (C : CmptName) (w : leibnizO Word) :
    interp_continuation stk W C ≡ interp_cont (fixpoint interp1) stk W C.
  Proof.
    rewrite /interp_continuation /interp /= //.
  Qed.

  Global Instance interp_persistent W C w : Persistent (interp W C w).
  Proof.
    intros. destruct_word w; simpl; rewrite fixpoint_interp1_eq; simpl.
    - apply _.
    - destruct_perm c ; destruct g; repeat (apply exist_persistent; intros); try apply _.
    - destruct (permit_seal sr), (permit_unseal sr); rewrite /safe_to_seal /safe_to_unseal; apply _ .
    - apply _.
    - apply exist_persistent; intros P.
      unfold Persistent. iIntros "(%Hpers & #Hmono & #Hs & HP & HPborrowed)".
      (* use knowledge about persistence *)
      iAssert (<pers> ▷ P W C (WSealable sb))%I with "[ HP ]" as "HP".
      { iApply later_persistently_1.
        ospecialize (Hpers (W,C,_)); cbn in Hpers.
        by iApply persistent_persistently_2.
      }
      iAssert (<pers> ▷ P W C (borrow (WSealable sb)))%I with "[ HPborrowed ]" as "HPborrowed".
      { iApply later_persistently_1.
        ospecialize (Hpers (W,C,_)); cbn in Hpers.
        by iApply persistent_persistently_2.
      }
      iApply persistently_sep_2; iSplitR; auto.
      iApply persistently_sep_2; iSplitR; auto; iFrame "Hs".
      iApply persistently_sep_2;iFrame.
  Qed.

  (* Non-curried version of interp *)
  Definition interpC := safeC interp.

  Lemma interp1_eq interp (W: WORLD) (C : CmptName) p g b e a:
    ((interp1 interp W C (WCap p g b e a)) ≡
       (if (isO p)
        then True
        else
          if (has_sreg_access p)
          then False
          else ([∗ list] a ∈ finz.seq_between b e,
                  ∃ (p' : Perm) (P:V),
                    ⌜PermFlowsTo p p'⌝
                    ∗ ⌜persistent_cond P⌝
                    ∗ rel C a p' (safeC P)
                    ∗ ▷ zcond P C
                    ∗ (if readAllowed p' then ▷ (rcond P C p' interp) else True)
                    ∗ (if writeAllowed p' then ▷ (wcond P C interp) else True)
                    ∗ monoReq W C a p' P
                    ∗ ⌜ if isWL p then region_state_pwl W a else region_state_nwl W a g⌝)
               ∗ (⌜ if isWL p then g = Local else True⌝))%I).
  Proof.
    (* iSplit. *)
    (* { iIntros "HA". *)
    (*   destruct (isO p) eqn:HnotO; subst; auto. *)
    (*   destruct p; cbn. *)
    (*   destruct rx ; destruct w ; try (cbn in HnotO ; congruence); auto. *)
    (*   all: destruct g ;auto ; try (iSplit;eauto). *)
    (*   all: try (iApply (big_sepL_mono with "HA"); intros k a' ?; iIntros "H"). *)
    (*   all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a')"). *)
    (*   all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)). *)
    (* } *)
    (* { iIntros "A". *)
    (*   destruct (isO p) eqn:HnotO; subst; auto. *)
    (*   { destruct_perm p ; cbn in *;auto;try congruence. } *)
    (*   destruct (has_sreg_access p) eqn:HnotXSR; subst; auto. *)
    (*   iDestruct "A" as "(A & %)". *)
    (*   destruct_perm p; cbn in HnotO,HnotXSR; try congruence; auto. *)
    (*   all: destruct g eqn:Hg; simplify_eq ; eauto ; cbn. *)
    (*   all: try (iApply (big_sepL_mono with "A"); intros; iIntros "H"). *)
    (*   all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a')"). *)
    (*   all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)). *)
    (* } *)
  Admitted. (* TODO holds, but very long to compile *)


  (* Inversion lemmas about interp  *)
  Lemma read_allowed_inv (W : WORLD) (C : CmptName) (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp W C (WCap p g b e a)) →
    ∃ (p' : Perm) (P:V),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ rel C a' p' (safeC P)
      ∗ ▷ zcond P C
      ∗ ▷ rcond P C p' interp
      ∗ (if writeAllowed p' then (▷ wcond P C interp) else True)
      ∗ monoReq W C a' p' P
  .
  Proof.
    iIntros (Hin Ra) "Hinterp".
    apply Is_true_eq_true in Ra.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply readAllowed_nonO in Ra ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & _)";eauto.
    pose proof (readAllowed_flowsto _ _ Hfl' Ra) as Ra'.
    rewrite Ra'.
    iExists p',P'; iFrame "#∗%"; try done.
  Qed.


  Lemma write_allowed_inv (W : WORLD) (C : CmptName) (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    writeAllowed p →
    ⊢ (interp W C (WCap p g b e a)) →
    ∃ (p' : Perm) (P:V),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ rel C a' p' (safeC P)
      ∗ ▷ zcond P C
      ∗ ▷ wcond P C interp
      ∗ (if readAllowed p' then (▷ rcond P C p' interp) else True)
      ∗ monoReq W C a' p' P
  .
  Proof.
    iIntros (Hin Ra) "Hinterp".
    apply Is_true_eq_true in Ra.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply writeAllowed_nonO in Ra ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & _)";eauto.
    pose proof (writeAllowed_flowsto _ _ Hfl' Ra) as Ra'.
    rewrite Ra'.
    iExists p',P'; iFrame "#∗%"; try done.
  Qed.

  Lemma readAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a:
    readAllowed p = true ->
    withinBounds b e a = true ->
    interp W C (WCap p g b e a) -∗
    ⌜∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked⌝.
  Proof.
    intros Hra Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply readAllowed_nonO in Hra ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    iPureIntro.
    destruct (isWL p); simplify_eq.
    + naive_solver.
    + destruct g; naive_solver.
  Qed.

  Lemma writeAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a:
    writeAllowed p = true ->
    withinBounds b e a = true ->
    interp W C (WCap p g b e a) -∗
    ⌜∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked⌝.
  Proof.
    intros Hra Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply writeAllowed_nonO in Hra ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    iPureIntro.
    destruct (isWL p); simplify_eq.
    + naive_solver.
    + destruct g; naive_solver.
  Qed.

  Lemma writeLocalAllowed_implies_local (W : WORLD) (C : CmptName) p g b e a:
    isWL p = true ->
    interp W C (WCap p g b e a) -∗ ⌜ isLocal g = true ⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct_perm p; simpl in H; try congruence; destruct g; auto.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a:
    isWL p = true ->
    withinBounds b e a = true ->
    interp W C (WCap p g b e a) -∗
    ⌜std W !! a = Some Temporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply isWL_nonO in Hp ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    by rewrite Hp in Hstate.
  Qed.

  Lemma interp_in_registers
    (W : WORLD) (C : CmptName)
    (regs : leibnizO Reg) (p : Perm) (g : Locality) (b e a : Addr):
      (∀ (r : RegName) (v : Word), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)%I
    -∗ (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel C a p' (safeC P)
        ∗ ▷ zcond P C
        ∗ (if readAllowed p' then ▷ rcond P C p' interp else True)
        ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
        ∗ monoReq W C a p' P
        ∗ ⌜if isWL p then region_state_pwl W a else region_state_nwl W a g⌝
       )
    -∗ (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel C a p' (safeC P)
        ∗ ▷ zcond P C
        ∗ (if decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a)
            then ▷ (rcond P C p' interp)
            else emp)
        ∗ (if decide (writeAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a)
            then ▷ wcond P C interp
            else emp)
        ∗ monoReq W C a p' P
        ∗ ⌜if isWL p then region_state_pwl W a else region_state_nwl W a g⌝
       ).
  Proof.
    iIntros "#Hreg #H".
    iDestruct "H" as (p0 P0 Hflp0 Hperscond_P0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0 & HmonoR0 & %Hstate0)".
    iExists p0,P0.
    iFrame "%#".
    iSplit.
    - (* rcond *)
      destruct (decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a))
        as [Hra'|Hra']; auto.
      destruct (readAllowed p0) eqn:Hra; auto.
      destruct Hra' as (r & w & Hsome & Hrar & Hvw).
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert in Hsome; simplify_eq.
        eapply readAllowed_flowsto in Hrar; eauto.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      iDestruct ("Hreg" $! r w n Hsome) as "Hinterp_w".
      destruct_word w; cbn in * ; try done.
      destruct Hvw as [Hvw ->].
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_w".
      replace (isO c) with false.
      2: { eapply readAllowed_nonO in Hrar ;done. }
      destruct (has_sreg_access c) eqn:HnXSR; auto.
      iDestruct "Hinterp_w" as "[Hinterp_w %Hc_cond ]".
      iDestruct (extract_from_region_inv with "Hinterp_w")
        as (p1 P1 Hflc1 Hperscond_P1) "(Hrel1 & Hzcond1 & Hrcond1 & Hwcond1 & HmonoR1 & %Hstate1)"
      ; eauto; iClear "Hinterp_w".
      apply readAllowed_flowsto in Hflc1; auto.
      iDestruct (rel_agree C a0 _ _ p0 p1 with "[$Hrel0 $Hrel1]") as "(-> & Heq)".
      congruence.
    - (* wcond *)
      destruct (decide (writeAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a))
        as [Hwa'|Hwa']; auto.
      destruct (writeAllowed p0) eqn:Hwa; auto.
      destruct Hwa' as (r & w & Hsome & Hwaw & Hvw).
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert in Hsome; simplify_eq.
        eapply writeAllowed_flowsto in Hwaw; eauto.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      iDestruct ("Hreg" $! r w n Hsome) as "Hinterp_w".
      destruct_word w; cbn in * ; try done.
      destruct Hvw as [Hvw ->].
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_w".
      replace (isO c) with false.
      2: { eapply writeAllowed_nonO in Hwaw ;done. }
      destruct (has_sreg_access c) eqn:HnXSR; auto.
      iDestruct "Hinterp_w" as "[Hinterp_w %Hc_cond ]".
      iDestruct (extract_from_region_inv with "Hinterp_w")
        as (p1 P1 Hflc1 Hperscond_P1) "(Hrel1 & Hzcond1 & Hrcond1 & Hwcond1 & HmonoR1 & %Hstate1)"
      ; eauto; iClear "Hinterp_w".
      apply writeAllowed_flowsto in Hflc1; auto.
      iDestruct (rel_agree C a0 _ _ p0 p1 with "[$Hrel0 $Hrel1]") as "(-> & Heq)".
      congruence.
  Qed.

  Lemma writeAllowed_valid_cap (W : WORLD) (C : CmptName) p g b e a':
    writeAllowed p = true ->
    interp W C (WCap p g b e a') -∗
    ⌜Forall (fun a => ∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked) (finz.seq_between b e)⌝.
  Proof.
    iIntros (Hwa) "Hinterp".
    rewrite Forall_forall.
    iIntros (a Ha).
    apply elem_of_finz_seq_between in Ha.
    rewrite /interp; cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply writeAllowed_nonO in Hwa ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    iPureIntro.
    destruct (isWL p); simplify_eq.
    + naive_solver.
    + destruct g; naive_solver.
  Qed.

End logrel.
