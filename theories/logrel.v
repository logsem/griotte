From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export cap_lang region seal_store region_invariants.
From iris.algebra Require Export gmap agree auth.
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
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).
  Implicit Types WC : CVIEW.
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* -------------------------------------------------------------------------------- *)

  (* Future world relation *)
  Definition future_world (g : Locality) (W W' : WORLD) (C : CmptName) : iProp Σ :=
    (match g with
     | Local => ⌜related_sts_pub_world W W' C⌝
     | Global => ⌜related_sts_priv_world W W' C⌝
     end)%I.

  Lemma localityflowsto_futureworld (g g' : Locality) (W W' : WORLD) (C : CmptName):
    LocalityFlowsTo g' g ->
    (@future_world g' W W' C -∗
     @future_world g  W W' C).
  Proof.
    intros Hflows.
    destruct g, g'; auto.
    rewrite /future_world; iIntros "%".
    iPureIntro. eapply related_sts_pub_priv_world; auto.
  Qed.

  Lemma futureworld_refl (g : Locality) (W : WORLD) (C : CmptName) :
    ⊢ @future_world g W W C.
  Proof.
    rewrite /future_world.
    destruct g; iPureIntro
    ; [apply related_sts_priv_refl_world
      | apply related_sts_pub_refl_world].
  Qed.

  Global Instance future_world_persistent (g : Locality) (W W' : WORLD) (C : CmptName) :
    Persistent (future_world g W W' C).
  Proof.
    unfold future_world. destruct g; apply bi.pure_persistent.
  Qed.


  (* interp expression definitions *)
  Definition registers_pointsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Program Definition interp_reg (interp : D) : R :=
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

  Program Definition interp_expr (interp : D) (regs : Reg) : D :=
    (λne (W : WORLD) (C : CmptName) (w : Word),
       ( interp_reg interp W C regs
        ∗ registers_pointsto (<[PC:=w]> regs)
        ∗ region W C
        ∗ sts_full_world W C
        ∗ na_own logrel_nais ⊤
          -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  (* Condition definitions *)
  Definition zcond (P : D) (C : CmptName) : iProp Σ :=
    (□ ∀ (W1 W2: WORLD) (z : Z), P W1 C (WInt z) -∗ P W2 C (WInt z)).
  Global Instance zcond_ne n :
    Proper ((=) ==> (=) ==> dist n) zcond.
  Proof. solve_proper_prepare.
         repeat f_equiv;auto. Qed.
  Global Instance zcond_contractive (P : D) (C : CmptName) :
    Contractive (λ interp, ▷ zcond P C)%I.
  Proof. solve_contractive. Qed.

  Definition rcond (P : D) (C : CmptName) (p : Perm) (interp : D) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word), P W C w -∗ interp W C (load_word p w)).
  Global Instance rcond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) rcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance rcond_contractive (P : D) (C : CmptName) (p : Perm) :
    Contractive (λ interp, ▷ rcond P C p interp)%I.
  Proof. solve_contractive. Qed.

  Definition wcond (P : D) (C : CmptName) (interp : D) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word), interp W C w -∗ P W C w).
  Global Instance wcond_ne n :
    Proper ((=) ==> (=)  ==> dist n ==> dist n) wcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance wcond_contractive (P : D) (C : CmptName) :
    Contractive (λ interp, ▷ wcond P C interp)%I.
  Proof. solve_contractive. Qed.


  Definition exec_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e : Addr)
    (interp : D) : iProp Σ :=
    (∀ a regs W', ⌜a ∈ₐ [[ b , e ]]⌝
               → future_world g W W' C
               → ▷ interp_expr interp regs W' C (WCap p g b e a))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof. unfold exec_cond. solve_proper. Qed.
  Global Instance exec_cond_contractive W C b e g p :
    Contractive (λ interp, exec_cond W C b e g p interp).
  Proof. solve_contractive. Qed.

  Definition enter_cond (W : WORLD) (C : CmptName) (p : Perm) (g : Locality) (b e a : Addr) (interp : D) : iProp Σ :=
    (∀ r W', future_world g W W' C →
             (▷ interp_expr interp r W' C (WCap p g b e a))
               ∗ (▷ interp_expr interp r W' C (WCap p Local b e a))
    )%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. unfold enter_cond. solve_proper. Qed.
  Global Instance enter_cond_contractive W C p g b e a :
    Contractive (λ interp, enter_cond W C p g b e a interp).
  Proof.
    solve_contractive.
  Qed.

  Definition persistent_cond (P:D) := (∀ WCv, Persistent (P WCv.1.1 WCv.1.2  WCv.2)).

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

  Definition region_state_pwl (W : WORLD) (C : CmptName) (a : Addr) : Prop :=
    (std W C) !! a = Some Temporary.

  Definition region_state_nwl (W : WORLD) (C : CmptName) (a : Addr) (l : Locality) : Prop :=
    match l with
     | Local => (std W C) !! a = Some Permanent ∨ (std W C) !! a = Some Temporary
     | Global => (std W C) !! a = Some Permanent
    end.

  (* For simplicity we might want to have the following statement in valididy of caps.
     However, it is strictly not necessary since it can be derived form full_sts_world *)

  Definition safeC (P : D) :=
    (λ WCv : WORLD * CmptName * (leibnizO Word), P WCv.1.1 WCv.1.2 WCv.2).

  Definition monoReq (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (P : D) :=
    (match (std W C) !! a with
        | Some Temporary =>
            (if isWL p
             then mono_pub C (safeC P)
             else mono_priv C (safeC P) p)
        | Some Permanent => mono_priv C (safeC P) p
        | _ => True
        end)%I.

  Definition interp_z : D := λne _ _ w, ⌜match w with WInt z => True | _ => False end⌝%I.
  Definition interp_cap_O : D := λne _ _ _, True%I.

  Program Definition interp_cap_E (interp : D) : D :=
    λne W C w, (match w with
                | WCap (E rx pw dl dro) g b e a =>
                    (□ enter_cond W C (BPerm rx pw dl dro) g b e a interp)
                | _ => False
                end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap (interp : D) : D :=
    λne W C w, (match w with
              | WCap (E _ _ _ _) _ _ _ _
              | WCap (O _ _) _ _ _ _
              | WCap (BPerm XSR _ _ _) _ _ _ _ (* XRS capabilities are never safe-to-share *)
              | WCap (BPerm _ WL _ _) Global _ _ _ (* WL Global capabilities are never safe-to-share *)
                => False
              | WCap p g b e a =>
                  [∗ list] a ∈ (finz.seq_between b e),
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo p p'⌝
                      ∧ ⌜persistent_cond P⌝
                      ∧ rel C a p' (safeC P)
                      ∧ ▷ zcond P C
                      ∧ (if readAllowed p' then ▷ rcond P C p' interp else True)
                      ∧ (if writeAllowed p' then ▷ wcond P C interp else True)
                      ∧ monoReq W C a p' P
                      ∧ ⌜ if isWL p then region_state_pwl W C a else region_state_nwl W C a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with auto;solve_proper.

  (* (un)seal permission definitions *)
  (* Note the asymmetry: to seal values, we need to know that we are using a persistent predicate to create a value, whereas we do not need this information when unsealing values (it is provided by the `interp_sb` case). *)
  Definition safe_to_seal (W : WORLD) (C : CmptName) (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : D, ⌜persistent_cond P⌝
                ∗ (∀ w, future_priv_mono C (safeC P) w)
                ∗ (seal_pred a (safeC P))
                ∗ ▷ wcond P C interp)%I.
  Definition safe_to_unseal (W : WORLD) (C : CmptName) (interp : D) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : D, (∀ w, future_priv_mono C (safeC P) w)
                ∗ (seal_pred a (safeC P))
                ∗ ▷ rcond P C RO interp)%I.

  Program Definition interp_sr (interp : D) : D :=
    λne W C w, (match w with
    | WSealRange p g b e a =>
    (if permit_seal p then safe_to_seal W C interp b e else True)
    ∗ (if permit_unseal p then safe_to_unseal W C interp b e else True)
    | _ => False end ) %I.
  Solve All Obligations with solve_proper.

  Program Definition interp_sb (W : WORLD) (C : CmptName) (o : OType) (w : Word) :=
    (∃ (P : D) ,
        ⌜persistent_cond P⌝
        ∗ (∀ w, future_priv_mono C (safeC P) w)
        ∗ seal_pred o (safeC P)
        ∗ ▷ P W C w
        ∗ ▷ P W C (borrow w)
    )%I.

  Definition interp_False : D := λne _ _ _, False%I.

  Program Definition interp1 (interp : D) : D :=
    (λne W C w,
    match w return _ with
    | WInt _ => interp_z W C w
    | WCap (O _ _) g b e a => interp_cap_O W C w
    | WCap (E _ _ _ _) g b e a => interp_cap_E interp W C w
    | WCap _ g b e a => interp_cap interp W C w
    | WSealRange p g b e a => interp_sr interp W C w
    | WSealed o sb => interp_sb W C o (WSealable sb)
    end)%I.
  Solve All Obligations with solve_proper.

  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.

  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    solve_proper_prepare.
    destruct_word x2; auto.
    destruct c ; auto.
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
   (*  intros n x y Hdistn W C w. *)
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

  Lemma fixpoint_interp1_eq (W : WORLD) (C : CmptName) (w : leibnizO Word) :
    fixpoint (interp1) W C w ≡ interp1 (fixpoint (interp1)) W C w.
  Proof. exact: (fixpoint_unfold (interp1) W C w). Qed.

  Program Definition interp : D := λne W C w, (fixpoint (interp1)) W C w.
  Solve All Obligations with solve_proper.
  Definition interp_expression (r : Reg) : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent W C w : Persistent (interp W C w).
  Proof.
    (* intros. destruct_word w; simpl; rewrite fixpoint_interp1_eq; simpl. *)
    (* - apply _. *)
    (* - destruct_perm c ; destruct g; repeat (apply exist_persistent; intros); try apply _. *)
    (* - destruct (permit_seal sr), (permit_unseal sr); rewrite /safe_to_seal /safe_to_unseal; apply _ . *)
    (* - apply exist_persistent; intros P. *)
    (*   unfold Persistent. iIntros "(%Hpers & #Hmono & #Hs & HP & HPborrowed)". *)
    (*   (* use knowledge about persistence *) *)
    (*   iAssert (<pers> ▷ P W C (WSealable sb))%I with "[ HP ]" as "HP". *)
    (*   { iApply later_persistently_1. *)
    (*     ospecialize (Hpers (W,C,_)); cbn in Hpers. *)
    (*     by iApply persistent_persistently_2. *)
    (*   } *)
    (*   iAssert (<pers> ▷ P W C (borrow (WSealable sb)))%I with "[ HPborrowed ]" as "HPborrowed". *)
    (*   { iApply later_persistently_1. *)
    (*     ospecialize (Hpers (W,C,_)); cbn in Hpers. *)
    (*     by iApply persistent_persistently_2. *)
    (*   } *)
    (*   iApply persistently_sep_2; iSplitR; auto. *)
    (*   iApply persistently_sep_2; iSplitR; auto; iFrame "Hs". *)
    (*   iApply persistently_sep_2;iFrame. *)
  Admitted. (* TODO holds, but very loooong *)

  (* Non-curried version of interp *)
  Definition interpC := safeC interp.

  Lemma interp1_eq interp (W: WORLD) (C : CmptName) p g b e a:
    ((interp1 interp W C (WCap p g b e a)) ≡
       (if (isO p)
        then True
        else
          if (isSentry p)
          then ∃ rx pw dl dro,
              ⌜ p = (E rx pw dl dro)⌝
              ∗ □ enter_cond W C (BPerm rx pw dl dro) g b e a interp
          else
            if (has_sreg_access p)
            then False
            else ([∗ list] a ∈ finz.seq_between b e,
                    ∃ (p' : Perm) (P:D),
                      ⌜PermFlowsTo p p'⌝
                      ∗ ⌜persistent_cond P⌝
                      ∗ rel C a p' (safeC P)
                      ∗ ▷ zcond P C
                      ∗ (if readAllowed p' then ▷ (rcond P C p' interp) else True)
                      ∗ (if writeAllowed p' then ▷ (wcond P C interp) else True)
                      ∗ monoReq W C a p' P
                      ∗ ⌜ if isWL p then region_state_pwl W C a else region_state_nwl W C a g⌝)
                 ∗ (⌜ if isWL p then g = Local else True⌝))%I).
  Proof.
    (* iSplit. *)
    (* { iIntros "HA". *)
    (*   destruct (isO p) eqn:HnotO; subst; auto. *)
    (*   destruct (isSentry p) eqn:Hsentry. *)
    (*   { destruct p; cbn in Hsentry; [congruence| by iFrame]. } *)
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
    (*   destruct (isSentry p) eqn:Hsentry. *)
    (*   { destruct p; cbn in Hsentry; [congruence|]. *)
    (*     iDestruct "A" as (rx' pw' dl' dro') "[%Hpeq A]". *)
    (*     by inv Hpeq. *)
    (*   } *)
    (*   destruct (has_sreg_access p) eqn:HnotXSR; subst; auto. *)
    (*   iDestruct "A" as "(A & %)". *)
    (*   destruct_perm p; cbn in HnotO,Hsentry,HnotXSR; try congruence; auto ; clear Hsentry. *)
    (*   all: destruct g eqn:Hg; simplify_eq ; eauto ; cbn. *)
    (*   all: try (iApply (big_sepL_mono with "A"); intros; iIntros "H"). *)
    (*   all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a')"). *)
    (*   all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)). *)
    (*   all: try (iApply (big_sepL_mono with "A"); intros; iIntros "H"). *)
    (* } *)
  Admitted. (* TODO holds, but very long to compile *)


  (* Inversion lemmas about interp  *)
  Lemma read_allowed_inv (W : WORLD) (C : CmptName) (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp W C (WCap p g b e a)) →
    ∃ (p' : Perm) (P:D),
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
    replace (isSentry p) with false.
    2: { eapply readAllowed_nonSentry in Ra ;done. }
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
    ∃ (p' : Perm) (P:D),
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
    replace (isSentry p) with false.
    2: { eapply writeAllowed_nonSentry in Ra ;done. }
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
    ⌜∃ ρ, std W C !! a = Some ρ ∧ ρ <> Revoked ∧ (∀ m, ρ ≠ Frozen m)⌝.
  Proof.
    intros Hra Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply readAllowed_nonO in Hra ;done. }
    replace (isSentry p) with false.
    2: { eapply readAllowed_nonSentry in Hra ;done. }
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
    ⌜∃ ρ, std W C !! a = Some ρ ∧ ρ <> Revoked ∧ (∀ m, ρ ≠ Frozen m)⌝.
  Proof.
    intros Hra Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite /interp. cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply writeAllowed_nonO in Hra ;done. }
    replace (isSentry p) with false.
    2: { eapply writeAllowed_nonSentry in Hra ;done. }
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
    ⌜std W C !! a = Some Temporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hinterp".
    eapply withinBounds_le_addr in Hb.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply isWL_nonO in Hp ;done. }
    replace (isSentry p) with false.
    2: { eapply isWL_nonSentry in Hp ;done. }
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
    -∗ (∃ (p' : Perm) (P : D),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel C a p' (safeC P)
        ∗ ▷ zcond P C
        ∗ (if readAllowed p' then ▷ rcond P C p' interp else True)
        ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
        ∗ monoReq W C a p' P
        ∗ ⌜if isWL p then region_state_pwl W C a else region_state_nwl W C a g⌝
       )
    -∗ (∃ (p' : Perm) (P : D),
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
        ∗ ⌜if isWL p then region_state_pwl W C a else region_state_nwl W C a g⌝
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
      replace (isSentry c) with false.
      2: { eapply readAllowed_nonSentry in Hrar ;done. }
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
      replace (isSentry c) with false.
      2: { eapply writeAllowed_nonSentry in Hwaw ;done. }
      destruct (has_sreg_access c) eqn:HnXSR; auto.
      iDestruct "Hinterp_w" as "[Hinterp_w %Hc_cond ]".
      iDestruct (extract_from_region_inv with "Hinterp_w")
        as (p1 P1 Hflc1 Hperscond_P1) "(Hrel1 & Hzcond1 & Hrcond1 & Hwcond1 & HmonoR1 & %Hstate1)"
      ; eauto; iClear "Hinterp_w".
      apply writeAllowed_flowsto in Hflc1; auto.
      iDestruct (rel_agree C a0 _ _ p0 p1 with "[$Hrel0 $Hrel1]") as "(-> & Heq)".
      congruence.
  Qed.

End logrel.
