From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
(* From cap_machine.rules Require Export rules. *)
From cap_machine Require Export cap_lang region.
From cap_machine.binary_model Require Export region_invariants_binary.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
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
    logrel_na_invG :> na_invG Σ;
    logrel_nais : na_inv_pool_name;
  }.

(** interp : is a unary logical relation. *)
Section logrel.
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
  Implicit Types w : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types interp : (D).

  (* -------------------------------------------------------------------------------- *)

  (* interp expression definitions *)
  Definition spec_registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↣ᵣ w)%I.
  Definition full_map (regpair : Reg * Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (regpair.1 !! r) ∧ is_Some (regpair.2 !! r)⌝)%I.
  Definition registers_mapsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Program Definition interp_reg (interp : D) : R :=
   λne (W : WORLD) (regpair : prodO (leibnizO Reg) (leibnizO Reg)), (full_map regpair ∧
                                          ∀ (r : RegName), (⌜r ≠ PC⌝ → interp W (regpair.1 !r! r,regpair.2 !r! r)))%I.
  Solve All Obligations with solve_proper.

  Definition interp_conf W : iProp Σ :=
    (WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ →
             ∃ r W', ⤇ of_val HaltedV
                   ∗ full_map r
                   ∗ registers_mapsto r.1
                   ∗ spec_registers_mapsto r.2
                   ∗ ⌜related_sts_priv_world W W'⌝
                   ∗ na_own logrel_nais ⊤
                   ∗ sts_full_world W'
                   ∗ region W' }})%I.

  Program Definition interp_expr (interp : D) r : D :=
    (λne W w, (interp_reg interp W r ∗ registers_mapsto (<[PC:=w.1]> r.1)
                                     ∗ spec_registers_mapsto (<[PC:=w.2]> r.2)
                                     ∗ region W
                                     ∗ sts_full_world W
                                     ∗ na_own logrel_nais ⊤
                                     ∗ ⤇ Seq (Instr Executable) -∗
                                     ⌜match w with (inr _,inr _) => True | _ => False end⌝ ∧ interp_conf W))%I.
  Solve All Obligations with solve_proper.

  (* condition definitions *)
  Program Definition read_write_cond l (interp : D) : iProp Σ :=
    rel l (λne Wv, interp Wv.1 Wv.2).
  Next Obligation.
  Proof. solve_proper. Qed.
  Global Instance read_write_cond_ne n :
    Proper ((=) ==> dist n ==> dist n) read_write_cond.
  Proof.
    rewrite /read_write_cond rel_eq /rel. solve_proper_prepare.
    f_equiv =>γ. f_equiv.
    apply saved_anything_ne.
    solve_proper.
  Qed.

  Definition rcond (P interp : D) : iProp Σ :=
    (▷ □ ∀ (W: WORLD) (w : Word * Word), P W w -∗ interp W w)
  ∗ (▷ □ ∀ (W1 W2: WORLD) (z1 z2 : Z), P W1 (inl z1,inl z2) -∗ P W2 (inl z1,inl z2)).
  Definition wcond (P interp : D) : iProp Σ :=
    (▷ □ ∀ (W: WORLD) (w : Word * Word), interp W w -∗ P W w).
  Program Definition read_cond l (P : D) (interp : D) : iProp Σ :=
    rcond P interp ∗ rel l (λne Wv, P Wv.1 Wv.2).
  Next Obligation.
  Proof. solve_proper. Qed.
  Global Instance read_cond_ne n :
    Proper ((=) ==> dist n ==> dist n ==> dist n) read_cond.
  Proof.
    rewrite /read_cond /rcond rel_eq /rel. solve_proper_prepare.
    apply sep_ne.
    - repeat f_equiv;auto.
    - solve_proper_prepare.
      f_equiv =>γ. f_equiv.
      apply saved_anything_ne.
      solve_proper.
  Qed.

  Definition future_world g l W W' : iProp Σ :=
    (match g with
    (* | Local => ⌜related_sts_pub_plus_world W W'⌝ *)
    | Local | Global => ⌜related_sts_priv_world W W'⌝
    | Directed => ⌜related_sts_a_world W W' l⌝
     end)%I.

  Global Instance future_world_persistent g l W W': Persistent (future_world g l W W').
  Proof.
    unfold future_world. destruct g; apply bi.pure_persistent.
  Qed.

  Definition exec_cond W b e g p b' e' g' p'  (interp : D) : iProp Σ :=
    (∀ a r W', ⌜a ∈ₐ [[ b , e ]]⌝ → future_world g e W W' →
            ▷ interp_expr interp r W' ((inr ((p,g),b, e,a)),inr ((p',g'),b',e',a)))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof. unfold exec_cond. solve_proper. Qed.

  Definition enter_cond W b e a g b' e' a' g' (interp : D) : iProp Σ :=
    (∀ r W', future_world g e W W' →
        ▷ interp_expr interp r W' (inr ((RX,g),b,e,a),inr ((RX,g'),b',e',a')))%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof. unfold enter_cond. solve_proper. Qed.

  (* interp definitions *)
  Program Definition interp_z : D := λne _ w, ⌜match w with (inl z, inl z') => (z = z')%Z | _ => False end⌝%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_O : D := λne _ w, (match w with
            | (inr (O,g,b,e,a),inr (O,g',b',e',a')) => ⌜g = g' ∧ b = b' ∧ e = e' ∧ a = a'⌝
            | _ => False
            end)%I.
  Solve All Obligations with solve_proper.


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

  (* Definition region_state_pwl W (a : Addr) : Prop := *)
  (*   (std W) !! a = Some Temporary. *)

  Definition region_state_pwl_mono W (a : Addr) : Prop :=
    (std W) !! a = Some Monotemporary.

  Definition region_state_nwl W (a : Addr) (l : Locality) : Prop :=
    match l with
     | Local => (std W) !! a = Some Permanent
     | Global => (std W) !! a = Some Permanent
     | Directed => (std W) !! a = Some Monotemporary
                  ∨ (std W) !! a = Some Permanent
    end.

  Definition region_state_U W (a : Addr) : Prop :=
    (std W) !! a = Some Permanent.

  Definition region_state_U_mono W (a : Addr) : Prop :=
    (std W) !! a = Some Monotemporary
    \/ (std W) !! a = Some Permanent
    ∨ (exists w, (std W) !! a = Some (Uninitialized w)).

  (* Definition region_state_U_pwl W (a : Addr) : Prop := *)
  (*   (std W) !! a = Some Temporary *)
  (*   ∨ (exists w, (std W) !! a = Some (Static {[a:=w]})). *)

  Definition region_state_U_pwl_mono W (a : Addr) : Prop :=
    (std W) !! a = Some Monotemporary
    ∨ (exists w, (std W) !! a = Some (Uninitialized w)).


  (* For simplicity we might want to have the following statement in valididy of caps. However, it is strictly not
     necessary since it can be derived form full_sts_world *)
  (* Definition region_std W (a : Addr) : Prop := rel_is_std_i W (countable.encode a). *)

  Program Definition interp_cap_RO (interp : D) : D :=
    λne W w, (match w with
              | (inr ((RO,g),b,e,a),inr ((RO,g'),b',e',a')) =>
                ⌜g = g' ∧ b = b' ∧ e = e' ∧ a = a'⌝ ∗
                [∗ list] a ∈ (region_addrs b e), ∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∧ (read_cond a P interp) ∧ ⌜region_state_nwl W a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.


  Program Definition interp_cap_RW (interp : D) : D :=
    λne W w, (match w with
              | (inr ((RW,g),b,e,a), inr (RW,g',b',e',a')) =>
                ⌜g = g' ∧ b = b' ∧ e = e' ∧ a = a'⌝ ∗
                [∗ list] a ∈ (region_addrs b e), (read_write_cond a interp) ∧ ⌜region_state_nwl W a g⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWL (interp : D) : D :=
    λne W w, (match w with
              | (inr ((RWL,Directed),b,e,a), inr (RWL,Directed,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                [∗ list] a ∈ (region_addrs b e), (read_write_cond a interp) ∧ ⌜region_state_pwl_mono W a⌝
              (* | inr ((RWL,Local),b,e,a) => *)
              (*   [∗ list] a ∈ (region_addrs b e), ∃ p, ⌜PermFlows RWL p⌝ ∗ (read_write_cond a p interp) ∧ ⌜region_state_pwl W a⌝ *)
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp_cap_RX (interp : D) : D :=
    λne W w, (match w with
              | (inr ((RX,g),b,e,a), inr (RX,g',b',e',a')) =>
                ⌜g = g' ∧ b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a ∈ (region_addrs b e), ∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∧
                                                           (read_cond a P interp)
                                                  ∧ ⌜region_state_nwl W a g⌝)
             | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_E (interp : D) : D :=
    λne W w, (match w with
              | (inr ((E,g),b,e,a), inr (E,g',b',e',a')) => ⌜g = g' ∧ b = b' ∧ e = e' ∧ a = a'⌝
                                                           ∗ □ enter_cond W b e a g b' e' a' g' interp
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWX (interp : D) : D :=
    λne W w, (match w with
              | (inr ((RWX,g),b,e,a), inr (RWX,g',b',e',a')) =>
                ⌜g = g' ∧ b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a ∈ (region_addrs b e), (read_write_cond a interp)
                                                  ∧ ⌜region_state_nwl W a g⌝)
              | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_RWLX (interp : D) : D :=
    λne W w, (match w with
              | (inr ((RWLX,Directed),b,e,a),inr (RWLX,Directed,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a ∈ (region_addrs b e), (read_write_cond a interp)
                                                  ∧ ⌜region_state_pwl_mono W a⌝)
              (* | inr ((RWLX,Local),b,e,a) => *)
              (*   ([∗ list] a ∈ (region_addrs b e), ∃ p, ⌜PermFlows RWLX p⌝ ∗ (read_write_cond a p interp) *)
              (*                                          ∧ ⌜region_state_pwl W a⌝) *)
              | _ => False end)%I.
  Solve All Obligations with solve_proper.

  Program Definition interp_cap_URW (interp : D) : D :=
    λne W w, (match w with
              | (inr ((URW,Directed),b,e,a), inr (URW,Directed,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a' ∈ (region_addrs b (addr_reg.min a e)), (read_write_cond a' interp)
                                                                    ∧ ⌜region_state_nwl W a' Directed⌝) ∗
                                             ([∗ list] a' ∈ (region_addrs (addr_reg.max b a) e),                                                                    (read_write_cond a' interp) ∧ ⌜region_state_U_mono W a'⌝)
              | (inr ((URW,Local),b,e,a), inr (URW,Local,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a' ∈ (region_addrs b (addr_reg.min a e)), (read_write_cond a' interp)
                                                                    ∧ ⌜region_state_nwl W a' Local⌝) ∗
                ([∗ list] a' ∈ (region_addrs (addr_reg.max b a) e), (read_write_cond a' interp) ∧ ⌜region_state_U W a'⌝)
              | (inr ((URW,Global),b,e,a), inr (URW,Global,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                [∗ list] a' ∈ (region_addrs b e), (read_write_cond a' interp) ∧ ⌜region_state_nwl W a' Global⌝
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp_cap_URWL (interp : D) : D :=
    λne W w, (match w with
              | (inr ((URWL,Directed),b,e,a), inr (URWL,Directed,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a' ∈ (region_addrs b (addr_reg.min a e)), (read_write_cond a' interp)
                                                                 ∧ ⌜region_state_pwl_mono W a'⌝) ∗
                ([∗ list] a' ∈ (region_addrs (addr_reg.max b a) e), (read_write_cond a' interp) ∧
                                                                 ⌜region_state_U_pwl_mono W a'⌝)
              (* | inr ((URWL,Local),b,e,a) => *)
              (*   ([∗ list] a' ∈ (region_addrs b (addr_reg.min a e)), ∃ p, ⌜PermFlows (promote_perm URWL) p⌝ ∗ (read_write_cond a' p interp) *)
              (*                                                    ∧ ⌜region_state_pwl W a'⌝) ∗ *)
              (*   ([∗ list] a' ∈ (region_addrs (addr_reg.max b a) e), ∃ p, ⌜PermFlows (promote_perm URWL) p⌝ ∗ (read_write_cond a' p interp) ∧ *)
              (*                                                    ⌜region_state_U_pwl W a'⌝) *)
              | _ => False
              end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp_cap_URWX (interp : D) : D :=
    λne W w, (match w with
              | (inr ((URWX,Directed),b,e,a), inr (URWX,Directed,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a' ∈ (region_addrs b (addr_reg.min a e)), (read_write_cond a' interp)
                                                                 ∧ ⌜region_state_nwl W a' Directed⌝)
               ∗ ([∗ list] a' ∈ (region_addrs (addr_reg.max b a) e), (read_write_cond a' interp)
                                                                   ∧ ⌜region_state_U_mono W a'⌝)
              | (inr ((URWX,Local),b,e,a), inr (URWX,Local,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a' ∈ (region_addrs b (addr_reg.min a e)), (read_write_cond a' interp)
                                                                 ∧ ⌜region_state_nwl W a' Local⌝)
               ∗ ([∗ list] a' ∈ (region_addrs (addr_reg.max b a) e), (read_write_cond a' interp)
                                                                   ∧ ⌜region_state_U W a'⌝)
              | (inr ((URWX,Global),b,e,a), inr (URWX,Global,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a' ∈ (region_addrs b e), (read_write_cond a' interp)
                                                                 ∧ ⌜region_state_nwl W a' Global⌝)
             | _ => False end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp_cap_URWLX (interp : D) : D :=
    λne W w, (match w with
              | (inr ((URWLX,Directed),b,e,a), inr (URWLX,Directed,b',e',a')) =>
                ⌜b = b' ∧ e = e' ∧ a = a'⌝ ∗
                ([∗ list] a' ∈ (region_addrs b (addr_reg.min a e)), (read_write_cond a' interp)
                                                                 ∧ ⌜region_state_pwl_mono W a'⌝)
                ∗ ([∗ list] a' ∈ (region_addrs (addr_reg.max b a) e), (read_write_cond a' interp) ∧
                                                                   ⌜region_state_U_pwl_mono W a'⌝)
             | _ => False end)%I.
  Solve All Obligations with solve_proper;auto.

  Program Definition interp1 (interp : D) : D :=
    (λne W w,
    match w return _ with
    | (inl _, inl _) => interp_z W w
    | (inr ((O, g), b, e, a),inr ((O, g'), b', e', a')) => interp_cap_O W w
    | (inr ((RO, g), b, e, a),inr ((RO, g'), b', e', a')) => interp_cap_RO interp W w
    | (inr ((RW, g), b, e, a),inr ((RW, g'), b', e', a')) => interp_cap_RW interp W w
    | (inr ((RWL, g), b, e, a),inr ((RWL, g'), b', e', a')) => interp_cap_RWL interp W w
    | (inr ((RX, g), b, e, a),inr ((RX, g'), b', e', a')) => interp_cap_RX interp W w
    | (inr ((E, g), b, e, a),inr ((E, g'), b', e', a')) => interp_cap_E interp W w
    | (inr ((RWLX, g), b, e, a),inr ((RWLX, g'), b', e', a')) => interp_cap_RWLX interp W w
    | (inr ((RWX, g), b, e, a),inr ((RWX, g'), b', e', a')) => interp_cap_RWX interp W w
    | (inr ((URW, g), b, e, a),inr ((URW, g'), b', e', a')) => interp_cap_URW interp W w
    | (inr ((URWL, g), b, e, a),inr ((URWL, g'), b', e', a')) => interp_cap_URWL interp W w
    | (inr ((URWLX, g), b, e, a),inr ((URWLX, g'), b', e', a')) => interp_cap_URWLX interp W w
    | (inr ((URWX, g), b, e, a),inr ((URWX, g'), b', e', a')) => interp_cap_URWX interp W w
    | (_,_) => False
    end)%I.
  Solve All Obligations with solve_proper.

  (* Global Instance interp_expr_contractive : *)
  (*   Contractive (interp_expr). *)
  (* Proof. solve_contractive. Qed.  *)
  Global Instance interp_cap_O_contractive :
    Contractive (interp_cap_O).
  Proof. solve_contractive. Qed.
  Global Instance interp_cap_RO_contractive :
    Contractive (interp_cap_RO).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p; auto.
         apply sep_ne. solve_contractive.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         apply exist_ne. rewrite /pointwise_relation; intros.
         rewrite /read_cond rel_eq /rel_def /saved_pred_own.
         repeat apply and_ne; auto. apply sep_ne;[solve_contractive|].
         apply exist_ne =>γ. apply sep_ne; auto.
  Qed.
  Global Instance interp_cap_RW_contractive :
    Contractive (interp_cap_RW).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p; auto.
         apply sep_ne. solve_contractive.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_RWL_contractive :
    Contractive (interp_cap_RWL).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p,l,l0; auto.
         apply sep_ne. solve_contractive.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply and_ne;auto. apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance exec_cond_contractive W b e g pl b' e' g' pl' :
    Contractive (λ interp, exec_cond W b e g pl b' e' g' pl' interp).
  Proof.
    solve_contractive.
  Qed.
  Global Instance enter_cond_contractive W b e a g b' e' a' g' :
    Contractive (λ interp, enter_cond W b e a g b' e' a' g' interp).
  Proof.
    solve_contractive.
  Qed.
  Global Instance interp_cap_RX_contractive :
    Contractive (interp_cap_RX).
  Proof.
    rewrite /interp_cap_RX.
    solve_proper_prepare.
    destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p; auto.
    apply sep_ne. solve_contractive.
    rewrite /read_cond rel_eq /rel_def /saved_pred_own.
    apply big_opL_ne; auto. intros ? ? ?.
    apply exist_ne. rewrite /pointwise_relation; intros.
    repeat apply and_ne;auto. apply sep_ne. solve_contractive.
    apply exist_ne =>γ. apply sep_ne; auto.
  Qed.
  Global Instance interp_cap_E_contractive :
    Contractive (interp_cap_E).
  Proof.
    rewrite /interp_cap_E.
    solve_proper_prepare.
    destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p; auto.
    apply sep_ne. solve_contractive.
    solve_proper_prepare.
      by apply affinely_ne; apply persistently_ne; apply enter_cond_contractive.
  Qed.
  Global Instance interp_cap_RWX_contractive :
    Contractive (interp_cap_RWX).
  Proof.
    rewrite /interp_cap_RWX.
    solve_proper_prepare.
    destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p; auto.
    apply sep_ne. solve_contractive.
    rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
    apply big_opL_ne; auto. intros ? ? ?.
    f_equiv. apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. (* apply sep_ne. *)
    f_equiv. solve_contractive.
    (* - solve_proper_prepare. *)
    (*   by apply affinely_ne; apply persistently_ne; apply exec_cond_contractive. *)
  Qed.
  Global Instance interp_cap_RWLX_contractive :
    Contractive (interp_cap_RWLX).
  Proof.
    rewrite /interp_cap_RWLX.
    solve_proper_prepare.
    destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p,l,l0; auto.
    apply sep_ne. solve_contractive.
    rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
    apply big_opL_ne; auto. intros ? ? ?. f_equiv.
    apply exist_ne. rewrite /pointwise_relation; intros.
    apply sep_ne; auto. (* apply sep_ne. *)
    f_equiv.  solve_contractive.
  Qed.
  Global Instance interp_cap_URW_contractive :
    Contractive (interp_cap_URW).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p,l,l0; auto.
         all: apply sep_ne;[solve_contractive|].
         - apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
           f_equiv.
           rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
           apply exist_ne =>γ. apply sep_ne; auto.
           simpl. f_equiv. solve_contractive.
         - apply sep_ne; auto.
           apply big_opL_ne; auto; rewrite /pointwise_relation; intros.
           f_equiv.
           rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
           apply exist_ne =>γ. apply sep_ne; auto.
           simpl. f_equiv. solve_contractive.
           apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
           rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
           f_equiv. apply exist_ne. rewrite /pointwise_relation; intros.
           apply sep_ne; auto. f_equiv. solve_contractive.
         - apply sep_ne; auto.
           apply big_opL_ne; auto; rewrite /pointwise_relation; intros.
           f_equiv.
           rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
           apply exist_ne =>γ. apply sep_ne; auto. f_equiv. solve_contractive.
           apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
           rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
           f_equiv. apply exist_ne. rewrite /pointwise_relation; intros.
           apply sep_ne; auto.
           f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_URWL_contractive :
    Contractive (interp_cap_URWL).
  Proof. solve_proper_prepare.
         destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p,l,l0; auto.
         all: apply sep_ne;[solve_contractive|].
         apply sep_ne; auto.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         f_equiv. rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         apply exist_ne =>γ. apply sep_ne; auto.
         simpl. f_equiv. solve_contractive.
         apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
         rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
         f_equiv. apply exist_ne. rewrite /pointwise_relation; intros.
         apply sep_ne; auto.
         f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_URWX_contractive :
    Contractive (interp_cap_URWX).
  Proof.
    rewrite /interp_cap_URWX.
    solve_proper_prepare.
    destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p,l,l0; auto.
         all: apply sep_ne;[solve_contractive|].
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ? ?.
      f_equiv. apply exist_ne. rewrite /pointwise_relation; intros.
      apply sep_ne; auto. f_equiv. solve_contractive.
    - apply sep_ne; auto.
      + apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
        f_equiv.
        rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
        apply exist_ne =>γ. apply sep_ne; auto.
        simpl. f_equiv. solve_contractive.
      + apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
        f_equiv. rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
        apply exist_ne => γ. apply sep_ne; auto.
        simpl. f_equiv. solve_contractive.
    - apply sep_ne; auto.
      + apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
        f_equiv.
        rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
        apply exist_ne =>γ. apply sep_ne; auto.
        simpl. f_equiv. solve_contractive.
      + apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
        f_equiv. rewrite /pointwise_relation; intros.
        rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
        apply exist_ne => γ. apply sep_ne; auto.
        simpl. f_equiv. solve_contractive.
  Qed.
  Global Instance interp_cap_URWLX_contractive :
    Contractive (interp_cap_URWLX).
  Proof.
    rewrite /interp_cap_URWLX.
    solve_proper_prepare.
    destruct x1; auto. destruct o,o0;auto. destruct c, p, p, p, p,c0,p,p,p,p,l,l0; auto.
    all: apply sep_ne;[solve_contractive|].
    apply sep_ne.
    - rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply big_opL_ne; auto. intros ? ? ?.
      f_equiv. apply exist_ne. rewrite /pointwise_relation; intros.
      apply sep_ne; auto. f_equiv. solve_contractive.
    - apply big_opL_ne; auto. rewrite /pointwise_relation; intros.
      f_equiv.
      rewrite /read_write_cond rel_eq /rel_def /saved_pred_own.
      apply exist_ne => γ. apply sep_ne; auto.
      simpl. f_equiv. solve_contractive.
  Qed.

  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn W w.
    rewrite /interp1.
    destruct w;auto. destruct o,o0;auto.
    destruct c,p,p,p,p,c0,p,p,p,p; auto.
    - by apply interp_cap_RO_contractive.
    - by apply interp_cap_RW_contractive.
    - by apply interp_cap_RWL_contractive.
    - by apply interp_cap_RX_contractive.
    - by apply interp_cap_E_contractive.
    - by apply interp_cap_RWX_contractive.
    - by apply interp_cap_RWLX_contractive.
    - by apply interp_cap_URW_contractive.
    - by apply interp_cap_URWL_contractive.
    - by apply interp_cap_URWX_contractive.
    - by apply interp_cap_URWLX_contractive.
  Qed.

  Lemma fixpoint_interp1_eq (W : WORLD) (x : prodO (leibnizO Word) (leibnizO Word)) :
    fixpoint (interp1) W x ≡ interp1 (fixpoint (interp1)) W x.
  Proof. exact: (fixpoint_unfold (interp1) W x). Qed.

  Program Definition interp : D :=
    λne W w, (fixpoint (interp1)) W w.
  Solve All Obligations with solve_proper.
  Definition interp_expression r : D := interp_expr interp r.
  Definition interp_registers : R := interp_reg interp.

  Global Instance interp_persistent : Persistent (interp W w).
  Proof. intros. destruct w; destruct o,o0; simpl; rewrite fixpoint_interp1_eq; simpl.
         apply _. apply _. destruct c,p,p,p,p;apply _.
         destruct c,p,p,p,p,c0,p,p,p,p; destruct l,l0; repeat (apply exist_persistent; intros); try apply _.
  Qed.

  Instance ne_interpC : NonExpansive
                           (λ Wv : (WORLD * (prodO (leibnizO Word) (leibnizO Word))), (interp Wv.1) Wv.2).
  Proof. intros. solve_proper. Qed.

  (* Non-curried version of interp *)
  Definition interpC :=
    (λne Wv : WORLD * (prodO (leibnizO Word) (leibnizO Word)), (interp Wv.1) Wv.2).

  Lemma interp_eq W (w1 w2 : Word) :
    ⊢ interp W (w1,w2) →
    ⌜w1 = w2⌝.
  Proof.
    iIntros "Hv".
    rewrite fixpoint_interp1_eq.
    destruct w1,w2;simpl;auto.
    - iDestruct "Hv" as %->;auto.
    - destruct c,p,p,p,p;try done.
    - destruct c,p,p,p,p,c0,p,p,p,p;try done.
      iDestruct "Hv" as %(->&->&->&->);auto.
      all: try destruct l,l0;try done.
      all: try iDestruct "Hv" as "[(->&->&->&->) _]";auto.
      all: try iDestruct "Hv" as "[(->&->&->) _]";auto.
      all: try iDestruct "Hv" as "[(_&->&->&->) _]";auto.
  Qed.

  Lemma read_allowed_inv W (a'' a b e : Addr) p g (w:Word) :
    (b ≤ a'' ∧ a'' < e)%Z →
    readAllowed p →
    ⊢ interp W (inr ((p,g),b,e,a), w) →
    if writeAllowed p then read_write_cond a'' interp else (∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∧ read_cond a'' P interp).
  Proof.
    iIntros (Hin Ra) "Hinterp". iDestruct (interp_eq with "Hinterp") as %<-.
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p,g; try contradiction;simpl.
    all: try done.
    all: iDestruct "Hinterp" as "[_ Hinterp]".
    all: try (iDestruct (extract_from_region_inv with "Hinterp") as (P Hpers) "[Hinv _]";eauto).
    all: try (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv _]";eauto).
  Qed.

  Definition readAllowedU p : bool :=
    match p with
    | URW | URWL | URWX | URWLX => true
    | _ => false
    end.

  Lemma read_allowedU_inv W (a'' a b e : Addr) p g (w:Word) :
    (b ≤ a'' ∧ a'' < e)%Z →
    readAllowedU p →
    ⊢ interp W (inr ((p,g),b,e,a),w) →
    (read_write_cond a'' interp).
  Proof.
    iIntros (Hin Ra) "Hinterp".
    iDestruct (interp_eq with "Hinterp") as %<-.
    rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
    destruct p,g; try contradiction; try done;
      iDestruct "Hinterp" as "[_ Hinterp]";
      try (iDestruct "Hinterp" as "[Hinterp Hinterpe]"); try done.
    all: try by (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv _]";eauto).
    all: try (destruct (decide (a'' < a)%a);
    [iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv _]";
      [|eauto];solve_addr|
     iDestruct (extract_from_region_inv with "Hinterpe") as "[Hinv _]";
     [|eauto];solve_addr]).
  Qed.

  Definition isDirected l :=
    match l with
    | Directed => true
    | _ => false
    end.

  Lemma writeLocalAllowed_implies_local W (p : Perm) (l : Locality) (b e a : Addr) (w : Word):
    machine_base.pwl p = true ->
    interp W (inr ((p, l), b, e, a),w) -∗ ⌜isDirected l = true⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H; try congruence; destruct l; eauto.
    all: destruct w;try done.
    all: destruct c,p,p,p,p;done.
  Qed.

  Lemma writeLocalAllowedU_implies_local W p l b e a (w : Word):
    pwlU p = true ->
    interp W (inr (p, l, b, e, a),w) -∗ ⌜isDirected l = true⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in H; try congruence; destruct l; eauto.
    all: destruct w;try done.
    all: destruct c,p,p,p,p;done.
  Qed.

  Lemma readAllowed_valid_cap_implies W p l b e a (w:Word) :
    readAllowed p = true ->
    withinBounds (p, l, b, e, a) = true ->
    interp W (inr (p, l, b, e, a),w) -∗
           ⌜∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked ∧ (∀ g, ρ ≠ Monostatic g) ∧ (∀ w, ρ ≠ Uninitialized w)⌝.
  Proof.
    intros Hp Hb. iIntros "H".
    eapply withinBounds_le_addr in Hb.
    iDestruct (interp_eq with "H") as %<-.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in Hp; try congruence.
    all: try iDestruct "H" as "[_ H]".
    - iDestruct (extract_from_region_inv with "H") as (P Hpers) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. destruct l; eauto;simpl in HH.
      destruct HH;eauto; eexists;eauto.
    - iDestruct (extract_from_region_inv with "H") as "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. destruct l; eauto; simpl in HH.
      destruct HH;eexists;eauto.
    - destruct l; auto.
      iDestruct "H" as "[_ H]".
      iDestruct (extract_from_region_inv with "H") as "[_ %]"; eauto.
      iPureIntro. eexists;split;eauto.
    - iDestruct (extract_from_region_inv with "H") as (p Hpers) "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. destruct l; eauto. simpl in HH.
      destruct HH;eexists;eauto.
    - iDestruct (extract_from_region_inv with "H") as "[_ H]"; eauto.
      iDestruct "H" as %HH. iPureIntro. destruct l; eauto. simpl in HH.
      destruct HH;eexists;eauto.
    - destruct l;auto.
      iDestruct "H" as "[_ H]".
      iDestruct (extract_from_region_inv with "H") as "[_ %]"; eauto.
      rewrite H0. iPureIntro. eexists;eauto.
  Qed.

  Definition region_conditions W p g b e:=
  ([∗ list] a ∈ (region_addrs b e), (if writeAllowed p then read_write_cond a interp else (∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∧ read_cond a P interp))
                                          ∧ ⌜if machine_base.pwl p
                                             then region_state_pwl_mono W a
                                             else region_state_nwl W a g⌝)%I.

  Lemma readAllowed_implies_region_conditions W p l b e a (w:Word):
    readAllowed p = true ->
    interp W (inr (p, l, b, e, a),w) -∗ region_conditions W p l b e.
  Proof.
    intros. iIntros "Hvalid".
    iDestruct (interp_eq with "Hvalid") as %<-.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    unfold region_conditions.
    destruct p; simpl in *; try congruence; destruct l; try done; iDestruct "Hvalid" as "[_ Hvalid]"; simpl; eauto.
    all:iApply (big_sepL_mono with "Hvalid");iIntros (k y Hin) "H".
    all: iApply and_exist_r; iDestruct "H" as (P) "(?&?&?)"; iExists _; iFrame.
  Qed.

  Lemma read_write_cond_implies_read_cond a :
    read_write_cond a interp -∗ ∃ P, read_cond a P interp.
  Proof.
    iIntros "Hread". iExists interp. iFrame. rewrite /rcond. iSplit; auto.
    iNext. iModIntro. iIntros (W1 W2 z1 z2) "Heq". rewrite !fixpoint_interp1_eq.
    iDestruct "Heq" as %->. done.
  Qed.

  Definition writeAllowedWord (w : Word) : Prop :=
    match w with
    | inl _ => False
    | inr (p,_,_,_,_) => writeAllowed p || isU p = true
    end.

  Definition hasValidAddress (w : Word) (a : Addr) : Prop :=
    match w with
    | inl _ => False
    | inr (p,g,b,e,a') => (* (b ≤ a' ∧ a' < e)%Z ∧ *) (* a = a' *) (b <= a < e)%Z
    end.

  Definition writeAllowed_in_r_a r a :=
    ∃ reg, writeAllowedWord (r !r! reg) ∧ hasValidAddress (r !r! reg) a.


  From Coq Require Import Eqdep_dec.
  Global Instance reg_finite : finite.Finite RegName.
  Proof. apply (finite.enc_finite (λ r : RegName, match r with
                                                  | PC => S RegNum
                                                  | addr_reg.R n fin => n
                                                  end)
                                   (λ n : nat, match n_to_regname n with | Some r => r | None => PC end)
                                   (S (S RegNum))).
         - intros x. destruct x;auto.
           unfold n_to_regname.
           destruct (nat_le_dec n RegNum).
           + do 2 f_equal. apply eq_proofs_unicity. decide equality.
           + exfalso. by apply (Nat.leb_le n RegNum) in fin.
         - intros x.
           + destruct x;[lia|]. apply leb_le in fin. lia.
         - intros i Hlt. unfold n_to_regname.
           destruct (nat_le_dec i RegNum);auto.
           lia.
  Qed.

  Global Instance writeAllowedWord_dec v: Decision (writeAllowedWord v).
  Proof. destruct v;[right;auto|]. destruct c,p,p,p;simpl;apply _. Qed.

  Global Instance hasValidAddress_dec v a: Decision (hasValidAddress v a).
  Proof. destruct v;[right;auto|]. destruct c,p,p,p;simpl;apply _. Qed.

  Global Instance writeAllowed_in_r_a_Decidable r a: Decision (writeAllowed_in_r_a r a).
  Proof.
    apply finite.exists_dec.
    intros x. destruct (r !! x) eqn:Hsome.
    - rewrite /RegLocate. rewrite Hsome. apply _.
    - rewrite /RegLocate Hsome. right;simpl. intros [??]. done.
  Qed.

  Global Instance writeAllowed_in_r_a_Persistent r a: Persistent (if decide (writeAllowed_in_r_a r a)
                                                                    then read_write_cond a interp else emp)%I.
  Proof. intros. case_decide; apply _. Qed.

  Lemma interp_reg_eq W r1 r2 (w:Word) :
    ⊢ interp_registers W (r1, r2) →
    ⌜<[PC:=w]> r1 = <[PC:=w]> r2⌝.
  Proof.
    iIntros "Hv".
    rewrite /interp_registers /=.
    iDestruct "Hv" as (Hfull) "Hv".
    rewrite map_eq'. iIntros (k v). rewrite iff_to_and.
    iSplit.
    - iIntros (Hv). simpl in *.
      destruct (decide (k = PC));subst. rewrite lookup_insert in Hv;rewrite lookup_insert //.
      simplify_map_eq_alt. rewrite lookup_insert_ne//.
      specialize (Hfull k) as [ [v1 Hv1] [v2 Hv2] ]. simplify_map_eq_alt.
      rewrite /RegLocate. iSpecialize ("Hv" $! k n). rewrite Hv Hv2.
      iDestruct (interp_eq with "Hv") as %<-;auto.
    - iIntros (Hv). simpl in *.
      destruct (decide (k = PC));subst. rewrite lookup_insert in Hv;rewrite lookup_insert //.
      simplify_map_eq_alt. rewrite lookup_insert_ne//.
      specialize (Hfull k) as [ [v1 Hv1] [v2 Hv2] ]. simplify_map_eq_alt.
      rewrite /RegLocate. iSpecialize ("Hv" $! k n). rewrite Hv Hv1.
      iDestruct (interp_eq with "Hv") as %<-;auto.
  Qed.

  Lemma interp_reg_dupl W (r r' : Reg) :
    interp_registers W (r,r') -∗ interp_registers W (r,r).
  Proof.
    iIntros "[% #Hv]". rewrite /interp_registers /=.
    iSplit;[iPureIntro;intros x; destruct H0 with x;eauto|].
    iIntros (reg Hne). iDestruct ("Hv" $! reg Hne) as "Hval".
    destruct H0 with reg as [ [? Hreg1] [? Hreg2] ].
    rewrite /RegLocate Hreg1 Hreg2.
    iDestruct (interp_eq with "Hval") as %->. iFrame "Hval".
  Qed.

  Lemma read_allowed_inv_regs (a' a b e: Addr) p g W r (w:Word) :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp_registers W r -∗
      interp W (inr (p,g,b,e,a),w) -∗
      (∃ (P : D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∗ rel a' (λ Wv, P Wv.1 Wv.2) ∗ rcond P interp ∗
                if decide (writeAllowed_in_r_a (<[PC:=inr (p,g,b,e,a)]> r.1) a') then wcond P interp else emp))%I.
  Proof.
    iIntros (Hin Ra) "#Hregs #Hinterp".
    destruct r as [r1 r2].
    iDestruct (interp_reg_eq _ _ _ w with "Hregs" ) as %Heqregs.
    iDestruct (interp_eq with "Hinterp") as %<-.
    rewrite /interp_registers /interp_reg /=.
    iDestruct "Hregs" as "[Hfull Hregvalid]".
    case_decide as Hinra.
    - destruct Hinra as [reg [Hwa Ha] ].
      destruct (decide (reg = PC)).
      + rewrite /RegLocate in Hwa Ha. subst. rewrite lookup_insert in Ha.
        rewrite lookup_insert in Hwa.
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct p,g; try contradiction; inversion Hwa; try done;
          try (iDestruct "Hinterp" as "[_ Hinterp]");
          try (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv Hiff]"; eauto).
        all: iExists interp;iFrame "Hinv". all: iSplitR;[iPureIntro;apply _|]. all: rewrite /rcond /wcond /=;auto.
        all: iSplit;[iSplit;auto|].
        all: iNext;iModIntro;try (iIntros (W1 W2 z1 z2) "Heq";rewrite !fixpoint_interp1_eq;iDestruct "Heq" as %->;auto).
        all: auto.
      + rewrite /RegLocate in Hwa Ha. rewrite lookup_insert_ne// in Hwa,Ha.
        destruct (r1 !! reg) eqn:Hsome;rewrite Hsome in Ha Hwa;[|inversion Ha].
        assert (r2 !! reg = Some w) as Hsome'.
        { rewrite -(lookup_insert_ne _ PC reg (inr (p,g,b,e,a)))// -Heqregs lookup_insert_ne//. }
        destruct w;[inversion Ha|]. destruct c,p0,p0,p0.
        iSpecialize ("Hregvalid" $! _ n). rewrite /RegLocate Hsome Hsome'. iClear "Hinterp".
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct p0,l; try contradiction; inversion Hwa; try done;
          try (iDestruct "Hregvalid" as "[_ Hregvalid]").
        all: try (iDestruct (extract_from_region_inv _ _ a' with "Hregvalid") as "[Hinv Hiff]";[solve_addr|];iExists interp;iFrame "Hinv";rewrite /rcond /wcond /=;auto).
        all: try (iSplitR;[iPureIntro;apply _|auto]).
        all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z1 z2) "Heq";rewrite !fixpoint_interp1_eq;iDestruct "Heq" as %->;auto).
        all: iDestruct "Hregvalid" as "[Hhi Hlo]".
        all: assert (a2 <= a' < (addr_reg.min a0 a1) ∨ (addr_reg.max a2 a0) <= a' < a1)%a as [Hwb | Hwb];
          [solve_addr|iRename "Hhi" into "Hin"|iRename "Hlo" into "Hin"].
        all: iDestruct (extract_from_region_inv _ _ a' with "Hin") as "[Hinv Hiff]";[solve_addr|].
        all: iExists interp;iFrame "Hinv";rewrite /rcond /wcond /=.
        all: try (iSplitR;[iPureIntro;apply _|auto]).
        all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z1 z2) "Heq";rewrite !fixpoint_interp1_eq;iDestruct "Heq" as %->;auto).
    - rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
      destruct p,g; try contradiction; try done.
      all: try iDestruct "Hinterp" as "[_ Hinterp]".
      all: try (iDestruct (extract_from_region_inv with "Hinterp") as (P Hpers) "[ [Hrcond Hinv] Hiff]"; eauto).
      all: iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv Hiff]";eauto;iExists interp;iFrame "Hinv";rewrite /rcond /wcond /=.
      all: iSplitR;[iPureIntro;apply _|auto].
      all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z1 z2) "Heq";rewrite !fixpoint_interp1_eq;iDestruct "Heq" as %->;auto).
  Qed.

  Global Instance region_conditions_persistent : Persistent (region_conditions W p g b e).
  Proof. intros. rewrite /region_conditions. apply big_sepL_persistent. intros.
         destruct (writeAllowed p),(machine_base.pwl p);apply _. Qed.

  Lemma extract_from_region_inv_regs a (a' b e : Addr) p g W r :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp_registers W r -∗
       region_conditions W p g b e -∗
       (∃ (P : D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∗ rel a' (λ Wv, P Wv.1 Wv.2) ∗ rcond P interp ∗
                       if decide (writeAllowed_in_r_a (<[PC:=inr (p,g,b,e,a)]> r.1) a')
                       then wcond P interp else emp))%I.
  Proof.
    iIntros (Hin Hra) "#Hregs #Hinterp".
    rewrite /interp_registers /interp_reg /=.
    iDestruct "Hregs" as "[Hfull Hregvalid]".
    case_decide as Hinra.
    - destruct Hinra as [reg [Hwa Ha] ].
      destruct (decide (reg = PC)).
      + rewrite /RegLocate in Hwa Ha. subst. rewrite lookup_insert in Ha.
        rewrite lookup_insert in Hwa.
        rewrite /interp. cbn.
        destruct p,g; try contradiction; inversion Hwa; try done;
          try (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv Hiff]"; eauto).
        all: iExists interp;iFrame "Hinv". all: rewrite /rcond /wcond /=.
        all: iSplitR;[iPureIntro;apply _|].
        all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z1 z2) "Heq";rewrite !fixpoint_interp1_eq;iDestruct "Heq" as %->;auto).
      + rewrite /RegLocate in Hwa Ha. rewrite lookup_insert_ne// in Hwa,Ha.
        destruct (r.1 !! reg) eqn:Hsome;rewrite Hsome in Ha Hwa;[|inversion Ha].
        destruct w;[inversion Ha|]. destruct c,p0,p0,p0. iDestruct "Hfull" as %Hfull.
        destruct Hfull with reg as [ [v1 Hv1] [v2 Hv2] ]. rewrite Hsome in Hv1;inversion Hv1;subst.
        iSpecialize ("Hregvalid" $! _ n). rewrite /RegLocate Hsome Hv2.
        iDestruct (interp_eq with "Hregvalid") as %<-.
        rewrite /interp. cbn. rewrite fixpoint_interp1_eq /=; cbn.
        destruct p0,l; try contradiction; inversion Hwa; try done.
        all: iDestruct "Hregvalid" as "[_ Hregvalid]".
        all: try (iDestruct (extract_from_region_inv with "Hregvalid") as "[Hinv Hiff]";eauto;iExists interp;iFrame "Hinv";rewrite /rcond /wcond /=).
        all: try (iSplitR;[iPureIntro;apply _|]).
        all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z1 z2) "Heq";rewrite !fixpoint_interp1_eq;iDestruct "Heq" as %->;auto).
        all: iDestruct "Hregvalid" as "[Hhi Hlo]".
        all: assert (a2 <= a' < (addr_reg.min a0 a1) ∨ (addr_reg.max a2 a0) <= a' < a1)%a as [Hwb | Hwb];
          [solve_addr|iRename "Hhi" into "Hin"|iRename "Hlo" into "Hin"].
        all: iDestruct (extract_from_region_inv _ _ a' with "Hin") as "[Hinv Hiff]";[solve_addr|].
        all: iExists interp;iFrame "Hinv";rewrite /rcond /wcond /=;auto.
        all: try (iSplitR;[iPureIntro;apply _|]).
        all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z1 z2) "Heq";rewrite !fixpoint_interp1_eq;iDestruct "Heq" as %->;auto).
    - rewrite /interp. cbn.
      destruct p,g; try contradiction; try done. all: rewrite /region_conditions /=.
      all: try (iDestruct (extract_from_region_inv with "Hinterp") as "[Ha _]"; eauto; iDestruct "Ha" as (P Hpers) "[Ha Hcond]";iExists P;iFrame "Ha Hcond").
      all: try (iDestruct (extract_from_region_inv with "Hinterp") as "[Hinv Hiff]";eauto;iExists interp;iFrame "Hinv";rewrite /rcond /wcond /=).
      all: iSplitR;[iPureIntro;apply _|].
      all: try (iSplit;[iSplit|];auto;iNext;iModIntro;iIntros (W1 W2 z1 z2) "Heq";rewrite !fixpoint_interp1_eq;iDestruct "Heq" as %->;auto).
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies W p l b e a (w:Word):
    machine_base.pwl p = true ->
    withinBounds (p, l, b, e, a) = true ->
    interp W (inr (p, l, b, e, a),w) -∗
           ⌜std W !! a = Some Monotemporary⌝.
  Proof.
    intros Hp Hb. iIntros "Hvalid".
    iDestruct (interp_eq with "Hvalid") as %<-.
    iAssert (⌜isDirected l = true⌝)%I as "%". by iApply writeLocalAllowed_implies_local.
    eapply withinBounds_le_addr in Hb.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in Hp; try congruence; destruct l;try done.
    all: iDestruct "Hvalid" as "[_ Hvalid]".
    all: iDestruct (extract_from_region_inv with "Hvalid") as "[_ %]"; eauto.
  Qed.

  Lemma writeLocalAllowedU_valid_cap_implies W p l b e a (w:Word):
    pwlU p = true ->
    withinBounds (p, l, b, e, a) = true ->
    interp W (inr (p, l, b, e, a),w) -∗
           ⌜std W !! a = Some Monotemporary ∨ ∃ w, std W !! a = Some (Uninitialized w)⌝.
  Proof.
    intros Hp Hb. iIntros "Hvalid".
    iDestruct (interp_eq with "Hvalid") as %<-.
    iAssert (⌜isDirected l = true⌝)%I as "%". by iApply writeLocalAllowedU_implies_local.
    eapply withinBounds_le_addr in Hb.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in Hp; try congruence; destruct l;try done;
      iDestruct "Hvalid" as "[_ Hvalid]";
      try iDestruct (extract_from_region_inv with "Hvalid") as  "[_ %]"; eauto.
    - assert (addr_reg.max b a = a) as ->;[solve_addr|].
      iDestruct "Hvalid" as "[_ Hvalid]".
      iDestruct (extract_from_region_inv _ _ a with "Hvalid") as "[_ %]". solve_addr.
      destruct H1 as [? | ?];auto.
    - assert (addr_reg.max b a = a) as ->;[solve_addr|].
      iDestruct "Hvalid" as "[_ Hvalid]".
      iDestruct (extract_from_region_inv _ _ a with "Hvalid") as "[_ %]". solve_addr.
      destruct H1 as [? | ?];auto.
  Qed.

  Lemma writeLocalAllowedU_valid_cap_below_implies W p l b e a a' (w:Word):
    pwlU p = true -> withinBounds (p, l, b, e, a') = true ->
    (a' < a)%a →
    interp W (inr (p, l, b, e, a),w) -∗
           ⌜std W !! a' = Some Monotemporary⌝.
  Proof.
    intros Hp Hlt Hb. iIntros "Hvalid".
    iAssert (⌜isDirected l = true⌝)%I as "%". by iApply writeLocalAllowedU_implies_local.
    eapply withinBounds_le_addr in Hlt.
    iDestruct (interp_eq with "Hvalid") as %<-.
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct p; simpl in Hp; try congruence; destruct l;try done;
      iDestruct "Hvalid" as "[_ Hvalid]";
      try iDestruct (extract_from_region_inv _ _ a' with "Hvalid") as "[_ %]"; eauto; try solve_addr.
    - assert (addr_reg.max b a = a) as ->;[solve_addr|].
      iDestruct "Hvalid" as "[Hvalid _]".
      iDestruct (extract_from_region_inv _ _ a' with "Hvalid") as "[_ %]". solve_addr. auto.
    - assert (addr_reg.max b a = a) as ->;[solve_addr|].
      iDestruct "Hvalid" as "[Hvalid _]".
      iDestruct (extract_from_region_inv _ _ a' with "Hvalid") as "[_ %]". solve_addr. auto.
  Qed.

  Lemma interp1_eq interp (W: WORLD) p l b e a :
    ((interp1 interp W (inr (p, l, b, e, a),inr (p,l,b,e,a))) ≡
             (if perm_eq_dec p O then True else
             if perm_eq_dec p E then □ enter_cond W b e a l b e a l interp else
               ([∗ list] a ∈ region_addrs b (if isU p && isLocal l then (addr_reg.min a e) else e),
                (if writeAllowed p || readAllowedU p then read_write_cond a interp else (∃ (P:D), ⌜(∀ Wv, Persistent (P Wv.1 Wv.2))⌝ ∧ read_cond a P interp)) ∧
                      ⌜if pwlU p then region_state_pwl_mono W a else region_state_nwl W a l⌝) ∗
                (⌜if pwlU p then isDirected l else True⌝) ∗
                (if isU p && isLocal l then [∗ list] a ∈ region_addrs (addr_reg.max b a) e,
                                            read_write_cond a interp ∧
                                                  ⌜if pwlU p
                                                   then region_state_U_pwl_mono W a
                                                   else (match l with
                                                         | Directed => region_state_U_mono W a
                                                         | _ => region_state_U W a
                                                         end)⌝ else emp%I))%I).
  Proof.
    iSplit.
    { iIntros "HA".
      destruct (perm_eq_dec p O); subst; simpl; auto.
      destruct (perm_eq_dec p E); subst; simpl; auto.
      iDestruct "HA" as "[_ HA]";auto.
      destruct p; simpl; try congruence; auto; destruct l; simpl; try done;
        iDestruct "HA" as "[_ HA]"; auto;
        try (iSplit;auto;iApply (big_sepL_mono with "HA");intros;iIntros "H";iApply and_exist_r;
            iDestruct "H" as (P) "(?&?&?)"; iExists _; iFrame).
      all: iDestruct "HA" as "[HA HB]"; eauto. }
    { iIntros "A".
      destruct (perm_eq_dec p O); subst; simpl; auto.
      destruct (perm_eq_dec p E); subst; simpl; auto.
      iDestruct "A" as "(B & % & C)".
      destruct p; simpl in *; try congruence; subst; eauto; destruct l; eauto.
      all: iSplit;auto.
      all: (iApply (big_sepL_mono with "B");intros;iIntros "H").
      all: iDestruct (and_exist_r with "H") as (P) "((?&?)&?)".
      all: by iExists _;iFrame. }
  Qed.

End logrel.
