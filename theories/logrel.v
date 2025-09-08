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

Record cframe := MkCFrame {
      wret : Word;
      wstk : Word;
      wcgp : Word;
      wcs0 : Word;
      wcs1 : Word;
      is_untrusted_caller : bool;
  }.

Notation cstack := (list cframe).

Definition cstackR := excl_authR (leibnizO cstack).
Definition cstackUR := excl_authUR (leibnizO cstack).

Class CSTACK_preG Σ :=
  { cstack_preG :: inG Σ cstackUR; }.

Class CSTACKG Σ :=
  { cstack_inG :: inG Σ cstackUR;
    γcstack : gname;
  }.

Definition CSTACK_preΣ :=
  #[ GFunctor cstackUR ].

Instance subG_CSTACK_preΣ {Σ} :
  subG CSTACK_preΣ Σ → CSTACK_preG Σ.
Proof. solve_inG. Qed.

Section CStack.
  Context {Σ : gFunctors} {cstackg : CSTACKG Σ} .

  Definition cstack_full (cstk : cstack) : iProp Σ
    := own γcstack (●E (cstk : leibnizO cstack) : cstackUR).

  Definition cstack_frag (cstk : cstack) : iProp Σ
    := own γcstack (◯E (cstk : leibnizO cstack) : cstackUR).

  Lemma cstack_agree (cstk cstk' : cstack) :
   cstack_full cstk -∗
   cstack_frag cstk' -∗
   ⌜ cstk = cstk' ⌝.
  Proof.
    iIntros "Hfull Hfrag".
    rewrite /cstack_full /cstack_frag.
    iCombine "Hfull Hfrag" as "H".
    iDestruct (own_valid with "H") as "%H".
    by apply excl_auth_agree_L in H.
  Qed.

  Lemma cstack_update (cstk cstk' cstk'' : cstack) :
   cstack_full cstk -∗
   cstack_frag cstk' ==∗
   cstack_full cstk'' ∗ cstack_frag cstk''.
  Proof.
    iIntros "Hfull Hfrag".
    rewrite /cstack_full /cstack_frag.
    iCombine "Hfull Hfrag" as "H".
    iMod ( own_update _ _ _  with "H" ) as "H".
    { apply excl_auth_update. }
    iDestruct "H" as "[? ?]".
    by iFrame.
  Qed.

End CStack.

Section pre_CSTACK.
  Context {Σ : gFunctors} {tframeg : CSTACK_preG Σ}.

  Lemma gen_tframe_init (cstk : cstack) :
    ⊢ |==> (∃ (cstackg : CSTACKG Σ), cstack_full cstk ∗ cstack_frag cstk).
  Proof.
    iMod (own_alloc (A:=cstackUR) (●E (cstk : leibnizO _) ⋅ ◯E (cstk : leibnizO _) )) as (γcstack) "Hcstack"
    ; first by apply excl_auth_valid.
    iModIntro. iExists (Build_CSTACKG _ _ γcstack).
    by rewrite own_op.
  Qed.

End pre_CSTACK.

(** interp : is a unary logical relation. *)
Section logrel.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    `{swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (CSTK -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Definition safeC (P : V) :=
    (λ WCv : WORLD * CmptName * (leibnizO Word), P WCv.1.1 WCv.1.2 WCv.2).

  Program Definition safeUC (P : WORLD * CmptName * leibnizO Word → iPropO Σ) : V :=
    λne a b c, P (a, b, c).
  Solve All Obligations with solve_proper.

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
    (λne (cstk : CSTK) (W : WORLD) (C : CmptName) (wpc : Word) (wstk : Word),
       ∀ regs,
       ( interp_reg interp W C regs
        ∗ registers_pointsto (<[PC:=wpc]> regs)
        ∗ ⌜ regs !! csp = Some wstk ⌝ (* TODO: maybe we should also have the same for pc *)
        ∗ region W C
        ∗ sts_full_world W C
        ∗ interp_cont W C
        ∗ na_own logrel_nais ⊤
        ∗ cstack_frag cstk
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

  (* TODO move in machine_base *)
  Definition get_a (w : Word) :=
    match w with
    | WCap _ _ _ _ a => Some a
    | _ => None
    end.

  Definition get_e (w : Word) :=
    match w with
    | WCap _ _ _ e _ => Some e
    | _ => None
    end.

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


  (* TODO Is there any way to move this at a better place? *)
  Definition opening_resources (interp : V) W C a :=
    (∃ v φ p ρ,
      sts_state_std C a ρ
      ∗ ▷ (φ (W, C, v))
      ∗ ▷ (monotonicity_guarantees_region C φ p v ρ)
      ∗ a ↦ₐ v
      ∗ ▷ rcond (safeUC φ) C p interp
      ∗ ▷ wcond (safeUC φ) C interp
      ∗ rel C a p φ
      ∗ ⌜ ρ ≠ Revoked ⌝
      ∗ ⌜ isO p = false ⌝
      ∗ ⌜ forall Wv, Persistent (φ Wv) ⌝)%I.

  Definition closing_resources (interp : V) W C a w : iProp Σ :=
    ∃ φ p ρ,
      (sts_state_std C a ρ
       ∗ (φ (W, C, w))
       ∗ (monotonicity_guarantees_region C φ p w ρ)
       ∗ rcond (safeUC φ) C p interp
       ∗ wcond (safeUC φ) C interp
       ∗ rel C a p φ
       ∗ ⌜ ρ ≠ Revoked ⌝
       ∗ ⌜ isO p = false ⌝
       ∗ ⌜ forall Wv, Persistent (φ Wv) ⌝
      )%I.

  Global Instance closing_resources_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) closing_resources.
  Proof.
    intros interp interp0 Heq ????????????.
    rewrite /closing_resources.
    repeat (f_equiv; auto).
  Qed.

  Program Definition interp_cont_exec (interp : V) (interp_cont : K) :
    (CSTK -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO cframe) -n> iPropO Σ)
    :=
    (λne (cstk : CSTK) (W : WORLD) (C : CmptName)
       (frm : cframe)
     ,
       ∀ wca0 wca1 regs a_stk e_stk,
       let callee_stk_region :=
         finz.seq_between (a_stk ^+4)%a e_stk
         (* ( if frm.(is_untrusted_caller) *)
         (*   then finz.seq_between a_stk e_stk *)
         (*   else finz.seq_between (a_stk ^+4)%a e_stk) *)
       in
       ( PC ↦ᵣ updatePcPerm frm.(wret)
         ∗ cra ↦ᵣ frm.(wret)
         ∗ csp ↦ᵣ frm.(wstk)
         (* cgp, cs0 and cs1 are callee-saved registers *)
         ∗ cgp ↦ᵣ frm.(wcgp)
         ∗ cs0 ↦ᵣ frm.(wcs0)
         ∗ cs1 ↦ᵣ frm.(wcs1)
         (* ca0 and ca1 are the return value *)
         ∗ ca0 ↦ᵣ wca0 ∗ interp W C wca0
         ∗ ca1 ↦ᵣ wca1 ∗ interp W C wca1
         (* all other register contain 0 *)
         ∗ ⌜dom regs = all_registers_s ∖ {[PC; cra ; cgp; csp; cs0; cs1 ; ca0; ca1]}⌝
         ∗ ([∗ map] r↦w ∈ regs, r ↦ᵣ WInt 0)
         (* World interpretation *)
         ∗ ⌜ get_a frm.(wstk) = Some a_stk ⌝
         ∗ ⌜ get_e frm.(wstk) = Some e_stk ⌝
         ∗ [[ a_stk , e_stk ]] ↦ₐ [[ addr_reg_sample.region_addrs_zeroes a_stk e_stk ]]
         ∗ open_region_many W C callee_stk_region
         ∗ ([∗ list] a ∈ callee_stk_region, closing_resources interp W C a (WInt 0))
         ∗ sts_full_world W C
         (* Continuation *)
         ∗ interp_cont W C
         ∗ cstack_frag cstk
         ∗ na_own logrel_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  Global Instance interp_cont_exec_ne n :
    Proper (dist n ==> dist n ==> dist n) (interp_cont_exec).
  Proof.
    intros interp interp0 Heq K K0 HK.
    rewrite /interp_cont_exec. intros ????. simpl.
    (* do 10 f_equiv;[|apply HK]. *)
    do 22 f_equiv; auto;[apply Heq|].
    do 9 f_equiv; auto.
    by apply closing_resources_ne.
  Qed.

  Definition interp_callee_part_of_the_stack
    (interp : V) (W : WORLD) ( C : CmptName ) (wstk : Word)
    (with_register_save_area : bool)
    : iProp Σ :=
    match wstk with
    | WCap p g b e a =>
        let b_callee := if with_register_save_area then b else (a^+4)%a in
        interp W C (WCap p g b_callee e a)
    | _ => True
    end.

  Program Fixpoint interp_cont (interp : V) (cstk : CSTK) : K :=
    match cstk with
    | [] => λne (W : WORLD) (C : leibnizO CmptName), True%I
    | frm :: cstk' =>
        λne (W : WORLD) (C : leibnizO CmptName),
        (▷ (
             (* Continuation for the rest of the call-stack *)
             interp_cont interp cstk' W C
             (* The callee stack frame must be safe, because we use the old copy of the stack to clear the stack *)
             ∗ interp_callee_part_of_the_stack interp W C frm.(wstk) frm.(is_untrusted_caller)
             (* The continuation when matching the switcher's state at return-to-caller *)
             ∗ (∀ W', ⌜related_sts_pub_world W W'⌝
                      -∗  interp_cont_exec interp (interp_cont interp cstk') cstk' W' C frm)))%I
    end.
  Solve All Obligations with solve_proper.

  Global Instance interp_continuation_ne (* (interp : V) stk *) n :
    Proper (dist n ==> (=) ==> dist n ==> dist n) (interp_cont).
  Proof.
    intros interp interp0 Heq x y -> W W0 ->.
    generalize dependent W0. clear W.
    induction y;intros W0;[simpl;f_equiv|].
    destruct a.
    intros ?.
    simpl.
    f_equiv.
    f_equiv;[apply IHy|].
    f_equiv;[| repeat (f_equiv; auto)].
    rewrite /interp_callee_part_of_the_stack.
    destruct wstk0; auto.
    destruct sb ; auto.
    apply Heq.
  Qed.

  Definition exec_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e : Addr)
    (cstk : CSTK) (wstk : Word)
    (interp : V) : iProp Σ :=
    (∀ (a : Addr) (W' : WORLD),
       ⌜a ∈ₐ [[ b , e ]]⌝
       → future_world g W W'
       → ▷ interp_expr interp (interp_cont interp cstk) cstk W' C (WCap p g b e a) wstk)%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof.
    solve_proper_prepare.
    do 17 (f_equiv; try done).
    by (do 3 f_equiv).
    apply interp_continuation_ne; eauto.
  Qed.
  Global Instance exec_cond_contractive W C cstk b e g p wstk :
    Contractive (λ interp, exec_cond W C b e g p cstk wstk interp).
  Proof.
    intros ????. rewrite /exec_cond.
    do 6 f_equiv.
    apply later_contractive.
    { inversion H. constructor. intros.
      apply dist_later_lt in H0.
      apply interp_expr_ne;auto. intros ?.
      apply interp_continuation_ne;auto. }
    Qed.

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
    1,2: f_equiv;apply interp_continuation_ne; auto.
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
                    if is_switcher_entry_point w
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
    (* Qed. *)
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
    (* Qed. *)
  Admitted. (* TODO holds, but very loooong *)

  Lemma fixpoint_interp1_eq (W : WORLD) (C : CmptName) (w : leibnizO Word) :
    fixpoint (interp1) W C w ≡ interp1 (fixpoint (interp1)) W C w.
  Proof. exact: (fixpoint_unfold (interp1) W C w). Qed.

  Program Definition interp : V := (fixpoint (interp1)).
  Solve All Obligations with solve_proper.
  Definition interp_continuation (cstk : CSTK) : K := interp_cont interp cstk.
  Definition interp_expression : E :=
    λne cstk, interp_expr interp (interp_continuation cstk) cstk.
  Definition interp_registers : R := interp_reg interp.

  Lemma interp_continuation_eq (cstk : CSTK) (W : WORLD) (C : CmptName) (w : leibnizO Word) :
    interp_continuation cstk W C ≡ interp_cont (fixpoint interp1) cstk W C.
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

  (* Lemma read_allowed_inv' (W : WORLD) (C : CmptName) (a b e: Addr) p g l : *)
  (*   readAllowed p → *)
  (*   Forall (fun a' : Addr => (b <= a' < e)%a ) l -> *)
  (*   ⊢ (interp W C (WCap p g b e a)) → *)
  (*   [∗ list] a' ∈ l, *)
  (*         ( *)
  (*           ∃ (p' : Perm) (P:V), *)
  (*             ⌜ PermFlowsTo p p'⌝ *)
  (*             ∗ ⌜persistent_cond P⌝ *)
  (*             ∗ rel C a' p' (safeC P) *)
  (*             ∗ ▷ zcond P C *)
  (*             ∗ ▷ rcond P C p' interp *)
  (*             ∗ (if writeAllowed p' then (▷ wcond P C interp) else True) *)
  (*             ∗ monoReq W C a' p' P *)
  (*         ). *)
  (* Proof. *)
  (*   induction l; iIntros (Hra Hin) "#Hinterp"; first done. *)
  (*   simpl. *)
  (*   apply Forall_cons in Hin. destruct Hin as [Hin_a0 Hin]. *)
  (*   iDestruct (read_allowed_inv _ _ a0 with "Hinterp") *)
  (*     as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hrcond_P & Hwcond_P & HmonoV)" *)
  (*   ; auto. *)
  (*   iFrame "%#". *)
  (*   iApply (IHl with "Hinterp"); eauto. *)
  (* Qed. *)

  (* Lemma read_allowed_inv_full_cap (W : WORLD) (C : CmptName) (a b e: Addr) p g : *)
  (*   readAllowed p → *)
  (*   ⊢ (interp W C (WCap p g b e a)) → *)
  (*   [∗ list] a' ∈ (finz.seq_between b e), *)
  (*         ( *)
  (*           ∃ (p' : Perm) (P:V), *)
  (*             ⌜ PermFlowsTo p p'⌝ *)
  (*             ∗ ⌜persistent_cond P⌝ *)
  (*             ∗ rel C a' p' (safeC P) *)
  (*             ∗ ▷ zcond P C *)
  (*             ∗ ▷ rcond P C p' interp *)
  (*             ∗ (if writeAllowed p' then (▷ wcond P C interp) else True) *)
  (*             ∗ monoReq W C a' p' P *)
  (*         ). *)
  (* Proof. *)
  (*   iIntros (Hra) "Hinterp". *)
  (*   iApply (read_allowed_inv' with "Hinterp"); eauto. *)
  (*   apply Forall_forall. *)
  (*   intros a' Ha'. *)
  (*   by apply elem_of_finz_seq_between. *)
  (* Qed. *)

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

  Lemma readAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a a':
    readAllowed p = true ->
    withinBounds b e a' = true ->
    interp W C (WCap p g b e a) -∗
    ⌜∃ ρ, std W !! a' = Some ρ ∧ ρ <> Revoked⌝.
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
