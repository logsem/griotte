From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export cap_lang memory_region seal_store region_invariants.
From iris.algebra Require Export gmap agree auth excl_auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine Require Import rules_base.
From cap_machine Require Export call_stack.
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
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  Notation E := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

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

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Program Definition interp_reg (interp : V) : R :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO Reg),
      (full_map reg ∧
       ∀ (r : RegName) (v : Word), (⌜r ≠ PC⌝ → ⌜reg !! r = Some v⌝ → interp W C v))%I.
  Solve All Obligations with solve_proper.

  Definition interp_conf (W : WORLD) (C : CmptName) : iProp Σ :=
    (WP Seq (Instr Executable)
       {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.

  (** [frame_match] expresses that the call stack [cstk], the stack of worlds [Ws] and compartments [Cs],
      match with the current world [W] and compartment [C].

      When the switcher pushes/pops a stack frame, it also pushes/pops
      the current world and compartment together.

      It is necessary because the continuation relation is monotonic with public
      transitions only.
      Without this feature, when a user receives a world [W]
      (and it's corresponding continuation relation) from a caller,
      calling the switcher requires to give a world [W'] together with the
      corresponding continuation relation.
      But because the continuation relation is monotonic with public transition only,
      it would forbid the user to take private transitions
      (which usually happen, because the user revokes the world for taking control
      of its own stack frame).

      With the [frame_match] criteria, the user can take private transition during
      the duration of their call, and calling the switcher pushed the world
      into the stack of world [Ws] (done by the switcher).
      When the user return, they have to show that they end up in a
      public future world [W'] of the caller's world [W].
      It has to be public transition (and not equality), because the world
      can evolve publicly during an adversary's call.

      Finally, this matching only happens within a "chain of untrusted calls",
      because as soon as we hit a trusted caller, the chain of public world
      can be broken by a private transition taken by the user
      (which they'll have to prove public when returning).

      The compartment's name is an equality, because untrusted (physical) compartments
      that can call each others are considered as a unique logical compartment.
   *)
  Fixpoint frame_match
    (Ws : list WORLD) (Cs : list CmptName) (cstk : CSTK) (W : WORLD) (C : CmptName)
    : Prop :=
    match Ws,Cs,cstk with
    | W' :: Ws', C' :: Cs', frm :: cstk' =>
        related_sts_pub_world W' W
        ∧ C = C'
        ∧ (if frm.(is_untrusted_caller) then frame_match Ws' Cs' cstk' W C else True)
    | [], [] , []=> True
    | _,_,_ => False
    end.

  Lemma frame_match_mono
    (Ws : list WORLD) (Cs : list CmptName) (cstk : CSTK) (W W' : WORLD) ( C : CmptName ) :
    related_sts_pub_world W W' ->
    frame_match Ws Cs cstk W C ->
    frame_match Ws Cs cstk W' C.
  Proof.
    revert Ws Cs.
    induction cstk as [|frm cstk]; intros Ws Cs Hrelated Hfrm.
    - destruct Ws,Cs; cbn in *; try done.
    - destruct Ws,Cs; cbn in *; try done.
      destruct Hfrm as (Hrelated' & <- & IH).
      split;[|split]; auto.
      + eapply related_sts_pub_trans_world; eauto.
      + destruct (is_untrusted_caller frm); last done.
        by apply IHcstk.
  Qed.

  Program Definition interp_expr (interp : V) (interp_cont : K) : E :=
    (λne (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (W : WORLD) (C : CmptName) (wpc : Word),
       ∀ regs,
       ( interp_reg interp W C regs
        ∗ registers_pointsto (<[PC:=wpc]> regs)
        ∗ region W C
        ∗ sts_full_world W C
        ∗ interp_cont
        ∗ na_own logrel_nais ⊤
        ∗ cstack_frag cstk
        ∗ ⌜frame_match Ws Cs cstk W C⌝
          -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  Global Instance interp_expr_ne n :
    Proper (dist n ==> dist n ==> dist n) (interp_expr).
  Proof.
    intros interp interp0 Heq K K0 HK.
    rewrite /interp_expr. intros ??????. simpl.
    by repeat f_equiv.
  Qed.

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
      ∗ ⌜ isDRO p = false ⌝
      ∗ ⌜ isDL p = false ⌝
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
       ∗ ⌜ isDRO p = false ⌝
       ∗ ⌜ isDL p = false ⌝
       ∗ ⌜ forall Wv, Persistent (φ Wv) ⌝
      )%I.

  Global Instance closing_resources_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) closing_resources.
  Proof.
    intros interp interp0 Heq ????????????.
    rewrite /closing_resources.
    repeat (f_equiv; auto).
  Qed.

  (** [interp_cont_exec] provides a WP rule for the continuation relation.
      It matches the states of the machine at the point where the switcher returns to the caller.

      [interp_cont_exec] is somewhat the dual of [execute_entry_point]:
      - [interp_cont_exec] matches the state of the machine after the execution of return-to-switcher
      - [execute_entry_point] matches the state of the machine after the execution of call-switcher

      The state of the machine should:
      - [PC] points-to the caller's site
      - the callee-saved registers of the topmost call-frame [frm] are restored in their
        original registers
      - [ca0] and [ca1] contain some return values, [interp] in the current world
      - all the other registers have been clear and point to zero
      - the stack is given back, with some universally content (1) [stk_mem_l]
        and [stk_mem_h].
      - [stk_mem_h] corresponds to the callee's stack frame.
        It is shared with the caller, and therefore part of the standard world.
      - [stk_mem_l] corresponds the part of the stack used by the switcher to save the callee-save registers.
        When the caller is untrusted, the points-to have been shared with the callee,
        and therefore stored in the region invariant.
        When the caller is trusted, they are not shared with the callee,
        and therefore _not_ stored in the region invariant.
      - The region invariant is returned, but open to have the points-to of the stack region out.
      - Because the region invariant is open, we need to give the user a way to close the region invariant.
        That's the role of the resources [closing_resources interp W C a v].
      - Finally, we have the [interp_cont] of the (depoped) stack frame (we don't see it in this def,
        but we see it in the definition of [interp_cont] later),
        and the fragmental view of the call-stack [cstk].

    (1) Although we know it should contain zeroes due to the clearing during the return routine,
        it is logically hard to prove in the functional specification because the world
        given by the (known) user is revoked. Which means that we need to
        re-instate the world, together with keeping it open to keep track of its content.
        I think it should work, but the infrastructure for this case doesn't exist,
        and we don't lose anything to have the content universally quantified.
   *)
  Program Definition interp_cont_exec (interp : V) (interp_cont : K) :
    (CSTK -n> WORLD  -n> (leibnizO CmptName) -n> (leibnizO cframe) -n> iPropO Σ)
    :=
    (λne (cstk : CSTK) (W : WORLD) (C : CmptName) (frm : cframe)
     ,
       ∀ wca0 wca1 regs a_stk e_stk stk_mem_l stk_mem_h,
       let astk4 := (a_stk ^+4)%a in
       let callee_stk_region := finz.seq_between (if frm.(is_untrusted_caller) then a_stk else astk4) e_stk in
       let callee_stk_mem := if frm.(is_untrusted_caller) then stk_mem_l++stk_mem_h else stk_mem_h in
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
         ∗ ( [∗ map] r↦w ∈ regs, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
         (* points-to predicate of the stack region *)
         ∗ ⌜ get_a frm.(wstk) = Some a_stk ⌝
         ∗ ⌜ get_e frm.(wstk) = Some e_stk ⌝
         ∗ [[ a_stk , astk4 ]] ↦ₐ [[ stk_mem_l ]]
         ∗ [[ astk4 , e_stk ]] ↦ₐ [[ stk_mem_h ]]
         (* World interpretation *)
         ∗ open_region_many W C callee_stk_region
         ∗ ([∗ list] a ; v ∈ callee_stk_region ; callee_stk_mem, closing_resources interp W C a v)
         ∗ sts_full_world W C
         (* Continuation *)
         ∗ interp_cont
         ∗ cstack_frag cstk
         ∗ na_own logrel_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  Global Instance interp_cont_exec_ne n :
    Proper (dist n ==> dist n ==> dist n) (interp_cont_exec).
  Proof. solve_proper. Qed.

  (** [interp_callee_part_of_the_stack] interprets the stack pointer of the caller [wstk].
      When a caller calls the switcher-call routine with a capability [WCap p g b e a] in the [csp]
      register, the switcher is using the region `[a,a+4)` for as callee-saved registers area,
      and giving the region `[a+4,e)` as callee-stack frame.

      If the caller is trusted, the callee-saved registers area is expected to be solely accessed by the switcher,
      sharing in fact only the region `[a+4,e)` with the caller.

      If the caller is untrusted, there are no guarantees that the caller won't share its entire stack frame
      with the callee, through one of the arguments.
      In that case, we need to capture the worst possible case, i.e., the caller is sharing all its stack frame,
      making in fact the entire caller's stack pointer [interp].
      This is specifically important in the [ftlr_switcher_call],
      where we don't have any information about the registers,
      and so the points-to predicate of the callee-saved registers are in the region invariant.
   *)
  Definition interp_callee_part_of_the_stack
    (interp : V) (W : WORLD) ( C : CmptName ) (wstk : Word)
    (is_untrusted_caller : bool)
    : iProp Σ :=
    match wstk with
    | WCap p g b e a =>
        let a4 := (a^+4)%a in
        let b_callee := if is_untrusted_caller then b else a4 in
        interp W C (WCap p g b_callee e a)
    | _ => True
    end.


  (** [interp_cont] is the continuation relation.
      It takes a call-stack [cstk], a list of world [Ws] and a list of compartments [Cs],
      all of same size.
      All together, they keep track of the stack of continuations.
      [interp_cont] contains 3 components:
      - the recursive part of the definition, stating that the rest of the stack is also part of the continuation
      - safety of the stack callee stack pointer
      - [interp_cont_exec], which provides a WP rule for the continuation,
        matching the machine state after the return-to-caller
   *)
  Program Fixpoint interp_cont (interp : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) : K :=
    match cstk, Ws, Cs with
    | [],[],[] => True%I
    | frm :: cstk', Wt :: Ws', Ct :: Cs' =>
        (▷ (
             (* Continuation for the rest of the call-stack *)
             interp_cont interp cstk' Ws' Cs'
             (* The callee stack frame must be safe, because we use the old copy of the stack to clear the stack *)
             ∗ interp_callee_part_of_the_stack interp Wt Ct frm.(wstk) frm.(is_untrusted_caller)
             (* The continuation when matching the switcher's state at return-to-caller *)
             ∗ (∀ W', ⌜related_sts_pub_world Wt W'⌝
                      -∗  interp_cont_exec interp (interp_cont interp cstk' Ws' Cs') cstk' W' Ct frm)))%I
    | _,_,_ =>  False%I
    end.
  Solve All Obligations with ( solve_proper; split; intros ; (intros [?  [] ]; done) ).

  Global Instance interp_cont_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) (interp_cont).
  Proof.
    intros interp interp0 Heq x y -> W W0 -> C C0 ->.
    generalize dependent W0.
    generalize dependent C0.
    induction y; intros C0 W0;[simpl;f_equiv|].
    destruct a, W0, C0;simpl; [auto|auto|auto|].
    simpl.
    f_equiv.
    f_equiv;[apply IHy|].
    f_equiv;[| repeat (f_equiv; auto)].
    rewrite /interp_callee_part_of_the_stack.
    destruct wstk; auto.
    destruct sb ; auto.
    apply Heq.
  Qed.

  Definition exec_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e : Addr)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (interp : V) : iProp Σ :=
    (∀ (a : Addr) (W' : WORLD),
       ⌜a ∈ₐ [[ b , e ]]⌝
       → future_world g W W'
       → ▷ interp_expr interp (interp_cont interp cstk Ws Cs) cstk Ws Cs W' C (WCap p g b e a))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof.
    solve_proper_prepare.
    do 17 (f_equiv; try done).
    by (do 3 f_equiv).
  Qed.
  Global Instance exec_cond_contractive W C cstk Ws Cs b e g p :
    Contractive (λ interp, exec_cond W C b e g p cstk Ws Cs interp).
  Proof.
    intros ????. rewrite /exec_cond.
    do 6 f_equiv.
    apply later_contractive.
    { inversion H. constructor. intros.
      apply dist_later_lt in H0.
      apply interp_expr_ne;auto.
      apply interp_cont_ne;auto. }
    Qed.

  Definition enter_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr)
    (interp : V) : iProp Σ :=
    (∀ stk Ws Cs W',
       future_world g W W'
       → (∀ g', ⌜ LocalityFlowsTo g' g ⌝ → (▷ interp_expr interp (interp_cont interp stk Ws Cs) stk Ws Cs W' C (WCap p g' b e a)))
    )%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof.
    solve_proper_prepare.
    do 21 f_equiv;[by repeat f_equiv|..].
    apply interp_cont_ne; auto.
  Qed.

  Global Instance enter_cond_contractive W C p g b e a :
    Contractive (λ interp, enter_cond W C p g b e a interp).
  Proof.
    intros ????. rewrite /enter_cond.
    do 12 f_equiv.
    apply later_contractive.
    inversion H. constructor. intros.
    apply dist_later_lt in H0.
    apply interp_expr_ne;auto.
    apply interp_cont_ne;auto.
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

  (* For simplicity we might want to have the following statement in validity of caps.
     However, it is strictly not necessary since it can be derived form full_sts_world *)

  Definition monoReq (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (P : V) :=
    (match (std W) !! a with
        | Some Temporary =>
            (if isWL p
             then mono_pub C (safeC P)
             else (if isDL p then mono_pub C (safeC P) else mono_priv C (safeC P) p))
        | Some Permanent => mono_priv C (safeC P) p
        | _ => True
        end)%I.

  Definition interp_z : V := λne _ _ w, ⌜match w with WInt z => True | _ => False end⌝%I.
  Definition interp_cap_O : V := λne _ _ _, True%I.

  Program Definition interp_sentry (interp : V) : V :=
    λne W C w, (match w with
                | WSentry p g b e a => □ enter_cond W C p g b e a interp
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
    solve_proper_prepare.
    destruct_word x2; auto.
    destruct c ; auto.
    destruct rx,w,g; auto.
    par: solve_contractive.
  Qed.

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
    intros n x y Hdistn W C w.
    rewrite /interp1.
    destruct_word w; [auto|..].
    + destruct c; first auto.
      destruct rx,w,dl,dro.
      par: try (by apply interp_cap_O_contractive).
      par: by apply interp_cap_contractive.
    + by apply interp_sr_contractive.
    + by apply interp_sentry_contractive.
    + rewrite /interp_sb; solve_contractive.
    Qed.

  Lemma fixpoint_interp1_eq (W : WORLD) (C : CmptName) (w : leibnizO Word) :
    fixpoint (interp1) W C w ≡ interp1 (fixpoint (interp1)) W C w.
  Proof. exact: (fixpoint_unfold (interp1) W C w). Qed.

  Program Definition interp : V := (fixpoint (interp1)).
  Solve All Obligations with solve_proper.
  Definition interp_continuation
    (cstk : CSTK) (Ws : list WORLD) (Cs : leibnizO (list CmptName)) : K
    := interp_cont interp cstk Ws Cs.
  Program Definition interp_expression : E :=
    λne cstk Ws Cs, interp_expr interp (interp_continuation cstk Ws Cs) cstk Ws Cs.
  Solve Obligations with solve_proper.
  Definition interp_registers : R := interp_reg interp.

  Lemma interp_continuation_eq
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (w : leibnizO Word) :
    interp_continuation cstk Ws Cs ≡ interp_cont (fixpoint interp1) cstk Ws Cs.
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
    iSplit.
    { iIntros "HA".
      destruct (isO p) eqn:HnotO; subst; auto.
      destruct p; cbn.
      destruct rx ; destruct w ; try (cbn in HnotO ; congruence); auto.
      all: destruct g ;auto ; try (iSplit;eauto).
      all: try (iApply (big_sepL_mono with "HA"); intros k a' ?; iIntros "H").
      all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a')").
      all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)).
    }
    { iIntros "A".
      destruct (isO p) eqn:HnotO; subst; auto.
      { destruct_perm p ; cbn in *;auto;try congruence. }
      destruct (has_sreg_access p) eqn:HnotXSR; subst; auto.
      iDestruct "A" as "(A & %)".
      destruct_perm p; cbn in HnotO,HnotXSR; try congruence; auto.
      all: destruct g eqn:Hg; simplify_eq ; eauto ; cbn.
      all: try (iApply (big_sepL_mono with "A"); intros; iIntros "H").
      all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a')").
      all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)).
    }
  Qed.


  (* Inversion lemmas about interp  *)
  (* Inversion lemmas about about when R-capability *)
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

  Lemma read_allowed_inv_many (W : WORLD) (C : CmptName) (a b e: Addr) p g l :
    readAllowed p →
    Forall (fun a' : Addr => (b <= a' < e)%a ) l ->
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ l,
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then (▷ wcond P C interp) else True)
              ∗ monoReq W C a' p' P
          ).
  Proof.
    induction l; iIntros (Hra Hin) "#Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin. destruct Hin as [Hin_a0 Hin].
    iDestruct (read_allowed_inv _ _ a0 with "Hinterp")
      as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hrcond_P & Hwcond_P & HmonoV)"
    ; auto.
    iFrame "%#".
    iApply (IHl with "Hinterp"); eauto.
  Qed.

  Lemma read_allowed_inv_full_cap (W : WORLD) (C : CmptName) (a b e: Addr) p g :
    readAllowed p →
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ (finz.seq_between b e),
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then (▷ wcond P C interp) else True)
              ∗ monoReq W C a' p' P
          ).
  Proof.
    iIntros (Hra) "Hinterp".
    iApply (read_allowed_inv_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
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

  (* Inversion lemmas about about when W-capability *)
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

  Lemma write_allowed_inv_many (W : WORLD) (C : CmptName) (a b e: Addr) p g l :
    writeAllowed p →
    Forall (fun a' : Addr => (b <= a' < e)%a ) l ->
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ l,
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ (if readAllowed p' then (▷ rcond P C p' interp) else True)
              ∗ (▷ wcond P C interp)
              ∗ monoReq W C a' p' P
          ).
  Proof.
    induction l; iIntros (Hra Hin) "#Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin. destruct Hin as [Hin_a0 Hin].
    iDestruct (write_allowed_inv _ _ a0 with "Hinterp")
      as (p' P) "(%Hperm_flow & %Hpers_P & Hrel_P & Hzcond_P & Hrcond_P & Hwcond_P & HmonoV)"
    ; auto.
    iFrame "%#".
    iApply (IHl with "Hinterp"); eauto.
  Qed.

  Lemma write_allowed_inv_full_cap (W : WORLD) (C : CmptName) (a b e: Addr) p g :
    writeAllowed p →
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ (finz.seq_between b e),
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C a' p' (safeC P)
              ∗ ▷ zcond P C
              ∗ (if readAllowed p' then (▷ rcond P C p' interp) else True)
              ∗ (▷ wcond P C interp)
              ∗ monoReq W C a' p' P
          ).
  Proof.
    iIntros (Hra) "Hinterp".
    iApply (write_allowed_inv_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
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

  (* Inversion lemmas about about when WL-capability *)
  Lemma writeLocalAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a a':
    isWL p = true ->
    withinBounds b e a = true ->
    interp W C (WCap p g b e a') -∗
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

  Lemma writeLocalAllowed_valid_cap_implies_many (W : WORLD) (C : CmptName) p g b e a l:
    isWL p = true ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) l ->
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ l, ⌜std W !! a' = Some Temporary⌝.
  Proof.
    induction l; iIntros (Hra Hin) "#Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin; destruct Hin as [Hin_a0 Hin].
    iDestruct (writeLocalAllowed_valid_cap_implies with "Hinterp") as "$"; auto.
    { rewrite /withinBounds; solve_addr. }
    iApply (IHl with "Hinterp"); eauto.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies_full_cap (W : WORLD) (C : CmptName) p g b e a:
    isWL p = true ->
    ⊢ (interp W C (WCap p g b e a)) →
    [∗ list] a' ∈ (finz.seq_between b e), ⌜std W !! a' = Some Temporary⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iApply (writeLocalAllowed_valid_cap_implies_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  Lemma writeLocalAllowed_implies_local (W : WORLD) (C : CmptName) p g b e a:
    isWL p = true -> interp W C (WCap p g b e a) -∗ ⌜ isLocal g = true ⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /=.
    destruct_perm p; simpl in H; try congruence; destruct g; auto.
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

End logrel.
