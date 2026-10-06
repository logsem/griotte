From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From griotte Require Export griotte_lang memory_region.
From iris.algebra Require Export gmap agree auth excl_auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From griotte Require Export rules call_stack_binary.
From griotte Require Export memory_region_binary seal_store_binary region_invariants_binary.
From griotte Require Export world_ghost_theory_binary.
Import uPred.

Ltac auto_equiv :=
  (* Deal with "pointwise_relation" *)
  repeat lazymatch goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  end;
  (* Normalize away equalities. *)
  repeat match goal with
  | H : _ ≡{_}≡ _ |-  _ => apply (discrete_iff _ _ _) in H
  | H : _ ≡ _ |-  _ => apply leibniz_equiv in H
  | _ => progress simplify_eq
  end;
  (* repeatedly apply congruence lemmas and use the equalities in the hypotheses. *)
  try (f_equiv; fast_done || auto_equiv).

Ltac solve_proper ::= (repeat intros ?; simpl; auto_equiv).

(** * Binary logical relation

    [interp W C (w1, w2)] states that the word [w1] of the implementation run
    and the word [w2] of the specification run are related, i.e., safe to share
    with an untrusted compartment [C] in world [W].

    The relation is the diagonal, except for sealed words: two sealed words
    with the same otype are related when their payloads are related by the
    predicate associated to the otype in the seal store, and have the same
    locality (the locality of a sealed payload is observable through
    [canStore]). *)
Section logrel.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  (** Unary-shaped predicates, used for the diagonal cases of [interp]. *)
  Notation Vd := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTKP -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Reg * Reg)) -n> iPropO Σ).
  Implicit Types ww : (leibnizO (Word * Word)).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation safeC P :=
    (λ WCv : WORLD * CmptName * (leibnizO (Word * Word)), P WCv.1.1 WCv.1.2 WCv.2).

  Program Definition safeUC (P : WORLD * CmptName * leibnizO (Word * Word) → iPropO Σ) : V :=
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

  Definition spec_registers_pointsto (r : Reg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↣ᵣ w)%I.

  Definition full_map (reg : Reg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.

  (** [interp_reg] relates the register file of the implementation run
      with the register file of the specification run. *)
  Program Definition interp_reg (interp : V) : R :=
    λne (W : WORLD) (C : CmptName) (regs : leibnizO (Reg * Reg)),
      (full_map regs.1 ∧ full_map regs.2 ∧
       ∀ (r : RegName) (v1 v2 : Word),
         (⌜r ≠ PC⌝ → ⌜regs.1 !! r = Some v1⌝ → ⌜regs.2 !! r = Some v2⌝ → interp W C (v1, v2)))%I.
  Solve All Obligations with solve_proper.

  (** The configuration is safe if, whenever the implementation halts, the
      specification run can halt as well. *)
  Definition interp_conf (W : WORLD) (C : CmptName) : iProp Σ :=
    (WP Seq (Instr Executable)
       {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})%I.

  (** [frame_match] expresses that the pair of call stacks [stk], the stack of
      worlds [Ws] and compartments [Cs] match with the current world [W] and
      compartment [C].

      It follows the same principle as in the unary model: the matching only
      happens within a chain of untrusted calls. The caller-callee
      relationship is read on the implementation frame; the condition
      [cframe_pair_cond] (part of the continuation relation) ensures that it
      coincides with the one of the specification frame whenever an untrusted
      compartment is involved.
   *)
  Fixpoint frame_match
    (Ws : list WORLD) (Cs : list CmptName) (stk : cstack_pair) (W : WORLD) (C : CmptName)
    : Prop :=
    match Ws,Cs,stk with
    | W' :: Ws', C' :: Cs', frm :: stk' =>
        related_sts_pub_world W' W
        ∧ C = C'
        ∧ is_known_to_known_frm frm.1 = false
        ∧ (if (is_untrusted_caller_frm frm.1) then frame_match Ws' Cs' stk' W C else True)
    | [], [] , []=> True
    | _,_,_ => False
    end.

  Lemma frame_match_mono
    (Ws : list WORLD) (Cs : list CmptName) (stk : cstack_pair) (W W' : WORLD) ( C : CmptName ) :
    related_sts_pub_world W W' ->
    frame_match Ws Cs stk W C ->
    frame_match Ws Cs stk W' C.
  Proof.
    revert Ws Cs.
    induction stk as [|frm stk]; intros Ws Cs Hrelated Hfrm.
    - destruct Ws,Cs; cbn in *; try done.
    - destruct Ws,Cs; cbn in *; try done.
      destruct Hfrm as (Hrelated' & <- & is_not_known_to_known & IHframe).
      split;[|split;[|split] ]; auto.
      + eapply related_sts_pub_trans_world; eauto.
      + destruct (is_untrusted_caller_frm frm.1); last done.
        by apply IHstk.
  Qed.

  (** [interp_expr] is the expression relation.
      Both runs start executing from related program counters [wpc],
      with related register files, the implementation registers owned by the
      implementation points-to, the specification registers owned by the
      specification points-to, and the specification thread [⤇] ready to
      execute. *)
  Program Definition interp_expr (interp : V) (interp_cont : K) : E :=
    (λne (W : WORLD) (C : CmptName) (wpc : leibnizO (Word * Word)),
       ∀ stk Ws Cs regs1 regs2,
       ( spec_ctx
        ∗ interp_reg interp W C (regs1, regs2)
        ∗ registers_pointsto (<[PC:=wpc.1]> regs1)
        ∗ spec_registers_pointsto (<[PC:=wpc.2]> regs2)
        ∗ ⤇ Seq (Instr Executable)
        ∗ world_interp W C
        ∗ interp_cont stk Ws Cs
        ∗ na_own cerise_nais ⊤
        ∗ cstack_frag (map fst stk)
        ∗ cstack_frag_spec (map snd stk)
        ∗ ⌜frame_match Ws Cs stk W C⌝
          -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.

  Global Instance interp_expr_ne n :
    Proper (dist n ==> dist n ==> dist n) (interp_expr).
  Proof.
    intros interp interp0 Heq K K0 HK.
    rewrite /interp_expr. intros ???. simpl.
    by repeat f_equiv.
  Qed.

  (* Condition definitions *)
  (** [zcond] states that if the safety predicate [P] holds for some pair of
      integers in some world, then it holds for this pair in any world. *)
  Definition zcond (P : V) (C : CmptName) : iProp Σ :=
    (□ ∀ (W1 W2: WORLD) (z1 z2 : Z), P W1 C (WInt z1, WInt z2) -∗ P W2 C (WInt z1, WInt z2)).
  Global Instance zcond_ne n :
    Proper ((=) ==> (=) ==> dist n) zcond.
  Proof. solve_proper_prepare.
         repeat f_equiv;auto. Qed.
  Global Instance zcond_contractive (P : V) (C : CmptName) :
    Contractive (λ interp, ▷ zcond P C)%I.
  Proof. solve_contractive. Qed.

  (** [rcond] states that the safety predicate [P] implies [interp],
      after loading both words with permission [p]. *)
  Definition rcond (P : V) (C : CmptName) (p : Perm) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word * Word), P W C w -∗ interp W C (load_word p w.1, load_word p w.2)).
  Global Instance rcond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) rcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance rcond_contractive (P : V) (C : CmptName) (p : Perm) :
    Contractive (λ interp, ▷ rcond P C p interp)%I.
  Proof. solve_contractive. Qed.

  (** [wcond] states that [interp] implies the safety predicate [P]. *)
  Definition wcond (P : V) (C : CmptName) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : Word * Word), interp W C w -∗ P W C w).
  Global Instance wcond_ne n :
    Proper ((=) ==> (=)  ==> dist n ==> dist n) wcond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance wcond_contractive (P : V) (C : CmptName) :
    Contractive (λ interp, ▷ wcond P C interp)%I.
  Proof. solve_contractive. Qed.

  (** [persistent_cond] states that the safety predicate [P] is persistent. *)
  Definition persistent_cond (P:V) := (∀ WCv, Persistent (P WCv.1.1 WCv.1.2  WCv.2)).

  (** [valid_stk_interp] is a predicate stating that the safety predicate [φ]
      is a safety predicate for the stack (RWL capability). *)
  Definition valid_stk_interp (interp : V) (C : CmptName) (φ : V) (p : Perm) : iProp Σ :=
    mono_pub C (safeC φ) ∗
    zcond φ C ∗
    rcond φ C p interp ∗
    wcond φ C interp ∗
    ⌜ persistent_cond φ ⌝.
  Global Instance valid_interp_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) valid_stk_interp.
  Proof. rewrite /valid_stk_interp; solve_proper. Qed.

  (** [StackWorldResource] keeps track of the safety resources of a stack
      address [a] containing the pair of words [w]. It does not own the
      points-to predicates. *)
  Definition StackWorldResource (interp : V) (W : WORLD) (C : CmptName) (a : Addr) (w : Word * Word)
    : iProp Σ :=
    ∃ (φ : V) (p : Perm),
      φ W C w ∗
      mono_temporary C p (safeC φ) w ∗
      rel C a p (safeC φ) ∗
      valid_stk_interp interp C φ p ∗
      ⌜ PermFlowsTo RWL p ⌝.
  Global Instance StackWorldResource_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackWorldResource.
  Proof. rewrite /StackWorldResource; solve_proper. Qed.
  Global Instance StackWorldResource_Persistent
    (interp : V) (W : WORLD) (C : CmptName) (a : Addr) (v : Word * Word) :
    Persistent (StackWorldResource interp W C a v).
  Proof.
    assert ( forall interp W C a v,
               StackWorldResource interp W C a v ⊣⊢
                 (
                   (∃ (φ : V) (p : Perm) (_ : Persistent (φ W C v)),
                       ((φ W C v)
                        ∗ (mono_temporary C p (safeC φ) v)
                        ∗ rel C a p (safeC φ)
                        ∗ valid_stk_interp interp C φ p
                        ∗ ⌜ PermFlowsTo RWL p ⌝
                       )%I
                   )
                 )) as Heq; last (rewrite Heq; apply _).
    rewrite /StackWorldResource.
    intros.
    iSplit; [iIntros "(%&%&?&?&?&(?&?&?&?&%Hpers)&?)" | iIntros "(%&%&%&?&?&?&(?&?&?&?&?)&?)"]; iFrame.
    pose proof (Hpers (W0,C0,v0)) as H'; iExists H'; done.
  Qed.

  (** [StackWorldResources] keeps track of the safety resources of the stack
      region [la], containing the words [lw1] in the implementation memory and
      the words [lw2] in the specification memory. *)
  Definition StackWorldResources (interp : V) (W : WORLD) (C : CmptName)
    (la : list Addr) (lw1 lw2 : list Word) : iProp Σ :=
    ⌜ length lw1 = length lw2 ⌝ ∗
    ([∗ list] a ; v ∈ la ; zip lw1 lw2, StackWorldResource interp W C a v).
  Global Instance StackWorldResources_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackWorldResources.
  Proof. rewrite /StackWorldResources; solve_proper. Qed.
  Global Instance StackWorldResources_Persistent
    (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lv1 lv2 : list Word) :
    Persistent (StackWorldResources interp W C la lv1 lv2).
  Proof. apply _. Qed.

  (** [StackOpenWorldResources] additionally owns the fragmental view of the
      world for the stack region. It is obtained by opening a shared stack
      region, and is used to close it later. *)
  Definition StackOpenWorldResources (interp : V) (W : WORLD) (C : CmptName)
    (la : list Addr) (lw1 lw2 : list Word) : iProp Σ :=
    StackWorldResources interp W C la lw1 lw2 ∗ ([∗ list] a ∈ la, sts_state_std C a Temporary).
  Global Instance StackOpenWorldResources_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackOpenWorldResources.
  Proof. rewrite /StackOpenWorldResources; solve_proper; by apply StackWorldResources_ne. Qed.

  (** [interp_cont_exec] provides a WP rule for the continuation relation.
      It matches the states of both machines at the point where the switcher
      returns to the caller, after popping the pair of frames [frm].

      The stack bounds and the caller-callee relationship are read from the
      implementation frame [frm.1]; they coincide with the ones of the
      specification frame (see [cframe_pair_cond]). The callee-saved registers
      are restored on each side from its own frame. The return values in [ca0]
      and [ca1] are related. All other registers contain zero on both sides.

      The stack contents are universally quantified, separately for each run:
      [stk_mem_l] and [stk_mem_h] in the implementation memory,
      [stk_mem_l_spec] and [stk_mem_h_spec] in the specification memory.
   *)
  Program Definition interp_cont_exec (interp : V) (interp_cont : iProp Σ) :
    (CSTKP -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO (cframe * cframe)) -n> iPropO Σ)
    :=
    (λne (stk : CSTKP) (W : WORLD) (C : CmptName) (frm : leibnizO (cframe * cframe))
     ,
       ∀ (wca0 wca1 : Word * Word) (regs : Reg)
         (stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec : list Word),
       let frm1 := frm.1 in
       let frm2 := frm.2 in
       let b_stk := frm1.(b_stk) in
       let a_stk := frm1.(a_stk) in
       let e_stk := frm1.(e_stk) in
       let astk4 := (a_stk ^+4)%a in
       let callee_stk_region :=
         finz.seq_between (if (is_untrusted_caller_frm frm1) then a_stk else astk4) e_stk in
       let callee_stk_mem :=
         if (is_untrusted_caller_frm frm1) then stk_mem_l++stk_mem_h else stk_mem_h in
       let callee_stk_mem_spec :=
         if (is_untrusted_caller_frm frm1) then stk_mem_l_spec++stk_mem_h_spec else stk_mem_h_spec in
       ( spec_ctx
         ∗ PC ↦ᵣ updatePcPerm frm1.(wret)
         ∗ PC ↣ᵣ updatePcPerm frm2.(wret)
         ∗ cra ↦ᵣ frm1.(wret)
         ∗ cra ↣ᵣ frm2.(wret)
         ∗ csp ↦ᵣ (WCap RWL Local b_stk e_stk a_stk)
         ∗ csp ↣ᵣ (WCap RWL Local b_stk e_stk a_stk)
         (* cgp, cs0 and cs1 are callee-saved registers *)
         ∗ cgp ↦ᵣ frm1.(wcgp)
         ∗ cgp ↣ᵣ frm2.(wcgp)
         ∗ cs0 ↦ᵣ frm1.(wcs0)
         ∗ cs0 ↣ᵣ frm2.(wcs0)
         ∗ cs1 ↦ᵣ frm1.(wcs1)
         ∗ cs1 ↣ᵣ frm2.(wcs1)
         (* ca0 and ca1 are the return value *)
         ∗ ca0 ↦ᵣ wca0.1
         ∗ ca0 ↣ᵣ wca0.2
         ∗ interp W C wca0
         ∗ ca1 ↦ᵣ wca1.1
         ∗ ca1 ↣ᵣ wca1.2
         ∗ interp W C wca1
         (* all other register contain 0 *)
         ∗ ⌜dom regs = all_registers_s ∖ {[PC; cra ; cgp; csp; cs0; cs1 ; ca0; ca1]}⌝
         ∗ ( [∗ map] r↦w ∈ regs, r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
         (* points-to predicate of the stack region *)
         ∗ [[ a_stk , astk4 ]] ↦ₐ [[ stk_mem_l ]]
         ∗ [[ a_stk , astk4 ]] ↣ₐ [[ stk_mem_l_spec ]]
         ∗ [[ astk4 , e_stk ]] ↦ₐ [[ stk_mem_h ]]
         ∗ [[ astk4 , e_stk ]] ↣ₐ [[ stk_mem_h_spec ]]
         (* World interpretation *)
         ∗ world_interp_open W C callee_stk_region
         (* Bookkeeping resources for the opened world *)
         ∗ StackOpenWorldResources interp W C callee_stk_region callee_stk_mem callee_stk_mem_spec
         (* Continuation *)
         ∗ interp_cont
         ∗ cstack_frag (map fst stk)
         ∗ cstack_frag_spec (map snd stk)
         ∗ ⤇ Seq (Instr Executable)
         ∗ na_own cerise_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.
  Global Instance interp_cont_exec_ne n :
    Proper (dist n ==> dist n ==> dist n) (interp_cont_exec).
  Proof. solve_proper; by apply StackOpenWorldResources_ne. Qed.

  (** [interp_callee_part_of_the_stack] interprets the stack pointer of the
      caller [wstk] (see the unary model). Stack pointers are the same in both
      runs whenever an untrusted compartment is involved. *)
  Definition interp_callee_part_of_the_stack
    (interp : V) (W : WORLD) ( C : CmptName ) (wstk : Word)
    (is_untrusted_caller : bool)
    : iProp Σ :=
    match wstk with
    | WCap p g b e a =>
        let a4 := (a^+4)%a in
        let b_callee := if is_untrusted_caller then b else a4 in
        interp W C (WCap p g b_callee e a, WCap p g b_callee e a)
    | _ => True
    end.


  (** [interp_cont] is the continuation relation, over pairs of frames.
      Each pair of frames satisfies [cframe_pair_cond]. The body of the
      continuation is only enforced if the caller-callee relation involves
      an untrusted compartment. *)
  Program Fixpoint interp_cont_aux (interp : V) (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    : iProp Σ :=
    match stk, Ws, Cs with
    | [],[],[] => True%I
    | frm :: stk', Wt :: Ws', Ct :: Cs' =>
        (* Continuation for the rest of the call-stack *)
        interp_cont_aux interp stk' Ws' Cs' ∗
        ⌜ cframe_pair_cond frm ⌝ ∗
        (if is_known_to_known_frm frm.1
         then True%I
         else
           ((* The callee stack frame must be safe, because we use the old copy of the stack to clear the stack *)
             interp_callee_part_of_the_stack interp Wt Ct
               (WCap RWL Local frm.1.(b_stk) frm.1.(e_stk) frm.1.(a_stk)) (is_untrusted_caller_frm frm.1)
             (* The continuation when matching the switcher's state at return-to-caller *)
             ∗ (∀ W', ⌜related_sts_pub_world Wt W'⌝
                      -∗  interp_cont_exec interp (interp_cont_aux interp stk' Ws' Cs') stk' W' Ct frm)))%I
    | _,_,_ =>  False%I
    end.
  Solve All Obligations with ( solve_proper; split; intros ; (intros [?  [] ]; done) ).
  Global Instance interp_cont_aux_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) (interp_cont_aux).
  Proof.
    intros interp interp0 Heq x y -> W W0 -> C C0 ->.
    generalize dependent W0.
    generalize dependent C0.
    induction y; intros C0 W0;[simpl;f_equiv|].
    destruct a, W0, C0; cbn -[interp_cont_exec]; [auto|auto|auto|].
    f_equiv; [apply IHy|].
    f_equiv.
    destruct (is_known_to_known_frm c); first done.
    f_equiv; [apply Heq|].
    f_equiv; intros W'.
    f_equiv.
    apply interp_cont_exec_ne; [done|apply IHy].
  Qed.

  Program Definition interp_cont (interp : V) : K :=
    (λne (stk : CSTKP) (Ws : list WORLD) (Cs : leibnizO (list CmptName)),
       interp_cont_aux interp stk Ws Cs
    ).
  Solve All Obligations with solve_proper.
  Global Instance interp_cont_ne n :
    Proper (dist n ==> dist n) (interp_cont).
  Proof. solve_proper. Qed.

  (** Execute condition of the logical relation *)
  Definition exec_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e : Addr)
    (interp : V) : iProp Σ :=
    (∀ (a : Addr) (W' : WORLD),
       ⌜a ∈ₐ [[ b , e ]]⌝
       → future_world g W W'
       → ▷ interp_expr interp (interp_cont interp) W' C (WCap p g b e a, WCap p g b e a))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof.
    solve_proper_prepare.
    solve_proper.
  Qed.
  Global Instance exec_cond_contractive W C b e g p :
    Contractive (λ interp, exec_cond W C b e g p interp).
  Proof.
    intros ????. rewrite /exec_cond.
    do 6 f_equiv.
    apply later_contractive.
    { inversion H. constructor. intros.
      apply dist_later_lt in H0.
      apply interp_expr_ne;auto.
      apply interp_cont_ne;auto. }
    Qed.

  (** Enter condition of the logical relation. *)
  Definition enter_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr)
    (interp : V) : iProp Σ :=
    (∀ W',
       future_world g W W'
       → (∀ g', ⌜ LocalityFlowsTo g' g ⌝ →
                (▷ interp_expr interp (interp_cont interp) W' C (WCap p g' b e a, WCap p g' b e a)))
    )%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof.
    solve_proper_prepare.
    solve_proper.
  Qed.
  Global Instance enter_cond_contractive W C p g b e a :
    Contractive (λ interp, enter_cond W C p g b e a interp).
  Proof.
    intros ????. rewrite /enter_cond.
    do 6 f_equiv.
    apply later_contractive.
    inversion H. constructor. intros.
    apply dist_later_lt in H0.
    apply interp_expr_ne;auto.
    apply interp_cont_ne;auto.
  Qed.

  (** * Definitions interp *)

  (** Interp of the world state

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

  (** [monoReq] gives the monotonicity requirements of the pairs of words that
      can be stored through a capability with permission [p]. *)
  Definition monoReq (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (P : V) :=
    (match (std W) !! a with
        | Some Temporary =>
            (if isWL p
             then mono_pub C (safeC P)
             else (if isDL p then mono_pub C (safeC P) else mono_priv C (safeC P) p))
        | Some Permanent => mono_priv C (safeC P) p
        | _ => True
        end)%I.

  (** Interp for sentry in [enter_cond]. *)
  Program Definition interp_sentry (interp : V) : Vd :=
    λne W C w, (match w with
                | WSentry p g b e a => □ enter_cond W C p g b e a interp
                | _ => False
                end)%I.
  Solve All Obligations with solve_proper.

  (** Interp for memory capability. *)
  Program Definition interp_cap (interp : V) : Vd :=
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

  (** Interp for sealing capability. *)
  Program Definition interp_sr (interp : V) : Vd :=
    λne W C w, (match w with
    | WSealRange p g b e a =>
    (if permit_seal p then safe_to_seal W C interp b e else True)
    ∗ (if permit_unseal p then safe_to_unseal W C interp b e else True)
    | _ => False end ) %I.
  Solve All Obligations with solve_proper.

  (** Interp for a pair of sealed words with the same otype [o]:
      the payloads are related by the predicate of [o], before and after
      borrowing, and have the same locality. *)
  Definition interp_sb (W : WORLD) (C : CmptName) (o : OType) (sb1 sb2 : Sealable) : iProp Σ :=
    (∃ (P : V) ,
        ⌜persistent_cond P⌝
        ∗ (∀ w, future_priv_mono C (safeC P) w)
        ∗ seal_pred o (safeC P)
        ∗ ⌜isLocalSealable sb1 = isLocalSealable sb2⌝
        ∗ ▷ P W C (WSealable sb1, WSealable sb2)
        ∗ ▷ P W C (borrow (WSealable sb1), borrow (WSealable sb2))
    )%I.

  (** Diagonal part of the relation, on a single word. *)
  Definition interp1_diag (interp : V) (W : WORLD) (C : CmptName) (w : Word) : iProp Σ :=
    match w with
    | WInt _ => True
    | WCap (O _ _) g b e a => True
    | WCap _ g b e a => interp_cap interp W C w
    | WSentry p g b e a => interp_sentry interp W C w
    | WSealRange p g b e a => interp_sr interp W C w
    | WSealed _ _ => False
    end%I.

  (** Definition of interp, pre-fixpoint. *)
  Definition interp1_pair (interp : V) (W : WORLD) (C : CmptName) (w1 w2 : Word) : iProp Σ :=
    match w1, w2 with
    | WSealed o1 sb1, WSealed o2 sb2 => ⌜o1 = o2⌝ ∗ interp_sb W C o1 sb1 sb2
    | w1, w2 => ⌜w1 = w2⌝ ∗ interp1_diag interp W C w1
    end%I.

  Program Definition interp1 (interp : V) : V :=
    (λne W C (ww : leibnizO (Word * Word)), interp1_pair interp W C ww.1 ww.2)%I.
  Solve All Obligations with solve_proper.

  (** To be able to use the fixpoint combinator to define [interp],
      we need to show that all case of [interp] are contractive. *)
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

  Lemma interp1_diag_contractive n (x y : V) W C w :
    dist_later n x y →
    interp1_diag x W C w ≡{n}≡ interp1_diag y W C w.
  Proof.
    intros Hdistn.
    rewrite /interp1_diag.
    destruct_word w; [auto|..].
    + destruct c; first auto.
      destruct rx,w,dl,dro.
      par: try done.
      par: by apply interp_cap_contractive.
    + by apply interp_sr_contractive.
    + by apply interp_sentry_contractive.
    + done.
  Qed.

  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn W C [w1 w2].
    rewrite /interp1 /interp1_pair /=.
    destruct w1; try (f_equiv; by apply interp1_diag_contractive).
    destruct w2; try (f_equiv; by apply interp1_diag_contractive).
  Qed.

  (** Definition of [interp] via the fixpoint combinator. *)
  Lemma fixpoint_interp1_eq (W : WORLD) (C : CmptName) (ww : leibnizO (Word * Word)) :
    fixpoint (interp1) W C ww ≡ interp1 (fixpoint (interp1)) W C ww.
  Proof. exact: (fixpoint_unfold (interp1) W C ww). Qed.

  Program Definition interp : V := (fixpoint (interp1)).
  Solve All Obligations with solve_proper.
  Definition interp_continuation : K := interp_cont interp.
  Program Definition interp_expression : E :=
    interp_expr interp interp_continuation.
  Definition interp_registers : R := interp_reg interp.

  Lemma interp_continuation_eq :
    interp_continuation ≡ interp_cont (fixpoint interp1).
  Proof. rewrite /interp_continuation /interp /= //. Qed.

  (** We have, and we _WANT_, [interp] to be Persistent *)
  Global Instance interp_persistent W C ww : Persistent (interp W C ww).
  Proof.
    destruct ww as [w1 w2].
    rewrite /interp fixpoint_interp1_eq /= /interp1_pair.
    destruct w1 as [ z | sb | p g b e a | o1 sb1 ].
    1-3: apply bi.sep_persistent; first apply _.
    1-3: rewrite /interp1_diag.
    - apply _.
    - destruct sb as [ c g b e a | sr g b e a ]; cbn.
      + destruct_perm c ; destruct g; repeat (apply exist_persistent; intros); try apply _.
      + destruct (permit_seal sr), (permit_unseal sr); rewrite /safe_to_seal /safe_to_unseal; apply _ .
    - apply _.
    - destruct w2 as [ | | | o2 sb2 ]; try apply _.
      apply bi.sep_persistent; first apply _.
      rewrite /interp_sb.
      apply exist_persistent; intros P.
      unfold Persistent. iIntros "(%Hpers & #Hmono & #Hs & %Hloc & HP & HPborrowed)".
      iAssert (<pers> ▷ P W C (WSealable sb1, WSealable sb2))%I with "[ HP ]" as "HP".
      { iApply later_persistently_1.
        ospecialize (Hpers (W,C,_)); cbn in Hpers.
        by iApply persistent_persistently_2.
      }
      iAssert (<pers> ▷ P W C (borrow (WSealable sb1), borrow (WSealable sb2)))%I
        with "[ HPborrowed ]" as "HPborrowed".
      { iApply later_persistently_1.
        ospecialize (Hpers (W,C,_)); cbn in Hpers.
        by iApply persistent_persistently_2.
      }
      iApply persistently_sep_2; iSplitR; auto.
      iApply persistently_sep_2; iSplitR; auto; iFrame "Hs".
      iApply persistently_sep_2; iSplitR; auto.
      iApply persistently_sep_2;iFrame.
  Qed.

  (* Non-curried version of interp *)
  Notation interpC := (safeC interp).

  Lemma interp_int W C z : ⊢ interp W C (WInt z, WInt z).
  Proof. iIntros. rewrite /interp fixpoint_interp1_eq //. Qed.

  (** ** Inversion lemmas: related words are equal, unless they are sealed *)

  Lemma interp_eq_unless_sealed (W : WORLD) (C : CmptName) (w1 w2 : Word) :
    interp W C (w1, w2) -∗
    ⌜ w1 = w2 ∨ ∃ o sb1 sb2, w1 = WSealed o sb1 ∧ w2 = WSealed o sb2 ⌝.
  Proof.
    iIntros "Hinterp".
    rewrite /interp fixpoint_interp1_eq /= /interp1_pair.
    destruct w1 as [ | | | o1 sb1 ].
    1-3: by iDestruct "Hinterp" as "[-> _]"; iLeft.
    destruct w2 as [ | | | o2 sb2 ].
    1-3: by iDestruct "Hinterp" as "[-> _]"; iLeft.
    iDestruct "Hinterp" as "[-> _]".
    iRight; iPureIntro; eauto.
  Qed.

  Lemma interp_eq_not_sealed (W : WORLD) (C : CmptName) (w1 w2 : Word) :
    is_sealed w1 = false →
    interp W C (w1, w2) -∗ ⌜ w1 = w2 ⌝.
  Proof.
    iIntros (Hsealed) "Hinterp".
    iDestruct (interp_eq_unless_sealed with "Hinterp") as "[$|(%o & %sb1 & %sb2 & -> & ->)]".
    done.
  Qed.

  Lemma interp_eq_not_sealed_r (W : WORLD) (C : CmptName) (w1 w2 : Word) :
    is_sealed w2 = false →
    interp W C (w1, w2) -∗ ⌜ w1 = w2 ⌝.
  Proof.
    iIntros (Hsealed) "Hinterp".
    iDestruct (interp_eq_unless_sealed with "Hinterp") as "[$|(%o & %sb1 & %sb2 & -> & ->)]".
    done.
  Qed.

  Lemma interp_sealed_inv (W : WORLD) (C : CmptName) (o1 o2 : OType) (sb1 sb2 : Sealable) :
    interp W C (WSealed o1 sb1, WSealed o2 sb2) ⊣⊢
    ⌜ o1 = o2 ⌝ ∗ interp_sb W C o1 sb1 sb2.
  Proof. by rewrite /interp fixpoint_interp1_eq /= /interp1_pair. Qed.

  (** Related words have the same locality *)
  Lemma interp_isLocalWord (W : WORLD) (C : CmptName) (w1 w2 : Word) :
    interp W C (w1, w2) -∗ ⌜ isLocalWord w1 = isLocalWord w2 ⌝.
  Proof.
    iIntros "#Hinterp".
    iDestruct (interp_eq_unless_sealed with "Hinterp") as "[->|(%o & %sb1 & %sb2 & -> & ->)]"
    ; first done.
    rewrite interp_sealed_inv.
    iDestruct "Hinterp" as "[_ (%P & _ & _ & _ & %Hloc & _)]".
    done.
  Qed.

  Lemma interp_canStore (W : WORLD) (C : CmptName) (p : Perm) (w1 w2 : Word) :
    interp W C (w1, w2) -∗ ⌜ canStore p w1 = canStore p w2 ⌝.
  Proof.
    iIntros "Hinterp".
    iDestruct (interp_isLocalWord with "Hinterp") as "%Hloc".
    by rewrite /canStore Hloc.
  Qed.

  (** Related words have the same shape: integers *)
  Lemma interp_int_inv (W : WORLD) (C : CmptName) (z : Z) (w2 : Word) :
    interp W C (WInt z, w2) -∗ ⌜ w2 = WInt z ⌝.
  Proof.
    iIntros "Hinterp".
    by iDestruct (interp_eq_not_sealed with "Hinterp") as "<-".
  Qed.

  Lemma interp1_eq interp (W: WORLD) (C : CmptName) p g b e a:
    ((interp1 interp W C (WCap p g b e a, WCap p g b e a)) ≡
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
    rewrite /interp1 /= /interp1_pair /interp1_diag.
    iSplit.
    { iIntros "[_ HA]".
      destruct (isO p) eqn:HnotO; subst; auto.
      destruct p; cbn.
      destruct rx ; destruct w ; try (cbn in HnotO ; congruence); auto.
      all: destruct g ;auto ; try (iSplit;eauto).
      all: try (iApply (big_sepL_mono with "HA"); intros k a' ?; iIntros "H").
      all: try (iDestruct "H" as (p' P Hflp' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a')").
      all: try (iExists p',P ; iFrame "#∗"; repeat (iSplit;[done|];done)).
    }
    { iIntros "A".
      iSplit; first done.
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

  (** Unfolding [interp] on the diagonal of a non-sealed word *)
  Lemma interp_diag_eq (W : WORLD) (C : CmptName) (w : Word) :
    is_sealed w = false →
    interp W C (w, w) ⊣⊢ interp1_diag interp W C w.
  Proof.
    intros Hsealed.
    rewrite /interp fixpoint_interp1_eq /= /interp1_pair.
    destruct w; try done.
    all: iSplit; [iIntros "[_ $]" | iIntros "$"; done].
  Qed.

  (* Inversion lemmas about about when R-capability *)
  Lemma readAllowed_valid_cap (W : WORLD) (C : CmptName) p g b e a':
    readAllowed p = true ->
    interp W C (WCap p g b e a', WCap p g b e a') -∗
    ⌜Forall (fun a => ∃ ρ, std W !! a = Some ρ ∧ ρ <> Revoked) (finz.seq_between b e)⌝.
  Proof.
    iIntros (Hwa) "Hinterp".
    rewrite Forall_forall.
    iIntros (a Ha).
    apply elem_of_finz_seq_between in Ha.
    rewrite /interp; cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply readAllowed_nonO in Hwa ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
      as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    iPureIntro.
    destruct (isWL p); simplify_eq.
    + naive_solver.
    + destruct g; naive_solver.
  Qed.

  Lemma read_allowed_inv (W : WORLD) (C : CmptName) (a' a b e: Addr) p g :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp W C (WCap p g b e a, WCap p g b e a)) →
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
    ⊢ (interp W C (WCap p g b e a, WCap p g b e a)) →
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
    ⊢ (interp W C (WCap p g b e a, WCap p g b e a)) →
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
    interp W C (WCap p g b e a, WCap p g b e a) -∗
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
    ⊢ (interp W C (WCap p g b e a, WCap p g b e a)) →
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
    ⊢ (interp W C (WCap p g b e a, WCap p g b e a)) →
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
    ⊢ (interp W C (WCap p g b e a, WCap p g b e a)) →
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
    interp W C (WCap p g b e a, WCap p g b e a) -∗
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
    interp W C (WCap p g b e a', WCap p g b e a') -∗
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
    interp W C (WCap p g b e a', WCap p g b e a') -∗
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
    ⊢ (interp W C (WCap p g b e a, WCap p g b e a)) →
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
    ⊢ (interp W C (WCap p g b e a, WCap p g b e a)) →
    [∗ list] a' ∈ (finz.seq_between b e), ⌜std W !! a' = Some Temporary⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iApply (writeLocalAllowed_valid_cap_implies_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  Lemma writeLocalAllowed_implies_local (W : WORLD) (C : CmptName) p g b e a:
    isWL p = true -> interp W C (WCap p g b e a, WCap p g b e a) -∗ ⌜ isLocal g = true ⌝.
  Proof.
    intros. iIntros "Hvalid".
    unfold interp; rewrite fixpoint_interp1_eq /= /interp1_pair /interp1_diag.
    iDestruct "Hvalid" as "[_ Hvalid]".
    destruct_perm p; simpl in H; try congruence; destruct g; auto.
  Qed.

  Lemma interp_in_registers
    (W : WORLD) (C : CmptName)
    (regs1 regs2 : Reg) (p : Perm) (g : Locality) (b e a : Addr):
      interp_reg interp W C (regs1, regs2)
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
        ∗ (if decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs1) a)
            then ▷ (rcond P C p' interp)
            else emp)
        ∗ (if decide (writeAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs1) a)
            then ▷ wcond P C interp
            else emp)
        ∗ monoReq W C a p' P
        ∗ ⌜if isWL p then region_state_pwl W a else region_state_nwl W a g⌝
       ).
  Proof.
    iIntros "#(_ & %Hfull2 & Hreg) #H".
    iDestruct "H" as (p0 P0 Hflp0 Hperscond_P0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0 & HmonoR0 & %Hstate0)".
    iExists p0,P0.
    iFrame "%#".
    iSplit.
    - (* rcond *)
      destruct (decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs1) a))
        as [Hra'|Hra']; auto.
      destruct (readAllowed p0) eqn:Hra; auto.
      destruct Hra' as (r & w & Hsome & Hrar & Hvw).
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert_eq in Hsome; simplify_eq.
        eapply readAllowed_flowsto in Hrar; eauto.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      destruct (Hfull2 r) as [w2 Hw2].
      iDestruct ("Hreg" $! r w w2 n Hsome Hw2) as "Hinterp_w".
      destruct_word w; cbn in * ; try done.
      destruct Hvw as [Hvw ->].
      iDestruct (interp_eq_not_sealed with "Hinterp_w") as "<-"; first done.
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
      destruct (decide (writeAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs1) a))
        as [Hwa'|Hwa']; auto.
      destruct (writeAllowed p0) eqn:Hwa; auto.
      destruct Hwa' as (r & w & Hsome & Hwaw & Hvw).
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert_eq in Hsome; simplify_eq.
        eapply writeAllowed_flowsto in Hwaw; eauto.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      destruct (Hfull2 r) as [w2 Hw2].
      iDestruct ("Hreg" $! r w w2 n Hsome Hw2) as "Hinterp_w".
      destruct_word w; cbn in * ; try done.
      destruct Hvw as [Hvw ->].
      iDestruct (interp_eq_not_sealed with "Hinterp_w") as "<-"; first done.
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

Notation safeC P :=
  (λ WCv : WORLD * CmptName * (leibnizO (Word * Word)), P WCv.1.1 WCv.1.2 WCv.2).
Notation interpC := (safeC interp).
