From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From griotte Require Export griotte_lang memory_region region_invariants sealing_invariants.
From iris.algebra Require Export gmap agree auth excl_auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From griotte Require Export rules call_stack.
From griotte Require Export world_ghost_theory.
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

(** interp : is a unary logical relation. *)
Section logrel.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation safeC P :=
    (λ WCv : WORLD * CmptName * (leibnizO LWord), P WCv.1.1 WCv.1.2 WCv.2).

  Program Definition safeUC (P : WORLD * CmptName * leibnizO LWord → iPropO Σ) : V :=
    λne a b c, P (a, b, c).
  Solve All Obligations with solve_proper.

  (* -------------------------------------------------------------------------------- *)

  (* Future world relation *)
  Definition future_world (g : Locality) (W W' : WORLD) : iProp Σ :=
    (match g with
     | Local => ⌜related_sts_pub_world W W'⌝
     | Global => ⌜related_sts_priv_world W W'⌝
     end)%I.


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
  Definition registers_pointsto (r : LReg) : iProp Σ :=
    ([∗ map] r↦w ∈ r, r ↦ᵣ w)%I.

  Definition full_map (reg : LReg) : iProp Σ := (∀ (r : RegName), ⌜is_Some (reg !! r)⌝)%I.
  Program Definition interp_reg (interp : V) : R :=
    λne (W : WORLD) (C : CmptName) (reg : leibnizO LReg),
      (full_map reg ∧
       ∀ (r : RegName) (v : LWord), (⌜r ≠ PC⌝ → ⌜reg !! r = Some v⌝ → interp W C v))%I.
  Solve All Obligations with solve_proper.

  Definition interp_conf (W : WORLD) (C : CmptName) : iProp Σ :=
    (WP Seq (Instr Executable)
       {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.

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
        ∧ is_known_to_known_frm frm = false
        ∧ (if (is_untrusted_caller_frm frm) then frame_match Ws' Cs' cstk' W C else True)
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
      destruct Hfrm as (Hrelated' & <- & is_not_known_to_known & IHframe).
      split;[|split;[|split] ]; auto.
      + eapply related_sts_pub_trans_world; eauto.
      + destruct (is_untrusted_caller_frm frm); last done.
        by apply IHcstk.
  Qed.

  Program Definition interp_expr (interp : V) (interp_cont : K) : E :=
    (λne (W : WORLD) (C : CmptName) (wpc : LWord),
       ∀ cstk Ws Cs regs,
       ( interp_reg interp W C regs
        ∗ registers_pointsto (<[PC:=wpc]> regs)
        ∗ world_interp W C
        ∗ interp_cont cstk Ws Cs
        ∗ na_own cerise_nais ⊤
        ∗ cstack_frag cstk
        ∗ ⌜frame_match Ws Cs cstk W C⌝
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

  (** The Load filter as the world sees it. A word with heap authority and an
      identifier [ι] loads untagged once the world has [ι] Quarantined;
      every other word loads unchanged. The lookup is by the word's
      identifier, not by address (D5, D21). *)
  Definition filter_heap (W : WORLD) (w : LWord) : LWord :=
    match heap_authority_base w.(lw), w.(lprov) with
    | Some _, Some ι =>
        match heap_std W !! ι with
        | Some o =>
            match alloc_object_status o with
            | AllocObjectLive => w
            | AllocObjectQuarantined => lclear_tag w
            end
        | None => w
        end
    | _, _ => w
    end.

  Lemma filter_heap_nonheap W w :
    heap_authority_base w.(lw) = None -> filter_heap W w = w.
  Proof. intros Hw. by rewrite /filter_heap Hw. Qed.

  Lemma filter_heap_noid W w :
    w.(lprov) = None -> filter_heap W w = w.
  Proof. intros Hw. rewrite /filter_heap Hw. by destruct (heap_authority_base _). Qed.

  Lemma filter_heap_live W w ι o :
    w.(lprov) = Some ι ->
    heap_std W !! ι = Some o ->
    alloc_object_status o = AllocObjectLive -> filter_heap W w = w.
  Proof.
    intros Hι Hlookup Hstatus. rewrite /filter_heap Hι Hlookup Hstatus.
    by destruct (heap_authority_base _).
  Qed.

  Lemma filter_heap_quarantined W w b ι o :
    heap_authority_base w.(lw) = Some b ->
    w.(lprov) = Some ι ->
    heap_std W !! ι = Some o ->
    alloc_object_status o = AllocObjectQuarantined -> filter_heap W w = lclear_tag w.
  Proof. intros Hb Hι Hlookup Hstatus. by rewrite /filter_heap Hb Hι Hlookup Hstatus. Qed.

  Lemma filter_heap_result W w :
    filter_heap W w = w ∨ filter_heap W w = lclear_tag w.
  Proof.
    rewrite /filter_heap. destruct (heap_authority_base _) as [b|]; last by left.
    destruct (lprov w) as [ι|]; last by left.
    destruct (heap_std W !! ι) as [o|]; last by left.
    destruct (alloc_object_status o); [by left | by right].
  Qed.

  (** The filter strips a tag only from a quarantined identifier's word with
      authority. *)
  Lemma filter_heap_cleared W w :
    filter_heap W w ≠ w ->
    ∃ b ι o, heap_authority_base w.(lw) = Some b ∧ w.(lprov) = Some ι ∧
             heap_std W !! ι = Some o ∧ alloc_object_status o = AllocObjectQuarantined.
  Proof.
    rewrite /filter_heap. intros Hne.
    destruct (heap_authority_base _) as [b|]; last done.
    destruct (lprov w) as [ι|]; last done.
    destruct (heap_std W !! ι) as [o|] eqn:Ho; last done.
    destruct (alloc_object_status o) eqn:Hs; first done. eauto 10.
  Qed.

  Lemma filter_heap_untagged W w :
    get_tag w.(lw) = false -> filter_heap W w = w.
  Proof.
    intros Htag. destruct (filter_heap_result W w) as [-> | ->]; first done.
    by apply lclear_tag_untagged.
  Qed.

  Lemma filter_heap_lclear_tag W w :
    filter_heap W (lclear_tag w) = lclear_tag w.
  Proof. apply filter_heap_untagged. rewrite lw_lclear_tag. apply get_tag_clear_tag. Qed.

  (** A saved register has the result of a Load in the current world.
      The load outcome depends on the shadow, while the second conjunct
      records the world fact needed when its tag is retained. *)
  Definition load_heap_in_world (W : WORLD) (saved actual : LWord) : Prop :=
    load_heap saved actual ∧ filter_heap W actual = actual.

  Lemma load_heap_in_world_nonheap W saved actual :
    is_heap_cap saved.(lw) = false ->
    load_heap_in_world W saved actual -> actual = saved.
  Proof. intros Hnonheap [Hloaded _]. exact (load_heap_nonheap saved actual Hnonheap Hloaded). Qed.

  Definition interp_in_mem_pre
    (W : WORLD) (C : CmptName) (p : Perm) (interp : V) (w : LWord) : iProp Σ :=
    interp W C (filter_heap W (lload_word p w)).

  Global Instance interp_in_mem_pre_ne W C p w :
    NonExpansive (λ interp, interp_in_mem_pre W C p interp w).
  Proof. intros n x y Hxy. apply Hxy. Qed.

  Global Instance interp_in_mem_pre_contractive W C p w :
    Contractive (λ interp, ▷ interp_in_mem_pre W C p interp w)%I.
  Proof. rewrite /interp_in_mem_pre. solve_contractive. Qed.

  (* Condition definitions *)
  (** [zcond] states that if the safety predicate [P] is safe for some integer in some world,
      then this integer is safe in any worlds.
      We don't have simply [□ ∀ W z, P W C (WInt z)], because for RO capabilities,
      we might not have [P W C (WInt z)] !
   *)
  Definition zcond (P : V) (C : CmptName) : iProp Σ :=
    (□ ∀ (W1 W2: WORLD) (z : Z), P W1 C (WInt z) -∗ P W2 C (WInt z)).
    (* (□ ∀ (W1 W2: WORLD) (z : Z), P W1 C (WInt z) -∗ P W2 C (WInt z)). *)
  Global Instance zcond_ne n :
    Proper ((=) ==> (=) ==> dist n) zcond.
  Proof. solve_proper_prepare.
         repeat f_equiv;auto. Qed.
  Global Instance zcond_contractive (P : V) (C : CmptName) :
    Contractive (λ interp, ▷ zcond P C)%I.
  Proof. solve_contractive. Qed.

  (** [rcond] states that stored values satisfying [P] are safe after the
      deep-permission load filter and the current world's heap revocation filter. *)
  Definition rcond (P : V) (C : CmptName) (p : Perm) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : LWord), P W C w -∗ interp_in_mem_pre W C p interp w).
  Global Instance rcond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> dist n ==> dist n) rcond.
  Proof. rewrite /rcond /interp_in_mem_pre. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance rcond_contractive (P : V) (C : CmptName) (p : Perm) :
    Contractive (λ interp, ▷ rcond P C p interp)%I.
  Proof. rewrite /rcond /interp_in_mem_pre. solve_contractive. Qed.

  (** [wcond] states that [interp] implies the safety predicate [P].
      It comes from the fact that storing in memory consists of storing
      a value that is safe to share, but we need to store a value respecting [P]. *)
  Definition wcond (P : V) (C : CmptName) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : LWord), interp W C w -∗ P W C w).
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

  (** [StackWorldResource] keeps track of the safety resources of a stack address [a] containing word [w].
      Note that it does not own the points-to predicate (a ↦ₐ w). *)
  Definition StackWorldResource (interp : V) (W : WORLD) (C : CmptName) (a : Addr) (w : LWord) : iProp Σ :=
    ∃ (φ : V) (p : Perm),
      φ W C w ∗
      mono_temporary C p (safeC φ) w ∗
      rel C (LNonHeap a) p (safeC φ) ∗
      valid_stk_interp interp C φ p ∗
      ⌜ PermFlowsTo RWL p ⌝.
  Global Instance StackWorldResource_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackWorldResource.
  Proof. rewrite /StackWorldResource; solve_proper. Qed.
  Global Instance StackWorldResource_Persistent
    (interp : V) (W : WORLD) (C : CmptName) (a : Addr) (v : LWord) :
    Persistent (StackWorldResource interp W C a v).
  Proof.
    assert ( forall interp W C a v,
               StackWorldResource interp W C a v ⊣⊢
                 (
                   (∃ (φ : V) (p : Perm) (_ : Persistent (φ W C v)),
                       ((φ W C v)
                        ∗ (mono_temporary C p (safeC φ) v)
                        ∗ rel C (LNonHeap a) p (safeC φ)
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

  (** [StackWorldResources] keeps track of the safety resources of the stack region [la] containing words [lw].

      This resources comes hand-to-hand with revoking/reinstating or opening/closing the world.
      This is mostly bookkeeping resources, and the user would usually only passes it around.
   *)
  Definition StackWorldResources (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lws : list LWord) : iProp Σ :=
    ([∗ list] a ; v ∈ la ; lws, StackWorldResource interp W C a v).
  Global Instance StackWorldResources_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackWorldResources.
  Proof. rewrite /StackWorldResources; solve_proper. Qed.
  Global Instance StackWorldResources_Persistent
    (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lv : list LWord) :
    Persistent (StackWorldResources interp W C la lv).
  Proof. apply _. Qed.

  (** [StackOpenWorldResources] keeps track of the safety resources of the stack region [la] containing words [lw],
      but also owns the fragmental view of the world for the stack region.
      This resource is obtained by opening shared stack region, and is used to reinstate it later.

      This is mostly bookkeeping resources, and the user would usually only passes it around.
   *)
  Definition StackOpenWorldResources (interp : V) (W : WORLD) (C : CmptName) (la : list Addr) (lws : list LWord) : iProp Σ :=
    StackWorldResources interp W C la lws ∗ ([∗ list] a ∈ la, sts_state_std C (LNonHeap a) Temporary).
  Global Instance StackOpenWorldResources_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) StackOpenWorldResources.
  Proof. rewrite /StackOpenWorldResources; solve_proper. Qed.

  (** [interp_cont_exec] provides a WP rule for the continuation relation.
      It matches the states of the machine at the point where the switcher returns to the caller.

      [interp_cont_exec] is somewhat the dual of [execute_entry_point]:
      - [interp_cont_exec] matches the state of the machine after the execution of return-to-switcher
      - [execute_entry_point] matches the state of the machine after the execution of call-switcher

      The state of the machine should:
      - [PC] points-to the caller's site
      - the callee-saved registers of the topmost call-frame [frm] are restored in their
        original registers, each satisfying [load_heap_in_world] for its saved word
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
  Program Definition interp_cont_exec (interp : V) (interp_cont : iProp Σ)
    :
    (CSTK -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO cframe) -n> iPropO Σ)
    :=
    (λne (cstk : CSTK) (W : WORLD) (C : CmptName) (frm : cframe)
     ,
       ∀ (rcgp rcra rcs0 rcs1 wca0 wca1 : LWord) (regs : LReg) (stk_mem_l stk_mem_h : list LWord),
       let b_stk := frm.(b_stk) in
       let a_stk := frm.(a_stk) in
       let e_stk := frm.(e_stk) in
       let astk4 := (a_stk ^+4)%a in
       let callee_stk_region := finz.seq_between (if (is_untrusted_caller_frm frm) then a_stk else astk4) e_stk in
       let callee_stk_mem := if (is_untrusted_caller_frm frm) then stk_mem_l++stk_mem_h else stk_mem_h in
       ⌜load_heap_in_world W frm.(wcgp) rcgp⌝ -∗
       ⌜load_heap_in_world W frm.(wret) rcra⌝ -∗
       ⌜load_heap_in_world W frm.(wcs0) rcs0⌝ -∗
       ⌜load_heap_in_world W frm.(wcs1) rcs1⌝ -∗
       ( PC ↦ᵣ lupdatePcPerm rcra
         ∗ cra ↦ᵣ rcra
         ∗ csp ↦ᵣ (WCap true RWL Local b_stk e_stk a_stk)
         (* cgp, cs0 and cs1 are callee-saved registers *)
         ∗ cgp ↦ᵣ rcgp
         ∗ cs0 ↦ᵣ rcs0
         ∗ cs1 ↦ᵣ rcs1
         (* ca0 and ca1 are the return value *)
         ∗ ca0 ↦ᵣ wca0 ∗ interp W C wca0
         ∗ ca1 ↦ᵣ wca1 ∗ interp W C wca1
         (* all other register contain 0 *)
         ∗ ⌜dom regs = all_registers_s ∖ {[PC; cra ; cgp; csp; cs0; cs1 ; ca0; ca1]}⌝
         ∗ ( [∗ map] r↦w ∈ regs, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
         (* points-to predicate of the stack region *)
         ∗ [[ a_stk , astk4 ]] ↦ₐ [[ stk_mem_l ]]
         ∗ [[ astk4 , e_stk ]] ↦ₐ [[ stk_mem_h ]]
         (* World interpretation *)
         ∗ world_interp_open W C (LNonHeap <$> callee_stk_region)
         (* Bookkeeping resources for the opened world *)
         ∗ StackOpenWorldResources interp W C callee_stk_region callee_stk_mem
         (* Continuation *)
         ∗ interp_cont
         ∗ cstack_frag cstk
         ∗ na_own cerise_nais ⊤
           -∗ interp_conf W C)
    )%I.
  Solve All Obligations with solve_proper.
  Global Instance interp_cont_exec_ne n :
    Proper (dist n ==> dist n ==> dist n) (fun interp cont => interp_cont_exec interp cont).
  Proof. solve_proper. Qed.

  (** [interp_callee_part_of_the_stack] interprets the stack pointer of the caller [wstk].
      When a caller calls the switcher-call routine with a capability [WCap true p g b e a] in the [csp]
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
    | WCap t p g b e a =>
        let a4 := (a^+4)%a in
        let b_callee := if is_untrusted_caller then b else a4 in
        ⌜disjoint_from_heap b_callee e⌝ ∗
        interp W C (WCap t p g b_callee e a)
    | _ => True
    end.


  (** [interp_cont] is the continuation relation.
      It takes a call-stack [cstk], a list of world [Ws] and a list of compartments [Cs], all of same size.
      All together, they keep track of the stack of continuations.
      [interp_cont] contains 3 components:
      - the recursive part of the definition, stating that the rest of the stack is also part of the continuation
      - safety of the stack callee stack pointer
      - [interp_cont_exec], which provides a WP rule for the continuation,
        matching the machine state after the return-to-caller

      Each known caller records only its pure machine frame. The continuation
      accepts the four words restored by the switcher, each related to its
      saved word by [load_heap_in_world]. Neither shadow bits nor restoration
      resources are stored here.

      Unknown callers use the logical relation on the actual words loaded
      from their shared stack. Their frame's placeholder words do not classify
      those saved words and carry no restoration obligation here.

      The "body" of continuation relation is only enforced if the caller-callee relation
      involves an unknown compartment.
   *)
  Program Fixpoint interp_cont_aux (interp : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : iProp Σ :=
    match cstk, Ws, Cs with
    | [],[],[] => True%I
    | frm :: cstk', Wt :: Ws', Ct :: Cs' =>
        (* Continuation for the rest of the call-stack *)
        interp_cont_aux interp cstk' Ws' Cs' ∗
        (if is_known_to_known_frm frm
         then True%I
         else
           ((* The callee stack frame must be safe, because we use the old copy of the stack to clear the stack *)
             interp_callee_part_of_the_stack interp Wt Ct (WCap true RWL Local frm.(b_stk) frm.(e_stk) frm.(a_stk)) (is_untrusted_caller_frm frm)
             (* The continuation when matching the switcher's state at return-to-caller *)
             ∗ (if is_untrusted_caller_frm frm then True else
                    (∀ W', ⌜related_sts_pub_world Wt W'⌝
                      -∗ interp_cont_exec interp (interp_cont_aux interp cstk' Ws' Cs')
                           cstk' W' Ct frm))))%I
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
    destruct W0 as [|Wt Ws], C0 as [|Ct Cs]; [reflexivity|reflexivity|reflexivity|].
    cbn [interp_cont_aux].
    apply bi.sep_ne; first apply IHy.
    destruct (is_known_to_known_frm a); first done.
    apply bi.sep_ne.
    { unfold interp_callee_part_of_the_stack. apply bi.sep_ne; first reflexivity. apply Heq. }
    destruct (is_untrusted_caller_frm a); first done.
    apply bi.forall_ne; intros W'.
    apply bi.wand_ne; first reflexivity.
    exact (interp_cont_exec_ne n interp interp0 Heq _ _ (IHy Cs Ws)
      y W' Ct a).
  Qed.

  Program Definition interp_cont (interp : V) : K :=
    (λne (cstk : CSTK) (Ws : list WORLD) (Cs : leibnizO (list CmptName)),
       interp_cont_aux interp cstk Ws Cs
    ).
  Solve All Obligations with solve_proper.
  Global Instance interp_cont_ne n :
    Proper (dist n ==> dist n) (interp_cont).
  Proof. solve_proper. Qed.

  (** Execute condition of the logical relation. The capability keeps the
      identifier [π] of the word it comes from. *)
  Definition exec_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e : Addr) (π : option AId)
    (interp : V) : iProp Σ :=
    (∀ (a : Addr) (W' : WORLD),
       ⌜a ∈ₐ [[ b , e ]]⌝
       → future_world g W W'
       → ▷ interp_expr interp (interp_cont interp) W' C (WCap true p g b e a @@? π))%I.
  Global Instance exec_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) exec_cond.
  Proof.
    solve_proper_prepare.
    solve_proper.
  Qed.
  Global Instance exec_cond_contractive W C b e g p π :
    Contractive (λ interp, exec_cond W C b e g p π interp).
  Proof.
    intros ????. rewrite /exec_cond.
    do 6 f_equiv.
    apply later_contractive.
    { inversion H. constructor. intros.
      apply dist_later_lt in H0.
      apply interp_expr_ne;auto.
      apply interp_cont_ne;auto. }
    Qed.

  (** Enter condition of the logical relation
      Describes that, for a sentry capability to be safe to share,
      its unsealed version must be safe to execute.

      The world must be any future world of [W], public for local and private for global,
      because the world can evolve before invoking the capability.

      The locality must be any lower locality,
      because the locality of a sentry capability can be weakened.

      The unsealed capability keeps the sentry's identifier [π].
 *)
  Definition enter_cond
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId)
    (interp : V) : iProp Σ :=
    (∀ W',
       future_world g W W'
       → (∀ g', ⌜ LocalityFlowsTo g' g ⌝ → (▷ interp_expr interp (interp_cont interp) W' C (WCap true p g' b e a @@? π)))
    )%I.
  Global Instance enter_cond_ne n :
    Proper ((=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n ==> dist n) enter_cond.
  Proof.
    solve_proper_prepare.
    solve_proper.
  Qed.
  Global Instance enter_cond_contractive W C p g b e a π :
    Contractive (λ interp, enter_cond W C p g b e a π interp).
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

  (** The region key of the address [a] of a capability with identifier [π]:
      [LHeap a ι] exactly when [π = Some ι], [LNonHeap a] otherwise. It does
      not depend on the world. *)
  Definition addr_key (π : option AId) (a : Addr) : LAddr :=
    match π with
    | Some ι => LHeap a ι
    | None => LNonHeap a
    end.

  Lemma addr_key_addr π a : laddr_addr (addr_key π a) = a.
  Proof. by destruct π. Qed.

  Lemma addr_key_None a : addr_key None a = LNonHeap a.
  Proof. done. Qed.

  Lemma addr_key_Some ι a : addr_key (Some ι) a = LHeap a ι.
  Proof. done. Qed.

  Lemma addr_key_pointsto π a v :
    addr_key π a ↦ₖ v ⊣⊢ a ↦ₐ v ∗ key_share (addr_key π a).
  Proof. by rewrite key_pointsto_eq addr_key_addr. Qed.

  Lemma addr_key_pointsto_join π a v :
    a ↦ₐ v -∗ key_share (addr_key π a) -∗ addr_key π a ↦ₖ v.
  Proof. iIntros "Ha Hs". iApply addr_key_pointsto. iFrame. Qed.

  Definition region_state_pwl (W : WORLD) (k : LAddr) : Prop :=
    (std W) !! k = Some Temporary.

  Definition region_state_nwl (W : WORLD) (k : LAddr) (l : Locality) : Prop :=
    match l with
     | Local => (std W) !! k = Some Permanent ∨ (std W) !! k = Some Temporary
     | Global => (std W) !! k = Some Permanent
    end.

  (* For simplicity we might want to have the following statement in validity of caps.
     However, it is strictly not necessary since it can be derived form [world_interp].

     NOTE I actually think that it is necessary in Griotte, for proving the FTLR,
     and in particular the Store case.

     I don't have all the details in mind, but it comes from the fact that,
     in previous versions, having [wcond] implied having [rcond],
     and having both could derive P is [interp].
     And it enabled to derive the monotonicity requirement for the stored value.

     But in Griotte, not only we don't have [wcond] -> [rcond],
     but also having both does not necessarily means that P is [interp].
     And we can't use this for deriving monotonicity of the stored value.

     Therefore, we need to have [monoReq] is the definition of the logrel,
     to derive the monotonicity requirements of any values that can be stored
     with the capability. *)

  Definition monoReq (W : WORLD) (C : CmptName) (k : LAddr) (p : Perm) (P : V) :=
    (match (std W) !! k with
        | Some Temporary =>
            (if isWL p
             then mono_pub C (safeC P)
             else (if isDL p then mono_pub C (safeC P) else mono_priv C (safeC P) p))
        | Some Permanent => mono_priv C (safeC P) p
        | _ => True
        end)%I.

  (** Interp trivially holds for integers. *)
  Definition interp_z : V := λne _ _ w, ⌜match w.(lw) with WInt z => True | _ => False end⌝%I.

  (** Heap authority belongs to the live object of the word's identifier [ι],
      whose range covers both bounds (§4.6). *)
  Definition heap_cap_live (W : WORLD) (p : Perm) (b e : Addr) (ι : AId) : Prop :=
    ∃ o, heap_std W !! ι = Some o ∧
         alloc_object_status o = AllocObjectLive ∧
         (alloc_object_base o <= b)%a ∧ (e <= alloc_object_end o)%a ∧
         executeAllowed p = false ∧ isWL p = false.

  (** Empty and reversed ordinary capabilities carry no memory authority.
      A non-empty capability with an identifier has a heap base and is live;
      one without an identifier stays clear of the heap. *)
  Definition heap_cap_valid (W : WORLD) (p : Perm) (b e : Addr) (π : option AId) : Prop :=
    (b < e)%a ->
    match π with
    | Some ι => is_heap_address b = true ∧ heap_cap_live W p b e ι
    | None => disjoint_from_heap b e
    end.

  Lemma heap_cap_valid_key_status W p b e π a :
    heap_cap_valid W p b e π -> a ∈ finz.seq_between b e ->
    heap_key_status (heap_std W) (addr_key π a) = Some AllocObjectLive.
  Proof.
    intros Hvalid Ha. apply elem_of_finz_seq_between in Ha.
    specialize (Hvalid ltac:(solve_addr)).
    destruct π as [ι|]; last done.
    destruct Hvalid as (_ & o & Hι & Hlive & Hb & He & _).
    rewrite addr_key_Some (heap_key_status_lookup _ _ _ o) // ?Hlive //.
    rewrite /alloc_object_contains. solve_addr.
  Qed.

  Lemma heap_cap_valid_key_live W p b e π a :
    heap_cap_valid W p b e π -> a ∈ finz.seq_between b e ->
    heap_key_live (heap_std W) (addr_key π a).
  Proof. apply heap_cap_valid_key_status. Qed.

  (** Tagged O capabilities retain authority to free their heap payload.
      Nonheap ranges must stay disjoint from the heap under narrowing. *)
  Definition heap_cap_O_valid (W : WORLD) (p : Perm) (g : Locality)
      (b e : Addr) (π : option AId) : Prop :=
    heap_cap_valid W p b e π ∧
    ∀ a, a ∈ finz.seq_between b e ->
      is_heap_address a = true -> region_state_nwl W (addr_key π a) g.

  Program Definition interp_cap_O : V := λne W _ w,
    ⌜match w.(lw) with
      | WCap true p g b e a => heap_cap_O_valid W p g b e w.(lprov)
      | _ => True
      end⌝%I.
  Solve All Obligations with solve_proper.

  Lemma heap_cap_valid_disjoint W p b e :
    disjoint_from_heap b e -> heap_cap_valid W p b e None.
  Proof. by intros Hdisjoint Hnonempty. Qed.

  (** The key of an address of a valid capability is live in the world: the
      object's key when the capability has an identifier, a non-heap key
      otherwise. *)
  Lemma heap_cap_valid_addr_live W p b e π ea :
    withinBounds b e ea = true ->
    heap_cap_valid W p b e π ->
    heap_key_live (heap_std W) (addr_key π ea).
  Proof.
    intros Hbounds Hvalid. eapply heap_cap_valid_key_live; first done.
    apply elem_of_finz_seq_between. by apply withinBounds_true_iff in Hbounds.
  Qed.

  (** A valid capability over a heap payload names the live object covering
      it, and every cell of the payload is a live, non-revoked key of the
      world (D21). *)
  Lemma free_heap_cap_payload W p g b e π :
    (heap_b < b ∧ b < e ∧ e <= heap_e)%a ->
    heap_cap_O_valid W p g b e π ->
    ∃ ι o, π = Some ι ∧ heap_std W !! ι = Some o ∧
      alloc_object_status o = AllocObjectLive ∧
      (alloc_object_base o <= b)%a ∧ (e <= alloc_object_end o)%a ∧
      Forall (λ x, heap_key_live (heap_std W) (LHeap x ι) ∧
        ∃ ρ, ρ ≠ Revoked ∧ std W !! LHeap x ι = Some ρ) (finz.seq_between b e).
  Proof.
    intros (Hb & Hbe & He) (Hvalid & Hcoverage).
    pose proof (Hvalid Hbe) as Hlive.
    destruct π as [ι|]; last first.
    { exfalso. rewrite /disjoint_from_heap elem_of_disjoint in Hlive.
      eapply (Hlive b); apply elem_of_finz_seq_between; solve_addr. }
    destruct Hlive as (_ & o & Hι & Hstatus & Hbase & Hend & _).
    exists ι, o. do 5 (split; first done).
    apply Forall_forall. intros x Hx. split.
    { by eapply (heap_cap_valid_key_live W p b e (Some ι)). }
    assert (Hxheap : is_heap_address x = true).
    { apply withinBounds_true_iff.
      apply elem_of_finz_seq_between in Hx. solve_addr. }
    specialize (Hcoverage x Hx Hxheap). cbn in Hcoverage.
    destruct g.
    - exists Permanent. split; first discriminate. exact Hcoverage.
    - destruct Hcoverage as [Hperm|Htemp].
      + exists Permanent; split; first discriminate. exact Hperm.
      + exists Temporary; split; first discriminate. exact Htemp.
  Qed.

  (** Interp for sentry in [enter_cond]. *)
  Program Definition interp_sentry (interp : V) : V :=
    λne W C w, (match w.(lw) with
                | WSentry t p g b e a =>
                    ⌜not_heap_range b e⌝ ∗
                    □ enter_cond W C p g b e a w.(lprov) interp
                | _ => False
                end)%I.
  Solve All Obligations with solve_proper.

  (** The per-address part of a memory capability's validity. *)
  Definition interp_cap_body (interp : V)
      (W : WORLD) (C : CmptName) (p : Perm) (g : Locality)
      (b e : Addr) (π : option AId) : iProp Σ :=
    ([∗ list] a ∈ finz.seq_between b e,
      ∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∧ ⌜persistent_cond P⌝
        ∧ rel C (addr_key π a) p' (safeC P)
        ∧ ▷ zcond P C
        ∧ (if readAllowed p' then ▷ rcond P C p' interp else True)
        ∧ (if writeAllowed p' then ▷ wcond P C interp else True)
        ∧ monoReq W C (addr_key π a) p' P
        ∧ ⌜if isWL p then region_state_pwl W (addr_key π a)
            else region_state_nwl W (addr_key π a) g⌝)%I.

  Global Instance interp_cap_body_contractive W C p g b e π :
    Contractive (λ interp, interp_cap_body interp W C p g b e π).
  Proof.
    rewrite /interp_cap_body.
    solve_contractive.
  Qed.

  Global Instance interp_cap_body_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n)
      interp_cap_body.
  Proof. rewrite /interp_cap_body. solve_proper. Qed.

  Global Instance interp_cap_body_persistent interp W C p g b e π :
    Persistent (interp_cap_body interp W C p g b e π).
  Proof. apply _. Qed.

  Lemma interp_cap_body_eq interp W C p g b e π :
    interp_cap_body interp W C p g b e π ≡
    ([∗ list] a ∈ finz.seq_between b e,
      ∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel C (addr_key π a) p' (safeC P)
        ∗ ▷ zcond P C
        ∗ (if readAllowed p' then ▷ rcond P C p' interp else True)
        ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
        ∗ monoReq W C (addr_key π a) p' P
        ∗ ⌜if isWL p then region_state_pwl W (addr_key π a)
            else region_state_nwl W (addr_key π a) g⌝)%I.
  Proof.
    rewrite /interp_cap_body.
    apply big_sepL_proper; intros k a' Ha'.
    do 3 f_equiv. intros P.
    by rewrite !bi.persistent_and_sep.
  Qed.

  (** Interp for memory capability. *)
  Program Definition interp_cap (interp : V) : V :=
    λne W C w, (match w.(lw) with
              | WCap t (O _ _) _ _ _ _
              | WCap t (BPerm XSR _ _ _) _ _ _ _ (* XRS capabilities are never safe-to-share *)
              | WCap t (BPerm _ WL _ _) Global _ _ _ (* WL Global capabilities are never safe-to-share *)
                => False
              | WCap t p g b e a =>
                  interp_cap_body interp W C p g b e w.(lprov)
                  ∗ ⌜disjoint_from_mmio b e ∧ heap_cap_valid W p b e w.(lprov)⌝
              | _ => False
              end)%I.
  Solve All Obligations with auto;solve_proper.

  (* NOTE : Using [force_global] is a bit like a hack,
     waiting for an actual normalisation function for [sealing_map].

     Having both [w] and [borrow w] in [sts_seals_std]
     forces to have both P(w) and P(borrow w),
     where P is the sealing predicate associated with [o].
     The problem is that P is not Persistent in general,
     and therefore, having both P(w) ∗ P(borrow w)
     might not be possible.
   *)
  Definition unseal_cond (P : V) (C : CmptName) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : LWord), P W C (lforce_global w) -∗ interp W C (filter_heap W w)).
  Global Instance unseal_cond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) unseal_cond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance unseal_contractive (P : V) (C : CmptName) (p : Perm) :
    Contractive (λ interp, ▷ unseal_cond P C interp)%I.
  Proof. solve_contractive. Qed.

  Definition seal_cond (P : V) (C : CmptName) (interp : V) : iProp Σ :=
    (□ ∀ (W: WORLD) (w : LWord), interp W C w -∗ P W C (lforce_global w)).
  Global Instance seal_cond_ne n :
    Proper ((=) ==> (=) ==> dist n ==> dist n) seal_cond.
  Proof. solve_proper_prepare. repeat f_equiv;auto. Qed.
  Global Instance seal_contractive (P : V) (C : CmptName) (p : Perm) :
    Contractive (λ interp, ▷ seal_cond P C interp)%I.
  Proof. solve_contractive. Qed.

  (* (un)seal permission definitions *)
  (* Note the asymmetry: to seal values, we need to know that we are using a persistent predicate to create a value, whereas we do not need this information when unsealing values (it is provided by the `interp_sb` case). *)
  Definition safe_to_seal (W : WORLD) (C : CmptName) (interp : V) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : V, ⌜persistent_cond P⌝
                ∗ (seal_pred a (safeC P))
                ∗ ⌜ a ∈ dom (seal_std W) ⌝
                ∗ ▷ seal_cond P C interp)%I.
  Definition safe_to_unseal (W : WORLD) (C : CmptName) (interp : V) (b e : OType) : iPropO Σ :=
    ([∗ list] a ∈ (finz.seq_between b e),
       ∃ P : V, ⌜persistent_cond P⌝
                ∗ (seal_pred a (safeC P))
                ∗ ⌜ a ∈ dom (seal_std W) ⌝
                ∗ ▷ unseal_cond P C interp)%I.

  (** Interp for sealing capability. *)
  Program Definition interp_sr (interp : V) : V :=
    λne W C w, (match w.(lw) with
    | WSealRange t p g b e a =>
    (if permit_seal p then safe_to_seal W C interp b e else True)
    ∗ (if permit_unseal p then safe_to_unseal W C interp b e else True)
    | _ => False end ) %I.
  Solve All Obligations with solve_proper.

  (** Interp for sealed capability. The payload keeps the sealed word's
      identifier. *)
  Program Definition interp_sb (W : WORLD) (C : CmptName) (o : OType) (w : LWord) : iPropO Σ :=
    (sts_seals_std C o {[w ; lborrow w ]} ∗
     ⌜match w.(lw) with
       | WCap true p g b e a => heap_cap_valid W p b e w.(lprov)
       | _ => True
       end⌝)%I.
  Solve All Obligations with solve_proper.

  (** Definition of interp, pre-fixpoint. Untagged words are safe data.
      Only tagged words use the structural authority predicates above. *)
  Program Definition interp1 (interp : V) : V :=
    (λne W C w,
    if get_tag w.(lw) then match w.(lw) return _ with
    | WInt _ => interp_z W C w
    | WCap t (O _ _) g b e a => interp_cap_O W C w
    | WCap t _ g b e a => interp_cap interp W C w
    | WSentry t p g b e a => interp_sentry interp W C w
    | WSealRange t p g b e a => interp_sr interp W C w
    | WSealed o sb => interp_sb W C o (WSealable sb @@? w.(lprov))
    end else True)%I.
  Solve All Obligations with solve_proper.

  (** To be able to use the fixpoint combinator to define [interp],
      we need to show that all case of [interp] are contractive. *)
  Global Instance interp_sentry_contractive :
    Contractive (interp_sentry).
  Proof.
    intros n x y Hdist W C [w π].
    destruct_word w; cbn [interp_sentry]; try reflexivity.
    change (dist n
      (⌜not_heap_range b e⌝ ∗
        □ enter_cond W C sd g b e a π x)%I
      (⌜not_heap_range b e⌝ ∗
        □ enter_cond W C sd g b e a π y)%I).
    f_equiv. f_equiv. by apply enter_cond_contractive.
  Qed.

  Global Instance interp_cap_contractive :
    Contractive (interp_cap).
  Proof.
    intros n x y Hdist W C [w π].
    destruct_word w; try reflexivity.
    destruct c as [rx wp dl dro].
    destruct rx, wp, g; try reflexivity.
    all: match goal with
    | |- context [WCap _ ?p ?g _ _ _] =>
        change (dist n
          (interp_cap_body x W C p g b e π ∗
            ⌜disjoint_from_mmio b e ∧ heap_cap_valid W p b e π⌝)%I
          (interp_cap_body y W C p g b e π ∗
            ⌜disjoint_from_mmio b e ∧ heap_cap_valid W p b e π⌝)%I);
        f_equiv; exact (interp_cap_body_contractive W C p g b e π n x y Hdist)
    end.
  Qed.

  Global Instance interp_sr_contractive :
    Contractive (interp_sr).
  Proof.
    intros n x y Hdist W C [w π].
    destruct_word w; try reflexivity.
    simpl. destruct (permit_seal sr), (permit_unseal sr);
    rewrite /safe_to_seal /safe_to_unseal;
    solve_contractive.
  Qed.

  Global Instance interp1_contractive :
    Contractive (interp1).
  Proof.
    intros n x y Hdistn W C [w π].
    rewrite /interp1 /=.
    destruct (get_tag w); last reflexivity.
    destruct_word w; [reflexivity|..].
    - pose proof (interp_cap_contractive n x y Hdistn W C (WCap t c g b e a @@? π)) as Hcap.
      destruct c as [rx wp dl dro].
      destruct rx, wp; try reflexivity;
        exact Hcap.
    - exact (interp_sr_contractive n x y Hdistn W C (WSealRange t sr g b e a @@? π)).
    - exact (interp_sentry_contractive n x y Hdistn W C (WSentry t sd g b e a @@? π)).
    - reflexivity.
  Qed.

  (** Definition of [interp] via the fixpoint combinator. *)
  Lemma fixpoint_interp1_eq (W : WORLD) (C : CmptName) (w : leibnizO LWord) :
    fixpoint (interp1) W C w ≡ interp1 (fixpoint (interp1)) W C w.
  Proof. exact: (fixpoint_unfold (interp1) W C w). Qed.

  Program Definition interp : V := (fixpoint (interp1)).
  Solve All Obligations with solve_proper.
  Program Definition interp_in_mem (p : Perm) : V :=
    λne W C w, interp_in_mem_pre W C p interp w.
  Solve All Obligations with solve_proper.

  Lemma interp_in_mem_eq p W C w :
    interp_in_mem p W C w ≡ interp W C (filter_heap W (lload_word p w)).
  Proof. reflexivity. Qed.
  Definition interp_continuation : K := interp_cont interp.
  Program Definition interp_expression : E :=
    interp_expr interp interp_continuation.
  Definition interp_registers : R := interp_reg interp.

  Lemma interp_untagged_eq W C w :
    get_tag w.(lw) = false → interp W C w ≡ True%I.
  Proof.
    intros Htag. rewrite /interp fixpoint_interp1_eq /interp1 /= Htag. reflexivity.
  Qed.

  Lemma interp_untagged W C w :
    get_tag w.(lw) = false → ⊢ interp W C w.
  Proof. intros Htag. rewrite (interp_untagged_eq W C w Htag). done. Qed.

  Lemma interp_clear_tag W C w : ⊢ interp W C (lclear_tag w).
  Proof. apply interp_untagged. rewrite lw_lclear_tag. apply get_tag_clear_tag. Qed.

  Lemma interp_int W C z π : ⊢ interp W C (WInt z @@? π).
  Proof. by apply interp_untagged. Qed.

  Lemma interp_lnull W C : ⊢ interp W C lnull.
  Proof. by apply interp_untagged. Qed.


  (** We have, and we _WANT_, [interp] to be Persistent *)
  Global Instance interp_persistent W C w : Persistent (interp W C w).
  Proof.
    destruct (get_tag w.(lw)) eqn:Htag.
    2: { rewrite (interp_untagged_eq W C w Htag). apply _. }
    rewrite /interp fixpoint_interp1_eq.
    destruct w as [w π]; cbn in Htag.
    destruct_word w; try destruct t; cbn in Htag; try discriminate.
    - destruct c as [rx wp dl dro].
      destruct rx, wp, g;
        first [ apply bi.pure_persistent
              | match goal with
                | |- context [WCap _ ?p ?g _ _ _] =>
                    change (Persistent
                      (interp_cap_body (fixpoint interp1) W C p g b e π ∗
                        ⌜disjoint_from_mmio b e ∧ heap_cap_valid W p b e π⌝)%I);
                    apply _
                end ].
    - change (Persistent
        ((if permit_seal sr
          then safe_to_seal W C interp b e else True) ∗
         (if permit_unseal sr
          then safe_to_unseal W C interp b e else True))%I).
      destruct (permit_seal sr), (permit_unseal sr);
        rewrite /safe_to_seal /safe_to_unseal; apply _.
    - apply _.
    - destruct sb as [t p g b e' a | t p g b e' a];
        destruct t; cbn in Htag; try discriminate; apply _.
  Qed.

  Global Instance interp_in_mem_pre_persistent W C p w :
    Persistent (interp_in_mem_pre W C p interp w).
  Proof. apply _. Qed.

  Global Instance interp_in_mem_persistent p W C w : Persistent (interp_in_mem p W C w).
  Proof. apply _. Qed.

  Lemma interp_to_in_mem W C w : interp W C w -∗ interp_in_mem RWL W C w.
  Proof.
    change (⊢ interp W C w -∗ interp W C (filter_heap W (lload_word RWL w)))%I.
    replace (lload_word RWL w) with w by (destruct w; done).
    destruct (filter_heap_result W w) as [-> | ->].
    - iIntros "$".
    - iIntros "_". iApply interp_clear_tag.
  Qed.

  (** The observed load must justify retaining the tag. [load_heap] alone
      does not supply this evidence. *)
  Lemma interp_in_mem_load_result W C p raw actual :
    actual = lclear_tag (lload_word p raw) ∨
      (actual = lload_word p raw ∧ filter_heap W (lload_word p raw) = lload_word p raw) ->
    interp_in_mem p W C raw -∗ interp W C actual.
  Proof.
    intros [Hactual | [Hactual Hfilter] ]; subst actual.
    - iIntros "_". iApply interp_clear_tag.
    - change (⊢ interp W C (filter_heap W (lload_word p raw)) -∗
        interp W C (lload_word p raw))%I.
      rewrite Hfilter. iIntros "$".
  Qed.


  (* Non-curried version of interp *)
  Notation interpC := (safeC interp).
  Notation interp_in_memC := (safeC (interp_in_mem RWL)).

  Lemma interp1_eq interp (W: WORLD) (C : CmptName) p g b e a π :
    ((interp1 interp W C (WCap true p g b e a @@? π)) ≡
       (if (isO p)
        then interp_cap_O W C (WCap true p g b e a @@? π)
        else
          if (has_sreg_access p)
          then False
          else ([∗ list] a ∈ finz.seq_between b e,
                  ∃ (p' : Perm) (P:V),
                    ⌜PermFlowsTo p p'⌝
                    ∗ ⌜persistent_cond P⌝
                    ∗ rel C (addr_key π a) p' (safeC P)
                    ∗ ▷ zcond P C
                    ∗ (if readAllowed p' then ▷ (rcond P C p' interp) else True)
                    ∗ (if writeAllowed p' then ▷ (wcond P C interp) else True)
                    ∗ monoReq W C (addr_key π a) p' P
                    ∗ ⌜ if isWL p then region_state_pwl W (addr_key π a) else region_state_nwl W (addr_key π a) g⌝)
               ∗ ⌜(if isWL p then g = Local else True) ∧
                    disjoint_from_mmio b e ∧ heap_cap_valid W p b e π⌝)%I).
  Proof.
    pose proof (interp_cap_body_eq interp W C p g b e π) as Hbody.
    destruct p as [rx wp dl dro].
    destruct rx, wp, g; cbn [isO has_sreg_access isWL].
    all: rewrite -?Hbody.
    all: rewrite ?bi.pure_and ?bi.persistent_and_sep.
    all: rewrite ?(bi.pure_True (Local = Local) eq_refl).
    all: try
      (rewrite (bi.pure_False (Global = Local)); [|discriminate]).
    all: rewrite ?bi.sep_True ?bi.True_sep ?bi.False_sep.
    all: try (rewrite (comm bi_sep _ False%I) bi.sep_False).
    all: rewrite ?bi.sep_False ?bi.False_sep.
    all: rewrite -?(bi.persistent_and_sep ⌜disjoint_from_shadow b e⌝
      ⌜revoker_addr ∉ finz.seq_between b e⌝) -?bi.pure_and.
    all: rewrite -?(bi.persistent_and_sep
      ⌜disjoint_from_shadow b e ∧ revoker_addr ∉ finz.seq_between b e⌝
      ⌜heap_cap_valid W _ b e π⌝) -?bi.pure_and.
    all: reflexivity.
  Qed.


  Lemma interp_cap_regions (W : WORLD) (C : CmptName) p g b e a π :
    isO p = false →
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜disjoint_from_mmio b e ∧ heap_cap_valid W p b e π⌝.
  Proof.
    iIntros (HnonO) "Hinterp".
    rewrite fixpoint_interp1_eq interp1_eq HnonO.
    destruct (has_sreg_access p); first done.
    iDestruct "Hinterp" as "[_ %Hregions]".
    iPureIntro. naive_solver.
  Qed.

  Lemma interp_cap_addr_live W C p g b e a ea π :
    isO p = false ->
    withinBounds b e ea = true ->
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜heap_key_live (heap_std W) (addr_key π ea)⌝.
  Proof.
    iIntros (Hp Hbounds) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as %[_ Hvalid]; first done.
    iPureIntro. eapply heap_cap_valid_addr_live; eauto.
  Qed.

  Lemma interp_cap_heap_conditions W C p g b e a π :
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜heap_cap_O_valid W p g b e π⌝.
  Proof.
    rewrite fixpoint_interp1_eq interp1_eq.
    destruct (isO p); first by iIntros "$".
    destruct (has_sreg_access p); first by iIntros "H".
    iIntros "[#Hlist %Hconditions]".
    rewrite /heap_cap_O_valid.
    iSplit; first (iPureIntro; exact (proj2 (proj2 Hconditions))).
    iIntros (x Hx Hheap).
    iDestruct (big_sepL_elem_of with "Hlist") as (q P)
      "(Hflow & Hpers & Hrel & Hz & Hr & Hw & Hmono & %Hstate)";
      first exact Hx.
    iPureIntro. destruct (isWL p) eqn:Hwl; last done.
    destruct Hconditions as [Hlocal _]. subst g. by right.
  Qed.

  Lemma interp_cap_disjoint (W : WORLD) (C : CmptName) p g b e a π :
    executeAllowed p = true →
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜disjoint_from_mmio b e ∧ disjoint_from_heap b e⌝.
  Proof.
    iIntros (Hexec) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as %[Hshadow Hheap];
      first by eapply executeAllowed_nonO.
    iPureIntro. split; first done.
    destruct (decide (b < e)%a) as [Hnonempty|Hempty]; last first.
    { rewrite /disjoint_from_heap finz_seq_between_empty; [set_solver|solve_addr]. }
    specialize (Hheap Hnonempty).
    destruct π as [ι|]; last done.
    destruct Hheap as (_ & o & _ & _ & _ & _ & Hnonexec & Hnotwl). congruence.
  Qed.

  Lemma interp_cap_disjoint_wl (W : WORLD) (C : CmptName) p g b e a π :
    isWL p = true →
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜disjoint_from_mmio b e ∧ disjoint_from_heap b e⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as %[Hshadow Hheap];
      first (apply isWL_nonO; exact Hwl).
    iPureIntro. split; first done.
    destruct (decide (b < e)%a) as [Hnonempty|Hempty]; last first.
    { rewrite /disjoint_from_heap finz_seq_between_empty; [set_solver|solve_addr]. }
    specialize (Hheap Hnonempty).
    destruct π as [ι|]; last done.
    destruct Hheap as (_ & o & _ & _ & _ & _ & Hnonexec & Hnotwl). congruence.
  Qed.

  Lemma interp_cap_not_shadow (W : WORLD) (C : CmptName) p g b e a a' π :
    isO p = false →
    withinBounds b e a' = true →
    interp W C (WCap true p g b e a @@? π) -∗ ⌜is_shadow_address a' = false⌝.
  Proof.
    iIntros (HnonO Hbounds) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as %[Hshadow Hheap]; auto.
    iPureIntro. eapply disjoint_from_shadow_not_in; last eauto.
    by apply disjoint_from_mmio_shadow.
  Qed.

  Lemma interp_cap_not_mmio (W : WORLD) (C : CmptName) p g b e a a' π :
    isO p = false →
    withinBounds b e a' = true →
    interp W C (WCap true p g b e a @@? π) -∗ ⌜is_mmio_address a' = false⌝.
  Proof.
    iIntros (HnonO Hbounds) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as %[Hmmio Hheap]; auto.
    iPureIntro. eapply disjoint_from_mmio_not_in; eauto.
  Qed.

  (* Inversion lemmas about interp  *)
  (* Inversion lemmas about about when R-capability *)
  Lemma readAllowed_valid_cap (W : WORLD) (C : CmptName) p g b e a' π :
    readAllowed p = true ->
    interp W C (WCap true p g b e a' @@? π) -∗
    ⌜Forall (fun a => ∃ ρ, std W !! addr_key π a = Some ρ ∧ ρ <> Revoked) (finz.seq_between b e)⌝.
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

  Lemma read_allowed_inv (W : WORLD) (C : CmptName) (a' a b e: Addr) p g π :
    (b ≤ a' ∧ a' < e)%Z →
    readAllowed p →
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    ∃ (p' : Perm) (P:V),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ rel C (addr_key π a') p' (safeC P)
      ∗ ▷ zcond P C
      ∗ ▷ rcond P C p' interp
      ∗ (if writeAllowed p' then (▷ wcond P C interp) else True)
      ∗ monoReq W C (addr_key π a') p' P
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

  Lemma read_allowed_inv_many (W : WORLD) (C : CmptName) (a b e: Addr) p g l π :
    readAllowed p →
    Forall (fun a' : Addr => (b <= a' < e)%a ) l ->
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    [∗ list] a' ∈ l,
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C (addr_key π a') p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then (▷ wcond P C interp) else True)
              ∗ monoReq W C (addr_key π a') p' P
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

  Lemma read_allowed_inv_full_cap (W : WORLD) (C : CmptName) (a b e: Addr) p g π :
    readAllowed p →
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    [∗ list] a' ∈ (finz.seq_between b e),
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C (addr_key π a') p' (safeC P)
              ∗ ▷ zcond P C
              ∗ ▷ rcond P C p' interp
              ∗ (if writeAllowed p' then (▷ wcond P C interp) else True)
              ∗ monoReq W C (addr_key π a') p' P
          ).
  Proof.
    iIntros (Hra) "Hinterp".
    iApply (read_allowed_inv_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  Lemma readAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a a' π :
    readAllowed p = true ->
    withinBounds b e a' = true ->
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜∃ ρ, std W !! addr_key π a' = Some ρ ∧ ρ <> Revoked⌝.
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
  Lemma write_allowed_inv (W : WORLD) (C : CmptName) (a' a b e: Addr) p g π :
    (b ≤ a' ∧ a' < e)%Z →
    writeAllowed p →
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    ∃ (p' : Perm) (P:V),
      ⌜ PermFlowsTo p p'⌝
      ∗ ⌜persistent_cond P⌝
      ∗ rel C (addr_key π a') p' (safeC P)
      ∗ ▷ zcond P C
      ∗ ▷ wcond P C interp
      ∗ (if readAllowed p' then (▷ rcond P C p' interp) else True)
      ∗ monoReq W C (addr_key π a') p' P
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

  Lemma write_allowed_inv_many (W : WORLD) (C : CmptName) (a b e: Addr) p g l π :
    writeAllowed p →
    Forall (fun a' : Addr => (b <= a' < e)%a ) l ->
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    [∗ list] a' ∈ l,
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C (addr_key π a') p' (safeC P)
              ∗ ▷ zcond P C
              ∗ (if readAllowed p' then (▷ rcond P C p' interp) else True)
              ∗ (▷ wcond P C interp)
              ∗ monoReq W C (addr_key π a') p' P
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

  Lemma write_allowed_inv_full_cap (W : WORLD) (C : CmptName) (a b e: Addr) p g π :
    writeAllowed p →
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    [∗ list] a' ∈ (finz.seq_between b e),
          (
            ∃ (p' : Perm) (P:V),
              ⌜ PermFlowsTo p p'⌝
              ∗ ⌜persistent_cond P⌝
              ∗ rel C (addr_key π a') p' (safeC P)
              ∗ ▷ zcond P C
              ∗ (if readAllowed p' then (▷ rcond P C p' interp) else True)
              ∗ (▷ wcond P C interp)
              ∗ monoReq W C (addr_key π a') p' P
          ).
  Proof.
    iIntros (Hra) "Hinterp".
    iApply (write_allowed_inv_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  Lemma interp_cap_cur_addr W C t p g b e a a' π :
    interp W C (WCap t p g b e a @@? π) ≡
    interp W C (WCap t p g b e a' @@? π).
  Proof.
    destruct t.
    - rewrite !fixpoint_interp1_eq !interp1_eq. reflexivity.
    - rewrite !interp_untagged_eq; done.
  Qed.

  Lemma writeAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a π :
    writeAllowed p = true ->
    withinBounds b e a = true ->
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜∃ ρ, std W !! addr_key π a = Some ρ ∧ ρ <> Revoked⌝.
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

  Lemma writeAllowed_valid_cap_implies_at W C p g b e a ea π :
    writeAllowed p = true →
    withinBounds b e ea = true →
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜∃ ρ, std W !! addr_key π ea = Some ρ ∧ ρ <> Revoked⌝.
  Proof.
    intros Hwa Hb.
    rewrite (interp_cap_cur_addr W C true p g b e a ea).
    apply writeAllowed_valid_cap_implies; done.
  Qed.

  Lemma writeAllowed_valid_cap (W : WORLD) (C : CmptName) p g b e a' π :
    writeAllowed p = true ->
    interp W C (WCap true p g b e a' @@? π) -∗
    ⌜Forall (fun a => ∃ ρ, std W !! addr_key π a = Some ρ ∧ ρ <> Revoked) (finz.seq_between b e)⌝.
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
  Lemma writeLocalAllowed_valid_cap_implies (W : WORLD) (C : CmptName) p g b e a a' π :
    isWL p = true ->
    withinBounds b e a = true ->
    interp W C (WCap true p g b e a' @@? π) -∗
    ⌜std W !! addr_key π a = Some Temporary⌝.
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

  Lemma writeLocalAllowed_valid_cap_implies_many (W : WORLD) (C : CmptName) p g b e a l π :
    isWL p = true ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) l ->
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    [∗ list] a' ∈ l, ⌜std W !! addr_key π a' = Some Temporary⌝.
  Proof.
    induction l; iIntros (Hra Hin) "#Hinterp"; first done.
    simpl.
    apply Forall_cons in Hin; destruct Hin as [Hin_a0 Hin].
    iDestruct (writeLocalAllowed_valid_cap_implies with "Hinterp") as "$"; auto.
    { rewrite /withinBounds; solve_addr. }
    iApply (IHl with "Hinterp"); eauto.
  Qed.

  Lemma writeLocalAllowed_valid_cap_implies_full_cap (W : WORLD) (C : CmptName) p g b e a π :
    isWL p = true ->
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    [∗ list] a' ∈ (finz.seq_between b e), ⌜std W !! addr_key π a' = Some Temporary⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iApply (writeLocalAllowed_valid_cap_implies_many with "Hinterp"); eauto.
    apply Forall_forall.
    intros a' Ha'.
    by apply elem_of_finz_seq_between.
  Qed.

  (* A write-local capability never covers the heap, so its addresses are keyed
     by [LNonHeap]. *)
  Lemma interp_WL_addr_key W C p g b e a π :
    isWL p = true ->
    interp W C (WCap true p g b e a @@? π) -∗
    ⌜Forall (λ a', addr_key π a' = LNonHeap a') (finz.seq_between b e)⌝.
  Proof.
    iIntros (Hwl) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as %[_ Hvalid];
      first by apply isWL_nonO.
    iPureIntro. apply Forall_forall. intros a' Ha'.
    assert (b < e)%a as Hlt.
    { apply elem_of_finz_seq_between in Ha'. solve_addr. }
    specialize (Hvalid Hlt).
    destruct π as [ι|]; last done.
    destruct Hvalid as (_ & o & _ & _ & _ & _ & _ & Hnwl). congruence.
  Qed.


  (** The addresses of a write-local capability are non-heap, so its full
      [Temporary] coverage is stated over [LNonHeap] keys. *)
  Lemma writeLocalAllowed_valid_cap_implies_full_cap_nonheap (W : WORLD) (C : CmptName) p g b e a π :
    isWL p = true ->
    ⊢ (interp W C (WCap true p g b e a @@? π)) →
    [∗ list] a' ∈ (finz.seq_between b e), ⌜std W !! LNonHeap a' = Some Temporary⌝.
  Proof.
    iIntros (Hwl) "#Hinterp".
    iDestruct (interp_WL_addr_key with "Hinterp") as %Hkeys; first done.
    iDestruct (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp") as "Htmp"; first done.
    iApply (big_sepL_impl with "Htmp"); iIntros "!>" (k a' Ha') "%Htmp".
    by rewrite (Forall_lookup_1 _ _ _ _ Hkeys Ha') in Htmp.
  Qed.


  (** A register file can read (resp. write) the address [a] through a word
      without an identifier, i.e. through the region key [LNonHeap a]. A word
      with an identifier reaches [a] under another key. *)
  Definition readAllowed_a_in_lregs (regs : LReg) (a : Addr) :=
    ∃ r (w : LWord), regs !! r = Some w ∧ w.(lprov) = None ∧
                     readAllowedWord w.(lw) ∧ hasValidAddress w.(lw) a.

  Definition writeAllowed_a_in_lregs (regs : LReg) (a : Addr) :=
    ∃ r (w : LWord), regs !! r = Some w ∧ w.(lprov) = None ∧
                     writeAllowedWord w.(lw) ∧ hasValidAddress w.(lw) a.

  Global Instance readAllowed_a_in_lregs_Decidable (regs : LReg) (a : Addr) :
    Decision (readAllowed_a_in_lregs regs a).
  Proof.
    eapply finite.exists_dec.
    intros x. destruct (regs !! x) as [w|] eqn:Hsome;
      last (right; intros [w1 (Heq & _)]; congruence).
    destruct (decide (w.(lprov) = None)), (decide (readAllowedWord w.(lw))),
      (decide (hasValidAddress w.(lw) a));
      try (right; intros [w1 (Heq & ? & ? & ?)]; simplify_eq; contradiction).
    left; eexists _; eauto.
  Qed.

  Global Instance writeAllowed_a_in_lregs_Decidable (regs : LReg) (a : Addr) :
    Decision (writeAllowed_a_in_lregs regs a).
  Proof.
    eapply finite.exists_dec.
    intros x. destruct (regs !! x) as [w|] eqn:Hsome;
      last (right; intros [w1 (Heq & _)]; congruence).
    destruct (decide (w.(lprov) = None)), (decide (writeAllowedWord w.(lw))),
      (decide (hasValidAddress w.(lw) a));
      try (right; intros [w1 (Heq & ? & ? & ?)]; simplify_eq; contradiction).
    left; eexists _; eauto.
  Qed.

  (** A valid PC is executable and so carries no identifier. *)
  Lemma interp_pc_noid W C p g b e a π :
    isCorrectPC (WCap true p g b e a) ->
    interp W C (WCap true p g b e a @@? π) -∗ ⌜π = None⌝.
  Proof.
    iIntros (Hpc) "Hinterp".
    assert (executeAllowed p = true) as Hexec by (by inversion Hpc).
    iDestruct (interp_cap_regions with "Hinterp") as %[_ Hvalid];
      first by eapply executeAllowed_nonO.
    iPureIntro. destruct π as [ι|]; last done.
    pose proof (isCorrectPC_withinBounds _ _ _ _ _ _ Hpc) as Hwb.
    apply withinBounds_true_iff in Hwb.
    destruct (Hvalid ltac:(solve_addr)) as (_ & o & _ & _ & _ & _ & Hnexec & _).
    congruence.
  Qed.

  Lemma interp_in_registers
    (W : WORLD) (C : CmptName)
    (regs : leibnizO LReg) (p : Perm) (g : Locality) (b e a : Addr):
      (∀ (r : RegName) (v : LWord), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)%I
    -∗ (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel C (LNonHeap a) p' (safeC P)
        ∗ ▷ zcond P C
        ∗ (if readAllowed p' then ▷ rcond P C p' interp else True)
        ∗ (if writeAllowed p' then ▷ wcond P C interp else True)
        ∗ monoReq W C (LNonHeap a) p' P
        ∗ ⌜if isWL p then region_state_pwl W (LNonHeap a) else region_state_nwl W (LNonHeap a) g⌝
       )
    -∗ (∃ (p' : Perm) (P : V),
        ⌜PermFlowsTo p p'⌝
        ∗ ⌜persistent_cond P⌝
        ∗ rel C (LNonHeap a) p' (safeC P)
        ∗ ▷ zcond P C
        ∗ (if decide (readAllowed_a_in_lregs (<[PC:=WCap true p g b e a @@? None]> regs) a)
            then ▷ (rcond P C p' interp)
            else emp)
        ∗ (if decide (writeAllowed_a_in_lregs (<[PC:=WCap true p g b e a @@? None]> regs) a)
            then ▷ wcond P C interp
            else emp)
        ∗ monoReq W C (LNonHeap a) p' P
        ∗ ⌜if isWL p then region_state_pwl W (LNonHeap a) else region_state_nwl W (LNonHeap a) g⌝
       ).
  Proof.
    iIntros "#Hreg #H".
    iDestruct "H" as (p0 P0 Hflp0 Hperscond_P0) "(Hrel0 & Hzcond0 & Hrcond0 & Hwcond0 & HmonoR0 & %Hstate0)".
    iExists p0,P0.
    iFrame "%#".
    iSplit.
    - (* rcond *)
      destruct (decide (readAllowed_a_in_lregs (<[PC:=WCap true p g b e a @@? None]> regs) a))
        as [Hra'|Hra']; auto.
      destruct (readAllowed p0) eqn:Hra; auto.
      destruct Hra' as (r & [w π] & Hsome & Hπ & Hrar & Hvw); cbn in Hπ; subst π.
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert_eq in Hsome; simplify_eq.
        eapply readAllowed_flowsto in Hrar; eauto.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      iDestruct ("Hreg" $! r _ n Hsome) as "Hinterp_w".
      destruct_word w; try destruct t; cbn in * ; try done.
      apply withinBounds_le_addr in Hvw.
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_w".
      replace (isO c) with false.
      2: { eapply readAllowed_nonO in Hrar ;done. }
      destruct (has_sreg_access c) eqn:HnXSR; auto.
      iDestruct "Hinterp_w" as "[Hinterp_w %Hc_cond ]".
      iDestruct (extract_from_region_inv with "Hinterp_w")
        as (p1 P1 Hflc1 Hperscond_P1) "(Hrel1 & Hzcond1 & Hrcond1 & Hwcond1 & HmonoR1 & %Hstate1)"
      ; eauto; iClear "Hinterp_w".
      apply readAllowed_flowsto in Hflc1; auto.
      iDestruct (rel_agree C (LNonHeap a) _ _ p0 p1 with "[$Hrel0 $Hrel1]") as "(-> & Heq)".
      congruence.
    - (* wcond *)
      destruct (decide (writeAllowed_a_in_lregs (<[PC:=WCap true p g b e a @@? None]> regs) a))
        as [Hwa'|Hwa']; auto.
      destruct (writeAllowed p0) eqn:Hwa; auto.
      destruct Hwa' as (r & [w π] & Hsome & Hπ & Hwaw & Hvw); cbn in Hπ; subst π.
      destruct (decide (r = PC)); subst.
      { rewrite lookup_insert_eq in Hsome; simplify_eq.
        eapply writeAllowed_flowsto in Hwaw; eauto.
        cbn in *; congruence.
      }
      rewrite lookup_insert_ne in Hsome; auto.
      iDestruct ("Hreg" $! r _ n Hsome) as "Hinterp_w".
      destruct_word w; try destruct t; cbn in * ; try done.
      apply withinBounds_le_addr in Hvw.
      iEval (rewrite fixpoint_interp1_eq interp1_eq) in "Hinterp_w".
      replace (isO c) with false.
      2: { eapply writeAllowed_nonO in Hwaw ;done. }
      destruct (has_sreg_access c) eqn:HnXSR; auto.
      iDestruct "Hinterp_w" as "[Hinterp_w %Hc_cond ]".
      iDestruct (extract_from_region_inv with "Hinterp_w")
        as (p1 P1 Hflc1 Hperscond_P1) "(Hrel1 & Hzcond1 & Hrcond1 & Hwcond1 & HmonoR1 & %Hstate1)"
      ; eauto; iClear "Hinterp_w".
      apply writeAllowed_flowsto in Hflc1; auto.
      iDestruct (rel_agree C (LNonHeap a) _ _ p0 p1 with "[$Hrel0 $Hrel1]") as "(-> & Heq)".
      congruence.
  Qed.

  Lemma filter_heap_map W (f : Word -> Word) w :
    (∀ w' : Word, memory_cap_bounds (f w') = memory_cap_bounds w') ->
    clear_tag (f w.(lw)) = f (clear_tag w.(lw)) ->
    filter_heap W (lift_word f w) = lift_word f (filter_heap W w).
  Proof.
    intros Hbounds Hclear. destruct w as [w π].
    rewrite /filter_heap /= (heap_authority_base_bounds_eq (f w) w (Hbounds w)).
    destruct (heap_authority_base w) as [b|]; last done.
    destruct π as [ι|]; last done.
    destruct (heap_std W !! ι) as [o|]; last done.
    destruct (alloc_object_status o); first done.
    rewrite /lclear_tag /lift_word /=. by rewrite Hclear.
  Qed.

  Lemma filter_heap_borrow W w :
    filter_heap W (lborrow w) = lborrow (filter_heap W w).
  Proof.
    apply filter_heap_map.
    - intros w'. by destruct w' as [z|[t p g b e a|t p g b e a]|t p g b e a|ot [t p g b e a|t p g b e a] ].
    - destruct w as [w π].
      by destruct w as [z|[t p g b e a|t p g b e a]|t p g b e a|ot [t p g b e a|t p g b e a] ].
  Qed.

  Lemma filter_heap_load_word W p w :
    filter_heap W (lload_word p w) = lload_word p (filter_heap W w).
  Proof.
    apply filter_heap_map.
    - apply memory_cap_bounds_load_word.
    - symmetry. apply load_word_clear_tag.
  Qed.

  (** ** Loads in the current world

      The world supplies a status witness for the Load rule (§4.5): the
      quarantine witness [ι ⊒ AQuar] when it has the loaded word's
      identifier [ι] Quarantined, and the plain witness otherwise. *)
  Definition load_witness_of (W : WORLD) (v : LWord) : load_witness :=
    match v.(lprov) with
    | Some ι =>
        match heap_std W !! ι with
        | Some o =>
            match alloc_object_status o with
            | AllocObjectQuarantined => LoadQuar ι
            | AllocObjectLive => LoadPlain
            end
        | None => LoadPlain
        end
    | None => LoadPlain
    end.

  Lemma heap_provenance_load_witness W v :
    heap_provenance (heap_std W) -∗ load_witness_res (load_witness_of W v).
  Proof.
    iIntros "#Hprov". rewrite /load_witness_of.
    destruct (lprov v) as [ι|]; last done.
    destruct (heap_std W !! ι) as [o|] eqn:Hι; last done.
    destruct (alloc_object_status o) eqn:Ho; first done.
    by iApply (heap_provenance_quarantined with "Hprov").
  Qed.

  Lemma world_interp_open_load_witness W C s v :
    world_interp_open W C s -∗
    world_interp_open W C s ∗ load_witness_res (load_witness_of W v).
  Proof.
    iIntros "Hworld".
    iDestruct (world_interp_open_heap_provenance with "Hworld") as "[$ #Hprov]".
    by iApply heap_provenance_load_witness.
  Qed.

  (** The Load post under the world's witness: the loaded word is either
      untagged, or kept and kept by the world's filter. *)
  Lemma load_post_world W p v actual :
    load_post (load_witness_of W v) p v actual ->
    actual = lclear_tag (lload_word p v) ∨
      (actual = lload_word p v ∧ filter_heap W (lload_word p v) = lload_word p v).
  Proof.
    intros (Hplain & _ & _ & Hwit).
    destruct Hplain as [-> | [_ ->] ]; last by left.
    destruct (decide (filter_heap W (lload_word p v) = lload_word p v)) as [Hkeep|Hne];
      first by right.
    left. destruct (filter_heap_cleared W _ Hne) as (b & ι & o & Hb & Hι & Ho & Hq).
    rewrite lprov_lload_word in Hι. rewrite lw_lload_word in Hb.
    rewrite /load_witness_of Hι Ho Hq in Hwit.
    apply Hwit; first done.
    intros Htag. split; first done. exists b.
    rewrite -Hb. apply heap_authority_base_bounds_eq.
    symmetry. apply memory_cap_bounds_load_word.
  Qed.

  Lemma interp_in_mem_load_post W C p raw actual :
    load_post (load_witness_of W raw) p raw actual ->
    interp_in_mem p W C raw -∗ interp W C actual.
  Proof. intros Hpost. by apply interp_in_mem_load_result, load_post_world. Qed.

  Lemma load_post_world_load_heap_in_world W p v actual :
    load_post (load_witness_of W v) p v actual ->
    load_heap_in_world W (lload_word p v) actual.
  Proof.
    intros Hpost. split; first apply Hpost.
    destruct (load_post_world W p v actual Hpost) as [-> | [-> Hkeep] ]; last done.
    apply filter_heap_lclear_tag.
  Qed.

  (** A valid executable capability with a non-empty range carries no
      identifier: heap authority is never executable. *)
  Lemma interp_exec_noid W C p g b e a π :
    executeAllowed p = true → (b < e)%a →
    interp W C (WCap true p g b e a @@? π) -∗ ⌜π = None⌝.
  Proof.
    iIntros (Hexec Hbe) "Hinterp".
    iDestruct (interp_cap_regions with "Hinterp") as %[_ Hheap];
      first by eapply executeAllowed_nonO.
    iPureIntro. specialize (Hheap Hbe). destruct π as [ι|]; last done.
    destruct Hheap as (_ & o & _ & _ & _ & _ & Hnonexec & _). congruence.
  Qed.

  Lemma interp_lstore_word W C p v :
    interp W C v -∗ interp W C (lstore_word p v).
  Proof.
    iIntros "#Hv".
    destruct (canStore p v.(lw)) eqn:Hcs.
    - by rewrite lstore_word_canStore.
    - assert (lstore_word p v = lclear_tag v) as ->.
      { by rewrite /lstore_word /lclear_tag /lift_word /store_word Hcs. }
      iApply interp_clear_tag.
  Qed.

  (** The region of an address reached through a capability is the PC's
      region exactly when the address is the PC's and the capability has no
      identifier: a capability with an identifier reaches it under another key. *)
  Lemma addr_key_pc π ea pc_a :
    addr_key π ea = LNonHeap pc_a → π = None ∧ ea = pc_a.
  Proof. destruct π; cbn; intros; simplify_eq; done. Qed.

End logrel.

Notation safeC P :=
  (λ WCv : WORLD * CmptName * (leibnizO LWord), P WCv.1.1 WCv.1.2 WCv.2).
Notation interpC := (safeC interp).

Notation interp_in_memC := (safeC (interp_in_mem RWL)).
