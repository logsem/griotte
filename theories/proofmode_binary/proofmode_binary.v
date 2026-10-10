From iris.proofmode Require Import proofmode spec_patterns coq_tactics ltac_tactics reduction.
From griotte Require Export proofmode.
From griotte Require Export rules_binary memory_region_binary.
From griotte Require Import proofmode_instr_rules_binary.
From griotte Require Export NamedProp.
From machine_utils Require Export tactics.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option Bool Constr.
Set Default Proof Mode "Classic".

(** * Proof mode for spec-side (and lockstep) instruction steps

    Spec instruction rules have the shape
    [spec_ctx ∗ ⤇ Seq (Instr Executable) ∗ P ={E}=∗ ⤇ Seq (Instr NextI) ∗ Q].
    They are applied with the same on-demand framing as the impl-side WP rules
    ([iApplyCapAuto]), after turning the [|={E}=>] conclusion into a
    continuation using [ElimModal]. This works whenever the goal can eliminate
    the update, in particular in WP goals and in fupd goals.

    Tactics:
    - [iInstr_spec "Hscode"]: one spec step on the spec code fragment
      [spec_codefrag] named ["Hscode"], followed by the [Seq] reduction;
    - [iGo_spec "Hscode"]: repeated [iInstr_spec];
    - [iInstr_lockstep "Hscode" "Hcode"]: one spec step, then one impl step
      ([iInstr "Hcode"]), when both sides run the same code;
    - [iGo_lockstep "Hscode" "Hcode"]: repeated [iInstr_lockstep]. *)

(** ** Eliminating an update into a continuation *)

Section elim_modal_cps.
  Context {PROP : bi}.

  (** A resource [M] under a modality that the goal [G] can eliminate gives
      the goal from a continuation expecting the resource without modality. *)
  Lemma elim_modal_cps (M B G : PROP) :
    ElimModal True false false M B G G →
    M -∗ (B -∗ G) -∗ G.
  Proof.
    rewrite /ElimModal /= => HE. iIntros "HM HG".
    iApply HE; first done. iFrame.
  Qed.

  (** Specialization of the wand [j] with on-demand framing of its premise
      [P1] (as in [tac_specialize_frame']), where the update [P2] of its
      conclusion is eliminated into the goal [G]. The update is resolved
      against [G] before framing, so that its mask is fixed by the goal. *)
  Lemma tac_specialize_frame_elim_modal (Δ : envs PROP) j q R P1 P2 B G :
    envs_lookup j Δ = Some (q, R) →
    IntoWand q false R P1 P2 →
    ElimModal True false false P2 B G G →
    envs_entails (envs_delete true j q Δ) (P1 ∗ locked (B -∗ G)%I) →
    envs_entails Δ G.
  Proof.
    intros ?? HE HΔ. eapply tac_specialize_frame'; [done..|].
    rewrite envs_entails_unseal in HΔ |- *. rewrite HΔ. unlock.
    iIntros "[$ HG] HP2". iApply (elim_modal_cps _ _ _ HE with "HP2 HG").
  Qed.
End elim_modal_cps.

(* Starts the application of the spec rule [h]: the goal becomes
   [P1 ∗ locked (B -∗ G)]. *)
Ltac iSpecializeFrameElimModalStart h :=
  notypeclasses refine (tac_specialize_frame_elim_modal _ h _ _ _ _ _ _ _ _ _ _);
  [pm_reflexivity
  |solve_to_wand tt
  |tc_solve
  |pm_reduce].

(** ** Side conditions *)

#[export] Hint Extern 1 (↑specN ⊆ _) => solve_ndisj : solve_pure.

(** ** Framable spec resources *)

Class FramableSpecSRegisterPointsto (sr: SRegName) (w: Word) := {}.
#[export] Hint Mode FramableSpecSRegisterPointsto + - : typeclass_instances.
Class FramableSpecRegisterPointsto (r: RegName) (w: Word) := {}.
#[export] Hint Mode FramableSpecRegisterPointsto + - : typeclass_instances.
Class FramableSpecMemoryPointsto (a: Addr) (dq: dfrac) (w: Word) := {}.
#[export] Hint Mode FramableSpecMemoryPointsto + - - : typeclass_instances.
Class FramableSpecCodefrag (a: Addr) (l: list Word) := {}.
#[export] Hint Mode FramableSpecCodefrag + - : typeclass_instances.

Instance FramableSpecSRegisterPointsto_default sr w :
  FramableSpecSRegisterPointsto sr w
| 100. Qed.

Instance FramableSpecRegisterPointsto_default r w :
  FramableSpecRegisterPointsto r w
| 100. Qed.

Instance FramableSpecMemoryPointsto_default a dq w :
  FramableSpecMemoryPointsto a dq w
| 100. Qed.

Instance FramableSpecCodefrag_default a l :
  FramableSpecCodefrag a l
| 100. Qed.

Instance FramableMachineResource_spec_sreg `{specG Σ} sr dq w :
  FramableSpecSRegisterPointsto sr w →
  FramableMachineResource (sr ↣ₛᵣ{dq} w).
Qed.

Instance FramableMachineResource_spec_reg `{specG Σ} r dq w :
  FramableSpecRegisterPointsto r w →
  FramableMachineResource (r ↣ᵣ{dq} w).
Qed.

Instance FramableMachineResource_spec_mem `{specG Σ} a dq w :
  FramableSpecMemoryPointsto a dq w →
  FramableMachineResource (a ↣ₐ{dq} w).
Qed.

Instance FramableMachineResource_spec_codefrag `{specG Σ} `{MachineParameters} a l :
  FramableSpecCodefrag a l →
  FramableMachineResource (spec_codefrag a l).
Qed.

Instance FramableMachineResource_spec_res `{specG Σ} e :
  FramableMachineResource (⤇ e).
Qed.

(** ** Names of the framed spec resources *)

Ltac2 Type spec_hyp_table_kind :=
  [ SpecReg | SpecSReg | SpecMem | SpecCodefrag | SpecThread ].

Ltac2 record_framed_spec
      (table: (constr * constr * spec_hyp_table_kind) list ref)
      (framed: constr * constr)
  :=
  let (hname, hh) := framed in
  let (lhs, kind) :=
    lazy_match! hh with
    | (spec_reg_pointsto ?r _ _) => (r, SpecReg)
    | (spec_sreg_pointsto ?sr _ _) => (sr, SpecSReg)
    | (spec_mem_pointsto ?a _ _) => (a, SpecMem)
    | (spec_codefrag ?a _) => (a, SpecCodefrag)
    | (spec_res _) => ('tt, SpecThread)
    end in
  table.(contents) := (hname, lhs, kind) :: table.(contents).

Ltac2 name_spec_resource (name, lhs, kind) :=
  match kind with
  | SpecSReg =>
    match! goal with [ |- context [ spec_sreg_pointsto ?sr ?dq ?x ] ] =>
      assert_constr_eq sr lhs;
      ltac1:(x dq sr name |-
               change (spec_sreg_pointsto sr dq x) with (name ∷ spec_sreg_pointsto sr dq x)%I)
        (Ltac1.of_constr x) (Ltac1.of_constr dq) (Ltac1.of_constr sr) (Ltac1.of_constr name)
    end
  | SpecReg =>
    match! goal with [ |- context [ spec_reg_pointsto ?r ?dq ?x ] ] =>
      assert_constr_eq r lhs;
      ltac1:(x dq r name |-
               change (spec_reg_pointsto r dq x) with (name ∷ spec_reg_pointsto r dq x)%I)
        (Ltac1.of_constr x) (Ltac1.of_constr dq) (Ltac1.of_constr r) (Ltac1.of_constr name)
    end
  | SpecMem =>
    match! goal with [ |- context [ spec_mem_pointsto ?a ?dq ?x ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(x dq a name |-
               change (spec_mem_pointsto a dq x) with (name ∷ spec_mem_pointsto a dq x)%I)
        (Ltac1.of_constr x) (Ltac1.of_constr dq) (Ltac1.of_constr a) (Ltac1.of_constr name)
    end
  | SpecCodefrag =>
    match! goal with [ |- context [ spec_codefrag ?a ?l ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(l a name |- change (spec_codefrag a l) with (name ∷ spec_codefrag a l)%I)
        (Ltac1.of_constr l) (Ltac1.of_constr a) (Ltac1.of_constr name)
    end
  | SpecThread =>
    match! goal with [ |- context [ spec_res ?e ] ] =>
      ltac1:(e name |- change (spec_res e) with (name ∷ spec_res e)%I)
        (Ltac1.of_constr e) (Ltac1.of_constr name)
    end
  end.

Ltac2 reintro_spec_resources tbl :=
  (refine '(@envs_entails_rew_goal _ _ _ _ _ _);
   Control.shelve_unifiable ()) >
  [ List.iter (fun x => try (name_spec_resource x)) (tbl.(contents)); reflexivity | () ];
  iNamedIntro ().

(** ** Applying a spec rule with on-demand framing *)

(* Frames the [spec_ctx] premise from the intuitionistic context. *)
Ltac iFrameSpecCtx :=
  lazymatch goal with |- envs_entails (Envs ?Γp _ _) _ =>
    lazymatch Γp with context [ Esnoc _ ?h spec_ctx ] => iFrame h end
  end.

Ltac2 iApplyCapAutoSpecT_init0 lemma :=
  let tbl := { contents := [] } in
  let x := iFresh () in
  ltac1:(x lem |- once (iPoseProofCore lem as false (fun H => iRename H into x)))
    (Ltac1.of_constr x) (Ltac1.of_constr lemma);
  on_lasts [(fun _ => ltac1:(x |- iSpecializeFrameElimModalStart x) (Ltac1.of_constr x))];
  tbl.

Ltac2 iApplyCapAutoSpecCore lemma :=
  let tbl := iApplyCapAutoSpecT_init0 lemma in
  on_lasts [ (fun _ => try (ltac1:(iFrameSpecCtx))) ];
  let iFrameCap := fun () => record_framed_spec tbl (iFrameAuto ()) in
  grepeat (fun _ =>
    Control.extend [] (fun _ => try (Control.once solve_pure))
      [ (fun _ => try (iFrameCap ())) ]);
  on_lasts [ (fun _ =>
    ltac1:(iUnlockFramed);
    reintro_spec_resources tbl;
    iApplyCapAuto_cleanup ()
  )].

Ltac2 Notation "iApplyCapAutoSpec" lem(constr) := iApplyCapAutoSpecCore lem.
Tactic Notation "iApplyCapAutoSpec" constr(lem) :=
  let f := ltac2:(lem |- iApplyCapAutoSpecCore (Option.get (Ltac1.to_constr lem))) in
  f lem.

(** ** Reducing [Seq] on the spec side *)

(* Spec counterpart of [wp_pure]: reduces [⤇ Seq (Instr c)] for a finished
   instruction [c], using [spec_ctx] from the intuitionistic context. *)
Ltac iSpecSeq :=
  lazymatch goal with |- envs_entails (Envs ?Γp ?Γs _) _ =>
  lazymatch Γp with context [ Esnoc _ ?hctx spec_ctx ] =>
  lazymatch Γs with context [ Esnoc _ ?hj (spec_res (Seq (Instr ?c))) ] =>
    let lem :=
      lazymatch c with
      | NextI => constr:(step_seq_nexti)
      | Halted => constr:(step_seq_halted)
      | Failed => constr:(step_seq_failed)
      end in
    iMod (lem with [SIdent hctx nil; SIdent hj nil]) as hj;
    [try solve_ndisj ..]
  end end end.

(** ** Code fragments on the spec side *)

Ltac changePC_spec_next_block new_a :=
  match goal with |- context [ Esnoc _ _ (PC ↣ᵣ WCap _ _ _ _ ?prev_a)%I ] =>
    rewrite (_: prev_a = new_a) ; [ | solve_block_move ] end.

Ltac changePC_specto0 new_a :=
  match goal with |- context [ Esnoc _ _ (PC ↣ᵣ WCap _ _ _ _ ?a)%I ] =>
    rewrite (_: a = new_a); [| solve_addr]
  end.
Tactic Notation "changePC_specto" constr(a) := changePC_specto0 a.

Ltac spec_codefrag_facts h :=
  let h := constr:(h:ident) in
  match goal with |- context [ Esnoc _ h (spec_codefrag ?a_base ?code) ] =>
    (match goal with H : ContiguousRegion a_base _ |- _ => idtac end ||
     let HH := fresh in
     iDestruct (spec_codefrag_contiguous_region with h) as %HH;
     cbn [length map encodeInstrsW] in HH
    );
    (match goal with H : SubBounds _ _ a_base (a_base ^+ _)%a |- _ => idtac end ||
     (try match goal with H : SubBounds ?b ?e _ _ |- _ =>
            let HH := fresh in
            assert (HH: SubBounds b e a_base (a_base ^+ length code)%a) by solve_addr;
            cbn [length map encodeInstrsW] in HH
          end))
  end.

Ltac clear_spec_codefrag_facts h :=
  let h := constr:(h:ident) in
  match goal with |- context [ Esnoc _ h (spec_codefrag ?a_base ?code) ] =>
    try match goal with H : ContiguousRegion a_base _ |- _ => clear H end;
    try match goal with H : SubBounds _ _ a_base (a_base ^+ _)%a |- _ => clear H end
  end.

Ltac focus_block_0_spec_codefrag_facts hi a0 :=
  let HCR := fresh in
  iDestruct (spec_codefrag_contiguous_region with hi) as %HCR;
  cbn [length map encodeInstrsW] in HCR;
  try lazymatch goal with HSB : SubBounds ?b ?e a0 (a0 ^+ _)%a |- _ =>
    let HSB' := fresh in
    unshelve epose proof (focus_block_0_SubBounds _ _ _ _ _ HSB HCR _ _) as HSB';
    [solve_pure ..|];
    cbn [length map encodeInstrsW] in HSB'
  end.

Ltac focus_block_0_spec h hi hcont :=
  let h := constr:(h:ident) in
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let x := iFresh in
  match goal with |- context [ Esnoc _ h (spec_codefrag ?a0 _) ] =>
    iPoseProof (spec_codefrag_block0_acc with h) as x;
    eapply tac_and_destruct with x _ hi hcont _ _ _;
    [pm_reflexivity|pm_reduce;tc_solve|
     pm_reduce;
     lazymatch goal with
     | |- False =>
       let hi := pretty_ident hi in
       let hcont := pretty_ident hcont in
       fail "focus_block_0_spec:" hi "or" hcont "not fresh"
     | _ => idtac
     end];
    focus_block_0_spec_codefrag_facts hi a0
  end.

Tactic Notation "focus_block_0_spec" constr(h) "as" constr(hi) constr(hcont) :=
  focus_block_0_spec h hi hcont.

Ltac focus_block_spec_codefrag_facts hi a0 Ha_base :=
  let HCR := fresh in
  iDestruct (spec_codefrag_contiguous_region with hi) as %HCR;
  cbn [length map encodeInstrsW] in HCR;
  try lazymatch goal with HSB : SubBounds ?b ?e a0 (a0 ^+ _)%a |- _ =>
    let HSB' := fresh in
    unshelve epose proof (focus_block_SubBounds _ _ _ _ _ _ _ HSB HCR Ha_base _ _ _) as HSB';
    [solve_pure ..|];
    cbn [length map encodeInstrsW] in HSB'
  end.

Ltac focus_block_spec_nochangePC0 n h a_base Ha_base hi hcont :=
  let h := constr:(h:ident) in
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let x := iFresh in
  match goal with |- context [ Esnoc _ h (spec_codefrag ?a0 _) ] =>
    iPoseProof ((spec_codefrag_block_acc n) with h) as (a_base) x;
      [ once (typeclasses eauto with proofmode_focus) | ];
    let xbase := iFresh in
    let y := iFresh in
    eapply tac_and_destruct with x _ xbase y _ _ _;
      [pm_reflexivity|pm_reduce;tc_solve|pm_reduce];
    iPure xbase as Ha_base;
    eapply tac_and_destruct with y _ hi hcont _ _ _;
      [pm_reflexivity|pm_reduce;tc_solve|pm_reduce];
    focus_block_spec_codefrag_facts hi a0 Ha_base
  end.

Tactic Notation "focus_block_spec_nochangePC" constr(n) constr(h) "as"
       ident(a_base) simple_intropattern(Ha_base) constr(hi) constr(hcont) :=
  focus_block_spec_nochangePC0 n h a_base Ha_base hi hcont.

Ltac focus_block_spec0 n h a_base Ha_base hi hcont :=
  focus_block_spec_nochangePC0 n h a_base Ha_base hi hcont;
  changePC_spec_next_block a_base.

Tactic Notation "focus_block_spec" constr(n) constr(h) "as"
       ident(a_base) simple_intropattern(Ha_base) constr(hi) constr(hcont) :=
  focus_block_spec0 n h a_base Ha_base hi hcont.

Ltac unfocus_block_spec hi hcont h :=
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let h := constr:(h:ident) in
  clear_spec_codefrag_facts hi;
  iDestruct (hcont with hi) as h.

Tactic Notation "unfocus_block_spec" constr(hi) constr(hcont) "as" constr(h) :=
  unfocus_block_spec hi hcont h.

(** ** [iInstr_spec] *)

Ltac iInstr_spec_lookup0 hprog hi hcont :=
  let hprog := constr:(hprog:ident) in
  lazymatch goal with |- context [ Esnoc _ hprog (spec_codefrag ?a_base _) ] =>
  lazymatch goal with |- context [ Esnoc _ ?hpc (PC ↣ᵣ (WCap _ _ _ _ ?pc_a))%I ] =>
    let base_off := eval unfold as_weak_addr_incr in (@as_weak_addr_incr pc_a a_base _ _) in
    lazymatch base_off with
    | (?base, ?off) =>
      iPoseProofCore (spec_codefrag_lookup_acc _ _ off with hprog) as false (fun H =>
        eapply tac_and_destruct with H _ hi hcont _ _ _;
        [pm_reflexivity
        |pm_reduce; tc_solve
        |pm_reduce];
        rewrite ?addr_incr_zero ?addr_incr_zero_nat
      )
     end
  end end.

Tactic Notation "iInstr_spec_lookup" constr(hprog) "as" constr(hi) constr(hcont) :=
  iInstr_spec_lookup0 hprog hi hcont.

Ltac iInstr_spec_get_rule0 hi cont :=
  let hi := constr:(hi:ident) in
  once (
    (lazymatch goal with |- context [ Esnoc _ hi (_ ↣ₐ encodeInstrW ?instr)%I ] => idtac end
     + (lazymatch goal with |- context [ Esnoc _ hi (_ ↣ₐ ?instr)%I ] =>
           fail 1 "Next spec instruction is not of the form (encodeInstrW _):" instr
         end + fail "" hi "not found"))
  );
  lazymatch goal with |- context [ Esnoc _ hi (_ ↣ₐ encodeInstrW ?instr)%I ] =>
    dispatch_spec_instr_rule instr cont
  end.

Tactic Notation "iInstr_spec_get_rule" constr(hi) tactic(cont) :=
  iInstr_spec_get_rule0 hi cont.

Ltac iInstr_spec_close hprog :=
  (* [iApplyCapAutoSpec] renames the context: recover the instruction and the
     closing wand from their shapes. *)
  lazymatch goal with |- context [ Esnoc _ ?hi (_ ↣ₐ encodeInstrW _)%I ] =>
  lazymatch goal with |- context [ Esnoc _ ?hcont (_ ↣ₐ encodeInstrW _ -∗ _)%I ] =>
    notypeclasses refine (tac_specialize false _ hi _ hcont _ _ _ _ _ _ _ _ _);
    [pm_reflexivity
    |pm_reflexivity
    |tc_solve
    |pm_reduce];
    iRename hcont into hprog
  end end.

Ltac iInstr_spec0 hprog :=
  let hi := iFresh in
  let hcont := iFresh in
  iInstr_spec_lookup hprog as hi hcont;
  iInstr_spec_get_rule hi ltac:(fun rule =>
    iApplyCapAutoSpec rule;
    [ .. | iInstr_spec_close hprog;
           simpl_cnull_zero;
           try iSpecSeq ]).

Tactic Notation "iInstr_spec" constr(H) := iInstr_spec0 H.

Ltac2 rec iGo_spec hprog :=
  let stop_if_at_least_two_goals () :=
    on_lasts [ (fun _ => ()); (fun _ => ()) ] in
  match Control.case (fun _ => ltac1:(hprog |- iInstr_spec hprog) (Ltac1.of_constr hprog)) with
  | Err (_) => ()
  | Val (_) => Control.plus stop_if_at_least_two_goals (fun _ => iGo_spec hprog)
  end.

Ltac iGo_spec hprog :=
  let f := ltac2:(hprog |- iGo_spec (Option.get (Ltac1.to_constr hprog))) in
  f hprog.

(** ** Lockstep: the same instruction on both sides *)

(* Spec step first: its update is eliminated into the WP goal, which is then
   stepped by [iInstr]. *)
Ltac iInstr_lockstep0 hsprog hprog :=
  iInstr_spec hsprog; [ .. | iInstr hprog ].

Tactic Notation "iInstr_lockstep" constr(Hs) constr(H) := iInstr_lockstep0 Hs H.

Ltac2 rec iGo_lockstep hsprog hprog :=
  let stop_if_at_least_two_goals () :=
    on_lasts [ (fun _ => ()); (fun _ => ()) ] in
  match Control.case (fun _ =>
          ltac1:(hsprog hprog |- iInstr_lockstep hsprog hprog)
            (Ltac1.of_constr hsprog) (Ltac1.of_constr hprog)) with
  | Err (_) => ()
  | Val (_) => Control.plus stop_if_at_least_two_goals (fun _ => iGo_lockstep hsprog hprog)
  end.

Ltac iGo_lockstep hsprog hprog :=
  let f := ltac2:(hsprog hprog |-
                    iGo_lockstep (Option.get (Ltac1.to_constr hsprog))
                      (Option.get (Ltac1.to_constr hprog))) in
  f hsprog hprog.

(** ** Lockstep code blocks

    Both runs execute the same code at the same addresses: the impl and spec
    code fragments are focused on the same block. The impl [focus_block]
    moves the program counters of both runs, as it rewrites the old address
    everywhere in the goal. *)

Ltac focus_block_lockstep0 n hs h a_base Ha_base hsi hscont hi hcont :=
  let a' := fresh "a_base_spec" in
  let Ha' := fresh "Ha_base_spec" in
  focus_block_spec_nochangePC0 n hs a' Ha' hsi hscont;
  focus_block n h as a_base Ha_base hi hcont;
  assert (a' = a_base) as -> by (clear -Ha' Ha_base; solve_addr);
  clear Ha'.

Tactic Notation "focus_block_lockstep" constr(n) constr(hs) constr(h) "as"
       ident(a_base) ident(Ha_base) constr(hsi) constr(hscont) constr(hi) constr(hcont) :=
  focus_block_lockstep0 n hs h a_base Ha_base hsi hscont hi hcont.

Ltac focus_block_nochangePC_lockstep0 n hs h a_base Ha_base hsi hscont hi hcont :=
  let a' := fresh "a_base_spec" in
  let Ha' := fresh "Ha_base_spec" in
  focus_block_spec_nochangePC0 n hs a' Ha' hsi hscont;
  focus_block_nochangePC n h as a_base Ha_base hi hcont;
  assert (a' = a_base) as -> by (clear -Ha' Ha_base; solve_addr);
  clear Ha'.

Tactic Notation "focus_block_nochangePC_lockstep" constr(n) constr(hs) constr(h) "as"
       ident(a_base) ident(Ha_base) constr(hsi) constr(hscont) constr(hi) constr(hcont) :=
  focus_block_nochangePC_lockstep0 n hs h a_base Ha_base hsi hscont hi hcont.

Tactic Notation "focus_block_0_lockstep" constr(hs) constr(h) "as"
       constr(hsi) constr(hscont) constr(hi) constr(hcont) :=
  focus_block_0_spec hs as hsi hscont; focus_block_0 h as hi hcont.

Tactic Notation "unfocus_block_lockstep" constr(hsi) constr(hscont) constr(hi) constr(hcont)
       "as" constr(hs) constr(h) :=
  unfocus_block_spec hsi hscont as hs; unfocus_block hi hcont as h.
