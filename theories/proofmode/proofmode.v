From Stdlib Require Import Eqdep_dec List.
From griotte Require Import rules.
From griotte Require Export iris_extra memory_region.
From griotte Require Import classes tactics_helpers proofmode_instr_support
  proofmode_instr_rules.
From griotte Require Export class_instances solve_pure solve_addr_extra.
From iris.proofmode Require Import proofmode spec_patterns coq_tactics ltac_tactics reduction.
From griotte Require Export named_props_extra.
From machine_utils Require Export tactics.
From iris.bi Require Import bi.
Import bi.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option Bool Constr.
Set Default Proof Mode "Classic".

Section codefrag.
  Context {Σ:gFunctors} {ceriseg: ceriseG Σ}
    `{MP: MachineParameters}.

  (* The instruction word is given in the normal form [w @@? None]. *)
  Lemma codefrag_lookup_acc a0 (cs: list Word) (i: nat) w:
    SimplTC (cs !! i) (Some w) →
    codefrag a0 cs -∗
      (a0 ^+ i)%a ↦ₐ w @@? None ∗ ((a0 ^+ i)%a ↦ₐ w @@? None -∗ codefrag a0 cs).
  Proof.
    iIntros (Hi) "Hcs".
    iDestruct (codefrag_contiguous_region with "Hcs") as %Hub.
    rewrite /codefrag.
    destruct Hub as [? Hub].
    iDestruct (big_sepL2_lookup_acc _ _ _ i _ (lword_of_word w) with "Hcs") as "[Hw Hcont]".
    3: iFrame.
    { eapply finz_seq_between_lookup with (n:=length cs).
      { apply lookup_lt_is_Some_1; eauto. }
      { solve_addr. } }
    { rewrite list_lookup_fmap. by rewrite Hi. }
  Qed.

  (* Persistent code needs no accessor: the cell is persistent too. *)
  Lemma codefrag_lookup_acc_pers a0 (cs: list Word) (i: nat) w:
    SimplTC (cs !! i) (Some w) →
    codefrag_pers a0 cs -∗ (a0 ^+ i)%a ↦ₐ□ w @@? None.
  Proof.
    iIntros (Hi) "Hcs". by iApply (codefrag_lookup_pers with "Hcs").
  Qed.

End codefrag.

(* Administrative reduction steps *)
Ltac wp_pure := iApply wp_pure_step_later; [ by auto | iNext ; iIntros "_" ].
Ltac wp_pure_lc hlc := iApply wp_pure_step_later; [ by auto | iNext ; iIntros hlc ].
(* NOTE the last `iIntros "_"` fixes the later 1 introduceed in Iris 4.0.0.
   Remove it from the tactic if necessary. *)
Ltac wp_end := iApply wp_value.
Ltac wp_instr :=
  iApply (wp_bind (fill [SeqCtx]));
  (* Reduce the [fill] under the WP... *)
  let X := fresh in
  set X := (fill _);
  cbv in X;
  subst X;
  cbv beta.

Lemma z_addr_base {fb off off1 off2 : Z} {f0 f1 f2 : finz fb}: (f0 + off1)%f = Some f1 → (f0 + off2)%f = Some f2 → (off2 - off1)%Z = off → (f1 ^+ off)%f = f2.
  Proof. solve_addr. Qed.
Ltac solve_block_move :=
    first [solve_addr+ |
    lazymatch goal with
      | |- (?prev_a ^+ ?off)%f = ?cur_a =>
          match goal with
            | H: (prev_a + ?off1)%a = Some cur_a |- _ => solve_addr+H
            | H1: (?base_a + ?off1)%a = Some prev_a |- _ =>
                match goal with
                | H2 : (base_a + ?off2)%a = Some cur_a |- _ =>
                    apply (z_addr_base H1 H2); solve_addr+
                end
          end
     end ].

(* The normal form of logical words in the proof-mode context is
   [w @@? π]: the coercion [lword_of_word] is unfolded, so that the
   syntactic patterns over [(WCap …) @@? _] apply to coerced words too. *)
Ltac instr_normalize_lwords := try (unfold lword_of_word).

(* Ltac specifically meant for switching to the next block. Use `changePCto` to perform more arbitrary moves *)
Ltac changePC_next_block new_a :=
  instr_normalize_lwords;
  match goal with |- context [ Esnoc _ _ (PC ↦ₚ (WCap _ _ _ _ _ ?prev_a) @@? _)%I ] =>
                    rewrite (_: prev_a = new_a) ; [ | solve_block_move  ] end.
(* More powerful ltac to change the address of the pc. Might take longer to solve than the more specific alternative above.*)
Ltac changePCto0 new_a :=
  instr_normalize_lwords;
  match goal with |- context [ Esnoc _ _ (PC ↦ₚ (WCap _ _ _ _ _ ?a) @@? _)%I ] =>
    rewrite (_: a = new_a); [| solve_addr]
  end.
Tactic Notation "changePCto" constr(a) := changePCto0 a.

(* The contiguity of the code [h], exclusive or persistent. *)
Ltac codefrag_contiguous h HH :=
  lazymatch goal with
  | |- context [ Esnoc _ h (codefrag_pers _ _) ] =>
    iDestruct (codefrag_contiguous_region_pers with h) as %HH
  | _ => iDestruct (codefrag_contiguous_region with h) as %HH
  end.

(* The base address and the code of a code fragment, exclusive or
   persistent. *)
Ltac codefrag_base_code P :=
  lazymatch P with
  | codefrag ?a_base ?code => constr:((a_base, code))
  | codefrag_pers ?a_base ?code => constr:((a_base, code))
  end.

Ltac codefrag_facts h :=
  let h := constr:(h:ident) in
  match goal with |- context [ Esnoc _ h ?P ] =>
  let ac := codefrag_base_code P in
  lazymatch ac with (?a_base, ?code) =>
    (match goal with H : ContiguousRegion a_base _ |- _ => idtac end ||
     let HH := fresh in
     codefrag_contiguous h HH;
     cbn [length map encodeInstrsW] in HH
    );
    (match goal with H : SubBounds _ _ a_base (a_base ^+ _)%a |- _ => idtac end ||
     (try match goal with H : SubBounds ?b ?e _ _ |- _ =>
            let HH := fresh in
            assert (HH: SubBounds b e a_base (a_base ^+ length code)%a) by solve_addr;
            cbn [length map encodeInstrsW] in HH
          end))
  end end.

Ltac clear_codefrag_facts h :=
  let h := constr:(h:ident) in
  match goal with |- context [ Esnoc _ h ?P ] =>
  let ac := codefrag_base_code P in
  lazymatch ac with (?a_base, ?code) =>
    try match goal with H : ContiguousRegion a_base _ |- _ => clear H end;
    try match goal with H : SubBounds _ _ a_base (a_base ^+ _)%a |- _ => clear H end
  end end.

(* Classes for the code sub-block focusing tactic *)

Create HintDb proofmode_focus.
#[export] Hint Constants Opaque : proofmode_focus.
#[export] Hint Variables Opaque : proofmode_focus.

Definition App {A} (l1 l2 ll: list A) :=
  ll = l1 ++ l2.
#[export] Hint Mode App - ! ! - : proofmode_focus.

Lemma App_nil_r A (l: list A) : App l [] l.
Proof. rewrite /App app_nil_r //. Qed.
#[export] Hint Resolve App_nil_r : proofmode_focus.

Lemma App_nil_l A (l: list A) : App [] l l.
Proof. reflexivity. Qed.
#[export] Hint Resolve App_nil_l : proofmode_focus.

Lemma App_nil_default A (l1 l2: list A): App l1 l2 (l1 ++ l2).
Proof. reflexivity. Qed.
#[export] Hint Resolve App_nil_default | 100 : proofmode_focus.

Definition NthSubBlock {A} (ll: list A) (n: nat) (l1: list A) (l: list A) (l2: list A) :=
  ll = l1 ++ l ++ l2.
#[export] Hint Mode NthSubBlock + ! + - - - : proofmode_focus.

Lemma NthSubBlock_O_rest A (l1 l2: list A):
  NthSubBlock (l1 ++ l2) 0 [] l1 l2.
Proof. reflexivity. Qed.
#[export] Hint Resolve NthSubBlock_O_rest : proofmode_focus.

Lemma NthSubBlock_O_last A (l1: list A):
  NthSubBlock l1 0 [] l1 [].
Proof. unfold NthSubBlock. rewrite app_nil_r//. Qed.
#[export] Hint Resolve NthSubBlock_O_last | 100 : proofmode_focus.

Lemma NthSubBlock_S A (l0 ll l1 l2 l3 l0l1: list A) n:
  NthSubBlock ll n l1 l2 l3 →
  App l0 l1 l0l1 →
  NthSubBlock (l0 ++ ll) (S n) l0l1 l2 l3.
Proof. unfold NthSubBlock. intros -> ->. rewrite app_assoc //. Qed.
#[export] Hint Resolve NthSubBlock_S : proofmode_focus.

Section codefrag_subblock.
  Context {Σ:gFunctors} {ceriseg: ceriseG Σ}
          `{MP: MachineParameters}.

  Lemma codefrag_block0_acc a0 (l1 l2: list Word):
    codefrag a0 (l1 ++ l2) -∗
    codefrag a0 l1 ∗
    (codefrag a0 l1 -∗ codefrag a0 (l1 ++ l2)).
  Proof.
    iIntros "H".
    iDestruct (codefrag_contiguous_region with "H") as %Hregion.
    rewrite /codefrag fmap_app. rewrite /codefrag in Hregion.
    destruct Hregion as [an Han]. rewrite length_app in Han |- *.
    iDestruct (region_pointsto_split _ _ (a0 ^+ length l1)%a with "H") as "[H1 H2]".
    { by solve_addr. }
    { by rewrite ?length_fmap /finz.dist; solve_addr. }
    iFrame. iIntros "H1".
    rewrite region_pointsto_split; first iFrame.
    + solve_addr.
    + rewrite ?length_fmap /finz.dist; solve_addr.
  Qed.

  Lemma codefrag_block_acc (n: nat) a0 (cs: list Word) l1 l l2:
    NthSubBlock cs n l1 l l2 →
    codefrag a0 cs -∗
    ∃ (ai: Addr), ⌜(a0 + length l1)%a = Some ai⌝ ∗
    codefrag ai l ∗
    (codefrag ai l -∗ codefrag a0 cs).
  Proof.
    unfold NthSubBlock. intros ->. iIntros "H".
    iDestruct (codefrag_contiguous_region with "H") as %[a1 Ha1].
    rewrite /codefrag !fmap_app.
    rewrite !length_app in Ha1 |- *.
    iDestruct (region_pointsto_split _ _ (a0 ^+ length l1)%a with "H") as "[H1 H2]".
    { solve_addr. }
    { rewrite ?length_fmap /finz.dist; solve_addr. }
    iExists (a0 ^+ length l1)%a. iSplitR; first (iPureIntro; solve_addr).
    iDestruct (region_pointsto_split _ _ ((a0 ^+ length l1) ^+ length l)%a with "H2") as "[H2 H3]".
    { solve_addr. }
    { rewrite ?length_fmap /finz.dist; solve_addr. }
    iFrame.
    iIntros "H2".
    rewrite region_pointsto_split; [iFrame|..]; cycle 1.
    { solve_addr. }
    { rewrite ?length_fmap /finz.dist; solve_addr. }
    rewrite region_pointsto_split; first iFrame.
    { solve_addr. }
    { rewrite ?length_fmap /finz.dist; solve_addr. }
  Qed.

  Lemma codefrag_block_acc_pers (n: nat) a0 (cs: list Word) l1 l l2:
    NthSubBlock cs n l1 l l2 →
    codefrag_pers a0 cs -∗
    ∃ (ai: Addr), ⌜(a0 + length l1)%a = Some ai⌝ ∗
    codefrag_pers ai l.
  Proof.
    unfold NthSubBlock. intros ->. iIntros "H".
    iDestruct (codefrag_contiguous_region_pers with "H") as %[a1 Ha1].
    rewrite !length_app in Ha1.
    iDestruct (codefrag_app_pers with "H") as "[_ H]".
    iDestruct (codefrag_app_pers with "H") as "[H _]".
    iExists (a0 ^+ length l1)%a. iFrame. iPureIntro. solve_addr.
  Qed.

  (* The continuation of a focus or of an instruction lookup on persistent
     code: the code is persistent, so it is given back whatever is given. *)
  Lemma codefrag_pers_cont a0 (cs: list Word) (P: iProp Σ):
    codefrag_pers a0 cs -∗ (P -∗ codefrag_pers a0 cs).
  Proof. iIntros "#H _". iExact "H". Qed.

End codefrag_subblock.

(* Persistent code given back in the spatial context (e.g. by a continuation)
   is moved to the intuitionistic context. *)
Ltac codefrag_pers_intuitionistic h :=
  let h := constr:(h:ident) in
  lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ =>
    lazymatch Γs with
    | context [ Esnoc _ h (codefrag_pers _ _) ] =>
      let pat := constr:(intro_patterns.IIntuitionistic (intro_patterns.IIdent h)) in
      iDestructHyp h as pat
    | _ => idtac
    end
  end.

(* On persistent code, the continuation [hcont] of a fragment [hi] of the
   code [h] is created when its name is fresh: [hcont : hi -∗ h]. *)
Ltac codefrag_pers_mk_cont h hi hcont :=
  let h := constr:(h:ident) in
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  lazymatch goal with |- context [ Esnoc _ hi ?P ] =>
    try iPoseProof (codefrag_pers_cont _ _ P with h) as hcont
  end.

Lemma focus_block_0_SubBounds (b e b' : Addr) k m :
  SubBounds b e b' (b' ^+ k)%a →
  ContiguousRegion b' m →
  (0 ≤ m)%Z →
  (m ≤ k)%Z →
  SubBounds b e b' (b' ^+ m)%a.
Proof. solve_addr. Qed.

(* More efficient version of codefrag_facts (avoids calling [solve_addr])
   because we have slightly more information when doing focus_block_0 *)
Ltac focus_block_0_codefrag_facts hi a0 :=
  let HCR := fresh in
  codefrag_contiguous hi HCR;
  cbn [length map encodeInstrsW] in HCR;
  try lazymatch goal with HSB : SubBounds ?b ?e a0 (a0 ^+ _)%a |- _ =>
    let HSB' := fresh in
    unshelve epose proof (focus_block_0_SubBounds _ _ _ _ _ HSB HCR _ _) as HSB';
    [solve_pure ..|];
    cbn [length map encodeInstrsW] in HSB'
  end.

Ltac focus_block_0 h hi hcont :=
  let h := constr:(h:ident) in
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let x := iFresh in
  match goal with |- context [ Esnoc _ h (codefrag ?a0 _) ] =>
    iPoseProof (codefrag_block0_acc with h) as x;
    eapply tac_and_destruct with x _ hi hcont _ _ _;
    [pm_reflexivity|pm_reduce;tc_solve|
     pm_reduce;
     lazymatch goal with
     | |- False =>
       let hi := pretty_ident hi in
       let hcont := pretty_ident hcont in
       fail "focus_block_0:" hi "or" hcont "not fresh"
     | _ => idtac
     end];
    focus_block_0_codefrag_facts hi a0
  end.

(* On persistent code, the block is a persistent fragment [hi] of [h], and
   [h] is kept; the continuation [hcont] only gives [h] back. *)
Ltac focus_block_0_pers h hi hcont :=
  codefrag_pers_intuitionistic h;
  let h := constr:(h:ident) in
  let hi := constr:(hi:ident) in
  let x := iFresh in
  let y := iFresh in
  match goal with |- context [ Esnoc _ h (codefrag_pers ?a0 _) ] =>
    iPoseProof (codefrag_app_pers with h) as x;
    eapply tac_and_destruct with x _ hi y _ _ _;
    [pm_reflexivity|pm_reduce;tc_solve|pm_reduce];
    iClear y;
    let pat := constr:(intro_patterns.IIntuitionistic (intro_patterns.IIdent hi)) in
    iDestructHyp hi as pat;
    codefrag_pers_mk_cont h hi hcont;
    focus_block_0_codefrag_facts hi a0
  end.

Tactic Notation "focus_block_0" constr(h) "as" constr(hi) constr(hcont) :=
  let h' := constr:(h:ident) in
  lazymatch goal with
  | |- context [ Esnoc _ h' (codefrag_pers _ _) ] => focus_block_0_pers h hi hcont
  | _ => focus_block_0 h hi hcont
  end.

Lemma focus_block_SubBounds (b e b' b'': Addr) k m n :
  SubBounds b e b' (b' ^+ k)%a →
  ContiguousRegion b'' m →
  (b' + n)%a = Some b'' →
  (0 ≤ n)%Z →
  (0 ≤ m)%Z →
  ((n + m) <= k)%Z →
  SubBounds b e b'' (b'' ^+ m)%a.
Proof. solve_addr. Qed.

(* More efficient version of codefrag_facts (avoids calling [solve_addr])
   because we have slightly more information when doing focus_block *)
Ltac focus_block_codefrag_facts hi a0 Ha_base :=
  let HCR := fresh in
  codefrag_contiguous hi HCR;
  cbn [length map encodeInstrsW] in HCR;
  try lazymatch goal with HSB : SubBounds ?b ?e a0 (a0 ^+ _)%a |- _ =>
    let HSB' := fresh in
    unshelve epose proof (focus_block_SubBounds _ _ _ _ _ _ _ HSB HCR Ha_base _ _ _) as HSB';
    [solve_pure ..|];
    cbn [length map encodeInstrsW] in HSB'
  end.

(* On persistent code, the block is a persistent fragment [hi] of [h], and
   [h] is kept; the continuation [hcont] only gives [h] back. *)
Ltac focus_block_nochangePC_pers n h a_base Ha_base hi hcont :=
  codefrag_pers_intuitionistic h;
  let h := constr:(h:ident) in
  let hi := constr:(hi:ident) in
  let x := iFresh in
  match goal with |- context [ Esnoc _ h (codefrag_pers ?a0 _) ] =>
    iPoseProof ((codefrag_block_acc_pers n) with h) as (a_base) x;
      [ once (typeclasses eauto with proofmode_focus) | ];
    let xbase := iFresh in
    eapply tac_and_destruct with x _ xbase hi _ _ _;
      [pm_reflexivity|pm_reduce;tc_solve|pm_reduce];
    iPure xbase as Ha_base;
    let pat := constr:(intro_patterns.IIntuitionistic (intro_patterns.IIdent hi)) in
    iDestructHyp hi as pat;
    codefrag_pers_mk_cont h hi hcont;
    focus_block_codefrag_facts hi a0 Ha_base
  end.

Ltac focus_block n h a_base Ha_base hi hcont :=
  let h := constr:(h:ident) in
  lazymatch goal with
  | |- context [ Esnoc _ h (codefrag_pers _ _) ] =>
    focus_block_nochangePC_pers n h a_base Ha_base hi hcont;
    changePC_next_block a_base
  | _ =>
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let x := iFresh in
  match goal with |- context [ Esnoc _ h (codefrag ?a0 _) ] =>
    iPoseProof ((codefrag_block_acc n) with h) as (a_base) x;
      [ once (typeclasses eauto with proofmode_focus) | ];
    let xbase := iFresh in
    let y := iFresh in
    eapply tac_and_destruct with x _ xbase y _ _ _;
      [pm_reflexivity|pm_reduce;tc_solve|pm_reduce];
    iPure xbase as Ha_base;
    eapply tac_and_destruct with y _ hi hcont _ _ _;
      [pm_reflexivity|pm_reduce;tc_solve|pm_reduce];
    focus_block_codefrag_facts hi a0 Ha_base;
    changePC_next_block a_base
  end end.

Tactic Notation "focus_block" constr(n) constr(h) "as"
       ident(a_base) simple_intropattern(Ha_base) constr(hi) constr(hcont) :=
  focus_block n h a_base Ha_base hi hcont.

Ltac focus_block_nochangePC n h a_base Ha_base hi hcont :=
  let h := constr:(h:ident) in
  lazymatch goal with
  | |- context [ environments.Esnoc _ h (codefrag_pers _ _) ] =>
    focus_block_nochangePC_pers n h a_base Ha_base hi hcont
  | _ =>
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let x := iFresh in
  match goal with |- context [ environments.Esnoc _ h (codefrag ?a0 _) ] =>
                    iPoseProof ((codefrag_block_acc n) with h) as (a_base) x;
                    [ once (typeclasses eauto with proofmode_focus) | ];
                    let xbase := iFresh in
                    let y := iFresh in
                    eapply coq_tactics.tac_and_destruct with x _ xbase y _ _ _;
                    [reduction.pm_reflexivity|reduction.pm_reduce;tc_solve|reduction.pm_reduce];
                    iPure xbase as Ha_base;
                    eapply coq_tactics.tac_and_destruct with y _ hi hcont _ _ _;
                    [reduction.pm_reflexivity|reduction.pm_reduce;tc_solve|reduction.pm_reduce];
                    focus_block_codefrag_facts hi a0 Ha_base
  end end.
Tactic Notation "focus_block_nochangePC" constr(n) constr(h) "as"
  ident(a_base) simple_intropattern(Ha_base) constr(hi) constr(hcont) :=
  focus_block_nochangePC n h a_base Ha_base hi hcont.


Ltac unfocus_block hi hcont h :=
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let h := constr:(h:ident) in
  clear_codefrag_facts hi;
  lazymatch goal with
  | |- context [ Esnoc _ hi (codefrag_pers _ _) ] =>
    iClear hi; try iClear hcont; codefrag_pers_intuitionistic h
  | _ => iDestruct (hcont with hi) as h
  end.

Tactic Notation "unfocus_block" constr(hi) constr(hcont) "as" constr(h) :=
  unfocus_block hi hcont h.

(* "iApply with on-demand framing" *)

(* Variant of Iris' [tac_specialize_frame] where the conclusion [Q] of the
   wand is kept in the goal: the premise [P1] is framed in place from the
   context, and [P2 -∗ Q] is unlocked once [P1] has been framed entirely.
   The wand [R] is not a hypothesis of the context but is given as a proof
   [⊢ R] (e.g. an instruction rule, after the elimination of its Coq-level
   premises by [iIntoEmpValid]); as with [iPoseProof], it is used as an
   intuitionistic hypothesis. *)
Lemma tac_specialize_frame' {PROP: bi} (Δ: envs PROP) R P1 P2 Q :
  (⊢ R) →
  IntoWand true false R P1 P2 →
  envs_entails Δ (P1 ∗ locked (P2 -∗ Q)%I) →
  envs_entails Δ Q.
Proof.
  intros HR ? HΔ. rewrite envs_entails_unseal in HΔ |- *. rewrite HΔ. unlock.
  assert (⊢ □ R) as HR' by (iIntros "!>"; iApply HR).
  rewrite -(bi.emp_sep (P1 ∗ (P2 -∗ Q))%I) {1}HR'.
  iIntros "(HR & HP1 & HQ)". iApply "HQ".
  iApply (into_wand true false R P1 P2 with "HR HP1").
Qed.

(* Specialization of the wand [R] with on-demand framing of its premise [P1],
   where its conclusion [P2] is applied to the goal [Q] as in [iApply]. [P2]
   is unified with the goal before framing. *)
Lemma tac_specialize_frame_apply {PROP: bi} (Δ: envs PROP) R P1 P2 B Q :
  (⊢ R) →
  IntoWand true false R P1 P2 →
  IntoWand false false P2 B Q →
  envs_entails Δ (P1 ∗ locked B) →
  envs_entails Δ Q.
Proof.
  intros ??? HΔ. eapply tac_specialize_frame'; [done..|].
  rewrite envs_entails_unseal in HΔ |- *. rewrite HΔ. unlock.
  iIntros "[$ HB] HP2". iApply (into_wand false false P2 B Q with "HP2 HB").
Qed.

(* Typeclass instances to look-up framable resources in the goal, for
   [FramableMachineResource] from [machine_utils/tactics.v]
*)

Class FramableSRegisterPointsto (sr: SRegName) (w: Word) := {}.
#[export] Hint Mode FramableSRegisterPointsto + - : typeclass_instances.
Class FramableRegisterPointsto (r: RegName) (w: LWord) := {}.
#[export] Hint Mode FramableRegisterPointsto + - : typeclass_instances.
Class FramableMemoryPointsto (a: Addr) (dq: dfrac) (w: LWord) := {}.
#[export] Hint Mode FramableMemoryPointsto + - - : typeclass_instances.
Class FramableCodefrag (a: Addr) (l: list Word) := {}.
#[export] Hint Mode FramableCodefrag + - : typeclass_instances.

#[export] Instance FramableSRegisterPointsto_default sr w :
  FramableSRegisterPointsto sr w
| 100. Qed.

#[export] Instance FramableRegisterPointsto_default r w :
  FramableRegisterPointsto r w
| 100. Qed.

#[export] Instance FramableMemoryPointsto_default a dq w :
  FramableMemoryPointsto a dq w
| 100. Qed.

#[export] Instance FramableCodefrag_default a l :
  FramableCodefrag a l
| 100. Qed.

#[export] Instance FramableMachineResource_sreg `{ceriseG Σ} sr w :
  FramableSRegisterPointsto sr w →
  FramableMachineResource (sr ↦ₛᵣ w).
Qed.

#[export] Instance FramableMachineResource_pc `{ceriseG Σ} w :
  FramableMachineResource (PC ↦ₚ w).
Qed.

#[export] Instance FramableMachineResource_reg `{ceriseG Σ} r w :
  FramableRegisterPointsto r w →
  FramableMachineResource (r ↦ᵣ w).
Qed.

#[export] Instance FramableMachineResource_mem `{ceriseG Σ} a dq w :
  FramableMemoryPointsto a dq w →
  FramableMachineResource (a ↦ₐ{dq} w).
Qed.

#[export] Instance FramableMachineResource_codefrag `{ceriseG Σ} a l :
  FramableCodefrag a l →
  FramableMachineResource (codefrag a l).
Qed.

#[export] Instance FramableMachineResource_codefrag_pers `{ceriseG Σ} a l :
  FramableCodefrag a l →
  FramableMachineResource (codefrag_pers a l).
Qed.

(* Address claims, for the Subseg rule on heap roots (case 3). *)
#[export] Instance FramableMachineResource_addr_alloc `{ceriseG Σ} a c :
  FramableMachineResource (addr_alloc a c).
Qed.


(* Dereference resources: [deref_res (Some ι) q] is framed from a status
   share [ι ↦st{q} ALive], or from a hypothesis [deref_res (Some ι) q]. The
   identifier must be known: the lookup waits until the register holding the
   capability has been framed. [deref_res None q] is [emp]. *)
Class DerefResId (π : option AId) (ι : AId) := {}.
#[export] Hint Mode DerefResId ! - : typeclass_instances.

#[export] Instance DerefResId_some ι : DerefResId (Some ι) ι.
Qed.

#[export] Instance LookupFramableMachineResource_deref_res `{ceriseG Σ} π ι q :
  DerefResId π ι →
  LookupFramableMachineResource (deref_res π q) (ι ↦st{q} ALive)
| 10.
Qed.

#[export] Instance FramableMachineResource_deref_res `{ceriseG Σ} π ι q :
  DerefResId π ι →
  FramableMachineResource (deref_res π q).
Qed.

#[export] Instance frame_deref_res_status `{ceriseG Σ} p ι q :
  Frame p (ι ↦st{q} ALive) (deref_res (Some ι) q) emp.
Proof. rewrite /Frame /deref_res. iIntros "[H _]". by iApply bi.intuitionistically_if_elim. Qed.

(* Auto-framing from the intuitionistic context, beside the spatial lookup
   of [FramableMachineHyp_default]: a persistent resource (e.g. a persistent
   points-to) is framed and kept. The spatial context is tried first. *)
Class EnvsLookupIntuitionistic {PROP: bi} (Δ: envs PROP) (P: PROP) (i: ident) := {}.
#[export] Hint Mode EnvsLookupIntuitionistic + ! ! - : typeclass_instances.

#[export] Instance EnvsLookupIntuitionistic_here (PROP: bi) (Γp Γs: env PROP) P c i :
  EnvsLookupIntuitionistic (Envs (Esnoc Γp i P) Γs c) P i.
Qed.

#[export] Instance EnvsLookupIntuitionistic_next (PROP: bi) (Γp Γs: env PROP) P Q c i j :
  EnvsLookupIntuitionistic (Envs Γp Γs c) Q j →
  EnvsLookupIntuitionistic (Envs (Esnoc Γp i P) Γs c) Q j.
Qed.

#[export] Instance FramableMachineHyp_intuitionistic Σ (Δ: envs (uPredI (iResUR Σ))) G P i:
  LookupFramableMachineResource G P →
  EnvsLookupIntuitionistic Δ P i →
  FramableMachineHyp Δ G i
| 50.
Qed.

(* remembering names after auto-framing done by iFrameAuto *)

Ltac2 Type hyp_table_kind :=
  [ PCReg | Reg | SReg | Mem | Codefrag | CodefragPers | Claim | DerefRes ].

(* Whether the hypothesis named [hname] is in the intuitionistic context. *)
Ltac2 is_intuitionistic_hyp (hname: constr) :=
  lazy_match! goal with
  | [ |- envs_entails (Envs ?γp _ _) _ ] =>
    match! γp with
    | context [ Esnoc _ (INamed ?n) _ ] => assert_constr_eq n hname; true
    | _ => false
    end
  end.

(* A resource framed from the intuitionistic context is still there: its
   copy given back by the rule is dropped (named "_"). *)
Ltac2 record_framed
      (table: (constr * constr * hyp_table_kind) list ref)
      (framed: constr * constr)
  :=
  let (hname, hh) := framed in
  let hname := if is_intuitionistic_hyp hname then '("_") else hname in
  let (lhs, kind) :=
    lazy_match! hh with
    | (PC ↦ₚ _)%I => ('tt, PCReg)
    | (?r ↦ᵣ _)%I => (r, Reg)
    | (?sr ↦ₛᵣ _)%I => (sr, SReg)
    | (?a ↦ₐ{_} _)%I => (a, Mem)
    | (codefrag ?a _) => (a, Codefrag)
    | (codefrag_pers ?a _) => (a, CodefragPers)
    | (addr_alloc ?a _) => (a, Claim)
    | (st_own ?ι _ _) => (ι, DerefRes)
    | (deref_res (Some ?ι) _) => (ι, DerefRes)
    end in
  table.(contents) := (hname, lhs, kind) :: table.(contents).

(* iApplyCapAuto *)

(* Helpers *)

Ltac solve_to_wand tt :=
    tc_solve ||
    let P := match goal with |- IntoWand _ _ ?P _ _ => P end in
    fail "iSpecialize:" P "not an implication/wand".

Ltac2 iTypeOf (h: constr) :=
  let Δ := match! goal with [ |- envs_entails ?Δ _ ] => Δ end in
  (* XXX should be pm_eval *)
  eval cbv in (envs_lookup $h $Δ).

Ltac2 iFresh () :=
  ltac1:(iStartProof);
  lazy_match! goal with
  | [ |- envs_entails (Envs ?Δp ?Δs ?c) ?q ] =>
    let c' := eval vm_compute in (Pos.succ $c) in
    ltac1:(Δp Δs c' q |-
           change_no_check (envs_entails (Envs Δp Δs c') q))
      (Ltac1.of_constr Δp) (Ltac1.of_constr Δs) (Ltac1.of_constr c')
      (Ltac1.of_constr q);
    '(IAnon $c)
  end.

Ltac iNamedIntro :=
  let x := iFresh in
  iIntros x; iNamed x.
Ltac2 iNamedIntro () := ltac1:(iNamedIntro).

Ltac2 on_lasts tacs :=
  Control.extend [] (fun _ => ()) tacs.


(* iApplyCapAuto_init *)

(* Starts the application of the rule [lem]: its conclusion is applied to the
   goal, and the goal becomes [P1 ∗ locked B], where [P1] is the premise of
   the rule and [B] the premise of its conclusion. As with [iPoseProofCore],
   the Coq-level premises of [lem] become goals, before the main goal; the
   rule does not go through the context. *)
Ltac iSpecializeFrameApplyStart lem :=
  notypeclasses refine
    (tac_specialize_frame_apply _ _ _ _ _ _ (into_emp_valid_proj _ _ _ lem) _ _ _);
  [iIntoEmpValid; try tc_solve
  |solve_to_wand tt
  |tc_solve
  |pm_reduce].

Ltac iApplyHypLast H :=
  eapply tac_apply with H _ _ _;
  [pm_reflexivity
  |tc_solve
  |pm_reduce; pm_prettify].

Ltac2 iApplyCapAutoT_init0 lemma :=
  let tbl := { contents := [] } in
  ltac1:(lem |- once (iSpecializeFrameApplyStart lem)) (Ltac1.of_constr lemma);
  tbl.

Ltac2 iApplyCapAuto_init0 lemma :=
  let _ := iApplyCapAutoT_init0 lemma in ().

Ltac2 Notation "iApplyCapAuto_init" lem(constr) :=
  iApplyCapAuto_init0 lem.

Ltac iApplyCapAuto_init lemma :=
  let f := ltac2:(lem |- iApplyCapAuto_init0 (Option.get (Ltac1.to_constr lem))) in
  f lemma.

(* Name resources in the goal according to the table *)

Definition check_addr_eq (a b: Addr) `{FinZEq _ a b res} := res.

Ltac2 name_cap_resource (name, lhs, kind) :=
  match kind with
  | SReg =>
    match! goal with [ |- context [ (?sr ↦ₛᵣ ?x)%I ] ] =>
      assert_constr_eq sr lhs;
      ltac1:(x sr name |- change (sr ↦ₛᵣ x)%I with (name ∷ (sr ↦ₛᵣ x))%I)
        (Ltac1.of_constr x) (Ltac1.of_constr sr) (Ltac1.of_constr name)
    end
  | PCReg =>
    match! goal with [ |- context [ (PC ↦ₚ ?x)%I ] ] =>
      ltac1:(x name |- change (PC ↦ₚ x)%I with (name ∷ (PC ↦ₚ x))%I)
        (Ltac1.of_constr x) (Ltac1.of_constr name)
    end
  | Reg =>
    match! goal with [ |- context [ (?r ↦ᵣ ?x)%I ] ] =>
      assert_constr_eq r lhs;
      ltac1:(x r name |- change (r ↦ᵣ x)%I with (name ∷ (r ↦ᵣ x))%I)
        (Ltac1.of_constr x) (Ltac1.of_constr r) (Ltac1.of_constr name)
    end
  | Mem =>
    match! goal with [ |- context [ (?a ↦ₐ{?dq} ?x)%I ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(x dq a name |- change (a ↦ₐ{dq} x)%I with (name ∷ (a ↦ₐ{dq} x))%I)
        (Ltac1.of_constr x) (Ltac1.of_constr dq) (Ltac1.of_constr a) (Ltac1.of_constr name)
    end
  | Codefrag =>
    match! goal with [ |- context [ codefrag ?a ?l ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(l a name |- change (codefrag a l) with (name ∷ (codefrag a l)))
        (Ltac1.of_constr l) (Ltac1.of_constr a) (Ltac1.of_constr name)
    end
  | CodefragPers =>
    match! goal with [ |- context [ codefrag_pers ?a ?l ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(l a name |- change (codefrag_pers a l) with (name ∷ (codefrag_pers a l)))
        (Ltac1.of_constr l) (Ltac1.of_constr a) (Ltac1.of_constr name)
    end
  | Claim =>
    match! goal with [ |- context [ addr_alloc ?a ?c ] ] =>
      let is_lhs := eval unfold check_addr_eq in (@check_addr_eq $a $lhs _ _) in
      assert_constr_eq is_lhs 'true;
      ltac1:(c a name |- change (addr_alloc a c) with (name ∷ (addr_alloc a c)))
        (Ltac1.of_constr c) (Ltac1.of_constr a) (Ltac1.of_constr name)
    end
  | DerefRes =>
    (* The identifier may be a projection of the register's word. *)
    match! goal with [ |- context [ deref_res ?π ?q ] ] =>
      let π' := eval cbn in $π in
      assert_constr_eq π' '(Some $lhs);
      ltac1:(q π name |- change (deref_res π q) with (name ∷ (deref_res π q)))
        (Ltac1.of_constr q) (Ltac1.of_constr π) (Ltac1.of_constr name)
    end
  end.

Lemma envs_entails_rew_goal {Σ} (Δ: envs (uPredI (iResUR Σ))) P P' :
  P = P' →
  envs_entails Δ P' →
  envs_entails Δ P.
Proof. intros ->. auto. Qed.

Ltac2 reintro_cap_resources tbl :=
  (refine '(@envs_entails_rew_goal _ _ _ _ _ _);
   Control.shelve_unifiable ()) >
  [ List.iter (fun x => try (name_cap_resource x)) (tbl.(contents)); reflexivity | () ];
  iNamedIntro ().

(* cleanup *)
Ltac prove_cap_word_condition P :=
  constr:(ltac:(first [done | solve_pure]) : P).

Ltac cap_word_bool b :=
  match goal with
  | _ => let H := prove_cap_word_condition constr:(b = true) in constr:((true, H))
  | _ => let H := prove_cap_word_condition constr:(b = false) in constr:((false, H))
  end.

Ltac simplify_store_word p w :=
  without_evars p; without_evars w;
  first [
    let H := prove_cap_word_condition constr:(isWL p = true) in
    rewrite (store_word_isWL p w H)
  | let H := prove_cap_word_condition constr:(get_tag w = false) in
    rewrite (store_word_untagged p w H)
  | let H := prove_cap_word_condition constr:(canStore p w = true) in
    rewrite (store_word_canStore p w H)
  | let Hp := prove_cap_word_condition constr:(writeAllowed p = true) in
    let Hw := prove_cap_word_condition constr:(isLocalWord w = false) in
    rewrite (store_word_not_local p w Hp Hw)
  | let H := prove_cap_word_condition constr:(canStore p w = false) in
    let P := constr:(store_word p w = clear_tag w) in
    let Heq := constr:(ltac:(by rewrite /store_word H) : P) in
    rewrite Heq ].

Ltac simplify_load_word p w :=
  without_evars p; without_evars w;
  first [
    lazymatch w with
    | WInt ?z => rewrite (load_word_int p z)
    | WCap ?t ?pw ?g ?b ?e ?a => rewrite (load_word_cap t p pw g b e a)
    | WSentry ?t ?pw ?g ?b ?e ?a => rewrite (load_word_sentry t p pw g b e a)
    | WSealRange ?t ?pw ?g ?b ?e ?a => rewrite (load_word_sealrange t p pw g b e a)
    | WSealed ?o ?sb => rewrite (load_word_sealed p o sb)
    end
  | let dl := cap_word_bool constr:(isDL p) in
    let dro := cap_word_bool constr:(isDRO p) in
    lazymatch dl with (?bdl, ?Hdl) =>
    lazymatch dro with (?bdro, ?Hdro) =>
      let result := constr:(if bdro then readonly (if bdl then deeplocal (borrow w) else w)
                            else (if bdl then deeplocal (borrow w) else w)) in
      let P := constr:(load_word p w = result) in
      let Heq := constr:(ltac:(by rewrite /load_word Hdl Hdro) : P) in
      rewrite Heq
    end end ].

Ltac reduce_cap_word :=
  cbn [store_word canStore isLocalWord isLocalSealable isLocal isWL writeAllowed andb
       load_word load_word_perm isDL isDRO
       unseal_sb unseal_locality borrow borrow_sb deeplocal deeplocal_sb deeplocal_perm
       readonly readonly_sb readonly_perm
       clear_tag clear_tag_sealable get_tag get_tag_sealable].

(* Rewrite known word shapes and use available tag/permission facts before
   reducing definitions. Symbolic variables are supported; unresolved evars
   use reduction only, since rewriting could instantiate an operand to match
   a lemma. Neither path splits unknown tag or permission conditions. *)
Ltac simplify_cap_word_known :=
  repeat progress (
    rewrite ?get_tag_clear_tag ?get_tag_clear_tag_sealable ?get_tag_unseal
            ?unseal_global ?unseal_local
            ?get_tag_load_word ?get_tag_borrow ?get_tag_deeplocal
            ?get_tag_readonly ?get_tag_force_global ?get_tag_updatePcPerm
            ?clear_tag_idempotent ?clear_tag_sealable_idempotent
            ?borrow_sb_idempotent ?force_global_borrow ?force_global_borrow_sb;
    repeat match goal with
    | |- context [store_word ?p ?w] => simplify_store_word p w
    | |- context [load_word ?p ?w] => simplify_load_word p w
    | |- context [clear_tag ?w] =>
      without_evars w;
      let H := prove_cap_word_condition constr:(get_tag w = false) in
      rewrite (clear_tag_untagged w H)
    end;
    reduce_cap_word).

Ltac simplify_cap_word :=
  let G := match goal with |- ?G => G end in
  tryif (has_evar G || match goal with x := ?v |- _ => has_evar v end)
  then reduce_cap_word else simplify_cap_word_known.

(* TODO: make this extensible. Remove updatePcPerm? unfolding sometimes causes issues. *)
Ltac2 iApplyCapAuto_cleanup () :=
  cbn [rules_Get.denote rules_BinOp.denote updatePcPerm deref_res
       get_a get_b get_e get_p get_l
       get_a_sealable get_b_sealable get_e_sealable get_p_sealable get_l_sealable
       encodePermSum
       lload_word lstore_word lclear_tag lupdatePcPerm lift_word lw lprov lword_of_word];
  ltac1:(simplify_cap_word).

(* iApplyCapAutoCore *)

(* The share of [deref_res None q] is irrelevant: once the identifier is
   known to be [None], an undetermined share is set to [1]. *)
Ltac instantiate_deref_res_none :=
  repeat match goal with
  | |- context [ deref_res ?π ?q ] =>
    is_evar q; assert_fails (has_evar π);
    let π' := eval cbn in π in
    lazymatch π' with None => unify q 1%Qp end
  end.

(* The resource given back for [deref_res None q] is an anonymous [emp]. *)
Ltac clear_anonymous_emp :=
  repeat match goal with
  | |- envs_entails (Envs _ ?Γs _) _ =>
    match Γs with context [ Esnoc _ (IAnon ?n) emp%I ] =>
      let h := constr:(IAnon n) in iClear h
    end
  end.

(* Once the premise of the rule has been framed, unlocks the rest of the
   goal, or reports the resources that could not be framed. *)
Ltac iUnlockFramed :=
  first
    [ notypeclasses refine (tac_unlock_emp _ _ _)
    | notypeclasses refine (tac_unlock_True _ _ _)
    | notypeclasses refine (tac_unlock _ _ _)
    | lazymatch goal with
      | |- envs_entails _ (?remaining ∗ locked _) =>
        fail "iApplyCapAuto: the following resources could not be found in the context:"
             remaining
      end ].

Ltac2 iApplyCapAutoCore lemma :=
  let tbl := iApplyCapAutoT_init0 lemma in
  let iFrameCap := fun () => record_framed tbl (iFrameAuto ()) in
  grepeat (fun _ =>
    Control.extend [] (fun _ => try (Control.once solve_pure_iinstr))
      [ (fun _ => try (iFrameCap ())) ]);
  on_lasts [ (fun _ =>
    ltac1:(instantiate_deref_res_none);
    ltac1:(iUnlockFramed);
    try ltac1:(iNext);
    reintro_cap_resources tbl;
    iApplyCapAuto_cleanup ();
    ltac1:(clear_anonymous_emp)
  )].

Ltac2 Notation "iApplyCapAuto" lem(constr) := iApplyCapAutoCore lem.
Tactic Notation "iApplyCapAuto" constr(lem) :=
  let f := ltac2:(lem |- iApplyCapAutoCore (Option.get (Ltac1.to_constr lem))) in
  f lem.



(* iInstr *)

Definition as_weak_addr_incr (a b: Addr) (z: Z) `{AsWeakFinZIncr _ a b z} :=
  (b, Z.to_nat z).

Lemma addr_incr_zero (a: Addr) : (a ^+ 0)%a = a.
Proof. solve_addr. Qed.

Lemma addr_incr_zero_nat (a: Addr) : (a ^+ 0%nat)%a = a.
Proof. solve_addr. Qed.

(* The current PC address, stated as a logical word or through the
   [lword_of_word] coercion. *)
Ltac instr_pc_addr :=
  lazymatch goal with
  | |- context [ Esnoc _ _ (PC ↦ₚ ((WCap _ _ _ _ _ ?pc_a) @@? _))%I ] => pc_a
  | |- context [ Esnoc _ _ (PC ↦ₚ lword_of_word (WCap _ _ _ _ _ ?pc_a))%I ] => pc_a
  end.

(* On persistent code, the instruction [hi] is a persistent points-to. [hi] is
   put in the spatial context, so that it is framed only into the fetch
   premise of the rule (a hypothesis of the intuitionistic context is framed
   into every premise it unifies with). The continuation [hcont : hi -∗
   hprog] only gives the code back: it is created when it has a name other
   than [hprog], and omitted when it is [hprog] (the code stays, and [hi] is
   dropped with [iClear] or [iInstr_close]) or anonymous (as in [iInstr]). *)
Ltac instr_lookup0_pers hprog hi hcont :=
  codefrag_pers_intuitionistic hprog;
  let hprog := constr:(hprog:ident) in
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  lazymatch goal with |- context [ Esnoc _ hprog (codefrag_pers ?a_base _) ] =>
    let pc_a := instr_pc_addr in
    let base_off := eval unfold as_weak_addr_incr in
      (@as_weak_addr_incr pc_a a_base _ _) in
    lazymatch base_off with
    | (?base, ?off) =>
      iPoseProofCore (codefrag_lookup_acc_pers _ _ off with hprog) as false (fun H =>
        let pat := constr:(intro_patterns.ISpatial (intro_patterns.IIdent hi)) in
        iDestructHyp H as pat;
        rewrite ?addr_incr_zero ?addr_incr_zero_nat
      );
      tryif constr_eq hcont hprog then idtac
      else
        (lazymatch hcont with
         | INamed _ => codefrag_pers_mk_cont hprog hi hcont
         | _ => idtac
         end)
    end
  end.

Ltac instr_lookup0 hprog hi hcont :=
  let hprog := constr:(hprog:ident) in
  lazymatch goal with
  | |- context [ Esnoc _ hprog (codefrag_pers _ _) ] => instr_lookup0_pers hprog hi hcont
  | |- context [ Esnoc _ hprog (codefrag ?a_base _) ] =>
    let pc_a := instr_pc_addr in
    let base_off := eval unfold as_weak_addr_incr in
      (@as_weak_addr_incr pc_a a_base _ _) in
    lazymatch base_off with
    | (?base, ?off) =>
      iPoseProofCore (codefrag_lookup_acc _ _ off with hprog) as false (fun H =>
        eapply tac_and_destruct with H _ hi hcont _ _ _;
        [pm_reflexivity
        |pm_reduce; tc_solve
        |pm_reduce];
        rewrite ?addr_incr_zero ?addr_incr_zero_nat
      )
     end
  end.

Tactic Notation "iInstr_lookup" constr(hprog) "as" constr(hi) constr(hcont) :=
  instr_lookup0 hprog hi hcont.

Ltac instr_get_rule_using dispatch hi cont :=
  let hi := constr:(hi:ident) in
  once (
    (lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ{_} (encodeInstrW ?instr) @@? _)%I ] => idtac end
     + (lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ{_} ?instr)%I ] =>
           fail 1 "Next instruction is not of the form (encodeInstrW _):" instr
         end + fail "" hi "not found"))
  );
  lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ{_} (encodeInstrW ?instr) @@? _)%I ] =>
    dispatch instr cont
  end.

Ltac instr_get_rule0 hi cont :=
  instr_get_rule_using dispatch_instr_rule hi cont.

Tactic Notation "iInstr_get_rule" constr(hi) tactic(cont) := instr_get_rule0 hi cont.

(* On persistent code, the instruction looked up is dropped: it is the
   persistent points-to to an instruction in the spatial context, or else an
   anonymous one. *)
Ltac instr_close_pers :=
  lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ =>
  first
    [ lazymatch Γs with context [ Esnoc _ ?hi (_ ↦ₐ□ encodeInstrW _ @@? _)%I ] =>
        iClear hi
      end
    | lazymatch goal with
      | |- context [ Esnoc _ (IAnon ?n) (_ ↦ₐ□ encodeInstrW _ @@? _)%I ] =>
        let hi := constr:(IAnon n) in
        iClear hi
      end ]
  end.

Ltac instr_close hprog :=
  let hprog' := constr:(hprog:ident) in
  lazymatch goal with
  | |- context [ Esnoc _ hprog' (codefrag_pers _ _) ] => instr_close_pers
  | _ =>
  (* [hi] goes through the instruction rule and is re-introduced from its
     post-condition, so its name may have changed: recover [hi] and
     [hcont] by shape. *)
  (* XXX make this a bit more robust *)
  lazymatch goal with |- context [ Esnoc _ ?hi (_ ↦ₐ encodeInstrW _ @@? _)%I ] =>
  lazymatch goal with |- context [ Esnoc _ ?hcont (_ ↦ₐ encodeInstrW _ @@? _ -∗ _)%I ] =>
    notypeclasses refine (tac_specialize false _ hi _ hcont _ _ _ _ _ _ _ _ _);
    [pm_reflexivity
    |pm_reflexivity
    |tc_solve
    |pm_reduce];
    iRename hcont into hprog
  end end
  end.

Tactic Notation "iInstr_close" constr(H) := instr_close H.

(* NOTE: iCombine doesn't allow to pass IAnon, so here it is *)
Tactic Notation "iCombine_ident" constr(Hs) "as" constr(pat) :=
  let H := iFresh in
  let Δ := iGetCtx in
  notypeclasses refine (tac_combine_as _ _ _ Hs _ _ H _ _ _ _ _ _);
  [pm_reflexivity ||
     let Hs := iMissingHypsCore Δ Hs in
     fail "iCombine: hypotheses" Hs "not found"
  |tc_solve
  |pm_reflexivity ||
     let H := pretty_ident H in
     fail "iCombine:" H "not fresh"
  (* should never happen in normal usage, since [H := iFresh]
     FIXME: improve once consistent error messages are added,
     see https://gitlab.mpi-sws.org/iris/iris/-/issues/499 *)
  |iDestructHyp H as pat].

Tactic Notation "iCombine_ident" constr(H1) constr(H2) "as" constr(pat) :=
  iCombine_ident [H1;H2] as pat.


(* Rewrites [WInt (if decide (r = cnull) then 0 else 0)] (from the rules
   writing an immediate to a register) to [WInt 0]. The occurrences are found
   syntactically, then changed by conversion when [decide (r = cnull)]
   computes (concrete [r]), or rewritten otherwise. *)
Ltac simpl_cnull_zero :=
  repeat
    match goal with
    | |- context [ WInt (if decide (?r = cnull) then ?z1 else ?z2) ] =>
        unify z1 0%Z; unify z2 0%Z;
        first
          [ change (WInt (if decide (r = cnull) then z1 else z2)) with (WInt 0)
          | replace (WInt (if decide (r = cnull) then z1 else z2)) with (WInt 0)
              by (destruct (decide _); done) ]
    end.

Ltac instr_finish hprog hlc hlc' :=
  instr_close hprog;
  simpl_cnull_zero;
  try wp_pure_lc hlc';
  try (iCombine_ident (INamed hlc) hlc' as (INamed hlc)).

(* Integer operands are matched through [IsLInt] rather than by framing a
   [WInt _] points-to, so a rule only applies if its [IsLInt] premises are
   proved. Fail otherwise, so that the dispatcher tries the next rule (e.g.
   [wp_binop_fail_z_r] when the register holds a capability). Other side
   goals are left to the caller. *)
Ltac instr_commit_lint :=
  lazymatch goal with
  | |- IsLInt _ _ => solve [ltac2:(solve_pure_iinstr ())]
  | _ => idtac
  end.

Ltac instr_apply_rule hprog hlc hlc' rule :=
  iApplyCapAuto rule;
  [ instr_commit_lint .. | instr_finish hprog hlc hlc' ].

(* TODO: find a way of displaying an error message if iApplyCapAuto fails,
   displaying the rule it was called on, and without silencing iApplyCapAuto's
   own error messages? *)
Ltac instr_using_rule dispatch apply_rule hprog hlc :=
  instr_normalize_lwords;
  let hi := iFresh in
  let hcont := iFresh in
  let hlc' :=
    match goal with
    | |- context [ Esnoc _ (INamed hlc) (£ ?n)%I ] => iFresh
    | _  => hlc
    end
  in
  iInstr_lookup hprog as hi hcont;
  try wp_instr;
  instr_get_rule_using dispatch hi ltac:(fun rule =>
    apply_rule hprog hlc hlc' rule).

Ltac instr_using dispatch hprog hlc :=
  instr_using_rule dispatch instr_apply_rule hprog hlc.

(* Explicit invalidation leaves the semantic premises that automation cannot
   prove to the caller; the Subseg conversion-overflow rules require their
   evidence before being selected. *)
Ltac instr_apply_invalidation hprog hlc hlc' rule :=
  iApplyCapAuto rule;
  [ instr_commit_lint; try instr_auto_solve_invalidation; instr_guard_invalidation_premise ..
  | instr_finish hprog hlc hlc'; try done ].

(* The success interface is the ordinary instruction-rule dispatch,
   including instructions whose specified behavior is Halt or Fail. *)
Ltac instr_lc hprog hlc := instr_using dispatch_instr_rule hprog hlc.
Ltac iInstr_lc hprog hlc := instr_lc hprog hlc.
Tactic Notation "iInstr_success" constr(H) := instr_lc H "_".
Tactic Notation "iInstr_success" constr(H) "with" constr(Hlc) := instr_lc H Hlc.
Tactic Notation "iInstr" constr(H) := iInstr_success H.
Tactic Notation "iInstr" constr(H) "with" constr(Hlc) := iInstr_success H with Hlc.

(* Runtime failure of the current instruction: the PC and the operand
   registers are returned unchanged and the result is [FailedV]. *)
Tactic Notation "iInstr_fail" constr(H) :=
  instr_using dispatch_instr_failure H "_";
  try solve [instr_auto_solve_failure | by simplify_map_eq].
Tactic Notation "iInstr_fail" constr(H) "with" constr(Hlc) :=
  instr_using dispatch_instr_failure H Hlc;
  try solve [instr_auto_solve_failure | by simplify_map_eq].

(* The instruction executes, but its result is a capability whose validity
   tag is cleared. *)
Tactic Notation "iInstr_invalidate" constr(H) :=
  instr_normalize_register_aliases;
  instr_using_rule dispatch_instr_invalidation instr_apply_invalidation H "_".
Tactic Notation "iInstr_invalidate" constr(H) "with" constr(Hlc) :=
  instr_normalize_register_aliases;
  instr_using_rule dispatch_instr_invalidation instr_apply_invalidation H Hlc.

(** * Explicit instruction rules

    [iInstrApply "Hcode" rule with "spat" as (x1 … xn) "ipat"] applies an
    explicit instruction [rule] to the next instruction of the code fragment
    ["Hcode"]. The instruction points-to is looked up, framed into the
    precondition of [rule] and removed from its postcondition by the tactic:
    it never appears in [spat] or [ipat]. The side goals that [solve_pure]
    does not prove stay before the main goal. In the main goal, the
    postcondition is introduced with [x1 … xn] and [ipat]; in every branch
    that gives the instruction back, [wp_pure] is tried and the instruction is
    put back into the code fragment.

    Split form, for a step between the lookup and the rule (e.g. opening an
    invariant): [iInstrStart "Hcode"] looks up the instruction,
    [iInstrApply rule with "spat" as … "ipat"] continues the started
    instruction, and [iInstrEnd] introduces the pending modality, takes the
    pure step and puts the instruction back if not done yet.

    [iInstrApply "Hcode" with "Hlc" rule …] collects the later credit of the
    pure step into ["Hlc"], as [iInstr "Hcode" with "Hlc"]. *)

(* [InstrFront I P Q]: the instruction [I] is at the front of [P], i.e.
   [P ⊢ I ∗ Q], through [∗] and [∃]. *)
Class InstrFront {PROP : bi} (I P Q : PROP) := instr_front : P ⊢ I ∗ Q.
#[export] Hint Mode InstrFront + + ! - : typeclass_instances.

(* [InstrFrontPost I P Q fl]: [Q] is [P] with [I] moved to the front of the
   branches of its top-level disjunction marked [true] in [fl]. *)
Class InstrFrontPost {PROP : bi} (I P Q : PROP) (fl : list bool) :=
  instr_front_post : P ⊢ Q.
#[export] Hint Mode InstrFrontPost + + ! - - : typeclass_instances.

Section instr_front.
  Context {PROP : bi}.
  Implicit Types I P Q : PROP.

  #[global] Instance instr_front_here I : InstrFront I I emp | 0.
  Proof. rewrite /InstrFront. iIntros "$". Qed.
  #[global] Instance instr_front_sep_here I Q : InstrFront I (I ∗ Q) Q | 0.
  Proof. by rewrite /InstrFront. Qed.
  #[global] Instance instr_front_sep_r I P Q Q' :
    InstrFront I Q Q' → InstrFront I (P ∗ Q) (P ∗ Q') | 1.
  Proof.
    rewrite /InstrFront => HQ. rewrite HQ. iIntros "(HP & HI & HQ)". iFrame.
  Qed.
  #[global] Instance instr_front_sep_l I P P' Q :
    InstrFront I P P' → InstrFront I (P ∗ Q) (P' ∗ Q) | 2.
  Proof.
    rewrite /InstrFront => HP. rewrite HP. iIntros "((HI & HP) & HQ)". iFrame.
  Qed.
  #[global] Instance instr_front_exist {A} I (Φ Ψ : A → PROP) :
    (∀ x, InstrFront I (Φ x) (Ψ x)) → InstrFront I (∃ x, Φ x) (∃ x, Ψ x) | 1.
  Proof.
    rewrite /InstrFront => HΦ. iIntros "[%x H]".
    iDestruct (HΦ x with "H") as "[$ H]". by iExists x.
  Qed.

  #[global] Instance instr_front_post_or I P1 P2 Q1 Q2 b fl :
    InstrFrontPost I P1 Q1 [b] → InstrFrontPost I P2 Q2 fl →
    InstrFrontPost I (P1 ∨ P2) (Q1 ∨ Q2) (b :: fl) | 0.
  Proof.
    rewrite /InstrFrontPost => H1 H2. iIntros "[H|H]".
    - iLeft. by iApply H1.
    - iRight. by iApply H2.
  Qed.
  #[global] Instance instr_front_post_branch I P Q :
    InstrFront I P Q → InstrFrontPost I P (I ∗ Q) [true] | 1.
  Proof. done. Qed.
  #[global] Instance instr_front_post_none I P : InstrFrontPost I P P [false] | 2.
  Proof. by rewrite /InstrFrontPost. Qed.

  Lemma instr_front_post_elim I P Q fl : InstrFrontPost I P Q fl → P -∗ Q.
  Proof. rewrite /InstrFrontPost => HPQ. iIntros "HP". by iApply HPQ. Qed.
End instr_front.

(* The intro pattern [p] of a postcondition, with the hidden name [h]
   inserted at the front of the branches marked in [fl]. *)
Definition instr_front_pat (h : ident.ident) (fl : list bool)
    (p : intro_patterns.intro_pat) : option intro_patterns.intro_pat :=
  match fl, p with
  | [true], _ => Some (intro_patterns.IList [ [intro_patterns.IIdent h; p] ])
  | [false], _ => Some p
  | _, intro_patterns.IList alts =>
      if decide (length alts = length fl) then
        Some (intro_patterns.IList (zip_with (λ (b : bool) alt,
          if b then [intro_patterns.IList [intro_patterns.IIdent h :: alt] ] else alt)
          fl alts))
      else None
  | _, _ => None
  end.

(* The specialization pattern [sps], with the hypothesis [h] framed in its
   first goal. *)
Definition instr_frame_spat (h : ident.ident) (sps : list spec_pat)
    : option (list spec_pat) :=
  match sps with
  | SGoal g :: sps =>
      Some (SGoal (SpecGoal (spec_goal_kind g) (spec_goal_negate g)
                            (h :: spec_goal_frame g) (spec_goal_hyps g)
                            (spec_goal_done g)) :: sps)
  | _ => None
  end.

(* The instruction points-to of the started instruction. *)
Ltac instr_started_hyp :=
  lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ =>
    lazymatch Γs with
    | context [ Esnoc _ ?hi (_ ↦ₐ{_} encodeInstrW _ @@? _)%I ] => hi
    | _ => fail "iInstrApply: no started instruction (use iInstrStart)"
    end
  end.

(* Puts the instruction back: into its code fragment, through the
   continuation left by the lookup, or dropped on persistent code. *)
Ltac instr_apply_close :=
  lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ =>
    lazymatch Γs with
    | context [ Esnoc _ ?hi (_ ↦ₐ{_} encodeInstrW _ @@? _)%I ] =>
      lazymatch Γs with
      | context [ Esnoc _ ?hcont ((_ ↦ₐ{_} encodeInstrW _ @@? _) -∗ _)%I ] =>
        let pat := constr:(cons (SIdent hi nil) nil) in
        iSpecialize (hcont with pat)
      | _ => iClear hi
      end
    end
  end.

(* Looks up the next instruction of [hprog] and binds it. The continuation
   back to the code fragment takes the name [hprog]. *)
Ltac instr_apply_start hprog :=
  instr_normalize_lwords;
  let hi := iFresh in
  iInstr_lookup hprog as hi hprog;
  try wp_instr.

(* In a branch of the postcondition: the pure step, then the instruction
   back, if the branch gives it back. *)
Ltac instr_apply_branch hlc hlc' :=
  simpl_cnull_zero;
  try wp_pure_lc hlc';
  try (iCombine_ident (INamed hlc) hlc' as (INamed hlc));
  try instr_apply_close.

(* The main goal: the postcondition, with the instruction moved to the
   front of the branches that give it back, is introduced with [ipat] and a
   hidden name for the instruction. *)
Ltac instr_apply_main hlc hlc' I intro_xs ipat :=
  iNext; intro_xs ();
  let Hp := iFresh in
  iIntros Hp;
  let P := lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ =>
    lazymatch Γs with context [ Esnoc _ Hp ?P ] => P end end in
  (* Solved here, and the lemma below given explicitly: a global resolution
     would also try the instances left pending by [iApply]. *)
  let c := constr:(ltac:(tc_solve) : InstrFrontPost I P _ _) in
  lazymatch type of c with InstrFrontPost _ _ ?Q ?fl =>
    let h := iFresh in
    let p := intro_patterns.intro_pat.parse_one ipat in
    lazymatch eval vm_compute in (instr_front_pat h fl p) with
    | Some ?p' =>
      iDestruct (instr_front_post_elim I P Q fl c with Hp) as p';
      instr_apply_branch hlc hlc'
    | None => fail "iInstrApply: the pattern" ipat
                "does not match the branches of the postcondition"
    end
  end.

Ltac instr_apply_core hlc rule spat intro_xs ipat :=
  let hi := instr_started_hyp in
  let I := lazymatch goal with |- envs_entails (Envs _ ?Γs _) _ =>
    lazymatch Γs with context [ Esnoc _ hi ?I ] => I end end in
  let sps := spec_pat.parse spat in
  let sps := lazymatch eval vm_compute in (instr_frame_spat hi sps) with
    | Some ?sps => sps
    | None => fail "iInstrApply: the pattern" spat "has no goal for the precondition"
    end in
  let hlc' :=
    match goal with
    | |- context [ Esnoc _ (INamed hlc) (£ _)%I ] => iFresh
    | _ => hlc
    end in
  iApply (rule with sps);
  [ try solve_pure .. | instr_apply_main hlc hlc' I intro_xs ipat ].

Tactic Notation "iInstrStart" constr(hprog) := instr_apply_start hprog.

Tactic Notation "iInstrEnd" :=
  iModIntro; try wp_pure; try instr_apply_close.

(* Continuing a started instruction. *)
Tactic Notation "iInstrApply" open_constr(rule) "with" constr(spat) "as" constr(ipat) :=
  instr_apply_core "_" rule spat ltac:(fun _ => idtac) ipat.
Tactic Notation "iInstrApply" open_constr(rule) "with" constr(spat)
    "as" "(" simple_intropattern(x1) ")" constr(ipat) :=
  instr_apply_core "_" rule spat ltac:(fun _ => iIntros (x1)) ipat.
Tactic Notation "iInstrApply" open_constr(rule) "with" constr(spat)
    "as" "(" simple_intropattern(x1) simple_intropattern(x2) ")" constr(ipat) :=
  instr_apply_core "_" rule spat ltac:(fun _ => iIntros (x1 x2)) ipat.
Tactic Notation "iInstrApply" open_constr(rule) "with" constr(spat)
    "as" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) ")" constr(ipat) :=
  instr_apply_core "_" rule spat ltac:(fun _ => iIntros (x1 x2 x3)) ipat.

(* Looking up the instruction and applying the rule. *)
Tactic Notation "iInstrApply" open_constr(hprog) open_constr(rule) "with" constr(spat)
    "as" constr(ipat) :=
  instr_apply_start hprog;
  instr_apply_core "_" rule spat ltac:(fun _ => idtac) ipat.
Tactic Notation "iInstrApply" open_constr(hprog) open_constr(rule) "with" constr(spat)
    "as" "(" simple_intropattern(x1) ")" constr(ipat) :=
  instr_apply_start hprog;
  instr_apply_core "_" rule spat ltac:(fun _ => iIntros (x1)) ipat.
Tactic Notation "iInstrApply" open_constr(hprog) open_constr(rule) "with" constr(spat)
    "as" "(" simple_intropattern(x1) simple_intropattern(x2) ")" constr(ipat) :=
  instr_apply_start hprog;
  instr_apply_core "_" rule spat ltac:(fun _ => iIntros (x1 x2)) ipat.
Tactic Notation "iInstrApply" open_constr(hprog) open_constr(rule) "with" constr(spat)
    "as" "(" simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) ")" constr(ipat) :=
  instr_apply_start hprog;
  instr_apply_core "_" rule spat ltac:(fun _ => iIntros (x1 x2 x3)) ipat.

(* With the later credit of the pure step. *)
Tactic Notation "iInstrApply" open_constr(hprog) "with" constr(hlc) open_constr(rule)
    "with" constr(spat) "as" constr(ipat) :=
  instr_apply_start hprog;
  instr_apply_core hlc rule spat ltac:(fun _ => idtac) ipat.
Tactic Notation "iInstrApply" open_constr(hprog) "with" constr(hlc) open_constr(rule)
    "with" constr(spat) "as" "(" simple_intropattern(x1) ")" constr(ipat) :=
  instr_apply_start hprog;
  instr_apply_core hlc rule spat ltac:(fun _ => iIntros (x1)) ipat.
Tactic Notation "iInstrApply" open_constr(hprog) "with" constr(hlc) open_constr(rule)
    "with" constr(spat) "as" "(" simple_intropattern(x1) simple_intropattern(x2) ")"
    constr(ipat) :=
  instr_apply_start hprog;
  instr_apply_core hlc rule spat ltac:(fun _ => iIntros (x1 x2)) ipat.

Ltac2 rec iGo hprog :=
  let stop_if_at_least_two_goals () :=
    on_lasts [ (fun _ => ()); (fun _ => ()) ] in
  match Control.case (fun _ => ltac1:(hprog |- iInstr hprog) (Ltac1.of_constr hprog)) with
  | Err (_) => ()
  | Val (_) => Control.plus stop_if_at_least_two_goals (fun _ => iGo hprog)
  end.

Ltac iGo hprog :=
  let f := ltac2:(hprog |- iGo (Option.get (Ltac1.to_constr hprog))) in
  f hprog.
