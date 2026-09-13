From Stdlib Require Import Eqdep_dec List.
From griotte Require Import rules.
From griotte Require Export iris_extra memory_region.
From griotte Require Import classes tactics_helpers proofmode_instr_rules.
From griotte Require Export class_instances solve_pure solve_addr_extra.
From iris.proofmode Require Import proofmode spec_patterns coq_tactics ltac_tactics reduction.
From griotte Require Export NamedProp.
From machine_utils Require Export tactics.
From iris.bi Require Import bi.
Import bi.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Option Bool Constr.
Set Default Proof Mode "Classic".

Section codefrag.
  Context {Σ:gFunctors} {ceriseg: ceriseG Σ}
    `{MP: MachineParameters}.

  Lemma codefrag_lookup_acc a0 (cs: list Word) (i: nat) w:
    SimplTC (cs !! i) (Some w) →
    codefrag a0 cs -∗
      (a0 ^+ i)%a ↦ₐ w ∗ ((a0 ^+ i)%a ↦ₐ w -∗ codefrag a0 cs).
  Proof.
    iIntros (Hi) "Hcs".
    iDestruct (codefrag_contiguous_region with "Hcs") as %Hub.
    rewrite /codefrag.
    destruct Hub as [? Hub].
    iDestruct (big_sepL2_lookup_acc with "Hcs") as "[Hw Hcont]"; only 2: by eauto.
    2: iFrame.
    eapply finz_seq_between_lookup with (n:=length cs).
    { apply lookup_lt_is_Some_1; eauto. }
    { solve_addr. }
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

(* Ltac specifically meant for switching to the next block. Use `changePCto` to perform more arbitrary moves *)
Ltac changePC_next_block new_a :=
  match goal with |- context [ Esnoc _ _ (PC ↦ᵣ WCap _ _ _ _ _ ?prev_a)%I ] =>
                    rewrite (_: prev_a = new_a) ; [ | solve_block_move  ] end.
(* More powerful ltac to change the address of the pc. Might take longer to solve than the more specific alternative above.*)
Ltac changePCto0 new_a :=
  match goal with |- context [ Esnoc _ _ (PC ↦ᵣ WCap _ _ _ _ _ ?a)%I ] =>
    rewrite (_: a = new_a); [| solve_addr]
  end.
Tactic Notation "changePCto" constr(a) := changePCto0 a.

Ltac codefrag_facts h :=
  let h := constr:(h:ident) in
  match goal with |- context [ Esnoc _ h (codefrag ?a_base ?code) ] =>
    (match goal with H : ContiguousRegion a_base _ |- _ => idtac end ||
     let HH := fresh in
     iDestruct (codefrag_contiguous_region with h) as %HH;
     cbn [length map encodeInstrsW] in HH
    );
    (match goal with H : SubBounds _ _ a_base (a_base ^+ _)%a |- _ => idtac end ||
     (try match goal with H : SubBounds ?b ?e _ _ |- _ =>
            let HH := fresh in
            assert (HH: SubBounds b e a_base (a_base ^+ length code)%a) by solve_addr;
            cbn [length map encodeInstrsW] in HH
          end))
  end.

Ltac clear_codefrag_facts h :=
  let h := constr:(h:ident) in
  match goal with |- context [ Esnoc _ h (codefrag ?a_base ?code) ] =>
    try match goal with H : ContiguousRegion a_base _ |- _ => clear H end;
    try match goal with H : SubBounds _ _ a_base (a_base ^+ _)%a |- _ => clear H end
  end.

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
    rewrite /codefrag. iIntros "H".
    iDestruct (codefrag_contiguous_region with "H") as %Hregion.
    destruct Hregion as [an Han]. rewrite length_app in Han |- *.
    iDestruct (region_pointsto_split _ _ (a0 ^+ length l1)%a with "H") as "[H1 H2]".
    { by solve_addr. }
    { by rewrite /finz.dist; solve_addr. }
    iFrame. iIntros "H1".
    rewrite region_pointsto_split; first iFrame.
    + solve_addr.
    + rewrite /finz.dist; solve_addr.
  Qed.

  Lemma codefrag_block_acc (n: nat) a0 (cs: list Word) l1 l l2:
    NthSubBlock cs n l1 l l2 →
    codefrag a0 cs -∗
    ∃ (ai: Addr), ⌜(a0 + length l1)%a = Some ai⌝ ∗
    codefrag ai l ∗
    (codefrag ai l -∗ codefrag a0 cs).
  Proof.
    unfold NthSubBlock. intros ->. rewrite /codefrag. iIntros "H".
    iDestruct (codefrag_contiguous_region with "H") as %[a1 Ha1].
    rewrite !length_app in Ha1 |- *.
    iDestruct (region_pointsto_split _ _ (a0 ^+ length l1)%a with "H") as "[H1 H2]".
    { solve_addr. }
    { rewrite /finz.dist; solve_addr. }
    iExists (a0 ^+ length l1)%a. iSplitR; first (iPureIntro; solve_addr).
    iDestruct (region_pointsto_split _ _ ((a0 ^+ length l1) ^+ length l)%a with "H2") as "[H2 H3]".
    { solve_addr. }
    { rewrite /finz.dist; solve_addr. }
    iFrame.
    iIntros "H2".
    rewrite region_pointsto_split; [iFrame|..]; cycle 1.
    { solve_addr. }
    { rewrite /finz.dist; solve_addr. }
    rewrite region_pointsto_split; first iFrame.
    { solve_addr. }
    { rewrite /finz.dist; solve_addr. }
  Qed.

End codefrag_subblock.

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
  iDestruct (codefrag_contiguous_region with hi) as %HCR;
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

Tactic Notation "focus_block_0" constr(h) "as" constr(hi) constr(hcont) :=
  focus_block_0 h hi hcont.

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
  iDestruct (codefrag_contiguous_region with hi) as %HCR;
  cbn [length map encodeInstrsW] in HCR;
  try lazymatch goal with HSB : SubBounds ?b ?e a0 (a0 ^+ _)%a |- _ =>
    let HSB' := fresh in
    unshelve epose proof (focus_block_SubBounds _ _ _ _ _ _ _ HSB HCR Ha_base _ _ _) as HSB';
    [solve_pure ..|];
    cbn [length map encodeInstrsW] in HSB'
  end.

Ltac focus_block n h a_base Ha_base hi hcont :=
  let h := constr:(h:ident) in
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
  end.

Tactic Notation "focus_block" constr(n) constr(h) "as"
       ident(a_base) simple_intropattern(Ha_base) constr(hi) constr(hcont) :=
  focus_block n h a_base Ha_base hi hcont.

Ltac focus_block_nochangePC n h a_base Ha_base hi hcont :=
  let h := constr:(h:ident) in
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
  end.
Tactic Notation "focus_block_nochangePC" constr(n) constr(h) "as"
  ident(a_base) simple_intropattern(Ha_base) constr(hi) constr(hcont) :=
  focus_block_nochangePC n h a_base Ha_base hi hcont.


Ltac unfocus_block hi hcont h :=
  let hi := constr:(hi:ident) in
  let hcont := constr:(hcont:ident) in
  let h := constr:(h:ident) in
  clear_codefrag_facts hi;
  iDestruct (hcont with hi) as h.

Tactic Notation "unfocus_block" constr(hi) constr(hcont) "as" constr(h) :=
  unfocus_block hi hcont h.

(* "iApply with on-demand framing" *)

(* TODO: These proofs should probably not use the proof mode tactics *)
Lemma envs_clear_spatial_sound_rev {PROP: bi} (Δ: envs PROP) :
  envs_wf Δ →
  of_envs (envs_clear_spatial Δ) ∗ [∗] env_spatial Δ ⊢ of_envs Δ.
Proof.
  intros.
  rewrite !of_envs_eq /envs_clear_spatial /=.
  rewrite -persistent_and_sep_assoc.
  iIntros "H". iDestruct "H" as "[% [[? _] ?]]". iFrame. iSplit; eauto.
Qed.

Lemma tac_specialize_assert_delay {PROP: bi} (Δ: envs PROP) j q R P1 P2 P1' F Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q false R P1 P2 → AddModal P1' P1 Q →
  envs_entails (envs_delete true j q Δ) (P1' ∗ F) →
  match
    envs_app false (Esnoc Enil j P2)
      (envs_clear_spatial (envs_delete true j q Δ))
  with
  | Some Δ1 =>
    envs_entails Δ1 (F -∗ Q)
  | None => False
  end → envs_entails Δ Q.
Proof.
  rewrite envs_entails_unseal. intros ??? HH.
  destruct (envs_app _ _ _) eqn:?; last done.
  intros HQ.
  rewrite envs_lookup_sound //.
  set Δ' := envs_delete true j q Δ in HH Heqo |- *.
  iIntros "[HR HΔ']".
  iAssert (⌜envs_wf Δ'⌝)%I as %?.
  { rewrite of_envs_eq. iDestruct "HΔ'" as "[? ?]". eauto. }
  rewrite envs_clear_spatial_sound.
  set Δ'i := envs_clear_spatial Δ'.
  set Δ's := env_spatial Δ'.
  iDestruct "HΔ'" as "[#HΔ'i Hs]".
  iDestruct (envs_clear_spatial_sound_rev with "[$HΔ'i $Hs]") as "HΔ'"; auto.
  iDestruct (HH with "HΔ'") as "[HP1' HF]".
  iApply add_modal; first eauto.
  iFrame. iIntros "HP1".
  iApply (HQ with "[HR HP1] HF").
  { iApply (envs_app_singleton_sound with "[] [HR HP1]"); first eauto.
    + iApply "HΔ'i".
    + iApply (into_wand with "[HR]"); eauto.
  }
Qed.

(* Typeclass instances to look-up framable resources in the goal, for
   [FramableMachineResource] from [machine_utils/tactics.v]
*)

Class FramableSRegisterPointsto (sr: SRegName) (w: Word) := {}.
#[export] Hint Mode FramableSRegisterPointsto + - : typeclass_instances.
Class FramableRegisterPointsto (r: RegName) (w: Word) := {}.
#[export] Hint Mode FramableRegisterPointsto + - : typeclass_instances.
Class FramableMemoryPointsto (a: Addr) (dq: dfrac) (w: Word) := {}.
#[export] Hint Mode FramableMemoryPointsto + - - : typeclass_instances.
Class FramableCodefrag (a: Addr) (l: list Word) := {}.
#[export] Hint Mode FramableCodefrag + - : typeclass_instances.

Instance FramableSRegisterPointsto_default sr w :
  FramableSRegisterPointsto sr w
| 100. Qed.

Instance FramableRegisterPointsto_default r w :
  FramableRegisterPointsto r w
| 100. Qed.

Instance FramableMemoryPointsto_default a dq w :
  FramableMemoryPointsto a dq w
| 100. Qed.

Instance FramableCodefrag_default a l :
  FramableCodefrag a l
| 100. Qed.

Instance FramableMachineResource_sreg `{ceriseG Σ} sr w :
  FramableSRegisterPointsto sr w →
  FramableMachineResource (sr ↦ₛᵣ w).
Qed.

Instance FramableMachineResource_reg `{ceriseG Σ} r w :
  FramableRegisterPointsto r w →
  FramableMachineResource (r ↦ᵣ w).
Qed.

Instance FramableMachineResource_mem `{ceriseG Σ} a dq w :
  FramableMemoryPointsto a dq w →
  FramableMachineResource (a ↦ₐ{dq} w).
Qed.

Instance FramableMachineResource_codefrag `{ceriseG Σ} a l :
  FramableCodefrag a l →
  FramableMachineResource (codefrag a l).
Qed.


(* remembering names after auto-framing done by iFrameAuto *)

Ltac2 Type hyp_table_kind := [ Reg | SReg | Mem | Codefrag ].

Ltac2 record_framed
      (table: (constr * constr * hyp_table_kind) list ref)
      (framed: constr * constr)
  :=
  let (hname, hh) := framed in
  let (lhs, kind) :=
    lazy_match! hh with
    | (?r ↦ᵣ _)%I => (r, Reg)
    | (?sr ↦ₛᵣ _)%I => (sr, SReg)
    | (?a ↦ₐ{_} _)%I => (a, Mem)
    | (codefrag ?a _) => (a, Codefrag)
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

Ltac2 iSpecializeDelay (h: constr) :=
  refine '(tac_specialize_assert_delay _ $h _ _ _ _ _ _ _ _ _ _ _ _);
  Control.shelve_unifiable ();
  Control.dispatch [
    (fun _ => ltac1:(pm_reflexivity));
    (fun _ => ltac1:(solve_to_wand tt));
    (fun _ => ltac1:(class_apply @add_modal_id));
    (fun _ => ltac1:(pm_reduce));
    (fun _ => ltac1:(pm_reduce))
  ].

Ltac iApplyHypLast H :=
  eapply tac_apply with H _ _ _;
  [pm_reflexivity
  |tc_solve
  |pm_reduce; pm_prettify].

Ltac2 iApplyCapAutoT_init0 lemma :=
  let tbl := { contents := [] } in
  let x := iFresh () in
  ltac1:(x lem |- once (iPoseProofCore lem as false (fun H => iRename H into x)))
    (Ltac1.of_constr x) (Ltac1.of_constr lemma);
  on_lasts [(fun _ =>
    iSpecializeDelay x > [|
      ltac1:(h |-
        let f := iFresh in
        iIntros f;
        iApplyHypLast h;
        iRevert f) (Ltac1.of_constr x)
    ]
  )];
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
       borrow borrow_sb deeplocal deeplocal_sb deeplocal_perm
       readonly readonly_sb readonly_perm
       clear_tag clear_tag_sealable get_tag get_tag_sealable].

(* Rewrite known word shapes and use available tag/permission facts before
   reducing definitions. Symbolic variables are supported; unresolved evars
   use reduction only, since rewriting could instantiate an operand to match
   a lemma. Neither path splits unknown tag or permission conditions. *)
Ltac simplify_cap_word_known :=
  repeat progress (
    rewrite ?get_tag_clear_tag ?get_tag_clear_tag_sealable
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
  cbn [rules_Get.denote rules_BinOp.denote updatePcPerm];
  ltac1:(simplify_cap_word).

(* iApplyCapAutoCore *)

Ltac iNamedAccu_fail_explain :=
  lazymatch goal with
  | |- envs_entails _ (?remaining ∗ _) =>
    fail "iApplyCapAuto: the following resources could not be found in the context:"
         remaining
  end.

Ltac2 iApplyCapAutoCore lemma :=
  let tbl := iApplyCapAutoT_init0 lemma in
  let iFrameCap := fun () => record_framed tbl (iFrameAuto ()) in
  grepeat (fun _ =>
    Control.extend [] (fun _ => try (Control.once solve_pure_iinstr))
      [ (fun _ => try (iFrameCap ())); (fun _ => ()) ]);
  on_lasts [ (fun _ => ltac1:(iNamedAccu || iNamedAccu_fail_explain)); (fun _ => ()) ];
  on_lasts [ (fun _ =>
    iNamedIntro ();
    try ltac1:(iNext);
    reintro_cap_resources tbl;
    iApplyCapAuto_cleanup ()
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

Ltac instr_lookup0 hprog hi hcont :=
  let hprog := constr:(hprog:ident) in
  lazymatch goal with |- context [ Esnoc _ hprog (codefrag ?a_base _) ] =>
  lazymatch goal with |- context [ Esnoc _ ?hpc (PC ↦ᵣ (WCap _ _ _ _ _ ?pc_a))%I ] =>
    let base_off := eval unfold as_weak_addr_incr in (@as_weak_addr_incr pc_a a_base _ _) in
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
  end end.

Tactic Notation "iInstr_lookup" constr(hprog) "as" constr(hi) constr(hcont) :=
  instr_lookup0 hprog hi hcont.

Ltac instr_get_rule_using dispatch hi cont :=
  let hi := constr:(hi:ident) in
  once (
    (lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ encodeInstrW ?instr)%I ] => idtac end
     + (lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ ?instr)%I ] =>
           fail 1 "Next instruction is not of the form (encodeInstrW _):" instr
         end + fail "" hi "not found"))
  );
  lazymatch goal with |- context [ Esnoc _ hi (_ ↦ₐ encodeInstrW ?instr)%I ] =>
    dispatch instr cont
  end.

Ltac instr_get_rule0 hi cont :=
  instr_get_rule_using dispatch_instr_rule hi cont.

Tactic Notation "iInstr_get_rule" constr(hi) tactic(cont) := instr_get_rule0 hi cont.

Ltac instr_close hprog :=
  (* because of iApplyCapAuto's context shuffling, [hi] and [hcont]
     are not valid anymore... recover them. *)
  (* XXX make this a bit more robust *)
  lazymatch goal with |- context [ Esnoc _ ?hi (_ ↦ₐ encodeInstrW _)%I ] =>
  lazymatch goal with |- context [ Esnoc _ ?hcont (_ ↦ₐ encodeInstrW _ -∗ _)%I ] =>
    notypeclasses refine (tac_specialize false _ hi _ hcont _ _ _ _ _ _ _ _ _);
    [pm_reflexivity
    |pm_reflexivity
    |tc_solve
    |pm_reduce];
    iRename hcont into hprog
  end end.

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


(* TODO: find a way of displaying an error message if iApplyCapAuto fails,
   displaying the rule it was called on, and without silencing iApplyCapAuto's
   own error messages? *)
Ltac instr_using dispatch hprog hlc:=
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
                             iApplyCapAuto rule;
                             [ .. | instr_close hprog
                                    ; repeat (replace ( WInt (if decide (_ = cnull) then 0 else 0) ) with (WInt 0) by (destruct (decide _); done))
                                    ; try wp_pure_lc hlc'
                                    ; try (iCombine_ident (INamed hlc) hlc' as (INamed hlc))
                          ])
.
(* The success interface preserves the ordinary instruction-rule dispatch,
   including instructions whose specified behavior is Halt or Fail. *)
Ltac instr_lc hprog hlc := instr_using dispatch_instr_rule hprog hlc.
Tactic Notation "iInstr_success" constr(H) := instr_lc H "_".
Tactic Notation "iInstr_success" constr(H) "with" constr(Hlc) := instr_lc H Hlc.
Tactic Notation "iInstr" constr(H) := iInstr_success H.
Tactic Notation "iInstr" constr(H) "with" constr(Hlc) := iInstr_success H with Hlc.
Tactic Notation "iInstr_fail" constr(H) :=
  instr_using dispatch_instr_failure H "_";
  try solve [solve_instr_failure | by simplify_map_eq].
Tactic Notation "iInstr_fail" constr(H) "with" constr(Hlc) :=
  instr_using dispatch_instr_failure H Hlc;
  try solve [solve_instr_failure | by simplify_map_eq].

Tactic Notation "iInstr_invalidate" constr(H) :=
  instr_using dispatch_instr_invalidation H "_"; try solve_instr_map.
Tactic Notation "iInstr_invalidate" constr(H) "with" constr(Hlc) :=
  instr_using dispatch_instr_invalidation H Hlc; try solve_instr_map.

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
