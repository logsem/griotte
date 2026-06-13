From stdpp Require Import ssreflect.
From griotte Require Export machine_utils_extra.
From griotte Require Import addresses otypes permissions.

(* Having different syntactic categories here simplifies the definition of instructions later, but requires some duplication in defining bounds changes and lea on sealing ranges *)
Inductive Sealable: Type :=
| SCap (p : Perm) (g : Locality) (b e a : Addr)
| SSealRange (p : SealPerms) (g : Locality) (b e a : OType).

Inductive Word: Type :=
| WInt (z : Z)
| WSealable (sb : Sealable)
| WSentry (p : Perm) (g : Locality) (b e a : Addr)
| WSealed (ot : OType) (sb : Sealable)
.

Notation WCap p g b e a := (WSealable (SCap p g b e a)).
Notation WSealRange p g b e a := (WSealable (SSealRange p g b e a)).


(* EqDecision instances *)

Global Instance sealb_eq_dec : EqDecision Sealable.
Proof. solve_decision. Qed.
Global Instance word_eq_dec : EqDecision Word.
Proof. solve_decision. Qed.

Ltac destruct_word w :=
  let z := fresh "z" in
  let c := fresh "c" in
  let sr := fresh "sr" in
  let sd := fresh "sd" in
  let e := fresh "e" in
  destruct w as [ z | [c | sr] | sd | e].

(***** Identifying parts of String.String.words *****)

Definition get_b (w : Word) :=
  match w with
  | WCap _ _ b _ _ => Some b
  | _ => None
  end.

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


(* Z <-> Word *)
Definition is_z (w : Word) : bool :=
  match w with
  | WInt z => true
  |  _ => false
  end.

(* Sealable <-> Word *)
Definition is_sealb (w : Word) : bool :=
  match w with
  | WSealable sb => true
  |  _ => false
  end.

(* Capability <-> Word *)
Definition is_cap (w : Word) : bool :=
  match w with
  | WCap p g b e a => true
  |  _ => false
  end.

(* SealRange <-> Word *)
Definition is_sealr (w : Word) : bool :=
  match w with
  | WSealRange p g b e a => true
  |  _ => false
  end.

(* Sealed <-> Word *)
Definition is_sealed (w : Word) : bool :=
  match w with
  | WSealed a sb => true
  |  _ => false
  end.

(* Sealed <-> Word *)
Definition is_sentry (w : Word) : bool :=
  match w with
  | WSentry _ _ _ _ _ => true
  |  _ => false
  end.

Definition is_sealed_with_o (w : Word) (o : OType) : bool :=
  match w with
  | WSealed o' sb => (o =? o')%ot
  | _ => false end.

Definition seal_capability ( w : Word ) (ot : OType) :=
  match w with
  | WCap p g b e a => WSealed ot (SCap p g b e a)
  | _ => w
  end.

(* non-E capability or range of seals *)
Definition is_mutable_range (w : Word) : bool:=
  match w with
  | WCap p _ _ _ _ => true
  | WSealRange _ _ _ _ _ => true
  | _ => false end.

Definition isLocalSealable (sb : Sealable): bool :=
  match sb with
  | SCap _ l _ _ _ | SSealRange _ l _ _ _ => isLocal l
  end.

Definition isLocalWord (w : Word): bool :=
  match w with
  | WInt _ => false
  | WSentry _ l _ _ _ => isLocal l
  | WSealed _ sb
  | WSealable sb => isLocalSealable sb
  end.

Definition isGlobal (l: Locality): bool :=
  match l with
  | Global => true
  | _ => false
  end.

Definition isGlobalSealable (sb : Sealable): bool :=
  match sb with
  | SCap _ l _ _ _ | SSealRange _ l _ _ _ => isGlobal l
  end.

Definition isGlobalWord (w : Word): bool :=
  match w with
  | WInt _ => false
  | WSentry _ l _ _ _ => isGlobal l
  | WSealed _ sb
  | WSealable sb => isGlobalSealable sb
  end.


Definition canStore (p: Perm) (w: Word): bool :=
  if (isLocalWord w)
  then isWL p
  else writeAllowed p.

Definition readAllowedWord (w : Word) : Prop :=
  match w with
  | WCap p _ _ _ _ => readAllowed p = true
  | _ => False
  end.

Definition writeAllowedWord (w : Word) : Prop :=
  match w with
  | WCap p _ _ _ _ => writeAllowed p = true
  | _ => False
  end.

Definition hasValidAddress (w : Word) (a : Addr) : Prop :=
  match w with
  | WCap _ _ b e a' => (b ≤ a' ∧ a' < e)%Z ∧ a = a'
  | _ => False
  end.


(* Helper definitions for capabilities *)

(* Turn E into RX, and ESR into XSR after a jump *)
Definition updatePcPerm (w: Word): Word :=
  match w with
  | WSentry p g b e a => WCap p g b e a
  | _ => w
  end.

Definition nonZero (w: Word): bool :=
  match w with
  | WInt n => negb (Z.eqb n 0)
  | _ => true
  end.

Definition cap_size (w : Word) : Z :=
  match w with
  | WCap _ _ b e _ => (e - b)%Z
  | _ => 0%Z
  end.

Definition deeplocal_perm (p : Perm) :=
  match p with
  | BPerm rx w _ dro => BPerm rx w DL dro
  end.

Definition deeplocal_sb (sb : Sealable) :=
  match sb with
  | SCap p g b e a => SCap (deeplocal_perm p) g b e a
  | SSealRange sp g b e a => SSealRange sp g b e a
  end.

Definition deeplocal (w : Word) :=
  match w with
  | WSealable sb => WSealable (deeplocal_sb sb)
  | _ => w
  end.

Definition borrow_sb (sb : Sealable) :=
  match sb with
  | SSealRange sp _ b e a => SSealRange sp Local b e a
  | SCap p _ b e a => SCap p Local b e a
  end.

Definition borrow (w : Word) :=
  match w with
  | WSealable sb => WSealable (borrow_sb sb)
  | WSentry p _ b e a => WSentry p Local b e a
  | WSealed ot sb => WSealed ot (borrow_sb sb)
  | _ => w
  end.

Definition readonly_perm (p : Perm) :=
  match p with
  | BPerm rx _ dl _ => BPerm rx Ow dl DRO
  end.

Definition readonly_sb (sb : Sealable) :=
  match sb with
  | SCap p g b e a => SCap (readonly_perm p) g b e a
  | _ => sb
  end.

Definition readonly (w : Word) :=
  match w with
  | WSealable sb => WSealable (readonly_sb sb)
  | _ => w
  end.

Definition load_word (p : Perm) (w : Word) :=
  let borrow_w := (if isDL p then deeplocal (borrow w) else w) in
  let borrow_dro_w := (if isDRO p then readonly borrow_w else borrow_w) in
  borrow_dro_w.

Definition load_word_perm (pload p : Perm) :=
  match p with
  | BPerm rx pw dl dro => (BPerm rx
                            (if isDRO pload then Ow else pw)
                            (if isDL pload then DL else dl)
                            (if isDRO pload then DRO else dro)
                         )
  end.



Definition PermFlowsToCap (p: Perm) (w: Word) : bool :=
  match w with
  | WCap p' _  _ _ _ => PermFlowsTo p p'
  | _ => false
  end.

Lemma DL_flowsto (rx : RXperm) (w : Wperm) dl dro :
  PermFlowsTo (BPerm rx w DL dro) (BPerm rx w dl dro).
Proof. destruct rx,w,dl,dro; cbn in *; done. Qed.

Lemma DRO_flowsto (rx : RXperm) (w : Wperm) dl dro :
  PermFlowsTo (BPerm rx Ow dl DRO) (BPerm rx w dl dro).
Proof. destruct rx,w,dl,dro; cbn in *; done. Qed.


(* Lemmas about canStore *)

Lemma canStore_flowsto (p p' : Perm) (w : Word) :
  PermFlowsTo p p'
  -> canStore p w = true
  -> canStore p' w = true.
Proof.
  intros Hfl HcanStore.
  rewrite /canStore in HcanStore |- *.
  destruct (isLocalWord w).
  + by eapply isWL_flowsto.
  + by eapply writeAllowed_flowsto.
Qed.

Lemma notcanStore_flowsfrom (p p' : Perm) (w : Word) :
  PermFlowsTo p p'
  -> canStore p' w = false
  -> canStore p w = false.
Proof.
  intros Hfl HcanStore.
  rewrite /canStore in HcanStore |- *.
  destruct (isLocalWord w).
  + by eapply notisWL_flowsfrom.
  + by eapply notwriteAllowed_flowsfrom.
Qed.

Lemma canStore_writeAllowed (p : Perm) (w : Word) :
  canStore p w = true -> writeAllowed p = true.
Proof.
  intros HcanStore.
  rewrite /canStore in HcanStore.
  destruct p as [? w0 ? ?]; cbn in *.
  destruct w0; cbn in *; try done.
  by rewrite Tauto.if_same in HcanStore.
Qed.

Lemma writeAllowed_canStore_int (p : Perm) (z : Z) :
  writeAllowed p = true ->
  canStore p (WInt z) = true.
Proof.
  intros Hwa.
  destruct p; first done.
Qed.

Lemma canStore_local_isWL (p : Perm) (w : Word) :
  isLocalWord w = true
  -> canStore p w = true
  -> isWL p = true.
Proof.
  intros Hw HcanStore.
  destruct p.
  by rewrite /canStore Hw in HcanStore.
Qed.

Lemma canStore_global_nonisWL (p : Perm) (w : Word) :
  isWL p = false
  → canStore p w = true
  → isLocalWord w = false.
Proof.
  intros Hpwl HcanStore.
  destruct p.
  - rewrite /canStore in HcanStore.
    destruct (isLocalWord w); congruence.
Qed.

Lemma canStoreRWL (w : Word) : canStore RWL w = true.
Proof.
  rewrite /canStore.
  destruct (isLocalWord w); done.
Qed.

(* Lemmas about load_word *)
Lemma load_word_cap
  (pload p : Perm) (g : Locality) (b e a : Addr) :
  load_word pload (WCap p g b e a ) =
  (WCap (load_word_perm pload p) (if isDL pload then Local else g) b e a).
Proof.
  rewrite /load_word /load_word_perm.
  destruct (isDRO pload) eqn:Hdro,(isDL pload) eqn:Hdl; cbn.
  all: rewrite /readonly_perm /deeplocal_perm.
  all: destruct p; cbn; try done.
Qed.

Lemma load_word_sentry
  (p' : Perm) (p : Perm)
  (g : Locality) (b e a : Addr) :
  load_word p' (WSentry p g b e a ) = (WSentry p (if isDL p' then Local else g) b e a ).
Proof.
  rewrite /load_word.
  by destruct (isDRO p'),(isDL p'); cbn.
Qed.

Lemma load_word_int (p : Perm) (z : Z) :
  load_word p (WInt z) = WInt z.
Proof.
  rewrite /load_word.
  by destruct (isDRO p),(isDL p); cbn.
Qed.

Lemma load_word_sealrange (p : Perm) (sp : SealPerms) (g : Locality) (b e a : OType) :
  load_word p (WSealRange sp g b e a) = (WSealRange sp (if isDL p then Local else g) b e a).
Proof.
  rewrite /load_word.
  by destruct (isDRO p),(isDL p); cbn.
Qed.

Lemma load_word_sealed (p : Perm) (ot : OType) (sb : Sealable)  :
  load_word p (WSealed ot sb) = (WSealed ot (if isDL p then borrow_sb sb else sb)).
Proof.
  rewrite /load_word /borrow_sb.
  destruct (isDRO p) eqn:Hdro,(isDL p) eqn:Hdl; cbn; auto.
Qed.

Lemma load_word_perm_flows (pload p : Perm) :
  PermFlowsTo (load_word_perm pload p) p.
Proof.
  destruct p.
  repeat (apply andb_True;split).
  + reflexivity.
  + destruct (isDRO pload) eqn:Hdro; done.
  + destruct (isDL pload) eqn:Hdl; done.
  + destruct (isDRO pload) eqn:Hdro; done.
Qed.

Lemma load_word_perm_load_flows (pload pload' p : Perm) :
  PermFlowsTo pload pload' ->
  PermFlowsTo (load_word_perm pload p) (load_word_perm pload' p).
Proof.
  intro Hfl.
  destruct p; cbn.
  repeat (apply andb_True;split).
  + reflexivity.
  + destruct (isDRO pload) eqn:Hdro; first done.
    apply notisDRO_flowsfrom in Hfl; auto.
    by rewrite Hfl.
  + destruct (isDL pload) eqn:Hdl; first done.
    apply notisDL_flowsfrom in Hfl; auto.
    by rewrite Hfl.
  + destruct (isDRO pload) eqn:Hdro; first done.
    apply notisDRO_flowsfrom in Hfl; auto.
    by rewrite Hfl.
Qed.

Lemma isO_load_word (pload p : Perm) :
  isO p = true -> isO (load_word_perm pload p) = true.
Proof.
  intros HO.
  destruct_perm p; cbn in * ; try congruence.
  all: by rewrite Tauto.if_same.
Qed.


(** Helper properties about String.words *)

Definition isPermWord (w : Word) (p : Perm): bool :=
  match w with
  | WCap p' _ _ _ _  => isPerm p p'
  | _ => false
  end.

Lemma isPermWord_cap_isPerm (w0:Word) p:
  isPermWord w0 p = true →
  ∃ p' g b e a, w0 = WCap p' g b e a ∧ isPerm p p' = true.
Proof.
  intros Hp. rewrite /isPermWord in Hp.
  destruct_word w0; try congruence.
  eexists _, _, _, _, _; split; eauto.
Qed.

(* Bound checking for both otypes and addresses *)

Definition isWithinCap (c: Word) (b e: finz MemNum) : bool :=
  match c with
  | WCap _ _ n1 n2 _ => isWithin n1 n2 b e
  | _ => false
  end.


(* isCorrectPC: valid capabilities for PC *)

Inductive isCorrectPC: Word → Prop :=
| isCorrectPC_intro:
    forall p g (b e a : Addr),
      (b <= a < e)%a →
      executeAllowed p = true ->
      isCorrectPC (WCap p g b e a).

Lemma isCorrectPC_dec:
  forall w, { isCorrectPC w } + { not (isCorrectPC w) }.
Proof.
  intro w; destruct w as [z | sb | |].
  - right. red; intros H. inversion H.
  - destruct sb as [p g b e a | ].
    -- case_eq (executeAllowed p); intros.
      + destruct (finz_le_dec b a).
        * destruct (finz_lt_dec a e).
          { left. econstructor; simpl; eauto. by auto. }
          { right. red; intro HH. inversion HH; subst. solve_addr. }
        * right. red; intros HH; inversion HH; subst. solve_addr.
      + right. red; intros HH; inversion HH; subst. congruence.
    -- right. red; intros H. inversion H.
 - right. red; intros H. inversion H.
 - right. red; intros H. inversion H.
Qed.

Lemma isCorrectPC_ra_wb pc_p pc_g pc_b pc_e pc_a :
  isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
  readAllowed pc_p && ((pc_b <=? pc_a)%a && (pc_a <? pc_e)%a).
Proof.
  intros Hcorrect. inversion Hcorrect as [ ? ? ? ? ? Hinbounds Hexec]; subst.
  - apply executeAllowed_is_readAllowed in Hexec.
    apply andb_prop_intro; split.
    + by apply Is_true_eq_left.
    + apply andb_prop_intro.
      split; apply Is_true_eq_left; [apply Z.leb_le | apply Z.ltb_lt]; solve_addr.
Qed.

Lemma not_isCorrectPC_perm p g b e a :
  executeAllowed p = false → ¬ isCorrectPC (WCap p g b e a).
Proof.
  intros Hexec.
  intros Hvpc; inversion Hvpc; congruence.
Qed.

Lemma not_isCorrectPC_bounds p g b e a :
 ¬ (b <= a < e)%a → ¬ isCorrectPC (WCap p g b e a).
Proof.
  intros Hbounds.
  intros Hvpc. inversion Hvpc.
  by exfalso.
Qed.

Lemma isCorrectPC_bounds p g b e (a0 a1 a2 : Addr) :
  isCorrectPC (WCap p g b e a0) →
  isCorrectPC (WCap p g b e a2) →
  (a0 ≤ a1 < a2)%Z → isCorrectPC (WCap p g b e a1).
Proof.
  intros Hvpc0 Hvpc2 [Hle Hlt].
  inversion Hvpc0 as [p' g' b' e' a' Ha0 Hp]; simplify_eq.
  subst; econstructor; auto.
  inversion Hvpc2 as [p'' g'' ? ? ? Ha2 Hp']; simplify_eq.
  destruct Ha0 as [Hb He]. destruct Ha2 as [Hb2 He2].
  split.
  { apply Z.le_trans with a0; auto. }
  { apply Z.lt_trans with a2; auto. }
Qed.

Lemma isCorrectPC_bounds_alt p g b e (a0 a1 a2 : Addr) :
  isCorrectPC (WCap p g b e a0)
  → isCorrectPC (WCap p g b e a2)
  → (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z
  → isCorrectPC (WCap p g b e a1).
Proof.
  intros Hvpc0 Hvpc2 [Hle0 Hle2].
  apply Z.lt_eq_cases in Hle2 as [Hlt2 | Heq2].
  - apply isCorrectPC_bounds with a0 a2; auto.
  - apply finz_to_z_eq in Heq2. rewrite Heq2. auto.
Qed.

Lemma isCorrectPC_withinBounds p g b e a :
  isCorrectPC (WCap p g b e a) →
  withinBounds b e a = true.
Proof.
  intros HH. inversion HH; subst.
  rewrite /withinBounds !andb_true_iff Z.leb_le Z.ltb_lt. auto.
Qed.

Lemma isCorrectPC_le_addr p g b e a :
  isCorrectPC (WCap p g b e a) →
  (b <= a)%a ∧ (a < e)%a.
Proof.
  intros HH. by eapply withinBounds_le_addr, isCorrectPC_withinBounds.
Qed.

Lemma isCorrectPC_nonO p p' g b e a :
  PermFlowsTo p p' → isCorrectPC (WCap p g b e a) → isO p' = false.
Proof.
  intros Hfl HcPC.
  inversion HcPC.
  by eapply executeAllowed_nonO, executeAllowed_flowsto.
Qed.

Lemma in_range_is_correctPC p g b e a b' e' :
  isCorrectPC (WCap p g b e a) →
  (b' <= b)%a ∧ (e <= e')%a →
  (b' <= a)%a ∧ (a < e')%a.
Proof.
  intros Hvpc [Hb He].
  inversion Hvpc; simplify_eq. solve_addr.
Qed.

Lemma isCorrectPC_executeAllowed_InBounds p g b e a :
  executeAllowed p = true →
  InBounds b e a →
  isCorrectPC (WCap p g b e a).
Proof.
  unfold InBounds. intros. constructor; eauto.
Qed.

Lemma isCorrectPC_ExecPCPerm_InBounds p g b e a :
  executeAllowed p = true →
  InBounds b e a →
  isCorrectPC (WCap p g b e a).
Proof.
  unfold InBounds. intros. constructor; eauto.
Qed.

Lemma seal_capability_inj (o : OType) (c1 c2 : Word) :
  is_cap c1 ->
  is_cap c2 ->
  c1 ≠ c2 ->
  seal_capability c1 o ≠ seal_capability c2 o.
Proof.
  intros Hcap1 Hcap2 Hc Hcontra.
  apply Hc.
  destruct c1 as [| [|] | |], c2 as [| [|] | |] ; cbn in *; simplify_eq.
Qed.

Lemma borrow_seal_capability_inj (o : OType) (c1 c2 : Word) :
  is_cap c1 ->
  is_cap c2 ->
  isGlobalWord c1 ->
  isGlobalWord c2 ->
  c1 ≠ c2 ->
  seal_capability c1 o ≠ borrow (seal_capability c2 o).
Proof.
  intros Hcap1 Hcap2 Hg1 Hg2 Hc Hcontra.
  apply Hc.
  destruct c1 as [| [|] | |], c2 as [| [|] | |] ; cbn in *; simplify_eq.
Qed.

Lemma borrow_seal_capability_inj' (o : OType) (c1 c2 : Word) :
  is_cap c1 ->
  is_cap c2 ->
  isGlobalWord c1 ->
  isGlobalWord c2 ->
  c1 ≠ c2 ->
  borrow (seal_capability c1 o) ≠ borrow (seal_capability c2 o).
Proof.
  intros Hcap1 Hcap2 Hg1 Hg2 Hc Hcontra.
  apply Hc.
  destruct c1 as [| [|] | |], c2 as [| [|] | |] ; cbn in *; simplify_eq.
  destruct g,g0; simplify_eq.
Qed.

Lemma borrow_inj (w : Word) :
  isGlobalWord w ->
  is_sealed w ->
  w ≠ borrow w.
Proof.
  intros Hw Hcontra.
  destruct w as [| [|] | |]; cbn in *; simplify_eq; auto.
  destruct sb; cbn in *; auto; destruct g; cbn in *; auto.
Qed.

Ltac entry_point_inj :=
  try ( apply seal_capability_inj; auto )
  ; try (apply borrow_inj; auto)
  ; try (symmetry ; apply borrow_inj; auto)
  ; try (apply borrow_seal_capability_inj ; auto)
  ; try (apply borrow_seal_capability_inj' ; auto).


(** Useful instances *)


Global Instance sealable_countable : Countable Sealable.
Proof.
  set (enc := fun sb =>
       match sb with
       | SCap p g b e a => inl (p,g,b,e,a)
       | SSealRange p g b e a => inr (p,g,b,e,a) end
      ).
  set (dec := fun e =>
       match e with
       | inl (p,g,b,e,a) => SCap p g b e a
       | inr (p,g,b,e,a) => SSealRange p g b e a end
      ).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Defined.

Global Instance word_countable : Countable Word.
Proof.
  set (enc := fun w =>
      match w with
      | WInt z => inl (inl z)
      | WSentry p g b e a => inl (inr (p,g,b,e,a))
      | WSealable sb => inr (inl sb)
      | WSealed x x0 => inr (inr (x, x0))
      end ).
  set (dec := fun e =>
      match e with
      | inl (inl z) => WInt z
      | inl (inr (p,g,b,e,a)) => WSentry p g b e a
      | inr (inl sb) => WSealable sb
      | inr (inr (x, x0)) => WSealed x x0
      end ).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Qed.

Global Instance word_inhabited: Inhabited Word := populate (WInt 0).


Global Instance readAllowedWord_dec w: Decision (readAllowedWord w).
Proof. destruct w as [| [ p g b e a |  ] | | ]; try (right; solve [auto]). destruct p;simpl;apply _. Qed.

Global Instance writeAllowedWord_dec w: Decision (writeAllowedWord w).
Proof. destruct w as [| [ p g b e a |  ] | | ]; try (right; solve [auto]). destruct p;simpl;apply _. Qed.

Global Instance hasValidAddress_dec w a: Decision (hasValidAddress w a).
Proof. destruct w as [| [ p g b e a' |  ] | | ]; try (right; solve [auto]). destruct p;simpl;apply _. Qed.

