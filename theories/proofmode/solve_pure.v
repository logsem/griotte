From Stdlib Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From griotte Require Import machine_base machine_parameters solve_addr.
From griotte Require Export solve_addr_extra classes class_instances.
From griotte Require Import rules_Get rules_BinOp.
From machine_utils Require Export solve_pure.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac solve_pure_addr := solve_pure_finz.

(* Extend the [solve_pure] tactic from [machine_utils] with additional hints
   for solving goals specific to our machine, involving (additionally from what
   [solve_pure] already handles):

   - ExecPCPerm
   - PermFlowsTo, PermFlowsTo  (TODO: extend)
   - decodeInstrW w = ?
   - readAllowed p (TODO: extend)
   - writeAllowed p (TODO: extend)
   - withinBounds (p, b, e, a) = true
   - is_Get
   - is_BinOp

   See the comments in [machine_utils/theories/solve_pure.v] on how to
   extend [solve_pure] with more hints.
*)

Lemma withinBounds_InCtx {z} (b e a : finz z) :
  InCtx (withinBounds b e a = true) →
  InBounds b e a.
Proof.
  unfold InCtx, InBounds. cbn.
  intros [?%Z.leb_le ?%Z.ltb_lt]%andb_true_iff. solve_addr.
Qed.
#[export] Hint Resolve withinBounds_InCtx : solve_pure.

(* isCorrectPC *)

#[export] Hint Mode isCorrectPC + : solve_pure.

#[export] Hint Resolve isCorrectPC_executeAllowed_InBounds : solve_pure.
(* Proxy lemma for DecodeInstr *)

Lemma DecodeInstr_prove `{MachineParameters} w i :
  DecodeInstr w i →
  decodeInstrW w = i.
Proof.
  intros ->. reflexivity.
Qed.
#[export] Hint Resolve DecodeInstr_prove : solve_pure.

(* ExecPCPerm, PermFlowsTo *)

(* #[export] Hint Mode ExecPCPerm + : solve_pure. *)
#[export] Hint Mode PermFlowsTo - + : solve_pure.
#[export] Hint Mode LocalityFlowsTo - + : solve_pure.

(* Lemma ExecPCPerm_InCtx p : *)
(*   InCtx (ExecPCPerm p) → ExecPCPerm p. *)
(* Proof. auto. Qed. *)
(* #[export] Hint Resolve ExecPCPerm_InCtx : solve_pure. *)


Lemma executeAllowed_InCtx p :
  InCtx (executeAllowed p = true) → (executeAllowed p = true).
Proof. auto. Qed.
#[export] Hint Resolve executeAllowed_InCtx : solve_pure.

(* #[export] Hint Resolve ExecPCPerm_RX : solve_pure. *)
(* #[export] Hint Resolve ExecPCPerm_RWX : solve_pure. *)
(* #[export] Hint Resolve ExecPCPerm_not_E : solve_pure. *)
(* #[export] Hint Resolve ExecPCPerm_flows_to : solve_pure. *)
(* TODO: add a test checking the use of ExecPCPerm_flows_to (if it is still *)
(*    needed) *)
(* #[export] Hint Resolve ExecPCPerm_readAllowed : solve_pure. *)
(* Will only work if arguments are concrete terms *)
#[export] Hint Extern 1 (executeAllowed _ = true) => reflexivity : solve_pure.
#[export] Hint Extern 1 (readAllowed _ = true) => reflexivity : solve_pure.
#[export] Hint Extern 1 (writeAllowed _ = true) => reflexivity : solve_pure.
#[export] Hint Extern 1 (PermFlowsTo _ _ = true) => reflexivity : solve_pure.
#[export] Hint Extern 1 (LocalityFlowsTo _ _ = true) => reflexivity : solve_pure.
(* Permissions allowed *)
#[export] Hint Resolve executeAllowed_is_readAllowed : solve_pure.
#[export] Hint Extern 1 (has_sreg_access _ = true) => reflexivity : solve_pure.
#[export] Hint Extern 1 (has_sreg_access _ = false) => reflexivity : solve_pure.
(* Follows the same behavior as the Hint Mode for PermFlowsTo *)
#[export] Hint Extern 1 (PermFlowsTo ?p ?p' = true) =>
  (without_evars p'; apply PermFlowsToReflexive): solve_pure.
#[export] Hint Extern 1 (LocalityFlowsTo ?p ?p' = true) =>
  (without_evars p'; apply LocalityFlowsToReflexive): solve_pure.

(* withinBounds *)

(* There's no use defining a Hint Mode for withinBounds, as it doesn't appear as
   the head symbol. (in "withinBounds _ = true", (=) is the head symbol).

   That's fine: this proxy lemma applies without risking instantiating any evar,
   and then the Hint Mode on [InBounds] can take effect. *)

#[export] Hint Resolve withinBounds_InBounds : solve_pure.

(* is_Get *)
#[export] Hint Mode is_Get ! - - : solve_pure.
#[export] Hint Resolve is_Get_GetP : solve_pure.
#[export] Hint Resolve is_Get_GetL : solve_pure.
#[export] Hint Resolve is_Get_GetB : solve_pure.
#[export] Hint Resolve is_Get_GetE : solve_pure.
#[export] Hint Resolve is_Get_GetA : solve_pure.
#[export] Hint Resolve is_Get_GetOType : solve_pure.
#[export] Hint Resolve is_Get_GetWType : solve_pure.
#[export] Hint Resolve is_Get_GetTag : solve_pure.

(* is_BinOp *)
#[export] Hint Mode is_BinOp ! - - - : solve_pure.
#[export] Hint Resolve is_BinOp_Add : solve_pure.
#[export] Hint Resolve is_BinOp_Sub : solve_pure.
#[export] Hint Resolve is_BinOp_Mul : solve_pure.
#[export] Hint Resolve is_BinOp_LAnd : solve_pure.
#[export] Hint Resolve is_BinOp_LOr : solve_pure.
#[export] Hint Resolve is_BinOp_LShiftL : solve_pure.
#[export] Hint Resolve is_BinOp_LShiftR : solve_pure.
#[export] Hint Resolve is_BinOp_Lt : solve_pure.

(* is_z *)
#[export] Hint Extern 1 (is_z _ = false) => reflexivity : solve_pure.
#[export] Hint Extern 1 (is_z _ = true) => reflexivity : solve_pure.

(* validity tags *)
#[export] Hint Extern 1 (get_tag _ = true) => reflexivity : solve_pure.
#[export] Hint Extern 1 (get_tag_sealable _ = true) => reflexivity : solve_pure.

(* canStore *)
#[export] Hint Extern 1 (canStore WO (WCap true _ Global _ _ _ ) = true) => done : solve_pure.
#[export] Hint Extern 1 (canStore WO (WCap true _ Local _ _ _ ) = false) => done : solve_pure.
#[export] Hint Extern 1 (canStore RW (WCap true _ Global _ _ _ ) = true) => done : solve_pure.
#[export] Hint Extern 1 (canStore RW (WCap true _ Local _ _ _ ) = false) => done : solve_pure.
#[export] Hint Extern 1 (canStore RWX (WCap true _ Global _ _ _ ) = true) => done : solve_pure.
#[export] Hint Extern 1 (canStore RWX (WCap true _ Local _ _ _ ) = false) => done : solve_pure.
#[export] Hint Extern 1 (canStore WLO (WCap true _ _ _ _ _ ) = true) => done : solve_pure.
#[export] Hint Extern 1 (canStore RWL (WCap true _ _ _ _ _ ) = true) => done : solve_pure.
#[export] Hint Extern 1 (canStore RWLX (WCap true _ _ _ _ _ ) = true) => done : solve_pure.
#[export] Hint Resolve canStoreRWL : solve_pure.

(* Untagged data does not require store-local permission. Avoid choosing
   permissions or payloads while solving a side condition. *)
#[export] Hint Extern 1 (canStore ?p ?w = true) =>
  (without_evars p; without_evars w;
   rewrite (canStore_untagged p w); [reflexivity | first [reflexivity | apply get_tag_clear_tag]]) : solve_pure.
#[export] Hint Resolve get_tag_clear_tag get_tag_clear_tag_sealable : solve_pure.

(* store_word *)
#[export] Hint Extern 1 (store_word WLO ?w = ?w) =>
  apply store_word_isWL; reflexivity : solve_pure.
#[export] Hint Extern 1 (store_word RWL ?w = ?w) =>
  apply store_word_isWL; reflexivity : solve_pure.
#[export] Hint Extern 1 (store_word RWLX ?w = ?w) =>
  apply store_word_isWL; reflexivity : solve_pure.
#[export] Hint Extern 1 (?w = store_word WLO ?w) =>
  symmetry; apply store_word_isWL; reflexivity : solve_pure.
#[export] Hint Extern 1 (?w = store_word RWL ?w) =>
  symmetry; apply store_word_isWL; reflexivity : solve_pure.
#[export] Hint Extern 1 (?w = store_word RWLX ?w) =>
  symmetry; apply store_word_isWL; reflexivity : solve_pure.

(* Identifier-less operands *)
#[export] Hint Extern 1 (@eq (option AId) ?x None) =>
  (assert_fails (has_evar x); cbn; reflexivity) : solve_pure.

(* load_exact_cond: a tagged word with non-empty bounds has authority or no
   heap base; an untagged word satisfies it vacuously. *)
#[export] Hint Extern 1 (load_exact_cond ?v) =>
  (assert_fails (has_evar v); intros ?; discriminate) : solve_pure.
#[export] Hint Extern 2 (load_exact_cond ?v) =>
  (assert_fails (has_evar v); eapply nonempty_exact_cond; [reflexivity | solve_addr]) : solve_pure.
(* A word whose base is known not to be in the heap. *)
Lemma load_exact_cond_nonheap_cap `{MachineParameters} t p g b e a π :
  is_heap_address b = false → load_exact_cond (WCap t p g b e a @@? π).
Proof. intros Hb _. right. by rewrite /heap_cap_base /= Hb. Qed.
(* Only on a known word: on an undetermined one (e.g. the source of a GetTag
   before its register is framed), the hint would fix it to a capability. *)
#[export] Hint Extern 1 (load_exact_cond ?v) =>
  (assert_fails (has_evar v); eapply load_exact_cond_nonheap_cap) : solve_pure.

(* denote - required for Get *)
#[export] Hint Extern 1 (rules_Get.denote (GetTag _ _) _ = Some _) =>
  apply gettag_denote : solve_pure.
#[export] Hint Extern 1 (denote (GetWType _ _) ?w = Some _) =>
  (eapply getwtype_denote ; reflexivity) : solve_pure.
#[export] Hint Extern 1 (rules_Get.denote _ _ = Some _) => reflexivity : solve_pure. (* unification fails if lhs has evars *)

(* The Subseg premise ruling out a fresh heap root (case 3): it is vacuous
   when the source has an identifier, and otherwise needs the new base to be
   outside the heap. *)
#[export] Hint Extern 1 (is_heap_address _ = false) =>
  first [ reflexivity
        | match goal with H : Some _ = None |- _ => discriminate H end
        | match goal with H : InCtx (is_heap_address _ = false) |- _ => exact H end ]
  : solve_pure.

(* IsLInt: an abstract word is an integer when the context says so. Only
   frozen (literal) hypotheses are used, so no evar is instantiated. *)
#[global] Instance IsLInt_InCtx w z : InCtx (w.(lw) = WInt z) → IsLInt w z.
Proof. by constructor. Qed.

Ltac griotte_freeze_hyp_once1 h :=
  let P := type of h in
  lazymatch type of P with
  | Prop =>
      lazymatch P with
      | InCtx _ => fail
      | _ => change P with (InCtx P) in h
      end
  | _ => fail
  end.

Ltac2 griotte_freeze_hyp_once (h : ident) :=
  ltac1:(h |- griotte_freeze_hyp_once1 h) (Ltac1.of_ident h).

Ltac2 rec griotte_freeze_hyps_once_aux hyps :=
  match hyps with
  | [] => ()
  | (h, _, _) :: hyps =>
      let _ := Control.case (fun _ => griotte_freeze_hyp_once h) in
      griotte_freeze_hyps_once_aux hyps
  end.

Ltac2 griotte_freeze_hyps_once () :=
  griotte_freeze_hyps_once_aux (List.rev (Control.hyps ())).

Ltac2 solve_pure_iinstr () :=
  first [ assumption
        | discriminate
        | griotte_freeze_hyps_once ();
          typeclasses_eauto with solve_pure typeclass_instances;
          ltac1:(unfreeze_hyps) ].

(* Tests *)

Goal forall (r_t1 r_t2: RegName) `{MachineParameters}, exists r1 r2,
  decodeInstrW (encodeInstrW (Mov r_t1 r_t2)) = Mov r1 r2 ∧
  r1 = r_t1 ∧ r2 = inr r_t2.
Proof. do 2 eexists. repeat apply conj; first solve_pure. all: reflexivity. Qed.

Goal forall p g b e a,
  executeAllowed p = true →
  SubBounds b e a (a ^+ 5)%a →
  ContiguousRegion a 5 →
  isCorrectPC (WCap true p g b e a).
Proof. intros. solve_pure. Qed.

Goal forall (r_t1 r_t2: RegName), exists r1 r2,
  is_Get (GetB r_t2 r_t1) r1 r2 ∧
  r1 = r_t2 ∧ r2 = r_t1.
Proof. do 2 eexists. repeat apply conj; first solve_pure. all: reflexivity. Qed.

Goal forall p g b e a,
  executeAllowed p = true →
  SubBounds b e a (a ^+ 5)%a →
  ContiguousRegion a 5 →
  isCorrectPC (WCap true p g b e (a ^+ 1)%a).
Proof. intros. solve_pure. Qed.

Goal forall (r_t1 r_t2 r_t3: RegName), exists r1 r2 r3,
  is_BinOp (Sub r_t2 r_t2 r_t3) r1 (inr r2) (inr r3) ∧
  r1 = r_t2 ∧ r2 = r_t2 ∧ r3 = r_t3.
Proof. do 3 eexists. repeat apply conj; first solve_pure. all: reflexivity. Qed.

Goal forall (P: Prop), P → P. intros. solve_pure. Qed.

Goal forall w, canStore RWL w = true. Proof. intros. solve_pure. Qed.
Goal forall w, store_word RWL w = w. Proof. intros. solve_pure. Qed.
Goal has_sreg_access XSRW_ = true. Proof. solve_pure. Qed.
Goal has_sreg_access RW = false. Proof. solve_pure. Qed.
