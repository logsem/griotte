From Coq Require Import ssreflect Eqdep_dec.
From stdpp Require Import gmap fin_maps list countable.
From iris.proofmode Require Import proofmode.
From cap_machine Require Export addr_reg solve_addr machine_utils_extra.

(* Definition and auxiliary facts on capabilities, permissions and addresses.

   The [solve_cap_pure] tactic automates the proof of some of these facts (see
   solve_cap_pure.v on how to extend it). *)

(* Definitions: capabilities, machine String.words, machine instructions *)

Inductive RXperm : Type :=
| Orx
| R
| X
| XSR (* eXecute with System Access Register, high level of execution *)
.

Inductive Wperm : Type :=
| Ow
| W
| WL.

Inductive DLperm : Type :=
| LG (* Load Global, i.e., does not change the locality bit when loading *)
| DL (* Deep Local, i.e., any loaded capability set DL and Local *)
.

Inductive DROperm : Type :=
| LM (* Load Mutable, i.e., does not change the W permission when loading *)
| DRO (* Deep RO, i.e., any loaded capability has their Wperm set to Ow *)
.

Inductive Perm: Type :=
| BPerm (rx: RXperm) (w: Wperm) (dl: DLperm) (dro: DROperm)
| E     (* Sentry, unseals to (BPerm RX Ow LG LM) *)
| ESR   (* Privileged Sentry, unseals to (BPerm XSR Ow LG LM)  *)
.

Notation O dl dro := (BPerm Orx Ow dl dro).

Notation WO        := (BPerm Orx W LG LM).
Notation WO_DL     := (BPerm Orx W DL LM).
Notation WO_DRO    := (BPerm Orx W LG DRO).
Notation WO_DL_DRO := (BPerm Orx W DL DRO).

Notation WLO        := (BPerm Orx WL LG LM).
Notation WLO_DL     := (BPerm Orx WL DL LM).
Notation WLO_DRO    := (BPerm Orx WL LG DRO).
Notation WLO_DL_DRO := (BPerm Orx WL DL DRO).

Notation RO        := (BPerm R Ow LG LM).
Notation RO_DL     := (BPerm R Ow DL LM).
Notation RO_DRO    := (BPerm R Ow LG DRO).
Notation RO_DL_DRO := (BPerm R Ow DL DRO).

Notation RW        := (BPerm R W LG LM).
Notation RW_DL     := (BPerm R W DL LM).
Notation RW_DRO    := (BPerm R W LG DRO).
Notation RW_DL_DRO := (BPerm R W DL DRO).

Notation RWL        := (BPerm R WL LG LM).
Notation RWL_DL     := (BPerm R WL DL LM).
Notation RWL_DRO    := (BPerm R WL LG DRO).
Notation RWL_DL_DRO := (BPerm R WL DL DRO).

Notation RX        := (BPerm X Ow LG LM).
Notation RX_DL     := (BPerm X Ow DL LM).
Notation RX_DRO    := (BPerm X Ow LG DRO).
Notation RX_DL_DRO := (BPerm X Ow DL DRO).

Notation RWX        := (BPerm X W LG LM).
Notation RWX_DL     := (BPerm X W DL LM).
Notation RWX_DRO    := (BPerm X W LG DRO).
Notation RWX_DL_DRO := (BPerm X W DL DRO).

Notation RWLX        := (BPerm X WL LG LM).
Notation RWLX_DL     := (BPerm X WL DL LM).
Notation RWLX_DRO    := (BPerm X WL LG DRO).
Notation RWLX_DL_DRO := (BPerm X WL DL DRO).

Notation XSR_       := (BPerm XSR Ow LG LM).
Notation XSR_DL     := (BPerm XSR Ow DL LM).
Notation XSR_DRO    := (BPerm XSR Ow LG DRO).
Notation XSR_DL_DRO := (BPerm XSR Ow DL DRO).

Notation XSRW_       := (BPerm XSR W LG LM).
Notation XSRW_DL     := (BPerm XSR W DL LM).
Notation XSRW_DRO    := (BPerm XSR W LG DRO).
Notation XSRW_DL_DRO := (BPerm XSR W DL DRO).

Notation XSRWL_       := (BPerm XSR WL LG LM).
Notation XSRWL_DL     := (BPerm XSR WL DL LM).
Notation XSRWL_DRO    := (BPerm XSR WL LG DRO).
Notation XSRWL_DL_DRO := (BPerm XSR WL DL DRO).

Inductive Locality: Type :=
| Global
| Local.

Definition SealPerms: Type := bool * bool. (* Permit_Seal x Permit_Unseal *)
Definition permit_seal (s : SealPerms) :=
  s.1.
Definition permit_unseal (s : SealPerms) :=
  s.2.

Inductive Sealable: Type :=
| SCap (p : Perm) (g : Locality) (b e a : Addr)
| SSealRange (p : SealPerms) (g : Locality) (b e a : OType).

(* Having different syntactic categories here simplifies the definition of instructions later, but requires some duplication in defining bounds changes and lea on sealing ranges *)
Inductive Word: Type :=
| WInt (z : Z)
| WSealable (sb : Sealable)
| WSealed (ot : OType) (sb : Sealable).

Notation WCap p g b e a := (WSealable (SCap p g b e a)).
Notation WSealRange p g b e a := (WSealable (SSealRange p g b e a)).

Inductive instr: Type :=
| Jmp (r: RegName)
| Jnz (r1 r2: RegName)
| Mov (dst: RegName) (src: Z + RegName)
| Load (dst src: RegName)
| Store (dst: RegName) (src: Z + RegName)
| Lt (dst: RegName) (r1 r2: Z + RegName)
| Add (dst: RegName) (r1 r2: Z + RegName)
| Sub (dst: RegName) (r1 r2: Z + RegName)
| Lea (dst: RegName) (r: Z + RegName)
| Restrict (dst: RegName) (r: Z + RegName)
| Subseg (dst: RegName) (r1 r2: Z + RegName)
| GetB (dst r: RegName)
| GetE (dst r: RegName)
| GetA (dst r: RegName)
| GetP (dst r: RegName)
| GetL (dst r: RegName)
| GetWType (dst r : RegName) (* combine IsCap, GetTag, and GetSealed all together into a unique encoding *)
| GetOType (dst r: RegName)
| Seal (dst : RegName) (r1 r2: RegName)
| UnSeal (dst : RegName) (r1 r2: RegName)
(* Separate SpecialRW into 2 instructions *)
| ReadSR (dst: RegName) (src: SRegName)
| WriteSR (dst: SRegName) (src: RegName)
| Fail
| Halt.

(* Convenient coercion when writing instructions *)
Definition regn : RegName → (Z+RegName)%type := inr.
Definition cst : Z → (Z+RegName)%type := inl.
Coercion regn : RegName >-> sum.
Coercion cst : Z >-> sum.

(* Registers and memory: maps from register names/addresses to String.words *)

Definition Reg := gmap RegName Word.
Definition SReg := gmap SRegName Word.
Definition Mem := gmap Addr Word.

(* EqDecision instances *)

Global Instance rxperm_eq_dec : EqDecision RXperm.
Proof. solve_decision. Defined.
Global Instance wperm_eq_dec : EqDecision Wperm.
Proof. solve_decision. Defined.
Global Instance dlperm_eq_dec : EqDecision DLperm.
Proof. solve_decision. Defined.
Global Instance droperm_eq_dec : EqDecision DROperm.
Proof. solve_decision. Defined.
Global Instance perm_eq_dec : EqDecision Perm.
Proof. solve_decision. Defined.
Global Instance loc_eq_dec : EqDecision Locality.
Proof. solve_decision. Defined.
Global Instance sealb_eq_dec : EqDecision Sealable.
Proof. solve_decision. Qed.
Global Instance word_eq_dec : EqDecision Word.
Proof. solve_decision. Qed.
Global Instance instr_eq_dec : EqDecision instr.
Proof. solve_decision. Defined.

Ltac destruct_word w :=
  let z := fresh "z" in
  let c := fresh "c" in
  let sr := fresh "sr" in
  let sd := fresh "sd" in
  destruct w as [ z | [c | sr] | sd].

Ltac destruct_perm p :=
  let rx := fresh "rx" in
  let w := fresh "w" in
  let dl := fresh "dl" in
  let dro := fresh "dro" in
  destruct p as [rx w dl dro | |]; [destruct rx, w, dl, dro| |].

Ltac destruct_sealperm p :=
  let b := fresh "b" in
  let b1 := fresh "b1" in
  destruct p as [b b1]; destruct b, b1.

(***** Identifying parts of String.words *****)

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

Definition is_sealed_with_o (w : Word) (o : OType) : bool :=
  match w with
  | WSealed o' sb => (o =? o')%ot
  | _ => false end.


(* non-E capability or range of seals *)
Definition is_mutable_range (w : Word) : bool:=
  match w with
  | WCap p _ _ _ _ => match p with | E | ESR => false | _ => true end
  | WSealRange _ _ _ _ _ => true
  | _ => false end.

(* Auxiliary definitions to work on permissions *)
Definition executeAllowed (p: Perm): bool :=
  match p with
  | BPerm X _ _ _
  | BPerm XSR _ _ _ => true
  | _ => false
  end.

Definition readAllowed (p: Perm): bool :=
  match p with
  | BPerm R _ _ _
  | BPerm X _ _ _
  | BPerm XSR _ _ _ => true
  | _ => false
  end.

Definition writeAllowed (p: Perm): bool :=
  match p with
  | BPerm _ W _ _
  | BPerm _ WL _ _=> true
  | _ => false
  end.

Definition has_sreg_access (p: Perm): bool :=
  match p with
  | BPerm XSR _ _ _ => true
  | _ => false
  end.

Definition isWL p : bool :=
  match p with
  | BPerm _ WL _ _ => true
  | _ => false
  end.

Definition isDL p : bool :=
  match p with
  | BPerm _ _ DL _ => true
  | _ => false
  end.

Definition isDRO p : bool :=
  match p with
  | BPerm _ _ _ DRO => true
  | _ => false
  end.

Definition isO (p : Perm) : bool :=
  match p with
  | BPerm Orx Ow _ _ => true
  | _ => false
  end.

Definition isE (p : Perm) : bool :=
 match p with
   | E => true
   | _ => false
 end.

Definition isESR (p : Perm) : bool :=
 match p with
   | ESR => true
   | _ => false
 end.

Definition isSentry (p : Perm) : bool :=
 match p with
   | E | ESR => true
   | BPerm _ _ _ _ => false
 end.

Definition isLocal (l: Locality): bool :=
  match l with
  | Local  => true
  | _ => false
  end.

Definition isLocalSealable (sb : Sealable): bool :=
  match sb with
  | SCap _ l _ _ _ | SSealRange _ l _ _ _ => isLocal l
  end.

Definition isLocalWord (w : Word): bool :=
  match w with
  | WInt _ => false
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

Definition writeAllowed_a_in_regs (r : Reg) (a : Addr) :=
  ∃ reg (w : Word), r !! reg = Some w ∧ writeAllowedWord w ∧ hasValidAddress w a.

Definition readAllowed_a_in_regs (r : Reg) (a : Addr) :=
  ∃ reg (w : Word), r !! reg = Some w ∧ readAllowedWord w ∧ hasValidAddress w a.


(* Helper definitions for capabilities *)

(* Turn E into RX, and ESR into XSR after a jump *)
Definition updatePcPerm (w: Word): Word :=
  match w with
  | WCap E g b e a => WCap RX g b e a
  | WCap ESR g b e a => WCap XSR_ g b e a
  | _ => w
  end.

Definition nonZero (w: Word): bool :=
  match w with
  | WInt n => Zneq_bool n 0
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
  | E => E
  | ESR => ESR
  end.

Definition deeplocal_sb (sb : Sealable) :=
  match sb with
  | SCap p g b e a => SCap (deeplocal_perm p) g b e a
  | SSealRange sp g b e a => SSealRange sp g b e a
  end.

Definition borrow_sb (sb : Sealable) :=
  match sb with
  | SSealRange sp _ b e a => SSealRange sp Local b e a
  | SCap p _ b e a => SCap p Local b e a
  end.

Definition borrow (w : Word) :=
  match w with
  | WSealable sb => WSealable (borrow_sb sb)
  | WSealed ot sb => WSealed ot (borrow_sb sb)
  | _ => w
  end.

Definition deeplocal (w : Word) :=
  match w with
  | WSealable sb => WSealable (deeplocal_sb sb)
  | _ => w
  end.

Definition readonly_perm (p : Perm) :=
  match p with
  | BPerm rx _ dl _ => BPerm rx Ow dl DRO
  | E => E
  | ESR => ESR
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
  | E => E
  | ESR => ESR
  end.



(** FlowsTo relation for capability permissions *)

Definition RXPermFlowsTo (rx1 rx2: RXperm): bool :=
  match rx1 with
  | Orx => true
  | R => match rx2 with
        | R | X | XSR => true
        | _ => false
        end
  | X => match rx2 with
        | X | XSR => true
        | _ => false
        end
  | XSR => match rx2 with
        | XSR => true
        | _ => false
        end
  end.

Lemma RXPermFlowsTo_refl : forall rx,  RXPermFlowsTo rx rx.
Proof.
  destruct rx; cbn ; done.
Qed.
Global Instance RXPermFlowsToReflexive: Reflexive RXPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply RXPermFlowsTo_refl.
Qed.

Lemma RXPermFlowsTo_trans : transitive _ RXPermFlowsTo.
Proof.
  red; intros.
  destruct x; destruct y; destruct z; try congruence; auto.
Qed.
Global Instance RXPermFlowsToTransitive: Transitive RXPermFlowsTo.
Proof.
  rewrite /Transitive.
  apply RXPermFlowsTo_trans.
Qed.


Definition WPermFlowsTo (w1 w2 : Wperm) : bool :=
  match w1 with
  | Ow => true
  | W => match w2 with
        | W | WL => true
        | _ => false
        end
  | WL => match w2 with
         | WL => true
         | _ => false
         end
  end.

Lemma WPermFlowsTo_refl : forall rx,  WPermFlowsTo rx rx.
Proof.
  destruct rx; cbn ; done.
Qed.
Global Instance WPermFlowsToReflexive: Reflexive WPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply WPermFlowsTo_refl.
Qed.

Lemma WPermFlowsTo_trans : transitive _ WPermFlowsTo.
Proof.
  red; intros.
  destruct x; destruct y; destruct z; try congruence; auto.
Qed.
Global Instance WPermFlowsToTransitive: Transitive WPermFlowsTo.
Proof.
  rewrite /Transitive.
  apply WPermFlowsTo_trans.
Qed.


Definition DLPermFlowsTo (dl1 dl2 : DLperm) : bool :=
  match dl1 with
  | DL => true
  | LG => match dl2 with
             | LG => true
             | _ => false
             end
  end.

Lemma DLPermFlowsTo_refl : forall rx,  DLPermFlowsTo rx rx.
Proof.
  destruct rx; cbn ; done.
Qed.
Global Instance DLPermFlowsToReflexive: Reflexive DLPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply DLPermFlowsTo_refl.
Qed.

Lemma DLPermFlowsTo_trans : transitive _ DLPermFlowsTo.
Proof.
  red; intros.
  destruct x; destruct y; destruct z; try congruence; auto.
Qed.
Global Instance DLPermFlowsToTransitive: Transitive DLPermFlowsTo.
Proof.
  rewrite /Transitive.
  apply DLPermFlowsTo_trans.
Qed.


Definition DROPermFlowsTo (dro1 dro2 : DROperm) : bool :=
  match dro1 with
  | DRO => true
  | LM => match dro2 with
             | LM => true
             | _ => false
             end
  end.

Lemma DROPermFlowsTo_refl : forall rx,  DROPermFlowsTo rx rx.
Proof.
  destruct rx; cbn ; done.
Qed.
Global Instance DROPermFlowsToReflexive: Reflexive DROPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply DROPermFlowsTo_refl.
Qed.

Lemma DROPermFlowsTo_trans : transitive _ DROPermFlowsTo.
Proof.
  red; intros.
  destruct x; destruct y; destruct z; try congruence; auto.
Qed.
Global Instance DROPermFlowsToTransitive: Transitive DROPermFlowsTo.
Proof.
  rewrite /Transitive.
  apply DROPermFlowsTo_trans.
Qed.


Definition PermFlowsTo (p1 p2: Perm): bool :=
  match p1,p2 with
  | BPerm rx1 w1 dl1 dro1, BPerm rx2 w2 dl2 dro2 =>
      RXPermFlowsTo rx1 rx2
      && WPermFlowsTo w1 w2
      && DLPermFlowsTo dl1 dl2
      && DROPermFlowsTo dro1 dro2
  | E, E => true
  | ESR, ESR => true
  | E, BPerm rx w LG LM =>
      RXPermFlowsTo X rx
  | ESR, BPerm rx w LG LM =>
      RXPermFlowsTo XSR rx
  | _, _ => false
  end.

(* Sanity check *)
Lemma PermFlowsTo_trans:
  transitive _ PermFlowsTo.
Proof.
  red; intros.
  destruct_perm x; destruct_perm y; destruct_perm z; try congruence; auto.
Qed.
Global Instance PermFlowsToTransitive: Transitive PermFlowsTo.
Proof.
  rewrite /Transitive.
  apply PermFlowsTo_trans.
Qed.

(* Sanity check 2 *)
Lemma PermFlowsTo_refl:
  forall p, PermFlowsTo p p.
Proof.
  intros; destruct_perm p; auto.
Qed.
Global Instance PermFlowsToReflexive: Reflexive PermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply PermFlowsTo_refl.
Qed.

Definition PermFlowsToCap (p: Perm) (w: Word) : bool :=
  match w with
  | WCap p' _  _ _ _ => PermFlowsTo p p'
  | _ => false
  end.


(** FlowsTo relation for locality *)

Definition LocalityFlowsTo (l1 l2: Locality): bool :=
  match l1 with
  | Local => true
  | Global => match l2 with
             | Global => true
             | _ => false
             end
  end.

(* Sanity check *)
Lemma localityflowsto_trans :
  transitive _ LocalityFlowsTo.
Proof.
  red; intros; destruct x; destruct y; destruct z; try congruence; auto.
Qed.
Global Instance LocalityFlowsToTransitive: Transitive LocalityFlowsTo.
Proof.
  rewrite /Transitive.
  apply localityflowsto_trans.
Qed.

(* Sanity check 2 *)
Lemma localityflowsto_refl:
  forall g, LocalityFlowsTo g g.
Proof.
  intros; destruct g; auto.
Qed.
Global Instance LocalityFlowsToReflexive: Reflexive LocalityFlowsTo.
Proof.
  rewrite /Reflexive.
  apply localityflowsto_refl.
Qed.


(** FlowsTo relation for sealing permissions *)

Definition SealPermFlowsTo (s1 s2 : SealPerms): bool :=
  (if permit_seal(s1) then permit_seal(s2) else true) &&
  (if permit_unseal(s1) then permit_unseal(s2) else true).

(* Sanity check *)
Lemma SealPermFlowsTo_trans:
  transitive _ SealPermFlowsTo.
Proof.
  red; intros. unfold SealPermFlowsTo in *. repeat destruct (permit_seal _); repeat destruct (permit_unseal _); auto.
Qed.
Global Instance SealPermFlowsToTransitive: Transitive SealPermFlowsTo.
Proof.
  rewrite /Transitive.
  apply SealPermFlowsTo_trans.
Qed.

(* Sanity check 2 *)
Lemma SealPermFlowsTo_refl:
  forall p, SealPermFlowsTo p p.
Proof.
  intros; unfold SealPermFlowsTo. destruct (permit_seal _), (permit_unseal _); auto.
Qed.
Global Instance SealPermFlowsToReflexive: Reflexive SealPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply SealPermFlowsTo_refl.
Qed.



(** Lemmas about permissions *)

(* Lemmas about readAllowed *)

Lemma readAllowed_flowsto (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> readAllowed p1 = true
  -> readAllowed p2 = true.
Proof.
  intros Hfl Hra.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma notreadAllowed_flowsfrom (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> readAllowed p2 = false
  -> readAllowed p1 = false.
Proof.
  intros Hfl Hra.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma readAllowed_nonO (p : Perm) :
  readAllowed p = true → isO p = false.
Proof.
  intros Hra.
  destruct_perm p; auto ; done.
Qed.

Lemma readAllowed_nonE (p : Perm) :
  readAllowed p = true -> isE p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma readAllowed_nonESR (p : Perm) :
  readAllowed p = true -> isESR p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma readAllowed_nonSentry (p : Perm) :
  readAllowed p = true -> isSentry p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

(* Lemmas about writeAllowed *)

Lemma writeAllowed_flowsto (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> writeAllowed p1 = true
  -> writeAllowed p2 = true.
Proof.
  intros Hfl Hra.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma notwriteAllowed_flowsfrom (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> writeAllowed p2 = false
  -> writeAllowed p1 = false.
Proof.
  intros Hfl Hra.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma writeAllowed_nonO (p : Perm):
  writeAllowed p = true → isO p = false.
Proof.
  intros Hwa.
  destruct_perm p; auto ; try congruence.
Qed.

Lemma writeAllowed_nonE (p : Perm) :
  writeAllowed p = true -> isE p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma writeAllowed_nonESR (p : Perm) :
  writeAllowed p = true -> isESR p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma writeAllowed_nonSentry (p : Perm) :
  writeAllowed p = true -> isSentry p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.


(* Lemmas about executeAllowed *)

Lemma executeAllowed_flowsto (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> executeAllowed p1 = true
  -> executeAllowed p2 = true.
Proof.
  intros Hfl Hxa.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma notexecuteAllowed_flowsfrom (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> executeAllowed p2 = false
  -> executeAllowed p1 = false.
Proof.
  intros Hfl Hxa.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma executeAllowed_nonO (p : Perm) :
  executeAllowed p = true → isO p = false.
Proof.
  intros Hxa.
  destruct_perm p; auto; try congruence.
Qed.

Lemma executeAllowed_nonE (p : Perm) :
  executeAllowed p = true -> isE p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma executeAllowed_nonESR (p : Perm) :
  executeAllowed p = true -> isESR p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma executeAllowed_nonSentry (p : Perm) :
  executeAllowed p = true -> isSentry p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma executeAllowed_is_readAllowed (p : Perm) :
  executeAllowed p = true
  -> readAllowed p = true.
Proof.
  intros Hxa.
  destruct_perm p; cbn in *; done.
Qed.

Lemma notreadAllowed_is_notexecuteAllowed (p : Perm) :
  readAllowed p = false
  -> executeAllowed p = false.
Proof.
  intros Hxa.
  destruct_perm p; cbn in *; done.
Qed.


(* Lemmas about isWL *)

Lemma isWL_flowsto (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> isWL p1 = true
  -> isWL p2 = true.
Proof.
  intros Hfl Hra.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma notisWL_flowsfrom (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> isWL p2 = false
  -> isWL p1 = false.
Proof.
  intros Hfl Hra.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma isWL_nonO p:
  isWL p = true → isO p = false.
Proof.
  intros Hra.
  destruct_perm p; auto ; try congruence.
Qed.

Lemma isWL_nonE (p : Perm) :
  isWL p = true -> isE p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma isWL_nonESR (p : Perm) :
  isWL p = true -> isESR p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.

Lemma isWL_nonSentry (p : Perm) :
  isWL p = true -> isSentry p = false.
Proof.
  intros Hexec.
  destruct_perm p; cbn in *; done.
Qed.


(* Lemmas about sentrys *)

Lemma isE_isSentry (p : Perm) :
  isE p = true -> isSentry p = true .
Proof.
  intros HE.
  destruct_perm p; cbn in *; done.
Qed.

Lemma isESR_isSentry (p : Perm) :
  isESR p = true -> isSentry p = true .
Proof.
  intros HESR.
  destruct_perm p; cbn in *; done.
Qed.

Lemma isSentry_isE_ESR (p : Perm) :
  isSentry p = true -> (isE p = true ) \/ (isESR p = true).
Proof.
  intros Hsentry.
  destruct_perm p; cbn in *; naive_solver.
Qed.

Lemma isnotSentry_isnotE_ESR (p : Perm) :
  isSentry p = false -> (isE p = false ) /\ (isESR p = false).
Proof.
  intros Hsentry.
  destruct_perm p; cbn in *; naive_solver.
Qed.


(* Lemmas about isO *)

Lemma isO_flowsto (p p' : Perm) :
  PermFlowsTo p p'
  -> isO p = false
  -> isO p' = false.
Proof.
  intros Hfl Hra.
  destruct_perm p; destruct_perm p' ; cbn in *; done.
Qed.

Lemma notisO_flowsfrom (p p' : Perm) :
  PermFlowsTo p p'
  -> isO p' = true
  -> isO p = true.
Proof.
  intros Hfl Hra.
  destruct_perm p; destruct_perm p' ; cbn in *; done.
Qed.


(* Lemmas about isDL *)

Lemma isDL_flowsto (p p' : Perm) :
  PermFlowsTo p p' ->
  isDL p' = true ->
  isDL p = true.
Proof.
  intros Hfl Hra.
  destruct_perm p; destruct_perm p' ; cbn in *; done.
Qed.

Lemma notisDL_flowsfrom (p p' : Perm) :
  PermFlowsTo p p' ->
  isDL p = false ->
  isDL p' = false.
Proof.
  intros Hfl Hra.
  destruct_perm p; destruct_perm p' ; cbn in *; done.
Qed.


(* Lemmas about isDRO *)

Lemma isDRO_flowsto (p p' : Perm) :
  PermFlowsTo p p' ->
  isDRO p' = true ->
  isDRO p = true.
Proof.
  intros Hfl Hra.
  destruct_perm p; destruct_perm p' ; cbn in *; done.
Qed.

Lemma notisDRO_flowsfrom (p p' : Perm) :
  PermFlowsTo p p' ->
  isDRO p = false ->
  isDRO p' = false.
Proof.
  intros Hfl Hra.
  destruct_perm p; destruct_perm p' ; cbn in *; done.
Qed.


(* Lemmas about sealing permissions *)

Lemma permit_seal_flowsto p' p:
  SealPermFlowsTo p' p -> permit_seal p' = true → permit_seal p = true.
Proof.  destruct_sealperm p; destruct_sealperm p'; done. Qed.

Lemma permit_unseal_flowsto p' p:
  SealPermFlowsTo p' p -> permit_unseal p' = true → permit_unseal p = true.
Proof.  destruct_sealperm p; destruct_sealperm p'; done. Qed.


(* Lemmas about canStore *)

Lemma canStore_flowsto (p p' : Perm) (w : Word) :
  PermFlowsTo p p'
  -> canStore p w = true
  -> canStore p' w = true.
Proof.
  intros Hfl HcanStore.
  rewrite /canStore in HcanStore |- *.
  destruct (isLocalWord w).
  by eapply isWL_flowsto.
  by eapply writeAllowed_flowsto.
Qed.

Lemma notcanStore_flowsfrom (p p' : Perm) (w : Word) :
  PermFlowsTo p p'
  -> canStore p' w = false
  -> canStore p w = false.
Proof.
  intros Hfl HcanStore.
  rewrite /canStore in HcanStore |- *.
  destruct (isLocalWord w).
  by eapply notisWL_flowsfrom.
  by eapply notwriteAllowed_flowsfrom.
Qed.

Lemma canStore_writeAllowed (p : Perm) (w : Word) :
  canStore p w = true -> writeAllowed p = true.
Proof.
  intros HcanStore.
  rewrite /canStore in HcanStore.
  destruct p; cbn in *.
  - destruct w0; cbn in *; try done.
    by rewrite Tauto.if_same in HcanStore.
  - destruct (isLocalWord w); by cbn in *.
  - destruct (isLocalWord w); by cbn in *.
Qed.

Lemma canStore_nonE (p : Perm) (w : Word) :
  canStore p w = true -> isE p = false.
Proof.
  intros HcanStore.
  by eapply writeAllowed_nonE, canStore_writeAllowed.
Qed.

Lemma canStore_nonESR (p : Perm) (w : Word) :
  canStore p w = true -> isESR p = false.
Proof.
  intros HcanStore.
  by eapply writeAllowed_nonESR, canStore_writeAllowed.
Qed.

Lemma canStore_nonSentry (p : Perm) (w : Word) :
  canStore p w = true -> isSentry p = false.
Proof.
  intros HcanStore.
  by eapply writeAllowed_nonSentry, canStore_writeAllowed.
Qed.

Lemma writeAllowed_canStore_int (p : Perm) (z : Z) :
  writeAllowed p = true ->
  canStore p (WInt z) = true.
Proof.
  intros Hwa.
  destruct p; first done.
  - apply writeAllowed_nonSentry in Hwa ; done.
  - apply writeAllowed_nonSentry in Hwa ; done.
Qed.

Lemma canStore_local_isWL (p : Perm) (w : Word) :
  isLocalWord w = true
  -> canStore p w = true
  -> isWL p = true.
Proof.
  intros Hw HcanStore.
  destruct p; cycle 1.
  - apply canStore_nonSentry in HcanStore; cbn; done.
  - by rewrite /canStore Hw in HcanStore.
  - by rewrite /canStore Hw in HcanStore.
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
  - apply canStore_nonSentry in HcanStore; cbn; done.
  - apply canStore_nonSentry in HcanStore; cbn; done.
Qed.

(* Lemmas about updatePcPerm *)
Lemma updatePcPerm_cap_nonSentry
  (p : Perm) (g : Locality) (b e a : Addr) :
  isSentry p = false ->
  updatePcPerm (WCap p g b e a) = WCap p g b e a.
Proof.
  intros HnE. destruct_perm p; cbn in *; try done.
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

Lemma load_word_ESR (p : Perm) (g : Locality) (b e a : Addr) :
  load_word p (WCap ESR g b e a ) = (WCap ESR (if isDL p then Local else g) b e a ).
Proof.
  rewrite /load_word.
  by destruct (isDRO p),(isDL p); cbn.
Qed.

Lemma load_word_E (p : Perm) (g : Locality) (b e a : Addr) :
  load_word p (WCap E g b e a ) = (WCap E (if isDL p then Local else g) b e a ).
Proof.
  rewrite /load_word.
  by destruct (isDRO p),(isDL p); cbn.
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
  destruct p; [| done | done].
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
  destruct p; cbn ; [| done | done].
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



(** Helper properties about words *)

(* isPerm: permission of the capability *)
Definition isPerm p p' := @bool_decide _ (perm_eq_dec p p').

Lemma isPerm_refl p : isPerm p p = true.
Proof. destruct_perm p; auto. Qed.
Lemma isPerm_ne p p' : p ≠ p' → isPerm p p' = false.
Proof. intros Hne. destruct_perm p; destruct_perm p'; auto; congruence. Qed.

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
  destruct w.
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
  inversion Hvpc0.
  - subst; econstructor; auto.
    inversion Hvpc2; subst.
    + destruct H1 as [Hb He]. destruct H2 as [Hb2 He2]. split.
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

Lemma isCorrectPC_nonSentry p g b e a :
  isCorrectPC (WCap p g b e a) → isSentry p = false.
Proof.
  intros HcPC; inv HcPC.
  destruct_perm p; naive_solver.
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


(** Useful instances *)

Global Instance rxperm_countable : Countable RXperm.
Proof.
  set encode :=
    fun p => match p with
          | Orx => 1
          | R => 2
          | X => 3
          | XSR => 4
          end%positive.
  set decode :=
    fun n => match n with
    | 1 => Some Orx
    | 2 => Some R
    | 3 => Some X
    | 4 => Some XSR
    | _ => None
    end%positive.
  eapply (Build_Countable _ _ encode decode).
  intro p. destruct p; reflexivity.
Defined.

Global Instance wperm_countable : Countable Wperm.
Proof.
  set encode :=
    fun p => match p with
          | Ow => 1
          | W => 2
          | WL => 3
          end%positive.
  set decode :=
    fun n => match n with
    | 1 => Some Ow
    | 2 => Some W
    | 3 => Some WL
    | _ => None
    end%positive.
  eapply (Build_Countable _ _ encode decode).
  intro p. destruct p; reflexivity.
Defined.

Global Instance dlperm_countable : Countable DLperm.
Proof.
  set encode :=
    fun p => match p with
          | DL => 1
          | LG => 2
          end%positive.
  set decode :=
    fun n => match n with
    | 1 => Some DL
    | 2 => Some LG
    | _ => None
    end%positive.
  eapply (Build_Countable _ _ encode decode).
  intro p. destruct p; reflexivity.
Defined.

Global Instance droperm_countable : Countable DROperm.
Proof.
  set encode :=
    fun p => match p with
          | DRO => 1
          | LM => 2
          end%positive.
  set decode :=
    fun n => match n with
    | 1 => Some DRO
    | 2 => Some LM
    | _ => None
    end%positive.
  eapply (Build_Countable _ _ encode decode).
  intro p. destruct p; reflexivity.
Defined.

Global Instance perm_countable : Countable Perm.
Proof.
  set encode :=
    fun p => match p with
          | BPerm rx w dl dro=> inl (rx,w,dl,dro)
          | E => inr true
          | ESR => inr false
          end.
  set decode :=
    fun n => match n with
          | inl (rx,w,dl,dro) => BPerm rx w dl dro
          | inr true => E
          | inr false => ESR
          end.
  refine (inj_countable' encode decode _).
  intro p. destruct p; reflexivity.
Defined.

Global Instance locality_countable : Countable Locality.
Proof.
  set encode := fun l => match l with
    | Local => 1
    | Global => 2
    end%positive.
  set decode := fun n => match n with
    | 1 => Some Local
    | 2 => Some Global
    | _ => None
    end%positive.
  eapply (Build_Countable _ _ encode decode).
  intro l. destruct l; reflexivity.
Defined.

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
      | WInt z => inl z
      | WSealable sb => inr (inl sb)
      | WSealed x x0 => inr (inr (x, x0))
      end ).
  set (dec := fun e =>
      match e with
      | inl z => WInt z
      | inr (inl sb) => WSealable sb
      | inr (inr (x, x0)) => WSealed x x0
      end ).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Qed.

Global Instance word_inhabited: Inhabited Word := populate (WInt 0).
Global Instance addr_inhabited: Inhabited Addr := populate (@finz.FinZ MemNum 0%Z eq_refl eq_refl).
Global Instance otype_inhabited: Inhabited OType := populate (@finz.FinZ ONum 0%Z eq_refl eq_refl).

Global Instance instr_countable : Countable instr.
Proof.

  set (enc := fun e =>
      match e with
      | Jmp r => GenNode 0 [GenLeaf (inl (inl r))]
      | Jnz r1 r2 => GenNode 1 [GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))]
      | Mov dst src => GenNode 2 [GenLeaf (inl (inl dst)); GenLeaf (inr src)]
      | Load dst src => GenNode 3 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src))]
      | Store dst src => GenNode 4 [GenLeaf (inl (inl dst)); GenLeaf (inr src)]
      | Lt dst r1 r2 => GenNode 5 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Add dst r1 r2 => GenNode 6 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Sub dst r1 r2 => GenNode 7 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | Lea dst r => GenNode 8 [GenLeaf (inl (inl dst)); GenLeaf (inr r)]
      | Restrict dst r => GenNode 9 [GenLeaf (inl (inl dst)); GenLeaf (inr r)]
      | Subseg dst r1 r2 => GenNode 10 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)]
      | GetB dst r => GenNode 11 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetE dst r => GenNode 12 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetA dst r => GenNode 13 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetP dst r => GenNode 14 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetL dst r => GenNode 15 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]

      | GetOType dst r => GenNode 16 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]
      | GetWType dst r => GenNode 17 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))]

      | Seal dst r1 r2 => GenNode 18 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))]
      | UnSeal dst r1 r2 => GenNode 19 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))]
      | ReadSR dst src => GenNode 20 [GenLeaf (inl (inl dst)); GenLeaf (inl (inr src))]
      | WriteSR dst src => GenNode 21 [GenLeaf (inl (inr dst)); GenLeaf (inl (inl src))]
      | Fail => GenNode 22 []
      | Halt => GenNode 23 []
      end).
  set (dec := fun e =>
      match e with
      | GenNode 0 [GenLeaf (inl (inl r))] => Jmp r
      | GenNode 1 [GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))] => Jnz r1 r2
      | GenNode 2 [GenLeaf (inl (inl dst)); GenLeaf (inr src)] => Mov dst src
      | GenNode 3 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl src))] => Load dst src
      | GenNode 4 [GenLeaf (inl (inl dst)); GenLeaf (inr src)] => Store dst src
      | GenNode 5 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Lt dst r1 r2
      | GenNode 6 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Add dst r1 r2
      | GenNode 7 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Sub dst r1 r2
      | GenNode 8 [GenLeaf (inl (inl dst)); GenLeaf (inr r)] => Lea dst r
      | GenNode 9 [GenLeaf (inl (inl dst)); GenLeaf (inr r)] => Restrict dst r
      | GenNode 10 [GenLeaf (inl (inl dst)); GenLeaf (inr r1); GenLeaf (inr r2)] => Subseg dst r1 r2
      | GenNode 11 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetB dst r
      | GenNode 12 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetE dst r
      | GenNode 13 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetA dst r
      | GenNode 14 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetP dst r
      | GenNode 15 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetL dst r

      | GenNode 16 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetOType dst r
      | GenNode 17 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r))] => GetWType dst r

      | GenNode 18 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))] => Seal dst r1 r2
      | GenNode 19 [GenLeaf (inl (inl dst)); GenLeaf (inl (inl r1)); GenLeaf (inl (inl r2))] => UnSeal dst r1 r2
      | GenNode 20 [GenLeaf (inl (inl dst)); GenLeaf (inl (inr src))] => ReadSR dst src
      | GenNode 21 [GenLeaf (inl (inr dst)); GenLeaf (inl (inl src))] => WriteSR dst src
      | GenNode 22 [] => Fail
      |  GenNode 23 [] => Halt
      | _ => Fail (* dummy *)
      end).
  refine (inj_countable' enc dec _).
  intros i. destruct i; simpl; done.
Defined.

Global Instance readAllowedWord_dec w: Decision (readAllowedWord w).
Proof. destruct_word w; try (right; solve [auto]). destruct c;simpl;apply _. Qed.

Global Instance writeAllowedWord_dec w: Decision (writeAllowedWord w).
Proof. destruct_word w; try (right; solve [auto]). destruct c;simpl;apply _. Qed.

Global Instance hasValidAddress_dec w a: Decision (hasValidAddress w a).
Proof. destruct_word w; try (right; solve [auto]). destruct c;simpl;apply _. Qed.

Global Instance writeAllowed_a_in_regs_Decidable
  (r : Reg) (a : Addr) :
  Decision (writeAllowed_a_in_regs r a).
Proof.
  eapply finite.exists_dec.
  intros x. destruct (r !! x) eqn:Hsome;
    first destruct (decide (writeAllowedWord w)), (decide (hasValidAddress w a)).
  left. eexists _; auto.
  all : (right; intros [w1 (Heq & ? & ?)]; inversion Heq; try congruence ).
Qed.

Global Instance readAllowed_a_in_regs_Decidable
  (r : Reg) (a : Addr) :
  Decision (readAllowed_a_in_regs r a).
Proof.
  eapply finite.exists_dec.
  intros x.
  destruct (r !! x) eqn:Hsome;
    first destruct (decide (readAllowedWord w)), (decide (hasValidAddress w a)).
  left. eexists _; eauto.
  all : (right; intros [w1 (Heq & ? & ?)]; inversion Heq; try congruence ).
Qed.
