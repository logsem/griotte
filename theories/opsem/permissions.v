From Stdlib Require Import ssreflect Eqdep_dec.
From stdpp Require Import decidable countable.
From griotte Require Import stdpp_extra .
(* From stdpp Require Import gmap fin_maps list countable. *)
(* From griotte Require Export registers. *)

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
.

Notation O dl dro       := (BPerm Orx Ow dl dro).

Notation WO             := (BPerm Orx W LG LM).
Notation WO_DL          := (BPerm Orx W DL LM).
Notation WO_DRO         := (BPerm Orx W LG DRO).
Notation WO_DL_DRO      := (BPerm Orx W DL DRO).

Notation WLO            := (BPerm Orx WL LG LM).
Notation WLO_DL         := (BPerm Orx WL DL LM).
Notation WLO_DRO        := (BPerm Orx WL LG DRO).
Notation WLO_DL_DRO     := (BPerm Orx WL DL DRO).

Notation RO             := (BPerm R Ow LG LM).
Notation RO_DL          := (BPerm R Ow DL LM).
Notation RO_DRO         := (BPerm R Ow LG DRO).
Notation RO_DL_DRO      := (BPerm R Ow DL DRO).

Notation RW             := (BPerm R W LG LM).
Notation RW_DL          := (BPerm R W DL LM).
Notation RW_DRO         := (BPerm R W LG DRO).
Notation RW_DL_DRO      := (BPerm R W DL DRO).

Notation RWL            := (BPerm R WL LG LM).
Notation RWL_DL         := (BPerm R WL DL LM).
Notation RWL_DRO        := (BPerm R WL LG DRO).
Notation RWL_DL_DRO     := (BPerm R WL DL DRO).

Notation RX             := (BPerm X Ow LG LM).
Notation RX_DL          := (BPerm X Ow DL LM).
Notation RX_DRO         := (BPerm X Ow LG DRO).
Notation RX_DL_DRO      := (BPerm X Ow DL DRO).

Notation RWX            := (BPerm X W LG LM).
Notation RWX_DL         := (BPerm X W DL LM).
Notation RWX_DRO        := (BPerm X W LG DRO).
Notation RWX_DL_DRO     := (BPerm X W DL DRO).

Notation RWLX           := (BPerm X WL LG LM).
Notation RWLX_DL        := (BPerm X WL DL LM).
Notation RWLX_DRO       := (BPerm X WL LG DRO).
Notation RWLX_DL_DRO    := (BPerm X WL DL DRO).

Notation XSR_           := (BPerm XSR Ow LG LM).
Notation XSR_DL         := (BPerm XSR Ow DL LM).
Notation XSR_DRO        := (BPerm XSR Ow LG DRO).
Notation XSR_DL_DRO     := (BPerm XSR Ow DL DRO).

Notation XSRW_          := (BPerm XSR W LG LM).
Notation XSRW_DL        := (BPerm XSR W DL LM).
Notation XSRW_DRO       := (BPerm XSR W LG DRO).
Notation XSRW_DL_DRO    := (BPerm XSR W DL DRO).

Notation XSRWL_         := (BPerm XSR WL LG LM).
Notation XSRWL_DL       := (BPerm XSR WL DL LM).
Notation XSRWL_DRO      := (BPerm XSR WL LG DRO).
Notation XSRWL_DL_DRO   := (BPerm XSR WL DL DRO).

Inductive Locality: Type :=
| Global
| Local.

Definition SealPerms: Type := bool * bool. (* Permit_Seal x Permit_Unseal *)
Definition permit_seal (s : SealPerms) :=
  s.1.
Definition permit_unseal (s : SealPerms) :=
  s.2.

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

Ltac destruct_perm p :=
  let rx := fresh "rx" in
  let w := fresh "w" in
  let dl := fresh "dl" in
  let dro := fresh "dro" in
  destruct p as [rx w dl dro]; destruct rx, w, dl, dro.

Ltac destruct_sealperm p :=
  let b := fresh "b" in
  let b1 := fresh "b1" in
  destruct p as [b b1]; destruct b, b1.

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

Definition isLocal (l: Locality): bool :=
  match l with
  | Local  => true
  | _ => false
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
  intro rx; destruct rx; cbn ; done.
Qed.
Global Instance RXPermFlowsToReflexive: Reflexive RXPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply RXPermFlowsTo_refl.
Qed.

Lemma RXPermFlowsTo_trans : transitive _ RXPermFlowsTo.
Proof.
  red; intros x y z.
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
  intro rx; destruct rx; cbn ; done.
Qed.
Global Instance WPermFlowsToReflexive: Reflexive WPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply WPermFlowsTo_refl.
Qed.

Lemma WPermFlowsTo_trans : transitive _ WPermFlowsTo.
Proof.
  red; intros x y z.
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
  intro rx; destruct rx; cbn ; done.
Qed.
Global Instance DLPermFlowsToReflexive: Reflexive DLPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply DLPermFlowsTo_refl.
Qed.

Lemma DLPermFlowsTo_trans : transitive _ DLPermFlowsTo.
Proof.
  red; intros x y z.
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
  intro rx; destruct rx; cbn ; done.
Qed.
Global Instance DROPermFlowsToReflexive: Reflexive DROPermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply DROPermFlowsTo_refl.
Qed.

Lemma DROPermFlowsTo_trans : transitive _ DROPermFlowsTo.
Proof.
  red; intros x y z.
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
  end.

(* Sanity check *)
Lemma PermFlowsTo_trans:
  transitive _ PermFlowsTo.
Proof.
  red. intros p1 p2 p3 Hp12 Hp23.
  destruct p1 as [rx1 w1 dl1 dro1]
           , p2 as [rx2 w2 dl2 dro2]
           , p3  as [rx3 w3 dl3 dro3]
             ; try done.
  cbn in *.
    apply andb_prop_elim in Hp12,Hp23
    ; destruct Hp12 as [Hp12 Hdro12]
    ; destruct Hp23 as [Hp23 Hdro23].
    apply andb_prop_elim in Hp12,Hp23
    ; destruct Hp12 as [Hp12 Hdl12]
    ; destruct Hp23 as [Hp23 Hdl23].
    apply andb_prop_elim in Hp12,Hp23
    ; destruct Hp12 as [Hrx12 Hw12]
    ; destruct Hp23 as [Hrx23 Hw23].
    repeat (apply andb_prop_intro;split;try (etransitivity; eassumption) ).
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
  intros p; destruct_perm p; auto.
Qed.
Global Instance PermFlowsToReflexive: Reflexive PermFlowsTo.
Proof.
  rewrite /Reflexive.
  apply PermFlowsTo_refl.
Qed.

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
  red; intros x y z; destruct x; destruct y; destruct z; try congruence; auto.
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
  intros g; destruct g; auto.
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


(* Lemmas about isO *)

Lemma notisO_flowsfrom (p p' : Perm) :
  PermFlowsTo p p'
  -> isO p = false
  -> isO p' = false.
Proof.
  intros Hfl Hra.
  destruct_perm p; destruct_perm p' ; cbn in *; done.
Qed.

Lemma isO_flowsto (p p' : Perm) :
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



(* Lemmas about has_sreg_access *)

Lemma has_sreg_access_flowsto (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> has_sreg_access p1 = true
  -> has_sreg_access p2 = true.
Proof.
  intros Hfl Hra.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

Lemma nothas_sreg_access_flowsfrom (p1 p2 : Perm) :
  PermFlowsTo p1 p2
  -> has_sreg_access p2 = false
  -> has_sreg_access p1 = false.
Proof.
  intros Hfl Hra.
  destruct_perm p1; destruct_perm p2 ; cbn in *; done.
Qed.

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
    fun (p : Perm) => match p with
          | BPerm rx w dl dro => (rx,w,dl,dro)
          end.
  set decode :=
    fun n => match n with
          | (rx,w,dl,dro) => BPerm rx w dl dro
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


(* isPerm: permission of the capability *)
Definition isPerm p p' := @bool_decide _ (perm_eq_dec p p').

Lemma isPerm_refl p : isPerm p p = true.
Proof. destruct_perm p; auto. Qed.
Lemma isPerm_ne p p' : p ≠ p' → isPerm p p' = false.
Proof. intros Hne. destruct_perm p; destruct_perm p'; auto; congruence. Qed.
