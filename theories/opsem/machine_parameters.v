From griotte Require Import machine_base.

Class InstructionEncoding := {
    decodeInstr : Z → instr;
    encodeInstr : instr → Z;

    decode_encode_instr_inv :
    forall (i: instr), decodeInstr (encodeInstr i) = i;
  }.

Class PermissionEncoding := {
    encodePerm : Perm → Z;
    encodePerm_inj : Inj eq eq encodePerm;
    decodePerm : Z → Perm;

    encodeLoc : Locality → Z;
    encodeLoc_inj : Inj eq eq encodeLoc;

    decodePermPair : Z → Perm * Locality;
    encodePermPair : Perm * Locality → Z;

    decode_encode_permPair_inv :
    forall pl, decodePermPair (encodePermPair pl) = pl;

    encodeSealPerms : SealPerms → Z;
    encodeSealPerms_inj : Inj eq eq encodeSealPerms;
    decodeSealPerms : Z → SealPerms;

    decode_encode_seal_perms_inv :
    forall pl, decodeSealPerms (encodeSealPerms pl) = pl;

    decodeSealPermPair : Z → SealPerms * Locality;
    encodeSealPermPair : SealPerms * Locality → Z;

    decode_encode_SealPermPair_inv :
    forall pl, decodeSealPermPair (encodeSealPermPair pl) = pl;
  }.

Class WordEncoding := {
    encodeWordType : Word -> Z;
    decodeWordType : Z -> Word;
    encodeWordType_correct :
    forall w w', match w,w' with
            | WCap _ _ _ _ _ _, WCap _ _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSentry _ _ _ _ _ _, WSentry _ _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealRange _ _ _ _ _ _, WSealRange _ _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealed _ _, WSealed _ _ => encodeWordType w = encodeWordType w'
            | WInt _, WInt _ => encodeWordType w = encodeWordType w'
            | _, _ => encodeWordType w <> encodeWordType w'
            end;
  }.

Class HeapRegion := {
    heap_b : Addr;
    heap_e : Addr;
    heap_valid : (heap_b < heap_e)%a;
  }.

Class ShadowRegion := {
    shadow_b : Addr;
    shadow_e : Addr;
    shadow_valid : (shadow_b < shadow_e)%a;
  }.

(** Shadow memory is addressed through a separate region, while [ShadowTbl]
    and shadow points-to are indexed by heap addresses. The machine may use
    any bijection between these equally sized regions. Translation is checked:
    precisely the addresses in the source region have an image. *)
Class HeapShadowTranslation `{HeapRegion} `{ShadowRegion} := {
    heap_to_shadow : Addr -> option Addr;
    shadow_to_heap : Addr -> option Addr;
    heap_shadow_same_size : (heap_e - heap_b = shadow_e - shadow_b)%Z;
    heap_to_shadow_domain a :
      is_Some (heap_to_shadow a) <-> withinBounds heap_b heap_e a = true;
    shadow_to_heap_domain a :
      is_Some (shadow_to_heap a) <-> withinBounds shadow_b shadow_e a = true;
    heap_shadow_inverse a s :
      heap_to_shadow a = Some s <-> shadow_to_heap s = Some a;
  }.

(** The default translation preserves the offset from the region's base.
    Checked addition prevents an out-of-range address from wrapping around. *)
Definition translate_region (b e target a : Addr) : option Addr :=
  if withinBounds b e a then (target + (a - b))%a else None.

Lemma translate_region_spec (b e target target_e a a' : Addr) :
  (e - b = target_e - target)%Z ->
  translate_region b e target a = Some a' <->
  (b <= a < e)%a ∧ (target <= a' < target_e)%a ∧
  (a' : Z) = (target + (a - b))%Z.
Proof.
  intros Hsize. unfold translate_region.
  destruct (withinBounds b e a) eqn:Hbounds.
  - apply withinBounds_true_iff in Hbounds. split.
    + intros Hadd. split; first done. split; solve_addr.
    + intros (_ & _ & Heq). solve_addr.
  - split; first discriminate.
    intros (Hbounds' & _). apply withinBounds_true_iff in Hbounds'. congruence.
Qed.

Lemma translate_region_domain (b e target target_e a : Addr) :
  (e - b = target_e - target)%Z ->
  is_Some (translate_region b e target a) <-> withinBounds b e a = true.
Proof.
  intros Hsize. split.
  - intros [a' Ha']. apply (translate_region_spec b e target target_e) in Ha'; last done.
    apply withinBounds_true_iff. exact (proj1 Ha').
  - intros Hb. unfold translate_region. rewrite Hb.
    apply withinBounds_true_iff in Hb.
    destruct (finz_incr_spec MemNum target (a - b)%Z)
      as [(a' & Ha' & _)|[Hnone Hbad]].
    + by exists a'.
    + solve_addr.
Qed.

Lemma translate_region_inverse (b e target target_e a a' : Addr) :
  (e - b = target_e - target)%Z ->
  translate_region b e target a = Some a' <->
  translate_region target target_e b a' = Some a.
Proof.
  intros Hsize.
  rewrite (translate_region_spec b e target target_e) //.
  rewrite (translate_region_spec target target_e b e); last lia.
  split; intros (? & ? & ?); repeat split; solve_addr.
Qed.

Definition affine_heap_shadow_translation `{HeapRegion} `{ShadowRegion}
    (Hsize : (heap_e - heap_b = shadow_e - shadow_b)%Z) : HeapShadowTranslation.
Proof.
  refine {| heap_to_shadow := translate_region heap_b heap_e shadow_b;
            shadow_to_heap := translate_region shadow_b shadow_e heap_b;
            heap_shadow_same_size := Hsize |}.
  - intros a. apply (translate_region_domain _ _ _ shadow_e). done.
  - intros a. apply (translate_region_domain _ _ _ heap_e). lia.
  - intros a s. apply translate_region_inverse. done.
Defined.

Section Translation.
  Context `{HeapRegion} `{ShadowRegion} `{!HeapShadowTranslation}.

  Lemma heap_to_shadow_bounds a s : heap_to_shadow a = Some s ->
    withinBounds heap_b heap_e a = true ∧ withinBounds shadow_b shadow_e s = true.
  Proof.
    intros Ha. split.
    - apply heap_to_shadow_domain. by exists s.
    - apply shadow_to_heap_domain. exists a. by apply heap_shadow_inverse.
  Qed.

  Lemma shadow_to_heap_bounds s a : shadow_to_heap s = Some a ->
    withinBounds shadow_b shadow_e s = true ∧ withinBounds heap_b heap_e a = true.
  Proof.
    intros Ha. apply heap_shadow_inverse in Ha.
    apply heap_to_shadow_bounds in Ha. tauto.
  Qed.

  Lemma heap_to_shadow_inj a a' s :
    heap_to_shadow a = Some s -> heap_to_shadow a' = Some s -> a = a'.
  Proof. intros Ha Ha'. apply heap_shadow_inverse in Ha, Ha'. congruence. Qed.

  Lemma shadow_to_heap_inj s s' a :
    shadow_to_heap s = Some a -> shadow_to_heap s' = Some a -> s = s'.
  Proof. intros Ha Ha'. apply heap_shadow_inverse in Ha, Ha'. congruence. Qed.
End Translation.

Class MachineParameters := {
    instruction_encoding_mixin :: InstructionEncoding;
    permission_encoding_mixin :: PermissionEncoding;
    word_encoding_mixin :: WordEncoding;
    (* Machine parameters for the heap and the shadow regions *)
    heap_mixin :: HeapRegion;
    shadow_mixin :: ShadowRegion;
    heap_shadow_translation_mixin :: HeapShadowTranslation;
    heap_shadow_disjoint :
    (finz.seq_between heap_b heap_e) ##
      (finz.seq_between shadow_b shadow_e);
  }.

(* Region predicates shared by the operational semantics and specifications. *)
Definition is_heap_address `{HeapRegion} (a : Addr) : bool :=
  withinBounds heap_b heap_e a.

Definition is_shadow_address `{ShadowRegion} (a : Addr) : bool :=
  withinBounds shadow_b shadow_e a.

(* Only ordinary capabilities are checked for revocation, using their base. *)
Definition is_heap_cap `{HeapRegion} (w : Word) : bool :=
  match w with
  | WCap _ _ _ b _ _ => is_heap_address b
  | _ => false
  end.

Definition disjoint_from_shadow `{ShadowRegion} (b e : Addr) : Prop :=
  finz.seq_between b e ## finz.seq_between shadow_b shadow_e.

Definition disjoint_from_heap `{HeapRegion} (b e : Addr) : Prop :=
  finz.seq_between b e ## finz.seq_between heap_b heap_e.

Lemma disjoint_from_shadow_not_in `{ShadowRegion} (b e a : Addr) :
  disjoint_from_shadow b e →
  withinBounds b e a = true →
  is_shadow_address a = false.
Proof.
  intros Hdisjoint Hbounds. apply not_true_is_false. intros Hshadow.
  apply withinBounds_true_iff in Hbounds, Hshadow.
  rewrite /disjoint_from_shadow elem_of_disjoint in Hdisjoint.
  eapply Hdisjoint; apply elem_of_finz_seq_between; eauto.
Qed.

(* Lift the encoding / decoding between Z and instructions on Words: simplify
   fail on capabilities. *)

Definition decodeInstrW `{MachineParameters} : Word → instr :=
  fun w =>
    match w with
    | WInt z => decodeInstr z
    | _ => Fail
    end.

Definition encodeInstrW `{MachineParameters} : instr → Word :=
  fun i => WInt (encodeInstr i).

Lemma decode_encode_instrW_inv `{MachineParameters} (i: instr):
  decodeInstrW (encodeInstrW i) = i.
Proof. apply decode_encode_instr_inv. Qed.

Definition encodeInstrsW `{MachineParameters} : list instr → list Word :=
  map encodeInstrW.

Global Instance decode_encode_cancel `{MachineParameters}: Cancel (=) decodeInstr encodeInstr.
Proof. intro. eapply decode_encode_instr_inv. Qed.

Global Instance decode_encode_cancelW `{MachineParameters}: Cancel (=) decodeInstrW encodeInstrW.
Proof. intro. eapply decode_encode_instrW_inv. Qed.

Global Instance decode_instr_surj `{MachineParameters}: Surj (=) decodeInstr.
Proof. eapply cancel_surj. Qed.

Global Instance encode_instr_inj `{MachineParameters}: Inj (=) (=) encodeInstr.
Proof. eapply cancel_inj. Qed.

Global Instance decode_instrW_surj `{MachineParameters}: Surj (=) decodeInstrW.
Proof. eapply cancel_surj. Qed.

Global Instance encode_instrw_inj `{MachineParameters}: Inj (=) (=) encodeInstrW.
Proof. eapply cancel_inj. Qed.


Section word_type_encoding.
  Definition wt_cap := WCap true (O LG LM) Global 0%a 0%a 0%a.
  Definition wt_sentry := WSentry true (O LG LM) Global 0%a 0%a 0%a.
  Definition wt_sealrange := WSealRange true (false, false) Global 0%ot 0%ot 0%ot.
  Definition wt_sealed := WSealed 0%ot (SCap true (O LG LM) Global 0%a 0%a 0%a).
  Definition wt_int := WInt 0.
End word_type_encoding.

Ltac solve_encodeWordType :=
  match goal with
  | H: _ |- encodeWordType ?x = encodeWordType ?y =>
      try reflexivity
      ; pose proof (encodeWordType_correct x y) as Heq
      ; unfold wt_cap, wt_sentry, wt_int, wt_sealrange, wt_cap; simpl in Heq
      ; auto
  end.

Ltac simpl_encodeWordType :=
  match goal with
  | H: _ |- context G [encodeWordType (WCap ?t ?p ?g ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WCap t p g b e a) = encodeWordType wt_cap) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSentry ?t ?p ?g ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WSentry t p g b e a) = encodeWordType wt_sentry) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSealRange ?t ?p ?g ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WSealRange t p g b e a) = encodeWordType wt_sealrange) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WInt ?n)] =>
      rewrite (_: encodeWordType (WInt n) = encodeWordType wt_int) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSealed ?o ?s)] =>
      rewrite (_: encodeWordType (WSealed o s) = encodeWordType wt_sealed) ; last solve_encodeWordType
  end.

Lemma encodeWordType_correct_cap `{MachineParameters} : forall t p g b e a t' p' g' b' e' a',
  encodeWordType (WCap t p g b e a) = encodeWordType (WCap t' p' g' b' e' a').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sentry `{MachineParameters} : forall t p g b e a t' p' g' b' e' a',
  encodeWordType (WSentry t p g b e a) = encodeWordType (WSentry t' p' g' b' e' a').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_int `{MachineParameters} : forall z z',
  encodeWordType (WInt z) = encodeWordType (WInt z').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sealrange `{MachineParameters} : forall t p g b e a t' p' g' b' e' a',
  encodeWordType (WSealRange t p g b e a) = encodeWordType (WSealRange t' p' g' b' e' a').
Proof.
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sealed `{MachineParameters} : forall o s o' s',
  encodeWordType (WSealed o s) = encodeWordType (WSealed o' s').
  intros; solve_encodeWordType.
Qed.
