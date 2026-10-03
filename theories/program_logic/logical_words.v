From stdpp Require Import gmap countable.
From griotte Require Export machine_base machine_parameters griotte_opsem region_keys.

(** * Logical words

    A logical word is a physical word together with the identifier of the
    allocation it belongs to, if any. Identifiers are ghost only: the machine
    never sees them. The state interpretation relates logical and physical
    words by erasure ([erasure.v]).

    Every word operation acts on the physical word and keeps the identifier.
    There is no coercion from [LWord] to [Word]: the projection [lw] is
    written explicitly, so that no identifier is silently dropped. *)

Record LWord := MkLWord { lw : Word; lprov : option AId }.
Add Printing Constructor LWord.

Global Instance LWord_eq_dec : EqDecision LWord.
Proof. solve_decision. Defined.

Global Instance LWord_countable : Countable LWord.
Proof.
  refine (inj_countable' (λ v, (lw v, lprov v)) (λ x, MkLWord x.1 x.2) _).
  by intros [].
Qed.

Global Instance LWord_inhabited : Inhabited LWord := populate (MkLWord (WInt 0) None).

(** Words without identifier, e.g. integers and code. *)
Definition lword_of_word (w : Word) : LWord := MkLWord w None.
Coercion lword_of_word : Word >-> LWord.
Arguments lword_of_word / w.

(* Arbitrary provenance [π : option AId]. Declared before [@@] so that
   [MkLWord w (Some ι)] still prints as [w @@ ι]. *)
Notation "w @@? π" := (MkLWord w π) (at level 15, no associativity).
Notation "w @@ ι" := (MkLWord w (Some ι)) (at level 15, no associativity).

Lemma lword_of_word_inj w w' : lword_of_word w = lword_of_word w' → w = w'.
Proof. by intros [=]. Qed.

Lemma MkLWord_eta (v : LWord) : MkLWord v.(lw) v.(lprov) = v.
Proof. by destruct v. Qed.

(** ** Lifted word operations *)

(** The uniform lift of an operation on words: it keeps the identifier. *)
Definition lift_word (f : Word → Word) (v : LWord) : LWord :=
  MkLWord (f v.(lw)) v.(lprov).

Lemma lw_lift_word f v : (lift_word f v).(lw) = f v.(lw).
Proof. done. Qed.
Lemma lprov_lift_word f v : (lift_word f v).(lprov) = v.(lprov).
Proof. done. Qed.

Definition lclear_tag : LWord → LWord := lift_word clear_tag.
Definition lload_word (p : Perm) : LWord → LWord := lift_word (load_word p).
Definition lstore_word (p : Perm) : LWord → LWord := lift_word (store_word p).
Definition lupdatePcPerm : LWord → LWord := lift_word updatePcPerm.
Definition lborrow : LWord → LWord := lift_word borrow.
Definition lforce_global : LWord → LWord := lift_word force_global.
Definition lreadonly : LWord → LWord := lift_word readonly.
Definition ldeeplocal : LWord → LWord := lift_word deeplocal.
Definition lseal_capability (v : LWord) (ot : OType) : LWord :=
  lift_word (λ w, seal_capability w ot) v.

(** Unsealing acts on a sealed word only; other words are kept. *)
Definition lunseal (g : Locality) (v : LWord) : LWord :=
  match v with
  | MkLWord (WSealed _ sb) π => MkLWord (WSealable (machine_word.unseal g sb)) π
  | _ => v
  end.

Lemma lw_lclear_tag v : (lclear_tag v).(lw) = clear_tag v.(lw).
Proof. done. Qed.
Lemma lprov_lclear_tag v : (lclear_tag v).(lprov) = v.(lprov).
Proof. done. Qed.
Lemma lw_lload_word p v : (lload_word p v).(lw) = load_word p v.(lw).
Proof. done. Qed.
Lemma lprov_lload_word p v : (lload_word p v).(lprov) = v.(lprov).
Proof. done. Qed.
Lemma lw_lstore_word p v : (lstore_word p v).(lw) = store_word p v.(lw).
Proof. done. Qed.
Lemma lprov_lstore_word p v : (lstore_word p v).(lprov) = v.(lprov).
Proof. done. Qed.
Lemma lw_lupdatePcPerm v : (lupdatePcPerm v).(lw) = updatePcPerm v.(lw).
Proof. done. Qed.
Lemma lprov_lupdatePcPerm v : (lupdatePcPerm v).(lprov) = v.(lprov).
Proof. done. Qed.
Lemma lw_lborrow v : (lborrow v).(lw) = borrow v.(lw).
Proof. done. Qed.
Lemma lprov_lborrow v : (lborrow v).(lprov) = v.(lprov).
Proof. done. Qed.
Lemma lw_lforce_global v : (lforce_global v).(lw) = force_global v.(lw).
Proof. done. Qed.
Lemma lprov_lforce_global v : (lforce_global v).(lprov) = v.(lprov).
Proof. done. Qed.
Lemma lw_lseal_capability v ot :
  (lseal_capability v ot).(lw) = seal_capability v.(lw) ot.
Proof. done. Qed.
Lemma lprov_lseal_capability v ot : (lseal_capability v ot).(lprov) = v.(lprov).
Proof. done. Qed.
Lemma lprov_lunseal g v : (lunseal g v).(lprov) = v.(lprov).
Proof. by destruct v as [[] ?]. Qed.

Lemma lclear_tag_lword_of_word w : lclear_tag (lword_of_word w) = lword_of_word (clear_tag w).
Proof. done. Qed.
Lemma lload_word_lword_of_word p w :
  lload_word p (lword_of_word w) = lword_of_word (load_word p w).
Proof. done. Qed.
Lemma lstore_word_lword_of_word p w :
  lstore_word p (lword_of_word w) = lword_of_word (store_word p w).
Proof. done. Qed.

Lemma lclear_tag_idempotent v : lclear_tag (lclear_tag v) = lclear_tag v.
Proof. rewrite /lclear_tag /lift_word /=. by rewrite clear_tag_idempotent. Qed.

Lemma lclear_tag_untagged v : get_tag v.(lw) = false → lclear_tag v = v.
Proof.
  destruct v as [w π]. rewrite /lclear_tag /lift_word /=. intros Ht.
  by rewrite clear_tag_untagged.
Qed.

Lemma lstore_word_canStore p w :
  canStore p w.(lw) = true → lstore_word p w = w.
Proof.
  intros Hstore. destruct w as [w π].
  by rewrite /lstore_word /lift_word /= store_word_canStore.
Qed.

Global Hint Rewrite lw_lclear_tag lprov_lclear_tag lw_lload_word lprov_lload_word
  lw_lstore_word lprov_lstore_word lw_lupdatePcPerm lprov_lupdatePcPerm
  lw_lborrow lprov_lborrow lw_lforce_global lprov_lforce_global
  lw_lseal_capability lprov_lseal_capability lprov_lunseal : lword.

(** The plain Load post: the loaded word, or its untagged copy when it is a
    heap capability (the Load filter may have stripped it). The identifier is
    kept in both cases. *)
Definition lload_heap `{HeapRegion} (s v : LWord) : Prop :=
  v = s ∨ (is_heap_cap s.(lw) = true ∧ v = lclear_tag s).

(** ** Logical register files and memories *)

Notation LReg := (gmap RegName LWord).
Notation LMem := (gmap Addr LWord).

(** The word held by [cnull]: a write to [cnull] stores it, and a read of
    [cnull] returns it, as in [opsem/register_file.v]. *)
Definition lnull : LWord := MkLWord (WInt 0) None.

Definition llookup_reg (r : RegName) (regs : LReg) : option LWord :=
  w ← (regs !! r);
  Some (if (decide (r = cnull)) then lnull else w).
Definition linsert_reg (r : RegName) (w : LWord) (regs : LReg) : LReg :=
  let w' := if (decide (r = cnull)) then lnull else w in
  <[r:=w']>regs.

Notation "m !!ₗ i" := (llookup_reg i m) (at level 20) : stdpp_scope.
Notation "<[ k := a ]ₗ>" := (linsert_reg k a)
  (at level 5, right associativity, format "<[ k := a ]ₗ>") : stdpp_scope.

Lemma is_Some_llookup_reg (regs : LReg) (r : RegName) :
  is_Some (regs !!ₗ r) ↔ is_Some (regs !! r).
Proof. rewrite /llookup_reg. destruct (regs !! r); cbn; done. Qed.

Lemma llookup_reg_not_cnull (regs : LReg) (r : RegName) :
  r ≠ cnull → regs !!ₗ r = regs !! r.
Proof.
  intros Hr. rewrite /llookup_reg.
  destruct (regs !! r); cbn; last done. by rewrite decide_False.
Qed.

Lemma llookup_reg_cnull (regs : LReg) w :
  regs !! cnull = Some w → regs !!ₗ cnull = Some lnull.
Proof. rewrite /llookup_reg. by intros ->. Qed.

Lemma elem_of_dom_lreg (regs : LReg) (r : RegName) :
  r ∈ dom regs ↔ is_Some (regs !!ₗ r).
Proof. rewrite is_Some_llookup_reg. apply elem_of_dom. Qed.

Lemma llookup_reg_weaken (regs1 regs2 : LReg) (r : RegName) (w : LWord) :
  regs1 !!ₗ r = Some w → regs1 ⊆ regs2 → regs2 !!ₗ r = Some w.
Proof.
  rewrite /llookup_reg. intros Hr1 Hincl.
  destruct (regs1 !! r) eqn:Hr; cbn in *; last done.
  by rewrite (lookup_weaken _ _ _ _ Hr Hincl).
Qed.

Lemma linsert_reg_insert r w1 w2 (regs : LReg) :
  <[ r := w1 ]ₗ> (<[ r := w2 ]> regs) = <[ r := w1 ]ₗ> regs.
Proof. rewrite /linsert_reg. by rewrite insert_insert_eq. Qed.

Lemma insert_linsert_reg r w1 w2 (regs : LReg) :
  <[ r := w1 ]> (<[ r := w2 ]ₗ> regs) = <[ r := w1 ]> regs.
Proof. rewrite /linsert_reg. by rewrite insert_insert_eq. Qed.

Lemma linsert_reg_not_cnull r w (regs : LReg) :
  r ≠ cnull → <[ r := w ]ₗ> regs = <[ r := w ]> regs.
Proof. intros Hr. rewrite /linsert_reg. by rewrite decide_False. Qed.

Lemma linsert_reg_cnull w (regs : LReg) :
  <[ cnull := w ]ₗ> regs = <[ cnull := lnull ]> regs.
Proof. rewrite /linsert_reg. by case_decide. Qed.

Lemma lookup_linsert_reg_eq r w (regs : LReg) :
  (<[ r := w ]ₗ> regs) !! r = Some (if decide (r = cnull) then lnull else w).
Proof. rewrite /linsert_reg. by rewrite lookup_insert_eq. Qed.

Lemma lookup_linsert_reg_ne r r' w (regs : LReg) :
  r ≠ r' → (<[ r := w ]ₗ> regs) !! r' = regs !! r'.
Proof. intros Hne. rewrite /linsert_reg. by rewrite lookup_insert_ne. Qed.

Lemma dom_linsert_reg r w (regs : LReg) :
  dom (<[ r := w ]ₗ> regs) = {[ r ]} ∪ dom regs.
Proof. rewrite /linsert_reg. by rewrite dom_insert_L. Qed.

Lemma linsert_reg_mono r w (regs regs' : LReg) :
  regs ⊆ regs' → <[ r := w ]ₗ> regs ⊆ <[ r := w ]ₗ> regs'.
Proof. intros. rewrite /linsert_reg. by apply insert_mono. Qed.

(** ** Arguments of instructions *)

Definition lword_of_argument (regs : LReg) (a : Z + RegName) : option LWord :=
  match a with
  | inl n => Some (lword_of_word (WInt n))
  | inr r => regs !!ₗ r
  end.

Definition lz_of_argument (regs : LReg) (a : Z + RegName) : option Z :=
  match a with
  | inl z => Some z
  | inr r =>
    match regs !!ₗ r with
    | Some (MkLWord (WInt z) _) => Some z
    | _ => None
    end
  end.

Definition laddr_of_argument (regs : LReg) (src : Z + RegName) : option Addr :=
  match lz_of_argument regs src with
  | Some n => z_to_addr n
  | None => None
  end.

Definition lotype_of_argument (regs : LReg) (src : Z + RegName) : option OType :=
  match lz_of_argument regs src with
  | Some n => (z_to_otype n) : option OType
  | None => None : option OType
  end.

Lemma lz_of_argument_Some_inv (regs : LReg) (arg : Z + RegName) (z : Z) :
  lz_of_argument regs arg = Some z →
  (arg = inl z ∨ ∃ r π, arg = inr r ∧ regs !!ₗ r = Some (MkLWord (WInt z) π)).
Proof.
  unfold lz_of_argument. intro. repeat case_match; simplify_eq/=; eauto.
Qed.

Lemma lz_of_argument_Some_inv' (regs regs' : LReg) (arg : Z + RegName) (z : Z) :
  lz_of_argument regs arg = Some z →
  regs ⊆ regs' →
  (arg = inl z ∨ ∃ r π, arg = inr r ∧ regs !!ₗ r = Some (MkLWord (WInt z) π) ∧
                       regs' !!ₗ r = Some (MkLWord (WInt z) π)).
Proof.
  intros Ha Hincl. apply lz_of_argument_Some_inv in Ha as [? | (r & π & -> & Hr)]; eauto.
  right. exists r, π. split; [done|split; [done|]]. eapply llookup_reg_weaken; eauto.
Qed.

Lemma lz_of_arg_mono (regs r : LReg) arg argz :
  regs ⊆ r → lz_of_argument regs arg = Some argz → lz_of_argument r arg = Some argz.
Proof.
  intros Hincl Ha. eapply lz_of_argument_Some_inv' in Ha as [-> | (? & ? & -> & _ & Hr)]; eauto.
  cbn. by rewrite Hr.
Qed.

Lemma lword_of_argument_Some_inv (regs : LReg) (arg : Z + RegName) (w : LWord) :
  lword_of_argument regs arg = Some w →
  ((∃ z, arg = inl z ∧ w = lword_of_word (WInt z)) ∨
   (∃ r, arg = inr r ∧ regs !!ₗ r = Some w)).
Proof. unfold lword_of_argument. intro. repeat case_match; simplify_eq/=; eauto. Qed.

Lemma lword_of_argument_Some_inv' (regs regs' : LReg) (arg : Z + RegName) (w : LWord) :
  lword_of_argument regs arg = Some w →
  regs ⊆ regs' →
  ((∃ z, arg = inl z ∧ w = lword_of_word (WInt z)) ∨
   (∃ r, arg = inr r ∧ regs !!ₗ r = Some w ∧ regs' !!ₗ r = Some w)).
Proof.
  intros Ha Hincl. apply lword_of_argument_Some_inv in Ha as [? | (r & -> & Hr)]; eauto.
  right. exists r. split; [done|split; [done|]]. eapply llookup_reg_weaken; eauto.
Qed.

Lemma lword_of_arg_mono (regs r : LReg) arg w :
  regs ⊆ r → lword_of_argument regs arg = Some w → lword_of_argument r arg = Some w.
Proof.
  intros Hincl Ha. eapply lword_of_argument_Some_inv' in Ha as [(? & -> & ->) | (? & -> & _ & Hr)];
    eauto.
Qed.

Lemma laddr_of_argument_Some_inv (regs : LReg) (arg : Z + RegName) (a : Addr) :
  laddr_of_argument regs arg = Some a →
  ∃ z, z_to_addr z = Some a ∧
       (arg = inl z ∨ ∃ r π, arg = inr r ∧ regs !!ₗ r = Some (MkLWord (WInt z) π)).
Proof.
  rewrite /laddr_of_argument. destruct (lz_of_argument regs arg) eqn:Hz; last done.
  intros. eexists. split; eauto. by apply lz_of_argument_Some_inv.
Qed.

Lemma laddr_of_arg_mono (regs r : LReg) arg a :
  regs ⊆ r → laddr_of_argument regs arg = Some a → laddr_of_argument r arg = Some a.
Proof.
  rewrite /laddr_of_argument. intros Hincl.
  destruct (lz_of_argument regs arg) eqn:Hz; last done.
  by rewrite (lz_of_arg_mono _ _ _ _ Hincl Hz).
Qed.

Lemma lotype_of_argument_Some_inv (regs : LReg) (arg : Z + RegName) (o : OType) :
  lotype_of_argument regs arg = Some o →
  ∃ z, z_to_otype z = Some o ∧
       (arg = inl z ∨ ∃ r π, arg = inr r ∧ regs !!ₗ r = Some (MkLWord (WInt z) π)).
Proof.
  rewrite /lotype_of_argument. destruct (lz_of_argument regs arg) eqn:Hz; last done.
  intros. eexists. split; eauto. by apply lz_of_argument_Some_inv.
Qed.

Lemma lotype_of_arg_mono (regs r : LReg) arg o :
  regs ⊆ r → lotype_of_argument regs arg = Some o → lotype_of_argument r arg = Some o.
Proof.
  rewrite /lotype_of_argument. intros Hincl.
  destruct (lz_of_argument regs arg) eqn:Hz; last done.
  by rewrite (lz_of_arg_mono _ _ _ _ Hincl Hz).
Qed.

(** ** Erasure of identifiers

    The physical register file erases the identifiers of the logical one,
    except at [cnull], whose physical entry is never read. *)

Definition lregs_erase (regs : LReg) : Reg := lw <$> regs.
Definition lmem_erase (m : LMem) : Mem := lw <$> m.

Lemma lookup_reg_erase (regs : LReg) r :
  lookup_reg r (lregs_erase regs) = lw <$> (regs !!ₗ r).
Proof.
  rewrite /lookup_reg /llookup_reg /lregs_erase lookup_fmap.
  destruct (regs !! r) as [v|] eqn:Hv; rewrite ?Hv /=; [case_decide; done|done].
Qed.

Lemma insert_reg_erase (regs : LReg) r v :
  insert_reg r v.(lw) (lregs_erase regs) = lregs_erase (<[ r := v ]ₗ> regs).
Proof.
  rewrite /insert_reg /linsert_reg /lregs_erase fmap_insert. by case_decide.
Qed.

Lemma lookup_lregs_erase (regs : LReg) r : lregs_erase regs !! r = lw <$> regs !! r.
Proof. apply lookup_fmap. Qed.

Lemma dom_lregs_erase (regs : LReg) : dom (lregs_erase regs) = dom regs.
Proof. apply dom_fmap_L. Qed.

Lemma lregs_erase_mono (regs regs' : LReg) :
  regs ⊆ regs' → lregs_erase regs ⊆ lregs_erase regs'.
Proof. apply map_fmap_mono. Qed.

Lemma lregs_erase_insert (regs : LReg) r v :
  lregs_erase (<[ r := v ]> regs) = <[ r := v.(lw) ]> (lregs_erase regs).
Proof. apply fmap_insert. Qed.

Lemma lookup_lmem_erase (m : LMem) a : lmem_erase m !! a = lw <$> m !! a.
Proof. apply lookup_fmap. Qed.

Lemma z_of_argument_erase (regs : LReg) arg :
  z_of_argument (lregs_erase regs) arg = lz_of_argument regs arg.
Proof.
  destruct arg as [z|r]; cbn; first done.
  rewrite lookup_reg_erase. by destruct (regs !!ₗ r) as [[[] ?]|].
Qed.

Lemma word_of_argument_erase (regs : LReg) arg :
  word_of_argument (lregs_erase regs) arg = lw <$> lword_of_argument regs arg.
Proof. destruct arg as [z|r]; cbn; first done. apply lookup_reg_erase. Qed.

Lemma addr_of_argument_erase (regs : LReg) arg :
  addr_of_argument (lregs_erase regs) arg = laddr_of_argument regs arg.
Proof. by rewrite /addr_of_argument /laddr_of_argument z_of_argument_erase. Qed.

Lemma otype_of_argument_erase (regs : LReg) arg :
  otype_of_argument (lregs_erase regs) arg = lotype_of_argument regs arg.
Proof. by rewrite /otype_of_argument /lotype_of_argument z_of_argument_erase. Qed.

(** ** Simplification through logical register operations

    stdpp's [simplify_map_eq] does not see through [<[ r := w ]ₗ>], [!!ₗ] and
    the logical argument functions. We extend it (and [simplify_map_eq /=],
    [simplify_map_eq by tac]) to unfold them (the argument functions first, so
    that the lookups they expose are unfolded too) and to resolve the [cnull]
    conditionals that a hypothesis decides, before stdpp's simplifications.
    Statements keep the folded forms.

    [simplify_map_eq] is a [Tactic Notation], and overriding a notation is
    import-order dependent: any later [Import] of [stdpp.fin_maps], including
    a transitive [Export] through stdpp/iris, re-activates stdpp's notation.
    Instead, we hook into the [Ltac] [decompose_map_disjoint], which stdpp's
    [simplify_map_eq by tac] runs first. An [Ltac ::=] redefinition is global
    as soon as this file is loaded, whatever the import order. This follows
    stdpp's own [Ltac simplify_list_eq ::=] (list_tactics.v) and the
    [Zify.zify_post_hook ::=] hooks. *)

Lemma if_decide_cnull_ne {A} r (x y : A) :
  r ≠ cnull → (if decide (r = cnull) then x else y) = y.
Proof. intros. by case_decide. Qed.

Lemma if_decide_cnull_eq {A} (x y : A) :
  (if decide (cnull = cnull) then x else y) = x.
Proof. by case_decide. Qed.

Ltac lmap_resolve_cnull :=
  repeat match goal with
  | H : ?r ≠ cnull |- context [decide (?r = cnull)] =>
      rewrite (if_decide_cnull_ne r _ _ H)
  | H : ?r ≠ cnull, H' : context [decide (?r = cnull)] |- _ =>
      rewrite (if_decide_cnull_ne r _ _ H) in H'
  | H : cnull ≠ ?r |- context [decide (?r = cnull)] =>
      rewrite (if_decide_cnull_ne r _ _ (not_eq_sym H))
  | H : cnull ≠ ?r, H' : context [decide (?r = cnull)] |- _ =>
      rewrite (if_decide_cnull_ne r _ _ (not_eq_sym H)) in H'
  | |- context [decide (cnull = cnull)] => rewrite if_decide_cnull_eq
  | H : context [decide (cnull = cnull)] |- _ => rewrite if_decide_cnull_eq in H
  end.

Ltac unfold_lregs :=
  (* One [unfold] per constant: [unfold c in *] fails when [c] does not occur. *)
  try (unfold lword_of_argument in * ); try (unfold lz_of_argument in * );
  try (unfold laddr_of_argument in * ); try (unfold lotype_of_argument in * );
  try (unfold llookup_reg in * ); try (unfold linsert_reg in * ).

(* stdpp's body (stdpp 1.13, fin_maps.v), preceded by [unfold_lregs] and
   [lmap_resolve_cnull]. Keep in sync with stdpp when upgrading. *)
Ltac decompose_map_disjoint ::=
  unfold_lregs; lmap_resolve_cnull;
  repeat
  match goal with
  | H : _ ∪ _ ##ₘ _ |- _ => apply map_disjoint_union_l in H; destruct H
  | H : _ ##ₘ _ ∪ _ |- _ => apply map_disjoint_union_r in H; destruct H
  | H : {[ _ := _ ]} ##ₘ _ |- _ => apply map_disjoint_singleton_l in H
  | H : _ ##ₘ {[ _ := _ ]} |- _ =>  apply map_disjoint_singleton_r in H
  | H : <[_:=_]>_ ##ₘ _ |- _ => apply map_disjoint_insert_l in H; destruct H
  | H : _ ##ₘ <[_:=_]>_ |- _ => apply map_disjoint_insert_r in H; destruct H
  | H : ⋃ _ ##ₘ _ |- _ => apply map_disjoint_union_list_l in H
  | H : _ ##ₘ ⋃ _ |- _ => apply map_disjoint_union_list_r in H
  | H : ∅ ##ₘ _ |- _ => clear H
  | H : _ ##ₘ ∅ |- _ => clear H
  | H : Forall (.##ₘ _) _ |- _ => rewrite Forall_vlookup in H
  | H : Forall (.##ₘ _) [] |- _ => clear H
  | H : Forall (.##ₘ _) (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall (.##ₘ _) (_ :: _) |- _ => rewrite Forall_app in H; destruct H
  end.

(* Alias, for explicitness at call sites. *)
Ltac simplify_lmap_eq := simplify_map_eq.
