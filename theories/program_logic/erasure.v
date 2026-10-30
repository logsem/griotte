From stdpp Require Import gmap.
From iris.base_logic.lib Require Import ghost_map.
From griotte Require Export logical_words alloc_registry griotte_opsem griotte_opsem_prop.

(** * The erasure invariant

    The state interpretation relates the logical registers and memory to the
    physical machine state by erasure: physical words are the logical ones
    with their identifiers erased, except that a memory word whose allocation
    is quarantined or dead may be, or must be, untagged. The registry [R]
    and the address claims [C] are ghost state of the state interpretation.

    Every clause quantifies over the logical word: the tag, the bounds and
    the identifier are those of the logical word, never of its physical
    copy. *)

(** Memory never covers a memory-mapped address (shadow region or revoker):
    CLoad and Store reach those devices only through their dedicated branches. *)
Definition mem_avoids_mmio `{MachineParameters} (m : Mem) : Prop :=
  ∀ a, a ∈ dom m → is_mmio_address a = false.

Section mem_avoids_mmio.
  Context `{MachineParameters}.

  Lemma mem_avoids_mmio_lookup m a w :
    mem_avoids_mmio m → m !! a = Some w → is_mmio_address a = false.
  Proof. intros Hm Ha. apply Hm. by apply elem_of_dom_2 in Ha. Qed.

  Lemma mem_avoids_mmio_not_shadow m a w :
    mem_avoids_mmio m → m !! a = Some w → is_shadow_address a = false.
  Proof. intros. eapply not_mmio_not_shadow, mem_avoids_mmio_lookup; eauto. Qed.

  Lemma mem_avoids_mmio_not_revoker m a w :
    mem_avoids_mmio m → m !! a = Some w → is_revoker_address a = false.
  Proof. intros. eapply not_mmio_not_revoker, mem_avoids_mmio_lookup; eauto. Qed.

  Lemma mem_avoids_mmio_insert m a w :
    is_mmio_address a = false → mem_avoids_mmio m → mem_avoids_mmio (<[a := w]> m).
  Proof.
    intros Ha Hm a'. rewrite dom_insert_L elem_of_union elem_of_singleton.
    intros [-> | Ha']; [done | by apply Hm].
  Qed.

  Lemma mem_avoids_mmio_update m a w w' :
    m !! a = Some w' → mem_avoids_mmio m → mem_avoids_mmio (<[a := w]> m).
  Proof.
    intros Ha Hm. apply mem_avoids_mmio_insert; last done.
    eapply mem_avoids_mmio_lookup; eauto.
  Qed.

  Lemma mem_avoids_mmio_sweep shadow m :
    mem_avoids_mmio m → mem_avoids_mmio (sweep_mem shadow m).
  Proof. intros Hm a. rewrite dom_sweep_mem. apply Hm. Qed.

  Lemma mem_avoids_mmio_union m1 m2 :
    mem_avoids_mmio m1 → mem_avoids_mmio m2 → mem_avoids_mmio (m1 ∪ m2).
  Proof.
    intros Hm1 Hm2 a. rewrite dom_union_L elem_of_union.
    intros [Ha | Ha]; [by apply Hm1 | by apply Hm2].
  Qed.

  Lemma mem_avoids_mmio_empty : mem_avoids_mmio ∅.
  Proof. intros a. rewrite dom_empty_L. set_solver. Qed.

  Lemma advancePC_mem φ imm c :
    advancePC φ imm = Some c → mem c.2 = mem φ.
  Proof. rewrite /advancePC. repeat case_match; intros; simplify_eq; done. Qed.

  (* Every instruction preserves the clause: CLoad and Store reach the shadow
     region and the revoker through their own branches, an ordinary store
     writes a non-MMIO address, and the sweep keeps the memory's domain. *)
  Lemma exec_mem_avoids_mmio i p φ :
    mem_avoids_mmio (mem φ) → mem_avoids_mmio (mem (exec i p φ).2).
  Proof.
    intros Hφ. rewrite /exec.
    destruct (exec_opt i p φ) as [c|] eqn:Hexec; last done.
    rewrite /exec_opt /exec_jcond in Hexec.
    destruct i; cbn in Hexec; repeat case_match; simplify_eq; try done.
    all: repeat match goal with
      | H : mbind _ ?x = Some _ |- _ => destruct x eqn:?; cbn in H; try discriminate
      | H : (match ?x with _ => _ end) = Some _ |- _ =>
          destruct x eqn:?; cbn in H; try discriminate
      end.
    all: try (match goal with H : advancePC _ _ = Some _ |- _ =>
                rewrite (advancePC_mem _ _ _ H) end).
    all: try (match goal with H : nextPC _ = Some _ |- _ =>
                rewrite (advancePC_mem _ _ _ H) end).
    all: try (match goal with H : Some _ = Some _ |- _ => injection H as <- end).
    (* Jalr may write mstatus. *)
    all: try (match goal with |- context [jalr_mstatus ?w ?z] => destruct (jalr_mstatus w z) end).
    all: cbn; try done.
    - (* Revoker store *)
      by apply mem_avoids_mmio_sweep.
    - (* Ordinary store *)
      apply mem_avoids_mmio_insert; last done.
      by rewrite /is_mmio_address Heqb2 Heqb3.
  Qed.

  Lemma step_mem_avoids_mmio (cf cf' : ConfFlag) (φ φ' : ExecConf) :
    griotte_opsem.step (cf, φ) (cf', φ') →
    mem_avoids_mmio (mem φ) →
    mem_avoids_mmio (mem φ').
  Proof.
    inversion 1; subst; try done.
    intros. by apply exec_mem_avoids_mmio.
  Qed.
End mem_avoids_mmio.

(** Memory covers every heap address: a load or a store in the heap never
    reaches an absent address. *)
Definition heap_mapped `{MachineParameters} (m : Mem) : Prop :=
  ∀ a, is_heap_address a = true → a ∈ dom m.

Section heap_mapped.
  Context `{MachineParameters}.

  Lemma heap_mapped_lookup m a :
    heap_mapped m → is_heap_address a = true → is_Some (m !! a).
  Proof. intros Hm Ha. apply elem_of_dom. by apply Hm. Qed.

  Lemma heap_mapped_insert m a w :
    heap_mapped m → heap_mapped (<[a := w]> m).
  Proof. intros Hm a' Ha'. rewrite dom_insert_L elem_of_union. right. by apply Hm. Qed.

  Lemma heap_mapped_sweep shadow m :
    heap_mapped m → heap_mapped (sweep_mem shadow m).
  Proof. intros Hm a. rewrite dom_sweep_mem. apply Hm. Qed.

  Lemma heap_mapped_union_l m1 m2 :
    heap_mapped m1 → heap_mapped (m1 ∪ m2).
  Proof. intros Hm a Ha. rewrite dom_union_L elem_of_union. left. by apply Hm. Qed.
End heap_mapped.

(** The heap addresses. *)
Definition heap_addresses `{HeapRegion} : gset Addr :=
  list_to_set (finz.seq_between heap_b heap_e).

Lemma elem_of_heap_addresses `{HeapRegion} a :
  a ∈ heap_addresses <-> is_heap_address a = true.
Proof.
  rewrite /heap_addresses elem_of_list_to_set elem_of_finz_seq_between.
  symmetry. apply withinBounds_true_iff.
Qed.

(** ** Word toolkit *)

Lemma memory_cap_base_bounds (w : Word) :
  memory_cap_base w = fst <$> memory_cap_bounds w.
Proof. by destruct w as [| [] | | ? [] ]. Qed.

Lemma heap_cap_base_bounds_eq `{HeapRegion} (w w' : Word) :
  memory_cap_bounds w = memory_cap_bounds w' → heap_cap_base w = heap_cap_base w'.
Proof. rewrite /heap_cap_base !memory_cap_base_bounds. by intros ->. Qed.

Lemma heap_authority_base_bounds_eq `{HeapRegion} (w w' : Word) :
  memory_cap_bounds w = memory_cap_bounds w' →
  heap_authority_base w = heap_authority_base w'.
Proof.
  intros Hb. destruct (heap_authority_base w) as [b|] eqn:Hw;
    destruct (heap_authority_base w') as [b'|] eqn:Hw'; try done.
  - apply heap_authority_base_memory_cap_bounds in Hw as (e & He & ?).
    apply heap_authority_base_memory_cap_bounds in Hw' as (e' & He' & ?). congruence.
  - apply heap_authority_base_memory_cap_bounds in Hw as (e & He & ? & ?).
    assert (heap_authority_base w' = Some b) as Hc; last congruence.
    apply heap_authority_base_memory_cap_bounds. exists e. rewrite -Hb. done.
  - apply heap_authority_base_memory_cap_bounds in Hw' as (e & He & ? & ?).
    assert (heap_authority_base w = Some b') as Hc; last congruence.
    apply heap_authority_base_memory_cap_bounds. exists e. rewrite Hb. done.
Qed.

Lemma heap_authority_base_None_bounds `{HeapRegion} (w : Word) :
  memory_cap_bounds w = None → heap_authority_base w = None.
Proof.
  intros Hb. destruct (heap_authority_base w) eqn:Hw; last done.
  apply heap_authority_base_memory_cap_bounds in Hw as (? & ? & _). congruence.
Qed.

Lemma memory_cap_bounds_clear_tag w : memory_cap_bounds (clear_tag w) = memory_cap_bounds w.
Proof. by destruct w as [| [] | | ? [] ]. Qed.

Lemma memory_cap_bounds_load_word p w :
  memory_cap_bounds (load_word p w) = memory_cap_bounds w.
Proof.
  rewrite /load_word. destruct w as [| [] | | ? [] ]; repeat case_match; done.
Qed.

Lemma memory_cap_bounds_store_word p w :
  memory_cap_bounds (store_word p w) = memory_cap_bounds w.
Proof. rewrite /store_word. case_match; auto using memory_cap_bounds_clear_tag. Qed.

Lemma memory_cap_bounds_updatePcPerm w :
  memory_cap_bounds (updatePcPerm w) = memory_cap_bounds w.
Proof. by destruct w as [| [] | | ? [] ]. Qed.

Lemma get_tag_store_word p w : get_tag (store_word p w) = true → get_tag w = true.
Proof.
  rewrite /store_word. case_match; first done. by rewrite get_tag_clear_tag.
Qed.

Lemma load_word_clear_tag p w : load_word p (clear_tag w) = clear_tag (load_word p w).
Proof. rewrite /load_word. destruct w as [| [] | | ? [] ]; repeat case_match; simplify_eq; done. Qed.

Lemma decodeInstrW_clear_tag `{MachineParameters} w :
  decodeInstrW (clear_tag w) = decodeInstrW w.
Proof. by destruct w as [| [] | | ? [] ]. Qed.

Lemma heap_cap_base_clear_tag `{HeapRegion} w : heap_cap_base (clear_tag w) = heap_cap_base w.
Proof. apply heap_cap_base_bounds_eq, memory_cap_bounds_clear_tag. Qed.

Lemma heap_cap_base_load_word `{HeapRegion} p w :
  heap_cap_base (load_word p w) = heap_cap_base w.
Proof. apply heap_cap_base_bounds_eq, memory_cap_bounds_load_word. Qed.

Lemma is_heap_cap_load_word `{HeapRegion} p w : is_heap_cap (load_word p w) = is_heap_cap w.
Proof. by rewrite /is_heap_cap heap_cap_base_load_word. Qed.

Lemma memory_cap_bounds_heap_cap_base `{HeapRegion} w b e :
  memory_cap_bounds w = Some (b, e) → is_heap_address b = true → heap_cap_base w = Some b.
Proof.
  rewrite /heap_cap_base memory_cap_base_bounds. intros -> Hb. by rewrite /= Hb.
Qed.

Lemma heap_authority_base_bounds `{HeapRegion} w b :
  heap_authority_base w = Some b → ∃ e, memory_cap_bounds w = Some (b, e) ∧ (b < e)%a.
Proof. intros Hb. apply heap_authority_base_memory_cap_bounds in Hb as (e & ? & ? & _). eauto. Qed.

Lemma executable_word_bounds w :
  executable_word w = true → is_Some (memory_cap_bounds w).
Proof. destruct w as [| [] | | ? [] ]; cbn; by eauto. Qed.

Lemma executable_word_load_word p w : executable_word (load_word p w) = executable_word w.
Proof.
  rewrite /load_word.
  destruct w as [| [? [] | ] | | ? [? [] | ] ]; repeat case_match; simplify_eq; done.
Qed.

Lemma executable_word_store_word p w : executable_word (store_word p w) = executable_word w.
Proof. rewrite /store_word. case_match; auto using executable_word_clear_tag. Qed.


(** A copy of a word whose tag is kept ([s = true]) or cleared ([s = false]):
    a physical register word is such a copy of its logical word. *)
Definition and_tag_sealable (s : bool) (sb : Sealable) : Sealable :=
  match sb with
  | SCap t p g b e a => SCap (s && t) p g b e a
  | SSealRange t p g b e a => SSealRange (s && t) p g b e a
  end.

Definition and_tag (s : bool) (w : Word) : Word :=
  match w with
  | WInt z => WInt z
  | WSealable sb => WSealable (and_tag_sealable s sb)
  | WSentry k t p g b e a => WSentry k (s && t) p g b e a
  | WSealed o sb => WSealed o (and_tag_sealable s sb)
  end.

Lemma and_tag_true w : and_tag true w = w.
Proof. by destruct w as [| [] | | ? [] ]. Qed.

Lemma and_tag_false w : and_tag false w = clear_tag w.
Proof. by destruct w as [| [] | | ? [] ]. Qed.

Lemma and_tag_if s w : and_tag s w = if s then w else clear_tag w.
Proof. destruct s; [apply and_tag_true | apply and_tag_false]. Qed.

Lemma and_tag_cases w w' : w' = w ∨ w' = clear_tag w → ∃ s, w' = and_tag s w.
Proof.
  intros [-> | ->]; [exists true | exists false];
    by rewrite ?and_tag_true ?and_tag_false.
Qed.

Lemma and_tag_sealable_true sb : and_tag_sealable true sb = sb.
Proof. by destruct sb. Qed.

Lemma and_tag_sealable_false sb : and_tag_sealable false sb = clear_tag_sealable sb.
Proof. by destruct sb. Qed.

Lemma get_tag_and_tag s w : get_tag (and_tag s w) = s && get_tag w.
Proof. by destruct s, w as [| [] | | ? [] ]. Qed.

Lemma memory_cap_bounds_and_tag s w : memory_cap_bounds (and_tag s w) = memory_cap_bounds w.
Proof. by destruct w as [| [] | | ? [] ]. Qed.

Lemma heap_cap_base_and_tag `{HeapRegion} s w : heap_cap_base (and_tag s w) = heap_cap_base w.
Proof. apply heap_cap_base_bounds_eq, memory_cap_bounds_and_tag. Qed.

Lemma clear_tag_and_tag s w : clear_tag (and_tag s w) = clear_tag w.
Proof. destruct s; by rewrite ?and_tag_true ?and_tag_false ?clear_tag_idempotent. Qed.

(** The field reads ignore the tag. *)
Lemma get_a_and_tag s w : get_a (and_tag s w) = get_a w.
Proof. rewrite and_tag_if. destruct s; auto using get_a_clear_tag. Qed.
Lemma get_b_and_tag s w : get_b (and_tag s w) = get_b w.
Proof. rewrite and_tag_if. destruct s; auto using get_b_clear_tag. Qed.
Lemma get_e_and_tag s w : get_e (and_tag s w) = get_e w.
Proof. rewrite and_tag_if. destruct s; auto using get_e_clear_tag. Qed.
Lemma get_p_and_tag s w : get_p (and_tag s w) = get_p w.
Proof. rewrite and_tag_if. destruct s; auto using get_p_clear_tag. Qed.
Lemma get_l_and_tag s w : get_l (and_tag s w) = get_l w.
Proof. rewrite and_tag_if. destruct s; auto using get_l_clear_tag. Qed.
Lemma nonZero_and_tag s w : nonZero (and_tag s w) = nonZero w.
Proof. by rewrite /nonZero get_a_and_tag. Qed.

Lemma and_tag_untagged s w : get_tag w = false → and_tag s w = w.
Proof. intros Ht. rewrite and_tag_if. destruct s; auto using clear_tag_untagged. Qed.

Lemma store_word_clear_tag p w : store_word p (clear_tag w) = clear_tag (store_word p w).
Proof.
  rewrite /store_word.
  destruct (canStore p (clear_tag w)), (canStore p w); by rewrite ?clear_tag_idempotent.
Qed.

Lemma store_word_and_tag p s w : store_word p (and_tag s w) = and_tag s (store_word p w).
Proof. rewrite !and_tag_if. destruct s; auto using store_word_clear_tag. Qed.

Lemma load_word_and_tag p s w : load_word p (and_tag s w) = and_tag s (load_word p w).
Proof. rewrite !and_tag_if. destruct s; auto using load_word_clear_tag. Qed.

Lemma updatePcPerm_clear_tag w : updatePcPerm (clear_tag w) = clear_tag (updatePcPerm w).
Proof. by destruct w as [| [] | | ? [] ]. Qed.

Lemma updatePcPerm_and_tag s w : updatePcPerm (and_tag s w) = and_tag s (updatePcPerm w).
Proof. rewrite !and_tag_if. destruct s; auto using updatePcPerm_clear_tag. Qed.

Lemma jalr_target_ok_and_tag rdst rsrc s w :
  jalr_target_ok rdst rsrc (and_tag s w) = s && jalr_target_ok rdst rsrc w.
Proof. destruct s; [by rewrite and_tag_true | by rewrite and_tag_false jalr_target_ok_clear_tag]. Qed.

Lemma jalr_target_mie_and_tag s w : jalr_target_mie (and_tag s w) = jalr_target_mie w.
Proof. by destruct s, w as [| [] | | ? [] ]. Qed.

Lemma decodeInstrW_and_tag `{MachineParameters} s w :
  decodeInstrW (and_tag s w) = decodeInstrW w.
Proof. by destruct w as [| [] | | ? [] ]. Qed.

(** ** Registry entries *)

Notation RegEntry := (Addr * Addr * gname * AllocLifecycle)%type.

Definition re_b (x : RegEntry) : Addr := x.1.1.1.
Definition re_e (x : RegEntry) : Addr := x.1.1.2.
Definition re_status (x : RegEntry) : AllocLifecycle := x.2.
Definition re_covers (x : RegEntry) (a : Addr) : Prop := (a ∈ₐ [re_b x, re_e x)).
#[global] Arguments re_b /.
#[global] Arguments re_e /.
#[global] Arguments re_status /.

Section erasure.
  Context `{MP : MachineParameters}.
  Implicit Types (R : RegState) (C : gmap Addr AddrClaim) (v : LWord) (w pw : Word).

  (** Provenance: every tagged, non-empty capability with an identifier lies
      in the range of that identifier, which is registered. *)
  Definition lword_prov R v : Prop :=
    ∀ ι b e, get_tag v.(lw) = true → memory_cap_bounds v.(lw) = Some (b, e) → (b < e)%a →
      v.(lprov) = Some ι →
      ∃ x, R !! ι = Some x ∧ (re_b x <= b)%a ∧ (e <= re_e x)%a.

  (** A word with authority has a registered identifier, or a heap-root
      base. *)
  Definition reg_authority R C v : Prop :=
    ∀ b, get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b →
      match v.(lprov) with
      | Some ι => is_Some (R !! ι)
      | None => C !! b = Some HeapRoot
      end.

  (** Heap capabilities are never executable: a tagged executable word has no
      identifier, and its base and its closed bounds avoid the heap. *)
  Definition lword_exec v : Prop :=
    get_tag v.(lw) = true → executable_word v.(lw) = true →
    v.(lprov) = None ∧
    ∀ b e, memory_cap_bounds v.(lw) = Some (b, e) →
      is_heap_address b = false ∧ ∀ y, (b <= y)%a ∧ (y <= e)%a → is_heap_address y = false.

  Definition reg_word_ok R C v : Prop :=
    lword_prov R v ∧ reg_authority R C v ∧ lword_exec v.

  (** An identifier that is registered and no longer live. *)
  Definition stale_id R v : Prop :=
    ∃ ι x, v.(lprov) = Some ι ∧ R !! ι = Some x ∧ re_status x ≠ ALive.

  (** A memory capability (possibly a sentry or sealed) whose identifier is
      no longer live. *)
  Definition stale_cap R v : Prop :=
    stale_id R v ∧ is_Some (memory_cap_bounds v.(lw)).

  (** The words whose physical copy may be untagged: memory capabilities
      whose identifier is no longer live, and heap-based words without
      authority, which the CLoad filter strips by their base. *)
  Definition reg_strip_ok R v : Prop :=
    stale_cap R v ∨ (¬ has_authority v.(lw) ∧ is_Some (heap_cap_base v.(lw))).

  Definition quar_or_dead (s : AllocLifecycle) : Prop := s = AQuar ∨ s = ADead.

  (** The register clause, for a logical word [v] and its physical copy
      [w]: the copy is exact, or untagged when the word may be stripped; it
      is untagged when the word has authority and its identifier is
      quarantined or dead. *)
  Definition reg_phys R v w : Prop :=
    (w = v.(lw) ∨ (w = clear_tag v.(lw) ∧ reg_strip_ok R v)) ∧
    (∀ ι x, has_authority v.(lw) → v.(lprov) = Some ι → R !! ι = Some x →
       quar_or_dead (re_status x) → w = clear_tag v.(lw)).

  (** Every register of [regs] has a physical copy in [r]. *)
  Definition lregs_phys R (regs : LReg) (r : Reg) : Prop :=
    ∀ x v, regs !! x = Some v → ∃ w, r !! x = Some w ∧ reg_phys R v w.

  (** Every system register of [sregs] has a physical copy in [sr]. *)
  Definition lsregs_phys R (sregs : LSReg) (sr : SReg) : Prop :=
    ∀ x v, sregs !! x = Some v → ∃ w, sr !! x = Some w ∧ reg_phys R v w.

  (** The memory clause, for a logical word [v] and its physical copy [pw]. *)
  Definition mem_authority R C v pw : Prop :=
    ∀ b, get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b →
      match v.(lprov) with
      | Some ι => ∃ x, R !! ι = Some x ∧
                  (re_status x = ALive → pw = v.(lw)) ∧
                  (re_status x = ADead → pw = clear_tag v.(lw))
      | None => pw = v.(lw) ∧ C !! b = Some HeapRoot
      end.

  Definition mem_word_ok R C v pw : Prop :=
    lword_prov R v ∧
    (pw = v.(lw) ∨ pw = clear_tag v.(lw)) ∧
    (heap_cap_base v.(lw) = None → pw = v.(lw) ∨ stale_cap R v) ∧
    mem_authority R C v pw ∧
    lword_exec v.

  (** Registry and claims, whatever words exist. *)
  Record registry_ok R C (shadow : ShadowTbl) : Prop := {
    reg_ok_heap ι x a : R !! ι = Some x → re_covers x a → is_heap_address a = true;
    reg_ok_live ι x a : R !! ι = Some x → re_status x = ALive → re_covers x a →
                        shadow !! a = Some ShadowLive;
    reg_ok_quar ι x a : R !! ι = Some x → re_status x = AQuar → re_covers x a →
                        shadow !! a = Some ShadowQuarantined;
    reg_ok_claims_dom a : is_Some (C !! a) ↔ is_heap_address a = true;
    reg_ok_claimed a ι : C !! a = Some (Claimed ι) ↔
                         ∃ x, R !! ι = Some x ∧ re_covers x a ∧ re_status x ≠ ADead;
    reg_ok_root a : C !! a = Some HeapRoot → shadow !! a = Some ShadowLive;
    reg_ok_shadow a : is_heap_address a = true → is_Some (shadow !! a);
  }.

  (** The physical registers, system registers and PC are copies of the
      logical ones by the register clause. The system registers other than
      MTDC, which legalise the words written to them, hold no word with
      authority and identifier, and a tagged MTCC or MEPCC is an unsealed
      executable capability. Memory covers the heap. *)
  Record erasure R C (σ : ExecConf) (lpc : LWord) (lreg : LReg) (lsreg : LSReg)
      (lmem : LMem) : Prop := {
    er_registry : registry_ok R C (shadowtbl σ);
    er_regs : dom (reg σ) = dom lreg ∧ lregs_phys R lreg (reg σ);
    er_cnull v : lreg !! cnull = Some v → v = lnull;
    er_reg_words r v : lreg !! r = Some v → reg_word_ok R C v;
    er_sregs : lsregs_phys R lsreg (sreg σ);
    er_sreg_words sr v : lsreg !! sr = Some v → reg_word_ok R C v;
    er_sreg_legal_id sr v : sr ≠ mtdc → lsreg !! sr = Some v →
                            has_authority v.(lw) → v.(lprov) = None;
    er_sreg_pc_ok sr v : is_pc_sreg sr = true → lsreg !! sr = Some v → pc_ok v.(lw);
    er_mem_dom : dom lmem = dom (mem σ);
    er_mem_words a v pw : lmem !! a = Some v → mem σ !! a = Some pw → mem_word_ok R C v pw;
    er_mmio : mem_avoids_mmio (mem σ);
    er_pc : reg_phys R lpc (pcc σ);
    er_pc_word : reg_word_ok R C lpc;
    er_pc_ok : pc_ok lpc.(lw);
    er_heap_mapped : heap_mapped (mem σ);
  }.

  (** *** Words *)

  Lemma lword_prov_untagged R v : get_tag v.(lw) = false → lword_prov R v.
  Proof. intros Ht ι b e Ht'. congruence. Qed.

  Lemma lword_prov_no_bounds R v : memory_cap_bounds v.(lw) = None → lword_prov R v.
  Proof. intros Hb ι b e _ Hb'. congruence. Qed.

  Lemma lword_prov_no_id R v : v.(lprov) = None → lword_prov R v.
  Proof. intros Hp ι b e _ _ _ Hp'. congruence. Qed.

  Lemma lword_exec_untagged v : get_tag v.(lw) = false → lword_exec v.
  Proof. intros Ht Ht'. congruence. Qed.

  Lemma lword_exec_not_executable v : executable_word v.(lw) = false → lword_exec v.
  Proof. intros Hx _ Hx'. congruence. Qed.

  Lemma reg_word_ok_int R C z π : reg_word_ok R C (MkLWord (WInt z) π).
  Proof.
    split_and!; [by apply lword_prov_untagged | intros b Ht; done | by apply lword_exec_untagged].
  Qed.

  Lemma reg_word_ok_lnull R C : reg_word_ok R C lnull.
  Proof. apply reg_word_ok_int. Qed.

  Lemma reg_word_ok_untagged R C v : get_tag v.(lw) = false → reg_word_ok R C v.
  Proof.
    intros Ht. split_and!;
      [by apply lword_prov_untagged | intros b Ht'; congruence | by apply lword_exec_untagged].
  Qed.

  (** A word derived by an operation that keeps the bounds, does not add a
      tag and keeps the identifier. *)
  Lemma lword_prov_derive R v w' :
    (memory_cap_bounds w' = memory_cap_bounds v.(lw) ∨ memory_cap_bounds w' = None) →
    (get_tag w' = true → get_tag v.(lw) = true) →
    lword_prov R v → lword_prov R (MkLWord w' v.(lprov)).
  Proof.
    intros Hb Ht Hprov ι b e Ht' Hb' Hlt Hι; cbn in *.
    destruct Hb as [Hb|Hb]; last congruence.
    eapply Hprov; eauto. congruence.
  Qed.

  (** The same derivation, which moreover does not add the execute
      permission. *)
  Lemma lword_exec_derive v w' :
    (memory_cap_bounds w' = memory_cap_bounds v.(lw) ∨ memory_cap_bounds w' = None) →
    (get_tag w' = true → get_tag v.(lw) = true) →
    (get_tag w' = true → executable_word w' = true → executable_word v.(lw) = true) →
    lword_exec v → lword_exec (MkLWord w' v.(lprov)).
  Proof.
    intros Hb Ht Hx Hexec Ht' Hx'; cbn in *.
    destruct (Hexec (Ht Ht') (Hx Ht' Hx')) as [Hp Havoid]. split; first done.
    intros b e Hbe. destruct Hb as [Hb|Hb]; last congruence.
    apply Havoid. congruence.
  Qed.

  Lemma reg_word_ok_derive R C v w' :
    (memory_cap_bounds w' = memory_cap_bounds v.(lw) ∨ memory_cap_bounds w' = None) →
    (get_tag w' = true → get_tag v.(lw) = true) →
    (get_tag w' = true → executable_word w' = true → executable_word v.(lw) = true) →
    reg_word_ok R C v → reg_word_ok R C (MkLWord w' v.(lprov)).
  Proof.
    intros Hb Ht Hx (Hprov & Hauth & Hexec). split_and!.
    - by apply lword_prov_derive.
    - intros b Ht' Hab; cbn in *.
      destruct Hb as [Hb|Hb].
      + apply (Hauth b); first auto. by rewrite -(heap_authority_base_bounds_eq _ _ Hb).
      + by rewrite heap_authority_base_None_bounds in Hab.
    - by apply lword_exec_derive.
  Qed.

  Lemma reg_word_ok_lift R C f v :
    (∀ w, memory_cap_bounds (f w) = memory_cap_bounds w ∨ memory_cap_bounds (f w) = None) →
    (∀ w, get_tag (f w) = true → get_tag w = true) →
    (∀ w, get_tag (f w) = true → executable_word (f w) = true → executable_word w = true) →
    reg_word_ok R C v → reg_word_ok R C (lift_word f v).
  Proof. intros Hb Ht Hx. apply reg_word_ok_derive; auto. Qed.

  Lemma reg_word_ok_lclear_tag R C v : reg_word_ok R C (lclear_tag v).
  Proof. apply reg_word_ok_untagged. apply get_tag_clear_tag. Qed.

  Lemma reg_word_ok_lload_word R C p v : reg_word_ok R C v → reg_word_ok R C (lload_word p v).
  Proof.
    apply reg_word_ok_lift; intros w.
    - left. apply memory_cap_bounds_load_word.
    - by rewrite get_tag_load_word.
    - by rewrite executable_word_load_word.
  Qed.

  Lemma reg_word_ok_lupdatePcPerm R C v :
    reg_word_ok R C v → reg_word_ok R C (lupdatePcPerm v).
  Proof.
    apply reg_word_ok_lift; intros w.
    - left. apply memory_cap_bounds_updatePcPerm.
    - by rewrite get_tag_updatePcPerm.
    - by rewrite executable_word_updatePcPerm.
  Qed.


  Lemma reg_word_ok_lstore_word R C p v :
    reg_word_ok R C v → reg_word_ok R C (lstore_word p v).
  Proof.
    apply reg_word_ok_lift; intros w.
    - left. apply memory_cap_bounds_store_word.
    - apply get_tag_store_word.
    - by rewrite executable_word_store_word.
  Qed.

  (** *** The register clause *)

  Lemma reg_phys_cases R v w : reg_phys R v w → w = v.(lw) ∨ w = clear_tag v.(lw).
  Proof. intros [[-> | [-> _] ] _]; auto. Qed.

  Lemma reg_phys_and_tag R v w : reg_phys R v w → ∃ s, w = and_tag s v.(lw).
  Proof. intros Hw. by apply and_tag_cases, (reg_phys_cases R). Qed.

  Lemma has_authority_tag w : has_authority w → get_tag w = true.
  Proof. by intros [? _]. Qed.

  Lemma has_authority_clear_tag w : ¬ has_authority (clear_tag w).
  Proof. intros [Ht _]. by rewrite get_tag_clear_tag in Ht. Qed.

  (** An exact copy, when no quarantined or dead identifier forces the tag
      off. *)
  Lemma reg_phys_exact R v :
    (∀ ι x, has_authority v.(lw) → v.(lprov) = Some ι → R !! ι = Some x →
       ¬ quar_or_dead (re_status x)) →
    reg_phys R v v.(lw).
  Proof.
    intros Hnq. split; first by left.
    intros ι x Ha Hι Hx Hq. exfalso. by eapply Hnq.
  Qed.

  Lemma reg_phys_no_id R v : v.(lprov) = None → reg_phys R v v.(lw).
  Proof. intros Hp. apply reg_phys_exact. intros ι x _ Hι. congruence. Qed.

  Lemma reg_phys_untagged R v : get_tag v.(lw) = false → reg_phys R v v.(lw).
  Proof.
    intros Ht. apply reg_phys_exact. intros ι x Ha. by rewrite (has_authority_tag _ Ha) in Ht.
  Qed.

  Lemma reg_phys_lword_of_word R w : reg_phys R (lword_of_word w) w.
  Proof. by apply reg_phys_no_id. Qed.

  Lemma reg_phys_int R z π : reg_phys R (MkLWord (WInt z) π) (WInt z).
  Proof. by apply reg_phys_untagged. Qed.

  Lemma reg_phys_lnull R : reg_phys R lnull (WInt 0).
  Proof. apply reg_phys_int. Qed.

  (** A physical word with tag 1 is exact. *)
  Lemma reg_phys_tagged R v w : reg_phys R v w → get_tag w = true → w = v.(lw).
  Proof.
    intros Hw Ht. destruct (reg_phys_cases _ _ _ Hw) as [-> | ->]; first done.
    by rewrite get_tag_clear_tag in Ht.
  Qed.

  (** A word without bounds (an integer or a sealing range) is exact. *)
  Lemma reg_phys_no_bounds R v w : memory_cap_bounds v.(lw) = None → reg_phys R v w → w = v.(lw).
  Proof.
    intros Hb [[-> | [-> [[_ Hbs] | [_ [b Hh] ] ] ] ] _]; first done.
    - rewrite Hb in Hbs. by destruct Hbs.
    - by rewrite /heap_cap_base memory_cap_base_bounds Hb in Hh.
  Qed.

  (** A copy is exact when the identifier is live or absent and the word has
      authority or no heap base. *)
  Lemma reg_phys_exact_cond R v w :
    reg_phys R v w →
    ¬ stale_id R v →
    (get_tag v.(lw) = true → has_authority v.(lw) ∨ heap_cap_base v.(lw) = None) →
    w = v.(lw).
  Proof.
    intros [[-> | [-> [Hst | [Hna [b Hb] ] ] ] ] _] Hns Hcond; first done.
    - exfalso. by destruct Hst.
    - destruct (get_tag v.(lw)) eqn:Ht; last by rewrite clear_tag_untagged.
      destruct (Hcond eq_refl) as [Ha | Hn]; [done | congruence].
  Qed.

  (** A word derived by an operation that keeps the bounds, does not add a
      tag and keeps the identifier: its physical copy is derived the same
      way. *)
  Lemma reg_phys_derive R v s w' :
    reg_phys R v (and_tag s v.(lw)) →
    memory_cap_bounds w' = memory_cap_bounds v.(lw) →
    (get_tag w' = true → get_tag v.(lw) = true) →
    reg_phys R (MkLWord w' v.(lprov)) (and_tag s w').
  Proof.
    intros [Hrel Hq] Hb Ht; cbn.
    assert (has_authority w' → has_authority v.(lw)) as Hauth.
    { intros [Ht' [b Hab] ]. split; first by apply Ht.
      exists b. by rewrite -(heap_authority_base_bounds_eq _ _ Hb). }
    destruct s.
    - rewrite !and_tag_true in Hrel Hq |- *. split; first by left.
      intros ι x Ha Hι Hx Hqd. exfalso.
      pose proof (Hauth Ha) as Hav. pose proof (Hq ι x Hav Hι Hx Hqd) as Heq.
      apply has_authority_tag in Hav. rewrite Heq get_tag_clear_tag in Hav. done.
    - rewrite !and_tag_false in Hrel Hq |- *. split; last done.
      destruct Hrel as [Heq | [_ Hstrip] ].
      + left. assert (get_tag v.(lw) = false) as Hf.
        { destruct (get_tag v.(lw)) eqn:Hv; last done.
          rewrite -Heq get_tag_clear_tag in Hv. done. }
        assert (get_tag w' = false) as Hw'.
        { apply not_true_is_false. intros Hw'. by rewrite (Ht Hw') in Hf. }
        by rewrite clear_tag_untagged.
      + right. split; first done. destruct Hstrip as [[Hst Hbs] | [Hna Hh] ].
        { left. split; first done. by rewrite Hb. }
        right. split; first naive_solver.
        by rewrite (heap_cap_base_bounds_eq _ _ Hb).
  Qed.

  Lemma reg_phys_lift R f v s :
    (∀ w, memory_cap_bounds (f w) = memory_cap_bounds w) →
    (∀ w, get_tag (f w) = true → get_tag w = true) →
    (∀ w, f (and_tag s w) = and_tag s (f w)) →
    reg_phys R v (and_tag s v.(lw)) → reg_phys R (lift_word f v) (f (and_tag s v.(lw))).
  Proof.
    intros Hb Ht Hc Hv. rewrite Hc /lift_word. apply reg_phys_derive; auto.
  Qed.

  Lemma reg_phys_lclear_tag R v w : reg_phys R v w → reg_phys R (lclear_tag v) (clear_tag w).
  Proof.
    intros Hw. destruct (reg_phys_cases _ _ _ Hw) as [-> | ->];
      rewrite ?clear_tag_idempotent; apply reg_phys_untagged, get_tag_clear_tag.
  Qed.

  Lemma reg_phys_lupdatePcPerm R v w :
    reg_phys R v w → reg_phys R (lupdatePcPerm v) (updatePcPerm w).
  Proof.
    intros Hw. destruct (reg_phys_and_tag _ _ _ Hw) as [s ->].
    apply reg_phys_lift; auto; intros w'.
    - apply memory_cap_bounds_updatePcPerm.
    - by rewrite get_tag_updatePcPerm.
    - apply updatePcPerm_and_tag.
  Qed.

  Lemma reg_phys_lstore_word R p v w :
    reg_phys R v w → reg_phys R (lstore_word p v) (store_word p w).
  Proof.
    intros Hw. destruct (reg_phys_and_tag _ _ _ Hw) as [s ->].
    apply reg_phys_lift; auto; intros w'.
    - apply memory_cap_bounds_store_word.
    - apply get_tag_store_word.
    - apply store_word_and_tag.
  Qed.

  Lemma reg_phys_lload_word R p v w :
    reg_phys R v w → reg_phys R (lload_word p v) (load_word p w).
  Proof.
    intros Hw. destruct (reg_phys_and_tag _ _ _ Hw) as [s ->].
    apply reg_phys_lift; auto; intros w'.
    - apply memory_cap_bounds_load_word.
    - by rewrite get_tag_load_word.
    - apply load_word_and_tag.
  Qed.

  (** A register word stored to memory satisfies the memory clause. *)
  Lemma reg_phys_mem_word_ok R C v w :
    reg_word_ok R C v → reg_phys R v w → mem_word_ok R C v w.
  Proof.
    intros (Hprov & Hauth & Hexec) [Hrel Hq].
    split; first done. split.
    { destruct Hrel as [-> | [-> _] ]; auto. }
    split.
    { intros Hn. destruct Hrel as [-> | [-> [Hst | [_ Hs] ] ] ]; auto.
      rewrite Hn in Hs. by destruct Hs. }
    split; last done.
    intros b Ht Hab. specialize (Hauth b Ht Hab).
    assert (has_authority v.(lw)) as Ha by (split; eauto).
    destruct (lprov v) as [ι|] eqn:Hι.
    - destruct Hauth as [x Hx]. exists x. split; first done. split.
      + intros Hl. destruct Hrel as [-> | [-> [[(ι' & x' & Hι' & Hx' & Hs) _] | [Hna _] ] ] ]; first done.
        * simplify_eq; congruence.
        * done.
      + intros Hd. eapply Hq; eauto. by right.
    - split; last done.
      destruct Hrel as [-> | [-> [[(ι' & x' & Hι' & _) _] | [Hna _] ] ] ]; [done | congruence | by exfalso].
  Qed.

  (** A CLoad: the physical result of the CLoad filter on the physical copy
      [pw] of a memory word [v]. *)
  Definition load_filter (shadow : ShadowTbl) (p : Perm) (pw : Word) : option Word :=
    match heap_cap_base pw with
    | Some base =>
        match shadow !! base with
        | Some ShadowLive => Some (load_word p pw)
        | Some ShadowQuarantined => Some (clear_tag (load_word p pw))
        | None => None
        end
    | None => Some (load_word p pw)
    end.

  Lemma load_filter_cases shadow p pw pl :
    load_filter shadow p pw = Some pl →
    pl = load_word p pw ∨ (is_heap_cap pw = true ∧ pl = clear_tag (load_word p pw)).
  Proof.
    rewrite /load_filter /is_heap_cap.
    destruct (heap_cap_base pw); last (intros; simplify_eq; by left).
    destruct (shadow !! _) as [[]|]; intros; simplify_eq; auto.
  Qed.

  Lemma mem_word_ok_load_word R C v pw p pl shadow :
    mem_word_ok R C v pw →
    load_filter shadow p pw = Some pl →
    pl = load_word p v.(lw) ∨ pl = clear_tag (load_word p v.(lw)).
  Proof.
    intros (_ & Hpw & _) Hpl.
    apply load_filter_cases in Hpl as [-> | (_ & ->)];
      destruct Hpw as [-> | ->]; rewrite ?load_word_clear_tag ?clear_tag_idempotent; auto.
  Qed.

  Lemma mem_word_ok_reg_word_ok R C v pw : mem_word_ok R C v pw → reg_word_ok R C v.
  Proof.
    intros (Hprov & _ & _ & Hauth & Hexec). split_and!; [done | | done].
    intros b Ht Hab. specialize (Hauth b Ht Hab).
    destruct (lprov v) as [ι|]; last by destruct Hauth.
    destruct Hauth as (x & Hx & _). by exists x.
  Qed.

  Lemma mem_word_ok_load_reg_word R C v pw p pl shadow :
    mem_word_ok R C v pw →
    load_filter shadow p pw = Some pl →
    reg_word_ok R C (MkLWord pl v.(lprov)).
  Proof.
    intros Hok Hpl. pose proof (mem_word_ok_load_word _ _ _ _ _ _ _ Hok Hpl) as Hcases.
    apply reg_word_ok_derive; last by eapply mem_word_ok_reg_word_ok.
    - left. destruct Hcases as [-> | ->];
        rewrite ?memory_cap_bounds_clear_tag memory_cap_bounds_load_word //.
    - destruct Hcases as [-> | ->]; rewrite ?get_tag_clear_tag ?get_tag_load_word //.
    - destruct Hcases as [-> | ->];
        rewrite ?get_tag_clear_tag ?executable_word_clear_tag ?executable_word_load_word //.
  Qed.

  Lemma has_authority_load_word p w : has_authority (load_word p w) ↔ has_authority w.
  Proof.
    rewrite /has_authority get_tag_load_word.
    by rewrite (heap_authority_base_bounds_eq _ _ (memory_cap_bounds_load_word p w)).
  Qed.

  (** The CLoad result is a copy of the loaded logical word by the register
      clause: the loaded word is exact, whatever the filter did. *)
  Lemma load_filter_reg_phys R C st v pw p pl :
    registry_ok R C st →
    mem_word_ok R C v pw →
    load_filter st p pw = Some pl →
    reg_phys R (lload_word p v) pl.
  Proof.
    intros Hreg Hok Hpl. destruct v as [w π].
    destruct Hok as (Hprov & Hrel & Hnh & Hauth & _); cbn in *.
    assert (heap_cap_base pw = heap_cap_base w) as Hhb.
    { apply heap_cap_base_bounds_eq.
      destruct Hrel as [-> | ->]; rewrite ?memory_cap_bounds_clear_tag //. }
    assert (stale_id R (lload_word p (MkLWord w π)) ↔ stale_id R (MkLWord w π)) as Hst by done.
    (* The facts of a word with authority: its base and identifier. *)
    assert (∀ b, has_authority w → heap_authority_base w = Some b →
      heap_cap_base w = Some b ∧
      match π with
      | Some ι => ∃ x, R !! ι = Some x ∧ re_covers x b ∧
                  (re_status x = ALive → pw = w) ∧ (re_status x = ADead → pw = clear_tag w)
      | None => pw = w ∧ C !! b = Some HeapRoot
      end) as Hauthb.
    { intros b [Ht _] Hab. split; first by apply heap_authority_base_heap_cap_base.
      specialize (Hauth b Ht Hab). destruct π as [ι|]; last done.
      destruct Hauth as (x & Hx & Hl & Hd).
      pose proof Hab as (e & Hbe & Hlt)%heap_authority_base_bounds.
      destruct (Hprov ι b e Ht Hbe Hlt eq_refl) as (x0 & Hx0 & ? & ?).
      rewrite Hx in Hx0. injection Hx0 as <-.
      exists x. split_and!; try done. rewrite /re_covers. solve_addr. }
    rewrite /load_filter Hhb in Hpl.
    destruct (heap_cap_base w) as [base|] eqn:Hbase.
    - destruct (st !! base) as [[]|] eqn:Hsb; simplify_eq.
      + (* Live *)
        split.
        * destruct Hrel as [-> | ->]; first by left.
          right. rewrite load_word_clear_tag. split; first done.
          destruct (decide (has_authority w)) as [Ha | Hna].
          -- destruct Ha as [Ht [b Hab] ]. destruct (Hauthb b (conj Ht (ex_intro _ b Hab)) Hab) as [Hb' Hc].
             destruct π as [ι|].
             ++ destruct Hc as (x & Hx & _ & Hl & _). left. split.
                ** exists ι, x. split_and!; try done.
                   intros Hs. specialize (Hl Hs). rewrite -Hl get_tag_clear_tag in Ht. done.
                ** rewrite /= memory_cap_bounds_load_word.
                   apply heap_authority_base_bounds in Hab as (? & -> & _). by eexists.
             ++ destruct Hc as [Heq _]. rewrite -Heq get_tag_clear_tag in Ht. done.
          -- right. rewrite /= has_authority_load_word heap_cap_base_load_word Hbase. eauto.
        * intros ι x Ha Hι Hx Hq; cbn in *. apply has_authority_load_word in Ha.
          pose proof Ha as [Ht [b Hab] ]. destruct (Hauthb b Ha Hab) as [Hb' Hc]. simplify_eq.
          destruct Hc as (x' & Hx' & Hcov & _ & Hd). simplify_eq.
          destruct Hq as [Hq | Hq].
          -- exfalso. rewrite (reg_ok_quar _ _ _ Hreg _ _ _ Hx Hq Hcov) in Hsb. done.
          -- rewrite (Hd Hq) load_word_clear_tag //.
      + (* Quarantined *)
        assert (clear_tag (load_word p pw) = clear_tag (load_word p w)) as ->.
        { destruct Hrel as [-> | ->]; by rewrite ?load_word_clear_tag ?clear_tag_idempotent. }
        split; last done. right. split; first done.
        destruct (decide (has_authority w)) as [Ha | Hna].
        * pose proof Ha as [Ht [b Hab] ]. destruct (Hauthb b Ha Hab) as [Hb' Hc]. simplify_eq.
          destruct π as [ι|].
          -- destruct Hc as (x & Hx & Hcov & _). left. split.
             ++ exists ι, x. split_and!; try done.
                intros Hs. rewrite (reg_ok_live _ _ _ Hreg _ _ _ Hx Hs Hcov) in Hsb. done.
             ++ rewrite /= memory_cap_bounds_load_word.
                   apply heap_authority_base_bounds in Hab as (? & -> & _). by eexists.
          -- destruct Hc as [_ Hroot]. rewrite (reg_ok_root _ _ _ Hreg _ Hroot) in Hsb. done.
        * right. rewrite /= has_authority_load_word heap_cap_base_load_word Hbase. eauto.
    - simplify_eq. split.
      + destruct (Hnh eq_refl) as [Heq | Hs].
        * subst pw. by left.
        * destruct Hrel as [-> | ->]; first by left.
          right. rewrite load_word_clear_tag. split; first done.
          left. destruct Hs as [Hs Hbs]. split; first done.
          by rewrite /= memory_cap_bounds_load_word.
      + intros ι x Ha. exfalso. apply has_authority_load_word in Ha as [_ [b Hab] ].
        apply heap_authority_base_heap_cap_base in Hab. cbn in Hab. congruence.
  Qed.

  (** *** Registers *)

  Lemma erasure_lookup_reg R C σ lpc lreg lsreg lmem r v :
    erasure R C σ lpc lreg lsreg lmem → lreg !! r = Some v →
    ∃ w, reg σ !! r = Some w ∧ reg_phys R v w.
  Proof. intros Her Hv. by apply (proj2 (er_regs _ _ _ _ _ _ _ Her)). Qed.

  Lemma erasure_regs_incl R C σ lpc lreg lsreg lmem regs :
    erasure R C σ lpc lreg lsreg lmem → regs ⊆ lreg → lregs_phys R regs (reg σ).
  Proof.
    intros Her Hincl x v Hv. eapply erasure_lookup_reg; first done. by eapply lookup_weaken.
  Qed.

  Lemma erasure_reg_word R C σ lpc lreg lsreg lmem r v :
    erasure R C σ lpc lreg lsreg lmem → lreg !! r = Some v → reg_word_ok R C v.
  Proof. intros Her. apply Her. Qed.

  Lemma erasure_llookup_reg_word R C σ lpc lreg lsreg lmem regs r v :
    erasure R C σ lpc lreg lsreg lmem → regs ⊆ lreg → regs !!ₗ r = Some v → reg_word_ok R C v.
  Proof.
    intros Her Hincl Hv. rewrite /llookup_reg in Hv.
    case_decide; simplify_eq; first apply reg_word_ok_lnull.
    eapply er_reg_words; first done. by eapply lookup_weaken.
  Qed.

  Lemma erasure_lword_of_argument_word R C σ lpc lreg lsreg lmem regs arg v :
    erasure R C σ lpc lreg lsreg lmem → regs ⊆ lreg → lword_of_argument regs arg = Some v →
    reg_word_ok R C v.
  Proof.
    intros Her Hincl Hv. destruct arg as [z|r]; cbn in Hv.
    - simplify_eq. apply reg_word_ok_int.
    - by eapply erasure_llookup_reg_word.
  Qed.

  (** Writes a register; a write to [cnull] changes nothing. *)
  Lemma erasure_linsert_reg R C pc r sr m st lpc lreg lsreg lmem x v w :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    reg_word_ok R C v →
    reg_phys R v w →
    erasure R C (pc, insert_reg x w r, sr, m, st) lpc (<[x := v]ₗ> lreg) lsreg lmem.
  Proof.
    intros Her Hok Hw.
    destruct (decide (x = cnull)) as [->|Hx].
    { by rewrite linsert_reg_cnull insert_reg_cnull. }
    rewrite linsert_reg_not_cnull // insert_reg_not_cnull //.
    destruct Her as [Hreg [Hrdom Hregs] Hcnull Hrw Hsregs Hsrw Hsrlid Hsrpc Hdom Hmw Hmmio
                     Hpc Hpcw Hpcok Hhmap].
    constructor; cbn in *; try done.
    - split.
      + rewrite !dom_insert_L. by rewrite Hrdom.
      + intros y v'. destruct (decide (x = y)) as [<-|Hne].
        * rewrite !lookup_insert_eq. intros [= <-]. by eexists.
        * rewrite !lookup_insert_ne //. apply Hregs.
    - intros v'. rewrite lookup_insert_ne //. apply Hcnull.
    - intros r' v'. destruct (decide (x = r')) as [<-|Hne].
      + rewrite lookup_insert_eq. by intros [= <-].
      + rewrite lookup_insert_ne //. apply Hrw.
  Qed.

  Lemma erasure_insert_reg R C pc r sr m st lpc lreg lsreg lmem x v w :
    x ≠ cnull →
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    reg_word_ok R C v →
    reg_phys R v w →
    erasure R C (pc, <[x := w]> r, sr, m, st) lpc (<[x := v]> lreg) lsreg lmem.
  Proof.
    intros Hx Her Hok Hw. pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ _ _ _ x v w Her Hok Hw) as H.
    by rewrite insert_reg_not_cnull // linsert_reg_not_cnull // in H.
  Qed.

  (** Writes a system register. *)
  Lemma erasure_insert_sreg R C pc r sr m st lpc lreg lsreg lmem x v w :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    reg_word_ok R C v →
    (x ≠ mtdc → has_authority v.(lw) → v.(lprov) = None) →
    (is_pc_sreg x = true → pc_ok v.(lw)) →
    reg_phys R v w →
    erasure R C (pc, r, <[x := w]> sr, m, st) lpc lreg (<[x := v]> lsreg) lmem.
  Proof.
    intros Her Hok Hπ Hxpc Hw.
    destruct Her as [Hreg Hregs Hcnull Hrw Hsregs Hsrw Hsrlid Hsrpc Hdom Hmw Hmmio
                     Hpc Hpcw Hpcok Hhmap].
    constructor; cbn in *; try done.
    - intros y v'. destruct (decide (x = y)) as [<-|Hne].
      + rewrite !lookup_insert_eq. intros [= <-]. by eexists.
      + rewrite !lookup_insert_ne //. apply Hsregs.
    - intros y v'. destruct (decide (x = y)) as [<-|Hne].
      + rewrite lookup_insert_eq. by intros [= <-].
      + rewrite lookup_insert_ne //. apply Hsrw.
    - intros y v' Hy. destruct (decide (x = y)) as [<-|Hne].
      + rewrite lookup_insert_eq. intros [= <-]. by apply Hπ.
      + rewrite lookup_insert_ne //. by apply Hsrlid.
    - intros y v' Hy. destruct (decide (x = y)) as [<-|Hne].
      + rewrite lookup_insert_eq. intros [= <-]. by apply Hxpc.
      + rewrite lookup_insert_ne //. by apply Hsrpc.
  Qed.

  Lemma erasure_lookup_sreg R C σ lpc lreg lsreg lmem x v :
    erasure R C σ lpc lreg lsreg lmem → lsreg !! x = Some v →
    ∃ w, sreg σ !! x = Some w ∧ reg_phys R v w.
  Proof. intros Her Hv. by apply (er_sregs _ _ _ _ _ _ _ Her). Qed.

  (** *** Legalisation of system-register writes *)

  Lemma reg_phys_llegalise R x v w :
    reg_phys R v w → reg_phys R (llegalise x v) (legalise x w).
  Proof.
    intros Hw. destruct (reg_phys_and_tag _ _ _ Hw) as [s ->].
    assert (∀ w', legalise_pc (and_tag s w') = and_tag s (legalise_pc w')) as Hcomm.
    { intros w'. destruct s; rewrite ?and_tag_true ?and_tag_false //.
      apply (legalise_clear_tag mtcc). }
    assert (∀ w', memory_cap_bounds (legalise_pc w') = memory_cap_bounds w') as Hb.
    { intros w'. rewrite /legalise_pc. case_match; by rewrite ?memory_cap_bounds_clear_tag. }
    assert (∀ w', get_tag (legalise_pc w') = true → get_tag w' = true) as Ht.
    { intros w'. rewrite /legalise_pc. case_match; by rewrite ?get_tag_clear_tag. }
    destruct x.
    all: try (by apply (reg_phys_lift R legalise_pc)).
    1: by rewrite llegalise_mtdc.
    (* The CSRs store the integer view, which ignores the tag. *)
    all: rewrite /llegalise /lift_word /=; destruct s;
      rewrite ?and_tag_true ?and_tag_false ?get_a_clear_tag; apply reg_phys_int.
  Qed.

  Lemma reg_word_ok_llegalise R C x v :
    reg_word_ok R C v → reg_word_ok R C (llegalise x v).
  Proof.
    intros Hok. destruct x.
    all: try (apply (reg_word_ok_lift R C legalise_pc); [| | |done]; intros w';
      rewrite /legalise_pc; case_match;
      rewrite ?memory_cap_bounds_clear_tag ?get_tag_clear_tag; by auto).
    1: by rewrite llegalise_mtdc.
    all: apply reg_word_ok_int.
  Qed.

  Lemma llegalise_pc_ok x v : is_pc_sreg x = true → pc_ok (llegalise x v).(lw).
  Proof. apply legalise_pc_sreg_pc_ok. Qed.

  (** A legalised word with authority, outside MTDC, has no identifier: the
      CSRs store an integer, and a tagged MTCC or MEPCC is executable. *)
  Lemma llegalise_no_id R C x v :
    reg_word_ok R C v → x ≠ mtdc → has_authority (llegalise x v).(lw) →
    (llegalise x v).(lprov) = None.
  Proof.
    intros Hok Hx Ha. pose proof (has_authority_tag _ Ha) as Ht.
    destruct (reg_word_ok_llegalise R C x v Hok) as (_ & _ & Hexec).
    apply Hexec; first done.
    destruct x; try done.
    all: try (by destruct (llegalise_pc_ok mtcc v eq_refl Ht)).
    all: try (by destruct (llegalise_pc_ok mepcc v eq_refl Ht)).
    all: exfalso; revert Ht; by rewrite /llegalise /lift_word /=.
  Qed.

  (** Writes the legalised value of [v] to a system register. *)
  Lemma erasure_write_sreg R C pc r sr m st lpc lreg lsreg lmem x v w :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    reg_word_ok R C v →
    reg_phys R v w →
    erasure R C (pc, r, <[x := legalise x w]> sr, m, st) lpc lreg
      (<[x := llegalise x v]> lsreg) lmem.
  Proof.
    intros Her Hok Hw. apply erasure_insert_sreg; first done.
    - by apply reg_word_ok_llegalise.
    - intros Hx Ha. by apply (llegalise_no_id R C x v).
    - apply llegalise_pc_ok.
    - by apply reg_phys_llegalise.
  Qed.

  (** Writes the PC. *)
  Lemma erasure_set_pc R C pc r sr m st lpc lreg lsreg lmem lpc' pc' :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    reg_word_ok R C lpc' →
    reg_phys R lpc' pc' →
    pc_ok lpc'.(lw) →
    erasure R C (pc', r, sr, m, st) lpc' lreg lsreg lmem.
  Proof.
    intros Her Hok Hw Hpcok'.
    destruct Her as [Hreg Hregs Hcnull Hrw Hsregs Hsrw Hsrlid Hsrpc Hdom Hmw Hmmio
                     Hpc Hpcw Hpcok Hhmap].
    by constructor.
  Qed.

  (** A tagged executable word is exact: it has no identifier and no heap
      base. *)
  Lemma reg_phys_executable R C v w :
    reg_word_ok R C v → reg_phys R v w →
    get_tag v.(lw) = true → executable_word v.(lw) = true → w = v.(lw).
  Proof.
    intros (_ & _ & Hexec) Hw Ht Hx.
    destruct (Hexec Ht Hx) as [Hπ Havoid].
    apply (reg_phys_exact_cond R v w Hw).
    - intros (ι & x & Hι & _). congruence.
    - intros _. right. destruct (executable_word_bounds _ Hx) as [[b e] Hbe].
      rewrite /heap_cap_base memory_cap_base_bounds Hbe /=. by rewrite (proj1 (Havoid b e Hbe)).
  Qed.

  (** A correct logical PC is exact: it is tagged and executable. *)
  Lemma reg_phys_correct_pc R C lpc pc :
    reg_word_ok R C lpc → reg_phys R lpc pc → isCorrectPC lpc.(lw) → pc = lpc.(lw).
  Proof.
    intros Hok Hw Hcorr. apply (reg_phys_executable R C); [done | done | |].
    - by apply isCorrectPC_tag.
    - inversion Hcorr; by cbn.
  Qed.

  (** By the tagged-PC invariant, the physical PC is the logical one: a
      tagged PC is executable, hence exact, and an untagged one is its own
      untagged copy. *)
  Lemma erasure_pc_exact R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem → pcc σ = lpc.(lw).
  Proof.
    intros Her.
    pose proof (er_pc _ _ _ _ _ _ _ Her) as Hw.
    destruct (get_tag lpc.(lw)) eqn:Ht.
    - destruct (er_pc_ok _ _ _ _ _ _ _ Her Ht) as [_ Hx].
      by apply (reg_phys_executable R C); first apply Her.
    - destruct (reg_phys_cases _ _ _ Hw) as [-> | ->]; first done.
      by rewrite clear_tag_untagged.
  Qed.

  Lemma erasure_pc_correct R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem → isCorrectPC lpc.(lw) → pcc σ = lpc.(lw).
  Proof. intros Her _. by apply (erasure_pc_exact R C _ _ lreg lsreg lmem). Qed.

  (** A correct logical PC has no identifier. *)
  Lemma erasure_pc_no_id R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem → isCorrectPC lpc.(lw) → lpc.(lprov) = None.
  Proof.
    intros Her Hcorr. destruct (er_pc_word _ _ _ _ _ _ _ Her) as (_ & _ & Hexec).
    apply Hexec; first by apply isCorrectPC_tag.
    inversion Hcorr; by cbn.
  Qed.

  (** A tagged logical PC has no identifier: it is executable. *)
  Lemma erasure_pc_tagged_no_id R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem → get_tag lpc.(lw) = true → lpc.(lprov) = None.
  Proof.
    intros Her Ht. destruct (er_pc_word _ _ _ _ _ _ _ Her) as (_ & _ & Hexec).
    destruct (er_pc_ok _ _ _ _ _ _ _ Her Ht) as [_ Hx].
    by apply Hexec.
  Qed.

  (** The logical word MEPCC receives on exception entry from the logical PC:
      the physical word [mepcc_of_pc] (untagged on a fetch fault), without
      identifier. A tagged PC has no identifier, so only an untagged PC loses
      one. *)
  Definition lmepcc_of_pc (v : LWord) : LWord := lword_of_word (mepcc_of_pc v.(lw)).

  (** The MEPCC word of the logical PC of an erasure is a valid system
      register word. *)
  Lemma erasure_lmepcc_of_pc R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem →
    reg_word_ok R C (lmepcc_of_pc lpc) ∧ pc_ok (lmepcc_of_pc lpc).(lw).
  Proof.
    intros Her. rewrite /lmepcc_of_pc /mepcc_of_pc /=.
    destruct (get_tag lpc.(lw)) eqn:Ht; cbn.
    - destruct (isCorrectPCb lpc.(lw)); cbn.
      + pose proof (erasure_pc_tagged_no_id _ _ _ _ _ _ _ Her Ht) as Hπ.
        destruct lpc as [w π]; cbn in *; subst π. split.
        * apply (er_pc_word _ _ _ _ _ _ _ Her).
        * apply (er_pc_ok _ _ _ _ _ _ _ Her).
      + split; [apply reg_word_ok_untagged | apply pc_ok_untagged]; apply get_tag_clear_tag.
    - split; [by apply reg_word_ok_untagged | by apply pc_ok_untagged].
  Qed.

  (** The logical system registers after trap entry with cause [c] and value
      [v]: MEPCC receives the logical PC, untagged on a fetch fault
      ([lmepcc_of_pc]), and mstatus, mcause and mtval receive the integers
      that the machine writes. *)
  Definition lsregs_enter_exc (cv : Z * Z) (σ : ExecConf) (lpc : LWord) (lsreg : LSReg) : LSReg :=
    <[mtval := lword_of_word (WInt cv.2)]>
      (<[mcause := lword_of_word (WInt cv.1)]>
         (<[mstatus := lword_of_word
                         (WInt (mstatus_enc InterruptDisabled
                                  (mie_of (get_a (sreg_word σ mstatus)))))]>
            (<[mepcc := lmepcc_of_pc lpc]> lsreg))).

  (** *** The stack high-water mark *)

  (** A logical system register holding an integer is the physical one. *)
  Lemma erasure_lookup_sreg_int R C σ lpc lreg lsreg lmem x (z : Z) :
    erasure R C σ lpc lreg lsreg lmem →
    lsreg !! x = Some (lword_of_word (WInt z)) →
    sreg σ !! x = Some (WInt z).
  Proof.
    intros Her Hx.
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Hx) as (w & Hw & Hrel).
    rewrite Hw. f_equal. by apply reg_phys_no_bounds in Hrel.
  Qed.

  (** A store at [ea] outside [[MSHWMB, MSHWM)] leaves MSHWM. *)
  Lemma erasure_hwm_update R C pc r sr m st lpc lreg lsreg lmem (ea : Addr) (hb h : Z) :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    lsreg !! mshwmb = Some (lword_of_word (WInt hb)) →
    lsreg !! mshwm = Some (lword_of_word (WInt h)) →
    ¬ (hb ≤ ea < h)%Z →
    erasure R C (pc, r, hwm_update ea sr, m, st) lpc lreg lsreg lmem.
  Proof.
    intros Her Hb Hh Hout.
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her Hb) as Hpb.
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her Hh) as Hph.
    cbn in Hpb, Hph.
    rewrite hwm_update_id //. intros wb wh Hwb Hwh.
    rewrite Hpb in Hwb. rewrite Hph in Hwh. by simplify_eq.
  Qed.

  (** A store at [ea] in [[hb, h)] lowers MSHWM to [ea]. *)
  Lemma erasure_hwm_update_lower R C pc r sr m st lpc lreg lsreg lmem (ea : Addr) (hb h : Z) :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    lsreg !! mshwmb = Some (lword_of_word (WInt hb)) →
    lsreg !! mshwm = Some (lword_of_word (WInt h)) →
    (hb ≤ ea < h)%Z →
    erasure R C (pc, r, hwm_update ea sr, m, st) lpc lreg
      (<[mshwm := lword_of_word (WInt ea)]> lsreg) lmem.
  Proof.
    intros Her Hb Hh Hin.
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her Hb) as Hpb.
    pose proof (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her Hh) as Hph.
    cbn in Hpb, Hph.
    rewrite /hwm_update Hpb Hph /= decide_True //.
    apply erasure_insert_sreg; [done | apply reg_word_ok_int | by intros | done |].
    apply reg_phys_lword_of_word.
  Qed.

  (** Trap entry: the PC receives MTCC. *)
  Lemma erasure_enter_exc R C σ lpc lreg lsreg lmem cv vtcc :
    erasure R C σ lpc lreg lsreg lmem →
    lsreg !! mtcc = Some vtcc →
    erasure R C (enter_exc cv σ) vtcc lreg (lsregs_enter_exc cv σ lpc lsreg) lmem.
  Proof.
    intros Her Htcc.
    destruct (erasure_lmepcc_of_pc _ _ _ _ _ _ _ Her) as [Hepcc_ok Hepcc_pc].
    destruct σ as [[[[pc r] sr] m] st].
    destruct (erasure_lookup_sreg _ _ _ _ _ _ _ _ _ Her Htcc) as (wtcc & Hwtcc & Hreltcc).
    pose proof (erasure_pc_exact _ _ _ _ _ _ _ Her) as Hpc. cbn in Hpc.
    assert (∀ x (z : Z), is_pc_sreg x = false →
      ∀ pc' r' sr' m' st' lpc' lsreg',
        erasure R C (pc', r', sr', m', st') lpc' lreg lsreg' lmem →
        erasure R C (pc', r', <[x := WInt z]> sr', m', st') lpc' lreg
          (<[x := lword_of_word (WInt z)]> lsreg') lmem) as Hint.
    { intros x z Hx ????????. apply erasure_insert_sreg; first done.
      - apply reg_word_ok_int.
      - by intros.
      - by rewrite Hx.
      - apply reg_phys_lword_of_word. }
    rewrite /enter_exc /lsregs_enter_exc /update_sreg /update_pcc /sreg_word /=.
    rewrite Hwtcc /=.
    apply (erasure_set_pc R C pc _ _ _ _ lpc _ _ _ vtcc wtcc).
    - apply Hint; first done. apply Hint; first done. apply Hint; first done.
      change (pcc (pc, r, sr, m, st)) with pc.
      apply erasure_insert_sreg; [done | done | by intros | by intros _ |].
      rewrite Hpc. apply reg_phys_lword_of_word.
    - by apply (er_sreg_words _ _ _ _ _ _ _ Her mtcc).
    - done.
    - by apply (er_sreg_pc_ok _ _ _ _ _ _ _ Her mtcc).
  Qed.

  (** A logical PC that is not correct has a physical copy that is not
      correct either. *)
  Lemma erasure_pc_not_correct R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem → ¬ isCorrectPC lpc.(lw) → ¬ isCorrectPC (pcc σ).
  Proof.
    intros Her Hn Hc. destruct (reg_phys_cases _ _ _ (er_pc _ _ _ _ _ _ _ Her)) as [Heq | Heq];
      rewrite Heq in Hc; first done.
    by apply (not_isCorrectPC_untagged (clear_tag lpc.(lw))); first apply get_tag_clear_tag.
  Qed.

  (** *** Memory *)

  Lemma erasure_lookup_mem R C σ lpc lreg lsreg lmem a v :
    erasure R C σ lpc lreg lsreg lmem → lmem !! a = Some v →
    ∃ pw, mem σ !! a = Some pw ∧ mem_word_ok R C v pw.
  Proof.
    intros Her Hv.
    assert (is_Some (mem σ !! a)) as [pw Hpw].
    { apply elem_of_dom. rewrite -(er_mem_dom _ _ _ _ _ _ _ Her). by apply elem_of_dom_2 in Hv. }
    exists pw. split; first done. by eapply er_mem_words.
  Qed.

  Lemma mem_word_ok_decode R C v pw :
    mem_word_ok R C v pw → decodeInstrW pw = decodeInstrW v.(lw).
  Proof. intros (_ & [-> | ->] & _); [done | apply decodeInstrW_clear_tag]. Qed.

  Lemma erasure_store R C pc r sr m st lpc lreg lsreg lmem a v v' pw :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    lmem !! a = Some v' →
    mem_word_ok R C v pw →
    erasure R C (pc, r, sr, <[a := pw]> m, st) lpc lreg lsreg (<[a := v]> lmem).
  Proof.
    intros Her Ha Hok.
    destruct Her as [Hreg Hregs Hcnull Hrw Hsregs Hsrw Hsrlid Hsrpc Hdom Hmw Hmmio
                     Hpc Hpcw Hpcok Hhmap].
    constructor; cbn in *; try done.
    - rewrite !dom_insert_L. by rewrite Hdom.
    - intros a' v'' pw'. destruct (decide (a = a')) as [<-|Hne].
      + rewrite !lookup_insert_eq. intros [= <-] [= <-]. done.
      + rewrite !lookup_insert_ne //. apply Hmw.
    - assert (is_Some (m !! a)) as [pw0 Hpw0].
      { apply elem_of_dom. rewrite -Hdom. by apply elem_of_dom_2 in Ha. }
      by eapply mem_avoids_mmio_update.
    - by apply heap_mapped_insert.
  Qed.

  (** *** Shadow stores *)

  (** A shadow store keeps erasure when the stored bit is the old one, or when
      the cell is unclaimed or claimed by a painting allocation, and it is not
      a heap root. *)
  Definition shadow_store_ok R C (shadow : ShadowTbl) (a : Addr) (s : AllocStatus) : Prop :=
    shadow !! a = Some s ∨
    C !! a = Some Unclaimed ∨
    (∃ ι x, C !! a = Some (Claimed ι) ∧ R !! ι = Some x ∧ re_status x = APainting).

  Lemma erasure_shadow_store R C pc r sr m st lpc lreg lsreg lmem a s :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    is_Some (st !! a) →
    shadow_store_ok R C st a s →
    erasure R C (pc, r, sr, m, <[a := s]> st) lpc lreg lsreg lmem.
  Proof.
    intros Her Hst Hok.
    destruct Her as [Hreg Hregs Hcnull Hrw Hsregs Hsrw Hsrlid Hsrpc Hdom Hmw Hmmio
                     Hpc Hpcw Hpcok Hhmap].
    constructor; cbn in *; try done.
    destruct Hreg as [Hheap Hlive Hquar Hcdom Hclaimed Hroot Hshadow].
    (* The cells whose shadow bit matters are those of live or quarantined
       identifiers, and heap roots. None of them is [a], unless [s] is its
       old bit. *)
    assert (∀ a', a' = a → st !! a' = Some s ∨
       ((∀ ι x, R !! ι = Some x → re_covers x a' →
                re_status x ≠ ALive ∧ re_status x ≠ AQuar) ∧
        C !! a' ≠ Some HeapRoot)) as Hcell.
    { intros a' ->. destruct Hok as [Hs | [Hun | (ι & x & Hcl & Hx & Hpaint)] ]; first by left.
      - right. split; last congruence.
        intros ι x Hx Hcov. destruct (decide (re_status x = ADead)) as [Hd|Hd].
        + rewrite Hd. done.
        + assert (C !! a = Some (Claimed ι)) by (apply Hclaimed; eauto). congruence.
      - right. split; last congruence.
        intros ι' x' Hx' Hcov. destruct (decide (re_status x' = ADead)) as [Hd|Hd].
        + rewrite Hd. done.
        + assert (C !! a = Some (Claimed ι')) by (apply Hclaimed; eauto).
          simplify_eq. rewrite Hpaint. done. }
    constructor; try done.
    - intros ι x a' Hx Hs Hcov. destruct (decide (a = a')) as [<-|Hne].
      + rewrite lookup_insert_eq. destruct (Hcell a eq_refl) as [Hs'|[Hc _] ].
        * by rewrite -(Hlive _ _ _ Hx Hs Hcov) Hs'.
        * exfalso. by destruct (Hc _ _ Hx Hcov).
      + rewrite lookup_insert_ne //. eauto.
    - intros ι x a' Hx Hs Hcov. destruct (decide (a = a')) as [<-|Hne].
      + rewrite lookup_insert_eq. destruct (Hcell a eq_refl) as [Hs'|[Hc _] ].
        * by rewrite -(Hquar _ _ _ Hx Hs Hcov) Hs'.
        * exfalso. by destruct (Hc _ _ Hx Hcov).
      + rewrite lookup_insert_ne //. eauto.
    - intros a' Hr. destruct (decide (a = a')) as [<-|Hne].
      + rewrite lookup_insert_eq. destruct (Hcell a eq_refl) as [Hs'|[_ Hc] ].
        * by rewrite -(Hroot _ Hr) Hs'.
        * done.
      + rewrite lookup_insert_ne //. eauto.
    - intros a' Ha'. destruct (decide (a = a')) as [<-|Hne].
      + by rewrite lookup_insert_eq.
      + rewrite lookup_insert_ne //. eauto.
  Qed.

  (** *** Registry transitions *)

  (** A status step between non-dead statuses, out of [ALive] and into
      [AQuar] only with the whole range painted and with no register, system
      register or PC word with authority carrying [ι] (its physical copy may
      be tagged). *)
  Lemma erasure_reg_step R C σ lpc lreg lsreg lmem ι b e γ s s' :
    erasure R C σ lpc lreg lsreg lmem →
    R !! ι = Some (b, e, γ, s) →
    s ≠ ADead → s' ≠ ADead → s' ≠ ALive →
    (s' = AQuar → ∀ a, a ∈ₐ [b, e) → shadowtbl σ !! a = Some ShadowQuarantined) →
    (s' = AQuar → ∀ v, (v = lpc ∨ (∃ x, lreg !! x = Some v) ∨ ∃ x, lsreg !! x = Some v) →
       has_authority v.(lw) → v.(lprov) ≠ Some ι) →
    erasure (<[ι := (b, e, γ, s')]> R) C σ lpc lreg lsreg lmem.
  Proof.
    intros Her HR Hs Hs' Hs'live Hquar' Hclean.
    destruct Her as [Hreg [Hrdom Hregs] Hcnull Hrw Hsregs Hsrw Hsrlid Hsrpc Hdom Hmw Hmmio
                     Hpc Hpcw Hpcok Hhmap].
    destruct Hreg as [Hheap Hlive Hquar Hcdom Hclaimed Hroot Hshadow].
    set (R' := <[ι := (b, e, γ, s')]> R).
    (* Lookups in the new registry *)
    assert (∀ ι' x', R' !! ι' = Some x' →
      (ι' = ι ∧ x' = (b, e, γ, s')) ∨ (ι' ≠ ι ∧ R !! ι' = Some x')) as Hlook.
    { intros ι' x'. destruct (decide (ι = ι')) as [<-|Hne].
      - rewrite /R' lookup_insert_eq. intros [= <-]. by left.
      - rewrite /R' lookup_insert_ne //. by right. }
    assert (∀ ι' x, R !! ι' = Some x → ∃ x', R' !! ι' = Some x' ∧
      re_b x' = re_b x ∧ re_e x' = re_e x ∧
      (ι' ≠ ι → x' = x) ∧ (re_status x' = ADead ↔ re_status x = ADead)) as Hlook'.
    { intros ι' x Hx. destruct (decide (ι = ι')) as [<-|Hne].
      - rewrite /R' lookup_insert_eq. rewrite HR in Hx. simplify_eq.
        eexists. split; first done. cbn. naive_solver.
      - rewrite /R' lookup_insert_ne //. eexists. split; first done. naive_solver. }
    assert (∀ v, lword_prov R v → lword_prov R' v) as Hprov.
    { intros v Hp ι' b' e' Ht Hb Hlt Hι.
      destruct (Hp ι' b' e' Ht Hb Hlt Hι) as (x & Hx & Hb1 & He1).
      destruct (Hlook' _ _ Hx) as (x' & Hx' & Hb' & He' & _).
      exists x'. by rewrite Hb' He'. }
    assert (∀ v, stale_id R v → stale_id R' v) as Hstale.
    { intros v (ι' & x & Hι' & Hx & Hl). destruct (decide (ι = ι')) as [<-|Hne].
      - exists ι, (b, e, γ, s'). by rewrite /R' lookup_insert_eq.
      - exists ι', x. by rewrite /R' lookup_insert_ne. }
    assert (∀ v, reg_authority R C v → reg_authority R' C v) as Hauth'.
    { intros v Hauth b' Ht Hab. specialize (Hauth b' Ht Hab).
      destruct (lprov v) as [ι'|]; last done.
      destruct Hauth as [x Hx]. destruct (Hlook' _ _ Hx) as (x' & Hx' & _). by exists x'. }
    assert (∀ v w, (v = lpc ∨ (∃ x, lreg !! x = Some v) ∨ ∃ x, lsreg !! x = Some v) →
              reg_phys R v w → reg_phys R' v w)
      as Hphys.
    { intros v w Hv [Hrel Hq]. split.
      - destruct Hrel as [-> | [-> Hstrip] ]; first by left. right. split; first done.
        destruct Hstrip as [[Hst Hbs] | Hh]; [left; split; [by apply Hstale | done] | by right].
      - intros ι' x' Ha Hι' Hx' Hqd. destruct (Hlook _ _ Hx') as [[-> ->] | [_ Hx] ].
        + destruct Hqd as [Hqd | Hqd]; cbn in Hqd; last done.
          exfalso. by eapply (Hclean Hqd v Hv Ha).
        + by eapply Hq. }
    constructor; cbn; try done.
    - constructor; try done.
      + intros ι' x a Hx Hcov. destruct (Hlook _ _ Hx) as [[-> ->]|[_ Hx'] ].
        * eapply (Hheap ι); eauto.
        * eauto.
      + intros ι' x a Hx Hst Hcov. destruct (Hlook _ _ Hx) as [[-> ->]|[_ Hx'] ].
        * by cbn in Hst.
        * eauto.
      + intros ι' x a Hx Hst Hcov. destruct (Hlook _ _ Hx) as [[-> ->]|[_ Hx'] ].
        * apply Hquar'; first done. apply Hcov.
        * eauto.
      + intros a ι'. rewrite Hclaimed. split.
        * intros (x & Hx & Hcov & Hd). destruct (Hlook' _ _ Hx) as (x' & Hx' & Hb & He & _ & Hd').
          exists x'. split; first done. split; first by rewrite /re_covers Hb He. by rewrite Hd'.
        * intros (x' & Hx' & Hcov & Hd). destruct (Hlook _ _ Hx') as [[-> ->]|[Hne Hx] ].
          -- exists (b, e, γ, s). split; first done. split; first done. done.
          -- exists x'. eauto.
    - split; first done. intros x v Hv. destruct (Hregs x v Hv) as (w & Hw & Hok).
      eexists. split; first done. apply Hphys; eauto.
    - intros r v Hv. destruct (Hrw r v Hv) as (Hp & Hauth & Hexec).
      split_and!; [by apply Hprov | by apply Hauth' | done].
    - intros srn vs Hvs. destruct (Hsregs srn vs Hvs) as (ws & Hws & Hrel).
      exists ws. split; first done. apply Hphys; eauto.
    - intros srn vs Hvs. destruct (Hsrw srn vs Hvs) as (Hp & Hauth & Hexec).
      split_and!; [by apply Hprov | by apply Hauth' | done].
    - intros a v pw Hv Hpw. destruct (Hmw a v pw Hv Hpw) as (Hp & Hrel & Hnh & Hauth & Hexec).
      split; first by apply Hprov. split; first done.
      split; first (intros Hn; destruct (Hnh Hn) as [? | [? ?] ]; [by left | right; split; [by apply Hstale | done] ]).
      split; last done.
      intros b' Ht Hab. specialize (Hauth b' Ht Hab).
      destruct (lprov v) as [ι'|]; last done.
      destruct Hauth as (x & Hx & Hl & Hd).
      destruct (decide (ι = ι')) as [<-|Hne].
      + rewrite /R' lookup_insert_eq. eexists. split; first done. cbn.
        split; intros; done.
      + rewrite /R' lookup_insert_ne //. eauto.
    - apply Hphys; auto.
    - destruct Hpcw as (Hp & Hauth & Hexec).
      split_and!; [by apply Hprov | by apply Hauth' | done].
  Qed.

  (** *** Allocation *)

  Lemma lword_prov_fresh R v ι b e :
    lword_prov R v → R !! ι = None → v.(lprov) = Some ι →
    get_tag v.(lw) = true → memory_cap_bounds v.(lw) = Some (b, e) → (b < e)%a → False.
  Proof. intros Hp HR Hι Ht Hb Hlt. destruct (Hp ι b e Ht Hb Hlt Hι) as (x & Hx & _). congruence. Qed.

  (** Allocation of a fresh identifier over unclaimed, unpainted cells. *)
  Lemma erasure_alloc R C C' σ lpc lreg lsreg lmem ι b e γ :
    erasure R C σ lpc lreg lsreg lmem →
    R !! ι = None →
    (∀ a, a ∈ₐ [b, e) → C !! a = Some Unclaimed ∧ shadowtbl σ !! a = Some ShadowLive) →
    (∀ a, C' !! a = if decide (a ∈ₐ [b, e)) then Some (Claimed ι) else C !! a) →
    erasure (<[ι := (b, e, γ, ALive)]> R) C' σ lpc lreg lsreg lmem.
  Proof.
    intros Her HR Hcells HC'.
    destruct Her as [Hreg [Hrdom Hregs] Hcnull Hrw Hsregs Hsrw Hsrlid Hsrpc Hdom Hmw Hmmio
                     Hpc Hpcw Hpcok Hhmap].
    destruct Hreg as [Hheap Hlive Hquar Hcdom Hclaimed Hroot Hshadow].
    set (R' := <[ι := (b, e, γ, ALive)]> R).
    assert (∀ ι', ι' ≠ ι → R' !! ι' = R !! ι') as HR'ne.
    { intros. by rewrite /R' lookup_insert_ne. }
    assert (R' !! ι = Some (b, e, γ, ALive)) as HR'eq by by rewrite /R' lookup_insert_eq.
    (* A heap root is not in the range. *)
    assert (∀ a, C !! a = Some HeapRoot → C' !! a = Some HeapRoot) as Hroot'.
    { intros a Ha. rewrite HC'. case_decide as Hin; last done.
      destruct (Hcells a Hin) as [Hc _]. congruence. }
    assert (∀ v, lword_prov R v → lword_prov R' v) as Hprov.
    { intros v Hp ι' b' e' Ht Hb Hlt Hι'.
      destruct (decide (ι' = ι)) as [->|Hne].
      - exfalso. eapply lword_prov_fresh; eauto.
      - rewrite HR'ne //. eauto. }
    assert (∀ v b', lword_prov R v → get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b' →
              v.(lprov) ≠ Some ι) as Hnotι.
    { intros v b' Hp Ht Hab Hι. apply heap_authority_base_bounds in Hab as (e' & Hb' & Hlt).
      eapply lword_prov_fresh; eauto. }
    assert (∀ v, stale_id R v → stale_id R' v) as Hstale.
    { intros v (ι' & x & Hι' & Hx & Hl). exists ι', x.
      destruct (decide (ι' = ι)) as [->|Hne]; first congruence. by rewrite HR'ne. }
    assert (∀ v w, reg_phys R v w → reg_phys R' v w) as Hphys.
    { intros v w [Hrel Hq]. split.
      - destruct Hrel as [-> | [-> Hstrip] ]; first by left. right. split; first done.
        destruct Hstrip as [[Hst Hbs] | Hh]; [left; split; [by apply Hstale | done] | by right].
      - intros ι' x' Ha Hι' Hx' Hqd. destruct (decide (ι' = ι)) as [->|Hne].
        + rewrite HR'eq in Hx'. simplify_eq. by destruct Hqd.
        + rewrite HR'ne // in Hx'. by eapply Hq. }
    constructor; cbn; try done.
    - constructor.
      + intros ι' x a Hx Hcov. destruct (decide (ι' = ι)) as [->|Hne].
        * rewrite HR'eq in Hx. simplify_eq. destruct (Hcells a Hcov) as [Hc _].
          apply Hcdom. eauto.
        * rewrite HR'ne // in Hx. eauto.
      + intros ι' x a Hx Hs Hcov. destruct (decide (ι' = ι)) as [->|Hne].
        * rewrite HR'eq in Hx. simplify_eq. by destruct (Hcells a Hcov).
        * rewrite HR'ne // in Hx. eauto.
      + intros ι' x a Hx Hs Hcov. destruct (decide (ι' = ι)) as [->|Hne].
        * rewrite HR'eq in Hx. by simplify_eq.
        * rewrite HR'ne // in Hx. eauto.
      + intros a. rewrite HC'. case_decide as Hin.
        * split; first (intros _; apply Hcdom; destruct (Hcells a Hin); eauto). eauto.
        * apply Hcdom.
      + intros a ι'. rewrite HC'. case_decide as Hin.
        * split.
          -- intros [= <-]. exists (b, e, γ, ALive). done.
          -- intros (x & Hx & Hcov & Hd). destruct (decide (ι' = ι)) as [->|Hne]; first done.
             rewrite HR'ne // in Hx. destruct (Hcells a Hin) as [Hc _].
             assert (C !! a = Some (Claimed ι')) by (apply Hclaimed; eauto). congruence.
        * rewrite Hclaimed. split.
          -- intros (x & Hx & Hcov & Hd). exists x.
             destruct (decide (ι' = ι)) as [->|Hne]; first congruence.
             by rewrite HR'ne.
          -- intros (x & Hx & Hcov & Hd). destruct (decide (ι' = ι)) as [->|Hne].
             ++ rewrite HR'eq in Hx. by simplify_eq.
             ++ rewrite HR'ne // in Hx. eauto.
      + intros a. rewrite HC'. case_decide; first done. apply Hroot.
      + done.
    - split; first done. intros x v Hv. destruct (Hregs x v Hv) as (w & Hw & Hok).
      eexists. split; first done. by apply Hphys.
    - intros r v Hv. destruct (Hrw r v Hv) as (Hp & Hauth & Hexec). split; first by apply Hprov. split; last done.
      intros b' Ht Hab. pose proof (Hnotι v b' Hp Ht Hab) as Hne. specialize (Hauth b' Ht Hab).
      destruct (lprov v) as [ι'|]; last by apply Hroot'.
      destruct Hauth as [x Hx]. exists x. rewrite HR'ne //. congruence.
    - intros srn vs Hvs. destruct (Hsregs srn vs Hvs) as (ws & Hws & Hrel).
      exists ws. split; first done. by apply Hphys.
    - intros srn vs Hvs. destruct (Hsrw srn vs Hvs) as (Hp & Hauth & Hexec). split; first by apply Hprov. split; last done.
      intros b' Ht Hab. pose proof (Hnotι vs b' Hp Ht Hab) as Hne. specialize (Hauth b' Ht Hab).
      destruct (lprov vs) as [ι'|]; last by apply Hroot'.
      destruct Hauth as [x Hx]. exists x. rewrite HR'ne //. congruence.
    - intros a v pw Hv Hpw. destruct (Hmw a v pw Hv Hpw) as (Hp & Hrel & Hnh & Hauth & Hexec).
      split; first by apply Hprov. split; first done.
      split; first (intros Hn; destruct (Hnh Hn) as [? | [? ?] ]; [by left | right; split; [by apply Hstale | done] ]).
      split; last done.
      intros b' Ht Hab. pose proof (Hnotι v b' Hp Ht Hab) as Hne. specialize (Hauth b' Ht Hab).
      destruct (lprov v) as [ι'|].
      + destruct Hauth as (x & Hx & Hl & Hd). exists x. rewrite HR'ne //. congruence.
      + destruct Hauth. split; first done. by apply Hroot'.
    - by apply Hphys.
    - destruct Hpcw as (Hp & Hauth & Hexec). split; first by apply Hprov. split; last done.
      intros b' Ht Hab. pose proof (Hnotι lpc b' Hp Ht Hab) as Hne. specialize (Hauth b' Ht Hab).
      destruct (lprov lpc) as [ι'|]; last by apply Hroot'.
      destruct Hauth as [x Hx]. exists x. rewrite HR'ne //. congruence.
  Qed.

  (** *** The revoker *)

  (** The sweep kills the identifiers of [K]: they are quarantined, so their
      ranges are painted and the sweep untags their memory words, and the
      physical register copies of their words with authority are already
      untagged. *)
  Lemma erasure_revoke R R' C C' pc r sr m st lpc lreg lsreg lmem (K : gset AId) :
    erasure R C (pc, r, sr, m, st) lpc lreg lsreg lmem →
    (∀ ι, ι ∈ K → ∃ x, R !! ι = Some x ∧ re_status x = AQuar) →
    (∀ ι, R' !! ι = (λ x : RegEntry, if decide (ι ∈ K) then (x.1, ADead) else x) <$> R !! ι) →
    (∀ a, C' !! a = (λ c, match c with
                          | Claimed ι => if decide (ι ∈ K) then Unclaimed else c
                          | _ => c end) <$> C !! a) →
    erasure R' C' (pc, r, sr, sweep_mem st m, st) lpc lreg lsreg lmem.
  Proof.
    intros Her HK HR' HC'.
    destruct Her as [Hreg [Hrdom Hregs] Hcnull Hrw Hsregs Hsrw Hsrlid Hsrpc Hdom Hmw Hmmio
                     Hpc Hpcw Hpcok Hhmap]; cbn in *.
    destruct Hreg as [Hheap Hlive Hquar Hcdom Hclaimed Hroot Hshadow].
    (* Lookups in [R'] *)
    assert (∀ ι x', R' !! ι = Some x' → ∃ x, R !! ι = Some x ∧ re_b x' = re_b x ∧
      re_e x' = re_e x ∧ re_status x' = if decide (ι ∈ K) then ADead else re_status x) as HR'l.
    { intros ι x' Hx'. rewrite HR' in Hx'. apply fmap_Some in Hx' as (x & Hx & ->).
      exists x. case_decide; done. }
    assert (∀ ι x, R !! ι = Some x → ∃ x', R' !! ι = Some x' ∧ re_b x' = re_b x ∧
      re_e x' = re_e x ∧ re_status x' = if decide (ι ∈ K) then ADead else re_status x) as HR'r.
    { intros ι x Hx. rewrite HR' Hx /=. eexists. split; first done. case_decide; done. }
    assert (∀ v, lword_prov R v → lword_prov R' v) as Hprov.
    { intros v Hp ι b e Ht Hb Hlt Hι.
      destruct (Hp ι b e Ht Hb Hlt Hι) as (x & Hx & ? & ?).
      destruct (HR'r _ _ Hx) as (x' & Hx' & Hb' & He' & _). exists x'. by rewrite Hb' He'. }
    assert (∀ a, C !! a = Some HeapRoot → C' !! a = Some HeapRoot) as Hroot'.
    { intros a Ha. by rewrite HC' Ha. }
    assert (∀ v, stale_id R v → stale_id R' v) as Hstale.
    { intros v (ι & x & Hι & Hx & Hl). destruct (HR'r _ _ Hx) as (x' & Hx' & _ & _ & Hs').
      exists ι, x'. split_and!; try done. rewrite Hs'. by case_decide. }
    assert (∀ v w, reg_phys R v w → reg_phys R' v w) as Hphys.
    { intros v w [Hrel Hq]. split.
      - destruct Hrel as [-> | [-> Hstrip] ]; first by left. right. split; first done.
        destruct Hstrip as [[Hst Hbs] | Hh]; [left; split; [by apply Hstale | done] | by right].
      - intros ι x' Ha Hι Hx' Hqd. destruct (HR'l _ _ Hx') as (x & Hx & _ & _ & Hs').
        eapply Hq; eauto. case_decide as HιK.
        + destruct (HK ι HιK) as (x1 & Hx1 & Hq1). rewrite Hx in Hx1. simplify_eq. by left.
        + by rewrite -Hs'. }
    assert (∀ v, reg_authority R C v → reg_authority R' C' v) as Hauth'.
    { intros v Hauth b Ht Hab. specialize (Hauth b Ht Hab).
      destruct (lprov v) as [ι|]; last by apply Hroot'.
      destruct Hauth as [x Hx]. destruct (HR'r _ _ Hx) as (x' & Hx' & _). by exists x'. }
    constructor; cbn; try done.
    - constructor.
      + intros ι x' a Hx' Hcov. destruct (HR'l _ _ Hx') as (x & Hx & Hb & He & _).
        eapply Hheap; first done. by rewrite /re_covers -Hb -He.
      + intros ι x' a Hx' Hs Hcov. destruct (HR'l _ _ Hx') as (x & Hx & Hb & He & Hs').
        case_decide; first congruence.
        eapply Hlive; first done; first congruence. by rewrite /re_covers -Hb -He.
      + intros ι x' a Hx' Hs Hcov. destruct (HR'l _ _ Hx') as (x & Hx & Hb & He & Hs').
        case_decide; first congruence.
        eapply Hquar; first done; first congruence. by rewrite /re_covers -Hb -He.
      + intros a. rewrite HC' fmap_is_Some. apply Hcdom.
      + intros a ι. rewrite HC'. split.
        * intros Hc. apply fmap_Some in Hc as (c & Hc & Heq).
          destruct c as [|ι'|]; try done. case_decide; simplify_eq.
          apply Hclaimed in Hc as (x & Hx & Hcov & Hd).
          destruct (HR'r _ _ Hx) as (x' & Hx' & Hb & He & Hs').
          exists x'. split; first done. split; first by rewrite /re_covers Hb He.
          by rewrite Hs' decide_False.
        * intros (x' & Hx' & Hcov & Hd). destruct (HR'l _ _ Hx') as (x & Hx & Hb & He & Hs').
          case_decide as HιK; first done.
          assert (C !! a = Some (Claimed ι)) as Hc.
          { apply Hclaimed. exists x. rewrite /re_covers -Hb -He. rewrite Hs' in Hd. done. }
          by rewrite Hc /= decide_False.
      + intros a. rewrite HC'. intros Hc. apply fmap_Some in Hc as (c & Hc & Heq).
        destruct c as [|ι'|]; try done; first by case_decide. by apply Hroot.
      + done.
    - split; first done. intros x v Hv. destruct (Hregs x v Hv) as (w & Hw & Hok).
      eexists. split; first done. by apply Hphys.
    - intros x v Hv. destruct (Hrw x v Hv) as (Hp & Hauth & Hexec).
      split_and!; [by apply Hprov | by apply Hauth' | done].
    - intros srn vs Hvs. destruct (Hsregs srn vs Hvs) as (ws & Hws & Hrel).
      exists ws. split; first done. by apply Hphys.
    - intros srn vs Hvs. destruct (Hsrw srn vs Hvs) as (Hp & Hauth & Hexec).
      split_and!; [by apply Hprov | by apply Hauth' | done].
    - by rewrite dom_sweep_mem.
    - intros a v pw' Hv Hpw'. rewrite lookup_sweep_mem in Hpw'.
      apply fmap_Some in Hpw' as (pw & Hpw & ->).
      destruct (Hmw a v pw Hv Hpw) as (Hp & Hrel & Hnh & Hauth & Hexec).
      assert (memory_cap_bounds pw = memory_cap_bounds v.(lw)) as Hbpw.
      { destruct Hrel as [-> | ->]; rewrite ?memory_cap_bounds_clear_tag //. }
      split; first by apply Hprov. split.
      { destruct (sweep_word_cases st pw) as [-> | ->]; first done.
        destruct Hrel as [-> | ->]; rewrite ?clear_tag_idempotent; auto. }
      split.
      { intros Hn. rewrite sweep_word_nonheap; last by rewrite (heap_cap_base_bounds_eq _ _ Hbpw).
        destruct (Hnh Hn) as [? | [? ?] ]; [by left | right; split; [by apply Hstale | done] ]. }
      split; last done.
      intros b Ht Hab. specialize (Hauth b Ht Hab).
      pose proof Hab as (e & Hbe & Hlt)%heap_authority_base_bounds.
      assert (is_heap_address b = true) as Hbh.
      { apply heap_authority_base_memory_cap_bounds in Hab as (? & ? & ? & ?). done. }
      assert (heap_cap_base pw = Some b) as Hhb.
      { eapply memory_cap_bounds_heap_cap_base; last done. by rewrite Hbpw. }
      destruct (lprov v) as [ι|] eqn:Hι.
      + destruct Hauth as (x & Hx & Hl & Hd).
        destruct (Hp ι b e Ht Hbe Hlt Hι) as (x0 & Hx0 & Hb0 & He0). rewrite Hx in Hx0.
        simplify_eq.
        destruct (HR'r _ _ Hx) as (x' & Hx' & _ & _ & Hs'). exists x'. split; first done.
        assert (re_covers x0 b) as Hcov by (rewrite /re_covers; solve_addr).
        case_decide as HιK.
        * split; first by rewrite Hs'. intros _.
          destruct (HK ι HιK) as (x1 & Hx1 & Hq). rewrite Hx in Hx1. simplify_eq.
          rewrite (sweep_word_quarantined _ _ b) //; last by eapply Hquar.
          destruct Hrel as [-> | ->]; rewrite ?clear_tag_idempotent //.
        * rewrite Hs'. split.
          -- intros Hlv. rewrite sweep_word_unchanged; first by apply Hl.
             intros base Hbase. rewrite Hhb in Hbase. simplify_eq.
             by rewrite (Hlive _ _ _ Hx Hlv Hcov).
          -- intros Hdd. rewrite (Hd Hdd).
             destruct (sweep_word_cases st (clear_tag v.(lw))) as [-> | ->];
               rewrite ?clear_tag_idempotent //.
      + destruct Hauth as [-> Hc]. split; last by apply Hroot'.
        apply sweep_word_unchanged. intros base Hbase.
        assert (heap_cap_base v.(lw) = Some b) as Hb'.
        { eapply memory_cap_bounds_heap_cap_base; eauto. }
        rewrite Hb' in Hbase. simplify_eq. by rewrite (Hroot _ Hc).
    - by apply mem_avoids_mmio_sweep.
    - by apply Hphys.
    - destruct Hpcw as (Hp & Hauth & Hexec).
      split_and!; [by apply Hprov | by apply Hauth' | done].
    - by apply heap_mapped_sweep.
  Qed.

  (** *** Loads *)

  (** Variant 2: the identifier is quarantined or dead, so the loaded copy is
      untagged. *)
  Lemma load_filter_quarantined R C st v pw p pl ι x :
    registry_ok R C st →
    mem_word_ok R C v pw →
    load_filter st p pw = Some pl →
    v.(lprov) = Some ι → R !! ι = Some x →
    lifecycle_enc AQuar ≤ lifecycle_enc (re_status x) →
    (get_tag v.(lw) = true → has_authority v.(lw)) →
    pl = clear_tag (load_word p v.(lw)).
  Proof.
    intros Hreg Hok Hpl Hι Hx Hle Hside.
    pose proof (mem_word_ok_load_word _ _ _ _ _ _ _ Hok Hpl) as Hcases.
    destruct (get_tag v.(lw)) eqn:Ht.
    - destruct (Hside eq_refl) as [_ (b & Hab)].
      destruct Hok as (Hp & Hrel & Hnh & Hauth & _). specialize (Hauth b Ht Hab).
      rewrite Hι in Hauth. destruct Hauth as (x' & Hx' & _ & Hd). rewrite Hx in Hx'. simplify_eq.
      destruct (re_status x') eqn:Hs; cbn in Hle; try lia.
      + (* AQuar *)
        pose proof Hab as (e & Hbe & Hlt)%heap_authority_base_bounds.
        destruct (Hp ι b e Ht Hbe Hlt Hι) as (x0 & Hx0 & Hb0 & He0). rewrite Hx in Hx0. simplify_eq.
        assert (st !! b = Some ShadowQuarantined) as Hsb.
        { eapply reg_ok_quar; eauto. rewrite /re_covers. solve_addr. }
        assert (heap_cap_base pw = Some b) as Hhb.
        { eapply memory_cap_bounds_heap_cap_base.
          - destruct Hrel as [-> | ->]; rewrite ?memory_cap_bounds_clear_tag; exact Hbe.
          - apply heap_authority_base_memory_cap_bounds in Hab as (? & ? & ? & ?). done. }
        rewrite /load_filter Hhb Hsb in Hpl. simplify_eq.
        destruct Hrel as [-> | ->]; rewrite ?load_word_clear_tag ?clear_tag_idempotent //.
      + (* ADead *)
        rewrite (Hd eq_refl) in Hpl.
        apply load_filter_cases in Hpl as [-> | (_ & ->)];
          rewrite load_word_clear_tag ?clear_tag_idempotent //.
    - assert (get_tag (load_word p v.(lw)) = false) as Ht' by by rewrite get_tag_load_word.
      destruct Hcases as [-> | ->]; last done. by rewrite clear_tag_untagged.
  Qed.

  (** The side condition of the exact variants: a tagged word either has
      authority or is not a heap capability. *)
  Definition load_exact_cond (v : LWord) : Prop :=
    get_tag v.(lw) = true → has_authority v.(lw) ∨ heap_cap_base v.(lw) = None.

  Lemma load_filter_exact_aux R C st v pw p pl :
    registry_ok R C st →
    mem_word_ok R C v pw →
    load_filter st p pw = Some pl →
    load_exact_cond v →
    ¬ stale_id R v →
    (∀ b, get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b →
          pw = v.(lw) ∧ st !! b = Some ShadowLive) →
    pl = load_word p v.(lw).
  Proof.
    intros Hreg Hok Hpl Hside Hns Hauth.
    pose proof (mem_word_ok_load_word _ _ _ _ _ _ _ Hok Hpl) as Hcases.
    destruct Hok as (Hp & Hrel & Hnh & _).
    destruct (get_tag v.(lw)) eqn:Ht.
    - destruct (Hside Ht) as [[_ (b & Hab)] | Hnone].
      + destruct (Hauth b eq_refl Hab) as [-> Hsb].
        assert (heap_cap_base v.(lw) = Some b) as Hhb.
        { by apply heap_authority_base_heap_cap_base. }
        rewrite /load_filter Hhb Hsb in Hpl. by simplify_eq.
      + destruct (Hnh Hnone) as [Heq | Hst]; last by destruct Hst.
        rewrite Heq /load_filter Hnone in Hpl. by simplify_eq.
    - assert (get_tag (load_word p v.(lw)) = false) as Ht' by by rewrite get_tag_load_word.
      destruct Hcases as [-> | ->]; first done. by rewrite clear_tag_untagged.
  Qed.

  (** Variant 3: the identifier is live, so the loaded copy is exact. *)
  Lemma load_filter_live R C st v pw p pl ι x :
    registry_ok R C st →
    mem_word_ok R C v pw →
    load_filter st p pw = Some pl →
    v.(lprov) = Some ι → R !! ι = Some x → re_status x = ALive →
    load_exact_cond v →
    pl = load_word p v.(lw).
  Proof.
    intros Hreg Hok Hpl Hι Hx Hs Hside.
    eapply load_filter_exact_aux; eauto.
    { intros (ι' & x' & Hι' & Hx' & Hs'). simplify_eq; congruence. }
    intros b Ht Hab. destruct Hok as (Hp & _ & _ & Hauth & _). specialize (Hauth b Ht Hab).
    rewrite Hι in Hauth. destruct Hauth as (x' & Hx' & Hl & _). rewrite Hx in Hx'. simplify_eq.
    split; first by apply Hl.
    pose proof Hab as (e & Hbe & Hlt)%heap_authority_base_bounds.
    destruct (Hp ι b e Ht Hbe Hlt Hι) as (x0 & Hx0 & Hb0 & He0). rewrite Hx in Hx0. simplify_eq.
    eapply reg_ok_live; eauto. rewrite /re_covers. solve_addr.
  Qed.

  (** Variant 4: identifier-less words with authority are on heap roots,
      which are never painted, so the loaded copy is exact. *)
  Lemma load_filter_none R C st v pw p pl :
    registry_ok R C st →
    mem_word_ok R C v pw →
    load_filter st p pw = Some pl →
    v.(lprov) = None →
    load_exact_cond v →
    pl = load_word p v.(lw).
  Proof.
    intros Hreg Hok Hpl Hι Hside.
    eapply load_filter_exact_aux; eauto.
    { intros (ι' & x' & Hι' & _). congruence. }
    intros b Ht Hab. destruct Hok as (_ & _ & _ & Hauth & _). specialize (Hauth b Ht Hab).
    rewrite Hι in Hauth. destruct Hauth as [Hpw Hc]. split; first done.
    eapply reg_ok_root; eauto.
  Qed.

  (** A heap capability's base is in the shadow table, so the filter does
      not fail. *)
  Lemma load_filter_is_Some R C st p pw :
    registry_ok R C st → is_Some (load_filter st p pw).
  Proof.
    intros Hreg. rewrite /load_filter. destruct (heap_cap_base pw) as [b|] eqn:Hb; last eauto.
    assert (is_heap_address b = true) as Hbh.
    { rewrite /heap_cap_base in Hb. destruct (memory_cap_base pw); last done.
      case_match; by simplify_eq. }
    destruct (reg_ok_shadow _ _ _ Hreg b Hbh) as [[] ->]; eauto.
  Qed.

  (** *** Observation *)

  (** A word with authority is claimed at its base by its identifier while
      the identifier is not dead, and its base is a heap root if it has
      none. *)
  Lemma reg_word_observe R C st v b :
    registry_ok R C st →
    reg_word_ok R C v →
    get_tag v.(lw) = true →
    heap_authority_base v.(lw) = Some b →
    match v.(lprov) with
    | Some ι => ∃ x, R !! ι = Some x ∧ (re_status x ≠ ADead → C !! b = Some (Claimed ι))
    | None => C !! b = Some HeapRoot
    end.
  Proof.
    intros Hreg (Hp & Hauth & _) Ht Hab.
    specialize (Hauth b Ht Hab). destruct (lprov v) as [ι|] eqn:Hι; last done.
    pose proof Hab as (e & Hbe & Hlt)%heap_authority_base_bounds.
    destruct (Hp ι b e Ht Hbe Hlt Hι) as (x & Hx & Hb0 & He0).
    exists x. split; first done. intros Hd.
    apply (reg_ok_claimed _ _ _ Hreg).
    exists x. split; first done. split; last done. rewrite /re_covers. solve_addr.
  Qed.

  Lemma erasure_observe R C σ lpc lreg lsreg lmem r v b :
    erasure R C σ lpc lreg lsreg lmem →
    lreg !! r = Some v →
    get_tag v.(lw) = true →
    heap_authority_base v.(lw) = Some b →
    match v.(lprov) with
    | Some ι => ∃ x, R !! ι = Some x ∧ (re_status x ≠ ADead → C !! b = Some (Claimed ι))
    | None => C !! b = Some HeapRoot
    end.
  Proof.
    intros Her Hv. apply (reg_word_observe _ _ (shadowtbl σ)); first apply Her.
    by eapply er_reg_words.
  Qed.

  (** The observation by a physical tag of 1: the identifier of a word with
      authority is live or painting, and claims the base. *)
  Lemma reg_phys_observe R C st v w b :
    registry_ok R C st →
    reg_word_ok R C v →
    reg_phys R v w →
    get_tag w = true →
    heap_authority_base v.(lw) = Some b →
    match v.(lprov) with
    | Some ι => ∃ x, R !! ι = Some x ∧ (re_status x = ALive ∨ re_status x = APainting) ∧
                C !! b = Some (Claimed ι)
    | None => C !! b = Some HeapRoot
    end.
  Proof.
    intros Hreg Hok Hw Htw Hab.
    pose proof (reg_phys_tagged _ _ _ Hw Htw) as Heq. subst w.
    pose proof (reg_word_observe _ _ _ _ _ Hreg Hok Htw Hab) as Hobs.
    destruct (lprov v) as [ι|] eqn:Hι; last done.
    destruct Hobs as (x & Hx & Hc).
    assert (re_status x = ALive ∨ re_status x = APainting) as Hs.
    { destruct (re_status x) eqn:Hs; auto; exfalso.
      all: pose proof ((proj2 Hw) ι x (conj Htw (ex_intro _ b Hab)) Hι Hx
                         ltac:(rewrite Hs; by [left|right])) as Hc'.
      all: rewrite Hc' get_tag_clear_tag in Htw; done. }
    exists x. split_and!; try done. apply Hc. destruct Hs as [-> | ->]; done.
  Qed.

  (** *** Subseg *)

  (** A Subseg result keeps the identifier of its source. A tagged result lies
      in the source's bounds, so the source's provenance covers it; an
      identifier-less, tagged, non-empty heap result needs a heap root. The
      closed bounds of a tagged result are within those of its source. *)
  Lemma reg_word_ok_subseg R C st t p g b e a t' a1 a2 π :
    registry_ok R C st →
    reg_word_ok R C (MkLWord (WCap t p g b e a) π) →
    (t' = true → t = true ∧ (b <= a1)%a ∧ (a2 <= e)%a ∧ (a1 <= a2)%a) →
    (t' = true → (a1 < a2)%a → is_heap_address a1 = true → π = None → C !! a1 = Some HeapRoot) →
    reg_word_ok R C (MkLWord (WCap t' p g a1 a2 a) π).
  Proof.
    intros Hreg (Hp & Hauth & Hexec) Ht' Hroot. split_and!.
    - intros ι b' e' Ht Hb Hlt Hι; cbn in *.
      destruct (Ht' Ht) as (-> & Hb1 & He1 & _). simplify_eq.
      destruct (Hp ι b e eq_refl eq_refl ltac:(solve_addr) eq_refl) as (x & Hx & ? & ?).
      exists x. split; first done. cbn in *. split; solve_addr.
    - intros b' Ht Hab; cbn in *. subst t'.
      destruct (Ht' eq_refl) as (-> & Hb1 & He1 & _).
      case_decide as Hlt; last done. destruct (is_heap_address a1) eqn:Hh; last done. simplify_eq.
      destruct π as [ι|]; last by apply Hroot.
      destruct (Hp ι b e eq_refl eq_refl ltac:(solve_addr) eq_refl) as (x & Hx & ? & ?).
      by exists x.
    - intros Ht Hx; cbn in *. subst t'.
      destruct (Ht' eq_refl) as (-> & Hb1 & He1 & Hle).
      destruct (Hexec eq_refl Hx) as [Hπ Havoid]. split; first done.
      intros b' e' [= <- <-]. destruct (Havoid b e eq_refl) as [_ Hy].
      split; first (apply Hy; solve_addr).
      intros y Hy'. apply Hy. solve_addr.
  Qed.

  (** The physical Subseg result is the same copy of the logical result. *)
  Lemma reg_phys_subseg R C st t p g b e a t' a1 a2 π s :
    registry_ok R C st →
    reg_word_ok R C (MkLWord (WCap t p g b e a) π) →
    reg_phys R (MkLWord (WCap t p g b e a) π) (WCap (s && t) p g b e a) →
    (t' = true → t = true ∧ (b <= a1)%a ∧ (a2 <= e)%a ∧ (a1 <= a2)%a) →
    reg_phys R (MkLWord (WCap t' p g a1 a2 a) π) (WCap (s && t') p g a1 a2 a).
  Proof.
    intros Hreg (Hp & _ & _) [Hrel Hq] Ht'; cbn in *.
    (* A tagged result with authority and an identifier comes from a source
       with authority. *)
    assert (∀ ι, has_authority (WCap t' p g a1 a2 a) → π = Some ι →
              has_authority (WCap t p g b e a)) as Hauth.
    { intros ι [Ht [b' Hab] ] Hι. cbn in Ht. subst t' π.
      destruct (Ht' eq_refl) as (-> & Hb1 & He1 & _).
      apply heap_authority_base_memory_cap_bounds in Hab as (e' & [= <- <-] & Hlt & Hh).
      split; first done. exists b. apply heap_authority_base_memory_cap_bounds.
      exists e. split; first done. split; first solve_addr.
      destruct (Hp ι b e eq_refl eq_refl ltac:(solve_addr) eq_refl) as (x & Hx & ? & ?).
      eapply reg_ok_heap; eauto. rewrite /re_covers. solve_addr. }
    destruct s; cbn.
    - split; first by left.
      intros ι x Ha Hι Hx Hqd. exfalso.
      pose proof (Hauth ι Ha Hι) as Has.
      pose proof (Hq ι x Has Hι Hx Hqd) as Heq.
      destruct Has as [Hts _]. cbn in Hts. subst t. done.
    - split; last done. destruct t' eqn:Ht'eq; last by left.
      destruct (Ht' eq_refl) as (-> & Hb1 & He1 & Hle).
      right. split; first done.
      destruct Hrel as [Heq | [_ [Hst | [Hna Hh] ] ] ]; first done.
      + left. destruct Hst as [Hst _]. split; first done. by eexists.
      + right. destruct Hh as [base Hbase].
        assert (is_heap_address b = true) as Hbh.
        { rewrite /heap_cap_base /= in Hbase. by destruct (is_heap_address b). }
        assert (¬ (b < e)%a) as Hnlt.
        { intros Hlt. apply Hna. split; first done. exists b.
          apply heap_authority_base_memory_cap_bounds. eauto. }
        assert (a1 = b) as -> by solve_addr. assert (a2 = b) as -> by solve_addr.
        split.
        * intros [_ [b' Hab] ]. apply heap_authority_base_memory_cap_bounds in Hab as (? & [= <- <-] & ? & _).
          solve_addr.
        * rewrite /heap_cap_base /= Hbh. eauto.
  Qed.

  (** The rebase: a non-executable capability with exactly the range of a
      non-dead identifier. *)
  Lemma reg_word_ok_rebase R C t p g a ι b e γ s :
    R !! ι = Some (b, e, γ, s) → s ≠ ADead → executeAllowed p = false →
    reg_word_ok R C (MkLWord (WCap t p g b e a) (Some ι)).
  Proof.
    intros Hx Hs Hp. split_and!.
    - intros ι' b' e' Ht Hb Hlt Hι; cbn in *. simplify_eq.
      exists (b', e', γ, s). split; first done. cbn. split; solve_addr.
    - intros b' Ht Hab; cbn. exists (b, e, γ, s). done.
    - by apply lword_exec_not_executable.
  Qed.

End erasure.

(** * The split of erasure

    The state interpretation is split into a part shared by the threads and
    a part of the running thread. Each part has its own erasure: the shared
    one for the shared system registers, which exclude MTDC, mstatus, MSHWM
    and MSHWMB, and memory; the one of the thread for its registers, its PC,
    its mtdc word, and the integers of MSHWMB and MSHWM. mstatus is not a
    logical system register of either part: each part pins its own bit,
    MPIE in the shared part and MIE in the part of the thread. Together they
    give today's [erasure], whose logical system registers are the shared
    ones with mtdc, MSHWMB, MSHWM and the mstatus word ([lsregs_join]). *)

(** mstatus is present and holds [mstatus_enc mie mpie]. *)
Definition mstatus_ok (σ : ExecConf) (mie mpie : InterruptStatus) : Prop :=
  sreg σ !! mstatus = Some (WInt (mstatus_enc mie mpie)).

Lemma mstatus_ok_agree σ mie mpie mie' mpie' :
  mstatus_ok σ mie mpie → mstatus_ok σ mie' mpie' → mie = mie' ∧ mpie = mpie'.
Proof.
  rewrite /mstatus_ok. intros H1 H2. rewrite H1 in H2. simplify_eq.
  by apply mstatus_enc_inj.
Qed.

(** The logical system registers of [erasure]: the shared ones, the logical
    mtdc word [vm], the integers [hb] and [h] of MSHWMB and MSHWM, and the
    mstatus word. *)
Definition lsregs_join (lsh : LSReg) (vm : LWord) (hb h : Z) (mie mpie : InterruptStatus)
    : LSReg :=
  <[mstatus := lword_of_word (WInt (mstatus_enc mie mpie))]>
    (<[mtdc := vm]>
       (<[mshwmb := lword_of_word (WInt hb)]> (<[mshwm := lword_of_word (WInt h)]> lsh))).

Lemma lsregs_join_mstatus lsh vm hb h mie mpie :
  lsregs_join lsh vm hb h mie mpie !! mstatus =
    Some (lword_of_word (WInt (mstatus_enc mie mpie))).
Proof. by rewrite /lsregs_join lookup_insert_eq. Qed.

Lemma lsregs_join_mtdc lsh vm hb h mie mpie : lsregs_join lsh vm hb h mie mpie !! mtdc = Some vm.
Proof. by rewrite /lsregs_join lookup_insert_ne // lookup_insert_eq. Qed.

Lemma lsregs_join_mshwmb lsh vm hb h mie mpie :
  lsregs_join lsh vm hb h mie mpie !! mshwmb = Some (lword_of_word (WInt hb)).
Proof.
  by rewrite /lsregs_join (lookup_insert_ne _ mstatus) // (lookup_insert_ne _ mtdc) //
    lookup_insert_eq.
Qed.

Lemma lsregs_join_mshwm lsh vm hb h mie mpie :
  lsregs_join lsh vm hb h mie mpie !! mshwm = Some (lword_of_word (WInt h)).
Proof.
  by rewrite /lsregs_join (lookup_insert_ne _ mstatus) // (lookup_insert_ne _ mtdc) //
    (lookup_insert_ne _ mshwmb) // lookup_insert_eq.
Qed.

Lemma lsregs_join_ne lsh vm hb h mie mpie sr :
  sr ≠ mtdc → sr ≠ mstatus → sr ≠ mshwm → sr ≠ mshwmb →
  lsregs_join lsh vm hb h mie mpie !! sr = lsh !! sr.
Proof. intros H1 H2 H3 H4. by rewrite /lsregs_join !lookup_insert_ne. Qed.

Section erasure_split.
  Context `{MP : MachineParameters}.

  (** The shared part: registry, the shared system registers, memory, and
      MPIE. *)
  Record erasure_sh R C (σ : ExecConf) (lsh : LSReg) (lmem : LMem) (mpie : InterruptStatus)
    : Prop := {
    es_registry : registry_ok R C (shadowtbl σ);
    es_no_mtdc : lsh !! mtdc = None;
    es_no_mstatus : lsh !! mstatus = None;
    es_sregs : lsregs_phys R lsh (sreg σ);
    es_sreg_words sr v : lsh !! sr = Some v → reg_word_ok R C v;
    es_sreg_legal_id sr v : lsh !! sr = Some v → has_authority v.(lw) → v.(lprov) = None;
    es_sreg_pc_ok sr v : is_pc_sreg sr = true → lsh !! sr = Some v → pc_ok v.(lw);
    es_mem_dom : dom lmem = dom (mem σ);
    es_mem_words a v pw : lmem !! a = Some v → mem σ !! a = Some pw → mem_word_ok R C v pw;
    es_mmio : mem_avoids_mmio (mem σ);
    es_heap_mapped : heap_mapped (mem σ);
    es_mstatus : ∃ mie, mstatus_ok σ mie mpie;
    es_no_mshwm : lsh !! mshwm = None;
    es_no_mshwmb : lsh !! mshwmb = None;
  }.

  (** The part of a thread: its registers, its PC, its logical mtdc word
      [vm], MIE, and the values [hb] and [h] of MSHWMB and MSHWM, which the
      physical registers hold. *)
  Record erasure_th R C (σ : ExecConf) (lpc : LWord) (lreg : LReg) (vm : LWord)
      (mie : InterruptStatus) (hb h : Z) : Prop := {
    et_regs : dom (reg σ) = dom lreg ∧ lregs_phys R lreg (reg σ);
    et_cnull v : lreg !! cnull = Some v → v = lnull;
    et_reg_words r v : lreg !! r = Some v → reg_word_ok R C v;
    et_mtdc : ∃ w, sreg σ !! mtdc = Some w ∧ reg_phys R vm w;
    et_mtdc_word : reg_word_ok R C vm;
    et_pc : reg_phys R lpc (pcc σ);
    et_pc_word : reg_word_ok R C lpc;
    et_pc_ok : pc_ok lpc.(lw);
    et_mstatus : ∃ mpie, mstatus_ok σ mie mpie;
    et_hwmb : sreg σ !! mshwmb = Some (WInt hb);
    et_hwm : sreg σ !! mshwm = Some (WInt h);
  }.

  (** The two parts give today's record. *)
  Lemma erasure_join R C σ lpc lreg lsh vm mie mpie hb h lmem :
    erasure_sh R C σ lsh lmem mpie → erasure_th R C σ lpc lreg vm mie hb h →
    erasure R C σ lpc lreg (lsregs_join lsh vm hb h mie mpie) lmem.
  Proof.
    intros Hsh Hth.
    destruct Hsh as [Hreg Hnm Hns Hsr Hsrw Hsrid Hsrpc Hmd Hmw Hmmio Hhm [mie' Hst1] Hnh Hnhb].
    destruct Hth as [Hregs Hcnull Hrw Hmt Hmtw Hpc Hpcw Hpcok [mpie' Hst2] Hhb Hh].
    destruct (mstatus_ok_agree _ _ _ _ _ Hst1 Hst2) as [<- <-].
    constructor; try done.
    - intros sr v. rewrite /lsregs_join.
      destruct (decide (sr = mstatus)) as [->|Hne1].
      { rewrite lookup_insert_eq. intros [=<-]. eexists. split; first exact Hst1.
        apply reg_phys_lword_of_word. }
      rewrite lookup_insert_ne //.
      destruct (decide (sr = mtdc)) as [->|Hne2].
      { rewrite lookup_insert_eq. intros [=<-]. done. }
      rewrite lookup_insert_ne //.
      destruct (decide (sr = mshwmb)) as [->|Hne3].
      { rewrite lookup_insert_eq. intros [=<-]. eexists. split; first exact Hhb.
        apply reg_phys_lword_of_word. }
      rewrite lookup_insert_ne //.
      destruct (decide (sr = mshwm)) as [->|Hne4].
      { rewrite lookup_insert_eq. intros [=<-]. eexists. split; first exact Hh.
        apply reg_phys_lword_of_word. }
      rewrite lookup_insert_ne //. apply Hsr.
    - intros sr v. rewrite /lsregs_join.
      destruct (decide (sr = mstatus)) as [->|Hne1].
      { rewrite lookup_insert_eq. intros [=<-]. apply reg_word_ok_int. }
      rewrite lookup_insert_ne //.
      destruct (decide (sr = mtdc)) as [->|Hne2].
      { rewrite lookup_insert_eq. intros [=<-]. done. }
      rewrite lookup_insert_ne //.
      destruct (decide (sr = mshwmb)) as [->|Hne3].
      { rewrite lookup_insert_eq. intros [=<-]. apply reg_word_ok_int. }
      rewrite lookup_insert_ne //.
      destruct (decide (sr = mshwm)) as [->|Hne4].
      { rewrite lookup_insert_eq. intros [=<-]. apply reg_word_ok_int. }
      rewrite lookup_insert_ne //. eauto.
    - intros sr v Hne. rewrite /lsregs_join.
      destruct (decide (sr = mstatus)) as [->|Hne1].
      { rewrite lookup_insert_eq. intros [=<-] Ha. by inversion Ha. }
      rewrite !(lookup_insert_ne _ mstatus) // (lookup_insert_ne _ mtdc) //.
      destruct (decide (sr = mshwmb)) as [->|Hne3].
      { rewrite lookup_insert_eq. intros [=<-] Ha. by inversion Ha. }
      rewrite lookup_insert_ne //.
      destruct (decide (sr = mshwm)) as [->|Hne4].
      { rewrite lookup_insert_eq. intros [=<-] Ha. by inversion Ha. }
      rewrite lookup_insert_ne //. eauto.
    - intros sr v Hpcs. rewrite /lsregs_join.
      destruct (decide (sr = mstatus)) as [->|Hne1]; first done.
      destruct (decide (sr = mtdc)) as [->|Hne2]; first done.
      destruct (decide (sr = mshwmb)) as [->|Hne3]; first done.
      destruct (decide (sr = mshwm)) as [->|Hne4]; first done.
      rewrite !lookup_insert_ne //. eauto.
  Qed.

  (** And conversely, for shared system registers without MTDC, mstatus,
      MSHWM and MSHWMB. *)
  Lemma erasure_split R C σ lpc lreg lsh vm mie mpie hb h lmem :
    lsh !! mtdc = None → lsh !! mstatus = None →
    lsh !! mshwm = None → lsh !! mshwmb = None →
    erasure R C σ lpc lreg (lsregs_join lsh vm hb h mie mpie) lmem →
    erasure_sh R C σ lsh lmem mpie ∧ erasure_th R C σ lpc lreg vm mie hb h.
  Proof.
    intros Hmtdc Hmst Hnh Hnhb Her.
    assert (mstatus_ok σ mie mpie) as Hok.
    { destruct (er_sregs _ _ _ _ _ _ _ Her mstatus _ (lsregs_join_mstatus _ _ _ _ _ _))
        as (w & Hw & Hrel).
      rewrite /mstatus_ok Hw. f_equal. by apply reg_phys_no_bounds in Hrel. }
    split; constructor; try apply Her; try done; try by eexists.
    - intros sr v Hv. apply (er_sregs _ _ _ _ _ _ _ Her).
      rewrite lsregs_join_ne //; congruence.
    - intros sr v Hv. apply (er_sreg_words _ _ _ _ _ _ _ Her sr).
      rewrite lsregs_join_ne //; congruence.
    - intros sr v Hv. apply (er_sreg_legal_id _ _ _ _ _ _ _ Her sr); first congruence.
      rewrite lsregs_join_ne //; congruence.
    - intros sr v Hpc Hv. apply (er_sreg_pc_ok _ _ _ _ _ _ _ Her sr); first done.
      rewrite lsregs_join_ne //; congruence.
    - apply lsregs_join_mtdc.
    - apply (er_sreg_words _ _ _ _ _ _ _ Her mtdc). apply lsregs_join_mtdc.
    - apply (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her). apply lsregs_join_mshwmb.
    - apply (erasure_lookup_sreg_int _ _ _ _ _ _ _ _ _ Her). apply lsregs_join_mshwm.
  Qed.
End erasure_split.
