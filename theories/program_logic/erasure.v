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
    Load and Store reach those devices only through their dedicated branches. *)
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

  Lemma updatePC_gen_mem φ imm c :
    updatePC_gen φ imm = Some c → mem c.2 = mem φ.
  Proof. rewrite /updatePC_gen. repeat case_match; intros; simplify_eq; done. Qed.

  (* Every instruction preserves the clause: Load and Store reach the shadow
     region and the revoker through their own branches, an ordinary store
     writes a non-MMIO address, and the sweep keeps the memory's domain. *)
  Lemma exec_mem_avoids_mmio i p φ :
    mem_avoids_mmio (mem φ) → mem_avoids_mmio (mem (exec i p φ).2).
  Proof.
    intros Hφ. rewrite /exec.
    destruct (exec_opt i p φ) as [c|] eqn:Hexec; last done.
    destruct i; cbn in Hexec; repeat case_match; simplify_eq; try done.
    all: repeat match goal with
      | H : mbind _ ?x = Some _ |- _ => destruct x eqn:?; cbn in H; try discriminate
      | H : (match ?x with _ => _ end) = Some _ |- _ =>
          destruct x eqn:?; cbn in H; try discriminate
      end.
    all: try (match goal with H : updatePC_gen _ _ = Some _ |- _ =>
                rewrite (updatePC_gen_mem _ _ _ H) end).
    all: try (match goal with H : updatePC _ = Some _ |- _ =>
                rewrite (updatePC_gen_mem _ _ _ H) end).
    all: try (match goal with H : Some _ = Some _ |- _ => injection H as <- end).
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
Proof. by destruct w as [| [] | | ? []]. Qed.

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
Proof. by destruct w as [| [] | | ? []]. Qed.

Lemma memory_cap_bounds_load_word p w :
  memory_cap_bounds (load_word p w) = memory_cap_bounds w.
Proof.
  rewrite /load_word. destruct w as [| [] | | ? []]; repeat case_match; done.
Qed.

Lemma memory_cap_bounds_store_word p w :
  memory_cap_bounds (store_word p w) = memory_cap_bounds w.
Proof. rewrite /store_word. case_match; auto using memory_cap_bounds_clear_tag. Qed.

Lemma memory_cap_bounds_updatePcPerm w :
  memory_cap_bounds (updatePcPerm w) = memory_cap_bounds w.
Proof. by destruct w as [| [] | | ? []]. Qed.

Lemma get_tag_store_word p w : get_tag (store_word p w) = true → get_tag w = true.
Proof.
  rewrite /store_word. case_match; first done. by rewrite get_tag_clear_tag.
Qed.

Lemma load_word_clear_tag p w : load_word p (clear_tag w) = clear_tag (load_word p w).
Proof. rewrite /load_word. destruct w as [| [] | | ? []]; repeat case_match; simplify_eq; done. Qed.

Lemma decodeInstrW_clear_tag `{MachineParameters} w :
  decodeInstrW (clear_tag w) = decodeInstrW w.
Proof. by destruct w as [| [] | | ? []]. Qed.

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

(** ** Registry entries *)

Notation RegEntry := (Addr * Addr * gname * AllocLifecycle)%type.

Definition re_b (x : RegEntry) : Addr := x.1.1.1.
Definition re_e (x : RegEntry) : Addr := x.1.1.2.
Definition re_status (x : RegEntry) : AllocLifecycle := x.2.
Definition re_covers (x : RegEntry) (a : Addr) : Prop := (re_b x <= a < re_e x)%a.
Global Arguments re_b /.
Global Arguments re_e /.
Global Arguments re_status /.

Section erasure.
  Context `{MP : MachineParameters}.
  Implicit Types (R : RegState) (C : gmap Addr AddrClaim) (v : LWord) (w pw : Word).

  (** Provenance: every tagged, non-empty capability with an identifier lies
      in the range of that identifier, which is registered. *)
  Definition lword_prov R v : Prop :=
    ∀ ι b e, get_tag v.(lw) = true → memory_cap_bounds v.(lw) = Some (b, e) → (b < e)%a →
      v.(lprov) = Some ι →
      ∃ x, R !! ι = Some x ∧ (re_b x <= b)%a ∧ (e <= re_e x)%a.

  (** The register clause: a word with authority is not dead if it has an
      identifier, and its base is a heap root otherwise. *)
  Definition reg_authority R C v : Prop :=
    ∀ b, get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b →
      match v.(lprov) with
      | Some ι => ∃ x, R !! ι = Some x ∧ re_status x ≠ ADead
      | None => C !! b = Some HeapRoot
      end.

  Definition reg_word_ok R C v : Prop := lword_prov R v ∧ reg_authority R C v.

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
    (heap_cap_base v.(lw) = None → pw = v.(lw)) ∧
    mem_authority R C v pw.

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

  Record erasure R C (σ : ExecConf) (lreg : LReg) (lmem : LMem) : Prop := {
    er_registry : registry_ok R C (shadowtbl σ);
    er_regs : reg σ = lregs_erase lreg;
    er_cnull v : lreg !! cnull = Some v → v = lnull;
    er_reg_words r v : lreg !! r = Some v → reg_word_ok R C v;
    er_sreg_words sr w : sreg σ !! sr = Some w → reg_word_ok R C (lword_of_word w);
    er_mem_dom : dom lmem = dom (mem σ);
    er_mem_words a v pw : lmem !! a = Some v → mem σ !! a = Some pw → mem_word_ok R C v pw;
    er_mmio : mem_avoids_mmio (mem σ);
  }.

  (** *** Words *)

  Lemma lword_prov_untagged R v : get_tag v.(lw) = false → lword_prov R v.
  Proof. intros Ht ι b e Ht'. congruence. Qed.

  Lemma lword_prov_no_bounds R v : memory_cap_bounds v.(lw) = None → lword_prov R v.
  Proof. intros Hb ι b e _ Hb'. congruence. Qed.

  Lemma lword_prov_no_id R v : v.(lprov) = None → lword_prov R v.
  Proof. intros Hp ι b e _ _ _ Hp'. congruence. Qed.

  Lemma reg_word_ok_int R C z π : reg_word_ok R C (MkLWord (WInt z) π).
  Proof. split; [by apply lword_prov_untagged | intros b Ht; done]. Qed.

  Lemma reg_word_ok_lnull R C : reg_word_ok R C lnull.
  Proof. apply reg_word_ok_int. Qed.

  Lemma reg_word_ok_untagged R C v : get_tag v.(lw) = false → reg_word_ok R C v.
  Proof. intros Ht. split; [by apply lword_prov_untagged | intros b Ht'; congruence]. Qed.

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

  Lemma reg_word_ok_derive R C v w' :
    (memory_cap_bounds w' = memory_cap_bounds v.(lw) ∨ memory_cap_bounds w' = None) →
    (get_tag w' = true → get_tag v.(lw) = true) →
    reg_word_ok R C v → reg_word_ok R C (MkLWord w' v.(lprov)).
  Proof.
    intros Hb Ht [Hprov Hauth]. split; first by apply lword_prov_derive.
    intros b Ht' Hab; cbn in *.
    destruct Hb as [Hb|Hb].
    - apply (Hauth b); first auto. by rewrite -(heap_authority_base_bounds_eq _ _ Hb).
    - by rewrite heap_authority_base_None_bounds in Hab.
  Qed.

  Lemma reg_word_ok_lift R C f v :
    (∀ w, memory_cap_bounds (f w) = memory_cap_bounds w ∨ memory_cap_bounds (f w) = None) →
    (∀ w, get_tag (f w) = true → get_tag w = true) →
    reg_word_ok R C v → reg_word_ok R C (lift_word f v).
  Proof. intros Hb Ht. apply reg_word_ok_derive; auto. Qed.

  Lemma reg_word_ok_lclear_tag R C v : reg_word_ok R C (lclear_tag v).
  Proof. apply reg_word_ok_untagged. apply get_tag_clear_tag. Qed.

  Lemma reg_word_ok_lload_word R C p v : reg_word_ok R C v → reg_word_ok R C (lload_word p v).
  Proof.
    apply reg_word_ok_lift; intros w.
    - left. apply memory_cap_bounds_load_word.
    - by rewrite get_tag_load_word.
  Qed.

  Lemma reg_word_ok_lupdatePcPerm R C v :
    reg_word_ok R C v → reg_word_ok R C (lupdatePcPerm v).
  Proof.
    apply reg_word_ok_lift; intros w.
    - left. apply memory_cap_bounds_updatePcPerm.
    - by rewrite get_tag_updatePcPerm.
  Qed.

  Lemma reg_word_ok_mem R C v : reg_word_ok R C v → mem_word_ok R C v v.(lw).
  Proof.
    intros [Hprov Hauth]. split; first done. split; first by left.
    split; first done.
    intros b Ht Hab. specialize (Hauth b Ht Hab).
    destruct (lprov v) as [ι|]; last done.
    destruct Hauth as (x & Hx & Hs). exists x. split; first done. split; first done.
    intros; congruence.
  Qed.

  Lemma reg_word_ok_lstore_word R C p v :
    reg_word_ok R C v → reg_word_ok R C (lstore_word p v).
  Proof.
    apply reg_word_ok_lift; intros w.
    - left. apply memory_cap_bounds_store_word.
    - apply get_tag_store_word.
  Qed.

  (** A Load: the physical result of the Load filter on the physical copy
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

  Lemma mem_word_ok_load_reg_word R C v pw p pl shadow :
    mem_word_ok R C v pw →
    load_filter shadow p pw = Some pl →
    reg_word_ok R C (MkLWord pl v.(lprov)).
  Proof.
    intros Hok Hpl. pose proof (mem_word_ok_load_word _ _ _ _ _ _ _ Hok Hpl) as Hcases.
    destruct Hok as (Hprov & Hpw & Hnh & Hauth).
    assert (memory_cap_bounds pl = memory_cap_bounds v.(lw)) as Hb.
    { destruct Hcases as [-> | ->];
        rewrite ?memory_cap_bounds_clear_tag memory_cap_bounds_load_word //. }
    split.
    - apply lword_prov_derive; auto.
      destruct Hcases as [-> | ->]; rewrite ?get_tag_clear_tag ?get_tag_load_word //.
    - intros b Ht Hab; cbn in *.
      assert (get_tag pw = true) as Htpw.
      { apply load_filter_cases in Hpl as [-> | (_ & ->)].
        - by rewrite get_tag_load_word in Ht.
        - by rewrite get_tag_clear_tag in Ht. }
      assert (get_tag v.(lw) = true) as Htv.
      { destruct Hpw as [<- | ->]; first done. by rewrite get_tag_clear_tag in Htpw. }
      rewrite (heap_authority_base_bounds_eq _ _ Hb) in Hab.
      specialize (Hauth b Htv Hab).
      destruct (lprov v) as [ι|].
      + destruct Hauth as (x & Hx & _ & Hdead). exists x. split; first done.
        intros Hd. specialize (Hdead Hd). subst pw. by rewrite get_tag_clear_tag in Htpw.
      + by destruct Hauth.
  Qed.

  Lemma mem_word_ok_load_lload_heap R C v pw p pl shadow :
    mem_word_ok R C v pw →
    load_filter shadow p pw = Some pl →
    lload_heap (lload_word p v) (MkLWord pl v.(lprov)).
  Proof.
    intros Hok Hpl. destruct v as [w π]; cbn in *.
    pose proof (mem_word_ok_load_word _ _ _ _ _ _ _ Hok Hpl) as [-> | ->]; first by left.
    destruct (decide (load_word p w = clear_tag (load_word p w))) as [Heq|Hne].
    { left. rewrite /lload_word /lift_word /=. by rewrite -Heq. }
    right. split; last done. rewrite /= is_heap_cap_load_word.
    destruct Hok as (_ & Hpw & Hnh & _).
    destruct (heap_cap_base w) eqn:Hb.
    - by rewrite /is_heap_cap Hb.
    - exfalso. cbn in Hnh. specialize (Hnh Hb). subst pw. cbn in Hpl.
      apply load_filter_cases in Hpl as [Heq | (Hh & _)]; first congruence.
      by rewrite /is_heap_cap Hb in Hh.
  Qed.

  (** *** Registers *)

  Lemma erasure_lookup_reg R C σ lreg lmem r v :
    erasure R C σ lreg lmem → lreg !! r = Some v → reg σ !! r = Some v.(lw).
  Proof. intros Her Hv. by rewrite (er_regs _ _ _ _ _ Her) lookup_lregs_erase Hv. Qed.

  Lemma erasure_regs_incl R C σ lreg lmem regs :
    erasure R C σ lreg lmem → regs ⊆ lreg → lregs_erase regs ⊆ reg σ.
  Proof. intros Her Hincl. rewrite (er_regs _ _ _ _ _ Her). by apply lregs_erase_mono. Qed.

  Lemma erasure_reg_word R C σ lreg lmem r v :
    erasure R C σ lreg lmem → lreg !! r = Some v → reg_word_ok R C v.
  Proof. intros Her. apply Her. Qed.

  Lemma erasure_llookup_reg_word R C σ lreg lmem regs r v :
    erasure R C σ lreg lmem → regs ⊆ lreg → regs !!ₗ r = Some v → reg_word_ok R C v.
  Proof.
    intros Her Hincl Hv. rewrite /llookup_reg in Hv.
    destruct (regs !! r) as [v'|] eqn:Hr; cbn in Hv; last done.
    case_decide; simplify_eq; first apply reg_word_ok_lnull.
    eapply er_reg_words; first done. by eapply lookup_weaken.
  Qed.

  Lemma erasure_lword_of_argument_word R C σ lreg lmem regs arg v :
    erasure R C σ lreg lmem → regs ⊆ lreg → lword_of_argument regs arg = Some v →
    reg_word_ok R C v.
  Proof.
    intros Her Hincl Hv. destruct arg as [z|r]; cbn in Hv.
    - simplify_eq. apply reg_word_ok_int.
    - by eapply erasure_llookup_reg_word.
  Qed.

  (** Writes a register, [cnull] included. *)
  Lemma erasure_linsert_reg R C r sr m st lreg lmem x v :
    erasure R C (r, sr, m, st) lreg lmem →
    reg_word_ok R C v →
    erasure R C (insert_reg x v.(lw) r, sr, m, st) (<[x := v]ₗ> lreg) lmem.
  Proof.
    intros Her Hok. destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio].
    constructor; cbn in *; try done.
    - by rewrite Hregs insert_reg_erase.
    - intros v'. rewrite /linsert_reg.
      destruct (decide (x = cnull)) as [->|Hne].
      + rewrite lookup_insert_eq. by intros [=].
      + rewrite lookup_insert_ne //. apply Hcnull.
    - intros r' v'. rewrite /linsert_reg.
      destruct (decide (x = r')) as [<-|Hne].
      + rewrite lookup_insert_eq. intros [= <-]. case_decide; [apply reg_word_ok_lnull|done].
      + rewrite lookup_insert_ne //. apply Hrw.
  Qed.

  Lemma erasure_insert_reg R C r sr m st lreg lmem x v :
    x ≠ cnull →
    erasure R C (r, sr, m, st) lreg lmem →
    reg_word_ok R C v →
    erasure R C (<[x := v.(lw)]> r, sr, m, st) (<[x := v]> lreg) lmem.
  Proof.
    intros Hx Her Hok. pose proof (erasure_linsert_reg _ _ _ _ _ _ _ _ x v Her Hok) as H.
    by rewrite /insert_reg /linsert_reg !decide_False in H.
  Qed.

  Lemma erasure_insert_sreg R C r sr m st lreg lmem x w :
    erasure R C (r, sr, m, st) lreg lmem →
    reg_word_ok R C (lword_of_word w) →
    erasure R C (r, <[x := w]> sr, m, st) lreg lmem.
  Proof.
    intros Her Hok. destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio].
    constructor; cbn in *; try done.
    intros sr' w'. destruct (decide (x = sr')) as [<-|Hne].
    - rewrite lookup_insert_eq. by intros [= <-].
    - rewrite lookup_insert_ne //. apply Hsrw.
  Qed.

  (** *** Memory *)

  Lemma erasure_lookup_mem R C σ lreg lmem a v :
    erasure R C σ lreg lmem → lmem !! a = Some v →
    ∃ pw, mem σ !! a = Some pw ∧ mem_word_ok R C v pw.
  Proof.
    intros Her Hv.
    assert (is_Some (mem σ !! a)) as [pw Hpw].
    { apply elem_of_dom. rewrite -(er_mem_dom _ _ _ _ _ Her). by apply elem_of_dom_2 in Hv. }
    exists pw. split; first done. by eapply er_mem_words.
  Qed.

  Lemma mem_word_ok_decode R C v pw :
    mem_word_ok R C v pw → decodeInstrW pw = decodeInstrW v.(lw).
  Proof. intros (_ & [-> | ->] & _); [done | apply decodeInstrW_clear_tag]. Qed.

  Lemma erasure_store R C r sr m st lreg lmem a v v' :
    erasure R C (r, sr, m, st) lreg lmem →
    lmem !! a = Some v' →
    reg_word_ok R C v →
    erasure R C (r, sr, <[a := v.(lw)]> m, st) lreg (<[a := v]> lmem).
  Proof.
    intros Her Ha Hok. destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio].
    constructor; cbn in *; try done.
    - rewrite !dom_insert_L. by rewrite Hdom.
    - intros a' v'' pw. destruct (decide (a = a')) as [<-|Hne].
      + rewrite !lookup_insert_eq. intros [= <-] [= <-]. by apply reg_word_ok_mem.
      + rewrite !lookup_insert_ne //. apply Hmw.
    - assert (is_Some (m !! a)) as [pw Hpw].
      { apply elem_of_dom. rewrite -Hdom. by apply elem_of_dom_2 in Ha. }
      by eapply mem_avoids_mmio_update.
  Qed.

  (** *** Shadow stores *)

  (** A shadow store keeps erasure when the stored bit is the old one, or when
      the cell is unclaimed or claimed by a painting allocation, and it is not
      a heap root. *)
  Definition shadow_store_ok R C (shadow : ShadowTbl) (a : Addr) (s : AllocStatus) : Prop :=
    shadow !! a = Some s ∨
    C !! a = Some Unclaimed ∨
    (∃ ι x, C !! a = Some (Claimed ι) ∧ R !! ι = Some x ∧ re_status x = APainting).

  Lemma erasure_shadow_store R C r sr m st lreg lmem a s :
    erasure R C (r, sr, m, st) lreg lmem →
    is_Some (st !! a) →
    shadow_store_ok R C st a s →
    erasure R C (r, sr, m, <[a := s]> st) lreg lmem.
  Proof.
    intros Her Hst Hok. destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio].
    constructor; cbn in *; try done.
    destruct Hreg as [Hheap Hlive Hquar Hcdom Hclaimed Hroot Hshadow].
    (* The cells whose shadow bit matters are those of live or quarantined
       identifiers, and heap roots. None of them is [a], unless [s] is its
       old bit. *)
    assert (∀ a', a' = a → st !! a' = Some s ∨
       ((∀ ι x, R !! ι = Some x → re_covers x a' →
                re_status x ≠ ALive ∧ re_status x ≠ AQuar) ∧
        C !! a' ≠ Some HeapRoot)) as Hcell.
    { intros a' ->. destruct Hok as [Hs | [Hun | (ι & x & Hcl & Hx & Hpaint)]]; first by left.
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
      + rewrite lookup_insert_eq. destruct (Hcell a eq_refl) as [Hs'|[Hc _]].
        * by rewrite -(Hlive _ _ _ Hx Hs Hcov) Hs'.
        * exfalso. by destruct (Hc _ _ Hx Hcov).
      + rewrite lookup_insert_ne //. eauto.
    - intros ι x a' Hx Hs Hcov. destruct (decide (a = a')) as [<-|Hne].
      + rewrite lookup_insert_eq. destruct (Hcell a eq_refl) as [Hs'|[Hc _]].
        * by rewrite -(Hquar _ _ _ Hx Hs Hcov) Hs'.
        * exfalso. by destruct (Hc _ _ Hx Hcov).
      + rewrite lookup_insert_ne //. eauto.
    - intros a' Hr. destruct (decide (a = a')) as [<-|Hne].
      + rewrite lookup_insert_eq. destruct (Hcell a eq_refl) as [Hs'|[_ Hc]].
        * by rewrite -(Hroot _ Hr) Hs'.
        * done.
      + rewrite lookup_insert_ne //. eauto.
    - intros a' Ha'. destruct (decide (a = a')) as [<-|Hne].
      + by rewrite lookup_insert_eq.
      + rewrite lookup_insert_ne //. eauto.
  Qed.

  (** *** Registry transitions *)

  (** A status step between non-dead statuses, out of [ALive] and into
      [AQuar] only with the whole range painted. *)
  Lemma erasure_reg_step R C σ lreg lmem ι b e γ s s' :
    erasure R C σ lreg lmem →
    R !! ι = Some (b, e, γ, s) →
    s ≠ ADead → s' ≠ ADead → s' ≠ ALive →
    (s' = AQuar → ∀ a, (b <= a < e)%a → shadowtbl σ !! a = Some ShadowQuarantined) →
    erasure (<[ι := (b, e, γ, s')]> R) C σ lreg lmem.
  Proof.
    intros Her HR Hs Hs' Hs'live Hquar'.
    destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio].
    destruct Hreg as [Hheap Hlive Hquar Hcdom Hclaimed Hroot Hshadow].
    (* Lookups in the new registry *)
    assert (∀ ι' x', <[ι := (b, e, γ, s')]> R !! ι' = Some x' →
      (ι' = ι ∧ x' = (b, e, γ, s')) ∨ (ι' ≠ ι ∧ R !! ι' = Some x')) as Hlook.
    { intros ι' x'. destruct (decide (ι = ι')) as [<-|Hne].
      - rewrite lookup_insert_eq. intros [= <-]. by left.
      - rewrite lookup_insert_ne //. by right. }
    assert (∀ ι' x, R !! ι' = Some x → ∃ x', <[ι := (b, e, γ, s')]> R !! ι' = Some x' ∧
      re_b x' = re_b x ∧ re_e x' = re_e x ∧
      (ι' ≠ ι → x' = x) ∧ (re_status x' = ADead ↔ re_status x = ADead)) as Hlook'.
    { intros ι' x Hx. destruct (decide (ι = ι')) as [<-|Hne].
      - rewrite lookup_insert_eq. rewrite HR in Hx. simplify_eq.
        eexists. split; first done. cbn. naive_solver.
      - rewrite lookup_insert_ne //. eexists. split; first done. naive_solver. }
    assert (∀ v, lword_prov R v → lword_prov (<[ι := (b, e, γ, s')]> R) v) as Hprov.
    { intros v Hp ι' b' e' Ht Hb Hlt Hι.
      destruct (Hp ι' b' e' Ht Hb Hlt Hι) as (x & Hx & Hb1 & He1).
      destruct (Hlook' _ _ Hx) as (x' & Hx' & Hb' & He' & _).
      exists x'. by rewrite Hb' He'. }
    constructor; cbn; try done.
    - constructor; try done.
      + intros ι' x a Hx Hcov. destruct (Hlook _ _ Hx) as [[-> ->]|[_ Hx']].
        * eapply (Hheap ι); eauto.
        * eauto.
      + intros ι' x a Hx Hst Hcov. destruct (Hlook _ _ Hx) as [[-> ->]|[_ Hx']].
        * by cbn in Hst.
        * eauto.
      + intros ι' x a Hx Hst Hcov. destruct (Hlook _ _ Hx) as [[-> ->]|[_ Hx']].
        * apply Hquar'; first done. apply Hcov.
        * eauto.
      + intros a ι'. rewrite Hclaimed. split.
        * intros (x & Hx & Hcov & Hd). destruct (Hlook' _ _ Hx) as (x' & Hx' & Hb & He & _ & Hd').
          exists x'. split; first done. split; first by rewrite /re_covers Hb He. by rewrite Hd'.
        * intros (x' & Hx' & Hcov & Hd). destruct (Hlook _ _ Hx') as [[-> ->]|[Hne Hx]].
          -- exists (b, e, γ, s). split; first done. split; first done. done.
          -- exists x'. eauto.
    - intros r v Hv. destruct (Hrw r v Hv) as [Hp Hauth]. split; first by apply Hprov.
      intros b' Ht Hab. specialize (Hauth b' Ht Hab).
      destruct (lprov v) as [ι'|]; last done.
      destruct Hauth as (x & Hx & Hd). destruct (Hlook' _ _ Hx) as (x' & Hx' & _ & _ & _ & Hd').
      exists x'. split; first done. by rewrite Hd'.
    - intros sr w Hw. destruct (Hsrw sr w Hw) as [Hp Hauth]. split; first by apply Hprov.
      intros b' Ht Hab. by specialize (Hauth b' Ht Hab).
    - intros a v pw Hv Hpw. destruct (Hmw a v pw Hv Hpw) as (Hp & Hrel & Hnh & Hauth).
      split; first by apply Hprov. split; first done. split; first done.
      intros b' Ht Hab. specialize (Hauth b' Ht Hab).
      destruct (lprov v) as [ι'|]; last done.
      destruct Hauth as (x & Hx & Hl & Hd).
      destruct (decide (ι = ι')) as [<-|Hne].
      + rewrite lookup_insert_eq. eexists. split; first done. cbn.
        split; intros; done.
      + rewrite lookup_insert_ne //. eauto.
  Qed.

  (** *** Allocation *)

  Lemma lword_prov_fresh R v ι b e :
    lword_prov R v → R !! ι = None → v.(lprov) = Some ι →
    get_tag v.(lw) = true → memory_cap_bounds v.(lw) = Some (b, e) → (b < e)%a → False.
  Proof. intros Hp HR Hι Ht Hb Hlt. destruct (Hp ι b e Ht Hb Hlt Hι) as (x & Hx & _). congruence. Qed.

  Lemma heap_authority_base_bounds `{HeapRegion} w b :
    heap_authority_base w = Some b → ∃ e, memory_cap_bounds w = Some (b, e) ∧ (b < e)%a.
  Proof. intros Hb. apply heap_authority_base_memory_cap_bounds in Hb as (e & ? & ? & _). eauto. Qed.

  (** Allocation of a fresh identifier over unclaimed, unpainted cells. *)
  Lemma erasure_alloc R C C' σ lreg lmem ι b e γ :
    erasure R C σ lreg lmem →
    R !! ι = None →
    (∀ a, (b <= a < e)%a → C !! a = Some Unclaimed ∧ shadowtbl σ !! a = Some ShadowLive) →
    (∀ a, C' !! a = if decide ((b <= a < e)%a) then Some (Claimed ι) else C !! a) →
    erasure (<[ι := (b, e, γ, ALive)]> R) C' σ lreg lmem.
  Proof.
    intros Her HR Hcells HC'.
    destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio].
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
    - intros r v Hv. destruct (Hrw r v Hv) as [Hp Hauth]. split; first by apply Hprov.
      intros b' Ht Hab. pose proof (Hnotι v b' Hp Ht Hab) as Hne. specialize (Hauth b' Ht Hab).
      destruct (lprov v) as [ι'|]; last by apply Hroot'.
      destruct Hauth as (x & Hx & Hd). exists x. rewrite HR'ne //. congruence.
    - intros sr w Hw. destruct (Hsrw sr w Hw) as [Hp Hauth]. split; first by apply Hprov.
      intros b' Ht Hab. apply Hroot'. by apply (Hauth b' Ht Hab).
    - intros a v pw Hv Hpw. destruct (Hmw a v pw Hv Hpw) as (Hp & Hrel & Hnh & Hauth).
      split; first by apply Hprov. split; first done. split; first done.
      intros b' Ht Hab. pose proof (Hnotι v b' Hp Ht Hab) as Hne. specialize (Hauth b' Ht Hab).
      destruct (lprov v) as [ι'|].
      + destruct Hauth as (x & Hx & Hl & Hd). exists x. rewrite HR'ne //. congruence.
      + destruct Hauth. split; first done. by apply Hroot'.
  Qed.

  (** *** The revoker *)

  (** The sweep kills the identifiers of [K]: they are quarantined, so their
      ranges are painted and the sweep untags their memory words, and no
      register holds one of their words with authority. *)
  Lemma erasure_revoke R R' C C' r sr m st lreg lmem (K : gset AId) :
    erasure R C (r, sr, m, st) lreg lmem →
    (∀ ι, ι ∈ K → ∃ x, R !! ι = Some x ∧ re_status x = AQuar) →
    (∀ x v ι b, lreg !! x = Some v → get_tag v.(lw) = true →
       heap_authority_base v.(lw) = Some b → v.(lprov) = Some ι → ι ∉ K) →
    (∀ ι, R' !! ι = (λ x : RegEntry, if decide (ι ∈ K) then (x.1, ADead) else x) <$> R !! ι) →
    (∀ a, C' !! a = (λ c, match c with
                          | Claimed ι => if decide (ι ∈ K) then Unclaimed else c
                          | _ => c end) <$> C !! a) →
    erasure R' C' (r, sr, sweep_mem st m, st) lreg lmem.
  Proof.
    intros Her HK Hregs_clean HR' HC'.
    destruct Her as [Hreg Hregs Hcnull Hrw Hsrw Hdom Hmw Hmmio]; cbn in *.
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
    - intros x v Hv. destruct (Hrw x v Hv) as [Hp Hauth]. split; first by apply Hprov.
      intros b Ht Hab. pose proof (Hregs_clean x v) as Hclean. specialize (Hauth b Ht Hab).
      destruct (lprov v) as [ι|] eqn:Hι; last by apply Hroot'.
      destruct Hauth as (x0 & Hx0 & Hd). destruct (HR'r _ _ Hx0) as (x' & Hx' & _ & _ & Hs').
      exists x'. split; first done. rewrite Hs' decide_False //. eapply Hclean; eauto.
    - intros sr' w Hw. destruct (Hsrw sr' w Hw) as [Hp Hauth]. split; first by apply Hprov.
      intros b Ht Hab. apply Hroot'. by apply (Hauth b Ht Hab).
    - by rewrite dom_sweep_mem.
    - intros a v pw' Hv Hpw'. rewrite lookup_sweep_mem in Hpw'.
      apply fmap_Some in Hpw' as (pw & Hpw & ->).
      destruct (Hmw a v pw Hv Hpw) as (Hp & Hrel & Hnh & Hauth).
      assert (memory_cap_bounds pw = memory_cap_bounds v.(lw)) as Hbpw.
      { destruct Hrel as [-> | ->]; rewrite ?memory_cap_bounds_clear_tag //. }
      split; first by apply Hprov. split.
      { destruct (sweep_word_cases st pw) as [-> | ->]; first done.
        destruct Hrel as [-> | ->]; rewrite ?clear_tag_idempotent; auto. }
      split.
      { intros Hn. rewrite sweep_word_nonheap; first by apply Hnh.
        by rewrite (heap_cap_base_bounds_eq _ _ Hbpw). }
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
      destruct Hok as (Hp & Hrel & Hnh & Hauth). specialize (Hauth b Ht Hab).
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
    (∀ b, get_tag v.(lw) = true → heap_authority_base v.(lw) = Some b →
          pw = v.(lw) ∧ st !! b = Some ShadowLive) →
    pl = load_word p v.(lw).
  Proof.
    intros Hreg Hok Hpl Hside Hauth.
    pose proof (mem_word_ok_load_word _ _ _ _ _ _ _ Hok Hpl) as Hcases.
    destruct Hok as (Hp & Hrel & Hnh & _).
    destruct (get_tag v.(lw)) eqn:Ht.
    - destruct (Hside Ht) as [[_ (b & Hab)] | Hnone].
      + destruct (Hauth b eq_refl Hab) as [-> Hsb].
        assert (heap_cap_base v.(lw) = Some b) as Hhb.
        { by apply heap_authority_base_heap_cap_base. }
        rewrite /load_filter Hhb Hsb in Hpl. by simplify_eq.
      + rewrite (Hnh Hnone) /load_filter Hnone in Hpl. by simplify_eq.
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
    intros b Ht Hab. destruct Hok as (Hp & _ & _ & Hauth). specialize (Hauth b Ht Hab).
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
    intros b Ht Hab. destruct Hok as (_ & _ & _ & Hauth). specialize (Hauth b Ht Hab).
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

  Lemma erasure_observe R C σ lreg lmem r v b :
    erasure R C σ lreg lmem →
    lreg !! r = Some v →
    get_tag v.(lw) = true →
    heap_authority_base v.(lw) = Some b →
    match v.(lprov) with
    | Some ι => ∃ x, R !! ι = Some x ∧ re_status x ≠ ADead ∧ C !! b = Some (Claimed ι)
    | None => C !! b = Some HeapRoot
    end.
  Proof.
    intros Her Hv Ht Hab. destruct (er_reg_words _ _ _ _ _ Her r v Hv) as [Hp Hauth].
    specialize (Hauth b Ht Hab). destruct (lprov v) as [ι|] eqn:Hι; last done.
    destruct Hauth as (x & Hx & Hd). exists x. do 2 (split; first done).
    pose proof Hab as (e & Hbe & Hlt)%heap_authority_base_bounds.
    destruct (Hp ι b e Ht Hbe Hlt Hι) as (x0 & Hx0 & Hb0 & He0). rewrite Hx in Hx0. simplify_eq.
    apply (reg_ok_claimed _ _ _ (er_registry _ _ _ _ _ Her)).
    exists x0. split; first done. split; last done. rewrite /re_covers. solve_addr.
  Qed.

  (** *** Subseg *)

  (** A Subseg result keeps the identifier of its source. A tagged result lies
      in the source's bounds, so the source's provenance covers it; an
      identifier-less, tagged, non-empty heap result needs a heap root. *)
  Lemma reg_word_ok_subseg R C st t p g b e a t' a1 a2 π :
    registry_ok R C st →
    reg_word_ok R C (MkLWord (WCap t p g b e a) π) →
    (t' = true → t = true ∧ (b <= a1)%a ∧ (a2 <= e)%a) →
    (t' = true → (a1 < a2)%a → is_heap_address a1 = true → π = None → C !! a1 = Some HeapRoot) →
    reg_word_ok R C (MkLWord (WCap t' p g a1 a2 a) π).
  Proof.
    intros Hreg [Hp Hauth] Ht' Hroot. split.
    - intros ι b' e' Ht Hb Hlt Hι; cbn in *.
      destruct (Ht' Ht) as (-> & Hb1 & He1). simplify_eq.
      destruct (Hp ι b e eq_refl eq_refl ltac:(solve_addr) eq_refl) as (x & Hx & ? & ?).
      exists x. split; first done. cbn in *. split; solve_addr.
    - intros b' Ht Hab; cbn in *. subst t'.
      destruct (Ht' eq_refl) as (-> & Hb1 & He1).
      case_decide as Hlt; last done. destruct (is_heap_address a1) eqn:Hh; last done. simplify_eq.
      destruct π as [ι|]; last by apply Hroot.
      destruct (Hp ι b e eq_refl eq_refl ltac:(solve_addr) eq_refl) as (x & Hx & ? & ?).
      (* The source has authority: its base is in the heap, as [ι]'s range. *)
      assert (heap_authority_base (WCap true p g b e a) = Some b) as Hsrc.
      { apply heap_authority_base_memory_cap_bounds. exists e. split; first done.
        split; first solve_addr. eapply reg_ok_heap; eauto. rewrite /re_covers. cbn in *. solve_addr. }
      destruct (Hauth b eq_refl Hsrc) as (x' & Hx' & Hd). eauto.
  Qed.

  (** The rebase: a capability with exactly the range of a non-dead
      identifier. *)
  Lemma reg_word_ok_rebase R C t p g a ι b e γ s :
    R !! ι = Some (b, e, γ, s) → s ≠ ADead →
    reg_word_ok R C (MkLWord (WCap t p g b e a) (Some ι)).
  Proof.
    intros Hx Hs. split.
    - intros ι' b' e' Ht Hb Hlt Hι; cbn in *. simplify_eq.
      exists (b', e', γ, s). split; first done. cbn. split; solve_addr.
    - intros b' Ht Hab; cbn. exists (b, e, γ, s). done.
  Qed.

End erasure.
