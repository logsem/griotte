From iris.proofmode Require Import proofmode environments spec_patterns.
From griotte Require Export rules_base.

(** * The exact cause of a fault

    Trap entry writes [trap_cause σ] to mcause, computed from the physical
    state. [lcause] computes it from the logical view: the logical PC, the
    logical registers and the logical memory, with the shadow table of a
    heap whose every address has an entry. Under erasure, which covers the
    heap with memory ([er_heap_mapped]), the two agree
    ([erasure_trap_cause]).

    A fault site that owns the code points-to, the registers that the
    instruction reads and, for an access past the capability checks, the
    points-to of the effective address, computes the cause from these
    fragments ([lcause_frag]), and hands it to trap entry with
    [wp_trap_cause]. A fragment cannot tell an absent address from one that
    it does not own, so the access-fault causes are excluded
    ([lcause_known]). *)

Section trap_cause.
  Context `{MP : MachineParameters}.

  (** * The logical cause *)

  (** A shadow table with an entry at every heap address. *)
  Definition heap_shadow : ShadowTbl := gset_to_gmap ShadowLive heap_addresses.

  Lemma heap_shadow_lookup a :
    is_heap_address a = true → is_Some (heap_shadow !! a).
  Proof.
    intros Ha. rewrite /heap_shadow lookup_gset_to_gmap option_guard_True; first by eexists.
    by apply elem_of_heap_addresses.
  Qed.

  (** The logical view as a configuration: the logical words without their
      identifiers. [trap_cause] reads no system register. *)
  Definition lview (lpc : LWord) (lregs : LReg) (lm : LMem) : ExecConf :=
    (lpc.(lw), lw <$> lregs, ∅, lw <$> lm, heap_shadow).

  (** The logical cause of a fault at the PC [lpc], from the logical
      registers [lregs] and the logical memory [lm]. *)
  Definition lcause (lpc : LWord) (lregs : LReg) (lm : LMem) : Z :=
    trap_cause (lview lpc lregs lm).

  (** * An agreement relation between two configurations *)

  (** A physical register word is the logical one, or its untagged copy; in
      the latter case a tagged logical capability addresses heap memory only
      (it is stale, or has no authority and so empty bounds). *)
  Definition word_agree (x y : Word) : Prop :=
    y = x ∨
    (y = clear_tag x ∧
     ∀ p g b e a ea, x = WCap true p g b e a → withinBounds b e ea = true →
       is_heap_address ea = true).

  (** Memory words agree on what the causes read: the decoded instruction and
      the heap base. *)
  Definition mem_agree (x y : Word) : Prop :=
    decodeInstrW x = decodeInstrW y ∧ heap_cap_base x = heap_cap_base y.

  Record cause_rel (φl φp : ExecConf) : Prop := {
    cr_pc : pcc φl = pcc φp;
    cr_reg r : option_Forall2 word_agree (reg φl !! r) (reg φp !! r);
    cr_mem a : option_Forall2 mem_agree (mem φl !! a) (mem φp !! a);
    cr_shadow_l a : is_heap_address a = true → is_Some (shadowtbl φl !! a);
    cr_shadow_p a : is_heap_address a = true → is_Some (shadowtbl φp !! a);
    cr_heap_mapped : heap_mapped (mem φp);
  }.

  Lemma heap_not_shadow a : is_heap_address a = true → is_shadow_address a = false.
  Proof.
    intros Ha. destruct (is_shadow_address a) eqn:Hs; last done. exfalso.
    apply (heap_shadow_disjoint a); apply elem_of_finz_seq_between;
      by apply withinBounds_true_iff.
  Qed.

  Lemma heap_not_revoker a : is_heap_address a = true → is_revoker_address a = false.
  Proof.
    intros Ha. destruct (is_revoker_address a) eqn:Hr; last done.
    apply is_revoker_address_spec in Hr as ->.
    by rewrite revoker_not_heap_address in Ha.
  Qed.

  Lemma shadow_to_heap_heap s a : shadow_to_heap s = Some a → is_heap_address a = true.
  Proof. intros Hs. by destruct (shadow_to_heap_bounds _ _ Hs). Qed.

  Lemma heap_cap_base_heap w base :
    heap_cap_base w = Some base → is_heap_address base = true.
  Proof.
    rewrite /heap_cap_base. destruct (memory_cap_base w) as [f|]; last done.
    destruct (is_heap_address f) eqn:Hh; last done. by intros [= <-].
  Qed.

  Lemma lookup_reg_rel φl φp r :
    cause_rel φl φp → option_Forall2 word_agree (reg φl !!ᵣ r) (reg φp !!ᵣ r).
  Proof.
    intros Hrel. rewrite /lookup_reg.
    destruct (cr_reg _ _ Hrel r) as [x y Hxy|]; cbn; constructor.
    case_decide; [by left | done].
  Qed.

  Lemma word_of_argument_rel φl φp ρ :
    cause_rel φl φp →
    option_Forall2 word_agree (word_of_argument (reg φl) ρ) (word_of_argument (reg φp) ρ).
  Proof.
    intros Hrel. destruct ρ as [z|r]; cbn; last by apply lookup_reg_rel.
    constructor. by left.
  Qed.

  (** Under the agreement, a heap address read logically is mapped there. *)
  Lemma rel_mem_mapped φl φp ea :
    cause_rel φl φp → is_heap_address ea = true → is_Some (mem φl !! ea).
  Proof.
    intros Hrel Hea. pose proof (cr_mem _ _ Hrel ea) as Hm.
    destruct (heap_mapped_lookup _ _ (cr_heap_mapped _ _ Hrel) Hea) as [? Hp].
    rewrite Hp in Hm. inversion Hm. eauto.
  Qed.

  (** ** Loads *)

  Lemma load_cause_rel φl φp src imm :
    cause_rel φl φp → load_cause φl src imm = load_cause φp src imm.
  Proof.
    intros Hrel. rewrite /load_cause.
    destruct (lookup_reg_rel _ _ src Hrel) as [x y [-> | [-> Hheap]] |]; [| | done].
    - (* Exact copy: the same branches; memory agrees on the heap base, and
         both shadow tables have an entry at every heap address. *)
      destruct x as [| [[] p g b e a | ] | | ]; try done.
      destruct (a + imm)%a as [ea|]; last done.
      destruct (readAllowed p && withinBounds b e ea); last done.
      destruct (is_shadow_address ea).
      { destruct (shadow_to_heap ea) as [ha|] eqn:Hha; last done.
        pose proof (shadow_to_heap_heap _ _ Hha) as Hh.
        by destruct (cr_shadow_l _ _ Hrel ha Hh) as [? ->],
          (cr_shadow_p _ _ Hrel ha Hh) as [? ->]. }
      destruct (is_revoker_address ea); first done.
      destruct (cr_mem _ _ Hrel ea) as [x' y' [_ Hb]|]; last done.
      rewrite Hb. destruct (heap_cap_base y') as [base|] eqn:Hbase; last done.
      pose proof (heap_cap_base_heap _ _ Hbase) as Hh.
      by destruct (cr_shadow_l _ _ Hrel base Hh) as [? ->],
        (cr_shadow_p _ _ Hrel base Hh) as [? ->].
    - (* Untagged physical copy: the physical cause is 28, and so is the
         logical one, since a stale capability reads mapped heap memory whose
         loaded heap base has a shadow entry. *)
      destruct x as [| [[] p g b e a | ] | | ]; try done; cbn.
      destruct (a + imm)%a as [ea|]; last done.
      destruct (readAllowed p && withinBounds b e ea) eqn:Hrw; last done.
      apply andb_true_iff in Hrw as [_ Hwb].
      pose proof (Hheap p g b e a ea eq_refl Hwb) as Hea.
      rewrite (heap_not_shadow _ Hea) (heap_not_revoker _ Hea).
      destruct (rel_mem_mapped _ _ ea Hrel Hea) as [x' ->].
      destruct (heap_cap_base x') as [base|] eqn:Hbase; last done.
      by destruct (cr_shadow_l _ _ Hrel base (heap_cap_base_heap _ _ Hbase)) as [? ->].
  Qed.

  (** ** Stores *)

  Lemma store_cause_rel φl φp dst ρ imm :
    cause_rel φl φp → store_cause φl dst ρ imm = store_cause φp dst ρ imm.
  Proof.
    intros Hrel. rewrite /store_cause.
    destruct (word_of_argument_rel _ _ ρ Hrel) as [t t' Ht|]; last done.
    destruct (lookup_reg_rel _ _ dst Hrel) as [x y [-> | [-> Hheap]] |]; [| | done].
    - (* Exact copy: the stored words have the same shape, memory the same
         domain. *)
      destruct x as [| [[] p g b e a | ] | | ]; try done.
      destruct (a + imm)%a as [ea|]; last done.
      destruct (writeAllowed p && withinBounds b e ea); last done.
      destruct (is_shadow_address ea).
      { destruct Ht as [-> | [-> _]]; first done. by destruct t as [| [] | | ? []]. }
      destruct (is_revoker_address ea); first done.
      by destruct (cr_mem _ _ Hrel ea).
    - (* Untagged physical copy: a stale capability writes mapped heap
         memory. *)
      destruct x as [| [[] p g b e a | ] | | ]; try done; cbn.
      destruct (a + imm)%a as [ea|]; last done.
      destruct (writeAllowed p && withinBounds b e ea) eqn:Hrw; last done.
      apply andb_true_iff in Hrw as [_ Hwb].
      pose proof (Hheap p g b e a ea eq_refl Hwb) as Hea.
      rewrite (heap_not_shadow _ Hea) (heap_not_revoker _ Hea).
      by destruct (rel_mem_mapped _ _ ea Hrel Hea) as [x' ->].
  Qed.

  (** ** Every fault class *)

  Lemma instr_cause_rel i φl φp :
    cause_rel φl φp → instr_cause i φl = instr_cause i φp.
  Proof.
    intros Hrel. destruct i; cbn; try done.
    - by apply load_cause_rel.
    - by apply store_cause_rel.
  Qed.

  (** Fetch faults (PC checks, unmapped PC address), then the decoded
      instruction's cause. *)
  Lemma trap_cause_rel φl φp : cause_rel φl φp → trap_cause φl = trap_cause φp.
  Proof.
    intros Hrel. rewrite /trap_cause (cr_pc _ _ Hrel).
    destruct (pcc φp) as [| [[] p g b e a | ] | | ]; try done.
    destruct (isCorrectPCb _); last done.
    destruct (cr_mem _ _ Hrel a) as [x y [Hdec _]|]; last done.
    rewrite Hdec. by apply instr_cause_rel.
  Qed.

  (** * Erasure gives the agreement *)

  (** The register clause: an untagged copy of a tagged capability is the
      copy of a stale capability, whose in-bounds addresses its registered
      range covers, or of a word without authority, whose bounds are
      empty. *)
  Lemma reg_phys_word_agree R C st v w :
    registry_ok R C st → reg_word_ok R C v → reg_phys R v w → word_agree v.(lw) w.
  Proof.
    intros Hreg Hok [[-> | [-> Hstrip]] _]; first by left.
    right. split; first done.
    intros p g b e a ea Hv Hwb.
    pose proof Hwb as Hwb'. apply withinBounds_true_iff in Hwb'.
    destruct Hstrip as [[(ι & x & Hι & Hx & _) _] | [Hna [b' Hhb]]].
    - destruct Hok as (Hprov & _ & _).
      destruct (Hprov ι b e) as (x' & Hx' & Hb & He);
        [by rewrite Hv | by rewrite Hv | solve_addr | done |].
      eapply (reg_ok_heap _ _ _ Hreg); first exact Hx'.
      rewrite /re_covers. solve_addr.
    - exfalso. apply Hna. rewrite Hv. split; first done. exists b'.
      apply heap_authority_base_memory_cap_bounds.
      rewrite Hv in Hhb. pose proof (heap_cap_base_heap _ _ Hhb) as Hh.
      rewrite /heap_cap_base /= in Hhb. destruct (is_heap_address b) eqn:Hbh; last done.
      simplify_eq. exists e. split_and!; [done | solve_addr | done].
  Qed.

  Lemma mem_word_ok_agree R C v pw : mem_word_ok R C v pw → mem_agree v.(lw) pw.
  Proof.
    intros Hok. split; first by rewrite (mem_word_ok_decode _ _ _ _ Hok).
    destruct Hok as (_ & [-> | ->] & _); first done.
    by rewrite heap_cap_base_clear_tag.
  Qed.

  Lemma erasure_cause_rel R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem →
    cause_rel (lview lpc lreg lmem) σ.
  Proof.
    intros Her. constructor; cbn.
    - symmetry. by eapply erasure_pc_exact.
    - intros r. rewrite lookup_fmap.
      destruct (lreg !! r) as [v|] eqn:Hv; cbn.
      + destruct (erasure_lookup_reg _ _ _ _ _ _ _ _ _ Her Hv) as (w & -> & Hw).
        constructor. eapply reg_phys_word_agree; [apply Her | by eapply er_reg_words | done].
      + destruct (reg σ !! r) eqn:Hr; last constructor. exfalso.
        apply elem_of_dom_2 in Hr. rewrite (proj1 (er_regs _ _ _ _ _ _ _ Her)) in Hr.
        apply elem_of_dom in Hr as [? ?]. congruence.
    - intros a. rewrite lookup_fmap.
      destruct (lmem !! a) as [v|] eqn:Hv; cbn.
      + destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hv) as (pw & -> & Hok).
        constructor. by eapply mem_word_ok_agree.
      + destruct (mem σ !! a) eqn:Hm; last constructor. exfalso.
        apply elem_of_dom_2 in Hm. rewrite -(er_mem_dom _ _ _ _ _ _ _ Her) in Hm.
        apply elem_of_dom in Hm as [? ?]. congruence.
    - apply heap_shadow_lookup.
    - apply (reg_ok_shadow _ _ _ (er_registry _ _ _ _ _ _ _ Her)).
    - apply (er_heap_mapped _ _ _ _ _ _ _ Her).
  Qed.

  (** Agreement: under erasure, which covers the heap with memory, the
      logical cause is the physical one, for every fault class (fetch,
      illegal instruction, load, store, every other CHERI fault). *)
  Theorem erasure_trap_cause R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem →
    trap_cause σ = lcause lpc lreg lmem.
  Proof. intros Her. symmetry. apply trap_cause_rel. by eapply erasure_cause_rel. Qed.

  (** * The cause from fragments *)

  (** The cause is known from the registers [lregs] and the memory [lm]:
      they contain the registers that the instruction at the PC reads, and
      the cause is not an access fault, which an address that the fragment
      misses would give. *)
  Definition lcause_known (lpc : LWord) (lregs : LReg) (lm : LMem) : Prop :=
    (∀ p g b e a wi, lpc.(lw) = WCap true p g b e a → lm !! a = Some wi →
       regs_of (decodeInstrW wi.(lw)) ⊆ dom lregs) ∧
    lcause lpc lregs lm ≠ MCAUSE_INST_ACCESS_FAULT ∧
    lcause lpc lregs lm ≠ MCAUSE_LOAD_ACCESS_FAULT ∧
    lcause lpc lregs lm ≠ MCAUSE_STORE_ACCESS_FAULT.

  Lemma load_cause_frag φf φ src imm :
    reg φf !! src = reg φ !! src →
    mem φf ⊆ mem φ →
    shadowtbl φf = shadowtbl φ →
    load_cause φf src imm ≠ MCAUSE_LOAD_ACCESS_FAULT →
    load_cause φ src imm = load_cause φf src imm.
  Proof.
    intros Hsrc Hmem Hsh. rewrite /load_cause /lookup_reg Hsrc Hsh.
    destruct (reg φ !! src) as [w|]; last done. cbn.
    case_decide; first done.
    destruct w as [| [[] p g b e a | ] | | ]; try done.
    destruct (a + imm)%a as [ea|]; last done.
    destruct (readAllowed p && withinBounds b e ea); last done.
    destruct (is_shadow_address ea); first done.
    destruct (is_revoker_address ea); first done.
    destruct (mem φf !! ea) as [x|] eqn:Hx; last done.
    by rewrite (lookup_weaken _ _ _ _ Hx Hmem).
  Qed.

  Lemma store_cause_frag φf φ dst ρ imm :
    reg φf !! dst = reg φ !! dst →
    (∀ r, ρ = inr r → reg φf !! r = reg φ !! r) →
    mem φf ⊆ mem φ →
    store_cause φf dst ρ imm ≠ MCAUSE_STORE_ACCESS_FAULT →
    store_cause φ dst ρ imm = store_cause φf dst ρ imm.
  Proof.
    intros Hdst Hρ Hmem. rewrite /store_cause /lookup_reg Hdst.
    assert (word_of_argument (reg φf) ρ = word_of_argument (reg φ) ρ) as ->.
    { destruct ρ as [z|r]; first done. cbn. rewrite /lookup_reg (Hρ r eq_refl). done. }
    destruct (word_of_argument (reg φ) ρ) as [t|]; last done.
    destruct (reg φ !! dst) as [w|]; last done. cbn.
    case_decide; first done.
    destruct w as [| [[] p g b e a | ] | | ]; try done.
    destruct (a + imm)%a as [ea|]; last done.
    destruct (writeAllowed p && withinBounds b e ea); last done.
    destruct (is_shadow_address ea); first done.
    destruct (is_revoker_address ea); first done.
    destruct (mem φf !! ea) as [x|] eqn:Hx; last done.
    by rewrite (lookup_weaken _ _ _ _ Hx Hmem).
  Qed.

  (** The cause from fragments is the cause from any registers and memory
      that contain them. *)
  Lemma lcause_frag lpc lregs lm lreg lmem :
    lcause_known lpc lregs lm →
    lregs ⊆ lreg →
    lm ⊆ lmem →
    lcause lpc lreg lmem = lcause lpc lregs lm.
  Proof.
    intros (Hregs & Hfetch & Hload & Hstore) Hsub Hmsub.
    assert ((lw <$> lm) ⊆ (lw <$> lmem)) as Hmsub' by by apply map_fmap_mono.
    assert (∀ r, r ∈ dom lregs → (lw <$> lregs) !! r = (lw <$> lreg) !! r) as Hr.
    { intros r [v Hv]%elem_of_dom. by rewrite !lookup_fmap Hv (lookup_weaken _ _ _ _ Hv Hsub). }
    revert Hfetch Hload Hstore. rewrite /lcause /trap_cause /lview /=.
    destruct lpc as [w π]; cbn in Hregs |- *.
    destruct w as [| [[] p g b e a | ] | | ]; try done.
    destruct (isCorrectPCb _); last done.
    rewrite !lookup_fmap.
    destruct (lm !! a) as [wi|] eqn:Hwi; last done.
    rewrite (lookup_weaken _ _ _ _ Hwi Hmsub) /=.
    pose proof (Hregs _ _ _ _ _ _ eq_refl Hwi) as Hdom.
    destruct (decodeInstrW wi.(lw)) eqn:Hi; cbn in Hdom |- *; try done.
    - intros _ Hload _. apply load_cause_frag; [| done | done | done].
      apply Hr. set_solver.
    - intros _ _ Hstore. apply store_cause_frag; [| | done | done].
      + apply Hr. set_solver.
      + intros r ->. apply Hr. set_solver.
  Qed.

  (** * The fault rule with the exact cause *)

  Context `{ceriseg : ceriseG Σ}.

  (** A fault with the exact cause, from the PC [w], the registers [lregs]
      and the memory [lm] (the code, and the effective address of an access
      past the capability checks): the obligation receives a cause in
      [mcause_ok] that is [lcause w lregs lm]. *)
  Lemma wp_trap_cause E Φ w (lregs : LReg) (lm : LMem) dq :
    lcause_known w lregs lm →
    PC ↦ₚ w -∗
    ([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
    ([∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x) -∗
    (([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
     ([∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x) -∗
     trap_safe_cause (λ c : Z, (mcause_ok c ∧ c = lcause w lregs lm)%type) w E Φ) -∗
    WP Seq (Instr Faulted) @ E {{ Φ }}.
  Proof.
    intros Hknown. iApply wp_trap_gen.
    intros R C σ lreg lsreg lmem Her Hregs Hmem. split; first apply trap_cause_ok.
    rewrite (erasure_trap_cause _ _ _ _ _ _ _ Her). by apply lcause_frag.
  Qed.

End trap_cause.

(* [iTrap cause with "Hregs" "Hmem"] closes a fault
   [WP Seq (Instr Faulted) @ E {{ Φ }}] with [wp_trap_cause], from the PC
   points-to of the context, the register map ["Hregs"] and the memory map
   ["Hmem"]. The maps come back under the same names, for the obligation
   [trap_safe_cause] with the exact cause, after the side condition
   [lcause_known], which is left to the caller. *)
Tactic Notation "iTrap" "cause" "with" constr(Hregs) constr(Hmem) :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Seq ?e) _) => unify e (Instr Faulted)
  | _ => fail "iTrap cause: the goal is not a fault WP Seq (Instr Faulted)"
  end;
  let hpc := instr_trap_pc in
  iApply (wp_trap_cause with
           [SIdent hpc nil; SIdent (INamed Hregs) nil; SIdent (INamed Hmem) nil]);
  last (iIntros Hregs; iIntros Hmem).
