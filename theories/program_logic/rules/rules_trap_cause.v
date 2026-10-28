From iris.proofmode Require Import proofmode environments spec_patterns.
From griotte Require Export rules_trap_entry.

(** * The exact cause and value of a fault

    Trap entry writes the cause and the value of the fault [trap_fault σ],
    computed from the physical state, to mcause and mtval. [lfault]
    computes the fault from the logical view: the logical PC, the logical
    registers and the logical memory, with the shadow table of a heap whose
    every address has an entry. Under erasure, which covers the heap with
    memory ([er_heap_mapped]), the two agree on the cause
    ([erasure_trap_cause]), and the physical fault is the logical one, or a
    tag violation on the authority of the instruction (the capability of a
    load or a store, the target of a jump) when its logical word may have
    been stripped ([erasure_trap_fault], [fault_ok]).

    A fault site that owns the code points-to, the registers that the
    instruction reads and, for an access past the capability checks, the
    points-to of the effective address, computes the fault from these
    fragments ([lfault_frag]), and hands it to trap entry with
    [wp_trap_fault]. A fragment cannot tell an absent address from one
    that it does not own, so the access faults are excluded
    ([lfault_known]). *)

Section trap_cause.
  Context `{MP : MachineParameters}.

  (** * The logical fault *)

  (** A shadow table with an entry at every heap address. *)
  Definition heap_shadow : ShadowTbl := gset_to_gmap ShadowLive heap_addresses.

  Lemma heap_shadow_lookup a :
    is_heap_address a = true → is_Some (heap_shadow !! a).
  Proof.
    intros Ha. rewrite /heap_shadow lookup_gset_to_gmap option_guard_True; first by eexists.
    by apply elem_of_heap_addresses.
  Qed.

  (** The logical view as a configuration: the logical words without their
      identifiers. [trap_fault] reads no system register. *)
  Definition lview (lpc : LWord) (lregs : LReg) (lm : LMem) : ExecConf :=
    (lpc.(lw), lw <$> lregs, ∅, lw <$> lm, heap_shadow).

  (** The logical fault at the PC [lpc], from the logical registers [lregs]
      and the logical memory [lm], and its cause. *)
  Definition lfault (lpc : LWord) (lregs : LReg) (lm : LMem) : fault :=
    trap_fault (lview lpc lregs lm).

  Definition lcause (lpc : LWord) (lregs : LReg) (lm : LMem) : Z :=
    trap_cause (lview lpc lregs lm).

  Lemma lcause_lfault lpc lregs lm : lcause lpc lregs lm = fault_mcause (lfault lpc lregs lm).
  Proof. done. Qed.

  (** The register whose capability authorises the instruction [i], whose
      tag the fault reads: the capability of a load or a store, the target
      of a jump. *)
  Definition fault_auth_reg (i : instr) : option RegName :=
    match i with
    | CLoad _ src _ => Some src
    | Store dst _ _ => Some dst
    | Jalr _ rsrc => Some rsrc
    | _ => None
    end.

  (** * An agreement relation between two configurations *)

  (** A physical register word is the logical one, or its untagged copy; in
      the latter case a tagged logical word satisfies [P], and a tagged
      logical capability addresses heap memory only (it is stale, or has no
      authority and so empty bounds). *)
  Definition word_agree (P : Prop) (x y : Word) : Prop :=
    y = x ∨
    (y = clear_tag x ∧ (get_tag x = true → P) ∧
     ∀ p g b e a ea, x = Cap p g b e a → withinBounds b e ea = true →
       is_heap_address ea = true).

  (** Memory words agree on what the faults read: the decoded instruction and
      the heap base. *)
  Definition mem_agree (x y : Word) : Prop :=
    decodeInstrW x = decodeInstrW y ∧ heap_cap_base x = heap_cap_base y.

  (** The agreement, where a register [r] whose physical word is stripped
      satisfies [S r]. *)
  Record cause_rel (S : RegName → Prop) (φl φp : ExecConf) : Prop := {
    cr_pc : pcc φl = pcc φp;
    cr_reg r : option_Forall2 (word_agree (S r)) (reg φl !! r) (reg φp !! r);
    cr_mem a : option_Forall2 mem_agree (mem φl !! a) (mem φp !! a);
    cr_shadow_l a : is_heap_address a = true → is_Some (shadowtbl φl !! a);
    cr_shadow_p a : is_heap_address a = true → is_Some (shadowtbl φp !! a);
    cr_heap_mapped : heap_mapped (mem φp);
  }.

  (** The physical fault [fp] of an instruction with authority [r] is the
      logical one [fl], or a tag violation on [r] when [r] may be stripped,
      while the logical fault is a CHERI fault. *)
  Definition fault_rel (S : RegName → Prop) (r : RegName) (fl fp : fault) : Prop :=
    fp = fl ∨
    (fp = FaultCheri TagViolation (CheriGPR r) ∧ S r ∧ fault_mcause fl = MCAUSE_CHERI).

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
    destruct (is_heap_address f) eqn:Hf_heap; last done. by intros [= <-].
  Qed.

  Lemma lookup_reg_rel S φl φp r :
    cause_rel S φl φp → option_Forall2 (word_agree (S r)) (reg φl !!ᵣ r) (reg φp !!ᵣ r).
  Proof.
    intros Hrel. rewrite /lookup_reg. case_decide.
    - constructor. by left.
    - destruct (cr_reg _ _ _ Hrel r); by constructor.
  Qed.

  Lemma word_of_argument_rel S φl φp ρ :
    cause_rel S φl φp →
    option_Forall2 (λ x y, y = x ∨ y = clear_tag x)
      (word_of_argument (reg φl) ρ) (word_of_argument (reg φp) ρ).
  Proof.
    intros Hrel. destruct ρ as [z|r]; cbn; first (constructor; by left).
    destruct (lookup_reg_rel _ _ _ r Hrel) as [x y [-> | [-> _]] |]; constructor;
      [by left | by right].
  Qed.

  (** Under the agreement, a heap address read logically is mapped there. *)
  Lemma rel_mem_mapped S φl φp ea :
    cause_rel S φl φp → is_heap_address ea = true → is_Some (mem φl !! ea).
  Proof.
    intros Hrel Hea. pose proof (cr_mem _ _ _ Hrel ea) as Hm.
    destruct (heap_mapped_lookup _ _ (cr_heap_mapped _ _ _ Hrel) Hea) as [? Hp].
    rewrite Hp in Hm. inversion Hm. eauto.
  Qed.

  (** An untagged authority fails the tag check. *)
  Lemma data_cap_check_untagged perm_ok perm_code r w imm :
    get_tag w = false →
    data_cap_check perm_ok perm_code r w imm = inl (FaultCheri TagViolation (CheriGPR r)).
  Proof. by destruct w as [| [[] | [] ] | ? [] | ? [ [] | [] ] ]. Qed.

  Lemma data_cap_check_clear_tag perm_ok perm_code r w imm :
    data_cap_check perm_ok perm_code r (clear_tag w) imm =
    inl (FaultCheri TagViolation (CheriGPR r)).
  Proof. apply data_cap_check_untagged, get_tag_clear_tag. Qed.

  (** ** Loads *)

  Lemma load_fault_rel S φl φp src imm :
    cause_rel S φl φp →
    fault_rel S src (load_fault φl src imm) (load_fault φp src imm).
  Proof.
    intros Hrel. rewrite /load_fault.
    destruct (lookup_reg_rel _ _ _ src Hrel) as [x y [-> | (-> & Hstrip & Hheap)] |];
      [| | by left].
    - (* Exact copy: the same branches; memory agrees on the heap base, and
         both shadow tables have an entry at every heap address. *)
      left.
      destruct (data_cap_check readAllowed PermitLoadViolation src x imm) as [f|ea];
        first done.
      destruct (is_shadow_address ea).
      { destruct (shadow_to_heap ea) as [ha|] eqn:Hha; last done.
        pose proof (shadow_to_heap_heap _ _ Hha) as Hha_heap.
        by destruct (cr_shadow_l _ _ _ Hrel ha Hha_heap) as [? ->],
          (cr_shadow_p _ _ _ Hrel ha Hha_heap) as [? ->]. }
      destruct (is_revoker_address ea); first done.
      destruct (cr_mem _ _ _ Hrel ea) as [x' y' [_ Hb]|]; last done.
      rewrite Hb. destruct (heap_cap_base y') as [base|] eqn:Hbase; last done.
      pose proof (heap_cap_base_heap _ _ Hbase) as Hbase_heap.
      by destruct (cr_shadow_l _ _ _ Hrel base Hbase_heap) as [? ->],
        (cr_shadow_p _ _ _ Hrel base Hbase_heap) as [? ->].
    - (* Untagged physical copy: a tag violation; the logical fault is a
         CHERI fault, since a stale capability reads mapped heap memory whose
         loaded heap base has a shadow entry. *)
      rewrite data_cap_check_clear_tag.
      destruct (get_tag x) eqn:Htag; last (left; by rewrite data_cap_check_untagged).
      right. split_and!; [done | by apply Hstrip |].
      destruct x as [| [[] p g b e a | [] ] | k [] | ? [ [] | [] ] ]; try done; cbn.
      destruct (readAllowed p); last done.
      destruct (a + imm)%a as [ea|]; last done.
      destruct (withinBounds b e ea) eqn:Hwb; last done.
      pose proof (Hheap p g b e a ea eq_refl Hwb) as Hea.
      rewrite (heap_not_shadow _ Hea) (heap_not_revoker _ Hea).
      destruct (rel_mem_mapped _ _ _ ea Hrel Hea) as [x' ->].
      destruct (heap_cap_base x') as [base|] eqn:Hbase; last done.
      by destruct (cr_shadow_l _ _ _ Hrel base (heap_cap_base_heap _ _ Hbase)) as [? ->].
  Qed.

  (** ** Stores *)

  Lemma store_fault_rel S φl φp dst ρ imm :
    cause_rel S φl φp →
    fault_rel S dst (store_fault φl dst ρ imm) (store_fault φp dst ρ imm).
  Proof.
    intros Hrel. rewrite /store_fault.
    destruct (word_of_argument_rel _ _ _ ρ Hrel) as [t t' Ht|]; last by left.
    destruct (lookup_reg_rel _ _ _ dst Hrel) as [x y [-> | (-> & Hstrip & Hheap)] |];
      [| | by left].
    - (* Exact copy: the stored words have the same shape, memory the same
         domain. *)
      left.
      destruct (data_cap_check writeAllowed PermitStoreViolation dst x imm) as [f|ea];
        first done.
      destruct (is_shadow_address ea).
      { destruct Ht as [-> | ->]; first done. by destruct t as [| [] | | ? []]. }
      destruct (is_revoker_address ea); first done.
      by destruct (cr_mem _ _ _ Hrel ea).
    - (* Untagged physical copy: a tag violation; a stale capability writes
         mapped heap memory. *)
      rewrite data_cap_check_clear_tag.
      destruct (get_tag x) eqn:Htag; last (left; by rewrite data_cap_check_untagged).
      right. split_and!; [done | by apply Hstrip |].
      destruct x as [| [[] p g b e a | [] ] | k [] | ? [ [] | [] ] ]; try done; cbn.
      destruct (writeAllowed p); last done.
      destruct (a + imm)%a as [ea|]; last done.
      destruct (withinBounds b e ea) eqn:Hwb; last done.
      pose proof (Hheap p g b e a ea eq_refl Hwb) as Hea.
      rewrite (heap_not_shadow _ Hea) (heap_not_revoker _ Hea).
      by destruct (rel_mem_mapped _ _ _ ea Hrel Hea) as [x' ->].
  Qed.

  (** ** Jumps *)

  Lemma jalr_fault_rel S φl φp rdst rsrc :
    cause_rel S φl φp →
    fault_rel S rsrc (jalr_fault φl rdst rsrc) (jalr_fault φp rdst rsrc).
  Proof.
    intros Hrel. rewrite /jalr_fault.
    destruct (lookup_reg_rel _ _ _ rsrc Hrel) as [x y [-> | (-> & Hstrip & _)] |];
      [by left | | by left].
    rewrite get_tag_clear_tag /=.
    destruct (get_tag x) eqn:Htag; last by left.
    right. split_and!; [done | by apply Hstrip | by repeat case_match].
  Qed.

  (** ** Every fault class *)

  Lemma instr_fault_rel S i p φl φp :
    cause_rel S φl φp →
    match fault_auth_reg i with
    | Some r => fault_rel S r (instr_fault i p φl) (instr_fault i p φp)
    | None => instr_fault i p φp = instr_fault i p φl
    end.
  Proof.
    intros Hrel. destruct i; cbn; try done.
    - by apply jalr_fault_rel.
    - by apply load_fault_rel.
    - by apply store_fault_rel.
  Qed.

  (** Fetch faults (PC checks, unmapped PC address), then the decoded
      instruction's fault. *)
  Lemma trap_fault_rel S φl φp :
    cause_rel S φl φp →
    trap_fault φp = trap_fault φl ∨
    (fault_mcause (trap_fault φl) = MCAUSE_CHERI ∧
     ∃ p g b e a wi r,
       pcc φl = Cap p g b e a ∧ isCorrectPCb (pcc φl) = true ∧
       mem φl !! a = Some wi ∧ fault_auth_reg (decodeInstrW wi) = Some r ∧ S r ∧
       trap_fault φp = FaultCheri TagViolation (CheriGPR r)).
  Proof.
    intros Hrel. pose proof (cr_pc _ _ _ Hrel) as Hpc.
    rewrite /trap_fault -Hpc.
    destruct (pcc φl) as [| [[] p g b e a | ] | | ] eqn:Hpcl; try by left.
    destruct (isCorrectPCb _) eqn:Hcorrect; last by left.
    pose proof (cr_mem _ _ _ Hrel a) as Hm.
    destruct (mem φl !! a) as [x|] eqn:Hx; inversion Hm as [? y [Hdec _] Hx' Hy|];
      last by left.
    rewrite -Hdec.
    pose proof (instr_fault_rel S (decodeInstrW x) p _ _ Hrel) as Hi.
    destruct (fault_auth_reg (decodeInstrW x)) as [r|] eqn:Hr; last by left.
    destruct Hi as [-> | (Hp & HS & Hl)]; first by left.
    right. split; first done.
    by exists p, g, b, e, a, x, r.
  Qed.

  (** * Erasure gives the agreement *)

  (** A logical word whose physical copy may be untagged: a tagged word with
      an identifier, or with a heap base (an over-approximation of
      [reg_strip_ok], which does not depend on the registry). *)
  Definition may_strip (v : LWord) : Prop :=
    get_tag v.(lw) = true ∧ (is_Some v.(lprov) ∨ is_Some (heap_cap_base v.(lw))).

  (** The registers whose physical copy may be untagged. *)
  Definition reg_may_strip (lreg : LReg) (r : RegName) : Prop :=
    ∃ v, lreg !! r = Some v ∧ may_strip v.

  (** The register clause: an untagged copy of a tagged word is the copy of
      a word that may be stripped; an untagged copy of a tagged capability
      is the copy of a stale capability, whose in-bounds addresses its
      registered range covers, or of a word without authority, whose bounds
      are empty. *)
  Lemma reg_phys_word_agree R C st lreg r v w :
    registry_ok R C st → lreg !! r = Some v → reg_word_ok R C v → reg_phys R v w →
    word_agree (reg_may_strip lreg r) v.(lw) w.
  Proof.
    intros Hreg Hr Hok [[-> | [-> Hstrip]] _]; first by left.
    right. split; first done. split.
    { intros Htag. exists v. split; first done. split; first done.
      destruct Hstrip as [[(ι & x & Hι & _) _] | [_ Hb]]; [left | right]; by eauto. }
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
      rewrite Hv in Hhb.
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
    cause_rel (reg_may_strip lreg) (lview lpc lreg lmem) σ.
  Proof.
    intros Her. constructor; cbn.
    - symmetry. by eapply erasure_pc_exact.
    - intros r. rewrite lookup_fmap.
      destruct (lreg !! r) as [v|] eqn:Hv; cbn.
      + destruct (erasure_lookup_reg _ _ _ _ _ _ _ _ _ Her Hv) as (w & -> & Hw).
        constructor.
        eapply reg_phys_word_agree; [apply Her | done | by eapply er_reg_words | done].
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

  (** Agreement on the cause: under erasure, which covers the heap with
      memory, the logical cause is the physical one, for every fault class
      (fetch, illegal instruction, load, store, every other CHERI fault). *)
  Theorem erasure_trap_cause R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem →
    trap_cause σ = lcause lpc lreg lmem.
  Proof.
    intros Her. rewrite /lcause /trap_cause.
    destruct (trap_fault_rel _ _ _ (erasure_cause_rel _ _ _ _ _ _ _ Her))
      as [-> | (Hl & _ & _ & _ & _ & _ & _ & r & _ & _ & _ & _ & _ & ->)]; first done.
    by rewrite Hl.
  Qed.

  (** The instruction word that the PC [lpc] fetches from the logical memory
      [lm], if it is a correct PC. *)
  Definition instr_at (lpc : LWord) (lm : LMem) : option LWord :=
    match lpc.(lw) with
    | Cap _ _ _ _ a => if isCorrectPCb lpc.(lw) then lm !! a else None
    | _ => None
    end.

  (** The faults that the logical view allows: the logical fault, or a tag
      violation on the authority of the instruction at the PC, when its
      logical word may have been stripped. *)
  Definition fault_ok (lpc : LWord) (lregs : LReg) (lm : LMem) (f : fault) : Prop :=
    f = lfault lpc lregs lm ∨
    ∃ wi r v,
      instr_at lpc lm = Some wi ∧ fault_auth_reg (decodeInstrW wi.(lw)) = Some r ∧
      r ≠ cnull ∧ lregs !! r = Some v ∧ may_strip v ∧
      f = FaultCheri TagViolation (CheriGPR r).

  (** Agreement on the fault: under erasure, the physical fault is one that
      the logical view allows. *)
  Theorem erasure_trap_fault R C σ lpc lreg lsreg lmem :
    erasure R C σ lpc lreg lsreg lmem →
    fault_ok lpc lreg lmem (trap_fault σ).
  Proof.
    intros Her.
    destruct (trap_fault_rel _ _ _ (erasure_cause_rel _ _ _ _ _ _ _ Her))
      as [-> | (_ & p & g & b & e & a & wi & r & Hpc & Hcorrect & Hwi & Hr & (v & Hv & Hs) & ->)];
      first by left.
    right. cbn [lview pcc mem fst snd] in Hpc, Hcorrect, Hwi. rewrite lookup_fmap in Hwi.
    destruct (lmem !! a) as [wi'|] eqn:Hwi'; inversion Hwi; subst wi.
    (* [cnull] holds the null word, which is never stripped. *)
    assert (r ≠ cnull) as Hr_cnull.
    { intros ->. rewrite (er_cnull _ _ _ _ _ _ _ Her _ Hv) in Hs. cbn in Hs.
      by destruct Hs as [Htag _]. }
    exists wi', r, v. split_and!; try done.
    by rewrite /instr_at Hcorrect Hpc.
  Qed.

  (** * The fault from fragments *)

  (** Whether a fault is an access fault. *)
  Definition fault_is_access (f : fault) : bool :=
    match f with
    | FaultInstAccess _ | FaultLoadAccess _ | FaultStoreAccess _ => true
    | _ => false
    end.

  (** The fault is known from the registers [lregs] and the memory [lm]:
      they contain the registers that the instruction at the PC reads, and
      the fault is not an access fault, which an address that the fragment
      misses would give. *)
  Definition lfault_known (lpc : LWord) (lregs : LReg) (lm : LMem) : Prop :=
    (∀ p g b e a wi, lpc.(lw) = Cap p g b e a → lm !! a = Some wi →
       regs_of (decodeInstrW wi.(lw)) ⊆ dom lregs) ∧
    fault_is_access (lfault lpc lregs lm) = false.

  Lemma load_fault_frag φf φ src imm :
    reg φf !!ᵣ src = reg φ !!ᵣ src →
    mem φf ⊆ mem φ →
    shadowtbl φf = shadowtbl φ →
    fault_is_access (load_fault φf src imm) = false →
    load_fault φ src imm = load_fault φf src imm.
  Proof.
    intros Hsrc Hmem Hsh. rewrite /load_fault Hsrc Hsh.
    destruct (reg φ !!ᵣ src) as [w|]; last done. cbn.
    destruct (data_cap_check readAllowed PermitLoadViolation src w imm) as [f|ea]; first done.
    destruct (is_shadow_address ea); first done.
    destruct (is_revoker_address ea); first done.
    destruct (mem φf !! ea) as [x|] eqn:Hx; last done.
    by rewrite (lookup_weaken _ _ _ _ Hx Hmem).
  Qed.

  Lemma store_fault_frag φf φ dst ρ imm :
    reg φf !!ᵣ dst = reg φ !!ᵣ dst →
    (∀ r, ρ = inr r → reg φf !!ᵣ r = reg φ !!ᵣ r) →
    mem φf ⊆ mem φ →
    fault_is_access (store_fault φf dst ρ imm) = false →
    store_fault φ dst ρ imm = store_fault φf dst ρ imm.
  Proof.
    intros Hdst Hρ Hmem. rewrite /store_fault Hdst.
    assert (word_of_argument (reg φf) ρ = word_of_argument (reg φ) ρ) as ->.
    { destruct ρ as [z|r]; first done. cbn. by rewrite (Hρ r eq_refl). }
    destruct (word_of_argument (reg φ) ρ) as [t|]; last done.
    destruct (reg φ !!ᵣ dst) as [w|]; last done. cbn.
    destruct (data_cap_check writeAllowed PermitStoreViolation dst w imm) as [f|ea]; first done.
    destruct (is_shadow_address ea); first done.
    destruct (is_revoker_address ea); first done.
    destruct (mem φf !! ea) as [x|] eqn:Hx; last done.
    by rewrite (lookup_weaken _ _ _ _ Hx Hmem).
  Qed.

  Lemma jalr_fault_frag φf φ rdst rsrc :
    reg φf !!ᵣ rsrc = reg φ !!ᵣ rsrc →
    jalr_fault φ rdst rsrc = jalr_fault φf rdst rsrc.
  Proof. intros Hsrc. by rewrite /jalr_fault Hsrc. Qed.

  (** The fault from fragments is the fault from any registers and memory
      that contain them. *)
  Lemma lfault_frag lpc lregs lm lreg lmem :
    lfault_known lpc lregs lm →
    lregs ⊆ lreg →
    lm ⊆ lmem →
    lfault lpc lreg lmem = lfault lpc lregs lm.
  Proof.
    intros (Hregs & Hknown) Hsub Hmsub.
    assert ((lw <$> lm) ⊆ (lw <$> lmem)) as Hmsub' by by apply map_fmap_mono.
    (* An operand reads the same word: [cnull] reads 0, the others are in
       the fragment. *)
    assert (∀ r, r = cnull ∨ r ∈ dom lregs → (lw <$> lregs) !!ᵣ r = (lw <$> lreg) !!ᵣ r) as Hr.
    { intros r Hr. rewrite /lookup_reg. case_decide as Hr_cnull; first done.
      destruct Hr as [->|[v Hv]%elem_of_dom]; first done.
      by rewrite !lookup_fmap Hv (lookup_weaken _ _ _ _ Hv Hsub). }
    revert Hknown. rewrite /lfault /trap_fault /lview /=.
    destruct lpc as [w π]; cbn in Hregs |- *.
    destruct w as [| [[] p g b e a | ] | | ]; try done.
    destruct (isCorrectPCb _); last done.
    rewrite !lookup_fmap.
    destruct (lm !! a) as [wi|] eqn:Hwi; last done.
    rewrite (lookup_weaken _ _ _ _ Hwi Hmsub) /=.
    pose proof (Hregs _ _ _ _ _ _ eq_refl Hwi) as Hdom.
    destruct (decodeInstrW wi.(lw)) eqn:Hi; cbn in Hdom |- *; try done.
    - intros _. apply jalr_fault_frag. apply Hr.
      eapply elem_of_lregs_dom; [exact Hdom | set_solver].
    - intros Hload. apply load_fault_frag; [| done | done | done].
      apply Hr. eapply elem_of_lregs_dom; [exact Hdom | set_solver].
    - intros Hstore. apply store_fault_frag; [| | done | done].
      + apply Hr. eapply elem_of_lregs_dom; [exact Hdom | set_solver].
      + intros r ->. apply Hr. eapply elem_of_lregs_dom; [exact Hdom | set_solver].
  Qed.

  Lemma lcause_frag lpc lregs lm lreg lmem :
    lfault_known lpc lregs lm →
    lregs ⊆ lreg →
    lm ⊆ lmem →
    lcause lpc lreg lmem = lcause lpc lregs lm.
  Proof. intros. rewrite !lcause_lfault. f_equal. by apply lfault_frag. Qed.

  Lemma fault_auth_reg_operands_of i r : fault_auth_reg i = Some r → r ∈ operands_of i.
  Proof. destruct i; cbn; intros [=<-]; set_solver. Qed.

  (** The faults that the full view allows are those that fragments
      allow. *)
  Lemma fault_ok_frag lpc lregs lm lreg lmem f :
    lfault_known lpc lregs lm →
    lregs ⊆ lreg →
    lm ⊆ lmem →
    fault_ok lpc lreg lmem f →
    fault_ok lpc lregs lm f.
  Proof.
    intros Hknown Hsub Hmsub [-> | (wi & r & v & Hwi & Hr & Hr_cnull & Hv & Hs & ->)].
    { left. by apply lfault_frag. }
    right. destruct Hknown as [Hregs Hacc].
    rewrite /instr_at in Hwi.
    destruct lpc as [w π]; cbn in Hwi, Hregs.
    destruct w as [| [[] p g b e a | ] | | ]; try done.
    destruct (isCorrectPCb _) eqn:Hcorrect; last done.
    (* The fragment has the instruction word: otherwise the fault would be a
       fetch access fault. *)
    destruct (lm !! a) as [wi'|] eqn:Hwi'; last first.
    { exfalso. revert Hacc. rewrite /lfault /trap_fault /lview. cbn [pcc mem fst snd lw].
      by rewrite Hcorrect lookup_fmap Hwi'. }
    rewrite (lookup_weaken _ _ _ _ Hwi' Hmsub) in Hwi. injection Hwi as ->.
    pose proof (Hregs _ _ _ _ _ _ eq_refl Hwi') as Hdom.
    pose proof (fault_auth_reg_operands_of _ _ Hr) as Hrr.
    destruct (elem_of_dom lregs r) as [[v' Hv'] _].
    { apply Hdom. rewrite /regs_of. set_solver. }
    rewrite (lookup_weaken _ _ _ _ Hv' Hsub) in Hv. injection Hv as ->.
    exists wi, r, v. split_and!; try done.
    rewrite /instr_at. cbn [lw]. by rewrite Hcorrect.
  Qed.

  (** * The fault rule with the exact cause and value *)

  Context `{ceriseg : ceriseG Σ}.

  (** A fault with the exact cause and value, from the PC [w], the
      registers [lregs] and the memory [lm], each cell at its own fraction
      (the code, and the effective address of an access past the capability
      checks): the obligation receives a cause in [mcause_ok] that is
      [lcause w lregs (snd <$> lm)], and the value of a fault that
      [fault_ok] allows. *)
  Lemma wp_trap_fault_frac E Φ w (lregs : LReg) (lm : gmap Addr (dfrac * LWord)) :
    lfault_known w lregs (snd <$> lm) →
    PC ↦ₚ w -∗
    ([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
    ([∗ map] a ↦ qx ∈ lm, a ↦ₐ{qx.1} qx.2) -∗
    (([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
     ([∗ map] a ↦ qx ∈ lm, a ↦ₐ{qx.1} qx.2) -∗
     trap_safe_cause
       (λ c : Z, (mcause_ok c ∧ c = lcause w lregs (snd <$> lm))%type)
       (λ v : Z, (∃ f, fault_ok w lregs (snd <$> lm) f ∧ v = fault_mtval f)%type)
       w E Φ) -∗
    WP Seq (Instr Faulted) @ E {{ Φ }}.
  Proof.
    intros Hknown. iApply wp_trap_gen_frac.
    intros R C σ lreg lsreg lmem Her Hregs Hmem. split_and!.
    - apply trap_cause_ok.
    - rewrite (erasure_trap_cause _ _ _ _ _ _ _ Her). by apply lcause_frag.
    - exists (trap_fault σ). split; last done.
      eapply fault_ok_frag; [done | done | done |]. by eapply erasure_trap_fault.
  Qed.

  (** A fault with the exact cause and value, from the PC [w], the
      registers [lregs] and the memory [lm] (the code, and the effective
      address of an access past the capability checks): the obligation
      receives a cause in [mcause_ok] that is [lcause w lregs lm], and the
      value of a fault that [fault_ok] allows. *)
  Lemma wp_trap_fault E Φ w (lregs : LReg) (lm : LMem) dq :
    lfault_known w lregs lm →
    PC ↦ₚ w -∗
    ([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
    ([∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x) -∗
    (([∗ map] r ↦ x ∈ lregs, r ↦ᵣ x) -∗
     ([∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x) -∗
     trap_safe_cause
       (λ c : Z, (mcause_ok c ∧ c = lcause w lregs lm)%type)
       (λ v : Z, (∃ f, fault_ok w lregs lm f ∧ v = fault_mtval f)%type)
       w E Φ) -∗
    WP Seq (Instr Faulted) @ E {{ Φ }}.
  Proof.
    iIntros (Hknown) "HPC Hregs Hmem Hsafe".
    iApply (wp_trap_fault_frac _ _ _ _ ((λ x, (dq, x)) <$> lm)
             with "HPC Hregs [Hmem] [Hsafe]").
    - by rewrite -map_fmap_compose map_fmap_id.
    - by rewrite big_sepM_fmap.
    - rewrite big_sepM_fmap /= -map_fmap_compose map_fmap_id. iExact "Hsafe".
  Qed.

End trap_cause.

(* [iTrap cause with "Hregs" "Hmem"] closes a fault
   [WP Seq (Instr Faulted) @ E {{ Φ }}] with the exact cause and value, from
   the PC points-to of the context, the register map ["Hregs"]
   ([[∗ map] r ↦ x ∈ lregs, r ↦ᵣ x]) and the memory map ["Hmem"]: with
   [wp_trap_fault_frac] when each cell has its own fraction
   ([[∗ map] a ↦ qx ∈ lm, a ↦ₐ{qx.1} qx.2]), with [wp_trap_fault] when all
   have one ([[∗ map] a ↦ x ∈ lm, a ↦ₐ{dq} x]). The side condition
   [lfault_known] is left to the caller, first; the maps come back under the
   same names, for the obligation [trap_safe_cause] with the exact cause and
   value. *)
Tactic Notation "iTrap" "cause" "with" constr(Hregs) constr(Hmem) :=
  lazymatch goal with
  | |- envs_entails _ (wp _ _ (Seq ?e) _) => unify e (Instr Faulted)
  | _ => fail "iTrap cause: the goal is not a fault WP Seq (Instr Faulted)"
  end;
  let hpc := instr_trap_pc in
  first
    [ iApply (wp_trap_fault_frac with
               [SIdent hpc nil; SIdent (INamed Hregs) nil; SIdent (INamed Hmem) nil])
    | iApply (wp_trap_fault with
               [SIdent hpc nil; SIdent (INamed Hregs) nil; SIdent (INamed Hmem) nil])
    | fail "iTrap cause: no register map" Hregs "or no memory map" Hmem ];
  last (iIntros Hregs; iIntros Hmem).
