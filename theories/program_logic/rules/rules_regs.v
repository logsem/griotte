From iris.proofmode Require Import proofmode.
From griotte Require Import rules_base capability_monotonicity_base.
#[local] Open Scope capability_scope.

(** * Register-step WP rules by shape

    One WP rule for every instruction that writes at most one register and
    moves the PC ([wp_regs_step]). Its premises are pure: an agreement over
    an abstract step function ([regs_next_agree_strip]), stated on every
    physical copy of the owned registers (each exact or stripped), and a
    source ([lsource_witness_ok]) that makes the written logical word
    well-formed for the erasure and gives it the property
    [written_word_ok]. A source may use the pure facts of a witness
    resource, read from the registry and the claim map. A source is any
    strip-bit function with that property: the sources below are lemmas, a
    new one is a new lemma. The exact rules ([wp_regs_next] and the k-ary
    rules) are the instance with a fixed written word and no witness. *)

(** ** The pure part *)

Section regs_pure.
  Context `{MP : MachineParameters}.
  Implicit Types (R : RegState) (C : gmap Addr AddrClaim) (v : LWord) (w : Word).

  (** A logical word whose physical copy may be untagged has bounds. *)
  Definition strippable v : Prop := is_Some (memory_cap_bounds v.(lw)).

  (** A physical configuration whose registers are copies of the owned
      ones, each exact ([S r = true]) or stripped. *)
  Definition regs_copy (φ : ExecConf) (S : RegName → bool) (regs : LReg) : Prop :=
    ∀ r v0, regs !! r = Some v0 →
      reg φ !!ᵣ r = Some (and_tag (S r) v0.(lw)) ∧ (S r = false → strippable v0).

  (** The agreement, on any such configuration whose PC is the logical PC:
      the step writes the copy of [v] given by the strip bits [sb S], and
      moves the PC by [n]. *)
  Definition regs_next_agree (step : instr → Perm → ExecConf → option Conf)
      (i : instr) (p : Perm) (lpc : LWord) (regs : LReg) (dst : RegName) (v : LWord) (n : Z)
      (sb : (RegName → bool) → bool) : Prop :=
    ∀ φ (S : RegName → bool), pcc φ = lpc.(lw) → regs_copy φ S regs →
      step i p φ = advancePC ((regs_effect φ) .[dst :=ᵣ and_tag (sb S) v.(lw)]) n.

  (** The agreement when the written word [vS S] depends on the strip bits.
      [regs_next_agree … v n sb] is [regs_next_agree_strip … (λ _, v) n sb]
      by conversion. *)
  Definition regs_next_agree_strip (step : instr → Perm → ExecConf → option Conf)
      (i : instr) (p : Perm) (lpc : LWord) (regs : LReg) (dst : RegName)
      (vS : (RegName → bool) → LWord) (n : Z) (sb : (RegName → bool) → bool) : Prop :=
    ∀ φ (S : RegName → bool), pcc φ = lpc.(lw) → regs_copy φ S regs →
      step i p φ = advancePC ((regs_effect φ) .[dst :=ᵣ and_tag (sb S) (vS S).(lw)]) n.

  (** Operands read on a copy. *)
  Lemma regs_copy_llookup φ S regs r v :
    regs_copy φ S regs → regs !!ₗ r = Some v → reg φ !!ᵣ r = Some (and_tag (S r) v.(lw)).
  Proof.
    intros Hcopy Hr. rewrite /llookup_reg in Hr. case_decide as Hcnull; last by apply Hcopy.
    simplify_eq. done.
  Qed.

  Lemma regs_copy_z φ S regs arg z :
    regs_copy φ S regs → lz_of_argument regs arg = Some z → z_of_argument (reg φ) arg = Some z.
  Proof.
    intros Hcopy. destruct arg as [z' | r]; cbn; first done.
    destruct (regs !!ₗ r) as [v |] eqn:Hr; last done. intros [= <-].
    by rewrite (regs_copy_llookup _ _ _ _ _ Hcopy Hr) get_a_and_tag.
  Qed.

  (** A source of [v]: on well-formed registers and PC, each copied with its
      strip bit, [v] is well-formed and its copy is given by [sb S]. *)
  Definition lsource_ok (regs : LReg) (lpc v : LWord) (sb : (RegName → bool) → bool) : Prop :=
    ∀ R C st (S : RegName → bool), registry_ok R C st →
      (∀ r v0, regs !! r = Some v0 → reg_word_ok R C v0 ∧ reg_phys R v0 (and_tag (S r) v0.(lw))) →
      reg_word_ok R C lpc → reg_phys R lpc lpc.(lw) →
      reg_word_ok R C v ∧ reg_phys R v (and_tag (sb S) v.(lw)).

  (** A source of [vS] under the facts [written_word_witness_ok R C] that a
      witness gives: [vS S] is well-formed, copied by [sb S], and has
      [written_word_ok]. *)
  Definition lsource_witness_ok (written_word_witness_ok : RegState → gmap Addr AddrClaim → Prop)
      (regs : LReg) (lpc : LWord) (vS : (RegName → bool) → LWord) (sb : (RegName → bool) → bool)
      (written_word_ok : LWord → Prop) : Prop :=
    ∀ R C st (S : RegName → bool), registry_ok R C st → written_word_witness_ok R C →
      (∀ r v0, regs !! r = Some v0 → reg_word_ok R C v0 ∧ reg_phys R v0 (and_tag (S r) v0.(lw))) →
      reg_word_ok R C lpc → reg_phys R lpc lpc.(lw) →
      reg_word_ok R C (vS S) ∧ reg_phys R (vS S) (and_tag (sb S) (vS S).(lw)) ∧
      written_word_ok (vS S).

  (** The exact instance: a fixed word, no witness. *)
  Lemma lsource_ok_witness regs lpc v sb :
    lsource_ok regs lpc v sb →
    lsource_witness_ok (λ _ _, True) regs lpc (λ _, v) sb (λ v', v' = v).
  Proof.
    intros Hsrc R C st S Hreg _ Hregs Hok Hphys.
    destruct (Hsrc R C st S Hreg Hregs Hok Hphys) as [Hvok Hvphys]. by split_and!.
  Qed.

  (** The heap-root clause for an identifier-less source: no new heap
      authority base (generalises [subseg_root_free]). *)
  Definition lroot_free (v0 : LWord) (w : Word) : Prop :=
    v0.(lprov) = None → get_tag w = true →
    heap_authority_base w = heap_authority_base v0.(lw) ∨ heap_authority_base w = None.

  Lemma and_tag_untagged s w : get_tag w = false → and_tag s w = w.
  Proof. intros Ht. rewrite and_tag_if clear_tag_untagged //. by destruct s. Qed.

  (** A word below a copied word, with its provenance, is copied with the
      same strip bit (generalises [reg_phys_subseg] and [reg_phys_derive]). *)
  Lemma reg_phys_word_le_and_tag R C st v0 v s :
    registry_ok R C st → reg_word_ok R C v0 →
    reg_phys R v0 (and_tag s v0.(lw)) →
    v.(lw) ⊑ v0.(lw) → v.(lprov) = v0.(lprov) →
    reg_phys R v (and_tag s v.(lw)).
  Proof.
    intros Hreg Hok Hphys0 Hle Hprov.
    destruct (get_tag v.(lw)) eqn:Ht; last by rewrite and_tag_untagged //; apply reg_phys_untagged.
    pose proof (word_le_tagged _ _ Hle Ht) as Ht0.
    destruct s.
    - rewrite and_tag_true in Hphys0. rewrite and_tag_true.
      destruct v as [w π]; cbn in *; subst π.
      by eapply (reg_phys_shrink _ _ st); [| | | apply word_le_shrinks |].
    - rewrite and_tag_false in Hphys0. rewrite and_tag_false. split; last done.
      right. split; first done.
      destruct Hphys0 as [ [Heq | [_ Hstrip] ] _].
      { by rewrite -Heq get_tag_clear_tag in Ht0. }
      destruct v as [w π], v0 as [w0 π0]; cbn in *; subst π.
      destruct Hle as [w_le w_ge Ht_le | w_refl
                      | t t' p p' g g' b b' e e' a a' _ _ _ Hb_le He_le Hrebased
                      | t t' p p' g g' b b' e e' a a' _ _ _ Hb_le He_le].
      + congruence.
      + done.
      + destruct Hstrip as [ [Hstuck _] | [Hnot_auth [base Hbase] ] ].
        { left. split; [done | by eexists]. }
        right. cbn in Ht, Ht0; subst t t'.
        assert (is_heap_address b = true) as Hbh.
        { rewrite /heap_cap_base /= in Hbase. by destruct (is_heap_address b). }
        assert (¬ (b < e)%a) as Hnlt.
        { intros Hlt. apply Hnot_auth. split; first done. exists b.
          apply heap_authority_base_memory_cap_bounds. eauto. }
        assert (b' = b) as -> by (destruct Hrebased as [ [-> ->] | Hbe']; solve_addr).
        split.
        * intros [_ [b'' Hab] ].
          apply heap_authority_base_memory_cap_bounds in Hab as (e'' & [= <- <-] & Hlt'' & _).
          solve_addr.
        * rewrite /heap_cap_base /= Hbh. eauto.
      + destruct Hstrip as [ [_ [b'' Hb] ] | [_ [b'' Hb] ] ]; first done.
        by rewrite /heap_cap_base /= in Hb.
  Qed.

  (** *** Sources *)

  (** A word below a source register, with its provenance. *)
  Lemma lsource_reg regs lpc r v0 v :
    regs !! r = Some v0 → v.(lw) ⊑ v0.(lw) → v.(lprov) = v0.(lprov) → lroot_free v0 v.(lw) →
    lsource_ok regs lpc v (λ S, S r).
  Proof.
    intros Hr Hle Hprov Hroot R C st S Hreg Hregs _ _.
    destruct (Hregs r v0 Hr) as [Hok Hphys]. split; last by eapply reg_phys_word_le_and_tag.
    destruct (get_tag v.(lw)) eqn:Ht; last by apply reg_word_ok_untagged.
    destruct v as [w π]; cbn in *; subst π.
    apply reg_word_ok_shrink; [done | by apply word_le_shrinks | done |].
    intros Hprov0 _ b' Hab. destruct Hok as (_ & Hauth & _).
    destruct (Hroot Hprov0 Ht) as [Heq | Hnone]; last congruence.
    specialize (Hauth b' (word_le_tagged _ _ Hle Ht)). rewrite -Heq Hprov0 in Hauth.
    by apply Hauth.
  Qed.

  (** A word derived from a source register keeping its bounds, its
      provenance, and adding neither the tag nor execution (Mov, Lea, SetA,
      ClearTag, Seal of the sealee): no heap-root clause. *)
  Lemma lsource_derive regs lpc r v0 w :
    regs !!ₗ r = Some v0 →
    memory_cap_bounds w = memory_cap_bounds v0.(lw) →
    (get_tag w = true → get_tag v0.(lw) = true) →
    (get_tag w = true → executable_word w = true → executable_word v0.(lw) = true) →
    lsource_ok regs lpc (MkLWord w v0.(lprov)) (λ S, S r).
  Proof.
    intros Hr Hbounds Htag Hexec R C st S _ Hregs _ _. rewrite /llookup_reg in Hr.
    case_decide as Hcnull.
    - simplify_eq. destruct (get_tag w) eqn:Htw; first by specialize (Htag eq_refl).
      rewrite and_tag_untagged //.
      split; [by apply reg_word_ok_untagged | by apply reg_phys_untagged].
    - destruct (Hregs r v0 Hr) as [Hok Hphys].
      split; [apply reg_word_ok_derive; auto | by apply reg_phys_derive].
  Qed.

  (** An untagged word, from nothing. *)
  Lemma lsource_untagged regs lpc v :
    get_tag v.(lw) = false → lsource_ok regs lpc v (λ _, true).
  Proof.
    intros Ht R C st S _ _ _ _. rewrite and_tag_true.
    split; [by apply reg_word_ok_untagged | by apply reg_phys_untagged].
  Qed.

  (** A word below the PC, with its provenance (Auipcc). *)
  Lemma lsource_pc regs lpc v :
    v.(lw) ⊑ lpc.(lw) → v.(lprov) = lpc.(lprov) → lroot_free lpc v.(lw) →
    lsource_ok regs lpc v (λ _, true).
  Proof.
    intros Hle Hprov Hroot R C st S Hreg _ Hok Hphys.
    refine (lsource_reg {[cnull := lpc]} lpc cnull lpc v _ Hle Hprov Hroot R C st (λ _, true)
              Hreg _ Hok Hphys).
    - apply lookup_singleton_eq.
    - intros r v0 [<- <-]%lookup_singleton_Some. by rewrite and_tag_true.
  Qed.

  (** The pure premise of the k-ary rules: a source and the agreement, the
      PC moved by [n]. *)
  Definition regs_next_ok (i : instr) (p : Perm) (lpc : LWord) (regs : LReg) (dst : RegName)
      (v : LWord) (n : Z) : Prop :=
    ∃ sb, lsource_ok regs lpc v sb ∧ regs_next_agree exec_opt i p lpc regs dst v n sb.

  (** [regs_next_ok] from a source register keeping the bounds, the
      agreement first: computing it instantiates the written word. *)
  Lemma regs_next_ok_derive i p lpc regs dst r v0 w π n :
    regs !!ₗ r = Some v0 → v0.(lprov) = π →
    regs_next_agree exec_opt i p lpc regs dst (MkLWord w π) n (λ S, S r) →
    memory_cap_bounds w = memory_cap_bounds v0.(lw) →
    (get_tag w = true → get_tag v0.(lw) = true) →
    (get_tag w = true → executable_word w = true → executable_word v0.(lw) = true) →
    regs_next_ok i p lpc regs dst (MkLWord w π) n.
  Proof.
    intros Hr <- Hagree Hbounds Htag Hexec. exists (λ S, S r).
    split; last done. by apply lsource_derive.
  Qed.

  (** [regs_next_ok] for an untagged word, from nothing. *)
  Lemma regs_next_ok_untagged i p lpc regs dst w n :
    regs_next_agree exec_opt i p lpc regs dst (MkLWord w None) n (λ _, true) →
    get_tag w = false →
    regs_next_ok i p lpc regs dst (MkLWord w None) n.
  Proof.
    intros Hagree Ht. exists (λ _, true). split; last done. by apply lsource_untagged.
  Qed.

  (** The agreement of a step that writes no register and moves the PC by
      [n] (jumps, branches). *)
  Definition regs_jump_agree (i : instr) (p : Perm) (lpc : LWord) (regs : LReg) (n : Z) : Prop :=
    ∀ φ (S : RegName → bool), pcc φ = lpc.(lw) → regs_copy φ S regs →
      exec_opt i p φ = advancePC (regs_effect φ) n.

  (** A step that writes no register writes [lnull] to [cnull]. *)
  Lemma regs_jump_agree_next_ok i p lpc regs n :
    regs_jump_agree i p lpc regs n → regs_next_ok i p lpc regs cnull lnull n.
  Proof.
    intros Hagree. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S Hpc Hcopy. by rewrite update_reg_cnull (Hagree φ S Hpc Hcopy).
  Qed.

  (** Conversely, a step that writes [cnull] writes no register. *)
  Lemma regs_next_ok_cnull_jump i p lpc regs v n :
    regs_next_ok i p lpc regs cnull v n → regs_jump_agree i p lpc regs n.
  Proof.
    intros (sb & _ & Hagree) φ S Hpc Hcopy.
    by rewrite (Hagree φ S Hpc Hcopy) update_reg_cnull.
  Qed.

  (** The physical registers as copies of the owned ones, with strip bits. *)
  Lemma lregs_phys_strip R (regs : LReg) (r : Reg) :
    lregs_phys R regs r → (∀ v, regs !! cnull = Some v → v = lnull) →
    ∃ S : RegName → bool, ∀ x v0, regs !! x = Some v0 →
      r !!ᵣ x = Some (and_tag (S x) v0.(lw)) ∧ reg_phys R v0 (and_tag (S x) v0.(lw)) ∧
      (S x = false → strippable v0).
  Proof.
    intros Hphys Hcnull.
    exists (λ x, match regs !! x, r !! x with
                 | Some v0, Some w => bool_decide (w = v0.(lw) ∨ x = cnull)
                 | _, _ => true end).
    intros x v0 Hx. rewrite Hx. destruct (Hphys x v0 Hx) as (w & Hw & Hphys_x). rewrite Hw.
    destruct (decide (x = cnull)) as [-> | Hne].
    { rewrite (Hcnull v0 Hx) bool_decide_true; last by right.
      rewrite and_tag_true /=. split_and!; [done | apply reg_phys_lnull | done]. }
    rewrite /lookup_reg decide_False //.
    case_bool_decide as Hexact.
    { destruct Hexact as [-> | Hx_cnull]; last done. rewrite and_tag_true. split_and!; done. }
    destruct Hphys_x as [ [Heq | [Hclear Hstrip] ] Hquar]; first (exfalso; apply Hexact; by left).
    rewrite and_tag_false -Hclear. split_and!; [done | split; [by right | done] |].
    intros _. destruct Hstrip as [ [_ Hb] | [_ [b Hb] ] ]; first done.
    rewrite /heap_cap_base memory_cap_base_bounds in Hb. rewrite /strippable.
    destruct (memory_cap_bounds v0.(lw)); [by eexists | done].
  Qed.

End regs_pure.

(** ** The register steps in closed form

    The register step of an instruction in closed form is a lemma that
    concludes [regs_next_ok] or [regs_jump_agree] for it. [iInstr] finds
    these lemmas in the hint database [regs_next_ok_db], indexed by the
    instruction; each lemma is registered on the line after it. The
    settings below are global: the database is searched in client proofs,
    which do not import this file. *)
Create HintDb regs_next_ok_db discriminated.
#[global] Hint Constants Opaque : regs_next_ok_db.
#[global] Hint Opaque regs_next_ok regs_jump_agree llookup_reg lz_of_argument : regs_next_ok_db.
#[global] Hint Mode regs_next_ok - ! - - - - - - : regs_next_ok_db.
#[global] Hint Mode regs_jump_agree - ! - - - - : regs_next_ok_db.
(* Every such lemma at [cnull] serves the instruction with no destination. The
   converse [regs_jump_agree_next_ok] is not a hint: the two would loop. *)
#[global] Hint Extern 10 (regs_jump_agree _ _ _ _ _) =>
  simple eapply regs_next_ok_cnull_jump : regs_next_ok_db.

(** ** The generic rule *)

(** The outcome of a register step whose PC move gives [mv]: the move and
    the write of a word with [written_word_ok], or a fault. Griotte's PC
    move is [incrementPC_gen lpc n]; a move that never fails has no fault. *)
Definition regs_outcome `{MachineParameters} {k : kind} (mv : option LWord) (lpc : LWord)
    (regs : LReg) (dst : RegName) (written_word_ok : LWord → Prop)
    (lpc' : LWord) (regs' : LReg) (retv : tval k) : Prop :=
  match mv with
  | Some l => retv = NextIV ∧ lpc' = l ∧ ∃ v, written_word_ok v ∧ regs' = <[dst := v]ₗ> regs
  | None => faulted_outcome lpc regs lpc' regs' retv
  end.

(** The per-instruction side condition of the register rules: the
    instruction does not switch threads. *)
Definition regs_instr_ok (th : Thread) (i : instr) : Prop := sw_of (kind_of th) i = None.

Section regs_rules.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (** The witness [written_word_witness] is kept; its pure facts
      [written_word_witness_ok], read against the registry and the claim
      map, are available to the source. *)
  Lemma wp_regs_step E pc_p pc_g pc_b pc_e pc_a pc_π w dq i (regs : LReg) dst vS n sb
      (written_word_ok : LWord → Prop) (written_word_witness : iProp Σ)
      (written_word_witness_ok : RegState → gmap Addr AddrClaim → Prop) :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    lsource_witness_ok written_word_witness_ok regs (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
      vS sb written_word_ok →
    regs_next_agree_strip exec_opt i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst vS n sb →
    dst = cnull ∨ dst ∈ dom regs →
    (∀ R C,
       reg_auth R -∗
       addr_alloc_auth C -∗
       written_word_witness -∗
       ⌜written_word_witness_ok R C⌝) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        written_word_witness ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ lpc' regs' retv, RET retv;
        ⌜regs_outcome (incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n)
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst written_word_ok lpc' regs' retv⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        written_word_witness ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hsrc Hagree Hdst Hwitness Φ) "(>HPC & >Hpc_a & Hwit & >Hmap) HΦ".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [by rewrite Hdec | done |].
    iNext; iIntros (r sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (Hwitness with "HR HC Hwit") as %Hwit_ok.
    (* The strip bits of the owned registers. *)
    destruct (lregs_phys_strip R regs r Hregs) as [S HS].
    { intros v0 Hv0. eapply er_cnull; [exact Her | by eapply lookup_weaken]. }
    (* The source: the written word is well-formed. *)
    pose proof (er_pc _ _ _ _ _ _ _ Her) as Hpc.
    rewrite (erasure_pc_exact _ _ _ _ _ _ _ Her) in Hpc.
    assert (∀ x v0, regs !! x = Some v0 → reg_word_ok R C v0 ∧ reg_phys R v0 (and_tag (S x) v0.(lw)))
      as Hwords.
    { intros x v0 Hx. split; last apply (HS x v0 Hx).
      eapply er_reg_words; [exact Her | by eapply lookup_weaken]. }
    destruct (Hsrc R C st S (er_registry _ _ _ _ _ _ _ Her) Hwit_ok Hwords
                (er_pc_word _ _ _ _ _ _ _ Her) Hpc) as (Hok & Hphys & Hwritten).
    (* The agreement: the step writes the copy and moves the PC. *)
    rewrite Hdec /exec (Hagree (MkExecConf _ r sr m st td) S) /regs_effect in Hstep; [| done |].
    2: { intros x v0 Hx. by destruct (HS x v0 Hx) as (Hx_reg & _ & Hx_strip). }
    iApply (instr_close_reg_update_advancePC _ _ _ _ _ _ _ _ _ _ _ _ regs dst (vS S) _ n _ _ _
      (λ lpc' regs' retv, regs_outcome (incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n)
                            (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst written_word_ok
                            lpc' regs' retv)
      Her Hdst Hok Hstep Hphys with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [HΦ Hpc_a Hwit]").
    { intros lpc' ->. split_and!; [done | done | by exists (vS S)]. }
    { intros ->. apply faulted_outcome_refl. }
    iIntros (lpc' regs' retv Hout) "HPC Hmap". iApply "HΦ". by iFrame.
  Qed.

  (** The exact rule: a fixed written word [v]. *)
  Lemma wp_regs_next E pc_p pc_g pc_b pc_e pc_a pc_π w dq i (regs : LReg) dst v n sb lpc' :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    lsource_ok regs (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) v sb →
    regs_next_agree exec_opt i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst v n sb →
    dst = cnull ∨ dst ∈ dom regs →
    incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        [∗ map] k↦y ∈ <[dst := v]ₗ> regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hsrc Hagree Hdst Hinc Φ) "(HPC & Hpc_a & Hmap) HΦ".
    iApply (wp_regs_step _ _ _ _ _ _ _ _ _ _ _ dst (λ _, v) n sb (λ v', v' = v) emp%I (λ _ _, True)
      with "[$HPC $Hpc_a $Hmap]");
      [done | done | done | by apply lsource_ok_witness | exact Hagree | done | by iIntros |].
    iIntros "!>" (lpc0 regs' retv) "(%Hout & HPC & Hpc_a & _ & Hmap)".
    rewrite /regs_outcome Hinc in Hout. destruct Hout as (-> & -> & v' & -> & ->).
    iApply "HΦ". by iFrame.
  Qed.

  (** *** k-ary client rules: the destination first, its new word [v] *)

  Lemma wp_regs_next_gen_1 E pc_p pc_g pc_b pc_e pc_a pc_π w dq i r1 w1 v n lpc' :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n = Some lpc' →
    r1 ≠ cnull →
    regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) {[r1 := w1]} r1 v n →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ v }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hinc Hr1 (sb & Hsrc & Hagree) Φ) "(>HPC & >Hpc_a & >Hr1) HΦ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (wp_regs_next with "[$HPC $Hpc_a $Hmap]"); [exact Hdec | exact Hsw | exact Hvpc
      | exact Hsrc | exact Hagree | right; set_solver | exact Hinc |].
    iIntros "!> (HPC & Hpc_a & Hmap)".
    rewrite linsert_reg_not_cnull // insert_singleton decide_True //.
    iDestruct (regs_of_map_1 with "Hmap") as "Hr1". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_regs_next_gen_2 E pc_p pc_g pc_b pc_e pc_a pc_π w dq i r1 w1 r2 w2 v n lpc' :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n = Some lpc' →
    r1 ≠ cnull →
    (r1 ≠ r2 →
     regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
       (<[r1 := w1]> (<[r2 := w2]> ∅)) r1 v n) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ v ∗
        r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hinc Hr1 Hnext_ok Φ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) HΦ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    destruct (Hnext_ok Hne) as (sb & Hsrc & Hagree).
    iApply (wp_regs_next with "[$HPC $Hpc_a $Hmap]"); [exact Hdec | exact Hsw | exact Hvpc
      | exact Hsrc | exact Hagree | right; set_solver | exact Hinc |].
    iIntros "!> (HPC & Hpc_a & Hmap)".
    rewrite linsert_reg_not_cnull // insert_insert decide_True //.
    iDestruct (regs_of_map_2 with "Hmap") as "[Hr1 Hr2]"; first done. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_regs_next_gen_3 E pc_p pc_g pc_b pc_e pc_a pc_π w dq i r1 w1 r2 w2 r3 w3 v n lpc' :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n = Some lpc' →
    r1 ≠ cnull →
    (r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
     regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
       (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅))) r1 v n) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 ∗
        ▷ r3 ↦ᵣ w3 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ v ∗
        r2 ↦ᵣ w2 ∗
        r3 ↦ᵣ w3 }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hinc Hr1 Hnext_ok Φ) "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Hr3) HΦ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap (%Hne12 & %Hne13 & %Hne23)]".
    destruct (Hnext_ok Hne12 Hne13 Hne23) as (sb & Hsrc & Hagree).
    iApply (wp_regs_next with "[$HPC $Hpc_a $Hmap]"); [exact Hdec | exact Hsw | exact Hvpc
      | exact Hsrc | exact Hagree | right; set_solver | exact Hinc |].
    iIntros "!> (HPC & Hpc_a & Hmap)".
    rewrite linsert_reg_not_cnull // insert_insert decide_True //.
    iDestruct (regs_of_map_3 with "Hmap") as "(Hr1 & Hr2 & Hr3)"; [done | done | done |].
    iApply "HΦ". iFrame.
  Qed.

  (** The PC moved by [1]. *)
  Lemma wp_regs_next_1 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i r1 w1 v :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) {[r1 := w1]} r1 v 1 →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ v }}}.
  Proof.
    intros Hdec Hsw Hvpc Hpc_a' Hr1 Hok.
    eapply wp_regs_next_gen_1; [exact Hdec | exact Hsw | exact Hvpc | | exact Hr1 | exact Hok].
    by rewrite /incrementPC_gen Hpc_a'.
  Qed.

  Lemma wp_regs_next_2 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i r1 w1 r2 w2 v :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    (r1 ≠ r2 →
     regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
       (<[r1 := w1]> (<[r2 := w2]> ∅)) r1 v 1) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ v ∗
        r2 ↦ᵣ w2 }}}.
  Proof.
    intros Hdec Hsw Hvpc Hpc_a' Hr1 Hok.
    eapply wp_regs_next_gen_2; [exact Hdec | exact Hsw | exact Hvpc | | exact Hr1 | exact Hok].
    by rewrite /incrementPC_gen Hpc_a'.
  Qed.

  Lemma wp_regs_next_3 E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i r1 w1 r2 w2 r3 w3 v :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    (r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
     regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
       (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅))) r1 v 1) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 ∗
        ▷ r3 ↦ᵣ w3 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ v ∗
        r2 ↦ᵣ w2 ∗
        r3 ↦ᵣ w3 }}}.
  Proof.
    intros Hdec Hsw Hvpc Hpc_a' Hr1 Hok.
    eapply wp_regs_next_gen_3; [exact Hdec | exact Hsw | exact Hvpc | | exact Hr1 | exact Hok].
    by rewrite /incrementPC_gen Hpc_a'.
  Qed.

  (** *** k-ary rules with no destination: an operand may be [cnull] *)

  Lemma wp_regs_jump_0 E pc_p pc_g pc_b pc_e pc_a pc_π w dq i n lpc' :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n = Some lpc' →
    regs_jump_agree i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ∅ n →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hinc Hagree Φ) "(HPC & Hpc_a) HΦ".
    destruct (regs_jump_agree_next_ok _ _ _ _ _ Hagree) as (sb & Hsrc & Hagree_next).
    iApply (wp_regs_next with "[$HPC $Hpc_a]"); [exact Hdec | exact Hsw | exact Hvpc
      | exact Hsrc | exact Hagree_next | by left | exact Hinc | by rewrite big_sepM_empty |].
    iIntros "!> (HPC & Hpc_a & _)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_regs_jump_1 E pc_p pc_g pc_b pc_e pc_a pc_π w dq i r1 w1 n lpc' :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n = Some lpc' →
    regs_jump_agree i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) {[r1 := w1]} n →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ w1 }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hinc Hagree Φ) "(>HPC & >Hpc_a & >Hr1) HΦ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    destruct (regs_jump_agree_next_ok _ _ _ _ _ Hagree) as (sb & Hsrc & Hagree_next).
    iApply (wp_regs_next with "[$HPC $Hpc_a $Hmap]"); [exact Hdec | exact Hsw | exact Hvpc
      | exact Hsrc | exact Hagree_next | by left | exact Hinc |].
    iIntros "!> (HPC & Hpc_a & Hmap)". rewrite linsert_reg_cnull.
    iDestruct (regs_of_map_1 with "Hmap") as "Hr1". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_regs_jump_2 E pc_p pc_g pc_b pc_e pc_a pc_π w dq i r1 w1 r2 w2 n lpc' :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n = Some lpc' →
    (r1 ≠ r2 →
     regs_jump_agree i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
       (<[r1 := w1]> (<[r2 := w2]> ∅)) n) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ w1 ∗
        r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hinc Hagree Φ) "(>HPC & >Hpc_a & >Hr1 & >Hr2) HΦ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %Hne]".
    destruct (regs_jump_agree_next_ok _ _ _ _ _ (Hagree Hne)) as (sb & Hsrc & Hagree_next).
    iApply (wp_regs_next with "[$HPC $Hpc_a $Hmap]"); [exact Hdec | exact Hsw | exact Hvpc
      | exact Hsrc | exact Hagree_next | by left | exact Hinc |].
    iIntros "!> (HPC & Hpc_a & Hmap)". rewrite linsert_reg_cnull.
    iDestruct (regs_of_map_2 with "Hmap") as "[Hr1 Hr2]"; first done. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_regs_jump_3 E pc_p pc_g pc_b pc_e pc_a pc_π w dq i r1 w1 r2 w2 r3 w3 n lpc' :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    incrementPC_gen (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) n = Some lpc' →
    (r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
     regs_jump_agree i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
       (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅))) n) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 ∗
        ▷ r3 ↦ᵣ w3 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ w1 ∗
        r2 ↦ᵣ w2 ∗
        r3 ↦ᵣ w3 }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hinc Hagree Φ) "(>HPC & >Hpc_a & >Hr1 & >Hr2 & >Hr3) HΦ".
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hr3") as "[Hmap (%Hne12 & %Hne13 & %Hne23)]".
    destruct (regs_jump_agree_next_ok _ _ _ _ _ (Hagree Hne12 Hne13 Hne23))
      as (sb & Hsrc & Hagree_next).
    iApply (wp_regs_next with "[$HPC $Hpc_a $Hmap]"); [exact Hdec | exact Hsw | exact Hvpc
      | exact Hsrc | exact Hagree_next | by left | exact Hinc |].
    iIntros "!> (HPC & Hpc_a & Hmap)". rewrite linsert_reg_cnull.
    iDestruct (regs_of_map_3 with "Hmap") as "(Hr1 & Hr2 & Hr3)"; [done | done | done |].
    iApply "HΦ". iFrame.
  Qed.

  (** *** k-ary rules whose destination may be [cnull]

      A write to [cnull] leaves its word unchanged: the destination holds
      its old word if it is [cnull], the written word otherwise. *)

  Lemma wp_regs_next_1_any_dst E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i r1 w1 v :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) {[r1 := w1]} r1 v 1 →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ (if decide (r1 = cnull) then w1 else v) }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hpc_a' Hok Φ) "(HPC & Hpc_a & Hr1) HΦ".
    destruct (decide (r1 = cnull)) as [-> | Hr1].
    - iApply (wp_regs_jump_1 with "[$HPC $Hpc_a $Hr1]");
        [exact Hdec | exact Hsw | exact Hvpc
        | exact (incrementPC_gen_add true _ _ _ _ _ _ _ _ Hpc_a')
        | by eapply regs_next_ok_cnull_jump |].
      iNext. iIntros "H". by iApply "HΦ".
    - by iApply (wp_regs_next_1 with "[$HPC $Hpc_a $Hr1]").
  Qed.

  Lemma wp_regs_next_2_any_dst E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i r1 w1 r2 w2 v :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (r1 ≠ r2 →
     regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
       (<[r1 := w1]> (<[r2 := w2]> ∅)) r1 v 1) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ (if decide (r1 = cnull) then w1 else v) ∗
        r2 ↦ᵣ w2 }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hpc_a' Hok Φ) "(HPC & Hpc_a & Hr1 & Hr2) HΦ".
    destruct (decide (r1 = cnull)) as [-> | Hr1].
    - iApply (wp_regs_jump_2 with "[$HPC $Hpc_a $Hr1 $Hr2]");
        [exact Hdec | exact Hsw | exact Hvpc
        | exact (incrementPC_gen_add true _ _ _ _ _ _ _ _ Hpc_a')
        | intros Hne; by eapply regs_next_ok_cnull_jump, Hok |].
      iNext. iIntros "H". by iApply "HΦ".
    - by iApply (wp_regs_next_2 with "[$HPC $Hpc_a $Hr1 $Hr2]").
  Qed.

  Lemma wp_regs_next_3_any_dst E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i r1 w1 r2 w2 r3 w3 v :
    decodeInstrW w.(lw) = i → regs_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    (r1 ≠ r2 → r1 ≠ r3 → r2 ≠ r3 →
     regs_next_ok i pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)
       (<[r1 := w1]> (<[r2 := w2]> (<[r3 := w3]> ∅))) r1 v 1) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ r2 ↦ᵣ w2 ∗
        ▷ r3 ↦ᵣ w3 }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ (if decide (r1 = cnull) then w1 else v) ∗
        r2 ↦ᵣ w2 ∗
        r3 ↦ᵣ w3 }}}.
  Proof.
    iIntros (Hdec Hsw Hvpc Hpc_a' Hok Φ) "(HPC & Hpc_a & Hr1 & Hr2 & Hr3) HΦ".
    destruct (decide (r1 = cnull)) as [-> | Hr1].
    - iApply (wp_regs_jump_3 with "[$HPC $Hpc_a $Hr1 $Hr2 $Hr3]");
        [exact Hdec | exact Hsw | exact Hvpc
        | exact (incrementPC_gen_add true _ _ _ _ _ _ _ _ Hpc_a')
        | intros Hne12 Hne13 Hne23; by eapply regs_next_ok_cnull_jump, Hok |].
      iNext. iIntros "H". by iApply "HΦ".
    - by iApply (wp_regs_next_3 with "[$HPC $Hpc_a $Hr1 $Hr2 $Hr3]").
  Qed.

End regs_rules.
