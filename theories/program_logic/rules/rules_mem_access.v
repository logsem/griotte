From iris.proofmode Require Import proofmode.
From griotte Require Import rules_base memory_region.

(** The erasure lemmas, the closers and [SI_close] take their hypotheses
    only: the other arguments are determined by them. *)
#[local] Arguments llookup_reg_cap {regs r t p g b e a}.
#[local] Arguments llookup_reg_phys {MP R regs r x v}.
#[local] Arguments erasure_regs_incl {MP R C σ lpc lreg lsreg lmem regs}.
#[local] Arguments erasure_lookup_mem {MP R C σ lpc lreg lsreg lmem a v}.
#[local] Arguments erasure_store {MP R C pc r sr m st td lpc lreg lsreg lmem a v v' pw}.
#[local] Arguments erasure_incrementPC {MP R C pc r sr m st td lpc lpc' lreg lsreg lmem}.
#[local] Arguments erasure_incrementPC_fail {MP R C pc r sr m st td lpc lreg lsreg lmem n}.
#[local] Arguments er_registry {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments er_mmio {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments er_pc {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments erasure_set_timedevs {MP R C σ lpc lreg lsreg lmem} td.
#[local] Arguments SI_close {MP Σ pcG0 gen_heapGS0 gen_heapGS1 gen_heapGS2 gen_heapGS3
  allocRegistryG0 addrAllocG0 H mtdcG0 mieG0 mpieG0 postureG0 mtdcLentG0 σ lpc lreg ls lmem R C}.
#[local] Arguments instr_close_reg_update {MP Σ ceriseg k pc r sr m st td lpc lreg lsreg lmem R C
  regs dst v w c σ' Φ} P.
#[local] Arguments instr_close_pc_update {MP Σ ceriseg k pc r sr m st td lpc lreg lsreg lmem R C
  regs n c σ' Φ} P.

(** * Memory accesses lifted from their membership

    A memory access (a load or a store) is described by a pure membership:
    every successful step of the instruction is one of the steps of
    [load_step] or [store_step], authorised by a register and an offset
    given by the instruction. The WP rules of this file are proved once
    from that membership, for any instruction that has it: one master rule
    per kind of access, whose instances are the rule of the fundamental
    theorem (faults allowed, no witness) and the rules that exclude the
    fault on a cell (with an agreement of the step, and a witness that
    keeps the authority live). *)

Inductive mem_access_kind := MemAccessRead | MemAccessWrite.

Definition mem_access_perm (k : mem_access_kind) : Perm → bool :=
  match k with MemAccessRead => readAllowed | MemAccessWrite => writeAllowed end.

(** The per-instruction side condition of the memory rules: the
    instruction does not switch threads. *)
Definition mem_instr_ok (th : Thread) (i : instr) : Prop := sw_of (kind_of th) i = None.

(** Closes [mem_instr_ok th i] for a concrete instruction. *)
Ltac solve_mem_instr_ok := rewrite /mem_instr_ok; by apply sw_of_none.

(** ** Pure part *)

Section mem_access_pure.
  Context `{MP : MachineParameters}.

  (** The register [r] authorises an access of kind [k] at [ea]: it holds
      a capability whose address plus [imm] is [ea], within its bounds,
      with the permission of [k]. A read is [reg_allows_load_imm] of
      [rules_Load.v]; a write is [reg_allows_store_imm] of [rules_Store.v]. *)
  Definition reg_allows_mem_access k (regs : LReg) (r : RegName) (imm : Z)
      p g b e a (ea : Addr) : Prop :=
    lw <$> regs !!ₗ r = Some (Cap p g b e a) ∧ (a + imm)%a = Some ea ∧
    mem_access_perm k p = true ∧ withinBounds b e ea = true.

  (** Whether [r] authorises an access is decidable. *)
  Lemma reg_allows_mem_access_cases k regs r imm :
    (∃ p g b e a ea, reg_allows_mem_access k regs r imm p g b e a ea) ∨
    ¬ ∃ p g b e a ea, reg_allows_mem_access k regs r imm p g b e a ea.
  Proof.
    destruct (lw <$> regs !!ₗ r) as [ [z | [ [|] p g b e a | tsr psr gsr bsr esr asr] | sk ts ps gs bs es as_ | ot sb] |] eqn:Hr;
      try (right; intros (p1 & g1 & b1 & e1 & a1 & ea1 & Hsrc & _); congruence).
    destruct (a + imm)%a as [ea|] eqn:Hadd;
      [destruct (mem_access_perm k p) eqn:Hperm, (withinBounds b e ea) eqn:Hwb;
       [left; by exists p, g, b, e, a, ea|..]|];
      right; intros (p1 & g1 & b1 & e1 & a1 & ea1 & Hsrc & Hadd1 & Hperm1 & Hwb1);
      rewrite Hr in Hsrc; simplify_eq; congruence.
  Qed.

  (** The authorising capability and the accessed address are determined
      by the registers. *)
  Lemma reg_allows_mem_access_det {k regs r imm p g b e a ea p1 g1 b1 e1 a1 ea1} :
    reg_allows_mem_access k regs r imm p g b e a ea →
    reg_allows_mem_access k regs r imm p1 g1 b1 e1 a1 ea1 →
    p1 = p ∧ g1 = g ∧ b1 = b ∧ e1 = e ∧ a1 = a ∧ ea1 = ea.
  Proof. intros (Hsrc & Hadd & _) (Hsrc1 & Hadd1 & _). rewrite Hsrc in Hsrc1. by simplify_eq. Qed.

  (** An access permission is not [O]. *)
  Lemma mem_access_perm_nonO k p : mem_access_perm k p = true → isO p = false.
  Proof. destruct k; [apply readAllowed_nonO|apply writeAllowed_nonO]. Qed.

  (** Every address the register may access is an exposed device, absent
      from [mem], or a cell of [mem], wholly owned for a write. A cell is
      off the devices (the erasure says so). *)
  Definition mem_access_footprint k regs r imm (mem : LMem) (dfracs : gmap Addr dfrac) : Prop :=
    ∀ p g b e a ea, reg_allows_mem_access k regs r imm p g b e a ea →
      (is_exposed_mmio_address ea = true ∧ mem !! ea = None) ∨
      (is_Some (mem !! ea) ∧
       (k = MemAccessWrite → dfracs !! ea = Some (DfracOwn 1))).

  (** An untagged register authorises no access. *)
  Lemma mem_access_footprint_untagged k regs r imm mem dfracs v :
    regs !! r = Some v → get_tag v.(lw) = false → mem_access_footprint k regs r imm mem dfracs.
  Proof.
    intros Hr Ht p g b e a ea (Hsrc & _).
    destruct (llookup_reg_cap Hsrc) as (_ & π & Hr').
    rewrite Hr in Hr'. by simplify_eq.
  Qed.

  (** The success of the capability checks, as [data_cap_check] states
      them. *)
  Definition mem_access_authorised (perm_ok : Perm → bool) (φ : ExecConf) (r : RegName) (imm : Z)
      (p : Perm) (ea : Addr) : Prop :=
    ∃ g b e a, reg φ !!ᵣ r = Some (Cap p g b e a) ∧ perm_ok p = true ∧
               (a + imm)%a = Some ea ∧ withinBounds b e ea = true.

  (** [mem_access_authorised] is exactly the success of the machine's [data_cap_check]. *)
  Lemma mem_access_authorised_data_cap_check perm_ok code φ r imm ea :
    (∃ p, mem_access_authorised perm_ok φ r imm p ea) ↔
    ∃ w, reg φ !!ᵣ r = Some w ∧ data_cap_check perm_ok code r w imm = inr ea.
  Proof.
    split.
    - intros (p & g & b & e & a & Hr & Hp & Hea & Hwb).
      exists (Cap p g b e a). by rewrite /= Hp Hea Hwb.
    - intros (w & Hr & Hchk).
      destruct w as [| [ [] p g b e a | ] | | ]; cbn in Hchk;
        repeat case_match; simplify_eq.
      by exists p, g, b, e, a.
  Qed.

  (** Two authorisations by the same register and offset authorise the
      same permission and address. *)
  Lemma mem_access_authorised_det {perm_ok1 perm_ok2 φ r imm p1 ea1 p2 ea2} :
    mem_access_authorised perm_ok1 φ r imm p1 ea1 →
    mem_access_authorised perm_ok2 φ r imm p2 ea2 →
    p1 = p2 ∧ ea1 = ea2.
  Proof.
    intros (g1 & b1 & e1 & a1 & Hr1 & _ & Hadd1 & _) (g2 & b2 & e2 & a2 & Hr2 & _ & Hadd2 & _).
    rewrite Hr1 in Hr2. by simplify_eq.
  Qed.

  (** What a write to memory at [ea] does to the rest of the machine:
      nothing. This is the place where such an effect (for example on a
      watermark) enters; a model with one changes this definition and the
      closers and tactics that unfold it ([wp_store_step_gen],
      [solve_mem_access_member_with], [Store_agree]). *)
  Definition store_effect (ea : Addr) (φ : ExecConf) : ExecConf := φ.

  (** Loads, whose result on a cell is the loaded word through the filter
      [flt]. The authorising register and offset come from the
      instruction, so that the fundamental theorem can open the region
      before the step. *)
  Inductive load_step (flt : ExecConf → Perm → Word → option Word)
      (dst r : RegName) (imm : Z) (φ : ExecConf) (c : Conf) : Prop :=
  (* A plain load, live or quarantined shadow, or off the heap. *)
  | ls_cell p ea v w :
      mem_access_authorised readAllowed φ r imm p ea → is_mmio_address ea = false →
      mem φ !! ea = Some v → flt φ p v = Some w →
      nextPC (φ .[dst :=ᵣ w]) = Some c → load_step flt dst r imm φ c
  (* A load answered by a device. *)
  | ls_device p ea w :
      mem_access_authorised readAllowed φ r imm p ea → is_mmio_address ea = true →
      mmio_load φ ea = Some w →
      nextPC (φ .[dst :=ᵣ w]) = Some c → load_step flt dst r imm φ c.

  (** Stores, of a word that [stored_word_ok] allows. *)
  Inductive store_step (stored_word_ok : ExecConf → Word → Prop) (r : RegName) (imm : Z)
      (φ : ExecConf) (c : Conf) : Prop :=
  (* A plain store to a cell. *)
  | ss_cell p ea w :
      mem_access_authorised writeAllowed φ r imm p ea → is_mmio_address ea = false →
      is_Some (mem φ !! ea) → stored_word_ok φ w →
      nextPC ((store_effect ea φ) .[ea :=ₐ store_word p w]) = Some c →
      store_step stored_word_ok r imm φ c
  (* A store answered by a device. *)
  | ss_device p ea w φ' :
      mem_access_authorised writeAllowed φ r imm p ea → is_mmio_address ea = true →
      mmio_store φ ea w = Some φ' → nextPC φ' = Some c → stored_word_ok φ w →
      store_step stored_word_ok r imm φ c.

  (** The membership, for a step function [step]: the WP rules take
      [exec_opt]; another semantics reuses the definitions and tactics with
      its own. *)
  Definition load_member (step : instr → Perm → ExecConf → option Conf)
      (flt : ExecConf → Perm → Word → option Word) (i : instr) (dst r : RegName) (imm : Z) : Prop :=
    ∀ p φ c, step i p φ = Some c → load_step flt dst r imm φ c.
  Definition store_member (step : instr → Perm → ExecConf → option Conf)
      (stored_word_ok : ExecConf → Word → Prop) (i : instr) (r : RegName) (imm : Z) : Prop :=
    ∀ p φ c, step i p φ = Some c → store_step stored_word_ok r imm φ c.

  (** The filter of Griotte's CLoad: the shadow table of the
      configuration. *)
  Definition griotte_load_filter (φ : ExecConf) : Perm → Word → option Word :=
    load_filter (shadowtbl φ).

  (** The agreement of a load: on the checked path to a cell, the step is
      the access. *)
  Definition load_agree (step : instr → Perm → ExecConf → option Conf)
      (flt : ExecConf → Perm → Word → option Word) (i : instr) (dst r : RegName) (imm : Z) : Prop :=
    ∀ pl φ p ea pv w,
      mem_access_authorised readAllowed φ r imm p ea → is_mmio_address ea = false →
      mem φ !! ea = Some pv → flt φ p pv = Some w →
      step i pl φ = nextPC (φ .[dst :=ᵣ w]).

  (** The agreement of a store: on the checked path to a cell, the step is
      the access, for any word that [stored_word_ok] allows. *)
  Definition store_agree (step : instr → Perm → ExecConf → option Conf)
      (stored_word_ok : ExecConf → Word → Prop) (i : instr) (r : RegName) (imm : Z) : Prop :=
    ∀ pl φ p ea w,
      mem_access_authorised writeAllowed φ r imm p ea → is_mmio_address ea = false →
      is_Some (mem φ !! ea) → stored_word_ok φ w →
      step i pl φ = nextPC ((store_effect ea φ) .[ea :=ₐ store_word p w]).

  (** The devices answer loads with integers. *)
  Lemma mmio_load_untagged φ ea w : mmio_load φ ea = Some w → get_tag w = false.
  Proof.
    rewrite /mmio_load /shadow_load /revoker_load /time_dev_load.
    repeat case_match; intros; simplify_option_eq; done.
  Qed.

  (** A tagged physical authority is the logical one. *)
  Lemma mem_access_authorised_reg_allows k R regs φ r imm p ea :
    lregs_phys R regs (reg φ) → r ∈ dom regs → mem_access_authorised (mem_access_perm k) φ r imm p ea →
    ∃ g b e a, reg_allows_mem_access k regs r imm p g b e a ea.
  Proof.
    intros Hphys Hr (g & b & e & a & Hlook & Hperm & Hadd & Hwb).
    destruct (proj2 (is_Some_llookup_reg regs r)) as [v Hv].
    { right. by apply elem_of_dom. }
    destruct (llookup_reg_phys Hphys Hv) as (s & Hlook' & _).
    rewrite Hlook' in Hlook. injection Hlook as Heq.
    assert (s = true) as ->.
    { apply (f_equal get_tag) in Heq. rewrite get_tag_and_tag in Heq.
      by destruct s. }
    rewrite and_tag_true in Heq.
    exists g, b, e, a. split_and!; [|done..]. by rewrite Hv /= Heq.
  Qed.
  #[local] Arguments mem_access_authorised_reg_allows k {R regs φ r imm p ea}.

  (** A live logical authority is the physical one: its identifier is not
      stale and its bounds are not empty, so its copy is exact. *)
  Lemma mem_access_authorised_live k R C φ lpc lreg lsreg lmem regs r imm p g b e a ea :
    erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg →
    (∀ v, regs !! r = Some v → ¬ stale_id R v) →
    reg_allows_mem_access k regs r imm p g b e a ea →
    mem_access_authorised (mem_access_perm k) φ r imm p ea.
  Proof.
    intros Her Hincl Hlive (Hsrc & Hadd & Hperm & Hwb).
    destruct (llookup_reg_cap Hsrc) as (Hne & π & Hr).
    assert (regs !!ₗ r = Some (Cap p g b e a @@? π)) as Hr'.
    { by rewrite llookup_reg_not_cnull. }
    destruct (llookup_reg_phys (erasure_regs_incl Her Hincl) Hr') as (s & Hlook & Hrel).
    cbn [lw] in Hlook, Hrel.
    pose proof (proj1 (withinBounds_true_iff b e ea) Hwb) as [Hb He].
    assert (and_tag s (Cap p g b e a) = Cap p g b e a) as Hexact.
    { apply (reg_phys_exact_cond R (Cap p g b e a @@? π)); [exact Hrel | by apply Hlive |].
      apply (nonempty_exact_cond (Cap p g b e a @@? π) b e); first done.
      solve_addr. }
    rewrite Hexact in Hlook.
    exists g, b, e, a. split_and!; done.
  Qed.
  #[local] Arguments mem_access_authorised_live k {R C φ lpc lreg lsreg lmem regs r imm p g b e a ea}.

  (** A configuration whose PC is a copy of a logical PC that increments
      moves its PC. *)
  Lemma nextPC_is_Some_erasure R C φ φ' lpc lreg lsreg lmem lpc' :
    erasure R C φ lpc lreg lsreg lmem → pcc φ' = pcc φ →
    incrementPC lpc = Some lpc' → is_Some (nextPC φ').
  Proof.
    intros Her Hpc Hinc. destruct φ' as [pc' rf sr m st td]. cbn in Hpc. subst pc'.
    destruct (incrementPC_gen_phys R lpc lpc' (pcc φ) rf sr m st td 1 (er_pc Her) Hinc)
      as (pc'' & Hadv & _).
    rewrite /nextPC Hadv. by eexists.
  Qed.

  (** On a copy of the owned registers ([regs_fault]'s premise), a register
      read by the instruction has a copy. *)
  Lemma regs_fault_llookup (regs : LReg) φ r v :
    (∀ x v0, regs !! x = Some v0 → ∃ s, reg φ !!ᵣ x = Some (and_tag s v0.(lw))) →
    regs !!ₗ r = Some v →
    ∃ s, reg φ !!ᵣ r = Some (and_tag s v.(lw)).
  Proof.
    intros Hcopy Hr. rewrite /llookup_reg in Hr. case_decide as Hcnull; simplify_eq.
    - exists true. simplify_eq. by rewrite lookup_reg_cnull and_tag_true.
    - by apply Hcopy.
  Qed.

  (** Every word that [stored_word_ok] allows lifts to a logical word with [Q]. *)
  Definition store_lift (stored_word_ok : ExecConf → Word → Prop) (Q : LWord → Prop) (regs : LReg) :
      Prop :=
    ∀ R C φ lpc lreg lsreg lmem w, erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg →
      stored_word_ok φ w → ∃ v, Q v ∧ reg_word_ok R C v ∧ reg_phys R v w.

  (** Some word is allowed by [stored_word_ok]. *)
  Definition store_lift_some (stored_word_ok : ExecConf → Word → Prop) (regs : LReg) : Prop :=
    ∀ R C φ lpc lreg lsreg lmem, erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg →
      ∃ w, stored_word_ok φ w.

  (** [stored_word_ok] allows exactly one word, a copy of the logical word [v]. *)
  Definition store_lift_exact (stored_word_ok : ExecConf → Word → Prop) (v : LWord) (regs : LReg) :
      Prop :=
    ∀ R C φ lpc lreg lsreg lmem, erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg →
      ∃ w, stored_word_ok φ w ∧ reg_word_ok R C v ∧ reg_phys R v w ∧
        ∀ w', stored_word_ok φ w' → w' = w.

  Lemma store_lift_exact_lift stored_word_ok v regs :
    store_lift_exact stored_word_ok v regs → store_lift stored_word_ok (λ v', v' = v) regs.
  Proof.
    intros Hexact R C φ lpc lreg lsreg lmem w Her Hincl Hw.
    destruct (Hexact R C φ lpc lreg lsreg lmem Her Hincl) as (w0 & _ & Hok & Hphys & Huniq).
    rewrite (Huniq w Hw). exists v. by split_and!.
  Qed.

  Lemma store_lift_exact_some stored_word_ok v regs :
    store_lift_exact stored_word_ok v regs → store_lift_some stored_word_ok regs.
  Proof.
    intros Hexact R C φ lpc lreg lsreg lmem Her Hincl.
    destruct (Hexact R C φ lpc lreg lsreg lmem Her Hincl) as (w & Hw & _). by exists w.
  Qed.

  (** The word of an argument, an integer or a register: its physical copy. *)
  Lemma store_lift_argument regs ρ v :
    lword_of_argument regs ρ = Some v →
    store_lift_exact (λ φ w, word_of_argument (reg φ) ρ = Some w) v regs.
  Proof.
    intros Hv R C φ lpc lreg lsreg lmem Her Hincl.
    destruct ρ as [z | r0]; cbn [lword_of_argument] in Hv.
    - injection Hv as <-. exists (WInt z).
      split_and!; [done | by apply reg_word_ok_untagged | by apply reg_phys_untagged |].
      intros w' Hw'. by simplify_eq/=.
    - destruct (llookup_reg_phys (erasure_regs_incl Her Hincl) Hv) as (s & Hlook & Hphys).
      exists (and_tag s v.(lw)).
      split_and!; [exact Hlook | by eapply erasure_llookup_reg_word | exact Hphys |].
      intros w' Hw'. cbn [word_of_argument] in Hw'. rewrite Hlook in Hw'. by simplify_eq.
  Qed.

  (** ** Outcomes *)

  (** A fault, or a read of a cell of [mem] through [post], or a read of
      a device. The PC moves to [mv] (Griotte's move is [incrementPC lpc]). *)
  Definition load_result {kd : kind} (post : Perm → LWord → LWord → Prop) (mv : option LWord)
      lpc regs dst r imm (mem : LMem) lpc' regs' (retv : tval kd) : Prop :=
    faulted_outcome lpc regs lpc' regs' retv ∨
    ∃ p g b e a ea, reg_allows_mem_access MemAccessRead regs r imm p g b e a ea ∧ retv = NextIV ∧
      mv = Some lpc' ∧
      ((∃ v v', mem !! ea = Some v ∧ post p v v' ∧ regs' = <[dst := v']ₗ> regs) ∨
       (is_exposed_mmio_address ea = true ∧ mem !! ea = None ∧
        ∃ w, get_tag w = false ∧ regs' = <[dst := MkLWord w None]ₗ> regs)).

  (** A fault, or a write of a word with [Q] to a cell of [mem], or a write
      to a device. The PC moves to [mv]. *)
  Definition store_result {kd : kind} (Q : LWord → Prop) (mv : option LWord)
      lpc regs r imm (mem : LMem) lpc' mem' (retv : tval kd) : Prop :=
    faulted_outcome lpc mem lpc' mem' retv ∨
    ∃ p g b e a ea, reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea ∧ retv = NextIV ∧
      mv = Some lpc' ∧
      ((∃ v, Q v ∧ is_Some (mem !! ea) ∧ mem' = <[ea := lstore_word p v]> mem) ∨
       (is_exposed_mmio_address ea = true ∧ mem !! ea = None ∧ mem' = mem)).

  (** The register authorises an access to a cell of [mem]. *)
  Definition mem_access_cell k regs r imm (mem : LMem) : Prop :=
    ∃ p g b e a ea, reg_allows_mem_access k regs r imm p g b e a ea ∧ is_Some (mem !! ea).

  (** Progress: an access to a cell whose PC moves does not fault. *)
  Definition mem_access_progress {kd : kind} k regs r imm (mem : LMem) (mv : option LWord)
      (retv : tval kd) : Prop :=
    mem_access_cell k regs r imm mem → is_Some mv → retv = NextIV.

  (** ** Load witnesses *)

  (** What a load may return, given the facts [R] and [C] of a witness: on
      every erasure, the filter succeeds on the copy of a cell, and some
      logical word with [post] is a copy of the result. *)
  Definition load_choice_ok (flt : ExecConf → Perm → Word → option Word)
      (post : Perm → LWord → LWord → Prop) (R : RegState) (C : gmap Addr AddrClaim) : Prop :=
    ∀ φ lpc lreg lsreg lmem lv pv p, erasure R C φ lpc lreg lsreg lmem → mem_word_ok R C lv pv →
      ∃ pl v', flt φ p pv = Some pl ∧ post p lv v' ∧ reg_word_ok R C v' ∧ reg_phys R v' pl.

  (** The same, for a given result of the filter. *)
  Lemma load_choice_ok_inv {flt post R C φ lpc lreg lsreg lmem} :
    load_choice_ok flt post R C → erasure R C φ lpc lreg lsreg lmem →
    ∀ lv pv p pl, mem_word_ok R C lv pv → flt φ p pv = Some pl →
      ∃ v', post p lv v' ∧ reg_word_ok R C v' ∧ reg_phys R v' pl.
  Proof.
    intros Hok Her lv pv p pl Hmok Hflt.
    destruct (Hok φ lpc lreg lsreg lmem lv pv p Her Hmok) as (pl' & v' & Hflt' & Hrest).
    rewrite Hflt in Hflt'. injection Hflt' as <-. by exists v'.
  Qed.

  (** The exact load: the logical word as [lload_word] reads it. *)
  Definition load_exact (p : Perm) (lv v' : LWord) : Prop := v' = lload_word p lv.

  (** ** Inversions *)

  (** A load step gives the loaded logical word, chosen by [post], and its
      physical copy. *)
  Lemma load_step_inv flt post R C φ lpc lreg lsreg lmem regs dst r imm (mem : LMem) dfracs c :
    erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg → r ∈ dom regs → mem ⊆ lmem →
    (∀ lv pv p pl, mem_word_ok R C lv pv → flt φ p pv = Some pl →
       ∃ v', post p lv v' ∧ reg_word_ok R C v' ∧ reg_phys R v' pl) →
    mem_access_footprint MemAccessRead regs r imm mem dfracs → load_step flt dst r imm φ c →
    ∃ p g b e a ea v pw, reg_allows_mem_access MemAccessRead regs r imm p g b e a ea ∧
      reg_word_ok R C v ∧ reg_phys R v pw ∧ nextPC (φ .[dst :=ᵣ pw]) = Some c ∧
      ((∃ lv, mem !! ea = Some lv ∧ post p lv v) ∨
       (is_exposed_mmio_address ea = true ∧ mem !! ea = None ∧
        get_tag pw = false ∧ v = MkLWord pw None)).
  Proof.
    intros Her Hincl Hr Hmem Hchoice Hok Hstep.
    pose proof (erasure_regs_incl Her Hincl) as Hphys.
    destruct Hstep as [p ea pv pw Hauth Hmmio Hpv Hfilter Hnext
                      |p ea pw Hauth Hmmio Hload Hnext].
    - destruct (mem_access_authorised_reg_allows MemAccessRead Hphys Hr Hauth)
        as (g & b & e & a & Hacc).
      destruct (Hok _ _ _ _ _ _ Hacc) as [ [Hexp _] | ([lv Hlv] & _) ].
      { by rewrite not_mmio_not_exposed_mmio in Hexp. }
      destruct (erasure_lookup_mem Her (lookup_weaken _ _ _ _ Hlv Hmem))
        as (pv' & Hpv' & Hmok).
      rewrite Hpv in Hpv'. injection Hpv' as <-.
      destruct (Hchoice lv pv p pw Hmok Hfilter) as (v & Hpost & Hvok & Hvphys).
      exists p, g, b, e, a, ea, v, pw. split_and!; [done..|].
      left. eauto.
    - destruct (mem_access_authorised_reg_allows MemAccessRead Hphys Hr Hauth)
        as (g & b & e & a & Hacc).
      pose proof (mmio_load_untagged _ _ _ Hload) as Ht.
      destruct (Hok _ _ _ _ _ _ Hacc) as [ [Hexp Hnone] | ([lv Hlv] & _) ].
      2: { (* A cell is not a device. *)
           destruct (erasure_lookup_mem Her (lookup_weaken _ _ _ _ Hlv Hmem)) as (pv & Hpv & _).
           pose proof (mem_avoids_mmio_lookup _ _ _ (er_mmio Her) Hpv) as Hmmio'.
           congruence. }
      exists p, g, b, e, a, ea, (MkLWord pw None), pw. split_and!; [done| | | done |].
      + by apply reg_word_ok_untagged.
      + by apply reg_phys_untagged.
      + right. by split_and!.
  Qed.

  (** A store step writes the logical word of [store_lift] to a wholly
      owned cell, or writes a time device. *)
  Lemma store_step_inv stored_word_ok Q R C φ lpc lreg lsreg lmem regs r imm (mem : LMem) dfracs c :
    erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg → r ∈ dom regs → mem ⊆ lmem →
    store_lift stored_word_ok Q regs → mem_access_footprint MemAccessWrite regs r imm mem dfracs →
    store_step stored_word_ok r imm φ c →
    ∃ p g b e a ea, reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea ∧
      ((∃ v pw, Q v ∧ is_Some (mem !! ea) ∧ dfracs !! ea = Some (DfracOwn 1) ∧
          mem_word_ok R C (lstore_word p v) pw ∧
          nextPC ((store_effect ea φ) .[ea :=ₐ pw]) = Some c) ∨
       (is_exposed_mmio_address ea = true ∧ mem !! ea = None ∧
        ∃ td, nextPC (φ .[TD := td]) = Some c)).
  Proof.
    intros Her Hincl Hr Hmem Hlift Hok Hstep.
    pose proof (erasure_regs_incl Her Hincl) as Hphys.
    destruct Hstep as [p ea w Hauth Hmmio Hin Hwok Hnext
                      |p ea w φ' Hauth Hmmio Hstore Hnext Hwok].
    - destruct (mem_access_authorised_reg_allows MemAccessWrite Hphys Hr Hauth)
        as (g & b & e & a & Hacc).
      destruct (Hok _ _ _ _ _ _ Hacc) as [ [Hexp _] | (Hlv & Hdq) ].
      { by rewrite not_mmio_not_exposed_mmio in Hexp. }
      destruct (Hlift _ _ _ _ _ _ _ _ Her Hincl Hwok) as (v & HQ & Hvok & Hvphys).
      exists p, g, b, e, a, ea. split; first done. left.
      exists v, (store_word p w). split_and!; [done | done | by apply Hdq | | done].
      apply reg_phys_mem_word_ok; first by apply reg_word_ok_lstore_word.
      by apply reg_phys_lstore_word.
    - destruct (mem_access_authorised_reg_allows MemAccessWrite Hphys Hr Hauth)
        as (g & b & e & a & Hacc).
      destruct (Hok _ _ _ _ _ _ Hacc) as [ [Hexp Hnone] | ([lv Hlv] & _) ].
      2: { (* A cell is not a device. *)
           destruct (erasure_lookup_mem Her (lookup_weaken _ _ _ _ Hlv Hmem)) as (pv & Hpv & _).
           pose proof (mem_avoids_mmio_lookup _ _ _ (er_mmio Her) Hpv) as Hmmio'.
           congruence. }
      exists p, g, b, e, a, ea. split; first done. right. split_and!; [done | done |].
      rewrite /mmio_store (exposed_mmio_not_shadow _ Hexp) (exposed_mmio_not_revoker _ Hexp) in Hstore.
      rewrite /is_exposed_mmio_address in Hexp. rewrite Hexp in Hstore.
      destruct (time_dev_store (timedevs φ) ea w) as [td|]; simplify_eq/=. by exists td.
  Qed.

  (** A load by a live authority from a cell: the step is the access. *)
  Lemma load_step_live_inv step flt post i R C φ lpc lreg lsreg lmem regs dst r imm (mem : LMem)
      pl p g b e a ea lv :
    erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg → mem ⊆ lmem →
    load_agree step flt i dst r imm → load_choice_ok flt post R C →
    (∀ v, regs !! r = Some v → ¬ stale_id R v) →
    reg_allows_mem_access MemAccessRead regs r imm p g b e a ea → mem !! ea = Some lv →
    ∃ pw, step i pl φ = nextPC (φ .[dst :=ᵣ pw]).
  Proof.
    intros Her Hincl Hmem Hagree Hchoice Hlive Hacc Hlv.
    pose proof (mem_access_authorised_live MemAccessRead Her Hincl Hlive Hacc) as Hauth.
    destruct (erasure_lookup_mem Her (lookup_weaken _ _ _ _ Hlv Hmem)) as (pv & Hpv & Hmok).
    pose proof (mem_avoids_mmio_lookup _ _ _ (er_mmio Her) Hpv) as Hmmio.
    destruct (Hchoice φ lpc lreg lsreg lmem lv pv p Her Hmok) as (pw & v' & Hflt & _).
    exists pw. exact (Hagree pl φ p ea pv pw Hauth Hmmio Hpv Hflt).
  Qed.

  (** A store by a live authority to a cell: the step is the access, of a
      word that [stored_word_ok] allows. *)
  Lemma store_step_live_inv step stored_word_ok i R C φ lpc lreg lsreg lmem regs r imm (mem : LMem)
      pl p g b e a ea :
    erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg → mem ⊆ lmem →
    store_agree step stored_word_ok i r imm → store_lift_some stored_word_ok regs →
    (∀ v, regs !! r = Some v → ¬ stale_id R v) →
    reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea → is_Some (mem !! ea) →
    ∃ w, stored_word_ok φ w ∧ step i pl φ = nextPC ((store_effect ea φ) .[ea :=ₐ store_word p w]).
  Proof.
    intros Her Hincl Hmem Hagree Hsome Hlive Hacc [lv Hlv].
    pose proof (mem_access_authorised_live MemAccessWrite Her Hincl Hlive Hacc) as Hauth.
    destruct (erasure_lookup_mem Her (lookup_weaken _ _ _ _ Hlv Hmem)) as (pv & Hpv & _).
    pose proof (mem_avoids_mmio_lookup _ _ _ (er_mmio Her) Hpv) as Hmmio.
    destruct (Hsome R C φ lpc lreg lsreg lmem Her Hincl) as [w Hw].
    exists w. split; first done.
    apply (Hagree pl φ p ea w Hauth Hmmio); [by eexists | done].
  Qed.

  (** The device branch of a store by a live authority. *)
  Lemma store_step_device_inv stored_word_ok R C φ lpc lreg lsreg lmem regs r imm c p g b e a ea :
    erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg →
    reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea →
    (∀ v, regs !! r = Some v → ¬ stale_id R v) →
    is_mmio_address ea = true → store_step stored_word_ok r imm φ c →
    ∃ w φ', stored_word_ok φ w ∧ mmio_store φ ea w = Some φ' ∧ nextPC φ' = Some c.
  Proof.
    intros Her Hincl Hacc Hlive Hmmio Hstep.
    pose proof (mem_access_authorised_live MemAccessWrite Her Hincl Hlive Hacc) as Hauth.
    destruct Hstep as [p0 ea0 w Hauth0 Hmmio0 Hin Hwok Hnext
                      |p0 ea0 w φ' Hauth0 Hmmio0 Hstore Hnext Hwok].
    - destruct (mem_access_authorised_det Hauth Hauth0) as [_ <-]. congruence.
    - destruct (mem_access_authorised_det Hauth Hauth0) as [_ <-]. by exists w, φ'.
  Qed.

End mem_access_pure.

#[local] Arguments load_step_inv {MP flt post R C φ lpc lreg lsreg lmem regs dst r imm mem dfracs c}.
#[local] Arguments store_step_inv
  {MP stored_word_ok Q R C φ lpc lreg lsreg lmem regs r imm mem dfracs c}.
#[local] Arguments load_step_live_inv {MP step flt post i R C φ lpc lreg lsreg lmem regs dst r imm mem}
  pl {p g b e a ea lv}.
#[local] Arguments store_step_live_inv
  {MP step stored_word_ok i R C φ lpc lreg lsreg lmem regs r imm mem}
  pl {p g b e a ea}.

(** Closes [mem_access_authorised perm_ok φ r imm p ea] from the lookup of [r] and the
    checks of the step, split at their conjunctions. *)
Ltac solve_mem_access_authorised :=
  repeat match goal with
    | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
    end;
  eexists _, _, _, _; split_and!; eassumption.

(** Closes [load_member] and [store_member] of a concrete step function:
    one constructor per branch of the unfolded step. The stored word's
    condition is left to [solve_wok], after the word is fixed by the
    branch. *)
Ltac solve_mem_access_member_with solve_wok :=
  let Hex := fresh "Hex" in
  intros ? ? ? Hex; cbn in Hex;
  repeat (simplify_option_eq; try case_match);
  first
    [ eapply ls_device; [solve_mem_access_authorised | eassumption | eassumption | eassumption]
    | eapply ls_cell; [solve_mem_access_authorised | eassumption | eassumption
                      | rewrite /griotte_load_filter /load_filter; by simplify_option_eq
                      | eassumption]
    | eapply ss_device; [solve_mem_access_authorised | eassumption | eassumption | eassumption
                        | solve_wok]
    | eapply ss_cell; [solve_mem_access_authorised | eassumption | by eexists | solve_wok
                      | rewrite /store_effect; eassumption] ].

Ltac solve_mem_access_member := solve_mem_access_member_with idtac.

(** [CLoad dst src imm] loads at the address that [src] authorises at
    offset [imm], into [dst], through the shadow table. *)
Lemma CLoad_member `{MachineParameters} dst src imm :
  load_member exec_opt griotte_load_filter (CLoad dst src imm) dst src imm.
Proof. solve_mem_access_member. Qed.

(** [Store dst ρ imm] writes the word of its argument [ρ] at the address
    that [dst] authorises at offset [imm]; that word has [stored_word_ok]. *)
Lemma Store_member `{MachineParameters} (stored_word_ok : ExecConf → Word → Prop) dst ρ imm :
  (∀ φ w, word_of_argument (reg φ) ρ = Some w → stored_word_ok φ w) →
  store_member exec_opt stored_word_ok (Store dst ρ imm) dst imm.
Proof.
  intros Hwok. solve_mem_access_member_with ltac:(by eapply Hwok).
Qed.

(** The same, with the word of the argument itself. *)
Lemma Store_member_argument `{MachineParameters} dst ρ imm :
  store_member exec_opt (λ φ w, word_of_argument (reg φ) ρ = Some w) (Store dst ρ imm) dst imm.
Proof. apply Store_member. intros φ w Hw. exact Hw. Qed.

(** On the checked path to a cell, [CLoad dst src imm] is the access. *)
Lemma CLoad_agree `{MachineParameters} dst src imm :
  load_agree exec_opt griotte_load_filter (CLoad dst src imm) dst src imm.
Proof.
  intros pl φ p ea pv w (g & b & e & a & Hsrc & Hperm & Hadd & Hwb) Hmmio Hpv Hflt.
  rewrite /griotte_load_filter /load_filter in Hflt.
  cbn [exec_opt]. rewrite Hsrc /=. rewrite Hadd /=. rewrite Hperm Hwb /=.
  rewrite Hmmio Hpv /=. revert Hflt.
  destruct (heap_cap_base pv) as [base|];
    [destruct (shadowtbl φ !! base) as [ [] |]|]; intros Hflt; simplify_eq/=; done.
Qed.

(** On the checked path to a cell, [Store dst ρ imm] is the access, of the
    word of [ρ]. *)
Lemma Store_agree `{MachineParameters} dst ρ imm :
  store_agree exec_opt (λ φ w, word_of_argument (reg φ) ρ = Some w) (Store dst ρ imm) dst imm.
Proof.
  intros pl φ p ea w (g & b & e & a & Hdst & Hperm & Hadd & Hwb) Hmmio [v Hv] Hw.
  cbv beta in Hw.
  cbn [exec_opt]. rewrite Hw /=. rewrite Hdst /=. rewrite Hadd /=. rewrite Hperm Hwb /=.
  rewrite Hmmio Hv /=. by rewrite /store_effect.
Qed.

(** On the checked path to a device, [CLoad dst src imm] reads the
    device. *)
Lemma CLoad_device_agree `{MachineParameters} dst src imm pl φ p ea :
  mem_access_authorised readAllowed φ src imm p ea → is_mmio_address ea = true →
  exec_opt (CLoad dst src imm) pl φ = (w ← mmio_load φ ea; nextPC (φ .[dst :=ᵣ w])).
Proof.
  intros (g & b & e & a & Hsrc & Hperm & Hadd & Hwb) Hmmio.
  cbn [exec_opt]. rewrite Hsrc /=. rewrite Hadd /=. rewrite Hperm Hwb /=. by rewrite Hmmio.
Qed.

(** On the checked path to a device, [Store dst ρ imm] writes the device. *)
Lemma Store_device_agree `{MachineParameters} dst ρ imm pl φ p ea w :
  mem_access_authorised writeAllowed φ dst imm p ea → is_mmio_address ea = true →
  word_of_argument (reg φ) ρ = Some w →
  exec_opt (Store dst ρ imm) pl φ = (φ' ← mmio_store φ ea w; nextPC φ').
Proof.
  intros (g & b & e & a & Hdst & Hperm & Hadd & Hwb) Hmmio Hw.
  cbn [exec_opt]. rewrite Hw /=. rewrite Hdst /=. rewrite Hadd /=. rewrite Hperm Hwb /=.
  by rewrite Hmmio.
Qed.

(** ** The memory steps in closed form

    The memberships and agreements of the memory instructions are lemmas.
    The fallback of [iInstr] finds them in the hint database [mem_agree_db],
    indexed by the instruction; each lemma is registered on the line after
    it, or here for those above. The settings are global: the database is
    searched in client proofs, which do not import this file. *)
Create HintDb mem_agree_db discriminated.
#[global] Hint Constants Opaque : mem_agree_db.
#[global] Hint Opaque load_member load_agree store_member store_agree : mem_agree_db.
#[global] Hint Mode load_member - - - ! - - - : mem_agree_db.
#[global] Hint Mode load_agree - - - ! - - - : mem_agree_db.
#[global] Hint Mode store_member - - - ! - - : mem_agree_db.
#[global] Hint Mode store_agree - - - ! - - : mem_agree_db.
#[global] Hint Resolve CLoad_member CLoad_agree Store_member_argument Store_agree : mem_agree_db.

(** ** The closer of a memory write *)

Section mem_access_close.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ} {kd : kind}.

  (** Closes an instruction that writes the physical word [pw] to a wholly
      owned cell [ea] then increments the PC, as the physical
      [nextPC (update_mem φ ea pw)]; the logical cell gets [v]. The spec
      [P] holds of the new PC and memory on success, and of the old ones on
      failure. *)
  Lemma instr_close_mem_update pc (rf : Reg) sr m st td lpc (lreg : LReg) lsreg lmem R C
      (regs : LReg) (mem : LMem) (dfracs : gmap Addr dfrac) ea (v : LWord) (pw : Word) c σ'
      (Φ : tval kd → iProp Σ) (P : LWord → LMem → tval kd → Prop) :
    erasure R C (MkExecConf pc rf sr m st td) lpc lreg (ls_join lsreg) lmem →
    is_Some (mem !! ea) → dfracs !! ea = Some (DfracOwn 1) →
    mem_word_ok R C v pw →
    (match nextPC (update_mem (MkExecConf pc rf sr m st td) ea pw) with
     | Some conf => conf | None => (Faulted, (MkExecConf pc rf sr m st td)) end) = (c, σ') →
    (∀ lpc', incrementPC lpc = Some lpc' → P lpc' (<[ea := v]> mem) NextIV) →
    (incrementPC lpc = None → P lpc mem FaultedV) →
    PC_auth lpc -∗
    gen_heap_interp lreg -∗
    sys_interp lsreg -∗
    gen_heap_interp lmem -∗
    gen_heap_interp st -∗
    reg_auth R -∗
    addr_alloc_auth C -∗
    PC ↦ₚ lpc -∗
    ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) -∗
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    (∀ lpc' mem' retv,
       ⌜P lpc' mem' retv⌝ -∗
       PC ↦ₚ lpc' -∗
       ([∗ map] a↦dv ∈ prod_merge dfracs mem', a ↦ₐ{dv.1} dv.2) -∗
       ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
       Φ retv)
    ==∗
    ⌜sys_kept (MkExecConf pc rf sr m st td) σ'⌝ ∗
    cerise_state_interp σ' ∗
    from_option Φ False (flag_val c).
  Proof.
    iIntros (Her [v0 Hv0] Hdq Hok Hstep HPs HPf)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hmem Hmap Hφ".
    assert (prod_merge dfracs mem !! ea = Some (DfracOwn 1, v0)) as Hmerge.
    { by rewrite lookup_merge Hv0 Hdq. }
    iDestruct (gen_mem_valid_inSepM_general with "Hm Hmem") as %Hlv0; first exact Hmerge.
    pose proof (erasure_store Her Hlv0 Hok) as Her1.
    rewrite /update_mem /= in Hstep.
    destruct (incrementPC lpc) as [lpc'|] eqn:Hi.
    - destruct (erasure_incrementPC Her1 Hi) as (pc' & Hu & Her2).
      rewrite Hu in Hstep. simplify_eq.
      iDestruct (big_sepM_delete _ _ ea with "Hmem") as "[Hea Hmem]"; first exact Hmerge.
      iMod (gen_heap_update with "Hm Hea") as "[Hm Hea]".
      iMod (PC_update _ _ lpc' with "HPCa HPC") as "[HPCa HPC]".
      iModIntro. iSplit; first (iPureIntro; by apply sys_kept_same_sreg).
      iSplitR "Hφ HPC Hmem Hea Hmap".
      + iApply (SI_close Her2 with "HPCa Hr Hsr Hm Hst HR HC").
      + iApply ("Hφ" with "[%] HPC [Hmem Hea] Hmap"); first by apply HPs.
        rewrite -(insert_id dfracs ea (DfracOwn 1)) // /prod_merge
          -(insert_merge _ _ _ _ (DfracOwn 1, v)) // big_sepM_insert_delete.
        iFrame. by rewrite insert_id.
    - pose proof (erasure_incrementPC_fail Her1 Hi) as Hfail.
      rewrite /nextPC Hfail in Hstep.
      simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply ("Hφ" with "[%] HPC Hmem Hmap"). by apply HPf.
  Qed.

End mem_access_close.

#[local] Arguments instr_close_mem_update {MP Σ ceriseg kd pc rf sr m st td lpc lreg lsreg lmem R C
  regs mem dfracs ea v pw c σ' Φ} P.

(** ** Witnesses *)

Section mem_access_witness.
  Context `{MP : MachineParameters} `{ceriseg : ceriseG Σ}.

  (** The witness [W] keeps the authorising word [v] live: its identifier
      is not stale, so its physical copy is exact. *)
  Definition live_witness (W : iProp Σ) (v : LWord) : Prop :=
    ∀ R, reg_auth R -∗ W -∗ ⌜¬ stale_id R v⌝.

  (** The liveness of the authority of [r], when [L] holds. *)
    Lemma live_witness_cond (L : Prop) (W : iProp Σ) (regs : LReg) r R :
    (L → ∀ v, regs !! r = Some v → live_witness W v) →
    reg_auth R -∗ W -∗ ⌜L → ∀ v, regs !! r = Some v → ¬ stale_id R v⌝.
  Proof.
    rewrite /live_witness. iIntros (Hlive) "HR HW". iIntros (HL v Hv).
    iApply (Hlive HL v Hv R with "HR HW").
  Qed.

  (** A dereference witness keeps the words of its identifier live. *)
  Lemma deref_witness_live dw v : v.(lprov) = deref_id dw → live_witness (deref_witness_res dw) v.
  Proof.
    intros Hπ R. iIntros "HR Hw".
    iDestruct (deref_witness_lookup with "HR Hw") as %Hok.
    iPureIntro. exact (deref_witness_not_stale R dw v Hok Hπ).
  Qed.

  Lemma deref_res_live π q v : v.(lprov) = π → live_witness (deref_res π q) v.
  Proof.
    intros Hπ. rewrite deref_res_witness. apply deref_witness_live.
    by rewrite deref_id_witness_of.
  Qed.

  (** A word without identifier is live with any witness. *)
  Lemma live_witness_no_id W v : v.(lprov) = None → live_witness W v.
  Proof. intros Hπ R. iIntros "_ _ !%". intros (ι & x & Hι & _). congruence. Qed.

  (** A part of the witness is enough. *)
  Lemma live_witness_sep_r W W' v : live_witness W' v → live_witness (W ∗ W') v.
  Proof. intros Hlive R. iIntros "HR [_ HW']". iApply (Hlive R with "HR HW'"). Qed.

  (** The witness [W] lets a load through the filter [flt] return a word
      with [post]. *)
  Definition load_choice (flt : ExecConf → Perm → Word → option Word) (W : iProp Σ)
      (post : Perm → LWord → LWord → Prop) : Prop :=
    ∀ R, reg_auth R -∗ W -∗ ⌜∀ C, load_choice_ok flt post R C⌝.

  (** A part of the witness is enough. *)
  Lemma load_choice_sep_l flt W W' post : load_choice flt W post → load_choice flt (W ∗ W') post.
  Proof. intros Hchoice R. iIntros "HR [HW _]". iApply (Hchoice R with "HR HW"). Qed.

  (** Griotte's filter, with any witness: the exact word. *)
  Lemma load_choice_exact W : load_choice griotte_load_filter W load_exact.
  Proof.
    intros R. iIntros "_ _ !%". intros C φ lpc lreg lsreg lmem lv pv p Her Hok.
    destruct (load_filter_is_Some R C (shadowtbl φ) p pv (er_registry Her)) as [pl Hpl].
    exists pl, (lload_word p lv). split_and!; [done | by rewrite /load_exact | |].
    - by apply reg_word_ok_lload_word, (mem_word_ok_reg_word_ok _ _ _ pv).
    - by eapply load_filter_reg_phys; first apply (er_registry Her).
  Qed.

  (** ** Status witnesses

      [load_witness], [load_witness_res] and [load_post] are in
      [instr_operands.v]. Witnesses are preconditions, returned unchanged. *)

  Definition load_witness_ok (R : RegState) (wit : load_witness) : Prop :=
    match wit with
    | LoadPlain => True
    | LoadQuar ι => ∃ x, R !! ι = Some x ∧ lifecycle_enc AQuar ≤ lifecycle_enc (re_status x)
    | LoadLive ι q => ∃ x, R !! ι = Some x ∧ re_status x = ALive
    end.

  Lemma load_witness_lookup R wit :
    reg_auth R -∗ load_witness_res wit -∗ ⌜load_witness_ok R wit⌝.
  Proof.
    iIntros "HR Hw". destruct wit as [|ι|ι q]; cbn; first done.
    - iDestruct (reg_lookup_lb with "HR Hw") as %(b & e & γ & s & HRι & Hle).
      iPureIntro. eexists. split; first done. done.
    - iDestruct (reg_lookup_own with "HR Hw") as %(b & e & γ & HRι).
      iPureIntro. eexists. split; first done. done.
  Qed.

  (** The logical loaded word: a copy of the physical CLoad result by the
      register clause, which satisfies the post. *)
  Lemma load_post_choose R C st wit (v : LWord) pw p pl :
    registry_ok R C st →
    load_witness_ok R wit →
    mem_word_ok R C v pw →
    load_filter st p pw = Some pl →
    ∃ v' : LWord, load_post wit p v v' ∧ reg_word_ok R C v' ∧ reg_phys R v' pl.
  Proof.
    intros Hreg Hwit Hok Hpl.
    pose proof (mem_word_ok_reg_word_ok _ _ _ _ Hok) as Hokv.
    (* The exact loaded word. *)
    assert (load_post LoadPlain p v (lload_word p v) ∧ reg_word_ok R C (lload_word p v) ∧
            reg_phys R (lload_word p v) pl) as (Hpost & Hok' & Hphys).
    { split_and!; [|by apply reg_word_ok_lload_word|by eapply load_filter_reg_phys].
      split_and!; [by left|done|done|done]. }
    destruct wit as [|ι|ι q].
    - by exists (lload_word p v).
    - destruct (decide (v.(lprov) = Some ι ∧ (get_tag v.(lw) = true → has_authority v.(lw))))
        as [ [Hι Hside] | Hn].
      + destruct Hwit as (x & Hx & Hle).
        pose proof (load_filter_quarantined _ _ _ _ _ _ _ _ _ Hreg Hok Hpl Hι Hx Hle Hside) as Hpl'.
        exists (lclear_tag (lload_word p v)). split_and!.
        * destruct (get_tag v.(lw)) eqn:Ht.
          -- destruct (Hside eq_refl) as [_ [b Hab] ].
             split_and!; [right; split; last done | | |].
             ++ rewrite /= is_heap_cap_load_word /is_heap_cap.
                by rewrite (heap_authority_base_heap_cap_base _ _ Hab).
             ++ intros Hn. apply heap_authority_base_heap_cap_base in Hab. congruence.
             ++ intros Hn. congruence.
             ++ done.
          -- rewrite lclear_tag_untagged; last by rewrite /= get_tag_load_word.
             split_and!; [by left|done|done|].
             intros _ _. by rewrite lclear_tag_untagged // /= get_tag_load_word.
        * by apply reg_word_ok_lclear_tag.
        * rewrite Hpl'. apply reg_phys_untagged. by rewrite /= get_tag_clear_tag.
      + exists (lload_word p v). split_and!; try done.
        destruct Hpost as (? & ? & ? & _). split_and!; try done.
        intros Hι Hside. by exfalso; apply Hn.
    - exists (lload_word p v). split_and!; try done.
      destruct Hpost as (? & ? & ? & _). by split_and!.
  Qed.

  (** Griotte's filter, with a status witness: a word with [load_post]. *)
  Lemma load_choice_witness wit :
    load_choice griotte_load_filter (load_witness_res wit) (load_post wit).
  Proof.
    intros R. iIntros "HR Hwit".
    iDestruct (load_witness_lookup with "HR Hwit") as %Hwit_ok.
    iPureIntro. intros C φ lpc lreg lsreg lmem lv pv p Her Hok.
    destruct (load_filter_is_Some R C (shadowtbl φ) p pv (er_registry Her)) as [pl Hpl].
    destruct (load_post_choose R C (shadowtbl φ) wit lv pv p pl (er_registry Her) Hwit_ok Hok Hpl)
      as (v' & Hpost & Hvok & Hphys).
    by exists pl, v'.
  Qed.

End mem_access_witness.

#[global] Hint Resolve load_choice_exact : mem_agree_db.

(** ** The rules *)

Section mem_access_rules.
  Context `{MP : MachineParameters}.
  Context `{ceriseg : ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.

  (** A cell of [mem], at its fraction in [dfracs] of the same domain. *)
  Lemma prod_merge_lookup_dom (mem : LMem) (dfracs : gmap Addr dfrac) x w :
    mem !! x = Some w → dom dfracs = dom mem →
    ∃ dq, prod_merge dfracs mem !! x = Some (dq, w).
  Proof.
    intros Hw Hdom. destruct (proj1 (elem_of_dom dfracs x)) as [dq Hdq].
    { rewrite Hdom. by eapply elem_of_dom_2. }
    exists dq. by rewrite lookup_merge Hw Hdq.
  Qed.
  #[local] Arguments prod_merge_lookup_dom {mem dfracs x w}.

  (** One cell, as a map of fractional points-to. *)
  Lemma prod_merge_pointsto_1 a dq v :
    a ↦ₐ{dq} v ⊣⊢
    [∗ map] a'↦dv ∈ prod_merge (<[a := dq]> ∅) (<[a := v]> ∅), a' ↦ₐ{dv.1} dv.2.
  Proof.
    rewrite /prod_merge -(insert_merge _ _ _ _ (dq, v)) // merge_empty.
    by rewrite big_sepM_insert // big_sepM_empty right_id.
  Qed.

  (** *** The master rules *)

  (** A load of a membership [load_member exec_opt flt i dst r imm], with
      the cells [mem] that [r] may read (the PC's cell included) at
      fractions [dfracs], and a witness [W] that lets the load return a
      word with [post] ([load_choice]): a fault, or the PC incremented and
      [dst] holding a word with [post] of a cell of [mem], or an untagged
      word of a device ([load_result]). When [L] holds, the step agrees
      with the access ([load_agree]) and [W] keeps the authority live: an
      access to a cell does not fault ([mem_access_progress]). *)
  Lemma wp_load_step_gen Ep pc_p pc_g pc_b pc_e pc_a pc_π w i dst r imm flt post
      (L : Prop) (W : iProp Σ) (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) :
    decodeInstrW w.(lw) = i → load_member exec_opt flt i dst r imm → load_choice flt W post →
    mem_instr_ok th i →
    (L → load_agree exec_opt flt i dst r imm) →
    (L → ∀ v, regs !! r = Some v → live_witness W v) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → (dst = cnull ∨ dst ∈ dom regs) →
    mem !! pc_a = Some w → dom dfracs = dom mem → mem_access_footprint MemAccessRead regs r imm mem dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜load_result post (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst r imm mem lpc' regs' retv⌝ ∗
        ⌜L → mem_access_progress MemAccessRead regs r imm mem
               (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hi Hmember Hchoice Hsw Hagree Hlive Hvpc Hr Hdst Hmem_pc Hdom Hok Φ).
    iIntros "(>HPC & >Hmem & >Hmap & Hwit) Hφ".
    rewrite /load_choice in Hchoice.
    destruct (prod_merge_lookup_dom Hmem_pc Hdom) as [dq_pc Hmerge_pc].
    iDestruct (big_sepM_delete _ _ pc_a with "Hmem") as "[Hpc_a Hmem]"; first exact Hmerge_pc.
    iSimpl in "Hpc_a".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hi; exact Hsw | done |].
    iNext. iIntros (rf sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (big_sepM_delete _ _ pc_a (dq_pc, w) with "[Hpc_a $Hmem]") as "Hmem";
      [exact Hmerge_pc | iExact "Hpc_a" |].
    iAssert (⌜mem ⊆ lmem⌝)%I as %Hmem_incl.
    { rewrite map_subseteq_spec. iIntros (a v Hv).
      destruct (prod_merge_lookup_dom Hv Hdom) as [dq Hmerge].
      by iApply (gen_mem_valid_inSepM_general with "Hm Hmem"). }
    (* The facts of the witness. *)
    iDestruct (Hchoice R with "HR Hwit") as %Hchoice_ok.
    iDestruct (live_witness_cond L W regs r R Hlive with "HR Hwit") as %Hlive_ok.
    rewrite Hi /exec in Hstep.
    destruct (exec_opt i pc_p _) as [conf|] eqn:Hexec; cycle 1.
    { (* A fault: with the liveness, not on a cell. *)
      simplify_eq.
      assert (L → mem_access_progress MemAccessRead regs r imm mem
                    (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
                    (FaultedV : tval (kind_of th))) as Hprog.
      { intros HL (p & g & b & e & a & ea & Hacc & [lv Hlv]) [lpc' Hinc].
        destruct (load_step_live_inv pc_p Her Hlregs Hmem_incl (Hagree HL) (Hchoice_ok C)
                    (Hlive_ok HL) Hacc Hlv) as [pw Hnext].
        rewrite Hexec in Hnext.
        destruct (nextPC_is_Some_erasure _ _ _ (_ .[dst :=ᵣ pw]) _ _ _ _ _ Her ltac:(done) Hinc)
          as [conf Hconf].
        congruence. }
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply "Hφ". iFrame "HPC Hmem Hmap Hwit". iPureIntro.
      split; [left; apply faulted_outcome_refl | exact Hprog]. }
    subst conf.
    destruct (load_step_inv Her Hlregs Hr Hmem_incl (load_choice_ok_inv (Hchoice_ok C) Her) Hok
                (Hmember _ _ _ Hexec))
      as (p & g & b & e & a & ea & v & pw & Hacc & Hvok & Hpw & Hnext & Hcases).
    iApply (instr_close_reg_update (dst := dst) (v := v) (w := pw)
      (λ lpc' regs' retv,
         load_result post (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst r imm mem lpc' regs' retv ∧
         (L → mem_access_progress MemAccessRead regs r imm mem
                (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) retv))
      Her Hlregs Hdst Hvok with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hmem Hwit]").
    { by rewrite Hnext. } { exact Hpw. }
    { intros lpc' Hinc. split; last (intros _ _ _; done).
      right. exists p, g, b, e, a, ea. split_and!; [done..|].
      destruct Hcases as [ (lv & Hlv & Hpost) | (Hexp & Hnone & Ht & ->) ]; [left | right]; eauto 10. }
    { intros Hinc. split; first (left; apply faulted_outcome_refl).
      intros _ _ [lpc' Hinc']. congruence. }
    iIntros (lpc' regs' retv [Hres Hprog]) "HPC Hmap". iApply "Hφ".
    iFrame "HPC Hmem Hmap Hwit". iPureIntro. by split.
  Qed.

  (** A store of a membership [store_member exec_opt stored_word_ok i r imm], whose
      stored word lifts to a logical word with [Q] ([store_lift]), with the
      cells [mem] that [r] may write (wholly owned, the PC's cell included):
      a fault, or the PC incremented and a cell of [mem] holding the stored
      word as [lstore_word] writes it, or a device written
      ([store_result]). When [L] holds, the step agrees with the access
      ([store_agree]), some word is stored ([store_lift_some]) and [W]
      keeps the authority live: an access to a cell does not fault
      ([mem_access_progress]). *)
  Lemma wp_store_step_gen Ep pc_p pc_g pc_b pc_e pc_a pc_π w i r imm stored_word_ok
      (Q : LWord → Prop) (L : Prop) (W : iProp Σ) (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) :
    decodeInstrW w.(lw) = i → store_member exec_opt stored_word_ok i r imm → mem_instr_ok th i →
    (L → store_agree exec_opt stored_word_ok i r imm) →
    (L → store_lift_some stored_word_ok regs) →
    (L → ∀ v, regs !! r = Some v → live_witness W v) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → store_lift stored_word_ok Q regs →
    mem !! pc_a = Some w → dom dfracs = dom mem → mem_access_footprint MemAccessWrite regs r imm mem dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ Ep
    {{{ lpc' mem' retv, RET retv;
        ⌜store_result Q (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r imm mem lpc' mem' retv⌝ ∗
        ⌜L → mem_access_progress MemAccessWrite regs r imm mem
               (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dv ∈ prod_merge dfracs mem', a ↦ₐ{dv.1} dv.2) ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hi Hmember Hsw Hagree Hsome Hlive Hvpc Hr Hlift Hmem_pc Hdom Hok Φ).
    iIntros "(>HPC & >Hmem & >Hmap & Hwit) Hφ".
    destruct (prod_merge_lookup_dom Hmem_pc Hdom) as [dq_pc Hmerge_pc].
    iDestruct (big_sepM_delete _ _ pc_a with "Hmem") as "[Hpc_a Hmem]"; first exact Hmerge_pc.
    iSimpl in "Hpc_a".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [rewrite Hi; exact Hsw | done |].
    iNext. iIntros (rf sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (big_sepM_delete _ _ pc_a (dq_pc, w) with "[Hpc_a $Hmem]") as "Hmem";
      [exact Hmerge_pc | iExact "Hpc_a" |].
    iAssert (⌜mem ⊆ lmem⌝)%I as %Hmem_incl.
    { rewrite map_subseteq_spec. iIntros (a v Hv).
      destruct (prod_merge_lookup_dom Hv Hdom) as [dq Hmerge].
      by iApply (gen_mem_valid_inSepM_general with "Hm Hmem"). }
    iDestruct (live_witness_cond L W regs r R Hlive with "HR Hwit") as %Hlive_ok.
    rewrite Hi /exec in Hstep.
    destruct (exec_opt i pc_p _) as [conf|] eqn:Hexec; cycle 1.
    { (* A fault: with the liveness, not on a cell. *)
      simplify_eq.
      assert (L → mem_access_progress MemAccessWrite regs r imm mem
                    (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
                    (FaultedV : tval (kind_of th))) as Hprog.
      { intros HL (p & g & b & e & a & ea & Hacc & Hin) [lpc' Hinc].
        destruct (store_step_live_inv pc_p Her Hlregs Hmem_incl (Hagree HL) (Hsome HL)
                    (Hlive_ok HL) Hacc Hin) as (w' & _ & Hnext).
        rewrite Hexec in Hnext.
        destruct (nextPC_is_Some_erasure _ _ _ ((store_effect ea _) .[ea :=ₐ store_word p w'])
                    _ _ _ _ _ Her ltac:(done) Hinc) as [conf Hconf].
        congruence. }
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply "Hφ". iFrame "HPC Hmem Hmap Hwit". iPureIntro.
      split; [left; apply faulted_outcome_refl | exact Hprog]. }
    subst conf.
    destruct (store_step_inv Her Hlregs Hr Hmem_incl Hlift Hok (Hmember _ _ _ Hexec))
      as (p & g & b & e & a & ea & Hacc &
          [ (v & pw & HQ & Hin & Hdq & Hpw & Hnext) | (Hexp & Hnone & td' & Hnext) ]).
    - (* A cell. *)
      rewrite /store_effect in Hnext.
      iApply (instr_close_mem_update
        (λ lpc' mem' retv,
           store_result Q (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
             (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r imm mem lpc' mem' retv ∧
           (L → mem_access_progress MemAccessWrite regs r imm mem
                  (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) retv))
        Her Hin Hdq Hpw with "HPCa Hr Hsr Hm Hst HR HC HPC Hmem Hmap [Hφ Hwit]").
      { by rewrite Hnext. }
      { intros lpc' Hinc. split; last (intros _ _ _; done).
        right. exists p, g, b, e, a, ea. split_and!; [done..|]. left. eauto. }
      { intros Hinc. split; first (left; apply faulted_outcome_refl).
        intros _ _ [lpc' Hinc']. congruence. }
      iIntros (lpc' mem' retv [Hres Hprog]) "HPC Hmem Hmap". iApply "Hφ".
      iFrame "HPC Hmem Hmap Hwit". iPureIntro. by split.
    - (* A time device. *)
      pose proof (erasure_set_timedevs td' Her) as Her1.
      change (nextPC (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) rf sr m st td') = Some (c, σ'))
        in Hnext.
      iApply (instr_close_kept_trans _ (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) rf sr m st td'));
        first by apply sys_kept_same_sreg.
      iApply (instr_close_pc_update (n := 1)
        (λ lpc' retv,
           store_result Q (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
             (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r imm mem lpc' mem retv ∧
           (L → mem_access_progress MemAccessWrite regs r imm mem
                  (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) retv))
        Her1 with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hmem Hwit]").
      { rewrite /nextPC in Hnext. by rewrite Hnext. }
      { intros lpc' Hinc. split; last (intros _ _ _; done).
        right. exists p, g, b, e, a, ea. split_and!; [done..|]. right. by split_and!. }
      { intros Hinc. split; first (left; apply faulted_outcome_refl).
        intros _ _ [lpc' Hinc']. rewrite /incrementPC in Hinc'. congruence. }
      iIntros (lpc' retv [Hres Hprog]) "HPC Hmap". iApply "Hφ".
      iFrame "HPC Hmem Hmap Hwit". iPureIntro. by split.
  Qed.

  (** *** Instances *)

  (** The load of the fundamental theorem: faults allowed, no witness. *)
  Lemma wp_load_step Ep pc_p pc_g pc_b pc_e pc_a pc_π w i dst r imm flt post
      (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) :
    decodeInstrW w.(lw) = i → load_member exec_opt flt i dst r imm → load_choice flt emp post →
    mem_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → (dst = cnull ∨ dst ∈ dom regs) →
    mem !! pc_a = Some w → dom dfracs = dom mem → mem_access_footprint MemAccessRead regs r imm mem dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜load_result post (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst r imm mem lpc' regs' retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hi Hmember Hchoice Hsw Hvpc Hr Hdst Hmem_pc Hdom Hok Φ) "(HPC & Hmem & Hmap) Hφ".
    iApply (wp_load_step_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ False emp%I with "[$HPC $Hmem $Hmap]");
      [exact Hi | exact Hmember | exact Hchoice | exact Hsw | intros [] | intros []
      | exact Hvpc | exact Hr | exact Hdst | exact Hmem_pc | exact Hdom | exact Hok |].
    iIntros "!>" (lpc' regs' retv) "(%Hres & _ & HPC & Hmem & Hmap & _)".
    iApply "Hφ". iFrame "HPC Hmem Hmap". by iPureIntro.
  Qed.

  (** The load whose authority [W] keeps live: an access to a cell does
      not fault. *)
  Lemma wp_load_step_live Ep pc_p pc_g pc_b pc_e pc_a pc_π w i dst r imm flt post
      (W : iProp Σ) (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) :
    decodeInstrW w.(lw) = i → load_member exec_opt flt i dst r imm → load_choice flt W post →
    mem_instr_ok th i → load_agree exec_opt flt i dst r imm →
    (∀ v, regs !! r = Some v → live_witness W v) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → (dst = cnull ∨ dst ∈ dom regs) →
    mem !! pc_a = Some w → dom dfracs = dom mem → mem_access_footprint MemAccessRead regs r imm mem dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜load_result post (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst r imm mem lpc' regs' retv⌝ ∗
        ⌜mem_access_progress MemAccessRead regs r imm mem
           (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ([∗ map] k↦y ∈ regs', k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hi Hmember Hchoice Hsw Hagree Hlive Hvpc Hr Hdst Hmem_pc Hdom Hok Φ) "Hpre Hφ".
    iApply (wp_load_step_gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ True with "Hpre");
      [exact Hi | exact Hmember | exact Hchoice | exact Hsw | intros _; exact Hagree
      | intros _; exact Hlive | exact Hvpc | exact Hr | exact Hdst | exact Hmem_pc | exact Hdom
      | exact Hok |].
    iIntros "!>" (lpc' regs' retv) "(%Hres & %Hprog & HPC & Hmem & Hmap & Hwit)".
    iApply "Hφ". iFrame "HPC Hmem Hmap Hwit". iPureIntro. split; [exact Hres | exact (Hprog I)].
  Qed.

  (** The store of the fundamental theorem: faults allowed, no witness. *)
  Lemma wp_store_step Ep pc_p pc_g pc_b pc_e pc_a pc_π w i r imm stored_word_ok
      (Q : LWord → Prop) (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) :
    decodeInstrW w.(lw) = i → store_member exec_opt stored_word_ok i r imm → mem_instr_ok th i →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → store_lift stored_word_ok Q regs →
    mem !! pc_a = Some w → dom dfracs = dom mem → mem_access_footprint MemAccessWrite regs r imm mem dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) }}}
      Instr Executable @ Ep
    {{{ lpc' mem' retv, RET retv;
        ⌜store_result Q (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r imm mem lpc' mem' retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dv ∈ prod_merge dfracs mem', a ↦ₐ{dv.1} dv.2) ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hi Hmember Hsw Hvpc Hr Hlift Hmem_pc Hdom Hok Φ) "(HPC & Hmem & Hmap) Hφ".
    iApply (wp_store_step_gen _ _ _ _ _ _ _ _ _ _ _ _ _ False emp%I with "[$HPC $Hmem $Hmap]");
      [exact Hi | exact Hmember | exact Hsw | intros [] | intros [] | intros []
      | exact Hvpc | exact Hr | exact Hlift | exact Hmem_pc | exact Hdom | exact Hok |].
    iIntros "!>" (lpc' mem' retv) "(%Hres & _ & HPC & Hmem & Hmap & _)".
    iApply "Hφ". iFrame "HPC Hmem Hmap". by iPureIntro.
  Qed.

  (** The store whose authority [W] keeps live: an access to a cell does
      not fault. *)
  Lemma wp_store_step_live Ep pc_p pc_g pc_b pc_e pc_a pc_π w i r imm stored_word_ok
      (Q : LWord → Prop) (W : iProp Σ) (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) :
    decodeInstrW w.(lw) = i → store_member exec_opt stored_word_ok i r imm → mem_instr_ok th i →
    store_agree exec_opt stored_word_ok i r imm → store_lift_some stored_word_ok regs →
    (∀ v, regs !! r = Some v → live_witness W v) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → store_lift stored_word_ok Q regs →
    mem !! pc_a = Some w → dom dfracs = dom mem → mem_access_footprint MemAccessWrite regs r imm mem dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ Ep
    {{{ lpc' mem' retv, RET retv;
        ⌜store_result Q (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π))
           (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r imm mem lpc' mem' retv⌝ ∗
        ⌜mem_access_progress MemAccessWrite regs r imm mem
           (incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π)) retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dv ∈ prod_merge dfracs mem', a ↦ₐ{dv.1} dv.2) ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hi Hmember Hsw Hagree Hsome Hlive Hvpc Hr Hlift Hmem_pc Hdom Hok Φ) "Hpre Hφ".
    iApply (wp_store_step_gen _ _ _ _ _ _ _ _ _ _ _ _ _ True with "Hpre");
      [exact Hi | exact Hmember | exact Hsw | intros _; exact Hagree | intros _; exact Hsome
      | intros _; exact Hlive | exact Hvpc | exact Hr | exact Hlift | exact Hmem_pc | exact Hdom
      | exact Hok |].
    iIntros "!>" (lpc' mem' retv) "(%Hres & %Hprog & HPC & Hmem & Hmap & Hwit)".
    iApply "Hφ". iFrame "HPC Hmem Hmap Hwit". iPureIntro. split; [exact Hres | exact (Hprog I)].
  Qed.

  (** *** Success rules, map form

      A load or a store by a live authority, of a cell other than the PC's
      ([ea ≠ pc_a]) or of the PC's cell ([_pc]): the fault is excluded by
      the progress, the device by the cell. *)

    Lemma wp_load_choice_next {E pc_p pc_g pc_b pc_e pc_a pc_π w dq i dst r imm flt post}
      {regs : LReg} {p g b e a ea v dq'} {W : iProp Σ} {lpc'} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i dst r imm → load_agree exec_opt flt i dst r imm →
    load_choice flt W post →
    (∀ v0, regs !! r = Some v0 → live_witness W v0) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    dst = cnull ∨ dst ∈ dom regs →
    reg_allows_mem_access MemAccessRead regs r imm p g b e a ea → ea ≠ pc_a →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ea ↦ₐ{dq'} v ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ E
    {{{ v', RET NextIV;
        ⌜post p v v'⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ea ↦ₐ{dq'} v ∗
        ([∗ map] k↦y ∈ <[dst := v']ₗ> regs, k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hdst Hacc Hne Hinc Φ)
      "(>HPC & >Hpc_a & >Hea & >Hmap & Hwit) HΦ".
    assert (pc_a ≠ ea) as Hne' by done.
    pose proof Hacc as (Hsrc & _). destruct (llookup_reg_cap Hsrc) as (_ & π & Hr).
    iAssert ([∗ map] a0↦dv ∈ prod_merge (<[pc_a := dq]> (<[ea := dq']> ∅))
               (<[pc_a := w]> (<[ea := v]> ∅)), a0 ↦ₐ{dv.1} dv.2)%I
      with "[Hpc_a Hea]" as "Hmem".
    { rewrite memMap_resource_2ne_dq //. iFrame. }
    iApply (wp_load_step_live _ _ _ _ _ _ _ w i dst r imm flt post W
              (<[pc_a := w]> (<[ea := v]> ∅)) (<[pc_a := dq]> (<[ea := dq']> ∅)) regs
              with "[$HPC $Hmem $Hmap $Hwit]");
      [exact Hi | exact Hmember | exact Hchoice | exact Hsw | exact Hagree | exact Hlive
      | exact Hvpc | by eapply elem_of_dom_2 | exact Hdst | by simplify_map_eq
      | by rewrite !dom_insert_L | |].
    { intros p0 g0 b0 e0 a0 ea0 Hacc0.
      destruct (reg_allows_mem_access_det Hacc Hacc0) as (_ & _ & _ & _ & _ & ->).
      right. split; [by simplify_map_eq | done]. }
    iIntros "!>" (lpc0 regs' retv) "(%Hres & %Hprog & HPC & Hmem & Hmap & Hwit)".
    destruct Hres as [ (-> & -> & ->) | (p1 & g1 & b1 & e1 & a1 & ea1 & Hacc1 & -> & Hinc1 & Hcases) ].
    - exfalso.
      assert (mem_access_cell MemAccessRead regs r imm (<[pc_a := w]> (<[ea := v]> ∅))) as Hcell.
      { exists p, g, b, e, a, ea. split; first done. by simplify_map_eq. }
      specialize (Hprog Hcell (ex_intro _ _ Hinc)). discriminate.
    - rewrite Hinc in Hinc1. injection Hinc1 as <-.
      destruct (reg_allows_mem_access_det Hacc Hacc1) as (-> & -> & -> & -> & -> & ->).
      destruct Hcases as [ (lv & v' & Hlv & Hpost & ->) | (_ & Hnone & _) ];
        last by simplify_map_eq.
      simplify_map_eq.
      rewrite memMap_resource_2ne_dq //. iDestruct "Hmem" as "[Hpc_a Hea]".
      iApply ("HΦ" $! v'). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  Lemma wp_load_choice_next_pc {E pc_p pc_g pc_b pc_e pc_a pc_π w dq i dst r imm flt post}
      {regs : LReg} {p g b e a} {W : iProp Σ} {lpc'} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i dst r imm → load_agree exec_opt flt i dst r imm →
    load_choice flt W post →
    (∀ v0, regs !! r = Some v0 → live_witness W v0) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    dst = cnull ∨ dst ∈ dom regs →
    reg_allows_mem_access MemAccessRead regs r imm p g b e a pc_a →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ E
    {{{ v', RET NextIV;
        ⌜post p w v'⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ([∗ map] k↦y ∈ <[dst := v']ₗ> regs, k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hdst Hacc Hinc Φ)
      "(>HPC & >Hpc_a & >Hmap & Hwit) HΦ".
    pose proof Hacc as (Hsrc & _). destruct (llookup_reg_cap Hsrc) as (_ & π & Hr).
    iEval (rewrite prod_merge_pointsto_1) in "Hpc_a".
    iApply (wp_load_step_live _ _ _ _ _ _ _ w i dst r imm flt post W
              (<[pc_a := w]> ∅) (<[pc_a := dq]> ∅) regs
              with "[$HPC $Hpc_a $Hmap $Hwit]");
      [exact Hi | exact Hmember | exact Hchoice | exact Hsw | exact Hagree | exact Hlive
      | exact Hvpc | by eapply elem_of_dom_2 | exact Hdst | by simplify_map_eq
      | by rewrite !dom_insert_L | |].
    { intros p0 g0 b0 e0 a0 ea0 Hacc0.
      destruct (reg_allows_mem_access_det Hacc Hacc0) as (_ & _ & _ & _ & _ & ->).
      right. split; [by simplify_map_eq | done]. }
    iIntros "!>" (lpc0 regs' retv) "(%Hres & %Hprog & HPC & Hmem & Hmap & Hwit)".
    destruct Hres as [ (-> & -> & ->) | (p1 & g1 & b1 & e1 & a1 & ea1 & Hacc1 & -> & Hinc1 & Hcases) ].
    - exfalso.
      assert (mem_access_cell MemAccessRead regs r imm (<[pc_a := w]> ∅)) as Hcell.
      { exists p, g, b, e, a, pc_a. split; first done. by simplify_map_eq. }
      specialize (Hprog Hcell (ex_intro _ _ Hinc)). discriminate.
    - rewrite Hinc in Hinc1. injection Hinc1 as <-.
      destruct (reg_allows_mem_access_det Hacc Hacc1) as (-> & -> & -> & -> & -> & ->).
      destruct Hcases as [ (lv & v' & Hlv & Hpost & ->) | (_ & Hnone & _) ];
        last by simplify_map_eq.
      simplify_map_eq.
      rewrite -prod_merge_pointsto_1.
      iApply ("HΦ" $! v'). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

    Lemma wp_store_next {E pc_p pc_g pc_b pc_e pc_a pc_π w dq i stored_word_ok r imm} {regs : LReg}
      {p g b e a ea v0 v} {W : iProp Σ} {lpc'} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    store_member exec_opt stored_word_ok i r imm → store_agree exec_opt stored_word_ok i r imm →
    store_lift_exact stored_word_ok v regs →
    (∀ v1, regs !! r = Some v1 → live_witness W v1) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea → ea ≠ pc_a →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ ea ↦ₐ v0 ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        ea ↦ₐ lstore_word p v ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hexact Hlive Hvpc Hacc Hne Hinc Φ)
      "(>HPC & >Hpc_a & >Hea & >Hmap & Hwit) HΦ".
    assert (pc_a ≠ ea) as Hne' by done.
    pose proof Hacc as (Hsrc & _). destruct (llookup_reg_cap Hsrc) as (_ & π & Hr).
    iAssert ([∗ map] a0↦dv ∈ prod_merge (<[pc_a := dq]> (<[ea := DfracOwn 1]> ∅))
               (<[pc_a := w]> (<[ea := v0]> ∅)), a0 ↦ₐ{dv.1} dv.2)%I
      with "[Hpc_a Hea]" as "Hmem".
    { rewrite memMap_resource_2ne_dq //. iFrame. }
    iApply (wp_store_step_live _ _ _ _ _ _ _ w i r imm stored_word_ok (λ v', v' = v) W
              (<[pc_a := w]> (<[ea := v0]> ∅)) (<[pc_a := dq]> (<[ea := DfracOwn 1]> ∅)) regs
              with "[$HPC $Hmem $Hmap $Hwit]");
      [exact Hi | exact Hmember | exact Hsw | exact Hagree | by eapply store_lift_exact_some
      | exact Hlive | exact Hvpc | by eapply elem_of_dom_2 | by apply store_lift_exact_lift
      | by simplify_map_eq | by rewrite !dom_insert_L | |].
    { intros p0 g0 b0 e0 a0 ea0 Hacc0.
      destruct (reg_allows_mem_access_det Hacc Hacc0) as (_ & _ & _ & _ & _ & ->).
      right. split; [by simplify_map_eq | intros _; by simplify_map_eq]. }
    iIntros "!>" (lpc0 mem' retv) "(%Hres & %Hprog & HPC & Hmem & Hmap & Hwit)".
    destruct Hres as [ (-> & -> & ->) | (p1 & g1 & b1 & e1 & a1 & ea1 & Hacc1 & -> & Hinc1 & Hcases) ].
    - exfalso.
      assert (mem_access_cell MemAccessWrite regs r imm (<[pc_a := w]> (<[ea := v0]> ∅))) as Hcell.
      { exists p, g, b, e, a, ea. split; first done. by simplify_map_eq. }
      specialize (Hprog Hcell (ex_intro _ _ Hinc)). discriminate.
    - rewrite Hinc in Hinc1. injection Hinc1 as <-.
      destruct (reg_allows_mem_access_det Hacc Hacc1) as (-> & -> & -> & -> & -> & ->).
      destruct Hcases as [ (v1 & Hv1 & _ & ->) | (_ & Hnone & _) ]; last by simplify_map_eq.
      cbv beta in Hv1. subst v1.
      rewrite (insert_insert_ne _ ea pc_a) // insert_insert_eq memMap_resource_2ne_dq //.
      iDestruct "Hmem" as "[Hpc_a Hea]". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_store_next_pc {E pc_p pc_g pc_b pc_e pc_a pc_π w i stored_word_ok r imm} {regs : LReg}
      {p g b e a v} {W : iProp Σ} {lpc'} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    store_member exec_opt stored_word_ok i r imm → store_agree exec_opt stored_word_ok i r imm →
    store_lift_exact stored_word_ok v regs →
    (∀ v1, regs !! r = Some v1 → live_witness W v1) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    reg_allows_mem_access MemAccessWrite regs r imm p g b e a pc_a →
    incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ w ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ lstore_word p v ∗
        ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hexact Hlive Hvpc Hacc Hinc Φ)
      "(>HPC & >Hpc_a & >Hmap & Hwit) HΦ".
    pose proof Hacc as (Hsrc & _). destruct (llookup_reg_cap Hsrc) as (_ & π & Hr).
    iEval (rewrite prod_merge_pointsto_1) in "Hpc_a".
    iApply (wp_store_step_live _ _ _ _ _ _ _ w i r imm stored_word_ok (λ v', v' = v) W
              (<[pc_a := w]> ∅) (<[pc_a := DfracOwn 1]> ∅) regs
              with "[$HPC $Hpc_a $Hmap $Hwit]");
      [exact Hi | exact Hmember | exact Hsw | exact Hagree | by eapply store_lift_exact_some
      | exact Hlive | exact Hvpc | by eapply elem_of_dom_2 | by apply store_lift_exact_lift
      | by simplify_map_eq | by rewrite !dom_insert_L | |].
    { intros p0 g0 b0 e0 a0 ea0 Hacc0.
      destruct (reg_allows_mem_access_det Hacc Hacc0) as (_ & _ & _ & _ & _ & ->).
      right. split; [by simplify_map_eq | intros _; by simplify_map_eq]. }
    iIntros "!>" (lpc0 mem' retv) "(%Hres & %Hprog & HPC & Hmem & Hmap & Hwit)".
    destruct Hres as [ (-> & -> & ->) | (p1 & g1 & b1 & e1 & a1 & ea1 & Hacc1 & -> & Hinc1 & Hcases) ].
    - exfalso.
      assert (mem_access_cell MemAccessWrite regs r imm (<[pc_a := w]> ∅)) as Hcell.
      { exists p, g, b, e, a, pc_a. split; first done. by simplify_map_eq. }
      specialize (Hprog Hcell (ex_intro _ _ Hinc)). discriminate.
    - rewrite Hinc in Hinc1. injection Hinc1 as <-.
      destruct (reg_allows_mem_access_det Hacc Hacc1) as (-> & -> & -> & -> & -> & ->).
      destruct Hcases as [ (v1 & Hv1 & _ & ->) | (_ & Hnone & _) ]; last by simplify_map_eq.
      cbv beta in Hv1. subst v1.
      rewrite insert_insert_eq -prod_merge_pointsto_1.
      iApply "HΦ". iFrame.
  Qed.

  (** *** k-ary client rules

      The registers by name, the PC moved by [1]; the authorising word is
      split into its capability, address, permission and bounds. A choice
      rule returns a word with [post]; an exact rule is its instance
      [load_exact]. *)

  Lemma wp_load_choice_next_1 {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i flt post}
      {r1 w1 imm p g b e a ea dq' v} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i r1 r1 imm → load_agree exec_opt flt i r1 r1 imm →
    load_choice flt W post → live_witness W w1 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    w1.(lw) = Cap p g b e a → (a + imm)%a = Some ea → readAllowed p = true →
    withinBounds b e ea = true → ea ≠ pc_a →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ ea ↦ₐ{dq'} v ∗
        W }}}
      Instr Executable @ E
    {{{ v', RET NextIV;
        ⌜post p v v'⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ v' ∗
        ea ↦ₐ{dq'} v ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hpc_a' Hr1 Hw1 Hadd Hperm Hwb Hne Φ)
      "(>HPC & >Hpc_a & >Hr1 & >Hea & Hwit) HΦ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (wp_load_choice_next with "[$HPC $Hpc_a $Hea $Hmap Hwit]");
      [exact Hi | exact Hsw | exact Hmember | exact Hagree | exact Hchoice
      | intros v0 Hv0; simplify_map_eq; exact Hlive
      | exact Hvpc | right; set_solver | | exact Hne | by apply incrementPC_add | iExact "Hwit" |].
    { split_and!; [| exact Hadd | exact Hperm | exact Hwb].
      rewrite llookup_reg_not_cnull // lookup_singleton_eq /= Hw1 //. }
    iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hea & Hmap & Hwit)".
    rewrite linsert_reg_not_cnull // insert_singleton decide_True //.
    iDestruct (regs_of_map_1 with "Hmap") as "Hr1".
    iApply ("HΦ" $! v'). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  Lemma wp_load_choice_next_1_pc {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i flt post}
      {r1 w1 imm p g b e a} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i r1 r1 imm → load_agree exec_opt flt i r1 r1 imm →
    load_choice flt W post → live_witness W w1 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    w1.(lw) = Cap p g b e a → (a + imm)%a = Some pc_a → readAllowed p = true →
    withinBounds b e pc_a = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        W }}}
      Instr Executable @ E
    {{{ v', RET NextIV;
        ⌜post p w v'⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ v' ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hpc_a' Hr1 Hw1 Hadd Hperm Hwb Φ)
      "(>HPC & >Hpc_a & >Hr1 & Hwit) HΦ".
    iDestruct (map_of_regs_1 with "Hr1") as "Hmap".
    iApply (wp_load_choice_next_pc with "[$HPC $Hpc_a $Hmap Hwit]");
      [exact Hi | exact Hsw | exact Hmember | exact Hagree | exact Hchoice
      | intros v0 Hv0; simplify_map_eq; exact Hlive
      | exact Hvpc | right; set_solver | | by apply incrementPC_add | iExact "Hwit" |].
    { split_and!; [| exact Hadd | exact Hperm | exact Hwb].
      rewrite llookup_reg_not_cnull // lookup_singleton_eq /= Hw1 //. }
    iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hmap & Hwit)".
    rewrite linsert_reg_not_cnull // insert_singleton decide_True //.
    iDestruct (regs_of_map_1 with "Hmap") as "Hr1".
    iApply ("HΦ" $! v'). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  Lemma wp_load_choice_next_2 {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i flt post}
      {dst wd src ws imm p g b e a ea dq' v} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i dst src imm → load_agree exec_opt flt i dst src imm →
    load_choice flt W post → live_witness W ws →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    ws.(lw) = Cap p g b e a → (a + imm)%a = Some ea → readAllowed p = true →
    withinBounds b e ea = true → ea ≠ pc_a →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ▷ src ↦ᵣ ws ∗
        ▷ ea ↦ₐ{dq'} v ∗
        W }}}
      Instr Executable @ E
    {{{ v', RET NextIV;
        ⌜post p v v'⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ v' ∗
        src ↦ᵣ ws ∗
        ea ↦ₐ{dq'} v ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hpc_a' Hdst Hsrc Hws Hadd Hperm Hwb Hne Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hsrc & >Hea & Hwit) HΦ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hdst_src]".
    iApply (wp_load_choice_next with "[$HPC $Hpc_a $Hea $Hmap Hwit]");
      [exact Hi | exact Hsw | exact Hmember | exact Hagree | exact Hchoice
      | intros v0 Hv0; simplify_map_eq; exact Hlive
      | exact Hvpc | right; set_solver | | exact Hne | by apply incrementPC_add | iExact "Hwit" |].
    { split_and!; [| exact Hadd | exact Hperm | exact Hwb].
      rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq /= Hws //. }
    iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hea & Hmap & Hwit)".
    rewrite linsert_reg_not_cnull // insert_insert decide_True //.
    iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
    iApply ("HΦ" $! v'). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  Lemma wp_load_choice_next_2_pc {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i flt post}
      {dst wd src ws imm p g b e a} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i dst src imm → load_agree exec_opt flt i dst src imm →
    load_choice flt W post → live_witness W ws →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    ws.(lw) = Cap p g b e a → (a + imm)%a = Some pc_a → readAllowed p = true →
    withinBounds b e pc_a = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ▷ src ↦ᵣ ws ∗
        W }}}
      Instr Executable @ E
    {{{ v', RET NextIV;
        ⌜post p w v'⌝ ∗
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ v' ∗
        src ↦ᵣ ws ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hpc_a' Hdst Hsrc Hws Hadd Hperm Hwb Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hsrc & Hwit) HΦ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hdst_src]".
    iApply (wp_load_choice_next_pc with "[$HPC $Hpc_a $Hmap Hwit]");
      [exact Hi | exact Hsw | exact Hmember | exact Hagree | exact Hchoice
      | intros v0 Hv0; simplify_map_eq; exact Hlive
      | exact Hvpc | right; set_solver | | by apply incrementPC_add | iExact "Hwit" |].
    { split_and!; [| exact Hadd | exact Hperm | exact Hwb].
      rewrite llookup_reg_not_cnull // lookup_insert_ne // lookup_insert_eq /= Hws //. }
    iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hmap & Hwit)".
    rewrite linsert_reg_not_cnull // insert_insert decide_True //.
    iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
    iApply ("HΦ" $! v'). iSplitR; first (iPureIntro; exact Hpost). iFrame.
  Qed.

  (** Exact loads. The cell [ea] may be the PC's cell: both points-to then
      agree. *)
  Lemma wp_load_next_1 {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i flt}
      {r1 w1 imm p g b e a ea dq' v} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i r1 r1 imm → load_agree exec_opt flt i r1 r1 imm →
    load_choice flt W load_exact → live_witness W w1 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    w1.(lw) = Cap p g b e a → (a + imm)%a = Some ea → readAllowed p = true →
    withinBounds b e ea = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        ▷ ea ↦ₐ{dq'} v ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ lload_word p v ∗
        ea ↦ₐ{dq'} v ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hpc_a' Hr1 Hw1 Hadd Hperm Hwb Φ)
      "(>HPC & >Hpc_a & >Hr1 & >Hea & Hwit) HΦ".
    destruct (decide (ea = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Hpc_a Hea") as %<-.
      iApply (wp_load_choice_next_1_pc (post := load_exact) with "[$HPC $Hpc_a $Hr1 Hwit]");
        try done.
      iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hr1 & Hwit)".
      rewrite /load_exact in Hpost. subst v'. iApply "HΦ". iFrame.
    - iApply (wp_load_choice_next_1 (post := load_exact) with "[$HPC $Hpc_a $Hr1 $Hea Hwit]");
        try done.
      iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hr1 & Hea & Hwit)".
      rewrite /load_exact in Hpost. subst v'. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_next_1_pc {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i flt}
      {r1 w1 imm p g b e a} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i r1 r1 imm → load_agree exec_opt flt i r1 r1 imm →
    load_choice flt W load_exact → live_witness W w1 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    w1.(lw) = Cap p g b e a → (a + imm)%a = Some pc_a → readAllowed p = true →
    withinBounds b e pc_a = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ r1 ↦ᵣ w1 ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        r1 ↦ᵣ lload_word p w ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hpc_a' Hr1 Hw1 Hadd Hperm Hwb Φ) "Hpre HΦ".
    iApply (wp_load_choice_next_1_pc (post := load_exact) with "Hpre"); [done.. |].
    iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hr1 & Hwit)".
    rewrite /load_exact in Hpost. subst v'. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_next_2 {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i flt}
      {dst wd src ws imm p g b e a ea dq' v} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i dst src imm → load_agree exec_opt flt i dst src imm →
    load_choice flt W load_exact → live_witness W ws →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    ws.(lw) = Cap p g b e a → (a + imm)%a = Some ea → readAllowed p = true →
    withinBounds b e ea = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ▷ src ↦ᵣ ws ∗
        ▷ ea ↦ₐ{dq'} v ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ lload_word p v ∗
        src ↦ᵣ ws ∗
        ea ↦ₐ{dq'} v ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hpc_a' Hdst Hsrc Hws Hadd Hperm Hwb Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hsrc & >Hea & Hwit) HΦ".
    destruct (decide (ea = pc_a)) as [-> | Hne].
    - iDestruct (pointsto_agree with "Hpc_a Hea") as %<-.
      iApply (wp_load_choice_next_2_pc (post := load_exact)
                with "[$HPC $Hpc_a $Hdst $Hsrc Hwit]"); try done.
      iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hdst & Hsrc & Hwit)".
      rewrite /load_exact in Hpost. subst v'. iApply "HΦ". iFrame.
    - iApply (wp_load_choice_next_2 (post := load_exact)
                with "[$HPC $Hpc_a $Hdst $Hsrc $Hea Hwit]"); try done.
      iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hdst & Hsrc & Hea & Hwit)".
      rewrite /load_exact in Hpost. subst v'. iApply "HΦ". iFrame.
  Qed.

  Lemma wp_load_next_2_pc {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i flt}
      {dst wd src ws imm p g b e a} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    load_member exec_opt flt i dst src imm → load_agree exec_opt flt i dst src imm →
    load_choice flt W load_exact → live_witness W ws →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    ws.(lw) = Cap p g b e a → (a + imm)%a = Some pc_a → readAllowed p = true →
    withinBounds b e pc_a = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ▷ src ↦ᵣ ws ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ lload_word p w ∗
        src ↦ᵣ ws ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hchoice Hlive Hvpc Hpc_a' Hdst Hsrc Hws Hadd Hperm Hwb Φ)
      "Hpre HΦ".
    iApply (wp_load_choice_next_2_pc (post := load_exact) with "Hpre"); [done.. |].
    iIntros "!>" (v') "(%Hpost & HPC & Hpc_a & Hdst & Hsrc & Hwit)".
    rewrite /load_exact in Hpost. subst v'. iApply "HΦ". iFrame.
  Qed.

  (** Stores. With one register, the stored word does not read another
      register (an integer, or the authority itself). The cell [ea], wholly
      owned, is not the PC's cell. *)
  Lemma wp_store_next_1 {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i stored_word_ok}
      {dst wd imm p g b e a ea v0 v} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    store_member exec_opt stored_word_ok i dst imm → store_agree exec_opt stored_word_ok i dst imm →
    store_lift_exact stored_word_ok v {[dst := wd]} → live_witness W wd →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    wd.(lw) = Cap p g b e a → (a + imm)%a = Some ea → writeAllowed p = true →
    withinBounds b e ea = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ▷ ea ↦ₐ v0 ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ wd ∗
        ea ↦ₐ lstore_word p v ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hexact Hlive Hvpc Hpc_a' Hdst Hwd Hadd Hperm Hwb Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hea & Hwit) HΦ".
    iDestruct (pointsto_ne with "Hea Hpc_a") as %Hne.
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_next with "[$HPC $Hpc_a $Hea $Hmap Hwit]");
      [exact Hi | exact Hsw | exact Hmember | exact Hagree | exact Hexact
      | intros v1 Hv1; simplify_map_eq; exact Hlive
      | exact Hvpc | | exact Hne | by apply incrementPC_add | iExact "Hwit" |].
    { split_and!; [| exact Hadd | exact Hperm | exact Hwb].
      rewrite llookup_reg_not_cnull // lookup_singleton_eq /= Hwd //. }
    iIntros "!> (HPC & Hpc_a & Hea & Hmap & Hwit)".
    iDestruct (regs_of_map_1 with "Hmap") as "Hdst".
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_store_next_1_pc {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w i stored_word_ok}
      {dst wd imm p g b e a v} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    store_member exec_opt stored_word_ok i dst imm → store_agree exec_opt stored_word_ok i dst imm →
    store_lift_exact stored_word_ok v {[dst := wd]} → live_witness W wd →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    wd.(lw) = Cap p g b e a → (a + imm)%a = Some pc_a → writeAllowed p = true →
    withinBounds b e pc_a = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ w ∗
        ▷ dst ↦ᵣ wd ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ lstore_word p v ∗
        dst ↦ᵣ wd ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hexact Hlive Hvpc Hpc_a' Hdst Hwd Hadd Hperm Hwb Φ)
      "(>HPC & >Hpc_a & >Hdst & Hwit) HΦ".
    iDestruct (map_of_regs_1 with "Hdst") as "Hmap".
    iApply (wp_store_next_pc with "[$HPC $Hpc_a $Hmap Hwit]");
      [exact Hi | exact Hsw | exact Hmember | exact Hagree | exact Hexact
      | intros v1 Hv1; simplify_map_eq; exact Hlive
      | exact Hvpc | | by apply incrementPC_add | iExact "Hwit" |].
    { split_and!; [| exact Hadd | exact Hperm | exact Hwb].
      rewrite llookup_reg_not_cnull // lookup_singleton_eq /= Hwd //. }
    iIntros "!> (HPC & Hpc_a & Hmap & Hwit)".
    iDestruct (regs_of_map_1 with "Hmap") as "Hdst".
    iApply "HΦ". iFrame.
  Qed.

  (** With two registers: the authority [dst] and the source [src]. *)
  Lemma wp_store_next_2 {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w dq i stored_word_ok}
      {dst wd src ws imm p g b e a ea v0 v} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    store_member exec_opt stored_word_ok i dst imm → store_agree exec_opt stored_word_ok i dst imm →
    (dst ≠ src → store_lift_exact stored_word_ok v (<[dst := wd]> (<[src := ws]> ∅))) →
    live_witness W wd →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    wd.(lw) = Cap p g b e a → (a + imm)%a = Some ea → writeAllowed p = true →
    withinBounds b e ea = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        ▷ dst ↦ᵣ wd ∗
        ▷ src ↦ᵣ ws ∗
        ▷ ea ↦ₐ v0 ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ{dq} w ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ ws ∗
        ea ↦ₐ lstore_word p v ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hexact Hlive Hvpc Hpc_a' Hdst Hwd Hadd Hperm Hwb Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hsrc & >Hea & Hwit) HΦ".
    iDestruct (pointsto_ne with "Hea Hpc_a") as %Hne.
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hdst_src]".
    iApply (wp_store_next with "[$HPC $Hpc_a $Hea $Hmap Hwit]");
      [exact Hi | exact Hsw | exact Hmember | exact Hagree | exact (Hexact Hdst_src)
      | intros v1 Hv1; simplify_map_eq; exact Hlive
      | exact Hvpc | | exact Hne | by apply incrementPC_add | iExact "Hwit" |].
    { split_and!; [| exact Hadd | exact Hperm | exact Hwb].
      rewrite llookup_reg_not_cnull // lookup_insert_eq /= Hwd //. }
    iIntros "!> (HPC & Hpc_a & Hea & Hmap & Hwit)".
    iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_store_next_2_pc {E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w i stored_word_ok}
      {dst wd src ws imm p g b e a v} {W : iProp Σ} :
    decodeInstrW w.(lw) = i → mem_instr_ok th i →
    store_member exec_opt stored_word_ok i dst imm → store_agree exec_opt stored_word_ok i dst imm →
    (dst ≠ src → store_lift_exact stored_word_ok v (<[dst := wd]> (<[src := ws]> ∅))) →
    live_witness W wd →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) → (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull →
    wd.(lw) = Cap p g b e a → (a + imm)%a = Some pc_a → writeAllowed p = true →
    withinBounds b e pc_a = true →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ w ∗
        ▷ dst ↦ᵣ wd ∗
        ▷ src ↦ᵣ ws ∗
        W }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
        pc_a ↦ₐ lstore_word p v ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ ws ∗
        W }}}.
  Proof.
    iIntros (Hi Hsw Hmember Hagree Hexact Hlive Hvpc Hpc_a' Hdst Hwd Hadd Hperm Hwb Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hsrc & Hwit) HΦ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %Hdst_src]".
    iApply (wp_store_next_pc with "[$HPC $Hpc_a $Hmap Hwit]");
      [exact Hi | exact Hsw | exact Hmember | exact Hagree | exact (Hexact Hdst_src)
      | intros v1 Hv1; simplify_map_eq; exact Hlive
      | exact Hvpc | | by apply incrementPC_add | iExact "Hwit" |].
    { split_and!; [| exact Hadd | exact Hperm | exact Hwb].
      rewrite llookup_reg_not_cnull // lookup_insert_eq /= Hwd //. }
    iIntros "!> (HPC & Hpc_a & Hmap & Hwit)".
    iDestruct (regs_of_map_2 with "Hmap") as "[Hdst Hsrc]"; first done.
    iApply "HΦ". iFrame.
  Qed.

End mem_access_rules.
