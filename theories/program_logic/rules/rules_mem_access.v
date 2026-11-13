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
    given by the instruction. The two WP rules of this file are proved once
    from that membership, for any instruction that has it. *)

Inductive mem_access_kind := MemAccessRead | MemAccessWrite.

Definition mem_access_perm (k : mem_access_kind) : Perm → bool :=
  match k with MemAccessRead => readAllowed | MemAccessWrite => writeAllowed end.

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
      from [mem], or a cell of [mem], wholly owned for a write. *)
  Definition mem_access_footprint k regs r imm (mem : LMem) (dfracs : gmap Addr dfrac) : Prop :=
    ∀ p g b e a ea, reg_allows_mem_access k regs r imm p g b e a ea →
      (is_exposed_mmio_address ea = true ∧ mem !! ea = None) ∨
      (is_mmio_address ea = false ∧ is_Some (mem !! ea) ∧
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

  (** What a write to memory at [ea] does to the rest of the machine:
      nothing. This is the place where such an effect (for example on a
      watermark) enters; a model with one changes this definition and the
      closers and tactics that unfold it ([wp_store_step],
      [solve_mem_access_member_with]). *)
  Definition store_effect (ea : Addr) (φ : ExecConf) : ExecConf := φ.

  (** Loads. The authorising register and offset come from the
      instruction, so that the fundamental theorem can open the region
      before the step. *)
  Inductive load_step (dst r : RegName) (imm : Z) (φ : ExecConf) (c : Conf) : Prop :=
  (* A plain load, live or quarantined shadow, or off the heap. *)
  | ls_cell p ea v w :
      mem_access_authorised readAllowed φ r imm p ea → is_mmio_address ea = false →
      mem φ !! ea = Some v → load_filter (shadowtbl φ) p v = Some w →
      nextPC (φ .[dst :=ᵣ w]) = Some c → load_step dst r imm φ c
  (* A load answered by a device. *)
  | ls_device p ea w :
      mem_access_authorised readAllowed φ r imm p ea → is_mmio_address ea = true →
      mmio_load φ ea = Some w →
      nextPC (φ .[dst :=ᵣ w]) = Some c → load_step dst r imm φ c.

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
      mmio_store φ ea w = Some φ' → nextPC φ' = Some c → store_step stored_word_ok r imm φ c.

  (** The membership, for a step function [step]: the WP rules take
      [exec_opt]; another semantics reuses the definitions and tactics with
      its own. *)
  Definition load_member (step : instr → Perm → ExecConf → option Conf)
      (i : instr) (dst r : RegName) (imm : Z) : Prop :=
    ∀ p φ c, step i p φ = Some c → load_step dst r imm φ c.
  Definition store_member (step : instr → Perm → ExecConf → option Conf)
      (stored_word_ok : ExecConf → Word → Prop) (i : instr) (r : RegName) (imm : Z) : Prop :=
    ∀ p φ c, step i p φ = Some c → store_step stored_word_ok r imm φ c.

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

  (** Every word that [stored_word_ok] allows lifts to a logical word with [Q]. *)
  Definition store_lift (stored_word_ok : ExecConf → Word → Prop) (Q : LWord → Prop) (regs : LReg) :
      Prop :=
    ∀ R C φ lpc lreg lsreg lmem w, erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg →
      stored_word_ok φ w → ∃ v, Q v ∧ reg_word_ok R C v ∧ reg_phys R v w.

  (** ** Outcomes *)

  (** A fault, or a read of a cell of [mem] or of a device. *)
  Definition load_result {kd : kind} lpc regs dst r imm (mem : LMem) lpc' regs'
      (retv : tval kd) : Prop :=
    (retv = FaultedV ∧ lpc' = lpc ∧ regs' = regs) ∨
    ∃ p g b e a ea, reg_allows_mem_access MemAccessRead regs r imm p g b e a ea ∧ retv = NextIV ∧
      incrementPC lpc = Some lpc' ∧
      ((∃ v, mem !! ea = Some v ∧ regs' = <[dst := lload_word p v]ₗ> regs) ∨
       (∃ w, get_tag w = false ∧ regs' = <[dst := MkLWord w None]ₗ> regs)).

  (** A fault, or a write of a word with [Q] to a cell of [mem], or a write
      to a device. *)
  Definition store_result {kd : kind} (Q : LWord → Prop) lpc regs r imm (mem : LMem) lpc' mem'
      (retv : tval kd) : Prop :=
    (retv = FaultedV ∧ lpc' = lpc ∧ mem' = mem) ∨
    ∃ p g b e a ea, reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea ∧ retv = NextIV ∧
      incrementPC lpc = Some lpc' ∧
      ((∃ v, Q v ∧ is_Some (mem !! ea) ∧ mem' = <[ea := lstore_word p v]> mem) ∨ mem' = mem).

  (** ** Inversions *)

  (** A load step gives the loaded logical word and its physical copy. *)
  Lemma load_step_inv R C φ lpc lreg lsreg lmem regs dst r imm (mem : LMem) dfracs c :
    erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg → r ∈ dom regs → mem ⊆ lmem →
    mem_access_footprint MemAccessRead regs r imm mem dfracs → load_step dst r imm φ c →
    ∃ p g b e a ea v pw, reg_allows_mem_access MemAccessRead regs r imm p g b e a ea ∧
      reg_word_ok R C v ∧ reg_phys R v pw ∧ nextPC (φ .[dst :=ᵣ pw]) = Some c ∧
      ((∃ lv, mem !! ea = Some lv ∧ v = lload_word p lv) ∨
       (get_tag pw = false ∧ v = MkLWord pw None)).
  Proof.
    intros Her Hincl Hr Hmem Hok Hstep.
    pose proof (erasure_regs_incl Her Hincl) as Hphys.
    destruct Hstep as [p ea pv pw Hauth Hmmio Hpv Hfilter Hnext
                      |p ea pw Hauth Hmmio Hload Hnext].
    - destruct (mem_access_authorised_reg_allows MemAccessRead Hphys Hr Hauth)
        as (g & b & e & a & Hacc).
      destruct (Hok _ _ _ _ _ _ Hacc) as [ [Hexp _] | (_ & [lv Hlv] & _) ].
      { by rewrite not_mmio_not_exposed_mmio in Hexp. }
      destruct (erasure_lookup_mem Her (lookup_weaken _ _ _ _ Hlv Hmem))
        as (pv' & Hpv' & Hmok).
      rewrite Hpv in Hpv'. injection Hpv' as <-.
      exists p, g, b, e, a, ea, (lload_word p lv), pw. split_and!; [done| | | done |].
      + by apply reg_word_ok_lload_word, (mem_word_ok_reg_word_ok _ _ _ pv).
      + by eapply load_filter_reg_phys; first apply (er_registry Her).
      + left. eauto.
    - destruct (mem_access_authorised_reg_allows MemAccessRead Hphys Hr Hauth)
        as (g & b & e & a & Hacc).
      pose proof (mmio_load_untagged _ _ _ Hload) as Ht.
      exists p, g, b, e, a, ea, (MkLWord pw None), pw. split_and!; [done| | | done |].
      + by apply reg_word_ok_untagged.
      + by apply reg_phys_untagged.
      + by right.
  Qed.

  (** A store step writes the logical word of [store_lift] to a wholly
      owned cell, or writes a time device. *)
  Lemma store_step_inv stored_word_ok Q R C φ lpc lreg lsreg lmem regs r imm (mem : LMem) dfracs c :
    erasure R C φ lpc lreg lsreg lmem → regs ⊆ lreg → r ∈ dom regs →
    store_lift stored_word_ok Q regs → mem_access_footprint MemAccessWrite regs r imm mem dfracs →
    store_step stored_word_ok r imm φ c →
    ∃ p g b e a ea, reg_allows_mem_access MemAccessWrite regs r imm p g b e a ea ∧
      ((∃ v pw, Q v ∧ is_Some (mem !! ea) ∧ dfracs !! ea = Some (DfracOwn 1) ∧
          mem_word_ok R C (lstore_word p v) pw ∧
          nextPC ((store_effect ea φ) .[ea :=ₐ pw]) = Some c) ∨
       (∃ td, nextPC (φ .[TD := td]) = Some c)).
  Proof.
    intros Her Hincl Hr Hlift Hok Hstep.
    pose proof (erasure_regs_incl Her Hincl) as Hphys.
    destruct Hstep as [p ea w Hauth Hmmio Hin Hwok Hnext
                      |p ea w φ' Hauth Hmmio Hstore Hnext].
    - destruct (mem_access_authorised_reg_allows MemAccessWrite Hphys Hr Hauth)
        as (g & b & e & a & Hacc).
      destruct (Hok _ _ _ _ _ _ Hacc) as [ [Hexp _] | (_ & Hlv & Hdq) ].
      { by rewrite not_mmio_not_exposed_mmio in Hexp. }
      destruct (Hlift _ _ _ _ _ _ _ _ Her Hincl Hwok) as (v & HQ & Hvok & Hvphys).
      exists p, g, b, e, a, ea. split; first done. left.
      exists v, (store_word p w). split_and!; [done | done | by apply Hdq | | done].
      apply reg_phys_mem_word_ok; first by apply reg_word_ok_lstore_word.
      by apply reg_phys_lstore_word.
    - destruct (mem_access_authorised_reg_allows MemAccessWrite Hphys Hr Hauth)
        as (g & b & e & a & Hacc).
      destruct (Hok _ _ _ _ _ _ Hacc) as [ [Hexp _] | (Hmmio' & _) ]; last congruence.
      exists p, g, b, e, a, ea. split; first done. right.
      rewrite /mmio_store (exposed_mmio_not_shadow _ Hexp) (exposed_mmio_not_revoker _ Hexp) in Hstore.
      rewrite /is_exposed_mmio_address in Hexp. rewrite Hexp in Hstore.
      destruct (time_dev_store (timedevs φ) ea w) as [td|]; simplify_eq/=. by exists td.
  Qed.

End mem_access_pure.

#[local] Arguments load_step_inv {MP R C φ lpc lreg lsreg lmem regs dst r imm mem dfracs c}.
#[local] Arguments store_step_inv
  {MP stored_word_ok Q R C φ lpc lreg lsreg lmem regs r imm mem dfracs c}.

(** Closes [mem_access_authorised perm_ok φ r imm p ea] from the lookup of [r] and the
    checks of the step, split at their conjunctions. *)
Ltac solve_mem_access_authorised :=
  repeat match goal with
    | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
    end;
  eexists _, _, _, _; split_and!; eassumption.

(** Closes [load_member] and [store_member] of a concrete step function:
    one constructor per branch of the unfolded step. The stored word's
    condition is left to [solve_wok]. *)
Ltac solve_mem_access_member_with solve_wok :=
  let Hex := fresh "Hex" in
  intros ? ? ? Hex; cbn in Hex;
  repeat (simplify_option_eq; try case_match);
  first
    [ eapply ls_device; [solve_mem_access_authorised | eassumption | eassumption | eassumption]
    | eapply ls_cell; [solve_mem_access_authorised | eassumption | eassumption
                      | rewrite /load_filter; by simplify_option_eq | eassumption]
    | eapply ss_device; [solve_mem_access_authorised | eassumption | eassumption | eassumption]
    | eapply ss_cell; [solve_mem_access_authorised | eassumption | by eexists | solve_wok
                      | rewrite /store_effect; eassumption] ].

Ltac solve_mem_access_member := solve_mem_access_member_with idtac.

(** [CLoad dst src imm] loads at the address that [src] authorises at
    offset [imm], into [dst]. *)
Lemma CLoad_member `{MachineParameters} dst src imm :
  load_member exec_opt (CLoad dst src imm) dst src imm.
Proof. solve_mem_access_member. Qed.

(** [Store dst ρ imm] writes the word of its argument [ρ] at the address
    that [dst] authorises at offset [imm]; that word has [stored_word_ok]. *)
Lemma Store_member `{MachineParameters} (stored_word_ok : ExecConf → Word → Prop) dst ρ imm :
  (∀ φ w, word_of_argument (reg φ) ρ = Some w → stored_word_ok φ w) →
  store_member exec_opt stored_word_ok (Store dst ρ imm) dst imm.
Proof.
  intros Hwok. solve_mem_access_member_with ltac:(by eapply Hwok).
Qed.

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

  (** A load of a membership [load_member exec_opt i dst r imm], with the
      cells [mem] that [r] may read (the PC's cell included) at fractions
      [dfracs]: a fault, or the PC incremented and [dst] holding a cell of
      [mem] as [lload_word] reads it, or an untagged word of a device
      ([load_result]). *)
  Lemma wp_load_step Ep pc_p pc_g pc_b pc_e pc_a pc_π w i dst r imm
      (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) :
    decodeInstrW w.(lw) = i → load_member exec_opt i dst r imm → sw_of (kind_of th) i = None →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → (dst = cnull ∨ dst ∈ dom regs) →
    mem !! pc_a = Some w → dom dfracs = dom mem → mem_access_footprint MemAccessRead regs r imm mem dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜load_result (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst r imm mem lpc' regs' retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hi Hmember Hsw Hvpc Hr Hdst Hmem_pc Hdom Hok Φ).
    iIntros "(>HPC & >Hmem & >Hmap) Hφ".
    destruct (prod_merge_lookup_dom Hmem_pc Hdom) as [dq_pc Hmerge_pc].
    iDestruct (big_sepM_delete _ _ pc_a with "Hmem") as "[Hpc_a Hmem]"; first exact Hmerge_pc.
    iSimpl in "Hpc_a".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [by rewrite Hi | done |].
    iNext. iIntros (rf sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (big_sepM_delete _ _ pc_a (dq_pc, w) with "[Hpc_a $Hmem]") as "Hmem";
      [exact Hmerge_pc | iExact "Hpc_a" |].
    iAssert (⌜mem ⊆ lmem⌝)%I as %Hmem_incl.
    { rewrite map_subseteq_spec. iIntros (a v Hv).
      destruct (prod_merge_lookup_dom Hv Hdom) as [dq Hmerge].
      by iApply (gen_mem_valid_inSepM_general with "Hm Hmem"). }
    rewrite Hi /exec in Hstep.
    destruct (exec_opt i pc_p _) as [conf|] eqn:Hexec; cycle 1.
    { simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro. by left. }
    subst conf.
    destruct (load_step_inv Her Hlregs Hr Hmem_incl Hok (Hmember _ _ _ Hexec))
      as (p & g & b & e & a & ea & v & pw & Hacc & Hvok & Hpw & Hnext & Hcases).
    iApply (instr_close_reg_update (dst := dst) (v := v) (w := pw)
      (λ lpc' regs' retv, load_result (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst r imm mem
                            lpc' regs' retv)
      Her Hlregs Hdst Hvok with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hmem]").
    { by rewrite Hnext. } { exact Hpw. }
    { intros lpc' Hinc. right. exists p, g, b, e, a, ea. split_and!; [done..|].
      destruct Hcases as [ (lv & Hlv & ->) | (Ht & ->) ]; [left | right]; eauto. }
    { intros _. by left. }
    iIntros (lpc' regs' retv Hres) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

  (** A store of a membership [store_member exec_opt stored_word_ok i r imm],
      whose stored word lifts to a logical word with [Q] ([store_lift]), with the
      cells [mem] that [r] may write (wholly owned, the PC's cell included):
      a fault, or the PC incremented and a cell of [mem] holding the stored
      word as [lstore_word] writes it, or a device written
      ([store_result]). *)
  Lemma wp_store_step Ep pc_p pc_g pc_b pc_e pc_a pc_π w i r imm stored_word_ok
      (Q : LWord → Prop) (mem : LMem) (dfracs : gmap Addr dfrac) (regs : LReg) :
    decodeInstrW w.(lw) = i → store_member exec_opt stored_word_ok i r imm →
    sw_of (kind_of th) i = None →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    r ∈ dom regs → store_lift stored_word_ok Q regs →
    mem !! pc_a = Some w → dom dfracs = dom mem → mem_access_footprint MemAccessWrite regs r imm mem dfracs →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
        ▷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) }}}
      Instr Executable @ Ep
    {{{ lpc' mem' retv, RET retv;
        ⌜store_result Q (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r imm mem lpc' mem' retv⌝ ∗
        PC ↦ₚ lpc' ∗
        ([∗ map] a↦dv ∈ prod_merge dfracs mem', a ↦ₐ{dv.1} dv.2) ∗
        [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}.
  Proof.
    iIntros (Hi Hmember Hsw Hvpc Hr Hlift Hmem_pc Hdom Hok Φ).
    iIntros "(>HPC & >Hmem & >Hmap) Hφ".
    destruct (prod_merge_lookup_dom Hmem_pc Hdom) as [dq_pc Hmerge_pc].
    iDestruct (big_sepM_delete _ _ pc_a with "Hmem") as "[Hpc_a Hmem]"; first exact Hmerge_pc.
    iSimpl in "Hpc_a".
    iApply (wp_instr_step_nosw with "HPC Hpc_a Hmap"); [by rewrite Hi | done |].
    iNext. iIntros (rf sr m st td lreg lsreg lmem R C c σ') "@".
    iDestruct (big_sepM_delete _ _ pc_a (dq_pc, w) with "[Hpc_a $Hmem]") as "Hmem";
      [exact Hmerge_pc | iExact "Hpc_a" |].
    rewrite Hi /exec in Hstep.
    destruct (exec_opt i pc_p _) as [conf|] eqn:Hexec; cycle 1.
    { simplify_eq. iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap". iApply "Hφ". iFrame. iPureIntro. by left. }
    subst conf.
    destruct (store_step_inv Her Hlregs Hr Hlift Hok (Hmember _ _ _ Hexec))
      as (p & g & b & e & a & ea & Hacc & [ (v & pw & HQ & Hin & Hdq & Hpw & Hnext) | (td' & Hnext) ]).
    - (* A cell. *)
      rewrite /store_effect in Hnext.
      iApply (instr_close_mem_update
        (λ lpc' mem' retv, store_result Q (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r imm mem
                             lpc' mem' retv)
        Her Hin Hdq Hpw with "HPCa Hr Hsr Hm Hst HR HC HPC Hmem Hmap [Hφ]").
      { by rewrite Hnext. }
      { intros lpc' Hinc. right. exists p, g, b, e, a, ea. split_and!; [done..|]. left. eauto. }
      { intros _. by left. }
      iIntros (lpc' mem' retv Hres) "HPC Hmem Hmap". iApply "Hφ". by iFrame.
    - (* A time device. *)
      pose proof (erasure_set_timedevs td' Her) as Her1.
      change (nextPC (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) rf sr m st td') = Some (c, σ'))
        in Hnext.
      iApply (instr_close_kept_trans _ (MkExecConf (Cap pc_p pc_g pc_b pc_e pc_a) rf sr m st td'));
        first by apply sys_kept_same_sreg.
      iApply (instr_close_pc_update (n := 1)
        (λ lpc' retv, store_result Q (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs r imm mem
                        lpc' mem retv)
        Her1 with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [Hφ Hmem]").
      { rewrite /nextPC in Hnext. by rewrite Hnext. }
      { intros lpc' Hinc. right. exists p, g, b, e, a, ea. split_and!; [done..|]. by right. }
      { intros _. by left. }
      iIntros (lpc' retv Hres) "HPC Hmap". iApply "Hφ". by iFrame.
  Qed.

End mem_access_rules.
