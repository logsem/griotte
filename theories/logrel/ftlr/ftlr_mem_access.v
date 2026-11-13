From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Import rules_mem_access capability_monotonicity ftlr_shapes ftlr_base
  ftlr_contract interp_weakening world_interp_cells rules_registry.
Import CoreWPNotations.
#[local] Open Scope capability_scope.

(** The register lookup and the projections of the erasure take their
    hypothesis only; the accessed address of a capability is explicit. *)
#[local] Arguments llookup_reg_cap {regs r t p g b e a}.
#[local] Arguments er_registry {MP R C σ lpc lreg lsreg lmem}.
#[local] Arguments interp_cap_mem_or_exposed_mmio {Σ ceriseb th Cname sealsg stsg relg cstackg
  cthreads CL MP CR W C p g b e a} a' {π}.

(** * The memory shape of the fundamental theorem

    A memory instruction is a load or a store. The membership of a load or
    a store names its authorising register and offset, so the accessed
    region is opened before the step: a quarantined authority
    ([mem_access_quarantined]) or owned cells lent to the WP rules of
    [rules_mem_access.v] ([mem_access_map]). A stored word is below a
    register ([store_source]), hence safe before the world closes. *)

(** ** Stored words *)

Section store_source.
  Context `{MP : MachineParameters}.

  (** A word with no more authority than a register of [φ]. An untagged
      word is below [cnull]. *)
  Definition store_source (φ : ExecConf) (w : Word) : Prop :=
    ∃ r w0, reg φ !!ᵣ r = Some w0 ∧ w ⊑ w0.

  (** Its logical counterpart: untagged, or below a logical register. *)
  Definition lstore_source (regs : LReg) (v : LWord) : Prop :=
    get_tag v.(lw) = false ∨ ∃ r v0, regs !! r = Some v0 ∧ v ⊑ₗ v0.

  (** An argument of an instruction, a register or an integer, is below a
      register. *)
  Lemma word_of_argument_store_source φ ρ w :
    word_of_argument (reg φ) ρ = Some w → store_source φ w.
  Proof.
    destruct ρ as [n | r]; cbn; intros Harg.
    - simplify_eq. exists cnull, (WInt 0). split.
      + by apply lookup_reg_cnull.
      + by apply wle_untagged.
    - exists r, w. split; [done | apply wle_refl].
  Qed.

  (** A word below a register lifts to a logical word below a logical
      register. *)
  Lemma store_source_lift regs :
    (∀ x, is_Some (regs !! x)) →
    (∀ r v, regs !! r = Some v → no_prov_disjoint_from_heap v) →
    store_lift store_source (lstore_source regs) regs.
  Proof.
    intros Hsome Hnoid R C φ lpc lreg lsreg lmem w Her Hincl (r & w0 & Hr & Hle).
    pose proof (full_regs_incl_eq regs lreg Hsome Hincl) as ->.
    destruct (get_tag w) eqn:Ht.
    - destruct (erasure_reg_tagged Her Hr (word_le_tagged _ _ Hle Ht))
        as (vs & Hvs & <- & Hok & Hphys).
      destruct (word_le_lift R C _ vs w (er_registry Her) Hok Hphys
                  (Hnoid r vs Hvs) Hle Ht) as (Hok' & Hphys' & Hle').
      eexists. split_and!; [right; by exists r, vs | exact Hok' | exact Hphys'].
    - exists (MkLWord w None). split_and!;
        [by left | by apply reg_word_ok_untagged | by apply reg_phys_untagged].
  Qed.

End store_source.

(** A store writes the word of its argument. *)
Lemma Store_member_store_source `{MachineParameters} dst ρ imm :
  store_member exec_opt store_source (Store dst ρ imm) dst imm.
Proof. apply Store_member. intros φ w. apply word_of_argument_store_source. Qed.

(** ** Membership tactics *)

(** Closes [store_source φ w] from the hypothesis that read [w]: an argument,
    a register or an integer. The stored word [w] may be an evar, fixed
    first by the memory write of the step, so that it never binds to the
    lookup of the authorising register. *)
Ltac solve_store_source :=
  try lazymatch goal with
    | _ : nextPC (_ .[_ :=ₐ store_word _ ?v]) = Some _ |- store_source _ ?w => unify w v
    end;
  lazymatch goal with
  | H : word_of_argument (reg ?φ) _ = Some ?w |- store_source ?φ ?w =>
      exact (word_of_argument_store_source _ _ _ H)
  | H : reg ?φ !!ᵣ ?r = Some ?w |- store_source ?φ ?w =>
      exists r, w; split; [exact H | apply wle_refl]
  | |- store_source _ (WInt _) =>
      exists cnull, (WInt 0); split;
      [by apply lookup_reg_cnull | by apply wle_untagged]
  | _ => reject_shape "the stored word is neither an argument, a register nor an integer"
  end.

(** The memberships of the two parts of the shape. [idtac] delays
    [solve_store_source] to the stored-word goal. *)
Ltac solve_load_member := solve_mem_access_member.
Ltac solve_store_member := solve_mem_access_member_with ltac:(idtac; solve_store_source).

(** ** The memory shape *)

(** A memory instruction: a load, or a store of a word below a register. *)
Definition mem_member `{MachineParameters} (step : instr → Perm → ExecConf → option Conf)
    (i : instr) : Prop :=
  (∃ dst r imm, load_member step griotte_load_filter i dst r imm) ∨
  (∃ r imm, store_member step store_source i r imm).

(** Closes [mem_member step i]: a load, else a store. *)
Ltac solve_mem_member :=
  first [ left; do 3 eexists; solve_load_member
        | right; do 2 eexists; solve_store_member ].

(** ** The fundamental theorem for memory accesses *)

Section ftlr_mem_access.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).

  (** An untagged register authorises no access. *)
  Lemma reg_allows_mem_access_untagged k regs r imm p g b e a ea v :
    regs !! r = Some v → get_tag v.(lw) = false →
    ¬ reg_allows_mem_access k regs r imm p g b e a ea.
  Proof.
    intros Hr Ht (Hsrc & _).
    destruct (llookup_reg_cap Hsrc) as (_ & π & Hr').
    rewrite Hr in Hr'. by simplify_eq.
  Qed.

  (** One cell, as a map of fractional points-to. *)
  Lemma pointsto_prod_merge_1 a dq v :
    a ↦ₐ{dq} v ⊣⊢
    [∗ map] a'↦dv ∈ prod_merge (<[a := dq]> ∅) (<[a := v]> ∅), a' ↦ₐ{dv.1} dv.2.
  Proof.
    rewrite /prod_merge -(insert_merge _ _ _ _ (dq, v)) // merge_empty.
    by rewrite big_sepM_insert // big_sepM_empty right_id.
  Qed.

  (** Two regions of the same key outside the heap, in the same part, have
      the same contents, one step later. *)
  Lemma region_rel_part_pc_content_agree ρ W C a p1 p2 P1 P2 :
    region_rel_part ρ W C (LNonHeap a) p1 P1 -∗
    region_rel_part ρ W C (LNonHeap a) p2 P2 -∗
    ∀ v, ▷ (pc_content ρ W C P1 v ≡ pc_content ρ W C P2 v).
  Proof.
    iIntros "#H1 #H2" (v).
    destruct ρ; rewrite /region_rel_part /region_rel_perm /region_rel_l /pc_content.
    - iDestruct (rel_perm_agree with "H1 H2") as "[_ Heq]". iApply ("Heq" $! (C, v)).
    - iDestruct "H1" as "(H1 & _)". iDestruct "H2" as "(H2 & _)".
      iDestruct (rel_l_agree with "H1 H2") as "[_ Heq]". iApply ("Heq" $! (W, C, v)).
  Qed.

  (** *** Access condition *)

  (** What an access of kind [k] through permission [p] may do to a cell of
      content predicate [P]: read a valid word, or write any valid word. *)
  Definition mem_access_cond (k : mem_access_kind) ρ W C (P : D) (p : Perm) : iProp Σ :=
    match k with
    | MemAccessRead => □ ∀ v, pc_content ρ W C P v -∗ interp W C (lload_word p v)
    | MemAccessWrite => ⌜ρ = InPerm → isWL p = false⌝ ∗
                  □ ∀ v, interp W C v -∗ pc_content ρ W C P (lstore_word p v)
    end.
  #[global] Instance mem_access_cond_persistent k ρ W C P p : Persistent (mem_access_cond k ρ W C P p).
  Proof. destruct k; apply _. Qed.

  (** From the register, for any key and any part of its region. *)
  Lemma mem_access_cond_of_reg k W C p g b e a ea π :
    mem_access_perm k p = true → withinBounds b e ea = true → is_exposed_mmio_address ea = false →
    thread_in th C -∗
    interp W C (Cap p g b e a @@? π) -∗
    ∃ p'' P'', ⌜persistent_cond P''⌝ ∗
      region_rel W C (addr_key π ea) p'' P'' p g ∗
      ▷ (∀ ρ, ⌜ρ = InPerm → isWL p = false⌝ -∗ mem_access_cond k ρ W C P'' p).
  Proof.
    iIntros (Hperm Hwb%withinBounds_true_iff Hnexp) "#Hth #Hv".
    destruct k; cbn in Hperm.
    - iDestruct (read_allowed_inv _ _ ea with "Hth Hv")
        as (p'' P'' Hfl Hpers) "(#Hrel & _ & #Hrc & _)"; [solve_addr|done|by rewrite Hperm|].
      iExists p'', P''. iFrame "Hrel %". iIntros "!>" (ρ _) "!>". iIntros (v) "Hc".
      iApply (interp_weakening_word_load with "Hth"); first exact Hfl.
      iApply (pc_content_rcond with "Hrc Hc").
    - iDestruct (write_allowed_inv _ _ ea with "Hv")
        as (p'' P'' _ Hpers) "(#Hrel & _ & #Hwc & _)"; [solve_addr|done|by rewrite Hperm|].
      iExists p'', P''. iFrame "Hrel %". iIntros "!>" (ρ Hρ). iSplit; first done.
      iIntros "!>" (v) "Hv'". by iApply (pc_content_wcond with "Hwc Hv'").
  Qed.
  #[local] Arguments mem_access_cond_of_reg k {W C p g b e a} ea π.

  (** Transport along the region agreement. *)
  Lemma mem_access_cond_agree k ρ W C P1 P2 p :
    (∀ v, ▷ (pc_content ρ W C P1 v ≡ pc_content ρ W C P2 v)) -∗
    ▷ mem_access_cond k ρ W C P1 p -∗
    ▷ mem_access_cond k ρ W C P2 p.
  Proof.
    iIntros "#Heq Hacc". destruct k; cbn [mem_access_cond]; iNext.
    - iDestruct "Hacc" as "#Hacc". iIntros "!>" (v) "Hc".
      iApply "Hacc". by iRewrite ("Heq" $! v).
    - iDestruct "Hacc" as "[$ #Hacc]". iIntros "!>" (v) "Hv".
      iRewrite -("Heq" $! (lstore_word p v)). by iApply "Hacc".
  Qed.

  (** The PC's cell, from the authorising register only. *)
  Lemma mem_access_cond_pc k W C p g b e a pc_a ρ pc_p' P pc_w :
    mem_access_perm k p = true → withinBounds b e pc_a = true → is_exposed_mmio_address pc_a = false →
    thread_in th C -∗
    interp W C (Cap p g b e a @@? None) -∗
    region_rel_part ρ W C (LNonHeap pc_a) pc_p' P -∗
    world_interp_open W C [LNonHeap pc_a] -∗
    pc_a ↦ₐ pc_w -∗
    world_interp_open W C [LNonHeap pc_a] ∗
    pc_a ↦ₐ pc_w ∗
    ▷ mem_access_cond k ρ W C P p.
  Proof.
    iIntros (Hperm Hwb Hnexp) "#Hth #Hv #Hinva Hworld Ha".
    iDestruct (mem_access_cond_of_reg k pc_a None with "Hth Hv")
      as (p'' P'' _) "[Hrel Hacc]"; [done..|].
    iDestruct (region_rel_part_of with "Hrel") as (ρ'' Hρ'') "#Hpart".
    iDestruct (region_rel_part_agree_open with "Hworld Ha Hinva Hpart") as "($ & $ & %Heq)".
    destruct Heq as [<- <-].
    iApply (mem_access_cond_agree with "[] [Hacc]").
    - iApply (region_rel_part_pc_content_agree with "Hpart Hinva").
    - iNext. by iApply "Hacc".
  Qed.

  (** *** The outcomes of the opening *)

  (** A read finds a valid word. *)
  Definition mem_access_value k W C regs r imm (mem : LMem) : iProp Σ :=
    □ ∀ p g b e a ea v, ⌜k = MemAccessRead⌝ → ⌜reg_allows_mem_access k regs r imm p g b e a ea⌝ →
      ⌜mem !! ea = Some v⌝ → interp W C (lload_word p v).

  (** What the access did to [mem]: nothing, or a write of a valid word. *)
  Definition mem_access_update k W C regs r imm (mem mem' : LMem) : iProp Σ :=
    ⌜mem' = mem⌝ ∨
    ∃ p g b e a ea v,
      ⌜k = MemAccessWrite⌝ ∗
      ⌜reg_allows_mem_access k regs r imm p g b e a ea⌝ ∗
      ⌜is_Some (mem !! ea)⌝ ∗
      ⌜mem' = <[ea := lstore_word p v]> mem⌝ ∗
      interp W C v.

  (** The authorising object is quarantined: the PC's cell at a fraction
      [dq] and the closing of the world. *)
  Definition mem_access_quarantined W C (regs : LReg) (r : RegName) pc_a (dq : dfrac) pc_w : iProp Σ :=
    ∃ ι ws,
      ⌜regs !! r = Some ws⌝ ∗
      ⌜has_authority ws.(lw)⌝ ∗
      ⌜ws.(lprov) = Some ι⌝ ∗
      ι ⊒ AQuar ∗
      pc_a ↦ₐ{dq} pc_w ∗
      ▷ (pc_a ↦ₐ{dq} pc_w -∗ world_interp W C).

  (** The memory of the access, the PC's cell included, at fractions
      [dfracs], with the closing of the world. *)
  Definition mem_access_map k W C regs r imm pc_a pc_w : iProp Σ :=
    ∃ (mem : LMem) (dfracs : gmap Addr dfrac),
      ⌜dom dfracs = dom mem⌝ ∗
      ⌜mem !! pc_a = Some pc_w⌝ ∗
      ⌜mem_access_footprint k regs r imm mem dfracs⌝ ∗
      ([∗ map] a↦dv ∈ prod_merge dfracs mem, a ↦ₐ{dv.1} dv.2) ∗
      ▷ mem_access_value k W C regs r imm mem ∗
      ▷ (∀ mem',
           ([∗ map] a↦dv ∈ prod_merge dfracs mem', a ↦ₐ{dv.1} dv.2) -∗
           mem_access_update k W C regs r imm mem mem' -∗
           world_interp W C).

  (** The opening of an access: a quarantined authority, or the memory of the
      access. *)
  Definition mem_access_open k W C regs r imm pc_a pc_w : iProp Σ :=
    mem_access_quarantined W C regs r pc_a (DfracOwn 1) pc_w ∨ mem_access_map k W C regs r imm pc_a pc_w.

  (** Only the PC's cell, at a fraction [dq]: no access, a device, or the
      PC's cell itself. *)
  Lemma mem_access_map_pc k W C regs r imm pc_a dq pc_w ρ P :
    persistent_cond P →
    mem_access_footprint k regs r imm (<[pc_a := pc_w]> ∅) (<[pc_a := dq]> ∅) →
    ▷ (□ ∀ p g b e a, ⌜reg_allows_mem_access k regs r imm p g b e a pc_a⌝ → mem_access_cond k ρ W C P p) -∗
    ▷ pc_cell_close W C pc_a dq P ρ -∗
    ▷ pc_content ρ W C P pc_w -∗
    world_interp_open W C [LNonHeap pc_a] -∗
    pc_a ↦ₐ{dq} pc_w -∗
    mem_access_map k W C regs r imm pc_a pc_w.
  Proof.
    iIntros (Hpers Hok). pose proof (pc_content_persistent ρ W C P pc_w Hpers).
    iIntros "#Hcell Hpc_close #Hw Hworld Ha".
    iExists (<[pc_a := pc_w]> ∅), (<[pc_a := dq]> ∅).
    rewrite -pointsto_prod_merge_1. iFrame "Ha".
    iSplit; first by rewrite !dom_insert_L. iSplit; first by simplify_map_eq.
    iSplit; first done. iSplitR; iNext.
    - iIntros "!>" (p g b e a ea v -> Hacc Hv).
      apply lookup_insert_Some in Hv as [ [<- <-] | [_ Hv] ]; last by simplify_map_eq.
      iApply ("Hcell" $! _ _ _ _ _ Hacc with "Hw").
    - iIntros (mem') "Hmem [-> | (%p & %g & %b & %e & %a & %ea & %v & -> & %Hacc & %Hin & -> & #Hv)]".
      + rewrite -pointsto_prod_merge_1. iApply ("Hpc_close" with "Hworld Hmem Hw").
      + apply lookup_insert_is_Some in Hin as [<- | [_ Hin] ]; last by destruct Hin; simplify_map_eq.
        rewrite insert_insert_eq -pointsto_prod_merge_1.
        iDestruct ("Hcell" $! _ _ _ _ _ Hacc) as "[_ Hwr]".
        iApply ("Hpc_close" with "Hworld Hmem"). by iApply "Hwr".
  Qed.

  (** Another cell: the cell at [ea] in a region of another key, with the
      PC's cell. *)
  Lemma mem_access_map_cell k W C regs r imm p g b e a ea π pc_a pc_w ρ P ρ' p'' P'' w0 :
    reg_allows_mem_access k regs r imm p g b e a ea → is_mmio_address ea = false →
    addr_key π ea ≠ LNonHeap pc_a →
    persistent_cond P → persistent_cond P'' →
    region_rel_part ρ' W C (addr_key π ea) p'' P'' -∗
    ▷ mem_access_cond k ρ' W C P'' p -∗
    ▷ pc_cell_close W C pc_a (DfracOwn 1) P ρ -∗
    ▷ pc_content ρ W C P pc_w -∗
    world_interp_open W C ({[addr_key π ea]} ∪ [LNonHeap pc_a]) -∗
    ▷ pc_open W C (addr_key π ea) p'' P'' w0 ρ' -∗
    pc_a ↦ₐ pc_w -∗
    ◇ mem_access_map k W C regs r imm pc_a pc_w.
  Proof.
    iIntros (Hacc Hmmio Hkey Hpers Hpers'').
    pose proof (pc_content_persistent ρ W C P pc_w Hpers).
    pose proof (pc_content_persistent ρ' W C P'' w0 Hpers'').
    iIntros "#Hpart #Hacc_ea Hpc_close #Hw Hworld Hres Ha".
    iDestruct (pc_open_acc_forall with "Hpart Hres") as "[ [Hea #HP] Hclose]".
    iEval (rewrite addr_key_pointsto) in "Hea". iDestruct "Hea" as "[>Hea Hshare]".
    iDestruct (address_neq with "Hea Ha") as %Hne.
    iModIntro.
    iExists (<[ea := w0]> (<[pc_a := pc_w]> ∅)),
      (<[ea := DfracOwn 1]> (<[pc_a := DfracOwn 1]> ∅)).
    iSplit; first by rewrite !dom_insert_L. iSplit; first by simplify_map_eq. iSplit.
    { iPureIntro. intros ?????? Hacc1.
      destruct (reg_allows_mem_access_det Hacc Hacc1) as (_ & _ & _ & _ & _ & ->).
      right. split; [by simplify_map_eq | intros _; by simplify_map_eq]. }
    rewrite memMap_resource_2ne_dq //. iFrame "Hea Ha". iSplitR; iNext.
    - iIntros "!>" (????? ea1 v -> Hacc1 Hv).
      destruct (reg_allows_mem_access_det Hacc Hacc1) as (-> & _ & _ & _ & _ & ->).
      rewrite lookup_insert_eq in Hv. injection Hv as <-. by iApply "Hacc_ea".
    - iIntros (mem') "Hmem [-> | (%p1 & %g1 & %b1 & %e1 & %a1 & %ea1 & %v & -> & %Hacc1 & _ & -> & #Hstored)]".
      + rewrite memMap_resource_2ne_dq //. iDestruct "Hmem" as "[Hea Ha]".
        iApply ("Hpc_close" with "[-Ha] Ha Hw").
        iApply (pc_close_next with "Hworld Hpart [-]"); [set_solver|done|].
        iApply "Hclose". iFrame "HP". iApply (addr_key_pointsto_join with "Hea Hshare").
      + destruct (reg_allows_mem_access_det Hacc Hacc1) as (-> & _ & _ & _ & _ & ->).
        rewrite insert_insert_eq memMap_resource_2ne_dq //. iDestruct "Hmem" as "[Hea Ha]".
        iApply ("Hpc_close" with "[-Ha] Ha Hw").
        iApply (pc_close_next with "Hworld Hpart [-]"); [set_solver|done|].
        iApply ("Hclose" $! (lstore_word p v)). iDestruct "Hacc_ea" as "[_ Hwr]".
        iSplitL; first iApply (addr_key_pointsto_join with "Hea Hshare"). by iApply "Hwr".
  Qed.

  (** The opening of a memory access by the register [r] at offset [imm],
      before the step: a quarantined authority, or the memory of the access. *)
  Lemma mem_access_open_intro k {W C regs} r imm {pc_p pc_g pc_b pc_e pc_a pc_w ρ pc_p' P} :
    persistent_cond P → validPCperm pc_p pc_g → (pc_b <= pc_a)%a ∧ (pc_a < pc_e)%a →
    thread_in th C -∗
    (∀ r v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    interp W C (Cap pc_p pc_g pc_b pc_e pc_a) -∗
    region_rel_part ρ W C (LNonHeap pc_a) pc_p' P -∗
    ▷ pc_open W C (LNonHeap pc_a) pc_p' P pc_w ρ -∗
    world_interp_open W C [LNonHeap pc_a] -∗
    ◇ mem_access_open k W C regs r imm pc_a pc_w.
  Proof.
    iIntros (Hpers Hp Hbae). pose proof (pc_content_persistent ρ W C P pc_w Hpers).
    iIntros "#Hth #Hreg #Hpc #Hinva WorldRes Hworld".
    iDestruct (interp_cap_disjoint with "Hpc") as %[Hpc_mmio _]; first by destruct Hp.
    assert (is_mmio_address pc_a = false) as Hpc_nmmio.
    { apply (disjoint_from_mmio_not_in pc_b pc_e); first done.
      apply withinBounds_true_iff. solve_addr. }
    iDestruct (pc_cell_open with "Hinva WorldRes") as "(>Ha & #Hw & Hpc_close)"; first done.
    destruct (reg_allows_mem_access_cases k regs r imm)
      as [(p & g & b & e & a & ea & Hacc) | Hnot].
    2: { (* No access. *)
         iModIntro. iRight. iApply (mem_access_map_pc with "[] Hpc_close Hw Hworld Ha"); first done.
         - intros ?????? Hacc1; exfalso; eauto 10.
         - iIntros "!> !>" (????? Hacc1). exfalso; eauto 10. }
    pose proof Hacc as (Hsrc & _ & Hperm & Hwb).
    destruct (llookup_reg_cap Hsrc) as (_ & π & Hr).
    iDestruct ("Hreg" $! r _ Hr) as "Hv".
    destruct (is_exposed_mmio_address ea) eqn:Hexp.
    { (* An exposed device. *)
      assert (ea ≠ pc_a) as Hne by (intros ->; by rewrite not_mmio_not_exposed_mmio in Hexp).
      iModIntro. iRight. iApply (mem_access_map_pc with "[] Hpc_close Hw Hworld Ha"); first done.
      - intros ?????? Hacc1. destruct (reg_allows_mem_access_det Hacc Hacc1) as (_ & _ & _ & _ & _ & ->).
        left. by simplify_map_eq.
      - iIntros "!> !>" (????? Hacc1).
        by destruct (reg_allows_mem_access_det Hacc Hacc1) as (_ & _ & _ & _ & _ & ->). }
    iDestruct (interp_cap_mem_or_exposed_mmio ea with "Hv")
      as %[ [Hmmio _] | (Hexp' & _)]; [by eapply mem_access_perm_nonO|done| |congruence].
    destruct (decide (addr_key π ea = LNonHeap pc_a)) as [Hkey|Hkey].
    { (* The PC's cell. *)
      destruct (addr_key_pc _ _ _ Hkey) as [-> ->].
      iDestruct (mem_access_cond_pc with "Hth Hv Hinva Hworld Ha") as "(Hworld & Ha & #Hacc_pc)";
        [done..|].
      iModIntro. iRight. iApply (mem_access_map_pc with "[] Hpc_close Hw Hworld Ha"); first done.
      - intros ?????? Hacc1. destruct (reg_allows_mem_access_det Hacc Hacc1) as (_ & _ & _ & _ & _ & ->).
        right. split; [by simplify_map_eq | intros _; by simplify_map_eq].
      - iIntros "!> !>" (????? Hacc1). by destruct (reg_allows_mem_access_det Hacc Hacc1) as (-> & _). }
    (* Another cell, or a quarantined authority. *)
    iDestruct (mem_access_cond_of_reg with "Hth Hv") as (p'' P'' Hpers'') "[#Hrel Hacc]"; [done..|].
    iDestruct (open_world_interp_next_cases _ _ _ π ea with "Hrel Hworld")
      as "[(%ρ' & %Hρ' & #Hpart & Hworld & Hres) | (%ι & -> & #Hq & Hworld)]"; [done|set_solver|..].
    2: { iDestruct (interp_cap_has_authority with "Hv") as %Hauth; [by eapply mem_access_perm_nonO|done|].
         iModIntro. iLeft. iExists ι, _. iFrame "Hq Ha %". iSplit; first done.
         iIntros "!> Ha". iApply ("Hpc_close" with "Hworld Ha Hw"). }
    iDestruct "Hres" as (w0) "Hres".
    iDestruct ("Hacc" $! ρ' Hρ') as "#Hacc_ea".
    iMod (mem_access_map_cell with "Hpart Hacc_ea Hpc_close Hw Hworld Hres Ha") as "Hmem"; [done..|].
    iModIntro. by iRight.
  Qed.

  (** *** Closers *)

  (** The registers stay safe when the tag of one of them is cleared. *)
  Lemma interp_refilter W C (regs : LReg) r ws :
    regs !! r = Some ws →
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    ∀ (r' : RegName) v, ⌜<[r := lclear_tag ws]> regs !! r' = Some v⌝ → interp W C v.
  Proof.
    iIntros (Hws) "#Hreg". iIntros (r' v Hv). destruct (decide (r' = r)) as [->|Hne].
    - rewrite lookup_insert_eq in Hv. injection Hv as <-. iApply interp_clear_tag.
    - rewrite lookup_insert_ne // in Hv. by iApply "Hreg".
  Qed.

  (** The access faulted on the tag of the authorising register [r]. *)
  Lemma ftlr_close_quarantined W C regs r ws pc :
    (∀ r, is_Some (regs !! r)) → regs !! r = Some ws →
    PC ↦ₚ[th] pc -∗
    regs[th] (<[r := lclear_tag ws]> regs) -∗
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    ▷ world_interp W C -∗
    ftlr_contract_intro_post W C FaultedV.
  Proof.
    iIntros (Hfull Hws) "HPC Hmap #Hreg Hworld".
    iApply (ftlr_contract_intro_post_fault with "HPC Hmap [$Hworld]").
    { intros r'. rewrite lookup_insert_is_Some'. by right. }
    iNext. by iApply interp_refilter.
  Qed.

  (** A word below a safe register is safe. *)
  Lemma lstore_source_sound W C (regs : LReg) v :
    lstore_source regs v →
    ftlr_IH -∗
    thread_in th C -∗
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    interp W C v.
  Proof.
    iIntros ([Ht | (r & v0 & Hr & Hle)]) "#IH #Hthread #Hreg".
    - by iApply interp_untagged.
    - iApply (lword_le_sound with "IH Hthread"); first exact Hle. by iApply "Hreg".
  Qed.

  (** A quarantined authority: the tag of the authorising register [r] is cleared. *)
  Lemma mem_access_quarantined_refilter E W C regs r pc_a dq pc_w :
    mem_access_quarantined W C regs r pc_a dq pc_w -∗
    regs[th] regs -∗
    |~{E}~>
    ∃ ws,
      ⌜regs !! r = Some ws⌝ ∗
      regs[th] (<[r := lclear_tag ws]> regs) ∗
      pc_a ↦ₐ{dq} pc_w ∗
      ▷ (pc_a ↦ₐ{dq} pc_w -∗ world_interp W C).
  Proof.
    iIntros "Hquarantined Hmap".
    iDestruct "Hquarantined" as (ι ws Hws Hauth Hι) "(#Hq & Ha & Hclose)".
    iDestruct (big_sepM_insert_acc with "Hmap") as "[Hr Hmap]"; first exact Hws.
    iMod (reg_refilter with "Hq Hr") as "Hr"; [done..|].
    iModIntro. iExists ws. iFrame "Ha Hclose". iSplit; first done. by iApply "Hmap".
  Qed.

  (** *** The cases *)

  (** A load through a quarantined authority: the load faults on the cleared tag
      of [r], with the PC's cell alone. *)
  Lemma load_case_quarantined W C regs p g b e a w i dst r imm ws dq :
    load_member exec_opt griotte_load_filter i dst r imm →
    not_switch_instr i →
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap p g b e a) →
    (∀ x : RegName, is_Some (regs !! x)) →
    regs !! r = Some ws →
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    PC ↦ₚ[th] Cap p g b e a -∗
    regs[th] (<[r := lclear_tag ws]> regs) -∗
    a ↦ₐ{dq} w -∗
    ▷ (a ↦ₐ{dq} w -∗ world_interp W C) -∗
    WP Instr Executable @core[th] {{ ftlr_contract_intro_post W C }}.
  Proof.
    iIntros (Hmember Hsw Hi HcorrectPC Hsome Hws) "#Hreg HPC Hmap Ha Hclose".
    iApply (wp_load_step (CL := link_core) ⊤ p g b e a None w i dst r imm
              griotte_load_filter load_exact (<[a := w]> ∅) (<[a := dq]> ∅) with "[$HPC Ha $Hmap]");
      [done | done | apply load_choice_exact | exact (Hsw _) | done
      | apply elem_of_dom; rewrite lookup_insert_is_Some'; by left
      | right; apply elem_of_dom; rewrite lookup_insert_is_Some'; right; apply Hsome
      | by simplify_map_eq | by rewrite !dom_insert_L
      | eapply mem_access_footprint_untagged; [apply lookup_insert_eq | by rewrite lw_lclear_tag get_tag_clear_tag]
      | by rewrite -pointsto_prod_merge_1 |].
    iIntros "!>" (lpc' regs' retv) "(%Hres & HPC & Hmem & Hmap)".
    destruct Hres as [ (-> & -> & ->) | (p1 & g1 & b1 & e1 & a1 & ea1 & Hacc1 & _) ].
    - rewrite -pointsto_prod_merge_1.
      iApply (ftlr_close_quarantined with "HPC Hmap Hreg [Hclose Hmem]"); [done | done |].
      iNext. by iApply "Hclose".
    - exfalso. eapply reg_allows_mem_access_untagged; [apply lookup_insert_eq | | exact Hacc1].
      by rewrite lw_lclear_tag get_tag_clear_tag.
  Qed.

  (** A load of the memory of the access: the loaded word is safe by
      the access condition of its cell, or is an integer from a device. *)
  Lemma load_case_mem W C regs p g b e a w i dst r imm :
    load_member exec_opt griotte_load_filter i dst r imm →
    not_switch_instr i →
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap p g b e a) →
    (∀ x : RegName, is_Some (regs !! x)) →
    ftlr_IH -∗
    interp W C (Cap p g b e a) -∗
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    PC ↦ₚ[th] Cap p g b e a -∗
    regs[th] regs -∗
    mem_access_map MemAccessRead W C regs r imm a w -∗
    WP Instr Executable @core[th] {{ ftlr_contract_intro_post W C }}.
  Proof.
    iIntros (Hmember Hsw Hi HcorrectPC Hsome) "#IH #Hinv_interp #Hreg HPC Hmap Hacc".
    iDestruct "Hacc" as (mem dfracs Hdom Hpc Hok) "(Hmem & #Hval & Hclose)".
    iApply (wp_load_step (CL := link_core) ⊤ p g b e a None w i dst r imm
              griotte_load_filter load_exact mem dfracs with "[$HPC $Hmem $Hmap]");
      [done | done | apply load_choice_exact | exact (Hsw _) | done | apply elem_of_dom, Hsome
      | right; apply elem_of_dom, Hsome | exact Hpc | exact Hdom | exact Hok |].
    iIntros "!>" (lpc' regs' retv) "(%Hres & HPC & Hmem & Hmap)".
    destruct Hres as [ (-> & -> & ->)
                     | (p1 & g1 & b1 & e1 & a1 & ea1 & Hacc1 & -> & Hinc & Hcases) ].
    - (* A fault. *)
      iApply (ftlr_contract_intro_post_fault with "HPC Hmap [Hclose Hmem]"); first done.
      iNext. iFrame "Hreg". iApply ("Hclose" with "Hmem"). by iLeft.
    - (* A read of a cell or of a device. *)
      iApply (ftlr_contract_intro_post_next with "IH Hinv_interp HPC Hmap [Hclose Hmem]");
        [destruct Hcases as [ (lv & v' & _ & _ & ->) | (_ & w' & _ & ->) ]; by apply full_map_linsert
        | done | exact Hinc |].
      iNext. iSplit; last (iApply ("Hclose" with "Hmem"); by iLeft).
      destruct Hcases as [ (lv & v' & Hlv & Hpost & ->) | (_ & w' & Ht & ->) ];
        iApply (interp_linsert with "Hreg"); iIntros (_).
      + rewrite /load_exact in Hpost. subst v'.
        iApply ("Hval" $! _ _ _ _ _ _ _ eq_refl Hacc1 Hlv).
      + by iApply interp_untagged.
  Qed.

  (** A load: a quarantined authority ([load_case_quarantined]) or the memory of the
      access ([load_case_mem]). *)
  Lemma load_case m W C regs p p' g b e a w i ρ P dst r imm :
    load_member exec_opt griotte_load_filter i dst r imm →
    not_switch_instr i →
    ftlr_contract m W C regs p p' g b e a w i ρ P.
  Proof.
    intros Hmember Hsw. apply ftlr_contract_intro.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@". iClear "Hrcond Hwcond".
    iMod (mem_access_open_intro MemAccessRead r imm Hpers Hp Hbae
           with "Hthread Hreg Hinv_interp Hinva WorldRes Hworld_interp") as "[Hquarantined | Hacc]".
    - iMod (mem_access_quarantined_refilter with "Hquarantined Hmap") as (ws Hws) "(Hmap & Ha & Hclose)".
      by iApply (load_case_quarantined with "Hreg HPC Hmap Ha Hclose").
    - by iApply (load_case_mem with "IH Hinv_interp Hreg HPC Hmap Hacc").
  Qed.

  (** A store through a quarantined authority: the store faults on the cleared
      tag of [r], with the PC's cell alone. *)
  Lemma store_case_quarantined W C regs p g b e a w i r imm ws dq :
    store_member exec_opt store_source i r imm →
    not_switch_instr i →
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap p g b e a) →
    (∀ x : RegName, is_Some (regs !! x)) →
    regs !! r = Some ws →
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    PC ↦ₚ[th] Cap p g b e a -∗
    regs[th] (<[r := lclear_tag ws]> regs) -∗
    a ↦ₐ{dq} w -∗
    ▷ (a ↦ₐ{dq} w -∗ world_interp W C) -∗
    WP Instr Executable @core[th] {{ ftlr_contract_intro_post W C }}.
  Proof.
    iIntros (Hmember Hsw Hi HcorrectPC Hsome Hws) "#Hreg HPC Hmap Ha Hclose".
    iDestruct (interp_refilter with "Hreg") as "#Hreg_refiltered"; first exact Hws.
    iAssert (⌜∀ r' v, <[r := lclear_tag ws]> regs !! r' = Some v → no_prov_disjoint_from_heap v⌝)%I
      as %Hnoid.
    { iIntros (r' v Hv). iApply (interp_no_prov_disjoint_from_heap W C). by iApply "Hreg_refiltered". }
    iApply (wp_store_step (CL := link_core) ⊤ p g b e a None w i r imm store_source
              (lstore_source (<[r := lclear_tag ws]> regs)) (<[a := w]> ∅) (<[a := dq]> ∅)
              with "[$HPC Ha $Hmap]");
      [done | done | exact (Hsw _) | done
      | apply elem_of_dom; rewrite lookup_insert_is_Some'; by left
      | apply store_source_lift; [intros r'; rewrite lookup_insert_is_Some'; by right | done]
      | by simplify_map_eq | by rewrite !dom_insert_L
      | eapply mem_access_footprint_untagged; [apply lookup_insert_eq | by rewrite lw_lclear_tag get_tag_clear_tag]
      | by rewrite -pointsto_prod_merge_1 |].
    iIntros "!>" (lpc' mem' retv) "(%Hres & HPC & Hmem & Hmap)".
    destruct Hres as [ (-> & -> & ->) | (p1 & g1 & b1 & e1 & a1 & ea1 & Hacc1 & _) ].
    - rewrite -pointsto_prod_merge_1.
      iApply (ftlr_close_quarantined with "HPC Hmap Hreg [Hclose Hmem]"); [done | done |].
      iNext. by iApply "Hclose".
    - exfalso. eapply reg_allows_mem_access_untagged; [apply lookup_insert_eq | | exact Hacc1].
      by rewrite lw_lclear_tag get_tag_clear_tag.
  Qed.

  (** A store to the memory of the access: the stored word is below
      a register, hence safe. *)
  Lemma store_case_mem W C regs p g b e a w i r imm :
    store_member exec_opt store_source i r imm →
    not_switch_instr i →
    decodeInstrW w.(lw) = i →
    isCorrectPC (Cap p g b e a) →
    (∀ x : RegName, is_Some (regs !! x)) →
    ftlr_IH -∗
    thread_in th C -∗
    interp W C (Cap p g b e a) -∗
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    PC ↦ₚ[th] Cap p g b e a -∗
    regs[th] regs -∗
    mem_access_map MemAccessWrite W C regs r imm a w -∗
    WP Instr Executable @core[th] {{ ftlr_contract_intro_post W C }}.
  Proof.
    iIntros (Hmember Hsw Hi HcorrectPC Hsome) "#IH #Hthread #Hinv_interp #Hreg HPC Hmap Hacc".
    iDestruct "Hacc" as (mem dfracs Hdom Hpc Hok) "(Hmem & _ & Hclose)".
    iAssert (⌜∀ r' v, regs !! r' = Some v → no_prov_disjoint_from_heap v⌝)%I as %Hnoid.
    { iIntros (r' v Hv). iApply (interp_no_prov_disjoint_from_heap W C). by iApply "Hreg". }
    iApply (wp_store_step (CL := link_core) ⊤ p g b e a None w i r imm store_source
              (lstore_source regs) mem dfracs with "[$HPC $Hmem $Hmap]");
      [done | done | exact (Hsw _) | done | apply elem_of_dom, Hsome
      | by apply store_source_lift | exact Hpc | exact Hdom | exact Hok |].
    iIntros "!>" (lpc' mem' retv) "(%Hres & HPC & Hmem & Hmap)".
    destruct Hres as [ (-> & -> & ->)
                     | (p1 & g1 & b1 & e1 & a1 & ea1 & Hacc1 & -> & Hinc & Hcases) ].
    - (* A fault. *)
      iApply (ftlr_contract_intro_post_fault with "HPC Hmap [Hclose Hmem]"); first done.
      iNext. iFrame "Hreg". iApply ("Hclose" with "Hmem"). by iLeft.
    - (* A write to a cell or to a device. *)
      iApply (ftlr_contract_intro_post_next with "IH Hinv_interp HPC Hmap [Hclose Hmem]");
        [done | done | exact Hinc |].
      iNext. iFrame "Hreg". iApply ("Hclose" with "Hmem").
      destruct Hcases as [ (v & Hstore_source & Hin & ->) | (_ & ->) ]; last by iLeft.
      iRight. iExists p1, g1, b1, e1, a1, ea1, v. do 4 (iSplit; first done).
      by iApply (lstore_source_sound with "IH Hthread Hreg").
  Qed.

  (** A store: a quarantined authority ([store_case_quarantined]) or the memory of the
      access ([store_case_mem]). *)
  Lemma store_case m W C regs p p' g b e a w i ρ P r imm :
    store_member exec_opt store_source i r imm →
    not_switch_instr i →
    ftlr_contract m W C regs p p' g b e a w i ρ P.
  Proof.
    intros Hmember Hsw. apply ftlr_contract_intro.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@". iClear "Hrcond Hwcond".
    iMod (mem_access_open_intro MemAccessWrite r imm Hpers Hp Hbae
           with "Hthread Hreg Hinv_interp Hinva WorldRes Hworld_interp") as "[Hquarantined | Hacc]".
    - iMod (mem_access_quarantined_refilter with "Hquarantined Hmap") as (ws Hws) "(Hmap & Ha & Hclose)".
      by iApply (store_case_quarantined with "Hreg HPC Hmap Ha Hclose").
    - by iApply (store_case_mem with "IH Hthread Hinv_interp Hreg HPC Hmap Hacc").
  Qed.

  (** A memory instruction: a load ([load_case]) or a store
      ([store_case]). *)
  Lemma mem_case m W C regs p p' g b e a w i ρ P :
    mem_member exec_opt i →
    not_switch_instr i →
    ftlr_contract m W C regs p p' g b e a w i ρ P.
  Proof.
    intros [ (dst & r & imm & Hload) | (r & imm & Hstore) ] Hsw.
    - by eapply load_case.
    - by eapply store_case.
  Qed.

End ftlr_mem_access.
