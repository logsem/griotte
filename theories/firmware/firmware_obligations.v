From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import assert_spec.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_base_interp.
From griotte Require Import stack_world_resources mkregion_helpers disjoint_regions_tactics.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common_obligations.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import locks firmware_ok firmware_adequacy_obligations.
From griotte Require Import switcher_spec_return.
(* Imported last: the fields of the image records shadow the fields of the
   layout records of [compartment_layout] and of [switcherLayout]. *)
From griotte Require Import image firmware.

(** * The obligations of a firmware, over prepared resources

    [fw_obligations_of_pinned] ([firmware_thread_obligations.v]) proves
    [fw_obligations Σ fw] for a firmware with one thread from an obligation
    over the resources [fw_init_res fw img C_sched]: those of
    [fw_shared_res] and [fw_thread_res], with every compartment but the
    scheduler's initialised ([fw_cmpt_res_user]) and the first thread starting
    at the code of its compartment. A case study proves its obligations as
    follows.

    - [apply (fw_obligations_of_pinned Σ fw Sched); [reflexivity |
      reflexivity |] ], [Sched] the scheduler's logical compartment: the
      export the first thread starts at is at the end of the imports of its
      compartment ([fw_entry_at_code]), and the firmware has one thread.
    - Per compartment at position [i] of the firmware, [fw_cmpt_ok_at Hok i
      eq_refl] gives its contents (reduced with [cbv] as the predicate is)
      and [fw_cmpt_layout_at Hok i eq_refl] its layout [Hc], hence its record
      [layout_cmpt_of _ Hc]. The layouts the specifications take are
      [fw_switcher_layout img] (well formed by [fw_switcher_layout_wf_of
      Hok]), [fw_assert_layout img], and the switcher record with the stacks
      of the first thread [fw_switcher_cmpt Hok]; [fw_cmpts_disjoint_at] and
      [fw_switcher_cmpt_disjoint_at] relate them. [fw_fold_cmpt] writes the
      fields of an image compartment as those of its record.
    - [iNamed] on [fw_init_res] gives the invariants of the switcher and of
      the assert library, the compartments ["Hcmpts"] (a list, destructed
      after [cbv] of the firmware; the scheduler's entry is [emp]), the
      registers in the form of the main specifications ([cra] the
      switcher's return sentry; cleared registers: [fw_cleared_regs_dom]
      and [fw_cleared_regs_lookup]), the stack and the fact that it holds the
      minimum stack size of the entry of the first thread plus the reserved
      space (["%Hstack_min"]), the worlds of the logical compartments but
      [Sched] and the sealing types of the firmware.
    - A compartment splits into its imports, code and globals
      ([fw_cmpt_mem_res]; [fw_cmpt_mem_persist] for trusted code run in
      place), its static sealed objects ([fw_cmpt_static_res]) and the
      persistent part ([fw_cmpt_pers_res]): its export table and its sealed
      export entries.
    - The case-specific setup comes next: ghost state, sealing predicates of
      the sealing types of the firmware, invariants of trusted compartments,
      secrets of an adversary (its static sealed objects) moved into an
      invariant, the sealing of trusted exports in the world of an
      adversary.
    - Each untrusted compartment is then closed in the world of its logical
      compartment by [fw_close_adv_world] (the stack temporary: the
      adversary may keep it) or [fw_close_adv_world_revoked] (the stack
      revoked: the trusted code keeps it). The case study proves the safety
      of its imports, one [fw_import_safe] per import of the firmware
      ([fw_switcher_call_safe] for the switcher call); the lemmas return
      the closed world and the safety of the adversary's exports.
    - The main specification applies to what remains. *)

(** ** Facts about the compartments of a firmware, by position *)
Section obligation_facts.
  Context `{MP : MachineParameters}.

  Lemma fw_cmpt_ok_at fw img σ i fc :
    firmware_ok fw img σ → fw_cmpts fw !! i = Some fc → cmpt_ok fw img fc.
  Proof.
    intros (Hok & _) Hi. apply big_and_fw_map in Hok.
    by eapply Forall_lookup_1.
  Qed.

  Lemma fw_cmpt_layout_at fw img σ i fc :
    firmware_ok fw img σ →
    fw_cmpts fw !! i = Some fc →
    img_cmpt_layout (cmpt_of img (fc_name fc)).
  Proof.
    intros (_ & _ & _ & Hwf) Hi. eapply img_wf_cmpt_layout; first done.
    by eapply list_elem_of_lookup_2.
  Qed.

  (** The layouts of the trusted stack and of the stack of the first
      thread, with the switcher. *)
  Lemma fw_switcher_layouts fw img σ :
    firmware_ok fw img σ →
    trusted_stack_layout (b_trusted_stack (thread_of img 0)) (e_trusted_stack (thread_of img 0))
      (b_hazard (thread_of img 0)) (e_hazard (thread_of img 0))
      (fw_tstack_content fw img 0 (fw_thread0 fw)) ∧
    img_switcher_layout (img_sw img) (thread_of img 0)
      (replicate (ft_stack_size (fw_thread0 fw)) (WInt 0)).
  Proof.
    intros Hok. pose proof Hok as (_ & _ & _ & Hwf).
    pose proof (firmware_ok_thread0 _ _ _ Hok) as H0.
    split; [exact (img_wf_trusted_stack_layout _ _ _ _ H0 Hwf)
           | exact (img_wf_switcher_layout _ _ _ _ H0 Hwf)].
  Qed.

  Lemma fw_cmpts_disjoint_at fw img σ i j fci fcj
      (Hci : img_cmpt_layout (cmpt_of img (fc_name fci)))
      (Hcj : img_cmpt_layout (cmpt_of img (fc_name fcj))) :
    firmware_ok fw img σ →
    i ≠ j →
    fw_cmpts fw !! i = Some fci →
    fw_cmpts fw !! j = Some fcj →
    layout_cmpt_of _ Hci ## layout_cmpt_of _ Hcj.
  Proof. intros (_ & _ & _ & Hwf). by apply img_wf_cmpts_disjoint. Qed.

  (** The layouts of the program logic for the switcher, with the stacks
      of the first thread, and for the assert library of an image, as the
      specifications take them. *)
  Definition fw_assert_layout (img : fw_image) : assertLayout :=
    mkAssertLayout (b_assert (img_asrt img)) (e_assert (img_asrt img)) (flag_assert (img_asrt img)).

  (** The layout of the lock library of an image. *)
  Definition fw_locks_layout (img : fw_image) : locksLayout :=
    mkLocksLayout (b_locks (img_lck img)) (e_locks (img_lck img)).

  Lemma fw_switcher_layout_wf_of fw img σ :
    firmware_ok fw img σ → @switcherLayoutWf MP (fw_switcher_layout img).
  Proof.
    intros Hok. pose proof Hok as (_ & _ & _ & Hwf).
    exact (fw_switcher_layout_wf fw img Hwf (firmware_ok_thread0 _ _ _ Hok)).
  Qed.

  Definition fw_switcher_cmpt fw img σ (Hok : firmware_ok fw img σ) : cmptSwitcher :=
    layout_switcher_of (img_sw img) (thread_of img 0) _ _
      (proj1 (fw_switcher_layouts fw img σ Hok)) (proj2 (fw_switcher_layouts fw img σ Hok)).

  Lemma fw_switcher_cmpt_disjoint_at fw img σ (Hok : firmware_ok fw img σ) i fc
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) :
    fw_cmpts fw !! i = Some fc →
    switcher_cmpt_disjoint (layout_cmpt_of _ Hc) (fw_switcher_cmpt fw img σ Hok).
  Proof.
    intros Hi. pose proof Hok as (_ & _ & _ & Hwf).
    destruct (firmware_ok_threads_inv _ _ _ Hok) as ([fts Hthreads] & _).
    eapply img_wf_switcher_cmpt_disjoint; [exact Hthreads | done |].
    by eapply list_elem_of_lookup_2.
  Qed.

  (** The conditions on the machine of a firmware with heap roots, for its
      allocator. *)
  Lemma fw_heap_machine fw img σ :
    firmware_ok fw img σ →
    fw_heap_roots fw ≠ [] →
    (∀ a, heap_to_shadow a = translate_region heap_b heap_e shadow_b a) ∧
    (revoker_addr < revoker_addr ^+ 1)%a.
  Proof. intros (_ & _ & _ & Hwf). exact (img_wf_heap_machine _ _ Hwf). Qed.

  Lemma fw_cleared_regs_dom : dom fw_cleared_regs = all_registers_s ∖ {[cgp; cra; csp]}.
  Proof. by rewrite /fw_cleared_regs dom_gset_to_gmap. Qed.

  Lemma fw_cleared_regs_lookup r :
    r ∈ dom fw_cleared_regs → fw_cleared_regs !! r = Some (lword_of_word (WInt 0)).
  Proof.
    rewrite fw_cleared_regs_dom. intros Hr.
    by rewrite /fw_cleared_regs lookup_gset_to_gmap option_guard_True.
  Qed.

  (** The image's return sentry is the one of the switcher's layout. *)
  Lemma fw_thread_cra_eq img :
    fw_thread_cra img = thread_return_sentry (swlayout := fw_switcher_layout img).
  Proof. reflexivity. Qed.

  (** The stack of the first thread holds the minimum stack size of the
      export it starts at plus the reserved space. *)
  Lemma fw_entry_min_stack_ok fw img σ :
    firmware_ok fw img σ →
    (b_stack (thread_of img 0) + Z.of_nat (fw_entry_min_stack fw 0) + StackEntry_reserved_space <=
       e_stack (thread_of img 0))%Z.
  Proof.
    intros Hok. pose proof Hok as (_ & _ & _ & Hwf).
    destruct (firmware_ok_threads_inv _ _ _ Hok) as ([fts Hthreads] & _).
    pose proof Hwf as (_ & _ & _ & Hthreads_wf & _).
    rewrite Hthreads in Hthreads_wf.
    apply big_and_cons in Hthreads_wf as [Hthread0 _].
    apply thread_wf_min_stack. by rewrite fw_thread_of_0.
  Qed.

  (** The first thread starts, in a trusted compartment, at the end of its
      imports. *)
  Definition fw_entry_at_code (fw : firmware) : Prop :=
    match fc_body (fw_entry_fc fw 0) with
    | TrustedBody _ => fw_entry_offset fw 0 = length (fc_imports (fw_entry_fc fw 0))
    | UntrustedBody _ | SchedulerBody _ => False
    end.

  Lemma fw_imap_const {A B} (g : A → B) (k : nat) (l : list A) :
    fw_imap_from (λ _ x, g x) k l = g <$> l.
  Proof. revert k. induction l as [|x l IH]; intros k; cbn; [done | by rewrite IH]. Qed.

  Lemma cmpt_ok_imports fw img fc :
    cmpt_ok fw img fc →
    let c := cmpt_of img (fc_name fc) in
    cmpt_imports c = fw_word_of fw img (fc_static_sealed fc) c <$> fc_imports fc.
  Proof. intros (_ & Himports & _)%cmpt_ok_inv. by rewrite /= Himports /fw_imap fw_imap_const. Qed.

  Lemma fw_entry_pc_code fw img σ :
    fw_entry_at_code fw →
    firmware_ok fw img σ →
    let m := fw_entry_cmpt fw img 0 in
    fw_entry_pc fw img 0 = Cap RX Global (cmpt_b_pcc m) (cmpt_e_pcc m) (cmpt_a_code m).
  Proof.
    intros Hentry Hok m. pose proof Hok as (Hcmpts & _ & _ & Hwf).
    destruct (firmware_ok_threads_inv _ _ _ Hok) as ([fts Hthreads] & Hentries).
    destruct (Hentries 0 (fw_thread0 fw)) as [Hin Hname]; first by rewrite Hthreads.
    pose proof (img_wf_cmpt_layout _ _ _ Hwf Hin) as Hc.
    apply big_and_fw_map in Hcmpts. rewrite Forall_forall in Hcmpts.
    pose proof (cmpt_ok_imports _ _ _ (Hcmpts _ Hin)) as Himports.
    pose proof (icl_import_size _ Hc) as Hsize.
    rewrite /m /fw_entry_pc. rewrite /fw_entry_at_code in Hentry.
    destruct (fc_body (fw_entry_fc fw 0)) as [tb| |]; [|done..].
    rewrite Himports length_fmap -Hentry Hname -fw_thread_of_0 in Hsize.
    rewrite /fw_entry_cmpt addr_off_eq. cbv zeta.
    do 2 f_equal. solve_addr.
  Qed.

  Lemma hole_exports_spec (c : img_cmpt) (ns : list nat) (k : list Word → Prop) :
    hole_exports c ns k →
    ∃ ps : list (nat * nat),
      length ps = length ns ∧
      Forall (λ p, (Z.of_nat p.1 < cmpt_e_pcc c - cmpt_b_pcc c)%Z) ps ∧
      k (zip_with (λ p n, export_word (MkFwExport "" p.1 n p.2 InterruptEnabled)) ps ns).
  Proof.
    revert k. induction ns as [|n ns IH]; intros k Hk; cbn in Hk.
    - by exists [].
    - destruct Hk as (off & minstk & Hoff & Hk). destruct (IH _ Hk) as (ps & Hlen & Hps & Hws).
      exists ((off, minstk) :: ps). split_and!; [by rewrite /= Hlen | by constructor | exact Hws].
  Qed.
End obligation_facts.

(** The layouts of the trusted stack and of the stack of the thread [k],
    with the switcher. *)
Lemma fw_switcher_layouts_at `{MP : MachineParameters} fw img σ k ft :
  firmware_ok fw img σ →
  fw_threads fw !! k = Some ft →
  trusted_stack_layout (b_trusted_stack (thread_of img k)) (e_trusted_stack (thread_of img k))
    (b_hazard (thread_of img k)) (e_hazard (thread_of img k))
    (fw_tstack_content fw img k ft) ∧
  img_switcher_layout (img_sw img) (thread_of img k) (replicate (ft_stack_size ft) (WInt 0)).
Proof.
  intros (_ & _ & _ & Hwf) Hk.
  split; [exact (img_wf_trusted_stack_layout _ _ _ _ Hk Hwf)
         | exact (img_wf_switcher_layout _ _ _ _ Hk Hwf)].
Qed.

(** The switcher record with the stacks of the thread [k]. *)
Definition fw_switcher_cmpt_at `{MP : MachineParameters} fw img σ k ft
    (Hok : firmware_ok fw img σ) (Hk : fw_threads fw !! k = Some ft) : cmptSwitcher :=
  layout_switcher_of (img_sw img) (thread_of img k) _ _
    (proj1 (fw_switcher_layouts_at fw img σ k ft Hok Hk))
    (proj2 (fw_switcher_layouts_at fw img σ k ft Hok Hk)).

Lemma fw_switcher_cmpt_disjoint_thread `{MP : MachineParameters} fw img σ k ft
    (Hok : firmware_ok fw img σ) (Hk : fw_threads fw !! k = Some ft) i fc
    (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) :
  fw_cmpts fw !! i = Some fc →
  switcher_cmpt_disjoint (layout_cmpt_of _ Hc) (fw_switcher_cmpt_at fw img σ k ft Hok Hk).
Proof.
  intros Hi. pose proof Hok as (_ & _ & _ & Hwf).
  eapply img_wf_switcher_cmpt_disjoint_at; [exact Hk | done |].
  by eapply list_elem_of_lookup_2.
Qed.

(** [fw_fold_cmpt X], for a local definition [X := layout_cmpt_of c Hc],
    writes the fields of the image record [c] as the fields of [X], in the
    hypotheses and in the goal (with the proof-mode context). *)
Ltac fw_fold_cmpt X :=
  let c := lazymatch eval cbv delta [X] in X with layout_cmpt_of ?c _ => c end in
  change (image.cmpt_b_pcc c) with (compartment_layout.cmpt_b_pcc X) in *;
  change (image.cmpt_a_code c) with (compartment_layout.cmpt_a_code X) in *;
  change (image.cmpt_e_pcc c) with (compartment_layout.cmpt_e_pcc X) in *;
  change (image.cmpt_b_cgp c) with (compartment_layout.cmpt_b_cgp X) in *;
  change (image.cmpt_e_cgp c) with (compartment_layout.cmpt_e_cgp X) in *;
  change (image.cmpt_b_static_sealed c)
    with (compartment_layout.cmpt_b_static_sealed X) in *;
  change (image.cmpt_e_static_sealed c)
    with (compartment_layout.cmpt_e_static_sealed X) in *;
  change (image.cmpt_exp_tbl_pcc c) with (compartment_layout.cmpt_exp_tbl_pcc X) in *;
  change (image.cmpt_exp_tbl_cgp c) with (compartment_layout.cmpt_exp_tbl_cgp X) in *;
  change (image.cmpt_exp_tbl_entries_start c)
    with (compartment_layout.cmpt_exp_tbl_entries_start X) in *;
  change (image.cmpt_exp_tbl_entries_end c)
    with (compartment_layout.cmpt_exp_tbl_entries_end X) in *;
  change (image.cmpt_imports c) with (compartment_layout.cmpt_imports X) in *;
  change (image.cmpt_code c) with (compartment_layout.cmpt_code X) in *;
  change (image.cmpt_data c) with (compartment_layout.cmpt_data X) in *;
  change (image.cmpt_static_sealed c) with (compartment_layout.cmpt_static_sealed X) in *;
  change (image.cmpt_exp_tbl_handler c) with (compartment_layout.cmpt_exp_tbl_handler X) in *;
  change (image.cmpt_exp_tbl_handler_stackless c)
    with (compartment_layout.cmpt_exp_tbl_handler_stackless X) in *;
  change (image.cmpt_exp_tbl_entries c)
    with (compartment_layout.cmpt_exp_tbl_entries X) in *.

(** ** The prepared resources *)
Section prepared.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** The imports, the code and the globals of a compartment. *)
  Definition fw_cmpt_mem_res (c : img_cmpt) : iProp Σ :=
    [[ cmpt_b_pcc c, cmpt_a_code c ]] ↦ₐ [[ lword_of_word <$> cmpt_imports c ]] ∗
    [[ cmpt_a_code c, cmpt_e_pcc c ]] ↦ₐ [[ lword_of_word <$> cmpt_code c ]] ∗
    [[ cmpt_b_cgp c, cmpt_e_cgp c ]] ↦ₐ [[ lword_of_word <$> cmpt_data c ]].

  (** The static sealed objects of a compartment. *)
  Definition fw_cmpt_static_res (c : img_cmpt) : iProp Σ :=
    [[ cmpt_b_static_sealed c, cmpt_e_static_sealed c ]] ↦ₐ
      [[ lword_of_word <$> cmpt_static_sealed c ]].

  (** The error handler offsets of the compartment [fc], at the base [b] of
      its export table: the declared ones for a trusted compartment,
      arbitrary for an untrusted one. *)
  Definition fw_handler_res (fc : fw_cmpt) (b : Addr) : iProp Σ :=
    match fc_body fc with
    | TrustedBody tb =>
        match tb_error_handler tb, tb_error_handler_stackless tb with
        | None, None => no_handler b
        | eh, ehs => b ↦ₑ□{stackful} handler_word eh ∗ b ↦ₑ□{stackless} handler_word ehs
        end
    | UntrustedBody _ => ∃ eh ehs : Z, b ↦ₑ□{stackful} eh ∗ b ↦ₑ□{stackless} ehs
    | SchedulerBody _ =>
        b ↦ₑ□{stackful} ExportTable_no_handler ∗ b ↦ₑ□{stackless} ExportTable_no_handler
    end.

  #[global] Instance fw_handler_res_persistent fc b : Persistent (fw_handler_res fc b).
  Proof. rewrite /fw_handler_res. repeat case_match; apply _. Qed.

  (** The entries [ws] of the export table at [b], from [s] to [e], each at
      its offset. *)
  Lemma exp_tbl_entries_offsets_from (b s e : Addr) (j : nat) (ws : list Word) :
    (b + ExportTable_offset_entry j)%a = Some s →
    (s + length ws)%a = Some e →
    ([∗ list] a;v ∈ finz.seq_between s e; ws, a ↦ₐ□ lword_of_word v) ⊣⊢
    [∗ list] k ↦ v ∈ ws, (b ^+ ExportTable_offset_entry (j + k)) ↦ₐ□ lword_of_word v.
  Proof.
    revert s j. induction ws as [|w ws IH]; intros s j Hs He.
    - cbn in He. rewrite finz_seq_between_empty; [done | solve_addr].
    - cbn in He. rewrite finz_seq_between_cons; last solve_addr.
      rewrite big_sepL2_cons big_sepL_cons.
      rewrite (IH (s ^+ 1) (S j)); [| solve_addr | solve_addr].
      rewrite Nat.add_0_r.
      replace (b ^+ ExportTable_offset_entry j) with s by solve_addr.
      f_equiv. apply big_sepL_proper. intros k v _. by rewrite Nat.add_succ_r.
  Qed.

  Lemma exp_tbl_entries_offsets (b s e : Addr) (ws : list Word) :
    (b + ExportTable_offset_entries)%a = Some s →
    (s + length ws)%a = Some e →
    ([∗ list] a;v ∈ finz.seq_between s e; ws, a ↦ₐ□ lword_of_word v) ⊣⊢
    [∗ list] k ↦ v ∈ ws, (b ^+ ExportTable_offset_entry k) ↦ₐ□ lword_of_word v.
  Proof.
    intros Hs He. rewrite (exp_tbl_entries_offsets_from b s e 0); [done | solve_addr | done].
  Qed.

  (** The export table of a compartment. *)
  Definition fw_cmpt_pers_res (img : fw_image) (fc : fw_cmpt) : iProp Σ :=
    let c := cmpt_of img (fc_name fc) in
    cmpt_exp_tbl_pcc c ↦ₐ□ Cap RX Global (cmpt_b_pcc c) (cmpt_e_pcc c) (cmpt_b_pcc c) ∗
    cmpt_exp_tbl_cgp c ↦ₐ□ Cap RW Global (cmpt_b_cgp c) (cmpt_e_cgp c) (cmpt_b_cgp c) ∗
    fw_handler_res fc (cmpt_exp_tbl_pcc c) ∗
    ([∗ list] k ↦ v ∈ cmpt_exp_tbl_entries c,
       (cmpt_exp_tbl_pcc c ^+ ExportTable_offset_entry k) ↦ₐ□ lword_of_word v).

  #[global] Instance fw_cmpt_pers_res_persistent img fc : Persistent (fw_cmpt_pers_res img fc).
  Proof. rewrite /fw_cmpt_pers_res. apply _. Qed.

  (** The number of arguments of export [k] of a compartment, read off its
      export table, at the address of [cmpt_export_sb]. *)
  Lemma fw_cmpt_pers_res_entry_nargs fw img fc k n :
    let c := cmpt_of img (fc_name fc) in
    cmpt_ok fw img fc →
    fc_export_nargs fc !! k = Some n →
    n ≤ 7 →
    fw_cmpt_pers_res img fc ⊢ (cmpt_exp_tbl_pcc c ^+ ExportTable_offset_entry k) ↦ₑ□{nargs} n.
  Proof.
    intros c Hok Hk Hn.
    assert (∃ ie (m off : nat),
               cmpt_exp_tbl_entries c !! k = Some (WInt (encode_entry_point ie n m off)))
      as (ie & m & off & Hentry).
    { destruct (cmpt_ok_inv _ _ _ Hok) as (_ & _ & _ & Hbody).
      rewrite /fc_export_nargs in Hk.
      destruct (fc_body fc) as [tb|ub|sb]; last done.
      - destruct Hbody as (_ & _ & _ & Hexp).
        rewrite fw_map_eq list_lookup_fmap in Hk.
        destruct (tb_exports tb !! k) as [e|] eqn:He; simplify_eq/=.
        rewrite /c Hexp /fw_imap fw_imap_const list_lookup_fmap He /=.
        by eexists _, _, _.
      - destruct Hbody as (_ & _ & _ & Hexp). rewrite /note in Hexp.
        destruct (hole_exports_spec _ _ _ Hexp) as (ps & Hlen & _ & Hws).
        destruct (lookup_lt_is_Some_2 ps k) as [p Hp].
        { rewrite Hlen. by eapply lookup_lt_Some. }
        rewrite /c Hws lookup_zip_with Hp Hk /=.
        by eexists _, _, _. }
    iIntros "(_ & _ & _ & Hetbl)".
    iDestruct (big_sepL_lookup with "Hetbl") as "Ha"; first exact Hentry.
    by iApply entry_nargs_intro.
  Qed.

  (** The number of arguments of export [k] of a compartment, at its sealable
      [cmpt_export_sb]. *)
  Lemma fw_cmpt_pers_res_export_nargs fw img fc k n :
    cmpt_ok fw img fc →
    fc_export_nargs fc !! k = Some n →
    n ≤ 7 →
    fw_cmpt_pers_res img fc ⊢ cmpt_export_sb (cmpt_of img (fc_name fc)) k ↦ₑ□{nargs} n.
  Proof.
    iIntros (Hok Hk Hn) "Hres".
    iDestruct (fw_cmpt_pers_res_entry_nargs with "Hres") as "Ha"; [done..|].
    by iApply entry_nargs_sb_intro.
  Qed.

  (** A compartment, initialised. *)
  Definition fw_cmpt_res (img : fw_image) (fc : fw_cmpt) : iProp Σ :=
    let c := cmpt_of img (fc_name fc) in
    fw_cmpt_mem_res c ∗ fw_cmpt_static_res c ∗ fw_cmpt_pers_res img fc.

  (** The memory of a compartment, initialised: the export table becomes
      persistent. *)
  Lemma fw_adv_cmpt_init {E : coPset} img fc (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) :
    let c := cmpt_of img (fc_name fc) in
    let a_eh := (cmpt_exp_tbl_pcc c ^+ ExportTable_offset_errorHandler) in
    let a_ehs := (cmpt_exp_tbl_pcc c ^+ ExportTable_offset_errorHandlerStackless) in
    ([∗ map] a↦w ∈ cmpt_mem img fc, a ↦ₐ lword_of_word w)
    ={E}=∗
    [[ cmpt_b_pcc c, cmpt_a_code c ]] ↦ₐ [[ lword_of_word <$> cmpt_imports c ]] ∗
    [[ cmpt_a_code c, cmpt_e_pcc c ]] ↦ₐ [[ lword_of_word <$> cmpt_code c ]] ∗
    [[ cmpt_b_cgp c, cmpt_e_cgp c ]] ↦ₐ [[ lword_of_word <$> cmpt_data c ]] ∗
    [[ cmpt_b_static_sealed c, cmpt_e_static_sealed c ]] ↦ₐ
      [[ lword_of_word <$> cmpt_static_sealed c ]] ∗
    cmpt_exp_tbl_pcc c ↦ₐ□ Cap RX Global (cmpt_b_pcc c) (cmpt_e_pcc c) (cmpt_b_pcc c) ∗
    cmpt_exp_tbl_cgp c ↦ₐ□ Cap RW Global (cmpt_b_cgp c) (cmpt_e_cgp c) (cmpt_b_cgp c) ∗
    a_eh ↦ₐ□ lword_of_word (cmpt_exp_tbl_handler c) ∗
    a_ehs ↦ₐ□ lword_of_word (cmpt_exp_tbl_handler_stackless c) ∗
    ([∗ list] a;v ∈ finz.seq_between (cmpt_exp_tbl_entries_start c) (cmpt_exp_tbl_entries_end c);
                    cmpt_exp_tbl_entries c, a ↦ₐ□ lword_of_word v).
  Proof.
    intros c a_eh a_ehs. subst a_eh a_ehs.
    rewrite (cmpt_mem_layout img fc Hc). iIntros "Hmem".
    by iMod (initialise_adversary_compartment with "Hmem")
      as "($ & $ & $ & $ & $ & $ & $ & $ & $)".
  Qed.

  (** Every compartment of a firmware, initialised. *)
  Lemma fw_cmpts_init {E : coPset} fw img σ :
    firmware_ok fw img σ →
    ([∗ list] fc ∈ fw_cmpts fw, [∗ map] a↦w ∈ cmpt_mem img fc, a ↦ₐ lword_of_word w)
    ={E}=∗
    [∗ list] fc ∈ fw_cmpts fw, fw_cmpt_res img fc.
  Proof.
    intros Hok. pose proof Hok as (_ & _ & _ & Hwf). iIntros "Hcmpts".
    iApply big_sepL_fupd. iApply (big_sepL_impl with "Hcmpts").
    iIntros "!>" (k fc Hk) "Hmem".
    pose proof (img_wf_cmpt_layout _ _ _ Hwf (list_elem_of_lookup_2 _ _ _ Hk)) as Hc.
    destruct (cmpt_ok_inv _ _ _ (fw_cmpt_ok_at _ _ _ _ _ Hok Hk)) as (_ & _ & _ & Hbody).
    iMod (fw_adv_cmpt_init with "Hmem")
      as "(Himports & Hcode & Hdata & Hstatic & #Hpcc & #Hcgp & #Heh & #Hehs & #Hetbl)";
      first exact Hc.
    iModIntro. rewrite /fw_cmpt_res /fw_cmpt_mem_res /fw_cmpt_pers_res /fw_handler_res.
    iFrame "∗ #".
    iSplitR; last first.
    { iApply (exp_tbl_entries_offsets with "Hetbl").
      - exact (icl_exp_tbl_header_size _ Hc).
      - exact (icl_exp_tbl_entries_size _ Hc). }
    destruct (fc_body fc) as [tb|ub|sb]; rewrite /body_ok /note in Hbody.
    - destruct Hbody as (_ & _ & Hh & _).
      destruct (tb_error_handler tb), (tb_error_handler_stackless tb);
        destruct Hh as [Heh_eq Hehs_eq];
        rewrite Heh_eq Hehs_eq;
        (iSplit; [by iApply handler_stackful_intro | by iApply handler_stackless_intro]).
    - destruct Hbody as (_ & _ & (eh & ehs & Heh_eq & Hehs_eq) & _).
      rewrite Heh_eq Hehs_eq.
      iExists eh, ehs.
      iSplit; [by iApply handler_stackful_intro | by iApply handler_stackless_intro].
    - destruct Hbody as (_ & _ & [Heh_eq Hehs_eq] & _).
      rewrite Heh_eq Hehs_eq.
      iSplit; [by iApply handler_stackful_intro | by iApply handler_stackless_intro].
  Qed.

  (** The imports and the code of a trusted compartment, persistent. *)
  Lemma fw_cmpt_mem_persist {E : coPset} (c : img_cmpt) :
    img_cmpt_layout c →
    fw_cmpt_mem_res c
    ={E}=∗
    [[ cmpt_b_pcc c, cmpt_a_code c ]] ↦ₐ□ [[ lword_of_word <$> cmpt_imports c ]] ∗
    codefrag_pers (cmpt_a_code c) (cmpt_code c) ∗
    [[ cmpt_b_cgp c, cmpt_e_cgp c ]] ↦ₐ [[ lword_of_word <$> cmpt_data c ]].
  Proof.
    intros Hc. iIntros "(Himports & Hcode & $)".
    iMod (region_pointsto_persist with "Himports") as "$".
    iMod (codefrag_persist with "[Hcode]") as "$"; last done.
    rewrite /codefrag.
    replace (cmpt_a_code c ^+ length (cmpt_code c)) with (cmpt_e_pcc c); first done.
    pose proof (icl_code_size _ Hc). solve_addr.
  Qed.
End prepared.

Section cmpt_res_thread_indep.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}.

  (** The resources of a compartment are the same at any two threads. *)
  Lemma fw_cmpt_res_thread_indep (t t' : Thread) (img : fw_image) (fc : fw_cmpt) :
    fw_cmpt_res (th := t) img fc ⊣⊢ fw_cmpt_res (th := t') img fc.
  Proof.
    rewrite /fw_cmpt_res /fw_cmpt_mem_res /fw_cmpt_static_res /fw_cmpt_pers_res.
    rewrite !(region_pointsto_thread_indep t t') !(pointsto_thread_indep t t').
    setoid_rewrite (pointsto_thread_indep t t').
    rewrite /fw_handler_res /no_handler.
    destruct (fc_body fc) as [tb|ub|sb]; [repeat case_match | |];
      try setoid_rewrite (handler_stackful_thread_indep t t');
      try setoid_rewrite (handler_stackless_thread_indep t t'); reflexivity.
  Qed.
End cmpt_res_thread_indep.

(** ** Closing the world of an untrusted compartment *)
Section adversary.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** An import [w] is safe to store in the memory of [C] in every world,
      for the switcher of layout [swlayout]. *)
  Definition fw_import_safe {swlayout : switcherLayout} (C : CmptName) (w : Word) : iProp Σ :=
    safeGC interp_cmpt_threads (C, lword_of_word w).

  (** The imports of a compartment, as the words of the firmware. *)
  Lemma fw_imports_safe_words fw img fc C :
    let swl := fw_switcher_layout img in
    cmpt_ok fw img fc →
    let c := cmpt_of img (fc_name fc) in
    ([∗ list] v ∈ lword_of_word <$> cmpt_imports c, safeGC interp_cmpt_threads (C, v)) ⊣⊢
    [∗ list] w ∈ fc_imports fc, fw_import_safe C (fw_word_of fw img (fc_static_sealed fc) c w).
  Proof.
    intros swl Hok c. rewrite (cmpt_ok_imports _ _ _ Hok) -list_fmap_compose big_sepL_fmap //.
  Qed.

  (** The switcher call sentry is safe to import. *)
  Lemma fw_switcher_call_safe fw img σ c C :
    let swl := fw_switcher_layout img in
    firmware_ok fw img σ →
    switcher_threads (swlayout := swl) C -∗
    fw_import_safe C (fw_word_of fw img [] c ISwitcherCall).
  Proof.
    intros swl Hok.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    iIntros "#Hswitcher_threads".
    rewrite /fw_import_safe /fw_word_of /note.
    iEval (cbn [fst snd]; rewrite /interp_cmpt_threads /=).
    iIntros "!>" (t') "#Ht'".
    iDestruct ("Hswitcher_threads" $! t' with "Ht'") as "[Hswitcher Hswitcher_static]".
    iApply (interp_switcher_call (th := t') (swlayout := fw_switcher_layout img));
      iFrame "Hswitcher Hswitcher_static".
  Qed.

  (** A time-device import is safe in any compartment: it reaches only
      exposed devices. *)
  Lemma fw_time_dev_import_safe fw img ss c C w :
    let swl := fw_switcher_layout img in
    w = IMtime ∨ w = IMtimecmp →
    ⊢ fw_import_safe C (fw_word_of fw img ss c w).
  Proof.
    intros swl Hw.
    assert (∃ a, fw_word_of fw img ss c w = time_dev_cap a ∧
                 (a = mtime_addr ∨ a = mtimecmp_addr)) as (a & -> & Ha).
    { destruct Hw as [-> | ->];
        [exists mtime_addr; split; [reflexivity | by left]
        | exists mtimecmp_addr; split; [reflexivity | by right] ]. }
    rewrite /fw_import_safe /time_dev_cap.
    iEval (cbn [fst snd]; rewrite /interp_cmpt_threads /=).
    iIntros "!>" (t') "_".
    iApply (interp_exposed_mmio_cap (th := t')); [done | done |].
    split_and!; [done | done | done |].
    apply Forall_forall. intros x Hx%elem_of_finz_seq_between.
    assert (x = a) as -> by solve_addr.
    rewrite /is_exposed_mmio_address.
    by rewrite (proj2 (is_time_device_address_spec a) Ha).
  Qed.

  (** The facts about an untrusted compartment [fc] of a firmware that the
      allocation of its world needs: the contents of its code and globals,
      and the sealing predicate of the switcher for its export entries. *)
  Lemma fw_adv_cmpt_facts fw img σ fc ub
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) (W : WORLD) (C : CmptName) :
    let swl := fw_switcher_layout img in
    let c := cmpt_of img (fc_name fc) in
    let C_cmpt := layout_cmpt_of c Hc in
    firmware_ok fw img σ →
    fc ∈ fw_cmpts fw →
    fc_body fc = UntrustedBody ub →
    Forall (λ n, n < 7) (fw_map ue_nargs (ub_exports ub)) →
    Forall is_z (compartment_layout.cmpt_code C_cmpt) ∧
    Forall (is_initial_data_word C_cmpt) (compartment_layout.cmpt_data C_cmpt) ∧
    (switcher_threads (swlayout := swl) C -∗
     fw_cmpt_pers_res img fc -∗
     □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
         interp W C (cmpt_pcc_cap C_cmpt) -∗
         interp W C (cmpt_cgp_cap C_cmpt) -∗
         ot_switcher_prop (swlayout := swl) W C (WSealable (cmpt_export C_cmpt a)))).
  Proof.
    intros swl c C_cmpt Hok Hin Hbody Hnargs.
    pose proof Hok as (Hcmpts_ok & _).
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    apply big_and_fw_map in Hcmpts_ok. rewrite Forall_forall in Hcmpts_ok.
    pose proof (Hcmpts_ok fc Hin) as Hfc_ok.
    destruct (cmpt_ok_inv _ _ _ Hfc_ok) as (_ & _ & _ & Hbody_ok).
    rewrite Hbody in Hbody_ok.
    destruct Hbody_ok as (Hcode & Hdata & _ & Hexps). rewrite /note in Hcode Hdata Hexps.
    remember (fw_map ue_nargs (ub_exports ub)) as ns eqn:Hns.
    destruct (hole_exports_spec _ _ _ Hexps) as (ps & Hlen & Hps & Hentries_eq).
    split; first exact Hcode. split; first exact Hdata.
    iIntros "#Hswitcher #(Hpcc & Hcgp & Hh & Hetbl)".
    rewrite /fw_handler_res Hbody.
    iDestruct "Hh" as (eh ehs) "[Heh Hehs]".
    iApply (adversary_exports_prop W C C_cmpt
              (zip_with (λ p n, (InterruptEnabled, n, p.2, p.1)) ps ns) eh ehs
             with "Hswitcher Hpcc Hcgp Heh Hehs Hetbl").
    - rewrite /= Hentries_eq. clear -Hlen. revert ns Hlen.
      induction ps as [|p ps IH]; intros [|n ns] Hlen; cbn in *; try done.
      by rewrite IH; last lia.
    - clear -Hlen Hnargs. revert ns Hlen Hnargs.
      induction ps as [|p ps IH]; intros [|n ns] Hlen Hnargs; cbn in *; try constructor.
      + apply Forall_cons in Hnargs as [Hn _]. exact Hn.
      + apply Forall_cons in Hnargs as [_ Hnargs]. apply IH; [lia | exact Hnargs].
    - assert (Forall (λ p : nat * nat, is_Some (cmpt_b_pcc c + Z.of_nat p.1)%a) ps) as Hsome.
      { eapply Forall_impl; first exact Hps. intros p Hp. cbn in Hp |- *.
        pose proof (icl_import_size _ Hc). pose proof (icl_code_size _ Hc).
        rewrite /c. destruct (cmpt_b_pcc (cmpt_of img (fc_name fc)) + p.1)%a eqn:Hoff_eq;
          first done.
        exfalso. solve_addr. }
      clear -Hlen Hsome. revert ns Hlen.
      induction ps as [|p ps IH]; intros [|n ns] Hlen; cbn in *; try constructor.
      + apply Forall_cons in Hsome as [Hs _]. exact Hs.
      + apply Forall_cons in Hsome as [_ Hsome]. apply IH; [exact Hsome | lia].
  Qed.

  (** The exports of an untrusted compartment are safe to share, given the
      safety of its sealed export entries. *)
  Lemma fw_adv_exports_interp fw img fc ub
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) (W : WORLD) (C : CmptName) :
    let swl := fw_switcher_layout img in
    cmpt_ok fw img fc →
    fc_body fc = UntrustedBody ub →
    ([∗ set] v ∈ exported_entries_sealed (swlayout := swl)
                   (layout_cmpt_of _ Hc), interp W C v) -∗
    [∗ list] k ↦ _ ∈ ub_exports ub,
      interp W C (WSealed (ot_switcher (img_sw img)) (cmpt_export_sb (cmpt_of img (fc_name fc)) k)).
  Proof.
    intros swl Hok Hbody. iIntros "#Hexp".
    pose proof (fc_export_nargs_length _ _ _ Hok) as Hlen.
    rewrite /fc_export_nargs Hbody fw_map_eq length_fmap in Hlen.
    iApply big_sepL_intro. iIntros "!>" (k n Hk).
    apply lookup_lt_Some in Hk.
    rewrite /cmpt_export_sb.
    iApply (adversary_export_interp (swlayout := fw_switcher_layout img) _ _
              (layout_cmpt_of _ Hc) k with "Hexp"); [done | cbn; lia].
  Qed.

  (** The world of an untrusted compartment [fc], at position [i] of the
      firmware and owned by the logical compartment [C], once its
      compartment and the stack of the first thread are allocated in it:
      the compartment's imports, code and globals become permanent, its
      export entries sealed, and the stack temporary. The PCC and the CGP
      of the compartment are safe in that world, for a thread that starts
      in it. The case study proves that the imports are safe. The static
      sealed objects of [fc] are not used: the case study may have moved
      them into an invariant. *)
  Lemma fw_close_adv_world_entry {E : coPset} fw img σ i fc ub
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) (W : WORLD) (C : CmptName) :
    let swl := fw_switcher_layout img in
    let c := cmpt_of img (fc_name fc) in
    let C_cmpt := layout_cmpt_of c Hc in
    let t := thread_of img 0 in
    let Wadv := std_update_multiple W (finz.seq_between (b_stack t) (e_stack t)) Temporary in
    firmware_ok fw img σ →
    fw_cmpts fw !! i = Some fc →
    fc_body fc = UntrustedBody ub →
    Forall (λ n, n < 7) (fw_map ue_nargs (ub_exports ub)) →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ finz.seq_between (b_stack t) (e_stack t) →
          std W !! LNonHeap a = None) →
    switcher_threads (swlayout := swl) C -∗
    switcher_static (swlayout := swl) -∗
    fw_cmpt_mem_res c -∗
    fw_cmpt_pers_res img fc -∗
    [[ b_stack t, e_stack t ]] ↦ₐ
      [[ lword_of_word <$> replicate (ft_stack_size (fw_thread0 fw)) (WInt 0) ]] -∗
    ((interp W C (cmpt_pcc_cap C_cmpt) ∗
      interp W C (cmpt_cgp_cap C_cmpt) ∗
      ([∗ set] v ∈ exported_entries_sealed (swlayout := swl) C_cmpt, interp W C v)) -∗
     [∗ list] w ∈ fc_imports fc,
       fw_import_safe C (fw_word_of fw img (fc_static_sealed fc) c w)) -∗
    thread_in th C -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    interp Wadv C (fw_thread_csp img 0) ∗
    [∗ list] k ↦ _ ∈ ub_exports ub,
      interp Wadv C (WSealed (ot_switcher (img_sw img)) (cmpt_export_sb c k)).
  Proof.
    intros swl c C_cmpt t Wadv Hok Hi Hbody Hnargs Hfree.
    iIntros "#Hswitcher #Hstatic (Himp & Hcode & Hdata) #Hpers Hstack Himports #Hthread Hworld".
    iDestruct (switcher_static_seal_pred with "Hstatic") as "#Hseal".
    pose proof (list_elem_of_lookup_2 _ _ _ Hi) as Hin.
    pose proof (fw_cmpt_ok_at _ _ _ _ _ Hok Hi) as Hfc_ok.
    set (swc := fw_switcher_cmpt fw img σ Hok).
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    destruct (fw_adv_cmpt_facts fw img σ fc ub Hc W C Hok Hin Hbody Hnargs)
      as (Hcode & Hdata & Hexports).
    iMod (initialise_adversary_world (swlayout := swl) W swc C_cmpt C
           with "Hseal Himp Hcode Hdata Hstack [] [Himports] Hthread Hworld")
      as "($ & $ & $ & $ & #Hexp)".
    - by eapply (fw_switcher_cmpt_disjoint_at _ _ _ Hok).
    - exact Hfree.
    - exact Hcode.
    - exact Hdata.
    - by apply Forall_replicate.
    - iApply (Hexports with "Hswitcher Hpers").
    - iIntros "H". iApply fw_imports_safe_words; first exact Hfc_ok. by iApply "Himports".
    - iModIntro. by iApply (fw_adv_exports_interp with "Hexp").
  Qed.

  (** [fw_close_adv_world_entry], without the PCC and the CGP. *)
  Lemma fw_close_adv_world {E : coPset} fw img σ i fc ub
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) (W : WORLD) (C : CmptName) :
    let swl := fw_switcher_layout img in
    let c := cmpt_of img (fc_name fc) in
    let C_cmpt := layout_cmpt_of c Hc in
    let t := thread_of img 0 in
    let Wadv := std_update_multiple W (finz.seq_between (b_stack t) (e_stack t)) Temporary in
    firmware_ok fw img σ →
    fw_cmpts fw !! i = Some fc →
    fc_body fc = UntrustedBody ub →
    Forall (λ n, n < 7) (fw_map ue_nargs (ub_exports ub)) →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ finz.seq_between (b_stack t) (e_stack t) →
          std W !! LNonHeap a = None) →
    switcher_threads (swlayout := swl) C -∗
    switcher_static (swlayout := swl) -∗
    fw_cmpt_mem_res c -∗
    fw_cmpt_pers_res img fc -∗
    [[ b_stack t, e_stack t ]] ↦ₐ
      [[ lword_of_word <$> replicate (ft_stack_size (fw_thread0 fw)) (WInt 0) ]] -∗
    ((interp W C (cmpt_pcc_cap C_cmpt) ∗
      interp W C (cmpt_cgp_cap C_cmpt) ∗
      ([∗ set] v ∈ exported_entries_sealed (swlayout := swl) C_cmpt, interp W C v)) -∗
     [∗ list] w ∈ fc_imports fc, fw_import_safe C (fw_word_of fw img (fc_static_sealed fc) c w)) -∗
    thread_in th C -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (fw_thread_csp img 0) ∗
    [∗ list] k ↦ _ ∈ ub_exports ub, interp Wadv C (WSealed (ot_switcher (img_sw img)) (cmpt_export_sb c k)).
  Proof.
    intros swl c C_cmpt t Wadv Hok Hi Hbody Hnargs Hfree.
    iIntros "#Hswitcher #Hstatic Hmem #Hpers Hstack Himports #Hthread Hworld".
    by iMod (fw_close_adv_world_entry fw img σ i fc ub Hc W C Hok Hi Hbody Hnargs Hfree
           with "Hswitcher Hstatic Hmem Hpers Hstack Himports Hthread Hworld")
      as "($ & _ & _ & $ & $)".
  Qed.

  (** The same, with the stack of the first thread revoked in the world of
      [C] rather than temporary: the trusted code keeps the stack, and
      receives the revoked-stack resources of [C]. *)
  Lemma fw_close_adv_world_revoked {E : coPset} fw img σ i fc ub
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) (W : WORLD) (C : CmptName) :
    let swl := fw_switcher_layout img in
    let c := cmpt_of img (fc_name fc) in
    let C_cmpt := layout_cmpt_of c Hc in
    let t := thread_of img 0 in
    let Wadv := std_update_multiple W (finz.seq_between (b_stack t) (e_stack t)) Revoked in
    firmware_ok fw img σ →
    fw_cmpts fw !! i = Some fc →
    fc_body fc = UntrustedBody ub →
    Forall (λ n, n < 7) (fw_map ue_nargs (ub_exports ub)) →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ finz.seq_between (b_stack t) (e_stack t) →
          std W !! LNonHeap a = None) →
    switcher_threads (swlayout := swl) C -∗
    switcher_static (swlayout := swl) -∗
    fw_cmpt_mem_res c -∗
    fw_cmpt_pers_res img fc -∗
    ((interp W C (cmpt_pcc_cap C_cmpt) ∗
      interp W C (cmpt_cgp_cap C_cmpt) ∗
      ([∗ set] v ∈ exported_entries_sealed (swlayout := swl) C_cmpt, interp W C v)) -∗
     [∗ list] w ∈ fc_imports fc, fw_import_safe C (fw_word_of fw img (fc_static_sealed fc) c w)) -∗
    thread_in th C -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    StackRevokedResources Wadv C (finz.seq_between (b_stack t) (e_stack t)) ∗
    [∗ list] k ↦ _ ∈ ub_exports ub, interp Wadv C (WSealed (ot_switcher (img_sw img)) (cmpt_export_sb c k)).
  Proof.
    intros swl c C_cmpt t Wadv Hok Hi Hbody Hnargs Hfree.
    iIntros "#Hswitcher #Hstatic (Himp & Hcode & Hdata) #Hpers Himports #Hthread Hworld".
    iDestruct (switcher_static_seal_pred with "Hstatic") as "#Hseal".
    pose proof (list_elem_of_lookup_2 _ _ _ Hi) as Hin.
    pose proof (fw_cmpt_ok_at _ _ _ _ _ Hok Hi) as Hfc_ok.
    set (swc := fw_switcher_cmpt fw img σ Hok).
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    destruct (fw_adv_cmpt_facts fw img σ fc ub Hc W C Hok Hin Hbody Hnargs)
      as (Hcode & Hdata & Hexports).
    iMod (initialise_adversary_world_revoked (swlayout := swl) W swc C_cmpt C
           with "Hseal Himp Hcode Hdata [] [Himports] Hthread Hworld")
      as "($ & _ & _ & $ & #Hexp)".
    - by eapply (fw_switcher_cmpt_disjoint_at _ _ _ Hok).
    - exact Hfree.
    - exact Hcode.
    - exact Hdata.
    - iApply (Hexports with "Hswitcher Hpers").
    - iIntros "H". iApply fw_imports_safe_words; first exact Hfc_ok. by iApply "Himports".
    - iModIntro. by iApply (fw_adv_exports_interp with "Hexp").
  Qed.

  (** [fw_close_adv_world_entry], with the stack of the thread [k]. *)
  Lemma fw_close_adv_world_entry_at {E : coPset} fw img σ k ft i fc ub
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) (W : WORLD) (C : CmptName) :
    let swl := fw_switcher_layout img in
    let c := cmpt_of img (fc_name fc) in
    let C_cmpt := layout_cmpt_of c Hc in
    let t := thread_of img k in
    let Wadv := std_update_multiple W (finz.seq_between (b_stack t) (e_stack t)) Temporary in
    firmware_ok fw img σ →
    fw_threads fw !! k = Some ft →
    fw_cmpts fw !! i = Some fc →
    fc_body fc = UntrustedBody ub →
    Forall (λ n, n < 7) (fw_map ue_nargs (ub_exports ub)) →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ finz.seq_between (b_stack t) (e_stack t) →
          std W !! LNonHeap a = None) →
    switcher_threads (swlayout := swl) C -∗
    switcher_static (swlayout := swl) -∗
    fw_cmpt_mem_res c -∗
    fw_cmpt_pers_res img fc -∗
    [[ b_stack t, e_stack t ]] ↦ₐ
      [[ lword_of_word <$> replicate (ft_stack_size ft) (WInt 0) ]] -∗
    ((interp W C (cmpt_pcc_cap C_cmpt) ∗
      interp W C (cmpt_cgp_cap C_cmpt) ∗
      ([∗ set] v ∈ exported_entries_sealed (swlayout := swl) C_cmpt, interp W C v)) -∗
     [∗ list] w ∈ fc_imports fc,
       fw_import_safe C (fw_word_of fw img (fc_static_sealed fc) c w)) -∗
    thread_in th C -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    interp Wadv C (fw_thread_csp img k) ∗
    [∗ list] j ↦ _ ∈ ub_exports ub,
      interp Wadv C (WSealed (ot_switcher (img_sw img)) (cmpt_export_sb c j)).
  Proof.
    intros swl c C_cmpt t Wadv Hok Hk Hi Hbody Hnargs Hfree.
    iIntros "#Hswitcher #Hstatic (Himp & Hcode & Hdata) #Hpers Hstack Himports #Hthread Hworld".
    iDestruct (switcher_static_seal_pred with "Hstatic") as "#Hseal".
    pose proof (list_elem_of_lookup_2 _ _ _ Hi) as Hin.
    pose proof (fw_cmpt_ok_at _ _ _ _ _ Hok Hi) as Hfc_ok.
    set (swc := fw_switcher_cmpt_at fw img σ k ft Hok Hk).
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    destruct (fw_adv_cmpt_facts fw img σ fc ub Hc W C Hok Hin Hbody Hnargs)
      as (Hcode & Hdata & Hexports).
    iMod (initialise_adversary_world (swlayout := swl) W swc C_cmpt C
           with "Hseal Himp Hcode Hdata Hstack [] [Himports] Hthread Hworld")
      as "($ & $ & $ & $ & #Hexp)".
    - by eapply (fw_switcher_cmpt_disjoint_thread _ _ _ _ _ Hok Hk).
    - exact Hfree.
    - exact Hcode.
    - exact Hdata.
    - by apply Forall_replicate.
    - iApply (Hexports with "Hswitcher Hpers").
    - iIntros "Hinterp". iApply fw_imports_safe_words; first exact Hfc_ok.
      by iApply "Himports".
    - iModIntro. by iApply (fw_adv_exports_interp with "Hexp").
  Qed.

  (** [fw_close_adv_world_entry] without a stack, on the map of Permanent
      regions of [C] alone: the imports, code and data of an untrusted
      compartment become Permanent regions, and its export entries are
      sealed. No local map is touched, so a shared compartment is opened
      once, before its map goes into its invariant. *)
  Lemma fw_open_adv_cmpt_perm {E : coPset} fw img σ i fc ub
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) (W : WORLD) (C : CmptName) :
    let swl := fw_switcher_layout img in
    let c := cmpt_of img (fc_name fc) in
    let C_cmpt := layout_cmpt_of c Hc in
    firmware_ok fw img σ →
    fw_cmpts fw !! i = Some fc →
    fc_body fc = UntrustedBody ub →
    Forall (λ n, n < 7) (fw_map ue_nargs (ub_exports ub)) →
    switcher_threads (swlayout := swl) C -∗
    switcher_static (swlayout := swl) -∗
    fw_cmpt_mem_res c -∗
    fw_cmpt_pers_res img fc -∗
    ((interp W C (cmpt_pcc_cap C_cmpt) ∗
      interp W C (cmpt_cgp_cap C_cmpt) ∗
      ([∗ set] v ∈ exported_entries_sealed (swlayout := swl) C_cmpt, interp W C v)) -∗
     [∗ list] w ∈ fc_imports fc,
       fw_import_safe C (fw_word_of fw img (fc_static_sealed fc) c w)) -∗
    thread_in th C -∗
    perm_region_map C ∅
    ={E}=∗
    perm_region_map C ∅ ∗
    interp W C (cmpt_pcc_cap C_cmpt) ∗
    interp W C (cmpt_cgp_cap C_cmpt) ∗
    [∗ list] k ↦ _ ∈ ub_exports ub,
      interp W C (WSealed (ot_switcher (img_sw img)) (cmpt_export_sb c k)).
  Proof.
    intros swl c C_cmpt Hok Hi Hbody Hnargs.
    iIntros "#Hswitcher #Hstatic (Himp & Hcode & Hdata) #Hpers Himports #Hthread Hperm".
    iDestruct (switcher_static_seal_pred with "Hstatic") as "#Hseal".
    pose proof (list_elem_of_lookup_2 _ _ _ Hi) as Hin.
    pose proof (fw_cmpt_ok_at _ _ _ _ _ Hok Hi) as Hfc_ok.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    destruct (fw_adv_cmpt_facts fw img σ fc ub Hc W C Hok Hin Hbody Hnargs)
      as (Hcode & Hdata & Hexports).
    iMod (alloc_adversary_compartment_perm (swlayout := swl) W C_cmpt C Hcode Hdata
           with "Hseal Himp Hcode Hdata [] [Himports] Hthread Hperm")
      as "($ & $ & $ & #Hexp)".
    - iApply (Hexports with "Hswitcher Hpers").
    - iIntros "Hinterp". iApply fw_imports_safe_words; first exact Hfc_ok.
      by iApply "Himports".
    - iModIntro. by iApply (fw_adv_exports_interp with "Hexp").
  Qed.
End adversary.

(** The first thread starts in an untrusted compartment. *)
Definition fw_entry_untrusted (fw : firmware) : Prop :=
  match fc_body (fw_entry_fc fw 0) with
  | UntrustedBody _ => True
  | TrustedBody _ | SchedulerBody _ => False
  end.

(** The PCC of the compartment the thread [i] starts in, at its base, as
    its export table holds it. *)
Definition fw_entry_pcc `{MP : MachineParameters} (fw : firmware) (img : fw_image) (i : nat)
  : Word :=
  let m := fw_entry_cmpt fw img i in
  Cap RX Global (cmpt_b_pcc m) (cmpt_e_pcc m) (cmpt_b_pcc m).
