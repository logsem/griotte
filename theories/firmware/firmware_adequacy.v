From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import assert_spec.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_base_interp.
From griotte Require Import stack_world_resources mkregion_helpers disjoint_regions_tactics.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import firmware_ok.
(* Imported last: the fields of the image records shadow the fields of the
   layout records of [compartment_layout] and of [switcherLayout]. *)
From griotte Require Import image firmware.

(** * The generic adequacy theorem of firmware images

    [firmware_adequacy] proves the assert flag of every machine run from a
    state satisfying [firmware_ok fw img σ], given the obligations
    [fw_obligations fw] of the trusted code of [fw]. The obligations
    receive the resources the loader's image provides once the switcher
    and the assert library are initialised ([fw_shared_res]) and those of
    the thread ([fw_thread_res]).

    The layout records of the program logic ([cmpt], [cmptSwitcher],
    [cmptAssert]) carry their well-formedness proofs. The bridges
    [layout_cmpt_of], [layout_switcher_of] and [layout_assert_of] build them
    from an image record and its layout conditions, stated by the records
    [img_cmpt_layout], [img_switcher_layout] (with [trusted_stack_layout])
    and [img_assert_layout]; the lemmas [img_wf_*_layout] derive these from
    [img_wf]. *)

(** ** Lists of the translation *)

Lemma fw_app_eq {A} (l1 l2 : list A) : fw_app l1 l2 = l1 ++ l2.
Proof. induction l1 as [|x l1 IH]; cbn; [done | by rewrite IH]. Qed.

Lemma fw_map_eq {A B} (f : A → B) (l : list A) : fw_map f l = f <$> l.
Proof. induction l as [|x l IH]; cbn; [done | by rewrite IH]. Qed.

Lemma fw_flat_map_cons {A B} (f : A → list B) (x : A) (l : list A) :
  fw_flat_map f (x :: l) = f x ++ fw_flat_map f l.
Proof. by rewrite /= fw_app_eq. Qed.

Lemma big_union_cons (m : Mem) (ms : list Mem) : big_union (m :: ms) = m ∪ big_union ms.
Proof. destruct ms as [|m' ms]; cbn; [by rewrite right_id_L | done]. Qed.

Lemma big_and_cons (p : Prop) (ps : list Prop) : big_and (p :: ps) ↔ p ∧ big_and ps.
Proof. destruct ps as [|p' ps]; cbn; [tauto | done]. Qed.

Lemma big_and_fw_map {A} (P : A → Prop) (l : list A) : big_and (fw_map P l) → Forall P l.
Proof.
  induction l as [|x l IH]; intros Hl; first by constructor.
  apply big_and_cons in Hl as [Hx Hl]. constructor; [exact Hx | by apply IH].
Qed.

Lemma big_and_fw_app (ps qs : list Prop) : big_and (fw_app ps qs) → big_and ps ∧ big_and qs.
Proof.
  induction ps as [|p ps IH]; cbn [fw_app]; intros Hpq; first done.
  apply big_and_cons in Hpq as [Hp Hpq]. apply IH in Hpq as [Hps Hqs].
  split; last done. by apply big_and_cons.
Qed.

(** ** Disjoint lists of address ranges *)

Lemma disjoint_list_elem_of (X Y : list Addr) (Xs : list (list Addr)) :
  ## (X :: Xs) → Y ∈ Xs → X ## Y.
Proof.
  rewrite disjoint_list_cons. intros [HX _] HY a Ha1 Ha2.
  apply (HX a Ha1). apply elem_of_union_list. by exists Y.
Qed.

Lemma disjoint_list_app_cross (Xs Ys : list (list Addr)) (X Y : list Addr) :
  ## (Xs ++ Ys) → X ∈ Xs → Y ∈ Ys → X ## Y.
Proof.
  induction Xs as [|X0 Xs IH]; intros Hd HX HY; first by apply not_elem_of_nil in HX.
  rewrite -app_comm_cons in Hd.
  apply elem_of_cons in HX as [->|HX].
  - eapply disjoint_list_elem_of; first exact Hd. apply elem_of_app; by right.
  - apply IH; [|done|done]. by apply disjoint_list_cons in Hd as [_ Hd].
Qed.

Lemma disjoint_list_sublist (Xs Ys : list (list Addr)) :
  Xs `sublist_of` Ys → ## Ys → ## Xs.
Proof.
  induction 1 as [|X Xs Ys Hsub IH|X Xs Ys Hsub IH]; intros HYs.
  - constructor.
  - apply disjoint_list_cons in HYs as [HX HYs].
    apply disjoint_list_cons; split; last by apply IH.
    intros a Ha1 Ha2. apply (HX a Ha1).
    apply elem_of_union_list in Ha2 as (Z & HZ & Ha2).
    apply elem_of_union_list. exists Z; split; last done.
    by eapply sublist_subseteq.
  - apply disjoint_list_cons in HYs as [_ HYs]. by apply IH.
Qed.

Section regions.
  Context `{MP : MachineParameters}.

  (** The addresses of a named range of the translation. *)
  Definition rng_addrs (t : string * Addr * Addr) : list Addr := finz.seq_between t.1.2 t.2.

  Definition rngs_disjoint (ts : list (string * Addr * Addr)) : Prop := ## (rng_addrs <$> ts).

  Lemma rngs_disjoint_sublist ts1 ts2 :
    ts1 `sublist_of` ts2 → rngs_disjoint ts2 → rngs_disjoint ts1.
  Proof. intros Hsub. apply disjoint_list_sublist. by apply fmap_sublist. Qed.

  Lemma rngs_disjoint_app_cross ts1 ts2 t1 t2 :
    rngs_disjoint (ts1 ++ ts2) → t1 ∈ ts1 → t2 ∈ ts2 → rng_addrs t1 ## rng_addrs t2.
  Proof.
    rewrite /rngs_disjoint fmap_app. intros Hd H1 H2.
    eapply disjoint_list_app_cross; [exact Hd | |]; apply list_elem_of_fmap; eauto.
  Qed.

  (** The domain of [m] is covered by the ranges [ts]. *)
  Definition mem_in (m : Mem) (ts : list (string * Addr * Addr)) : Prop :=
    ∀ a, a ∈ dom m → ∃ t, t ∈ ts ∧ a ∈ rng_addrs t.

  Lemma mem_in_union m1 m2 ts1 ts2 :
    mem_in m1 ts1 → mem_in m2 ts2 → mem_in (m1 ∪ m2) (ts1 ++ ts2).
  Proof.
    intros H1 H2 a Ha. rewrite dom_union_L elem_of_union in Ha.
    destruct Ha as [Ha|Ha];
      [destruct (H1 a Ha) as (t & Ht & Hat) | destruct (H2 a Ha) as (t & Ht & Hat)];
      exists t; (split; last done); apply elem_of_app; auto.
  Qed.

  Lemma mem_in_mono m ts1 ts2 : ts1 ⊆ ts2 → mem_in m ts1 → mem_in m ts2.
  Proof.
    intros Hsub H1 a Ha. destruct (H1 a Ha) as (t & Ht & Hat).
    exists t. split; [by apply Hsub | done].
  Qed.

  Lemma mem_in_empty ts : mem_in ∅ ts.
  Proof. intros a Ha. by rewrite dom_empty_L in Ha. Qed.

  Lemma mem_in_disjoint m1 m2 ts1 ts2 :
    mem_in m1 ts1 →
    mem_in m2 ts2 →
    (∀ t1 t2, t1 ∈ ts1 → t2 ∈ ts2 → rng_addrs t1 ## rng_addrs t2) →
    m1 ##ₘ m2.
  Proof.
    intros H1 H2 Hd. apply map_disjoint_spec. intros a w1 w2 Ha1 Ha2.
    destruct (H1 a (elem_of_dom_2 _ _ _ Ha1)) as (t1 & Ht1 & Hat1).
    destruct (H2 a (elem_of_dom_2 _ _ _ Ha2)) as (t2 & Ht2 & Hat2).
    by apply (Hd t1 t2 Ht1 Ht2 a).
  Qed.

  Lemma mem_in_heap_disjoint m ts :
    mem_in m ts →
    Forall (λ t, range_ok t.1.2 t.2) ts →
    initial_heap_memory ##ₘ m.
  Proof.
    intros Hm Hts. apply map_disjoint_spec. intros a w1 w2 Ha1 Ha2.
    destruct (Hm a (elem_of_dom_2 _ _ _ Ha2)) as (t & Ht & Hat).
    rewrite Forall_forall in Hts. destruct (Hts t Ht) as [ [_ Hheap] _].
    apply (Hheap a Hat).
    rewrite /initial_heap_memory lookup_gset_to_gmap_Some /heap_addresses
      elem_of_list_to_set in Ha1.
    by destruct Ha1.
  Qed.

  Lemma mem_region_mkregion (b e : Addr) (ws : list Word) :
    (b + length ws)%a = Some e → mem_region b ws = mkregion b e ws.
  Proof.
    intros Hbe. rewrite /mem_region /mkregion /finz.seq_between.
    by apply finz_incr_iff_dist in Hbe as [_ ->].
  Qed.

  Lemma mkregion_app (b a e : Addr) (ws1 ws2 : list Word) :
    (b + length ws1)%a = Some a →
    (a + length ws2)%a = Some e →
    mkregion b e (ws1 ++ ws2) = mkregion b a ws1 ∪ mkregion a e ws2.
  Proof.
    intros Hba Hae.
    rewrite /mkregion (finz_seq_between_split b a e); last solve_addr.
    rewrite zip_with_app; first apply list_to_map_app.
    rewrite finz_seq_between_length. by apply finz_incr_iff_dist in Hba as [_ Hdist].
  Qed.

  Lemma mem_in_mem_region s (b e : Addr) (ws : list Word) :
    (b + length ws)%a = Some e → mem_in (mem_region b ws) [(s, b, e)].
  Proof.
    intros Hbe a Ha. exists (s, b, e). split; first by apply list_elem_of_singleton.
    rewrite (mem_region_mkregion b e) // in Ha.
    by apply dom_mkregion_incl, elem_of_list_to_set in Ha.
  Qed.
End regions.

(** ** Bridges to the layout records of the program logic *)
Section layout_bridges.
  Context `{MP : MachineParameters}.

  (** *** Compartments *)

  (** The proof fields of [compartment_layout.cmpt], for a compartment of an
      image. *)
  Record img_cmpt_layout (c : img_cmpt) : Prop := MkImgCmptLayout {
    icl_import_size :
      (cmpt_b_pcc c + length (cmpt_imports c))%a = Some (cmpt_a_code c);
    icl_code_size :
      (cmpt_a_code c + length (cmpt_code c))%a = Some (cmpt_e_pcc c);
    icl_data_size :
      (cmpt_b_cgp c + length (cmpt_data c))%a = Some (cmpt_e_cgp c);
    icl_static_sealed_size :
      (cmpt_b_static_sealed c + length (cmpt_static_sealed c))%a = Some (cmpt_e_static_sealed c);
    icl_exp_tbl_pcc_size :
      (cmpt_exp_tbl_pcc c + ExportTable_offset_cgp)%a = Some (cmpt_exp_tbl_cgp c);
    icl_exp_tbl_header_size :
      (cmpt_exp_tbl_pcc c + ExportTable_offset_entries)%a = Some (cmpt_exp_tbl_entries_start c);
    icl_exp_tbl_entries_size :
      (cmpt_exp_tbl_entries_start c + length (cmpt_exp_tbl_entries c))%a =
        Some (cmpt_exp_tbl_entries_end c);
    icl_disjointness :
      ## [finz.seq_between (cmpt_b_pcc c) (cmpt_e_pcc c);
          finz.seq_between (cmpt_b_cgp c) (cmpt_e_cgp c);
          finz.seq_between (cmpt_b_static_sealed c) (cmpt_e_static_sealed c);
          finz.seq_between (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c)];
    icl_pcc_mmio : disjoint_from_mmio (cmpt_b_pcc c) (cmpt_e_pcc c);
    icl_pcc_not_heap : not_heap_range (cmpt_b_pcc c) (cmpt_e_pcc c);
    icl_cgp_mmio : disjoint_from_mmio (cmpt_b_cgp c) (cmpt_e_cgp c);
    icl_cgp_not_heap : not_heap_range (cmpt_b_cgp c) (cmpt_e_cgp c);
    icl_exp_tbl_mmio : disjoint_from_mmio (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c);
    icl_static_sealed_mmio :
      disjoint_from_mmio (cmpt_b_static_sealed c) (cmpt_e_static_sealed c);
    icl_exp_tbl_not_heap : not_heap_range (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c);
    icl_static_sealed_not_heap :
      not_heap_range (cmpt_b_static_sealed c) (cmpt_e_static_sealed c);
    icl_pcc_end_not_heap : is_heap_address (cmpt_e_pcc c) = false;
  }.

  Definition layout_cmpt_of (c : img_cmpt) (Hc : img_cmpt_layout c) : cmpt :=
    mkCmpt
      (cmpt_b_pcc c) (cmpt_a_code c) (cmpt_e_pcc c)
      (cmpt_b_cgp c) (cmpt_e_cgp c)
      (cmpt_b_static_sealed c) (cmpt_e_static_sealed c)
      (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_cgp c)
      (cmpt_exp_tbl_entries_start c) (cmpt_exp_tbl_entries_end c)
      (cmpt_imports c) (cmpt_code c) (cmpt_data c)
      (cmpt_static_sealed c) (cmpt_exp_tbl_handler c) (cmpt_exp_tbl_handler_stackless c)
      (cmpt_exp_tbl_entries c)
      (icl_import_size _ Hc) (icl_code_size _ Hc) (icl_data_size _ Hc)
      (icl_static_sealed_size _ Hc) (icl_exp_tbl_pcc_size _ Hc) (icl_exp_tbl_header_size _ Hc)
      (icl_exp_tbl_entries_size _ Hc) (icl_disjointness _ Hc)
      (icl_pcc_mmio _ Hc) (icl_pcc_not_heap _ Hc) (icl_cgp_mmio _ Hc) (icl_cgp_not_heap _ Hc)
      (icl_exp_tbl_mmio _ Hc) (icl_static_sealed_mmio _ Hc) (icl_exp_tbl_not_heap _ Hc)
      (icl_static_sealed_not_heap _ Hc) (icl_pcc_end_not_heap _ Hc).

  (** *** The switcher and the thread's stacks

      The conditions on the contents of the trusted stack are kept apart:
      they change with the contents the loader writes there. *)

  Record trusted_stack_layout (b e b_hz e_hz : Addr) (ts : list Word) : Prop :=
    MkTrustedStackLayout {
    tsl_size : (b + length ts)%a = Some e;
    tsl_frameoffset :
      ts !! Z.to_nat TrustedStack_offset_frameoffset = Some (WInt (tstack_frameoffset 0));
    tsl_frames_fit : ∃ n : nat, (b + tstack_frame_offset (S n))%a = Some e;
    tsl_error_count :
      ts !! Z.to_nat (tstack_frame_offset 0 + TrustedStackFrame_offset_errorHandlerCount)
      = Some (WInt 0);
    tsl_words : Forall trusted_stack_word ts;
    tsl_hazard :
      ts !! Z.to_nat TrustedStack_offset_hazardPointers = Some (WCap true WO Global b_hz e_hz b_hz);
  }.

  Record img_switcher_layout (sw : img_switcher) (t : img_thread) (ss : list Word) : Prop :=
    MkImgSwitcherLayout {
    isl_switcher_size :
      (a_switcher_call sw + length switcher_instrs)%a = Some (e_switcher sw);
    isl_call_entry_point : (b_switcher sw + 5)%a = Some (a_switcher_call sw);
    isl_return_entry_point :
      (b_switcher sw + (5 + length switcher_call_instrs))%a = Some (a_switcher_return sw);
    isl_ot_switcher_size : (ot_switcher sw < ot_switcher sw ^+ 1)%ot;
    isl_stack_size : (b_stack t + length ss)%a = Some (e_stack t);
    isl_disjointness :
      finz.seq_between (b_switcher sw) (e_switcher sw) ##
        finz.seq_between (b_trusted_stack t) (e_trusted_stack t) ∧
      finz.seq_between (b_switcher sw) (e_switcher sw) ##
        finz.seq_between (b_stack t) (e_stack t) ∧
      finz.seq_between (b_trusted_stack t) (e_trusted_stack t) ##
        finz.seq_between (b_stack t) (e_stack t);
    isl_trusted_stack_mmio : disjoint_from_mmio (b_trusted_stack t) (e_trusted_stack t);
    isl_switcher_key_not_shadow : is_shadow_address (b_switcher sw ^+ 1)%a = false;
    isl_switcher_not_heap : not_heap_range (b_switcher sw) (e_switcher sw);
    isl_stack_mmio : disjoint_from_mmio (b_stack t) (e_stack t);
    isl_stack_not_heap : disjoint_from_heap (b_stack t) (e_stack t);
    isl_switcher_mmio : disjoint_from_mmio (b_switcher sw) (e_switcher sw);
    isl_switcher_end_not_heap : is_heap_address (e_switcher sw) = false;
    isl_trusted_stack_not_heap :
      not_heap_range (b_trusted_stack t) (b_trusted_stack t ^+ TSTACK_REGFRAME_SZ)%a;
    isl_trusted_stack_nonzero : (b_trusted_stack t : Z) ≠ 0;
    isl_hazard_size : (b_hazard t + 2)%a = Some (e_hazard t);
    isl_hazard_disjointness :
      finz.seq_between (b_hazard t) (e_hazard t) ## finz.seq_between (b_switcher sw) (e_switcher sw) ∧
      finz.seq_between (b_hazard t) (e_hazard t) ##
        finz.seq_between (b_trusted_stack t) (e_trusted_stack t) ∧
      finz.seq_between (b_hazard t) (e_hazard t) ## finz.seq_between (b_stack t) (e_stack t);
    isl_hazard_mmio : disjoint_from_mmio (b_hazard t) (e_hazard t);
    isl_hazard_not_heap : not_heap_range (b_hazard t) (e_hazard t);
  }.

  Definition layout_switcher_of (sw : img_switcher) (t : img_thread) (ts ss : list Word)
      (Hts : trusted_stack_layout (b_trusted_stack t) (e_trusted_stack t) (b_hazard t) (e_hazard t) ts)
      (Hsw : img_switcher_layout sw t ss) : cmptSwitcher :=
    mkCmptSwitcher
      (b_switcher sw) (e_switcher sw) (a_switcher_call sw) (a_switcher_return sw)
      (ot_switcher sw) (b_trusted_stack t) (e_trusted_stack t)
      (isl_switcher_size _ _ _ Hsw) (isl_call_entry_point _ _ _ Hsw) (isl_return_entry_point _ _ _ Hsw)
      (isl_ot_switcher_size _ _ _ Hsw)
      ts (tsl_size _ _ _ _ _ Hts) (tsl_frameoffset _ _ _ _ _ Hts) (tsl_frames_fit _ _ _ _ _ Hts)
      (tsl_error_count _ _ _ _ _ Hts) (tsl_words _ _ _ _ _ Hts)
      (b_stack t) (e_stack t) ss (isl_stack_size _ _ _ Hsw) (isl_disjointness _ _ _ Hsw)
      (isl_trusted_stack_mmio _ _ _ Hsw) (isl_switcher_key_not_shadow _ _ _ Hsw)
      (isl_switcher_not_heap _ _ _ Hsw) (isl_stack_mmio _ _ _ Hsw) (isl_stack_not_heap _ _ _ Hsw)
      (isl_switcher_mmio _ _ _ Hsw) (isl_switcher_end_not_heap _ _ _ Hsw)
      (isl_trusted_stack_not_heap _ _ _ Hsw)
      (b_hazard t) (e_hazard t) (isl_hazard_size _ _ _ Hsw) (tsl_hazard _ _ _ _ _ Hts)
      (isl_hazard_disjointness _ _ _ Hsw) (isl_hazard_mmio _ _ _ Hsw)
      (isl_hazard_not_heap _ _ _ Hsw).

  (** *** The assert library *)

  Record img_assert_layout (asrt : img_assert) : Prop := MkImgAssertLayout {
    ial_code_size :
      (b_assert asrt + length assert_subroutine_instrs)%a = Some (cap_assert asrt);
    ial_cap_size : (cap_assert asrt + 1)%a = Some (e_assert asrt);
    ial_flag_size : (flag_assert asrt + 1)%a = Some (flag_assert asrt ^+ 1)%a;
    ial_code_not_heap : is_heap_address (b_assert asrt) = false;
    ial_flag_disjoint :
      finz.seq_between (b_assert asrt) (e_assert asrt) ##
        finz.seq_between (flag_assert asrt) (flag_assert asrt ^+ 1)%a;
    ial_mmio : disjoint_from_mmio (b_assert asrt) (e_assert asrt);
    ial_flag_mmio : disjoint_from_mmio (flag_assert asrt) (flag_assert asrt ^+ 1)%a;
    ial_end_not_heap : is_heap_address (e_assert asrt) = false;
  }.

  Definition layout_assert_of (asrt : img_assert) (Ha : img_assert_layout asrt) : cmptAssert :=
    mkCmptAssert
      (b_assert asrt) (e_assert asrt) (cap_assert asrt) (flag_assert asrt)
      (ial_code_size _ Ha) (ial_cap_size _ Ha) (ial_flag_size _ Ha) (ial_code_not_heap _ Ha)
      (ial_flag_disjoint _ Ha) (ial_mmio _ Ha) (ial_flag_mmio _ Ha) (ial_end_not_heap _ Ha).
End layout_bridges.

(** ** The memory of an image, as the layout records' initial memories *)
Section layout_memory.
  Context `{MP : MachineParameters}.

  (** The contents of the trusted stack of the thread [i], as in
      [thread_mem]. *)
  Definition fw_tstack_content (img : fw_image) (i : nat) (ft : fw_thread) : list Word :=
    let t := thread_of img i in
    let c := cmpt_of img (ft_cmpt ft) in
    initial_trusted_stack_content
      (WCap true RWL Local (b_stack t) (e_stack t) (stk_start_a (b_stack t) (e_stack t)))
      (WCap true RW Global (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c) (cmpt_exp_tbl_pcc c))
      (WCap true WO Global (b_hazard t) (e_hazard t) (b_hazard t))
      (ft_tstack_frames ft).

  (** The stack pointer cell of the entry frame of the thread [i]. *)
  Lemma fw_tstack_content_csp (img : fw_image) (i : nat) (ft : fw_thread) :
    let t := thread_of img i in
    fw_tstack_content img i ft
      !! Z.to_nat (tstack_frame_offset 0 + TrustedStackFrame_offset_csp)
    = Some (WCap true RWL Local (b_stack t) (e_stack t) (stk_start_a (b_stack t) (e_stack t))).
  Proof. reflexivity. Qed.

  (** The export table cell of the entry frame of the thread [i]. *)
  Lemma fw_tstack_content_export_table (img : fw_image) (i : nat) (ft : fw_thread) :
    let c := cmpt_of img (ft_cmpt ft) in
    fw_tstack_content img i ft
      !! Z.to_nat (tstack_frame_offset 0 + TrustedStackFrame_offset_calleeExportTable)
    = Some (WCap true RW Global (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c) (cmpt_exp_tbl_pcc c)).
  Proof. reflexivity. Qed.

  Lemma mem_region_app (b a e : Addr) (ws1 ws2 : list Word) :
    (b + length ws1)%a = Some a →
    (a + length ws2)%a = Some e →
    mem_region b (ws1 ++ ws2) = mkregion b a ws1 ∪ mkregion a e ws2.
  Proof.
    intros Hba Hae.
    rewrite (mem_region_mkregion b e); first by apply mkregion_app.
    rewrite length_app. solve_addr.
  Qed.

  Lemma cmpt_mem_layout (img : fw_image) (fc : fw_cmpt)
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc))) :
    cmpt_mem img fc = mk_initial_cmpt (layout_cmpt_of _ Hc).
  Proof.
    generalize dependent Hc. rewrite /cmpt_mem /note.
    generalize (cmpt_of img (fc_name fc)). intros c Hc.
    rewrite /mk_initial_cmpt /cmpt_pcc_mregion /cmpt_cgp_mregion
      /cmpt_static_sealed_mregion /cmpt_exp_tbl_mregion /=.
    pose proof (icl_import_size _ Hc). pose proof (icl_code_size _ Hc).
    pose proof (icl_data_size _ Hc). pose proof (icl_static_sealed_size _ Hc).
    pose proof (icl_exp_tbl_pcc_size _ Hc). pose proof (icl_exp_tbl_header_size _ Hc).
    pose proof (icl_exp_tbl_entries_size _ Hc).
    rewrite (mem_region_app (cmpt_b_pcc c) (cmpt_a_code c) (cmpt_e_pcc c)) //.
    rewrite (mem_region_mkregion (cmpt_b_cgp c) (cmpt_e_cgp c)) //.
    rewrite (mem_region_mkregion (cmpt_b_static_sealed c) (cmpt_e_static_sealed c)) //.
    rewrite (mem_region_mkregion (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c));
      last (cbn; solve_addr).
    change (?w1 :: ?w2 :: ?w3 :: ?w4 :: cmpt_exp_tbl_entries c)
      with ([w1] ++ [w2; w3; w4] ++ cmpt_exp_tbl_entries c).
    rewrite (mkregion_app (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_cgp c));
      [| cbn; solve_addr | rewrite length_app; cbn; solve_addr].
    rewrite (mkregion_app (cmpt_exp_tbl_cgp c) (cmpt_exp_tbl_entries_start c));
      [| cbn; solve_addr | done].
    by rewrite assoc_L.
  Qed.

  Lemma switcher_mem_layout (img : fw_image) (t : img_thread) (ts ss : list Word)
      (Hts : trusted_stack_layout (b_trusted_stack t) (e_trusted_stack t) (b_hazard t) (e_hazard t) ts)
      (Hsw : img_switcher_layout (img_sw img) t ss) :
    switcher_mem img = cmpt_switcher_code_mregion (layout_switcher_of _ _ _ _ Hts Hsw).
  Proof.
    rewrite /switcher_mem /cmpt_switcher_code_mregion /=.
    pose proof (isl_switcher_size _ _ _ Hsw). pose proof (isl_call_entry_point _ _ _ Hsw).
    change (?w1 :: ?w2 :: ?w3 :: ?w4 :: ?w5 :: switcher_instrs)
      with ([w1; w2; w3; w4; w5] ++ switcher_instrs).
    by apply mem_region_app.
  Qed.

  (** The memory of the first thread: its trusted stack, its stack and its
      hazard slots. *)
  Lemma thread_mem_layout (img : fw_image) (ft : fw_thread)
      (Hts : trusted_stack_layout (b_trusted_stack (thread_of img 0))
               (e_trusted_stack (thread_of img 0))
               (b_hazard (thread_of img 0)) (e_hazard (thread_of img 0))
               (fw_tstack_content img 0 ft))
      (Hsw : img_switcher_layout (img_sw img) (thread_of img 0)
               (replicate (ft_stack_size ft) (WInt 0))) :
    thread_mem img 0 ft =
      cmpt_switcher_trusted_stack_mregion (layout_switcher_of _ _ _ _ Hts Hsw) ∪
      cmpt_switcher_stack_mregion (layout_switcher_of _ _ _ _ Hts Hsw) ∪
      cmpt_switcher_hazard_mregion (layout_switcher_of _ _ _ _ Hts Hsw).
  Proof.
    rewrite /thread_mem /note /cmpt_switcher_trusted_stack_mregion
      /cmpt_switcher_stack_mregion /cmpt_switcher_hazard_mregion /=.
    rewrite (mem_region_mkregion _ (e_trusted_stack (thread_of img 0)));
      last exact (tsl_size _ _ _ _ _ Hts).
    rewrite (mem_region_mkregion _ (e_stack (thread_of img 0)));
      last exact (isl_stack_size _ _ _ Hsw).
    by rewrite (mem_region_mkregion _ (e_hazard (thread_of img 0)));
      last exact (isl_hazard_size _ _ _ Hsw).
  Qed.

  Lemma assert_mem_layout (img : fw_image) (Ha : img_assert_layout (img_asrt img)) :
    assert_code_mem img ∪ assert_flag_mem img = mk_initial_assert (layout_assert_of _ Ha).
  Proof.
    pose proof (ial_code_size _ Ha). pose proof (ial_cap_size _ Ha).
    rewrite /assert_code_mem /assert_flag_mem.
    rewrite (mem_region_app (b_assert (img_asrt img)) (cap_assert (img_asrt img))
               (e_assert (img_asrt img))) //.
    by rewrite (mem_region_mkregion _ (flag_assert (img_asrt img) ^+ 1)%a);
      last exact (ial_flag_size _ Ha).
  Qed.
End layout_memory.

(** ** The layout conditions of an image, from [img_wf] *)
Section layout_of_img_wf.
  Context `{MP : MachineParameters}.

  (** The ranges of [all_ranges], with their names. *)
  Definition fw_ranges (fw : firmware) (img : fw_image) : list (string * Addr * Addr) :=
    let sw := img_sw img in
    let asrt := img_asrt img in
    ("switcher", b_switcher sw, e_switcher sw) ::
    ("assert", b_assert asrt, e_assert asrt) ::
    ("assert flag", flag_assert asrt, (flag_assert asrt ^+ 1)%a) ::
    (fw_flat_map (cmpt_ranges img) (fw_cmpts fw) ++
     fw_flat_map (λ x, x) (fw_imap (thread_ranges img) (fw_threads fw))).

  Lemma img_wf_rngs_disjoint fw img : img_wf fw img → rngs_disjoint (fw_ranges fw img).
  Proof.
    intros (_ & _ & _ & _ & Himg).
    rewrite /section in Himg. apply big_and_fw_app in Himg as [Himg _].
    apply big_and_cons in Himg as [Hdisj _].
    rewrite /note /ranges_disjoint /all_ranges fw_map_eq -list_fmap_compose in Hdisj.
    rewrite /rngs_disjoint /fw_ranges -fw_app_eq.
    erewrite list_fmap_ext; first exact Hdisj.
    by intros _ [ [s b] e] _.
  Qed.

  Lemma range_ok_mmio b e : range_ok b e → disjoint_from_mmio b e.
  Proof. intros (_ & Hsh & Hrev). by split. Qed.

  Lemma range_ok_not_heap b e : range_ok b e → not_heap_range b e.
  Proof. by intros [Hnh _]. Qed.

  Lemma disjoint_from_heap_shrink b e e' :
    (e' <= e)%a → disjoint_from_heap b e → disjoint_from_heap b e'.
  Proof.
    intros He Hdisj a Ha1 Ha2. apply (Hdisj a); last done.
    rewrite elem_of_finz_seq_between in Ha1. apply elem_of_finz_seq_between. solve_addr.
  Qed.

  (** The ranges of the compartments. *)
  Lemma cmpt_ranges_sublist img (fc : fw_cmpt) (fcs : list fw_cmpt) :
    fc ∈ fcs → cmpt_ranges img fc `sublist_of` fw_flat_map (cmpt_ranges img) fcs.
  Proof.
    induction fcs as [|fc' fcs IH]; intros Hin; first by apply not_elem_of_nil in Hin.
    rewrite fw_flat_map_cons. apply elem_of_cons in Hin as [->|Hin].
    - by apply sublist_inserts_r.
    - apply sublist_inserts_l. by apply IH.
  Qed.

  Lemma cmpt_wf_split fw img fc :
    cmpt_wf fw img fc →
    let c := cmpt_of img (fc_name fc) in
    (cmpt_b_pcc c + length (cmpt_imports c))%a = Some (cmpt_a_code c) ∧
    (cmpt_a_code c + length (cmpt_code c))%a = Some (cmpt_e_pcc c) ∧
    (cmpt_b_cgp c + length (cmpt_data c))%a = Some (cmpt_e_cgp c) ∧
    (cmpt_b_static_sealed c + length (cmpt_static_sealed c))%a = Some (cmpt_e_static_sealed c) ∧
    (cmpt_exp_tbl_pcc c + ExportTable_offset_cgp)%a = Some (cmpt_exp_tbl_cgp c) ∧
    (cmpt_exp_tbl_pcc c + ExportTable_offset_entries)%a = Some (cmpt_exp_tbl_entries_start c) ∧
    (cmpt_exp_tbl_entries_start c + length (cmpt_exp_tbl_entries c))%a =
      Some (cmpt_exp_tbl_entries_end c) ∧
    Forall (λ t, range_ok t.1.2 t.2) (cmpt_ranges img fc) ∧
    is_heap_address (cmpt_e_pcc c) = false ∧
    Forall (word_rooted (fw_set (fw_heap_roots fw))) (img_cmpt_words c) ∧
    Forall word_exec_ok (img_cmpt_words c).
  Proof.
    rewrite /cmpt_wf /section. intros Hwf.
    apply big_and_fw_app in Hwf as [Hlayout Hrest].
    apply big_and_fw_app in Hrest as [_ [Hrooted Hexec] ].
    destruct Hlayout as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hranges & Hend).
    split_and!; try done.
    destruct Hranges as (Hr1 & Hr2 & Hr3 & Hr4).
    apply Forall_cons; split; first exact Hr1. apply Forall_cons; split; first exact Hr2.
    apply Forall_cons; split; first exact Hr3. apply Forall_cons; split; first exact Hr4.
    constructor.
  Qed.

  Lemma initial_trusted_stack_content_length w_csp w_export_table w_hazard n :
    Z.of_nat (length (initial_trusted_stack_content w_csp w_export_table w_hazard n)) =
      tstack_frame_offset (S n).
  Proof.
    rewrite /initial_trusted_stack_content !length_app !length_replicate /=.
    rewrite /tstack_frame_offset /TrustedStack_offset_frames /TSTACK_REGFRAME_SZ
      /TSTACK_HEADER_SZ /TrustedStackFrame_size /TrustedStack_offset_hazardPointers.
    lia.
  Qed.

  Lemma initial_trusted_stack_layout b e b_hz e_hz w_csp w_export_table n :
    let w_hazard := WCap true WO Global b_hz e_hz b_hz in
    (b + tstack_frame_offset (S n))%a = Some e →
    trusted_stack_word w_csp →
    trusted_stack_word w_export_table →
    trusted_stack_word w_hazard →
    trusted_stack_layout b e b_hz e_hz
      (initial_trusted_stack_content w_csp w_export_table w_hazard n).
  Proof.
    intros w_hazard Hsize Hcsp Hexport_table Hhazard. split.
    - by rewrite initial_trusted_stack_content_length.
    - reflexivity.
    - by exists n.
    - reflexivity.
    - by apply initial_trusted_stack_content_words.
    - apply initial_trusted_stack_content_hazard.
  Qed.

  (** A capability of the entry frame. *)
  Lemma trusted_stack_word_cap t p g b e a :
    disjoint_from_heap b e →
    executable_word (WCap t p g b e a) = false →
    trusted_stack_word (WCap t p g b e a).
  Proof.
    intros Hbe Hx. split; last done.
    rewrite /heap_authority_base. case_decide; last done.
    rewrite /heap_cap_base /= (disjoint_from_heap_not_in b e b Hbe); first done.
    apply withinBounds_true_iff. solve_addr.
  Qed.

  Lemma fw_cmpt_of_trusted (l : list fw_cmpt) (n : string) tb :
    fc_body (fw_cmpt_of l n) = TrustedBody tb →
    fw_cmpt_of l n ∈ l ∧ fc_name (fw_cmpt_of l n) = n.
  Proof.
    induction l as [|fc l IH]; cbn; first done.
    destruct (String.eqb_spec n (fc_name fc)) as [->|Hne]; intros Hbody.
    - split; [apply list_elem_of_here | done].
    - destruct (IH Hbody) as [Hin Hname]. split; [by apply list_elem_of_further | done].
  Qed.

  (** An untrusted compartment found by name with the export [e] is in
      the list: the default compartment has no export. *)
  Lemma fw_cmpt_of_untrusted (l : list fw_cmpt) (n e : string) ub k :
    fc_body (fw_cmpt_of l n) = UntrustedBody ub →
    fw_index_of ue_name e (ub_exports ub) = Some k →
    fw_cmpt_of l n ∈ l ∧ fc_name (fw_cmpt_of l n) = n.
  Proof.
    induction l as [|fc l IH]; cbn.
    { intros Hbody Hk. injection Hbody as <-. discriminate Hk. }
    destruct (String.eqb_spec n (fc_name fc)) as [->|Hne]; intros Hbody Hk.
    - split; [apply list_elem_of_here | done].
    - destruct (IH Hbody Hk) as [Hin Hname]. split; [by apply list_elem_of_further | done].
  Qed.

  (** The layout conditions of a thread; it starts in a compartment of the
      firmware. *)
  Lemma thread_wf_inv fw img i ft :
    thread_wf fw img i ft →
    fw_cmpt_of (fw_cmpts fw) (ft_cmpt ft) ∈ fw_cmpts fw ∧
    fc_name (fw_cmpt_of (fw_cmpts fw) (ft_cmpt ft)) = ft_cmpt ft ∧
    (b_stack (thread_of img i) + Z.of_nat (ft_stack_size ft))%a = Some (e_stack (thread_of img i)) ∧
    (b_trusted_stack (thread_of img i) + tstack_frame_offset (S (ft_tstack_frames ft)))%a =
      Some (e_trusted_stack (thread_of img i)) ∧
    range_ok (b_stack (thread_of img i)) (e_stack (thread_of img i)) ∧
    range_ok (b_trusted_stack (thread_of img i)) (e_trusted_stack (thread_of img i)) ∧
    (b_trusted_stack (thread_of img i) : Z) ≠ 0.
  Proof.
    rewrite /thread_wf /thread_layout_ok /section /note.
    destruct (fc_body (fw_cmpt_of (fw_cmpts fw) (ft_cmpt ft))) as [tb|ub] eqn:Hbody.
    - destruct (fw_find_export (ft_entry ft) (tb_exports tb)); last done.
      intros (Hstack & Htstack & Hrange_stack & Hrange_tstack & Htstack_nonzero & _).
      destruct (fw_cmpt_of_trusted _ _ _ Hbody) as [Hin Hname].
      by split_and!.
    - destruct (fw_index_of ue_name (ft_entry ft) (ub_exports ub)) as [k|] eqn:Hk; last done.
      intros (Hstack & Htstack & Hrange_stack & Hrange_tstack & Htstack_nonzero & _).
      destruct (fw_cmpt_of_untrusted _ _ _ _ _ Hbody Hk) as [Hin Hname].
      by split_and!.
  Qed.

  (** The hazard slots of a thread. *)
  Lemma thread_wf_hazard fw img i ft :
    thread_wf fw img i ft →
    (b_hazard (thread_of img i) + 2)%a = Some (e_hazard (thread_of img i)) ∧
    range_ok (b_hazard (thread_of img i)) (e_hazard (thread_of img i)).
  Proof.
    rewrite /thread_wf /thread_layout_ok /section /note.
    destruct (fc_body (fw_cmpt_of (fw_cmpts fw) (ft_cmpt ft))) as [tb|ub].
    - destruct (fw_find_export (ft_entry ft) (tb_exports tb)); last done.
      intros (_ & _ & _ & _ & _ & _ & Hsize & Hrange). by split.
    - destruct (fw_index_of ue_name (ft_entry ft) (ub_exports ub)); last done.
      intros (_ & _ & _ & _ & _ & _ & Hsize & Hrange). by split.
  Qed.

  (** The capability to the hazard slots of a thread. *)
  Lemma thread_hazard_word fw img i ft :
    thread_wf fw img i ft →
    let t := thread_of img i in
    trusted_stack_word (WCap true WO Global (b_hazard t) (e_hazard t) (b_hazard t)).
  Proof.
    intros Hthread t.
    destruct (thread_wf_hazard _ _ _ _ Hthread) as (_ & [ [_ Hhz_heap] _]).
    by apply trusted_stack_word_cap.
  Qed.

  (** The words of the entry frame of a thread: its stack and the export
      table of its compartment lie outside the heap. *)
  Lemma thread_entry_frame_words fw img i ft :
    Forall (cmpt_wf fw img) (fw_cmpts fw) →
    thread_wf fw img i ft →
    let t := thread_of img i in
    let c := cmpt_of img (ft_cmpt ft) in
    trusted_stack_word (WCap true RWL Local (b_stack t) (e_stack t) (stk_start_a (b_stack t) (e_stack t))) ∧
    trusted_stack_word
      (WCap true RW Global (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c) (cmpt_exp_tbl_pcc c)) ∧
    exp_tbl_cap (cmpt_exp_tbl_pcc c)
      (WCap true RW Global (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c) (cmpt_exp_tbl_pcc c)).
  Proof.
    intros Hcmpts Hthread t c.
    destruct (thread_wf_inv _ _ _ _ Hthread) as (Hin & Hname & _ & _ & Hrange_stack & _).
    rewrite Forall_forall in Hcmpts.
    destruct (cmpt_wf_split _ _ _ (Hcmpts _ Hin))
      as (_ & _ & _ & _ & _ & Hheader & Hentries & Hranges & _).
    rewrite /cmpt_ranges Forall_cons Forall_cons Forall_cons Forall_singleton Hname in Hranges.
    rewrite Hname in Hheader Hentries.
    destruct Hranges as (_ & _ & _ & [ [_ Hexp_heap] [Hexp_shadow _] ]).
    destruct Hrange_stack as [ [_ Hstack_heap] _].
    split_and!; [by apply trusted_stack_word_cap.. |].
    subst t c. eexists _, _, _, _. split_and!; [done | done | solve_addr | done | done | done].
  Qed.

  (** The words of the trusted stack of a thread. *)
  Lemma thread_tstack_words fw img i ft :
    Forall (cmpt_wf fw img) (fw_cmpts fw) →
    thread_wf fw img i ft →
    Forall trusted_stack_word (fw_tstack_content img i ft).
  Proof.
    intros Hcmpts Hthread.
    destruct (thread_entry_frame_words _ _ _ _ Hcmpts Hthread) as (Hcsp & Hexport_table & _).
    apply initial_trusted_stack_content_words;
      [done | done | exact (thread_hazard_word _ _ _ _ Hthread)].
  Qed.

  Lemma img_wf_otypes fw img :
    img_wf fw img →
    NoDup (ot_switcher (img_sw img) :: fw_otypes fw) ∧
    Forall otype_valid (ot_switcher (img_sw img) :: fw_otypes fw).
  Proof.
    intros (_ & _ & _ & _ & Himg).
    rewrite /section in Himg. apply big_and_fw_app in Himg as [Himg _].
    apply big_and_cons in Himg as [_ Himg]. apply big_and_cons in Himg as [Hnodup Hvalid].
    split; [exact Hnodup | exact Hvalid].
  Qed.

  Lemma img_wf_heap_roots fw img :
    img_wf fw img → ∀ a, a ∈ fw_set (fw_heap_roots fw) → is_heap_address a = true.
  Proof.
    intros (_ & _ & _ & _ & Himg) a Ha.
    rewrite /section in Himg. apply big_and_fw_app in Himg as [_ Hroots].
    apply big_and_fw_app in Hroots as [Hroots _].
    apply big_and_fw_map in Hroots. rewrite Forall_forall in Hroots. apply Hroots.
    assert (∀ l : list Addr, fw_set l = list_to_set l) as Hset.
    { intros l. induction l as [|x l IH]; first done.
      destruct l as [|y l]; cbn; first set_solver.
      cbn in IH. by rewrite IH. }
    by rewrite Hset elem_of_list_to_set in Ha.
  Qed.

  (** The conditions on the machine of a firmware with heap roots. *)
  Lemma img_wf_heap_machine fw img :
    img_wf fw img →
    fw_heap_roots fw ≠ [] →
    (∀ a, heap_to_shadow a = translate_region heap_b heap_e shadow_b a) ∧
    (revoker_addr < revoker_addr ^+ 1)%a.
  Proof.
    intros (_ & _ & _ & _ & Himg) Hroots.
    rewrite /section in Himg. apply big_and_fw_app in Himg as [_ Hm].
    apply big_and_fw_app in Hm as [_ Hm].
    destruct (fw_heap_roots fw) as [|r rs]; first done.
    exact Hm.
  Qed.

  Lemma img_wf_assert_layout fw img : img_wf fw img → img_assert_layout (img_asrt img).
  Proof.
    intros Hwf. pose proof (img_wf_rngs_disjoint _ _ Hwf) as Hdisj.
    destruct Hwf as (_ & Hasrt & _).
    destruct Hasrt as (Hcode & Hcap & [flag' Hflag] & Hrange & Hend & Hrange_flag).
    split.
    - exact Hcode.
    - exact Hcap.
    - rewrite Hflag. f_equal. solve_addr.
    - apply (proj1 (range_ok_not_heap _ _ Hrange)).
    - apply (addr_disjoint_list_lookup _ 1 2 _ _ Hdisj); [done | done | lia].
    - by apply range_ok_mmio.
    - by apply range_ok_mmio.
    - exact Hend.
  Qed.

  Lemma img_wf_trusted_stack_layout fw img ft fts :
    fw_threads fw = ft :: fts →
    img_wf fw img →
    trusted_stack_layout (b_trusted_stack (thread_of img 0)) (e_trusted_stack (thread_of img 0))
      (b_hazard (thread_of img 0)) (e_hazard (thread_of img 0))
      (fw_tstack_content img 0 ft).
  Proof.
    intros Hthreads (_ & _ & Hcmpts & Hthread & _).
    apply big_and_fw_map in Hcmpts.
    rewrite Hthreads in Hthread. apply big_and_cons in Hthread as [Hthread _].
    destruct (thread_entry_frame_words _ _ _ _ Hcmpts Hthread)
      as (Hcsp & Hexport_table & _).
    destruct (thread_wf_inv _ _ _ _ Hthread) as (_ & _ & _ & Htstack & _).
    apply initial_trusted_stack_layout;
      [done | done | done | exact (thread_hazard_word _ _ _ _ Hthread)].
  Qed.

  Lemma img_wf_switcher_layout fw img ft fts :
    fw_threads fw = ft :: fts →
    img_wf fw img →
    img_switcher_layout (img_sw img) (thread_of img 0) (replicate (ft_stack_size ft) (WInt 0)).
  Proof.
    intros Hthreads Hwf.
    pose proof (img_wf_rngs_disjoint _ _ Hwf) as Hdisj.
    destruct (img_wf_otypes _ _ Hwf) as [_ Hvalid].
    destruct Hwf as (Hsw & _ & _ & Hthread & _).
    rewrite Hthreads in Hthread. apply big_and_cons in Hthread as [Hthread _].
    destruct Hsw as (Hcall & Hsize & Hret & Hrange & Hend).
    destruct (thread_wf_inv _ _ _ _ Hthread)
      as (_ & _ & Hstack & Htstack & Hrange_stack & Hrange_tstack & Htstack_nonzero).
    destruct (thread_wf_hazard _ _ _ _ Hthread) as (Hhazard & Hrange_hazard).
    assert (rngs_disjoint
      [("switcher", b_switcher (img_sw img), e_switcher (img_sw img));
       ("thread 0, trusted stack",
         b_trusted_stack (thread_of img 0), e_trusted_stack (thread_of img 0));
       ("thread 0, stack", b_stack (thread_of img 0), e_stack (thread_of img 0));
       ("thread 0, hazard slots", b_hazard (thread_of img 0), e_hazard (thread_of img 0))])
      as Hdisj3.
    { eapply rngs_disjoint_sublist; last exact Hdisj.
      rewrite /fw_ranges Hthreads /=.
      apply sublist_skip, sublist_cons, sublist_cons, sublist_inserts_l. cbn.
      apply sublist_skip, sublist_skip, sublist_skip, sublist_nil_l. }
    split.
    - exact Hsize.
    - exact Hcall.
    - exact Hret.
    - exact (Forall_inv Hvalid).
    - by rewrite length_replicate.
    - split_and!;
        [ apply (addr_disjoint_list_lookup _ 0 1 _ _ Hdisj3)
        | apply (addr_disjoint_list_lookup _ 0 2 _ _ Hdisj3)
        | apply (addr_disjoint_list_lookup _ 1 2 _ _ Hdisj3)]; try done; lia.
    - by apply range_ok_mmio.
    - apply (disjoint_from_shadow_not_in (b_switcher (img_sw img)) (e_switcher (img_sw img))).
      + by destruct Hrange as (_ & Hsh & _).
      + apply withinBounds_true_iff. solve_addr.
    - by apply range_ok_not_heap.
    - by apply range_ok_mmio.
    - by destruct Hrange_stack as [ [_ Hheap] _].
    - by apply range_ok_mmio.
    - exact Hend.
    - destruct Hrange_tstack as [ [Hbase Hheap] _]. split; first done.
      eapply disjoint_from_heap_shrink; last exact Hheap.
      rewrite /tstack_frame_offset /TrustedStack_offset_frames /TrustedStackFrame_size
        /TSTACK_REGFRAME_SZ /TSTACK_HEADER_SZ in Htstack.
      rewrite /TSTACK_REGFRAME_SZ. solve_addr.
    - exact Htstack_nonzero.
    - exact Hhazard.
    - split_and!;
        [ apply (addr_disjoint_list_lookup _ 3 0 _ _ Hdisj3)
        | apply (addr_disjoint_list_lookup _ 3 1 _ _ Hdisj3)
        | apply (addr_disjoint_list_lookup _ 3 2 _ _ Hdisj3)]; try done; lia.
    - by apply range_ok_mmio.
    - by apply range_ok_not_heap.
  Qed.

  Lemma img_wf_cmpt_layout fw img fc :
    img_wf fw img → fc ∈ fw_cmpts fw → img_cmpt_layout (cmpt_of img (fc_name fc)).
  Proof.
    intros Hwf Hin. pose proof (img_wf_rngs_disjoint _ _ Hwf) as Hdisj.
    destruct Hwf as (_ & _ & Hcmpts & _).
    apply big_and_fw_map in Hcmpts. rewrite Forall_forall in Hcmpts.
    destruct (cmpt_wf_split _ _ _ (Hcmpts fc Hin))
      as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hranges & Hend & _).
    assert (rngs_disjoint (cmpt_ranges img fc)) as Hdisj4.
    { eapply rngs_disjoint_sublist; last exact Hdisj.
      rewrite /fw_ranges. do 3 apply sublist_cons.
      apply sublist_inserts_r. by apply cmpt_ranges_sublist. }
    rewrite /cmpt_ranges Forall_cons Forall_cons Forall_cons Forall_singleton in Hranges.
    destruct Hranges as (Hr1 & Hr2 & Hr3 & Hr4).
    split; try done.
    all: first [ by apply range_ok_mmio | by apply range_ok_not_heap ].
  Qed.
End layout_of_img_wf.

(** ** The threads and their initial registers *)
Section entry.
  Context `{MP : MachineParameters}.

  Definition fw_thread0 (fw : firmware) : fw_thread :=
    match fw_threads fw with [] => MkFwThread "" "" 0 0 | ft :: _ => ft end.

  (** The thread [i] of a firmware. *)
  Definition fw_thread_of (fw : firmware) (i : nat) : fw_thread :=
    fw_nth i (fw_threads fw) (MkFwThread "" "" 0 0).

  Lemma fw_thread_of_0 fw : fw_thread_of fw 0 = fw_thread0 fw.
  Proof. rewrite /fw_thread_of /fw_thread0. by destruct (fw_threads fw). Qed.

  (** The compartment the thread [i] starts in. *)
  Definition fw_entry_fc (fw : firmware) (i : nat) : fw_cmpt :=
    fw_cmpt_of (fw_cmpts fw) (ft_cmpt (fw_thread_of fw i)).

  (** The offset of the export the thread [i] starts at, for a trusted
      compartment (the PC of an untrusted entry is [fw_entry_pc]'s). *)
  Definition fw_entry_offset (fw : firmware) (i : nat) : nat :=
    match fc_body (fw_entry_fc fw i) with
    | TrustedBody b => fe_offset (fw_export_named (ft_entry (fw_thread_of fw i)) (tb_exports b))
    | UntrustedBody _ => 0
    end.

  (** The minimum stack size of the export the thread [i] starts at, for a
      trusted compartment; an untrusted entry's is in its entry word
      ([thread_wf]), which the obligations do not use. *)
  Definition fw_entry_min_stack (fw : firmware) (i : nat) : nat :=
    match fc_body (fw_entry_fc fw i) with
    | TrustedBody b => fe_min_stack (fw_export_named (ft_entry (fw_thread_of fw i)) (tb_exports b))
    | UntrustedBody _ => 0
    end.

  (** The stack of a thread holds the minimum stack size of its entry plus
      the reserved space. *)
  Lemma thread_wf_min_stack fw img i :
    thread_wf fw img i (fw_thread_of fw i) →
    (b_stack (thread_of img i) + Z.of_nat (fw_entry_min_stack fw i) + StackEntry_reserved_space <=
       e_stack (thread_of img i))%Z.
  Proof.
    rewrite /thread_wf /thread_layout_ok /fw_entry_min_stack /fw_entry_fc /section /note.
    destruct (fc_body (fw_cmpt_of (fw_cmpts fw) (ft_cmpt (fw_thread_of fw i)))) as [tb|ub].
    - rewrite /fw_export_named.
      destruct (fw_find_export (ft_entry (fw_thread_of fw i)) (tb_exports tb)) as [e|]; last done.
      intros (Hstack & _ & _ & _ & _ & Hmin & _).
      solve_addr+Hstack Hmin.
    - destruct (fw_index_of ue_name (ft_entry (fw_thread_of fw i)) (ub_exports ub)); last done.
      intros (Hstack & _ & _ & _ & _ & (z & _ & Hmin) & _).
      assert (0 ≤ export_entry_min_stack z)%Z as Hz.
      { rewrite /export_entry_min_stack /ExportEntry_byte_mask.
        apply Z.land_nonneg; right; lia. }
      cbn. solve_addr+Hstack Hmin Hz.
  Qed.

  Definition fw_entry_cmpt (fw : firmware) (img : fw_image) (i : nat) : img_cmpt :=
    cmpt_of img (ft_cmpt (fw_thread_of fw i)).

  (** The entry word, in the image's export table, of the export of an
      untrusted compartment that the thread [i] starts at, as an integer
      (0 if it is not one). *)
  Definition fw_entry_word (fw : firmware) (img : fw_image) (i : nat) : Z :=
    match fc_body (fw_entry_fc fw i) with
    | UntrustedBody b =>
        match fw_index_of ue_name (ft_entry (fw_thread_of fw i)) (ub_exports b) with
        | Some k =>
            match cmpt_exp_tbl_entries (fw_entry_cmpt fw img i) !! k with
            | Some (WInt z) => z
            | _ => 0%Z
            end
        | None => 0%Z
        end
    | TrustedBody _ => 0%Z
    end.

  (** The PC of the thread [i]: the PCC of its compartment at the offset of
      its entry, the firmware's for a trusted compartment, and the one
      its entry word encodes for an untrusted one. *)
  Definition fw_entry_pc (fw : firmware) (img : fw_image) (i : nat) : Word :=
    let m := fw_entry_cmpt fw img i in
    WCap true RX Global (cmpt_b_pcc m) (cmpt_e_pcc m)
      (match fc_body (fw_entry_fc fw i) with
       | TrustedBody _ => addr_off (cmpt_b_pcc m) (fw_entry_offset fw i)
       | UntrustedBody _ => (cmpt_b_pcc m ^+ export_entry_offset (fw_entry_word fw img i))%a
       end).

  Definition fw_entry_cgp (fw : firmware) (img : fw_image) (i : nat) : Word :=
    let m := fw_entry_cmpt fw img i in
    WCap true RW Global (cmpt_b_cgp m) (cmpt_e_cgp m) (cmpt_b_cgp m).

  Definition fw_thread_csp (img : fw_image) (i : nat) : Word :=
    let t := thread_of img i in
    WCap true RWL Local (b_stack t) (e_stack t) (stk_start_a (b_stack t) (e_stack t)).

  (** The capability to the export table of the compartment the thread [i]
      starts in, as its entry frame holds it. *)
  Definition fw_entry_tbl (fw : firmware) (img : fw_image) (i : nat) : Word :=
    let c := fw_entry_cmpt fw img i in
    WCap true RW Global (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c) (cmpt_exp_tbl_pcc c).

  (** The entry frame of the thread [i]: its stack pointer, the export table
      of the compartment it starts in, and no error handler invocation. *)
  Definition fw_entry_frame (fw : firmware) (img : fw_image) (i : nat) : trusted_frame :=
    {| tf_csp := lword_of_word (fw_thread_csp img i);
       tf_export_tbl := lword_of_word (fw_entry_tbl fw img i);
       tf_error_count := 0 |}.

  Definition fw_thread_mtdc (img : fw_image) : Word :=
    let t := thread_of img 0 in
    WCap true RWL Global (b_trusted_stack t) (e_trusted_stack t) (b_trusted_stack t).

  (** The trap vector: the exception entry of the switcher. *)
  Definition fw_mtcc (img : fw_image) : Word :=
    let sw := img_sw img in
    WCap true XSRW_ Local (b_switcher sw) (e_switcher sw)
      (a_switcher_call sw ^+
         assembler.Asm_Griotte.label_offset_from (concat switcher_asm)
           ".Lswitch_csp_check" "exception_entry_asm")%a.

  (** The return sentry the loader gives the thread in [cra]: into the
      switcher, at [switcher_after_compartment_call], interrupts disabled. *)
  Definition fw_thread_cra (img : fw_image) : Word :=
    let sw := img_sw img in
    WSentry RetDisable true XSRW_ Local (b_switcher sw) (e_switcher sw) (a_switcher_return sw).

  Definition fw_trap_vector (img : fw_image) : trapVector :=
    {| mtcc_vec := fw_mtcc img; mtcc_vec_tagged := eq_refl |}.

  Definition fw_initial_sreg (img : fw_image) (sr : SRegName) : Word :=
    match sr with
    | MTDC => fw_thread_mtdc img
    | MSTATUS => WInt (mstatus_enc InterruptDisabled InterruptDisabled)
    | MTCC => fw_mtcc img
    | MEPCC | MCAUSE | MTVAL => WInt 0
    end.

  Lemma regs_ok_inv fw img σ :
    regs_ok fw img σ →
    (∃ fts, fw_threads fw = fw_thread0 fw :: fts) ∧
    fw_entry_fc fw 0 ∈ fw_cmpts fw ∧
    fc_name (fw_entry_fc fw 0) = ft_cmpt (fw_thread0 fw) ∧
    pcc σ = fw_entry_pc fw img 0 ∧
    reg σ !! cgp = Some (fw_entry_cgp fw img 0) ∧
    reg σ !! csp = Some (fw_thread_csp img 0) ∧
    reg σ !! cra = Some (fw_thread_cra img) ∧
    (∀ r, r ∉ ({[cgp; cra; csp]} : gset RegName) → reg σ !! r = Some (WInt 0)) ∧
    (∀ sr, sreg σ !! sr = Some (fw_initial_sreg img sr)).
  Proof.
    rewrite /regs_ok /note /fw_entry_pc /fw_entry_cgp /fw_entry_offset /fw_entry_word
      /fw_entry_fc /fw_entry_cmpt fw_thread_of_0 /fw_thread0.
    destruct (fw_threads fw) as [|ft fts]; first done.
    intros (Hpc & Hcgp & Hcsp & Hcra & Hregs & Hmtdc & Hmstatus & Hmtcc & Hmepcc & Hmcause
            & Hmtval).
    destruct (fc_body (fw_cmpt_of (fw_cmpts fw) (ft_cmpt ft))) as [tb|ub] eqn:Hbody.
    - destruct (fw_cmpt_of_trusted _ _ _ Hbody) as [Hin Hname].
      split_and!; [by exists fts | done..|].
      intros sr. by destruct sr.
    - destruct (fw_index_of ue_name (ft_entry ft) (ub_exports ub)) as [k|] eqn:Hk;
        last by destruct Hpc.
      destruct Hpc as (z & Hz & Hpc).
      destruct (fw_cmpt_of_untrusted _ _ _ _ _ Hbody Hk) as [Hin Hname].
      split_and!; [by exists fts | done | done | by rewrite Hpc Hz /= | done..|].
      intros sr. by destruct sr.
  Qed.
End entry.

(** ** The initial memory of an image *)
Section initial_memory.
  Context `{MP : MachineParameters}.

  Lemma mem_rooted_mem_region H b ws :
    Forall (word_rooted H) ws → mem_rooted H (mem_region b ws).
  Proof.
    intros Hws a w Ha. apply elem_of_list_to_map_2, elem_of_zip_r in Ha.
    by eapply Forall_forall.
  Qed.

  Lemma mem_exec_ok_mem_region b ws :
    Forall word_exec_ok ws → mem_exec_ok (mem_region b ws).
  Proof.
    intros Hws a w Ha. apply elem_of_list_to_map_2, elem_of_zip_r in Ha.
    by eapply Forall_forall.
  Qed.

  Lemma mem_in_avoids_mmio m ts :
    mem_in m ts → Forall (λ t, range_ok t.1.2 t.2) ts → mem_avoids_mmio m.
  Proof.
    intros Hm Hts a Ha. destruct (Hm a Ha) as (t & Ht & Hat).
    rewrite Forall_forall in Hts. destruct (Hts t Ht) as (_ & Hsh & Hrev).
    apply (disjoint_from_mmio_not_in t.1.2 t.2); first by split.
    by apply withinBounds_true_iff, elem_of_finz_seq_between.
  Qed.

  Lemma mem_in_disjoint_sub m1 m2 ts1 ts2 ts :
    mem_in m1 ts1 →
    mem_in m2 ts2 →
    (ts1 ++ ts2) `sublist_of` ts →
    rngs_disjoint ts →
    m1 ##ₘ m2.
  Proof.
    intros H1 H2 Hsub Hdisj. eapply mem_in_disjoint; [exact H1 | exact H2 |].
    intros t1 t2 Ht1 Ht2. eapply rngs_disjoint_app_cross; [|exact Ht1|exact Ht2].
    by eapply rngs_disjoint_sublist.
  Qed.

  (** *** The memory of each part of an image lies in its ranges *)

  Lemma switcher_mem_in img :
    switcher_wf img →
    mem_in (switcher_mem img) [("switcher", b_switcher (img_sw img), e_switcher (img_sw img))].
  Proof.
    intros (Hcall & Hsize & _). apply mem_in_mem_region.
    change (length (?w :: ?ws)) with (S (length ws)). solve_addr.
  Qed.

  Lemma assert_code_mem_in img :
    assert_wf img →
    mem_in (assert_code_mem img) [("assert", b_assert (img_asrt img), e_assert (img_asrt img))].
  Proof.
    intros (Hcode & Hcap & _). apply mem_in_mem_region.
    rewrite length_app /=. solve_addr.
  Qed.

  Lemma assert_flag_mem_in img :
    assert_wf img →
    mem_in (assert_flag_mem img)
      [("assert flag", flag_assert (img_asrt img), (flag_assert (img_asrt img) ^+ 1)%a)].
  Proof.
    intros (_ & _ & [flag' Hflag] & _). apply mem_in_mem_region.
    cbn. rewrite Hflag. f_equal. solve_addr.
  Qed.

  Lemma cmpt_mem_in fw img fc :
    cmpt_wf fw img fc → mem_in (cmpt_mem img fc) (cmpt_ranges img fc).
  Proof.
    intros Hwf. destruct (cmpt_wf_split _ _ _ Hwf) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
    rewrite /cmpt_mem /cmpt_ranges /note.
    change [?t1; ?t2; ?t3; ?t4] with ((([t1] ++ [t2]) ++ [t3]) ++ [t4]).
    repeat apply mem_in_union; apply mem_in_mem_region.
    - rewrite length_app. solve_addr.
    - done.
    - done.
    - change (length (?w1 :: ?w2 :: ?ws)) with (S (S (length ws))). solve_addr.
  Qed.

  Lemma cmpts_mem_in fw img (fcs : list fw_cmpt) :
    Forall (cmpt_wf fw img) fcs →
    mem_in (big_union (fw_map (cmpt_mem img) fcs)) (fw_flat_map (cmpt_ranges img) fcs).
  Proof.
    induction fcs as [|fc fcs IH]; intros Hwf; first apply mem_in_empty.
    apply Forall_cons in Hwf as [Hfc Hwf].
    rewrite fw_flat_map_cons. cbn [fw_map]. rewrite big_union_cons.
    apply mem_in_union; [by eapply cmpt_mem_in | by apply IH].
  Qed.

  Lemma thread_mem_in fw img i ft :
    thread_wf fw img i ft → mem_in (thread_mem img i ft) (thread_ranges img i ft).
  Proof.
    intros Hthread. destruct (thread_wf_inv _ _ _ _ Hthread) as (_ & _ & Hstack & Htstack & _).
    destruct (thread_wf_hazard _ _ _ _ Hthread) as (Hhazard & _).
    rewrite /thread_mem /thread_ranges /note.
    change [?t1; ?t2; ?t3] with (([t1] ++ [t2]) ++ [t3]).
    apply mem_in_union; first apply mem_in_union; apply mem_in_mem_region;
      [by rewrite initial_trusted_stack_content_length | by rewrite length_replicate | done].
  Qed.

  Lemma threads_mem_in fw img k (fts : list fw_thread) :
    big_and (fw_imap_from (thread_wf fw img) k fts) →
    mem_in (big_union (fw_imap_from (thread_mem img) k fts))
      (fw_flat_map (λ x, x) (fw_imap_from (thread_ranges img) k fts)).
  Proof.
    revert k. induction fts as [|ft fts IH]; intros k Hwf; first apply mem_in_empty.
    cbn [fw_imap_from]. apply big_and_cons in Hwf as [Hft Hwf].
    rewrite fw_flat_map_cons big_union_cons.
    apply mem_in_union; [by eapply thread_mem_in | by apply IH].
  Qed.
End initial_memory.

Section initial_memory_wf.
  Context `{MP : MachineParameters}.

  Lemma Forall_fw_flat_map {A B} (P : B → Prop) (f : A → list B) (l : list A) :
    Forall (λ x, Forall P (f x)) l → Forall P (fw_flat_map f l).
  Proof.
    induction l as [|x l IH]; intros Hl; first constructor.
    apply Forall_cons in Hl as [Hx Hl]. rewrite fw_flat_map_cons.
    apply Forall_app; split; [done | by apply IH].
  Qed.

  Lemma threads_ranges_ok fw img k (fts : list fw_thread) :
    big_and (fw_imap_from (thread_wf fw img) k fts) →
    Forall (λ t, range_ok t.1.2 t.2)
      (fw_flat_map (λ x, x) (fw_imap_from (thread_ranges img) k fts)).
  Proof.
    revert k. induction fts as [|ft fts IH]; intros k Hwf; first constructor.
    cbn [fw_imap_from]. apply big_and_cons in Hwf as [Hft Hwf].
    rewrite fw_flat_map_cons. apply Forall_app; split; last by apply IH.
    destruct (thread_wf_inv _ _ _ _ Hft) as (_ & _ & _ & _ & Hstack & Htstack & _).
    destruct (thread_wf_hazard _ _ _ _ Hft) as (_ & Hhazard).
    rewrite /thread_ranges.
    apply Forall_cons; split; first exact Htstack.
    apply Forall_cons; split; first exact Hstack.
    apply Forall_singleton. exact Hhazard.
  Qed.

  Lemma img_wf_ranges_ok fw img :
    img_wf fw img → Forall (λ t, range_ok t.1.2 t.2) (fw_ranges fw img).
  Proof.
    intros (Hsw & Hasrt & Hcmpts & Hthreads & _).
    destruct Hsw as (_ & _ & _ & Hsw & _).
    destruct Hasrt as (_ & _ & _ & Hasrt & _ & Hflag).
    repeat apply Forall_cons_2; [done..|].
    apply Forall_app; split.
    - apply Forall_fw_flat_map. apply big_and_fw_map in Hcmpts.
      eapply Forall_impl; first exact Hcmpts.
      intros fc Hfc. by destruct (cmpt_wf_split _ _ _ Hfc) as (_ & _ & _ & _ & _ & _ & _ & Hok & _).
    - by apply (threads_ranges_ok fw).
  Qed.
End initial_memory_wf.

(** ** The initial condition of the ghost state *)
Section ghost_init.
  Context `{MP : MachineParameters}.

  Lemma mem_rooted_big_union H (ms : list Mem) :
    Forall (mem_rooted H) ms → mem_rooted H (big_union ms).
  Proof.
    induction ms as [|m ms IH]; intros Hms.
    - intros a w Ha. by rewrite lookup_empty in Ha.
    - apply Forall_cons in Hms as [Hm Hms]. rewrite big_union_cons.
      apply mem_rooted_union; [done | by apply IH].
  Qed.

  Lemma mem_exec_ok_big_union (ms : list Mem) :
    Forall mem_exec_ok ms → mem_exec_ok (big_union ms).
  Proof.
    induction ms as [|m ms IH]; intros Hms.
    - intros a w Ha. by rewrite lookup_empty in Ha.
    - apply Forall_cons in Hms as [Hm Hms]. rewrite big_union_cons.
      apply mem_exec_ok_union; [done | by apply IH].
  Qed.

  (** The error handler offsets of a compartment are integers. *)
  Lemma cmpt_ok_handlers fw img fc :
    cmpt_ok fw img fc →
    let c := cmpt_of img (fc_name fc) in
    ∃ eh ehs : Z,
      cmpt_exp_tbl_handler c = WInt eh ∧ cmpt_exp_tbl_handler_stackless c = WInt ehs.
  Proof.
    rewrite /cmpt_ok /section. destruct (fc_unknown_export fw fc); first done.
    intros (_ & _ & Hbody). rewrite /body_ok /note in Hbody.
    destruct (fc_body fc) as [tb|ub].
    - destruct Hbody as (_ & _ & Hh & _).
      destruct (tb_error_handler tb), (tb_error_handler_stackless tb);
        destruct Hh as [Heh Hehs]; by eexists _, _.
    - by destruct Hbody as (_ & _ & Hh & _).
  Qed.

  Lemma cmpt_mem_rooted_exec_ok fw img fc :
    cmpt_ok fw img fc →
    cmpt_wf fw img fc →
    mem_rooted (fw_set (fw_heap_roots fw)) (cmpt_mem img fc) ∧ mem_exec_ok (cmpt_mem img fc).
  Proof.
    intros Hok Hwf.
    destruct (cmpt_ok_handlers _ _ _ Hok) as (eh & ehs & Heh & Hehs).
    destruct (cmpt_wf_split _ _ _ Hwf) as (_ & _ & _ & _ & _ & _ & _ & Hranges & Hend & Hrooted & Hexec).
    rewrite /cmpt_ranges Forall_cons Forall_cons Forall_cons Forall_singleton in Hranges.
    destruct Hranges as ([ [Hpcc Hpcc_heap] _] & [ [Hcgp _] _] & _ & _).
    rewrite /img_cmpt_words !Forall_app in Hrooted Hexec.
    destruct Hrooted as (Hr1 & Hr2 & Hr3 & Hr4 & Hr5).
    destruct Hexec as (He1 & He2 & He3 & He4 & He5).
    rewrite /cmpt_mem /note. split.
    - repeat apply mem_rooted_union; apply mem_rooted_mem_region; try done.
      + by apply Forall_app.
      + apply Forall_cons; split; first by apply word_rooted_cap_nonheap.
        apply Forall_cons; split; first by apply word_rooted_cap_nonheap.
        rewrite Heh Hehs.
        do 2 (apply Forall_cons; split; first apply word_rooted_int).
        done.
    - repeat apply mem_exec_ok_union; apply mem_exec_ok_mem_region; try done.
      + by apply Forall_app.
      + apply Forall_cons; split.
        { eapply word_exec_ok_closed; [done | by split | done]. }
        apply Forall_cons; split; first by apply word_exec_ok_not_executable.
        rewrite Heh Hehs.
        do 2 (apply Forall_cons; split; first apply word_exec_ok_int).
        done.
  Qed.

  Lemma thread_mem_rooted_exec_ok H fw img i ft :
    Forall (cmpt_wf fw img) (fw_cmpts fw) →
    thread_wf fw img i ft →
    mem_rooted H (thread_mem img i ft) ∧ mem_exec_ok (thread_mem img i ft).
  Proof.
    intros Hcmpts Hthread.
    pose proof (thread_tstack_words _ _ _ _ Hcmpts Hthread) as Hts.
    assert (Forall is_z (replicate (ft_stack_size ft) (WInt 0))) as Hs.
    { by apply Forall_replicate. }
    assert (Forall is_z [WInt 0; WInt 0]) as Hhz by repeat constructor.
    rewrite /thread_mem /note. split.
    - apply mem_rooted_union; first apply mem_rooted_union;
        apply mem_rooted_mem_region; try by apply word_rooted_ints.
      eapply Forall_impl; first exact Hts. apply word_rooted_trusted_stack_word.
    - apply mem_exec_ok_union; first apply mem_exec_ok_union;
        apply mem_exec_ok_mem_region; try by apply word_exec_ok_ints.
      eapply Forall_impl; first exact Hts. apply word_exec_ok_trusted_stack_word.
  Qed.

  Lemma threads_mem_rooted_exec_ok H fw img k (fts : list fw_thread) :
    Forall (cmpt_wf fw img) (fw_cmpts fw) →
    big_and (fw_imap_from (thread_wf fw img) k fts) →
    mem_rooted H (big_union (fw_imap_from (thread_mem img) k fts)) ∧
    mem_exec_ok (big_union (fw_imap_from (thread_mem img) k fts)).
  Proof.
    intros Hcmpts. revert k. induction fts as [|ft fts IH]; intros k Hthreads.
    - split; intros a w Ha; by rewrite lookup_empty in Ha.
    - cbn [fw_imap_from] in Hthreads |- *. rewrite big_union_cons.
      apply big_and_cons in Hthreads as [Hft Hthreads].
      destruct (thread_mem_rooted_exec_ok H fw img k ft Hcmpts Hft) as [Hr He].
      destruct (IH (S k) Hthreads) as [Hr' He'].
      split; [by apply mem_rooted_union | by apply mem_exec_ok_union].
  Qed.

  (** The memory of an image, in the order of [mem_ok], and the ranges of
      its parts. *)
  Lemma firmware_ok_mem_in fw img σ :
    firmware_ok fw img σ →
    mem_in (switcher_mem img ∪ assert_code_mem img ∪ assert_flag_mem img ∪
            big_union (fw_map (cmpt_mem img) (fw_cmpts fw)) ∪
            big_union (fw_imap (thread_mem img) (fw_threads fw)))
      (fw_ranges fw img).
  Proof.
    intros (_ & _ & _ & Hwf).
    destruct Hwf as (Hsw & Hasrt & Hcmpts & Hthreads & _).
    apply big_and_fw_map in Hcmpts.
    eapply mem_in_mono; last first.
    { repeat apply mem_in_union.
      - by apply switcher_mem_in.
      - by apply assert_code_mem_in.
      - by apply assert_flag_mem_in.
      - by apply (cmpts_mem_in fw).
      - by apply (threads_mem_in fw). }
    rewrite /fw_ranges. intros t. rewrite !elem_of_app !elem_of_cons. naive_solver.
  Qed.

  Lemma firmware_ok_ghost_init_cond fw img w_pc regs sregs m sh :
    firmware_ok fw img (w_pc, regs, sregs, m, sh) →
    ghost_init_cond (TV := fw_trap_vector img) (w_pc, regs, sregs, m, sh) (fw_set (fw_heap_roots fw)) ∧
    regs !! cnull = Some (WInt 0).
  Proof.
    intros Hok.
    pose proof (firmware_ok_mem_in _ _ _ Hok) as Hmem_in.
    destruct Hok as (Hcmpts_ok & [Hmem Hsh] & Hregs & Hwf).
    change (mem (w_pc, regs, sregs, m, sh)) with m in Hmem.
    change (shadowtbl (w_pc, regs, sregs, m, sh)) with sh in Hsh.
    rewrite /note in Hmem Hsh. subst m sh.
    destruct (regs_ok_inv _ _ _ Hregs)
      as ([fts Hthreads] & Hentry & Hname & Hpc & Hcgp & Hcsp & Hcra & Hzero & Hsreg).
    clear Hregs.
    change (pcc (w_pc, regs, sregs, _, _)) with w_pc in Hpc.
    change (reg (w_pc, regs, sregs, _, _)) with regs in Hcgp, Hcsp, Hcra, Hzero.
    change (sreg (w_pc, regs, sregs, _, _)) with sregs in Hsreg.
    subst w_pc.
    pose proof (img_wf_cmpt_layout _ _ _ Hwf Hentry) as Hm. rewrite Hname in Hm.
    pose proof (img_wf_switcher_layout _ _ _ _ Hthreads Hwf) as Hsw.
    pose proof (img_wf_heap_roots _ _ Hwf) as Hroots.
    assert (cnull ∉ ({[cgp; cra; csp]} : gset RegName)) as Hcnull by set_solver+.
    split; last by apply Hzero.
    pose proof Hwf as (Hsw_wf & Hasrt_wf & Hcmpts_wf & Hthreads_wf & _).
    pose proof Hsw_wf as (_ & _ & _ & [Hsw_not_heap _] & Hsw_end).
    apply big_and_fw_map in Hcmpts_wf.
    apply big_and_fw_map in Hcmpts_ok.
    assert (Forall (λ fc, cmpt_ok fw img fc ∧ cmpt_wf fw img fc) (fw_cmpts fw)) as Hcmpts_ok_wf.
    { by apply Forall_and. }
    apply ghost_init_cond_roots; first done.
    - (* The memory is rooted. *)
      assert (is_heap_address (flag_assert (img_asrt img)) = false) as Hflag_heap.
      { destruct Hasrt_wf as (_ & _ & [flag' Hflag] & _ & _ & ([_ Hheap] & _)).
        apply (disjoint_from_heap_not_in _ _ _ Hheap), withinBounds_true_iff. solve_addr. }
      apply mem_rooted_union; last by apply (threads_mem_rooted_exec_ok _ fw).
      apply mem_rooted_union.
      2: { apply mem_rooted_big_union. rewrite fw_map_eq. apply Forall_fmap.
           eapply Forall_impl; first exact Hcmpts_ok_wf.
           intros fc [Hfc_ok Hfc]. by destruct (cmpt_mem_rooted_exec_ok _ _ _ Hfc_ok Hfc). }
      apply mem_rooted_union.
      2: { apply mem_rooted_mem_region. apply Forall_singleton. apply word_rooted_int. }
      apply mem_rooted_union.
      2: { apply mem_rooted_mem_region. apply Forall_app; split; first apply word_rooted_instrs.
           apply Forall_singleton. by apply word_rooted_cap_nonheap. }
      apply mem_rooted_union; first apply mem_rooted_initial_heap.
      apply mem_rooted_mem_region.
      do 5 (apply Forall_cons; split; first by apply word_rooted_nonheap).
      rewrite /switcher_instrs. apply Forall_concat, Forall_fmap, Forall_true.
      intros l. apply word_rooted_instrs.
    - apply word_rooted_cap_nonheap. exact (proj1 (icl_pcc_not_heap _ Hm)).
    - intros r w Hr.
      destruct (decide (r = cgp)) as [->|Hne1].
      { rewrite Hcgp in Hr. injection Hr as <-.
        apply word_rooted_cap_nonheap. exact (proj1 (icl_cgp_not_heap _ Hm)). }
      destruct (decide (r = csp)) as [->|Hne2].
      { rewrite Hcsp in Hr. injection Hr as <-.
        apply word_rooted_cap_disjoint. exact (isl_stack_not_heap _ _ _ Hsw). }
      destruct (decide (r = cra)) as [->|Hne3].
      { (* the switcher's return sentry, outside the heap *)
        rewrite Hcra in Hr. injection Hr as <-.
        apply word_rooted_nonheap.
        by rewrite /fw_thread_cra /heap_cap_base /= (proj1 Hsw_not_heap). }
      rewrite Hzero in Hr; last set_solver+Hne1 Hne2 Hne3. injection Hr as <-.
      apply word_rooted_int.
    - assert (disjoint_from_heap (b_trusted_stack (thread_of img 0))
                (e_trusted_stack (thread_of img 0))) as Hts_heap.
      { rewrite Hthreads in Hthreads_wf.
        apply big_and_cons in Hthreads_wf as [Hthread0 _].
        destruct (thread_wf_inv _ _ _ _ Hthread0) as (_ & _ & _ & _ & _ & [ [_ Hheap] _] & _).
        exact Hheap. }
      intros sr w Hw. rewrite Hsreg in Hw. injection Hw as <-.
      destruct sr; try apply word_rooted_int.
      + (* MTCC: the switcher's capability, outside the heap *)
        apply word_rooted_cap_nonheap. exact (proj1 Hsw_not_heap).
      + by apply word_rooted_cap_disjoint.
    - (* The memory avoids the memory-mapped devices. *)
      match goal with |- mem_avoids_mmio (?H ∪ ?S ∪ ?AC ∪ ?AF ∪ ?CM ∪ ?TM) =>
        replace (H ∪ S ∪ AC ∪ AF ∪ CM ∪ TM) with (H ∪ (S ∪ AC ∪ AF ∪ CM ∪ TM))
          by (by rewrite !(assoc_L (∪)))
      end.
      apply mem_avoids_mmio_union; first apply mem_avoids_mmio_initial_heap.
      eapply mem_in_avoids_mmio; first exact Hmem_in.
      by apply img_wf_ranges_ok.
    - (* The memory covers the heap. *)
      repeat apply heap_mapped_union_l. apply heap_mapped_initial_heap.
    - by apply Hzero.
    - (* The executable words of the memory avoid the heap. *)
      apply mem_exec_ok_union;
        last exact (proj2 (threads_mem_rooted_exec_ok ∅ fw img 0 _ Hcmpts_wf Hthreads_wf)).
      apply mem_exec_ok_union.
      2: { apply mem_exec_ok_big_union. rewrite fw_map_eq. apply Forall_fmap.
           eapply Forall_impl; first exact Hcmpts_ok_wf.
           intros fc [Hfc_ok Hfc]. by destruct (cmpt_mem_rooted_exec_ok _ _ _ Hfc_ok Hfc). }
      apply mem_exec_ok_union.
      2: { apply mem_exec_ok_mem_region. apply Forall_singleton. apply word_exec_ok_int. }
      apply mem_exec_ok_union.
      2: { apply mem_exec_ok_mem_region. apply Forall_app; split; first apply word_exec_ok_instrs.
           apply Forall_singleton. by apply word_exec_ok_not_executable. }
      apply mem_exec_ok_union; first apply mem_exec_ok_initial_heap.
      apply mem_exec_ok_mem_region.
      do 5 (apply Forall_cons; split; first by apply word_exec_ok_not_executable).
      rewrite /switcher_instrs. apply Forall_concat, Forall_fmap, Forall_true.
      intros l. apply word_exec_ok_instrs.
    - eapply word_exec_ok_closed;
        [done | exact (icl_pcc_not_heap _ Hm) | exact (icl_pcc_end_not_heap _ Hm)].
    - intros r w Hr.
      destruct (decide (r = cgp)) as [->|Hne1].
      { rewrite Hcgp in Hr. injection Hr as <-. by apply word_exec_ok_not_executable. }
      destruct (decide (r = csp)) as [->|Hne2].
      { rewrite Hcsp in Hr. injection Hr as <-. by apply word_exec_ok_not_executable. }
      destruct (decide (r = cra)) as [->|Hne3].
      { (* the switcher's return sentry, with closed bounds outside the heap *)
        rewrite Hcra in Hr. injection Hr as <-.
        eapply word_exec_ok_closed; [reflexivity | exact Hsw_not_heap | exact Hsw_end]. }
      rewrite Hzero in Hr; last set_solver+Hne1 Hne2 Hne3. injection Hr as <-.
      apply word_exec_ok_int.
    - intros sr w Hw. rewrite Hsreg in Hw. injection Hw as <-.
      destruct sr; try by apply word_exec_ok_not_executable.
      (* MTCC: the switcher's capability, with closed bounds outside the heap *)
      eapply word_exec_ok_closed; [reflexivity | exact Hsw_not_heap | exact Hsw_end].
    - by intros _.
    - intros sr w Hsr Hw. rewrite Hsreg in Hw. injection Hw as <-.
      (* MTCC is an unsealed executable capability *)
      destruct sr; try done; by apply pc_ok_untagged.
    - intros sr _. eexists. apply Hsreg.
    - exact (Hsreg MTCC).
    - exists 0%Z. exact (Hsreg MTVAL).
    - exists InterruptDisabled, InterruptDisabled. exact (Hsreg MSTATUS).
  Qed.
End ghost_init.

(** ** The export entries of an image *)
Section entries.
  Context `{MP : MachineParameters}.

  (** The number of arguments of the exports of a compartment. *)
  Definition fc_export_nargs (fc : fw_cmpt) : list nat :=
    match fc_body fc with
    | TrustedBody b => fw_map fe_nargs (tb_exports b)
    | UntrustedBody b => fw_map ue_nargs (ub_exports b)
    end.

  (** The unsealed capability of export [k] of [c], as in the imports
      ([IExport]). *)
  Definition cmpt_export_sb (c : img_cmpt) (k : nat) : Sealable :=
    SCap true RO Global (cmpt_exp_tbl_pcc c) (cmpt_exp_tbl_entries_end c)
      (cmpt_exp_tbl_pcc c ^+ ExportTable_offset_entry k)%a.
End entries.

Section entries_facts.
  Context `{MP : MachineParameters}.

  Lemma addr_off_eq (a : Addr) (k : nat) : addr_off a k = (a ^+ Z.of_nat k)%a.
  Proof.
    rewrite /addr_off.
    destruct k as [|k]; first (symmetry; apply finz_add_0_default).
    do 15 (destruct k as [|k]; first reflexivity).
    reflexivity.
  Qed.

  Lemma length_fw_imap_from {A B} (f : nat → A → B) k (l : list A) :
    length (fw_imap_from f k l) = length l.
  Proof. revert k. induction l as [|x l IH]; intros k; cbn; [done | by rewrite IH]. Qed.

  Lemma hole_exports_length (c : img_cmpt) (ns : list nat) (k : list Word → Prop) :
    hole_exports c ns k → ∃ ws, length ws = length ns ∧ k ws.
  Proof.
    revert k. induction ns as [|n ns IH]; intros k Hk; cbn in Hk.
    - by exists [].
    - destruct Hk as (off & minstk & _ & Hk). destruct (IH _ Hk) as (ws & Hlen & Hws).
      exists (export_word (MkFwExport "" off n minstk InterruptEnabled) :: ws). by rewrite /= Hlen.
  Qed.

  (** The conditions on a compartment whose imports and globals name known
      exports. *)
  Lemma cmpt_ok_inv fw img fc :
    cmpt_ok fw img fc →
    let c := cmpt_of img (fc_name fc) in
    fc_unknown_export fw fc = None ∧
    cmpt_imports c = fw_imap (λ _ w, fw_word_of fw img (fc_static_sealed fc) c w) (fc_imports fc) ∧
    cmpt_static_sealed c = fw_map ss_word (fc_static_sealed fc) ∧
    body_ok fw img (fc_static_sealed fc) c (fc_body fc).
  Proof. rewrite /cmpt_ok /section. by destruct (fc_unknown_export fw fc). Qed.

  Lemma fc_export_nargs_length fw img fc :
    cmpt_ok fw img fc →
    length (fc_export_nargs fc) = length (cmpt_exp_tbl_entries (cmpt_of img (fc_name fc))).
  Proof.
    rewrite /fc_export_nargs. intros (_ & _ & _ & Hbody)%cmpt_ok_inv.
    destruct (fc_body fc) as [tb|ub].
    - destruct Hbody as (_ & _ & _ & ->). by rewrite fw_map_eq length_fmap /fw_imap length_fw_imap_from.
    - destruct Hbody as (_ & _ & _ & Hexp). rewrite /note in Hexp.
      destruct (hole_exports_length _ _ _ Hexp) as (ws & Hlen & ->).
      done.
  Qed.

End entries_facts.

(** ** The resources handed to the trusted code *)

(** The layout of the switcher of an image, with the trusted stack of the
    first thread. *)
Definition fw_switcher_layout (img : fw_image) : switcherLayout :=
  mkSwitcherLayout
    (b_switcher (img_sw img)) (e_switcher (img_sw img))
    (a_switcher_call (img_sw img)) (a_switcher_return (img_sw img))
    (ot_switcher (img_sw img))
    (b_trusted_stack (thread_of img 0)) (e_trusted_stack (thread_of img 0))
    (b_hazard (thread_of img 0)) (e_hazard (thread_of img 0)).

(** The registers other than [cgp], [cra] and [csp], cleared. *)
Definition fw_cleared_regs : LReg :=
  gset_to_gmap (lword_of_word (WInt 0)) (all_registers_s ∖ {[cgp; cra; csp]}).

Section resources.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** The empty world. *)
  Definition fw_world0 : WORLD := (∅, (∅, ∅), ∅, ∅).

  (** The resources shared by the threads: the invariants of the switcher
      and of the assert library, the memory of every compartment (trusted or
      not), the sealing types handed to the trusted code, the world of each
      logical compartment, and the heap. The switcher invariant is in the
      pool of the user thread [0], whose layout it describes; the predicates
      generic in [ceriseG] are taken at the instance of that thread, the
      shared heaps at the base. *)
  Definition fw_shared_res (fw : firmware) (img : fw_image) : iProp Σ :=
    let sw := img_sw img in
    let asrt := img_asrt img in
    "Hswitcher" ∷
      na_inv (tpool (UserThread 0)) Nswitcher
        (switcher_inv (th := UserThread 0) (swlayout := fw_switcher_layout img)) ∗
    "Hswitcher_static" ∷ switcher_static (th := UserThread 0) (swlayout := fw_switcher_layout img) ∗
    "Hseal_switcher" ∷
      seal_pred (ot_switcher sw)
        (ot_switcher_propC (th := UserThread 0) (swlayout := fw_switcher_layout img)) ∗
    "Hassert" ∷
      assert_static (ceriseg := ceriseG_of (UserThread 0))
        (b_assert asrt) (e_assert asrt) (flag_assert asrt) ∗
    "Hcmpts" ∷
      ([∗ list] fc ∈ fw_cmpts fw, [∗ map] a↦w ∈ cmpt_mem img fc, a ↦ₐ lword_of_word w) ∗
    "Hotypes" ∷ ([∗ list] o ∈ fw_otypes fw, can_alloc_pred o) ∗
    "Hworlds" ∷
      ([∗ set] C ∈ CNames, world_interp (ceriseg := ceriseG_of (UserThread 0)) fw_world0 C) ∗
    "Hheap" ∷ ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) ∗
    "Hshadow" ∷ ([∗ map] a↦s ∈ initial_heap_shadow, a ↦ₛ s) ∗
    "Hclaims" ∷ ([∗ map] a↦c ∈ init_claims (fw_set (fw_heap_roots fw)), addr_alloc a c).

  (** The resources of the thread [i], the user thread [i]: its registers,
      its stack, its call stack and the non-atomic token of its pool. *)
  Definition fw_thread_res (fw : firmware) (img : fw_image) (i : nat) : iProp Σ :=
    let t := thread_of img i in
    "HPC" ∷ PC ↦ₚ[u i] fw_entry_pc fw img i ∗
    "Hcgp" ∷ cgp ↦ᵣ[u i] fw_entry_cgp fw img i ∗
    "Hcsp" ∷ csp ↦ᵣ[u i] fw_thread_csp img i ∗
    "Hcra" ∷ cra ↦ᵣ[u i] fw_thread_cra img ∗
    "Hregs" ∷ ([∗ map] r↦w ∈ fw_cleared_regs, r ↦ᵣ[u i] w) ∗
    "Hstack" ∷
      region_pointsto (ceriseg := ceriseG_of (UserThread i)) (b_stack t) (e_stack t)
        (lword_of_word <$> replicate (ft_stack_size (fw_thread_of fw i)) (WInt 0)) ∗
    "Hcstk" ∷ cstack_frag (entry_cstack (fw_entry_frame fw img i)) ∗
    "Hna" ∷ na_own (tpool (UserThread i)) ⊤.
End resources.

(** ** Splitting the initial memory *)
Section memory_split.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  Lemma cmpts_mem_split fw img (fcs : list fw_cmpt) :
    Forall (cmpt_wf fw img) fcs →
    rngs_disjoint (fw_flat_map (cmpt_ranges img) fcs) →
    ([∗ map] a↦w ∈ big_union (fw_map (cmpt_mem img) fcs), a ↦ₐ lword_of_word w) ⊢
    [∗ list] fc ∈ fcs, [∗ map] a↦w ∈ cmpt_mem img fc, a ↦ₐ lword_of_word w.
  Proof.
    induction fcs as [|fc fcs IH]; intros Hwf Hdisj; first by iIntros "_".
    apply Forall_cons in Hwf as [Hfc Hwf]. rewrite fw_flat_map_cons in Hdisj.
    cbn [fw_map]. rewrite big_union_cons big_sepL_cons.
    iIntros "Hmem". iDestruct (big_sepM_union with "Hmem") as "[$ Hmem]".
    { eapply mem_in_disjoint_sub; [by eapply cmpt_mem_in | by apply (cmpts_mem_in fw) | done | done]. }
    iApply (IH with "Hmem"); first done.
    eapply rngs_disjoint_sublist; last exact Hdisj. by apply sublist_inserts_l.
  Qed.

  (** The memory of a state satisfying [firmware_ok], by part. *)
  Lemma firmware_ok_mem_split fw img σ :
    firmware_ok fw img σ →
    ([∗ map] a↦w ∈ mem σ, a ↦ₐ lword_of_word w) ⊢
    ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) ∗
    ([∗ map] a↦w ∈ switcher_mem img, a ↦ₐ lword_of_word w) ∗
    ([∗ map] a↦w ∈ assert_code_mem img ∪ assert_flag_mem img, a ↦ₐ lword_of_word w) ∗
    ([∗ list] fc ∈ fw_cmpts fw, [∗ map] a↦w ∈ cmpt_mem img fc, a ↦ₐ lword_of_word w) ∗
    ([∗ map] a↦w ∈ thread_mem img 0 (fw_thread0 fw), a ↦ₐ lword_of_word w).
  Proof.
    intros Hok.
    pose proof (firmware_ok_mem_in _ _ _ Hok) as Hmem_in.
    destruct Hok as (_ & [Hmem _] & Hregs & Hwf).
    destruct (regs_ok_inv _ _ _ Hregs) as ([fts Hthreads] & _). clear Hregs.
    pose proof (img_wf_rngs_disjoint _ _ Hwf) as Hdisj.
    pose proof (img_wf_ranges_ok _ _ Hwf) as Hrok.
    pose proof Hwf as (Hsw & Hasrt & Hcmpts & Hthr & _). apply big_and_fw_map in Hcmpts.
    pose proof (switcher_mem_in _ Hsw) as HS.
    pose proof (assert_code_mem_in _ Hasrt) as HAC.
    pose proof (assert_flag_mem_in _ Hasrt) as HAF.
    pose proof (cmpts_mem_in fw _ _ Hcmpts) as HCM.
    pose proof (threads_mem_in fw _ 0 _ Hthr) as HTM.
    rewrite /note in Hmem. rewrite Hmem.
    match goal with |- context [ ?H ∪ ?S ∪ ?AC ∪ ?AF ∪ ?CM ∪ ?TM ] =>
      replace (H ∪ S ∪ AC ∪ AF ∪ CM ∪ TM) with (H ∪ (S ∪ AC ∪ AF ∪ CM ∪ TM))
        by (by rewrite !(assoc_L (∪)))
    end.
    iIntros "Hmem". iDestruct (big_sepM_union with "Hmem") as "[$ Hmem]".
    { eapply mem_in_heap_disjoint; [exact Hmem_in | exact Hrok]. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hthreads]".
    { eapply mem_in_disjoint_sub;
        [ exact (mem_in_union _ _ _ _ (mem_in_union _ _ _ _ (mem_in_union _ _ _ _ HS HAC) HAF) HCM)
        | exact HTM | | exact Hdisj].
      rewrite /fw_ranges -!app_assoc. reflexivity. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpts]".
    { eapply mem_in_disjoint_sub;
        [ exact (mem_in_union _ _ _ _ (mem_in_union _ _ _ _ HS HAC) HAF) | exact HCM | | exact Hdisj].
      rewrite /fw_ranges -!app_assoc. cbn. do 3 apply sublist_skip. by apply sublist_inserts_r. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hflag]".
    { eapply mem_in_disjoint_sub; [exact (mem_in_union _ _ _ _ HS HAC) | exact HAF | | exact Hdisj].
      rewrite /fw_ranges. cbn. do 3 apply sublist_skip. apply sublist_nil_l. }
    iDestruct (big_sepM_union with "Hmem") as "[$ Hassert]".
    { eapply mem_in_disjoint_sub; [exact HS | exact HAC | | exact Hdisj].
      rewrite /fw_ranges. cbn. do 2 apply sublist_skip. apply sublist_nil_l. }
    iSplitL "Hassert Hflag".
    { iApply big_sepM_union; last iFrame.
      eapply mem_in_disjoint_sub; [exact HAC | exact HAF | | exact Hdisj].
      rewrite /fw_ranges. cbn. apply sublist_cons. do 2 apply sublist_skip. apply sublist_nil_l. }
    iSplitL "Hcmpts".
    { iApply (cmpts_mem_split with "Hcmpts"); first done.
      eapply rngs_disjoint_sublist; last exact Hdisj.
      rewrite /fw_ranges. do 3 apply sublist_cons. by apply sublist_inserts_r. }
    rewrite Hthreads in Hthr. apply big_and_cons in Hthr as [Hthr0 Hthr].
    rewrite Hthreads /fw_imap. cbn [fw_imap_from]. rewrite big_union_cons.
    iDestruct (big_sepM_union with "Hthreads") as "[$ _]".
    eapply mem_in_disjoint_sub;
      [by eapply thread_mem_in | by apply (threads_mem_in fw) | | exact Hdisj].
    rewrite /fw_ranges Hthreads /fw_imap. cbn [fw_imap_from]. rewrite fw_flat_map_cons.
    do 3 apply sublist_cons. by apply sublist_inserts_l.
  Qed.

  (** The registers of a state satisfying [firmware_ok]. *)
  Lemma firmware_ok_regs_split fw img σ :
    firmware_ok fw img σ →
    PC ↦ₚ lword_of_word (pcc σ) ∗
    ([∗ map] r↦w ∈ lword_of_word <$> reg σ, r ↦ᵣ w) ⊢
    PC ↦ₚ fw_entry_pc fw img 0 ∗
    cgp ↦ᵣ fw_entry_cgp fw img 0 ∗
    csp ↦ᵣ fw_thread_csp img 0 ∗
    cra ↦ᵣ fw_thread_cra img ∗
    [∗ map] r↦w ∈ fw_cleared_regs, r ↦ᵣ w.
  Proof.
    intros (_ & _ & Hregs & _).
    destruct (regs_ok_inv _ _ _ Hregs) as (_ & _ & _ & Hpc & Hcgp & Hcsp & Hcra & Hzero & _).
    rewrite Hpc. iIntros "[$ Hreg]".
    iDestruct (big_sepM_delete _ _ cgp with "Hreg") as "[$ Hreg]";
      first by rewrite lookup_fmap Hcgp.
    iDestruct (big_sepM_delete _ _ csp with "Hreg") as "[$ Hreg]";
      first by rewrite lookup_delete_ne // lookup_fmap Hcsp.
    iDestruct (big_sepM_delete _ _ cra with "Hreg") as "[$ Hreg]";
      first by rewrite !lookup_delete_ne // lookup_fmap Hcra.
    assert (delete cra (delete csp (delete cgp (lword_of_word <$> reg σ))) = fw_cleared_regs)
      as ->; last done.
    apply map_eq. intros r. rewrite /fw_cleared_regs lookup_gset_to_gmap.
    destruct (decide (r = cra)) as [->|Hne3].
    { rewrite lookup_delete option_guard_False //. }
    destruct (decide (r = csp)) as [->|Hne2].
    { rewrite lookup_delete_ne // lookup_delete option_guard_False //. }
    destruct (decide (r = cgp)) as [->|Hne1].
    { rewrite lookup_delete_ne // lookup_delete_ne // lookup_delete option_guard_False //. }
    rewrite !lookup_delete_ne // lookup_fmap Hzero; last set_solver+Hne1 Hne2 Hne3.
    rewrite option_guard_True //. pose proof (all_registers_s_correct r).
    set_solver+Hne1 Hne2 Hne3.
  Qed.
End memory_split.

(** The obligations of the trusted code of a firmware, for the ghost state
    [Σ]: for every image and initial state satisfying [firmware_ok], the
    first thread, the user thread [0], runs safely from the resources of
    the image. A case study with its own ghost state proves them for every
    [Σ] with its [subG] assumptions, and allocates its ghost state inside
    the proof. *)
Definition fw_obligations (Σ : gFunctors) {Cname : CmptNameG} `{MP : MachineParameters}
    (fw : firmware) : Prop :=
  ∀ (img : fw_image) (σ : ExecConf)
    (ceriseb : ceriseBaseG Σ) (sealsg : sealStoreG Σ)
    (stsg : STSG LAddr region_type OType LWord Σ) (relg : relGS Σ)
    (cstackg : CSTACKG Σ),
    firmware_ok fw img σ →
    ⊢ fw_shared_res fw img -∗
      fw_thread_res fw img 0
      ={⊤}=∗
      WP Seq (Instr Executable) @[u 0] {{ _, True }}.

Theorem firmware_adequacy (Σ : gFunctors)
    {inv_preg : invGpreS Σ}
    {cerise_preg : ceriseGpreS Σ}
    {na_invg : na_invariants.na_invG Σ}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG LAddr region_type OType LWord Σ}
    {cstack_preg : CSTACK_preG Σ}
    {Cname : CmptNameG}
    {relpreg : relGpreS Σ}
    `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ σ' : ExecConf) (es : list griotte_lang.expr) :
  fw_obligations Σ fw →
  firmware_ok fw img σ →
  rtc erased_step ([Seq (Instr Executable)], σ) (es, σ') →
  mem σ' !! flag_assert (img_asrt img) = Some (WInt 0).
Proof.
  intros Hobl Hok Hstep.
  destruct σ as [ [ [ [w_pc regs] sregs] m] sh].
  destruct σ' as [ [ [ [w_pc' regs'] sregs'] m'] sh'].
  pose proof Hok as (_ & [_ Hsh] & Hregs & Hwf).
  change (shadowtbl (w_pc, regs, sregs, m, sh)) with sh in Hsh. rewrite /note in Hsh.
  destruct (regs_ok_inv _ _ _ Hregs) as ([fts Hthreads] & _ & _ & _ & _ & _ & _ & _ & Hsreg).
  clear Hregs.
  change (sreg (w_pc, regs, sregs, m, sh)) with sregs in Hsreg.
  pose proof (img_wf_switcher_layout _ _ _ _ Hthreads Hwf) as Hsw.
  pose proof (img_wf_trusted_stack_layout _ _ _ _ Hthreads Hwf) as Hts.
  pose proof (img_wf_assert_layout _ _ Hwf) as Hasrt.
  destruct (img_wf_otypes _ _ Hwf) as [Hot_nodup _].
  apply NoDup_cons in Hot_nodup as [Hot_notin Hot_nodup].
  destruct (firmware_ok_ghost_init_cond _ _ _ _ _ _ _ Hok) as [Hinit Hnull].
  (* The program-logic resources of the initial state. *)
  eapply (cerise_flag_adequacy Σ (TV := fw_trap_vector img)
            Nassert_flag (flag_assert (img_asrt img)) (fw_set (fw_heap_roots fw)));
    [exact Hinit | exact Hnull | exact (Hsreg MTDC) | | exact Hstep].
  iIntros (ceriseb Hmtcc) "HPC Hreg Hmtdc Hmem Hshadow Hclaims Hna".
  (* The seal store, the call stack and the worlds. *)
  iMod (initialise_world (ceriseg := ceriseG_of (UserThread 0)) (finite.enum CmptName)
          ({[ot_switcher (img_sw img)]} ∪ list_to_set (fw_otypes fw)) (fw_entry_frame fw img 0))
    as (sealsg relg stsg cstackg) "(Hseal_store & Hcstk_full & Hcstk_frag & Hworlds)";
    [done | apply finite.NoDup_enum |].
  rewrite big_sepS_union; last (apply disjoint_singleton_l; by rewrite elem_of_list_to_set).
  rewrite big_sepS_singleton big_sepS_list_to_set //.
  iDestruct "Hseal_store" as "[Hseal_switcher Hotypes]".
  (* The memory and the registers, by part. *)
  iDestruct (firmware_ok_mem_split (ceriseg := ceriseG_of (UserThread 0))
              fw img (w_pc, regs, sregs, m, sh) Hok with "Hmem")
    as "(Hheap & Hsw_code & Hasrt & Hcmpts & Hthread)".
  iDestruct (firmware_ok_regs_split (ceriseg := ceriseG_of (UserThread 0))
              fw img (w_pc, regs, sregs, m, sh) Hok with "[$HPC $Hreg]")
    as "(HPC & Hcgp & Hcsp & Hcra & Hregs)".
  subst sh.
  (* The assert library. *)
  rewrite (assert_mem_layout _ Hasrt).
  iMod (initialise_assert_compartment _ with "Hasrt") as "[#Hflag #Hassert]".
  (* The switcher, with the trusted stack and the stack of the thread. *)
  rewrite (switcher_mem_layout _ _ _ _ Hts Hsw) (thread_mem_layout _ _ Hts Hsw).
  set (swc := layout_switcher_of (img_sw img) (thread_of img 0) _ _ Hts Hsw).
  iAssert ([∗ map] a↦w ∈ mk_initial_switcher swc, a ↦ₐ lword_of_word w)%I
    with "[Hsw_code Hthread]" as "Hswitcher".
  { rewrite /mk_initial_switcher.
    match goal with |- context [ ?C ∪ ?T ∪ ?S ∪ ?H ] =>
      replace (C ∪ T ∪ S ∪ H) with (C ∪ (T ∪ S ∪ H)) by (by rewrite !(assoc_L (∪)))
    end.
    iApply (big_sepM_union with "[$Hsw_code $Hthread]").
    pose proof (cmpt_switcher_stack_mregion_disjoint swc) as Hd1.
    pose proof (cmpt_switcher_trusted_stack_mregion_disjoint swc) as Hd2.
    pose proof (cmpt_switcher_hazard_mregion_disjoint swc) as Hd3.
    apply map_disjoint_union_l in Hd1 as [Hd1 _].
    apply map_disjoint_union_l in Hd3 as [Hd3 _].
    apply map_disjoint_union_l in Hd3 as [Hd3 _].
    apply map_disjoint_union_r; split; last done.
    by apply map_disjoint_union_r. }
  (* The entry frame: the stack pointer of the thread and the export table
     of the compartment it starts in *)
  pose proof Hwf as (_ & _ & Hcmpts_wf & Hthreads_wf & _).
  apply big_and_fw_map in Hcmpts_wf.
  rewrite Hthreads in Hthreads_wf. apply big_and_cons in Hthreads_wf as [Hthread0 _].
  destruct (thread_entry_frame_words _ _ _ _ Hcmpts_wf Hthread0) as (_ & _ & Htbl_cap).
  iMod (initialise_switcher_compartment (th := UserThread 0) swc
          (fw_thread_csp img 0) (fw_entry_tbl fw img 0)
          (cmpt_exp_tbl_pcc (fw_entry_cmpt fw img 0)) Hmtcc
         with "Hswitcher Hseal_switcher Hcstk_full Hmtdc")
    as "(#Hseal_pred & #Hswitcher & #Hswitcher_static & Hstack)".
  { change (trusted_stack_content swc) with (fw_tstack_content img 0 (fw_thread0 fw)).
    apply fw_tstack_content_csp. }
  { change (trusted_stack_content swc) with (fw_tstack_content img 0 (fw_thread0 fw)).
    rewrite /fw_entry_tbl /fw_entry_cmpt fw_thread_of_0.
    apply fw_tstack_content_export_table. }
  { rewrite /fw_entry_cmpt fw_thread_of_0. exact Htbl_cap. }
  (* The obligations of the trusted code. *)
  iPoseProof (Hobl img _ ceriseb sealsg stsg relg cstackg Hok) as "Hobl".
  iMod ("Hobl" with "[-HPC Hcgp Hcsp Hcra Hregs Hstack Hcstk_frag Hna]
                     [$HPC $Hcgp $Hcsp $Hcra $Hregs $Hstack $Hcstk_frag $Hna]") as "Hwp".
  { rewrite /fw_shared_res /CNames big_sepS_list_to_set; last apply finite.NoDup_enum.
    iFrame "Hotypes Hheap Hshadow Hclaims Hcmpts Hworlds". iFrame "#". }
  iModIntro. iFrame "Hwp Hflag".
Qed.

(** The ghost state of the template. A case study with ghost state [Σcs]
    proves [∀ Σ, subG Σcs Σ → fw_obligations Σ fw] in a section whose
    context derives its pre-instances from [subG], and concludes with
    [firmware_adequacy_closed] at [Σcs]. *)
Definition firmwarePreΣ {Cname : CmptNameG} : gFunctors :=
  #[invΣ; ceriseGpreΣ; CSTACK_preΣ; na_invΣ; sealStorePreΣ;
    STS_preΣ LAddr region_type OType LWord; relPreΣ;
    savedPredΣ (WorldT * CmptName * LWord)].

Theorem firmware_adequacy_closed (Σcs : gFunctors) {Cname : CmptNameG}
    `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ σ' : ExecConf) (es : list griotte_lang.expr) :
  fw_obligations #[firmwarePreΣ; Σcs] fw →
  firmware_ok fw img σ →
  rtc erased_step ([Seq (Instr Executable)], σ) (es, σ') →
  mem σ' !! flag_assert (img_asrt img) = Some (WInt 0).
Proof.
  intros Hobl Hok Hstep.
  eapply (firmware_adequacy #[firmwarePreΣ; Σcs]); eauto; typeclasses eauto.
Qed.

(** ** Layout facts for the obligations *)
Section obligation_layouts.
  Context `{MP : MachineParameters}.

  Lemma rngs_cross_elem ts1 ts2 s1 b1 e1 s2 b2 e2 (a : Addr) :
    rngs_disjoint (ts1 ++ ts2) →
    (s1, b1, e1) ∈ ts1 →
    (s2, b2, e2) ∈ ts2 →
    a ∈ finz.seq_between b1 e1 →
    a ∈ finz.seq_between b2 e2 →
    False.
  Proof.
    intros Hd H1 H2 Ha1 Ha2.
    by apply (rngs_disjoint_app_cross _ _ _ _ Hd H1 H2 a).
  Qed.

  Lemma cmpt_ranges_pair_sublist img (fcs : list fw_cmpt) i j fci fcj :
    i < j →
    fcs !! i = Some fci →
    fcs !! j = Some fcj →
    (cmpt_ranges img fci ++ cmpt_ranges img fcj) `sublist_of` fw_flat_map (cmpt_ranges img) fcs.
  Proof.
    revert i j. induction fcs as [|fc fcs IH]; intros i j Hij Hi Hj; first done.
    rewrite fw_flat_map_cons.
    destruct i as [|i]; cbn in Hi.
    - injection Hi as <-. destruct j as [|j]; first lia. cbn in Hj.
      apply sublist_app; first done.
      apply cmpt_ranges_sublist. by eapply list_elem_of_lookup_2.
    - destruct j as [|j]; first lia. cbn in Hj.
      apply sublist_inserts_l. apply (IH i j); [lia | done | done].
  Qed.

  Lemma layout_cmpts_disjoint_of_rngs img X Y
      (HX : img_cmpt_layout (cmpt_of img (fc_name X)))
      (HY : img_cmpt_layout (cmpt_of img (fc_name Y))) :
    rngs_disjoint (cmpt_ranges img X ++ cmpt_ranges img Y) →
    layout_cmpt_of _ HX ## layout_cmpt_of _ HY.
  Proof.
    intros HdXY a HaX HaY.
    rewrite /cmpt_region /cmpt_pcc_region /cmpt_cgp_region /cmpt_static_sealed_region
      /cmpt_exp_tbl_region /= in HaX HaY.
    rewrite !elem_of_union in HaX HaY.
    destruct HaX as [ [ [HaX|HaX]|HaX]|HaX]; destruct HaY as [ [ [HaY|HaY]|HaY]|HaY];
      (eapply (rngs_cross_elem _ _ _ _ _ _ _ _ a HdXY); [ | | exact HaX | exact HaY]);
      rewrite /cmpt_ranges; repeat first [apply list_elem_of_here | apply list_elem_of_further].
  Qed.

  (** Compartments at different positions of the firmware are disjoint. *)
  Lemma img_wf_cmpts_disjoint fw img i j fci fcj
      (Hci : img_cmpt_layout (cmpt_of img (fc_name fci)))
      (Hcj : img_cmpt_layout (cmpt_of img (fc_name fcj))) :
    img_wf fw img →
    i ≠ j →
    fw_cmpts fw !! i = Some fci →
    fw_cmpts fw !! j = Some fcj →
    layout_cmpt_of _ Hci ## layout_cmpt_of _ Hcj.
  Proof.
    intros Hwf Hij Hi Hj. pose proof (img_wf_rngs_disjoint _ _ Hwf) as Hdisj.
    assert (∀ i' j' fci' fcj', i' < j' →
              fw_cmpts fw !! i' = Some fci' →
              fw_cmpts fw !! j' = Some fcj' →
              rngs_disjoint (cmpt_ranges img fci' ++ cmpt_ranges img fcj')) as Hpair.
    { intros i' j' fci' fcj' Hlt Hi' Hj'. eapply rngs_disjoint_sublist; last exact Hdisj.
      rewrite /fw_ranges. do 3 apply sublist_cons. apply sublist_inserts_r.
      by eapply cmpt_ranges_pair_sublist. }
    destruct (decide (i < j)) as [Hlt|Hge].
    - apply layout_cmpts_disjoint_of_rngs. by apply (Hpair i j).
    - pose proof (layout_cmpts_disjoint_of_rngs img fcj fci Hcj Hci
                    (Hpair j i fcj fci ltac:(lia) Hj Hi)) as Hd.
      rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt in Hd |- *. by symmetry.
  Qed.

  (** A compartment is disjoint from the switcher and the stacks of the
      first thread. *)
  Lemma img_wf_switcher_cmpt_disjoint fw img ft fts fc ts ss
      (Hc : img_cmpt_layout (cmpt_of img (fc_name fc)))
      (Hts : trusted_stack_layout (b_trusted_stack (thread_of img 0))
               (e_trusted_stack (thread_of img 0))
               (b_hazard (thread_of img 0)) (e_hazard (thread_of img 0)) ts)
      (Hsw : img_switcher_layout (img_sw img) (thread_of img 0) ss) :
    fw_threads fw = ft :: fts →
    img_wf fw img →
    fc ∈ fw_cmpts fw →
    switcher_cmpt_disjoint (layout_cmpt_of _ Hc) (layout_switcher_of _ _ _ _ Hts Hsw).
  Proof.
    intros Hthreads Hwf Hin. pose proof (img_wf_rngs_disjoint _ _ Hwf) as Hdisj.
    assert (rngs_disjoint ([("switcher", b_switcher (img_sw img), e_switcher (img_sw img))] ++
                           cmpt_ranges img fc)) as H1.
    { eapply rngs_disjoint_sublist; last exact Hdisj.
      rewrite /fw_ranges. apply sublist_skip. do 2 apply sublist_cons.
      apply sublist_inserts_r. by apply cmpt_ranges_sublist. }
    assert (rngs_disjoint (cmpt_ranges img fc ++ thread_ranges img 0 ft)) as H2.
    { eapply rngs_disjoint_sublist; last exact Hdisj.
      rewrite /fw_ranges Hthreads /fw_imap. cbn [fw_imap_from]. rewrite fw_flat_map_cons.
      do 3 apply sublist_cons. apply sublist_app; first by apply cmpt_ranges_sublist.
      by apply sublist_inserts_r. }
    intros a Ha_sw Ha_c.
    rewrite /cmpt_switcher_region /cmpt_switcher_code_region /cmpt_switcher_trusted_stack_region
      /cmpt_switcher_stack_region /= in Ha_sw.
    rewrite /cmpt_region /cmpt_pcc_region /cmpt_cgp_region /cmpt_static_sealed_region
      /cmpt_exp_tbl_region /= in Ha_c.
    rewrite !elem_of_union in Ha_sw Ha_c.
    destruct Ha_sw as [ [Ha_sw|Ha_sw]|Ha_sw].
    - destruct Ha_c as [ [ [Ha_c|Ha_c]|Ha_c]|Ha_c];
        (eapply (rngs_cross_elem _ _ _ _ _ _ _ _ a H1); [ | | exact Ha_sw | exact Ha_c]);
        rewrite /cmpt_ranges; repeat first [apply list_elem_of_here | apply list_elem_of_further].
    - destruct Ha_c as [ [ [Ha_c|Ha_c]|Ha_c]|Ha_c];
        (eapply (rngs_cross_elem _ _ _ _ _ _ _ _ a H2); [ | | exact Ha_c | exact Ha_sw]);
        rewrite /cmpt_ranges /thread_ranges;
        repeat first [apply list_elem_of_here | apply list_elem_of_further].
    - destruct Ha_c as [ [ [Ha_c|Ha_c]|Ha_c]|Ha_c];
        (eapply (rngs_cross_elem _ _ _ _ _ _ _ _ a H2); [ | | exact Ha_c | exact Ha_sw]);
        rewrite /cmpt_ranges /thread_ranges;
        repeat first [apply list_elem_of_here | apply list_elem_of_further].
  Qed.
End obligation_layouts.

(** ** The switcher layout of an image is well formed *)
Definition fw_switcher_layout_wf `{MP : MachineParameters} (img : fw_image) (ts ss : list Word)
    (Hts : trusted_stack_layout (b_trusted_stack (thread_of img 0))
             (e_trusted_stack (thread_of img 0))
             (b_hazard (thread_of img 0)) (e_hazard (thread_of img 0)) ts)
    (Hsw : img_switcher_layout (img_sw img) (thread_of img 0) ss) :
    @switcherLayoutWf MP (fw_switcher_layout img) :=
  mkSwitcherLayoutWf (fw_switcher_layout img)
    (isl_switcher_size _ _ _ Hsw) (isl_call_entry_point _ _ _ Hsw)
    (isl_return_entry_point _ _ _ Hsw) (isl_ot_switcher_size _ _ _ Hsw)
    (proj1 (isl_trusted_stack_mmio _ _ _ Hsw)) (isl_switcher_key_not_shadow _ _ _ Hsw)
    (isl_switcher_not_heap _ _ _ Hsw) (isl_trusted_stack_not_heap _ _ _ Hsw)
    (tsl_frames_fit _ _ _ _ _ Hts) (isl_trusted_stack_nonzero _ _ _ Hsw)
    (isl_hazard_size _ _ _ Hsw) (proj1 (isl_hazard_mmio _ _ _ Hsw))
    (isl_hazard_not_heap _ _ _ Hsw).
