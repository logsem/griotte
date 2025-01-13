From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
Require Import Eqdep_dec.
From cap_machine Require Import
     stdpp_extra iris_extra
     rules logrel fundamental region_invariants sts
     region_invariants_revocation region_invariants_static
     region_invariants_batch_uninitialized region_invariants_allocation.
From cap_machine.examples Require Import
     disjoint_regions_tactics
     macros downwards_lse downwards_lse_preamble.

Instance DisjointList_list_Addr : DisjointList (list Addr).
Proof. exact (@disjoint_list_default _ _ app []). Defined.

Class memory_layout `{MachineParameters} := {
  (* lse example: preamble & body *)
  lse_region_start : Addr;
  lse_preamble_start : Addr;
  lse_body_start : Addr;
  lse_region_end : Addr;

  (* pointer to the linking table, at the beginning of the region *)
  lse_linking_ptr_size :
    (lse_region_start + 1)%a = Some lse_preamble_start;

  (* preamble code, that allocates the closure *)
  lse_preamble_size :
    (lse_preamble_start + downwards_lse_preamble_instrs_length)%a
    = Some lse_body_start;

  (* code of the body, wrapped in the closure allocated by the preamble *)
  lse_body_size :
    (lse_body_start + length (lse_instrs 0))%a
    = Some lse_region_end;

  (* stack *)
  stack_start : Addr;
  stack_end : Addr;

  (* adversary code *)
  adv_start : Addr;
  adv_end : Addr;

  (* malloc routine *)
  malloc_start : Addr;
  malloc_memptr : Addr;
  malloc_mem_start : Addr;
  malloc_end : Addr;

  malloc_code_size :
    (malloc_start + length malloc_subroutine_instrs)%a
    = Some malloc_memptr;

  malloc_memptr_size :
    (malloc_memptr + 1)%a = Some malloc_mem_start;

  malloc_mem_size :
    (malloc_mem_start <= malloc_end)%a;

  (* fail routine *)
  fail_start : Addr;
  fail_end : Addr;

  fail_size :
    (fail_start
     + (length assert_fail_instrs (* code of the subroutine *)
        + 1 (* pointer to the flag *))
    )%a
    = Some fail_end;

  (* link table *)
  link_table_start : Addr;
  link_table_end : Addr;

  link_table_size :
    (link_table_start + 2)%a = Some link_table_end;

  (* failure flag *)
  fail_flag : Addr;
  fail_flag_next : Addr;
  fail_flag_size :
    (fail_flag + 1)%a = Some fail_flag_next;

  (* disjointness of all the regions above *)
  regions_disjoint :
    ## [
        [fail_flag];
        region_addrs link_table_start link_table_end;
        region_addrs fail_start fail_end;
        region_addrs malloc_mem_start malloc_end;
        [malloc_memptr];
        region_addrs malloc_start malloc_memptr;
        region_addrs adv_start adv_end;
        region_addrs stack_start stack_end;
        region_addrs lse_body_start lse_region_end;
        region_addrs lse_preamble_start lse_body_start;
        [lse_region_start]
       ];
}.

Definition mkregion (r_start r_end: Addr) (contents: list Word): gmap Addr Word :=
  list_to_map (zip (region_addrs r_start r_end) contents).

Definition offset_to_lse `{memory_layout} : Z :=
  (* in this setup, the body of the lse examples comes just after the code
     of the preamble *)
  (downwards_lse_preamble_instrs_length - downwards_lse_preamble_move_offset)%Z.

Definition mk_initial_memory `{memory_layout} (adv_val stack_val: list Word) : gmap Addr Word :=
  (* pointer to the linking table *)
    list_to_map [(lse_region_start,
                  inr (RO, Global, link_table_start, link_table_end, link_table_start))]
  ∪ mkregion lse_preamble_start lse_body_start
       (* preamble: code that creates the lse example closure *)
      (downwards_lse_preamble_instrs 0%Z (* offset to malloc in linking table *)
         offset_to_lse (* offset to the body of the example *))
  ∪ mkregion lse_body_start lse_region_end
       (* body of the lse example, that will be encapsulated in the closure
          created by the preamble *)
      (lse_instrs 1%Z (* offset to fail in the linking table *))
  ∪ mkregion stack_start stack_end
      (* initial content of the stack: can be anything *)
      stack_val
  ∪ mkregion adv_start adv_end
      (* adversarial code: any code or data, but no capabilities (see condition below), except for the malloc capability *)
      ((inr (E, Global, malloc_start, malloc_end, malloc_start)) :: adv_val)
  ∪ mkregion malloc_start malloc_memptr
      (* code for the malloc subroutine *)
      malloc_subroutine_instrs
  ∪ list_to_map
      (* Capability to malloc's memory pool, used by the malloc subroutine *)
      [(malloc_memptr, inr (RWX, Global, malloc_memptr, malloc_end, malloc_mem_start))]
  ∪ mkregion malloc_mem_start malloc_end
      (* Malloc's memory pool, initialized to zero *)
      (region_addrs_zeroes malloc_mem_start malloc_end)
  ∪ mkregion fail_start fail_end
      ((* code for the failure subroutine *)
        assert_fail_instrs ++
       (* pointer to the "failure" flag, set to 1 by the routine *)
       [inr (RW, Global, fail_flag, fail_flag_next, fail_flag)])
  ∪ mkregion link_table_start link_table_end
      (* link table, with pointers to the malloc and failure subroutines *)
      [inr (E, Global, malloc_start, malloc_end, malloc_start);
       inr (E, Global, fail_start, fail_end, fail_start)]
  ∪ list_to_map [(fail_flag, inl 0%Z)] (* failure flag, initially set to 0 *)
.

Definition is_initial_memory `{memory_layout} (m: gmap Addr Word) :=
  ∃ (adv_val stack_val: list Word),
  m = mk_initial_memory adv_val stack_val
  ∧
  (* the adversarial region in memory must only contain instructions, no
     capabilities (it can thus only access capabilities the lse preamble
     passes it through the registers, and malloc) *)
  Forall (λ w, is_cap w = false) adv_val
  ∧
  (adv_start + (length adv_val + 1))%a = Some adv_end
  ∧
  (stack_start + length stack_val)%a = Some stack_end.

Definition is_initial_registers `{memory_layout} (reg: gmap RegName Word) :=
  reg !! PC = Some (inr (RX, Global, lse_region_start, lse_region_end, lse_preamble_start)) ∧
  reg !! r_stk = Some (inr (URWLX, Directed, stack_start, stack_end, stack_start)) ∧
  reg !! r_t0 = Some (inr (RWX, Global, adv_start, adv_end, adv_start)) ∧
  (∀ (r: RegName), r ∉ ({[ PC; r_stk; r_t0 ]} : gset RegName) →
    ∃ (w:Word), reg !! r = Some w ∧ is_cap w = false).

Lemma initial_registers_full_map `{MachineParameters, memory_layout} reg :
  is_initial_registers reg →
  (∀ r, is_Some (reg !! r)).
Proof.
  intros (HPC & Hstk & Hr0 & Hothers) r.
  destruct (decide (r = PC)) as [->|]. by eauto.
  destruct (decide (r = r_stk)) as [->|]. by eauto.
  destruct (decide (r = r_t0)) as [->|]. by eauto.
  destruct (Hothers r) as (w & ? & ?); [| eauto]. set_solver.
Qed.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invPreG Σ}.
  Context {mem_preg: gen_heapPreG Addr Word Σ}.
  Context {reg_preg: gen_heapPreG RegName Word Σ}.
  Context {na_invg: na_invG Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {heappreg: heapPreG Σ}.
  Context `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).

  Lemma dom_mkregion_incl a e l:
    dom (gset Addr) (mkregion a e l) ⊆ list_to_set (region_addrs a e).
  Proof.
    rewrite /mkregion. generalize (region_addrs a e). induction l.
    { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L. apply empty_subseteq. }
    { intros ll. destruct ll as [| x ll].
      - cbn. rewrite dom_empty_L. done.
      - cbn [list_to_set zip zip_with list_to_map foldr fst snd]. rewrite dom_insert_L.
        set_solver. }
  Qed.

  Lemma dom_mkregion_incl_rev a e l:
    (a + length l = Some e)%a →
    list_to_set (region_addrs a e) ⊆ dom (gset Addr) (mkregion a e l).
  Proof.
    rewrite /mkregion. intros Hl.
    assert (length (region_addrs a e) = length l) as Hl'.
    { rewrite region_addrs_length /region_size. solve_addr. }
    clear Hl. revert Hl'. generalize (region_addrs a e). induction l.
    { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L.
      destruct l; [| inversion Hl']. cbn. apply empty_subseteq. }
    { intros ll Hll. destruct ll as [| x ll]; [by inversion Hll|].
      cbn [list_to_set zip zip_with list_to_map foldr fst snd].
      rewrite dom_insert_L. cbn in Hll. apply Nat.succ_inj in Hll.
      specialize (IHl ll Hll). set_solver. }
  Qed.

  Lemma dom_mkregion_eq a e l:
    (a + length l = Some e)%a →
    dom (gset Addr) (mkregion a e l) = list_to_set (region_addrs a e).
  Proof.
    intros Hlen. apply (anti_symm _).
    - apply dom_mkregion_incl.
    - by apply dom_mkregion_incl_rev.
  Qed.

  Lemma in_dom_mkregion a e l k:
    k ∈ dom (gset Addr) (mkregion a e l) →
    k ∈ region_addrs a e.
  Proof.
    intros H.
    pose proof (dom_mkregion_incl a e l) as HH.
    rewrite elem_of_subseteq in HH |- * => HH.
    specialize (HH _ H). eapply @elem_of_list_to_set; eauto. apply _.
  Qed.

  Lemma in_dom_mkregion' a e l k:
    (a + length l = Some e)%a →
    k ∈ region_addrs a e →
    k ∈ dom (gset Addr) (mkregion a e l).
  Proof.
    intros. rewrite dom_mkregion_eq // elem_of_list_to_set //.
  Qed.

  Ltac disjoint_map_to_list :=
    rewrite (@map_disjoint_dom _ _ (gset Addr)) ?dom_union_L;
    eapply disjoint_mono_l;
    rewrite ?dom_list_to_map_singleton;
    repeat (
      try lazymatch goal with
          | |- _ ∪ _ ⊆ _ =>
            etransitivity; [ eapply union_mono_l | eapply union_mono_r ]
          end;
      [ first [ apply dom_mkregion_incl | reflexivity ] |..]
    );
    try match goal with |- _ ## dom _ (mkregion _ _ _) =>
      eapply disjoint_mono_r; [ apply dom_mkregion_incl |] end;
    rewrite -?list_to_set_app_L ?dom_list_to_map_singleton;
    apply list_to_set_disj.

  Lemma mkregion_sepM_to_sepL2 (a e: Addr) l (φ: Addr → Word → iProp Σ) :
    (a + length l)%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, φ k v) -∗ ([∗ list] k;v ∈ (region_addrs a e); l, φ k v).
  Proof.
    rewrite /mkregion. revert a e. induction l as [| x l].
    { cbn. intros. rewrite zip_with_nil_r /=. assert (a = e) as -> by solve_addr.
      rewrite /region_addrs region_size_0. 2: solve_addr. cbn. eauto. }
    { cbn. intros a e Hlen. rewrite region_addrs_cons. 2: solve_addr.
      cbn. iIntros "H". iDestruct (big_sepM_insert with "H") as "[? H]".
      { rewrite -not_elem_of_list_to_map /=.
        intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_region_addrs] ]%elem_of_list_fmap.
        solve_addr. }
      iFrame. iApply (IHl with "H"). solve_addr. }
  Qed.

  Lemma mkregion_prepare `{memG Σ} (a e: Addr) l :
    (a + length l)%a = Some e →
    ([∗ map] k↦v ∈ mkregion a e l, k ↦ₐ v) ==∗ ([∗ list] k;v ∈ (region_addrs a e); l, k ↦ₐ v).
  Proof.
    iIntros (?) "H". iDestruct (mkregion_sepM_to_sepL2 with "H") as "H"; auto.
  Qed.

  Definition flagN : namespace := nroot .@ "lse" .@ "fail_flag".
  Definition mallocN : namespace := nroot .@ "lse" .@ "malloc".

  Lemma downwards_lse_adequacy' `{memory_layout} (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
    is_initial_memory m →
    is_initial_registers reg →
    rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
    m' !! fail_flag = Some (inl 0%Z).
  Proof.
    intros Hm Hreg Hstep.
    pose proof (@wp_invariance Σ cap_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c: ExecConf) => c.2 !! fail_flag = Some (inl 0%Z)) as state_is_good.
    specialize (WPI (Seq (Instr Executable)) (reg, m) es (reg', m') (state_is_good (reg', m'))).
    eapply WPI. 2: assumption. intros Hinv κs. clear WPI.

    destruct Hm as (adv_val & stack_val & Hm & Hadv_val & adv_size & stack_size).
    iMod (gen_heap_init (∅:Mem)) as (mem_heapg) "Hmem_ctx".
    iMod (gen_heap_init (∅:Reg)) as (reg_heapg) "Hreg_ctx".
    unshelve iMod gen_sts_init as (stsg) "Hsts"; eauto. (*XX*)
    set W0 := ((∅, (∅, ∅)) : WORLD).
    iMod heap_init as (heapg) "HRELS".
    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose memg := MemG Σ Hinv mem_heapg.
    pose regg := RegG Σ Hinv reg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.

    pose proof (
      @downwards_lse_preamble_spec Σ memg regg stsg heapg logrel_na_invs
    ) as Spec.

    iMod (gen_heap_alloc_gen _ reg with "Hreg_ctx") as "(Hreg_ctx & Hreg & _)".
      by apply map_disjoint_empty_r. rewrite right_id_L.
    iMod (gen_heap_alloc_gen _ m with "Hmem_ctx") as "(Hmem_ctx & Hmem & _)".
      by apply map_disjoint_empty_r. rewrite right_id_L.

    (* Extract points-to for the various regions in memory *)

    pose proof regions_disjoint as Hdisjoint.
    rewrite {2}Hm.
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_fail_flag & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hfail_flag]".
    { disjoint_map_to_list. set_solver +Hdisj_fail_flag. }
    iDestruct (big_sepM_insert with "Hfail_flag") as "[Hfail_flag _]".
      by apply lookup_empty. cbn [fst snd].
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_link_table & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hlink_table]".
    { disjoint_map_to_list. set_solver +Hdisj_link_table. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_fail & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hfail]".
    { disjoint_map_to_list. set_solver +Hdisj_fail. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_malloc_mem & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_mem]".
    { disjoint_map_to_list. set_solver +Hdisj_malloc_mem. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_malloc_memptr & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_memptr]".
    { disjoint_map_to_list. set_solver +Hdisj_malloc_memptr. }
    iDestruct (big_sepM_insert with "Hmalloc_memptr") as "[Hmalloc_memptr _]".
      by apply lookup_empty. cbn [fst snd].
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_malloc_code & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hmalloc_code]".
    { disjoint_map_to_list. set_solver +Hdisj_malloc_code. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_adv & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hadv]".
    { disjoint_map_to_list. set_solver +Hdisj_adv. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_stack & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hstack]".
    { disjoint_map_to_list. set_solver +Hdisj_stack. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_lse_body & Hdisjoint).
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hlse_body]".
    { disjoint_map_to_list. set_solver +Hdisj_lse_body. }
    rewrite disjoint_list_cons in Hdisjoint |- *. intros (Hdisj_lse_preamble & _).
    iDestruct (big_sepM_union with "Hmem") as "[Hlse_link Hlse_preamble]".
    { disjoint_map_to_list. set_solver +Hdisj_lse_preamble. }
    iDestruct (big_sepM_insert with "Hlse_link") as "[Hlse_link _]". by apply lookup_empty.
    cbn [fst snd].
    clear Hdisj_fail_flag Hdisj_link_table Hdisj_fail Hdisj_malloc_mem Hdisj_malloc_memptr
          Hdisj_malloc_code Hdisj_adv Hdisj_stack Hdisj_lse_body Hdisj_lse_preamble.

    (* Massage points-to into sepL2s with permission-pointsto *)

    iDestruct (mkregion_prepare with "[$Hlink_table]") as ">Hlink_table". by apply link_table_size.
    iDestruct (mkregion_prepare with "[$Hfail]") as ">Hfail". by apply fail_size.
    iDestruct (mkregion_prepare with "[$Hmalloc_mem]") as ">Hmalloc_mem".
    { rewrite replicate_length /region_size. clear.
      generalize malloc_mem_start malloc_end malloc_mem_size. solve_addr. }
    iDestruct (mkregion_prepare with "[$Hmalloc_code]") as ">Hmalloc_code".
      by apply malloc_code_size.
    iDestruct (mkregion_prepare with "[$Hadv]") as ">Hadv". simpl. clear -adv_size. solve_addr.
    (* Keep the stack as a sepM, it'll be easier to allocate the corresponding
       uninitialized region later. *)
    iDestruct (mkregion_prepare with "[$Hlse_preamble]") as ">Hlse_preamble".
      by apply lse_preamble_size.
    iDestruct (mkregion_prepare with "[$Hlse_body]") as ">Hlse_body". simpl. by apply lse_body_size.
    rewrite -/(lse _ _ _ _) -/(downwards_lse_preamble _ _ _ _).

    (* Split the link table *)

    rewrite (region_addrs_cons link_table_start link_table_end).
    2: { generalize link_table_size; clear; solve_addr. }
    set link_entry_fail := ^(link_table_start + 1)%a.
    rewrite (region_addrs_cons link_entry_fail link_table_end).
    2: { generalize link_table_size; clear. subst link_entry_fail.
         generalize link_table_start link_table_end. solve_addr. }
    rewrite (_: ^(link_entry_fail + 1)%a = link_table_end).
    2: { generalize link_table_size; clear. subst link_entry_fail.
         generalize link_table_start link_table_end. solve_addr. }
    iDestruct (big_sepL2_cons with "Hlink_table") as "[Hlink1 Hlink_table]".
    iDestruct (big_sepL2_cons with "Hlink_table") as "[Hlink2 _]".

    (* Allocate relevant invariants *)

    (* First we want to assert that the stack and the malloc region is disjoint *)
    iAssert (⌜∀ k,
      is_Some (mkregion stack_start stack_end stack_val !! k) →
      k ∉ region_addrs malloc_start malloc_memptr⌝)%I
    as %Hstack_adv_disj1.
    { iIntros (k Hk Hk'). destruct Hk.
      iDestruct (big_sepM_lookup _ _ k with "Hstack") as "Hk"; eauto.
      apply elem_of_list_lookup in Hk'. destruct Hk' as [i Hi].
      iDestruct (big_sepL2_length with "Hmalloc_code") as %Hlen.
      destruct (lookup_lt_is_Some_2 malloc_subroutine_instrs i).
      { rewrite -Hlen. simplify_eq. apply lookup_lt_is_Some_1. eauto. }
      iDestruct (big_sepL2_lookup _ _ _ i with "Hmalloc_code") as "Hk'"; eauto.
      iApply (addr_dupl_false with "[Hk] [Hk']"). done. done. }
    iAssert (⌜∀ k,
      is_Some (mkregion stack_start stack_end stack_val !! k) →
      k ≠ malloc_memptr⌝)%I
    as %Hstack_adv_disj2.
    { iIntros (k Hk Hk'). destruct Hk.
      iDestruct (big_sepM_lookup _ _ k with "Hstack") as "Hk"; eauto. subst k.
      iApply (addr_dupl_false with "[$Hk] [$Hmalloc_memptr]"). }
    iAssert (⌜∀ k,
      is_Some (mkregion stack_start stack_end stack_val !! k) →
      k ∉ region_addrs malloc_mem_start malloc_end⌝)%I
    as %Hstack_adv_disj3.
    { iIntros (k Hk Hk'). destruct Hk.
      iDestruct (big_sepM_lookup _ _ k with "Hstack") as "Hk"; eauto.
      apply elem_of_list_lookup in Hk'. destruct Hk' as [i Hi].
      iDestruct (big_sepL2_length with "Hmalloc_mem") as %Hlen.
      destruct (lookup_lt_is_Some_2 (region_addrs_zeroes malloc_mem_start malloc_end) i).
      { rewrite -Hlen. simplify_eq. apply lookup_lt_is_Some_1. eauto. }
      iDestruct (big_sepL2_lookup _ _ _ i with "Hmalloc_mem") as "Hk'"; eauto.
      iApply (addr_dupl_false with "[$Hk] [$Hk']"). }
    (* ---------------------------------------------------------------------- *)

    (* Next we want to similarly assert that the adv code and the malloc region are disjoint *)
    iAssert (⌜∀ k,
      k ∈ region_addrs adv_start adv_end →
      k ∉ region_addrs malloc_start malloc_memptr⌝)%I
    as %Hstack_adv_disj'1.
    { iIntros (k Hk Hk').
      apply elem_of_list_lookup in Hk. destruct Hk as [j Hj].
      iDestruct (big_sepL2_extract_l j with "Hadv") as "[_ Hk]";[apply Hj|].
      iDestruct "Hk" as (b) "Hk".
      apply elem_of_list_lookup in Hk'. destruct Hk' as [i Hi].
      iDestruct (big_sepL2_length with "Hmalloc_code") as %Hlen.
      destruct (lookup_lt_is_Some_2 malloc_subroutine_instrs i).
      { rewrite -Hlen. simplify_eq. apply lookup_lt_is_Some_1. eauto. }
      iDestruct (big_sepL2_lookup _ _ _ i with "Hmalloc_code") as "Hk'"; eauto.
      iApply (addr_dupl_false with "[$Hk] [$Hk']"). }
    iAssert (⌜∀ k,
      k ∈ region_addrs adv_start adv_end →
      k ≠ malloc_memptr⌝)%I
    as %Hstack_adv_disj'2.
    { iIntros (k Hk Hk'). apply elem_of_list_lookup in Hk. destruct Hk as [j Hj].
      iDestruct (big_sepL2_extract_l j with "Hadv") as "[_ Hk]";[apply Hj|].
      iDestruct "Hk" as (b) "Hk". subst k.
      iApply (addr_dupl_false with "[$Hk] [$Hmalloc_memptr]"). }
    iAssert (⌜∀ k,
      k ∈ region_addrs adv_start adv_end →
      k ∉ region_addrs malloc_mem_start malloc_end⌝)%I
    as %Hstack_adv_disj'3.
    { iIntros (k Hk Hk'). apply elem_of_list_lookup in Hk. destruct Hk as [j Hj].
      iDestruct (big_sepL2_extract_l j with "Hadv") as "[_ Hk]";[apply Hj|].
      iDestruct "Hk" as (b) "Hk".
      apply elem_of_list_lookup in Hk'. destruct Hk' as [i Hi].
      iDestruct (big_sepL2_length with "Hmalloc_mem") as %Hlen.
      destruct (lookup_lt_is_Some_2 (region_addrs_zeroes malloc_mem_start malloc_end) i).
      { rewrite -Hlen. simplify_eq. apply lookup_lt_is_Some_1. eauto. }
      iDestruct (big_sepL2_lookup _ _ _ i with "Hmalloc_mem") as "Hk'"; eauto.
      iApply (addr_dupl_false with "[$Hk] [$Hk']"). }
    (* ---------------------------------------------------------------------- *)

    iMod (inv_alloc flagN ⊤ (fail_flag ↦ₐ inl 0%Z) with "Hfail_flag")%I as "#Hinv_fail_flag".
    iMod (na_inv_alloc logrel_nais ⊤ mallocN (malloc_inv malloc_start malloc_end)
            with "[Hmalloc_code Hmalloc_memptr Hmalloc_mem]") as "#Hinv_malloc".
    { iNext. rewrite /malloc_inv. iExists malloc_memptr, malloc_mem_start.
      iFrame. iPureIntro. generalize malloc_code_size malloc_mem_size malloc_memptr_size. cbn.
      clear; solve_addr. }

    (* Allocate a reboked region for the malloc subroutine *)

    iAssert (region W0) with "[HRELS]" as "Hr".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty. }

    iMod (extend_region_revoked_sepL2 _ _ (region_addrs malloc_start malloc_end)
                                      (λne Wv, interp Wv.1 Wv.2) with "Hsts Hr") as "(Hr & #Hrels & Hsts)".
    { rewrite Forall_forall. intros x Hin. auto. }


    (* Allocate a permanent region for the adversary code *)

    iAssert (⌜∀ k,
      is_Some (mkregion stack_start stack_end stack_val !! k) →
      k ∉ region_addrs adv_start adv_end⌝)%I
    as %Hstack_adv_disj.
    { iIntros (k Hk Hk'). destruct Hk.
      iDestruct (big_sepM_lookup _ _ k with "Hstack") as "Hk"; eauto.
      apply elem_of_list_lookup in Hk'. destruct Hk' as [i Hi].
      iDestruct (big_sepL2_length with "Hadv") as %Hlen.
      destruct (lookup_lt_is_Some_2 ((inr (E, Global, malloc_start, malloc_end, malloc_start) :: adv_val)) i).
      { simpl in *. rewrite -Hlen. simplify_eq. apply lookup_lt_is_Some_1. eauto. }
      iDestruct (big_sepL2_lookup _ _ _ i with "Hadv") as "Hk'"; eauto.
      iApply (addr_dupl_false with "[$Hk] [$Hk']"). }

    assert (region_addrs malloc_start malloc_end = region_addrs malloc_start malloc_memptr
                                                                ++ malloc_memptr ::
                                                                region_addrs malloc_mem_start malloc_end) as Hmalloceq.
    { generalize malloc_code_size malloc_mem_size malloc_memptr_size. clear. intros.
      rewrite (region_addrs_split malloc_start malloc_memptr malloc_end);[|solve_addr]. f_equiv.
      rewrite (region_addrs_split malloc_memptr malloc_mem_start malloc_end);[|solve_addr].
      rewrite region_addrs_single//. }

    iDestruct (big_sepL2_cons_inv_r with "Hadv") as (x l Heq) "[Hmalloc Hadv]".
    iMod (extend_region_perm_sepL2 _ _ (x :: l) ((inr (E, Global, malloc_start, malloc_end, malloc_start)) :: adv_val) (λ Wv, interp Wv.1 Wv.2)
            with "Hsts Hr [Hmalloc Hadv]") as "(Hr & Hadv & Hsts)".
    2: {
      iApply big_sepL2_cons. iSplitL "Hmalloc".
      - (* malloc capability *) iFrame "Hmalloc". iSplit.
        2: { iAlways. iIntros (W W' Hrelated) "Hv". iApply interp_monotone_nm;eauto. }
        iApply (simple_malloc_subroutine_valid with "[$Hinv_malloc] [$Hrels]").
        rewrite /= Forall_forall. intros x' Hx'. apply std_sta_update_multiple_lookup_in_i. auto.
      - iApply (big_sepL2_mono with "Hadv").
        intros k v1 v2 Hv1 Hv2. cbn. iIntros. iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ Hadv_val Hv2) as Hncap.
         destruct v2; [| by inversion Hncap].
         rewrite fixpoint_interp1_eq /=. iSplit; eauto.
         unfold future_priv_mono. iModIntro. iIntros.
         rewrite !fixpoint_interp1_eq //=. }
    { rewrite Forall_forall -Heq. intros y Hy.
      rewrite std_sta_update_multiple_lookup_same_i.
      eapply (@lookup_empty _ (gmap Addr)); typeclasses eauto.
      rewrite Hmalloceq. apply not_elem_of_app. split;auto.
      apply not_elem_of_cons. split;auto. }
    iDestruct "Hadv" as "#Hadv". rewrite -Heq.

    set W1 := (std_update_multiple (std_update_multiple W0 (region_addrs malloc_start malloc_end) Revoked) (region_addrs adv_start adv_end) Permanent).

    iMod (extend_region_static_single_sepM _ _ _ (λ Wv, interp Wv.1 Wv.2)
            with "Hsts Hr Hstack") as "(Hr & Hstack & Hsts)"; auto.
    { intros ? HH. rewrite /W1.
      specialize (Hstack_adv_disj _ HH). specialize (Hstack_adv_disj1 _ HH).
      specialize (Hstack_adv_disj2 _ HH). specialize (Hstack_adv_disj3 _ HH).
      rewrite std_sta_update_multiple_lookup_same_i //. rewrite std_sta_update_multiple_lookup_same_i //.
      rewrite Hmalloceq. apply not_elem_of_app. split;auto.
      apply not_elem_of_cons. split;auto. }
    iDestruct (big_sepM_to_big_sepL _ (region_addrs stack_start stack_end) with "Hstack")
      as "Hstack".
    { apply region_addrs_NoDup. }
    { intros a Ha. eapply in_dom_mkregion' in Ha; [| apply stack_size].
      apply elem_of_gmap_dom in Ha; auto. }
    iDestruct "Hstack" as "#Hstack".

    set W2 := (override_uninitialize (mkregion stack_start stack_end stack_val) W1).

    (* Apply the spec, obtain that the PC is in the expression relation *)

    iAssert (((interp_expr interp reg) W2) (inr (RX, Global, lse_region_start, lse_region_end, lse_preamble_start)))
      with "[Hlse_preamble Hlse_body Hinv_malloc Hlse_link Hlink1 Hlink2]" as "HE".
    { assert (isCorrectPC_range RX Global lse_region_start lse_region_end
                                lse_preamble_start lse_body_start).
      { intros a [Ha1 Ha2]. constructor; auto.
        generalize lse_linking_ptr_size lse_preamble_size lse_body_size. revert Ha1 Ha2. clear.
        unfold downwards_lse_preamble_instrs_length. simpl. solve_addr. }
      set lse_preamble_move_addr := ^(lse_preamble_start + downwards_lse_preamble_move_offset)%a.
      assert ((lse_preamble_start + downwards_lse_preamble_move_offset)%a = Some lse_preamble_move_addr).
      { clear. subst lse_preamble_move_addr.
        generalize lse_preamble_size.
        unfold downwards_lse_preamble_instrs_length, downwards_lse_preamble_move_offset.
        generalize lse_preamble_start lse_body_start. solve_addr. }
      assert (lse_preamble_move_addr + offset_to_lse = Some lse_body_start)%a.
      { generalize lse_preamble_size.
        unfold lse_preamble_move_addr, offset_to_lse, downwards_lse_preamble_instrs_length.
        unfold downwards_lse_preamble_move_offset. clear.
        generalize lse_preamble_start lse_body_start. solve_addr. }
      assert (isCorrectPC_range RX Global lse_region_start lse_region_end
                                lse_body_start lse_region_end).
      { intros a [Ha1 Ha2]. constructor; auto.
        generalize lse_linking_ptr_size lse_preamble_size lse_body_size. revert Ha1 Ha2; clear.
        unfold downwards_lse_preamble_instrs_length. simpl. solve_addr. }

      iApply (Spec with "[$Hinv_malloc $Hlse_body $Hlse_preamble $Hlse_link $Hlink1 $Hlink2]");
        try eassumption.
      - apply contiguous_between_region_addrs. generalize lse_preamble_size; clear.
        unfold downwards_lse_preamble_instrs_length. solve_addr.
      - apply le_addr_withinBounds. clear; solve_addr.
        generalize link_table_size; clear; solve_addr.
      - subst link_entry_fail. apply le_addr_withinBounds.
        generalize link_table_start; clear; solve_addr.
        generalize link_table_start link_table_end link_table_size. clear; solve_addr.
      - clear; generalize link_table_start; solve_addr.
      - clear; subst link_entry_fail;
        generalize link_table_start link_table_end link_table_size; solve_addr.
      - apply contiguous_between_region_addrs. generalize lse_body_size; clear.
        simpl. solve_addr. }

    clear Hm Spec. rewrite /interp_expr /=.

    (* prepare registers *)

    unfold is_initial_registers in Hreg.
    destruct Hreg as (HPC & Hstk & Hr0 & Hrothers).

    (* Specialize the expression relation, showing that registers are valid *)

    iSpecialize ("HE" with "[Hreg Hr Hsts Hna]").
    { iFrame. iSplit; cycle 1.
      { iFrame. rewrite /registers_mapsto. by rewrite insert_id. }
      { iSplit. iPureIntro; intros; by apply initial_registers_full_map.
        (* All capabilities in registers are valid! *)
        iIntros (r HrnPC).
        (* r0 (return pointer to the adversary) is valid. Prove it using the
           fundamental theorem. *)
        destruct (decide (r = r_t0)) as [ -> |].
        { rewrite /RegLocate Hr0 fixpoint_interp1_eq /=.
          iAssert
            ([∗ list] a ∈ region_addrs adv_start adv_end,
             read_write_cond a (fixpoint interp1) ∧ ⌜std W2 !! a = Some Permanent⌝)%I
            as "#Hrwcond".
          { iApply (big_sepL_mono with "Hadv"). iIntros (k v Hkv). cbn.
            iIntros "H". rewrite /read_write_cond /=. iFrame. iPureIntro.
            rewrite override_uninitialize_std_sta_lookup_none.
            { eapply std_sta_update_multiple_lookup_in_i, elem_of_list_lookup_2; eauto. }
            apply not_elem_of_dom. intro Hv. eapply Hstack_adv_disj. by rewrite elem_of_gmap_dom //.
            eapply elem_of_list_lookup_2; eauto. }
          auto. }

        (* Stack: trivially valid because fully uninitialized *)
        destruct (decide (r = r_stk)) as [ -> |].
        { rewrite /RegLocate Hstk fixpoint_interp1_eq /=.
          rewrite (region_addrs_empty stack_start (addr_reg.min _ _)) /=.
          2: clear; solve_addr. iSplitR; [auto|].
          rewrite (_: addr_reg.max stack_start stack_start = stack_start). 2: clear; solve_addr.
          iApply (big_sepL_mono with "Hstack").
          iIntros (? ? Hk) "H". iDestruct "H" as (?) "?".
          rewrite /read_write_cond /region_state_U_pwl_mono. iFrame.
          iPureIntro. right.
          assert (is_Some (mkregion stack_start stack_end stack_val !! y)) as [? ?].
          { rewrite elem_of_gmap_dom //. apply in_dom_mkregion'. apply stack_size.
            eapply elem_of_list_lookup_2; eauto. }
          unfold W2. eexists. rewrite /std. apply override_uninitialize_std_sta_lookup_some; eauto. }

        (* Other registers *)
        rewrite /RegLocate.
        destruct (Hrothers r) as [rw [Hrw Hncap] ]. set_solver.
        destruct rw; [| by inversion Hncap].
        by rewrite Hrw fixpoint_interp1_eq /=. } }

    (* We get a WP; conclude using the rest of the Iris adequacy theorem *)

    iDestruct "HE" as "[_ HWP]". unfold interp_conf.

    iModIntro.
    (* Same as the state_interp of [memG_irisG] in rules_base.v *)
    iExists (fun σ κs _ => ((gen_heap_ctx σ.1) ∗ (gen_heap_ctx σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    iSplitL "HWP". { iApply (wp_wand with "HWP"). eauto. }
    iIntros "[Hreg' Hmem']". iExists (⊤ ∖ ↑flagN).
    iInv flagN as ">Hflag" "Hclose".
    iDestruct (gen_heap_valid with "Hmem' Hflag") as %Hm'_flag.
    iModIntro. iPureIntro. apply Hm'_flag.
  Qed.

End Adequacy.

Theorem downwards_lse_adequacy `{MachineParameters} `{memory_layout}
        (m m': Mem) (reg reg': Reg) (es: list cap_lang.expr):
  is_initial_memory m →
  is_initial_registers reg →
  rtc erased_step ([Seq (Instr Executable)], (reg, m)) (es, (reg', m')) →
  m' !! fail_flag = Some (inl 0%Z).
Proof.
  set (Σ := #[invΣ; gen_heapΣ Addr Word; gen_heapΣ RegName Word;
              na_invΣ;
              STS_preΣ Addr region_type; heapPreΣ;
              savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * Word)
      ]).
  eapply (@downwards_lse_adequacy' Σ); typeclasses eauto.
Qed.
