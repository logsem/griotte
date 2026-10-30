From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From iris.program_logic Require Export weakestpre.
From griotte Require Export griotte_lang region_invariants.
From iris.algebra Require Export gmap agree auth excl_auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From griotte Require Import rules_base.
From griotte Require Export clear_registers.


Section ClearRegistersMacro.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition dom_arg_rmap (nargs : nat) : gset RegName :=
    let rargs := [ca0 ; ca1 ; ca2 ; ca3 ; ca4 ; ca5 ; ct0] in
    list_to_set (firstn nargs rargs).

  Definition is_arg_rmap (rmap : LReg) (nargs : nat) :=
    dom rmap = dom_arg_rmap nargs.

  Lemma rclear_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (l : list RegName)
    (rmap : LReg) φ :
    l ≠ [] ->
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (rclear_instrs' l )) ->

    dom rmap = list_to_set l  ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag_pers pc_a (rclear_instrs' l)
      ∗ ▷ ( (∃ (rmap' : LReg),
              ⌜ dom rmap' = list_to_set l ⌝
              ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l ))
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag_pers pc_a (rclear_instrs' l))
               -∗ WP Exec {{ φ }})
    )
    ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hne Hx Hbounds Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    iRevert (Hbounds Hdom).
    iInduction (l) as [|r l] "IH" forall (rmap pc_a); iIntros (Hbounds Hrdom); first congruence.

    cbn [list_to_set] in Hrdom.
    assert (is_Some (rmap !! r)) as [rv Hr].
    { apply elem_of_dom; rewrite Hrdom; set_solver. }
    iDestruct (big_sepM_delete _ _ r with "Hregs") as "[Hr Hregs]"; eauto.
    cbn.
    codefrag_facts "Hcode".

    iApply (wp_reg_cnull_lnull with "Hr"); first done.
    iIntros (Hrv) "Hr".
    (* Mov r 0. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ 1)); auto; solve_addr. }
    iAssert (r ↦ᵣ WInt 0)%I with "[Hr]" as "Hr".
    { case_decide as Hr_cnull; last done. by rewrite (Hrv Hr_cnull). }
    destruct (decide (l = [])).
    { subst l. iApply "Hcont". iFrame "∗ #".
      replace (delete r rmap) with (∅ : LReg).
      2: { symmetry.
           rewrite -dom_empty_iff_L.
           rewrite dom_delete_L.
           rewrite Hrdom.
           set_solver.
      }
      iExists (<[r := lword_of_word (WInt 0)]> ∅).
      iSplit; cycle 1.
      + iDestruct (big_sepM_insert (fun r w => r ↦ᵣ w ∗ ⌜ w = WInt 0⌝ )%I ∅ r with "[Hr Hregs]") as "H".
        { done. }
        { iFrame. iSplit; done. }
        iFrame "H".
      + iPureIntro ; set_solver.
    }

    iAssert (codefrag_pers (pc_a ^+ 1) (rclear_instrs' l))%I as "#Hcode'".
    { iDestruct (codefrag_app_pers _ [_] with "Hcode") as "[_ $]". }

    match goal with H : SubBounds _ _ _ _ |- _ =>
      rewrite (_: pc_a ^+ (length (rclear_instrs' (r :: l))) =
                  (pc_a ^+ 1) ^+ length (rclear_instrs' l)) in H |- *
    end.
    2: { unfold rclear_instrs'; cbn; solve_addr. }

    destruct (decide (r ∈ l)).
    + iDestruct (big_sepM_insert _ _ r with "[Hr $Hregs]") as "Hregs".
      { by rewrite lookup_delete_eq//. }
      { by iFrame. }
      iApply ("IH" with "[] Hcode' HPC Hregs [Hcont]"); eauto.
      { iNext.
        iIntros "H"; iDestruct "H" as (rmap' Hdom_rmap')  "(HPC & Hregs & _)".
        iApply "Hcont"; iFrame "∗ #".
        iPureIntro; set_solver.
      }
      { iPureIntro; solve_pure_addr. }
      {  iPureIntro. rewrite insert_delete_eq. set_solver. }
    + iApply ("IH" with "[] Hcode' HPC Hregs [Hcont Hr]"); eauto.
      { iNext.
        iIntros "H"; iDestruct "H" as (rmap' Hdom_rmap')  "(HPC & Hregs & _)".
        iDestruct (big_sepM_insert _ _ r with "[Hr $Hregs]") as "Hregs".
        { rewrite -not_elem_of_dom Hdom_rmap'; set_solver. }
        { iFrame. done. }
        iApply "Hcont"; iFrame "∗ #".
        iPureIntro; set_solver.
      }
      { iPureIntro; solve_pure_addr. }
      {  iPureIntro; set_solver. }
  Qed.

  (** [rclear_spec] over a map that may also hold [cnull], which [l] does
      not clear: an owned [cnull] holds the null word, which is 0. *)
  Lemma rclear_spec_cnull
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (l : list RegName) (D : gset RegName)
    (rmap : LReg) φ :
    l ≠ [] ->
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (rclear_instrs' l )) ->
    D ∖ {[ cnull ]} = list_to_set l ->
    dom rmap = D ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag_pers pc_a (rclear_instrs' l)
      ∗ ▷ ( (∃ (rmap' : LReg),
              ⌜ dom rmap' = D ⌝
              ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l ))
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag_pers pc_a (rclear_instrs' l))
               -∗ WP Exec {{ φ }})
    )
    ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hne Hx Hbounds HD Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    assert (cnull ∉ (list_to_set l : gset RegName)) as Hl by (rewrite -HD; apply not_elem_of_difference; right; by apply elem_of_singleton).
    destruct (rmap !! cnull) as [wn|] eqn:Hn.
    - (* [cnull] is owned: split off, it holds the null word. *)
      assert (cnull ∈ D) as HnD by (rewrite -Hdom; by eapply elem_of_dom_2).
      iDestruct (big_sepM_delete _ _ cnull with "Hregs") as "[Hn Hregs]"; first done.
      iApply (wp_reg_cnull_lnull with "Hn"); first done.
      iIntros (Hwn) "Hn". rewrite (Hwn eq_refl).
      iApply (rclear_spec _ _ _ _ _ l (delete cnull rmap)); eauto.
      { rewrite dom_delete_L Hdom. done. }
      iFrame "∗ #". iNext.
      iIntros "(%rmap' & %Hdom' & HPC & Hregs & Hcode')".
      iApply "Hcont". iFrame "HPC Hcode'".
      iExists (<[cnull := lnull]> rmap'). iSplit.
      { iPureIntro. rewrite dom_insert_L Hdom' -HD. by rewrite -union_difference_singleton_L. }
      iApply (big_sepM_insert with "[$Hregs Hn]").
      { apply not_elem_of_dom. by rewrite Hdom'. }
      by iFrame.
    - (* [cnull] is not owned: the map is the cleared one. *)
      assert (cnull ∉ D) as HnD by (rewrite -Hdom; by apply not_elem_of_dom).
      iApply (rclear_spec _ _ _ _ _ l rmap); eauto.
      { rewrite Hdom -HD. symmetry. apply difference_disjoint_L. by apply disjoint_singleton_r. }
      iFrame "∗ #". iNext.
      iIntros "(%rmap' & %Hdom' & HPC & Hregs & Hcode')".
      iApply "Hcont". iFrame. iPureIntro.
      rewrite Hdom' -HD. apply difference_disjoint_L. by apply disjoint_singleton_r.
  Qed.

  Lemma list_to_set_registers_except (keep : list RegName) :
    (list_to_set (registers_except keep) : gset RegName) =
      all_registers_s ∖ ({[ cnull ]} ∪ list_to_set keep).
  Proof.
    apply set_eq. intros r.
    rewrite elem_of_list_to_set elem_of_difference elem_of_union elem_of_singleton
      elem_of_list_to_set /registers_except list_elem_of_filter.
    pose proof (all_registers_s_correct r). pose proof (all_registers_correct r).
    naive_solver.
  Qed.

  (** CHERIoT's [zeroAllRegistersExcept]: the registers but those of [keep]
      hold 0. *)
  Lemma zero_all_registers_except_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (keep : list RegName) (rmap : LReg) φ :
    let l := registers_except keep in
    l ≠ [] ->
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (rclear_instrs' l)) ->
    dom rmap = all_registers_s ∖ list_to_set keep ->

    PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
    codefrag_pers pc_a (rclear_instrs' l) ∗
    ▷ ( (∃ rmap' : LReg,
           ⌜dom rmap' = all_registers_s ∖ list_to_set keep⌝ ∗
           PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l)) ∗
           ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) ∗
           codefrag_pers pc_a (rclear_instrs' l))
        -∗ WP Exec {{ φ }})
    ⊢ WP Exec {{ φ }}.
  Proof.
    intros l. iIntros (Hne Hx Hbounds Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    iApply (rclear_spec_cnull _ _ _ _ _ l (all_registers_s ∖ list_to_set keep)); eauto.
    { rewrite /l list_to_set_registers_except. set_solver+. }
    iFrame "∗ #".
  Qed.

  Lemma clear_registers_post_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : LReg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_post_call_instrs) ->

    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag_pers pc_a clear_registers_post_call_instrs
      ∗ ▷ ( (∃ (rmap' : LReg),
              ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_post_call_instrs)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag_pers pc_a clear_registers_post_call_instrs)
               -∗ WP Exec {{ φ }})
    )
    ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    iApply (rclear_spec_cnull _ _ _ _ _ registers_post_call
              (all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]})); eauto.
    iFrame "∗ #".
  Qed.

  Lemma clear_registers_pre_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : LReg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_instrs) ->

    dom rmap = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag_pers pc_a clear_registers_pre_call_instrs
      ∗ ▷ ( (∃ (rmap' : LReg),
              ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝
              ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_instrs)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag_pers pc_a clear_registers_pre_call_instrs)
               -∗ WP Exec {{ φ }})
    )
    ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    iApply (rclear_spec_cnull _ _ _ _ _ registers_pre_call
              (all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}))); eauto.
    iFrame "∗ #".
  Qed.

  (** [rclear_spec] with a possibly empty list, and a continuation without
      later: with no register to clear, no instruction executes. *)
  Lemma rclear_spec_any
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (l : list RegName)
    (rmap : LReg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (rclear_instrs' l )) ->
    dom rmap = list_to_set l  ->
    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag_pers pc_a (rclear_instrs' l)
      ∗ ( (∃ (rmap' : LReg),
              ⌜ dom rmap' = list_to_set l ⌝
              ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l ))
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag_pers pc_a (rclear_instrs' l))
               -∗ WP Exec {{ φ }})
    )
    ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hexec Hbounds Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    destruct (decide (l = [])) as [-> | Hne]; last first.
    { iApply rclear_spec; eauto. iFrame "∗ #". }
    apply dom_empty_inv_L in Hdom as ->.
    rewrite /= (_ : pc_a ^+ 0 = pc_a); last solve_addr.
    iApply "Hcont". iExists ∅.
    rewrite dom_empty_L !big_sepM_empty.
    by iFrame "∗ #".
  Qed.

  (** Splitting a register map along a set of registers to keep. *)
  Lemma big_sepM_regs_filter_split (rmap : LReg) (keep : gset RegName) :
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ⊣⊢
    ([∗ map] r↦w ∈ filter (λ kv, kv.1 ∈ keep) rmap, r ↦ᵣ w) ∗
    ([∗ map] r↦w ∈ filter (λ kv, kv.1 ∉ keep) rmap, r ↦ᵣ w).
  Proof.
    rewrite -big_sepM_union; last apply map_disjoint_filter_complement.
    by rewrite map_filter_union_complement.
  Qed.

  (** The argument-clearing sled: a jump to its instruction [nargs] skips
      the clearing of the first [nargs] argument registers, and the rest of
      the sled clears the others, the suffix
      [drop nargs registers_pre_call_skip]. *)
  Lemma clear_registers_pre_call_skip_instrs_eq :
    clear_registers_pre_call_skip_instrs = rclear_instrs' registers_pre_call_skip.
  Proof. reflexivity. Qed.

  Lemma length_clear_registers_pre_call_skip_instrs :
    length clear_registers_pre_call_skip_instrs = 7.
  Proof. reflexivity. Qed.

  Lemma length_registers_pre_call_skip : length registers_pre_call_skip = 7.
  Proof. reflexivity. Qed.

  Lemma NoDup_registers_pre_call_skip : NoDup registers_pre_call_skip.
  Proof. rewrite /registers_pre_call_skip. repeat constructor; set_solver. Qed.

  Lemma dom_arg_rmap_take (n : nat) :
    dom_arg_rmap n = list_to_set (take n registers_pre_call_skip).
  Proof. reflexivity. Qed.

  Lemma dom_arg_rmap_subseteq (n : nat) : dom_arg_rmap n ⊆ dom_arg_rmap 8.
  Proof.
    rewrite !dom_arg_rmap_take (take_ge registers_pre_call_skip 8);
      last (rewrite length_registers_pre_call_skip; lia).
    rewrite -{2}(take_drop n registers_pre_call_skip) list_to_set_app_L.
    set_solver.
  Qed.

  Lemma list_to_set_drop_registers_pre_call_skip (n : nat) :
    (list_to_set (drop n registers_pre_call_skip) : gset RegName)
    = dom_arg_rmap 8 ∖ dom_arg_rmap n.
  Proof.
    pose proof NoDup_registers_pre_call_skip as Hnodup.
    rewrite !dom_arg_rmap_take (take_ge registers_pre_call_skip 8);
      last (rewrite length_registers_pre_call_skip; lia).
    rewrite -{1 3}(take_drop n registers_pre_call_skip) in Hnodup |- *.
    apply NoDup_app in Hnodup as (_ & Hdisj & _).
    rewrite list_to_set_app_L.
    set_solver.
  Qed.

  Lemma clear_registers_pre_call_skip_codefrag_drop (pc_a : Addr) (k : nat) :
    k <= 7 ->
    codefrag_pers pc_a clear_registers_pre_call_skip_instrs -∗
    codefrag_pers (pc_a ^+ k) (rclear_instrs' (drop k registers_pre_call_skip)).
  Proof.
    iIntros (Hk) "Hcode".
    rewrite clear_registers_pre_call_skip_instrs_eq -{1}(take_drop k registers_pre_call_skip).
    rewrite /rclear_instrs' fmap_app.
    iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode]".
    rewrite length_fmap length_take_le; last by rewrite length_registers_pre_call_skip.
    iExact "Hcode".
  Qed.

  (** The kept argument registers and the cleared ones form an argument map. *)
  Lemma clear_registers_pre_call_skip_recombine
    (arg_rmap rmap' : LReg) (keep : nat) :
    is_arg_rmap arg_rmap 8 ->
    dom rmap' = dom_arg_rmap 8 ∖ dom_arg_rmap keep ->
    ([∗ map] r↦w ∈ filter (λ kv, kv.1 ∈ dom_arg_rmap keep) arg_rmap, r ↦ᵣ w) -∗
    ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) -∗
    ∃ arg_rmap',
      ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
      [∗ map] rarg↦warg ∈ arg_rmap',
        rarg ↦ᵣ warg
        ∗ if decide (rarg ∈ dom_arg_rmap keep)
          then ⌜ arg_rmap !! rarg = Some warg ⌝
          else ⌜ warg = WInt 0 ⌝.
  Proof.
    iIntros (Hargmap Hdom') "Hkept Hcleared".
    set (kept := filter (λ kv, kv.1 ∈ dom_arg_rmap keep) arg_rmap).
    pose proof (dom_arg_rmap_subseteq keep) as Hsub.
    assert (dom kept = dom_arg_rmap keep) as Hdom_kept.
    { apply dom_filter_L. intros r.
      split; [intros Hr | intros (w & _ & Hr); exact Hr].
      assert (r ∈ dom arg_rmap) as [w Hw]%elem_of_dom by (rewrite Hargmap; set_solver).
      eauto. }
    assert (kept ##ₘ rmap') as Hdisj.
    { apply map_disjoint_dom. rewrite Hdom_kept Hdom'. set_solver. }
    iExists (kept ∪ rmap').
    iSplit.
    { iPureIntro. rewrite /is_arg_rmap dom_union_L Hdom_kept Hdom'.
      symmetry; by apply union_difference_L. }
    rewrite big_sepM_union //.
    iSplitL "Hkept".
    - iApply (big_sepM_impl with "Hkept").
      iIntros "!>" (r w Hr) "Hr".
      apply map_lookup_filter_Some in Hr as [Hr Hin].
      rewrite decide_True //. by iFrame.
    - iApply (big_sepM_impl with "Hcleared").
      iIntros "!>" (r w Hr) "[Hr %Hw]".
      assert (r ∉ dom_arg_rmap keep) as Hnin.
      { apply elem_of_dom_2 in Hr. rewrite Hdom' in Hr. set_solver. }
      rewrite decide_False //. by iFrame.
  Qed.

  (** From the instruction [nargs] of the argument-clearing sled: the first
      [nargs] argument registers keep their values, the others are
      cleared. *)
  Lemma clear_registers_pre_call_skip_spec_known
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (arg_rmap : LReg) (nargs : nat)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_skip_instrs) ->

    is_arg_rmap arg_rmap 8 ->
    (nargs <= 7)%nat ->

    ( PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ nargs)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg )
      ∗ codefrag_pers pc_a clear_registers_pre_call_skip_instrs
      ∗ ( (∃ arg_rmap',
              ⌜ is_arg_rmap arg_rmap' 8 ⌝
              ∗ PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)
              ∗ (  [∗ map] rarg↦warg ∈ arg_rmap',
                     rarg ↦ᵣ warg
                     ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                       then ⌜ arg_rmap !! rarg = Some warg ⌝
                       else ⌜ warg = WInt 0 ⌝
                )
              ∗ codefrag_pers pc_a clear_registers_pre_call_skip_instrs)
               -∗ WP Exec {{ φ }})
    )
    ⊢ WP Exec {{ φ }}%I.
  Proof.
    iIntros (Hexec Hbounds Hargmap Hnargs) "(HPC & Hargs & #Hcode & Hcont)".
    rewrite length_clear_registers_pre_call_skip_instrs in Hbounds |- *.
    iDestruct (clear_registers_pre_call_skip_codefrag_drop pc_a nargs with "Hcode")
      as "Hcode_drop"; first lia.
    iDestruct (big_sepM_regs_filter_split _ (dom_arg_rmap nargs) with "Hargs")
      as "[Hkept Hcleared]".
    iApply (rclear_spec_any _ _ _ _ _ (drop nargs registers_pre_call_skip)
             with "[- $HPC $Hcleared $Hcode_drop]"); auto.
    { rewrite /rclear_instrs' length_fmap length_drop length_registers_pre_call_skip.
      solve_addr. }
    { rewrite list_to_set_drop_registers_pre_call_skip -Hargmap.
      apply dom_filter_L. intros r.
      rewrite elem_of_difference elem_of_dom. split.
      - intros [ [w Hw] Hnin]. by exists w.
      - intros (w & Hw & Hnin). split; [by exists w | done]. }
    iIntros "(%rmap' & %Hdom' & HPC & Hcleared & _)".
    rewrite list_to_set_drop_registers_pre_call_skip in Hdom'.
    iDestruct (clear_registers_pre_call_skip_recombine with "Hkept Hcleared")
      as (arg_rmap') "[%Hargmap' Hargs]"; [done | done |].
    iApply "Hcont".
    iExists arg_rmap'.
    rewrite (_ : (pc_a ^+ nargs)
                  ^+ length (rclear_instrs' (drop nargs registers_pre_call_skip))
                 = pc_a ^+ 7%nat).
    2: { rewrite /rclear_instrs' length_fmap length_drop length_registers_pre_call_skip.
         solve_addr. }
    by iFrame "∗ #".
  Qed.

End ClearRegistersMacro.
