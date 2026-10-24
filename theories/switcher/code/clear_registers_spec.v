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
    {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
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
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (rclear_instrs' l ))%a ->

    dom rmap = list_to_set l  ->

    ( PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag_pers pc_a (rclear_instrs' l)
      ∗ ▷ ( (∃ (rmap' : LReg),
              ⌜ dom rmap' = list_to_set l ⌝
              ∗ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l ))%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag_pers pc_a (rclear_instrs' l))
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
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

    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ 1)%a); auto; solve_addr. }
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

    iAssert (codefrag_pers (pc_a ^+ 1)%a (rclear_instrs' l))%I as "#Hcode'".
    { iDestruct (codefrag_app_pers _ [_] with "Hcode") as "[_ $]". }

    match goal with H : SubBounds _ _ _ _ |- _ =>
      rewrite (_: (pc_a ^+ (length (rclear_instrs' (r :: l))))%a =
                  ((pc_a ^+ 1)%a ^+ length (rclear_instrs' l))%a) in H |- *
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

  Lemma list_to_set_registers_except (keep : list RegName) :
    (list_to_set (registers_except keep) : gset RegName) = all_registers_s ∖ list_to_set keep.
  Proof.
    apply set_eq. intros r.
    rewrite elem_of_list_to_set elem_of_difference elem_of_list_to_set
      /registers_except list_elem_of_filter.
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
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (rclear_instrs' l))%a ->
    dom rmap = all_registers_s ∖ list_to_set keep ->

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
    codefrag_pers pc_a (rclear_instrs' l) ∗
    ▷ ( (∃ rmap' : LReg,
           ⌜dom rmap' = all_registers_s ∖ list_to_set keep⌝ ∗
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l))%a ∗
           ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) ∗
           codefrag_pers pc_a (rclear_instrs' l))
        -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros l. iIntros (Hne Hx Hbounds Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    iApply (rclear_spec _ _ _ _ _ l); eauto.
    { by rewrite /l list_to_set_registers_except. }
    iFrame "∗ #". iNext.
    iIntros "(%rmap' & %Hdom' & HPC & Hregs & Hcode')".
    iApply "Hcont". iFrame. iPureIntro.
    by rewrite Hdom' /l list_to_set_registers_except.
  Qed.

  Lemma clear_registers_post_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : LReg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_post_call_instrs)%a ->

    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    ( PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag_pers pc_a clear_registers_post_call_instrs
      ∗ ▷ ( (∃ (rmap' : LReg),
              ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_post_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag_pers pc_a clear_registers_post_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    iApply (rclear_spec _ _ _ _ _ registers_post_call); eauto.
    iFrame "∗ #".
  Qed.

  Lemma clear_registers_pre_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : LReg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_instrs)%a ->

    dom rmap = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ->

    ( PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag_pers pc_a clear_registers_pre_call_instrs
      ∗ ▷ ( (∃ (rmap' : LReg),
              ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝
              ∗ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag_pers pc_a clear_registers_pre_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom) "(HPC & Hregs & #Hcode & Hcont)".
    iApply (rclear_spec _ _ _ _ _ registers_pre_call); eauto.
    iFrame "∗ #".
  Qed.


End ClearRegistersMacro.
