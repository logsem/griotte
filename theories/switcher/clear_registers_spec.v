From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import memory_region rules proofmode.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export cap_lang seal_store region_invariants.
From iris.algebra Require Export gmap agree auth excl_auth.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine Require Import rules_base.
From cap_machine Require Export clear_registers.


Section ClearRegistersMacro.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {heapg : heapGS Σ}
    `{MP: MachineParameters}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition dom_arg_rmap (nargs : nat) : gset RegName :=
    let rargs := [ca0 ; ca1 ; ca2 ; ca3 ; ca4 ; ca5 ; ct0] in
    list_to_set (firstn nargs rargs).

  Definition is_arg_rmap (rmap : Reg) (nargs : nat) :=
    dom rmap = dom_arg_rmap nargs.

  Lemma rclear_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (l : list RegName)
    (rmap : Reg) φ :
    l ≠ [] ->
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (rclear_instrs' l ))%a ->

    dom rmap = list_to_set l  ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag pc_a (rclear_instrs' l)
      ∗ ▷ ( (∃ (rmap' : Reg),
              ⌜ dom rmap' = list_to_set l ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (rclear_instrs' l ))%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a (rclear_instrs' l))
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hne Hx Hbounds Hdom) "(HPC & Hregs & Hcode & Hcont)".
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
    { subst l. iApply "Hcont". iFrame.
      replace (delete r rmap) with (∅ : Reg).
      2: { symmetry.
           rewrite -dom_empty_iff_L.
           rewrite dom_delete_L.
           rewrite Hrdom.
           set_solver.
         }
      iExists (<[r := WInt 0]> ∅).
      iSplit; cycle 1.
      + iDestruct (big_sepM_insert (fun r w => r ↦ᵣ w ∗ ⌜ w = WInt 0⌝ )%I ∅ r with "[Hr Hregs]") as "H".
        { done. }
        { iFrame. iSplit; done. }
        iFrame "H".
      + iPureIntro ; set_solver.
    }

   iAssert (codefrag (pc_a ^+ 1)%a (rclear_instrs' l) ∗
             (codefrag (pc_a ^+ 1)%a (rclear_instrs' l) -∗ codefrag pc_a (rclear_instrs' (r :: l))))%I
    with "[Hcode]" as "[Hcode Hcls]".
    { cbn. unfold codefrag. rewrite (region_pointsto_cons _ (pc_a ^+ 1)%a). 2,3: solve_addr.
      iDestruct "Hcode" as "[? Hr]".
      rewrite (_: ((pc_a ^+ 1) ^+ (length (rclear_instrs' l)))%a =
                    (pc_a ^+ (S (length (rclear_instrs' l))))%a). 2: solve_addr.
      iFrame. eauto. }

    match goal with H : SubBounds _ _ _ _ |- _ =>
      rewrite (_: (pc_a ^+ (length (rclear_instrs' (r :: l))))%a =
                  ((pc_a ^+ 1)%a ^+ length (rclear_instrs' l))%a) in H |- *
    end.
    2: { unfold rclear_instrs'; cbn; solve_addr. }

    destruct (decide (r ∈ l)).
    - iDestruct (big_sepM_insert _ _ r with "[Hr $Hregs]") as "Hregs".
      { by rewrite lookup_delete//. }
      { by iFrame. }
      iApply ("IH" with "[] HPC Hregs Hcode [Hcont Hcls]"); eauto.
      { iNext.
        iIntros "H"; iDestruct "H" as (rmap' Hdom_rmap')  "(HPC & Hregs & Hcode)".
        iApply "Hcont"; iFrame.
        iDestruct ("Hcls" with "Hcode") as "$".
        iPureIntro; set_solver.
      }
      { iPureIntro; solve_pure_addr. }
      {  iPureIntro. rewrite insert_delete_insert. set_solver. }
    - iApply ("IH" with "[] HPC Hregs Hcode [Hcont Hcls Hr]"); eauto.
      { iNext.
        iIntros "H"; iDestruct "H" as (rmap' Hdom_rmap')  "(HPC & Hregs & Hcode)".
        iDestruct (big_sepM_insert _ _ r with "[Hr $Hregs]") as "Hregs".
        { rewrite -not_elem_of_dom Hdom_rmap'; set_solver. }
        { iFrame. done. }
        iApply "Hcont"; iFrame.
        iDestruct ("Hcls" with "Hcode") as "$".
        iPureIntro; set_solver.
      }
      { iPureIntro; solve_pure_addr. }
      {  iPureIntro; set_solver. }
  Qed.

  Lemma clear_registers_post_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : Reg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_post_call_instrs)%a ->

    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag pc_a clear_registers_post_call_instrs
      ∗ ▷ ( (∃ (rmap' : Reg),
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_post_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a clear_registers_post_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom) "(HPC & Hregs & Hcode & Hcont)".
    iApply (rclear_spec _ _ _ _ _ registers_post_call); eauto.
    iFrame.
  Qed.

  Lemma clear_registers_pre_call_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (rmap : Reg) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_instrs)%a ->

    dom rmap = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      ∗ codefrag pc_a clear_registers_pre_call_instrs
      ∗ ▷ ( (∃ (rmap' : Reg),
              ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ PC ; cra ; cgp ; csp ]}) ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_instrs)%a
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ codefrag pc_a clear_registers_pre_call_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hx Hbounds Hdom) "(HPC & Hregs & Hcode & Hcont)".
    iApply (rclear_spec _ _ _ _ _ registers_pre_call); eauto.
    iFrame.
  Qed.

End ClearRegistersMacro.
