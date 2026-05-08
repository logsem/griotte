From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import memory_region rules proofmode.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export cap_lang region_invariants.
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
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ}
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
    + iDestruct (big_sepM_insert _ _ r with "[Hr $Hregs]") as "Hregs".
      { by rewrite lookup_delete_eq//. }
      { by iFrame. }
      iApply ("IH" with "[] HPC Hregs Hcode [Hcont Hcls]"); eauto.
      { iNext.
        iIntros "H"; iDestruct "H" as (rmap' Hdom_rmap')  "(HPC & Hregs & Hcode)".
        iApply "Hcont"; iFrame.
        iDestruct ("Hcls" with "Hcode") as "$".
        iPureIntro; set_solver.
      }
      { iPureIntro; solve_pure_addr. }
      {  iPureIntro. rewrite insert_delete_eq. set_solver. }
    + iApply ("IH" with "[] HPC Hregs Hcode [Hcont Hcls Hr]"); eauto.
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


  Lemma clear_registers_pre_call_skip_spec_known
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (arg_rmap : Reg) (nargs : nat)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a ->

    is_arg_rmap arg_rmap 8 ->
    (1 <= nargs <= 8)%nat ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ct2 ↦ᵣ WInt (Z.of_nat nargs)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg )
      ∗ codefrag pc_a clear_registers_pre_call_skip_instrs
      ∗ ▷ ( (∃ arg_rmap',
              ⌜ is_arg_rmap arg_rmap' 8 ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a
              ∗ ct2 ↦ᵣ WInt (Z.of_nat nargs)
              ∗ (  [∗ map] rarg↦warg ∈ arg_rmap',
                     rarg ↦ᵣ warg
                     ∗ if decide (rarg ∈ dom_arg_rmap (nargs-1))
                       then ⌜ arg_rmap !! rarg = Some warg ⌝
                       else ⌜ warg = WInt 0 ⌝
                )
              ∗ codefrag pc_a clear_registers_pre_call_skip_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hexec Hbounds Hargmap Hz) "(HPC & Hct2 & Hargs & Hcode & Hcont)".
    codefrag_facts "Hcode". clear H0.

    assert (∃ w0 w1 w2 w3 w4 w5 w, arg_rmap = <[ca0:=w0]> (<[ca1:=w1]> (<[ca2:=w2]> (<[ca3:=w3]> (<[ca4:=w4]>
             (<[ca5:=w5]> (<[ct0:=w]> ∅))))))) as [w0 [w1 [w2 [w3 [w4 [w5 [w Heq] ] ] ] ] ] ].
    { assert (is_Some (arg_rmap !! ca0)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca1)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca2)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca3)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca4)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ca5)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      assert (is_Some (arg_rmap !! ct0)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
      exists x,x0,x1,x2,x3,x4,x5. apply map_eq.
      intros i. destruct (decide (ca0 = i));simplify_map_eq=>//.
      destruct (decide (ca1 = i));simplify_map_eq=>//.
      destruct (decide (ca2 = i));simplify_map_eq=>//.
      destruct (decide (ca3 = i));simplify_map_eq=>//.
      destruct (decide (ca4 = i));simplify_map_eq=>//.
      destruct (decide (ca5 = i));simplify_map_eq=>//.
      destruct (decide (ct0 = i));simplify_map_eq=>//.
      repeat (rewrite lookup_insert_ne; auto).
      apply not_elem_of_dom. rewrite Hargmap. set_solver. }

    rewrite Heq.
    repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
    iDestruct "Hargs" as "(Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hct0 & _)".

    (* Hardcoded proof of cases *)
    destruct (decide (1 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame. cbn.
      destruct (decide (_ ∈ ∅)) as [Hcontra|]; first set_solver+Hcontra.
      rewrite /is_arg_rmap /dom_arg_rmap; cbn.
      repeat iSplit;[|done..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (2 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; try set_solver+Hca0.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit;[|done..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (3 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit;[|done..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (4 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit;[|done..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (5 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (ca3 ∈ _)) as [Hca3|Hca3]; last set_solver+Hca3.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit;[|done..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (6 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (ca3 ∈ _)) as [Hca3|Hca3]; last set_solver+Hca3.
      destruct (decide (ca4 ∈ _)) as [Hca4|Hca4]; last set_solver+Hca4.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit;[|done..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (7 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (ca3 ∈ _)) as [Hca3|Hca3]; last set_solver+Hca3.
      destruct (decide (ca4 ∈ _)) as [Hca4|Hca4]; last set_solver+Hca4.
      destruct (decide (ca5 ∈ _)) as [Hca5|Hca5]; last set_solver+Hca5.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit;[|done..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    destruct (decide (8 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (ca3 ∈ _)) as [Hca3|Hca3]; last set_solver+Hca3.
      destruct (decide (ca4 ∈ _)) as [Hca4|Hca4]; last set_solver+Hca4.
      destruct (decide (ca5 ∈ _)) as [Hca5|Hca5]; last set_solver+Hca5.
      destruct (decide (ct0 ∈ _)) as [Hct0|Hct0]; last set_solver+Hct0.
      repeat iSplit;[|done..|done].
      iPureIntro. rewrite /is_arg_rmap !dom_insert_L. set_solver. }

    exfalso. lia.
  Qed.


End ClearRegistersMacro.
