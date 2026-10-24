From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import clear_registers_spec.

(** The argument-clearing macro, with the number of arguments known. *)

Section ClearRegistersSkipMacro.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  Lemma clear_registers_pre_call_skip_spec_known
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (arg_rmap : LReg) (nargs : nat)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a ->

    is_arg_rmap arg_rmap 8 ->
    (1 <= nargs <= 8)%nat ->

    ( PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a
      ∗ ct2 ↦ᵣ WInt (Z.of_nat nargs)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg )
      ∗ codefrag_pers pc_a clear_registers_pre_call_skip_instrs
      ∗ ▷ ( (∃ arg_rmap',
              ⌜ is_arg_rmap arg_rmap' 8 ⌝
              ∗ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a
              ∗ ct2 ↦ᵣ WInt (Z.of_nat nargs)
              ∗ (  [∗ map] rarg↦warg ∈ arg_rmap',
                     rarg ↦ᵣ warg
                     ∗ if decide (rarg ∈ dom_arg_rmap (nargs-1))
                       then ⌜ arg_rmap !! rarg = Some warg ⌝
                       else ⌜ warg = WInt 0 ⌝
                )
              ∗ codefrag_pers pc_a clear_registers_pre_call_skip_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hexec Hbounds Hargmap Hz) "(HPC & Hct2 & Hargs & #Hcode & Hcont)".
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
      iFrame "∗ #". cbn.
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

End ClearRegistersSkipMacro.
