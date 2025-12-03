From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel region_invariants.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import rules proofmode monotone.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.
From cap_machine Require Import wp_rules_interp.
From cap_machine Require Import clear_stack clear_registers.

Section switcher_macros.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma clear_stack_interp_spec (W : WORLD) (C : CmptName) (r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (csp_p : Perm) (csp_g : Locality) (csp_b csp_e csp_a : Addr)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs r1 r2))%a ->
    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ csp ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_a
      ∗ interp W C (WCap csp_p csp_g csp_b csp_e csp_a)
      ∗ r1 ↦ᵣ WInt csp_e ∗ r2 ↦ᵣ WInt csp_a
      ∗ codefrag pc_a (clear_stack_instrs r1 r2)
      ∗ region W C
      ∗ sts_full_world W C
      ∗ ▷ ( (PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a
             ∗ csp ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_a
             ∗ r1 ↦ᵣ WInt 0 ∗ r2 ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_e
             ∗ codefrag pc_a (clear_stack_instrs r1 r2))
             ∗ region W C ∗ sts_full_world W C
            -∗ WP Seq (Instr Executable) {{ φ }})
      ∗ ▷ φ FailedV
    )
      ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds)
      "(HPC & Hcsp & Hinterp & Hr1 & Hr2 & Hcode & Hr & Hsts & Hφ & Hfailed)".
    codefrag_facts "Hcode". clear H0.

    (* --- Sub r1 r2 r1 --- *)
    iInstr "Hcode".

    (* --- Mov r2 csp --- *)
    iInstr "Hcode".

    remember (WCap csp_p csp_g csp_b csp_e csp_a) as sp.
    rewrite{1 3} Heqsp. clear Heqsp.
    iLöb as "IH" forall (csp_a).
    iDestruct "Hinterp" as "#Hinterp".

    destruct (decide (csp_a = csp_e)).
    - (* csp_a = csp_2 ==> loop has ended *)
      replace (csp_a - csp_e)%Z with 0%Z by solve_addr.
      (* --- Jnz 2 r1 --- *)
      iInstr "Hcode".
      (* --- Jmp 5 ---- *)
      iInstr "Hcode".
      iApply "Hφ". subst. iFrame.
    - (* csp_a ≠ csp_2 ==> another iteration (or failure) *)
      (* --- Jnz 2 r1 --- *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hr1]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; solve_addr. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").

      (* --- Store r2 0%Z --- *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_interp_z_cap with "[$HPC $Hi $Hr $Hsts Hr2]"); try solve_pure.
      { iFrame "∗ #". }
      iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hr2
      & Hr & Hsts & %Hwa & _)] /=".
      { wp_pure. wp_end. iFrame. }
      wp_pure.
      iSpecialize ("Hcode" with "[$]").

      (* --- Lea r2 1 --- *)
      destruct (csp_a + 1)%a eqn:Ha;cycle 1.
      { iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hr2]")
        ; try solve_pure
        ; eauto.
        iIntros "!> _". wp_pure. wp_end. iFrame. }
      iInstr "Hcode".

      (* --- Add r1 r1 1 --- *)
      iInstr "Hcode".

      (* --- Jmp -5 --- *)
      iInstr "Hcode".
      { instantiate (1:=(pc_a ^+ 2)%a). solve_addr. }

      (* IH *)
      replace (csp_a - csp_e + 1)%Z with (f - csp_e)%Z by solve_addr.
      iApply ("IH" $! f with "[] Hr Hsts Hφ Hfailed Hct2 Hcode HPC Hr2 Hcsp").
      iApply interp_lea;eauto.
      destruct csp_p,rx,w;auto. done.
  Qed.


  Lemma clear_registers_pre_call_skip_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (arg_rmap : Reg) (nargs : nat)
    (W : WORLD) (C : CmptName) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a ->

    is_arg_rmap arg_rmap 8 ->
    (1 <= nargs <= 8)%nat ->

    ( PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ct2 ↦ᵣ WInt (Z.of_nat nargs)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg
                                        ∗ if decide (rarg ∈ dom_arg_rmap (nargs-1))
                                          then interp W C warg
                                          else True
        )
      ∗ codefrag pc_a clear_registers_pre_call_skip_instrs
      ∗ ▷ ( (∃ arg_rmap',
              ⌜ is_arg_rmap arg_rmap' 8 ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a
              ∗ ct2 ↦ᵣ WInt (Z.of_nat nargs)
              ∗ (  [∗ map] rarg↦warg ∈ arg_rmap',
                     rarg ↦ᵣ warg
                     ∗ if decide (rarg ∈ dom_arg_rmap (nargs-1))
                       then interp W C warg
                       else ⌜ warg = WInt 0⌝
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
    iDestruct "Hargs" as "([Hca0 #Hca0v] & [Hca1 #Hca1v] & [Hca2 #Hca2v] & [Hca3 #Hca3v]
    & [Hca4 #Hca4v] & [Hca5 #Hca5v] & [Hct0 #Hct0v] & _)".

    (* Hardcoded proof of cases *)
    destruct (decide (1 = nargs));[subst|].
    { iGo "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM_insert;[|simplify_map_eq=>//]).
      iFrame. cbn.
      destruct (decide (_ ∈ ∅)) as [Hcontra|]; first set_solver+Hcontra.
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

    iAssert ([∗ map] r↦_ ∈ rmap, ∃ w, r ↦ᵣ w)%I with "[Hregs]" as "Hregs".
    { iApply (big_sepM_mono with "Hregs"). intros. eauto. }

    iDestruct (big_sepM_dom with "Hregs") as "Hregs".
    rewrite Hdom.

    iDestruct (big_sepS_delete _ _ cnull with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ctp with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct1 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct2 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs0 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs1 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca6 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ca7 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs2 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs3 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs4 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs5 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs6 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs7 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs8 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs9 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs10 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ cs11 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct3 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct4 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct5 with "Hregs") as "[[% ?] Hregs]";[set_solver|].
    iDestruct (big_sepS_delete _ _ ct6 with "Hregs") as "[[% ?] _]";[set_solver|].

    codefrag_facts "Hcode". clear H0.
    iGo "Hcode".

    iApply "Hcont".
    iExists (<[cnull:=_]> (<[ctp:=_]> (<[ct1:=_]> (<[ct2:=_]> (<[cs0:=_]> (<[cs1:=_]> (<[ca6:=_]> (<[ca7:=_]> (<[cs2:=_]> (<[cs3:=_]> (<[cs4:=_]> (<[cs5:=_]> (<[cs6:=_]> (<[cs7:=_]> (<[cs8:=_]> (<[cs9:=_]> (<[cs10:=_]> (<[cs11:=_]> (<[ct3:=_]> (<[ct4:=_]> (<[ct5:=_]> (<[ct6:=_]> ∅)))))))))))))))))))))).
    repeat (rewrite big_sepM_insert;[|by simplify_map_eq]).
    iFrame. iSplit.
    { iPureIntro. rewrite !dom_insert_L. set_solver. }
    repeat (iSplit;[done|]). done.
  Qed.

End switcher_macros.
