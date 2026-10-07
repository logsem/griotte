From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import sts_multiple_updates.
From griotte Require Export logrel_binary region_invariants_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules proofmode_binary monotone_binary.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import wp_rules_interp_binary.
From griotte Require Import clear_stack_spec_binary clear_registers_spec_binary.

(** * Specifications of the switcher macros in the binary model

    Both runs execute the same macros. The stack is cleared through a
    capability that is related to itself, hence identical in both runs, and
    the cleared region is shared with the adversary through the world. *)

Section switcher_macros.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma clear_stack_interp_spec (W : WORLD) (C : CmptName) (r1 r2 : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (csp_p : Perm) (csp_g : Locality) (csp_b csp_e csp_a : Addr)
    φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (clear_stack_instrs r1 r2))%a ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->
    ( spec_ctx
      ∗ ⤇ Seq (Instr Executable)
      ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ csp ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_a
      ∗ csp ↣ᵣ WCap csp_p csp_g csp_b csp_e csp_a
      ∗ interp W C (WCap csp_p csp_g csp_b csp_e csp_a, WCap csp_p csp_g csp_b csp_e csp_a)
      ∗ r1 ↦ᵣ WInt csp_e ∗ r2 ↦ᵣ WInt csp_a
      ∗ r1 ↣ᵣ WInt csp_e ∗ r2 ↣ᵣ WInt csp_a
      ∗ codefrag pc_a (clear_stack_instrs r1 r2)
      ∗ spec_codefrag pc_a (clear_stack_instrs r1 r2)
      ∗ world_interp W C
      ∗ ▷ ( (⤇ Seq (Instr Executable)
             ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a
             ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length (clear_stack_instrs r1 r2))%a
             ∗ csp ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_a
             ∗ csp ↣ᵣ WCap csp_p csp_g csp_b csp_e csp_a
             ∗ r1 ↦ᵣ WInt 0 ∗ r2 ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_e
             ∗ r1 ↣ᵣ WInt 0 ∗ r2 ↣ᵣ WCap csp_p csp_g csp_b csp_e csp_e
             ∗ codefrag pc_a (clear_stack_instrs r1 r2)
             ∗ spec_codefrag pc_a (clear_stack_instrs r1 r2))
            ∗ world_interp W C
            -∗ WP Seq (Instr Executable) {{ φ }})
      ∗ ▷ φ FailedV
    )
      ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hpc_exec Hbounds Hr1cnull Hr2cnull)
      "(#Hctx & Hj & HPC & HsPC & Hcsp & Hscsp & Hinterp & Hr1 & Hr2 & Hsr1 & Hsr2
        & Hcode & Hscode & Hworld_interp & Hφ & Hfailed)".
    codefrag_facts "Hcode". clear H0.

    (* Sub r1 r2 r1 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Mov r2 csp *)
    iInstr_lockstep "Hscode" "Hcode".

    remember (WCap csp_p csp_g csp_b csp_e csp_a) as sp.
    iAssert (r2 ↦ᵣ WCap csp_p csp_g csp_b csp_e csp_a)%I with "[Hr2]" as "Hr2"; first by rewrite Heqsp.
    iAssert (r2 ↣ᵣ WCap csp_p csp_g csp_b csp_e csp_a)%I with "[Hsr2]" as "Hsr2"; first by rewrite Heqsp.
    iAssert (interp W C (WCap csp_p csp_g csp_b csp_e csp_a, WCap csp_p csp_g csp_b csp_e csp_a))%I
      with "[Hinterp]" as "Hinterp"; first by rewrite Heqsp.
    clear Heqsp.
    iLöb as "IH" forall (csp_a).
    iDestruct "Hinterp" as "#Hinterp".

    destruct (decide (csp_a = csp_e)).
    - (* the loop has ended *)
      replace (csp_a - csp_e)%Z with 0%Z by solve_addr.
      (* Jnz 2 r1 *)
      iInstr_lockstep "Hscode" "Hcode".
      (* Jmp 5 *)
      iInstr_lockstep "Hscode" "Hcode".
      iApply "Hφ". subst. iFrame.
    - (* another iteration (or failure) *)
      (* Jnz 2 r1 *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: intros Hcontr; inversion Hcontr; solve_addr.

      (* Store r2 0 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
      wp_instr.
      iApply (wp_store_interp_z_cap with "[$Hctx $Hj $HPC $HsPC $Hi $Hsi $Hworld_interp $Hr2 $Hsr2 $Hinterp]")
      ; try solve_pure; try solve_ndisj.
      iIntros "!>" (v) "[-> | (-> & Hj & HPC & HsPC & Hi & Hsi & Hr2 & Hsr2
      & Hworld_interp & %Hwa & _)] /=".
      { wp_pure. wp_end. iFrame. }
      wp_pure.
      iSpecSeq.
      iSpecialize ("Hcode" with "[$]").
      iSpecialize ("Hscode" with "[$]").

      (* Lea r2 1 *)
      destruct (csp_a + 1)%a eqn:Ha;cycle 1.
      { iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hr2]")
        ; try solve_pure
        ; eauto.
        iIntros "!> _". wp_pure. wp_end. iFrame. }
      iInstr_lockstep "Hscode" "Hcode".

      (* Add r1 r1 1 *)
      iInstr_lockstep "Hscode" "Hcode".

      (* Jmp -5 *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: instantiate (1:=(pc_a ^+ 2)%a); solve_addr.

      replace (csp_a - csp_e + 1)%Z with (f - csp_e)%Z by solve_addr.
      iApply ("IH" $! f with "Hworld_interp Hφ Hfailed [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] []").
      iApply interp_lea;eauto.
      destruct csp_p,rx,w;auto. done.
  Qed.

  Lemma clear_registers_pre_call_skip_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (arg_rmap arg_smap : Reg) (nargs : nat)
    (W : WORLD) (C : CmptName) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a ->

    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->
    (1 <= nargs <= 8)%nat ->

    ( spec_ctx
      ∗ ⤇ Seq (Instr Executable)
      ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e pc_a
      ∗ ct2 ↦ᵣ WInt (Z.of_nat nargs)
      ∗ ct2 ↣ᵣ WInt (Z.of_nat nargs)
      ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
            rarg ↦ᵣ warg
            ∗ rarg ↣ᵣ sarg
            ∗ if decide (rarg ∈ dom_arg_rmap (nargs-1))
              then interp W C (warg, sarg)
              else True
        )
      ∗ codefrag pc_a clear_registers_pre_call_skip_instrs
      ∗ spec_codefrag pc_a clear_registers_pre_call_skip_instrs
      ∗ ▷ ( (∃ arg_rmap' arg_smap',
              ⌜ is_arg_rmap arg_rmap' 8 ⌝
              ∗ ⌜ is_arg_rmap arg_smap' 8 ⌝
              ∗ ⤇ Seq (Instr Executable)
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a
              ∗ PC ↣ᵣ WCap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)%a
              ∗ ct2 ↦ᵣ WInt (Z.of_nat nargs)
              ∗ ct2 ↣ᵣ WInt (Z.of_nat nargs)
              ∗ (  [∗ map] rarg↦warg;sarg ∈ arg_rmap';arg_smap',
                     rarg ↦ᵣ warg
                     ∗ rarg ↣ᵣ sarg
                     ∗ if decide (rarg ∈ dom_arg_rmap (nargs-1))
                       then interp W C (warg, sarg)
                       else ⌜ warg = WInt 0 ∧ sarg = WInt 0 ⌝
                )
              ∗ codefrag pc_a clear_registers_pre_call_skip_instrs
              ∗ spec_codefrag pc_a clear_registers_pre_call_skip_instrs)
               -∗ WP Seq (Instr Executable) {{ φ }})
    )
    ⊢ WP Seq (Instr Executable) {{ φ }}%I.
  Proof.
    iIntros (Hexec Hbounds Hargmap Hargsmap Hz)
      "(#Hctx & Hj & HPC & HsPC & Hct2 & Hsct2 & Hargs & Hcode & Hscode & Hcont)".
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
    assert (∃ w0 w1 w2 w3 w4 w5 w, arg_smap = <[ca0:=w0]> (<[ca1:=w1]> (<[ca2:=w2]> (<[ca3:=w3]> (<[ca4:=w4]>
             (<[ca5:=w5]> (<[ct0:=w]> ∅))))))) as [s0 [s1 [s2 [s3 [s4 [s5 [s Hseq] ] ] ] ] ] ].
    { assert (is_Some (arg_smap !! ca0)) as [??];[apply elem_of_dom; rewrite Hargsmap; set_solver|].
      assert (is_Some (arg_smap !! ca1)) as [??];[apply elem_of_dom; rewrite Hargsmap; set_solver|].
      assert (is_Some (arg_smap !! ca2)) as [??];[apply elem_of_dom; rewrite Hargsmap; set_solver|].
      assert (is_Some (arg_smap !! ca3)) as [??];[apply elem_of_dom; rewrite Hargsmap; set_solver|].
      assert (is_Some (arg_smap !! ca4)) as [??];[apply elem_of_dom; rewrite Hargsmap; set_solver|].
      assert (is_Some (arg_smap !! ca5)) as [??];[apply elem_of_dom; rewrite Hargsmap; set_solver|].
      assert (is_Some (arg_smap !! ct0)) as [??];[apply elem_of_dom; rewrite Hargsmap; set_solver|].
      exists x,x0,x1,x2,x3,x4,x5. apply map_eq.
      intros i. destruct (decide (ca0 = i));simplify_map_eq=>//.
      destruct (decide (ca1 = i));simplify_map_eq=>//.
      destruct (decide (ca2 = i));simplify_map_eq=>//.
      destruct (decide (ca3 = i));simplify_map_eq=>//.
      destruct (decide (ca4 = i));simplify_map_eq=>//.
      destruct (decide (ca5 = i));simplify_map_eq=>//.
      destruct (decide (ct0 = i));simplify_map_eq=>//.
      repeat (rewrite lookup_insert_ne; auto).
      apply not_elem_of_dom. rewrite Hargsmap. set_solver. }

    rewrite Heq Hseq.
    repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
    iDestruct "Hargs" as "((Hca0 & Hsca0 & #Hca0v) & (Hca1 & Hsca1 & #Hca1v) & (Hca2 & Hsca2 & #Hca2v)
    & (Hca3 & Hsca3 & #Hca3v) & (Hca4 & Hsca4 & #Hca4v) & (Hca5 & Hsca5 & #Hca5v) & (Hct0 & Hsct0 & #Hct0v) & _)".

    (* Hardcoded proof of cases *)
    destruct (decide (1 = nargs));[subst|].
    { iGo_lockstep "Hscode" "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
      iFrame. cbn.
      destruct (decide (_ ∈ ∅)) as [Hcontra|]; first set_solver+Hcontra.
      rewrite /is_arg_rmap /dom_arg_rmap; cbn.
      repeat iSplit; try done.
      all: iPureIntro; rewrite /is_arg_rmap !dom_insert_L; set_solver. }

    destruct (decide (2 = nargs));[subst|].
    { iGo_lockstep "Hscode" "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; try set_solver+Hca0.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit; try done.
      all: iPureIntro; rewrite /is_arg_rmap !dom_insert_L; set_solver. }

    destruct (decide (3 = nargs));[subst|].
    { iGo_lockstep "Hscode" "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit; try done.
      all: iPureIntro; rewrite /is_arg_rmap !dom_insert_L; set_solver. }

    destruct (decide (4 = nargs));[subst|].
    { iGo_lockstep "Hscode" "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit; try done.
      all: iPureIntro; rewrite /is_arg_rmap !dom_insert_L; set_solver. }

    destruct (decide (5 = nargs));[subst|].
    { iGo_lockstep "Hscode" "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (ca3 ∈ _)) as [Hca3|Hca3]; last set_solver+Hca3.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit; try done.
      all: iPureIntro; rewrite /is_arg_rmap !dom_insert_L; set_solver. }

    destruct (decide (6 = nargs));[subst|].
    { iGo_lockstep "Hscode" "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (ca3 ∈ _)) as [Hca3|Hca3]; last set_solver+Hca3.
      destruct (decide (ca4 ∈ _)) as [Hca4|Hca4]; last set_solver+Hca4.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit; try done.
      all: iPureIntro; rewrite /is_arg_rmap !dom_insert_L; set_solver. }

    destruct (decide (7 = nargs));[subst|].
    { iGo_lockstep "Hscode" "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (ca3 ∈ _)) as [Hca3|Hca3]; last set_solver+Hca3.
      destruct (decide (ca4 ∈ _)) as [Hca4|Hca4]; last set_solver+Hca4.
      destruct (decide (ca5 ∈ _)) as [Hca5|Hca5]; last set_solver+Hca5.
      destruct (decide (_ ∈ _)) as [Hcontra|Hcontra]; first set_solver+Hcontra.
      repeat iSplit; try done.
      all: iPureIntro; rewrite /is_arg_rmap !dom_insert_L; set_solver. }

    destruct (decide (8 = nargs));[subst|].
    { iGo_lockstep "Hscode" "Hcode".
      iApply "Hcont".
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      iExists (<[ca0:=_]> (<[ca1:=_]> (<[ca2:=_]> (<[ca3:=_]> (<[ca4:=_]> (<[ca5:=_]> (<[ct0:=_]> ∅))))))).
      repeat (rewrite big_sepM2_insert;[|simplify_map_eq=>//..]).
      iFrame "∗ #".
      destruct (decide (ca0 ∈ _)) as [Hca0|Hca0]; last set_solver+Hca0.
      destruct (decide (ca1 ∈ _)) as [Hca1|Hca1]; last set_solver+Hca1.
      destruct (decide (ca2 ∈ _)) as [Hca2|Hca2]; last set_solver+Hca2.
      destruct (decide (ca3 ∈ _)) as [Hca3|Hca3]; last set_solver+Hca3.
      destruct (decide (ca4 ∈ _)) as [Hca4|Hca4]; last set_solver+Hca4.
      destruct (decide (ca5 ∈ _)) as [Hca5|Hca5]; last set_solver+Hca5.
      destruct (decide (ct0 ∈ _)) as [Hct0|Hct0]; last set_solver+Hct0.
      repeat iSplit; try done.
      all: iPureIntro; rewrite /is_arg_rmap !dom_insert_L; set_solver. }

    exfalso. lia.
  Qed.


End switcher_macros.
