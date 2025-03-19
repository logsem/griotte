From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation interp_weakening.
From cap_machine Require Import logrel rules proofmode.
From cap_machine Require Import fetch assert switcher_spec cmdc.

Section CMDC.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {switcherg :switcherG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.
  Context {B C : CmptName}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).

  Ltac iHide0 irisH coqH :=
    let coqH := fresh coqH in
    match goal with
    | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
        set (coqH := prop)
    end.

  Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
    iHide0 irisH coqH.

  Lemma cmdc_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr) (a_flag : Addr)
    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (csp_content : list Word)

    (φ : language.val cap_lang -> iProp Σ)
    (Nassert Nswitcher : namespace)
    (E : coPset)
    :

    let imports :=
     cmdc_main_imports b_switcher e_switcher a_cc_switcher ot_switcher b_assert e_assert B_f C_g
    in

    ↑Nswitcher ⊆ E ->
    ↑Nassert ⊆ E ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (WInt 0) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init_B) ->
    (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    length csp_content = finz.dist csp_b csp_e ->

    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_cc_switcher ot_switcher)
      ∗ na_own logrel_nais E

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a cmdc_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ cmdc_main_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ region W_init_B B ∗ sts_full_world W_init_B B
      ∗ region W_init_C C ∗ sts_full_world W_init_C C

      ∗ interp W_init_B B (WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g)

      ∗ ▷ (
            na_own logrel_nais E
              -∗ WP Instr Halted {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
      ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcherE HNassertE Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_c Hlen_stack)
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & HWreg_B & HWstd_full_B
      & HWreg_C & HWstd_full_C
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & Hφ)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    (* TODO tactic for extracting register.... *)
    (* --- Extract registers ca0 ctp ct0 ct1 cs0 cs1 cra --- *)
    assert ( rmap !! ca0 = Some (WInt 0) ) as Hwca0.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ctp = Some (WInt 0) ) as Hwctp.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct0 = Some (WInt 0) ) as Hwct0.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct1 = Some (WInt 0) ) as Hwct1.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! cs0 = Some (WInt 0) ) as Hwcs0.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! cs1 = Some (WInt 0) ) as Hwcs1.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! cra = Some (WInt 0) ) as Hwcra.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

    (* Extract the addresses of b and c *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_c _]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_B_f Himports_main]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_g _]".
    { transitivity (Some (pc_b ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)



    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { solve_addr. }
    iHide "Hφ" as hφ.
    (* Mov ca0 cgp; *)
    iInstr "Hcode".
    (* Lea cgp 1%Z; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { solve_addr. }
    (* GetA ct0 ca0; *)
    iInstr "Hcode".
    (* Add ct1 ct0 1%Z; *)
    iInstr "Hcode".
    (* Subseg ca0 ct0 ct1  *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hcs0 $Hct0 $Hct1 $Hcode $Himport_B_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcs0 & Hct0 & Hct1 & Hcode & Himport_B_f)".
    iEval (cbn) in "Hcs0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    (* ---- call B ---- *)
    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".

    (* -- separate argument registers -- *)
    assert ( rmap !! ca1 = Some (WInt 0) ) as Hwca1.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ca2 = Some (WInt 0) ) as Hwca2.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ca3 = Some (WInt 0) ) as Hwca3.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ca4 = Some (WInt 0) ) as Hwca4.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ca5 = Some (WInt 0) ) as Hwca5.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    set ( rmap_arg :=
           {[ ca0 := WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b;
              ca1 := WInt 0;
              ca2 := WInt 0;
              ca3 := WInt 0;
              ca4 := WInt 0;
              ca5 := WInt 0;
              ct0 := WInt 0
           ]} : Reg
        ).

    rewrite !(delete_commute _ _ ct1).
    iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    rewrite !(delete_commute _ _ ctp).
    iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).

    set (rmap' := (delete ca5 _)).

    iMod (extend_region_perm _ _ _ _ _ RW interpC
        with "[] [$HWstd_full_B] [$HWreg_B] [$Hcgp_b] []")
      as "(HWreg_B & Hrel_cgp_b & HWstd_full_B)".
    { done. }
    { done. }
    { iApply future_priv_mono_interp_z. }
    { cbn; iEval (rewrite fixpoint_interp1_eq); done. }

    set (W1 := <s[cgp_b:=Permanent]s>W_init_B).
    assert (related_sts_priv_world W_init_B W1) as HWinit_privB_W1.
    { subst W1; by eapply related_sts_priv_world_fresh_Permanent. }

    iAssert (interp W1 B (WSealed ot_switcher B_f)) as "#Hinterp_W1_B_f".
    { iApply monotone.interp_monotone_sd; eauto. }

    iAssert (interp W1 B (WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_W1_B_b".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite finz_seq_between_cons; last solve_addr.
      rewrite finz_seq_between_empty; last solve_addr.
      iApply big_sepL_singleton.
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      subst W1.
      iSplit.
      + iApply monoReq_interp; last done.
        rewrite /std_update /std.
        rewrite !lookup_insert; done.
      + iPureIntro.
        rewrite /std_update /std.
        rewrite !lookup_insert; done.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg ∗ interp W1 B warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W1 B (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    iApply (switcher_cc_specification _ _ W1 W1 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $HWreg_B $HWstd_full_B
              $Hinterp_W1_B_f]"); auto.
    { set_solver. }
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hrmap_dom; set_solver.
    }
    iSplitR.
    { iIntros "(Hcsp_stk & HWreg_B & Hstd_full_B)". iModIntro; iFrame. }
    iNext. subst rmap'.
    iIntros "H".
    iDestruct "H"
      as (W2 rmap') "(%HW1_pubB_W2 & %Hdom_rmap'
                      & Hna & HWreg_B & HWstd_full_B
                      & HPC & Hcgp & Hcra & Hcsp & Hca0 & Hca1
                      & Hrmap & Hcsp_stk)".
    iDestruct "Hca0" as (warg0) "[Hca0 _]".
    iDestruct "Hca1" as (warg1) "[Hca1 _]".
    iEval (cbn) in "HPC".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero".
    assert (∀ r : RegName, r ∈ dom rmap' → rmap' !! r = Some (WInt 0)) as Hrmap_init'.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ctp ct0 ct1 ct2 ct3 ct4 cs0 ----  *)
    assert ( rmap' !! ctp = Some (WInt 0) ) as Hwctp'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct0 = Some (WInt 0) ) as Hwct0'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct1 = Some (WInt 0) ) as Hwct1'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct2 = Some (WInt 0) ) as Hwct2'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct3 = Some (WInt 0) ) as Hwct3'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct4 = Some (WInt 0) ) as Hwct4'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct4 with "Hrmap") as "[Hct4 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! cs0 = Some (WInt 0) ) as Hwcs0'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! cs1 = Some (WInt 0) ) as Hwcs1'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.

    (* Load ct0 cgp  *)
    iInstr "Hcode".
    { split; [done| solve_addr]. }
    (* Mov ct1 0  *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* --------------- BLOCK 5: PREP CALL ---------------- *)
    (* --------------------------------------------------- *)

    set (cgp_c := (cgp_b ^+ 1)%a).
    focus_block 5 "Hcode_main" as a_prepC Ha_prepC "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov ca0 cgp  *)
    iInstr "Hcode".
    (* Mov ca1 0  *)
    iInstr "Hcode".
    (* Lea cgp (-1)%Z *)
    iInstr "Hcode".
    { transitivity (Some cgp_b%a); auto; subst cgp_c; solve_addr. }

    assert (std W2 !! cgp_b = Some Permanent) as HW2_B_cpg_b.
    { eapply monotone.region_state_pub_perm in HW1_pubB_W2; eauto.
      subst W1.
      (* TODO lemma *)
      rewrite /std_update /std.
      rewrite !lookup_insert; done.
    }
    iDestruct (region_open with "[$Hrel_cgp_b $HWreg_B $HWstd_full_B]")
      as (wcgp_b) "(HWreg_B & HWsts_full_B & HWstd_full_B & Hcpg_b & _ & HmonoR & #Hinterp_wcpgb)"
    ; auto.
    destruct (decide (Permanent = Temporary ∧ isWL RW = true)) as [ [? ?] | _ ]; first congruence.

    (* Store cgp 42%Z *)
    iInstr "Hcode".
    { solve_addr. }

    (* GetA ct0 ca0 *)
    iInstr "Hcode".

    (* Add ct1 ct0 1%Z *)
    iInstr "Hcode".

    (* Subseg ca0 ct0 ct1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_c ^+1)%a); auto; subst cgp_c; solve_addr. }
    { subst cgp_c; solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 6 and 7: FETCH --------------- *)
    (* --------------------------------------------------- *)

    focus_block 6 "Hcode_main" as a_fetch3 Ha_fetch3 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 7 "Hcode_main" as a_fetch4 Ha_fetch4 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hcs0 $Hct0 $Hct1 $Hcode $Himport_C_g]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcs0 & Hct0 & Hct1 & Hcode & Himport_C_g)".
    iEval (cbn) in "Hcs0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 8: CALL C ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 8 "Hcode_main" as a_callC Ha_callC "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".

    (* -- separate argument registers -- *)
    assert ( rmap' !! ca2 = Some (WInt 0) ) as Hwca2'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ca3 = Some (WInt 0) ) as Hwca3'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ca4 = Some (WInt 0) ) as Hwca4'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ca5 = Some (WInt 0) ) as Hwca5'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    subst rmap_arg.
    set ( rmap_arg :=
           {[ ca0 := WCap RW Global cgp_c%a (cgp_c ^+ 1)%a cgp_c%a;
              ca1 := WInt 0;
              ca2 := WInt 0;
              ca3 := WInt 0;
              ca4 := WInt 0;
              ca5 := WInt 0;
              ct0 := WInt 0
           ]} : Reg
        ).

    rewrite !(delete_commute _ _ ct4).
    iDestruct (big_sepM_insert _ _ ct4 with "[$Hrmap $Hct4]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    rewrite !(delete_commute _ _ ct3).
    iDestruct (big_sepM_insert _ _ ct3 with "[$Hrmap $Hct3]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    rewrite !(delete_commute _ _ ct2).
    iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    rewrite !(delete_commute _ _ ct1).
    iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    rewrite !(delete_commute _ _ ctp).
    iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).

    set (rmap'' := (delete ca5 _)).

    iMod (extend_region_perm _ _ _ _ _ RW interpC
           with "[] [$HWstd_full_C] [$HWreg_C] [$Hcgp_c] []")
      as "(HWreg_C & Hrel_cgp_c & HWstd_full_C)".
    { done. }
    { done. }
    { iApply future_priv_mono_interp_z. }
    { cbn; iEval (rewrite fixpoint_interp1_eq); done. }

    set (W3 := <s[cgp_c :=Permanent]s>W_init_C).
    assert (related_sts_priv_world W_init_C W3) as HWinit_privC_W3.
    { subst W3; by eapply related_sts_priv_world_fresh_Permanent. }

    iAssert (interp W3 C (WSealed ot_switcher C_g)) as "#Hinterp_W3_C_g".
    { iApply monotone.interp_monotone_sd; eauto. }

    iAssert (interp W3 C (WCap RW Global cgp_c (cgp_c ^+ 1)%a cgp_c)) as "#Hinterp_W3_C_c".
    { subst cgp_c.
      iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite finz_seq_between_cons; last solve_addr.
      rewrite finz_seq_between_empty; last solve_addr.
      iApply big_sepL_singleton.
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit; first iFrame "Hrel_cgp_c".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      subst W3.
      iSplit.
      + iApply monoReq_interp; last done.
        rewrite /std_update /std.
        rewrite !lookup_insert; done.
      + iPureIntro.
        rewrite /std_update /std.
        rewrite !lookup_insert; done.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg ∗ interp W3 C warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W3 C (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    iApply (switcher_cc_specification _ _ W3 W3 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $HWreg_C $HWstd_full_C
              $Hinterp_W3_C_g]"); auto.
    { set_solver. }
    { subst rmap''.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hdom_rmap'.
      set_solver.
    }
    iSplitR.
    { iIntros "(Hcsp_stk & HWreg_B & Hstd_full_B)". iModIntro; iFrame. }
    iNext. subst rmap''.
    iIntros "H".
    iDestruct "H"
      as (W4 rmap'') "(%HW1_pubB_W4 & %Hdom_rmap''
                      & Hna & HWreg_C & HWstd_full_C
                      & HPC & Hcgp & Hcra & Hcsp & Hca0 & Hca1
                      & Hrmap & Hcsp_stk)".
    iDestruct "Hca0" as (warg0') "[Hca0 _]".
    iDestruct "Hca1" as (warg1') "[Hca1 _]".
    iEval (cbn) in "HPC".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero'".
    assert (∀ r : RegName, r ∈ dom rmap'' → rmap'' !! r = Some (WInt 0)) as Hrmap_init''.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ctp ct0 ct1 ct2 ct3 ct4 cs0 ----  *)
    assert ( rmap'' !! ctp = Some (WInt 0) ) as Hwctp''.
    { apply Hrmap_init''. rewrite Hdom_rmap''.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    assert ( rmap'' !! ct0 = Some (WInt 0) ) as Hwct0''.
    { apply Hrmap_init''. rewrite Hdom_rmap''.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap'' !! ct1 = Some (WInt 0) ) as Hwct1''.
    { apply Hrmap_init''. rewrite Hdom_rmap''.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap'' !! ct2 = Some (WInt 0) ) as Hwct2''.
    { apply Hrmap_init''. rewrite Hdom_rmap''.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap'' !! ct3 = Some (WInt 0) ) as Hwct3''.
    { apply Hrmap_init''. rewrite Hdom_rmap''.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
    assert ( rmap'' !! ct4 = Some (WInt 0) ) as Hwct4''.
    { apply Hrmap_init''. rewrite Hdom_rmap''.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct4 with "Hrmap") as "[Hct4 Hrmap]"; first by simplify_map_eq.
    assert ( rmap'' !! cs0 = Some (WInt 0) ) as Hwcs0''.
    { apply Hrmap_init''. rewrite Hdom_rmap''.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap'' !! cs1 = Some (WInt 0) ) as Hwcs1''.
    { apply Hrmap_init''. rewrite Hdom_rmap''.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.

    (* Load ct0 cgp  *)
    iInstr "Hcode".
    { split; [done| solve_addr]. }
    (* Mov ct1 42  *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 9: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 9 "Hcode_main" as a_assert_b Ha_assert_b "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hcra $Hct0 $Hct1
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 10: HALT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 10 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    subst hφ; iApply ("Hφ" with "[$]").
  Qed.

  Lemma cmdc_spec_full

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr) (a_flag : Addr)
    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (csp_content : list Word)

    (φ : language.val cap_lang -> iProp Σ)
    (Nassert Nswitcher : namespace)
    (E : coPset)
    :

    let imports :=
     cmdc_main_imports b_switcher e_switcher a_cc_switcher ot_switcher b_assert e_assert B_f C_g
    in

    ↑Nswitcher ⊆ E ->
    ↑Nassert ⊆ E ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (WInt 0) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init_B) ->
    (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    length csp_content = finz.dist csp_b csp_e ->

    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_cc_switcher ot_switcher)
      ∗ na_own logrel_nais E

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a cmdc_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ cmdc_main_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ region W_init_B B ∗ sts_full_world W_init_B B
      ∗ region W_init_C C ∗ sts_full_world W_init_C C

      ∗ interp W_init_B B (WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g)

      ∗ ▷ (
            na_own logrel_nais E
              -∗ WP Instr Halted {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})
      ⊢ WP Seq (Instr Executable) {{ λ v, True }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcherE HNassertE Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_c Hlen_stack)
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & HWreg_B & HWstd_full_B
      & HWreg_C & HWstd_full_C
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & Hφ)".
    iApply (wp_wand with "[-]").
    { iApply (cmdc_spec
                pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e rmap
                b_switcher e_switcher a_cc_switcher ot_switcher
                b_assert e_assert a_flag B_f C_g W_init_B W_init_C
                csp_content φ Nassert Nswitcher E); eauto; iFrame "#∗".
    }
    by iIntros (v) "?".
  Qed.

End CMDC.
