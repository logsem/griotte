From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call cmdc.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics map_simpl.

Section CMDC.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {B C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.


  Lemma cmdc_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (φ : language.val griotte_lang -> iProp Σ)
    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := cmdc_main_imports B_f C_g in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (WInt 0) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init_B) ->
    (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    (* We suppose that the stack region is already revoked in each worlds.
       It's because the worlds are closed and if they we're Temporary,
       then the points-to predicates would be own by both `world_interp` at the same time,
       which is not possible. *)
    revoked_addresses W_init_B (finz.seq_between csp_b csp_e) ->
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->

    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ na_own cerise_nais ⊤

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

      ∗ world_interp W_init_B B
      ∗ world_interp W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_B B (WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g)

      ∗ (WSealed ot_switcher B_f) ↦□ₑ cmdc_B_f_args
      ∗ (WSealed ot_switcher C_g) ↦□ₑ cmdc_C_g_args

      (* initial stack are revoked in both worlds *)
      ∗ StackRevokedResources W_init_B B (finz.seq_between csp_b csp_e)
      ∗ StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e)

      ∗ ▷ (na_own cerise_nais ⊤
              -∗ WP Instr Halted {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_c
               Hrevoked_stack_B Hrevoked_stack_C)
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_interp_B
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & #HentryB_f & #HentryC_g
      & Hstack_revoked_B & Hstack_revoked_C
      & Hφ)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.
    iDestruct (big_sepL2_length with "Hcsp_stk") as "%Hlen_stack".

    (* Extract the needed registers from the register map *)
    iExtractList "Hrmap" [ca0;ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hca0";"Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].

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
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_B_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_B_f)".
    iEval (cbn) in "Hcs0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    (* ---- call B ---- *)
    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".


    (* Relinquish [Hcgp_b] and prove that the capability pointing to it is safe to share *)
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_b]") as "%Hcgp_b_stk".
    assert ( cgp_b ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_b_stk'.
    { clear -Hcgp_b_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_b_stk.
      destruct Hcgp_b_stk; [left|right]; solve_addr.
    }

    iDestruct ( init_PermRes W_init_B B cgp_b RW interpC with "[] [$Hcgp_b] []" ) as "Hcgp_b".
    { done. }
    { iApply future_priv_mono_interp_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm with "Hworld_interp_B Hcgp_b")
      as "(Hworld_interp_B & Hrel_cgp_b)"; auto.


    set (W1 := (<s[cgp_b:=Permanent]s>W_init_B)).
    assert (related_sts_priv_world W_init_B W1) as HWinit_privB_W1.
    { subst W1; eapply related_sts_priv_world_fresh_Permanent. }

    iAssert (interp W1 B (WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_W1_B_b".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons cgp_b); last solve_addr.
      rewrite (finz_seq_between_empty (cgp_b ^+ 1)%a); last solve_addr.
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
      + iApply (monoReq_interp _ _ _ _  Permanent); last done.
        rewrite /std_update.
        by rewrite lookup_insert_eq.
      + iPureIntro.
        by rewrite lookup_insert_eq.
    }

    (* Prove that the adversary's entry point is safe to share *)
    iAssert (interp W1 B (WSealed ot_switcher B_f)) as "#Hinterp_W1_B_f".
    { iApply interp_monotone_sd; eauto. }

    (* Prepare the argument registers for the call to the adversary *)
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5] as ["Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].
    set ( rmap_arg :=
           {[ ca0 := WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b;
              ca1 := wca1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WInt 0
           ]} : Reg
        ).
    iAssert ( [∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                            ∗ if decide (rarg ∈ dom_arg_rmap cmdc_B_f_args)
                                              then interp W1 B warg
                                              else True )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg; rewrite /cmdc_B_f_args.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    iInsertList "Hrmap" [ctp].
    repeat (rewrite -delete_insert_ne //).
    set (rmap' := (delete ca5 _)).


    (* Prepare the stack resources required by the cross-compartment call specification *)
    assert ( revoked_addresses W1 (finz.seq_between csp_b csp_e) ) as Hrevoked_stack_B_W1.
    { rewrite /revoked_addresses Forall_forall.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stack_B.
      intros a Ha; cbn in *.
      rewrite lookup_insert_ne; last (intros ->; set_solver+Hcgp_b_stk Ha).
      by apply Hrevoked_stack_B.
    }
    iDestruct (StackRevokedResources_mono_priv with "Hstack_revoked_B") as "Hstack_revoked_B"; eauto.

    iEval (cbn) in "Hct1".
    iApply (switcher_cc_specification _ W1 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap $Hrmap_arg
              $Hcsp_stk $Hworld_interp_B $Hstack_revoked_B $Hcstk_frag
              $Hinterp_W1_B_f $HentryB_f $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hrmap_dom; set_solver.
    }
    { by rewrite /is_arg_rmap. }

    iNext. subst rmap'.
    iIntros (W2_B rmap' stk_mem l)
      "( _ & _ & _
      & %HW1_pubB_W2 & Hstack_revoked_B & %Hdom_rmap' & Hclose_reg_B & %Hclose_reg_B
      & Hna & %Hcsp_bounds
      & Hworld_interp_B
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)" ; clear l.
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


    (* ---- extract the needed registers ----  *)
    iExtractList "Hrmap" [ctp;ct0;ct1;ct2;ct3;ct4;cnull]
      as ["Hctp";"Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hcnull"].

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
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
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

    (* we open the world to get the points-to predicate *)
    (* We know that cgp_b is Permanent because of private future world transition
       preserves Permanent invariant. *)
    assert (std W2_B !! cgp_b = Some Permanent) as HW2_B_cpg_b.
    { eapply region_state_pub_perm in HW1_pubB_W2; eauto.
      subst W1.
      (* TODO lemma *)
      rewrite std_update_multiple_insert_commute; last done.
      rewrite !lookup_insert_eq; done.
    }

    rewrite (open_world_interp_empty _ B).
    iDestruct (
       open_world_interp_permanent with "[$Hworld_interp_B] [$Hrel_cgp_b]"
      ) as "(Hworld_interp_B & Hstd_cgp_b & [%v Hcgp_b] )"; auto.
    { set_solver+. }
    {
      eapply (region_state_priv_perm W2_B); eauto.
      eapply revoke_related_sts_priv_world.
    }
    iEval (cbn) in "Hcgp_b".
    iDestruct (PermRes_acc with "Hcgp_b") as "[ (>Hcgp_b & Hcgp_b_interp) Hcgp_b_close]".

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
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_C_g]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcs0 & Hct0 & Hct1 & Hcode & Himport_C_g)".
    iEval (cbn) in "Hcs0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 8: CALL C ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 8 "Hcode_main" as a_callC Ha_callC "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".

    (* Relinquish [Hcgp_c] and prove that the capability pointing to it is safe to share *)
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_c]") as "%Hcgp_c_stk".

    iDestruct ( init_PermRes W_init_C C cgp_c RW interpC with "[] [$Hcgp_c] []" ) as "Hcgp_c".
    { done. }
    { iApply future_priv_mono_interp_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm with "Hworld_interp_C Hcgp_c")
      as "(Hworld_interp_C & Hrel_cgp_c)"; auto.

    set (W3 := (<s[cgp_c:=Permanent]s>W_init_C)).
    assert (related_sts_priv_world W_init_C W3) as HWinit_privC_W3.
    { subst W3; by eapply related_sts_priv_world_fresh_Permanent. }

    iAssert (interp W3 C (WCap RW Global cgp_c (cgp_c ^+ 1)%a cgp_c)) as "#Hinterp_W3_C_c".
    { subst cgp_c.
      iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_empty ((cgp_b ^+ 1) ^+ 1)%a); last solve_addr.
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
      + iApply (monoReq_interp _ _ _ _  Permanent); last done.
        by rewrite lookup_insert_eq.
      + iPureIntro.
        by rewrite lookup_insert_eq.
    }


    (* Prove that the adversary's entry point is safe to share *)
    iAssert (interp W3 C (WSealed ot_switcher C_g)) as "#Hinterp_W3_C_g".
    { iApply interp_monotone_sd; eauto. }


    (* Prepare the argument registers for the call to the adversary *)
    clear rmap_arg wca0 wca1 wca2 wca3 wca4 wca5.
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as ["Hca2";"Hca3";"Hca4";"Hca5"].
    set ( rmap_arg :=
           {[ ca0 := WCap RW Global cgp_c%a (cgp_c ^+ 1)%a cgp_c%a;
              ca1 := WInt 0;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WInt 0
           ]} : Reg
        ).
    iAssert ( [∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                            ∗ if decide (rarg ∈ dom_arg_rmap cmdc_C_g_args)
                                              then interp W3 C warg
                                              else True )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg; rewrite /cmdc_C_g_args.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    iInsertList "Hrmap" [cnull;ct4;ct3;ct2;ctp].
    repeat (rewrite -delete_insert_ne //).
    set (rmap'' := (delete ca5 _)).


    (* Prepare the stack resources required by the cross-compartment call specification *)
    assert ( revoked_addresses W3 (finz.seq_between csp_b csp_e) ) as Hrevoked_stack_C_W3.
    { rewrite /revoked_addresses Forall_forall.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stack_C.
      intros a Ha; cbn in *.
      rewrite lookup_insert_ne; last (intros ->; set_solver+Hcgp_c_stk Ha).
      by apply Hrevoked_stack_C.
    }
    iDestruct (StackRevokedResources_mono_priv with "Hstack_revoked_C") as "Hstack_revoked_C"; eauto.

    iApply (switcher_cc_specification _ W3 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap $Hrmap_arg
              $Hstk $Hworld_interp_C $Hstack_revoked_C $Hcstk_frag
              $Hinterp_W3_C_g $HentryC_g $HK]"); eauto; iFrame "%".
    { subst rmap''.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hdom_rmap'; set_solver.
    }
    { by rewrite /is_arg_rmap. }

    iNext. subst rmap''. clear dependent stk_mem.
    iIntros (W4_C rmap'' stk_mem l)
      "( _ & _ & _
      & %HW1_pubC_4 & Hstack_revoked_C & %Hdom_rmap'' & Hclose_reg_C & _
      & Hna & _
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg'0 [Hca0 _] ] & [%warg1' [Hca1 _] ]
      & Hrmap & Hstk & HK)" ; clear l.
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

    (* ---- extract the needed registers ----  *)
    clear wctp wct0 wct1 wct2 wct3 wct4 wcnull.
    iExtractList "Hrmap" [ctp;ct0;ct1;ct2;ct3;ct4;cnull]
      as ["Hctp";"Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hcnull"].

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
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hcra $Hct0 $Hct1 $Hcnull
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
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

    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (φ : language.val griotte_lang -> iProp Σ)
    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := cmdc_main_imports B_f C_g in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (WInt 0) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init_B) ->
    (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    revoked_addresses W_init_B (finz.seq_between csp_b csp_e) ->
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->

    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ na_own cerise_nais ⊤

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

      ∗ world_interp W_init_B B
      ∗ world_interp W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_B B (WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g)

      ∗ (WSealed ot_switcher B_f) ↦□ₑ cmdc_B_f_args
      ∗ (WSealed ot_switcher C_g) ↦□ₑ cmdc_C_g_args

      (* initial stack are revoked in both worlds *)
      ∗ StackRevokedResources W_init_B B (finz.seq_between csp_b csp_e)
      ∗ StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e)

      ∗ ▷ ( na_own cerise_nais ⊤
              -∗ WP Instr Halted {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
      ⊢ WP Seq (Instr Executable) {{ λ v, True }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_c
               Hrevoked_stack_B Hrevoked_stack_C)
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_interp_B
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & #HentryB_f & #HentryC_g
      & Hstack_revoked_B & Hstack_revoked_C
      & Hφ)".
    iApply (wp_wand with "[-]").
    { iApply (cmdc_spec
                pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e rmap
                B_f C_g W_init_B W_init_C
               Ws Cs csp_content φ Nassert Nswitcher cstk); eauto; iFrame "#∗".
    }
    by iIntros (v) "?".
  Qed.

End CMDC.
