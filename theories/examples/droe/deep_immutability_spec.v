From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening.
From cap_machine Require Import logrel rules proofmode.
From cap_machine Require Import fetch assert switcher_spec deep_immutability.

Section DROE.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .
  Context {C : CmptName}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Program Definition interp_ro_eq (w : Word) : V :=
    (λne (W : WORLD) (B : leibnizO CmptName) (v : leibnizO Word)
     , (⌜ v = w ⌝ ∗ interp W B (readonly w))%I).
  Solve All Obligations with solve_proper.

  Lemma droe_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (φ : language.val cap_lang -> iProp Σ)
    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports :=
     droe_main_imports b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp ; cra]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (WInt 0) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length droe_main_code)%a ->

    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W_init_C) ->
    (cgp_b ^+1 )%a ∉ dom (std W_init_C) ->

    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher switcher_inv
      ∗ na_own logrel_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ cra ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a droe_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ droe_main_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ region W_init_C C ∗ sts_full_world W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ interp W_init_C C (WCap RWL Local csp_b csp_e csp_b)

      ∗ ▷ (na_own logrel_nais ⊤
              -∗ WP Instr Halted {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_a
            )
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & HWreg_C & HWstd_full_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_C_g & #Hinterp_Winit_C_csp
      & Hφ)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.
    iDestruct (big_sepL2_length with "Hcsp_stk") as "%Hlen_stack".

    (* --- Extract registers ca0 ct0 ct1 ct2 ct3 cs0 cs1 --- *)
    assert ( rmap !! ca0 = Some (WInt 0) ) as Hwca0.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
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
    assert ( rmap !! ct2 = Some (WInt 0) ) as Hwct2.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct3 = Some (WInt 0) ) as Hwct3.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
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

    (* Extract the addresses of b and a *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_a _]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f _]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iHide "Hφ" as hφ.

    (* Store cgp 42%Z; *)
    iInstr "Hcode".
    { solve_addr. }
    (* Mov ct0 cgp; *)
    iInstr "Hcode".

    (* GetB ct1 cgp; *)
    iInstr "Hcode".
    (* Add ct2 ct1 1%Z; *)
    iInstr "Hcode".
    (* Subseg ct0 ct1 ct2; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

    (* Lea cgp 1%Z; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    (* Store cgp ct0; *)
    (* NOTE for some reason, iInstr doesnt work here lol *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg with "[$HPC $Hi $Hct0 $Hcgp $Hcgp_a]") ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hcgp_a)".
    iDestruct ("Hcode" with "Hi") as "Hcode".
    wp_pure.

    (* Mov ca0 cgp; *)
    iInstr "Hcode".
    (* Lea cgp (-1)%Z; *)
    iInstr "Hcode".
    { transitivity (Some cgp_b); auto; solve_addr. }
    (* Add ct1 ct2 1%Z; *)
    iInstr "Hcode".
    (* Subseg ca0 ct2 ct1; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    (* Restrict ca0 ro_dro *)
    iInstr "Hcode".
    { by rewrite decode_encode_permPair_inv. }
    { solve_pure. }
    { solve_pure. }

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hct1 $Hct2 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hct1 & Hct2 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct2 $Hct3 $Hcode $Himport_C_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    (* ---- call B ---- *)
    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode" with "Hlc".

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
           {[ ca0 := WCap RO_DRO Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a;
              ca1 := WInt 0;
              ca2 := WInt 0;
              ca3 := WInt 0;
              ca4 := WInt 0;
              ca5 := WInt 0;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_b]") as "%Hcgp_b_stk".
    assert ( cgp_b ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_b_stk'.
    { clear -Hcgp_b_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_b_stk.
      destruct Hcgp_b_stk; [left|right]; solve_addr.
    }


    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W_init_C.1 !! a = Some Temporary⌝)%I as "Hstack_temporary".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_Winit_C_csp"); eauto. }

    iMod (monotone_revoke_stack with "[$Hinterp_Winit_C_csp $HWstd_full_C $HWreg_C]")
        as "(HWstd_full_C & HWreg_C & Hstk')".
    iAssert (
        |={⊤}=>
          ([∗ list] a ∈ finz.seq_between csp_b csp_e,
             closing_revoked_resources W_init_C C a
             ∗ ⌜(revoke W_init_C).1 !! a = Some Revoked⌝
             ∗ ∃ v, a ↦ₐ v
          )
      )%I with "[Hstk' Hlc]" as ">Hstk'".
    {
      rewrite !big_sepL_sep.
      iDestruct "Hstk'" as "[Hstk' $]".
      iDestruct (big_sepL_later_2 with "Hstk'") as "Hstk'".
      iDestruct (lc_fupd_elim_later with "[$] [$Hstk']") as ">Hstk'".
      iModIntro.
      rewrite -big_sepL_sep.
      iApply (big_sepL_impl with "Hstk'").
      iModIntro; iIntros (k a Hx) "Hrev".
      (* by iApply close_revoked_resources. *)
      admit.
    }
    iAssert (
        ∃ stk_mem,
         ([∗ list] a ∈ finz.seq_between csp_b csp_e,
          closing_revoked_resources W_init_C C a ∗ ⌜(revoke W_init_C).1 !! a = Some Revoked⌝)
         ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      )%I with "[Hstk']" as (stk_mem) "[Hclose_res Hstk]".
    { rewrite !big_sepL_sep.
      iDestruct "Hstk'" as "(Hclose & Hrev & Hv)".
      iDestruct (big_sepL_sep with "[$Hclose $Hrev]") as "$".
      by iApply region_addrs_exists.
    }

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W0 := W')
    end.

    iMod (extend_region_perm _ _ _ _ _ RO_DRO (safeC (interp_ro_eq (WInt 42)))
        with "[] [$HWstd_full_C] [$HWreg_C] [$Hcgp_b] []")
      as "(HWreg_C & #Hrel_cgp_b & HWstd_full_C)".
    { done. }
    { subst W0.
      by rewrite -revoke_dom_eq.
    }
    { rewrite /future_priv_mono.
      iIntros "!>" (W W' Hrelared) "[% H]"; cbn.
      iSplitR; [done | by rewrite !fixpoint_interp1_eq].
    }
    { cbn.
      iSplitR; [done | by rewrite !fixpoint_interp1_eq].
    }

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W1 := W')
    end.

    iAssert (interp W1 C (WCap RO_DRO Global cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_cgp_b".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RO_DRO, (interp_ro_eq _).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z) "[-> H]".
        rewrite /interp_ro_eq /=.
        iSplitR; [done | by rewrite !fixpoint_interp1_eq].
      }
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (w') "[-> H]".
        done.
      }
      iSplit; first done.
      subst W0.
      iSplit.
      + rewrite /monoReq; simplify_map_eq.
        iIntros (?) "%Hcontra"; rewrite /canStore in Hcontra.
        destruct (isLocalWord w); done.
      + iPureIntro.
        by rewrite lookup_insert.
    }

    iMod (extend_region_perm _ _ _ _ _ RO_DRO (safeC (interp_ro_eq (WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b)))
        with "[] [$HWstd_full_C] [$HWreg_C] [$Hcgp_a] []")
      as "(HWreg_C & Hrel_cgp_a & HWstd_full_C)".
    { done. }
    { subst W1.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; solve_addr+Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }
    { rewrite /future_priv_mono.
      iIntros "!>" (W W' Hrelared) "[% H]"; cbn.
      iSplitR; [done |].
      iApply monotone.interp_monotone_nl; eauto.
    }
    { cbn. iSplit; done. }

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W2 := W')
    end.

    assert (related_sts_priv_world W_init_C W2) as HWinit_privC_W2.
    { subst W2.
      eapply related_sts_priv_trans_world with (W' := W0) ; eauto; first eapply revoke_related_sts_priv_world.
      eapply related_sts_priv_trans_world with (W' := W1) ; eauto; apply related_sts_priv_world_fresh_Permanent.
    }

    iAssert (interp W2 C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply monotone.interp_monotone_sd; eauto. }

    iAssert (interp W2 C (WCap RO_DRO Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a)) as "#Hinterp_W1_C_a".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RO_DRO, (interp_ro_eq _).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_a".
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z) "[% H]"; done.
      }
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (w') "[-> H]".
        done.
      }
      iSplit; first done.
      subst W1.
      iSplit.
      + rewrite /monoReq; simplify_map_eq.
        iIntros (?) "%Hcontra"; rewrite /canStore in Hcontra.
        destruct (isLocalWord w); done.
      + iPureIntro.
        by rewrite lookup_insert.
    }

    Set Nested Proofs Allowed.
    (* TODO move *)

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg ∗ interp W2 C warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W2 C (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      iSplit ; [ iApply switcher_call_interp |done].
    }

    (* iAssert (([∗ list] a ∈ finz.seq_between csp_b csp_e, rel C a RWL interpC ∗ ⌜std W2 !! a = Some Revoked⌝)%I) *)
    (*           with "[Hrel_stk_C]" as "Hrel_stk_C". *)
    (* { rewrite !big_sepL_sep. *)
    (*   iDestruct "Hrel_stk_B" as "[Hrel %Hrevoked]"; iFrame. *)
    (*   iPureIntro; subst W1. *)
    (*   intros k a Ha; cbn in *. *)
    (*   rewrite lookup_insert_ne. *)
    (*   eapply Hrevoked; eauto. *)
    (*   rewrite elem_of_list_lookup in Hcgp_b_stk. *)
    (*   intros -> ; apply Hcgp_b_stk. *)
    (*   by eexists. *)
    (* } *)

    (* replace frm_init with (frm W1). *)
    iEval (cbn) in "Hct1".
    iApply (switcher_cc_specification _ W2 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $HWreg_C $HWstd_full_C $Hcstk_frag
              $Hinterp_W1_C_f $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      admit.
      (* rewrite Hrmap_dom; set_solver. *)
    }
    { by rewrite /is_arg_rmap. }
    iSplitL "Hclose_res".
    { rewrite !big_sepL_sep.
      iDestruct "Hclose_res" as "[Hclose Hrev]".
      iSplitL "Hclose".
      - iApply (big_sepL_impl with "Hclose").
        iModIntro; iIntros (k a Ha) "Hclose".
        rewrite /closing_revoked_resources.
        iDestruct "Hclose" as (???) "(?&?&#Hmono&#Hzcond&#Hrcond&#Hwcond&?)".
        iExists φ0,p,Hpers; iFrame "∗#".
        iApply "Hzcond"; done.
      - iApply (big_sepL_impl with "Hrev").
        iModIntro; iIntros (k a Ha) "Hrev".
        iDestruct (big_sepL_pure_1 with "Hstack_temporary") as "%Hstack_temporary".
        subst W2 W1 W0.
        iPureIntro.
        rewrite lookup_insert_ne; last admit.
        rewrite lookup_insert_ne; last admit.
        destruct W_init_C as [WC ?]; cbn.
        apply revoke_lookup_Monotemp.
        eapply Hstack_temporary; eauto.
    }

    iNext. subst rmap'.
    iIntros (W2_B rmap')
      "(%HW1_pubB_W2 & %Hdom_rmap'
      & Hna & HWstd_full_B & HWreg_B & Hclose_reg_B
      & Hcstk_frag & Hrel_stk_B
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hcsp_stk & HK)".
    iEval (cbn) in "HPC".
    (* TODO here *)

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

    assert (std W2_B !! cgp_b = Some Permanent) as HW2_B_cpg_b.
    { eapply monotone.region_state_pub_perm in HW1_pubB_W2; eauto.
      subst W1.
      (* TODO lemma *)
      rewrite std_update_multiple_insert_commute; last done.
      rewrite !lookup_insert; done.
    }

    (* we open the world to get the points-to predicate *)
    iDestruct (region_open_next with "[$Hrel_cgp_b $HWreg_B $HWstd_full_B]")
      as (wcgp_b) "(HWreg_B & HWsts_full_B & HWstd_full_B & Hcpg_b & HmonoR & #Hinterp_wcpgb & _)"
    ; eauto ; first done.

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
    rewrite !(delete_commute _ _ ctp).
    iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).

    set (rmap'' := (delete ca5 _)).
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_c]") as "%Hcgp_c_stk".
    assert ( cgp_c ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_c_stk'.
    { clear -Hcgp_c_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_c_stk.
      destruct Hcgp_c_stk; [left|right]; solve_addr.
    }

    (* We add the newly shared address in the world of C *)
    iMod (extend_region_perm _ _ _ _ _ RW interpC
           with "[] [$HWstd_full_C] [$HWreg_C] [$Hcgp_c] []")
      as "(HWreg_C & Hrel_cgp_c & HWstd_full_C)".
    { done. }
    { done. }
    { iApply future_priv_mono_interp_z. }
    { rewrite /interpC /safeC; cbn; iEval (rewrite fixpoint_interp1_eq); done. }

    set (W3 := (<s[cgp_c:=Permanent]s>W_init_C)).
    assert (related_sts_priv_world W_init_C W3) as HWinit_privC_W3.
    { subst W3.
      by eapply related_sts_priv_world_fresh_Permanent.
    }
    iAssert ( ⌜ Forall (fun a => std W_init_C !! a = Some Revoked) (finz.seq_between csp_b csp_e) ⌝ )%I
      as "%Hrevoked_stack_C".
    {
      iDestruct (big_sepL_sep with "Hrel_stk_C") as "[ _ %Hstk ]".
      iPureIntro.
      apply Forall_forall.
      intros a Ha.
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [? Ha].
      eapply Hstk; eauto.
    }
    assert (Forall (fun a => std W3 !! a = Some Revoked) (finz.seq_between csp_b csp_e) ).
    { eapply Forall_forall; eauto.
      intros a Ha; cbn in *.
      rewrite lookup_insert_ne; last (intros ->; set_solver+Hcgp_c_stk Ha).
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [? Ha].
      eapply Forall_lookup_1 in Hrevoked_stack_C; eauto.
    }
    assert (Forall (fun a => std W3 !! a = Some Revoked) (finz.seq_between (csp_b ^+ 4)%a csp_e) ).
    {
      apply Forall_forall.
      intros a Ha.
      eapply Forall_forall in H3; eauto.
      apply elem_of_finz_seq_between.
      apply elem_of_finz_seq_between in Ha.
      solve_addr.
    }

    iAssert (interp W3 C (WSealed ot_switcher C_g)) as "#Hinterp_W3_C_g".
    { iApply monotone.interp_monotone_sd; eauto. }

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
        by rewrite lookup_insert.
      + iPureIntro.
        by rewrite lookup_insert.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg ∗ interp W3 C warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W3 C (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    iAssert (([∗ list] a ∈ finz.seq_between csp_b csp_e, rel C a RWL interpC ∗ ⌜std W3 !! a = Some Revoked⌝)%I)
              with "[Hrel_stk_C]" as "Hrel_stk_C".
    { rewrite !big_sepL_sep.
      iDestruct "Hrel_stk_C" as "[Hrel %Hrevoked]"; iFrame.
      iPureIntro; subst W1.
      intros k a Ha; cbn in *.
      rewrite lookup_insert_ne.
      eapply Hrevoked; eauto.
      rewrite elem_of_list_lookup in Hcgp_c_stk.
      intros -> ; apply Hcgp_c_stk.
      by eexists.
    }

    iApply (switcher_cc_specification _ W3 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $HWreg_C $HWstd_full_C $Hrel_stk_C $Hcstk_frag
              $Hinterp_W3_C_g $HK]"); eauto.
    { subst rmap''.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hdom_rmap'; set_solver.
    }
    { by rewrite /is_arg_rmap. }

    iNext. subst rmap''.
    iIntros (W4_C rmap'')
      "(%HW1_pubC_W4 & %Hdom_rmap''
      & Hna & HWstd_full_C & HWreg_C & Hclose_reg_C
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0' [Hca0 _] ] & [%warg1' [Hca1 _] ]
      & Hrmap & Hcsp_stk & HK)".
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
