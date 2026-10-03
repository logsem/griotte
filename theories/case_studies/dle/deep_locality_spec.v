From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call deep_locality.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.

Section DLE.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  Local Lemma dle_prepare_world {E : coPset}
      (W : WORLD) (b e : Addr) (z : Z) :
    (b + 2)%a = Some e ->
    disjoint_from_mmio b e ->
    not_heap_range b e ->
    LNonHeap b ∉ dom (std W) ->
    LNonHeap (b ^+ 1)%a ∉ dom (std W) ->
    world_interp (revoke W) C ∗
    b ↦ₐ WInt z ∗
    (b ^+ 1)%a ↦ₐ WCap true RW Global b (b ^+ 1)%a b
    ={E}=∗
    let W1 := revoke W in
    let W2 := <s[b := Temporary]s> W1 in
    let W3 := <s[(b ^+ 1)%a := Temporary]s> W2 in
    ⌜related_sts_priv_world W W3⌝ ∗
    world_interp W3 C ∗
    interp W3 C (WCap true RW_DL Local (b ^+ 1)%a (b ^+ 2)%a (b ^+ 1)%a).
  Proof.
    iIntros (Hcgp_contiguous Hcgp_shadow Hcgp_range Hcgp_b Hcgp_a)
      "(Hworld_interp_C & Hcgp_b & Hcgp_a)".
    destruct Hcgp_range as [Hcgp_nonheap Hcgp_heap].
    set (W1 := revoke W).
    iDestruct (init_TmpRes W1 C b RW_DL interp_in_memC
      with "[] [$Hcgp_b] []") as "TmpRes_cgp_b"; auto.
    { iApply future_pub_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_temp_nonheap
      with "Hworld_interp_C TmpRes_cgp_b")
      as "(Hworld_interp_C & #Hrel_cgp_b)"; auto.
    { by rewrite -revoke_dom_eq. }
    match goal with
    | _ : _ |- context [ world_interp ?W' ] => set (W2 := W')
    end.

    iAssert (interp W2 C (WCap true RW_DL Local b (b ^+ 1)%a b))
      as "#Hinterp_cgp_b".
    { iEval (rewrite fixpoint_interp1_eq); iEval (cbn).
      iSplit; cycle 1.
      { iPureIntro.
        pose proof (switcher_disjoint_subseg b e b (b ^+ 1)%a)
          as [Hsub_shadow Hsub_heap];
          [solve_addr + Hcgp_contiguous | solve_addr + Hcgp_contiguous | split; auto |].
        split; first done.
        apply heap_cap_valid_disjoint; done.
      }
      rewrite /interp_cap_body.
      rewrite (finz_seq_between_cons b); last solve_addr + Hcgp_contiguous.
      rewrite (finz_seq_between_empty _ (b ^+ 1)%a); last solve_addr + Hcgp_contiguous.
      iApply big_sepL_singleton.
      rewrite addr_key_None.
      iExists RW_DL, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit; first iApply zcond_interp_in_mem.
      iSplit; first iApply rcond_interp_in_mem.
      iSplit; first iApply wcond_interp_in_mem.
      iSplit; first iApply monoReq_interp_in_mem.
      + by simplify_map_eq.
      + by intro.
      + by iPureIntro; right; simplify_map_eq.
    }

    assert (is_heap_address (b ^+ 1)%a = false) as Hcgp1_nonheap.
    { apply not_true_is_false; intros Hheap.
      apply withinBounds_true_iff in Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hcgp_heap.
      eapply (Hcgp_heap (b ^+ 1)%a); apply elem_of_finz_seq_between;
        [solve_addr + Hcgp_contiguous | exact Hheap]. }

    iDestruct (init_TmpRes W2 C (b ^+ 1)%a RW_DL (safeC interp_in_mem_dl)
      with "[] [$Hcgp_a] []") as "TmpRes_cgp_a"; auto.
    { iApply future_pub_mono_interp_in_mem_dl. }
    { cbn; iApply interp_to_in_mem; iExact "Hinterp_cgp_b". }
    iMod (world_interp_extend_temp_nonheap
      with "Hworld_interp_C TmpRes_cgp_a")
      as "(Hworld_interp_C & Hrel_cgp_a)"; auto.
    { subst W2.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; intros [= Heq]; solve_addr + Heq Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }
    match goal with
    | _ : _ |- context [ world_interp ?W' ] => set (W3 := W')
    end.

    iAssert (interp W3 C
      (WCap true RW_DL Local (b ^+ 1)%a (b ^+ 2)%a (b ^+ 1)%a))
      as "#Hinterp_W3_cgp_a".
    { iEval (rewrite fixpoint_interp1_eq); iEval (cbn).
      iSplit; cycle 1.
      { iPureIntro.
        pose proof (switcher_disjoint_subseg b e (b ^+ 1)%a (b ^+ 2)%a)
          as [Hsub_shadow Hsub_heap];
          [solve_addr + Hcgp_contiguous | solve_addr + Hcgp_contiguous | split; auto |].
        split; first done.
        apply heap_cap_valid_disjoint; done.
      }
      rewrite /interp_cap_body.
      rewrite (finz_seq_between_cons (b ^+ 1)%a); last solve_addr + Hcgp_contiguous.
      rewrite (finz_seq_between_empty _ (b ^+ 2)%a); last solve_addr + Hcgp_contiguous.
      iApply big_sepL_singleton.
      rewrite addr_key_None.
      iExists RW_DL, interp_in_mem_dl.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro; apply persistent_cond_interp_in_mem_dl).
      iSplit; first iFrame "Hrel_cgp_a".
      iSplit; first iApply zcond_interp_in_mem_dl.
      iSplit; first (iApply rcond_interp_in_mem_dl; auto).
      iSplit; first iApply wcond_interp_in_mem_dl.
      iSplit; last (by iPureIntro; right; rewrite lookup_insert_eq).
      rewrite /monoReq; rewrite lookup_insert_eq; cbn.
      iApply mono_pub_interp_in_mem_dl.
    }

    assert (related_sts_priv_world W W3) as Hrelated_priv_W_W3.
    { eapply related_sts_priv_trans_world with (W' := W1); eauto
      ; first eapply revoke_related_sts_priv_world.
      eapply related_sts_pub_priv_trans_world with (W' := W2); eauto.
      { eapply related_sts_pub_world_revoked_temporary'.
        by rewrite -revoke_lookup_None -not_elem_of_dom.
      }
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_world_revoked_temporary'.
      rewrite lookup_insert_ne; last (apply LNonHeap_ne; solve_addr + Hcgp_contiguous).
      by rewrite -revoke_lookup_None -not_elem_of_dom.
    }
    iModIntro.
    iSplit; first by iPureIntro.
    iFrame "Hworld_interp_C Hinterp_W3_cgp_a".
  Qed.

  Lemma dle_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := dle_main_imports C_f in

    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    disjoint_from_mmio cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code)%a ->

    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    LNonHeap (cgp_b)%a ∉ dom (std W0) ->
    LNonHeap (cgp_b ^+1 )%a ∉ dom (std W0) ->

    is_heap_cap (WSealed ot_switcher C_f) = false ->
    frame_match Ws Cs cstk W0 C ->
    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ lword_of_word <$> imports ]]
      ∗ codefrag pc_a dle_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> dle_main_data ]]

      ∗ world_interp W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W0 C (WCap true RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hcgp_shadow Hcgp_range HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_a Hsealed_nonheap Hframe_match
            )
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      )".
    destruct Hcgp_range as [Hcgp_nonheap Hcgp_heap].
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    (* --- Extract registers ca0 ct0 ct1 ct2 ct3 cs0 cs1 --- *)
    iExtractList "Hrmap" [cra;ca0;ct0;ct1;ct2;ct3;cs0;cs1]
      as ["Hcra"; "Hca0"; "Hct0"; "Hct1"; "Hct2"; "Hct3"; "Hcs0"; "Hcs1"].

    (* Extract the addresses of b and a *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr + Hcgp_contiguous. }
    { solve_addr + Hcgp_contiguous. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_a _]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr + Hcgp_contiguous. }
    { solve_addr + Hcgp_contiguous. }

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr + Himports_contiguous. }
    { solve_addr + Himports_contiguous. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr + Himports_contiguous. }
    { solve_addr + Himports_contiguous. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f _]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr + Himports_contiguous. }
    { solve_addr + Himports_contiguous. }


    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜std W0 !! LNonHeap a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap_nonheap with "Hinterp_W0_csp"); eauto. }

    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_shadow Hstk_heap]; first done.
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_interp_C]")
        as (l) "(%Hl_unk & Hworld_interp_C & Hstack_revoked_W0 & >%Hstack_revoked_W0 & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_b]") as "%Hcgp_b_stk".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_a]") as "%Hcgp_a_stk".
    set (W1 := revoke W0).

    (* --------------------------------------------------------------- *)
    (* ----------------- Start the proof of the code ----------------- *)
    (* --------------------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.

    (* Store cgp 0%Z 0. *)
    iInstr "Hcode".
    (* Mov ct0 cgp; *)
    iInstr "Hcode".

    (* GetB ct1 cgp; *)
    iInstr "Hcode".
    (* Add ct2 ct1 1%Z; *)
    iInstr "Hcode".
    (* Subseg ct0 ct1 ct2; *)
    iInstr "Hcode".

    (* Lea cgp 1%Z; *)
    iInstr "Hcode".
    (* Store cgp ct0; *)
    iInstr "Hcode".

    (* Mov ca0 cgp; *)
    iInstr "Hcode".
    (* Lea cgp (-1)%Z; *)
    iInstr "Hcode".
    (* Add ct1 ct2 1%Z; *)
    iInstr "Hcode".
    assert (is_heap_address (cgp_b ^+ 1)%a = false) as Hcgp1_nonheap.
    { apply not_true_is_false; intros Hheap.
      apply withinBounds_true_iff in Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hcgp_heap.
      eapply (Hcgp_heap (cgp_b ^+ 1)%a); apply elem_of_finz_seq_between;
        [solve_addr + Hcgp_contiguous | exact Hheap]. }
    (* Subseg ca0 ct2 ct1; *)
    iInstr "Hcode".
    (* Restrict ca0 rw_dl *)
    iInstr "Hcode".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec _ _ _ _ _ _ _ _ _
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call) with "[- $HPC $Hct0 $Hct1 $Hct2 $Hcode]"); eauto using switcher_call_sentry_not_heap.
    { solve_addr + HsubBounds Hpc_contiguous Himports_contiguous Ha_fetch1. }
    replace (pc_b ^+ 0)%a with pc_b by (clear; solve_addr).
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hct1 & Hct2 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct2 $Hct3 $Hcode $Himport_C_f]"); eauto.
    { solve_addr + HsubBounds Hpc_contiguous Himports_contiguous Ha_fetch2. }
    iNext ; iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 3.1: CALL B ---------------- *)
    (* --------------------------------------------------- *)

    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch2.
    (* Mov cs0 ct0; *)
    iInstr "Hcode".
    (* Mov cs1 ct1; *)
    iInstr "Hcode".
    (* Jalr cra ct0; *)
    iInstr "Hcode".

    (* -- Update the world and prove interp of the the argument in `ca0` -- *)

    (* Extend the world with the two temporary data addresses. *)
    iMod (dle_prepare_world W0 cgp_b cgp_e 0%Z
      Hcgp_contiguous Hcgp_shadow (conj Hcgp_nonheap Hcgp_heap) Hcgp_b Hcgp_a
      with "[$Hworld_interp_C $Hcgp_b $Hcgp_a]")
      as "(%Hrelated_priv_W0_W3 & Hworld_interp_C & #Hinterp_W3_cgp_a)".
    set (W2 := <s[cgp_b := Temporary]s> W1) in *.
    set (W3 := <s[(cgp_b ^+ 1)%a := Temporary]s> W2) in *.

    (* -- separate argument registers -- *)
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5]
      as ["Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"].

    set ( rmap_arg :=
           {[ ca0 := lword_of_word (WCap true RW_DL Local (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a);
              ca1 := wca1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := lword_of_word (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
           ]} : LReg
        ).

    iInsertList "Hrmap" [ct2;ct3].
    repeat (iEval (rewrite -delete_insert_ne //) in "Hrmap").
    set (rmap' := (delete ca5 _)).

    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W3 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W3 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }


    (* Show that the entry point to C_f is still safe in W3 *)
    iAssert (interp W3 C (WSealed ot_switcher C_f)) as "#Hinterp_W3_C_f".
    { iApply (interp_monotone_sd_same_heap with "[] [$]"); eauto. }
    iClear "Hinterp_W0_C_f".
    iDestruct (StackRevokedResources_mono_priv _ W3 with "Hstack_revoked_W0") as "Hstack_revoked_W3"; auto.
    assert ( revoked_addresses W3 (finz.seq_between csp_b csp_e) ) as Hstack_revoked_W3.
    {
      rewrite /revoked_addresses Forall_forall.
      intros x Hx.
      assert (x ≠ (cgp_b ^+ 1)%a).
      { intros Hx'; simplify_eq; set_solver+Hx Hcgp_a_stk. }
      assert (x ≠ (cgp_b)%a).
      { intros Hx'; simplify_eq; set_solver+Hx Hcgp_b_stk. }
      simplify_map_eq.
      apply list_elem_of_lookup_1 in Hx; destruct Hx as [? Hx].
      rewrite /revoked_addresses Forall_forall in Hstack_revoked_W0; apply Hstack_revoked_W0.
      eapply list_elem_of_lookup_2; eauto.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
       with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W3 $Hcstk_frag
              $Hinterp_W3_C_f $HentryC_f $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    clear dependent wca0 wct0 wct1 wct2 wct3 wcs0 wcs1.
    clear dependent wca1 wca2 wca3 wca4 wca5 rmap.
    clear stk_mem.
    iNext.
    iIntros (W4 rmap stk_mem l' rcgp rcra rcs0 rcs1)
      "( %Hl_unk' & Hrevoked_l' & %Hrevoked_l'
      & %Hrelated_pub_W3ext_W4 & Hrel_stk_C' & %Hdom_rmap & Hstack_revoked_W4 & %Hstack_revoked_W4
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & Hrcs1).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0; [|exact switcher_call_sentry_not_heap].
    apply load_heap_nonheap in Hrcs1; [|exact Hsealed_nonheap].
    subst rcgp rcra rcs0 rcs1.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".


    (* ----- Revoke the world to get borrowed addresses back -----*)
    (* 1.5. Derive some properties on the world required later *)
    assert ( cgp_b ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_b_stk'.
    { clear -Hcgp_b_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_b_stk.
      destruct Hcgp_b_stk; [left|right]; solve_addr.
    }
    assert ( (cgp_b ^+1)%a  ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_a_stk'.
    { clear -Hcgp_a_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_a_stk.
      destruct Hcgp_a_stk; [left|right]; solve_addr.
    }
    assert (related_sts_pub_world W3 W4) as Hrelated_pub_W3_W4.
    {
      eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros a Ha.
      rewrite lookup_insert_ne;[|intros [= Hcontra]; subst a; set_solver+Ha Hcgp_a_stk'].
      rewrite lookup_insert_ne;[|intros [= Hcontra]; subst a; set_solver+Ha Hcgp_b_stk'].
      cbn.
      eapply revoke_lookup_Monotemp.
      destruct Hl_unk as [_ Htemp]; apply Htemp.
      apply elem_of_app; right; apply elem_of_LNonHeap_fmap.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
    }
    set (W5 := revoke W4).

    (* -- extract cgp_b out of the revoked -- *)
    (* TODO lemma *)
    iDestruct ( big_sepL_elem_of_extract _
      (fun k => (∀ a', ⌜k = LNonHeap a'⌝ -∗ ▷ ∃ v, a' ↦ₐ v)%I) (LNonHeap cgp_b)
      with "[] [$Hrevoked_l']")
      as (l'') "(%Hl_unk'' & Hrevoked_l'' & Hcgp_b_nonheap)".
    {
      assert ( std W4 !! LNonHeap cgp_b = Some Temporary ) as HW4.
      { eapply region_state_pub_temp; eauto.
        rewrite lookup_insert_ne; last (apply LNonHeap_ne; solve_addr + Hcgp_contiguous).
        by rewrite lookup_insert_eq.
      }
      destruct Hl_unk' as [_ Hl_unk'].
      pose proof (Hl_unk' (LNonHeap cgp_b)) as [Hl_unk'_cgp _].
      apply Hl_unk'_cgp in HW4.
      apply elem_of_app in HW4 as [?|HW4]; first done.
      rewrite elem_of_LNonHeap_fmap in HW4; done.
    }
    { by destruct Hl_unk' as [Hl_unk' _]; apply NoDup_app in Hl_unk' as (? & _ & _). }
    {
      iClear "#"; clear; cbn.
      iIntros (a) "(%&%&% & _ & Haddr)". iIntros (a' ->).
      iEval (cbn) in "Haddr".
      iDestruct "Haddr" as (wa) "(_ & Ha & _)".
      iNext. iExists wa. iExact "Ha".
    }
    iDestruct ("Hcgp_b_nonheap" $! cgp_b with "[//]") as ">[%wcgpb Hcgp_b]".
    iEval (cbn [laddr_addr]) in "Hcgp_b".

    (* simplify the knowledge about the new rmap *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero".
    assert (∀ r : RegName, r ∈ dom rmap → rmap !! r = Some (lword_of_word (WInt 0))) as Hrmap_init.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    iExtractList "Hrmap" [ct0;ct1] as ["Hct0"; "Hct1"].

    (* --------------------------------------------------- *)
    (* ------------- BLOCK 3.2: CALL B again -------------- *)
    (* --------------------------------------------------- *)

    (* Store cgp 42%Z; *)
    iInstr "Hcode".
    (* Mov ca0 0%Z; *)
    iInstr "Hcode".
    (* Mov ct0 cs0; *)
    iInstr "Hcode".
    (* Mov ct1 cs1; *)
    iInstr "Hcode".
    (* Jalr cra ct0; *)
    iInstr "Hcode".

    (* -- separate argument registers -- *)
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as ["Hca2"; "Hca3"; "Hca4"; "Hca5"].

    set ( rmap_arg :=
           {[ ca0 := lword_of_word (WInt 0);
              ca1 := warg1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := lword_of_word (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
           ]} : LReg
        ).
    set (rmap' := (delete ca5 _)).

    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W5 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W5 C (WInt 0)) as "Hinterp_0"; first by iApply interp_int.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    assert (related_sts_priv_world W4 W5) as Hrelated_priv_W4_W5 by apply revoke_related_sts_priv_world.

    (* Show that the entry point to C_f is still safe in W5 *)
    assert (heap_authority_base (WSealed ot_switcher C_f) = None) as Hsealed_heap_base.
    { destruct (heap_authority_base (WSealed ot_switcher C_f)) as [b|] eqn:Hbase;
        last done.
      apply heap_authority_base_heap_cap_base in Hbase.
      rewrite /is_heap_cap Hbase in Hsealed_nonheap. discriminate.
    }
    assert (filter_heap W4 (WSealed ot_switcher C_f) = WSealed ot_switcher C_f)
      as Hfilter.
    { apply filter_heap_nonheap. exact Hsealed_heap_base. }
    iAssert (interp W5 C (WSealed ot_switcher C_f)) as "#Hinterp_W5_C_f".
    { iApply (interp_monotone_sd_same_heap W4 W5 with "[]").
      { subst W5. by rewrite revoke_heap. }
      { iPureIntro. exact Hrelated_priv_W4_W5. }
      destruct (get_tag (WSealed ot_switcher C_f)) eqn:Htag.
      - iApply (interp_monotone_sd_retained W3 W4 C ot_switcher C_f
          with "Hinterp_W3_C_f");
          [by apply related_sts_pub_priv_world | exact Htag | exact Hfilter].
      - by iApply interp_untagged.
    }
    iClear "Hinterp_W3_C_f".

    (* Prepare the closing resources for the switcher call spec *)
    iDestruct (StackRevokedResources_mono_priv _ W5 with "Hstack_revoked_W4") as "#Hstack_revoked_W5"; auto.

    iApply (switcher_cc_specification _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
       with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W5 $Hcstk_frag
              $Hinterp_W5_C_f $HentryC_f $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hdom_rmap.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    iNext. subst rmap'.
    clear dependent warg0 warg1 rmap stk_mem.
    iIntros (W6 rmap stk_mem l0 rcgp rcra rcs0 rcs1)
      "( _ & _ & _
      & %Hrelated_pub_W5ext_W6 & Hrel_stk_C'' & %Hdom_rmap & Hstack_revoked_W6 & _
      & Hna & _
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK & %Hrestored)"; clear l0.
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & Hrcs1).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0; [|exact switcher_call_sentry_not_heap].
    apply load_heap_nonheap in Hrcs1; [|exact Hsealed_nonheap].
    subst rcgp rcra rcs0 rcs1.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".

    (* -- simplify our knowledge about rmap -- *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero'".
    assert (∀ r : RegName, r ∈ dom rmap → rmap !! r = Some (lword_of_word (WInt 0))) as Hrmap_init.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;cnull] as ["Hct0"; "Hct1"; "Hct2"; "Hct3"; "Hct4"; "Hcnull"].

    assert (readAllowed RW = true /\ withinBounds cgp_b cgp_e cgp_b = true) as Hcgp_read by
      (split; [reflexivity | solve_addr + Hcgp_contiguous]).
    (* Load ct0 cgp 0. *)
    iInstr "Hcode".
    (* Mov ct1 42  *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { solve_addr + HsubBounds Hpc_contiguous Himports_contiguous Ha_assert_c. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ------------------ BLOCK 5: HALT ------------------ *)
    (* --------------------------------------------------- *)
    focus_block 5 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Jalr cnull cra *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.

  Qed.

End DLE.
