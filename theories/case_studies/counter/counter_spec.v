From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules interp_weakening.
From griotte Require Import switcher_spec_call switcher_spec_return world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import counter_spec_states counter_spec_world_call counter_spec_world_return
  counter_spec_main_blocks_1 counter_spec_main_blocks_2.

Section Counter.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Context {C : CmptName}.

  Lemma counter_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)
    (csp_content : list Word)
    (C_f : Sealable)

    (W0 : WORLD)
    (cstk : CSTK)
    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nswitcher Ncounter : namespace)

    :

    let imports := counter_main_imports C_f in

    Nswitcher ## Ncounter ->
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp ; cra]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length counter_main_code)%a ->

    (cgp_b + length counter_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->

    (
      na_inv cerise_nais Nswitcher switcher_inv
      (* initial memory layout *)
      ∗ na_inv cerise_nais Ncounter
          ( ∃ (cnt : Z),
            [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
            ∗ codefrag pc_a counter_main_code
            ∗ [[ cgp_b, cgp_e ]] ↦ₐ [[ [WInt cnt] ]]
            ∗ ⌜ (0 <= cnt)%Z ⌝
          )
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ cra ↦ᵣ WSentry XSRW_ Local b_switcher e_switcher a_switcher_return
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      ∗ world_interp W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
      ∗ interp W0 C (WCap RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [counter_world_call]: revoke the world, to get the stack frame;
       - [counter_main_blocks_1_spec]: blocks 0-3, increment the counter,
         fetch the imports and jump to the switcher;
       - [switcher_call_args_0] and [switcher_cc_specification]: call to
         [C_f];
       - [counter_world_return]: repair the world;
       - [counter_main_blocks_2_spec]: block 4, clear the registers and
         jump to the switcher;
       - [switcher_ret_specification]: return to the caller. *)
    intros imports; subst imports.
    iIntros (HNswitcher_counter Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hframe_match Hcsp_sync
            )
      "(#Hswitcher & #Hmem & Hna
      & HPC & Hcgp & Hcsp & Hcra & Hrmap
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f & #Hentry_C_f
      & #Hinterp_W0_csp
      )".
    assert (counter_code_bounds pc_b pc_e pc_a C_f) as Hbounds by done.
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by (cbn in Hcgp_contiguous; solve_addr).
    iMod (na_inv_acc with "Hmem Hna")
      as "(( %cnt & >Himports_main & >Hcode_main & >Hcgp_main & >%Hcnt) & Hna & Hmem_close)"; auto.
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_C_f)".
    iRegionSplit "Hcgp_main" as "Hcgp_b".
    iExtractList "Hrmap" [ct0;ct1;cs0;cs1] as ["Hct0"; "Hct1"; "Hcs0"; "Hcs1"].

    (* Revoke the world, to get the stack frame *)
    iMod (counter_world_call with "Hinterp_W0_csp Hinterp_W0_C_f Hworld_interp_C")
      as (l stk_mem) "(%Hextract & %Hrevoked_l & %Hrevoked_stk & Hworld_interp_C
                      & #Hinterp_W1_C_f & Hstack_revoked & Hrevoked_l & Hstk)".

    (* Blocks 0-3: increment the counter, fetch the imports and jump to the
       switcher *)
    iApply (counter_main_blocks_1_spec with
             "[- $HPC $Hcgp $Hct0 $Hct1 $Hcs0 $Hcs1 $Hcra $Hcgp_b
              $Himport_switcher $Himport_C_f $Hcode_main]"); [done|done|].
    iNext; iIntros "(HPC & Hcgp & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcra & Hcgp_b
                    & Himport_switcher & Himport_C_f & Hcode_main)".
    iMod ("Hmem_close" with "[$Hna Himport_switcher Himport_C_f $Hcode_main Hcgp_b]")
      as "Hna".
    { iNext; iExists (cnt + 1)%Z.
      iSplitL "Himport_switcher Himport_C_f"; first (iRegionMerge; iFrame).
      iSplitL; first (iRegionMerge; iFrame).
      iPureIntro; lia. }
    clear dependent cnt.
    iInsertRegs "Hrmap" ["Hct0"].
    iDestruct (switcher_call_args_0 (revoke W0) C with "Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to [C_f] *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hentry_C_f $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked $Hcstk_frag
              $Hinterp_W1_C_f $HK]"); [done|done|].
    iSplit; first done.
    iNext.
    clear dependent arg_rmap rmap' stk_mem.
    iIntros (W2 rmap' stk_mem l')
      "(_ & _ & _ & %Hpub_ext_W2 & _ & %Hrmap'_dom & _ & _
      & Hna & _
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)".
    iEval (cbn [updatePcPerm]) in "HPC".

    (* Repair the world *)
    iMod (counter_world_return with "Hworld_interp_C Hrevoked_l Hstk")
      as "(Hworld_interp_C & Hrevoked_l & Hstk & %Hpub_W0_Wfixed)"; [done..|].

    (* Block 4: clear the registers and jump to the switcher *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [cnull] as ["Hcnull"].
    iMod (na_inv_acc with "Hmem Hna")
      as "(( %cnt & >Himports_main & >Hcode_main & >Hcgp_main & >%Hcnt) & Hna & Hmem_close)"; auto.
    iApply (counter_main_blocks_2_spec with
             "[- $HPC $Hcra $Hcs0 $Hcs1 $Hca0 $Hca1 $Hcnull $Hcode_main]"); first done.
    iNext; iIntros "(HPC & Hcra & Hcs0 & Hcs1 & Hca0 & Hca1 & Hcnull & Hcode_main)".
    iMod ("Hmem_close" with "[$Hna $Himports_main $Hcode_main $Hcgp_main]") as "Hna"; first done.
    iEval (cbn [updatePcPerm]) in "HPC".
    iInsertRegs "Hrmap" ["Hcnull"; "Hcs0"; "Hcs1"; "Hcgp"; "Hcra"].

    (* Return to the caller *)
    iApply (switcher_ret_specification _ W0 (revoke W2) with
             "[$Hswitcher $Hstk $Hcstk_frag $HK $Hworld_interp_C $Hna $HPC $Hrevoked_l
              $Hrmap $Hca0 $Hca1 $Hcsp]"); auto.
    { rewrite !dom_insert_L !dom_delete_L Hrmap'_dom; set_solver+. }
    { by destruct Hextract. }
    { intros a; destruct Hextract as [_ Htemp]; destruct (Htemp a); auto. }
    { iSplit; iApply interp_int. }
  Qed.

  Lemma counter_spec_entry_point

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (C_f : Sealable)

    (W0 : WORLD)

    (csp_content : list Word)

    (Nswitcher Ncounter : namespace)
    :

    let imports := counter_main_imports C_f in

    Nswitcher ## Ncounter ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length counter_main_code)%a ->
    (cgp_b + length counter_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    na_inv cerise_nais Nswitcher switcher_inv
    (* initial memory layout *)
    ∗ na_inv cerise_nais Ncounter
        ( ∃ (cnt : Z),
            [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
            ∗ codefrag pc_a counter_main_code
            ∗ [[ cgp_b, cgp_e ]] ↦ₐ [[ [WInt cnt] ]]
            ∗ ⌜ (0 <= cnt)%Z ⌝
        )
    ∗ interp W0 C (WSealed ot_switcher C_f)
    ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
    ⊢ execute_entry_point
      (WCap RX Global pc_b pc_e pc_a) (WCap RW Global cgp_b cgp_e cgp_b) 0 W0 C.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_counter HsubBounds
               Hcgp_contiguous Himports_contiguous)
      "(#Hswitcher & #Hmain & #Hinterp_C_f & #HentryC_f)
      % % % % % %
      (HK & %Hframe_match & Hregister_state & Hrmap & Hworld_interp_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as "(%Hfullrmap & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_csp & Hinterp_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

    iApply counter_spec; last iFrame "∗#"; eauto.
    { repeat (rewrite dom_delete_L).
      apply regmap_full_dom in Hfullrmap; rewrite Hfullrmap.
      set_solver.
    }
    { intros r Hr.
      repeat (rewrite dom_delete_L in Hr).
      repeat (rewrite lookup_delete_ne; last set_solver).
      set_solver.
    }
    destruct Hsync_csp as [ Hsync_csp <- ]; done.
  Qed.

End Counter.
