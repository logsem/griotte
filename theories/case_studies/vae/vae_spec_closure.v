From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel interp_weakening monotone.
From griotte Require Import fetch_spec assert_spec switcher_base switcher_base_interp.
From griotte Require Import vae vae_helper.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics.
From griotte Require Import allocator_resources heap_region vae_spec_closure_repair.
From griotte Require Import vae_spec_states vae_spec_world_call vae_spec_world_return
  vae_spec_awkward_blocks_1 vae_spec_awkward_blocks_2 vae_spec_awkward_blocks_3.

Section VAE.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  (** Tombstoned keys are heap keys: they are disjoint from any part of
      the stack. *)
  #[local] Lemma vae_quarantined_disjoint_nonheap (l : list LAddr) (stk : list Addr) :
    Forall (λ a, ∃ x ι, a = LHeap x ι) l ->
    l ## (LNonHeap <$> stk).
  Proof.
    intros Hq.
    rewrite elem_of_disjoint. intros a Ha Hstk_a.
    apply list_elem_of_fmap in Hstk_a as [a' [-> _] ].
    rewrite Forall_forall in Hq.
    by destruct (Hq _ Ha) as (x & ι & ?).
  Qed.

  Lemma vae_awkward_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)
    (g_vae_exp_tbl : Locality)

    (C_f : Sealable)

    (W : WORLD)

    i

    :

    let imports := vae_main_imports C_f in
    let a_vae_exp_tbl_cgp := (b_vae_exp_tbl ^+ ExportTable_offset_cgp) in
    let a_vae_entry_awkward := (b_vae_exp_tbl ^+ ExportTable_offset_entry vae_entry_awkward) in

    is_shadow_address cgp_b = false ->
    disjoint_from_shadow b_vae_exp_tbl e_vae_exp_tbl ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_address cgp_b = false ->
    a_vae_entry_awkward ∈ₐ [b_vae_exp_tbl, e_vae_exp_tbl) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length vae_main_code) ->
    (pc_b + vae_label ".Lvae_init")%a = Some pc_a ->
    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    is_Some (pc_b + length (imports ++ VAE_main_code_init))%a ->
    cmpt_threads C ⊆ {[th]} ->

    assert_static b_assert e_assert a_flag
    ∗ na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static
    ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
    ∗ codefrag_pers pc_a vae_main_code
    ∗ b_vae_exp_tbl ↦ₐ□ Cap RX Global pc_b pc_e pc_b
    ∗ a_vae_exp_tbl_cgp ↦ₐ□ Cap RW Global cgp_b cgp_e cgp_b
    ∗ no_handler b_vae_exp_tbl
    ∗ a_vae_entry_awkward ↦ₐ□ WInt (encode_entry_point InterruptEnabled 1 4 (length (imports ++ VAE_main_code_init)))
    (* invariant for d *)
    ∗ inv Nawk (awk_inv C i cgp_b)
    ∗ sts_rel_loc C i awk_rel_pub awk_rel_priv
      -∗
    ot_switcher_prop W C (Cap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl a_vae_entry_awkward).
  Proof.
    (* Outline of the proof:
       - unfold [ot_switcher_prop] and introduce the state of the machine at
         the entry point of [awkward];
       - [world_interp_revoke_stack]: revoke the world, to get the stack
         frame;
       - [vae_world_flag_false]: the flag can be set to [false];
       - [vae_awkward_blocks_1_spec]: blocks 4-6, set the flag to [0], and
         jump to the switcher;
       - [vae_world_quarantine]: close the tombstoned revoked keys;
       - [vae_world_stack], [vae_world_callback] and [vae_call_args]:
         prepare the first call to [g];
       - [switcher_cc_specification_alt]: first call to [g];
       - [vae_world_pub_call] and [vae_world_flag_true]: the flag can be set
         to [true];
       - [vae_awkward_blocks_2_spec]: blocks 7-9, set the flag to [1], and
         jump to the switcher;
       - [vae_world_quarantine]: close the tombstoned keys revoked by the
         first call;
       - [vae_world_stack], [vae_world_callback_restored] and
         [vae_call_args]: prepare the second call to [g];
       - [switcher_cc_specification_alt]: second call to [g];
       - [vae_world_pub_call] and [vae_world_return]: the flag is still
         [true], and the world can be repaired;
       - [vae_awkward_blocks_3_spec]: blocks 9-11, assert that the flag is
         [1], and return;
       - [switcher_ret_specification]: return to the caller of [awkward].
       The stack of [awkward] holds its minimum stack size, so the spills of
       the calls to [g] do not fault. *)
    intros imports a_vae_exp_tbl_cgp a_vae_entry_awkward.
    subst a_vae_exp_tbl_cgp a_vae_entry_awkward.
    iIntros (Hcgp_shadow Hexports_shadow Hpc_shadow Hpc_heap Hcgp_heap
               Hvae_exp_tbl_size Hvae_size_code Hvae_imports Hcgp_size Hentry_some Hpin)
      "(#Hassert & #Hswitcher & #Hswitcher_static
      & #Himports_main & #Hcode_main
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & [#Hvae_exp_eh #Hvae_exp_ehs]
      & #Hvae_exp_awkward
      & #Hawk_inv & #Hsts_rel)".
    iExists g_vae_exp_tbl, b_vae_exp_tbl, e_vae_exp_tbl,
      (b_vae_exp_tbl ^+ ExportTable_offset_entry vae_entry_awkward),
    pc_b, pc_e, cgp_b, cgp_e, 1, 4, _.
    iFrame "#".
    iSplit; first done.
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iSplit; first (iPureIntro; lia).
    iSplit; first done.
    iSplit; first (iPureIntro; eapply disjoint_from_shadow_not_in;
      [exact Hexports_shadow | apply withinBounds_true_iff; solve_addr]).
    iSplit; first (iPureIntro; eapply disjoint_from_shadow_not_in;
      [exact Hexports_shadow | apply withinBounds_true_iff; solve_addr]).
    iSplit; first (iPureIntro; eapply disjoint_from_shadow_not_in;
      [exact Hexports_shadow | apply withinBounds_true_iff; solve_addr]).
    iSplit; first done.
    iSplit; first done.
    iIntros "!>" (t') "#Ht'".
    iDestruct (thread_in_elim with "Ht'") as %Ht'.
    assert (t' = th) as -> by set_solver.
    iIntros (W0) "!> %cstk %Ws %Cs %rmap %csp_b %csp_e".
    iIntros "(#Hthread & _ & HK & %Hframe_match & _ & HPC & Hregister_state & Hrmap
      & Hworld_interp_C & _ & %Hsync_csp & %Hstk_min & Hcstk & Hna)".
    iEval (rewrite world_resources_exclusive) in "Hworld_interp_C".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %Hcgp & [%mie_ret %Hcra] & %Hcsp & #Hinterp_W0_csp & #Hinterp_rmap & #Hzeroed_rmap)".
    rewrite /registers_pointsto.
    assert (vae_code_bounds pc_b pc_e pc_a C_f) as Hbounds
      by (rewrite /vae_code_bounds; eauto 10).
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by (cbn in Hcgp_size; solve_addr).
    iDestruct (vae_args_zero with "Hzeroed_rmap") as %Hzero; first done.
    pose proof (lregmap_full_dom _ Hrmap_init) as Hrmap_dom.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    destruct (Hrmap_init ca0) as [wca0 Hwca0].
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]".
    { rewrite !lookup_delete_ne //; apply Hzero; set_solver+. }
    iExtractList "Hrmap" [ct0;ct1;cs0;cs1] as ["Hct0";"Hct1";"Hcs0";"Hcs1"].
    iAssert (interp W0 C wca0) as "#Hinterp_wca0".
    { iApply "Hinterp_rmap"; eauto. cbn; set_solver+. }
    iDestruct (world_interp_rel_loc_valid with "Hworld_interp_C Hsts_rel") as %Hrel_i_W0.
    iMod (vae_world_flag_valid ⊤ W0 C i cgp_b with "Hawk_inv Hworld_interp_C")
      as "[Hworld_interp_C %Hloc_i_W0]"; first done.
    iDestruct (switcher_static_seal_pred with "Hswitcher_static") as "#Hseal_switcher".

    (* Revoke the world, to get the stack frame *)
    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_mmio Hstk_heap]; first done.
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_interp_C]")
      as (l) "(%Hextract & Hworld_interp_C & #Hstack_revoked_W0 & >%Hstack_revoked_W0
               & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".

    (* The flag can be set to [false] *)
    set (W2 := <l[i:=false]l>(revoke W0)).
    destruct (vae_world_flag_false W0 i Hloc_i_W0 Hrel_i_W0)
      as ([b Hloc_i_W1] & Hrevoke_W1 & Hpriv_W1_W2 & Hpriv_W0_W2 & Hloc_i_W2 & Hrel_i_W2).

    (* Blocks 4-6: set the flag to [0], and jump to the switcher *)
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    change_pc_to (pc_a ^+ vae_label_offset ".Lvae_awkward")%a.
    iApply (vae_awkward_blocks_1_spec with
             "[- $Hawk_inv $Hworld_interp_C $HPC $Hcgp $Hcra $Hca0 $Hct0 $Hct1 $Hcs0 $Hcs1
              $Himport_switcher $Hcode_main]"); [done..|].
    iNext; iIntros (mie) "(Hworld_interp_C & HPC & Hcgp & Hcra & Hca0 & Hct0 & Hct1 & Hcs0 & Hcs1
                    & _ & _)".

    (* Close the quarantined revoked keys *)
    iMod (vae_world_quarantine W0 W2 C l with "Hworld_interp_C Hrevoked_l")
      as (l0_live l0_quarantined) "(%Hl0_partition & %Hl0_quarantined
                                    & Hworld_interp_C & Hl0_live)".
    set (W2q := close_list l0_quarantined W2).
    assert (related_sts_priv_world W0 W2q) as Hpriv_W0_W2q.
    { eapply related_sts_priv_pub_trans_world; [exact Hpriv_W0_W2|].
      subst W2q. apply close_list_related_sts_pub. }

    (* The free part of the stack, below the space reserved at its top *)
    assert (csp_b + StackEntry_reserved_space <= csp_e)%Z as Hstk_res_size
      by solve_addr+Hstk_min.
    iDestruct (stk_start_region_split with "Hstk") as (stk_mem_free stk_res) "[Hstk Hstk_res]";
      first exact Hstk_res_size.
    iDestruct (stk_start_revoked_split _ _ _ _ Hstk_res_size with "Hstack_revoked_W0")
      as "[Hstack_revoked_W0_free _]".
    pose proof (stk_start_revoked_addresses _ _ _ Hstk_res_size Hstack_revoked_W0)
      as Hstack_revoked_addrs_W0_free.

    (* Prepare the first call to [g] *)
    iDestruct (vae_world_stack W0 W2q C with "Hstack_revoked_W0_free")
      as "[Hstack_revoked_W2q %Hstack_revoked_W2q]"; first done.
    { apply vae_revoked_addresses_close_list; last exact Hstack_revoked_addrs_W0_free.
      by eapply vae_quarantined_disjoint_nonheap. }
    iDestruct (vae_world_callback W0 W2q C wca0 with "Hseal_switcher []") as "#Hinterp_W2q_wca0";
      [done|by case_match|].
    iDestruct (vae_call_args W2q C _ with "Hswitcher Hswitcher_static Hca0 Hca1 Hct0 Hrmap")
      as (rmap1) "(%Hrmap1_dom & Hrmap_arg & Hrmap)".
    { rewrite !dom_delete_L Hrmap_dom; set_solver+. }
    { intros r Hr.
      rewrite !lookup_delete_ne; [apply Hzero; set_solver+Hr|set_solver+Hr..]. }

    (* First call to [g] *)
    iApply (switcher_cc_specification_alt with
             "[- $Hthread $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W2q $Hcstk
              $Hinterp_W2q_wca0 $HK]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { apply stk_start_cursor_ok; solve_addr+Hstk_min. }
    { exact Hrmap1_dom. }
    { apply vae_call_adv_arg_rmap_is_arg. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_heap /=.
      reflexivity. }
    iSplit; first done.
    iSplit; cycle 1.
    { (* The spill cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits.
      apply stk_start_spill_fits; rewrite /SpillSlot_size; solve_addr+Hstk_min. }
    iNext.
    clear dependent rmap1 stk_mem.
    iIntros (W3 rmap3 stk_mem l1 rcgp rcra rcs0 callback1)
      "(%Hl1_unk & Hrevoked_l1 & %Hl1_revoked_W4 & %Hpub_ext_W3 & _ & %Hrmap3_dom
      & Hstack_revoked_W3 & %Hstack_revoked_W3
      & Hna & %Hcsp_bounds1
      & Hworld_interp_C
      & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & Hcallback1).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= switcher_base_not_heap /=;
        reflexivity].
    subst rcgp rcra rcs0.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".

    (* The flag can be set to [true] *)
    pose proof (vae_world_pub_call W2q W3 csp_b csp_e Hstack_revoked_W2q Hcsp_bounds1 Hpub_ext_W3)
      as Hpub_W2q_W3.
    assert (related_sts_pub_world W2 W3) as Hpub_W2_W3.
    { eapply related_sts_pub_trans_world; [subst W2q; apply close_list_related_sts_pub|exact Hpub_W2q_W3]. }
    iDestruct (world_interp_rel_loc_valid with "Hworld_interp_C Hsts_rel") as %Hrel_i_W3.
    set (W5 := <l[i:=true]l>(revoke W3)).
    destruct (vae_world_flag_true W2 W3 i false Hloc_i_W2 Hrel_i_W2 Hrel_i_W3 Hpub_W2_W3)
      as (Hrevoke_W4 & Hpriv_W4_W5 & Hpriv_W3_W5 & Hpriv_W2_W5 & Hloc_i_W5 & Hpub_W4_W5).

    (* Blocks 7-9: set the flag to [1], and jump to the switcher *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hzero3]".
    iDestruct (big_sepM_pure with "Hzero3") as %Hzero3.
    iExtractList "Hrmap" [ct0;ct1] as ["Hct0";"Hct1"].
    iApply (vae_awkward_blocks_2_spec with
             "[- $Hawk_inv $Hworld_interp_C $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct0 $Hct1 $Hcs0 $Hcs1
              $Himport_switcher $Hcode_main]"); [done..|].
    iNext; iIntros (mie') "(Hworld_interp_C & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct0 & Hct1 & Hcs0
                    & Hcs1 & _ & _)".

    (* Close the quarantined keys revoked by the first call *)
    iMod (vae_world_quarantine W3 W5 C l1 with "Hworld_interp_C Hrevoked_l1")
      as (l1_live l1_quarantined) "(%Hl1_partition & %Hl1_quarantined
                                    & Hworld_interp_C & Hl1_live)".
    set (W5q := close_list l1_quarantined W5).
    assert (related_sts_priv_world W3 W5q) as Hpriv_W3_W5q.
    { eapply related_sts_priv_pub_trans_world; [exact Hpriv_W3_W5|].
      subst W5q. apply close_list_related_sts_pub. }
    assert (related_sts_priv_world W2q W5q) as Hpriv_W2q_W5q.
    { eapply related_sts_pub_priv_trans_world; [exact Hpub_W2q_W3|exact Hpriv_W3_W5q]. }

    (* Prepare the second call to [g] *)
    iDestruct (vae_world_stack W3 W5q C with "Hstack_revoked_W3")
      as "[Hstack_revoked_W5q %Hstack_revoked_W5q]"; first done.
    { apply vae_revoked_addresses_close_list; last exact Hstack_revoked_W3.
      by eapply vae_quarantined_disjoint_nonheap. }
    iDestruct (vae_world_callback_restored W2q W3 W5q C wca0 callback1 with "Hseal_switcher Hinterp_W2q_wca0")
      as "#Hinterp_W5q_wca0"; [done..|].
    iDestruct (vae_call_args W5q C _ with "Hswitcher Hswitcher_static Hca0 Hca1 Hct0 Hrmap")
      as (rmap5) "(%Hrmap5_dom & Hrmap_arg & Hrmap)".
    { rewrite !dom_delete_L Hrmap3_dom; set_solver+. }
    { by apply vae_rmap_zero. }

    (* Second call to [g] *)
    iApply (switcher_cc_specification_alt with
             "[- $Hthread $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked_W5q $Hcstk
              $Hinterp_W5q_wca0 $HK]").
    { exact Hstk_mmio. }
    { exact Hstk_heap. }
    { apply stk_start_cursor_ok; solve_addr+Hstk_min. }
    { exact Hrmap5_dom. }
    { apply vae_call_adv_arg_rmap_is_arg. }
    { destruct mie'; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_heap /=.
      reflexivity. }
    iSplit; first done.
    iSplit; cycle 1.
    { (* The spill cannot fault: the stack holds it *)
      iApply switcher_cc_fault_stack_fits.
      apply stk_start_spill_fits; rewrite /SpillSlot_size; solve_addr+Hstk_min. }
    iNext.
    iIntros (W6 rmap6 stk_mem6 l2 rcgp rcra rcs0 rcs1)
      "(%Hl2_unk & Hrevoked_l2 & %Hl2_revoked_W7 & %Hpub_ext_W6 & _ & %Hrmap6_dom & _
      & %Hstack_revoked_W6
      & Hna & %Hcsp_bounds
      & Hworld_interp_C
      & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0' [Hca0 _] ] & [%warg1' [Hca1 _] ]
      & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hrcgp & Hrcra & Hrcs0 & Hrcs1).
    apply load_heap_nonheap in Hrcgp;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_heap /=; reflexivity].
    apply load_heap_nonheap in Hrcs0;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= switcher_base_not_heap /=;
        reflexivity].
    subst rcgp rcra rcs0.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".

    (* The flag is still [true], and the world can be repaired *)
    pose proof (vae_world_pub_call W5q W6 csp_b csp_e Hstack_revoked_W5q Hcsp_bounds Hpub_ext_W6)
      as Hpub_W5q_W6.
    (* The space reserved at the top of the stack is still revoked in
       [W7 = revoke W6], the world of the return *)
    assert (related_sts_priv_world W0 (revoke W6)) as Hpriv_W0_W7.
    { eapply related_sts_priv_trans_world; last apply revoke_related_sts_priv_world.
      eapply related_sts_priv_pub_trans_world; last exact Hpub_W5q_W6.
      eapply related_sts_priv_trans_world; last exact Hpriv_W3_W5q.
      eapply related_sts_priv_pub_trans_world; [exact Hpriv_W0_W2q|exact Hpub_W2q_W3]. }
    iMod (world_interp_revoked_by_separation_many (revoke W6) C
           (finz.seq_between (stk_start_a csp_b csp_e) csp_e) stk_res
           with "[$Hworld_interp_C $Hstk_res]")
      as "(Hworld_interp_C & Hstk_res & %Hstk_res_W7)".
    { apply Forall_forall; intros x Hx.
      destruct Hpriv_W0_W7 as [ [Hdom_W0_W7 _] _].
      apply Hdom_W0_W7. rewrite elem_of_dom.
      exists Temporary. apply (proj2 Hextract). apply elem_of_app; right.
      apply elem_of_LNonHeap_fmap, elem_of_finz_seq_between.
      apply elem_of_finz_seq_between in Hx.
      unfold stk_start_a, StackEntry_reserved_space in Hx, Hstk_res_size.
      solve_addr+Hx Hstk_res_size. }
    assert (revoked_addresses (revoke W6) (finz.seq_between csp_b csp_e))
      as Hstack_revoked_W6_full.
    { rewrite (stk_start_seq_split _ _ Hstk_res_size).
      apply revoked_addresses_app. split; [exact Hstack_revoked_W6|exact Hstk_res_W7]. }
    (* The calls' laters were stripped from the cells' contents. *)
    iAssert (RevokedCells W0 C l0_live ∗ RevokedCells W3 C l1_live)%I
      with "[Hl0_live Hl1_live]" as "[Hl0_live Hl1_live]".
    { iSplitL "Hl0_live";
        [iApply (big_sepL_mono with "Hl0_live")|iApply (big_sepL_mono with "Hl1_live")].
      all: iIntros (k a _) "(%pa & %Φa & %Hpers & Hrel & %wa & HpO & Hk & Hmono & HΦ)".
      all: iExists pa, Φa; iFrame "Hrel %"; iExists wa; iFrame "HpO Hk Hmono"; by iNext. }
    iMod (vae_world_return W0 W3 W6 C i b l l0_live l0_quarantined l1 l1_live l1_quarantined l2
           csp_b csp_e
           with "Hsts_rel Hworld_interp_C Hl0_live Hl1_live Hrevoked_l2")
      as (closing_revoked) "(Hworld_interp_C & Hrevoked_l & %Hloc_i_W7 & %Hpub_W0_Wfixed
                             & %Hclosing_nodup & %Hclosing_covers_W0)";
      [done..|].

    (* Blocks 9-11: assert that the flag is [1], and return *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iExtractList "Hrmap" [ct0;ct1;ct2;ca2]
      as ["Hct0";"Hct1";"Hct2";"Hca2"].
    iApply (vae_awkward_blocks_3_spec with
             "[- $Hawk_inv $Hworld_interp_C $Hassert $HPC $Hcgp $Hcra $Hcs0 $Hca0 $Hca1
              $Hct0 $Hct1 $Hct2 $Hca2 $Himport_assert $Hcode_main]");
      [done|done|done|exact Hloc_i_W7|exact (jalr_target_ok_switcher_return_sentry mie_ret)|].
    iNext; iIntros "(Hworld_interp_C & HPC & Hcgp & Hcra & Hcs0 & Hca0 & Hca1
                    & Hct0 & Hct1 & Hct2 & Hca2 & _ & _)".
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iInsertRegs "Hrmap" ["Hca2";"Hct2";"Hct1";"Hct0";"Hcs0";"Hcs1";"Hcgp";"Hcra"].

    (* Return to the caller of [awkward] *)
    iDestruct (stk_start_region_join with "Hstk Hstk_res") as "Hstk";
      first exact Hstk_res_size.
    iApply (switcher_ret_specification W0 (revoke W6) with
             "[$Hthread $Hswitcher $Hswitcher_static $Hstk $Hcstk $HK $Hworld_interp_C $Hna $HPC $Hrevoked_l
              $Hrmap $Hca0 $Hca1 $Hcsp]"); auto.
    { rewrite !dom_insert_L !dom_delete_L Hrmap6_dom; set_solver+. }
    { iSplit; iApply interp_int. }
  Qed.


End VAE.
