From iris.proofmode Require Import proofmode.
From griotte Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From griotte Require Import rules logrel world_interp_stack monotone proofmode register_tactics.
From griotte Require Import fetch_spec assert_spec switcher interp_switcher_call switcher_spec_call switcher_spec_return.
From griotte Require Import vae vae_helper.
From griotte Require Import proofmode.
From griotte Require Import vae_spec_states vae_spec_world_call
  vae_spec_init_blocks_1 vae_spec_init_blocks_2.

Section VAE.
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

  Lemma vae_init_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)

    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nswitcher : namespace)

    (cstk : CSTK)
    (i : positive)
    :

    let imports := vae_main_imports C_f in

    disjoint_from_shadow pc_b pc_e ->
    disjoint_from_shadow b_vae_exp_tbl e_vae_exp_tbl ->
    is_heap_address pc_b = false ->
    is_heap_address cgp_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    is_shadow_address cgp_b = false ->

    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->

    dom rmap = all_registers_s ∖ {[ cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length vae_main_code)%a ->

    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    (pc_b + vae_label ".Lvae_init")%a = Some pc_a ->

    loc W0 !! i = Some (encode false) ->
    frame_match Ws Cs cstk W0 C ->
    (
      assert_static b_assert e_assert a_flag
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ switcher_static
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a vae_main_code
      ∗ b_vae_exp_tbl ↦ₐ□ WCap true RX Global pc_b pc_e pc_b
      ∗ (b_vae_exp_tbl ^+ 1)%a ↦ₐ□ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ (b_vae_exp_tbl ^+ 2)%a ↦ₐ□ WInt (encode_entry_point InterruptEnabled 1 (length (imports ++ VAE_main_code_init)))
      ∗ inv awkN (awk_inv C i cgp_b)
      ∗ sts_rel_loc C i awk_rel_pub awk_rel_priv
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ₚ WCap true RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ world_interp W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
      ∗ interp W0 C (WCap true RWL Local csp_b csp_e csp_b)

      ∗ WSealed ot_switcher (SCap true RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a) ↦□ₑ 1
      ∗ WSealed ot_switcher (SCap true RO Local b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a) ↦□ₑ 1
      ∗ seal_pred ot_switcher ot_switcher_propC

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Outline of the proof:
       - [vae_world_run_call]: revoke the world, to get the stack frame;
       - [vae_init_blocks_1_spec]: blocks 0-3, set the flag to [0], fetch
         the imports and jump to the switcher;
       - [switcher_call_args_0] and [switcher_cc_specification]: call to
         [B.adv];
       - [vae_init_blocks_2_spec]: block 3, halt. *)
    intros imports; subst imports.
    iIntros (Hpc_shadow Hexports_shadow Hpc_nonheap Hcgp_nonheap Hsealed_nonheap Hcgp_shadow
               Hsize_vae_exp_tbl Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hloc_i_0 Hframe_match
            )
      "(#Hassert & #Hswitcher & #Hswitcher_static
      & #Himports_main & #Hcode_main
      & #Hvae_exp_tbl_PCC
      & #Hvae_exp_tbl_CGP
      & #Hvae_exp_tbl_awkward
      & #Hawk_inv & #Hrel_ι
      & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      & #Hentry_awkward & #Hentry_awkward'
      & #Hot_switcher
      )".
    assert (vae_code_bounds pc_b pc_e pc_a C_f) as Hbounds
      by (rewrite /vae_code_bounds; eauto 10).
    assert (cgp_b < cgp_e)%a as Hcgp_bounds by (cbn in Hcgp_contiguous; solve_addr).
    iRegionSplit "Himports_main" as "(Himport_switcher & Himport_assert & Himport_C_f)".
    iDestruct (interp_cap_disjoint_wl with "Hinterp_W0_csp")
      as %[Hstk_mmio Hstk_heap]; first done.
    iExtractList "Hrmap" [cra;ct0;ct1;cs0;cs1]
      as ["Hcra"; "Hct0"; "Hct1"; "Hcs0"; "Hcs1"].

    (* Revoke the world, to get the stack frame *)
    iMod (vae_world_run_call with "Hinterp_W0_csp Hinterp_W0_C_f Hworld_interp_C")
      as (stk_mem) "(Hworld_interp_C & #Hinterp_W1_C_f & Hstack_revoked & %Hrevoked_stk & Hstk)".

    (* Blocks 0-3: set the flag to [0], fetch the imports and jump to the
       switcher *)
    iApply (vae_init_blocks_1_spec with
             "[- $Hawk_inv $Hworld_interp_C $HPC $Hcgp $Hct0 $Hct1 $Hcra
              $Himport_switcher $Himport_C_f $Hcode_main]"); [done..|exact Hloc_i_0|].
    iNext; iIntros (mie) "(Hworld_interp_C & HPC & Hcgp & Hct0 & Hct1 & Hcra
                    & _ & _ & _)".
    iInsertRegs "Hrmap" ["Hct0"].
    iDestruct (switcher_call_args_0 (revoke W0) C with "Hrmap")
      as (arg_rmap rmap') "(%Hrmap'_dom & %Harg_rmap & Hrmap_arg & Hrmap)".
    { rewrite dom_insert_L !dom_delete_L Hrmap_dom; set_solver+. }

    (* Call to [B.adv] *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hswitcher_static $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $HentryC_f $Hrmap_arg $Hrmap
              $Hstk $Hworld_interp_C $Hstack_revoked $Hcstk_frag
              $Hinterp_W1_C_f $HK]"); [done..|].
    iSplit; first done.
    iNext.
    iIntros (W2 rmap'' stk_mem' l' rcgp rcra rcs0 rcs1)
      "(_ & _ & _ & _ & _ & _ & _ & _ & Hna & _ & _ & _ & HPC
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hrestored)".
    destruct Hrestored as (_ & Hrcra & _ & _).
    apply load_heap_nonheap in Hrcra;
      [|rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=; reflexivity].
    subst rcra.
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".

    (* Block 3: halt *)
    iApply (vae_init_blocks_2_spec with "[$HPC $Hcode_main Hna]");
      first done.
    iNext; iIntros "(HPC & _)".
    wp_end; iIntros "_"; iFrame.
  Qed.

End VAE.
