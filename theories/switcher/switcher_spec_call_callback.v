From iris.proofmode Require Import proofmode.
From griotte Require Import switcher_spec_call switcher_spec_call_failure.
From griotte Require Import sts_multiple_updates region_invariants_revocation world_ghost_theory world_interp_stack.
From griotte Require Import switcher_load_spec switcher_spec_call_blocks.
From griotte Require Import logrel memory_region rules proofmode map_simpl register_tactics.

Section Switcher_Callback.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  Lemma switcher_cc_specification_alt_callback
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    disjoint_from_shadow b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    is_heap_cap wcgp_caller = false ->
    is_heap_cap wcra_caller = false ->
    is_heap_cap wcs0_caller = false ->
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    allocator_ctx ∗ na_inv cerise_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ᵣ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C wct1_caller else True)
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wct1_caller
    (* Argument registers, need to be safe-to-share *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word) l' (callback : Word),
            (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_addresses (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ᵣ updatePcPerm wcra_caller
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ wcgp_caller
            ∗ cra ↦ᵣ wcra_caller
            ∗ cs0 ↦ᵣ wcs0_caller
            ∗ cs1 ↦ᵣ callback
            ∗ ⌜load_heap wct1_caller callback⌝
            ∗ ⌜filter_heap W2 callback = callback⌝
            ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ interp_continuation cstk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hstk_shadow Hstk_heap Hcgp Hcra Hcs0 Hdom Hrdom)
      "(#Halloc & #Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget
       & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hworld_interp_C & Hclose
       & %Hrevoked_stk & Hcstk_frag & HK & Hpost)".
    iApply (switcher_cc_specification_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
       with
      "[- $Halloc $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Htarget $Hcs0 $Hcs1
        $Hargs $Hregs $Hstk $Hworld_interp_C $Hclose $Hcstk_frag $HK]");
      try assumption.
    iSplit; first done.
    iIntros "!>" (W2 rmap' stk_mem' l' rcgp rcra rcs0 rcs1) "Hres".
    iDestruct "Hres" as
      "(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?
       & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & %Hrestored & %Hretained)".
    destruct Hrestored as (Hgp & Hra & Hs0 & Hs1).
    apply (load_heap_nonheap _ _ Hcgp) in Hgp.
    apply (load_heap_nonheap _ _ Hcra) in Hra.
    apply (load_heap_nonheap _ _ Hcs0) in Hs0.
    subst rcgp rcra rcs0.
    iApply ("Hpost" $! W2 rmap' stk_mem' l' rcs1).
    iFrame "∗%".
  Qed.
End Switcher_Callback.
