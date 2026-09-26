From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import ftlr_base interp_weakening interp_switcher_return.
From griotte Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Export switcher switcher_preamble switcher_macros_spec switcher_helpers.
From griotte Require Import switcher_spec_call_blocks world_ghost_theory world_interp_stack.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Import switcher_spec_call_gen_revoked.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  (** The four saved registers are restored according to [load_heap].
      Their shadow entries remain owned by the allocator invariant. *)
  Lemma switcher_cc_specification
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (w_entry_point : Sealable)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (nargs : nat)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher w_entry_point in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    disjoint_from_shadow b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
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
    ∗ ct1 ↦ᵣ wct1_caller ∗ interp W C wct1_caller ∗ wct1_caller ↦□ₑ nargs
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* Argument registers, need to be safe-to-share *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg
                                      ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                                        then interp W C warg
                                        else True )
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
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word) l' rcgp rcra rcs0 rcs1,
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
            ∗ PC ↦ᵣ updatePcPerm (rcra)
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ rcgp
            ∗ cra ↦ᵣ rcra
            ∗ cs0 ↦ᵣ rcs0
            ∗ cs1 ↦ᵣ rcs1
            ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 target callee_stk_region Hstk_shadow Hstk_heap Hdom Hrdom) "(#Halloc & #Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & #Hentry & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hworld_interp & Hstk_val & % & Hcstk & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked Nswitcher W C
      wcgp_caller wcra_caller wcs0_caller wcs1_caller target
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs true).
    1-4: eauto.
    iFrame "Halloc Hswitcher Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1 Hargs Hregs
      Hstk Hworld_interp Hstk_val Hcstk Hcont".
    iFrame "Hentry".
    iFrame "%".
    iSplitR.
    { subst target; cbn.
      destruct ((ot_switcher =? ot_switcher)%Z); eauto. }
    iNext.
    iIntros (W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1) "Hnew".
    iDestruct "Hnew" as
      "(%Hextract & Hrev & %Hrevoked & %Hrelated & Hstd & %Hdom_ret
      & Hstack & %Hrevstack & Hna & %Hbounds & Hworld & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Harg0 & Harg1
      & Hrmap & Hstk & Hcont & %Hloaded & %Hretained)".
    iApply ("Hpost" $! W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1 with
      "[$Hrev $Hstd $Hstack $Hna $Hworld $Hcstk $HPC $Hcgp $Hcra
        $Hcs0 $Hcs1 $Hcsp $Harg0 $Harg1 $Hrmap $Hstk $Hcont]").
    iFrame "%".
  Qed.

  Lemma switcher_cc_specification_alt
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    disjoint_from_shadow b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
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
    ∗ cs1 ↦ᵣ wcs1_caller
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
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word) l' rcgp rcra rcs0 rcs1,
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
            ∗ PC ↦ᵣ updatePcPerm (rcra)
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ rcgp
            ∗ cra ↦ᵣ rcra
            ∗ cs0 ↦ᵣ rcs0
            ∗ cs1 ↦ᵣ rcs1
            ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
              ∗ ⌜filter_heap W2 rcs1 = rcs1⌝
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hstk_shadow Hstk_heap Hdom Hrdom) "(#Halloc & #Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hworld_interp & Hstk_val & % & Hcstk & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked Nswitcher W C
      wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs false).
    1-4: eauto.
    iFrame "Halloc Hswitcher Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1 Hargs Hregs
      Hstk Hworld_interp Hstk_val Hcstk Hcont Hpost".
    iFrame "Htarget_v".
    iFrame "%".
  Qed.

  (** Compatibility corollaries for callers with no saved heap capabilities. *)

End Switcher.
