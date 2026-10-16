From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import ftlr_base interp_weakening interp_switcher_return.
From griotte Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Export switcher switcher_preamble switcher_macros_spec switcher_helpers.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import switcher_call_states switcher_call_world
  switcher_call_blocks_1 switcher_call_blocks_2 switcher_call_blocks_3 switcher_call_blocks_4
  switcher_call_blocks_5 switcher_call_blocks_6.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Import switcher_load_spec.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  (** The post-condition of [switcher_cc_specification_gen], once the
      caller's stack pointer [WCap true RWL Local b_stk e_stk a_stk] is known. *)
  Definition switcher_cc_post
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr) (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) : iProp Σ :=
    ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem_l stk_mem_h : list LWord) rcgp rcra rcs0 rcs1,
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais ⊤
              ∗ interp W2 C (WCap true RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a)
              ∗ ⌜ (b_stk <= (a_stk ^+ 4)%a ∧ (a_stk ^+ 4)%a <= e_stk ∧ (a_stk + 4) = Some (a_stk ^+ 4)%a)%a ⌝
              ∗ ⌜ disjoint_from_heap a_stk e_stk ⌝
              (* Interpretation of the world *)
              ∗ world_interp_open W2 C (LNonHeap <$> (finz.seq_between (a_stk ^+ 4)%a e_stk))
              ∗ StackOpenWorldResources interp W2 C (finz.seq_between (a_stk ^+ 4)%a e_stk) stk_mem_h
              ∗ cstack_frag cstk
              ∗ ([∗ list] a ∈ (finz.seq_between (a_stk ^+ 4)%a e_stk), ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ rcgp ∗ cra ↦ᵣ rcra ∗ cs0 ↦ᵣ rcs0 ∗ cs1 ↦ᵣ rcs1
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ stk_mem_l ]]
              ∗ [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ stk_mem_h ]]
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W2 wcgp_caller rcgp ∧
                load_heap_in_world W2 wcra_caller rcra ∧
                load_heap_in_world W2 wcs0_caller rcs0 ∧
                load_heap_in_world W2 wcs1_caller rcs1⌝
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't went through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ (b_stk <= (a_stk ^+ 4)%a ∧ (a_stk ^+ 4)%a <= e_stk ∧ (a_stk + 4) = Some (a_stk ^+ 4)%a)%a ⌝
              ∗ na_own cerise_nais ⊤
              (* Registers are preserved *)
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ rcgp
              ∗ cra ↦ᵣ rcra
              ∗ cs0 ↦ᵣ rcs0
              ∗ cs1 ↦ᵣ rcs1
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ WInt 0
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              (* Stack frame *)
              ∗ [[ a_stk , (a_stk ^+4)%a ]] ↦ₐ [[ [wcs0_caller; wcs1_caller; wcra_caller; wcgp_caller] ]]
              ∗ [[ (a_stk ^+4)%a , e_stk ]] ↦ₐ [[ (drop 4 stk_mem) ]]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_interp W C
              ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
              ∗ cstack_frag cstk
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W wcgp_caller rcgp ∧
                load_heap_in_world W wcra_caller rcra ∧
                load_heap_in_world W wcs0_caller rcs0 ∧
                load_heap_in_world W wcs1_caller rcs1⌝
              ∗ £ 2
            )
          )
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  (** Failure path of [switcher_cc_specification_gen]: the trusted stack is
      exhausted. *)
  Lemma switcher_cc_spec_tstack_exhausted
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller wct2 wctp : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    (a_tstk : Addr) (tstk_next : list LWord) :
    disjoint_from_mmio b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->
    (b_trusted_stack + length cstk')%a = Some a_tstk ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    (▷ switcher_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) ∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) ∗
    mtdc ↦ₛᵣ WCap true RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_static ∗
    cstack_full cstk' ∗
    cstack_interp cstk' a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0, cs0 ↦ᵣ wcs0) ∗
    cs1 ↦ᵣ wcs1_caller ∗
    cgp ↦ᵣ wcgp_caller ∗
    cra ↦ᵣ wcra_caller ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    ct1 ↦ᵣ wct1_caller ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    switcher_stk_cells a_stk wcs0_caller wcs1_caller wcra_caller wcgp_caller ∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ drop 4 stk_mem ]] ∗
    (if is_entry_point_known
     then ∃ nargs, wct1_caller.(lw) ↦□ₑ nargs
                   ∗ ( [∗ map] rarg↦warg ∈ arg_rmap,
                         rarg ↦ᵣ warg
                         ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                           then interp W C warg
                           else True )
     else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
    ) ∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), r ↦ᵣ w ) ∗
    world_interp W C ∗
    StackRevokedResources W C (finz.seq_between a_stk e_stk) ∗
    cstack_frag cstk ∗
    interp_continuation cstk Ws Cs ∗
    switcher_cc_post W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk stk_mem cstk Ws Cs
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: [switcher_cc_exhausted_regs] collects the
       registers, [switcher_call_blocks_5_spec] executes blocks 16 and 14-15,
       then close the switcher invariant and use the second post-condition. *)
    iIntros (Hstk_mmio Hdom Hrdom Hstk_bounds Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Hot_bounds)
      "(Hclose_switcher_inv & Hna & Hmtdc & Htstk & #Hstatic & Hcstk_full & Hstk_interp
      & #Hp_ot_switcher & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hctp & Hct2 & Hct1 & Hcsp & Hcells & Hstk
      & Hargs & Hregs & Hworld_interp & Hstk_val & Hcstk & Hcont & Hpost)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    iAssert ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg)%I
      with "[Hargs]" as "Hargs".
    { destruct is_entry_point_known.
      + iDestruct "Hargs" as "(% & _ & Hargs)".
        iApply (big_sepM_impl with "Hargs"); eauto.
        iIntros (r w Hr) "!> [$ _]".
      + iApply (big_sepM_impl with "Hargs"); eauto.
        iIntros (r w Hr) "!> [$ _]".
    }
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iApply (switcher_call_blocks_5_world_spec W C with
      "[- $HPC $Hcsp $Hcells $Hworld_interp $Hrmap0 $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1]");
      [done|done|done|].
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "(%Hrestored & %Hrmap' & Hworld_interp & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
      & Hcells & Hrmap & _ & Hlc)".
    iMod ("Hclose_switcher_inv" with "[$Hna $Hcstk_full Hmtdc Htstk Hstk_interp]") as "HH".
    { iNext. iExists _,_. iFrame "∗ # %".
      iPureIntro; split; auto.
    }
    iApply ("Hpost" $! W rmap' [] [] rcgp rcra rcs0 rcs1); iRight; iFrame "∗ %".
    iDestruct (switcher_stk_cells_region_4 with "Hcells") as "$"; first done.
    iPureIntro.
    split; first solve_addr+Hastk Hastk_bstk.
    split; first solve_addr+Hastk Hastk_bounds Hastk_bstk.
    done.
  Qed.

  Lemma switcher_cc_specification_gen
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller.(lw) ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller.(lw) ↦□ₑ nargs
                     (* Argument registers, need to be safe-to-share *)
                     ∗ ( [∗ map] rarg↦warg ∈ arg_rmap,
                           rarg ↦ᵣ warg
                           ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                             then interp W C warg
                             else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
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


    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem_l stk_mem_h : list LWord) rcgp rcra rcs0 rcs1,
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais ⊤
              ∗ interp W2 C (WCap true RWL Local a_stk4 e_stk a_stk4)
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              ∗ ⌜ disjoint_from_heap a_stk e_stk ⌝
              (* Interpretation of the world *)
              ∗ world_interp_open W2 C (LNonHeap <$> callee_stk_region)
              ∗ StackOpenWorldResources interp W2 C callee_stk_region stk_mem_h
              ∗ cstack_frag cstk
              ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ rcgp ∗ cra ↦ᵣ rcra ∗ cs0 ↦ᵣ rcs0 ∗ cs1 ↦ᵣ rcs1
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ stk_mem_l ]]
              ∗ [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ stk_mem_h ]]
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W2 wcgp_caller rcgp ∧
                load_heap_in_world W2 wcra_caller rcra ∧
                load_heap_in_world W2 wcs0_caller rcs0 ∧
                load_heap_in_world W2 wcs1_caller rcs1⌝
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't went through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              ∗ na_own cerise_nais ⊤
              (* Registers are preserved *)
              ∗ PC ↦ₚ lupdatePcPerm (rcra)
              ∗ cgp ↦ᵣ rcgp
              ∗ cra ↦ᵣ rcra
              ∗ cs0 ↦ᵣ rcs0
              ∗ cs1 ↦ᵣ rcs1
              ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ WInt 0
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              (* Stack frame *)
              ∗ [[ a_stk , (a_stk ^+4)%a ]] ↦ₐ [[ [wcs0_caller; wcs1_caller; wcra_caller; wcgp_caller] ]]
              ∗ [[ (a_stk ^+4)%a , e_stk ]] ↦ₐ [[ (drop 4 stk_mem) ]]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_interp W C
              ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
              ∗ cstack_frag cstk
              ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap_in_world W wcgp_caller rcgp ∧
                load_heap_in_world W wcra_caller rcra ∧
                load_heap_in_world W wcs0_caller rcs0 ∧
                load_heap_in_world W wcs1_caller rcs1⌝
              ∗ £ 2
            )
          )
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
  )

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - [switcher_call_blocks_1_spec]: checks on the stack pointer;
       - [switcher_call_blocks_2_spec]: spill the callee-save registers and
         push the stack pointer on the trusted stack;
       - when the trusted stack is exhausted:
         [switcher_cc_spec_tstack_exhausted];
       - [switcher_entry_point_prop]: the entry point satisfies the sealing
         predicate of the switcher;
       - [switcher_call_blocks_3_spec]: clear the callee's stack frame and
         unseal the entry point;
       - [switcher_cc_world_reinstate]: reinstate the callee's stack frame;
       - [switcher_call_blocks_4_spec]: load the callee and jump to it;
       - [switcher_inv_push_frame]: close the switcher invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros (a_stk4 callee_stk_region Hstk_mmio Hstk_heap Hdom Hrdom) "(#Hswitcher & #Hstatic & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hworld_interp & Hstk_val & %Hstk_revoked & Hcstk & Hcont & Hpost)".
    subst a_stk4 callee_stk_region.

    assert ( exists wr0, rmap !! ct2 = Some wr0) as [wr0 Hwr0].
    { rewrite -/(is_Some (rmap !! ct2)).
      apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hregs") as "[Hct2 Hregs]"; first by simplify_map_eq.
    assert ( exists wr1, rmap !! ctp = Some wr1) as [wr1 Hwr1].
    { rewrite -/(is_Some (rmap !! ctp)).
      apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ctp with "Hregs") as "[Hctp Hregs]"; first by simplify_map_eq.

    (* Open the switcher invariant *)
    iPoseProof "Hstatic" as "[#Hcode #Hb_switcher]".
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    (* Blocks 0-1: checks on the stack pointer *)
    iApply (switcher_call_blocks_1_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
    iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp & _) | (%Hcontra & _)]";
      last (exfalso; apply Hcontra, switcher_csp_checked_stk).

    (* Blocks 2-3: spill and push on the trusted stack *)
    iApply (switcher_call_blocks_2_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hctp $Hct2 $Hcsp $Hstk $Hmtdc $Htstk $Hcode]");
      [done|done|done|].
    iNext; iIntros "(%Hstk_bounds & Hcs1 & Hcra & Hcgp & Hcsp & Hcells & Hstk & _ & Hbranch)".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    iDestruct "Hbranch" as
      "[(%Ha_tstk2 & %Ha_tstk1_bound & HPC & Hcs0 & Hctp & Hct2 & Hmtdc & Ha_tstk1 & Htstk & Hlc)
       | (HPC & Hcs0 & Hctp & Hct2 & Hmtdc & Htstk)]"; cycle 1.
    { (* The trusted stack is exhausted *)
      iApply (switcher_cc_spec_tstack_exhausted with
        "[$Hclose_switcher_inv $Hna $Hmtdc $Htstk $Hstatic $Hcstk_full $Hstk_interp
          $Hp_ot_switcher $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hctp $Hct2 $Hct1 $Hcsp $Hcells $Hstk
          $Hargs $Hregs $Hworld_interp $Hstk_val $Hcstk $Hcont $Hpost]"); done.
    }

    (* Blocks 4-7: clear the callee's stack frame and unseal the entry point *)
    iDestruct (switcher_entry_point_prop with "Hp_ot_switcher Htarget_v Hworld_interp")
      as "[Hworld_interp Hentry_prop]".
    iApply (switcher_call_blocks_3_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcsp $Hstk $Hb_switcher $Hct1 $Hcode]"); [done|done|done|].
    iNext; iIntros (wsb π)
      "(-> & %Htag & HPC & Hcs0 & [%wcs1' Hcs1] & Hcsp & Hstk & _ & Hct1 & _)".
    iDestruct ("Hentry_prop" with "[//] [//]")
      as (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs off Heq Htbl Hbtbl Hbtbl1 Hnargs
          Hentry_some Hatbl_shadow Hbtbl_shadow Hbtbl1_shadow Hbpcc_heap Hbcgp_heap)
           "(#Htbl1 & #Htbl2 & #Htbl3 & #Hentry' & _ & #Hexec)".
    rewrite /lword_of_word in Heq; simplify_eq.
    iAssert ([∗ map] r↦w ∈ arg_rmap,
               r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True)%I
      with "[Hargs]" as "Hargs".
    { destruct is_entry_point_known.
      + iDestruct "Hargs" as "(%nargs0 & Hentry & Hargs)".
        iEval (cbn) in "Hentry'".
        iDestruct (entry_agree _ nargs nargs0 with "Hentry' Hentry") as "<-".
        iFrame.
      + iApply (big_sepM_impl with "Hargs").
        iIntros "!> %k %w' _ [$ Hinterp]".
        destruct ( decide (k ∈ dom_arg_rmap nargs) ) ; auto.
    }

    (* Reinstate the callee's stack frame in the world *)
    iMod (switcher_cc_world_reinstate with "Hworld_interp Hstk_val Hstk")
      as "(Hworld_interp & #Hstk4v & %Hrelated & %Hrev)"; [done|done|solve_addr| | |].
    { eapply switcher_disjoint_subseg; [|reflexivity|split; eassumption]. solve_addr. }
    { eapply switcher_disjoint_subseg; [|reflexivity|split; eassumption]. solve_addr. }
    set (W' := std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary).
    iSpecialize ("Hexec" $! W' with "[]").
    { iPureIntro. by apply related_sts_pub_priv_world. }

    (* Blocks 7-11: load the callee and jump to it *)
    iApply (switcher_call_blocks_4_spec W C with
      "[- $Htbl1 $Htbl2 $Htbl3 $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcgp $Hcra $Hargs $Hregs $Hcode]");
      [done|done|done|lia|done|done|done|done| |done| |].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { rewrite !dom_delete_L Hdom. set_solver. }
    iNext; iIntros (arg_rmap' rmap')
      "(%Harg_rmap' & %Hrmap' & HPC & Hcgp & Hcra & Hargs & Hregs & _)".

    (* Push the frame and close the switcher invariant *)
    set (frame :=
           {| wret := wcra_caller;
              wcgp := wcgp_caller;
              wcs0 := wcs0_caller;
              wcs1 := wcs1_caller;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Unknown
           |}).
    iMod (switcher_inv_push_frame frame cstk with
           "Hcstk_full Hcstk Hmtdc Ha_tstk1 Htstk Hstk_interp [Hcells] Hp_ot_switcher")
      as "[Hinv Hcstk]"; [done|done|done|done|done|done|done|done| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".

    (* Execute the entry point of the callee *)
    iDestruct (switcher_call_entry_registers W W' C nargs arg_rmap' rmap' with
                "[$Hcgp $Hcra $Hcsp $Hstk4v $Hargs $Hregs]")
      as (regs) "[Hregs Hregs_interp]"; [done| |done|done|].
    { symmetry. apply std_update_multiple_heap. }
    iApply ("Hexec" $! (frame :: cstk) (W' :: Ws) (C :: Cs) regs a_stk e_stk).
    iSplitL "Hpost Hlc Hcont".
    { simpl.
      iFrame.
      iEval (cbn).
      iDestruct (interp_cap_disjoint_wl with "Hstk4v") as %[_ Hstk4_heap]; first done.
      iSplitR.
      { iSplit; first (iPureIntro; exact Hstk4_heap).
        iApply (interp_lea with "Hstk4v"); done. }
      iIntros (W'' HW' rcgp rcra rcs0 rcs1 ?????)
        "%Hrcgp %Hrcra %Hrcs0 %Hrcs1 (HPC & Hcra & Hcsp & Hgp & Hcs0 & Hcs1 & Ha0 & #Hv
      & Hca1 & #Hv' & % & Hregs & Hstk & Hstk' & Hworld_interp & Hcls & Hcont & Hcstk & Own)".
      iApply "Hpost";iLeft. simplify_eq.
      iFrame "∗#%".
      iSplit.
      {
        iApply interp_monotone_cap_nonheap;
          [exact Hstk4_heap|exact HW'|].
        done.
      }
      iSplit.
      { iPureIntro; repeat split; solve_addr+Hastk_bstk Hastk_bounds Hastk. }
      iSplit.
      { iPureIntro.
        assert ((e_stk <= e_stk)%a) as He by solve_addr.
        destruct (switcher_disjoint_subseg b_stk e_stk a_stk e_stk
                    Hastk_bstk He (conj Hstk_mmio Hstk_heap)) as [_ Hstack_heap].
        exact Hstack_heap. }

      iSplit; last (iPureIntro; exact (conj Hrcgp (conj Hrcra (conj Hrcs0 Hrcs1)))).
      clear -Hrev HW'.
      iPureIntro; intros k a Ha; cbn.
      eapply region_state_pub_temp;[apply HW'|].
      apply std_sta_update_multiple_lookup_in_i.
      apply list_elem_of_lookup; eauto.
    }
    iSplit.
    { iPureIntro; simpl; split; [|split]; auto.
      apply related_sts_pub_refl_world.
    }
    iFrame "HPC Hregs Hregs_interp Hworld_interp Hcstk Hna".
    iPureIntro; split; [split; reflexivity | solve_addr].
  Qed.

  (* This specification unifies the two possible outcomes of the switcher call.
     It closes the world, and then revokes it.
   *)
  Lemma switcher_cc_specification_gen_revoked
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller.(lw) ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller.(lw) ↦□ₑ nargs
                     (* Argument registers, need to be safe-to-share *)
                     ∗ ( [∗ map] rarg↦warg ∈ arg_rmap,
                           rarg ↦ᵣ warg
                           ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                             then interp W C warg
                             else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
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
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem : list LWord) l' rcgp rcra rcs0 rcs1,
              (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2 (l' ++ (LNonHeap <$> finz.seq_between (a_stk ^+ 4)%a e_stk)) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_keys (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ₚ lupdatePcPerm (rcra)
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
              ∗ ⌜load_heap_in_world W2 wcgp_caller rcgp ∧
                load_heap_in_world W2 wcra_caller rcra ∧
                load_heap_in_world W2 wcs0_caller rcs0 ∧
                load_heap_in_world W2 wcs1_caller rcs1⌝
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})


    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: apply [switcher_cc_specification_gen], then
       revoke the world in the post-condition, with
       [switcher_cc_revoke_returned] when the callee returned, and with
       [switcher_cc_revoke_exhausted] when the trusted stack was exhausted. *)
    iIntros (a_stk4 callee_stk_region Hstk_mmio Hstk_heap Hdom Hrdom) "(#Hswitcher & #Hstatic & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hworld_interp & #Hstk_val & %Hrevoked_stk & Hcstk & Hcont & Hpost)".
    subst a_stk4.
    subst callee_stk_region.
    iApply switcher_cc_specification_gen; eauto; iFrame "∗#%".
    iIntros (W' rmap' stk_mem_l stk_mem_h rcgp rcra rcs0 rcs1).
    iNext; iIntros "[H|H]".
    + clear stk_mem.
      iDestruct "H" as
        "(%Hrelated_pub_Wext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds & %Hstack_heap
      & Hworld_interp_C & Hstack_revoked_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & Hca0 & Hca1 & Hrmap & Hstk_l & Hstk_h & HK & %Hrestored & Hlc)".
      iMod (switcher_cc_revoke_returned with
             "Hinterp_W2_csp Hstk_val Hworld_interp_C Hstack_revoked_W2 Hstk_l Hstk_h Hlc")
        as (stk_mem l') "(% & Hrevoked_l' & % & Hstk_revoked & % & Hworld_interp & Hstk)";
        [done|done|done|].
      iApply "Hpost"; iFrame "∗ %".
    + clear W' stk_mem_l stk_mem_h.
      iDestruct "H" as
        "( %Hdom_rmap & %Hcsp_bounds
           & Hna
           & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
           & Hrmap & Hstk_l & Hstk_h
           & Hworld_interp_C & _
           & Hcstk_frag & HK & %Hrestored & Hlc)".
      iMod (switcher_cc_revoke_exhausted with "Hworld_interp_C Hstk_val Hstk_l Hstk_h Hlc")
        as (l') "(% & Hrevoked_l & % & % & Htemp & Hstk_revoked & % & Hworld_interp & Hstk)";
        [done|done|done|].
      iApply "Hpost"; iFrame "∗ %".
      iSplit; first iApply interp_int.
      iSplit; first iApply interp_int.
      iPureIntro.
      destruct Hrestored as ([Hgp Hgpf] & [Hra Hraf] & [Hs0 Hs0f] & [Hs1 Hs1f]).
      rewrite /load_heap_in_world /filter_heap std_update_multiple_heap.
      by repeat split.
  Qed.

  Lemma switcher_cc_specification
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (w_entry_point : Sealable)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (nargs : nat)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher w_entry_point in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller ∗ interp W C wct1_caller ∗ wct1_caller.(lw) ↦□ₑ nargs
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
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem : list LWord) l' rcgp rcra rcs0 rcs1,
              (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2 (l' ++ (LNonHeap <$> finz.seq_between (a_stk ^+ 4)%a e_stk)) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_keys (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ₚ lupdatePcPerm (rcra)
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
    iIntros (a_stk4 target callee_stk_region Hstk_shadow Hstk_heap Hdom Hrdom) "(#Hswitcher & #Hstatic & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & #Hentry & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hworld_interp & Hstk_val & % & Hcstk & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked Nswitcher W C
      wcgp_caller wcra_caller wcs0_caller wcs1_caller target
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs true).
    1-4: eauto.
    iFrame "Hswitcher Hstatic Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1 Hargs Hregs
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
      & Hrmap & Hstk & Hcont & %Hloaded)".
    destruct Hloaded as ([Hgp _] & [Hra _] & [Hs0 _] & [Hs1 _]).
    assert (load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
            load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1)
      as Hloaded by (repeat split; assumption).
    iApply ("Hpost" $! W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1 with
      "[$Hrev $Hstd $Hstack $Hna $Hworld $Hcstk $HPC $Hcgp $Hcra
        $Hcs0 $Hcs1 $Hcsp $Harg0 $Harg1 $Hrmap $Hstk $Hcont]").
    iFrame "%".
  Qed.

  Lemma switcher_cc_specification_alt
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller ∗ (if is_sealed_with_o wct1_caller.(lw) ot_switcher then interp W C wct1_caller else True)
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
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem : list LWord) l' rcgp rcra rcs0 rcs1,
            (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2 (l' ++ (LNonHeap <$> finz.seq_between (a_stk ^+ 4)%a e_stk)) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_keys (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ₚ lupdatePcPerm (rcra)
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
              ∗ ⌜load_heap_in_world W2 wcgp_caller rcgp ∧
                load_heap_in_world W2 wcra_caller rcra ∧
                load_heap_in_world W2 wcs0_caller rcs0 ∧
                load_heap_in_world W2 wcs1_caller rcs1⌝
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hstk_shadow Hstk_heap Hdom Hrdom) "(#Hswitcher & #Hstatic & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hworld_interp & Hstk_val & % & Hcstk & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked Nswitcher W C
      wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs false).
    1-4: eauto.
    iFrame "Hswitcher Hstatic Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1 Hargs Hregs
      Hstk Hworld_interp Hstk_val Hcstk Hcont Hpost".
    iFrame "Htarget_v".
    iFrame "%".
  Qed.

End Switcher.
