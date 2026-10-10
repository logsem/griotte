From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary fundamental_binary interp_weakening_binary memory_region memory_region_binary.
From griotte Require Import rules proofmode proofmode_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Export switcher switcher_preamble_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary.
From griotte Require Export world_ghost_theory_binary world_interp_stack_binary switcher_helpers_binary.
From griotte Require Import switcher_call_states_binary switcher_call_world_binary
  switcher_call_blocks_1_binary switcher_call_blocks_2_binary switcher_call_blocks_3_binary
  switcher_call_blocks_4_binary switcher_call_blocks_5_binary.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The post-condition of [switcher_cc_specification_gen], once the
      caller's stack pointer [WCap RWL Local b_stk e_stk a_stk] is known. *)
  Definition switcher_cc_post
    (W : WORLD) (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (b_stk e_stk a_stk : Addr) (stk_mem stk_mem_spec : list Word)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) : iProp Σ :=
    ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec : list Word),
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais ⊤
              ∗ ⤇ Seq (Instr Executable)
              ∗ interp W2 C (WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a, WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a)
              ∗ ⌜ (b_stk <= (a_stk ^+ 4)%a ∧ (a_stk ^+ 4)%a <= e_stk ∧ (a_stk + 4) = Some (a_stk ^+ 4)%a)%a ⌝
              (* Interpretation of the world *)
              ∗ world_interp_open W2 C (finz.seq_between (a_stk ^+ 4)%a e_stk)
              ∗ StackOpenWorldResources interp W2 C (finz.seq_between (a_stk ^+ 4)%a e_stk) stk_mem_h stk_mem_h_spec
              ∗ cstack_frag (map fst stk)
              ∗ cstack_frag_spec (map snd stk)
              ∗ ([∗ list] a ∈ (finz.seq_between (a_stk ^+ 4)%a e_stk), ⌜ std W2 !! a = Some Temporary ⌝ )
              ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
              ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ wcgp_caller.1
              ∗ cgp ↣ᵣ wcgp_caller.2
              ∗ cra ↦ᵣ wcra_caller.1
              ∗ cra ↣ᵣ wcra_caller.2
              ∗ cs0 ↦ᵣ wcs0_caller.1
              ∗ cs0 ↣ᵣ wcs0_caller.2
              ∗ cs1 ↦ᵣ wcs1_caller.1
              ∗ cs1 ↣ᵣ wcs1_caller.2
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0.1 ∗ ca0 ↣ᵣ warg0.2 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1.1 ∗ ca1 ↣ᵣ warg1.2 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ stk_mem_l ]]
              ∗ [[ a_stk , (a_stk ^+ 4)%a ]] ↣ₐ [[ stk_mem_l_spec ]]
              ∗ [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ stk_mem_h ]]
              ∗ [[ (a_stk ^+ 4)%a , e_stk ]] ↣ₐ [[ stk_mem_h_spec ]]
              ∗ interp_continuation stk Ws Cs
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't go through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ (b_stk <= (a_stk ^+ 4)%a ∧ (a_stk ^+ 4)%a <= e_stk ∧ (a_stk + 4) = Some (a_stk ^+ 4)%a)%a ⌝
              ∗ na_own cerise_nais ⊤
              ∗ ⤇ Seq (Instr Executable)
              (* Registers are preserved *)
              ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
              ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
              ∗ cgp ↦ᵣ wcgp_caller.1
              ∗ cgp ↣ᵣ wcgp_caller.2
              ∗ cra ↦ᵣ wcra_caller.1
              ∗ cra ↣ᵣ wcra_caller.2
              ∗ cs0 ↦ᵣ wcs0_caller.1
              ∗ cs0 ↣ᵣ wcs0_caller.2
              ∗ cs1 ↦ᵣ wcs1_caller.1
              ∗ cs1 ↣ᵣ wcs1_caller.2
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca0 ↣ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ WInt 0
              ∗ ca1 ↣ᵣ WInt 0
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              (* Stack frame *)
              ∗ [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ [wcs0_caller.1; wcs1_caller.1; wcra_caller.1; wcgp_caller.1] ]]
              ∗ [[ a_stk , (a_stk ^+ 4)%a ]] ↣ₐ [[ [wcs0_caller.2; wcs1_caller.2; wcra_caller.2; wcgp_caller.2] ]]
              ∗ [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ drop 4 stk_mem ]]
              ∗ [[ (a_stk ^+ 4)%a , e_stk ]] ↣ₐ [[ drop 4 stk_mem_spec ]]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_interp W C
              ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
              ∗ cstack_frag (map fst stk)
              ∗ cstack_frag_spec (map snd stk)
              ∗ interp_continuation stk Ws Cs
              ∗ £ 2
            )
          )

      -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.

  (** Failure path of [switcher_cc_specification_gen]: the trusted stack is
      exhausted. *)
  Lemma switcher_cc_spec_tstack_exhausted
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (wct1_caller wct2 swct2 wctp swctp : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    (a_tstk : Addr) (tstk_next ststk_next : list Word) :
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->
    (b_trusted_stack + length (map fst stk))%a = Some a_tstk ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    spec_ctx ∗
    (▷ switcher_inv_binary ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) ∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) ∗
    ⤇ Seq (Instr Executable) ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↣ₐ [[ ststk_next ]] ∗
    switcher_code ∗
    switcher_spec_code ∗
    b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    b_switcher ↣ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    cstack_full (map fst stk) ∗
    cstack_full_spec (map snd stk) ∗
    cstack_interp (map fst stk) a_tstk ∗
    cstack_interp_spec (map snd stk) a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ᵣ switcher_block_pc 16 ∗
    PC ↣ᵣ switcher_block_pc 16 ∗
    (∃ w sw, cs0 ↦ᵣ w ∗ cs0 ↣ᵣ sw) ∗
    cs1 ↦ᵣ wcs1_caller.1 ∗
    cs1 ↣ᵣ wcs1_caller.2 ∗
    cgp ↦ᵣ wcgp_caller.1 ∗
    cgp ↣ᵣ wcgp_caller.2 ∗
    cra ↦ᵣ wcra_caller.1 ∗
    cra ↣ᵣ wcra_caller.2 ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    ct1 ↦ᵣ wct1_caller ∗
    ct1 ↣ᵣ wct1_caller ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    csp ↣ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
    switcher_stk_cells a_stk wcs0_caller.1 wcs1_caller.1 wcra_caller.1 wcgp_caller.1 ∗
    switcher_stk_cells_spec a_stk wcs0_caller.2 wcs1_caller.2 wcra_caller.2 wcgp_caller.2 ∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ drop 4 stk_mem ]] ∗
    [[ (a_stk ^+ 4)%a , e_stk ]] ↣ₐ [[ drop 4 stk_mem_spec ]] ∗
    (if is_entry_point_known
     then ∃ nargs, wct1_caller ↦□ₑ nargs
                   ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
                         rarg ↦ᵣ warg
                         ∗ rarg ↣ᵣ sarg
                         ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                           then interp W C (warg, sarg)
                           else True )
     else ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
              rarg ↦ᵣ warg
              ∗ rarg ↣ᵣ sarg
              ∗ interp W C (warg, sarg) )
    ) ∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), r ↦ᵣ w ) ∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 smap), r ↣ᵣ w ) ∗
    world_interp W C ∗
    StackRevokedResources W C (finz.seq_between a_stk e_stk) ∗
    cstack_frag (map fst stk) ∗
    cstack_frag_spec (map snd stk) ∗
    interp_continuation stk Ws Cs ∗
    switcher_cc_post W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk stk_mem stk_mem_spec stk Ws Cs
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: [switcher_cc_exhausted_regs] collects the
       registers, [switcher_call_blocks_5_spec] executes blocks 16 and 14-15,
       then close the switcher invariant and use the second post-condition. *)
    iIntros (Hdom Hsdom Hrdom Hsrdom Hstk_bounds Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Hot_bounds)
      "(#Hspec & Hclose_switcher_inv & Hna & Hj & Hmtdc & Hsmtdc & Htstk & Hststk & Hcode & Hscode
      & Hb_switcher & Hsb_switcher & Hcstk_full & Hcstk_full_spec & Hstk_interp & Hsstk_interp
      & #Hp_ot_switcher & HPC & HsPC & Hcs0 & Hcs1 & Hscs1 & Hcgp & Hscgp & Hcra & Hscra
      & Hctp & Hsctp & Hct2 & Hsct2 & Hct1 & Hsct1 & Hcsp & Hscsp & Hcells & Hscells & Hstk & Hsstk
      & Hargs & Hregs & Hsregs & Hworld_interp & Hstk_val & Hcstk & Hcstk_spec & Hcont & Hpost)".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    iAssert (([∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w) ∗ ([∗ map] r↦w ∈ arg_smap, r ↣ᵣ w))%I
      with "[Hargs]" as "[Hargs Hsargs]".
    { iAssert ([∗ map] r↦w;sw ∈ arg_rmap;arg_smap, r ↦ᵣ w ∗ r ↣ᵣ sw)%I with "[Hargs]" as "Hargs".
      { destruct is_entry_point_known.
        + iDestruct "Hargs" as "(% & _ & Hargs)".
          iApply (big_sepM2_impl with "Hargs").
          iIntros "!> %rk %rv1 %rv2 _ _ ($ & $ & _)".
        + iApply (big_sepM2_impl with "Hargs").
          iIntros "!> %rk %rv1 %rv2 _ _ ($ & $ & _)".
      }
      iDestruct (big_sepM2_sepM with "Hargs") as "$".
      intros k. rewrite -!elem_of_dom Hrdom Hsrdom. done.
    }
    iDestruct (switcher_cc_exhausted_regs with
                "Hargs Hsargs Hregs Hsregs Hct1 Hsct1 Hct2 Hsct2 Hctp Hsctp")
      as (wca0 swca0 wca1 swca1 rmap0 smap0)
           "(Hca0 & Hsca0 & Hca1 & Hsca1 & %Hrmap0 & %Hsmap0 & Hrmap0 & Hsmap0)";
      [done|done|done|done|].
    iApply (switcher_call_blocks_5_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hcsp $Hscsp $Hcells $Hscells $Hrmap0 $Hsmap0 $Hcode $Hscode]");
      [done|done|done|].
    iSplitL "Hcs1 Hscs1"; first iFrame.
    iSplitL "Hcgp Hscgp"; first iFrame.
    iSplitL "Hcra Hscra"; first iFrame.
    iSplitL "Hca0 Hsca0"; first iFrame.
    iSplitL "Hca1 Hsca1"; first iFrame.
    iNext; iIntros (rmap')
      "(%Hrmap' & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcgp & Hscgp & Hcra & Hscra
      & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcsp & Hscsp & Hcells & Hscells & Hrmap & Hcode & Hscode & Hlc)".
    iMod ("Hclose_switcher_inv"
           with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk
                  Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
    { iNext. iSplitL "Hmtdc Hcode Hb_switcher Htstk Hcstk_full Hstk_interp".
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto. by rewrite !length_map in Hlen_cstk |- *.
    }
    iApply ("Hpost" $! W rmap' [] [] [] []); iRight; iFrame "∗ %".
    iDestruct (switcher_stk_cells_region_4 with "Hcells") as "$"; first done.
    iDestruct (switcher_stk_cells_region_4_spec with "Hscells") as "$"; first done.
    iPureIntro.
    split; first solve_addr+Hastk Hastk_bstk.
    split; first solve_addr+Hastk Hastk_bounds Hastk_bstk.
    done.
  Qed.

  (** Specification of the switcher-call routine, for a trusted caller
      calling the same entry point in both runs (lockstep).

      The caller-saved registers [cgp], [cra], [cs0] and [cs1] may contain
      different words in the two runs: they are pairs of words. The stack
      pointer is the same in both runs, but the contents of the stack frame
      may differ. The entry point [wct1_caller] is the same in both runs. The
      argument registers are related when they are passed to the callee.

      The switcher pushes on both call stacks a pair of frames with the same
      stack bounds, each recording the callee-saved registers of its own run.
      As both trusted stacks have the same depth, the call either goes
      through in both runs, or fails in both runs because the trusted stack
      is exhausted. *)
  Lemma switcher_cc_specification_gen
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller.1
    ∗ cgp ↣ᵣ wcgp_caller.2
    ∗ cra ↦ᵣ wcra_caller.1
    ∗ cra ↣ᵣ wcra_caller.2
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C (wct1_caller, wct1_caller) else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller ↦□ₑ nargs
                     (* Argument registers, need to be related *)
                     ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
                           rarg ↦ᵣ warg
                           ∗ rarg ↣ᵣ sarg
                           ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                             then interp W C (warg, sarg)
                             else True )
       else ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
                rarg ↦ᵣ warg
                ∗ rarg ↣ᵣ sarg
                ∗ interp W C (warg, sarg) )
      )
    ∗ cs0 ↦ᵣ wcs0_caller.1
    ∗ cs0 ↣ᵣ wcs0_caller.2
    ∗ cs1 ↦ᵣ wcs1_caller.1
    ∗ cs1 ↣ᵣ wcs1_caller.2
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec : list Word),
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais ⊤
              ∗ ⤇ Seq (Instr Executable)
              ∗ interp W2 C (WCap RWL Local a_stk4 e_stk a_stk4, WCap RWL Local a_stk4 e_stk a_stk4)
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              (* Interpretation of the world *)
              ∗ world_interp_open W2 C callee_stk_region
              ∗ StackOpenWorldResources interp W2 C callee_stk_region stk_mem_h stk_mem_h_spec
              ∗ cstack_frag (map fst stk)
              ∗ cstack_frag_spec (map snd stk)
              ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
              ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
              ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ wcgp_caller.1
              ∗ cgp ↣ᵣ wcgp_caller.2
              ∗ cra ↦ᵣ wcra_caller.1
              ∗ cra ↣ᵣ wcra_caller.2
              ∗ cs0 ↦ᵣ wcs0_caller.1
              ∗ cs0 ↣ᵣ wcs0_caller.2
              ∗ cs1 ↦ᵣ wcs1_caller.1
              ∗ cs1 ↣ᵣ wcs1_caller.2
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0.1 ∗ ca0 ↣ᵣ warg0.2 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1.1 ∗ ca1 ↣ᵣ warg1.2 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ a_stk , a_stk4 ]] ↦ₐ [[ stk_mem_l ]]
              ∗ [[ a_stk , a_stk4 ]] ↣ₐ [[ stk_mem_l_spec ]]
              ∗ [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem_h ]]
              ∗ [[ a_stk4 , e_stk ]] ↣ₐ [[ stk_mem_h_spec ]]
              ∗ interp_continuation stk Ws Cs
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't go through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              ∗ na_own cerise_nais ⊤
              ∗ ⤇ Seq (Instr Executable)
              (* Registers are preserved *)
              ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
              ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
              ∗ cgp ↦ᵣ wcgp_caller.1
              ∗ cgp ↣ᵣ wcgp_caller.2
              ∗ cra ↦ᵣ wcra_caller.1
              ∗ cra ↣ᵣ wcra_caller.2
              ∗ cs0 ↦ᵣ wcs0_caller.1
              ∗ cs0 ↣ᵣ wcs0_caller.2
              ∗ cs1 ↦ᵣ wcs1_caller.1
              ∗ cs1 ↣ᵣ wcs1_caller.2
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca0 ↣ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ WInt 0
              ∗ ca1 ↣ᵣ WInt 0
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              (* Stack frame *)
              ∗ [[ a_stk , a_stk4 ]] ↦ₐ [[ [wcs0_caller.1; wcs1_caller.1; wcra_caller.1; wcgp_caller.1] ]]
              ∗ [[ a_stk , a_stk4 ]] ↣ₐ [[ [wcs0_caller.2; wcs1_caller.2; wcra_caller.2; wcgp_caller.2] ]]
              ∗ [[ a_stk4 , e_stk ]] ↦ₐ [[ drop 4 stk_mem ]]
              ∗ [[ a_stk4 , e_stk ]] ↣ₐ [[ drop 4 stk_mem_spec ]]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_interp W C
              ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
              ∗ cstack_frag (map fst stk)
              ∗ cstack_frag_spec (map snd stk)
              ∗ interp_continuation stk Ws Cs
              ∗ £ 2
            )
          )
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}
  )

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant of both runs;
       - [switcher_call_blocks_1_spec]: checks on the stack pointer;
       - [switcher_call_blocks_2_spec]: spill the callee-save registers and
         push the stack pointer on both trusted stacks;
       - when the trusted stack is exhausted:
         [switcher_cc_spec_tstack_exhausted];
       - [switcher_entry_point_prop]: the entry point satisfies the sealing
         predicate of the switcher;
       - [switcher_call_blocks_3_spec]: clear the callee's stack frame and
         unseal the entry point;
       - [switcher_cc_world_reinstate]: reinstate the callee's stack frame;
       - [switcher_call_blocks_4_spec]: load the callee and jump to it;
       - [switcher_inv_push_frame], [switcher_inv_spec_push_frame]: close
         the switcher invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros (a_stk4 callee_stk_region Hdom Hsdom Hrdom Hsrdom)
      "(#Hswitcher & #Hspec & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp
        & Hct1 & Hsct1 & #Htarget_v & Hargs & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hregs & Hsregs
        & Hstk & Hsstk & Hworld_interp & #Hstk_val & %Hstk_revoked & Hcstk & Hcstk_spec & Hcont & Hpost)".
    subst a_stk4 callee_stk_region.

    assert (is_Some (rmap !! ct2)) as [??].
    { apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|rewrite /dom_arg_rmap /=; set_solver]. }
    assert (is_Some (rmap !! ctp)) as [??].
    { apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|rewrite /dom_arg_rmap /=; set_solver]. }
    iExtractList "Hregs" [ct2;ctp] as ["Hct2";"Hctp"].
    assert (is_Some (smap !! ct2)) as [??].
    { apply elem_of_dom. rewrite Hsdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|rewrite /dom_arg_rmap /=; set_solver]. }
    assert (is_Some (smap !! ctp)) as [??].
    { apply elem_of_dom. rewrite Hsdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|rewrite /dom_arg_rmap /=; set_solver]. }
    iExtractList "Hsregs" [ct2;ctp] as ["Hsct2";"Hsctp"].

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "([Hswitcher_inv Hswitcher_inv_spec] & Hna & Hclose_switcher_inv)" ; auto.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & >Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iDestruct "Hswitcher_inv_spec"
      as (sa_tstk scstk' ststk_next)
           "(>Hsmtdc & >Hscode & >Hsb_switcher & >Hststk & >[%Hsbounds_tstk_b %Hsbounds_tstk_e]
           & >Hcstk_full_spec & >%Hslen_cstk & Hsstk_interp)".
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iDestruct (cstack_agree_spec with "Hcstk_full_spec Hcstk_spec") as %->.
    assert (sa_tstk = a_tstk) as ->.
    { eapply a_tstk_eq; [|exact Hslen_cstk|exact Hlen_cstk]. by rewrite !length_map. }
    clear Hsbounds_tstk_b Hsbounds_tstk_e Hslen_cstk.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    (* Blocks 0-1: checks on the stack pointer *)
    iApply (switcher_call_blocks_1_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcsp $Hscsp $Hct2 $Hsct2 $Hctp $Hsctp $Hcode $Hscode]").
    iNext; iIntros "[(_ & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp & Hcode & Hscode)
                    | (%Hcontra & _)]";
      last (exfalso; apply Hcontra, switcher_csp_checked_stk).

    (* Blocks 2-3: spill and push on the trusted stack *)
    iApply (switcher_call_blocks_2_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hcra $Hscra $Hcgp $Hscgp $Hctp $Hsctp
        $Hct2 $Hsct2 $Hcsp $Hscsp $Hstk $Hsstk $Hmtdc $Hsmtdc $Htstk $Hststk $Hcode $Hscode]");
      [done|done|].
    iNext; iIntros "(%Hstk_bounds & Hj & Hcs1 & Hscs1 & Hcra & Hscra & Hcgp & Hscgp & Hcsp & Hscsp
      & Hcells & Hscells & Hstk & Hsstk & Hcode & Hscode & Hbranch)".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    iDestruct "Hbranch" as
      "[(%Ha_tstk2 & %Ha_tstk1_bound & HPC & HsPC & Hcs0 & Hscs0 & Hctp & Hsctp & Hct2 & Hsct2
         & Hmtdc & Hsmtdc & Ha_tstk1 & Hsa_tstk1 & Htstk & Hststk & Hlc)
       | (HPC & HsPC & Hcs0 & Hscs0 & Hctp & Hsctp & Hct2 & Hsct2 & Hmtdc & Hsmtdc & Htstk & Hststk)]";
      cycle 1.
    { (* The trusted stack is exhausted *)
      iApply (switcher_cc_spec_tstack_exhausted with
        "[$Hspec $Hclose_switcher_inv $Hna $Hj $Hmtdc $Hsmtdc $Htstk $Hststk $Hcode $Hscode
          $Hb_switcher $Hsb_switcher $Hcstk_full $Hcstk_full_spec $Hstk_interp $Hsstk_interp
          $Hp_ot_switcher $HPC $HsPC Hcs0 Hscs0 $Hcs1 $Hscs1 $Hcgp $Hscgp $Hcra $Hscra $Hctp $Hsctp
          $Hct2 $Hsct2 $Hct1 $Hsct1 $Hcsp $Hscsp $Hcells $Hscells $Hstk $Hsstk
          $Hargs $Hregs $Hsregs $Hworld_interp $Hstk_val $Hcstk $Hcstk_spec $Hcont $Hpost]");
        [done..|iFrame].
    }

    (* Blocks 4-7: clear the callee's stack frame and unseal the entry point *)
    iDestruct (switcher_entry_point_prop with "Hp_ot_switcher Htarget_v") as "Hentry_prop".
    iApply (switcher_call_blocks_3_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hcsp $Hscsp $Hstk $Hsstk
        $Hb_switcher $Hsb_switcher $Hct1 $Hsct1 $Hcode $Hscode]"); [done|by intros|].
    iNext; iIntros (wsb) "(-> & Hj & HPC & HsPC & Hcs0 & Hscs0 & (%wcs1' & Hcs1 & Hscs1)
      & Hcsp & Hscsp & Hstk & Hsstk & Hb_switcher & Hsb_switcher & Hct1 & Hsct1 & Hcode & Hscode)".
    iDestruct "Hentry_prop" as "[_ Hentry_prop]".
    iDestruct ("Hentry_prop" with "[//]")
      as (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs off Nexp_tbl Heq Heq' Htbl Hbtbl Hbtbl1 Hnargs)
           "(Htbl1 & Htbl2 & Htbl3 & #Hentry' & #Hexec)".
    cbn in Heq; simplify_eq.
    iAssert ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
                rarg ↦ᵣ warg
                ∗ rarg ↣ᵣ sarg
                ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                  then interp W C (warg, sarg)
                  else True )%I with "[Hargs]" as "Hargs".
    { destruct is_entry_point_known.
      + iDestruct "Hargs" as "(%nargs0 & Hentry & Hargs)".
        iEval (cbn) in "Hentry'".
        iDestruct (entry_agree _ nargs nargs0 with "Hentry' Hentry") as "<-".
        iFrame.
      + iApply (big_sepM2_impl with "Hargs").
        iIntros "!> %k %w1 %w2 _ _ ($ & $ & Hinterp)".
        destruct ( decide (k ∈ dom_arg_rmap nargs) ) ; auto.
    }

    (* Reinstate the callee's stack frame in the world *)
    iMod (switcher_cc_world_reinstate with "Hworld_interp Hstk_val Hstk Hsstk")
      as "(Hworld_interp & #Hstk4v & %Hrelated & %Hrev)"; [done|done|solve_addr|].
    set (W' := std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary).
    iSpecialize ("Hexec" $! W' with "[]").
    { iPureIntro. by apply related_sts_pub_priv_world. }

    (* Blocks 7-11: load the callee and jump to it *)
    iApply (switcher_call_blocks_4_spec W C with
      "[- $Hspec $Hj $Htbl1 $Htbl2 $Htbl3 $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hct1 $Hsct1
        $Hct2 $Hsct2 $Hctp $Hsctp $Hcgp $Hscgp $Hcra $Hscra $Hargs $Hregs $Hsregs $Hcode $Hscode]");
      [done|done|lia|done|done| | |].
    { rewrite !dom_delete_L Hdom. set_solver. }
    { rewrite !dom_delete_L Hsdom. set_solver. }
    iNext; iIntros (arg_rmap' arg_smap' rmap' smap')
      "(%Harg_rmap' & %Harg_smap' & %Hrmap' & %Hsmap' & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra
      & Hargs & Hregs & Hsregs & Hcode & Hscode)".

    (* Push the frames and close the switcher invariant *)
    set (frm1 :=
           {| wret := wcra_caller.1;
              wcgp := wcgp_caller.1;
              wcs0 := wcs0_caller.1;
              wcs1 := wcs1_caller.1;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Unknown
           |}).
    set (frm2 :=
           {| wret := wcra_caller.2;
              wcgp := wcgp_caller.2;
              wcs0 := wcs0_caller.2;
              wcs1 := wcs1_caller.2;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Unknown
           |}).
    iMod (switcher_inv_push_frame frm1 (map fst stk) with
           "Hcstk_full Hcstk Hmtdc Ha_tstk1 Htstk Hstk_interp [Hcells] Hcode Hb_switcher Hp_ot_switcher")
      as "[Hinv Hcstk]"; [done|done|done|done|done|done| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
    iMod (switcher_inv_spec_push_frame frm2 (map snd stk) with
           "Hcstk_full_spec Hcstk_spec Hsmtdc Hsa_tstk1 Hststk Hsstk_interp [Hscells] Hscode Hsb_switcher")
      as "[Hsinv Hcstk_spec]"; [done|done|done| |done| |].
    { by rewrite !length_map in Hlen_cstk |- *. }
    { rewrite /cframe_stk_own_spec /=. iDestruct "Hscells" as "($&$&$&$)". }
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hsinv $Hna]") as "Hna".

    (* Execute the entry point of the callee *)
    iDestruct (switcher_call_entry_registers W W' C nargs arg_rmap' arg_smap' rmap' smap' with
                "[$HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hstk4v $Hargs $Hregs $Hsregs]")
      as (regs1 regs2) "(Hregs & Hsregs & Hregs_interp)"; [done|done|done|done|done|].
    iApply ("Hexec" $! ((frm1, frm2) :: stk) (W' :: Ws) (C :: Cs) regs1 regs2 a_stk e_stk).
    iSplitR; first iFrame "#".
    iSplitL "Hcont Hpost Hlc".
    { iFrame "Hcont". simpl.
      iSplit; first (iPureIntro; done).
      iSplit; first (iApply (interp_lea with "Hstk4v"); done).
      iIntros (W2 HW2 wca0 wca1 regs stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec)
        "(_ & HPC & HsPC & Hcra & Hscra & Hcsp & Hscsp & Hcgp & Hscgp & Hcs0 & Hscs0 & Hcs1 & Hscs1
          & Hca0 & Hsca0 & #Hv0 & Hca1 & Hsca1 & #Hv1 & %Hdom_regs & Hregs
          & Hstk_l & Hsstk_l & Hstk_h & Hsstk_h & Hworld_interp & Hres & Hcont' & Hcstk & Hcstk_spec
          & Hj & Hna)".
      iApply ("Hpost" $! W2 regs); iLeft.
      iFrame "∗#%".
      iSplit.
      { iApply interp_monotone; first done.
        iApply (interp_lea with "Hstk4v"); done. }
      iSplit.
      { iPureIntro; repeat split; solve_addr. }
      iPureIntro; intros k a Ha; cbn.
      eapply region_state_pub_temp;[apply HW2|].
      apply std_sta_update_multiple_lookup_in_i.
      apply list_elem_of_lookup; eauto.
    }
    iSplitR.
    { iPureIntro; simpl; split; [|split]; auto.
      apply related_sts_pub_refl_world.
    }
    iFrame "Hregs Hsregs Hregs_interp Hworld_interp Hcstk Hcstk_spec Hna Hj".
    iPureIntro; split; [repeat split; reflexivity | solve_addr].
  Qed.


  (** This specification unifies the two possible outcomes of the switcher
      call. It closes the world, and then revokes it. *)
  Lemma switcher_cc_specification_gen_revoked
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller.1
    ∗ cgp ↣ᵣ wcgp_caller.2
    ∗ cra ↦ᵣ wcra_caller.1
    ∗ cra ↣ᵣ wcra_caller.2
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C (wct1_caller, wct1_caller) else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller ↦□ₑ nargs
                     (* Argument registers, need to be related *)
                     ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
                           rarg ↦ᵣ warg
                           ∗ rarg ↣ᵣ sarg
                           ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                             then interp W C (warg, sarg)
                             else True )
       else ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
                rarg ↦ᵣ warg
                ∗ rarg ↣ᵣ sarg
                ∗ interp W C (warg, sarg) )
      )
    ∗ cs0 ↦ᵣ wcs0_caller.1
    ∗ cs0 ↣ᵣ wcs0_caller.2
    ∗ cs1 ↦ᵣ wcs1_caller.1
    ∗ cs1 ↣ᵣ wcs1_caller.2
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem stk_mem_spec : list Word) l',
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
            ∗ ⤇ Seq (Instr Executable)
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag (map fst stk)
            ∗ cstack_frag_spec (map snd stk)
            ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
            ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ wcgp_caller.1
            ∗ cgp ↣ᵣ wcgp_caller.2
            ∗ cra ↦ᵣ wcra_caller.1
            ∗ cra ↣ᵣ wcra_caller.2
            ∗ cs0 ↦ᵣ wcs0_caller.1
            ∗ cs0 ↣ᵣ wcs0_caller.2
            ∗ cs1 ↦ᵣ wcs1_caller.1
            ∗ cs1 ↣ᵣ wcs1_caller.2
            ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0.1 ∗ ca0 ↣ᵣ warg0.2 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1.1 ∗ ca1 ↣ᵣ warg1.2 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]
            ∗ interp_continuation stk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: apply [switcher_cc_specification_gen], then
       revoke the world in the post-condition, with
       [switcher_cc_revoke_returned] when the callee returned, and with
       [switcher_cc_revoke_exhausted] when the trusted stack was exhausted. *)
    iIntros (a_stk4 callee_stk_region Hdom Hsdom Hrdom Hsrdom)
      "(#Hswitcher & #Hspec & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp
        & Hct1 & Hsct1 & #Htarget_v & Hargs & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hregs & Hsregs
        & Hstk & Hsstk & Hworld_interp & #Hstk_val & %Hrevoked_stk & Hcstk & Hcstk_spec & Hcont & Hpost)".
    subst a_stk4.
    subst callee_stk_region.
    iApply (switcher_cc_specification_gen with "[-]");
      [exact Hdom|exact Hsdom|exact Hrdom|exact Hsrdom|].
    iFrame "∗#%".
    iIntros (W' rmap' stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec).
    iNext; iIntros "[H|H]".
    + clear stk_mem stk_mem_spec.
      iDestruct "H" as
        "(%Hrelated_pub_Wext_W2 & %Hdom_rmap & Hna & Hj & #Hinterp_W2_csp & %Hcsp_bounds
      & Hworld_interp_C & Hstack_revoked_W2
      & Hcstk_frag & Hcstk_frag_spec & Hrel_stk_C
      & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcsp & Hscsp
      & Hca0 & Hca1 & Hrmap & Hstk_l & Hsstk_l & Hstk_h & Hsstk_h & HK & Hlc)".
      iMod (switcher_cc_revoke_returned with
             "Hinterp_W2_csp Hstk_val Hworld_interp_C Hstack_revoked_W2 Hstk_l Hsstk_l Hstk_h Hsstk_h Hlc")
        as (stk_mem stk_mem_spec l')
             "(% & Hrevoked_l' & % & Hstk_revoked & % & Hworld_interp & Hstk & Hsstk)";
        [done|done|done|].
      iApply "Hpost"; iFrame "∗ %".
    + clear W' stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec.
      iDestruct "H" as
        "( %Hdom_rmap & %Hcsp_bounds
           & Hna & Hj
           & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcsp & Hscsp
           & Hca0 & Hsca0 & Hca1 & Hsca1
           & Hrmap & Hstk_l & Hsstk_l & Hstk_h & Hsstk_h
           & Hworld_interp_C & _
           & Hcstk_frag & Hcstk_frag_spec & HK & Hlc)".
      iMod (switcher_cc_revoke_exhausted with
             "Hworld_interp_C Hstk_val Hstk_l Hsstk_l Hstk_h Hsstk_h Hlc")
        as (l') "(% & Hrevoked_l & % & % & Htemp & Hstk_revoked & % & Hworld_interp & Hstk & Hsstk)";
        [done|done|done|done|].
      iApply "Hpost"; iFrame "∗ %".
      iSplitL "Hca0 Hsca0".
      { iExists (WInt ENOTENOUGHTRUSTEDSTACK, WInt ENOTENOUGHTRUSTEDSTACK). iFrame. iApply interp_int. }
      iExists (WInt 0, WInt 0). iFrame. iApply interp_int.
  Qed.


  (** Specification of the switcher-call routine, for a trusted caller
      calling a known entry point of a compartment, the same in both runs.
      Only the arguments of the entry point need to be related. *)
  Lemma switcher_cc_specification
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (b_stk e_stk a_stk : Addr)
    (w_entry_point : Sealable)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (nargs : nat)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher w_entry_point in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller.1
    ∗ cgp ↣ᵣ wcgp_caller.2
    ∗ cra ↦ᵣ wcra_caller.1
    ∗ cra ↣ᵣ wcra_caller.2
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ interp W C (wct1_caller, wct1_caller)
    ∗ wct1_caller ↦□ₑ nargs
    ∗ cs0 ↦ᵣ wcs0_caller.1
    ∗ cs0 ↣ᵣ wcs0_caller.2
    ∗ cs1 ↦ᵣ wcs1_caller.1
    ∗ cs1 ↣ᵣ wcs1_caller.2
    (* Argument registers, need to be related *)
    ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
          rarg ↦ᵣ warg
          ∗ rarg ↣ᵣ sarg
          ∗ if decide (rarg ∈ dom_arg_rmap nargs)
            then interp W C (warg, sarg)
            else True )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem stk_mem_spec : list Word) l',
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
            ∗ ⤇ Seq (Instr Executable)
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag (map fst stk)
            ∗ cstack_frag_spec (map snd stk)
            ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
            ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ wcgp_caller.1
            ∗ cgp ↣ᵣ wcgp_caller.2
            ∗ cra ↦ᵣ wcra_caller.1
            ∗ cra ↣ᵣ wcra_caller.2
            ∗ cs0 ↦ᵣ wcs0_caller.1
            ∗ cs0 ↣ᵣ wcs0_caller.2
            ∗ cs1 ↦ᵣ wcs1_caller.1
            ∗ cs1 ↣ᵣ wcs1_caller.2
            ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0.1 ∗ ca0 ↣ᵣ warg0.2 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1.1 ∗ ca1 ↣ᵣ warg1.2 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]
            ∗ interp_continuation stk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 target callee_stk_region Hdom Hsdom Hrdom Hsrdom)
      "(#Hswitcher & #Hspec & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp
        & Hct1 & Hsct1 & #Htarget_v & #Hentry & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hargs & Hregs & Hsregs
        & Hstk & Hsstk & Hworld_interp & Hstk_val & %Hrevoked_stk & Hcstk & Hcstk_spec & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked
              Nswitcher W C wcgp_caller wcra_caller wcs0_caller wcs1_caller target
              b_stk e_stk a_stk stk_mem stk_mem_spec arg_rmap arg_smap rmap smap stk Ws Cs true
             with "[-]");
      [exact Hdom|exact Hsdom|exact Hrdom|exact Hsrdom|].
    iFrame "∗#%".
    subst target; cbn.
    destruct ( (ot_switcher =? ot_switcher)%Z ); eauto.
  Qed.


  (** Specification of the switcher-call routine, for a trusted caller
      calling an arbitrary entry point, the same in both runs. All the
      argument registers need to be related. *)
  Lemma switcher_cc_specification_alt
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller.1
    ∗ cgp ↣ᵣ wcgp_caller.2
    ∗ cra ↦ᵣ wcra_caller.1
    ∗ cra ↣ᵣ wcra_caller.2
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C (wct1_caller, wct1_caller) else True)
    ∗ cs0 ↦ᵣ wcs0_caller.1
    ∗ cs0 ↣ᵣ wcs0_caller.2
    ∗ cs1 ↦ᵣ wcs1_caller.1
    ∗ cs1 ↣ᵣ wcs1_caller.2
    (* Argument registers, need to be related *)
    ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
          rarg ↦ᵣ warg
          ∗ rarg ↣ᵣ sarg
          ∗ interp W C (warg, sarg) )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem stk_mem_spec : list Word) l',
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
            ∗ ⤇ Seq (Instr Executable)
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag (map fst stk)
            ∗ cstack_frag_spec (map snd stk)
            ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
            ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ wcgp_caller.1
            ∗ cgp ↣ᵣ wcgp_caller.2
            ∗ cra ↦ᵣ wcra_caller.1
            ∗ cra ↣ᵣ wcra_caller.2
            ∗ cs0 ↦ᵣ wcs0_caller.1
            ∗ cs0 ↣ᵣ wcs0_caller.2
            ∗ cs1 ↦ᵣ wcs1_caller.1
            ∗ cs1 ↣ᵣ wcs1_caller.2
            ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0.1 ∗ ca0 ↣ᵣ warg0.2 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1.1 ∗ ca1 ↣ᵣ warg1.2 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]
            ∗ interp_continuation stk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hdom Hsdom Hrdom Hsrdom)
      "(#Hswitcher & #Hspec & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp
        & Hct1 & Hsct1 & #Htarget_v & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hargs & Hregs & Hsregs
        & Hstk & Hsstk & Hworld_interp & Hstk_val & %Hrevoked_stk & Hcstk & Hcstk_spec & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked
              Nswitcher W C wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
              b_stk e_stk a_stk stk_mem stk_mem_spec arg_rmap arg_smap rmap smap stk Ws Cs false
             with "[-]");
      [exact Hdom|exact Hsdom|exact Hrdom|exact Hsrdom|].
    iFrame "∗#%".
  Qed.

End Switcher.
