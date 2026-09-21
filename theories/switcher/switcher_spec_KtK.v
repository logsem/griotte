From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import
  switcher_spec_KtK_call switcher_spec_KtK_return.
From griotte Require Import map_simpl register_tactics.


Section Switcher_KtK.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Shape of the higher-order specification for entry points
      in the case of known-to-known cross-compartment calls.
      [P] is the precondition of the callee,
      and [Q] is the postcondition, parameterised by the returned values.

      The frame remembers call-time bits. The return continuation accepts
      independent return-time bits with their ownership, so quarantining a
      saved allocation does not require changing the ghost call-stack.
   **)
  Definition switcher_cc_specification_known_to_known_function
    (P : iProp Σ) (Q : Word -> Word -> iProp Σ)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap : Reg)
    (cstk : CSTK)
    (nargs : nat)
    (E : coPset)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z)
    (scgp scra scs0 scs1 : option bool)
    : iProp Σ :=
    let a_stk4 := (a_stk ^+ 4)%a in
    let frame :=
           {| wret := wcra_caller;
              wcgp := wcgp_caller;
              wcs0 := wcs0_caller;
              wcs1 := wcs1_caller;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Known;
              shadow_cgp := scgp;
              shadow_cra := scra;
              shadow_cs0 := scs0;
              shadow_cs1 := scs1
           |}
    in
    (∀ (arg_rmap' rmap' : Reg),
       ⌜ is_arg_rmap arg_rmap' 8 ⌝
       ∗ ⌜ dom rmap' =
             all_registers_s ∖
               ({[ PC ; cgp ; cra ; csp ]} ∪ dom_arg_rmap 8) ⌝
       ∗ na_own cerise_nais E
       ∗ PC ↦ᵣ WCap true RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a
       ∗ cgp ↦ᵣ WCap true RW Global bcgp_tgt ecgp_tgt bcgp_tgt
       ∗ cra ↦ᵣ WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return
       ∗ csp ↦ᵣ WCap true RWL Local a_stk4 e_stk a_stk4
       ∗ ([∗ map] rarg↦warg ∈ arg_rmap',
            rarg ↦ᵣ warg
            ∗ if decide (rarg ∈ dom_arg_rmap nargs)
              then ⌜ arg_rmap !! rarg = Some warg ⌝
              else ⌜ warg = WInt 0 ⌝)
       ∗ ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
       ∗ [[ a_stk4 , e_stk ]] ↦ₐ
           [[ region_addrs_zeroes a_stk4 e_stk ]]
       ∗ cstack_frag (frame :: cstk)
       ∗ saved_registers_shadow wcgp_caller wcra_caller wcs0_caller wcs1_caller scgp scra scs0 scs1
       ∗ P
       ∗ ▷ (∀ (scgp_ret scra_ret scs0_ret scs1_ret : option bool) (wca0 wca1 : Word) (rmap_ret : Reg)
                (stk_mem_ret : list Word),
              ⌜ dom rmap_ret =
                    all_registers_s ∖
                      {[ PC ; csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
              ∗ na_own cerise_nais E
              ∗ PC ↦ᵣ WCap true XSRW_ Local
                          b_switcher e_switcher a_switcher_return
              ∗ cgp ↦ᵣ - ∗ cra ↦ᵣ - ∗ cs0 ↦ᵣ - ∗ cs1 ↦ᵣ -
              ∗ csp ↦ᵣ WCap true RWL Local a_stk4 e_stk a_stk4
              ∗ ca0 ↦ᵣ wca0
              ∗ ca1 ↦ᵣ wca1
              ∗ ([∗ map] r↦w ∈ rmap_ret, r ↦ᵣ w)
              ∗ [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem_ret ]]
              ∗ cstack_frag (frame :: cstk)
       ∗ saved_registers_shadow wcgp_caller wcra_caller wcs0_caller wcs1_caller scgp_ret scra_ret scs0_ret scs1_ret
              ∗ Q wca0 wca1
                -∗ WP Seq (Instr Executable)
                      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
       -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.


  (** Specification of the switcher for known-to-known cross compartment call,
      with higher-order specification of the callee. *)
  (** Nonheap callers supply [None] bits using [saved_registers_shadow_empty].
      Return-time bits are existentially quantified: heap entries may change
      during the call. For nonheap saved words, [saved_registers_shadow_nonheap]
      recovers [None] for each returned bit, so restoration preserves the words.
   **)
  Lemma switcher_cc_specification_known_to_known_end_to_end
    (Nswitcher : namespace)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK)
    (nargs : nat)
    (E : coPset)
    (Nexp_tbl : namespace)
    (btbl_tgt atbl_tgt etbl_tgt : Addr)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z)
    (P : iProp Σ) (Q : Word -> Word -> iProp Σ)
    (scgp scra scs0 scs1 : option bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller :=
      WSealed ot_switcher (SCap true RO Global btbl_tgt etbl_tgt atbl_tgt) in
    disjoint_from_heap b_stk e_stk ->
    disjoint_from_shadow b_stk e_stk ->
    is_shadow_address atbl_tgt = false ->
    is_shadow_address btbl_tgt = false ->
    is_shadow_address (btbl_tgt ^+ 1)%a = false ->
    is_heap_address bpcc_tgt = false ->
    is_heap_address bcgp_tgt = false ->
    ↑Nswitcher ⊆ E ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    (btbl_tgt < (btbl_tgt ^+ 1))%a ->
    ((btbl_tgt ^+ 1) < atbl_tgt)%a ->
    (0 <= nargs <= 7)%nat ->
    is_Some (bpcc_tgt + off_tgt)%a ->
    dom rmap =
      all_registers_s ∖
        ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    na_inv cerise_nais Nswitcher switcher_inv
    ∗ inv (export_table_PCCN Nexp_tbl)
        (btbl_tgt ↦ₐ WCap true RX Global bpcc_tgt epcc_tgt bpcc_tgt)
    ∗ inv (export_table_CGPN Nexp_tbl)
        ((btbl_tgt ^+ 1)%a ↦ₐ WCap true RW Global bcgp_tgt ecgp_tgt bcgp_tgt)
    ∗ inv (export_table_entryN Nexp_tbl atbl_tgt)
        (atbl_tgt ↦ₐ WInt (encode_entry_point (Z.of_nat nargs) off_tgt))
    ∗ na_own cerise_nais E
    ∗ PC ↦ᵣ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    ∗ ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg)
    ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ cstack_frag cstk
    ∗ saved_registers_shadow wcgp_caller wcra_caller wcs0_caller wcs1_caller scgp scra scs0 scs1
    ∗ P
    ∗ switcher_cc_specification_known_to_known_function
        P Q wcgp_caller wcra_caller wcs0_caller wcs1_caller
        b_stk e_stk a_stk arg_rmap cstk nargs E
        bpcc_tgt epcc_tgt bcgp_tgt ecgp_tgt off_tgt scgp scra scs0 scs1
    ∗ ▷ (
        (∃ (scgp_ret scra_ret scs0_ret scs1_ret : option bool) (wca0 wca1 : Word) (rmap' : Reg),
           ⌜ dom rmap' =
                 all_registers_s ∖
                   {[ PC ; csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
           ∗ na_own cerise_nais E
           ∗ PC ↦ᵣ updatePcPerm (restore_saved_word scra_ret wcra_caller)
           ∗ cgp ↦ᵣ restore_saved_word scgp_ret wcgp_caller
           ∗ cra ↦ᵣ restore_saved_word scra_ret wcra_caller
           ∗ cs0 ↦ᵣ restore_saved_word scs0_ret wcs0_caller
           ∗ cs1 ↦ᵣ restore_saved_word scs1_ret wcs1_caller
           ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
           ∗ ca0 ↦ᵣ wca0
           ∗ ca1 ↦ᵣ wca1
           ∗ ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
           ∗ [[ a_stk , e_stk ]] ↦ₐ
               [[ region_addrs_zeroes a_stk e_stk ]]
           ∗ cstack_frag cstk
    ∗ saved_registers_shadow wcgp_caller wcra_caller wcs0_caller wcs1_caller scgp_ret scra_ret scs0_ret scs1_ret
           ∗ Q wca0 wca1)
        ∨
        (∃ (rmap' : Reg) (stk_mem' : list Word),
           ⌜ dom rmap' =
                 all_registers_s ∖
                   {[ PC ; cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
           ∗ na_own cerise_nais E
           ∗ PC ↦ᵣ updatePcPerm (restore_saved_word scra wcra_caller)
           ∗ cgp ↦ᵣ restore_saved_word scgp wcgp_caller
           ∗ cra ↦ᵣ restore_saved_word scra wcra_caller
           ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
           ∗ cs0 ↦ᵣ restore_saved_word scs0 wcs0_caller
           ∗ cs1 ↦ᵣ restore_saved_word scs1 wcs1_caller
           ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
           ∗ ca1 ↦ᵣ WInt 0
           ∗ ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
           ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem' ]]
           ∗ cstack_frag cstk
    ∗ saved_registers_shadow wcgp_caller wcra_caller wcs0_caller wcs1_caller scgp scra scs0 scs1
           ∗ P)
          -∗ WP Seq (Instr Executable)
                {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_stk4 wct1_caller.
    iIntros (Hstk_heap Hstk_shadow Hatbl_shadow Hbtbl_shadow Hbtbl1_shadow Hbpcc_nonheap Hbcgp_nonheap
             HE Hatbl Hbtbl0 Hbtbl1 Hnargs Hentry Hdom Harg_rmap)
      "(#Hswitcher & #Hinv_pcc & #Hinv_cgp & #Hinv_entry
       & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & Hcs0 & Hcs1
       & Hargs & Hregs & Hstk & Hcstk & Hshadow & HP & Hf & Hpost)".

    iApply (switcher_cc_specification_known_to_known
              Nswitcher wcgp_caller wcra_caller wcs0_caller wcs1_caller
              b_stk e_stk a_stk stk_mem arg_rmap rmap cstk nargs E
              Nexp_tbl btbl_tgt atbl_tgt etbl_tgt
              bpcc_tgt epcc_tgt bcgp_tgt ecgp_tgt off_tgt scgp scra scs0 scs1);
      try assumption.
    iFrame "Hswitcher Hinv_pcc Hinv_cgp Hinv_entry
            Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1
            Hargs Hregs Hstk Hcstk Hshadow".
    iNext.
    iIntros "[
      (%arg_rmap' & %rmap' & %Harg_rmap' & %Hrmap'
       & Hna & HPC & Hcgp & Hcra & Hcsp & Hargs & Hregs & Hstk & Hcstk & Hshadow)
      |
      (%rmap' & %stk_mem' & %Hrmap'
       & Hna & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hregs & Hstk & Hcstk & Hshadow)
      ]".
    - iAssert (
        ▷ (∀ (scgp_ret scra_ret scs0_ret scs1_ret : option bool) (wca0 wca1 : Word) (rmap_ret : Reg)
               (stk_mem_ret : list Word),
             ⌜ dom rmap_ret =
                   all_registers_s ∖
                     {[ PC ; csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
             ∗ na_own cerise_nais E
             ∗ PC ↦ᵣ WCap true XSRW_ Local
                         b_switcher e_switcher a_switcher_return
             ∗ cgp ↦ᵣ - ∗ cra ↦ᵣ - ∗ cs0 ↦ᵣ - ∗ cs1 ↦ᵣ -
             ∗ csp ↦ᵣ WCap true RWL Local a_stk4 e_stk a_stk4
             ∗ ca0 ↦ᵣ wca0
             ∗ ca1 ↦ᵣ wca1
             ∗ ([∗ map] r↦w ∈ rmap_ret, r ↦ᵣ w)
             ∗ [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem_ret ]]
             ∗ cstack_frag
                 ({| wret := wcra_caller;
                     wcgp := wcgp_caller;
                     wcs0 := wcs0_caller;
                     wcs1 := wcs1_caller;
                     b_stk := b_stk;
                     a_stk := a_stk;
                     e_stk := e_stk;
                     ccrel := Known_to_Known;
                     shadow_cgp := scgp;
                     shadow_cra := scra;
                     shadow_cs0 := scs0;
                     shadow_cs1 := scs1 |} :: cstk)
             ∗ saved_registers_shadow wcgp_caller wcra_caller wcs0_caller wcs1_caller scgp_ret scra_ret scs0_ret scs1_ret
             ∗ Q wca0 wca1
               -∗ WP Seq (Instr Executable)
                     {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}))%I
        with "[Hpost]" as "Hfpost".
      { iNext.
        iIntros (scgp_ret scra_ret scs0_ret scs1_ret wca0 wca1 rmap_ret stk_mem_ret)
          "(%Hrmap_ret & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1
           & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk & Hshadow & HQ)".
        iAssert (
          ▷ (∀ (rmap_final : Reg),
               ⌜ dom rmap_final =
                     all_registers_s ∖
                       {[ PC ; csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
               ∗ na_own cerise_nais E
               ∗ PC ↦ᵣ updatePcPerm (restore_saved_word scra_ret wcra_caller)
               ∗ cgp ↦ᵣ restore_saved_word scgp_ret wcgp_caller
               ∗ cra ↦ᵣ restore_saved_word scra_ret wcra_caller
               ∗ cs0 ↦ᵣ restore_saved_word scs0_ret wcs0_caller
               ∗ cs1 ↦ᵣ restore_saved_word scs1_ret wcs1_caller
               ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
               ∗ ca0 ↦ᵣ wca0
               ∗ ca1 ↦ᵣ wca1
               ∗ ([∗ map] r↦w ∈ rmap_final,
                    r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
               ∗ [[ a_stk , e_stk ]] ↦ₐ
                   [[ region_addrs_zeroes a_stk e_stk ]]
               ∗ cstack_frag cstk
    ∗ saved_registers_shadow wcgp_caller wcra_caller wcs0_caller wcs1_caller scgp_ret scra_ret scs0_ret scs1_ret
                 -∗ WP Seq (Instr Executable)
                       {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}))%I
          with "[HQ Hpost]" as "Hretpost".
        { iNext.
          iIntros (rmap_final)
            "(%Hrmap_final & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1
             & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk & Hshadow)".
          iApply "Hpost".
          iLeft.
          iExists scgp_ret, scra_ret, scs0_ret, scs1_ret, wca0, wca1, rmap_final.
          iFrame "∗#%".
        }
        iApply (switcher_cc_specification_return_known_to_known
                  Nswitcher wcgp_caller wcra_caller wcs0_caller wcs1_caller
                  wca0 wca1 b_stk e_stk a_stk stk_mem_ret rmap_ret cstk E scgp scra scs0 scs1 scgp_ret scra_ret scs0_ret scs1_ret
                  with
                  "[$Hswitcher $Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1
                    $Hcsp $Hca0 $Hca1 $Hregs $Hstk $Hcstk $Hshadow $Hretpost]").
        { exact Hstk_heap. }
        { exact Hstk_shadow. }
        { exact HE. }
        { exact Hrmap_ret. }
      }
      iApply ("Hf" $! arg_rmap' rmap').
      iFrame.
      iSplit; first done.
      iPureIntro. rewrite Hrmap' Hdom. set_solver.
    - iApply "Hpost".
      iRight.
      iExists rmap', stk_mem'.
      iFrame "∗#%".
  Qed.


End Switcher_KtK.
