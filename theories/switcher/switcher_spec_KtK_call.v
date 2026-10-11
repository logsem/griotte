From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import switcher_macros_spec.
From griotte Require Import switcher_call_states switcher_call_world
  switcher_call_blocks_1 switcher_call_blocks_2 switcher_call_blocks_3
  switcher_call_blocks_4 switcher_call_blocks_5.
From griotte Require Import map_simpl register_tactics proofmode.

(** * Call routine of the switcher, known-to-known calls

    The proof composes the block-group lemmas of [switcher_call_blocks_n],
    shared with [switcher_cc_specification_gen]. The caller and the callee
    are both known: the entry point is the sealed capability of a known
    export table, and the arguments are not required to be valid. *)

Section Switcher_KtK_Call.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  (** Failure path of [switcher_cc_specification_known_to_known]: the
      trusted stack is exhausted. *)
  Lemma switcher_cc_spec_tstack_exhausted_known_to_known
    (Nswitcher : namespace) (E : coPset)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller wct2 wctp : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk cstk' : CSTK)
    (a_tstk : Addr) (tstk_next : list LWord) :
    disjoint_from_mmio b_stk e_stk ->
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    switcher_stk_bounds b_stk e_stk a_stk ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->
    (b_trusted_stack + length cstk')%a = Some a_tstk ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    (▷ switcher_inv ∗ na_own cerise_nais (E ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais E) ∗
    na_own cerise_nais (E ∖ ↑Nswitcher) ∗
    mtdc ↦ₛᵣ WCap true RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_code ∗
    b_switcher ↦ₐ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    cstack_full cstk' ∗
    cstack_interp cstk' a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ᵣ switcher_block_pc 16 ∗
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
    ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ) ∗
    ( [∗ map] r↦w ∈ delete ctp (delete ct2 rmap), r ↦ᵣ w ) ∗
    cstack_frag cstk ∗
    ▷ ( ( ∃ rmap' stk_mem' rcgp rcra rcs0 rcs1,
            ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
            na_own cerise_nais E ∗
            PC ↦ᵣ lupdatePcPerm rcra ∗
            cgp ↦ᵣ rcgp ∗
            cra ↦ᵣ rcra ∗
            csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
            cs0 ↦ᵣ rcs0 ∗
            cs1 ↦ᵣ rcs1 ∗
            ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK ∗
            ca1 ↦ᵣ WInt 0 ∗
            ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
            [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem' ]] ∗
            cstack_frag cstk ∗
            ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
              load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝ )
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: [switcher_cc_exhausted_regs] collects the
       registers, [switcher_call_blocks_5_spec] executes blocks 16 and 14-15,
       then close the switcher invariant. *)
    iIntros (Hstk_mmio Hdom Hrdom Hstk_bounds Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Hot_bounds)
      "(Hclose_switcher_inv & Hna & Hmtdc & Htstk & Hcode & Hb_switcher & Hcstk_full & Hstk_interp
      & #Hp_ot_switcher & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hctp & Hct2 & Hct1 & Hcsp & Hcells & Hstk
      & Hargs & Hregs & Hcstk & Hpost)".
    pose proof Hstk_bounds as (Hastk_bstk & Hastk_bounds & Hastk).
    iDestruct (switcher_cc_exhausted_regs with "Hargs Hregs Hct1 Hct2 Hctp")
      as (wca0 wca1 rmap0) "(Hca0 & Hca1 & %Hrmap0 & Hrmap0)"; [done|done|].
    iApply (switcher_call_blocks_5_spec with
      "[- $HPC $Hcsp $Hcells $Hrmap0 $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1]");
      [done|done|done|].
    iNext; iIntros (rmap' rcgp rcra rcs0 rcs1)
      "(%Hrestored & %Hrmap' & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp & Hcells & Hrmap & Hcode & _)".
    iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hstk_interp]") as "Hna".
    { iNext. iExists _,_. iFrame "∗ # %".
      iPureIntro; split; auto.
    }
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
    iApply "Hpost"; iFrame.
    iPureIntro; split; last done. rewrite Hrmap'; set_solver.
  Qed.

  Lemma switcher_cc_specification_known_to_known
    (Nswitcher : namespace)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK)
    (nargs : nat)
    (E : coPset)

    (Nexp_tbl : namespace)
    (btbl_tgt atbl_tgt etbl_tgt : Addr)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z)

    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher (SCap true RO Global btbl_tgt etbl_tgt atbl_tgt) in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    let frame :=
           {| wret := wcra_caller;
              wcgp := wcgp_caller;
              wcs0 := wcs0_caller;
              wcs1 := wcs1_caller;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Known
           |}
    in

    disjoint_from_mmio b_stk e_stk ->
    is_shadow_address atbl_tgt = false ->
    is_shadow_address btbl_tgt = false ->
    is_shadow_address (btbl_tgt ^+ 1)%a = false ->
    is_heap_address bpcc_tgt = false ->
    is_heap_address bcgp_tgt = false ->

    (* (* NA mask *) *)
    disjoint_from_heap b_stk e_stk ->
    ↑Nswitcher ⊆ E ->

    (* Well formed entry point *)
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a →
    (btbl_tgt < (btbl_tgt ^+1))%a →
    ((btbl_tgt ^+1) < atbl_tgt)%a  →
    (0 <= nargs <= 7 )%nat →
    is_Some (bpcc_tgt + off_tgt)%a →

    (* Well formed register map *)
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv

    (* Entry Point Invariant *)
    ∗ inv (export_table_PCCN Nexp_tbl)             ( btbl_tgt ↦ₐ WCap true RX Global bpcc_tgt epcc_tgt bpcc_tgt)
    ∗ inv (export_table_CGPN Nexp_tbl)             ( (btbl_tgt ^+ 1)%a ↦ₐ WCap true RW Global bcgp_tgt ecgp_tgt bcgp_tgt)
    ∗ inv (export_table_entryN Nexp_tbl atbl_tgt) ( atbl_tgt ↦ₐ WInt (encode_entry_point (Z.of_nat nargs) off_tgt))


    (* PRE-CONDITION *)
    ∗ na_own cerise_nais E
    (* Registers *)
    ∗ PC ↦ᵣ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* All the other registers *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg )
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ cstack_frag cstk


    ∗ ▷ ( (∃ arg_rmap' rmap',
              ⌜ is_arg_rmap arg_rmap' 8 ⌝
              ∗ ⌜ dom rmap' = dom rmap ∪ {[ ct1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais E
              (* Registers *)
              ∗ PC ↦ᵣ WCap true RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a
              ∗ cgp ↦ᵣ WCap true RW Global bcgp_tgt ecgp_tgt bcgp_tgt
              ∗ cra ↦ᵣ (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
              (* Stack register *)
              ∗ csp ↦ᵣ WCap true RWL Local a_stk4 e_stk a_stk4
              (* All the other registers *)
              (* Entry point of the target compartment *)
              ∗ ( [∗ map] rarg↦warg ∈ arg_rmap', rarg ↦ᵣ warg
                                                 ∗ (if decide (rarg ∈ dom_arg_rmap nargs)
                                                    then ⌜ arg_rmap !! rarg = Some warg ⌝
                                                    else ⌜warg = WInt 0⌝)
                )
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )

              (* Stack frame *)
              ∗ ([[ a_stk4 , e_stk ]] ↦ₐ [[region_addrs_zeroes a_stk4 e_stk]])

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ cstack_frag (frame::cstk)
          )
          ∨
            (
              ∃ rmap' stk_mem' rcgp rcra rcs0 rcs1,
                ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
                ∗ na_own cerise_nais E
                (* Registers *)
                ∗ PC ↦ᵣ lupdatePcPerm (rcra)
                ∗ cgp ↦ᵣ rcgp
                ∗ cra ↦ᵣ rcra
                ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
                ∗ cs0 ↦ᵣ rcs0
                ∗ cs1 ↦ᵣ rcs1
                ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
                ∗ ca1 ↦ᵣ WInt 0
                (* All the other registers *)
                ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )

                (* Stack frame *)
                ∗ [[ a_stk , e_stk ]] ↦ₐ [[stk_mem']]

                (* Interpretation of the world and stack, at the moment of the switcher_call *)
                ∗ cstack_frag cstk
                ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                    load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
            )
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - [switcher_call_blocks_1_spec]: the checks on the stack pointer
         succeed;
       - [switcher_call_blocks_2_spec]: spill the callee-save registers and
         push the stack pointer on the trusted stack;
       - when the trusted stack is exhausted:
         [switcher_cc_spec_tstack_exhausted_known_to_known];
       - [switcher_call_blocks_3_spec]: clear the callee's stack frame and
         unseal the entry point;
       - [switcher_call_blocks_4_known_spec]: load the callee and jump to it;
       - [switcher_inv_push_frame]: push the frame and close the switcher
         invariant. *)
    intros astk4 wct1_caller callee_stk_region frame.
    iIntros (Hstk_mmio Hatbl_shadow Hbtbl_shadow Hbtbl1_shadow Hbpcc_heap Hbcgp_heap Hstk_heap
             HE atbl_tgt_inbounds btbl_tgt0 btbl_tgt1 Hnargs Hentry Hdom Harg_rmap)
      "(#Hswitcher & #Hinv_exp_tbl_pcc & #Hinv_exp_tbl_cgp & #Hinv_exp_tbl_entry
        & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hcstk & Hpost)".

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
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    (* Blocks 0-1: checks on the stack pointer *)
    iApply (switcher_call_blocks_1_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
    iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp & Hcode) | (%Hcontra & _)]";
      last (exfalso; apply Hcontra, switcher_csp_checked_stk).

    (* Blocks 2-3: spill and push on the trusted stack *)
    iApply (switcher_call_blocks_2_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hctp $Hct2 $Hcsp $Hstk $Hmtdc $Htstk $Hcode]");
      [done|done|done|].
    iNext; iIntros "(%Hstk_bounds & Hcs1 & Hcra & Hcgp & Hcsp & Hcells & Hstk & Hcode & Hbranch)".
    iDestruct "Hbranch" as
      "[(%Ha_tstk2 & %Ha_tstk1_bound & HPC & Hcs0 & Hctp & Hct2 & Hmtdc & Ha_tstk1 & Htstk & _)
       | (HPC & Hcs0 & Hctp & Hct2 & Hmtdc & Htstk)]"; cycle 1.
    { (* The trusted stack is exhausted *)
      iApply (switcher_cc_spec_tstack_exhausted_known_to_known with
        "[$Hclose_switcher_inv $Hna $Hmtdc $Htstk $Hcode $Hb_switcher $Hcstk_full $Hstk_interp
          $Hp_ot_switcher $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hctp $Hct2 $Hct1 $Hcsp $Hcells $Hstk
          $Hargs $Hregs $Hcstk Hpost]"); [done..|].
      iNext; iIntros "H"; iApply "Hpost"; iRight; iExact "H".
    }

    (* Blocks 4-7: clear the callee's stack frame and unseal the entry point *)
    iApply (switcher_call_blocks_3_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcsp $Hstk $Hb_switcher $Hct1 $Hcode]"); [done|done|done|].
    iNext; iIntros (wsb π) "(%Hwsb & _ & HPC & Hcs0 & [%wcs1' Hcs1] & Hcsp & Hstk & Hb_switcher & Hct1 & Hcode)".
    subst wct1_caller; rewrite /lword_of_word in Hwsb; simplify_eq.

    (* Blocks 7-11: load the callee and jump to it *)
    iApply (switcher_call_blocks_4_known_spec with
      "[- $Hinv_exp_tbl_pcc $Hinv_exp_tbl_cgp $Hinv_exp_tbl_entry $HPC $Hcs0 $Hcs1 $Hct1
        $Hct2 $Hctp $Hcgp $Hcra $Hargs $Hregs $Hcode]");
      [done|done|done|lia|done|done|done|done| |done| |].
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hbcgp_heap /=.
      reflexivity. }
    { rewrite !dom_delete_L Hdom. set_solver. }
    iNext; iIntros (arg_rmap' rmap')
      "(%Harg_rmap' & %Hrmap' & HPC & Hcgp & Hcra & Hargs & Hregs & Hcode)".

    (* Push the frame and close the switcher invariant *)
    iMod (switcher_inv_push_frame frame cstk with
           "Hcstk_full Hcstk Hmtdc Ha_tstk1 Htstk Hstk_interp [Hcells] Hcode Hb_switcher Hp_ot_switcher")
      as "[Hinv Hcstk]"; [done|done|done|done|done|exact Hstk_bounds|done|done| |].
    { rewrite /cframe_stk_own /=. iDestruct "Hcells" as "($&$&$&$)". }
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".
    iApply "Hpost"; iLeft; iFrame "∗ %".
    iPureIntro; rewrite Hrmap' Hdom; set_solver.
  Qed.

End Switcher_KtK_Call.
