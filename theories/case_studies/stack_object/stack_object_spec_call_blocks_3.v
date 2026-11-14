From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import stack_object_spec_states.

(** * Stack object, blocks 7-9: call to the callback [g]

    Block 7 pushes the secret on the stack and allocates the one-cell stack
    object [z] (in [ca1]) right below it. Block 8 fetches the entry point of
    the switcher in [ct0], and block 9 jumps to the switcher. The group ends
    at the entry point of the switcher, with the return address of the call
    in [cra]. The two stores keep MSHWM at or below its value. *)

Section SO_Call_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_call_blocks_3_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (csp_b csp_e : Addr) (stk_mem : list LWord)
    (wca1 wct0 wct1 wcs0 wcs1 wcra : LWord) (mie : InterruptStatus) (cstk : CSTK) (mshwm_v : Z) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    disjoint_from_shadow csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (* The stack frame holds the secret and [z], below the space reserved at
       the top of the stack *)
    (csp_b + 2 + StackEntry_reserved_space <= csp_e)%Z ->
    route_pre th mie ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_alloc")%a ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    cra ↦ᵣ[th] wcra ∗
    stack_region csp_b csp_e stk_mem ∗
    hwm_res cstk mshwm_v ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    codefrag_pers pc_a so_main_code ∗
    MIE ↦ₜ[th] mie ∗
    held (th := th) mie ∗
    ▷ (∀ a_stk1 a_stk2 stk_mem' stk_res (mshwm_v' : Z),
        ⌜(a_stk1 + (1 + StackEntry_reserved_space))%a = Some csp_e⌝ ∗
        ⌜(a_stk2 + 1)%a = Some a_stk1⌝ ∗
        ⌜(csp_b <= a_stk2)%a⌝ ∗
        PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        csp ↦ᵣ[th] Cap RWL Local csp_b csp_e a_stk2 ∗
        ca1 ↦ᵣ[th] Cap RWL Local a_stk2 a_stk1 a_stk2 ∗
        ct0 ↦ᵣ[th] switcher_entry_call ∗
        ct1 ↦ᵣ[th] wct1 ∗
        cs0 ↦ᵣ[th] wcra ∗
        cs1 ↦ᵣ[th] wct1 ∗
        cra ↦ᵣ[th] Sentry (ret_kind mie) RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_after_call")%a ∗
        stack_region (stk_start_a csp_b csp_e) csp_e stk_res ∗
        a_stk1 ↦ₐ WInt so_secret ∗
        a_stk2 ↦ₐ WInt 0 ∗
        stack_region csp_b a_stk2 stk_mem' ∗
        hwm_res cstk mshwm_v' ∗
        ⌜(mshwm_v' <= mshwm_v)%Z⌝ ∗
        pc_b ↦ₐ□ switcher_entry_call ∗
        codefrag_pers pc_a so_main_code ∗
        MIE ↦ₜ[th] InterruptDisabled ∗
        held (th := th) InterruptDisabled
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hstk_shadow Hstk_heap
      Hstk_size Hroute)
      "(HPC & Hcsp & Hca1 & Hct0 & Hct1 & Hcs0 & Hcs1 & Hcra & Hstk & Hhwm & Himport_switcher
      & Hcode_main & Hmie & Hheld & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.
    rewrite /switcher_entry_call.

    (* Block 7: push the secret and allocate the stack object [z] *)
    focus_block (so_block ".Lso_f_alloc") "Hcode_main" of so_main_blocks at pc_a as a_alloc Ha_alloc "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    assert ((stk_start_a csp_b csp_e + StackEntry_reserved_space)%a = Some csp_e) as Hstart
      by (unfold stk_start_a, StackEntry_reserved_space in Hstk_size |- *; solve_addr+Hstk_size).
    unfold StackEntry_reserved_space in Hstart, Hstk_size.
    remember (stk_start_a csp_b csp_e) as a_start eqn:Ha_start.
    assert (is_Some (a_start + -1)%a) as [a_stk1 Hastk1];
      [solve_addr+Hstk_size Hstart|].
    assert (is_Some (a_stk1 + -1)%a) as [a_stk2 Hastk2]; [solve_addr+Hstk_size Hstart Hastk1|].
    (* The cells of the frame: below [z], [z], the secret, and the two cells
       reserved at the top of the stack *)
    rewrite (stack_region_split csp_b a_stk2 csp_e);
      [|solve_addr+Hstk_size Hstart Hastk1 Hastk2..].
    iDestruct "Hstk" as "[Hstk Htop]".
    iDestruct (stack_region_length with "Htop") as %Hlen_top.
    destruct (drop (finz.dist csp_b a_stk2) stk_mem) as [|w1 [|w0 stk_res] ];
      [exfalso; rewrite finz_seq_between_length /finz.dist /= in Hlen_top;
       solve_addr+Hstk_size Hstart Hastk1 Hastk2 Hlen_top..|].
    rewrite (stack_region_cons a_stk2 a_stk1 csp_e);
      [|solve_addr+Hastk2|solve_addr+Hstk_size Hstart Hastk1 Hastk2].
    iDestruct "Htop" as "[Hastk2 Htop]".
    rewrite (stack_region_cons a_stk1 a_start csp_e);
      [|solve_addr+Hastk1|solve_addr+Hstk_size Hstart Hastk1].
    iDestruct "Htop" as "[Hastk1 Hres]".
    assert (is_heap_address a_stk2 = false) as Hastk2_nonheap.
    { eapply disjoint_from_heap_not_in; [exact Hstk_heap|].
      rewrite /withinBounds; solve_addr+Hstk_size Hstart Hastk1 Hastk2. }
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hord) #Hts]".
    iAssert (hwm_regs (cstk_hwm_base cstk) mshwm_v) with "[$Hmshwmb $Hmshwm]" as "Hregs".
    iPoseProof deref_res_none as "Hderef".
    (* Lea csp csp (-1) *)
    iInstr "Hcode".
    (* Store csp so_secret 0 *)
    iInstrApply "Hcode" (wp_store_stack_cell_z_imm_gen _ _ _ _ _ _ _ _ _ _ _ _
                           _ _ _ _ _ _ _ _ _ _ _ 1%Qp)
      with "[$HPC $Hcsp $Hastk1 $Hregs $Hderef]"
      as (mshwm_v1) "(%Hh1 & HPC & Hcsp & Hastk1 & Hregs & _)".
    { eapply disjoint_from_shadow_not_in; [exact Hstk_shadow|].
      rewrite /withinBounds; solve_addr+Hstk_size Hstart Hastk1. }
    { rewrite /withinBounds; solve_addr+Hstk_size Hstart Hastk1. }
    { solve_addr+Hastk1. }
    (* Lea csp csp (-1) *)
    iInstr "Hcode".
    (* Mov ca1 csp *)
    iInstr "Hcode".
    (* GetA cs0 ca1 *)
    iInstr "Hcode".
    (* Add cs1 cs0 1 *)
    iInstr "Hcode".
    (* Subseg ca1 ca1 cs0 cs1 *)
    iInstr "Hcode".
    { transitivity (Some a_stk1); auto. solve_addr+Hastk2. }
    { solve_addr+Hstk_size Hstart Hastk1 Hastk2. }
    { solve_addr+Hastk2. }
    iPoseProof deref_res_none as "Hderef2".
    (* Store ca1 0 0 *)
    iInstrApply "Hcode" (wp_store_stack_cell_z_imm_gen _ _ _ _ _ _ _ _ _ _ _ _
                           _ _ _ _ _ _ _ _ _ _ _ 1%Qp)
      with "[$HPC $Hca1 $Hastk2 $Hregs $Hderef2]"
      as (h2) "(%Hh2 & HPC & Hca1 & Hastk2 & [Hmshwmb Hmshwm] & _)".
    { eapply disjoint_from_shadow_not_in; [exact Hstk_shadow|].
      rewrite /withinBounds; solve_addr+Hstk_size Hstart Hastk1 Hastk2. }
    { rewrite /withinBounds; solve_addr+Hastk2. }
    { solve_addr+Hastk2. }
    (* MSHWM does not grow, and stays at or above MSHWMB *)
    assert (mshwm_v1 <= mshwm_v /\ cstk_hwm_base cstk <= mshwm_v1)%Z as [Hh1_le Hbh1].
    { destruct Hh1 as [-> | ->]; first lia.
      destruct (hwm_after_cases a_stk1 (cstk_hwm_base cstk) mshwm_v) as [-> | [-> ?] ]; lia. }
    assert (h2 <= mshwm_v1 /\ cstk_hwm_base cstk <= h2)%Z as [Hh2_le Hbh2].
    { destruct Hh2 as [-> | ->]; first lia.
      destruct (hwm_after_cases a_stk2 (cstk_hwm_base cstk) mshwm_v1) as [-> | [-> ?] ]; lia. }
    iAssert (hwm_res cstk h2) with "[Hmshwmb Hmshwm]" as "Hhwm".
    { rewrite /hwm_res /hwm_res_at. iFrame "Hmshwmb Hmshwm Hts". done. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 8: fetch the entry point of the switcher *)
    focus_block (so_block ".Lso_f_fetch_switcher") "Hcode_main" of so_main_blocks at pc_a as a_fetch Ha_fetch "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _
      switcher_entry_call
      with "[- $HPC $Hct0 $Hcode]"); eauto using switcher_call_sentry_not_heap; try done.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0) with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hct0 & _ & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 9: jump to the switcher *)
    focus_block (so_block ".Lso_f_call") "Hcode_main" of so_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Mov cs1 ct1 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert (a_call ^+ 3 = (pc_a ^+ so_label_offset ".Lso_f_after_call")%a) as ->
      by (offsets_compute; solve_addr).
    subst a_start.
    iApply ("Hpost" $! a_stk1 a_stk2 _ stk_res h2); iFrame "∗ Hcode_main".
    iPureIntro; repeat split; try lia; unfold StackEntry_reserved_space;
      solve_addr+Hstk_size Hstart Hastk1 Hastk2.
  Qed.

End SO_Call_Blocks_3.
