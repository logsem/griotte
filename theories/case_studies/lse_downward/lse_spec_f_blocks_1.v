From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import lse_spec_states.

(** * LSE [f], block 4: push the capability of [a], load [a]

    Block 4 restricts [cgp] to the capability of [a] (at [cgp_b]), stores
    it in the top cell of the stack frame, below the cursor, loads [a] in
    [ct0] and [2] in [ct1]. The stack frame holds the pushed capability.
    The store keeps MSHWM at or below its value. *)

Section LSE_F_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma lse_f_blocks_1_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (cgp_b cgp_e : Addr) (csp_b csp_e : Addr) (stk_mem : list LWord)
    (wct0 wct1 wcs0 wcs1 : LWord) (cstk : CSTK) (mshwm_v : Z) :
    lse_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    disjoint_from_mmio csp_b csp_e ->
    (* The stack frame holds the pushed capability, below the space reserved
       at the top of the stack *)
    (csp_b + 1 + StackEntry_reserved_space <= csp_e)%Z ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ lse_label_offset ".Llse_f")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    cgp_b ↦ₐ WInt 2 ∗
    stack_region csp_b csp_e stk_mem ∗
    hwm_res cstk mshwm_v ∗
    codefrag_pers pc_a lse_main_code ∗
    ▷ (∀ stk_mem' wcs0' wcs1' (mshwm_v' : Z),
        PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ lse_label_offset ".Llse_f_assert")%a ∗
        cgp ↦ᵣ[th] lse_a_cap cgp_b ∗
        csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
        ct0 ↦ᵣ[th] WInt 2 ∗
        ct1 ↦ᵣ[th] WInt 2 ∗
        cs0 ↦ᵣ[th] wcs0' ∗
        cs1 ↦ᵣ[th] wcs1' ∗
        cgp_b ↦ₐ WInt 2 ∗
        stack_region csp_b csp_e stk_mem' ∗
        hwm_res cstk mshwm_v' ∗
        ⌜(mshwm_v' <= mshwm_v)%Z⌝ ∗
        codefrag_pers pc_a lse_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hcgp_bounds Hcgp_shadow Hcgp_nonheap Hstk_mmio Hcsp_size)
      "(HPC & Hcgp & Hcsp & Hct0 & Hct1 & Hcs0 & Hcs1
      & Hcgp_b & Hstk & Hhwm & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    lse_unfold_code.
    rewrite /lse_a_cap.

    (* Block 4: push the capability of [a], load [a] *)
    focus_block (lse_block ".Llse_f") "Hcode_main" of lse_main_blocks at pc_a as a_f Ha_f "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* GetB cs0 cgp *)
    iInstr "Hcode".
    (* Add cs1 cs0 1 *)
    iInstr "Hcode".
    (* Subseg cgp cgp cs0 cs1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1%nat)); [solve_addr+Hcgp_bounds|reflexivity]. }
    { solve_addr+Hcgp_bounds. }
    { solve_addr+Hcgp_bounds. }
    unfold StackEntry_reserved_space in Hcsp_size.
    assert ((stk_start_a csp_b csp_e + 2)%a = Some csp_e) as Hstart
      by (unfold stk_start_a, StackEntry_reserved_space; solve_addr+Hcsp_size).
    remember (stk_start_a csp_b csp_e) as a_start eqn:Ha_start.
    assert (csp_b < a_start)%a as Hcsp_lt by solve_addr+Hcsp_size Hstart.
    (* The cell below the cursor *)
    rewrite (stack_region_split csp_b (a_start ^+ -1) csp_e); [|solve_addr+Hcsp_lt Hstart..].
    iDestruct "Hstk" as "[Hstk Htop]".
    destruct (drop (finz.dist csp_b (a_start ^+ -1)) stk_mem) as [|w_top ws_top].
    { iDestruct (stack_region_length with "Htop") as %Hlen.
      exfalso. rewrite finz_seq_between_length /finz.dist /= in Hlen. solve_addr. }
    rewrite (stack_region_cons (a_start ^+ -1) a_start csp_e); [|solve_addr+Hcsp_lt Hstart..].
    iDestruct "Htop" as "[Ha_stk Htop]".
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hord) #Hts]".
    iAssert (hwm_regs (cstk_hwm_base cstk) mshwm_v) with "[$Hmshwmb $Hmshwm]" as "Hregs".
    iPoseProof deref_res_none as "Hderef".
    assert ((a_start + -1)%a = Some (a_start ^+ -1)) as Hcsp_top
      by solve_addr+Hcsp_lt.
    (* Store csp cgp (-1) *)
    iInstrApply "Hcode" wp_store_stack_cell_reg_imm
      with "[$HPC $Hcgp $Hcsp $Ha_stk $Hregs $Hderef]"
      as (mshwm_v1) "(%Hh1 & HPC & Hcgp & Hcsp & Ha_stk & [Hmshwmb Hmshwm] & _)".
    { solve_not_shadow Hstk_mmio. }
    { rewrite /withinBounds; solve_addr+Hcsp_size Hstart. }
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode".
    { solve_addr+Hcgp_bounds. }
    (* Mov ct1 2 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    (* The stack, with the pushed capability *)
    iDestruct (stack_cell_of_pointsto with "Ha_stk") as "Ha_stk".
    iDestruct (stack_region_join_cell with "Hstk Ha_stk Htop") as "Hstk";
      [solve_addr+Hcsp_lt Hstart..|].
    (* MSHWM does not grow, and stays at or above MSHWMB *)
    assert (mshwm_v1 <= mshwm_v)%Z as Hh1_le.
    { destruct Hh1 as [-> | ->]; first lia.
      destruct (hwm_after_cases (a_start ^+ -1) (cstk_hwm_base cstk) mshwm_v)
        as [-> | [-> ?] ]; lia. }
    assert (cstk_hwm_base cstk <= mshwm_v1)%Z as Hbh1.
    { destruct Hh1 as [-> | ->]; first done.
      destruct (hwm_after_cases (a_start ^+ -1) (cstk_hwm_base cstk) mshwm_v)
        as [-> | [-> ?] ]; lia. }
    iAssert (hwm_res cstk mshwm_v1) with "[Hmshwmb Hmshwm]" as "Hhwm".
    { rewrite /hwm_res /hwm_res_at. iFrame "Hmshwmb Hmshwm Hts". done. }
    assert (a_f ^+ 6 = (pc_a ^+ lse_label_offset ".Llse_f_assert")%a) as ->
      by (offsets_compute; solve_addr).
    subst a_start.
    iApply "Hpost"; iFrame "∗ Hcode_main". by iPureIntro.
  Qed.

End LSE_F_Blocks_1.
