From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine Require Import logrel fundamental interp_weakening addr_reg_sample rules proofmode monotone.
From cap_machine Require Import multiple_updates region_invariants_revocation region_invariants_allocation.
From cap_machine Require Import switcher switcher_preamble.
From stdpp Require Import base.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

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
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher w_entry_point in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap) ->
    is_arg_rmap arg_rmap ->

    (* Switcher Invariant *)
    na_inv logrel_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own logrel_nais ⊤
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller ∗ interp W C wct1_caller
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* Argument registers, need to be safe-to-share *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ sts_full_world W C
    ∗ region W C
    ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), rel C a RWL interpC ∗ ⌜ std W !! a = Some Revoked ⌝ )
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg),
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W (finz.seq_between a_stk4 e_stk) Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own logrel_nais ⊤
              (* Interpretation of the world *)
              ∗ sts_full_world W2 C
              ∗ open_region_many W2 C (finz.seq_between a_stk4 e_stk)
              ∗ ([∗ list] a ∈ (finz.seq_between a_stk4 e_stk), closing_resources interp W2 C a (WInt 0))
              ∗ cstack_frag cstk
              ∗ ([∗ list] a ∈ (finz.seq_between a_stk4 e_stk), rel C a RWL interpC ∗ ⌜ std W2 !! a = Some Temporary ⌝ )
              ∗ PC ↦ᵣ updatePcPerm wcra_caller
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller ∗ cs0 ↦ᵣ wcs0_caller ∗ cs1 ↦ᵣ  wcs1_caller
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ a_stk , e_stk ]] ↦ₐ [[ region_addrs_zeroes a_stk e_stk ]]
              ∗ interp_continuation cstk Ws Cs
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.

    iIntros (a_stk4 target Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hsts & Hr & #Hstk_val & Hcstk & Hcont & Hpost)".
    subst a_stk4.

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

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.


    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.
    destruct (decide (b_stk <= a_stk < e_stk)%a) as [Hastk_inbounds|Hastk_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs0 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk_inbounds.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    assert (is_Some (a_stk + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hastk_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk Hstk]"; eauto.
    { solve_addr+Hastk_inbounds Hastk1. }

    (* --- Store csp cs0 --- *)
    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".


    destruct (decide (b_stk <= (a_stk ^+ 1)%a < e_stk)%a) as [Hastk1_inbounds|Hastk1_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs1 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk1_inbounds.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2];[solve_addr+Hastk1 Hastk1_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk1 Hstk]"; eauto.
    { solve_addr+Hastk1_inbounds Hastk1 Hastk2. }

    (* --- Store csp cs1 --- *)
    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    destruct (decide (b_stk <= (a_stk ^+ 2)%a < e_stk)%a) as [Hastk2_inbounds|Hastk2_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcra $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk2_inbounds.
    destruct stk_mem as [|w2 stk_mem]; simplify_eq.
    assert (is_Some (a_stk2 + 1)%a) as [a_stk3 Hastk3];[solve_addr+Hastk1 Hastk2 Hastk2_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk2 Hstk]"; eauto.
    { solve_addr+Hastk2_inbounds Hastk1 Hastk2 Hastk3. }

    (* --- Store csp cra --- *)
    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".


    destruct (decide (b_stk <= (a_stk ^+ 3)%a < e_stk)%a) as [Hastk3_inbounds|Hastk3_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcgp $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk3_inbounds.
    destruct stk_mem as [|w3 stk_mem]; simplify_eq.
    assert (is_Some (a_stk3 + 1)%a) as [a_stk4 Hastk4];[solve_addr+Hastk1 Hastk2 Hastk3 Hastk3_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk3 Hstk]"; eauto.
    { solve_addr+Hastk3_inbounds Hastk1 Hastk2 Hastk3 Hastk4. }
    assert ((a_stk + 4)%a = Some a_stk4) as Hastk by solve_addr.
    assert ((a_stk ^+4)%a = a_stk4) as -> by solve_addr.
    (* --- Store csp cgp --- *)
    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    (* --- GetP ct2 csp --- *)
    iInstr "Hcode".

    (* ---  Mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    replace (encodePerm RWL - encodePerm RWL)%Z with 0%Z by lia.
    iInstr "Hcode".

    (* --- Jmp 2 --- *)
    iInstr "Hcode".

    (* --- GetL ct2 csp --- *)
    iInstr "Hcode".

    (* --- Mov ctp (encodeLoc Local) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    replace (encodeLoc Local - encodeLoc Local)%Z with 0%Z by lia.
    iInstr "Hcode".

    (* --- Jmp 2 --- *)
    iInstr "Hcode".

    (* --- ReadSR ct2 mtdc --- *)
    iInstr "Hcode".

    (* --- Lea ct2 1 --- *)
    destruct (a_tstk + 1)%a eqn:Htastk;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hct2]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- Store ct2 csp --- *)
    destruct (decide (f < e_trusted_stack)%a); cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcsp $Hct2]");try solve_pure.
      { rewrite /withinBounds. solve_addr+n Hastk. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }

    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    erewrite finz_incr_eq in Hlen;[|eauto].
    rewrite finz_seq_between_length in Hlen.
    destruct tstk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hlen;[|solve_addr].
      assert (e_trusted_stack = f) as Heq;[solve_addr|].
      subst. solve_addr. }
    assert (is_Some (f + 1)%a) as [f4 Hf4];[solve_addr|].
    iDestruct (region_pointsto_cons _ f4 with "Htstk") as "[Hf3 Htstk]";[solve_addr|solve_addr|].
    replace (a_tstk ^+ 1)%a with f by solve_addr.
    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- WriteSR mtdc ct2 --- *)
    iInstr "Hcode".

    (* --- GetE cs0 csp --- *)
    iInstr "Hcode".

    (* --- GetA cs1 csp --- *)
    iInstr "Hcode".

    (* --- Subseg csp cs1 cs0 --- *)
    iInstr "Hcode".
    { rewrite /isWithin. solve_addr. }

    (* --- clear stack --- *)
    rewrite /switcher_instrs /switcher_call_instrs -app_assoc -app_assoc.
    focus_block 1 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcls". iHide "Hcls" as hcont.
    iApply (clear_stack_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hstk]"); try solve_pure.
    { solve_addr+. }
    { solve_addr. }
    iSplitL;[|iIntros "!> %Hcontr"; done].
    iIntros "!> (HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 2 "Hcode" as a_rest Ha_rest "Hcode" "Hcls". iHide "Hcls" as hcont.

    (* --- GetB cs1 PC --- *)
    iInstr "Hcode".

    (* --- GetA cs0 PC --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cs1 cs0 --- *)
    iInstr "Hcode".

    (* --- Mov cs0 PC --- *)
    iInstr "Hcode".

    (* --- Lea cs0 cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]");[solve_pure..| |].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea cs0 -2 --- *)
    iInstr "Hcode".
    { instantiate (1:= b_switcher). solve_addr. }

    (* --- Load cs0 cs0 --- *)
    iInstr "Hcode".

    (* --- UnSeal ct1 cs0 ct1 --- *)
    subst target.
    rewrite (fixpoint_interp1_eq _ _ (WSealed ot_switcher w_entry_point)).
    iDestruct "Htarget_v" as (P HpersP) "(HmonoP & HPseal & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,WSealable w_entry_point)).
    iInstr "Hcode";[done|..].
    { rewrite /withinBounds. solve_addr. }
    rewrite /safeC.
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    iDestruct "HP" as (?????????? Heq????) "(Htbl1 & Htbl2 & Htbl3 & Hexec)". simpl fst. simpl snd.
    inversion Heq.

    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Htbl3" as ">Ha_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    (* --- GetB cgp ct1 --- *)
    iInstr "Hcode".

    (* --- GetA cs1 ct1 --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cgp cs1 --- *)
    iInstr "Hcode".

    (* --- Lea ct1 cs1 --- *)
    iInstr "Hcode".
    { instantiate (1:=b_tbl); solve_addr. }

    (* --- Load cra ct1 --- *)
    wp_instr.
    iInv "Htbl1" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea ct1 1 --- *)
    iInstr "Hcode".
    { instantiate (1:=(b_tbl ^+ 1)%a). solve_addr. }

    (* --- Load cgp ct1 --- *)
    wp_instr.
    iInv "Htbl2" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea cra cs0 --- *)
    destruct (bpcc + encode_entry_point nargs off ≫ 3)%a eqn:Hentry;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    (* clear registers except parameters *)
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite -!app_assoc.
    focus_block 3 "Hcode" as a_clear Ha_clear "Hcode" "Hcls". iHide "Hcls" as hcont.

    iApply (ftlr_switcher_call.clear_registers_pre_call_skip_spec with "[- $HPC $Hct2 $Hcode $Hargs]")
    ; try solve_pure.
    { rewrite encode_entry_point_eq_nargs;[lia|]. auto. }
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 4 "Hcode" as a_clear' Ha_clear' "Hcode" "Hcls". iHide "Hcls" as hcont.

    iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_insert.
    rewrite -delete_insert_ne; last done.
    iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_insert.
    iDestruct (big_sepM_insert_2 with "[Hcs1] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcs0] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs";[iFrame|].

    iApply (ftlr_switcher_call.clear_registers_pre_call_spec with "[- $HPC $Hcode $Hregs]"); try solve_pure.
    { rewrite !dom_insert_L Hdom. set_solver-. }

    iIntros "!> (%rmap' & %Hrmap' & HPC & Hregs & Hcode)".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    focus_block 5 "Hcode" as a_jalr Ha_halr "Hcode" "Hcls". iHide "Hcls" as hcont.

    set (frame :=
           {| wret := wcra_caller;
              wstk := (WCap RWL Local b_stk e_stk a_stk);
              wcgp := wcgp_caller;
              wcs0 := wcs0_caller;
              wcs1 := wcs1_caller;
              is_untrusted_caller := false
           |}).


    (* --- Close the world with the cleared stack --- *)

    rewrite {1}(finz_seq_between_split _ a_stk4);[|solve_addr].
    iDestruct (big_sepL_app with "Hstk_val") as "[_ Hstk_val']".
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen'.
    iDestruct (big_sepL2_const_sepL_l with "[$Hstk_val']") as "Hstk_val_f";[iPureIntro;apply Hstklen'|].
    iDestruct (big_sepL2_sep with "[Hstk_val' Hstk]") as "Hstk";[iSplitL;[iExact "Hstk"|iExact "Hstk_val_f"]|].
    iMod (update_region_revoked_temp_pwl_multiple with "Hsts Hr [Hstk]") as "[Hr Hsts]".
    5: {
      iApply (big_sepL2_impl with "Hstk"). iIntros "!>" (k a v Ha Hv) "(Ha & Hr & Hrev)".
      iFrame.
      apply region_addrs_zeroes_lookup in Hv as ->.
      iSplit;[iApply interp_int|]. iIntros "!>" (? ? ?) "_". iApply interp_int. }
    { apply _. }
    { auto. }
    { auto. }
    { apply finz_seq_between_NoDup. }

    iAssert (⌜Forall (λ k : finz MemNum, W.1 !! k = Some Revoked) (finz.seq_between a_stk4 e_stk)⌝)%I as %Hrev.
    { rewrite Forall_forall. iIntros (a Ha).
      iDestruct (big_sepL_elem_of with "Hstk_val'") as "[_ $]";apply Ha. }
    iSpecialize ("Hexec" $! _
                   (frame :: cstk)
                   ((std_update_multiple W (finz.seq_between a_stk4 e_stk) Temporary) :: Ws)
                   (C::Cs)
                   (std_update_multiple W (finz.seq_between a_stk4 e_stk) Temporary)
                  with "[]").
    { iPureIntro.
      apply related_sts_pub_priv_world.
      apply related_sts_pub_update_multiple_temp. auto. }
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite /load_word. iSimpl in "Hcgp".

    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq'. subst.
    iMod (cstack_update _ _ (frame :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hf3 Hstk_interp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3]") as "HH".
    { iNext. iExists f,tstk_next.
      iFrame "Hmtdc Hb_switcher Hp_ot_switcher".
      rewrite (finz_incr_eq Hf4). simpl.
      replace (f ^+ -1)%a with a_tstk by solve_addr+Htastk.
      iSplit;[auto|]. iFrame "Htstk Hstk_interp".
      iSplit;[iPureIntro;solve_addr|].
      iSplit;[iPureIntro;solve_addr|].
      iFrame.
      replace (a_stk ^+ 1)%a with a_stk1 by solve_addr+Hastk1.
      replace (a_stk ^+ 2)%a with a_stk2 by solve_addr+Hastk1 Hastk2.
      replace (a_stk ^+ 3)%a with a_stk3 by solve_addr+Hastk1 Hastk2 Hastk3.
      iFrame. iPureIntro.
      replace (a_stk ^+ 4)%a with a_stk4 by solve_addr+Hastk.
      rewrite Hastk. split;auto. split;[solve_addr|]. split;[solve_addr|eauto]. }

    iApply "Hexec".
    iAssert (interp (std_update_multiple W (finz.seq_between a_stk4 e_stk) Temporary) C (WCap RWL Local a_stk4 e_stk a_stk)) as "Hstk4v".
    { iApply fixpoint_interp1_eq. iSimpl. iApply (big_sepL_impl with "Hstk_val'").
      iIntros "!>" (k a Ha) "(Hr & _)".
      iExists RWL,interp. iFrame. simpl.
      iSplit;[iPureIntro;intros ?;apply _|].
      iSplit;[iApply zcond_interp|].
      iSplit;[iApply rcond_interp|].
      iSplit;[iApply wcond_interp|].
      iSplit;[iApply monoReq_interp|].
      + apply std_sta_update_multiple_lookup_in_i. apply elem_of_list_lookup. eauto.
      + intros Hcontr;done.
      + iPureIntro. apply std_sta_update_multiple_lookup_in_i. apply elem_of_list_lookup. eauto. }
    iSplitL "Hpost Hcont".
    { simpl. (* iDestruct (interp_monotone_continuation with "Hcont") as "Hcont". *)
      (* { apply related_sts_pub_update_multiple_temp. apply Hrev. } *)
      iFrame.
      iEval (cbn).
      replace (a_stk ^+ 4)%a with a_stk4 by solve_addr. iSplitR.
      { iNext. iFrame "Hstk4v". }
      iIntros "!>" (W' HW' ?????) "(HPC & Hcra & Hcsp & Hgp & Hcs0 & Hcs1 & Ha0 & #Hv
      & Hca1 & #Hv' & % & Hregs & % & % & Hstk & Hr & Hcls & Hsts & Hcont & Hcstk & Own)".
      iApply "Hpost". simplify_eq.
      replace (a_stk0 ^+ 4)%a with a_stk4 by solve_addr.
      iFrame. iFrame "# %".
      iApply (big_sepL_mono with "Hstk_val'").
      iIntros (?? Hin) "[Hrel %]". iFrame. iPureIntro.
      eapply region_state_pub_temp;[apply HW'|].
      apply std_sta_update_multiple_lookup_in_i.
      apply elem_of_list_lookup. eauto.
    }
    iSplitR.
    { iPureIntro. simpl. auto. }

    iFrame.
    rewrite /execute_entry_point_register.

    iDestruct (big_sepM_sep with "Hregs") as "[Hregs #Hnil]".
    iDestruct (big_sepM_sep with "Hargs") as "[Hargs #Hval]".
    iDestruct (big_sepM_union with "[$Hargs $Hregs]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap' Harg_rmap'.
      set_solver+. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HPC] Hregs") as "Hregs";[iFrame|].

    iFrame.
    iSplit.
    { iPureIntro. simpl. intros rr. clear -Harg_rmap' Hrmap'.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hrmap' Harg_rmap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver]. }

    iSplit;[|iSplit;[|iSplit;[|iSplit;[|iSplit] ] ] ].
    - clear-Hentry. iPureIntro. simplify_map_eq. repeat f_equiv.
      rewrite encode_entry_point_eq_off in Hentry. solve_addr.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iIntros (wstk Hwstk'). clear -Hwstk'. iClear "Hexec". simplify_map_eq.
      iApply fixpoint_interp1_eq. iApply (big_sepL_impl with "Hstk_val'").
      iIntros "!>" (k a Ha) "(Hr & _)".
      iExists RWL,interp. iFrame. simpl.
      iSplit;[iPureIntro;intros ?;apply _|].
      iSplit;[iApply zcond_interp|].
      iSplit;[iApply rcond_interp|].
      iSplit;[iApply wcond_interp|].
      iSplit;[iApply monoReq_interp|].
      + apply std_sta_update_multiple_lookup_in_i. apply elem_of_list_lookup. eauto.
      + intros Hcontr;done.
      + iPureIntro. apply std_sta_update_multiple_lookup_in_i. apply elem_of_list_lookup. eauto.
    - iIntros (wret Hwret). simplify_map_eq.
      iApply fixpoint_interp1_eq. iSimpl.
      assert (is_switcher_entry_point (WSentry XSRW_ Local b_switcher e_switcher (a_jalr ^+ 1)%a) = true) as ->;[|done].
      rewrite /is_switcher_entry_point.
      pose proof switcher_return_entry_point.
      rewrite bool_decide_true//.
      right.
      f_equal.
      solve_addr.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      rewrite lookup_union_l in Hv;cycle 1.
      { apply not_elem_of_dom. rewrite Hrmap'.
        apply not_elem_of_difference. right.
        apply elem_of_union. by left. }
      iDestruct (big_sepM_lookup with "Hval") as "Hv";[apply Hv|].
      iApply (interp_monotone with "[] Hv").
      iPureIntro.
      apply related_sts_pub_update_multiple_temp. auto.
    - iIntros (r Hnin).
      apply not_elem_of_union in Hnin as [Hnin1 Hnin2].
      assert (is_Some (rmap' !! r)) as [v Hin].
      { apply elem_of_dom. rewrite Hrmap'.
        apply elem_of_difference. split;[apply all_registers_s_correct|].
        apply not_elem_of_union. auto. }
      iDestruct (big_sepM_lookup with "Hnil") as %Hnil;[eauto|].
      iPureIntro.
      repeat (rewrite lookup_insert_ne;[|set_solver+Hnin1 Hnin2]).
      rewrite lookup_union_r;[subst;auto|].
      apply not_elem_of_dom. by rewrite Harg_rmap'.
  Qed.

End Switcher.
