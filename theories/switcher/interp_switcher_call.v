From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants bitblast.
From griotte Require Import interp_weakening.
From griotte Require Import wp_rules_interp switcher_macros_spec.
From griotte Require Import rules proofmode monotone.
From griotte Require Import fundamental.
From griotte Require Import switcher_preamble.
From griotte Require Import interp_switcher_return switcher_helpers.
From griotte Require Import switcher_call_states switcher_call_world
  switcher_call_blocks_1 switcher_call_blocks_2 switcher_call_blocks_3 switcher_call_blocks_4
  switcher_call_blocks_5 switcher_call_blocks_6.
From griotte Require Import map_simpl register_tactics proofmode.


Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  (** Failure path of [interp_expr_switcher_call]: the checks on the stack
      pointer fail, and the call is unwound by the return routine. *)
  Lemma interp_switcher_call_force_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : Reg) (wcsp : Word) (zct2 zctp : Z)
    (a_tstk : Addr) (tstk_next : list Word) :
    (∀ r, is_Some (regs !! r)) ->
    regs !! csp = Some wcsp ->
    frame_match Ws Cs cstk W C ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->
    (b_trusted_stack + length cstk')%a = Some a_tstk ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    na_inv cerise_nais Nswitcher switcher_inv ∗
    (∀ (r : RegName) (v : Word), ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v) ∗
    (▷ switcher_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) ∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_code ∗
    b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    cstack_full cstk' ∗
    cstack_interp cstk' a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ᵣ switcher_block_pc 17 ∗
    csp ↦ᵣ wcsp ∗
    ct2 ↦ᵣ WInt zct2 ∗
    ctp ↦ᵣ WInt zctp ∗
    ( [∗ map] k↦y ∈ delete ctp (delete ct2 (delete csp (delete PC regs))), k ↦ᵣ y ) ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    cstack_frag cstk
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: [switcher_call_block_17_spec] executes block 17,
       then close the switcher invariant and use the validity of the return
       routine ([interp_expr_switcher_return]). *)
    iIntros (Hfull_rmap Hstk Hframe Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Hot_bounds)
      "(#Hinv_switcher & #Hreg & Hclose_switcher_inv & Hna & Hmtdc & Htstk & Hcode & Hb_switcher
      & Hcstk_full & Hstk_interp & #Hp_ot_switcher & HPC & Hcsp & Hct2 & Hctp & Hrmap
      & Hworld_interp & Hcont & Hcstk)".
    specialize (Hfull_rmap ca0) as HH; destruct HH as [? ?].
    specialize (Hfull_rmap ca1) as HH; destruct HH as [? ?].
    iExtract "Hrmap" ca0 as "Hca0".
    iExtract "Hrmap" ca1 as "Hca1".
    iApply (switcher_call_block_17_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & Hcode)".
    iMod ("Hclose_switcher_inv" with
      "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hstk_interp]") as "HH".
    { iNext. iExists _,_. iFrame "∗ # %".
      iPureIntro; split; auto. }

    iInsertList "Hrmap" [csp;ctp;ct2;ca0;ca1;PC].
    iApply interp_expr_switcher_return; iFrame "∗%#".
    rewrite /interp_reg /=.
    iSplit.
    + rewrite /full_map.
      iIntros (r); iPureIntro.
      destruct (decide (r = ca1)); first by simplify_map_eq.
      destruct (decide (r = ca0)); first by simplify_map_eq.
      destruct (decide (r = ct2)); first by simplify_map_eq.
      destruct (decide (r = ctp)); first by simplify_map_eq.
      destruct (decide (r = csp)); first by simplify_map_eq.
      simplify_map_eq. apply Hfull_rmap.
    + iIntros (r w HrPC Hr).
      destruct (decide (r = ca1)); first (simplify_map_eq; iApply interp_int).
      destruct (decide (r = ca0)); first (simplify_map_eq; iApply interp_int).
      destruct (decide (r = ct2)); first (simplify_map_eq; iApply interp_int).
      destruct (decide (r = ctp)); first (simplify_map_eq; iApply interp_int).
      destruct (decide (r = csp)); simplify_map_eq; iApply "Hreg"; eauto.
  Qed.

  (** Failure path of [interp_expr_switcher_call]: the trusted stack is
      exhausted. *)
  Lemma interp_switcher_call_tstack_exhausted
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk cstk' : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : Reg) (b e a : Addr) (lv : list Word)
    (wcs0 wcs1 wcra wcgp wct1 wct2 wctp : Word)
    (a_tstk : Addr) (tstk_next : list Word) :
    dom rmap = all_registers_s ∖ {[ PC ; csp ; ct2 ; ctp ; cs0 ; cs1 ; cra ; cgp ; ct1 ]} ->
    frame_match Ws Cs cstk W C ->
    switcher_stk_bounds b e a ->
    length (finz.seq_between a e) = length lv ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->
    (b_trusted_stack + length cstk')%a = Some a_tstk ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    interp W C wcs0 ∗
    interp W C wcs1 ∗
    interp W C wcra ∗
    interp W C wcgp ∗
    interp W C (WCap RWL Local b e a) ∗
    ([∗ list] w ∈ lv, interp W C w) ∗
    (▷ switcher_inv ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) ∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) ∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack a_tstk ∗
    [[ (a_tstk ^+ 1)%a , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_code ∗
    b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    cstack_full cstk' ∗
    cstack_interp cstk' a_tstk ∗
    seal_pred ot_switcher ot_switcher_propC ∗
    PC ↦ᵣ switcher_block_pc 16 ∗
    (∃ w, cs0 ↦ᵣ w) ∗
    cs1 ↦ᵣ wcs1 ∗
    cgp ↦ᵣ wcgp ∗
    cra ↦ᵣ wcra ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    ct1 ↦ᵣ wct1 ∗
    csp ↦ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ drop 4 lv ]] ∗
    switcher_stk_opened W C a e lv ∗
    ( [∗ map] k↦y ∈ rmap, k ↦ᵣ y ) ∗
    interp_cont interp cstk Ws Cs ∗
    cstack_frag cstk
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: [switcher_call_blocks_5_spec] executes blocks 16
       and 14-15, [switcher_call_stk_close] closes the caller's stack frame,
       then close the switcher invariant and [switcher_jump_to_caller_spec]. *)
    iIntros (Hdom Hframe Hstk_bounds Hlen_lv Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Hot_bounds)
      "(#Hcs0v & #Hcs1v & #Hcrav & #Hcgpv & #Hspv & #Hlv & Hclose_switcher_inv & Hna & Hmtdc & Htstk
      & Hcode & Hb_switcher & Hcstk_full & Hstk_interp & #Hp_ot_switcher & HPC & Hcs0 & Hcs1 & Hcgp
      & Hcra & Hctp & Hct2 & Hct1 & Hcsp & Hcells & Hstk & Hstk_opened & Hrmap & Hcont & Hcstk)".
    pose proof Hstk_bounds as (_ & Hba3 & Ha4).
    assert (4 <= length lv) as Hlen_lv4.
    { rewrite -Hlen_lv finz_seq_between_length /finz.dist. solve_addr. }
    assert (is_Some (rmap !! ca0)) as [? ?] by (apply elem_of_dom; rewrite Hdom; set_solver-).
    assert (is_Some (rmap !! ca1)) as [? ?] by (apply elem_of_dom; rewrite Hdom; set_solver-).
    iExtract "Hrmap" ca0 as "Hca0".
    iExtract "Hrmap" ca1 as "Hca1".
    iInsertList "Hrmap" [ct1;ctp;ct2].
    iApply (switcher_call_blocks_5_spec with
      "[- $HPC $Hcsp $Hcells $Hrmap $Hcode $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1]"); first done.
    { repeat (rewrite dom_insert_L). repeat (rewrite dom_delete_L). rewrite Hdom. set_solver. }
    iNext; iIntros (rmap')
      "(%Hrmap' & HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp & Hcells & Hrmap & Hcode & Hlc)".

    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
    iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk [Hlv]")
      as "Hworld_interp".
    { cbn; rewrite length_drop; lia. }
    { rewrite -{1}(take_drop 4 lv) big_sepL_app.
      iDestruct "Hlv" as "[_ Hlv]". iFrame "#". }

    (* Close the switcher invariant *)
    iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hstk_interp]") as "HH".
    { iNext. iExists _,_. iFrame "∗ # %".
      iPureIntro; split; auto.
    }
    iDestruct "Hlc" as "[Hlc _]".
    iApply (switcher_jump_to_caller_spec with
             "Hcrav Hcgpv Hcs0v Hcs1v Hspv [] [] HPC Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
              Hrmap Hworld_interp Hcont Hcstk HH Hlc"); [done|done|iApply interp_int|iApply interp_int].
  Qed.

  Lemma interp_expr_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv
    ⊢ interp_expr interp (interp_cont interp) W C (WCap XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - [switcher_call_blocks_1_spec]: checks on the stack pointer;
         when they fail, [interp_switcher_call_force_unwind];
       - [switcher_call_stk_open]: open the caller's stack frame in the world
         (when the stack pointer is not a valid stack capability,
         [switcher_call_blocks_2_fail_spec]);
       - [switcher_call_blocks_2_spec]: spill the callee-save registers and
         push the stack pointer on the trusted stack;
       - when the trusted stack is exhausted:
         [interp_switcher_call_tstack_exhausted];
       - [switcher_entry_point_prop]: the entry point satisfies the sealing
         predicate of the switcher;
       - [switcher_call_blocks_3_spec]: clear the callee's stack frame and
         unseal the entry point;
       - [switcher_call_stk_close]: close the caller's stack frame;
       - [switcher_call_blocks_4_spec]: load the callee and jump to it;
       - [switcher_inv_push_frame]: close the switcher invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros "#Hinv_switcher %cstk %Ws %Cs %regs [[%Hfull_rmap #Hreg] (Hrmap & Hworld_interp & Hcont & Hna & Hcstk & %Hframe)]".
    rewrite /registers_pointsto.
    iPoseProof fundamental_ih as "IH". (* used for weakening lemma later *)

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    iExtract "Hrmap" PC as "HPC".
    specialize (Hfull_rmap csp) as HH;destruct HH as [wcsp Hstk].
    specialize (Hfull_rmap ct2) as HH;destruct HH as [? wct2].
    specialize (Hfull_rmap ctp) as HH;destruct HH as [? wctp].
    iExtract "Hrmap" csp as "Hcsp".
    iExtract "Hrmap" ct2 as "Hct2".
    iExtract "Hrmap" ctp as "Hctp".
    iDestruct ("Hreg" $! csp with "[//] [//]") as "#Hspv".

    (* Blocks 0-1: checks on the stack pointer *)
    iApply (switcher_call_blocks_1_spec with "[- $HPC $Hcsp $Hct2 $Hctp $Hcode]").
    iNext; iIntros "[(%Hchecked & HPC & Hcsp & Hct2 & Hctp & Hcode)
                    | (_ & %zct2 & %zctp & HPC & Hcsp & Hct2 & Hctp & Hcode)]";
      cycle 1.
    { (* The checks fail: force the unwinding of the call *)
      iApply (interp_switcher_call_force_unwind with
        "[$Hinv_switcher $Hreg $Hclose_switcher_inv $Hna $Hmtdc $Htstk $Hcode $Hb_switcher
          $Hcstk_full $Hstk_interp $Hp_ot_switcher $HPC $Hcsp $Hct2 $Hctp $Hrmap
          $Hworld_interp $Hcont $Hcstk]"); done.
    }

    specialize (Hfull_rmap cs0) as HH; destruct HH as [wcs0 Hwcs0].
    specialize (Hfull_rmap cs1) as HH; destruct HH as [wcs1 Hwcs1].
    specialize (Hfull_rmap cra) as HH; destruct HH as [wcra Hwcra].
    specialize (Hfull_rmap cgp) as HH; destruct HH as [wcgp Hwcgp].
    specialize (Hfull_rmap ct1) as HH; destruct HH as [wct1 Hwct1].
    iExtract "Hrmap" cs0 as "Hcs0".
    iExtract "Hrmap" cs1 as "Hcs1".
    iExtract "Hrmap" cra as "Hcra".
    iExtract "Hrmap" cgp as "Hcgp".
    iExtract "Hrmap" ct1 as "Hct1".
    iAssert (interp W C wcs0) as "#Hcs0v".
    { iApply "Hreg"; eauto; done. }
    iAssert (interp W C wcs1) as "#Hcs1v".
    { iApply "Hreg"; eauto; done. }
    iAssert (interp W C wcra) as "#Hcrav".
    { iApply "Hreg"; eauto; done. }
    iAssert (interp W C wcgp) as "#Hcgpv".
    { iApply "Hreg"; eauto; done. }
    iAssert (interp W C wct1) as "#Hct1v".
    { iApply "Hreg"; eauto; done. }

    (* Open the caller's stack frame *)
    assert ((∃ b e a, wcsp = WCap RWL Local b e a ∧ (b <= a)%a)
            ∨ (∀ b e a, wcsp = WCap RWL Local b e a → (a < b)%a))
      as [(b & e & a & -> & Hba) | Hnot_stk].
    { destruct wcsp as [| [p g b e a|] | |]; try (right; intros; discriminate).
      destruct (decide (p = RWL ∧ g = Local)) as [ [-> ->] | Hpg].
      - destruct (decide (b <= a)%a);
          [left; eauto | right; intros ??? Heq; inversion Heq; subst; solve_addr].
      - right; intros ??? Heq; inversion Heq; subst; tauto. }
    2: { iApply (switcher_call_blocks_2_fail_spec with "[$HPC $Hcsp $Hcs0 $Hcode]"); done. }
    iDestruct (switcher_call_stk_open with "Hspv Hworld_interp")
      as (lv) "(Hstk & Hstk_opened & #Hlv)"; first done.
    iDestruct (big_sepL2_length with "Hstk") as %Hlen_lv.

    (* Blocks 2-3: spill and push on the trusted stack *)
    iApply (switcher_call_blocks_2_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hctp $Hct2 $Hcsp $Hstk $Hmtdc $Htstk $Hcode]");
      [done|done|].
    iNext; iIntros "(%Hstk_bounds & Hcs1 & Hcra & Hcgp & Hcsp & Hcells & Hstk & Hcode & Hbranch)".
    pose proof Hstk_bounds as (_ & Hba3 & Ha4).
    assert (4 <= length lv) as Hlen_lv4.
    { rewrite -Hlen_lv finz_seq_between_length /finz.dist. solve_addr. }
    iDestruct "Hbranch" as
      "[(%Ha_tstk2 & %Ha_tstk1_bound & HPC & Hcs0 & Hctp & Hct2 & Hmtdc & Ha_tstk1 & Htstk & Hlc)
       | (HPC & Hcs0 & Hctp & Hct2 & Hmtdc & Htstk)]"; cycle 1.
    { (* The trusted stack is exhausted *)
      iApply (interp_switcher_call_tstack_exhausted W C Nswitcher cstk _ Ws Cs _ b e a lv
                wcs0 wcs1 wcra wcgp with
        "[$Hcs0v $Hcs1v $Hcrav $Hcgpv $Hspv $Hlv $Hclose_switcher_inv $Hna $Hmtdc $Htstk $Hcode
          $Hb_switcher $Hcstk_full $Hstk_interp $Hp_ot_switcher $HPC $Hcs0 $Hcs1 $Hcgp $Hcra
          $Hctp $Hct2 $Hct1 $Hcsp $Hcells $Hstk $Hstk_opened $Hrmap $Hcont $Hcstk]"); try done.
      repeat (rewrite dom_delete_L). clear -Hfull_rmap.
      apply regmap_full_dom in Hfull_rmap. rewrite Hfull_rmap. set_solver.
    }

    (* Blocks 4-7: clear the callee's stack frame and unseal the entry point *)
    iDestruct (switcher_entry_point_prop with "Hp_ot_switcher []") as "Hentry_prop".
    { case_match; [iExact "Hct1v"|done]. }
    iApply (switcher_call_blocks_3_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcsp $Hstk $Hb_switcher $Hct1 $Hcode]"); first done.
    iNext; iIntros (wsb) "(-> & HPC & Hcs0 & [%wcs1' Hcs1] & Hcsp & Hstk & Hb_switcher & Hct1 & Hcode)".

    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
    iDestruct (switcher_call_stk_close _ _ _ _ lv with "Hstk_opened Hstk []")
      as "Hworld_interp".
    { cbn; rewrite /region_addrs_zeroes length_replicate -Hlen_lv !finz_seq_between_length /finz.dist.
      solve_addr. }
    { iFrame "#". iApply big_sepL_forall. iIntros (k w Hk).
      apply lookup_replicate in Hk as [-> _]. iApply interp_int. }

    iDestruct ("Hentry_prop" with "[//]")
      as (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs off Nexp_tbl Heq Htbl Hbtbl Hbtbl1 Hnargs)
           "(Htbl1 & Htbl2 & Htbl3 & #Hentry & #Hexec)".
    simplify_eq.
    iSpecialize ("Hexec" $! W with "[]").
    { iPureIntro. apply related_sts_priv_refl_world. }

    (* Blocks 7-11: load the callee and jump to it *)
    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↦ᵣ y)%I ] => set (rmap' := r) end.
    set (params := dom_arg_rmap 8).
    set (Pf := ((λ '(r,_), r ∈ params) : RegName * Word → Prop)).
    rewrite -(map_filter_union_complement Pf rmap').
    iDestruct (big_sepM_union with "Hrmap") as "[Hparams Hrest]".
    { apply map_disjoint_filter_complement. }
    iAssert ([∗ map] r↦w ∈ filter Pf rmap',
               r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True)%I
      with "[Hparams]" as "Hparams".
    { iApply big_sepM_sep. iFrame. iApply big_sepM_forall.
      { intros k v.
        destruct (decide ( (k ∈ dom_arg_rmap nargs) )); tc_solve.
      }
      iIntros (k v [Hin Hspec]%map_lookup_filter_Some).
      destruct ( decide (k ∈ dom_arg_rmap nargs) ); last done.
      iApply ("Hreg" $! k);iPureIntro; first set_solver+Hspec.
      repeat (apply lookup_delete_Some in Hin as [_ Hin]); auto.
    }
    iApply (switcher_call_blocks_4_spec W C with
      "[- $Htbl1 $Htbl2 $Htbl3 $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcgp $Hcra $Hparams $Hrest $Hcode]");
      [done|done|lia| | |].
    { rewrite /is_arg_rmap /dom_arg_rmap.
      apply dom_filter_L. clear -Hfull_rmap.
      rewrite /rmap'. split.
      - intros Hi.
        repeat (rewrite lookup_delete_ne;[|set_solver]).
        specialize (Hfull_rmap i) as [x Hx].
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    { clear -Hfull_rmap. apply regmap_full_dom in Hfull_rmap as Heq'.
      rewrite /rmap' !map_filter_delete !dom_delete_L.
      cut (dom (filter (λ v, ¬ Pf v) regs) = all_registers_s ∖ dom_arg_rmap 8);[set_solver|].
      apply (dom_filter_L _ (regs : gmap RegName Word)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_rmap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }
    iNext; iIntros (arg_rmap' rmap'')
      "(%Harg_rmap' & %Hrmap'' & HPC & Hcgp & Hcra & Hargs & Hregs & Hcode)".

    (* Push the frame and close the switcher invariant *)
    set (frame :=
           {| wret := WInt 0;
              wcgp := WInt 0;
              wcs0 := WInt 0;
              wcs1 := WInt 0;
              b_stk := b ;
              a_stk := a ;
              e_stk := e ;
              ccrel := Unknown_to_Unknown
           |}).
    iMod (switcher_inv_push_frame frame cstk with
           "Hcstk_full Hcstk Hmtdc Ha_tstk1 Htstk Hstk_interp [] Hcode Hb_switcher Hp_ot_switcher")
      as "[Hinv Hcstk]"; [done|done|done|done|done|done| |].
    { by rewrite /cframe_stk_own /=. }
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hna]") as "Hna".

    (* Execute the entry point of the callee *)
    iAssert (interp W C (WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a)) as "#Hstk4v".
    { iApply (interp_weakening with "IH Hspv"); auto; solve_addr. }
    iDestruct (switcher_call_entry_registers W W C nargs arg_rmap' rmap'' with
                "[$HPC $Hcgp $Hcra $Hcsp $Hstk4v $Hargs $Hregs]")
      as (regs') "[Hregs Hregs_interp]"; [apply related_sts_pub_refl_world|done|done|].
    iApply ("Hexec" $! (frame :: cstk) (W :: Ws) (C :: Cs) regs' a e).
    iSplitL "Hcont".
    { iFrame. simpl.
      iSplit.
      - iApply (interp_weakening with "IH Hspv");auto;solve_addr.
      - iIntros (W' HW' ?????) "(HPC & _)".
        rewrite /interp_conf.
        wp_instr.
        iApply (wp_notCorrectPC with "[$]").
        { intros Hcontr;inversion Hcontr. }
        iIntros "!> HPC". wp_pure. wp_end. iIntros (Hcontr);done. }
    iSplit.
    { iPureIntro. simpl. split;auto. apply related_sts_pub_refl_world. }
    iFrame "Hregs Hregs_interp Hworld_interp Hcstk Hna".
    iPureIntro; split; [split; reflexivity | solve_addr].
  Qed.

  Lemma interp_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /=.
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_call with "Hinv").
  Qed.

End fundamental.
