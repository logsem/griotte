From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import sts_multiple_updates.
From griotte Require Export logrel_binary region_invariants_binary bitblast.
From griotte Require Import interp_weakening_binary.
From griotte Require Import rules proofmode proofmode_binary monotone_binary.
From griotte Require Import memory_region memory_region_binary.
From griotte Require Import fundamental_binary.
From griotte Require Import switcher_preamble_binary.
From griotte Require Import interp_switcher_return_binary switcher_helpers_binary.
From griotte Require Import switcher_call_states_binary switcher_call_world_binary
  switcher_call_blocks_1_binary switcher_call_blocks_2_binary switcher_call_blocks_3_binary
  switcher_call_blocks_4_binary switcher_call_blocks_5_binary switcher_call_blocks_6_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary.

Section fundamental.
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

  (** Failure path of [interp_expr_switcher_call]: the checks on the stack
      pointer fail, and the call is unwound by the return routine. *)
  Lemma interp_switcher_call_force_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (rmap smap : Reg) (wcsp : Word) (zct2 zctp : Z)
    (a_tstk : Addr) (tstk_next ststk_next : list Word) :
    (∀ r, is_Some (rmap !! r)) ->
    (∀ r, is_Some (smap !! r)) ->
    rmap !! csp = Some wcsp ->
    smap !! csp = Some wcsp ->
    frame_match Ws Cs stk W C ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->
    (b_trusted_stack + length (map fst stk))%a = Some a_tstk ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    na_inv cerise_nais Nswitcher switcher_inv_binary ∗
    spec_ctx ∗
    (∀ (r : RegName) (v1 v2 : Word),
       ⌜r ≠ PC⌝ → ⌜rmap !! r = Some v1⌝ → ⌜smap !! r = Some v2⌝ → interp W C (v1, v2)) ∗
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
    PC ↦ᵣ switcher_block_pc 17 ∗
    PC ↣ᵣ switcher_block_pc 17 ∗
    csp ↦ᵣ wcsp ∗
    csp ↣ᵣ wcsp ∗
    ct2 ↦ᵣ WInt zct2 ∗
    ct2 ↣ᵣ WInt zct2 ∗
    ctp ↦ᵣ WInt zctp ∗
    ctp ↣ᵣ WInt zctp ∗
    ( [∗ map] k↦y ∈ delete ctp (delete ct2 (delete csp (delete PC rmap))), k ↦ᵣ y ) ∗
    ( [∗ map] k↦y ∈ delete ctp (delete ct2 (delete csp (delete PC smap))), k ↣ᵣ y ) ∗
    world_interp W C ∗
    interp_cont interp stk Ws Cs ∗
    cstack_frag (map fst stk) ∗
    cstack_frag_spec (map snd stk)
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: [switcher_call_block_17_spec] executes block 17,
       then close the switcher invariant and use the validity of the return
       routine ([interp_expr_switcher_return]). *)
    iIntros (Hfull_rmap Hfull_smap Hwcsp Hswcsp Hframe Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Hot_bounds)
      "(#Hinv_switcher & #Hspec & #Hreg & Hclose_switcher_inv & Hna & Hj & Hmtdc & Hsmtdc & Htstk & Hststk
      & Hcode & Hscode & Hb_switcher & Hsb_switcher & Hcstk_full & Hcstk_full_spec & Hstk_interp
      & Hsstk_interp & #Hp_ot_switcher & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp
      & Hrmap & Hsmap & Hworld_interp & Hcont & Hcstk & Hcstk_spec)".
    get_rvals_pair Hfull_rmap Hfull_smap [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iExtractList "Hsmap" [ca0;ca1] as ["Hsca0";"Hsca1"].
    iApply (switcher_call_block_17_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hca0 $Hsca0 $Hca1 $Hsca1 $Hcode $Hscode]").
    iNext; iIntros "(Hj & HPC & HsPC & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcode & Hscode)".
    iMod ("Hclose_switcher_inv"
           with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk
                  Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
    { iNext. iSplitL "Hmtdc Hcode Hb_switcher Htstk Hcstk_full Hstk_interp".
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto. by rewrite !length_map in Hlen_cstk |- *.
    }

    iInsertList "Hrmap" [csp;ctp;ct2;ca0;ca1;PC].
    iInsertListSpec "Hsmap" [csp;ctp;ct2;ca0;ca1;PC].
    iApply (interp_expr_switcher_return with "Hinv_switcher").
    iFrame "∗%#".
    rewrite /interp_reg /=.
    iSplit; [|iSplit].
    + iIntros (r) ; iPureIntro.
      destruct (decide (r = PC)); first by simplify_map_eq.
      destruct (decide (r = ca1)); first by simplify_map_eq.
      destruct (decide (r = ca0)); first by simplify_map_eq.
      destruct (decide (r = ct2)); first by simplify_map_eq.
      destruct (decide (r = ctp)); first by simplify_map_eq.
      destruct (decide (r = csp)); first by simplify_map_eq.
      simplify_map_eq.
      apply Hfull_rmap.
    + iIntros (r) ; iPureIntro.
      destruct (decide (r = PC)); first by simplify_map_eq.
      destruct (decide (r = ca1)); first by simplify_map_eq.
      destruct (decide (r = ca0)); first by simplify_map_eq.
      destruct (decide (r = ct2)); first by simplify_map_eq.
      destruct (decide (r = ctp)); first by simplify_map_eq.
      destruct (decide (r = csp)); first by simplify_map_eq.
      simplify_map_eq.
      apply Hfull_smap.
    + iIntros (r w1 w2 HrPC Hr1 Hr2).
      destruct (decide (r = ca1)); first (simplify_map_eq ; iApply interp_int).
      destruct (decide (r = ca0)); first (simplify_map_eq ; iApply interp_int).
      destruct (decide (r = ct2)); first (simplify_map_eq ; iApply interp_int).
      destruct (decide (r = ctp)); first (simplify_map_eq ; iApply interp_int).
      destruct (decide (r = csp)); simplify_map_eq; first (iApply "Hreg"; eauto).
      iApply "Hreg"; eauto.
  Qed.

  (** Failure path of [interp_expr_switcher_call]: the trusted stack is
      exhausted. *)
  Lemma interp_switcher_call_tstack_exhausted
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (rmap smap : Reg) (b e a : Addr) (lv slv : list Word)
    (wcs0 swcs0 wcs1 swcs1 wcra swcra wcgp swcgp wct1 swct1 wct2 swct2 wctp swctp : Word)
    (a_tstk : Addr) (tstk_next ststk_next : list Word) :
    dom rmap = all_registers_s ∖ {[ PC ; csp ; ct2 ; ctp ; cs0 ; cs1 ; cra ; cgp ; ct1 ]} ->
    dom smap = all_registers_s ∖ {[ PC ; csp ; ct2 ; ctp ; cs0 ; cs1 ; cra ; cgp ; ct1 ]} ->
    frame_match Ws Cs stk W C ->
    switcher_stk_bounds b e a ->
    length (finz.seq_between a e) = length lv ->
    length slv = length lv ->
    (b_trusted_stack <= a_tstk)%a ->
    (a_tstk <= e_trusted_stack)%a ->
    (b_trusted_stack + length (map fst stk))%a = Some a_tstk ->
    (ot_switcher < ot_switcher ^+ 1)%ot ->

    spec_ctx ∗
    interp W C (wcs0, swcs0) ∗
    interp W C (wcs1, swcs1) ∗
    interp W C (wcra, swcra) ∗
    interp W C (wcgp, swcgp) ∗
    interp W C (WCap RWL Local b e a, WCap RWL Local b e a) ∗
    ([∗ list] w;sw ∈ lv;slv, interp W C (w, sw)) ∗
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
    cs1 ↦ᵣ wcs1 ∗
    cs1 ↣ᵣ swcs1 ∗
    cgp ↦ᵣ wcgp ∗
    cgp ↣ᵣ swcgp ∗
    cra ↦ᵣ wcra ∗
    cra ↣ᵣ swcra ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    ct1 ↦ᵣ wct1 ∗
    ct1 ↣ᵣ swct1 ∗
    csp ↦ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    csp ↣ᵣ WCap RWL Local b e (a ^+ 4)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    switcher_stk_cells_spec a swcs0 swcs1 swcra swcgp ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ drop 4 lv ]] ∗
    [[ (a ^+ 4)%a , e ]] ↣ₐ [[ drop 4 slv ]] ∗
    switcher_stk_opened W C a e lv slv ∗
    ( [∗ map] k↦y ∈ rmap, k ↦ᵣ y ) ∗
    ( [∗ map] k↦y ∈ smap, k ↣ᵣ y ) ∗
    interp_cont interp stk Ws Cs ∗
    cstack_frag (map fst stk) ∗
    cstack_frag_spec (map snd stk)
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof: [switcher_call_blocks_5_spec] executes blocks 16
       and 14-15, [switcher_call_stk_close] closes the caller's stack frame,
       then close the switcher invariant and [switcher_jump_to_caller_spec]. *)
    iIntros (Hdom Hsdom Hframe Hstk_bounds Hlen_lv Hlen_slv Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Hot_bounds)
      "(#Hspec & #Hcs0v & #Hcs1v & #Hcrav & #Hcgpv & #Hspv & #Hlv & Hclose_switcher_inv & Hna & Hj
      & Hmtdc & Hsmtdc & Htstk & Hststk & Hcode & Hscode & Hb_switcher & Hsb_switcher
      & Hcstk_full & Hcstk_full_spec & Hstk_interp & Hsstk_interp & #Hp_ot_switcher & HPC & HsPC
      & Hcs0 & Hcs1 & Hscs1 & Hcgp & Hscgp & Hcra & Hscra & Hctp & Hsctp & Hct2 & Hsct2 & Hct1 & Hsct1
      & Hcsp & Hscsp & Hcells & Hscells & Hstk & Hsstk & Hstk_opened & Hrmap & Hsmap & Hcont
      & Hcstk & Hcstk_spec)".
    pose proof Hstk_bounds as (_ & Hba3 & Ha4).
    assert (4 <= length lv) as Hlen_lv4.
    { rewrite -Hlen_lv finz_seq_between_length /finz.dist. solve_addr. }
    assert (is_Some (rmap !! ca0)) as [? ?] by (apply elem_of_dom; rewrite Hdom; set_solver-).
    assert (is_Some (rmap !! ca1)) as [? ?] by (apply elem_of_dom; rewrite Hdom; set_solver-).
    assert (is_Some (smap !! ca0)) as [? ?] by (apply elem_of_dom; rewrite Hsdom; set_solver-).
    assert (is_Some (smap !! ca1)) as [? ?] by (apply elem_of_dom; rewrite Hsdom; set_solver-).
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iExtractList "Hsmap" [ca0;ca1] as ["Hsca0";"Hsca1"].
    iInsertList "Hrmap" [ct1;ctp;ct2].
    iInsertListSpec "Hsmap" [ct1;ctp;ct2].
    iApply (switcher_call_blocks_5_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hcsp $Hscsp $Hcells $Hscells $Hrmap $Hsmap $Hcode $Hscode]");
      first done.
    { repeat (rewrite dom_insert_L). repeat (rewrite dom_delete_L). rewrite Hdom. set_solver. }
    { repeat (rewrite dom_insert_L). repeat (rewrite dom_delete_L). rewrite Hsdom. set_solver. }
    iSplitL "Hcs1 Hscs1"; first iFrame.
    iSplitL "Hcgp Hscgp"; first iFrame.
    iSplitL "Hcra Hscra"; first iFrame.
    iSplitL "Hca0 Hsca0"; first iFrame.
    iSplitL "Hca1 Hsca1"; first iFrame.
    iNext; iIntros (rmap')
      "(%Hrmap' & Hj & HPC & HsPC & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcgp & Hscgp & Hcra & Hscra
      & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcsp & Hscsp & Hcells & Hscells & Hrmap & Hcode & Hscode & Hlc)".

    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
    iDestruct (switcher_stk_cells_region_spec with "Hscells Hsstk") as "Hsstk"; [done|solve_addr|].
    iDestruct (switcher_call_stk_close _ _ _ _ lv slv with "Hstk_opened Hstk Hsstk [Hlv]")
      as "Hworld_interp".
    { cbn; rewrite length_drop; lia. }
    { cbn; rewrite !length_drop; lia. }
    { rewrite -{1}(take_drop 4 lv) -{1}(take_drop 4 slv).
      iDestruct (big_sepL2_app_inv with "Hlv") as "[_ Hlv']".
      { left. rewrite !length_take. lia. }
      iFrame "#". }

    (* Close the switcher invariant *)
    iMod ("Hclose_switcher_inv"
           with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk
                  Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
    { iNext. iSplitL "Hmtdc Hcode Hb_switcher Htstk Hcstk_full Hstk_interp".
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto. by rewrite !length_map in Hlen_cstk |- *.
    }
    iDestruct "Hlc" as "[Hlc _]".
    iApply (switcher_jump_to_caller_spec W C stk Ws Cs rmap'
              (wcra, swcra) (wcgp, swcgp) (wcs0, swcs0) (wcs1, swcs1)
              (WCap RWL Local b e a, WCap RWL Local b e a)
              (WInt ENOTENOUGHTRUSTEDSTACK, WInt ENOTENOUGHTRUSTEDSTACK) (WInt 0, WInt 0) with
             "Hspec Hcrav Hcgpv Hcs0v Hcs1v Hspv [] [] HPC HsPC Hcra Hscra Hcgp Hscgp Hcs0 Hscs0
              Hcs1 Hscs1 Hcsp Hscsp Hca0 Hsca0 Hca1 Hsca1 Hrmap Hworld_interp Hcont Hcstk Hcstk_spec
              Hj Hna Hlc"); [done|done|iApply interp_int|iApply interp_int].
  Qed.

  (** The switcher-call entry point is safe to execute, in both runs.

      The proof follows the unary one. The stack pointer of the caller is
      related to itself: it is either sealed, and the execution fails in the
      implementation run, or the same capability in both runs. All the
      switcher's checks then take the same branch in both runs. Both trusted
      stacks have the same top address [a_tstk], hence trusted stack
      exhaustion happens in both runs together.
      The switcher pushes the same frame in both call stacks: the caller is
      untrusted, its saved registers are not recorded in the frame (they are
      saved in the shared callee-saved area). *)
  Lemma interp_expr_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ interp_expr interp (interp_cont interp) W C
        (WCap XSRW_ Local b_switcher e_switcher a_switcher_call,
         WCap XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    (* Outline of the proof:
       - open the switcher invariant of both runs;
       - when the stack pointer is sealed, [switcher_call_blocks_1_sealed_fail_spec];
       - [switcher_call_blocks_1_spec]: checks on the stack pointer;
         when they fail, [interp_switcher_call_force_unwind];
       - [switcher_call_stk_open]: open the caller's stack frame in the world
         (when the stack pointer is not a valid stack capability,
         [switcher_call_blocks_2_fail_spec]);
       - [switcher_call_blocks_2_spec]: spill the callee-save registers and
         push the stack pointer on both trusted stacks;
       - when the trusted stack is exhausted:
         [interp_switcher_call_tstack_exhausted];
       - [switcher_entry_point_prop]: the entry point satisfies the sealing
         predicate of the switcher, the same in both runs;
       - [switcher_call_blocks_3_spec]: clear the callee's stack frame and
         unseal the entry point;
       - [switcher_call_stk_close]: close the caller's stack frame;
       - [switcher_call_blocks_4_spec]: load the callee and jump to it;
       - [switcher_inv_push_frame], [switcher_inv_spec_push_frame]: close
         the switcher invariant;
       - [switcher_call_entry_registers]: execute the entry point. *)
    iIntros "#Hinv_switcher %stk %Ws %Cs %rmap %smap
      (#Hspec & [%Hfull_rmap [%Hfull_smap #Hreg]] & Hrmap & Hsmap & Hj & Hworld_interp
      & Hcont & Hna & Hcstk & Hcstk_spec & %Hframe)".
    rewrite /registers_pointsto /spec_registers_pointsto.
    cbn in Hfull_rmap, Hfull_smap.
    iPoseProof fundamental_ih as "IH". (* used for weakening lemma later *)

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
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
    iHide "Hinv_switcher" as hinv_switcher.

    iExtract "Hrmap" PC as "HPC".
    iExtract "Hsmap" PC as "HsPC".
    iEval (cbn) in "HPC". iEval (cbn) in "HsPC".
    get_rvals_pair Hfull_rmap Hfull_smap [csp;ct2;ctp].
    iExtractList "Hrmap" [csp;ct2;ctp] as ["Hcsp";"Hct2";"Hctp"].
    iExtractList "Hsmap" [csp;ct2;ctp] as ["Hscsp";"Hsct2";"Hsctp"].
    iDestruct ("Hreg" $! csp with "[//] [//] [//]") as "#Hspv".

    (* The stack pointer is either sealed, or the same in both runs *)
    iDestruct (interp_eq_unless_sealed with "Hspv") as %[<-|(o & sb1 & sb2 & -> & ->)]; cycle 1.
    { iApply (switcher_call_blocks_1_sealed_fail_spec with "[$HPC $Hcsp $Hct2 $Hcode]"). }

    (* Blocks 0-1: checks on the stack pointer *)
    iApply (switcher_call_blocks_1_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcsp $Hscsp $Hct2 $Hsct2 $Hctp $Hsctp $Hcode $Hscode]").
    iNext; iIntros "[(%Hchecked & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp
                      & Hcode & Hscode)
                    | (_ & %zct2 & %zctp & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp
                      & Hcode & Hscode)]";
      cycle 1.
    { (* The checks fail: force the unwinding of the call *)
      iApply (interp_switcher_call_force_unwind with
        "[$Hinv_switcher $Hspec $Hreg $Hclose_switcher_inv $Hna $Hj $Hmtdc $Hsmtdc $Htstk $Hststk
          $Hcode $Hscode $Hb_switcher $Hsb_switcher $Hcstk_full $Hcstk_full_spec $Hstk_interp
          $Hsstk_interp $Hp_ot_switcher $HPC $HsPC $Hcsp $Hscsp $Hct2 $Hsct2 $Hctp $Hsctp
          $Hrmap $Hsmap $Hworld_interp $Hcont $Hcstk $Hcstk_spec]"); done.
    }

    get_rvals_pair Hfull_rmap Hfull_smap [cs0;cs1;cra;cgp;ct1].
    iExtractList "Hrmap" [cs0;cs1;cra;cgp;ct1] as ["Hcs0";"Hcs1";"Hcra";"Hcgp";"Hct1"].
    iExtractList "Hsmap" [cs0;cs1;cra;cgp;ct1] as ["Hscs0";"Hscs1";"Hscra";"Hscgp";"Hsct1"].
    iDestruct ("Hreg" $! cs0 with "[//] [//] [//]") as "#Hcs0v".
    iDestruct ("Hreg" $! cs1 with "[//] [//] [//]") as "#Hcs1v".
    iDestruct ("Hreg" $! cra with "[//] [//] [//]") as "#Hcrav".
    iDestruct ("Hreg" $! cgp with "[//] [//] [//]") as "#Hcgpv".
    iDestruct ("Hreg" $! ct1 with "[//] [//] [//]") as "#Hct1v".

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
      as (lv slv) "(Hstk & Hsstk & Hstk_opened & #Hlv)"; first done.
    iDestruct (big_sepL2_length with "Hstk") as %Hlen_lv.
    iDestruct (big_sepL2_length with "Hsstk") as %Hlen_slv.

    (* Blocks 2-3: spill and push on the trusted stack *)
    iApply (switcher_call_blocks_2_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hcra $Hscra $Hcgp $Hscgp $Hctp $Hsctp
        $Hct2 $Hsct2 $Hcsp $Hscsp $Hstk $Hsstk $Hmtdc $Hsmtdc $Htstk $Hststk $Hcode $Hscode]");
      [done|done|].
    iNext; iIntros "(%Hstk_bounds & Hj & Hcs1 & Hscs1 & Hcra & Hscra & Hcgp & Hscgp & Hcsp & Hscsp
      & Hcells & Hscells & Hstk & Hsstk & Hcode & Hscode & Hbranch)".
    pose proof Hstk_bounds as (_ & Hba3 & Ha4).
    assert (4 <= length lv) as Hlen_lv4.
    { rewrite -Hlen_lv finz_seq_between_length /finz.dist. solve_addr. }
    iDestruct "Hbranch" as
      "[(%Ha_tstk2 & %Ha_tstk1_bound & HPC & HsPC & Hcs0 & Hscs0 & Hctp & Hsctp & Hct2 & Hsct2
         & Hmtdc & Hsmtdc & Ha_tstk1 & Hsa_tstk1 & Htstk & Hststk & Hlc)
       | (HPC & HsPC & Hcs0 & Hscs0 & Hctp & Hsctp & Hct2 & Hsct2 & Hmtdc & Hsmtdc & Htstk & Hststk)]";
      cycle 1.
    { (* The trusted stack is exhausted *)
      iApply (interp_switcher_call_tstack_exhausted W C Nswitcher stk Ws Cs _ _ b e a lv slv
                wcs0 swcs0 wcs1 swcs1 wcra swcra wcgp swcgp with
        "[$Hspec $Hcs0v $Hcs1v $Hcrav $Hcgpv $Hspv $Hlv $Hclose_switcher_inv $Hna $Hj $Hmtdc $Hsmtdc
          $Htstk $Hststk $Hcode $Hscode $Hb_switcher $Hsb_switcher $Hcstk_full $Hcstk_full_spec
          $Hstk_interp $Hsstk_interp $Hp_ot_switcher $HPC $HsPC Hcs0 Hscs0 $Hcs1 $Hscs1 $Hcgp $Hscgp
          $Hcra $Hscra $Hctp $Hsctp $Hct2 $Hsct2 $Hct1 $Hsct1 $Hcsp $Hscsp $Hcells $Hscells
          $Hstk $Hsstk $Hstk_opened $Hrmap $Hsmap $Hcont $Hcstk $Hcstk_spec]"); try done.
      { repeat (rewrite dom_delete_L). clear -Hfull_rmap.
        apply regmap_full_dom in Hfull_rmap. rewrite Hfull_rmap. set_solver. }
      { repeat (rewrite dom_delete_L). clear -Hfull_smap.
        apply regmap_full_dom in Hfull_smap. rewrite Hfull_smap. set_solver. }
      { lia. }
      iFrame.
    }

    (* Blocks 4-7: clear the callee's stack frame and unseal the entry point *)
    iDestruct (switcher_entry_point_prop with "Hp_ot_switcher []") as "[>%Hct1_eq Hentry_prop]".
    { case_match; [iExact "Hct1v"|done]. }
    iApply (switcher_call_blocks_3_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hcsp $Hscsp $Hstk $Hsstk
        $Hb_switcher $Hsb_switcher $Hct1 $Hsct1 $Hcode $Hscode]"); [done|done|].
    iNext; iIntros (wsb) "(-> & Hj & HPC & HsPC & Hcs0 & Hscs0 & (%wcs1' & Hcs1 & Hscs1)
      & Hcsp & Hscsp & Hstk & Hsstk & Hb_switcher & Hsb_switcher & Hct1 & Hsct1 & Hcode & Hscode)".

    (* Close the caller's stack frame *)
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
    iDestruct (switcher_stk_cells_region_spec with "Hscells Hsstk") as "Hsstk"; [done|solve_addr|].
    iDestruct (switcher_call_stk_close _ _ _ _ lv slv with "Hstk_opened Hstk Hsstk []")
      as "Hworld_interp".
    { cbn; rewrite /region_addrs_zeroes length_replicate -Hlen_lv !finz_seq_between_length /finz.dist.
      solve_addr. }
    { cbn; rewrite /region_addrs_zeroes !length_replicate. done. }
    { iFrame "#". iApply big_sepL2_forall. iSplit; first (by rewrite /region_addrs_zeroes).
      iIntros (k w sw Hk Hsk).
      apply lookup_replicate in Hk as [-> _].
      apply lookup_replicate in Hsk as [-> _].
      iApply interp_int. }

    iDestruct ("Hentry_prop" with "[//]")
      as (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs off Nexp_tbl Heq Heq' Htbl Hbtbl Hbtbl1 Hnargs)
           "(Htbl1 & Htbl2 & Htbl3 & #Hentry & #Hexec)".
    cbn in Heq; simplify_eq.
    iSpecialize ("Hexec" $! W with "[]").
    { iPureIntro. apply related_sts_priv_refl_world. }

    (* Blocks 7-11: load the callee and jump to it *)
    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↦ᵣ y)%I ] => set (rmap' := r) end.
    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↣ᵣ y)%I ] => set (smap' := r) end.
    set (params := dom_arg_rmap 8).
    set (Pf := ((λ '(r,_), r ∈ params) : RegName * Word → Prop)).
    assert (dom (filter Pf rmap') = dom_arg_rmap 8) as Hdom_params.
    { apply dom_filter_L. clear -Hfull_rmap.
      rewrite /rmap'. split.
      - intros Hi.
        repeat (rewrite lookup_delete_ne;[|rewrite /params /dom_arg_rmap /= in Hi; set_solver]).
        specialize (Hfull_rmap i) as [x Hx].
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    assert (dom (filter Pf smap') = dom_arg_rmap 8) as Hdom_sparams.
    { apply dom_filter_L. clear -Hfull_smap.
      rewrite /smap'. split.
      - intros Hi.
        repeat (rewrite lookup_delete_ne;[|rewrite /params /dom_arg_rmap /= in Hi; set_solver]).
        specialize (Hfull_smap i) as [x Hx].
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    rewrite -(map_filter_union_complement Pf rmap').
    rewrite -(map_filter_union_complement Pf smap').
    iDestruct (big_sepM_union with "Hrmap") as "[Hparams Hrest]".
    { apply map_disjoint_filter_complement. }
    iDestruct (big_sepM_union with "Hsmap") as "[Hsparams Hsrest]".
    { apply map_disjoint_filter_complement. }
    iDestruct (big_sepM2_sepM_2 with "Hparams Hsparams") as "Hparams".
    { intros k. rewrite -!elem_of_dom Hdom_params Hdom_sparams. done. }
    iAssert ([∗ map] r↦w;s ∈ filter Pf rmap';filter Pf smap',
               r ↦ᵣ w ∗ r ↣ᵣ s ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C (w, s) else True)%I
      with "[Hparams]" as "Hparams".
    { iApply (big_sepM2_impl with "Hparams").
      iIntros "!> %k %w1 %w2 %Hk1 %Hk2 [$ $]".
      destruct ( decide (k ∈ dom_arg_rmap nargs) ); last done.
      apply map_lookup_filter_Some in Hk1 as [Hk1 HPf].
      apply map_lookup_filter_Some in Hk2 as [Hk2 _].
      iApply ("Hreg" $! k); iPureIntro.
      - clear -HPf; rewrite /Pf /params /dom_arg_rmap /= in HPf; set_solver.
      - rewrite /rmap' in Hk1. repeat (apply lookup_delete_Some in Hk1 as [_ Hk1]); done.
      - rewrite /smap' in Hk2. repeat (apply lookup_delete_Some in Hk2 as [_ Hk2]); done.
    }
    iApply (switcher_call_blocks_4_spec W C with
      "[- $Hspec $Hj $Htbl1 $Htbl2 $Htbl3 $HPC $HsPC $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hct1 $Hsct1
        $Hct2 $Hsct2 $Hctp $Hsctp $Hcgp $Hscgp $Hcra $Hscra $Hparams $Hrest $Hsrest $Hcode $Hscode]");
      [done|done|lia|done|done| | |].
    { clear -Hfull_rmap. apply regmap_full_dom in Hfull_rmap as Heq'.
      rewrite /rmap' !map_filter_delete !dom_delete_L.
      cut (dom (filter (λ v, ¬ Pf v) rmap) = all_registers_s ∖ dom_arg_rmap 8);[set_solver|].
      apply (dom_filter_L _ (rmap : gmap RegName Word)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_rmap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }
    { clear -Hfull_smap. apply regmap_full_dom in Hfull_smap as Heq'.
      rewrite /smap' !map_filter_delete !dom_delete_L.
      cut (dom (filter (λ v, ¬ Pf v) smap) = all_registers_s ∖ dom_arg_rmap 8);[set_solver|].
      apply (dom_filter_L _ (smap : gmap RegName Word)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_smap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }
    iNext; iIntros (arg_rmap' arg_smap' rmap'' smap'')
      "(%Harg_rmap' & %Harg_smap' & %Hrmap'' & %Hsmap'' & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra
      & Hargs & Hregs & Hsregs & Hcode & Hscode)".

    (* Push the frames and close the switcher invariant *)
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
    iMod (switcher_inv_push_frame frame (map fst stk) with
           "Hcstk_full Hcstk Hmtdc Ha_tstk1 Htstk Hstk_interp [] Hcode Hb_switcher Hp_ot_switcher")
      as "[Hinv Hcstk]"; [done|done|done|done|done|done| |].
    { by rewrite /cframe_stk_own /=. }
    iMod (switcher_inv_spec_push_frame frame (map snd stk) with
           "Hcstk_full_spec Hcstk_spec Hsmtdc Hsa_tstk1 Hststk Hsstk_interp [] Hscode Hsb_switcher")
      as "[Hsinv Hcstk_spec]"; [done|done|done| |done| |].
    { by rewrite !length_map in Hlen_cstk |- *. }
    { by rewrite /cframe_stk_own_spec /=. }
    iMod ("Hclose_switcher_inv" with "[$Hinv $Hsinv $Hna]") as "Hna".

    (* Execute the entry point of the callee *)
    iAssert (interp W C (WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a, WCap RWL Local (a ^+ 4)%a e (a ^+ 4)%a))
      as "#Hstk4v".
    { iApply (interp_weakening with "IH Hspv"); auto; solve_addr. }
    iDestruct (switcher_call_entry_registers W W C nargs arg_rmap' arg_smap' rmap'' smap'' with
                "[$HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hstk4v $Hargs $Hregs $Hsregs]")
      as (regs1 regs2) "(Hregs & Hsregs & Hregs_interp)";
      [apply related_sts_pub_refl_world|done|done|done|done|].
    iApply ("Hexec" $! ((frame, frame) :: stk) (W :: Ws) (C :: Cs) regs1 regs2 a e).
    iSplitR; first iFrame "#".
    iSplitL "Hcont".
    { iFrame "Hcont". simpl.
      iSplit; first (iPureIntro; apply cframe_pair_cond_diag).
      iSplit.
      - iApply (interp_weakening with "IH Hspv");auto;solve_addr.
      - iIntros (W' HW' ???????) "(_ & HPC & _)".
        rewrite /interp_conf.
        wp_instr.
        iApply (wp_notCorrectPC with "[$]").
        { intros Hcontr;inversion Hcontr. }
        iIntros "!> HPC". wp_pure. wp_end. iIntros (Hcontr);done. }
    iSplitR.
    { iPureIntro. simpl. split;auto. apply related_sts_pub_refl_world. }
    iFrame "Hregs Hsregs Hregs_interp Hworld_interp Hcstk Hcstk_spec Hna Hj".
    iPureIntro; split; [repeat split; reflexivity | solve_addr].
  Qed.

  Lemma interp_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call,
                  WSentry XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /= /interp1_pair /=.
    iSplit; first done.
    iIntros "!> %W' % %g' %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_call with "Hinv").
  Qed.

End fundamental.
