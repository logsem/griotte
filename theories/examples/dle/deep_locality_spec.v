From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening.
From cap_machine Require Import logrel logrel_extra rules proofmode.
From cap_machine Require Import fetch assert switcher_spec_call deep_locality.

Section DLE.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

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
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

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
    ∗ sts_full_world W C
    ∗ region W C
    ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), closing_revoked_resources W C a ∗ ⌜(std W) !! a = Some Revoked⌝)
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg),
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W (finz.seq_between a_stk4 e_stk) Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own logrel_nais ⊤
              ∗ interp W2 C (WCap RWL Local a_stk4 e_stk a_stk4)
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk)%a ⌝
              (* Interpretation of the world *)
              ∗ sts_full_world W2 C
              ∗ open_region_many W2 C (finz.seq_between a_stk4 e_stk)
              ∗ ([∗ list] a ∈ (finz.seq_between a_stk a_stk4), closing_revoked_resources W C a ∗ ⌜(std W) !! a = Some Revoked⌝)
              ∗ ([∗ list] a ∈ (finz.seq_between a_stk4 e_stk), closing_resources interp W2 C a (WInt 0))
              ∗ cstack_frag cstk
              ∗ ([∗ list] a ∈ (finz.seq_between a_stk4 e_stk), ⌜ std W2 !! a = Some Temporary ⌝ )
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
  Admitted.

  Context {C : CmptName}.

  Lemma related_sts_pub_world_revoked_temporary' W a :
    (std W) !! a = None →
    related_sts_pub_world W (<s[a:=Temporary]s>W).
  Proof.
    intros Ha.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst.
        rewrite Hx in Ha. inversion Ha.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.
  Lemma std_update_lookup_ne a a' W ρ :
    a ≠ a' -> (std (<s[a:=ρ]s>W)) !! a' = (std W) !! a'.
  Proof.
    intros Ha; cbn.
    rewrite lookup_insert_ne;auto.
  Qed.

  Program Definition interp_dl : V :=
    (λne (W : WORLD) (B : leibnizO CmptName) (v : leibnizO Word)
     , (interp W B (deeplocal (borrow v)))%I).
  Solve All Obligations with solve_proper.



  Lemma dle_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports :=
     dle_main_imports b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp ; cra]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code)%a ->

    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W_init_C) ->
    (cgp_b ^+1 )%a ∉ dom (std W_init_C) ->

    frame_match Ws Cs cstk W_init_C C ->
    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher switcher_inv
      ∗ na_own logrel_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ (∃ wcra, cra ↦ᵣ wcra)
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a dle_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ dle_main_data ]]

      ∗ region W_init_C C ∗ sts_full_world W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W_init_C C (WCap RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_a Hframe_match
            )
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & [%wcra Hcra] & Hrmap
      & Himports_main & Hcode_main & Hcgp_main
      & HWreg_C & HWstd_full_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_C_g
      & #HentryC_g
      & #Hinterp_Winit_C_csp
      )".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    (* --- Extract registers ca0 ct0 ct1 ct2 ct3 cs0 cs1 --- *)
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct2) ) as [wct2 Hwct2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct3) ) as [wct3 Hwct3].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs0) ) as [wcs0 Hwcs0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cs1) ) as [wcs1 Hwcs1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.

    (* Extract the addresses of b and a *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_a _]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f _]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.

    (* Store cgp 42%Z; *)
    iInstr "Hcode".
    { solve_addr. }
    (* Mov ct0 cgp; *)
    iInstr "Hcode".

    (* GetB ct1 cgp; *)
    iInstr "Hcode".
    (* Add ct2 ct1 1%Z; *)
    iInstr "Hcode".
    (* Subseg ct0 ct1 ct2; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

    (* Lea cgp 1%Z; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    (* Store cgp ct0; *)
    (* NOTE for some reason, iInstr doesnt work here lol *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg with "[$HPC $Hi $Hct0 $Hcgp $Hcgp_a]") ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hcgp_a)".
    iDestruct ("Hcode" with "Hi") as "Hcode".
    wp_pure.

    (* Mov ca0 cgp; *)
    iInstr "Hcode".
    (* Lea cgp (-1)%Z; *)
    iInstr "Hcode".
    { transitivity (Some cgp_b); auto; solve_addr. }
    (* Add ct1 ct2 1%Z; *)
    iInstr "Hcode".
    (* Subseg ca0 ct2 ct1; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    (* Restrict ca0 rw_dl *)
    iInstr "Hcode".
    { by rewrite decode_encode_permPair_inv. }
    { solve_pure. }
    { solve_pure. }

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hct1 $Hct2 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hct1 & Hct2 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct2 $Hct3 $Hcode $Himport_C_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cs0 ct0; *)
    iInstr "Hcode".
    (* Mov cs1 ct1; *)
    iInstr "Hcode" with "Hlc".

    (* Jalr cra ct0; *)
    iInstr "Hcode" with "Hlc'".

    (* -- separate argument registers -- *)
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca2) ) as [wca2 Hwca2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca3) ) as [wca3 Hwca3].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca4) ) as [wca4 Hwca4].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca5) ) as [wca5 Hwca5].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    set ( rmap_arg :=
           {[ ca0 := WCap RW_DL Local (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a;
              ca1 := wca1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    rewrite !(delete_commute _ _ ct2).
    iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).
    rewrite !(delete_commute _ _ ct3).
    iDestruct (big_sepM_insert _ _ ct3 with "[$Hrmap $Hct3]") as "Hrmap"; first by simplify_map_eq.
    rewrite insert_delete_insert.
    repeat (rewrite -delete_insert_ne //).

    set (rmap' := (delete ca5 _)).

    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W_init_C.1 !! a = Some Temporary⌝)%I as "Hstack_temporary".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_Winit_C_csp"); eauto. }

    iMod (monotone_revoke_stack with "[$Hinterp_Winit_C_csp $HWstd_full_C $HWreg_C]")
        as (l_unk) "(%Hl_unk & HWstd_full_C & HWreg_C & Hstk' & Hrevoked_rest)".
    iAssert (
        |={⊤}=>
          ([∗ list] a ∈ finz.seq_between csp_b csp_e,
             closing_revoked_resources W_init_C C a
             ∗ ⌜(revoke W_init_C).1 !! a = Some Revoked⌝
             ∗ ∃ v, a ↦ₐ v
          )
      )%I with "[Hstk' Hlc']" as ">Hstk'".
    {
      rewrite !big_sepL_sep.
      iDestruct "Hstk'" as "[Hstk' $]".
      iDestruct (big_sepL_later_2 with "Hstk'") as "Hstk'".
      iDestruct (lc_fupd_elim_later with "[$] [$Hstk']") as ">Hstk'".
      iModIntro.
      rewrite -big_sepL_sep.
      iApply (big_sepL_impl with "Hstk'").
      iModIntro; iIntros (k a Hx) "Hrev".
      iDestruct (close_revoked_resources with "Hrev") as (v) "[$ $]".
    }
    iAssert (
        ∃ stk_mem,
         ([∗ list] a ∈ finz.seq_between csp_b csp_e,
          closing_revoked_resources W_init_C C a ∗ ⌜(revoke W_init_C).1 !! a = Some Revoked⌝)
         ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      )%I with "[Hstk']" as (stk_mem) "[Hclose_res Hcsp_stk]".
    { rewrite !big_sepL_sep.
      iDestruct "Hstk'" as "(Hclose & Hrev & Hv)".
      iDestruct (big_sepL_sep with "[$Hclose $Hrev]") as "$".
      by iApply region_addrs_exists.
    }
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_b]") as "%Hcgp_b_stk".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_a]") as "%Hcgp_a_stk".

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W0 := W')
    end.

    iMod (extend_region_temp _ _ _ _ _ RW_DL interpC
        with "[] [$HWstd_full_C] [$HWreg_C] [$Hcgp_b] []")
      as "(HWreg_C & #Hrel_cgp_b & HWstd_full_C)".
    { done. }
    { subst W0.
      by rewrite -revoke_dom_eq.
    }
    { rewrite /future_pub_mono.
      iIntros "!>" (W W' Hrelated) "H"; cbn.
      rewrite /interpC /safeC; iApply interp_int.
    }
    { rewrite /interpC /safeC; iApply interp_int. }

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W1 := W')
    end.

    iAssert (interp W1 C (WCap RW_DL Local cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_cgp_b".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RW_DL, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit; first iApply zcond_interp.
      iSplit; first iApply rcond_interp.
      iSplit; first iApply wcond_interp.
      iSplit; first iApply monoReq_interp.
      + by simplify_map_eq.
      + by intro.
      + by iPureIntro; right; simplify_map_eq.
    }


    iMod (extend_region_temp _ _ _ _ _ RW_DL (safeC interp_dl)
        with "[] [$HWstd_full_C] [$HWreg_C] [$Hcgp_a] []")
      as "(HWreg_C & Hrel_cgp_a & HWstd_full_C)".
    { done. }
    { subst W1.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; solve_addr+Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }
    { rewrite /future_pub_mono.
      iIntros "!>" (W W' Hrelated) "H"; cbn.
      iApply monotone.interp_monotone; eauto.
    }
    { done. }

    match goal with
    | _ : _ |- context [ region ?W' ] => set (W2 := W')
    end.

    assert (related_sts_priv_world W_init_C W2) as HWinit_privC_W2.
    { eapply related_sts_priv_trans_world with (W' := W0) ; eauto
      ; first eapply revoke_related_sts_priv_world.
      eapply related_sts_pub_priv_trans_world with (W' := W1) ; eauto.
      { eapply related_sts_pub_world_revoked_temporary'.
        subst W0.
        by rewrite -revoke_lookup_None -not_elem_of_dom.
      }
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_world_revoked_temporary'.
      subst W1.
      rewrite std_update_lookup_ne; last solve_addr.
      by rewrite -revoke_lookup_None -not_elem_of_dom.
    }

    iAssert (interp W2 C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply monotone.interp_monotone_sd; eauto. }

    iAssert (interp W2 C (WCap RW_DL Local (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a)) as "#Hinterp_W1_C_a".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)%a); last solve_addr.
      iApply big_sepL_singleton.
      iExists RW_DL, interp_dl.
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_a".
      (* TODO make lemma for the following *)
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z) "H".
        iApply interp_int.
      }
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (w') "H".
        done.
      }
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (w') "H".
        by iApply interp_deeplocal_word; iApply interp_borrow_word.
      }
      subst W2.
      iSplit.
      + rewrite /monoReq; simplify_map_eq.
        iIntros (?) "!> %W %W' %Hrelated H"; cbn.
        iApply monotone.interp_monotone; auto.
      + iPureIntro.
        by right; rewrite lookup_insert.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W2 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W2 C (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    iEval (cbn) in "Hct1".
    iApply (switcher_cc_specification _ W2 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk $HWreg_C $HWstd_full_C $Hcstk_frag
              $Hinterp_W1_C_f $HentryC_g $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }
    iSplitL "Hclose_res".
    { rewrite !big_sepL_sep.
      iDestruct "Hclose_res" as "[Hclose Hrev]".
      iSplitL "Hclose".
      - iApply (big_sepL_impl with "Hclose").
        iModIntro; iIntros (k a Ha) "Hclose".
        rewrite /closing_revoked_resources.
        iDestruct "Hclose" as (???) "(?&?&#Hmono&#Hzcond&#Hrcond&#Hwcond&?)".
        iExists φ,p,Hpers; iFrame "∗#".
        iApply "Hzcond"; done.
      - iApply (big_sepL_impl with "Hrev").
        iModIntro; iIntros (k a Ha) "Hrev".
        iDestruct (big_sepL_pure_1 with "Hstack_temporary") as "%Hstack_temporary".
        subst W2 W1 W0.
        iPureIntro.
        pose proof (elem_of_list_lookup_2 _ _ _ Ha) as Ha'.
        rewrite lookup_insert_ne; last (set_solver+Ha' Hcgp_a_stk).
        rewrite lookup_insert_ne; last (set_solver+Ha' Hcgp_b_stk).
        destruct W_init_C as [WC ?]; cbn.
        apply revoke_lookup_Monotemp.
        eapply Hstack_temporary; eauto.
    }

    iNext. subst rmap'.
    iIntros (W3 rmap')
      "(%HW1_pubB_W2 & %Hdom_rmap'
      & Hna & #Hinterp_csp & %Hcsp_bounds
      & HWstd_full_C & HWreg_C & Hclose_reg_C' & Hclose_reg_C
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hcsp_stk & HK)".
    iEval (cbn) in "HPC".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero".
    assert (∀ r : RegName, r ∈ dom rmap' → rmap' !! r = Some (WInt 0)) as Hrmap_init'.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    assert ( rmap' !! ct0 = Some (WInt 0) ) as Hwct0'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct1 = Some (WInt 0) ) as Hwct1'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.

    assert ( cgp_b ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_b_stk'.
    { clear -Hcgp_b_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_b_stk.
      destruct Hcgp_b_stk; [left|right]; solve_addr.
    }
    assert ( (cgp_b ^+1)%a  ∉ finz.seq_between (csp_b ^+ 4)%a csp_e ) as Hcgp_a_stk'.
    { clear -Hcgp_a_stk.
      apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_a_stk.
      destruct Hcgp_a_stk; [left|right]; solve_addr.
    }
    iEval (rewrite <- (app_nil_r (finz.seq_between (csp_b ^+ 4)%a csp_e))) in "HWreg_C".
    rewrite (region_addrs_zeroes_split _ (csp_b ^+4)%a).
    2: { split; solve_addr+Hcsp_bounds. }
    set (lv := region_addrs_zeroes (csp_b ^+4)%a csp_e).
    iDestruct (region_pointsto_split _ _ (csp_b ^+4)%a with "Hcsp_stk") as "[Hcsp_stk' Hcsp_stk]".
    { split; solve_addr+Hcsp_bounds. }
    { by rewrite length_replicate. }
    iAssert (
       [∗ list] a ; v ∈ finz.seq_between (csp_b ^+ 4)%a csp_e ; lv, a ↦ₐ v ∗ closing_resources interp W3 C a v
      )%I with "[Hclose_reg_C Hcsp_stk]" as "Hclose_reg_C".
    { rewrite /region_pointsto.
      iDestruct (big_sepL2_sep_sepL_l  with "[$Hclose_reg_C $Hcsp_stk]") as "H".
      iApply (big_sepL2_impl with "H").
      iIntros "!> % % % % % [? $]"; iFrame.
      subst lv; apply lookup_replicate in H2 as [-> _]; done.
    }
    iDestruct (
        ftlr_switcher_return.region_close_list_interp_gen
          with "[$HWreg_C $Hclose_reg_C]"
      ) as "HWreg_C".
    { apply finz_seq_between_NoDup. }
    { set_solver+. }
    { subst lv; by rewrite length_replicate finz_seq_between_length. }
    rewrite -region_open_nil.

    assert (related_sts_pub_world W2 W3) as Hrelated_pub_W2_W3.
    { eapply related_sts_pub_trans_world ; eauto.
      apply related_sts_pub_update_multiple_temp.
      apply Forall_forall; intros a Ha.
      rewrite std_update_lookup_ne;[|intro Hcontra; subst a; set_solver+Ha Hcgp_a_stk'].
      rewrite std_update_lookup_ne;[|intro Hcontra; subst a; set_solver+Ha Hcgp_b_stk'].
      cbn.
      eapply revoke_lookup_Monotemp.
      destruct Hl_unk as [_ Htemp]; apply Htemp.
      apply elem_of_app; right.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr+Ha.
    }

    assert ( cgp_b ∉ finz.seq_between csp_b (csp_b ^+ 4)%a ) as Hcgp_b_stk''.
    { apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_b_stk.
      destruct Hcgp_b_stk; [left|right]; solve_addr.
    }
    assert ( (cgp_b ^+1)%a ∉ finz.seq_between csp_b (csp_b ^+ 4)%a ) as Hcgp_a_stk''.
    { apply not_elem_of_finz_seq_between.
      apply not_elem_of_finz_seq_between in Hcgp_a_stk.
      destruct Hcgp_a_stk; [left|right]; solve_addr.
    }

    iMod (revoked_by_separation_many with "[$HWreg_C $HWstd_full_C $Hcsp_stk']")
      as "(HWreg_C & HWstd_full_C & Hcsp_stk' & %Hcsp_save_revoked)".
    { apply Forall_forall; intros a Ha.
      (* TODO lemma elem_of related *)
      assert (a ∈ dom (std W2)) as Ha'.
      { subst W2 W1 W0.
        cbn.
        rewrite elem_of_dom.
        rewrite lookup_insert_ne.
        2:{ intro Hcontra; subst a; set_solver +Ha Hcgp_a_stk''. }
        rewrite lookup_insert_ne.
        2:{ intro Hcontra; subst a; set_solver +Ha Hcgp_b_stk''. }
        rewrite revoke_lookup_Monotemp; first done.
        (* by applying Hl_unk *)
        admit.
      }
      rewrite elem_of_dom in Ha'; destruct Ha' as [? Ha'].
      destruct Hrelated_pub_W2_W3 as [ [ Hdom_sta Hrelated] _]. simpl in *.
      assert (is_Some ((std W3) !! a)) as [y Hy].
      { rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom;eauto. }
      by rewrite elem_of_dom.
    }
    rewrite Forall_forall in Hcsp_save_revoked.


    iMod (monotone_revoke_stack with "[$Hinterp_csp $HWstd_full_C $HWreg_C]")
        as (l_unk') "(%Hl_unk' & HWstd_full_C & HWreg_C & Hstk'' & Hrevoked_rest')".
    iAssert (
        |={⊤}=>
          ([∗ list] a ∈ finz.seq_between (csp_b ^+4)%a csp_e,
             closing_revoked_resources W3 C a
             ∗ ⌜(revoke W3).1 !! a = Some Revoked⌝
             ∗ ∃ v, a ↦ₐ v
          )
      )%I with "[Hstk'' Hlc]" as ">Hstk''".
    {
      rewrite !big_sepL_sep.
      iDestruct "Hstk''" as "[Hstk'' $]".
      iDestruct (big_sepL_later_2 with "Hstk''") as "Hstk''".
      iDestruct (lc_fupd_elim_later with "[$] [$Hstk'']") as ">Hstk''".
      iModIntro.
      rewrite -big_sepL_sep.
      iApply (big_sepL_impl with "Hstk''").
      iModIntro; iIntros (k a Hx) "Hrev".
      iDestruct (close_revoked_resources with "Hrev") as (v) "[$ $]".
    }
    iAssert (
        ∃ stk_mem,
         ([∗ list] a ∈ finz.seq_between (csp_b ^+4)%a csp_e,
          closing_revoked_resources W3 C a ∗ ⌜(revoke W3).1 !! a = Some Revoked⌝)
         ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      )%I with "[Hstk'' Hcsp_stk']" as (stk_mem') "[Hclose_res' Hcsp_stk']".
    { rewrite !big_sepL_sep.
      iDestruct "Hstk''" as "(Hclose & Hrev & Hv)".
      iDestruct (big_sepL_sep with "[$Hclose $Hrev]") as "$".
      iDestruct (region_addrs_exists with "Hv") as (ws) "Hws".
      rewrite -/(region_pointsto (csp_b ^+ 4)%a csp_e ws).
      iExists _.
      iDestruct (region_pointsto_split with "[$Hcsp_stk' $Hws]") as "Hws"; auto.
      by rewrite length_replicate.
    }


    (* TODO from here:
       we need to revoke the world again,
       to get the points-to of the DL shared memory back
     *)

    assert (cgp_b ∈ l_unk') as Hcgp_lunk'.
    {
      assert ( W3.1 !! cgp_b = Some Temporary ) as HW3.
      { eapply monotone.region_state_pub_temp; eauto.
        rewrite lookup_insert_ne; last solve_addr.
        by rewrite lookup_insert.
      }
      destruct Hl_unk' as [_ Hl_unk'].
      pose proof (Hl_unk' cgp_b) as [Hl_unk'_cgp _].
      apply Hl_unk'_cgp in HW3.
      apply elem_of_app in HW3 as [?|?]; done.
    }
    iAssert
      ( ∃ l_unk'',
          ⌜ l_unk' ≡ₚ cgp_b::l_unk'' ⌝
          ∗ ([∗ list] a ∈ l_unk'', (∃ (p' : Perm) (φ : WORLD * CmptName * Word → iPropI Σ),
                                             ⌜∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)⌝ ∗ ▷ temp_resources W3 C φ a p' ∗
                                             rel C a p' φ) ∗ ⌜(revoke W3).1 !! a = Some Revoked⌝)
          ∗ (▷ (∃ v, cgp_b ↦ₐ v)))%I with "[Hrevoked_rest']"
      as (l_unk'') "(%Hl_unk'' & Hrevoked_rest' & >[%wcgpb Hcgp_b])".
    { destruct Hl_unk' as [Hnodup ?].
      apply NoDup_app in Hnodup as (Hnodup_l_unk & ? & ?).
      apply elem_of_Permutation in Hcgp_lunk' as [l_unk'' Hl_unk''].
      iExists l_unk''; iFrame "%".
      iEval (setoid_rewrite Hl_unk'') in "Hrevoked_rest'".
      iDestruct "Hrevoked_rest'" as "[ [Hv _] $]".
      iDestruct "Hv" as (? ? ?) "[Hv _]".
      iNext.
      rewrite /temp_resources.
      iDestruct "Hv" as (??) "[$ _]".
    }

    (* Store cgp 42%Z; *)
    iInstr "Hcode".
    { solve_addr+Hcgp_contiguous. }
    (* Mov ca0 0%Z; *)
    iInstr "Hcode".
    (* Mov ct0 cs0; *)
    iInstr "Hcode".
    (* Mov ct1 cs1; *)
    iInstr "Hcode".
    (* Jalr cra ct0; *)
    iInstr "Hcode".

    clear dependent wca1 wca2 wca3 wca4 wca5.
    (* -- separate argument registers -- *)
    assert ( is_Some (rmap' !! ca2) ) as [wca2 Hwca2].
    { exists (WInt 0); apply Hrmap_init'; rewrite Hdom_rmap' ; done. }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap' !! ca3) ) as [wca3 Hwca3].
    { exists (WInt 0); apply Hrmap_init'; rewrite Hdom_rmap' ; done. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap' !! ca4) ) as [wca4 Hwca4].
    { exists (WInt 0); apply Hrmap_init'; rewrite Hdom_rmap' ; done. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap' !! ca5) ) as [wca5 Hwca5].
    { exists (WInt 0); apply Hrmap_init'; rewrite Hdom_rmap' ; done. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    set ( rmap_arg :=
           {[ ca0 := WInt 0;
              ca1 := warg1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).
    set (rmap'' := (delete ca5 _)).
    set (W4 := revoke W3).

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W4 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W4 C (WInt 0)) as "Hinterp_0".
      { iEval (rewrite fixpoint_interp1_eq); done. }
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    assert (related_sts_priv_world W3 W4) as Hrelated_priv_W3_W4 by apply revoke_related_sts_priv_world.

    iAssert (interp W4 C (WSealed ot_switcher C_f)) as "#Hinterp_W3_C_f".
    { iApply monotone.interp_monotone_sd; eauto.
      iApply monotone.interp_monotone_sd; eauto.
      iPureIntro; apply related_sts_pub_priv_world; auto.
    }

    iApply (switcher_cc_specification _ W4 with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hcsp_stk' $HWreg_C $HWstd_full_C $Hcstk_frag
              $Hinterp_W3_C_f $HentryC_g $HK]"); eauto.
    { subst rmap''.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hdom_rmap'.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }
    iSplitL "Hclose_reg_C' Hclose_res' Hrel_stk_C".
    { rewrite !big_sepL_sep.
      iDestruct "Hclose_res'" as "[Hclose Hrev]".
      iDestruct "Hclose_reg_C'" as "[Hclose' Hrev']".
      iSplitL "Hclose Hclose'".
      - rewrite (finz_seq_between_split csp_b (csp_b ^+ 4)%a csp_e); last solve_addr.
        rewrite big_sepL_app.
        iSplitL "Hclose'".
        + iApply (big_sepL_impl with "Hclose'").
          iModIntro; iIntros (k a Ha) "Hclose'".
          rewrite /closing_revoked_resources.
          iDestruct "Hclose'" as (???) "(?&?&#Hmono&#Hzcond&#Hrcond&#Hwcond&?)".
          iExists φ,p,Hpers; iFrame "∗#".
          iApply "Hzcond"; done.
        + iApply (big_sepL_impl with "Hclose").
          iModIntro; iIntros (k a Ha) "Hclose".
          rewrite /closing_revoked_resources.
          iDestruct "Hclose" as (???) "(?&?&#Hmono&#Hzcond&#Hrcond&#Hwcond&?)".
          iExists φ,p,Hpers; iFrame "∗#".
          iApply "Hzcond"; done.
      - rewrite (finz_seq_between_split csp_b (csp_b ^+ 4)%a csp_e); last solve_addr.
        rewrite big_sepL_app.
        iSplitL "Hrev'"; last done.
        iApply (big_sepL_impl with "Hrev'").
        iModIntro; iIntros (k a Ha) "%Hrev'".
        iDestruct (big_sepL_pure_1 with "Hstack_temporary") as "%Hstack_temporary".
        iPureIntro.
        subst W4.
        apply revoke_lookup_Revoked.
        by eapply Hcsp_save_revoked.
    }

    iNext. subst rmap''.
    clear dependent warg0 warg1 rmap'.
    iIntros (W5 rmap')
      "(%HW4_pubB_W5 & %Hdom_rmap'
      & Hna & #Hinterp_csp' & _
      & HWstd_full_C & HWreg_C & Hclose_reg_C' & Hclose_reg_C
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hcsp_stk & HK)".
    iEval (cbn) in "HPC".

    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hrmap_zero]".
    iDestruct (big_sepM_pure with "Hrmap_zero") as "%Hrmap_zero'".
    assert (∀ r : RegName, r ∈ dom rmap' → rmap' !! r = Some (WInt 0)) as Hrmap_init'.
    { intros r Hr.
      rewrite elem_of_dom in Hr. destruct Hr as [wr Hr].
      pose proof Hr as Hr'.
      eapply map_Forall_lookup in Hr'; eauto.
      by cbn in Hr' ; simplify_eq.
    }
    iClear "Hrmap_zero".

    (* ---- extract the needed registers ct0 ct1 ----  *)
    assert ( rmap' !! ct0 = Some (WInt 0) ) as Hwct0'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct1 = Some (WInt 0) ) as Hwct1'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct2 = Some (WInt 0) ) as Hwct2'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct3 = Some (WInt 0) ) as Hwct3'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct3 with "Hrmap") as "[Hct3 Hrmap]"; first by simplify_map_eq.
    assert ( rmap' !! ct4 = Some (WInt 0) ) as Hwct4'.
    { apply Hrmap_init'. rewrite Hdom_rmap'.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct4 with "Hrmap") as "[Hct4 Hrmap]"; first by simplify_map_eq.

    (* Load ct0 cgp  *)
    iInstr "Hcode".
    { split; [done| solve_addr]. }
    (* Mov ct1 42  *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ------------------ BLOCK 5: HALT ------------------ *)
    (* --------------------------------------------------- *)
    focus_block 5 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* JmpCap cra *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.

    (* iDestruct ( *)
    (*    region_close_next with "[$Hstd_cgp_b $HWreg_B $Hcgp_b $Hmono $Hrel_cgp_b Hinterp_cgp_b']") as "HWreg_B" *)
    (* ; auto. *)
    (* { iSplit; first done. *)
    (*   cbn. iNext; iSplit; done. *)
    (* } *)
    (* subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main". *)

    (* clear dependent a_fetch1 a_fetch2 a_callB a_assert_c. *)

    (* rewrite !(delete_commute _ _ ct0). *)
    (* iDestruct (big_sepM_insert _ _ ct0 with "[$Hrmap $Hct0]") as "Hrmap"; first by simplify_map_eq. *)
    (* rewrite insert_delete_insert. *)
    (* repeat (rewrite -delete_insert_ne //); rewrite insert_id; auto. *)

    (* rewrite !(delete_commute _ _ ct1). *)
    (* iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap"; first by simplify_map_eq. *)
    (* rewrite insert_delete_insert. *)
    (* repeat (rewrite -delete_insert_ne //); rewrite insert_id; auto. *)

    (* rewrite !(delete_commute _ _ ct2). *)
    (* iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap"; first by simplify_map_eq. *)
    (* rewrite insert_delete_insert. *)
    (* repeat (rewrite -delete_insert_ne //); rewrite insert_id; auto. *)

    (* rewrite !(delete_commute _ _ ct3). *)
    (* iDestruct (big_sepM_insert _ _ ct3 with "[$Hrmap $Hct3]") as "Hrmap"; first by simplify_map_eq. *)
    (* rewrite insert_delete_insert. *)
    (* repeat (rewrite -delete_insert_ne //); rewrite insert_id; auto. *)

    (* iDestruct (big_sepM_insert _ _ ct4 with "[$Hrmap $Hct4]") as "Hrmap"; first by simplify_map_eq. *)
    (* rewrite insert_delete_insert. *)
    (* repeat (rewrite -delete_insert_ne //); rewrite insert_id; auto. *)

    (* iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap". *)
    (* { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap'; set_solver+. } *)
    (* iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap". *)
    (* { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap'; set_solver+. } *)
    (* iDestruct (big_sepM_insert _ _ ca0 with "[$Hrmap $Hca0]") as "Hrmap". *)
    (* { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap'; set_solver+. } *)
    (* iDestruct (big_sepM_insert _ _ ca1 with "[$Hrmap $Hca1]") as "Hrmap". *)
    (* { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; rewrite Hdom_rmap'; set_solver+. } *)

    (* NOTE use the switcher's return functional spec *)

  Qed.

End DLE.
