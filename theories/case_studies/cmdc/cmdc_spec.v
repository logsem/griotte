From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call cmdc.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte Require Import cmdc_spec_helper.

Section CMDC.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {B C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.


  Lemma cmdc_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (φ : language.val griotte_lang -> iProp Σ)
    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := cmdc_main_imports B_f C_g in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (WInt 0) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init_B) ->
    (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    (* We suppose that the stack region is already revoked in each worlds.
       It's because the worlds are closed and if they we're Temporary,
       then the points-to predicates would be own by both `world_interp` at the same time,
       which is not possible. *)
    revoked_addresses W_init_B (finz.seq_between csp_b csp_e) ->
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->

    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a cmdc_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ cmdc_main_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ world_interp W_init_B B
      ∗ world_interp W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_B B (WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g)

      ∗ (WSealed ot_switcher B_f) ↦□ₑ cmdc_B_f_args
      ∗ (WSealed ot_switcher C_g) ↦□ₑ cmdc_C_g_args

      (* initial stack are revoked in both worlds *)
      ∗ StackRevokedResources W_init_B B (finz.seq_between csp_b csp_e)
      ∗ StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e)

      ∗ ▷ (na_own cerise_nais ⊤
              -∗ WP Instr Halted {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_c
               Hrevoked_stack_B Hrevoked_stack_C)
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_interp_B
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & #HentryB_f & #HentryC_g
      & Hstack_revoked_B & Hstack_revoked_C
      & Hφ)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.
    iDestruct (big_sepL2_length with "Hcsp_stk") as "%Hlen_stack".

    (* Extract the needed registers from the register map *)
    iExtractList "Hrmap" [ca0;ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hca0";"Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].

    (* Extract the addresses of b and c *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_c _]".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_B_f Himports_main]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_g _]".
    { transitivity (Some (pc_b ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { solve_addr. }
    iHide "Hφ" as hφ.
    (* Mov ca0 cgp; *)
    iInstr "Hcode".
    (* Lea cgp 1%Z; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { solve_addr. }
    (* GetA ct0 ca0; *)
    iInstr "Hcode".
    (* Add ct1 ct0 1%Z; *)
    iInstr "Hcode".
    (* Subseg ca0 ct0 ct1  *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_B_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_B_f)".
    iEval (cbn) in "Hcs0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".


    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    (* ---- call B ---- *)
    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".


    (* The call helper starts after [Jalr]. The caller proves separation of
       [shared_addr] here because it owns both pointsto predicates.
       [cmdc_call_adv_block_spec] then relinquishes [shared_addr] into the
       world, replacing its direct pointsto ownership with a permanent shared
       relation while it performs the switcher protocol. Here [shared_addr] is
       instantiated with [cgp_b]. *)
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hcgp_b]") as "%Hcgp_b_stk".
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5] as ["Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].
    iInsertList "Hrmap" [ctp].
    repeat (rewrite -delete_insert_ne //).
    set (rmap_call_B := (delete ca5 _)).
    iEval (cbn) in "Hct1".
    iApply (cmdc_call_adv_block_spec
      Nswitcher W_init_B B cgp_b (cgp_b ^+ 1)%a B_f with
      "[- $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1
       $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hct0 $Hrmap
       $Hcgp_b $Hcsp_stk $Hworld_interp_B $Hstack_revoked_B
       $Hcstk_frag $HK $Hinterp_Winit_B_f $HentryB_f]").
    { solve_addr. }
    { exact Hcgp_b. }
    { exact Hcgp_b_stk. }
    { exact Hrevoked_stack_B. }
    { solve_addr. }
    { subst rmap_call_B.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hrmap_dom; set_solver.
    }

    iNext. subst rmap_call_B.
    iIntros (W2_B rmap' stk_mem l)
      "( _ & _ & _ & _ & _
      & %HW2_B_cgp_b & #Hrel_cgp_b & %Hdom_rmap' & Hstack_revoked_B & _
      & Hna & %Hcsp_bounds
      & Hworld_interp_B
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)" ; clear l.
    iEval (cbn) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".

    (* ---- extract the needed registers ----  *)
    iExtractList "Hrmap" [ctp;ct0;ct1;ct2;ct3;ct4;cnull]
      as ["Hctp";"Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hcnull"].

    (* Load ct0 cgp  *)
    iInstr "Hcode".
    { split; [done| solve_addr]. }
    (* Mov ct1 0  *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 4: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_assert_c Ha_assert_c "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* --------------- BLOCK 5: PREP CALL ---------------- *)
    (* --------------------------------------------------- *)

    set (cgp_c := (cgp_b ^+ 1)%a).
    focus_block 5 "Hcode_main" as a_prepC Ha_prepC "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov ca0 cgp  *)
    iInstr "Hcode".
    (* Mov ca1 0  *)
    iInstr "Hcode".
    (* Lea cgp (-1)%Z *)
    iInstr "Hcode".
    { transitivity (Some cgp_b%a); auto; subst cgp_c; solve_addr. }

    rewrite (open_world_interp_empty _ B).
    iDestruct (
       open_world_interp_permanent with "[$Hworld_interp_B] [$Hrel_cgp_b]"
      ) as "(Hworld_interp_B & Hstd_cgp_b & [%v Hcgp_b] )"; auto.
    { set_solver+. }
    iEval (cbn) in "Hcgp_b".
    iDestruct (PermRes_acc with "Hcgp_b") as "[ (>Hcgp_b & Hcgp_b_interp) Hcgp_b_close]".

    (* Store cgp 42%Z *)
    iInstr "Hcode".
    { solve_addr. }

    (* GetA ct0 ca0 *)
    iInstr "Hcode".

    (* Add ct1 ct0 1%Z *)
    iInstr "Hcode".

    (* Subseg ca0 ct0 ct1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_c ^+1)%a); auto; subst cgp_c; solve_addr. }
    { subst cgp_c; solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 6 and 7: FETCH --------------- *)
    (* --------------------------------------------------- *)

    focus_block 6 "Hcode_main" as a_fetch3 Ha_fetch3 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 7 "Hcode_main" as a_fetch4 Ha_fetch4 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_C_g]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcs0 & Hct0 & Hct1 & Hcode & Himport_C_g)".
    iEval (cbn) in "Hcs0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ---------------- BLOCK 8: CALL C ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 8 "Hcode_main" as a_callC Ha_callC "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".

    (* As for call B, the caller establishes separation first. Then
       [cmdc_call_adv_block_spec] relinquishes [shared_addr] into the world,
       replacing direct pointsto ownership with a permanent shared relation;
       here [shared_addr] is instantiated with [cgp_c]. *)
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_c]") as "%Hcgp_c_stk".
    clear wca0 wca1 wca2 wca3 wca4 wca5.
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as ["Hca2";"Hca3";"Hca4";"Hca5"].
    iInsertList "Hrmap" [cnull;ct4;ct3;ct2;ctp].
    repeat (rewrite -delete_insert_ne //).
    set (rmap_call_C := (delete ca5 _)).

    iApply (cmdc_call_adv_block_spec
      Nswitcher W_init_C C cgp_c (cgp_c ^+ 1)%a C_g with
      "[- $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1
       $Hca0 $Hca1 $Hca2 $Hca3 $Hca4 $Hca5 $Hct0 $Hrmap
       $Hcgp_c $Hstk $Hworld_interp_C $Hstack_revoked_C
       $Hcstk_frag $HK $Hinterp_Winit_C_g $HentryC_g]").
    { subst cgp_c. solve_addr. }
    { subst cgp_c. exact Hcgp_c. }
    { exact Hcgp_c_stk. }
    { exact Hrevoked_stack_C. }
    { solve_addr. }
    { subst rmap_call_C.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite Hdom_rmap'; set_solver.
    }

    iNext. subst rmap_call_C. clear dependent stk_mem.
    iIntros (W4_C rmap'' stk_mem l)
      "( _ & _ & _ & _ & _ & _ & _
      & %Hdom_rmap'' & Hstack_revoked_C & _
      & Hna & _
      & Hworld_interp_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg'0 [Hca0 _] ] & [%warg1' [Hca1 _] ]
      & Hrmap & Hstk & HK)" ; clear l.
    iEval (cbn) in "HPC".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".

    (* ---- extract the needed registers ----  *)
    clear wctp wct0 wct1 wct2 wct3 wct4 wcnull.
    iExtractList "Hrmap" [ctp;ct0;ct1;ct2;ct3;ct4;cnull]
      as ["Hctp";"Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hcnull"].

    (* Load ct0 cgp  *)
    iInstr "Hcode".
    { split; [done| solve_addr]. }
    (* Mov ct1 42  *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 9: ASSERT ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 9 "Hcode_main" as a_assert_b Ha_assert_b "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hcra $Hct0 $Hct1 $Hcnull
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 10: HALT ------------------ *)
    (* --------------------------------------------------- *)

    focus_block 10 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    subst hφ; iApply ("Hφ" with "[$]").
  Qed.

  Lemma cmdc_spec_full

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (B_f C_g : Sealable)

    (W_init_B : WORLD)
    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (csp_content : list Word)

    (φ : language.val griotte_lang -> iProp Σ)
    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := cmdc_main_imports B_f C_g in

    Nswitcher ## Nassert ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (WInt 0) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init_B) ->
    (cgp_b ^+ 1)%a ∉ dom (std W_init_C) ->

    revoked_addresses W_init_B (finz.seq_between csp_b csp_e) ->
    revoked_addresses W_init_C (finz.seq_between csp_b csp_e) ->

    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a cmdc_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ cmdc_main_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ csp_content ]]

      ∗ world_interp W_init_B B
      ∗ world_interp W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_B B (WSealed ot_switcher B_f)
      ∗ interp W_init_C C (WSealed ot_switcher C_g)

      ∗ (WSealed ot_switcher B_f) ↦□ₑ cmdc_B_f_args
      ∗ (WSealed ot_switcher C_g) ↦□ₑ cmdc_C_g_args

      (* initial stack are revoked in both worlds *)
      ∗ StackRevokedResources W_init_B B (finz.seq_between csp_b csp_e)
      ∗ StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e)

      ∗ ▷ ( na_own cerise_nais ⊤
              -∗ WP Instr Halted {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
      ⊢ WP Seq (Instr Executable) {{ λ v, True }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hcgp_c
               Hrevoked_stack_B Hrevoked_stack_C)
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & Hworld_interp_B
      & Hworld_interp_C
      & HK
      & Hcstk_frag
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & #HentryB_f & #HentryC_g
      & Hstack_revoked_B & Hstack_revoked_C
      & Hφ)".
    iApply (wp_wand with "[-]").
    { iApply (cmdc_spec
                pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e rmap
                B_f C_g W_init_B W_init_C
               Ws Cs csp_content φ Nassert Nswitcher cstk); eauto; iFrame "#∗".
    }
    by iIntros (v) "?".
  Qed.

End CMDC.
