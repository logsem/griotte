From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import fetch assert.

Section CMDC_Main.
  Context `{MP: MachineParameters}.

  (* Expect:
     pc := (RX, Global, b_main, e_main, b_main_code )

     b_main + 0 : WCap E_XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WCap E_RX b_assert e_assert a_assert
     b_main + 2 : WSealed ot_switcher B.f
     b_main + 3 : WSealed ot_switcher C.g

   *)
  Definition cmdc_main_code : list Word :=
    encodeInstrsW [
      (* #"main_b_code"; *)

      (* set b <- 0 *)
      Store cgp 0%Z;
      Mov ca0 cgp;

      (* set c <- 0 *)
      Lea cgp 1%Z;
      Store cgp 0%Z;

      (* call B.f b *)
      GetA ct0 ca0;
      Add ct1 ct0 1%Z;
      Subseg ca0 ct0 ct1 (* ca0 -> b *)
    ]
    ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 2 cs0 ct0 ct1 (* cs0 -> {B.f}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ctp;
      (* assert c == 0 *)
      Load ct0 cgp; (* ct0 -> c *)
      Mov ct1 0%Z
    ]
    ++ assert_instrs 1 ct2 ct3 ct4 ct0 ct1 (* asserts that ( *ct0 = *ct1 ) *)
    ++
    encodeInstrsW [
      (* prepare for later *)
      Mov ca0 cgp;
      Mov ca1 0%Z; (* erase returned values from the call *)

      (* set b <- 42 *)
      Lea cgp (-1)%Z;
      Store cgp 42%Z;

      (* call C.g c *)
      GetA ct0 ca0;
      Add ct1 ct0 1%Z;
      Subseg ca0 ct0 ct1 (* ca0 -> c *)
    ]
    ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 3 cs0 ct0 ct1 (* cs0 -> {C.g}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ctp;
      (* assert b == 42 *)
      Load ct0 cgp; (* ct0 -> c *)
      Mov ct1 42%Z
    ]
    ++ assert_instrs 1 ct2 ct3 ct4 ct0 ct1 (* asserts that ( *ct0 = *ct1 ) *)
    ++ encodeInstrsW [
      Halt
      (* #"main_e" *)
    ].

  Definition cmdc_main_data : list Word := [WInt 0; WInt 0].

  Definition cmdc_main_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_f C_g : Sealable) : list Word :=
    [
      WCap E_XSRW_ Global b_switcher e_switcher a_cc_switcher;
      WCap E_RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f;
      WSealed ot_switcher C_g
    ].

End CMDC_Main.

From cap_machine Require Import logrel rules proofmode.
From cap_machine Require Import fetch assert switcher_spec.

Section CMDC.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.
  Context {B C : CmptName}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).

  Ltac iHide0 irisH coqH :=
    let coqH := fresh coqH in
    match goal with
    | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
        set (coqH := prop)
    end.

  Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
    iHide0 irisH coqH.

  Lemma cmdc_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr) (a_flag : Addr)
    (B_f C_g : Sealable)

    (W_init : WORLD)

    (φ : language.val cap_lang -> iProp Σ)
    (Nassert Nswitcher : namespace)
    (E : coPset)
    :

    let imports :=
     cmdc_main_imports b_switcher e_switcher a_cc_switcher ot_switcher b_assert e_assert B_f C_g
    in

    ↑Nswitcher ⊆ E ->
    ↑Nassert ⊆ E ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ dom rmap -> rmap !! r = Some (WInt 0) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->

    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (
      na_inv logrel_nais Nassert (assert_inv ct3 ct0 ct1 b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_cc_switcher ot_switcher)
      ∗ na_own logrel_nais E

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a cmdc_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ cmdc_main_data ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ region_addrs_zeroes csp_b csp_e ]]

      ∗ region W_init B ∗ sts_full_world W_init B
      ∗ region W_init C ∗ sts_full_world W_init C

      ∗ interp W_init B (WSealed ot_switcher B_f)
      ∗ interp W_init C (WSealed ot_switcher C_g)

      ∗ ▷ (
            na_own logrel_nais E

            (* final register file*)
            ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
            ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
            ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
            ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

            (* final memory layout *)
            ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
            ∗ codefrag pc_a cmdc_main_code
            ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ cmdc_main_data ]]
            ∗ [[ csp_b , csp_e ]] ↦ₐ [[ region_addrs_zeroes csp_b csp_e ]]
              -∗ WP Seq (Instr Executable) {{ φ }})
      ⊢ WP Seq (Instr Executable) {{ φ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcherE HNassertE Hrmap_dom Hrmap_init HsubBounds Hcgp_contiguous Himports_contiguous)
      "(#Hassert & #Hswitcher & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Himports_main & Hcode_main & Hcgp_main & Hcsp_stk
      & HWreg_B & HWstd_full_B
      & HWreg_C & HWstd_full_C
      & #Hinterp_Winit_B_f & #Hinterp_Winit_C_g
      & Hφ)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    (* TODO tactic for extracting register.... *)
    (* --- Extract registers ca0 ctp ct0 ct1 cs0 cs1 cra --- *)
    assert ( rmap !! ca0 = Some (WInt 0) ) as Hwca0.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ctp = Some (WInt 0) ) as Hwctp.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct0 = Some (WInt 0) ) as Hwct0.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ct1 = Some (WInt 0) ) as Hwct1.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! cs0 = Some (WInt 0) ) as Hwcs0.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! cs1 = Some (WInt 0) ) as Hwcs1.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! cra = Some (WInt 0) ) as Hwcra.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.

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

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { solve_addr. }
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

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hcs0 $Hct0 $Hct1 $Hcode $Himport_B_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcs0 & Hct0 & Hct1 & Hcode & Himport_B_f)".
    iEval (cbn) in "Hcs0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* ---- call B ---- *)
    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".

    (* -- separate argument registers -- *)
    assert ( rmap !! ca1 = Some (WInt 0) ) as Hwca1.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ca2 = Some (WInt 0) ) as Hwca2.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ca3 = Some (WInt 0) ) as Hwca3.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ca4 = Some (WInt 0) ) as Hwca4.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert ( rmap !! ca5 = Some (WInt 0) ) as Hwca5.
    { apply Hrmap_init. rewrite Hrmap_dom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.

    set ( rmap_arg :=
           {[ ca0 := WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b;
              ca1 := WInt 0;
              ca2 := WInt 0;
              ca3 := WInt 0;
              ca4 := WInt 0;
              ca5 := WInt 0;
              ct0 := WInt 0
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      repeat (iApply big_sepM_insert; [done|iFrame]).
      done.
    }

    (* TODO update Winit into W1, such that W(B)(b) = Permanent *)

    (* iApply (wp_wand with "[-]"). *)
    (* iApply (switcher_cc_specification with *)
    (*          "[- $Hswitcher $Hna *)
    (*           $HPC $Hcgp $Hcra $Hcsp $Hcs0 $Hcs1 $Hrmap_arg $Hrmap *)
    (*           $Hcsp_stk $HWreg_B $HWstd_full_B]"); auto. *)
    (* { admit. } *)
    (* { admit. } *)
    (* { admit. } *)


    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
  Admitted.
End CMDC.
