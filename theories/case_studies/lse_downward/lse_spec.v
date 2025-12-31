From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import rules logrel logrel_extra monotone proofmode register_tactics.
From cap_machine Require Import fetch_spec assert_spec switcher switcher_spec_call.
From cap_machine Require Import lse lse_spec_closure.
From cap_machine Require Import proofmode.

Section LSE.
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

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma lse_run_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_lse_exp_tbl e_lse_exp_tbl : Addr)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher Nlse_code LSEN : namespace)

    (cstk : CSTK)
    :

    let imports :=
     lse_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nlse_code ->
    Nassert ## Nlse_code ->

    (b_lse_exp_tbl <= b_lse_exp_tbl ^+ 2 < e_lse_exp_tbl)%a ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length lse_main_code)%a ->

    (cgp_b + length lse_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    frame_match Ws Cs cstk W0 C ->
    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher switcher_inv
      ∗ na_inv logrel_nais LSEN
          ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
           ∗ codefrag pc_a lse_main_code
           ∗ cgp_b ↦ₐ WInt 2
          )
      ∗ inv (export_table_PCCN LSEN) (b_lse_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
      ∗ inv (export_table_CGPN LSEN) ((b_lse_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
      ∗ inv (export_table_entryN LSEN (b_lse_exp_tbl ^+ 2)%a)
          ((b_lse_exp_tbl ^+ 2)%a ↦ₐ lse_exp_tbl_entry_f)
      ∗ na_own logrel_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ region W0 C ∗ sts_full_world W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 0
      ∗ interp W0 C (WCap RWL Local csp_b csp_e csp_b)

      ∗ WSealed ot_switcher (SCap RO Global b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+ 2)%a) ↦□ₑ 0
      ∗ WSealed ot_switcher (SCap RO Local b_lse_exp_tbl e_lse_exp_tbl (b_lse_exp_tbl ^+ 2)%a) ↦□ₑ 0
      ∗ seal_pred ot_switcher ot_switcher_propC

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert HNswitcher_lse HNassert_lse Hsize_lse_exp_tbl Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hframe_match
            )
      "(#Hassert & #Hswitcher
      & #Hlse
      & #Hlse_exp_tbl_PCC
      & #Hlse_exp_tbl_CGP
      & #Hlse_exp_tbl_awkward
      & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Hr_C & Hsts_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      & #Hentry_f & #Hentry_f'
      & #Hot_switcher
      )".
    iMod (na_inv_acc with "Hlse Hna")
      as "(( >Himports_main & >Hcode_main & >Hcgp_b) & Hna & Hlse_close)"; auto.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.
    (* --- Extract registers ca0 ct0 ct1 ct2 ct3 cs0 cs1 --- *)
    iExtractList "Hrmap" [cra;ct0;ct1;cs0;cs1]
      as ["Hcra"; "Hct0"; "Hct1"; "Hcs0"; "Hcs1"].

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_assert Himports_main]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_C_f Himports_main]".
    { transitivity (Some (pc_b ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }

    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l
           ) "(%Hl_unk & Hsts_C & Hr_C & Hfrm_close_W0 & >%Hrevoked_W0 & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".
    set (W1 := revoke W0).

    (* --------------------------------------------------------------- *)
    (* ----------------- Start the proof of the code ----------------- *)
    (* --------------------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)
    rewrite /lse_main_code /LSE_main_code_run.
    rewrite -!app_assoc.
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.

    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { apply withinBounds_true_iff; solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 to 3 : FETCH --------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcs0 $Hcs1 $Hcode $Himport_C_f]"); eauto.
    { apply withinBounds_true_iff; solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hcs0 & Hcs1 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 3 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch2.
    (* Jalr cra ct0; *)
    iInstr "Hcode".


    (*  -- prove that the LSE_awkward entry point is safe-to-share -- *)

    (* -- separate argument registers -- *)
    iExtractList "Hrmap" [ca0;ca1;ca2;ca3;ca4;ca5]
      as ["Hca0"; "Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"].

    set ( rmap_arg :=
           {[ ca0 := wca0;
              ca1 := wca1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    set (rmap' := (delete ca5 _)).

    pose proof (revoke_related_sts_priv_world W0) as Hpriv_W0_W1.

    (* Show that the entry point to C_f is still safe in W1 *)
    iAssert (interp W1 C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply interp_monotone_sd; eauto. }
    iClear "Hinterp_W0_C_f".

    (* Show that the arguments are safe, when necessary *)
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 0)
                                             then interp W1 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    (* Prepare the closing resources for the switcher call spec *)
    iAssert (
        ([∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W1 C a)
      )%I with "[Hfrm_close_W0]" as "#Hfrm_close_W1".
    {
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a Ha) "Hclose".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hlse_close" with
           "[$Hna Himport_assert Himport_switcher Himport_C_f Himports_main $Hcode_main $Hcgp_b]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_C_f $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $HentryC_f $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W1 $Hcstk_frag
              $Hinterp_W1_C_f $HK]"); eauto; iFrame "%".
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    clear dependent wct0 wct1 wcs0 wcs1.
    clear dependent wca0 wca1 wca2 wca3 wca4 wca5 rmap.
    clear stk_mem.
    iNext.
    iIntros (W2 rmap stk_mem l')
      "( _ & _ & _ & %Hrelated_pub_2ext_W2 & Hrel_stk_C' & %Hdom_rmap & Hfrm_close_W2 & %Hfrm_close_W2
      & Hna & %Hcsp_bounds
      & Hsts_C & Hr_C
      & Hcstk_frag
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk & HK)"; clear l'.
    iEval (cbn) in "HPC".

    (* Halt *)
    iMod (na_inv_acc with "Hlse Hna")
      as "(( >Himports_main & >Hcode_main & >Hcgp_b) & Hna & Hlse_close)"; auto.
    replace (encodeInstrsW [Jalr cra ct0; Halt]) with
      (encodeInstrsW [Jalr cra ct0] ++ encodeInstrsW [Halt])
    by auto.
    rewrite -app_assoc.
    focus_block 4 "Hcode_main" as a_callB' Ha_callB' "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iMod ("Hlse_close" with "[$Hna $Himports_main $Hcode_main $Hcgp_b]") as "Hna".
    wp_end; iIntros "_"; iFrame.
  Qed.

End LSE.
