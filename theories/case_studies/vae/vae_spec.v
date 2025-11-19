From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.
From cap_machine Require Import rules logrel logrel_extra monotone proofmode register_tactics.
From cap_machine Require Import fetch assert switcher_spec_call vae.
From cap_machine Require Import fetch assert vae.

Section VAE.
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

  Definition awk_inv C i a :=
    (∃ x:bool, sts_state_loc (A:=Addr) C i x
            ∗ if x
              then a ↦ₐ WInt 1%Z
              else a ↦ₐ WInt 0%Z)%I.

  Definition awk_rel_pub := λ a b, a = false ∨ b = true.
  Definition awk_rel_priv := λ (a b : bool), True.

  Lemma vae_awkward_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)
    (g_vae_exp_tbl : Locality)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nvae VAEN : namespace)
    i

    :

    let imports :=
     vae_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
       b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+2)%a
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae ->
    Nassert ## Nvae ->
    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nvae
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a (vae_main_code ot_switcher))
    ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (switcher.encode_entry_point 1 (length VAE_main_code_init)))
    ∗ interp W C (WSealed ot_switcher C_f)
    ∗ WSealed ot_switcher C_f ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ seal_pred ot_switcher ot_switcher_propC
    (* invariant for d *)
    ∗ (∃ ι, inv ι (awk_inv C i cgp_b))
    ∗ sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_pub awk_rel_priv
      -∗
    ot_switcher_prop W C (WCap RO g_vae_exp_tbl b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a).
  Proof.
    intros imports; subst imports.
    iIntros (Hswitcher_assert HNswitcher_vae HNassert_vae Hvae_size)
      "(#Hassert & #Hswitcher
      & #Hvae_code
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & #Hvae_exp_awkward
      & #Hinterp_W0_C_f
      & #HentryC_f & #Hentry_VAE & #Hot_switcher
      & [%ι #Hι] & #Hsts_rel)".
    iExists g_vae_exp_tbl, b_vae_exp_tbl, e_vae_exp_tbl, (b_vae_exp_tbl ^+ 2)%a,
    pc_b, pc_e, cgp_b, cgp_e, 1, (length VAE_main_code_init), VAEN.
    iFrame "#".
    iSplit; first done.
    iSplit; first solve_addr.
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; solve_addr).
    iSplit; first (iPureIntro; lia).
    iIntros "!> %regs %cstk %Ws %Cs %W' %Hpriv_W_W' !> %a_stk %e_stk".
    iIntros "(HK & %Hframe_cstk & (Hrmap_full & Hregs & Hreg & Hsts & %Hcsp_sync & Hcstk & Hna))".
  Admitted.

  Lemma vae_awkward_safe

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W : WORLD)

    (Nassert Nswitcher Nvae VAEN : namespace)
    i

    :

    let imports :=
     vae_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
       b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+2)%a
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae ->
    Nassert ## Nvae ->
    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->

    na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
    ∗ na_inv logrel_nais Nswitcher switcher_inv
    ∗ na_inv logrel_nais Nvae
        ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a (vae_main_code ot_switcher))
    ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
    ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
    ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
        ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (switcher.encode_entry_point 1 (length VAE_main_code_init)))
    ∗ interp W C (WSealed ot_switcher C_f)
    ∗ WSealed ot_switcher C_f ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ WSealed ot_switcher (SCap RO Local b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)
        ↦□ₑ 1
    ∗ seal_pred ot_switcher ot_switcher_propC
    ∗ (∃ ι, inv ι (awk_inv C i cgp_b))
    ∗ sts_rel_loc (A:=Addr) C i awk_rel_pub awk_rel_pub awk_rel_priv
      -∗
    interp W C
      (WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a)).
  Proof.
    intros imports; subst imports.
    iIntros (Hswitcher_assert HNswitcher_vae HNassert_vae Hvae_size)
      "(#Hassert & #Hswitcher
      & #Hvae_code
      & #Hvae_exp_PCC
      & #Hvae_exp_CGP
      & #Hvae_exp_awkward
      & #Hinterp_W0_C_f
      & #HentryC_f & #Hentry_VAE & #Hentry_VAE' & #Hot_switcher
      & [%ι #Hι] & #Hsts_rel)".
    iEval (rewrite fixpoint_interp1_eq /=).
    rewrite /interp_sb.
    iFrame "Hot_switcher".
    iSplit; [iPureIntro; apply persistent_cond_ot_switcher |].
    iSplit; [iIntros (w); iApply mono_priv_ot_switcher|].
    iSplit; iNext ; iApply vae_awkward_spec; try iFrame "HentryC_f #"; eauto.
  Qed.

  Lemma vae_init_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (b_vae_exp_tbl e_vae_exp_tbl : Addr)

    (b_assert e_assert : Addr) (a_flag : Addr)
    (C_f : Sealable)

    (W0 : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher Nvae_code VAEN : namespace)

    (cstk : CSTK)
    :

    let imports :=
     vae_main_imports
       b_switcher e_switcher a_switcher_call ot_switcher b_assert e_assert C_f
       b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+2)%a
    in

    Nswitcher ## Nassert ->
    Nswitcher ## Nvae_code ->
    Nassert ## Nvae_code ->

    (b_vae_exp_tbl <= b_vae_exp_tbl ^+ 2 < e_vae_exp_tbl)%a ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (vae_main_code ot_switcher))%a ->

    (cgp_b + length vae_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W0) ->

    frame_match Ws Cs cstk W0 C ->
    (
      na_inv logrel_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ na_inv logrel_nais Nswitcher switcher_inv
      ∗ na_inv logrel_nais Nvae_code
          ([[ pc_b , pc_a ]] ↦ₐ [[ imports ]] ∗ codefrag pc_a (vae_main_code ot_switcher))
      ∗ inv (export_table_PCCN VAEN) (b_vae_exp_tbl ↦ₐ WCap RX Global pc_b pc_e pc_b)
      ∗ inv (export_table_CGPN VAEN) ((b_vae_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global cgp_b cgp_e cgp_b)
      ∗ inv (export_table_entryN VAEN (b_vae_exp_tbl ^+ 2)%a)
          ((b_vae_exp_tbl ^+ 2)%a ↦ₐ WInt (switcher.encode_entry_point 1 (length VAE_main_code_init)))
      ∗ na_own logrel_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* initial memory layout *)
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ vae_main_data ]]

      ∗ region W0 C ∗ sts_full_world W0 C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W0 C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W0 C (WCap RWL Local csp_b csp_e csp_b)

      ∗ WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a) ↦□ₑ 1
      ∗ WSealed ot_switcher (SCap RO Local b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a) ↦□ₑ 1
      ∗ seal_pred ot_switcher ot_switcher_propC

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (HNswitcher_assert HNswitcher_vae HNassert_vae Hsize_vae_exp_tbl Hrmap_dom Hrmap_init HsubBounds
               Hcgp_contiguous Himports_contiguous Hcgp_b Hframe_match
            )
      "(#Hassert & #Hswitcher
      & #Hvae
      & #Hvae_exp_tbl_PCC
      & #Hvae_exp_tbl_CGP
      & #Hvae_exp_tbl_awkward
      & Hna
      & HPC & Hcgp & Hcsp & Hrmap
      & Hcgp_main
      & Hr_C & Hsts_C
      & HK
      & Hcstk_frag
      & #Hinterp_W0_C_f
      & #HentryC_f
      & #Hinterp_W0_csp
      & #Hentry_awkward & #Hentry_awkward'
      & #Hot_switcher
      )".
    iMod (na_inv_acc with "Hvae Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hvae_close)"; auto.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.
    (* --- Extract registers ca0 ct0 ct1 ct2 ct3 cs0 cs1 --- *)
    iExtractList "Hrmap" [cra;ca0;ct0;ct1;ct2;ct3;cs0;cs1]
      as ["Hcra"; "Hca0"; "Hct0"; "Hct1"; "Hct2"; "Hct3"; "Hcs0"; "Hcs1"].

    (* Extract the addresses of a *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hcgp_b Hcgp_main]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

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
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_VAE_awkward Himports_main]".
    { transitivity (Some (pc_b ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }

    (* Revoke the world to get the stack frame *)
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l) "(%Hl_unk & Hsts_C & Hr_C & Hfrm_close_W0 & >[%stk_mem Hstk] & Hrevoked_l)".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Hcgp_b]") as "%Hcgp_b_stk".
    set (W1 := revoke W0).

    (* --------------------------------------------------------------- *)
    (* ----------------- Start the proof of the code ----------------- *)
    (* --------------------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 0 : INIT ------------------ *)
    (* --------------------------------------------------- *)
    rewrite /vae_main_code /VAE_main_code_init.
    replace
     ((encodeInstrsW [Store cgp 0] ++
                     fetch_instrs 3 ca0 cs0 cs1 ++
                     fetch_instrs 0 ct0 cs0 cs1 ++
                     fetch_instrs 2 ct1 cs0 cs1 ++ encodeInstrsW [Jalr cra ct0; Halt]) ++
                    VAE_main_code_f ot_switcher)
       with
      (encodeInstrsW [Store cgp 0] ++
                     fetch_instrs 3 ca0 cs0 cs1 ++
                     fetch_instrs 0 ct0 cs0 cs1 ++
                     fetch_instrs 2 ct1 cs0 cs1 ++ encodeInstrsW [Jalr cra ct0; Halt] ++
                    VAE_main_code_f ot_switcher) by auto.
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.

    (* Store cgp 0%Z; *)
    iInstr "Hcode".
    { solve_addr. }

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 to 3 : FETCH --------------- *)
    (* --------------------------------------------------- *)

    focus_block 1 "Hcode_main" as a_fetch1 Ha_fetch1 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hca0 $Hcs0 $Hcs1 $Hcode $Himport_VAE_awkward]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hca0 & Hcs0 & Hcs1 & Hcode & Himport_VAE_awkward)".
    iEval (cbn) in "Hca0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch1.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hcs0 $Hcs1 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext ; iIntros "(HPC & Hct0 & Hcs0 & Hcs1 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    focus_block 3 "Hcode_main" as a_fetch3 Ha_fetch3 "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch2.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcs0 $Hcs1 $Hcode $Himport_C_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(HPC & Hct1 & Hcs0 & Hcs1 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    focus_block 4 "Hcode_main" as a_callB Ha_callB "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent a_fetch3.
    (* Jalr cra ct0; *)
    iInstr "Hcode".


    (*  -- prove that the VAE_awkward entry point is safe-to-share -- *)

    (* -- separate argument registers -- *)
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5]
      as ["Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"].

    set ( rmap_arg :=
           {[ ca0 :=
                WSealed ot_switcher
                (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a);
              ca1 := wca1;
              ca2 := wca2;
              ca3 := wca3;
              ca4 := wca4;
              ca5 := wca5;
              ct0 := WSentry XSRW_ Local b_switcher e_switcher a_switcher_call
           ]} : Reg
        ).

    iInsertList "Hrmap" [ct2;ct3].
    repeat (iEval (rewrite -delete_insert_ne //) in "Hrmap").
    set (rmap' := (delete ca5 _)).

    pose proof (revoke_related_sts_priv_world W0) as Hpriv_W0_W1.
    (* Show that the entry point to C_f is still safe in W1 *)
    iAssert (interp W1 C (WSealed ot_switcher C_f)) as "#Hinterp_W1_C_f".
    { iApply interp_monotone_sd; eauto. }
    iClear "Hinterp_W0_C_f".

    (* TODO alloc the invariant in the custom world *)
    (* Show that the arguments are safe, when necessary *)
    iAssert (
        interp W1 C
          (WSealed ot_switcher (SCap RO Global b_vae_exp_tbl e_vae_exp_tbl (b_vae_exp_tbl ^+ 2)%a))
      )%I as "#Hinterp_VAE".
    { iApply (vae_awkward_safe pc_b pc_e pc_a cgp_b cgp_e b_vae_exp_tbl e_vae_exp_tbl b_assert
                e_assert a_flag C_f W1); try iFrame "#"; eauto.
    }

    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg
                                           ∗ (if decide (rarg ∈ dom_arg_rmap 1)
                                             then interp W1 C warg
                                             else True)
            )%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      iAssert (interp W1 C (WInt 0)) as "Hinterp_0"; first iApply interp_int.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done.
    }

    (* Prepare the closing resources for the switcher call spec *)
    iAssert (
        ([∗ list] a ∈ finz.seq_between csp_b csp_e, closing_revoked_resources W1 C a ∗
                                                    ⌜W1.1 !! a = Some Revoked⌝)
      )%I with "[Hfrm_close_W0]" as "#Hfrm_close_W1".
    {
      iApply (big_sepL_impl with "Hfrm_close_W0").
      iModIntro; iIntros (k a Ha) "[Hclose %Hrev]".
      iDestruct (mono_priv_closing_revoked_resources with "Hclose") as "$"; auto.
    }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    iMod ("Hvae_close" with "[$Hna Himport_assert Himport_switcher Himport_C_f Himport_VAE_awkward Himports_main $Hcode_main]")
      as "Hna".
    { iNext.
      iDestruct (region_pointsto_cons with "[$Himport_VAE_awkward $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_C_f $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_assert $Himports_main]") as "Himports_main"
      ; [solve_addr|solve_addr|].
      iDestruct (region_pointsto_cons with "[$Himport_switcher $Himports_main]") as "$" ;solve_addr.
    }

    (* Apply the spec switcher call *)
    iApply (switcher_cc_specification with
             "[- $Hswitcher $Hna
              $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
              $Hstk $Hr_C $Hsts_C $Hfrm_close_W1 $Hcstk_frag
              $Hinterp_W1_C_f $HentryC_f $HK]"); eauto.
    { subst rmap'.
      repeat (rewrite dom_delete_L); repeat (rewrite dom_insert_L).
      rewrite /dom_arg_rmap Hrmap_dom.
      set_solver+.
    }
    { by rewrite /is_arg_rmap. }

    clear dependent wca0 wct0 wct1 wct2 wct3 wcs0 wcs1.
    clear dependent wca1 wca2 wca3 wca4 wca5 rmap.
    iNext.
    iIntros (W2 rmap stk_mem_l stk_mem_h)
      "(%Hrelated_pub_W3ext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds
      & Hsts_C & Hr_C & Hfrm_close_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 _] ] & [%warg1 [Hca1 _] ]
      & Hrmap & Hstk_l & Hstk_h & HK)".
    iEval (cbn) in "HPC".

    (* Halt *)
    iMod (na_inv_acc with "Hvae Hna")
      as "(( >Himports_main & >Hcode_main) & Hna & Hvae_close)"; auto.
    rewrite /vae_main_code /VAE_main_code_init.
    replace
     (encodeInstrsW [Store cgp 0] ++
                     fetch_instrs 3 ca0 cs0 cs1 ++
                     fetch_instrs 0 ct0 cs0 cs1 ++
                     fetch_instrs 2 ct1 cs0 cs1 ++ encodeInstrsW [Jalr cra ct0; Halt] ++
                    VAE_main_code_f ot_switcher)
       with
      (encodeInstrsW [Store cgp 0] ++
                     fetch_instrs 3 ca0 cs0 cs1 ++
                     fetch_instrs 0 ct0 cs0 cs1 ++
                     fetch_instrs 2 ct1 cs0 cs1
                     ++ encodeInstrsW [Jalr cra ct0 ]
                     ++ encodeInstrsW [Halt]
                     ++ VAE_main_code_f ot_switcher) by auto.
    focus_block 5 "Hcode_main" as a_callB' Ha_callB' "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iMod ("Hvae_close" with "[$Hna $Himports_main $Hcode_main]") as "Hna".
    wp_end; iIntros "_"; iFrame.
  Qed.

End VAE.
