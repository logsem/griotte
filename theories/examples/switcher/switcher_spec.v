From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening addr_reg_sample rules proofmode.
From cap_machine Require Import switcher.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).
  Implicit Types WC : CVIEW.
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* TODO should depend on the number of registers used by entry point. *)
  Definition is_arg_rmap (rmap : Reg) :=
    dom rmap = {[ ca0 ; ca1 ; ca2 ; ca3 ; ca4 ; ca5 ; ca5 ; ct0 ]}.

  Definition switcher_inv
    (b_switcher e_switcher a_switcher_cc : Addr)
    (ot_switcher : OType) : iProp Σ :=
    ∃ (b_tstk e_tstk a_tstk : Addr) (tstk : list Word),
     mtdc ↦ₛᵣ WCap RWL Local b_tstk e_tstk a_tstk
     ∗ ⌜ SubBounds
         b_switcher e_switcher
         a_switcher_cc (a_switcher_cc ^+ length switcher_instrs)%a ⌝
     ∗ codefrag a_switcher_cc switcher_instrs
     ∗ b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher
     ∗ [[ a_tstk, e_tstk ]] ↦ₐ [[ tstk ]]
  .

  (* TODO:
     - How to encode the number of registers to pass as arguments?
       A possibility is to use a resource that encodes it.
   *)
  Lemma switcher_cc_specification
    (E : coPset) (N : namespace)
    (W0 W1 : WORLD)
    (C : CmptName)
    (g_switcher : Locality)
    (b_switcher e_switcher a_switcher_cc : Addr)
    (b_stk e_stk a_stk : Addr)
    (ot_switcher : OType)
    (wcgp_caller wcra_caller wcs1_caller : Word)
    (w_entry_point : Sealable)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (φ : val -> iPropI Σ) :

    (* cs0 must contain the target entry points, which needs to be sealed with ot_switcher *)
    let wcs0_caller := WSealed ot_switcher w_entry_point in
    (* the state of the stack before the jump  *)
    let stk_pre_jmp :=
      [wcs0_caller;wcs1_caller;wcra_caller;wcgp_caller] ++
        (region_addrs_zeroes (a_stk ^+4)%a e_stk)
    in

    is_arg_rmap arg_rmap ->
    dom rmap = all_registers_s ∖ ((dom arg_rmap) ∪ {[ PC ; cgp ; cra ; csp ; cs0 ; cs1 ]} ) ->
    ↑N ⊆ E →

    ( na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc ot_switcher)
      ∗ na_own logrel_nais E
      (* Registers *)
      ∗ PC ↦ᵣ WCap XSRW_ g_switcher b_switcher e_switcher a_switcher_cc
      ∗ cgp ↦ᵣ wcgp_caller
      ∗ cra ↦ᵣ wcra_caller
      (* Stack register *)
      ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
      (* Entry point of the target compartment *)
      ∗ cs0 ↦ᵣ wcs0_caller ∗ interp W1 C wcs0_caller
      ∗ cs1 ↦ᵣ wcs1_caller
      (* Argument registers, need to be safe-to-share *)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W1 C warg )
      (* All the other registers *)
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      (* Stack frame *)
      ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

      (* Interpretation of the world, at the moment of the switcher_call *)
      ∗ region W0 C ∗ sts_full_world W0 C

      (* Transformation of the world, before the jump to the adversary *)
      ∗ ( [[ a_stk , e_stk ]] ↦ₐ [[ stk_pre_jmp ]]
          ∗ region W0 C ∗ sts_full_world W0 C
          ==∗ region W1 C ∗ sts_full_world W1 C)

      (* POST-CONDITION *)
      ∗ ▷ ( (∃ (W2 : WORLD) (rmap' : Reg),
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world W0 W2 C ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ]} ⌝
              ∗ na_own logrel_nais E
              (* Interpretation of the world *)
              ∗ region W2 C ∗ sts_full_world W2 C
              ∗ PC ↦ᵣ updatePcPerm wcra_caller
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ a_stk , e_stk ]] ↦ₐ [[ region_addrs_zeroes a_stk e_stk ]])
            -∗ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}
          )
    )
    ⊢ (WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }})%I.
  Proof.
    intros Hwcs0_caller Hstk_pre_jmp Harg_map Hrmap HNE.
    iIntros "(#Hinv_switcher & Hna
              & HPC & Hcgp & Hcra & Hcsp & Hcs0 & #Hinterp_cs0 & Hcs1 & Hargmap & Hrmap
              & Hstk & Hregion & Hworld & Hnext_world & Hcont)".

    (* ------------------------------------------------ *)
    (* -------- Prepare resources for the proof ------- *)
    (* ------------------------------------------------ *)

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (b_tstk e_tstk a_tstk tstk) ">(Hmtdc & %Hbounds & Hcode & Hb_switcher & Htstk)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region; clear H0.

    (* --- Extract scratch registers ct2 ctp --- *)
    (* TODO *)
    assert (exists wct2, rmap !! ct2 = Some wct2) as [wct2 Hwct2].
    { admit. }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap !! ctp = Some wctp) as [wctp Hwctp].
    { admit. }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    (* ------------------------------------------------ *)
    (* ----- Start the proof of the switcher here ----- *)
    (* ------------------------------------------------ *)

    (* --- First, we destruct cases where it will quickly fail ---  *)
    destruct (decide ((a_stk ^+ 4) < e_stk))%a as [Hstk_ae|Hstk_ae]; cycle 1.
    { admit. (* will fail in the next upcoming instructions *) }
    destruct (decide (b_stk <= a_stk))%a as [Hstk_ba|Hstk_ba]; cycle 1.
    { admit. (* will fail in the next upcoming instructions *) }

    iAssert (⌜ exists stk_wa stk_wa1 stk_wa2 stk_wa3 stk_mem',
                 (stk_mem = stk_wa::stk_wa1::stk_wa2::stk_wa3::stk_mem')⌝)%I
      as %(stk_wa & stk_wa1 & stk_wa2 & stk_wa3 & stk_mem' & ->).
    { iEval (rewrite /region_pointsto) in "Hstk".
      iDestruct (big_sepL2_length with "Hstk") as %Hlen_stk.
      iPureIntro.
      assert (length (finz.seq_between a_stk e_stk) > 4) as Hlen_stk_ae.
      { rewrite finz_seq_between_length.
        assert (a_stk^+4 < e_stk)%a by solve_addr.
        do 5 (rewrite finz_dist_S; last solve_addr); lia.
      }
      destruct stk_mem as [|stk_wa stk_mem0]; first (cbn in Hlen_stk; lia).
      destruct stk_mem0 as [|stk_wa1 stk_mem1]; first (cbn in Hlen_stk; lia).
      destruct stk_mem1 as [|stk_wa2 stk_mem2]; first (cbn in Hlen_stk; lia).
      destruct stk_mem2 as [|stk_wa3 stk_mem3]; first (cbn in Hlen_stk; lia).
      destruct stk_mem3 as [|stk_wa4 stk_mem4]; first (cbn in Hlen_stk; lia).
      eexists _,_,_,_,_; done.
    }

    (* ---- store csp cs0 ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha1_stk Hstk]".
    { transitivity (Some (a_stk ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 1%Z)%a); auto;solve_addr. }

    (* ---- store csp cs1 ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha2_stk Hstk]".
    { transitivity (Some (a_stk ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 2%Z)%a); auto;solve_addr. }

    (* ---- store csp cra ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha3_stk Hstk]".
    { transitivity (Some (a_stk ^+ 3)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 3%Z)%a); auto;solve_addr. }

    (* ---- store csp cgp ---- *)
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha4_stk Hstk]".
    { transitivity (Some (a_stk ^+ 4)%a); auto; solve_addr. }
    { solve_addr. }
    iInstr "Hcode".
    { apply withinBounds_true_iff; split;solve_addr. }

    (* --- getp ct2 csp --- *)
    iInstr "Hcode".

    (* --- mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".
    replace (
        match MP with
        | {| encodePerm := encodePerm |} => encodePerm
        end
      ) with encodePerm by ( by destruct MP ).

    (* --- sub ct2 ct2 ctp --- *)
    iInstr "Hcode".
    replace ((encodePerm RWL - encodePerm RWL)%Z) with 0%Z by lia.

    (* --- jnz 2 ct2 --- *)
    iInstr "Hcode".

    (* --- jmp 2 --- *)
    iInstr "Hcode".

    (* --- readsr ct2 mtdc --- *)
    (* TODO add ReadSR and WriteSR to iInstr *)
    (* iInstr "Hcode". *)
  Admitted.

  Lemma switcher_interp (W : WORLD) (C : CmptName) (N : namespace)
    (b_switcher e_switcher a_switcher_cc : Addr) (ot_switcher : OType) :
    na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc ot_switcher) -∗
    interp W C (WCap E_XSRW_ Global b_switcher e_switcher a_switcher_cc).
  Proof.
  Admitted.

  Lemma future_priv_mono_interp_switcher (C : CmptName) (N : namespace)
    (b_switcher e_switcher a_switcher_cc : Addr) (ot_switcher : OType) :
    na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc ot_switcher) -∗
    future_priv_mono C interpC (WCap E_XSRW_ Global b_switcher e_switcher a_switcher_cc).
  Proof.
  Admitted.


End Switcher.
