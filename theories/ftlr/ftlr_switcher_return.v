From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_JmpCap.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.

Section fundamental.
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

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma switcher_return_ftlr (W : WORLD) (C : CmptName) (rmap : leibnizO Reg)
    (cstk : CSTK) (wstk : Word)
    (Nswitcher : namespace)
    :
    (∀ x, is_Some (rmap !! x)) ->
    rmap !! csp = Some wstk ->
    ftlr_IH -∗
    (∀ (r : RegName) (v : leibnizO Word) , ⌜r ≠ PC⌝ → ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    na_inv logrel_nais Nswitcher switcher_inv -∗
    interp_continuation cstk W C -∗
    sts_full_world W C -∗
    na_own logrel_nais ⊤ -∗
    cstack_frag cstk -∗
    ([∗ map] k↦y ∈ <[PC:=WCap XSRW_ Local b_switcher e_switcher a_switcher_return]> rmap , k ↦ᵣ y) -∗
    region W C -∗
    ▷ (£ 1 -∗ WP Seq (Instr Executable) {{ v0, ⌜v0 = HaltedV⌝ → na_own logrel_nais ⊤ }}).
  Proof.
    iIntros (Hfull_rmap Hwstk) "#IH #Hreg #Hinv_switcher Hcont Hsts Hna Hcstk Hrmap Hr".
    iNext; iIntros "_".

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    (* --- Extract scratch registers ct2 ctp --- *)
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    rewrite delete_insert_delete.
    (* cbn in Hfull_rmap. *)
    assert (exists wcgp, rmap !! cgp = Some wcgp) as [wcgp Hwcgp] by (by specialize (Hfull_rmap cgp)).
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    assert (exists wcra, rmap !! cra = Some wcra) as [wcra Hwcra] by (by specialize (Hfull_rmap cra)).
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    assert (exists wcsp, rmap !! csp = Some wcsp) as [wcsp Hwcsp] by (by specialize (Hfull_rmap csp)).
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    assert (exists wct1, rmap !! ct1 = Some wct1) as [wct1 Hwct1] by (by specialize (Hfull_rmap ct1)).
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs0, rmap !! cs0 = Some wcs0) as [wcs0 Hwcs0] by (by specialize (Hfull_rmap cs0)).
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs1, rmap !! cs1 = Some wcs1) as [wcs1 Hwcs1] by (by specialize (Hfull_rmap cs1)).
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert (exists wct2, rmap !! ct2 = Some wct2) as [wct2 Hwct2] by (by specialize (Hfull_rmap ct2)).
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap !! ctp = Some wctp) as [wctp Hwctp] by (by specialize (Hfull_rmap ctp)).
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.


  Admitted.


End fundamental.
