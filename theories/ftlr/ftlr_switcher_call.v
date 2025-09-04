From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel region_invariants.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine Require Import rules proofmode monotone.
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
    

  Axiom foo : False.

  Lemma switcher_call_ftlr (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (cstk : CSTK) (wstk : Word)
    (Nswitcher : namespace)
    :
    (∀ x, is_Some (regs !! x)) ->
    regs !! csp = Some wstk ->
    ftlr_IH -∗
    (∀ (r : RegName) (v : leibnizO Word) , ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v) -∗
    na_inv logrel_nais Nswitcher switcher_inv -∗
    interp_continuation cstk W C -∗
    sts_full_world W C -∗
    na_own logrel_nais ⊤ -∗
    cstack_frag cstk -∗
    ([∗ map] k↦y ∈ <[PC:=WCap XSRW_ Local b_switcher e_switcher a_switcher_call]> regs , k ↦ᵣ y) -∗
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

    iExtract "Hrmap" PC as "HPC".
    iExtract "Hrmap" csp as "Hcsp".
    specialize (Hfull_rmap cs0) as HH;destruct HH as [? ?].
    iExtract "Hrmap" cs0 as "Hcs0".

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a) by solve_addr.
    
    (* --- Store csp cs0 --- *)

    (* store failure *)
    destruct (is_cap wstk) eqn:Hcap;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg_not_cap with "[$]"); try solve_pure.
      iIntros "!> _".
      wp_pure. wp_end. iIntros "%Hcontr";done. }

    destruct wstk;try done. destruct sb; try done.

    destruct (withinBounds b e a) eqn:Hbounds;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$]"); try solve_pure.
      iIntros "!> _".
      wp_pure. wp_end. iIntros "%Hcontr";done. }

    destruct (canStore p x) eqn:Hcanstore;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg_perm with "[$]"); try solve_pure.
      iIntros "!> _".
      wp_pure. wp_end. iIntros "%Hcontr";done. }
    
    iDestruct ("Hreg" $! csp with "[//] [//]") as "#Hspv".
    iDestruct ("Hreg" $! cs0 with "[//] [//]") as "#Hcs0v".
    apply canStore_writeAllowed in Hcanstore as Hwa.
    iDestruct (write_allowed_inv _ _ a with "Hspv") as (p' P Hflows Hpers) "(Hrel & Hzcond & Hwcond & Hrcond & Hmono)";[solve_addr|auto|..].
    iDestruct (writeAllowed_valid_cap_implies with "Hspv") as (ρ) "[%Hρ %Hnotrev]";auto.

    iDestruct (region_open with "[$]") as (v) "(Hr & Hsts & Hstate & Ha & %Hno & _ & _)";[|done|].
    { destruct ρ;auto. done. }

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg with "[$]");auto;try solve_pure.
    iIntros "!> (HPC & ? & Hcs0 & Hcsp & Ha)".
    wp_pure. iDestruct ("Hcode" with "[$]") as "Hcode".

    iDestruct (region_close with "[$Hr $Hstate $Ha $Hrel]") as "Hr";[auto|..].
    { destruct ρ;auto. done. }
    { iFrame "%". rewrite /safeC /=.
      iDestruct ("Hwcond" with "Hcs0v") as "HP".
      iFrame "HP".
      rewrite /monoReq Hρ.
      destruct ρ;[simpl..|exfalso;done].
      - destruct (isWL p');auto.
        destruct (isDL p')
        ; by (iSpecialize ("Hmono" with "[%]");[eapply canStore_flowsto;eauto|]).
      - by (iSpecialize ("Hmono" with "[%]");[eapply canStore_flowsto;eauto|]). }

    
    
    
    iGo "Hcode".
    
    exfalso. apply foo.
  Qed.    
    
    

End fundamental.
