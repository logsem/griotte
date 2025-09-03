From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Export rules_Get rules_base.
From cap_machine.proofmode Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {cstackg : CSTACKG Σ}
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

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma get_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst r : RegName) (ins: instr) (P:D) (cstk : CSTK) (wstk : Word)
        (Nswitcher : namespace) :
    is_Get ins dst r →
    ftlr_instr W C regs p p' g b e a w ins ρ P cstk wstk Nswitcher.
  Proof.
    intros Hinstr Hp Hsome i Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont Hsts Hown Htframe".
    iIntros "Hr Hstate Ha HPC Hmap %Hsp #Hswitcher".
    rewrite <- Hi in Hinstr; clear Hi.
    iInsert "Hmap" PC.
    iApply (wp_Get with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    - incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;contradiction. }

      assert (is_Some (<[dst:=WInt z]> (<[PC:=WCap x x0 x1 x2 x3]> regs) !! csp)) as [??].
      { destruct (decide (dst = csp)); simplify_map_eq=>//. }
      iApply ("IH" $! _ _ _ (<[dst := _]> (<[PC := _]> regs))
               with "[%] [] [Hmap] [%] [$Hr] [$Hsts] [$Hcont] [$Hown] [$Htframe]")
        ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { iApply "Hreg"; eauto. }
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
