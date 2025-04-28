From cap_machine Require Export logrel.
From cap_machine.rules Require Export rules_BinOp.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.rules Require Import rules_base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.proofmode Require Import map_simpl register_tactics.
From cap_machine Require Import machine_base.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {tframeg : TFRAMEG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation TFRAME := (leibnizO nat).
  Notation WORLD := ( prodO (prodO STS_STD STS) TFRAME) .
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma binop_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg) (p p' : Perm)
    (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName)
    (r1 r2: Z + RegName) (P:D):
    ftlr_instr_base W C regs p p' g b e a w ρ P
      (decodeInstrW w = Add dst r1 r2 \/
       decodeInstrW w = Sub dst r1 r2 \/
       decodeInstrW w = Mul dst r1 r2 \/
       decodeInstrW w = LAnd dst r1 r2 \/
       decodeInstrW w = LOr dst r1 r2 \/
       decodeInstrW w = LShiftL dst r1 r2 \/
       decodeInstrW w = LShiftR dst r1 r2 \/
       decodeInstrW w = Lt dst r1 r2
      ).
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hsts Htframe Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iInsert "Hmap" PC.

    iApply (wp_BinOp with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    - incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      assert (dst <> PC) as HdstPC by (intros ->; rewrite lookup_insert in H1; done).
      rewrite lookup_insert_ne in H1; eauto; simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;contradiction. }
      iApply ("IH" $! _ _ (<[dst:=_]> (<[PC:=_]> regs)) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Htframe] [$Hown]")
      ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
        { repeat rewrite fixpoint_interp1_eq; auto. }
        { iApply "Hreg"; eauto. }
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
