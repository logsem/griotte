From cap_machine Require Export logrel.
From cap_machine Require Export rules_BinOp.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import rules_base.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine.proofmode Require Import map_simpl register_tactics.
From cap_machine Require Import machine_base.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {cstackg : CSTACKG Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma binop_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg) (p p' : Perm)
    (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName)
    (r1 r2: Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr_base W C regs p p' g b e a w ρ P
      (decodeInstrW w = Add dst r1 r2 \/
       decodeInstrW w = Sub dst r1 r2 \/
       decodeInstrW w = Mul dst r1 r2 \/
       decodeInstrW w = LAnd dst r1 r2 \/
       decodeInstrW w = LOr dst r1 r2 \/
       decodeInstrW w = LShiftL dst r1 r2 \/
       decodeInstrW w = LShiftR dst r1 r2 \/
       decodeInstrW w = Lt dst r1 r2
      ) cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hown Htframe".
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

      assert (is_Some (<[dst:=WInt (rules_BinOp.denote (decodeInstrW w) n1 n2)]> (<[PC:=WCap x x0 x1 x2 x3]> regs) !! csp)) as [??].
      { destruct (decide (dst = csp)); simplify_map_eq=>//. }
      iApply ("IH" $! _ _ _ _ _ (<[dst:=_]> (<[PC:=_]> regs)) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$Htframe]")
      ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
        { destruct (decide (dst = cnull)) ; [iApply interp_int|].
         repeat rewrite fixpoint_interp1_eq; auto. }
        { iApply "Hreg"; eauto. }
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
