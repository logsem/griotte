From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_ReadSR.
From cap_machine.proofmode Require Import map_simpl register_tactics.
From cap_machine Require Import stdpp_extra.

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

  Lemma readsr_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst : RegName) (src : SRegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (wstk : Word)
    (Nswitcher : namespace) :
    ftlr_instr W C regs p p' g b e a w (ReadSR dst src) ρ P cstk Ws Cs wstk Nswitcher.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hown Htframe".
    iIntros "Hr Hstate Ha HPC Hmap %Hsp #Hswitcher".
    iInsert "Hmap" PC.
    destruct (has_sreg_access p) eqn:HpXRS.
    { iClear "IH Hreg Hinva Hrcond Hwcond Hmono HmonoV Hw Hsts Htframe Hown Hr Hstate Ha Hmap".
      iEval (rewrite !fixpoint_interp1_eq interp1_eq) in "Hinv_interp".
      destruct (isO p) eqn: HnO.
      { destruct Hp as [Hexec _]
        ; eapply executeAllowed_nonO in Hexec
        ; congruence.
      }
      destruct (has_sreg_access p) eqn:HpXRS'; first done.
      congruence.
    }

    iApply (wp_ReadSR with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }
    { by rewrite HpXRS. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    - by simplify_map_eq.
  Qed.

End fundamental.
