From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import logrel logrel_extra.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From cap_machine Require Export world_ghost_theory world_ghost_theory_interface.
From stdpp Require Import base.

Section switcher_helper.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* TODO Move the lemmas into a helper file for switcher spec *)

  Lemma open_world_interp_opening_resources (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) la ->
    la ## la' ->

    interp W C (WCap RWL g b e a)
    ∗ world_interp_open W C la'
      -∗

    world_interp_open W C (la++la')
    ∗ ([∗ list] a ∈ la, opening_resources interp W C a)
  .
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "(#Hinterp & [Hr Hsts] )"; cbn in * |- *.
    iDestruct (region_open_list_interp_gen _ _ _ _
                with "[$Hinterp $Hr $Hsts]") as "[$ $]"; eauto.
  Qed.

  Lemma close_world_interp_opening_resources (W : WORLD) (C : CmptName)
  (lv : list Word)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    world_interp_open W C (la++la')
    ∗ ([∗ list] a ; v ∈ la ; lv, a ↦ₐ v ∗ closing_resources interp W C a v)
    -∗ world_interp_open W C la'.
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "([Hr Hsts] & Hres )"; cbn in * |- *.
    iDestruct (region_close_list_interp_gen with "[$Hres $Hr]") as "$"; eauto.
  Qed.

  Lemma world_interp_reinstate_stack  E W C la lv :
    NoDup la →
    Forall (eq (WInt 0)) lv ->

    world_interp W C -∗
    ([∗ list] a;v ∈ la;lv ,
       (closing_revoked_resources W C a
        ∗ ⌜(std W) !! a = Some Revoked ⌝)
       ∗ a ↦ₐ v
    )

    ={E}=∗

    world_interp (std_update_multiple W la Temporary) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (??) "[Hr Hsts] Hres".
    iMod (update_region_revoked_temp_pwl_multiple'
           with "Hsts Hr [$Hres]") as "[ $ $ ]"; eauto.
  Qed.

  (* TODO This theorem is essentially [revoke_world], but with different RevokedResources *)
  Lemma world_interp_revoke_keep W C l :
    NoDup l ->
    ([∗ list] a ∈ l, ⌜(std W) !! a = Some Temporary⌝)
    ∗ world_interp W C
    ==∗
    world_interp (revoke W) C
    ∗ close_list_resources C W l true
    ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l⌝.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (Hdup) "(Hl & [Hr Hsts] )".
    iMod ( monotone_revoke_keep _ _ l with "[$Hr $Hsts Hl]") as
      "($ & $ & $ & $)"; auto.
  Qed.

  (* TODO This theorem is essentially [reinstate_world], but with different RevokedResources *)
  Lemma reinstate_close_list_gen W C (l : list Addr) :
    ⊢ world_interp W C
    ∗ close_list_resources_gen C W l l false
    ==∗
    world_interp (reinstate W l) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros "([Hr Hsts] & Htemp)".
    iMod (monotone_close_list_region_gen W W _ l with "[$Hr $Hsts $Htemp]") as "[Hsts Hr]"; iFrame.
    done.
  Qed.

End switcher_helper.
