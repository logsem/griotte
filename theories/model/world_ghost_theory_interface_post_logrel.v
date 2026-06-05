From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import logrel logrel_extra.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From cap_machine Require Export world_ghost_theory world_ghost_theory_interface.
From stdpp Require Import base.

Section world_ghost_theory_interface_post_logrel.

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

  Lemma world_interp_revoke_stack W C b e a :
    let la := finz.seq_between b e in

    interp W C (WCap RWL Local b e a)
    ∗ world_interp W C
    ==∗
    ∃ l_unk_temp,
      ⌜ NoDup (l_unk_temp ++ la) ∧ (forall (a : Addr), (std W) !! a = Some Temporary <-> a ∈ (l_unk_temp ++ la))⌝
      ∗ world_interp (revoke W) C
      ∗ ▷ ([∗ list] a ∈ la, closing_revoked_resources W C a)
      ∗ ▷ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) la⌝
      ∗ ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]])
      ∗ close_list_resources C W l_unk_temp true
      ∗ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la.
    rewrite world_interp_eq /world_interp_def.
    iIntros "(Hinterp & [Hr Hsts])".
    iMod (monotone_revoke_stack_alt with "[$Hinterp $Hr $ Hsts]")
        as (l) "($ & $ & $ & $ & $ & $ & $)".
    done.
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


End world_ghost_theory_interface_post_logrel.
