From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel.
From griotte Require Import memory_region proofmode.
From griotte Require Export world_ghost_theory stack_world_resources.
From griotte Require Import model_interp_stack.


Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  (*** World interpretation for stack region *)

  (** This file defines an interface to revoke and reinstate a stack region,
      using the knowledge that the stack region is safe-to-share. *)

  Lemma open_world_interp_opening_resources (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) la ->
    la ## la' ->

    interp W C (WCap RWL g b e a) ∗
    world_interp_open W C la'
    -∗

    world_interp_open W C (la++la') ∗
    (∃ lv, ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
           ▷ StackOpenWorldResources interp W C la lv)
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

    world_interp_open W C (la++la') ∗
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
   world_interp_open W C la'.
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "([Hr Hsts] & Hres )"; cbn in * |- *.
    iDestruct (region_close_list_interp_gen with "[$Hres $Hr]") as "$"; eauto.
  Qed.

  Lemma world_interp_revoke_stack (W : WORLD) (C : CmptName) (b e a : Addr) :
    let la := finz.seq_between b e in

    interp W C (WCap RWL Local b e a) ∗
    world_interp W C
    ==∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ la) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]]) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
     rewrite world_interp_eq /world_interp_def.
     iIntros "(Hinterp & [Hr Hsts])".
     iMod (monotone_revoke_stack with "[$Hinterp $Hr $ Hsts]")
        as (l) "($ & $ & $ & $ & $ & $ & $ & $)"; eauto.
  Qed.

  Lemma world_interp_reinstate_stack
    { E : coPset } (W : WORLD) (C : CmptName) (la : list Addr) (lv : list Word) :
    NoDup la →
    Forall (eq (WInt 0)) lv ->
    Forall (λ a, std W !! a = Some Revoked) la ->

    world_interp W C -∗
    StackRevokedResources W C la -∗
    ([∗ list] a;v ∈ la;lv,  a ↦ₐ v)

    ={E}=∗

    world_interp (std_update_multiple W la Temporary) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (???) "[Hr Hsts] Hres Hl".
    iMod (update_region_revoked_temp_pwl_multiple
           with "Hsts Hr [Hres] [Hl]") as "[$ $]"; eauto.
  Qed.

End WorldInterpStack.
