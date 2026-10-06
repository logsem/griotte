From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel_binary.
From griotte Require Import memory_region memory_region_binary.
From griotte Require Export world_ghost_theory_binary stack_world_resources_binary.
From griotte Require Import model_interp_stack_binary.


Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).

  (*** World interpretation for stack region *)

  (** This file defines an interface to revoke and reinstate a stack region,
      using the knowledge that the stack region is safe-to-share.
      The contents of the stack region are tracked separately for the
      implementation memory and for the specification memory. *)

  Lemma open_world_interp_opening_resources (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (b <= a' < e)%a ) la ->
    la ## la' ->

    interp W C (WCap RWL g b e a, WCap RWL g b e a) ∗
    world_interp_open W C la'
    -∗

    world_interp_open W C (la++la') ∗
    (∃ lv1 lv2,
        ([∗ list] a;v ∈ la;lv1, a ↦ₐ v) ∗
        ([∗ list] a;v ∈ la;lv2, a ↣ₐ v) ∗
        ▷ StackOpenWorldResources interp W C la lv1 lv2)
  .
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "(#Hinterp & [Hr Hsts] )"; cbn in * |- *.
    iDestruct (region_open_list_interp_gen _ _ _ _
                with "[$Hinterp $Hr $Hsts]") as "[$ $]"; eauto.
  Qed.

  Lemma close_world_interp_opening_resources (W : WORLD) (C : CmptName)
    (lv1 lv2 : list Word)
    (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv1 = length la ->

    world_interp_open W C (la++la') ∗
    ([∗ list] a;v ∈ la;lv1, a ↦ₐ v) ∗
    ([∗ list] a;v ∈ la;lv2, a ↣ₐ v) ∗
    StackOpenWorldResources interp W C la lv1 lv2
    -∗
   world_interp_open W C la'.
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "([Hr Hsts] & Hres )"; cbn in * |- *.
    iDestruct (region_close_list_interp_gen with "[$Hres $Hr]") as "$"; eauto.
  Qed.

  Lemma world_interp_revoke_stack (W : WORLD) (C : CmptName) (b e a : Addr) :
    let la := finz.seq_between b e in

    interp W C (WCap RWL Local b e a, WCap RWL Local b e a) ∗
    world_interp W C
    ==∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ la) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem stk_mem_spec, [[ b , e ]] ↦ₐ [[ stk_mem ]] ∗ [[ b , e ]] ↣ₐ [[ stk_mem_spec ]]) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
     rewrite world_interp_eq /world_interp_def.
     iIntros "(Hinterp & [Hr Hsts])".
     iMod (monotone_revoke_stack with "[$Hinterp $Hr $ Hsts]")
        as (l) "($ & $ & $ & $ & $ & $ & $ & $)"; eauto.
  Qed.

  Lemma world_interp_reinstate_stack
    { E : coPset } (W : WORLD) (C : CmptName) (la : list Addr) (lv1 lv2 : list Word) :
    NoDup la →
    Forall (eq (WInt 0)) lv1 ->
    Forall (eq (WInt 0)) lv2 ->
    Forall (λ a, std W !! a = Some Revoked) la ->

    world_interp W C -∗
    StackRevokedResources W C la -∗
    ([∗ list] a;v ∈ la;lv1,  a ↦ₐ v) -∗
    ([∗ list] a;v ∈ la;lv2,  a ↣ₐ v)

    ={E}=∗

    world_interp (std_update_multiple W la Temporary) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (????) "[Hr Hsts] Hres Hl Hsl".
    iMod (update_region_revoked_temp_pwl_multiple
           with "Hsts Hr Hres Hl Hsl") as "[$ $]"; eauto.
  Qed.

End WorldInterpStack.
