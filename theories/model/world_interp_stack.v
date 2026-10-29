From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel.
From griotte Require Import memory_region proofmode.
From griotte Require Export world_ghost_theory stack_world_resources.
From griotte Require Import model_interp_stack.


Section WorldInterpStack.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  (*** World interpretation for stack region *)

  (** This file defines an interface to revoke and reinstate a stack region,
      using the knowledge that the stack region is safe-to-share. *)

  Lemma open_world_interp_opening_resources (W : WORLD) (C : CmptName)
    (la la' : list Addr) (g : Locality) (b e a : Addr) :
    NoDup la ->
    Forall (fun a' : Addr => (a' ∈ₐ [b, e)) ) la ->
    la ## la' ->

    interp W C (Cap RWL g b e a) ∗
    world_interp_open W C (LNonHeap <$> la')
    -∗

    world_interp_open W C (LNonHeap <$> (la++la')) ∗
    (∃ lv, ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
           ▷ StackOpenWorldResources interp W C la lv)
  .
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "(#Hinterp & [Hr [Hsts $ ] ] )"; cbn in * |- *.
    iDestruct (region_open_list_interp_gen _ _ _ _
                with "[$Hinterp $Hr $Hsts]") as "[$ $]"; eauto.
  Qed.

  Lemma close_world_interp_opening_resources (W : WORLD) (C : CmptName)
  (lv : list LWord)
  (la la' : list Addr):

    NoDup la ->
    la ## la' ->
    length lv = length la ->

    world_interp_open W C (LNonHeap <$> (la++la')) ∗
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗
    StackOpenWorldResources interp W C la lv
    -∗
   world_interp_open W C (LNonHeap <$> la').
  Proof.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (???) "([Hr [Hsts $ ] ] & Hres )"; cbn in * |- *.
    iDestruct (region_close_list_interp_gen with "[$Hres $Hr]") as "$"; eauto.
  Qed.

  Lemma world_interp_revoke_stack (W : WORLD) (C : CmptName) (b e a : Addr) :
    let la := finz.seq_between b e in

    interp W C (Cap RWL Local b e a) ∗
    world_interp W C
    ==∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]]) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
     rewrite world_interp_eq /world_interp_def.
     iIntros "(Hinterp & @)".
     iMod (monotone_revoke_stack with "[$Hinterp $Hr $ Hsts]")
        as (l) "($ & $ & $ & $ & $ & $ & $ & $)"; eauto.
    iDestruct (sealing_map_monotone with "Hseals") as "$"; auto.
    apply revoke_related_sts_priv_world.
  Qed.

  (** Revoke a stack region, part of which ([bs, es]) has been opened: the
      open cells are revoked whatever they hold. *)
  Lemma world_interp_revoke_stack_open {E : coPset} (W : WORLD) (C : CmptName)
    (b e a bs es : Addr) (lv ws : list LWord) :
    let la := finz.seq_between b e in
    let ls := finz.seq_between bs es in
    (b <= bs)%a → (es <= e)%a →

    interp W C (Cap RWL Local b e a) ∗
    world_interp_open W C (LNonHeap <$> ls) ∗
    ▷ StackOpenWorldResources interp W C ls lv ∗
    [[ bs , es ]] ↦ₐ [[ ws ]]
    ={E}=∗
    ∃ l_unk_temp,
      ⌜ extract_temporaries_condition W (l_unk_temp ++ (LNonHeap <$> la)) ⌝ ∗
      world_interp (revoke W) C ∗
      ▷ StackRevokedResources W C la ∗
      ▷ ⌜Forall (λ a, std (revoke W) !! LNonHeap a = Some Revoked) la⌝ ∗
      ▷ (∃ stk_mem, [[ b , e ]] ↦ₐ [[ stk_mem ]]) ∗
      ▷ RevokedResources W C l_unk_temp ∗
      ⌜Forall (λ a, std (revoke W) !! a = Some Revoked) l_unk_temp⌝.
  Proof.
    intros la ls Hbs Hes.
    rewrite world_interp_open_eq /world_interp_open_def world_interp_eq /world_interp_def.
    iIntros "(Hinterp & @ & [Hslot_res >Hslot_states] & Hslot)".
    iMod (monotone_revoke_stack_open
           with "[$Hinterp $Hr $Hsts $Hslot_res $Hslot_states $Hslot]")
      as (l) "($ & $ & $ & $ & $ & $ & $ & $)"; [done|done|].
    iDestruct (sealing_map_monotone with "Hseals") as "$"; auto.
    apply revoke_related_sts_priv_world.
  Qed.

  Lemma world_interp_reinstate_stack
    { E : coPset } (W : WORLD) (C : CmptName) (la : list Addr) (lv : list LWord) :
    NoDup la →
    Forall (eq (lword_of_word (WInt 0))) lv ->
    Forall (λ a, std W !! LNonHeap a = Some Revoked) la ->

    world_interp W C -∗
    StackRevokedResources W C la -∗
    ([∗ list] a;v ∈ la;lv,  a ↦ₐ v)

    ={E}=∗

    world_interp (std_update_multiple W la Temporary) C.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (???) "@ Hres Hl".
    iMod (update_region_revoked_temp_pwl_multiple
           with "Hsts Hr [Hres] [Hl]") as "[$ $]"; eauto.
    iDestruct (sealing_map_monotone_pub with "Hseals") as "$"; auto.
    - by rewrite std_update_multiple_seals.
    - apply related_sts_pub_update_multiple_temp; done.
  Qed.

End WorldInterpStack.
