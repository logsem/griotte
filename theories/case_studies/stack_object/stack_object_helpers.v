From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From cap_machine Require Export world_ghost_theory.

Section stack_object_helpers.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma world_interp_revoked_by_separation
    (W : WORLD) (C' : CmptName)
    (a : Addr) (w : Word) :
    a ∈ dom (std W) →
    world_interp W C'
    ∗ a ↦ₐ w
    ==∗
    world_interp W C'
    ∗ a ↦ₐ w
    ∗ ⌜ std W !! a = Some Revoked ⌝
  .
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (?) "([Hr Hsts] & Ha)".
    iMod (revoked_by_separation with "[$Hr $Hsts $Ha]") as "($&$&$)";auto.
  Qed.

  (* TODO This theorem is essentially [reinstate_world], but with different RevokedResources *)
  Lemma reinstate_close_list W W' C' (l : list Addr) :
    related_sts_pub_world W (close_list l W') ->
    world_interp W' C' ∗ (close_list_resources C' W l false)
    ==∗
    world_interp (reinstate W' l) C'.
  Proof.
    rewrite world_interp_eq /world_interp_def.
    iIntros (Hrelated) "( [Hr Hsts] & Htemp)".
    iMod (monotone_close_list_region with "[] [$Hsts $Hr $Htemp]") as "[$ $]"; auto.
  Qed.

  Lemma open_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (Addr * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type))
    (l' : list Addr)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => (std W) !! a = Some ρ) l ->

    ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ)
    ∗ world_interp_open W C' l' -∗

    ∃ lv,
      world_interp_open W C' (la++l')
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ)
      ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₐ v)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C' φ p v ρ)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C',v))
      ∗ ⌜ length lv = length la ⌝
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
  .
  Proof.
    intros la.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (????) "(Hrels & [Hr Hsts])".
    iDestruct (region_open_list W C' l l' with "[$Hrels $Hr $Hsts]") as
      "(% & $ & $ & $ & $ & $ & $ & $)"; auto.
  Qed.

  Lemma close_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (Addr * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type))
    (l' : list Addr)
    (lv : list Word)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    length l = length lv ->
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => ∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)) l ->

    world_interp_open W C' (la++l')
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₐ v)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C' φ p v ρ)
    ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C',v))
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ)
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
      -∗ world_interp_open W C' l'.
  Proof.
    intros la.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (?????) "([Hr $] & Hstd & Hv & Hmono & Hφ & Hrel & Hp)".
    iDestruct (region_close_list with "[$Hr $Hstd $Hv $Hmono $Hφ $Hrel $Hp]") as "$"; auto.
  Qed.

  (* TODO temporary lemma, waiting to get rid off close_list_resources *)
  Lemma RevokedResources_close_list_resources_eq (W : WORLD) ( C : CmptName ) (l : list Addr) :
    RevokedResources W C l ⊣⊢ close_list_resources C W l false.
  Proof.
    iSplit; iIntros "H"; iApply (big_sepL_impl with "H")
    ; iModIntro ; iIntros (k ka Hka) "H".
    + iDestruct "H" as "(% &% & $ & $ & [% ($&$&$&?)])"; by rewrite mono_temporary_eq.
    + iDestruct "H" as "(% &% & $ & [% ($&$&?&$)] & $)"; by rewrite mono_temporary_eq.
  Qed.

  Lemma RevokedResources_separation_many_alt
    (C1 C2 : CmptName) (W1 W2 : WORLD) (l1 l2 : list Addr) :
    RevokedResources W1 C1 l1
    ∗ RevokedResources W2 C2 l2
      -∗ ⌜ l1 ## l2 ⌝.
  Proof.
    rewrite !RevokedResources_close_list_resources_eq.
    apply close_list_resources_separation_many_alt.
  Qed.

End stack_object_helpers.
