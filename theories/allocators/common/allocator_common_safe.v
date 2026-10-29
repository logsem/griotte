From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher_base switcher_base_ktk.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import world_interp_stack.
From griotte.allocators.common Require Import allocator_common_preamble.

(** World lemmas shared by the proofs that the entries of the allocators are
    safe to call. *)

Section AllocatorCommonSafe.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  (** Quarantined cells close as tombstones, with the witness that [ι] is
      quarantined. *)
  Lemma free_world_close_quarantined_list W C ι (la : list Addr) :
    NoDup la ->
    ι ⊒ AQuar -∗
    world_interp_open W C ((λ a, LHeap a ι) <$> la) ∗
    ([∗ list] a ∈ la,
      ∃ p φ ρ,
        ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
        rel C (LHeap a ι) p φ ∗
        sts_state_std C (LHeap a ι) ρ)
    -∗
    world_interp W C.
  Proof.
    intros Hnodup.
    induction la as [|a la IH].
    - iIntros "_ (Hworld & _)".
      by rewrite -open_world_interp_empty.
    - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      iIntros "#Hq (Hworld & Hhandles)".
      iDestruct "Hhandles" as "[Hhandle Hhandles]".
      iDestruct "Hhandle" as (p φ ρ) "(%Hpers & #Hrel & Hstate)".
      iDestruct (close_world_interp_next_quarantined_heap W C _ a ι p φ ρ
        with "Hq Hworld Hrel Hstate") as "Hworld".
      { intros Hin. apply list_elem_of_fmap in Hin as (a' & Heq & Hin).
        simplify_eq. done. }
      iApply (IH Hnodup with "Hq [$Hworld $Hhandles]").
  Qed.

  (** The registers outside the arguments carry no identifier at entry: the
      switcher's return sentry and the stack capability have none, and every
      other non-argument register holds zero. *)
  Lemma free_entry_regs_idfree (regs : LReg) (wcsp : Word) (nargs : nat) :
    regs !! csp = Some (lword_of_word wcsp) ->
    (∀ (r : RegName) (v : LWord),
      r ∉ ({[cra; cgp; csp]} ∪ dom_arg_rmap nargs : gset RegName) ->
      regs !! r = Some v -> v = WInt 0) ->
    ∀ r w, (r ∉ ({[cra; cgp]} ∪ dom_arg_rmap nargs : gset RegName)) ->
      regs !! r = Some w -> has_authority w.(lw) -> w.(lprov) = None.
  Proof.
    intros Hcsp Hzeros r w Hr Hw _.
    destruct (decide (r = csp)) as [->|Hne].
    - rewrite Hcsp in Hw. by simplify_eq.
    - rewrite (Hzeros r w); [done| |exact Hw]. set_solver.
  Qed.

End AllocatorCommonSafe.
