From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import world_ghost_theory.
From griotte Require Import ist_spec_states.

(** * Logical steps of the proof of [ist_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [ist_spec_<segment>_blocks_<n>] in the proof of
    [ist_spec]. Sharing [b] with the callee is [cmdc_world_share]. *)

Section IST_World.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types C : CmptName.

  (** After the call, the thread takes the shared address [a] out of the
      map of Permanent regions of [C], which it holds. *)
  Lemma ist_perm_open C (a : Addr) :
    perm_region_map C ∅ -∗
    (LNonHeap a) ↪ᵖ[C]{RW} (safeGC interp_nonlocal) -∗
    perm_region_map C {[ LNonHeap a ]} ∗ ∃ v, a ↦ₐ v.
  Proof.
    iIntros "Hmap #Hrel".
    iDestruct (open_perm_region_map C ∅ (LNonHeap a) RW (safeGC interp_nonlocal)
                with "Hmap Hrel") as "[Hmap Hres]".
    { set_solver+. }
    rewrite union_empty_r_L.
    iFrame "Hmap".
    iDestruct "Hres" as (v) "Hres".
    (* The old value's [▷ φ] is dropped: it mentions [interp] *)
    iDestruct (PermRes_acc with "Hres") as "[(Ha & _) _]".
    iEval (rewrite key_pointsto_nonheap) in "Ha".
    by iExists v.
  Qed.

  (** The thread puts [a] back, holding an integer. *)
  Lemma ist_perm_close C (a : Addr) (z : Z) :
    perm_region_map C {[ LNonHeap a ]} -∗
    (LNonHeap a) ↪ᵖ[C]{RW} (safeGC interp_nonlocal) -∗
    a ↦ₐ WInt z -∗
    perm_region_map C ∅.
  Proof.
    iIntros "Hmap #Hrel Ha".
    iDestruct (init_PermRes C (LNonHeap a) RW (safeGC interp_nonlocal) (WInt z)
                with "[Ha] []") as "Hres".
    { done. }
    { by iEval (rewrite key_pointsto_nonheap). }
    { iApply interp_nonlocal_int. }
    rewrite -(union_empty_r_L {[ LNonHeap a ]}).
    iApply (close_perm_region_map C ∅ (LNonHeap a) RW _ (WInt z)
              with "Hmap Hrel Hres").
    set_solver+.
  Qed.
End IST_World.
