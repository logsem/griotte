From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode logrel register_tactics clear_registers_spec.
From griotte Require Import stack_world_resources call_stack.
From griotte Require Export code_blocks.

(** * Shared helpers of the case-study specifications

    - [code_blocks] (re-exported): offsets of the blocks of the code of a
      compartment, and the tactics to focus on its blocks,
    - [switcher_call_args_0] ... [switcher_call_args_3]: the argument
      registers of a call to the switcher, for an entry point with 0 to 3
      arguments. *)

(** ** Arguments of a call to the switcher

    [switcher_call_args_<n>] builds the argument registers [arg_rmap] and
    the other registers [rmap'] expected by the specification of the
    switcher call, for an entry point with [n] arguments, passed in [ca0],
    [ca1] and [ca2]. The arguments must be safe to share; the other argument
    registers are passed unchanged. *)
Section Switcher_call_args.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma switcher_call_args_0 W C (rmap : LReg) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ->
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 0)
                                      then interp W C warg
                                      else True)) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w).
  Proof.
    iIntros (Hrmap_dom) "Hrmap".
    iExtractList "Hrmap" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["Hca0"; "Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  Lemma switcher_call_args_1 W C (rmap : LReg) (wca0 : LWord) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ]} ->
    ca0 ↦ᵣ wca0 -∗
    interp W C wca0 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 1)
                                      then interp W C warg
                                      else True)) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w).
  Proof.
    iIntros (Hrmap_dom) "Hca0 #Hinterp_ca0 Hrmap".
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5;ct0]
      as ["Hca1"; "Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  Lemma switcher_call_args_2 W C (rmap : LReg) (wca0 wca1 : LWord) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    ca0 ↦ᵣ wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    interp W C wca1 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 2)
                                      then interp W C warg
                                      else True)) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w).
  Proof.
    iIntros (Hrmap_dom) "Hca0 #Hinterp_ca0 Hca1 #Hinterp_ca1 Hrmap".
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5;ct0]
      as ["Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  Lemma switcher_call_args_3 W C (rmap : LReg) (wca0 wca1 wca2 : LWord) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ; ca2 ]} ->
    ca0 ↦ᵣ wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    interp W C wca1 -∗
    ca2 ↦ᵣ wca2 -∗
    interp W C wca2 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗
                                     (if decide (rarg ∈ dom_arg_rmap 3)
                                      then interp W C warg
                                      else True)) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w).
  Proof.
    iIntros (Hrmap_dom) "Hca0 #Hinterp_ca0 Hca1 #Hinterp_ca1 Hca2 #Hinterp_ca2 Hrmap".
    iExtractList "Hrmap" [ca3;ca4;ca5;ct0]
      as ["Hca3"; "Hca4"; "Hca5"; "Hct0"].
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := wca2; ca3 := wca3;
               ca4 := wca4; ca5 := wca5; ct0 := wct0 ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

End Switcher_call_args.

(** ** The free part of a fresh stack

    A call from a fresh stack [[b, e)] hands to the switcher the part of the
    stack below the space reserved at its top. *)
Section Fresh_stack.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Lemma stk_start_region_split (b e : Addr) (stk_mem : list LWord) :
    (b + StackEntry_reserved_space <= e)%Z ->
    [[b, e]] ↦ₐ [[stk_mem]] -∗
    ∃ stk_mem' stk_res,
      [[stk_free_b b (stk_start_a b e), stk_free_e e (stk_start_a b e)]] ↦ₐ [[stk_mem']] ∗
      [[stk_start_a b e, e]] ↦ₐ [[stk_res]].
  Proof.
    iIntros (Hsize) "Hstk".
    iDestruct (big_sepL2_length with "Hstk") as %Hlen.
    rewrite -(take_drop (finz.dist b (stk_start_a b e)) stk_mem).
    iDestruct (region_pointsto_split b e (stk_start_a b e) with "Hstk") as "[Hstk Hres]".
    { stk_unfold; solve_addr+Hsize. }
    { rewrite length_take finz_seq_between_length in Hlen |- *.
      stk_unfold; rewrite /finz.dist in Hlen |- *; solve_addr+Hsize Hlen. }
    iExists _, _. iFrame "Hstk Hres".
  Qed.

  Lemma stk_start_seq_split (b e : Addr) :
    (b + StackEntry_reserved_space <= e)%Z ->
    finz.seq_between b e =
      stk_free b e (stk_start_a b e) ++ finz.seq_between (stk_start_a b e) e.
  Proof.
    intros Hsize. rewrite /stk_free. apply finz_seq_between_split. stk_unfold; solve_addr+Hsize.
  Qed.

  Lemma stk_start_revoked_split (W : WORLD) (C : CmptName) (b e : Addr) :
    (b + StackEntry_reserved_space <= e)%Z ->
    StackRevokedResources W C (finz.seq_between b e) ⊣⊢
    StackRevokedResources W C (stk_free b e (stk_start_a b e)) ∗
    StackRevokedResources W C (finz.seq_between (stk_start_a b e) e).
  Proof.
    intros Hsize. by rewrite {1}(stk_start_seq_split b e Hsize) StackRevokedResources_app.
  Qed.

  Lemma stk_start_revoked_addresses (W : WORLD) (b e : Addr) :
    (b + StackEntry_reserved_space <= e)%Z ->
    revoked_addresses W (finz.seq_between b e) ->
    revoked_addresses W (stk_free b e (stk_start_a b e)).
  Proof.
    intros Hsize Hrevoked.
    rewrite (stk_start_seq_split b e Hsize) in Hrevoked.
    by apply revoked_addresses_app in Hrevoked as [? _].
  Qed.

  Lemma stk_start_region_join (b e : Addr) (stk_mem stk_res : list LWord) :
    (b + StackEntry_reserved_space <= e)%Z ->
    [[stk_free_b b (stk_start_a b e), stk_free_e e (stk_start_a b e)]] ↦ₐ [[stk_mem]] -∗
    [[stk_start_a b e, e]] ↦ₐ [[stk_res]] -∗
    [[b, e]] ↦ₐ [[stk_mem ++ stk_res]].
  Proof.
    iIntros (Hsize) "Hstk Hres".
    iDestruct (big_sepL2_length with "Hres") as %Hlen.
    iApply (region_pointsto_split_r b e (stk_start_a b e)); last iFrame.
    { stk_unfold; solve_addr+Hsize. }
    { rewrite -Hlen finz_seq_between_length. done. }
  Qed.
End Fresh_stack.

(** An address within bounds of a region disjoint from the MMIO (resp. heap)
    region is not a shadow (resp. heap) address. *)
Ltac solve_not_shadow H :=
  eapply disjoint_from_shadow_not_in;
  [exact (disjoint_from_mmio_shadow _ _ H) | rewrite /withinBounds; solve_addr].

Ltac solve_not_heap H :=
  eapply disjoint_from_heap_not_in; [exact H | rewrite /withinBounds; solve_addr].
