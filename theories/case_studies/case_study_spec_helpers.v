From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode logrel register_tactics clear_registers_spec.
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
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma switcher_call_args_0 W C (rmap : Reg) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ->
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
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

  Lemma switcher_call_args_1 W C (rmap : Reg) (wca0 : Word) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ]} ->
    ca0 ↦ᵣ wca0 -∗
    interp W C wca0 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
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

  Lemma switcher_call_args_2 W C (rmap : Reg) (wca0 wca1 : Word) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    ca0 ↦ᵣ wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    interp W C wca1 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
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

  Lemma switcher_call_args_3 W C (rmap : Reg) (wca0 wca1 wca2 : Word) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ; ca2 ]} ->
    ca0 ↦ᵣ wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    interp W C wca1 -∗
    ca2 ↦ᵣ wca2 -∗
    interp W C wca2 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
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
