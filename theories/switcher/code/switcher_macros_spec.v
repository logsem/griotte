From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_invariants.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules proofmode monotone.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Import wp_rules_interp.
From griotte Require Import clear_stack_spec clear_registers_spec.

Section switcher_macros.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> (leibnizO LWord) -n> iPropO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma big_sepM_arg_rmap (Φ : RegName → LWord → iProp Σ) w0 w1 w2 w3 w4 w5 w6 :
    ([∗ map] r↦w ∈ <[ca0:=w0]> (<[ca1:=w1]> (<[ca2:=w2]> (<[ca3:=w3]> (<[ca4:=w4]>
                     (<[ca5:=w5]> (<[ct0:=w6]> ∅)))))), Φ r w)
    ⊣⊢ Φ ca0 w0 ∗ Φ ca1 w1 ∗ Φ ca2 w2 ∗ Φ ca3 w3 ∗ Φ ca4 w4 ∗ Φ ca5 w5 ∗ Φ ct0 w6.
  Proof.
    rewrite !big_sepM_insert ?big_sepM_empty ?right_id //; by simplify_map_eq.
  Qed.

  Lemma is_arg_rmap_8 w0 w1 w2 w3 w4 w5 w6 :
    is_arg_rmap (<[ca0:=w0]> (<[ca1:=w1]> (<[ca2:=w2]> (<[ca3:=w3]> (<[ca4:=w4]>
                  (<[ca5:=w5]> (<[ct0:=w6]> ∅))))))) 8.
  Proof. rewrite /is_arg_rmap /dom_arg_rmap !dom_insert_L dom_empty_L. set_solver. Qed.

  Lemma is_arg_rmap_8_inv (arg_rmap : LReg) :
    is_arg_rmap arg_rmap 8 →
    ∃ w0 w1 w2 w3 w4 w5 w6,
      arg_rmap = <[ca0:=w0]> (<[ca1:=w1]> (<[ca2:=w2]> (<[ca3:=w3]> (<[ca4:=w4]>
                   (<[ca5:=w5]> (<[ct0:=w6]> ∅)))))).
  Proof.
    intros Hargmap.
    assert (is_Some (arg_rmap !! ca0)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
    assert (is_Some (arg_rmap !! ca1)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
    assert (is_Some (arg_rmap !! ca2)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
    assert (is_Some (arg_rmap !! ca3)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
    assert (is_Some (arg_rmap !! ca4)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
    assert (is_Some (arg_rmap !! ca5)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
    assert (is_Some (arg_rmap !! ct0)) as [??];[apply elem_of_dom; rewrite Hargmap; set_solver|].
    exists x,x0,x1,x2,x3,x4,x5. apply map_eq.
    intros i. destruct (decide (ca0 = i));simplify_map_eq=>//.
    destruct (decide (ca1 = i));simplify_map_eq=>//.
    destruct (decide (ca2 = i));simplify_map_eq=>//.
    destruct (decide (ca3 = i));simplify_map_eq=>//.
    destruct (decide (ca4 = i));simplify_map_eq=>//.
    destruct (decide (ca5 = i));simplify_map_eq=>//.
    destruct (decide (ct0 = i));simplify_map_eq=>//.
    repeat (rewrite lookup_insert_ne; auto).
    apply not_elem_of_dom. rewrite Hargmap. set_solver.
  Qed.

  (** [clear_registers_pre_call_skip_spec_known] where the kept argument
      registers are safe. *)
  Lemma clear_registers_pre_call_skip_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (arg_rmap : LReg) (nargs : nat)
    (W : WORLD) (C : CmptName) φ :
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length clear_registers_pre_call_skip_instrs) ->

    is_arg_rmap arg_rmap 8 ->
    (nargs <= 7)%nat ->

    ( PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e (pc_a ^+ nargs)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg
                                        ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                                          then interp W C warg
                                          else True
        )
      ∗ codefrag_pers pc_a clear_registers_pre_call_skip_instrs
      ∗ ( (∃ arg_rmap',
              ⌜ is_arg_rmap arg_rmap' 8 ⌝
              ∗ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e (pc_a ^+ length clear_registers_pre_call_skip_instrs)
              ∗ (  [∗ map] rarg↦warg ∈ arg_rmap',
                     rarg ↦ᵣ[th] warg
                     ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                       then interp W C warg
                       else ⌜ warg = WInt 0⌝
                )
              ∗ codefrag_pers pc_a clear_registers_pre_call_skip_instrs)
               -∗ WP Exec @[th] {{ φ }})
    )
    ⊢ WP Exec @[th] {{ φ }}%I.
  Proof.
    iIntros (Hexec Hbounds Hargmap Hnargs) "(HPC & Hargs & #Hcode & Hcont)".
    iDestruct (big_sepM_sep with "Hargs") as "[Hargs Hargs_valid]".
    iDestruct (big_sepM_mono _
                 (λ r w, □ (if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True))%I
                with "Hargs_valid") as "#Hvalid".
    { iIntros (r w _) "Hv". destruct (decide (r ∈ dom_arg_rmap nargs)); last done.
      iDestruct "Hv" as "#Hv". iModIntro. iExact "Hv". }
    iApply (clear_registers_pre_call_skip_spec_known with "[- $HPC $Hargs $Hcode]"); try done.
    iIntros "(%arg_rmap' & %Hargmap' & HPC & Hargs & _)".
    iApply "Hcont".
    iExists arg_rmap'.
    iFrame "HPC Hcode".
    iSplit; first done.
    iApply (big_sepM_impl with "Hargs").
    iIntros "!>" (r w Hr) "[Hr Hw]".
    iFrame "Hr".
    destruct (decide (r ∈ dom_arg_rmap nargs)); last done.
    iDestruct "Hw" as %Hw.
    iDestruct (big_sepM_lookup with "Hvalid") as "Hv"; first exact Hw.
    rewrite decide_True //.
  Qed.

End switcher_macros.
