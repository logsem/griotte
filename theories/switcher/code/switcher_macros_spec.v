From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel world_interp.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules proofmode monotone.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Import wp_rules_interp.
From griotte Require Import clear_stack_spec clear_registers_spec.

Section switcher_macros.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
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
