From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import logrel switcher_preamble interp_switcher_return switcher_trap_safety.
From griotte.switcher.failure Require Import switch_stack_too_small.
From griotte.switcher.callback Require Import switcher_zero_callee_frame.

(** * Returns of the switcher to the caller outside the return routine

    The return to [cra] at [.Lswitch_just_return], where the exception
    path resumes a context, and the return of [-ENOTENOUGHSTACK] when the
    callee's stack is too small, through the return routine. *)

Section Switcher_unwind.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_just_return], where the exception path resumes a
      context: the return to [cra]. *)
  Lemma switcher_just_return_spec (wret : LWord) :
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_just_return" ∗
    cra ↦ᵣ[th] wret ∗
    switcher_code ∗
    ( ▷ ( PC ↦ₚ[th] lupdatePcPerm wret ∗
          cra ↦ᵣ[th] wret ∗
          £ 1 -∗
          safe[th] ) ∧
      ( ⌜jalr_target_ok cnull cra wret.(lw) = false⌝ ∗
        cra ↦ᵣ[th] wret -∗
        trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
          (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros "(HPC & Hcra & #Hswitcher & Hpost)".
    iApply (switcher_return_to_caller_spec with "[$HPC $Hcra $Hswitcher $Hpost]").
  Qed.

  (** The callee's stack is smaller than the minimum stack size of the
      entry point plus the reserved space: [.Lswitch_stack_too_small] sets
      the return values, and the return routine pops the frame already
      pushed. No register needs to be safe. *)
  Lemma switcher_call_stack_too_small_unwind_of_safety
    (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_too_small" ∗
    registers_pointsto rmap ∗
    switcher_trap_safety ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own (tpool th) ⊤ ∗
    ◯(CSTK)[th] cstk
    ⊢ safe[th].
  Proof.
    iIntros (Hfull_rmap Hframe)
      "(HPC & Hrmap & #Hsafety & Hworld_interp & Hcont & Hna & Hcstk)".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[#Hinv_switcher #Hstatic]".
    iPoseProof "Hstatic" as "[#Hcode _]".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switch_stack_too_small_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1)".
    iEval (rewrite -switcher_return_offset) in "HPC".
    iInsertList "Hrmap" [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iSplit; iApply interp_int.
  Qed.

End Switcher_unwind.
