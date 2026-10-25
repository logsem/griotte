From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import logrel switcher_preamble interp_switcher_return.
From griotte Require Export switcher_error_handler.

(** * Trap safety of the switcher

    [switcher_trap_safety] bundles the switcher's invariant and static
    resources with the two facts that its exception path provides: the
    safety of the exception entry ([exception_entry_safe]) and the resume of
    a fault of the first spill of the call path at [.Lswitch_just_return]
    ([switcher_resume_safe]). It is persistent; [switcher_exception] proves
    it from the invariant and the static resources. The trap lemmas below
    are derived from it, so the specifications of the call and return
    routines do not depend on the proof of the exception path. *)

Section Switcher_trap_safety.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The safety of the exception entry, for a fault in an untrusted
      compartment (with the whole non-atomic token) or a fault that the
      switcher handles, for any token [F] that contains the switcher's
      invariant and the trap-entry part. *)
  Definition exception_entry_safe : iProp Σ :=
    □ ∀ (F : coPset) (cstk : CSTK) (rmap : LReg) (w : LWord),
      ⌜↑Nswitcher ⊆ F⌝ -∗
      ⌜↑N_trap ⊆ F⌝ -∗
      ⌜∀ r, is_Some (rmap !! r)⌝ -∗
      ((⌜F = ⊤⌝ ∗ untrusted_fault cstk rmap) ∨ trap_handler_ok F cstk w rmap) -∗
      PC ↦ₚ lword_of_word mtcc_vec -∗
      trap_entry_out w -∗
      registers_pointsto rmap -∗
      na_own cerise_nais (F ∖ ↑N_trap) -∗
      cstack_frag cstk -∗
      WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.

  #[global] Instance exception_entry_safe_persistent :
    Persistent (exception_entry_safe).
  Proof. rewrite /exception_entry_safe. apply _. Qed.

  (** A fault that the exception path resumes (a fault of the first spill
      of the call path) is safe: after trap entry, the switcher overwrites
      the return values with [-ENOTENOUGHSTACK] and 0, and installs the
      context again, at [.Lswitch_just_return]. *)
  Definition switcher_resume_safe : iProp Σ :=
    □ ∀ (F : coPset) (w : LWord),
      ⌜↑Nswitcher ⊆ F⌝ -∗
      ⌜↑N_trap ⊆ F⌝ -∗
      ⌜¬ trap_no_resume w⌝ -∗
      (|={⊤}=>
         ∃ rmap : LReg,
           ⌜∀ r, is_Some (rmap !! r)⌝ ∗
           na_own cerise_nais F ∗
           registers_pointsto rmap ∗
           (∀ rmap' : LReg,
              ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
              ⌜∀ r, r ≠ ca0 → r ≠ ca1 → rmap' !! r = rmap !! r⌝ -∗
              ⌜rmap' !! ca0 = Some (WInt ENOTENOUGHSTACK : LWord)⌝ -∗
              ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
              PC ↦ₚ switcher_label_pc ".Lswitch_just_return" -∗
              registers_pointsto rmap' -∗
              na_own cerise_nais F -∗
              WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})) -∗
      trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.

  #[global] Instance switcher_resume_safe_persistent :
    Persistent (switcher_resume_safe).
  Proof. rewrite /switcher_resume_safe. apply _. Qed.

  (** The trap safety of the switcher. *)
  Definition switcher_trap_safety : iProp Σ :=
    "Hinv_switcher" ∷ na_inv cerise_nais Nswitcher switcher_inv ∗
    "Hstatic" ∷ switcher_static ∗
    "Hentry_safe" ∷ exception_entry_safe ∗
    "Hresume_safe" ∷ switcher_resume_safe.

  #[global] Instance switcher_trap_safety_persistent :
    Persistent (switcher_trap_safety).
  Proof. rewrite /switcher_trap_safety. apply _. Qed.

  (** The invariant and the static resources of the switcher. *)
  Lemma switcher_trap_safety_res :
    switcher_trap_safety ⊢
    na_inv cerise_nais Nswitcher switcher_inv ∗ switcher_static.
  Proof. iIntros "#Hsafety". iNamed "Hsafety". iFrame "#". Qed.

  Lemma exception_entry_safe_vector :
    exception_entry_safe ⊢
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec).
  Proof.
    iIntros "#Hsafe !>" (cstk regs w Hfull) "Hfault HPC Hout Hrmap Hna Hcstk".
    iApply ("Hsafe" $! ⊤ with "[%] [%] [//] [Hfault] HPC Hout Hrmap Hna Hcstk");
      [set_solver | set_solver |].
    iDestruct "Hfault" as "[Hfault | Hfault]"; [iLeft; by iFrame | by iRight].
  Qed.

  (** The unwind continuation from the logical relation's resources, for a
      safe trap vector: the return routine pops the frame of the faulting
      compartment, whatever its error handler count. *)
  Lemma logrel_unwind_cont_gen (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    frame_match Ws Cs cstk W C →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec) -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    unwind_cont ⊤ cstk True.
  Proof.
    iIntros (Hframe) "#Hinv #Hstatic #Htrap Hworld Hcont".
    iIntros (n rmap Hfull Hca0 Hca1) "HPC Hrmap Hcstk _ Hna".
    iEval (rewrite -(interp_cont_set_top_count cstk Ws Cs n)) in "Hcont".
    iApply (switcher_return_unwind _ W C (cstack_set_top_count cstk n) Ws Cs
             with "[$HPC $Hrmap $Hinv $Hstatic $Htrap $Hworld $Hcont $Hna $Hcstk]");
      [done | done | done | by apply frame_match_set_top_count |].
    iSplit; iApply interp_int.
  Qed.

  (** ** Trap lemmas *)

  (** The trap vector of the machine is safe. *)
  Lemma switcher_mtcc_vec_safe_of_safety :
    switcher_trap_safety
    ⊢ trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec).
  Proof.
    iIntros "#Hsafety". iNamed "Hsafety".
    by iApply exception_entry_safe_vector.
  Qed.

  (** A fault closes through the exception path of the switcher: after
      trap entry, the switcher handles the fault ([trap_handler_ok F]). *)
  Lemma trap_safe_exception_entry_of_safety (F : coPset) (w : LWord) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    switcher_trap_safety -∗
    (|={⊤}=>
       ∃ (rmap : LReg) (cstk : CSTK),
         ⌜∀ r, is_Some (rmap !! r)⌝ ∗
         na_own cerise_nais F ∗
         registers_pointsto rmap ∗
         cstack_frag cstk ∗
         trap_handler_ok F cstk w rmap) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (HF HFtrap) "#Hsafety Hres".
    iNamed "Hsafety".
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iMod "Hres" as (rmap cstk Hfull_rmap) "(Hna & Hrmap & Hcstk & Hhandled)".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    iApply ("Hentry_safe" $! F cstk rmap w with
             "[//] [//] [//] [Hhandled] HPC Hout Hrmap Hna Hcstk").
    by iRight.
  Qed.

  (** A fault that the exception path resumes (a fault of the first spill
      of the call path) closes through the exception path of the switcher,
      which returns at [.Lswitch_just_return]. *)
  Lemma trap_safe_resume_of_safety (F : coPset) (w : LWord) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    ¬ trap_no_resume w →
    switcher_trap_safety -∗
    (|={⊤}=>
       ∃ rmap : LReg,
         ⌜∀ r, is_Some (rmap !! r)⌝ ∗
         na_own cerise_nais F ∗
         registers_pointsto rmap ∗
         (∀ rmap' : LReg,
            ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
            ⌜∀ r, r ≠ ca0 → r ≠ ca1 → rmap' !! r = rmap !! r⌝ -∗
            ⌜rmap' !! ca0 = Some (WInt ENOTENOUGHSTACK : LWord)⌝ -∗
            ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
            PC ↦ₚ switcher_label_pc ".Lswitch_just_return" -∗
            registers_pointsto rmap' -∗
            na_own cerise_nais F -∗
            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (HF HFtrap Hresume) "#Hsafety Hres".
    iNamed "Hsafety".
    by iApply ("Hresume_safe" with "[//] [//] [//] Hres").
  Qed.

  (** A fault in trusted code is safe: after exception entry, the exception
      entry of the switcher unwinds the call of the faulting compartment, or
      resumes a fault in an untrusted compartment. *)
  Lemma trap_safe_unwind_of_safety (cstk : CSTK) (rmap : LReg) (w : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    switcher_trap_safety -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       na_own cerise_nais ⊤ ∗
       cstack_frag cstk ∗
       (untrusted_fault cstk rmap ∨ trap_handler_ok ⊤ cstk w rmap)) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hfull_rmap) "#Hsafety Hres".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    iApply (interp_trap_safe with "Htrap Hres"); done.
  Qed.

  (** A fault in trusted code, with the logical relation's resources, in
      the switcher ([switcher_fault_pc w]) or in a compartment whose table
      declares no handler and whose frame's table word is set: the switcher unwinds the call of the faulting
      compartment through the return routine. *)
  Lemma trap_safe_unwind_logrel_of_safety
    (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (w : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->
    trap_no_resume w ->

    switcher_trap_safety -∗
    (⌜switcher_fault_pc w⌝ ∨
     (no_handler (top_export_tbl cstk) ∗
      ⌜(top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)⌝)) -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       world_interp W C ∗
       interp_cont interp cstk Ws Cs ∗
       na_own cerise_nais ⊤ ∗
       cstack_frag cstk) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hfull_rmap Hframe Hno_resume) "#Hsafety Hcase Hres".
    iApply (trap_safe_unwind_of_safety with "Hsafety"); [done |].
    iMod "Hres" as "(Hrmap & Hworld_interp & Hcont & Hna & Hcstk)".
    iModIntro. iFrame "Hrmap Hna Hcstk". iRight.
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".
    iNamed "Hsafety".
    iPoseProof (logrel_unwind_cont_gen with "Hinv_switcher Hstatic Htrap Hworld_interp Hcont")
      as "HU"; [done |].
    iDestruct "Hcase" as "[%Hpc | [Hnh %Hset] ]".
    - by iApply (trap_handler_ok_switcher with "HU").
    - by iApply (trap_handler_ok_no_handler with "Hnh HU").
  Qed.

End Switcher_trap_safety.
