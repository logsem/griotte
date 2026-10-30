From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import logrel fundamental switcher_preamble interp_switcher_return.
From griotte Require Import
  switcher_spec_install copy_context_spec world_ghost_theory wp_rules_interp.
From griotte.switcher.failure Require Import common_force_unwind switch_stack_too_small.
From griotte.switcher.callback Require Import switcher_zero_callee_frame.
From griotte.switcher.exception Require Import handle_error_handler_invoke exception_path.
From griotte Require Import switcher_unwind.
From griotte Require Export switcher_error_handler switcher_trap_safety.

(** * Exception entry of the switcher

    The exception path ([exception_entry_asm], see [exception_path])
    spills the interrupted context, then looks for an error handler of the
    faulting compartment. It reads the registers of the faulting
    compartment only to spill them, so its safety needs no validity of the
    register file, except when it resumes the faulting context (a fault of
    the first spill of the call path returns [-ENOTENOUGHSTACK] to the
    caller) or invokes an untrusted handler, which runs through the FTLR
    with the invocation registers (the [ErrorState] of a stackful one is
    stored in the world, through the faulting [csp]).

    It is a safe trap vector ([switcher_trap_vector_safe]) for the faults
    in an untrusted compartment ([untrusted_fault]) and for the faults that
    it handles ([trap_handler_ok]): with no handler (or for a fault in the
    switcher, or of a running handler) the switcher unwinds the call; a
    trusted compartment's handler runs through its table's
    [execute_error_handler], a stackful one with the [ErrorState] written
    in the slot that the fault site lends. This closes the faults of
    trusted code ([trap_safe_unwind], [trap_safe_exception_entry]); a
    resumed fault of trusted code is closed by [trap_safe_resume]. A
    handler returns to the switcher, which unwinds
    ([switcher_handler_return_unwind]) or installs the context of the
    [ErrorState] at the handler's stack pointer
    ([switcher_handler_return_install]); for an untrusted handler, both
    are safe ([interp_handler_return_sentry]). The
    file also hosts the safety of the return-to-switcher entry point
    ([interp_expr_switcher_return], [interp_switcher_return]), which needs
    the trap vector and would otherwise form an import cycle. *)

Section Switcher_Exception.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The return to the caller of the context that the exception path
      resumes, at [.Lswitch_just_return]: with safe registers, in an
      untrusted topmost compartment, the jump to [cra] is safe, or faults. *)
  Lemma switcher_just_return_safe (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    thread_in th C -∗
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    top_cmpt_untrusted interp W C cstk -∗
    switcher_static -∗
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_just_return" -∗
    registers_pointsto rmap -∗
    world_interp W C -∗
    interp_cont interp cstk Ws Cs -∗
    na_own (tpool th) ⊤ -∗
    ◯(CSTK)[th] cstk -∗
    safe[th].
  Proof.
    iIntros (Hfull Hframe) "#Htrap #Hthread #Hregs #Htop #Hstatic HPC Hrmap Hworld_interp Hcont Hna Hcstk".
    iPoseProof "Hstatic" as "[#Hswitcher _]".
    iDestruct (trap_vector_safe_untrusted with "Htrap") as "#Htv".
    iEval (rewrite -world_resources_exclusive) in "Hworld_interp".
    iPoseProof (shared_credit_exclusive C) as "Hcred".
    iAssert (interp_reg interp W C rmap) as "#Hregs_interp".
    { by iApply interp_reg_intro. }
    rewrite /registers_pointsto.
    getRegValList [cra].
    iDestruct ("Hregs" $! cra wcra with "[//]") as "#Hinterp_wcra".
    iExtract "Hrmap" cra as "Hcra".
    iApply (switcher_just_return_spec with "[- $HPC $Hcra $Hswitcher]").
    iSplit.
    - (* The jump to [cra] *)
      iNext; iIntros "(HPC & Hcra & Hlc)".
      iInsert "Hrmap" cra.
      rewrite insert_id //.
      iDestruct (jmp_or_fail_spec with "Hinterp_wcra") as "Hjmp".
      destruct (decide (isCorrectPC (updatePcPerm wcra.(lw)))) as [Hpc | Hpc]; cycle 1.
      { (* The return address is not a valid PC: the jump faults *)
        iApply "Hjmp"; iFrame "HPC".
        iApply (interp_trap_safe_untrusted with
                 "Htrap Hthread Hregs_interp Htop [$Hrmap $Hworld_interp $Hcred $Hcont $Hna $Hcstk]");
          done. }
      iDestruct "Hjmp" as (p g b e a π) "(%Hwcra_target & #Hjmp)".
      iAssert (future_world g W W) as "Hfuture".
      { destruct g; cbn; iPureIntro; [ done
                                     | apply related_sts_pub_refl_world]. }
      iSpecialize ("Hjmp" $! W with "Hfuture").
      iDestruct (lc_fupd_elim_later with "Hlc Hjmp") as ">Hjmp'".
      iApply ("Hjmp'" $! cstk Ws Cs rmap); iFrame "∗ #".
      done.
    - (* The jump faults *)
      iIntros "(_ & Hcra)".
      iInsert "Hrmap" cra.
      rewrite insert_id //.
      iApply (interp_trap_safe_untrusted with
               "Htrap Hthread Hregs_interp Htop [$Hrmap $Hworld_interp $Hcred $Hcont $Hna $Hcstk]");
        done.
  Qed.

  (** ** Small lemmas *)

  (** The destination of the [ErrorState] stores for an untrusted topmost
      compartment: the world, through the safe faulting [csp]. A [csp] of
      a heap object is checked first. If the object is quarantined, the
      tag of [csp] is cleared, and the stores fault. Otherwise its first
      cell stays open while the path runs. *)
  Lemma untrusted_error_state_acc (W : WORLD) (C : CmptName) (cstk : CSTK)
    (w : LWord) (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    registers_pointsto rmap -∗
    world_interp W C -∗
    (∀ (rmap' : LReg) (D : nat → iProp Σ),
       ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
       (∀ (r : RegName) (v : LWord), ⌜rmap' !! r = Some v⌝ → interp W C v) -∗
       registers_pointsto rmap' -∗
       D 0 -∗
       path_es_acc cstk w rmap' D -∗
       ▷ (∀ k, D k -∗ world_interp W C) -∗
       safe[th]) -∗
    safe[th].
  Proof.
    iIntros (Hfull) "#Hregs Hrmap Hworld_interp Hcont".
    destruct (Hfull csp) as [wcsp Hwcsp].
    assert (rmap !!! csp = wcsp) as Hcsp by by rewrite (lookup_total_correct _ _ _ Hwcsp).
    iAssert (interp W C wcsp) as "#Hcsp_interp"; first by iApply "Hregs".
    (* The stores through [csp] in the world, as it is *)
    iAssert (⌜∀ p g b e a ι, wcsp = Cap p g b e a @@? Some ι →
               ¬ error_state_first_store_ok wcsp⌝ -∗
             path_es_acc cstk w rmap (λ _, world_interp W C))%I as "#Hplain".
    { iIntros (Hnoheap).
      iIntros "!>" (eh p g b e a π _ _) "_ _ %Hcsp' %Hok".
      rewrite Hcsp in Hcsp' Hok. rewrite Hcsp' in Hok Hnoheap.
      destruct π as [ι|]; first by exfalso; eapply Hnoheap.
      rewrite /error_state_first_store_ok /= in Hok. destruct Hok as (Hwa & Hb & He).
      iApply (world_interp_cells_store_acc _ _ _ g b e).
      - done.
      - rewrite /ErrorState_size in Hb |- *. solve_addr.
      - done.
      - rewrite (interp_cap_cur_addr W C true p g b e (a ^+ (- ErrorState_size)) a None).
        by rewrite -Hcsp'.
      - by iApply interp_error_state_src. }
    destruct (decide (error_state_first_store_ok wcsp)) as [Hok|Hnok]; cycle 1.
    { iApply ("Hcont" $! rmap (λ _, world_interp W C)
               with "[//] Hregs Hrmap Hworld_interp [] []"); last by iIntros "!> % $".
      iApply "Hplain". iPureIntro. by intros ? ? ? ? ? ? _. }
    destruct wcsp as [wcsp [ι|] ]; cycle 1.
    { iApply ("Hcont" $! rmap (λ _, world_interp W C)
               with "[//] Hregs Hrmap Hworld_interp [] []"); last by iIntros "!> % $".
      iApply "Hplain". iPureIntro. by intros ? ? ? ? ? ? [=]. }
    assert (∃ p g b e a, wcsp = Cap p g b e a) as (p & g & b & e & a & ->).
    { rewrite /error_state_first_store_ok /= in Hok.
      destruct wcsp as [|[ [] p g b e a|]| |]; try done; by do 5 eexists. }
    pose proof Hok as (Hwa & Hb & He).
    rewrite /ErrorState_size in Hb He.
    (* A heap [csp]: its first cell, or a tombstone *)
    iMod (world_interp_cells_store_acc_heap W C p g b e (a ^+ (- ErrorState_size)) ι
            (error_state_src w rmap) with "[] [] Hworld_interp")
      as "[ [#Hq Hworld_interp] | (%D & HD0 & #Hacc & Hclose)]".
    { done. }
    { rewrite /ErrorState_size. solve_addr. }
    { rewrite /ErrorState_size. solve_addr. }
    { by rewrite (interp_cap_cur_addr W C true p g b e (a ^+ (- ErrorState_size)) a (Some ι)). }
    { by iApply interp_error_state_src. }
    - (* A tombstone: [ι] is quarantined, the tag of [csp] is cleared *)
      iDestruct (interp_cap_has_authority W C p g b e a (a ^+ (- ErrorState_size)) ι
                   with "Hcsp_interp") as %Hauth.
      { by apply writeAllowed_nonO. }
      { apply withinBounds_true_iff. rewrite /ErrorState_size. solve_addr. }
      rewrite /registers_pointsto.
      iDestruct (big_sepM_insert_acc with "Hrmap") as "[Hcspr Hrmap]"; first exact Hwcsp.
      iMod (reg_refilter _ csp (Cap p g b e a @@? Some ι) ι Hauth eq_refl with "Hq Hcspr")
        as "Hcspr".
      iDestruct ("Hrmap" with "Hcspr") as "Hrmap".
      iApply ("Hcont" $! _ (λ _, world_interp W C) with "[] [] Hrmap Hworld_interp [] []");
        last by iIntros "!> % $".
      + iPureIntro. intros r. rewrite lookup_insert_is_Some'. by right.
      + iIntros (r v Hv). destruct (decide (r = csp)) as [-> | Hne].
        * rewrite lookup_insert_eq in Hv. simplify_eq. iApply interp_clear_tag.
        * rewrite lookup_insert_ne in Hv; last done. by iApply "Hregs".
      + iIntros "!>" (eh p' g' b' e' a' π' _ _) "_ _ %Hcsp' _".
        by rewrite lookup_total_insert_eq in Hcsp'.
    - (* The first cell: the stores go through the open world *)
      iApply ("Hcont" $! rmap D with "[//] Hregs [Hrmap] HD0 [] Hclose"); first done.
      iIntros "!>" (eh p' g' b' e' a' π' _ _) "_ _ %Hcsp' _".
      rewrite Hcsp in Hcsp'. injection Hcsp' as <- <- <- <- <- <-.
      iExact "Hacc".
  Qed.

  (** The source of the context that the switcher installs for an
      untrusted handler: the world, through the handler's safe [csp]. As
      for the [ErrorState] stores, a [csp] of a quarantined object is
      untagged first, and otherwise its first cell stays open. *)
  #[local] Lemma untrusted_install_acc (W : WORLD) (C : CmptName) (rmap : LReg) (n : nat) :
    (∀ r, is_Some (rmap !! r)) →
    thread_in th C -∗
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    registers_pointsto rmap -∗
    world_interp W C -∗
    (∀ (rmap' : LReg) (L : nat → list LWord → iProp Σ),
       ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
       ⌜∀ r, r ≠ csp → rmap' !! r = rmap !! r⌝ -∗
       (∀ (r : RegName) (v : LWord), ⌜rmap' !! r = Some v⌝ → interp W C v) -∗
       registers_pointsto rmap' -∗
       L 0 [] -∗
       (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
          ⌜rmap' !!! csp = Cap p g b e a @@? π⌝ -∗
          ⌜readAllowed p = true ∧ (b <= a)%a⌝ -∗
          cells_load_acc L p e a π n) -∗
       ▷ (∀ i ls, L i ls -∗ world_interp W C ∗ [∗ list] v ∈ ls, interp W C v) -∗
       safe[th]) -∗
    safe[th].
  Proof.
    iIntros (Hfull) "#Hthread #Hregs Hrmap Hworld_interp Hcont".
    destruct (Hfull csp) as [wcsp Hwcsp].
    assert (rmap !!! csp = wcsp) as Hcsp by by rewrite (lookup_total_correct _ _ _ Hwcsp).
    iAssert (interp W C wcsp) as "#Hcsp_interp"; first by iApply "Hregs".
    set (Lw := λ (_ : nat) (ls : list LWord),
                 (world_interp W C ∗ [∗ list] v ∈ ls, interp W C v)%I).
    (* The loads through [csp] in the world, as it is *)
    iAssert (⌜∀ p g b e a ι, wcsp = Cap p g b e a @@? Some ι →
               readAllowed p = true → (b <= a)%a → (e <= a)%a⌝ -∗
             ∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
               ⌜rmap !!! csp = Cap p g b e a @@? π⌝ -∗
               ⌜readAllowed p = true ∧ (b <= a)%a⌝ -∗
               cells_load_acc Lw p e a π n)%I as "#Hplain".
    { iIntros (Hnoheap p g b e a π Hcsp') "[%Hra %Hb]".
      rewrite Hcsp in Hcsp'.
      destruct π as [ι|].
      - specialize (Hnoheap p g b e a ι Hcsp' Hra Hb).
        iIntros "!>" (i ls _ Hie). exfalso. solve_addr.
      - iApply (world_interp_cells_load_acc _ _ _ g b e with "Hthread"); [done | done | done |].
        by rewrite -Hcsp'. }
    destruct wcsp as [wcsp [ι|] ]; cycle 1.
    { iApply ("Hcont" $! rmap Lw with "[//] [//] Hregs Hrmap [Hworld_interp] [] []").
      - by iFrame.
      - iApply "Hplain". iPureIntro. by intros ? ? ? ? ? ? [=].
      - by iIntros "!> % % $". }
    assert ((∃ p g b e a, wcsp = Cap p g b e a ∧
               readAllowed p = true ∧ (b <= a)%a ∧ (a < e)%a) ∨
            (∀ p g b e a, wcsp = Cap p g b e a →
               readAllowed p = true → (b <= a)%a → (e <= a)%a))
      as [(p & g & b & e & a & -> & Hra & Hba & Hae) | Hnoheap].
    { destruct wcsp as [z|[ [] p g b e a|]| |]; try (right; by intros ? ? ? ? ? [=]).
      destruct (decide (readAllowed p = true ∧ (b <= a)%a ∧ (a < e)%a)) as [Hok|Hnok].
      - left. by do 5 eexists.
      - right. intros ? ? ? ? ? [= <- <- <- <- <-] Hra Hba.
        destruct (decide (a < e)%a); [exfalso; by apply Hnok | solve_addr]. }
    2: { iApply ("Hcont" $! rmap Lw with "[//] [//] Hregs Hrmap [Hworld_interp] [] []").
         - by iFrame.
         - iApply "Hplain". iPureIntro.
           intros p g b e a ι' Heq. injection Heq as Heq _. by eapply Hnoheap.
         - by iIntros "!> % % $". }
    (* A heap [csp]: its first cell, or a tombstone *)
    iMod (world_interp_cells_load_acc_heap W C p g b e a ι n Hra Hba Hae
            with "Hthread Hcsp_interp Hworld_interp")
      as "[ [#Hq Hworld_interp] | (%L & HL0 & #Hacc & Hclose)]".
    - (* A tombstone: [ι] is quarantined, the tag of [csp] is cleared *)
      iDestruct (interp_cap_has_authority W C p g b e a a ι with "Hcsp_interp") as %Hauth.
      { by apply readAllowed_nonO. }
      { apply withinBounds_true_iff. solve_addr. }
      rewrite /registers_pointsto.
      iDestruct (big_sepM_insert_acc with "Hrmap") as "[Hcspr Hrmap]"; first exact Hwcsp.
      iMod (reg_refilter _ csp (Cap p g b e a @@? Some ι) ι Hauth eq_refl with "Hq Hcspr")
        as "Hcspr".
      iDestruct ("Hrmap" with "Hcspr") as "Hrmap".
      iApply ("Hcont" $! _ Lw with "[] [] [] Hrmap [Hworld_interp] [] []").
      + iPureIntro. intros r. rewrite lookup_insert_is_Some'. by right.
      + iPureIntro. intros r Hr. by rewrite lookup_insert_ne.
      + iIntros (r v Hv). destruct (decide (r = csp)) as [-> | Hne].
        * rewrite lookup_insert_eq in Hv. simplify_eq. iApply interp_clear_tag.
        * rewrite lookup_insert_ne in Hv; last done. by iApply "Hregs".
      + by iFrame.
      + iIntros (p' g' b' e' a' π' Hcsp') "_".
        by rewrite lookup_total_insert_eq in Hcsp'.
      + by iIntros "!> % % $".
    - (* The first cell: the loads go through the open world *)
      iApply ("Hcont" $! rmap L with "[//] [//] Hregs Hrmap HL0 [] Hclose").
      iIntros (p' g' b' e' a' π' Hcsp') "_".
      rewrite Hcsp in Hcsp'. injection Hcsp' as <- <- <- <- <- <-.
      iExact "Hacc".
  Qed.

  (** A tagged capability that a [Lea] of a safe word gives is safe:
      [interp] does not read the cursor. *)
  Lemma interp_lea_result_cap (W : WORLD) (C : CmptName) (w : LWord) (z : Z)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) :
    lea_result w z = Some (Cap p g b e a @@? π) →
    interp W C w -∗ interp W C (Cap p g b e a @@? π).
  Proof.
    destruct w as [w π0]. rewrite /lea_result /=.
    destruct w as [n | [t p0 g0 b0 e0 a0 | t p0 g0 b0 e0 a0] | k t p0 g0 b0 e0 a0 | ot sb];
      cbn; try (intros Hlea; by inversion Hlea).
    - destruct (a0 + z)%a as [a1|]; intros Hlea; inversion Hlea; subst.
      iIntros "#H". by rewrite (interp_cap_cur_addr W C true p g b e a a0 π).
    - destruct (a0 + z)%ot; intros Hlea; by inversion Hlea.
  Qed.

  (** The destination of the [ErrorState] stores for a trusted topmost
      compartment with trusted handlers: the slot that the fault site lends,
      then, once the first word is written, the cells below the end of the
      faulting [csp], with the two facts of the site on it. *)
  Definition trusted_error_state (eh : Z) (w : LWord) (rmap : LReg) (i : nat) : iProp Σ :=
    match i with
    | 0%nat => error_state_slot eh rmap
    | S _ =>
        ⌜(rmap !!! csp).(lprov) = None⌝ ∗
        ⌜error_state_lent_shadow_free (rmap !!! csp)⌝ ∗
        error_state_cells w rmap i
    end.

  (** The [ErrorState], written in part, is a slot. *)
  Lemma trusted_error_state_slot (eh : Z) (w : LWord) (rmap : LReg) (k : nat) :
    trusted_error_state eh w rmap k -∗ error_state_slot eh rmap.
  Proof.
    destruct k as [|k]; first by iIntros "H".
    iIntros "(%Hprov & %Hshadow & Hcells)".
    iDestruct (error_state_cells_lent with "Hcells") as "Hlent".
    rewrite /error_state_slot.
    case_decide; last done. by iFrame.
  Qed.

  (** The stores to the lent slot: the first one opens the slot, which
      holds the part of the slot below the end of the faulting [csp] when
      the table declares the stackful handler [eh]. *)
  Lemma trusted_error_state_acc (cstk : CSTK) (w : LWord) (rmap : LReg) (eh : Z) :
    top_export_tbl cstk ↦ₑ□{stackful} eh -∗
    path_es_acc cstk w rmap (trusted_error_state eh w rmap).
  Proof.
    iIntros "#Heh !>" (eh' p g b e a π _ _) "#Heh' %Hsome %Hcsp %Hok".
    iDestruct (handler_stackful_agree with "Heh Heh'") as %<-.
    pose proof Hok as Hok'.
    rewrite /error_state_first_store_ok Hcsp /= in Hok'. destruct Hok' as (Hwa & Hb & He).
    iIntros "!>" (i Hi Hie) "Hes".
    rewrite length_error_state_src in Hi.
    iAssert (⌜π = None⌝ ∗ ⌜error_state_lent_shadow_free (rmap !!! csp)⌝ ∗
             error_state_cells w rmap i)%I with "[Hes]" as "(-> & %Hshadow & Hcells)".
    { destruct i as [|i]; cbn [trusted_error_state].
      - rewrite /error_state_slot decide_True; last done.
        iDestruct "Hes" as "(%Hprov & %Hsh & Hlent)".
        rewrite Hcsp in Hprov. rewrite error_state_cells_0. by iFrame.
      - iDestruct "Hes" as "(%Hprov & $ & $)". by rewrite Hcsp in Hprov. }
    iDestruct (error_state_cells_acc with "Hcells") as (v) "[Hv Hclose]";
      [exact Hcsp | done | done | done |].
    iModIntro. iExists v, 1%Qp. iFrame "Hv". iSplit.
    { iPureIntro. eapply (error_state_lent_not_shadow (rmap !!! csp)); try done.
      by rewrite Hcsp. }
    iSplitR; first iApply deref_res_none.
    iIntros "!> Hv _ !>". iDestruct ("Hclose" with "Hv") as "Hcells".
    cbn [trusted_error_state]. iFrame "Hcells".
    iPureIntro. split; [by rewrite Hcsp | done].
  Qed.

  (** The header of the table of an untrusted topmost compartment. *)
  Lemma top_cmpt_untrusted_header (W : WORLD) (C : CmptName) (cstk : CSTK) :
    top_cmpt_untrusted interp W C cstk -∗ handler_header cstk.
  Proof.
    iIntros "[(%pcc & %cgp & %eh & %ehs & #Hpcc & #Hcgp & #Heh & #Hehs & _ & %Htbl_set) _]".
    iSplit; first done.
    iExists eh, ehs. iFrame "Heh Hehs".
    iIntros "_". iExists pcc, cgp. iFrame "Hpcc Hcgp".
  Qed.

  (** The PCC and the CGP of the table of an untrusted topmost
      compartment, safe in the current world. *)
  Lemma top_cmpt_untrusted_pcc_cgp (W : WORLD) (C : CmptName) (cstk : CSTK) :
    top_cmpt_untrusted interp W C cstk -∗
    ∃ wpcc wcgp : LWord,
      top_export_tbl cstk ↦ₐ□ wpcc ∗
      (top_export_tbl cstk ^+ ExportTable_offset_cgp) ↦ₐ□ wcgp ∗
      interp W C wpcc ∗ interp W C wcgp.
  Proof.
    iIntros "[(%pcc & %cgp & %eh & %ehs & #Hpcc & #Hcgp & _ & _ & #Hsafe & _) _]".
    iExists pcc, cgp. iFrame "Hpcc Hcgp".
    iApply "Hsafe". iPureIntro. apply related_sts_priv_refl_world.
  Qed.

  (** At depth 0, the stackless handler's stack is the thread's stack,
      which the untrusted entry compartment holds. *)
  Lemma top_cmpt_untrusted_stackless_csp (W : WORLD) (C : CmptName) (cstk : CSTK) :
    cstk.(cstk_frames) = [] →
    top_cmpt_untrusted interp W C cstk -∗ interp W C (stackless_csp cstk).
  Proof.
    destruct cstk as [ef frms]; cbn. intros ->.
    rewrite /stackless_csp /=.
    iIntros "[_ (%p & %g & %b & %e & %a & _ & _ & #$)]".
  Qed.

  (** The handler's PC is safe when the table's PCC is: [interp] does not
      read the cursor of a capability. *)
  Lemma interp_handler_word (W : WORLD) (C : CmptName) (wpcc wpc : LWord) (off : Z) :
    handler_entry wpcc off = Some wpc →
    interp W C wpcc -∗ interp W C wpc.
  Proof.
    destruct wpcc as [w π]. rewrite /handler_entry.
    destruct_word w; try done.
    destruct (b + off)%a as [a'|]; cbn; last done.
    intros [= <-]. iIntros "H". by rewrite (interp_cap_cur_addr W C t c g b e a a' π).
  Qed.

  (** The stack of a stackless handler, the part of the topmost pushed
      frame's stack below the cursor, is safe. *)
  Lemma interp_cont_stackless_csp (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    frame_match Ws Cs cstk W C →
    top_frame_stack_ok cstk →
    cstk.(cstk_frames) ≠ [] →
    interp_continuation cstk Ws Cs -∗
    interp_continuation cstk Ws Cs ∗
    interp W C (stackless_csp cstk).
  Proof.
    destruct cstk as [ef [|frm frms] ]; first done.
    intros Hframe Hstack _.
    destruct (Hstack ltac:(done)) as (b_stk & e_stk & a_stk & Hcsp & Hb & Ha4).
    rewrite /top_tframe /= in Hcsp.
    destruct Ws as [|Wt Ws], Cs as [|Ct Cs]; try done.
    destruct Hframe as (Hrelated & <- & Hktk & _).
    rewrite /interp_continuation /interp_cont /= Hktk.
    iIntros "[Hrest [#Hcallee Htop] ]". iFrame "Hrest Htop Hcallee".
    rewrite (tf_caller_a_saved (cf_tframe frm) true RWL Local b_stk e_stk a_stk Ha4);
      last by rewrite Hcsp.
    rewrite /stackless_csp /= Hcsp /tf_stk_b /tf_stk_e Hcsp /=.
    iDestruct "Hcallee" as "[%Hheap Hcallee]".
    stk_unfold.
    iDestruct (interp_monotone_cap_nonheap with "Hcallee") as "Hcallee'";
      [exact Hheap | exact Hrelated |].
    iApply (interp_weakeningEO_gen with "[] Hcallee'"); try done.
    1,2: destruct (is_untrusted_caller_frm frm); solve_addr.
    iIntros "!>" (Hg _); discriminate Hg.
  Qed.

  (** ** The handler return *)

  (** From [.Lhandle_error_handler_return], with [ca0] non-zero, the
      switcher force-unwinds the call ([.Lhandle_error_handler_return] and
      [.Lcommon_force_unwind]). *)
  #[local] Lemma switcher_handler_return_force_unwind (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    nonZero (rmap !!! ca0).(lw) = true →
    switcher_static -∗
    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_return" -∗
    registers_pointsto rmap -∗
    (∀ rmap' : LReg,
       ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
       ⌜rmap' !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
       ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
       PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_return -∗
       registers_pointsto rmap' -∗
       safe[th]) -∗
    safe[th].
  Proof.
    iIntros (Hfull Hnz) "#Hstatic HPC Hrmap Hpost".
    iPoseProof "Hstatic" as "[#Hcode _]".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    assert (rmap !!! ca0 = wca0) as Hrmap_ca0 by (rewrite lookup_total_alt Hwca0; done).
    rewrite Hrmap_ca0 in Hnz.
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (handle_error_handler_return_spec with "[- $HPC $Hca0 $Hcode]").
    iNext; iSplit; last (iIntros (Hnz'); by rewrite Hnz in Hnz').
    iIntros (_) "(HPC & Hca0)".
    iApply (common_force_unwind_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1)".
    iEval (rewrite -switcher_return_offset) in "HPC".
    iInsertList "Hrmap" [ca0;ca1].
    iApply ("Hpost" with "[] [] [] HPC Hrmap").
    - iPureIntro. intros r. rewrite !lookup_insert_is_Some'. clear -Hfull. naive_solver.
    - iPureIntro. rewrite lookup_insert_ne //. apply lookup_insert_eq.
    - iPureIntro. apply lookup_insert_eq.
  Qed.

  (** A trusted handler returns to the switcher with [ca0] non-zero: the
      switcher unwinds the call through the unwind continuation of the
      fault site. *)
  Lemma switcher_handler_return_unwind
    (F : coPset) (cstk : CSTK) (n : Z) (R_unwind_stk : iProp Σ) (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    nonZero (rmap !!! ca0).(lw) = true →
    switcher_static -∗
    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_return" -∗
    registers_pointsto rmap -∗
    ◯(CSTK)[th] (cstack_set_top_count cstk n) -∗
    unwind_cont F cstk R_unwind_stk -∗
    R_unwind_stk -∗
    na_own (tpool th) F -∗
    safe[th].
  Proof.
    iIntros (Hfull Hnz) "#Hstatic HPC Hrmap Hcstk HU HS Hna".
    iApply (switcher_handler_return_force_unwind with "Hstatic HPC Hrmap"); [done | done |].
    iIntros (rmap' Hfull' Hca0 Hca1) "HPC Hrmap".
    iApply ("HU" with "[//] [//] [//] HPC Hrmap Hcstk HS Hna").
  Qed.

  (** An untrusted handler returns to the switcher with [ca0] zero: the
      switcher installs the context of the [ErrorState] at the handler's
      safe [csp]. The loaded words are safe, and so is the resumed PC, from
      the safe PCC of the topmost table: the installed context runs through
      the FTLR, with the count of the topmost frame incremented. A fault of
      the installation is a fault in the switcher, which unwinds. *)
  #[local] Lemma untrusted_handler_install_safe
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    nonZero (rmap !!! ca0).(lw) = false ->
    frame_match Ws Cs cstk W C ->

    thread_in th C -∗
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec) -∗
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    top_cmpt_untrusted interp W C cstk -∗
    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_return" -∗
    registers_pointsto rmap -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    na_own (tpool th) ⊤ -∗
    ◯(CSTK)[th] cstk -∗
    safe[th].
  Proof.
    iIntros (Hfull Hnz Hframe)
      "#Hthread #Hinv_switcher #Hstatic #Htrap #Hregs #Htop HPC Hrmap Hworld_interp Hcont Hna Hcstk".
    (* The source of the context, through [csp] *)
    iApply (untrusted_install_acc W C rmap (Z.to_nat ErrorState_size)
              with "Hthread Hregs Hrmap Hworld_interp"); first done.
    iIntros (rmap' L Hfull' Hsame) "#Hregs' Hrmap HL0 #Hacc Hclose".
    assert (nonZero (rmap' !!! ca0).(lw) = false) as Hnz'.
    { by rewrite !lookup_total_alt Hsame. }
    (* The PCC of the topmost table is safe *)
    iDestruct (top_cmpt_untrusted_pcc_cgp with "Htop")
      as (wpcc wcgp) "(#Hpcc & _ & #Hpcc_interp & _)".
    iDestruct (top_cmpt_untrusted_header with "Htop") as "[%Htbl_set _]".
    iApply (switcher_install_context_spec ⊤ cstk rmap' wpcc L
             with "[- ]"); [set_solver | set_solver | done | done | done |].
    iFrame "Hinv_switcher Hstatic HPC Hrmap Hna Hcstk Hpcc".
    iSplitL "HL0"; first iExact "HL0".
    iSplitR; first iExact "Hacc".
    iNext. iSplit.
    - (* A fault of the installation: the switcher unwinds *)
      iIntros (_ off rmap'' i ls Hno_resume Hfull'') "Hrmap Hcstk HL Hna".
      iDestruct ("Hclose" with "HL") as "[Hworld_interp _]".
      iApply (interp_trap_safe with "Htrap"); first done.
      iModIntro. iFrame "Hrmap Hna Hcstk". iRight.
      iApply trap_handler_ok_switcher; [done | apply switcher_fault_pc_cap |].
      by iApply (logrel_unwind_cont_gen with "Hthread Hinv_switcher Hstatic Htrap Hworld_interp Hcont").
    - (* The installed context runs through the FTLR *)
      iIntros (ls Hls) "HPC Hrmap Hcstk HL Hna".
      iDestruct ("Hclose" with "HL") as "[Hworld_interp #Hls_interp]".
      iAssert (interp W C (llegalise mepcc (resumed_pc wpcc (get_a (ls !!! 0%nat).(lw)))))
        as "#Hwpc".
      { iApply interp_llegalise_mepcc. by iApply interp_resumed_pc. }
      iDestruct (fundamental with "Hwpc") as "Hexpr".
      iDestruct (trap_vector_safe_untrusted with "Htrap") as "#Htv".
      iEval (rewrite -world_resources_exclusive) in "Hworld_interp".
      iPoseProof (shared_credit_exclusive C) as "Hcred".
      iApply ("Hexpr" $! (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) Ws Cs
                (error_state_install rmap' (drop 1 ls)) with "[- ]").
      iFrame "Hthread Htv HPC Hrmap Hworld_interp Hcred Hna Hcstk".
      rewrite top_cmpt_untrusted_set_top_count interp_cont_set_top_count.
      iFrame "Htop Hcont".
      iSplit; last (iPureIntro; by apply frame_match_set_top_count).
      iApply interp_reg_intro; first by apply error_state_install_full.
      iIntros (r v Hv).
      rewrite /error_state_install lookup_union_Some_raw in Hv.
      destruct Hv as [Hv | [_ Hv] ]; last by iApply "Hregs'".
      apply elem_of_list_to_map_2, elem_of_zip_r in Hv.
      iApply (big_sepL_elem_of with "Hls_interp").
      by apply (subseteq_drop 1 ls).
  Qed.

  (** The handler-return entry point is safe to execute, for a safe trap
      vector: with [ca0] non-zero, the switcher unwinds, and with [ca0] zero, it installs the context of the
      [ErrorState]. *)
  Lemma interp_expr_handler_return_gen (W : WORLD) (C : CmptName) :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec)
    ⊢ interp_expr interp (interp_cont interp) W C
        (switcher_label_pc ".Lhandle_error_handler_return").
  Proof.
    iIntros "(#Hinv_switcher & #Hstatic & #Htrap) %cstk %Ws %Cs %rmap
             (#Hthread & #Htv & Hregs & #Htop & HPC & Hrmap & Hworld_interp & Hcred & Hcont_K
              & Hna & Hcstk & %Hframe)".
    iEval (rewrite world_resources_exclusive) in "Hworld_interp".
    iDestruct "Hregs" as "[%Hfull_rmap #Hregs]".
    cbn in Hfull_rmap. change LReg in rmap.
    destruct (nonZero (rmap !!! ca0).(lw)) eqn:Hnz.
    - (* [ca0] non-zero: the switcher unwinds *)
      iApply (switcher_handler_return_force_unwind with "Hstatic HPC Hrmap"); [done | done |].
      iIntros (rmap' Hfull' Hca0 Hca1) "HPC Hrmap".
      iApply (switcher_return_unwind with
               "[$HPC $Hrmap $Hthread $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont_K $Hna $Hcstk]");
        [done | done | done | done |].
      iSplit; iApply interp_int.
    - (* [ca0] zero: the switcher installs the context *)
      iApply (untrusted_handler_install_safe with
               "Hthread Hinv_switcher Hstatic Htrap Hregs Htop HPC Hrmap Hworld_interp Hcont_K Hna Hcstk");
        done.
  Qed.

  (** The sentry that the switcher gives a handler is safe, for a safe trap
      vector (needed only under the sentry's later). *)
  Lemma interp_handler_return_sentry_gen
    (W : WORLD) (C : CmptName) (mie : InterruptStatus) :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    ▷ trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec)
    ⊢ interp W C (handler_return_sentry mie).
  Proof.
    iIntros "(#Hinv & #Hstatic & #Htrap)".
    rewrite /handler_return_sentry interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext; iApply (interp_expr_handler_return_gen with "[$Hinv $Hstatic $Htrap]"); done.
  Qed.

  (** ** Untrusted handlers *)

  (** A handler of an untrusted topmost compartment runs through the FTLR:
      its PC comes from the table's PCC, and the invocation registers are
      safe (the return sentry, the table's CGP, integers, and the stack:
      for a stackless handler, the stack below the frame's cursor; for a
      stackful one, the faulting [csp], safe, with other cursors). *)
  Lemma untrusted_handler_invoke_safe
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (kind : handler_kind) (wpcc wcgp wpc : LWord) (off mcause mtval : Z)
    (regs : LReg) :
    frame_match Ws Cs cstk W C ->
    top_frame_stack_ok cstk ->
    handler_entry wpcc off = Some wpc ->
    handler_invocation_regs kind cstk wcgp rmap mcause mtval regs ->

    thread_in th C -∗
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec) -∗
    top_cmpt_untrusted interp W C cstk -∗
    top_export_tbl cstk ↦ₐ□ wpcc -∗
    (top_export_tbl cstk ^+ ExportTable_offset_cgp) ↦ₐ□ wcgp -∗
    interp W C (rmap !!! csp) -∗
    PC ↦ₚ[th] wpc -∗
    registers_pointsto regs -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    ◯(CSTK)[th] (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) -∗
    na_own (tpool th) ⊤ -∗
    safe[th].
  Proof.
    iIntros (Hframe Hstack Hentry Hinv_regs)
      "#Hthread #Hinv_switcher #Hstatic #Htrap #Htop #Hpcc #Hcgp #Hcsp_fault HPC Hregs Hworld_interp
       Hcont Hcstk Hna".
    iAssert (interp W C wpcc ∗ interp W C wcgp)%I as "[#Hpcc_interp #Hcgp_interp]".
    { iDestruct (top_cmpt_untrusted_pcc_cgp with "Htop")
        as (pcc cgp) "(Hpcc' & Hcgp' & Hpcc_i & Hcgp_i)".
      iDestruct (pointsto_agree with "Hpcc Hpcc'") as %->.
      iDestruct (pointsto_agree with "Hcgp Hcgp'") as %->.
      iFrame "Hpcc_i Hcgp_i". }
    iDestruct (interp_handler_word with "Hpcc_interp") as "#Hwpc"; first exact Hentry.
    destruct Hinv_regs as (Hfull & [mie Hcra] & Hcgp_r & Hkind & Hzero).
    (* The stack and the arguments *)
    iAssert (∃ wcsp wca0 wca1 wca2 : LWord,
               ⌜regs !! csp = Some wcsp⌝ ∗ ⌜regs !! ca0 = Some wca0⌝ ∗
               ⌜regs !! ca1 = Some wca1⌝ ∗ ⌜regs !! ca2 = Some wca2⌝ ∗
               interp W C wcsp ∗ interp W C wca0 ∗ interp W C wca1 ∗ interp W C wca2 ∗
               interp_continuation cstk Ws Cs)%I
      with "[Hcont]"
      as (wcsp wca0 wca1 wca2 Hcsp_r Hca0 Hca1 Hca2)
           "(#Hcsp_interp & #Hca0_interp & #Hca1_interp & #Hca2_interp & Hcont)".
    { destruct kind.
      - destruct Hkind as (_ & wcsp & wa0 & Hsf & Hcsp_r & Hca0 & Hca1 & Hca2).
        iDestruct (interp_stackful_regs with "Hcsp_fault") as "[Hcsp_i Ha0_i]";
          first exact Hsf.
        iExists wcsp, wa0, _, _.
        do 4 (iSplit; first done).
        iFrame "Hcont Hcsp_i Ha0_i".
        iSplit; iApply interp_int.
      - destruct Hkind as (Hcsp_r & Hca0 & Hca1 & Hca2).
        iAssert (interp_continuation cstk Ws Cs ∗ interp W C (stackless_csp cstk))%I
          with "[Hcont]" as "[Hcont #Hcsp_i]".
        { destruct (cstk_frames cstk) as [|frm frms] eqn:Hframes.
          - (* depth 0: the thread's stack, held by the entry compartment *)
            iFrame "Hcont". by iApply top_cmpt_untrusted_stackless_csp.
          - iApply (interp_cont_stackless_csp with "Hcont");
              [done | done | by rewrite Hframes]. }
        iExists _, _, _, _.
        do 4 (iSplit; first done).
        iFrame "Hcont Hcsp_i".
        iSplit; [iApply interp_int | iSplit; iApply interp_int]. }
    clear Hkind.
    iDestruct (fundamental with "Hwpc") as "Hexpr".
    iDestruct (trap_vector_safe_untrusted with "Htrap") as "#Htv".
    iEval (rewrite -world_resources_exclusive) in "Hworld_interp".
    iPoseProof (shared_credit_exclusive C) as "Hcred".
    iApply ("Hexpr" $! (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) Ws Cs regs
             with "[- ]").
    iFrame "Hthread Htv HPC Hregs Hworld_interp Hcred Hna Hcstk".
    rewrite top_cmpt_untrusted_set_top_count interp_cont_set_top_count.
    iFrame "Htop Hcont".
    iSplit; last (iPureIntro; by apply frame_match_set_top_count).
    iApply interp_reg_intro; first done.
    iIntros (r v Hv).
    destruct (decide (r = cra)) as [-> | Hr_cra].
    { rewrite Hcra in Hv. simplify_eq.
      iApply (interp_handler_return_sentry_gen with "[$Hinv_switcher $Hstatic $Htrap]"); done. }
    destruct (decide (r = cgp)) as [-> | Hr_cgp].
    { rewrite Hcgp_r in Hv. by simplify_eq. }
    destruct (decide (r = csp)) as [-> | Hr_csp].
    { rewrite Hcsp_r in Hv. by simplify_eq. }
    destruct (decide (r = ca0)) as [-> | Hr_ca0].
    { rewrite Hca0 in Hv. by simplify_eq. }
    destruct (decide (r = ca1)) as [-> | Hr_ca1].
    { rewrite Hca1 in Hv. by simplify_eq. }
    destruct (decide (r = ca2)) as [-> | Hr_ca2].
    { rewrite Hca2 in Hv. by simplify_eq. }
    rewrite Hzero in Hv; first (simplify_eq; iApply interp_int).
    clear -Hr_cra Hr_cgp Hr_csp Hr_ca0 Hr_ca1 Hr_ca2. set_solver.
  Qed.

  (** ** The trap vector *)

  (** A fault of the exception path itself is a fault in the switcher: the
      unwind continuation is built from the destination of the [ErrorState]
      stores, after any number of them. *)
  Lemma exception_entry_safe_nested (F : coPset) (cstk : CSTK)
    (w : LWord) (rmap : LReg) (error_state_written : nat → iProp Σ) :
    ↑Ntstack ⊆ F →
    ↑Ntrap ⊆ F →
    exception_entry_safe -∗
    (∀ k : nat,
       ⌜(k <= Z.to_nat ErrorState_size)%nat⌝ -∗
       error_state_written k -∗
       unwind_cont F cstk True) -∗
    path_nested_fault F cstk w rmap error_state_written.
  Proof.
    iIntros (HF HFtrap) "#Hsafe HU _".
    iIntros (off n rmap' Hno_resume Hfull) "Hrmap Hcstk (%k & %Hk & Hes) Hna".
    iSpecialize ("HU" with "[//] Hes").
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    iApply ("Hsafe" $! mcause_ok (λ _ : Z, True%type) F (cstack_set_top_count cstk n) rmap'
              (switcher_pc off) with
             "[//] [//] [//] [//] [HU] HPC Hout Hrmap Hna Hcstk").
    iRight. iApply trap_handler_ok_switcher; [done | apply switcher_fault_pc_cap |].
    by rewrite unwind_cont_set_top_count.
  Qed.

  (** The forced unwind, with the unwind continuation built from the
      destination of the [ErrorState] stores before any of them. *)
  Lemma unwind_cont_path_unwind_k (F : coPset) (cstk : CSTK) (w : LWord) (rmap : LReg)
    (error_state_written : nat → iProp Σ) :
    (error_state_written 0 -∗ unwind_cont F cstk True) -∗
    path_unwind_k F cstk w rmap error_state_written.
  Proof.
    iIntros "HU" (_) "_". iIntros (n rmap' Hfull Hca0 Hca1) "HPC Hrmap Hcstk Hes Hna".
    iApply ("HU" with "Hes [//] [//] [//] HPC Hrmap Hcstk [//] Hna").
  Qed.

  (** A fault in an untrusted compartment: the switcher unwinds, resumes the caller, or invokes one of the
      compartment's handlers, which runs through the FTLR. The [ErrorState]
      of a stackful handler is stored in the world, through [csp]: a [csp]
      of a quarantined object is untagged first. The cause satisfies the
      cause predicate [P_mcause] of fault causes; the value is any. *)
  Lemma exception_entry_untrusted_safe (P_mcause P_mtval : Z → Prop)
    (cstk : CSTK) (rmap : LReg) (w : LWord) :
    (∀ c, P_mcause c → mcause_ok c) ->
    (∀ r, is_Some (rmap !! r)) ->

    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe -∗
    untrusted_fault cstk rmap -∗
    PC ↦ₚ[th] lword_of_word mtcc_vec -∗
    trap_entry_out_cause P_mcause P_mtval w -∗
    registers_pointsto rmap -∗
    na_own (tpool th) (⊤ ∖ ↑Ntrap) -∗
    ◯(CSTK)[th] cstk -∗
    safe[th].
  Proof.
    iIntros (HP_mcause Hfull_rmap)
      "#Hinv_switcher #Hstatic #Hsafe Huntrusted HPC Hout Hrmap Hna Hcstk".
    iDestruct "Huntrusted" as (W C Ws Cs Hframe)
      "(Hregs & #Htop & Hworld_interp & _ & #Hthread & Hcont)".
    iEval (rewrite world_resources_exclusive) in "Hworld_interp".
    iDestruct "Hregs" as "[_ #Hregs]".
    iApply (untrusted_error_state_acc W C cstk w rmap with "Hregs Hrmap Hworld_interp");
      first done.
    iIntros (rmap' D Hfull_rmap') "#Hregs' Hrmap HD0 #Hacc Hclose".
    iDestruct (top_cmpt_untrusted_header with "Htop") as "#Hheader".
    iApply (switcher_exception_path_spec P_mcause P_mtval ⊤ cstk (cstack_frag cstk)
              D with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcstk HD0 Hcont Hclose]");
      [done | set_solver | set_solver | done |].
    iSplitL "Hcstk"; first by case_decide.
    iSplitR; first (iIntros "_"; iExact "Hheader").
    iSplitL "HD0"; first iExact "HD0".
    iSplitR; first iExact "Hacc".
    iNext.
    iPoseProof (exception_entry_safe_vector with "Hsafe") as "#Htrap".
    iSplit; [|iSplit; [|iSplit] ].
    - (* The forced unwind *)
      iApply unwind_cont_path_unwind_k. iIntros "HD".
      iDestruct ("Hclose" with "HD") as "Hworld_interp".
      by iApply (logrel_unwind_cont_gen with "Hthread Hinv_switcher Hstatic Htrap Hworld_interp Hcont").
    - (* The resumed caller returns to [cra], with safe registers *)
      iIntros (_ rmap'' Hfull_rmap'' Hsame Hca0 Hca1) "HPC Hrmap Hcstk HD Hna".
      iDestruct ("Hclose" with "HD") as "Hworld_interp".
      iApply (switcher_just_return_safe with
               "Htrap Hthread [] Htop Hstatic HPC Hrmap Hworld_interp Hcont Hna Hcstk"); [done | done |].
      iIntros (r v Hv).
      destruct (decide (r = ca0)) as [-> | Hr0].
      { rewrite Hca0 in Hv. simplify_eq. iApply interp_int. }
      destruct (decide (r = ca1)) as [-> | Hr1].
      { rewrite Hca1 in Hv. simplify_eq. iApply interp_int. }
      rewrite Hsame in Hv; [| done | done].
      by iApply "Hregs'".
    - (* A fault of the path *)
      iIntros (_).
      iApply (exception_entry_safe_nested with "Hsafe"); [set_solver | set_solver |].
      iIntros (k _) "HD".
      iDestruct ("Hclose" with "HD") as "Hworld_interp".
      by iApply (logrel_unwind_cont_gen with "Hthread Hinv_switcher Hstatic Htrap Hworld_interp Hcont").
    - (* A handler *)
      iIntros (kind wpcc wcgp wpc off mcause mtval regs _ _ Hstack _ _ _ Hentry Hinv_regs)
        "_ Hpcc Hcgp _ HPC Hregs_h Hcstk HD Hna".
      iDestruct ("Hclose" with "HD") as "Hworld_interp".
      iApply (untrusted_handler_invoke_safe with
               "Hthread Hinv_switcher Hstatic Htrap Htop Hpcc Hcgp [] HPC Hregs_h Hworld_interp Hcont
                Hcstk Hna"); [done | done | done | done |].
      iApply "Hregs'". iPureIntro.
      destruct (Hfull_rmap' csp) as [v Hv]. by rewrite (lookup_total_correct _ _ _ Hv).
  Qed.

  (** A fault in the switcher, in a compartment whose table declares no
      handler, or in a running trusted handler (odd count): the switcher
      unwinds; a nested fault of the path is a fault in the switcher. The
      cause satisfies the cause predicate [P_mcause] of fault causes. *)
  Lemma exception_entry_unwind_safe (P_mcause P_mtval : Z → Prop) (F : coPset)
    (cstk : CSTK) (rmap : LReg) (w : LWord) :
    (∀ c, P_mcause c → mcause_ok c) ->
    ↑Ntstack ⊆ F ->
    ↑Ntrap ⊆ F ->
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume w ->
    (¬ switcher_fault_pc w → (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)) ->

    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe -∗
    unwind_cont F cstk True -∗
    (⌜switcher_fault_pc w⌝ ∨
     no_handler (top_export_tbl cstk) ∨
     (⌜Z.odd (top_error_count cstk) = true⌝ ∗
      ∃ eh ehs : Z,
        top_export_tbl cstk ↦ₑ□{stackful} eh ∗
        top_export_tbl cstk ↦ₑ□{stackless} ehs)) -∗
    PC ↦ₚ[th] lword_of_word mtcc_vec -∗
    trap_entry_out_cause P_mcause P_mtval w -∗
    registers_pointsto rmap -∗
    na_own (tpool th) (F ∖ ↑Ntrap) -∗
    ◯(CSTK)[th] cstk -∗
    safe[th].
  Proof.
    iIntros (HP_mcause HF HFtrap Hfull_rmap Hno_resume Htbl_set)
      "#Hinv_switcher #Hstatic #Hsafe HU #Hcase HPC Hout Hrmap Hna Hcstk".
    iAssert (⌜¬ switcher_fault_pc w⌝ → handler_header cstk)%I as "#Hheader".
    { iIntros (Hnot). iSplit; first (iPureIntro; by apply Htbl_set). rewrite /no_handler.
      iDestruct "Hcase" as "[%Hpc | [[Heh Hehs] | [%Hodd (%eh & %ehs & Heh & Hehs)] ] ]";
        first done.
      - iExists _, _. iFrame "Heh Hehs". iIntros ([ [Hne | Hne] _]); by contradict Hne.
      - iExists eh, ehs. iFrame "Heh Hehs". iIntros ([_ Hev]).
        exfalso. rewrite -Z.negb_odd Hodd in Hev. done. }
    iApply (switcher_exception_path_spec P_mcause P_mtval F cstk (cstack_frag cstk)
              (λ _, True%I) with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcstk HU]");
      [done | done | done | done |].
    iSplitL "Hcstk"; first by case_decide.
    iSplitR; first iExact "Hheader".
    iSplitR; first done.
    iSplitR.
    { (* No store of the [ErrorState] *)
      iIntros "!>" (eh p g b e a π Hnot Hev) "#Heh %Hsome _ _".
      rewrite /no_handler.
      iDestruct "Hcase" as "[%Hpc | [ [Hnone _] | [%Hodd _] ] ]"; first done.
      - iDestruct (handler_stackful_agree with "Hnone Heh") as %Heq. by subst eh.
      - exfalso. rewrite -Z.negb_odd Hodd in Hev. done. }
    iNext.
    iSplit; [|iSplit; [|iSplit] ].
    - iApply unwind_cont_path_unwind_k. by iIntros "_".
    - by iIntros (Hresume).
    - iIntros (_). iApply (exception_entry_safe_nested with "Hsafe"); [done | done |].
      by iIntros (k _) "_".
    - iIntros (kind wpcc wcgp wpc off mcause mtval regs Hnot Hev _ Hoff _ _ _ _)
        "_ _ _ #Hoff _ _ _ _ _".
      rewrite /no_handler.
      iDestruct "Hcase" as "[%Hpc | [ [Hnone Hnone'] | [%Hodd _] ] ]"; first done.
      + destruct kind; cbn [handler_offset].
        * iDestruct (handler_stackful_agree with "Hnone Hoff") as %Heq. by subst off.
        * iDestruct (handler_stackless_agree with "Hnone' Hoff") as %Heq. by subst off.
      + exfalso. rewrite -Z.negb_odd Hodd in Hev. done.
  Qed.

  (** A fault in a trusted compartment whose table declares trusted
      handlers, at the site's token [F]: the switcher invokes a handler,
      through the table's [execute_error_handler], or unwinds. An unwind
      happens only when the stackful handler is not invoked, which the
      site's unwind continuation covers. The [ErrorState] of a stackful
      handler is stored in the slot that the fault site lends. The handler
      receives [P_fault] at the cause and the value, which satisfy the cause
      predicate [P_mcause] of fault causes and the value predicate
      [P_mtval]. *)
  Lemma exception_entry_trusted_handler_safe (P_mcause P_mtval : Z → Prop) (F : coPset)
    (cstk : CSTK) (rmap : LReg) (w : LWord)
    (P_fault : coPset → CSTK → LWord → LReg → Z → Z → iProp Σ) (eh : Z) :
    (∀ c, P_mcause c → mcause_ok c) ->
    ↑Ntstack ⊆ F ->
    ↑Ntrap ⊆ F ->
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume w ->
    (¬ switcher_fault_pc w → (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)) ->

    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe -∗
    trusted_handler (top_export_tbl cstk) P_fault -∗
    top_export_tbl cstk ↦ₑ□{stackful} eh -∗
    error_state_slot eh rmap -∗
    (unwind_or_runs F cstk w rmap (error_state_slot eh rmap) ∧
     ∀ c v : Z, ⌜P_mcause c⌝ -∗ ⌜P_mtval v⌝ -∗ P_fault F cstk w rmap c v) -∗
    PC ↦ₚ[th] lword_of_word mtcc_vec -∗
    trap_entry_out_cause P_mcause P_mtval w -∗
    registers_pointsto rmap -∗
    na_own (tpool th) (F ∖ ↑Ntrap) -∗
    ◯(CSTK)[th] cstk -∗
    safe[th].
  Proof.
    iIntros (HP_mcause HF HFtrap Hfull_rmap Hno_resume Htbl_set)
      "#Hinv_switcher #Hstatic #Hsafe #Hhandler #Heh_site Hslot HUP HPC Hout Hrmap Hna Hcstk".
    iDestruct "Hhandler" as (wpcc wcgp eh' ehs)
      "(#Hpcc & #Hcgp & #Heh & #Hehs & #Hexec_sf & #Hexec_sl)".
    iDestruct (handler_stackful_agree with "Heh_site Heh") as %<-.
    (* The handler's WP, for this fault *)
    iAssert (□ ∀ (kind : handler_kind) (off mcause mtval : Z) (wpc : LWord) (regs : LReg),
               ▷ ( handler_offset kind (top_export_tbl cstk) off -∗
                   ⌜off ≠ ExportTable_no_handler⌝ -∗
                   switcher_res F -∗
                   ⌜top_export_tbl cstk = top_export_tbl cstk⌝ -∗
                   ⌜Z.even (top_error_count cstk) = true⌝ -∗
                   ⌜mcause_ok mcause⌝ -∗
                   ⌜handler_entry wpcc off = Some wpc⌝ -∗
                   ⌜handler_invocation_regs kind cstk wcgp rmap mcause mtval regs⌝ -∗
                   PC ↦ₚ wpc -∗
                   registers_pointsto regs -∗
                   handler_slot kind w rmap -∗
                   (⌜kind = Stackless⌝ → handler_skipped cstk w rmap) -∗
                   (unwind_or_runs F cstk w rmap (handler_unwind_res kind rmap) ∧
                    P_fault F cstk w rmap mcause mtval) -∗
                   cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
                   na_own (tpool th) F -∗
                   WP Exec {{ HO th }} ))%I
      as "#Hrun".
    { iIntros "!>" (kind off mcause mtval wpc regs).
      destruct kind; cbn [handler_offset].
      - destruct (decide (eh = ExportTable_no_handler)) as [Hnone | Hsome].
        + iNext. iIntros "#Hoff" (Hsome).
          iDestruct (handler_stackful_agree with "Heh Hoff") as %<-. done.
        + iDestruct ("Hexec_sf" with "[//]") as "#Hexec'".
          iSpecialize ("Hexec'" $! F cstk w rmap mcause mtval wpc regs).
          iNext. iIntros "#Hoff _".
          iDestruct (handler_stackful_agree with "Heh Hoff") as %<-. iExact "Hexec'".
      - destruct (decide (ehs = ExportTable_no_handler)) as [Hnone | Hsome].
        + iNext. iIntros "#Hoff" (Hsome).
          iDestruct (handler_stackless_agree with "Hehs Hoff") as %<-. done.
        + iDestruct ("Hexec_sl" with "[//]") as "#Hexec'".
          iSpecialize ("Hexec'" $! F cstk w rmap mcause mtval wpc regs).
          iNext. iIntros "#Hoff _".
          iDestruct (handler_stackless_agree with "Hehs Hoff") as %<-. iExact "Hexec'". }
    (* The switcher's resources, for the handler *)
    iAssert (switcher_res F) as "#Hswitcher_res".
    { by iFrame "Hinv_switcher Hstatic". }
    iApply (switcher_exception_path_spec P_mcause P_mtval F cstk (cstack_frag cstk)
              (trusted_error_state eh w rmap) with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcstk Hslot HUP]");
      [done | done | done | done |].
    iSplitL "Hcstk"; first by case_decide.
    iSplitR.
    { iIntros (Hnot). iSplit; first (iPureIntro; by apply Htbl_set).
      iExists eh, ehs. iFrame "Heh Hehs".
      iIntros "_". iExists wpcc, wcgp. iFrame "Hpcc Hcgp". }
    iSplitL "Hslot"; first iExact "Hslot".
    iSplitR; first by iApply trusted_error_state_acc.
    iNext.
    iSplit; [|iSplit; [|iSplit] ].
    - (* The unwind: the stackful handler is not invoked *)
      iIntros (Hno) "#Hskip".
      iDestruct "HUP" as "[ [Hruns | HU] _]".
      { iDestruct (handler_runs_skipped with "Hruns Hskip") as %[]. }
      iApply (unwind_cont_path_unwind_k with "[HU] [//] Hskip"). iIntros "Hslot".
      iApply (unwind_cont_give with "Hslot HU").
    - by iIntros (Hresume).
    - (* A fault of the path: the stackful handler is not invoked *)
      iIntros (_) "#Hskip".
      iDestruct "HUP" as "[ [Hruns | HU] _]".
      { iDestruct (handler_runs_skipped with "Hruns Hskip") as %[]. }
      iApply (exception_entry_safe_nested with "Hsafe [HU] Hskip"); [done | done |].
      iIntros (k _) "Hes". iApply (unwind_cont_give with "[Hes] HU").
      by iApply trusted_error_state_slot.
    - iIntros (kind wpcc' wcgp' wpc off mcause mtval regs _ Hev _ Hoff_some Hmcause Htval
                Hentry Hinv_regs)
        "#Hskip_sl #Hpcc' #Hcgp' #Hoff HPC Hregs Hcstk Hes Hna".
      iDestruct (pointsto_agree with "Hpcc Hpcc'") as %<-.
      iDestruct (pointsto_agree with "Hcgp Hcgp'") as %<-.
      pose proof (HP_mcause _ Hmcause) as Hmcause_ok.
      destruct kind.
      + (* Stackful: the written [ErrorState] goes to the handler, with the
           two facts of the site; the unwind continuation takes back the
           slot *)
        iAssert ⌜off = eh⌝%I as %->.
        { iApply (handler_stackful_agree with "Hoff Heh"). }
        pose proof Hinv_regs as (_ & _ & _ & [Hok _] & _).
        iDestruct "Hes" as "(%Hprov & %Hshadow & Hcells)".
        iEval (rewrite error_state_cells_full //) in "Hcells".
        iApply ("Hrun" with
                 "Hoff [//] Hswitcher_res [//] [//] [//] [//] [//] HPC Hregs [$Hcells] Hskip_sl
                  [HUP] Hcstk Hna").
        { iPureIntro. split; first done. by apply error_state_lent_shadow_free_full. }
        iSplit; last (iDestruct "HUP" as "[_ HP]"; by iApply "HP").
        iDestruct "HUP" as "[ [Hruns | HU] _]"; first by iLeft. iRight.
        iApply (unwind_cont_weaken with "[] HU").
        iIntros "Harea". rewrite /error_state_slot decide_True;
          last (split; [done | by apply error_state_stores_ok_first]).
        iDestruct (error_state_area_lent with "Harea") as "Hlent"; first done.
        by iFrame.
      + (* Stackless *)
        iApply ("Hrun" with
                 "Hoff [//] Hswitcher_res [//] [//] [//] [//] [//] HPC Hregs [//] Hskip_sl
                  [HUP Hes] Hcstk Hna").
        iSplit; last (iDestruct "HUP" as "[_ HP]"; by iApply "HP").
        iDestruct "HUP" as "[ [Hruns | HU] _]"; first by iLeft. iRight.
        iApply (unwind_cont_give with "Hes HU").
  Qed.

  (** The exception entry is safe, by Löb induction: the exception path
      needs it only after its first instruction, and a nested fault of the
      path enters it again under the later of trap entry. *)
  Lemma switcher_exception_entry_safe :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ exception_entry_safe.
  Proof.
    iIntros "[#Hinv_switcher #Hstatic]".
    iLöb as "IH".
    iIntros "!>" (P_mcause P_mtval F cstk rmap w HP_mcause HF HFtrap Hfull)
      "Hfault HPC Hout Hrmap Hna Hcstk".
    iDestruct "Hfault" as "[[-> Huntrusted] | Hhandled]".
    { iApply (exception_entry_untrusted_safe with
               "Hinv_switcher Hstatic IH Huntrusted HPC Hout Hrmap Hna Hcstk"); done. }
    iDestruct (trap_handler_ok_cases with "Hhandled")
      as (Hno_resume Htbl_set) "[ [HU Hcase] | [Hrow | (HU & %Hodd & Hheader)] ]".
    - (* A fault in the switcher, or no handler *)
      iApply (exception_entry_unwind_safe with
               "Hinv_switcher Hstatic IH HU [Hcase] HPC Hout Hrmap Hna Hcstk"); [done.. |].
      iDestruct "Hcase" as "[Hcase | Hcase]"; [by iLeft | iRight; by iLeft].
    - (* Trusted handlers *)
      iDestruct "Hrow" as (P_fault eh) "(Hhandler & Heh & Hslot & HUP)".
      iApply (exception_entry_trusted_handler_safe with
               "Hinv_switcher Hstatic IH Hhandler Heh Hslot HUP HPC Hout Hrmap Hna Hcstk");
        done.
    - (* A fault in a running trusted handler *)
      iApply (exception_entry_unwind_safe with
               "Hinv_switcher Hstatic IH HU [Hheader] HPC Hout Hrmap Hna Hcstk"); [done.. |].
      iRight; iRight. by iFrame.
  Qed.

  (** The resume of a fault of the first spill of the call path: after
      trap entry, the switcher spills the registers, overwrites the return
      values with [-ENOTENOUGHSTACK] and 0, and installs the context again,
      at [.Lswitch_just_return]. The non-atomic token [F] provides the
      trap-entry token, and the exception path opens the trusted-stack
      invariant with the rest of [F]. *)
  Lemma switcher_resume_safe_intro :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ switcher_resume_safe.
  Proof.
    iIntros "[#Hinv_switcher #Hstatic] !>" (F w HF HFtrap Hresume) "Hres".
    (* A resumed fault is in the switcher *)
    assert (switcher_fault_pc w) as Hpc.
    { rewrite /switcher_fault_pc.
      destruct (decide (get_b (lmepcc_of_pc w).(lw) = (b_switcher : Z))) as [Hb | Hb];
        first done.
      exfalso. apply Hresume. by left. }
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iMod "Hres" as (rmap Hfull_rmap) "(Hna & Hrmap & Hcont)".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    (* The path only resumes: its call stack is not used, any one does *)
    iApply (switcher_exception_path_spec mcause_ok (λ _ : Z, True%type) F
              (entry_cstack (MkTFrame (WInt 0) (WInt 0) 0)) True (λ _, True%I) rmap with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcont]");
      [done | exact HF | exact HFtrap | exact Hfull_rmap |].
    rewrite decide_False; last exact Hresume.
    iSplitR; first done.
    iSplitR; first by iIntros (Hnot).
    iSplitR; first done.
    iSplitR; first by iIntros "!>" (eh p g b e a π Hnot).
    iNext; iSplit; [|iSplit; [|iSplit] ].
    - by iIntros (Hno_resume).
    - iIntros (_ rmap' Hfull' Hsame Hca0 Hca1) "HPC Hrmap _ _ Hna".
      iApply ("Hcont" with "[//] [//] [//] [//] HPC Hrmap Hna").
    - by iIntros (Hnot).
    - by iIntros (kind wpcc wcgp wpc off mcause mtval regs Hnot).
  Qed.

  (** The trap safety of the switcher, from its invariant and static
      resources. *)
  Lemma switcher_trap_safety_intro :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ switcher_trap_safety.
  Proof.
    iIntros "#Hres".
    iPoseProof (switcher_exception_entry_safe with "Hres") as "#Hentry_safe".
    iPoseProof (switcher_resume_safe_intro with "Hres") as "#Hresume_safe".
    iDestruct "Hres" as "[Hinv_switcher Hstatic]".
    iFrame "Hinv_switcher Hstatic Hentry_safe Hresume_safe".
  Qed.

  (** The trap vector of the machine, the exception entry of the switcher,
      is safe, for the faults in an untrusted compartment and for the
      faults that it handles ([trap_handler_ok ⊤]). *)
  Lemma switcher_mtcc_vec_safe :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec).
  Proof.
    iIntros "Hres".
    iApply switcher_mtcc_vec_safe_of_safety.
    by iApply switcher_trap_safety_intro.
  Qed.

  (** The exception entry of the switcher is a safe trap vector. *)
  Lemma switcher_trap_vector_safe :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ trap_vector_safe (trap_handler_ok ⊤) (switcher_label_pc "exception_entry_asm").
  Proof.
    iIntros "[#Hinv_switcher #Hstatic]".
    iPoseProof "Hstatic" as "(_ & _ & %Hmtcc & _)".
    rewrite -Hmtcc.
    iApply (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hstatic]"); done.
  Qed.

  (** The unwind continuation from the logical relation's resources. *)
  Lemma logrel_unwind_cont (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    frame_match Ws Cs cstk W C →
    thread_in th C -∗
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    unwind_cont ⊤ cstk True.
  Proof.
    iIntros (Hframe) "#Hthread #Hinv #Hstatic Hworld Hcont".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (logrel_unwind_cont_gen with "Hthread Hinv Hstatic Htrap Hworld Hcont").
  Qed.

  (** The handler-return entry point is safe to execute. *)
  Lemma interp_expr_handler_return (W : WORLD) (C : CmptName) :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C
        (switcher_label_pc ".Lhandle_error_handler_return").
  Proof.
    iIntros "[#Hinv #Hstatic]".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (interp_expr_handler_return_gen with "[$Hinv $Hstatic $Htrap]").
  Qed.

  (** The sentry that the switcher gives a handler is safe. *)
  Lemma interp_handler_return_sentry
    (W : WORLD) (C : CmptName) (mie : InterruptStatus) :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ interp W C (handler_return_sentry mie).
  Proof.
    iIntros "[#Hinv #Hstatic]".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (interp_handler_return_sentry_gen with "[$Hinv $Hstatic $Htrap]").
  Qed.

  (** The callee's stack is smaller than the minimum stack size of the
      entry point plus the reserved space: [.Lswitch_stack_too_small] sets
      the return values, and the return routine pops the frame already
      pushed. No register needs to be safe. *)
  Lemma switcher_call_stack_too_small_unwind
    (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_too_small" ∗
    registers_pointsto rmap ∗
    thread_in th C ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own (tpool th) ⊤ ∗
    ◯(CSTK)[th] cstk
    ⊢ safe[th].
  Proof.
    iIntros (Hfull_rmap Hframe)
      "(HPC & Hrmap & #Hthread & #Hinv_switcher & #Hstatic & Hworld_interp & Hcont & Hna & Hcstk)".
    iPoseProof (switcher_trap_safety_intro with "[$Hinv_switcher $Hstatic]") as "#Hsafety".
    iApply (switcher_call_stack_too_small_unwind_of_safety with
             "[$HPC $Hrmap $Hthread $Hsafety $Hworld_interp $Hcont $Hna $Hcstk]"); done.
  Qed.

  (** A fault closes through the exception path of the switcher: after
      trap entry, the switcher handles the fault
      ([trap_handler_ok_cause P_mcause P_mtval F]), for a cause predicate
      [P_mcause] of fault causes and a value predicate [P_mtval]. The
      resources come under an update at the time of the fault; the
      non-atomic token [F] provides the trap-entry token, and the exception
      path opens the trusted-stack invariant with the rest of [F]. *)
  Lemma trap_safe_exception_entry (P_mcause P_mtval : Z → Prop) (F : coPset) (w : LWord) :
    (∀ c, P_mcause c → mcause_ok c) →
    ↑Ntstack ⊆ F →
    ↑Ntrap ⊆ F →
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    (|={⊤}=>
       ∃ (rmap : LReg) (cstk : CSTK),
         ⌜∀ r, is_Some (rmap !! r)⌝ ∗
         na_own (tpool th) F ∗
         registers_pointsto rmap ∗
         ◯(CSTK)[th] cstk ∗
         trap_handler_ok_cause P_mcause P_mtval F cstk w rmap) -∗
    trap_safe_cause P_mcause P_mtval w ⊤ (HO th).
  Proof.
    iIntros (HP_mcause HF HFtrap) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_trap_safety_intro with "[$Hinv_switcher $Hstatic]") as "#Hsafety".
    by iApply (trap_safe_exception_entry_of_safety with "Hsafety Hres").
  Qed.

  (** A fault that the exception path resumes (a fault of the first spill
      of the call path) closes through the exception path of the switcher:
      after trap entry, the switcher spills the registers, overwrites the
      return values with [-ENOTENOUGHSTACK] and 0, and installs the context
      again, at [.Lswitch_just_return]. The resources come under an update
      at the time of the fault; the non-atomic token [F] provides the
      trap-entry token, and the exception path opens the trusted-stack
      invariant with the rest of [F]. *)
  Lemma trap_safe_resume (F : coPset) (w : LWord) :
    ↑Ntstack ⊆ F →
    ↑Ntrap ⊆ F →
    ¬ trap_no_resume w →
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    (|={⊤}=>
       ∃ rmap : LReg,
         ⌜∀ r, is_Some (rmap !! r)⌝ ∗
         na_own (tpool th) F ∗
         registers_pointsto rmap ∗
         (∀ rmap' : LReg,
            ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
            ⌜∀ r, r ≠ ca0 → r ≠ ca1 → rmap' !! r = rmap !! r⌝ -∗
            ⌜rmap' !! ca0 = Some (WInt ENOTENOUGHSTACK : LWord)⌝ -∗
            ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
            PC ↦ₚ[th] switcher_label_pc ".Lswitch_just_return" -∗
            registers_pointsto rmap' -∗
            na_own (tpool th) F -∗
            safe[th])) -∗
    trap_safe w ⊤ (HO th).
  Proof.
    iIntros (HF HFtrap Hresume) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_trap_safety_intro with "[$Hinv_switcher $Hstatic]") as "#Hsafety".
    by iApply (trap_safe_resume_of_safety with "Hsafety Hres").
  Qed.

  (** A fault in trusted code is safe: after exception entry, the exception
      entry of the switcher unwinds the call of the faulting compartment, or
      resumes a fault in an untrusted compartment. The resources and the
      fault's justification come under an update at the time of the fault
      (for instance, to close an invariant). *)
  Lemma trap_safe_unwind (cstk : CSTK) (rmap : LReg) (w : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       na_own (tpool th) ⊤ ∗
       ◯(CSTK)[th] cstk ∗
       (untrusted_fault cstk rmap ∨ trap_handler_ok ⊤ cstk w rmap)) -∗
    trap_safe w ⊤ (HO th).
  Proof.
    iIntros (Hfull_rmap) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_trap_safety_intro with "[$Hinv_switcher $Hstatic]") as "#Hsafety".
    by iApply (trap_safe_unwind_of_safety with "Hsafety Hres").
  Qed.

  (** A fault in trusted code, with the logical relation's resources, in
      the switcher ([switcher_fault_pc w]) or in a compartment whose table
      declares no handler and whose frame's table word is set: the switcher unwinds the call of the faulting
      compartment through the return routine. *)
  Lemma trap_safe_unwind_logrel
    (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (w : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->
    trap_no_resume w ->

    thread_in th C -∗
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    (⌜switcher_fault_pc w⌝ ∨
     (no_handler (top_export_tbl cstk) ∗
      ⌜(top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)⌝)) -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       world_interp W C ∗
       interp_cont interp cstk Ws Cs ∗
       na_own (tpool th) ⊤ ∗
       ◯(CSTK)[th] cstk) -∗
    trap_safe w ⊤ (HO th).
  Proof.
    iIntros (Hfull_rmap Hframe Hno_resume) "#Hthread #Hinv_switcher #Hstatic Hcase Hres".
    iPoseProof (switcher_trap_safety_intro with "[$Hinv_switcher $Hstatic]") as "#Hsafety".
    by iApply (trap_safe_unwind_logrel_of_safety with "Hthread Hsafety Hcase Hres").
  Qed.

  (** A trusted handler returns to the switcher with [ca0] zero: the
      switcher installs the context of the [ErrorState] [ws], the 16 cells
      at the handler's [csp], a capability without identifier whose
      cells are outside the shadow table. The resumed PC is the PCC [wpcc]
      of the topmost table with the address of word 0, the registers hold
      words 1-15 as loaded through the permission of [csp], and the count
      of the topmost frame is incremented. The handler runs with the
      token [F] of its fault site; the word of the topmost frame's table is
      set. A fault of the installation ([csp] does not allow the loads:
      [install_skipped]) is a fault in the switcher, which unwinds. *)
  Lemma switcher_handler_return_install (F : coPset) (cstk : CSTK)
    (rmap : LReg) (wpcc : LWord) (p : Perm) (g : Locality) (b e a : Addr)
    (ws : list LWord) :
    ↑Ntstack ⊆ F →
    ↑Ntrap ⊆ F →
    (∀ r, is_Some (rmap !! r)) →
    nonZero (rmap !!! ca0).(lw) = false →
    (top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0) →
    rmap !!! csp = lword_of_word (Cap p g b e a) →
    is_Some (a + ErrorState_size)%a →
    disjoint_from_shadow a (a ^+ ErrorState_size) →
    length ws = Z.to_nat ErrorState_size →

    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    top_export_tbl cstk ↦ₐ□ wpcc ∗
    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_return" ∗
    registers_pointsto rmap ∗
    install_region a ws ∗
    ◯(CSTK)[th] cstk ∗
    na_own (tpool th) F ∗
    ▷ ( ( ⌜install_skipped cstk rmap⌝ -∗
          install_region a ws -∗
          unwind_cont F cstk True ) ∧
        ( install_region a ws -∗
          context_resume F (cstack_set_top_count cstk (top_error_count cstk + 1))
            (llegalise mepcc (resumed_pc wpcc (get_a (ws !!! 0%nat).(lw))))
            (error_state_install rmap (lload_word p <$> drop 1 ws)) ) )
    ⊢ safe[th].
  Proof.
    iIntros (HF HFtrap Hfull Hnz Htbl_set Hcsp [a_es Ha_es] Hshadow Hws)
      "(#Hinv_switcher & #Hstatic & #Hpcc & HPC & Hrmap & Hws & Hcstk & Hna & Hpost)".
    rewrite /install_region.
    assert (a ^+ ErrorState_size = a_es) as Ha_es' by solve_addr.
    rewrite Ha_es' in Hshadow.
    iRevert "Hws Hpost". rewrite Ha_es'. iIntros "Hws Hpost".
    assert ((a + length ws)%a = Some a_es) as Ha_end.
    { rewrite Hws. rewrite /ErrorState_size in Ha_es |- *. solve_addr. }
    iApply (switcher_install_context_spec F cstk rmap wpcc
              (λ (i : nat) (ls : list LWord),
                 [[ a , a_es ]] ↦ₐ [[ ws ]] ∗ ⌜ls = take i (lload_word p <$> ws)⌝)%I
             with "[- ]"); [done | done | done | done | done |].
    iFrame "Hinv_switcher Hstatic HPC Hrmap Hna Hcstk Hpcc".
    iSplitL "Hws"; first by iFrame.
    iSplitR.
    { iIntros (p' g' b' e' a' π' Hcsp' _).
      rewrite Hcsp in Hcsp'.
      injection Hcsp' as <- <- <- <- <- <-.
      rewrite -Hws.
      iApply (region_cells_load_acc p e a a_es ws Ha_end Hshadow). }
    iNext. iSplit.
    - (* A fault of the installation: the switcher unwinds *)
      iIntros (Hskipped off rmap' i ls Hno_resume Hfull') "Hrmap Hcstk [Hws _] Hna".
      iDestruct "Hpost" as "[Hfault _]".
      iApply (trap_safe_exception_entry mcause_ok (λ _ : Z, True%type)
                with "Hinv_switcher Hstatic");
        [done | done | done |].
      iModIntro. iExists rmap', cstk. iFrame "Hrmap Hna Hcstk". iSplit; first done.
      iApply trap_handler_ok_switcher; [done | apply switcher_fault_pc_cap |].
      by iApply ("Hfault" with "[//] Hws").
    - (* The context is installed *)
      iIntros (ls Hls) "HPC Hrmap Hcstk [Hws ->] Hna".
      iDestruct "Hpost" as "[_ Hresume]".
      rewrite take_ge; last by rewrite length_fmap Hws.
      destruct ws as [|w0 ws']; first done.
      iEval (rewrite fmap_cons /=) in "HPC".
      iEval (rewrite fmap_cons /=) in "Hrmap".
      rewrite get_a_lload_word.
      iApply ("Hresume" with "Hws [] HPC Hrmap Hcstk Hna").
      iPureIntro. by apply error_state_install_full.
  Qed.

  (** The return-to-switcher entry point is safe to execute: the return
      routine runs ([switcher_return_unwind]). *)
  Lemma interp_expr_switcher_return (W : WORLD) (C : CmptName) :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C (Cap XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "[#Hinv_switcher #Hstatic] %cstk %Ws %Cs %rmap
             (#Hthread & _ & Hregs & _ & HPC & Hrmap & Hworld_interp & _ & Hcont_K & Hna & Hcstk
              & %Hfreq)".
    iEval (rewrite world_resources_exclusive) in "Hworld_interp".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    iDestruct "Hregs" as "[%Hfull_rmap #Hrmap_interp]".
    change LReg in rmap.
    cbn in Hfull_rmap.
    getRegValList [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hthread $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont_K $Hna $Hcstk]");
      [done|done|done|done|].
    iSplit; iApply "Hrmap_interp"; done.
  Qed.

  Lemma interp_switcher_return (W : WORLD) (C : CmptName)
    (mie : InterruptStatus) :
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static
    ⊢ interp W C (Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "[#Hinv #Hstatic]".
    rewrite interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_return with "[$Hinv $Hstatic]"); done.
  Qed.


End Switcher_Exception.
