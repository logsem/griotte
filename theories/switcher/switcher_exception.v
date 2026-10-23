From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import logrel fundamental switcher_preamble switcher_return_blocks_1
  interp_switcher_return.
From griotte Require Import switcher_call_blocks_6 switcher_blocks_15_16 switcher_exception_blocks_6
  switcher_spec_exception switcher_spec_install copy_context_spec world_ghost_theory
  wp_rules_interp.
From griotte Require Export switcher_error_handler.

(** * Exception entry of the switcher

    The exception path ([exception_entry_asm], see [switcher_spec_exception])
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
    [ErrorState] below the handler's stack pointer
    ([switcher_handler_return_install]); for an untrusted handler, both
    are safe ([interp_handler_return_sentry]). The
    file also hosts the safety of the return-to-switcher entry point
    ([interp_expr_switcher_return], [interp_switcher_return]), which needs
    the trap vector and would otherwise form an import cycle. *)

Section Switcher_Exception.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Block 16 from [.Lswitch_just_return], where the exception path resumes
      a context: the return to [cra]. *)
  Lemma switcher_just_return_spec (wret : LWord) :
    PC ↦ₚ switcher_label_pc ".Lswitch_just_return" ∗
    cra ↦ᵣ wret ∗
    switcher_code ∗
    ( ▷ ( PC ↦ₚ lupdatePcPerm wret ∗
          cra ↦ᵣ wret ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
      ( ⌜jalr_target_ok cnull cra wret.(lw) = false⌝ ∗
        cra ↦ᵣ wret -∗
        trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hcra & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    rewrite (_ : (a_switcher_call ^+ switcher_label_offset ".Lswitch_just_return")%a =
                 (a_switcher_call ^+ switcher_label_offset ".Lswitcher_return_to_caller")%a);
      last by offsets_compute.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lswitcher_return_to_caller") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_return_block_16_spec _ _ _ _ ∅ with "[- $HPC $Hcra $Hcode]");
      first done.
    iSplitR; first by rewrite big_sepM_empty.
    iSplit.
    - iNext; iIntros "(HPC & Hcra & _ & _ & Hlc)".
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[$HPC $Hcra $Hlc]").
    - iIntros "(%Hjalr & Hcra & _)".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[$Hcra]"); done.
  Qed.

  (** The return to the caller of the context that the exception path
      resumes, at [.Lswitch_just_return]: with safe registers, in an
      untrusted topmost compartment, the jump to [cra] is safe, or faults. *)
  Lemma switcher_just_return_safe (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    top_cmpt_untrusted interp W C cstk -∗
    switcher_static -∗
    PC ↦ₚ switcher_label_pc ".Lswitch_just_return" -∗
    registers_pointsto rmap -∗
    world_interp W C -∗
    interp_cont interp cstk Ws Cs -∗
    na_own cerise_nais ⊤ -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfull Hframe) "#Htrap #Hregs #Htop #Hstatic HPC Hrmap Hworld_interp Hcont Hna Hcstk".
    iPoseProof "Hstatic" as "[#Hswitcher _]".
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
      iDestruct (jmp_or_fail_spec with "Htrap Hinterp_wcra") as "Hjmp".
      destruct (decide (isCorrectPC (updatePcPerm wcra.(lw)))) as [Hpc | Hpc]; cycle 1.
      { (* The return address is not a valid PC: the jump faults *)
        iApply "Hjmp"; iFrame "HPC".
        iApply (interp_trap_safe_untrusted with
                 "Htrap Hregs_interp Htop [$Hrmap $Hworld_interp $Hcont $Hna $Hcstk]");
          done. }
      iDestruct "Hjmp" as (p g b e a π) "(%Hwcra_target & #Hjmp)".
      iAssert (future_world g W W) as "Hfuture".
      { destruct g; cbn; iPureIntro; [ apply related_sts_priv_refl_world
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
               "Htrap Hregs_interp Htop [$Hrmap $Hworld_interp $Hcont $Hna $Hcstk]");
        done.
  Qed.

  (** ** Small lemmas *)

  (** The destination of the [ErrorState] stores for an untrusted topmost
      compartment: the world, through the safe faulting [csp]. *)
  Lemma untrusted_error_state_acc (W : WORLD) (C : CmptName) (cstk : CSTK) (w : LWord)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    path_es_acc cstk w rmap (λ _, world_interp W C).
  Proof.
    iIntros (Hfull) "#Hregs".
    iIntros "!>" (eh p g b e a π _ _) "_ _ %Hcsp %Hok".
    rewrite /error_state_stores_ok Hcsp /= in Hok. destruct Hok as (Hwa & Hb & He).
    iApply (world_interp_cells_store_acc _ _ _ g b e).
    - done.
    - done.
    - rewrite length_error_state_src /ErrorState_size. rewrite /ErrorState_size in He. lia.
    - rewrite -Hcsp. iApply "Hregs". iPureIntro.
      destruct (Hfull csp) as [v Hv]. by rewrite (lookup_total_correct _ _ _ Hv).
    - by iApply interp_error_state_src.
  Qed.

  (* TODO: move to wp_rules_interp.v *)
  (** The loads of [n] cells, safe in the world, through a safe capability
      with read permission, from its cursor: each load below the end opens
      the cell in the world, with the status witness of the world's heap
      provenance, and closes it as is. The loaded words are safe. *)
  Lemma world_interp_cells_load_acc (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (n : nat) :
    readAllowed p = true →
    (b <= a)%a →
    interp W C (WCap true p g b e a @@? π) -∗
    cells_load_acc (λ _ ls, world_interp W C ∗ [∗ list] v ∈ ls, interp W C v)%I p e a π n.
  Proof.
    iIntros (Hra Hb) "#Hinterp_src".
    iIntros "!>" (i ls Hi Hie) "[Hworld_interp #Hls]".
    set (ea := (a ^+ i)%a).
    assert (b <= ea < e)%a as Hbounds by (subst ea; solve_addr).
    assert (withinBounds b e ea = true) as Hwb by (apply withinBounds_true_iff; solve_addr).
    iDestruct (read_allowed_inv _ _ ea with "Hinterp_src")
      as (p' P Hflows Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & Hmono)"; [solve_addr | auto |].
    iDestruct (readAllowed_valid_cap_implies _ _ _ _ _ _ _ ea with "Hinterp_src")
      as %(ρ & Hρ & Hρ_not_revoked); [done | done |].
    iDestruct (interp_cap_addr_live _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hlive;
      [by eapply readAllowed_nonO | done |].
    iDestruct (interp_cap_not_shadow _ _ _ _ _ _ _ ea with "Hinterp_src") as %Hnot_shadow;
      [by eapply readAllowed_nonO | done |].
    iDestruct (open_world_interp W C (addr_key π ea) p' (safeC P) ρ with "Hrel Hworld_interp")
      as "(Hworld_interp & Hstate & (%v & WorldRes))";
      [exact Hlive | destruct ρ; auto; contradiction | exact Hρ |].
    iDestruct (WorldRes_acc with "WorldRes") as "[ (>Ha & Hinterp) WorldRes]".
    iDestruct (addr_key_pointsto with "Ha") as "[Ha Hshare]".
    iDestruct (world_interp_open_heap_provenance with "Hworld_interp")
      as "[Hworld_interp #Hprov]".
    iDestruct (heap_provenance_load_witness W v with "Hprov") as "Hwit".
    iDestruct (key_share_deref with "Hshare") as (dw Hdw) "[Hdw Hshare]".
    iModIntro. iExists v, (DfracOwn 1), (load_witness_of W v), dw.
    iFrame "Ha Hwit Hdw". iSplit; first done. iSplit; first done.
    iIntros "!>" (v' Hpost) "Ha _ Hdw".
    iDestruct ("Hshare" with "Hdw") as "Hshare".
    pose proof (Hpers (W, C, v)).
    iDestruct "Hinterp" as "#HφV /=".
    iDestruct ("Hrcond" with "HφV") as "#Hnormal_p'".
    iAssert (interp_in_mem p W C v)%I as "#Hnormal".
    { iEval (rewrite /interp_in_mem /= /interp_in_mem_pre filter_heap_load_word).
      iApply (interp_weakening_word_load W C p p' (filter_heap W v)); first exact Hflows.
      iEval (rewrite /interp_in_mem_pre filter_heap_load_word) in "Hnormal_p'".
      iExact "Hnormal_p'". }
    iDestruct (interp_in_mem_load_post with "Hnormal") as "#Hv'"; first exact Hpost.
    iDestruct (addr_key_pointsto_join with "Ha Hshare") as "Ha".
    iDestruct ("WorldRes" with "[$Ha $HφV]") as "WorldRes".
    iModIntro. iSplitL.
    - iApply (close_world_interp with "Hworld_interp Hstate Hrel WorldRes");
        first done; destruct ρ; auto; contradiction.
    - rewrite big_sepL_app /=. iFrame "Hls Hv'".
  Qed.

  (* TODO: move to memory_region.v *)
  (** The loads of the cells of an owned region outside the shadow table,
      through a capability of permission [p] without identifier: once [i]
      words are loaded, they are the first [i] words of the region, as
      loaded through [p]. *)
  Lemma region_cells_load_acc (p : Perm) (e a a' : Addr) (ws : list LWord) :
    (a + length ws)%a = Some a' →
    disjoint_from_shadow a a' →
    ⊢ cells_load_acc
        (λ i ls, [[ a , a' ]] ↦ₐ [[ ws ]] ∗ ⌜ls = take i (lload_word p <$> ws)⌝)%I
        p e a None (length ws).
  Proof.
    iIntros (Ha' Hshadow).
    iIntros "!>" (i ls Hi Hie) "[Hws ->]".
    destruct (lookup_lt_is_Some_2 ws i Hi) as [v Hv].
    iEval (rewrite (region_pointsto_cells a a' ws Ha')) in "Hws".
    iDestruct (big_sepL_lookup_acc with "Hws") as "[Ha Hclose]"; first exact Hv.
    iModIntro. iExists v, (DfracOwn 1), LoadPlain, DerefNoId.
    iFrame "Ha". iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in; first exact Hshadow.
      apply withinBounds_true_iff. solve_addr. }
    iSplit; first done. iSplitR; first done. iSplitR; first done.
    iIntros "!>" (v' (_ & _ & _ & ->)) "Ha _ _ !>".
    iDestruct ("Hclose" with "Ha") as "Hws".
    rewrite (region_pointsto_cells a a' ws Ha'). iFrame "Hws". iPureIntro.
    rewrite (take_S_r _ _ (lload_word p v)); first done.
    by rewrite list_lookup_fmap Hv.
  Qed.

  (* TODO: move to logical_words.v *)
  (** A load keeps the address of a word. *)
  Lemma get_a_lload_word (p : Perm) (v : LWord) :
    get_a (lload_word p v).(lw) = get_a v.(lw).
  Proof.
    rewrite lw_lload_word /load_word.
    destruct v as [w π]; cbn.
    destruct (isDL p), (isDRO p);
      destruct w as [n | [t p0 g0 b0 e0 a0 | t p0 g0 b0 e0 a0] | k t p0 g0 b0 e0 a0 | ot sb];
      try destruct sb; reflexivity.
  Qed.

  (** A tagged capability that a [Lea] of a safe word gives is safe:
      [interp] does not read the cursor. *)
  Lemma interp_lea_result_cap (W : WORLD) (C : CmptName) (w : LWord) (z : Z)
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) :
    lea_result w z = Some (WCap true p g b e a @@? π) →
    interp W C w -∗ interp W C (WCap true p g b e a @@? π).
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
      then, once the first word is written, the cells of the slot, with the
      two facts of the site on the faulting [csp]. *)
  Definition trusted_error_state (eh : Z) (w : LWord) (rmap : LReg) (i : nat) : iProp Σ :=
    match i with
    | 0%nat => error_state_slot eh rmap
    | S _ =>
        ⌜(rmap !!! csp).(lprov) = None⌝ ∗
        ⌜error_state_shadow_free (rmap !!! csp)⌝ ∗
        error_state_cells w rmap i
    end.

  (** The written [ErrorState] is a slot. *)
  Lemma trusted_error_state_slot (eh : Z) (w : LWord) (rmap : LReg) :
    trusted_error_state eh w rmap (Z.to_nat ErrorState_size) -∗ error_state_slot eh rmap.
  Proof.
    iIntros "(%Hprov & %Hshadow & Hcells)".
    iEval (rewrite error_state_cells_full) in "Hcells".
    iDestruct (error_state_pointsto_area with "Hcells") as "Harea".
    rewrite /error_state_slot.
    case_decide; last done. by iFrame.
  Qed.

  (** The stores to the lent slot: the first one opens the slot, which
      holds the area when the table declares the stackful handler [eh]. *)
  Lemma trusted_error_state_acc (cstk : CSTK) (w : LWord) (rmap : LReg) (eh : Z) :
    top_export_tbl cstk ↦ₕ□{stackful} eh -∗
    path_es_acc cstk w rmap (trusted_error_state eh w rmap).
  Proof.
    iIntros "#Heh !>" (eh' p g b e a π _ _) "#Heh' %Hsome %Hcsp %Hok".
    iDestruct (handler_stackful_agree with "Heh Heh'") as %<-.
    pose proof Hok as Hok'.
    rewrite /error_state_stores_ok Hcsp /= in Hok'. destruct Hok' as (Hwa & Hb & He).
    iIntros "!>" (i Hi) "Hes".
    rewrite length_error_state_src in Hi.
    iAssert (⌜π = None⌝ ∗ ⌜error_state_shadow_free (rmap !!! csp)⌝ ∗
             error_state_cells w rmap i)%I with "[Hes]" as "(-> & %Hshadow & Hcells)".
    { destruct i as [|i]; cbn [trusted_error_state].
      - rewrite /error_state_slot decide_True; last done.
        iDestruct "Hes" as "(%Hprov & %Hsh & Harea)".
        rewrite Hcsp in Hprov. rewrite error_state_cells_0. by iFrame.
      - iDestruct "Hes" as "(%Hprov & $ & $)". by rewrite Hcsp in Hprov. }
    iDestruct (error_state_cells_acc with "Hcells") as (v) "[Hv Hclose]";
      [exact Hcsp | done | done |].
    iModIntro. iExists v, 1%Qp. iFrame "Hv". iSplit.
    { iPureIntro. rewrite /error_state_shadow_free Hcsp /= in Hshadow.
      eapply disjoint_from_shadow_not_in; first exact Hshadow.
      rewrite /withinBounds /ErrorState_size in He Hi |- *. solve_addr. }
    iSplitR; first iApply deref_res_none.
    iIntros "!> Hv _ !>". iDestruct ("Hclose" with "Hv") as "Hcells".
    cbn [trusted_error_state]. iFrame "Hcells".
    iPureIntro. split; [by rewrite Hcsp | done].
  Qed.

  (** The header of the table of an untrusted topmost compartment. *)
  Lemma top_cmpt_untrusted_header (W : WORLD) (C : CmptName) (cstk : CSTK) :
    top_cmpt_untrusted interp W C cstk -∗ handler_header cstk.
  Proof.
    destruct cstk as [ef [|frm frms] ]; first by iIntros "[]".
    iIntros "(%pcc & %cgp & %eh & %ehs & #Hpcc & #Hcgp & #Heh & #Hehs & _)".
    iExists eh, ehs. iFrame "Heh Hehs".
    iIntros "_". iExists pcc, cgp. iFrame "Hpcc Hcgp".
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
      frame's stack above the cursor, is safe. *)
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
    destruct (Hstack ltac:(done)) as (b_stk & e_stk & a_stk & Hcsp & Hb & [a4 Ha4]).
    rewrite /top_tframe /= in Hcsp.
    destruct Ws as [|Wt Ws], Cs as [|Ct Cs]; try done.
    destruct Hframe as (Hrelated & <- & Hktk & _).
    rewrite /interp_continuation /interp_cont /= Hktk.
    iIntros "[Hrest [#Hcallee Htop]]". iFrame "Hrest Htop Hcallee".
    rewrite /stackless_csp /= Hcsp /tf_stk_b /tf_stk_e /tf_spill_a Hcsp /=.
    iDestruct "Hcallee" as "[%Hheap Hcallee]".
    assert (((a_stk ^+ 4) ^+ -4)%a = a_stk) as Hspill by solve_addr.
    rewrite Hspill. rewrite Hspill in Hheap.
    iDestruct (interp_monotone_cap_nonheap with "Hcallee") as "Hcallee'";
      [exact Hheap | exact Hrelated |].
    iApply (interp_weakeningEO with "Hcallee'"); try done.
    destruct (is_untrusted_caller_frm frm); solve_addr.
  Qed.

  (** The unwind continuation from the logical relation's resources, for a
      safe trap vector: the return routine pops the frame of the faulting
      compartment, whatever its error handler count. *)
  Lemma logrel_unwind_cont_gen (Nswitcher : namespace) (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    Nswitcher ## N_trap →
    frame_match Ws Cs cstk W C →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec) -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    unwind_cont ⊤ cstk True.
  Proof.
    iIntros (Hdisj Hframe) "#Hinv #Hstatic #Htrap Hworld Hcont".
    iIntros (n rmap Hfull Hca0 Hca1) "HPC Hrmap Hcstk _ Hna".
    iEval (rewrite -(interp_cont_set_top_count cstk Ws Cs n)) in "Hcont".
    iApply (switcher_return_unwind _ W C Nswitcher (cstack_set_top_count cstk n) Ws Cs
             with "[$HPC $Hrmap $Hinv $Hstatic $Htrap $Hworld $Hcont $Hna $Hcstk]");
      [done | done | done | by apply frame_match_set_top_count |].
    iSplit; iApply interp_int.
  Qed.

  (** ** The handler return *)

  (** From [.Lhandle_error_handler_return], with [ca0] non-zero, the
      switcher force-unwinds the call (block 34 and
      [.Lcommon_force_unwind]). *)
  #[local] Lemma switcher_handler_return_force_unwind (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) →
    nonZero (rmap !!! ca0).(lw) = true →
    switcher_static -∗
    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_return" -∗
    registers_pointsto rmap -∗
    (∀ rmap' : LReg,
       ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
       ⌜rmap' !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
       ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
       PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
       registers_pointsto rmap' -∗
       WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}) -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfull Hnz) "#Hstatic HPC Hrmap Hpost".
    iPoseProof "Hstatic" as "[#Hcode _]".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    assert (rmap !!! ca0 = wca0) as Hrmap_ca0 by (rewrite lookup_total_alt Hwca0; done).
    rewrite Hrmap_ca0 in Hnz.
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_handler_return_block_spec with "[- $HPC $Hca0 $Hcode]").
    iNext; iSplit; last (iIntros (Hnz'); by rewrite Hnz in Hnz').
    iIntros (_) "(HPC & Hca0 & _)".
    iApply (switcher_call_block_18_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
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
    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_return" -∗
    registers_pointsto rmap -∗
    cstack_frag (cstack_set_top_count cstk n) -∗
    unwind_cont F cstk R_unwind_stk -∗
    R_unwind_stk -∗
    na_own cerise_nais F -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfull Hnz) "#Hstatic HPC Hrmap Hcstk HU HS Hna".
    iApply (switcher_handler_return_force_unwind with "Hstatic HPC Hrmap"); [done | done |].
    iIntros (rmap' Hfull' Hca0 Hca1) "HPC Hrmap".
    iApply ("HU" with "[//] [//] [//] HPC Hrmap Hcstk HS Hna").
  Qed.

  (** An untrusted handler returns to the switcher with [ca0] zero: the
      switcher installs the context of the [ErrorState] below the handler's
      safe [csp]. The loaded words are safe, and so is the resumed PC, from
      the safe PCC of the topmost table: the installed context runs through
      the FTLR, with the count of the topmost frame incremented. A fault of
      the installation is a fault in the switcher, which unwinds. *)
  #[local] Lemma untrusted_handler_install_safe (Nswitcher : namespace)
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    nonZero (rmap !!! ca0).(lw) = false ->
    frame_match Ws Cs cstk W C ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec) -∗
    (∀ (r : RegName) (v : LWord), ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    top_cmpt_untrusted interp W C cstk -∗
    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_return" -∗
    registers_pointsto rmap -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    na_own cerise_nais ⊤ -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hfull Hnz Hframe)
      "#Hinv_switcher #Hstatic #Htrap #Hregs #Htop HPC Hrmap Hworld_interp Hcont Hna Hcstk".
    (* The PCC of the topmost table is safe *)
    iAssert (∃ wpcc, top_export_tbl cstk ↦ₐ□ wpcc ∗ interp W C wpcc)%I
      as (wpcc) "[#Hpcc #Hpcc_interp]".
    { destruct (cstk_frames cstk) as [|frm frms] eqn:Hframes.
      { by rewrite /top_cmpt_untrusted Hframes. }
      iEval (rewrite /top_cmpt_untrusted Hframes) in "Htop".
      iDestruct "Htop" as (pcc cgp eh ehs) "(Hpcc' & _ & _ & _ & #Hsafe)".
      iExists pcc. rewrite /top_export_tbl /top_tframe Hframes. iFrame "Hpcc'".
      iDestruct ("Hsafe" $! W with "[%]") as "[$ _]".
      apply related_sts_priv_refl_world. }
    iAssert (interp W C (rmap !!! csp)) as "#Hcsp".
    { iApply "Hregs". iPureIntro.
      destruct (Hfull csp) as [v Hv]. by rewrite (lookup_total_correct _ _ _ Hv). }
    iApply (switcher_install_context_spec Nswitcher cstk rmap wpcc
              (λ (_ : nat) (ls : list LWord), world_interp W C ∗ [∗ list] v ∈ ls, interp W C v)%I
             with "[- ]"); [done | done | done |].
    iFrame "Hinv_switcher Hstatic HPC Hrmap Hna Hcstk Hpcc".
    iSplitL "Hworld_interp"; first by iFrame.
    iSplitR.
    { iIntros (p g b e a π Hlea [Hra Hb]).
      iApply world_interp_cells_load_acc; [done | done |].
      by iApply (interp_lea_result_cap with "Hcsp"). }
    iNext. iSplit.
    - (* A fault of the installation: the switcher unwinds *)
      iIntros (off rmap' i ls Hno_resume Hfull') "Hrmap Hcstk [Hworld_interp _] Hna".
      iApply (interp_trap_safe with "Htrap"); first done.
      iModIntro. iFrame "Hrmap Hna Hcstk". iRight.
      iApply trap_handler_ok_switcher; [done | apply switcher_fault_pc_cap |].
      by iApply (logrel_unwind_cont_gen with "Hinv_switcher Hstatic Htrap Hworld_interp Hcont").
    - (* The installed context runs through the FTLR *)
      iIntros (ls Hls) "HPC Hrmap Hcstk [Hworld_interp #Hls_interp] Hna".
      iAssert (interp W C (llegalise MEPCC (resumed_pc wpcc (get_a (ls !!! 0%nat).(lw)))))
        as "#Hwpc".
      { iApply interp_llegalise_mepcc. by iApply interp_resumed_pc. }
      iDestruct (fundamental (trap_handler_ok ⊤) with "Htrap Hwpc") as "Hexpr".
      iApply ("Hexpr" $! (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) Ws Cs
                (error_state_install rmap (drop 1 ls)) with "[- ]").
      iFrame "HPC Hrmap Hworld_interp Hna Hcstk".
      rewrite top_cmpt_untrusted_set_top_count interp_cont_set_top_count.
      iFrame "Htop Hcont".
      iSplit; last (iPureIntro; by apply frame_match_set_top_count).
      iApply interp_reg_intro; first by apply error_state_install_full.
      iIntros (r v Hv).
      rewrite /error_state_install lookup_union_Some_raw in Hv.
      destruct Hv as [Hv | [_ Hv] ]; last by iApply "Hregs".
      apply elem_of_list_to_map_2, elem_of_zip_r in Hv.
      iApply (big_sepL_elem_of with "Hls_interp").
      by apply (subseteq_drop 1 ls).
  Qed.

  (** The handler-return entry point is safe to execute, for a safe trap
      vector: the registers are re-filtered; with [ca0] non-zero, the
      switcher unwinds, and with [ca0] zero, it installs the context of the
      [ErrorState]. *)
  Lemma interp_expr_handler_return_gen (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec)
    ⊢ interp_expr interp (interp_cont interp) W C
        (switcher_label_pc ".Lhandle_error_handler_return").
  Proof.
    iIntros (Hdisj) "(#Hinv_switcher & #Hstatic & #Htrap) %cstk %Ws %Cs %rmap0
             (Hregs & #Htop & HPC & Hrmap & Hworld_interp & Hcont_K & Hna & Hcstk & %Hframe)".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (rmap) "%Hfull_rmap #Hregs Hrmap Hworld_interp". clear rmap0.
    cbn in Hfull_rmap.
    destruct (nonZero (rmap !!! ca0).(lw)) eqn:Hnz.
    - (* [ca0] non-zero: the switcher unwinds *)
      iApply (switcher_handler_return_force_unwind with "Hstatic HPC Hrmap"); [done | done |].
      iIntros (rmap' Hfull' Hca0 Hca1) "HPC Hrmap".
      iApply (switcher_return_unwind with
               "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont_K $Hna $Hcstk]");
        [done | done | done | done |].
      iSplit; iApply interp_int.
    - (* [ca0] zero: the switcher installs the context *)
      iApply (untrusted_handler_install_safe with
               "Hinv_switcher Hstatic Htrap Hregs Htop HPC Hrmap Hworld_interp Hcont_K Hna Hcstk");
        done.
  Qed.

  (** The sentry that the switcher gives a handler is safe, for a safe trap
      vector (needed only under the sentry's later). *)
  Lemma interp_handler_return_sentry_gen
    (W : WORLD) (C : CmptName) (Nswitcher : namespace) (mie : InterruptStatus) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    ▷ trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec)
    ⊢ interp W C (handler_return_sentry mie).
  Proof.
    iIntros (Hdisj) "(#Hinv & #Hstatic & #Htrap)".
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
      for a stackless handler, the stack above the frame's cursor; for a
      stackful one, the faulting [csp], safe, with other cursors). *)
  Lemma untrusted_handler_invoke_safe (Nswitcher : namespace)
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (kind : handler_kind) (wpcc wcgp wpc : LWord) (off mcause mtval : Z)
    (regs : LReg) :
    Nswitcher ## N_trap ->
    frame_match Ws Cs cstk W C ->
    top_frame_stack_ok cstk ->
    handler_entry wpcc off = Some wpc ->
    handler_invocation_regs kind cstk wcgp rmap mcause mtval regs ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec) -∗
    top_cmpt_untrusted interp W C cstk -∗
    top_export_tbl cstk ↦ₐ□ wpcc -∗
    (top_export_tbl cstk ^+ ExportTable_offset_cgp)%a ↦ₐ□ wcgp -∗
    interp W C (rmap !!! csp) -∗
    PC ↦ₚ wpc -∗
    registers_pointsto regs -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) -∗
    na_own cerise_nais ⊤ -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hframe Hstack Hentry Hinv_regs)
      "#Hinv_switcher #Hstatic #Htrap #Htop #Hpcc #Hcgp #Hcsp_fault HPC Hregs Hworld_interp
       Hcont Hcstk Hna".
    destruct (cstk_frames cstk) as [|frm frms] eqn:Hframes.
    { by rewrite /top_cmpt_untrusted Hframes. }
    iAssert (interp W C wpcc ∗ interp W C wcgp)%I as "[#Hpcc_interp #Hcgp_interp]".
    { iEval (rewrite /top_cmpt_untrusted Hframes) in "Htop".
      iDestruct "Htop" as (pcc cgp eh ehs') "(Hpcc' & Hcgp' & _ & _ & #Hsafe)".
      rewrite /top_export_tbl /top_tframe Hframes.
      iDestruct (pointsto_agree with "Hpcc Hpcc'") as %->.
      iDestruct (pointsto_agree with "Hcgp Hcgp'") as %->.
      iApply "Hsafe". iPureIntro. apply related_sts_priv_refl_world. }
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
        iDestruct (interp_cont_stackless_csp with "Hcont") as "[Hcont #Hcsp_i]";
          [done | done | by rewrite Hframes |].
        iExists _, _, _, _.
        do 4 (iSplit; first done).
        iFrame "Hcont Hcsp_i".
        iSplit; [iApply interp_int | iSplit; iApply interp_int]. }
    clear Hkind.
    iDestruct (fundamental (trap_handler_ok ⊤) with "Htrap Hwpc") as "Hexpr".
    iApply ("Hexpr" $! (cstack_set_top_count cstk (top_error_count cstk + 1)%Z) Ws Cs regs
             with "[- ]").
    iFrame "HPC Hregs Hworld_interp Hna Hcstk".
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

  (** The safety of the exception entry, for a fault in an untrusted
      compartment (with the whole non-atomic token) or a fault that the
      switcher handles, for any token [F] that contains the switcher's
      invariant and the trap-entry part. *)
  Definition exception_entry_safe (Nswitcher : namespace) : iProp Σ :=
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

  #[global] Instance exception_entry_safe_persistent Nswitcher :
    Persistent (exception_entry_safe Nswitcher).
  Proof. rewrite /exception_entry_safe. apply _. Qed.

  Lemma exception_entry_safe_vector (Nswitcher : namespace) :
    exception_entry_safe Nswitcher ⊢
    trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec).
  Proof.
    iIntros "#Hsafe !>" (cstk regs w Hfull) "Hfault HPC Hout Hrmap Hna Hcstk".
    iApply ("Hsafe" $! ⊤ with "[%] [%] [//] [Hfault] HPC Hout Hrmap Hna Hcstk");
      [set_solver | set_solver |].
    iDestruct "Hfault" as "[Hfault | Hfault]"; [iLeft; by iFrame | by iRight].
  Qed.

  (** A fault of the exception path itself is a fault in the switcher: the
      unwind continuation is built from the destination of the [ErrorState]
      stores, before them or after all of them. *)
  Lemma exception_entry_safe_nested (Nswitcher : namespace) (F : coPset) (cstk : CSTK)
    (error_state_written : nat → iProp Σ) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    exception_entry_safe Nswitcher -∗
    ((error_state_written 0 ∨ error_state_written (Z.to_nat ErrorState_size)) -∗
     unwind_cont F cstk True) -∗
    path_nested_fault F cstk error_state_written.
  Proof.
    iIntros (HF HFtrap) "#Hsafe HU".
    iIntros (off n rmap' Hno_resume Hfull) "Hrmap Hcstk Hes Hna".
    iSpecialize ("HU" with "Hes").
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    iApply ("Hsafe" $! F (cstack_set_top_count cstk n) rmap' (switcher_pc off) with
             "[//] [//] [//] [HU] HPC Hout Hrmap Hna Hcstk").
    iRight. iApply trap_handler_ok_switcher; [done | apply switcher_fault_pc_cap |].
    by rewrite unwind_cont_set_top_count.
  Qed.

  (** The forced unwind, with the unwind continuation built from the
      destination of the [ErrorState] stores before any of them. *)
  Lemma unwind_cont_path_unwind_k (F : coPset) (cstk : CSTK) (w : LWord)
    (error_state_written : nat → iProp Σ) :
    (error_state_written 0 -∗ unwind_cont F cstk True) -∗
    path_unwind_k F cstk w error_state_written.
  Proof.
    iIntros "HU" (_ n rmap' Hfull Hca0 Hca1) "HPC Hrmap Hcstk Hes Hna".
    iApply ("HU" with "Hes [//] [//] [//] HPC Hrmap Hcstk [//] Hna").
  Qed.

  (** A fault in an untrusted compartment: the registers are re-filtered;
      the switcher unwinds, resumes the caller, or invokes one of the
      compartment's handlers, which runs through the FTLR. The [ErrorState]
      of a stackful handler is stored in the world. *)
  Lemma exception_entry_untrusted_safe (Nswitcher : namespace)
    (cstk : CSTK) (rmap : LReg) (w : LWord) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe Nswitcher -∗
    untrusted_fault cstk rmap -∗
    PC ↦ₚ lword_of_word mtcc_vec -∗
    trap_entry_out w -∗
    registers_pointsto rmap -∗
    na_own cerise_nais (⊤ ∖ ↑N_trap) -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hfull_rmap)
      "#Hinv_switcher #Hstatic #Hsafe Huntrusted HPC Hout Hrmap Hna Hcstk".
    iDestruct "Huntrusted" as (W C Ws Cs Hframe) "(#Hregs & #Htop & Hworld_interp & Hcont)".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (rmap') "%Hfull_rmap' #Hregs' Hrmap Hworld_interp".
    iDestruct (top_cmpt_untrusted_header with "Htop") as "#Hheader".
    iApply (switcher_exception_path_spec Nswitcher ⊤ cstk (cstack_frag cstk)
              (λ _, world_interp W C) with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcstk Hworld_interp Hcont]");
      [set_solver | set_solver | done | done |].
    iSplitL "Hcstk"; first by case_decide.
    iSplitR; first (iIntros "_"; iExact "Hheader").
    iSplitL "Hworld_interp"; first iExact "Hworld_interp".
    iSplitR; first by iApply untrusted_error_state_acc.
    iNext.
    iPoseProof (exception_entry_safe_vector with "Hsafe") as "#Htrap".
    iSplit; [|iSplit; [|iSplit] ].
    - (* The forced unwind *)
      iApply unwind_cont_path_unwind_k. iIntros "Hworld_interp".
      by iApply (logrel_unwind_cont_gen with "Hinv_switcher Hstatic Htrap Hworld_interp Hcont").
    - (* The resumed caller returns to [cra], with safe registers *)
      iIntros (_ rmap'' Hfull_rmap'' Hsame Hca0 Hca1) "HPC Hrmap Hcstk Hworld_interp Hna".
      iApply (switcher_just_return_safe with
               "Htrap [] Htop Hstatic HPC Hrmap Hworld_interp Hcont Hna Hcstk"); [done | done |].
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
      iIntros "Hworld_interp".
      iAssert (world_interp W C) with "[Hworld_interp]" as "Hworld_interp".
      { by iDestruct "Hworld_interp" as "[H | H]". }
      by iApply (logrel_unwind_cont_gen with "Hinv_switcher Hstatic Htrap Hworld_interp Hcont").
    - (* A handler *)
      iIntros (kind wpcc wcgp wpc off mcause mtval regs _ _ Hstack _ _ Hentry Hinv_regs)
        "Hpcc Hcgp _ HPC Hregs_h Hcstk Hworld_interp Hna".
      iApply (untrusted_handler_invoke_safe with
               "Hinv_switcher Hstatic Htrap Htop Hpcc Hcgp [] HPC Hregs_h Hworld_interp Hcont
                Hcstk Hna"); [done | done | done | done | done |].
      iApply "Hregs'". iPureIntro.
      destruct (Hfull_rmap' csp) as [v Hv]. by rewrite (lookup_total_correct _ _ _ Hv).
  Qed.

  (** A fault in the switcher, in a compartment whose table declares no
      handler, or in a running trusted handler (odd count): the switcher
      unwinds; a nested fault of the path is a fault in the switcher. *)
  Lemma exception_entry_unwind_safe (Nswitcher : namespace) (F : coPset)
    (cstk : CSTK) (rmap : LReg) (w : LWord) :
    ↑Nswitcher ⊆ F ->
    ↑N_trap ⊆ F ->
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume w ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe Nswitcher -∗
    unwind_cont F cstk True -∗
    (⌜switcher_fault_pc w⌝ ∨
     no_handler (top_export_tbl cstk) ∨
     (⌜Z.odd (top_error_count cstk) = true⌝ ∗
      ∃ eh ehs : Z,
        top_export_tbl cstk ↦ₕ□{stackful} eh ∗
        top_export_tbl cstk ↦ₕ□{stackless} ehs)) -∗
    PC ↦ₚ lword_of_word mtcc_vec -∗
    trap_entry_out w -∗
    registers_pointsto rmap -∗
    na_own cerise_nais (F ∖ ↑N_trap) -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HF HFtrap Hdisj Hfull_rmap Hno_resume)
      "#Hinv_switcher #Hstatic #Hsafe HU #Hcase HPC Hout Hrmap Hna Hcstk".
    iAssert (⌜¬ switcher_fault_pc w⌝ → handler_header cstk)%I as "#Hheader".
    { iIntros (Hnot). rewrite /no_handler.
      iDestruct "Hcase" as "[%Hpc | [[Heh Hehs] | [%Hodd (%eh & %ehs & Heh & Hehs)] ] ]";
        first done.
      - iExists _, _. iFrame "Heh Hehs". iIntros ([ [Hne | Hne] _]); by contradict Hne.
      - iExists eh, ehs. iFrame "Heh Hehs". iIntros ([_ Hev]).
        exfalso. rewrite -Z.negb_odd Hodd in Hev. done. }
    iApply (switcher_exception_path_spec Nswitcher F cstk (cstack_frag cstk) (λ _, True%I) with
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
      by iIntros "_".
    - iIntros (kind wpcc wcgp wpc off mcause mtval regs Hnot Hev _ Hoff _ _ _)
        "_ _ #Hoff _ _ _ _ _".
      rewrite /no_handler.
      iDestruct "Hcase" as "[%Hpc | [ [Hnone Hnone'] | [%Hodd _] ] ]"; first done.
      + destruct kind; cbn [handler_offset].
        * iDestruct (handler_stackful_agree with "Hnone Hoff") as %Heq. by subst off.
        * iDestruct (handler_stackless_agree with "Hnone' Hoff") as %Heq. by subst off.
      + exfalso. rewrite -Z.negb_odd Hodd in Hev. done.
  Qed.

  (** A fault in a trusted compartment whose table declares trusted
      handlers: the switcher invokes a handler, through the table's
      [execute_error_handler], or unwinds. The [ErrorState] of a stackful
      handler is stored in the slot that the fault site lends. *)
  Lemma exception_entry_trusted_handler_safe (Nswitcher : namespace)
    (cstk : CSTK) (rmap : LReg) (w : LWord)
    (P_fault : CSTK → LWord → LReg → iProp Σ) (eh : Z) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    trap_no_resume w ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    ▷ exception_entry_safe Nswitcher -∗
    trusted_handler (top_export_tbl cstk) P_fault -∗
    top_export_tbl cstk ↦ₕ□{stackful} eh -∗
    error_state_slot eh rmap -∗
    (unwind_cont ⊤ cstk (error_state_slot eh rmap) ∧ P_fault cstk w rmap) -∗
    PC ↦ₚ lword_of_word mtcc_vec -∗
    trap_entry_out w -∗
    registers_pointsto rmap -∗
    na_own cerise_nais (⊤ ∖ ↑N_trap) -∗
    cstack_frag cstk -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hfull_rmap Hno_resume)
      "#Hinv_switcher #Hstatic #Hsafe #Hhandler #Heh_site Hslot HUP HPC Hout Hrmap Hna Hcstk".
    iDestruct "Hhandler" as (wpcc wcgp eh' ehs)
      "(#Hpcc & #Hcgp & #Heh & #Hehs & #Hexec_sf & #Hexec_sl)".
    iDestruct (handler_stackful_agree with "Heh_site Heh") as %<-.
    (* The handler's WP, for this fault *)
    iAssert (□ ∀ (kind : handler_kind) (off mcause mtval : Z) (wpc : LWord) (regs : LReg),
               ▷ ( handler_offset kind (top_export_tbl cstk) off -∗
                   ⌜off ≠ ExportTable_no_handler⌝ -∗
                   ⌜top_export_tbl cstk = top_export_tbl cstk⌝ -∗
                   ⌜Z.even (top_error_count cstk) = true⌝ -∗
                   ⌜mcause_ok mcause⌝ -∗
                   ⌜handler_entry wpcc off = Some wpc⌝ -∗
                   ⌜handler_invocation_regs kind cstk wcgp rmap mcause mtval regs⌝ -∗
                   PC ↦ₚ wpc -∗
                   registers_pointsto regs -∗
                   handler_slot kind w rmap -∗
                   (unwind_cont ⊤ cstk (handler_unwind_res kind rmap) ∧ P_fault cstk w rmap) -∗
                   cstack_frag (cstack_set_top_count cstk (top_error_count cstk + 1)) -∗
                   na_own cerise_nais ⊤ -∗
                   WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ))%I
      as "#Hrun".
    { iIntros "!>" (kind off mcause mtval wpc regs).
      destruct kind; cbn [handler_offset].
      - destruct (decide (eh = ExportTable_no_handler)) as [Hnone | Hsome].
        + iNext. iIntros "#Hoff" (Hsome).
          iDestruct (handler_stackful_agree with "Heh Hoff") as %<-. done.
        + iDestruct ("Hexec_sf" with "[//]") as "#Hexec'".
          iSpecialize ("Hexec'" $! cstk w rmap mcause mtval wpc regs).
          iNext. iIntros "#Hoff _".
          iDestruct (handler_stackful_agree with "Heh Hoff") as %<-. iExact "Hexec'".
      - destruct (decide (ehs = ExportTable_no_handler)) as [Hnone | Hsome].
        + iNext. iIntros "#Hoff" (Hsome).
          iDestruct (handler_stackless_agree with "Hehs Hoff") as %<-. done.
        + iDestruct ("Hexec_sl" with "[//]") as "#Hexec'".
          iSpecialize ("Hexec'" $! cstk w rmap mcause mtval wpc regs).
          iNext. iIntros "#Hoff _".
          iDestruct (handler_stackless_agree with "Hehs Hoff") as %<-. iExact "Hexec'". }
    iApply (switcher_exception_path_spec Nswitcher ⊤ cstk (cstack_frag cstk)
              (trusted_error_state eh w rmap) with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcstk Hslot HUP]");
      [set_solver | set_solver | done | done |].
    iSplitL "Hcstk"; first by case_decide.
    iSplitR.
    { iIntros "_". iExists eh, ehs. iFrame "Heh Hehs".
      iIntros "_". iExists wpcc, wcgp. iFrame "Hpcc Hcgp". }
    iSplitL "Hslot"; first iExact "Hslot".
    iSplitR; first by iApply trusted_error_state_acc.
    iNext.
    iSplit; [|iSplit; [|iSplit] ].
    - iDestruct "HUP" as "[HU _]".
      iApply unwind_cont_path_unwind_k. iIntros "Hslot".
      iApply (unwind_cont_give with "Hslot HU").
    - by iIntros (Hresume).
    - iDestruct "HUP" as "[HU _]".
      iIntros (_). iApply (exception_entry_safe_nested with "Hsafe"); [set_solver | set_solver |].
      iIntros "Hes". iApply (unwind_cont_give with "[Hes] HU").
      iDestruct "Hes" as "[Hslot | Hes]"; first iExact "Hslot".
      by iApply trusted_error_state_slot.
    - iIntros (kind wpcc' wcgp' wpc off mcause mtval regs _ Hev _ Hoff_some Hmcause Hentry
                Hinv_regs)
        "#Hpcc' #Hcgp' #Hoff HPC Hregs Hcstk Hes Hna".
      iDestruct (pointsto_agree with "Hpcc Hpcc'") as %<-.
      iDestruct (pointsto_agree with "Hcgp Hcgp'") as %<-.
      destruct kind.
      + (* Stackful: the written [ErrorState] goes to the handler, with the
           two facts of the site; the unwind continuation takes back the
           slot *)
        iAssert ⌜off = eh⌝%I as %->.
        { iApply (handler_stackful_agree with "Hoff Heh"). }
        pose proof Hinv_regs as (_ & _ & _ & [Hok _] & _).
        iDestruct "Hes" as "(%Hprov & %Hshadow & Hcells)".
        iEval (rewrite error_state_cells_full) in "Hcells".
        iApply ("Hrun" with
                 "Hoff [//] [//] [//] [//] [//] [//] HPC Hregs [$Hcells //] [HUP] Hcstk Hna").
        iSplit; last by iDestruct "HUP" as "[_ HP]".
        iDestruct "HUP" as "[HU _]".
        iApply (unwind_cont_weaken with "[] HU").
        iIntros "Harea". rewrite /error_state_slot decide_True; last done.
        by iFrame.
      + (* Stackless *)
        iApply ("Hrun" with
                 "Hoff [//] [//] [//] [//] [//] [//] HPC Hregs [//] [HUP Hes] Hcstk Hna").
        iSplit; last by iDestruct "HUP" as "[_ HP]".
        iDestruct "HUP" as "[HU _]".
        iApply (unwind_cont_give with "Hes HU").
  Qed.

  (** The exception entry is safe, by Löb induction: the exception path
      needs it only after its first instruction, and a nested fault of the
      path enters it again under the later of trap entry. *)
  Lemma switcher_exception_entry_safe (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ exception_entry_safe Nswitcher.
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic]".
    iLöb as "IH".
    iIntros "!>" (F cstk rmap w HF HFtrap Hfull) "Hfault HPC Hout Hrmap Hna Hcstk".
    iDestruct "Hfault" as "[[-> Huntrusted] | Hhandled]".
    { iApply (exception_entry_untrusted_safe with
               "Hinv_switcher Hstatic IH Huntrusted HPC Hout Hrmap Hna Hcstk"); done. }
    iDestruct (trap_handler_ok_cases with "Hhandled")
      as (Hno_resume) "[ [HU Hcase] | [ [-> Hrow] | (HU & %Hodd & Hheader)] ]".
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

  (** The trap vector of the machine, the exception entry of the switcher,
      is safe, for the faults in an untrusted compartment and for the
      faults that it handles ([trap_handler_ok ⊤]). *)
  Lemma switcher_mtcc_vec_safe (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (trap_handler_ok ⊤) (lword_of_word mtcc_vec).
  Proof.
    iIntros (Hdisj) "Hres".
    iApply exception_entry_safe_vector.
    by iApply switcher_exception_entry_safe.
  Qed.

  (** The exception entry of the switcher is a safe trap vector. *)
  Lemma switcher_trap_vector_safe (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (trap_handler_ok ⊤) (switcher_label_pc "exception_entry_asm").
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic]".
    iPoseProof "Hstatic" as "(_ & _ & %Hmtcc)".
    rewrite -Hmtcc.
    iApply (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hstatic]"); done.
  Qed.

  (** The unwind continuation from the logical relation's resources. *)
  Lemma logrel_unwind_cont (Nswitcher : namespace) (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    Nswitcher ## N_trap →
    frame_match Ws Cs cstk W C →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    unwind_cont ⊤ cstk True.
  Proof.
    iIntros (Hdisj Hframe) "#Hinv #Hstatic Hworld Hcont".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (logrel_unwind_cont_gen with "Hinv Hstatic Htrap Hworld Hcont").
  Qed.

  (** The handler-return entry point is safe to execute. *)
  Lemma interp_expr_handler_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C
        (switcher_label_pc ".Lhandle_error_handler_return").
  Proof.
    iIntros (Hdisj) "[#Hinv #Hstatic]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (interp_expr_handler_return_gen with "[$Hinv $Hstatic $Htrap]").
  Qed.

  (** The sentry that the switcher gives a handler is safe. *)
  Lemma interp_handler_return_sentry
    (W : WORLD) (C : CmptName) (Nswitcher : namespace) (mie : InterruptStatus) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp W C (handler_return_sentry mie).
  Proof.
    iIntros (Hdisj) "[#Hinv #Hstatic]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv $Hstatic]") as "#Htrap".
    by iApply (interp_handler_return_sentry_gen with "[$Hinv $Hstatic $Htrap]").
  Qed.

  (** The callee's stack is smaller than the minimum stack size of the
      entry point: block 20 sets the return values, and the return routine
      pops the frame already pushed. No register needs to be safe. *)
  Lemma switcher_call_stack_too_small_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ switcher_label_pc ".Lswitch_stack_too_small" ∗
    registers_pointsto rmap ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own cerise_nais ⊤ ∗
    cstack_frag cstk
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hfull_rmap Hframe)
      "(HPC & Hrmap & #Hinv_switcher & #Hstatic & Hworld_interp & Hcont & Hna & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_call_block_20_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iInsertList "Hrmap" [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iSplit; iApply interp_int.
  Qed.

  (** A fault closes through the exception path of the switcher: after
      trap entry, the switcher handles the fault ([trap_handler_ok F]). The
      resources come under an update at the time of the fault; the
      non-atomic token [F] provides the trap-entry token, and the exception
      path opens the invariant of the switcher with the rest of [F]. *)
  Lemma trap_safe_exception_entry (Nswitcher : namespace) (F : coPset) (w : LWord) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    Nswitcher ## N_trap →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (|={⊤}=>
       ∃ (rmap : LReg) (cstk : CSTK),
         ⌜∀ r, is_Some (rmap !! r)⌝ ∗
         na_own cerise_nais F ∗
         registers_pointsto rmap ∗
         cstack_frag cstk ∗
         trap_handler_ok F cstk w rmap) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (HF HFtrap Hdisj) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_exception_entry_safe with "[$Hinv_switcher $Hstatic]") as "#Hsafe";
      first done.
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iMod "Hres" as (rmap cstk Hfull_rmap) "(Hna & Hrmap & Hcstk & Hhandled)".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    iApply ("Hsafe" $! F cstk rmap w with "[//] [//] [//] [Hhandled] HPC Hout Hrmap Hna Hcstk").
    by iRight.
  Qed.

  (** A fault that the exception path resumes (a fault of the first spill
      of the call path) closes through the exception path of the switcher:
      after trap entry, the switcher spills the registers, overwrites the
      return values with [-ENOTENOUGHSTACK] and 0, and installs the context
      again, at [.Lswitch_just_return]. The resources come under an update
      at the time of the fault; the non-atomic token [F] provides the
      trap-entry token, and the exception path opens the invariant of the
      switcher with the rest of [F]. *)
  Lemma trap_safe_resume (Nswitcher : namespace) (F : coPset) (w : LWord) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    Nswitcher ## N_trap →
    ¬ trap_no_resume w →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
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
    iIntros (HF HFtrap Hdisj Hresume) "#Hinv_switcher #Hstatic Hres".
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
    iApply (switcher_exception_path_spec Nswitcher F
              (entry_cstack (MkTFrame (WInt 0) (WInt 0) 0)) True (λ _, True%I) rmap with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hcont]");
      [exact HF | exact HFtrap | exact Hdisj | exact Hfull_rmap |].
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

  (** A fault in trusted code is safe: after exception entry, the exception
      entry of the switcher unwinds the call of the faulting compartment, or
      resumes a fault in an untrusted compartment. The resources and the
      fault's justification come under an update at the time of the fault
      (for instance, to close an invariant). *)
  Lemma trap_safe_unwind (Nswitcher : namespace) (cstk : CSTK) (rmap : LReg) (w : LWord) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       na_own cerise_nais ⊤ ∗
       cstack_frag cstk ∗
       (untrusted_fault cstk rmap ∨ trap_handler_ok ⊤ cstk w rmap)) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hdisj Hfull_rmap) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    iApply (interp_trap_safe with "Htrap Hres"); done.
  Qed.

  (** A fault in trusted code, with the logical relation's resources, in
      the switcher ([switcher_fault_pc w]) or in a compartment whose table
      declares no handler: the switcher unwinds the call of the faulting
      compartment through the return routine. *)
  Lemma trap_safe_unwind_logrel
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (w : LWord) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->
    trap_no_resume w ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (⌜switcher_fault_pc w⌝ ∨ no_handler (top_export_tbl cstk)) -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       world_interp W C ∗
       interp_cont interp cstk Ws Cs ∗
       na_own cerise_nais ⊤ ∗
       cstack_frag cstk) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hdisj Hfull_rmap Hframe Hno_resume) "#Hinv_switcher #Hstatic Hcase Hres".
    iApply (trap_safe_unwind with "Hinv_switcher Hstatic"); [done | done |].
    iMod "Hres" as "(Hrmap & Hworld_interp & Hcont & Hna & Hcstk)".
    iModIntro. iFrame "Hrmap Hna Hcstk". iRight.
    iPoseProof (logrel_unwind_cont with "Hinv_switcher Hstatic Hworld_interp Hcont")
      as "HU"; [done | done |].
    iDestruct "Hcase" as "[%Hpc | Hnh]".
    - by iApply (trap_handler_ok_switcher with "HU").
    - by iApply (trap_handler_ok_no_handler with "Hnh HU").
  Qed.

  (** A trusted handler returns to the switcher with [ca0] zero: the
      switcher installs the context of the [ErrorState] [ws], the 16 cells
      below the handler's [csp], a capability without identifier whose
      cells are outside the shadow table. The resumed PC is the PCC [wpcc]
      of the topmost table with the address of word 0, the registers hold
      words 1-15 as loaded through the permission of [csp], and the count
      of the topmost frame is incremented. A fault of the installation (the
      cell of the table is cleared, or [csp] does not allow the loads) is a
      fault in the switcher, which unwinds. *)
  Lemma switcher_handler_return_install (Nswitcher : namespace) (cstk : CSTK)
    (rmap : LReg) (wpcc : LWord) (p : Perm) (g : Locality) (b e a : Addr)
    (ws : list LWord) :
    Nswitcher ## N_trap →
    (∀ r, is_Some (rmap !! r)) →
    nonZero (rmap !!! ca0).(lw) = false →
    rmap !!! csp = lword_of_word (WCap true p g b e a) →
    is_Some (a + (- ErrorState_size))%a →
    disjoint_from_shadow (a ^+ (- ErrorState_size))%a a →
    length ws = Z.to_nat ErrorState_size →

    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    top_export_tbl cstk ↦ₐ□ wpcc ∗
    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_return" ∗
    registers_pointsto rmap ∗
    [[ (a ^+ (- ErrorState_size))%a , a ]] ↦ₐ [[ ws ]] ∗
    cstack_frag cstk ∗
    na_own cerise_nais ⊤ ∗
    ▷ ( ( [[ (a ^+ (- ErrorState_size))%a , a ]] ↦ₐ [[ ws ]] -∗
          unwind_cont ⊤ cstk True ) ∧
        ( [[ (a ^+ (- ErrorState_size))%a , a ]] ↦ₐ [[ ws ]] -∗
          context_resume (cstack_set_top_count cstk (top_error_count cstk + 1))
            (llegalise MEPCC (resumed_pc wpcc (get_a (ws !!! 0%nat).(lw))))
            (error_state_install rmap (lload_word p <$> drop 1 ws)) ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdisj Hfull Hnz Hcsp [a_es Ha_es] Hshadow Hws)
      "(#Hinv_switcher & #Hstatic & #Hpcc & HPC & Hrmap & Hws & Hcstk & Hna & Hpost)".
    assert ((a ^+ (- ErrorState_size))%a = a_es) as Ha_es' by solve_addr.
    rewrite Ha_es' in Hshadow.
    iRevert "Hws Hpost". rewrite Ha_es'. iIntros "Hws Hpost".
    assert ((a_es + length ws)%a = Some a) as Ha_end.
    { rewrite Hws. rewrite /ErrorState_size in Ha_es |- *. solve_addr. }
    iApply (switcher_install_context_spec Nswitcher cstk rmap wpcc
              (λ (i : nat) (ls : list LWord),
                 [[ a_es , a ]] ↦ₐ [[ ws ]] ∗ ⌜ls = take i (lload_word p <$> ws)⌝)%I
             with "[- ]"); [done | done | done |].
    iFrame "Hinv_switcher Hstatic HPC Hrmap Hna Hcstk Hpcc".
    iSplitL "Hws"; first by iFrame.
    iSplitR.
    { iIntros (p' g' b' e' a' π' Hlea _).
      rewrite Hcsp /lea_result /= Ha_es in Hlea.
      injection Hlea as <- <- <- <- <- <-.
      rewrite -Hws.
      iApply (region_cells_load_acc p e a_es a ws Ha_end Hshadow). }
    iNext. iSplit.
    - (* A fault of the installation: the switcher unwinds *)
      iIntros (off rmap' i ls Hno_resume Hfull') "Hrmap Hcstk [Hws _] Hna".
      iDestruct "Hpost" as "[Hfault _]".
      iApply (trap_safe_unwind with "Hinv_switcher Hstatic"); [done | done |].
      iModIntro. iFrame "Hrmap Hna Hcstk". iRight.
      iApply trap_handler_ok_switcher; [done | apply switcher_fault_pc_cap |].
      by iApply "Hfault".
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

  (** The return-to-switcher entry point is safe to execute: the registers
      are re-filtered, then the return routine runs ([switcher_return_unwind]). *)
  Lemma interp_expr_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C (WCap true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic] %cstk %Ws %Cs %rmap0
             (Hregs & _ & HPC & Hrmap & Hworld_interp & Hcont_K & Hna & Hcstk & %Hfreq)".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (rmap) "%Hfull_rmap #Hrmap_interp Hrmap Hworld_interp". clear rmap0.
    cbn in Hfull_rmap.
    getRegValList [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont_K $Hna $Hcstk]");
      [done|done|done|done|].
    iSplit; iApply "Hrmap_interp"; done.
  Qed.

  Lemma interp_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (mie : InterruptStatus) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp W C (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros (Hdisj) "[#Hinv #Hstatic]".
    rewrite interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_return with "[$Hinv $Hstatic]"); done.
  Qed.


End Switcher_Exception.
