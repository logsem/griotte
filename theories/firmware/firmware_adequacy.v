From iris.proofmode Require Import proofmode.
From griotte Require Import logrel.
From griotte Require Import hw_lang hw_instance pool.
From griotte Require Import switcher_preamble adequacy_helpers adequacy_common.
From griotte Require Import context_switch_layout_instance context_switching_support
  context_switching_hyps context_switching_scheduler_call context_switching_resume
  context_switching_wedge context_switching_scheduler_valid.
From griotte Require Import firmware_ok firmware_adequacy_obligations firmware_obligations
  firmware_thread_obligations.
(* Imported last: the fields of the image records shadow the fields of the
   layout records of [compartment_layout] and of [switcherLayout]. *)
From griotte Require Import image firmware.

(** * The end-to-end adequacy of a firmware

    The template: a firmware whose trusted code meets its per-thread
    obligations, started at the switcher's call of the scheduler, never
    sets the assert flag. Then its ghost state, and a sanity check on the
    scheduler's initial words. *)

(** ** The two stages of the template *)

(** The world of the scheduler's compartment at the start: the boot stack
    Temporary. *)
#[local] Definition sched_world0 (img : fw_image) : WORLD :=
  let bs := img_boot img in
  std_update_multiple fw_world0
    (finz.seq_between (img_b_boot_stack bs) (img_e_boot_stack bs)) Temporary.

(** The entry frame of the context-switch thread: the scheduler's stack and
    export table. *)
#[local] Definition sched_entry_frame `{MP : MachineParameters} (img : fw_image) (s : img_cmpt) :
    trusted_frame :=
  {| tf_csp := lword_of_word (sched_csp_word img);
     tf_export_tbl :=
       lword_of_word (Cap RW Global (cmpt_exp_tbl_pcc s) (cmpt_exp_tbl_entries_end s)
                        (cmpt_exp_tbl_pcc s));
     tf_error_count := 0 |}.

Section stages.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.
  (* The context-switch thread and the user threads meet here: every form
     names its thread. *)
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The slot of the user thread [i], Suspended at its entry: its
      trusted-stack invariant from its memory, allocated first, then its
      save area and its run by the obligations of the firmware, which
      receive the later credit of the slot. *)
  #[local] Lemma thread_slot fw img σ i ft :
    let swl := fw_switcher_layout img in
    firmware_ok fw img σ →
    fw_threads fw !! i = Some ft →
    mtdc_home_at (th := UserThread i) = tstack_home (swlayout := swl) i →
    ([∗ map] a↦w ∈ thread_mem fw img i ft, a ↦ₐ lword_of_word w) -∗
    ●(CSTK)[u i] (entry_cstack (fw_entry_frame fw img i)) -∗
    ◯(CSTK)[u i] (entry_cstack (fw_entry_frame fw img i)) -∗
    ([∗ set] C ∈ CNames,
       local_region_map (allocg := @cerise_registryG Σ (ceriseG_of (UserThread i)))
         (memg := @mem_gen_memG Σ (ceriseG_of (UserThread i)))
         (UserThread i) fw_world0 C ∅) -∗
    suspended_res i (fw_start_vals fw img i) -∗
    let _ : switcherLayout := swl in
    |={⊤}=>
      na_inv (tpool (UserThread i)) Ntstack
        (trusted_stack_inv (th := UserThread i) (swlayout := swl)) ∗
      ((fw_thread_res fw img i -∗
        £ 1
        ={⊤}=∗
        let _ : switcherLayout := swl in safe[u i]) -∗
       |={⊤}=> slot i None).
  Proof.
    intros swl Hok Hi Hhome.
    pose proof Hok as (_ & _ & _ & Hwf).
    pose proof (firmware_ok_thread0 _ _ _ Hok) as H0.
    pose proof (img_wf_threads_length _ _ Hwf) as Hlen.
    assert (i < length (img_threads img)) as Hlt.
    { rewrite Hlen. by eapply lookup_lt_Some. }
    assert (tstack_home (swlayout := swl) i = fw_thread_tstack img i) as Htst.
    { rewrite /tstack_home.
      change (@tlayout_of swl (UserThread i))
        with (@tlayout_of (fw_switcher_layout img) (UserThread i)).
      by rewrite fw_tlayout_lt. }
    assert (@mtdc_home Σ (@cb_mtdc_lent_of Σ ceriseb (UserThread i)) = fw_thread_tstack img i)
      as Hhome'.
    { etrans; [exact Hhome | exact Htst]. }
    assert (∀ r, r = cgp ∨ r = cra ∨ r = csp → fw_cleared_regs !! r = None) as Hnone.
    { intros r Hr. apply not_elem_of_dom. rewrite fw_cleared_regs_dom.
      intros [_ Hn]%elem_of_difference. apply Hn.
      rewrite !elem_of_union !elem_of_singleton. tauto. }
    iIntros "Hmem Hcstk_full Hcstk Hlocals Hres".
    iNamed "Hres".
    iEval (rewrite Hhome Htst) in "Hmtdc".
    iMod (fw_thread_trusted_stack_inv_alloc fw img i ft ⊤ Hwf H0 Hi Hhome'
           with "Hmem Hcstk_full Hmtdc") as "(#Hinv & Hstack & Hsa)".
    rewrite (fw_tstack_content_save_area fw img i ft Hwf Hi).
    destruct (fw_save_area_resume_ok fw img i) as [Hmie Hrok].
    iModIntro. iFrame "Hinv". iIntros "Hobl".
    iModIntro.
    iApply (slot_suspended_intro i _ _ Hmie Hrok with "Hsa Hlent Hauths").
    (* The run passes the slot's credit to the obligations *)
    iIntros "!> Hheld Hcred".
    iApply ("Hobl" with "[-Hcred] Hcred").
    rewrite /fw_thread_res /fw_start_vals /=.
    iDestruct (big_sepM_insert with "Hregs") as "[Hcra Hregs]".
    { rewrite !lookup_insert_ne //; auto. }
    iDestruct (big_sepM_insert with "Hregs") as "[Hcsp Hregs]".
    { rewrite !lookup_insert_ne //; auto. }
    iDestruct (big_sepM_insert with "Hregs") as "[Hcgp Hregs]".
    { auto. }
    iFrame "Hinv HPC Hcgp Hcsp Hcra Hregs Hstack Hcstk Hna HMIE Hheld Hlocals".
  Qed.

  (** The save area of the idle thread, from its memory. *)
  #[local] Lemma idle_save_area_of_mem fw img :
    let swl := fw_switcher_layout img in
    let d := img_idle img in
    img_wf fw img →
    ([∗ map] a↦w ∈ idle_mem img, a ↦ₐ lword_of_word w)
    ==∗
    save_area_holed (swlayout := swl) (UserThread (length (fw_threads fw)))
      (idle_save_area swl (img_b_idle_hazard d) (img_e_idle_hazard d)).
  Proof.
    intros swl d Hwf.
    destruct (img_wf_idle_boot _ _ Hwf) as [ [Hsize _] _].
    pose proof (img_wf_threads_length _ _ Hwf) as Hlen.
    pose proof (img_wf_threads_nonempty _ _ Hwf) as Hne.
    assert (fw_threads fw !! 0 = Some (fw_thread0 fw)) as H0.
    { rewrite /fw_thread0. by destruct (fw_threads fw). }
    pose proof (fw_switcher_layout_wf fw img Hwf H0) as Hswl_wf.
    set (n := length (fw_threads fw)).
    set (b := img_b_idle_trusted_stack d) in *.
    set (save := compartment_layout.save_area_content
                   (@context_switching_exit_tail.exited_thread_pcc swl) (WInt 0) (WInt 0) (WInt 0)
                   (Cap WO Global (img_b_idle_hazard d) (img_e_idle_hazard d) (img_b_idle_hazard d))
                   (WInt (mstatus_enc InterruptDisabled InterruptEnabled))).
    (* The loop of the idle thread is the one of an exited thread *)
    assert (idle_mem img =
              mem_region b (compartment_layout.initial_trusted_stack_content save
                              (WInt 0) (WInt 0) 0 0)
              ∪ mem_region (img_b_idle_hazard d) [WInt 0; WInt 0]) as ->.
    { rewrite /idle_mem /note /save /context_switching_exit_tail.exited_thread_pcc.
      change (@a_tail swl) with (a_switcher_call (img_sw img) ^+ switcher_offset_tail)%a.
      by rewrite switcher_offset_tail_eq. }
    (* Its save area, the first words of its trusted stack *)
    rewrite /compartment_layout.initial_trusted_stack_content.
    revert Hsize. tstack_unfold. intros Hsize.
    rewrite (mem_region_app b (b ^+ 21)%a (img_e_idle_trusted_stack d)).
    2: { rewrite /save compartment_layout.length_save_area_content. unfold b, d. solve_addr. }
    2: { rewrite !length_app length_replicate. cbn [length]. unfold b, d. solve_addr. }
    iIntros "Hmem".
    iDestruct (big_sepM_subseteq with "Hmem") as "Hmem".
    { etrans; [|apply map_union_subseteq_l]. apply map_union_subseteq_l. }
    iMod (@mkregion_helpers.mkregion_prepare Σ (ceriseG_of (UserThread n)) with "Hmem")
      as "Hmem".
    { rewrite /save compartment_layout.length_save_area_content. unfold b, d. solve_addr. }
    iModIntro.
    iAssert (region_pointsto (ceriseg := ceriseG_of (UserThread n))
               (@switcher.b_trusted_stack (@tlayout_of swl (UserThread n)))
               (@switcher.b_trusted_stack (@tlayout_of swl (UserThread n)) ^+ TSTACK_REGFRAME_SZ)%a
               (lword_of_word <$> save))%I with "[Hmem]" as "Hreg".
    { rewrite /region_pointsto big_sepL2_fmap_r.
      change (@tlayout_of swl (UserThread n))
        with (@tlayout_of (fw_switcher_layout img) (UserThread n)).
      rewrite /n -Hlen fw_tlayout_idle;
        last (rewrite Hlen; destruct (fw_threads fw); [done | cbn [length]; lia]).
      iExact "Hmem". }
    iDestruct (save_area_split (th := UserThread n) (swlayout := swl)
                  (lword_of_word <$> save) with "Hreg") as "[$ _]".
    rewrite list_lookup_fmap /save compartment_layout.save_area_content_hazard. done.
  Qed.

  (** The scheduler's compartment [fc] is the untrusted top of the call
      stack of the context-switch thread at its entry frame: its export
      table's header, its PCC and globals valid in every private future of
      [W], and its stack. *)
  #[local] Lemma sched_top_cmpt fw img σ fc sb (C_sched : CmptName) (W : WORLD) :
    let swl := fw_switcher_layout img in
    let s := cmpt_of img (fc_name fc) in
    firmware_ok fw img σ →
    fw_sched_of (fw_cmpts fw) = Some (fc, sb) →
    fw_cmpt_pers_res (th := UserThread 0) img fc -∗
    interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
      (CR := crit_route_full (swlayout := swl))
      W C_sched (lword_of_word (Cap RX Global (cmpt_b_pcc s) (cmpt_e_pcc s) (cmpt_b_pcc s))) -∗
    interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
      (CR := crit_route_full (swlayout := swl))
      W C_sched (lword_of_word (sched_cgp_word fw img)) -∗
    interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
      (CR := crit_route_full (swlayout := swl))
      W C_sched (lword_of_word (sched_csp_word img)) -∗
    top_cmpt_untrusted (th := CtxSwitch)
      (interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
         (CR := crit_route_full (swlayout := swl)))
      W C_sched (entry_cstack (sched_entry_frame img s)).
  Proof.
    intros swl s Hok Hsched.
    pose proof Hok as (_ & _ & _ & Hwf).
    destruct (fw_sched_of_in _ _ _ Hsched) as [Hfc_in Hbody].
    pose proof (img_wf_cmpt_layout _ _ _ Hwf Hfc_in) as Hc.
    pose proof (icl_exp_tbl_pcc_size _ Hc) as Htbl_cgp_size.
    assert (cmpt_exp_tbl_cgp s = (cmpt_exp_tbl_pcc s ^+ ExportTable_offset_cgp)%a)
      as Hcgp_eq by (unfold s; solve_addr+Htbl_cgp_size).
    iIntros "#Hpers #Hpcc #Hcgp #Hcsp".
    iEval (rewrite /fw_cmpt_pers_res /fw_handler_res Hbody -/s Hcgp_eq) in "Hpers".
    iDestruct "Hpers" as "(#Htbl_pcc & #Htbl_cgp & [#Heh #Hehs] & _)".
    rewrite /top_cmpt_untrusted /=.
    iSplitR.
    - (* The header of its export table, at the context-switch thread *)
      iExists _, _, ExportTable_no_handler, ExportTable_no_handler.
      rewrite -(handler_stackful_thread_indep (UserThread 0) CtxSwitch)
        -(handler_stackless_thread_indep (UserThread 0) CtxSwitch).
      iFrame "Htbl_pcc Htbl_cgp Heh Hehs".
      iSplit; last done.
      iIntros "!>" (W' _). iSplit.
      + iApply (interp_global_world_free with "Hpcc"). done.
      + iEval (rewrite /sched_cgp_word Hsched /note) in "Hcgp".
        iApply (interp_global_world_free with "Hcgp"). done.
    - (* Its stack *)
      rewrite /entry_stack_interp /sched_entry_frame /sched_csp_word /note /=.
      iEval (rewrite /sched_csp_word /note) in "Hcsp".
      iDestruct (interp_cap_disjoint_wl with "Hcsp") as %[_ Hheap]; first done.
      iExists RWL, Local, _, _, _.
      iSplit; first done. iSplit; first done.
      iModIntro. iExact "Hcsp".
  Qed.

  (** A compartment's resources give those of [fw_cmpt_res_user]. *)
  #[local] Lemma fw_cmpt_res_user_of img fc :
    fw_cmpt_res (th := UserThread 0) img fc ⊢ fw_cmpt_res_user (th := UserThread 0) img fc.
  Proof. rewrite /fw_cmpt_res_user. destruct (fc_body fc); by iIntros. Qed.

  (** The compartments, initialised: the scheduler's [fc], and the others. *)
  #[local] Lemma fw_cmpts_res_sched img (fcs : list fw_cmpt) fc sb :
    fc ∈ fcs →
    fc_body fc = SchedulerBody sb →
    ([∗ list] x ∈ fcs, fw_cmpt_res (th := UserThread 0) img x) ⊢
    fw_cmpt_res (th := UserThread 0) img fc ∗
    [∗ list] x ∈ fcs, fw_cmpt_res_user (th := UserThread 0) img x.
  Proof.
    intros Hin Hbody. induction fcs as [|x fcs IH]; first by apply elem_of_nil in Hin.
    rewrite !big_sepL_cons. apply elem_of_cons in Hin as [-> | Hin].
    - iIntros "[$ Hrest]". iSplitR; first by rewrite /fw_cmpt_res_user Hbody.
      iApply (big_sepL_mono with "Hrest"). intros. apply fw_cmpt_res_user_of.
    - iIntros "[Hx Hrest]". iDestruct (IH Hin with "Hrest") as "[$ $]".
      by iApply fw_cmpt_res_user_of.
  Qed.

  (** What the first stage leaves to the context-switch thread: the world
      of the scheduler's compartment [fc] and its call stack, its export
      table, the validity of its PCC, globals and stack, the switcher's
      static facts at every user thread, the scheduler's words in the
      switcher and its state between two activations. *)
  #[local] Definition sched_start_res (fw : firmware) (img : fw_image) (C_sched : CmptName)
      (fc : fw_cmpt) : iProp Σ :=
    let swl := fw_switcher_layout img in
    let s := cmpt_of img (fc_name fc) in
    let W := sched_world0 img in
    "Hworld" ∷ world_interp (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch) W C_sched ∗
    "Hcstk" ∷ ◯(CSTK)[CtxSwitch] (entry_cstack (sched_entry_frame img s)) ∗
    "#Htop" ∷
      top_cmpt_untrusted (th := CtxSwitch)
        (interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
           (CR := crit_route_full (swlayout := swl)))
        W C_sched (entry_cstack (sched_entry_frame img s)) ∗
    "#Hpcc" ∷
      interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
        (CR := crit_route_full (swlayout := swl))
        W C_sched (lword_of_word (Cap RX Global (cmpt_b_pcc s) (cmpt_e_pcc s) (cmpt_b_pcc s))) ∗
    "#Hcgp" ∷
      interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
        (CR := crit_route_full (swlayout := swl))
        W C_sched (lword_of_word (sched_cgp_word fw img)) ∗
    "#Hcsp" ∷
      interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
        (CR := crit_route_full (swlayout := swl))
        W C_sched (lword_of_word (sched_csp_word img)) ∗
    "#Hstatics" ∷
      ([∗ list] t ∈ seq 0 (S (length (fw_threads fw))),
         switcher_static (th := UserThread t) (swlayout := swl)) ∗
    "#Hwords" ∷
      scheduler_words (swlayout := swl) (lword_of_word (sched_pcc_word fw img))
        (lword_of_word (sched_cgp_word fw img)) (lword_of_word (sched_csp_word img)) ∗
    "#Hsched" ∷
      saved_prop_own γ_scheduler DfracDiscarded
        (scheduler_concrete (swlayout := swl) C_sched (lword_of_word (sched_csp_word img))).

  (** The first stage: the initial resources split by part; the libraries
      persistent, the assert flag in its invariant, the switcher, the
      compartments initialised; the switcher's
      static facts at every user thread; the scheduler's world closed at
      the context-switch thread and its state named; the obligations of
      the firmware run; the slots of the user threads and of the idle
      thread. *)
  #[local] Lemma template_stage1 fw img σ fc sb (C_sched : CmptName) :
    let swl := fw_switcher_layout img in
    let n := length (fw_threads fw) in
    let vs := imap (λ i _, fw_start_vals fw img i) (fw_threads fw) ++
                [idle_start_vals (swlayout := swl)] in
    let efs := imap (λ i _, fw_entry_frame fw img i) (fw_threads fw) ++
                 [fw_entry_frame fw img n] in
    let ots := {[ot_switcher (img_sw img); (ot_switcher (img_sw img) ^+ 1)%ot]} ∪
                 list_to_set (fw_otypes fw) in
    firmware_ok fw img σ →
    fw_sched_of (fw_cmpts fw) = Some (fc, sb) →
    CtxSwitch ∈ cmpt_threads C_sched →
    @mtcc_vec (@cb_trapVector Σ ceriseb) = fw_mtcc img →
    (∀ t, t < length vs → mtdc_home_at (th := UserThread t) = tstack_home (swlayout := swl) t) →
    (⊢ fw_shared_res fw img C_sched
       ={⊤}=∗
       [∗ list] i ↦ _ ∈ fw_threads fw,
         (fw_thread_res fw img i -∗
          £ 1
          ={⊤}=∗
          let _ : switcherLayout := swl in safe[u i])) →
    ([∗ map] a↦w ∈ mem σ, a ↦ₐ lword_of_word w) -∗
    ([∗ map] a↦s ∈ shadowtbl σ, a ↦ₛ s) -∗
    ([∗ map] a↦c ∈ init_claims (fw_set (fw_heap_roots fw)), addr_alloc a c) -∗
    ([∗ list] t ↦ v ∈ vs, suspended_res t v) -∗
    ([∗ list] t ↦ _ ∈ vs,
       saved_prop_own (γ_exit (UserThread t)) DfracDiscarded
         (exit_concrete (th := UserThread t) (swlayout := swl))) -∗
    saved_prop_own γ_scheduler (DfracOwn 1) True -∗
    ([∗ set] o ∈ ots, can_alloc_pred o) -∗
    ◯(CSTK)[CtxSwitch] (entry_cstack (sched_entry_frame img (cmpt_of img (fc_name fc)))) -∗
    ([∗ list] k ↦ ef ∈ efs, ●(CSTK)[u k] (entry_cstack ef) ∗ ◯(CSTK)[u k] (entry_cstack ef)) -∗
    world_interp (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch) fw_world0 C_sched -∗
    ([∗ set] C ∈ CNames ∖ {[C_sched]},
       perm_region_map (allocg := @cerise_registryG Σ (ceriseG_of (UserThread 0)))
         (memg := @mem_gen_memG Σ (ceriseG_of (UserThread 0))) C ∅) -∗
    ([∗ list] k ↦ _ ∈ efs, [∗ set] C ∈ CNames,
       local_region_map (allocg := @cerise_registryG Σ (ceriseG_of (UserThread k)))
         (memg := @mem_gen_memG Σ (ceriseG_of (UserThread k)))
         (UserThread k) fw_world0 C ∅)
    ={⊤}=∗
    (let _ : switcherLayout := swl in [∗ list] t ↦ _ ∈ vs, slot t None) ∗
    inv Nassert_flag (img_flag img ↦ₐ WInt 0) ∗
    sched_start_res fw img C_sched fc.
  Proof.
    intros swl n vs efs ots Hok Hsched Hin Htv Hhomes Hobl.
    pose proof Hok as (_ & [_ Hsh] & _ & Hwf).
    pose proof (firmware_ok_thread0 _ _ _ Hok) as H0.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    pose proof (img_wf_switcher_layout _ _ _ _ H0 Hwf) as Hsw.
    pose proof (img_wf_trusted_stack_layout _ _ _ _ H0 Hwf) as Hts.
    destruct (img_wf_flag _ _ Hwf) as (o_flag & Ho_flag & Hflag_size).
    destruct (fw_shared_of_Some _ _ _ Ho_flag) as [_ Hflag_name].
    destruct (img_wf_otypes _ _ Hwf) as [Hot_nodup _].
    apply NoDup_cons in Hot_nodup as [Hot_notin Hot_nodup].
    apply NoDup_cons in Hot_nodup as [Hot_notin' Hot_nodup].
    destruct (fw_sched_of_in _ _ _ Hsched) as [Hfc_in Hbody].
    pose proof (img_wf_cmpt_layout _ _ _ Hwf Hfc_in) as Hc.
    destruct (img_wf_idle_boot _ _ Hwf) as [_ (Hboot_size & _ & Hboot_range)].
    assert (length vs = S n) as Hlen_vs by rewrite /vs length_app length_imap /= Nat.add_1_r //.
    iIntros "Hmem Hshadow Hclaims Hsusp #Hexits Hsched Hots Hcstk_ctx Hcstks Hworld_ctx Hworlds
      Hlocals".
    rewrite /note in Hsh. rewrite Hsh.
    (* The memory, by part *)
    iDestruct (firmware_ok_mem_split (ceriseg := ceriseG_of (UserThread 0)) fw img σ Hok
                with "Hmem")
      as "(Hheap & Hsw_code & Hshared_mem & Hlibs_mem & Hcmpts & Hthreads_mem & Hidle_mem &
           Hboot_mem)".
    (* The libraries, persistent *)
    iAssert (|==> [∗ list] l ∈ fw_libs fw,
               [∗ map] a↦w ∈ lib_mem fw img l, a ↦ₐ□ lword_of_word w)%I
      with "[Hlibs_mem]" as ">#Hlibs".
    { iApply big_sepL_bupd. iApply (big_sepL_mono with "Hlibs_mem").
      iIntros (k l _) "Hl". iApply big_sepM_bupd. iApply (big_sepM_mono with "Hl").
      iIntros (a w _) "Ha". iApply (pointsto_persist with "Ha"). }
    (* The assert flag, in its invariant; the other shared objects *)
    iDestruct (big_sepL_shared_of with "Hshared_mem") as "[Hflag Hshared]"; first exact Ho_flag.
    iEval (rewrite (shared_mem_flag img o_flag Hflag_name Hflag_size) big_sepM_singleton)
      in "Hflag".
    iMod (inv_alloc Nassert_flag ⊤ (img_flag img ↦ₐ WInt 0) with "Hflag") as "#Hflag".
    (* The sealing types *)
    rewrite /ots big_sepS_union;
      last (apply disjoint_union_l; split; apply disjoint_singleton_l; rewrite elem_of_list_to_set;
            [intros ?; apply Hot_notin; by right | done]).
    rewrite big_sepS_union;
      last (apply disjoint_singleton_l, not_elem_of_singleton; intros Heq;
            apply Hot_notin; rewrite elem_of_cons; by left).
    rewrite !big_sepS_singleton big_sepS_list_to_set //.
    iDestruct "Hots" as "[ [Hot_sw Hot_ts] Hotypes]".
    (* The switcher, with the scheduler's words *)
    iEval (rewrite (switcher_mem_layout _ _ _ _ _ Hts Hsw)
             /compartment_layout.cmpt_switcher_code_mregion) in "Hsw_code".
    iDestruct (big_sepL_lookup _ _ 0 with "Hexits") as "Hexit0".
    { rewrite /vs lookup_app_l; last (rewrite length_imap; by eapply lookup_lt_Some).
      rewrite list_lookup_imap H0 //. }
    iMod (initialise_switcher_shared (th := UserThread 0) (swlayout := swl)
            (sched_pcc_word fw img) (sched_cgp_word fw img) (sched_csp_word img)
           with "Hsw_code Hot_sw Hot_ts Hexit0")
      as "(_ & _ & #Hstatic0 & #Hw_pcc & #Hw_cgp & #Hw_csp)".
    { rewrite Htv //. }
    iClear "Hexit0".
    iAssert (scheduler_words (swlayout := swl) (lword_of_word (sched_pcc_word fw img))
               (lword_of_word (sched_cgp_word fw img)) (lword_of_word (sched_csp_word img)))%I
      as "#Hwords".
    { rewrite /scheduler_words. iFrame "Hw_pcc Hw_cgp Hw_csp". iPureIntro.
      rewrite /sched_pcc_word /sched_cgp_word /sched_csp_word Hsched /note /=.
      rewrite /is_heap_cap /heap_cap_base /=.
      rewrite (proj1 (icl_pcc_not_heap _ Hc)) (proj1 (icl_cgp_not_heap _ Hc))
        (proj1 (range_ok_not_heap _ _ Hboot_range)). done. }
    (* The switcher's static facts at every user thread, the idle included *)
    iAssert (□ ∀ t, ⌜t < S n⌝ → switcher_static (th := UserThread t) (swlayout := swl))%I
      as "#Hst".
    { iIntros "!>" (t Ht).
      destruct (lookup_lt_is_Some_2 vs t) as [v Hv]; first lia.
      iDestruct (big_sepL_lookup _ _ t v with "Hexits") as "He"; first done.
      iApply (switcher_static_thread (UserThread 0) (UserThread t) with "Hstatic0 He"). }
    iAssert ([∗ list] t ∈ seq 0 (S n), switcher_static (th := UserThread t) (swlayout := swl))%I
      as "#Hstatics".
    { iApply big_sepL_intro. iIntros "!>" (k t Hk%lookup_seq). iApply "Hst". iPureIntro. lia. }
    (* The compartments, the scheduler's apart *)
    iMod (fw_cmpts_init (th := UserThread 0) with "Hcmpts") as "Hcmpts"; first exact Hok.
    iDestruct (fw_cmpts_res_sched with "Hcmpts") as "[(Hsched_mem & _ & #Hsched_pers) Hcmpts]";
      [exact Hfc_in | exact Hbody |].
    (* The trap vector of the context-switch thread *)
    iPoseProof "Hstatic0" as "Hstatic0'".
    iEval (rewrite /switcher_static) in "Hstatic0'".
    iDestruct "Hstatic0'" as "(Hcode0 & _ & %Hmtcc_vec & _)".
    iEval (rewrite (codefrag_pers_thread_indep (UserThread 0) CtxSwitch)) in "Hcode0".
    iPoseProof (ctx_trap_vector_safe_holds (swlayout := swl) Hmtcc_vec with "Hcode0")
      as "#Htrap".
    (* The scheduler's world at the context-switch thread *)
    iMod (@mkregion_helpers.mkregion_prepare Σ (ceriseG_of CtxSwitch) with "[Hboot_mem]")
      as "Hboot";
      [exact Hboot_size | rewrite /boot_mem /note (mem_region_mkregion _ _ _ Hboot_size) // |].
    iMod (fw_close_sched_world (E := ⊤) fw img σ fc sb C_sched Hok Hsched Hin
           with "Hcode0 Htrap Hstatics Hsched_mem [Hboot] Hworld_ctx")
      as "(Hworld_ctx & #Hpcc & #Hcgp & #Hcsp)".
    { rewrite /region_pointsto big_sepL2_fmap_r. iExact "Hboot". }
    iPoseProof (sched_top_cmpt fw img σ fc sb C_sched (sched_world0 img) Hok Hsched
                 with "Hsched_pers Hpcc Hcgp Hcsp") as "#Htop".
    (* The scheduler's state between two activations *)
    iMod (saved_prop_update (scheduler_concrete (swlayout := swl) C_sched
                               (lword_of_word (sched_csp_word img))) with "Hsched") as "Hsched".
    iMod (saved_prop_persist with "Hsched") as "#Hsched".
    (* The user threads, the idle thread apart *)
    iEval (rewrite /vs big_sepL_app big_sepL_imap_index big_sepL_singleton length_imap
             Nat.add_0_r) in "Hsusp".
    iDestruct "Hsusp" as "[Hsusp Hsusp_idle]".
    iEval (rewrite /efs big_sepL_app big_sepL_imap_index) in "Hcstks".
    iDestruct "Hcstks" as "[Hcstks _]".
    (* The local maps of the idle thread are dropped *)
    iEval (rewrite /efs big_sepL_app big_sepL_imap_index) in "Hlocals".
    iDestruct "Hlocals" as "[Hlocals _]".
    (* The trusted-stack invariants of the user threads, before the
       obligations; the rest of each slot waits for its run *)
    iAssert (|={⊤}=> [∗ list] k ↦ ft ∈ fw_threads fw,
               na_inv (tpool (UserThread k)) Ntstack
                 (trusted_stack_inv (th := UserThread k) (swlayout := swl)) ∗
               ((fw_thread_res fw img k -∗
                 £ 1
                 ={⊤}=∗
                 let _ : switcherLayout := swl in safe[u k]) -∗
                |={⊤}=> let _ : switcherLayout := swl in slot k None))%I
      with "[Hsusp Hcstks Hlocals Hthreads_mem]" as ">Hallocs".
    { iApply big_sepL_fupd.
      iDestruct (big_sepL_sep_2 with "Hlocals Hcstks") as "H".
      iDestruct (big_sepL_sep_2 with "Hsusp H") as "H".
      iDestruct (big_sepL_sep_2 with "Hthreads_mem H") as "H".
      iApply (big_sepL_impl with "H").
      iIntros "!>" (k ft Hk) "(Hm & Hs & Hl & [Hf Hfr])".
      iApply (thread_slot fw img σ k ft Hok Hk with "Hm Hf Hfr Hl Hs").
      apply Hhomes. rewrite Hlen_vs. apply lookup_lt_Some in Hk. rewrite /n. lia. }
    iDestruct (big_sepL_sep with "Hallocs") as "[#Htstacks Hslot_runs]".
    (* The obligations of the firmware *)
    iMod (Hobl with "[Hshared Hcmpts Hotypes Hworlds Hheap Hshadow Hclaims]") as "Hruns".
    { rewrite /fw_shared_res.
      iFrame "Htstacks Hlibs Hshared Hcmpts Hotypes Hworlds Hheap Hshadow Hclaims".
      iApply big_sepL_intro. iIntros "!>" (k ft Hk%lookup_lt_Some). iApply "Hst".
      iPureIntro. rewrite /n. lia. }
    (* The slots of the user threads *)
    iAssert (|={⊤}=> [∗ list] k ↦ ft ∈ fw_threads fw,
               let _ : switcherLayout := swl in slot k None)%I
      with "[Hslot_runs Hruns]" as ">Hslots".
    { iApply big_sepL_fupd.
      iDestruct (big_sepL_sep_2 with "Hslot_runs Hruns") as "H".
      iApply (big_sepL_impl with "H").
      iIntros "!>" (k ft Hk) "[Hslot Hrun]".
      iApply ("Hslot" with "Hrun"). }
    (* The slot of the idle thread *)
    iMod (idle_save_area_of_mem fw img Hwf with "Hidle_mem") as "Hidle_sa".
    iPoseProof ("Hst" $! n with "[]") as "Hstatic_n"; first (iPureIntro; lia).
    iEval (rewrite /switcher_static) in "Hstatic_n".
    iDestruct "Hstatic_n" as "(Hcode_n & _)".
    iPoseProof (idle_slot (swlayout := swl) n with "Hcode_n Hidle_sa Hsusp_idle") as "Hslot_idle".
    iModIntro. iFrame "Hflag".
    iSplitL "Hslots Hslot_idle".
    { iEval (rewrite /vs big_sepL_app big_sepL_imap_index big_sepL_singleton length_imap
               Nat.add_0_r).
      iFrame. }
    rewrite /sched_start_res.
    iFrame "Hworld_ctx Hcstk_ctx Htop Hpcc Hcgp Hcsp Hstatics Hwords Hsched".
  Qed.

  (** The second stage: the context-switch thread runs the scheduler's
      call, under the virtualisation of the switcher. *)
  #[local] Lemma template_stage2 fw img σ fc sb (C_sched : CmptName) :
    let swl := fw_switcher_layout img in
    firmware_ok fw img σ →
    fw_sched_of (fw_cmpts fw) = Some (fc, sb) →
    CtxSwitch ∈ cmpt_threads C_sched →
    cmpt_shared C_sched = false →
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    (∀ t, ∃ p b e a, mtdc_home_at (th := UserThread t) = TStack p b e a) →
    (∀ t, t < S (length (fw_threads fw)) →
          mtdc_home_at (th := UserThread t) = tstack_home (swlayout := swl) t) →
    sched_start_res fw img C_sched fc -∗
    PC ↦ₚ[CtxSwitch] lword_of_word (pcc σ) -∗
    regs[CtxSwitch] (lword_of_word <$> reg σ) -∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) -∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled -∗
    handover_res (ceriseg := ceriseG_of CtxSwitch) -∗
    mtdc_lent_at (th := CtxSwitch) -∗
    na_own (tpool CtxSwitch) ⊤ -∗
    inv Npool (let _ : switcherLayout := swl in Pool (seq 0 (S (length (fw_threads fw))))) -∗
    inv_CtxSwitch -∗
    thread_res CtxSwitch (Exec : thread_langs.expr CtxK) -∗
    WP_hw griotte_lang.Exec {{ _, True }}.
  Proof.
    intros swl Hok Hsched Hin Hexcl Hhome_ctx Hus Hhomes.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    pose proof Hok as (_ & _ & Hstart & Hwf).
    pose proof (img_wf_threads_length _ _ Hwf) as Hlen.
    destruct (fw_sched_of_in _ _ _ Hsched) as [Hfc_in _].
    pose proof (img_wf_cmpt_layout _ _ _ Hwf Hfc_in) as Hc.
    destruct σ as [w_pc regs sregs m sh td].
    rewrite /start_ok /note in Hstart.
    destruct Hstart as (Hpc & Hcra & Hcgp & Hcsp & Hca0 & (z1 & z2 & z3 & Hca1 & Hca2 & Hca3) &
                        Hzero & _).
    cbn [pcc reg] in *. subst w_pc.
    set (s := cmpt_of img (fc_name fc)) in *.
    set (W := sched_world0 img).
    set (n := length (fw_threads fw)).
    set (a_e := addr_off (cmpt_b_pcc s) (sb_entry sb)).
    assert (lword_of_word (sched_pcc_word fw img) =
              lword_of_word (Sentry FwdDisable RX Global (cmpt_b_pcc s) (cmpt_e_pcc s) a_e))
      as Hpcc_eq by (rewrite /sched_pcc_word Hsched /note //).
    assert (isLocalWord (lword_of_word (sched_cgp_word fw img)).(lw) = false) as Hcgp_loc.
    { rewrite /sched_cgp_word Hsched /note //. }
    assert (∀ B, B ∈ seq 0 (S n) ↔ B < @swl_nthreads swl) as Hts.
    { intros B. rewrite elem_of_seq.
      change (@swl_nthreads swl) with (S (length (img_threads img))). lia. }
    assert (∀ B, B ∈ seq 0 (S n) → mtdc_home_at (th := UserThread B) = tstack_home B)
      as Hhomes'.
    { intros B HB%elem_of_seq. apply Hhomes. lia. }
    iIntros "Hres HPC Hreg Hmtdc HMIE Hho Hlent Hna #Hpool #Hact Htr".
    iNamed "Hres".
    (* The switcher's code and trap vector at the context-switch thread *)
    iDestruct (big_sepL_lookup _ _ 0 0 with "Hstatics") as "Hstatic0"; first done.
    iEval (rewrite /switcher_static) in "Hstatic0". iNamed "Hstatic0".
    iEval (rewrite (codefrag_pers_thread_indep (UserThread 0) CtxSwitch)) in "Hswitcher_code".
    iPoseProof (ctx_trap_vector_safe_holds Hmtcc_vec with "Hswitcher_code") as "#Htrap".
    (* The scheduler's entry *)
    iPoseProof (scheduler_entry_valid_intro (swlayout := swl) C_sched
                  (lword_of_word (sched_pcc_word fw img)) (lword_of_word (sched_cgp_word fw img)) W
                  FwdDisable RX
                  (cmpt_b_pcc s) (cmpt_e_pcc s) (cmpt_b_pcc s) (cmpt_b_pcc s) (cmpt_e_pcc s) a_e
                  Hpcc_eq (icl_pcc_not_heap _ Hc) eq_refl ltac:(solve_addr) ltac:(solve_addr)
                  ltac:(done) Hcgp_loc with "Hpcc Hcgp") as "#Hentry".
    (* The return from the scheduler *)
    iAssert (ctx_switch_env (swlayout := swl) C_sched (lword_of_word (sched_pcc_word fw img))
               (lword_of_word (sched_cgp_word fw img)) (lword_of_word (sched_csp_word img))
               (seq 0 (S n))) as "#Henv".
    { rewrite /ctx_switch_env.
      iSplit; first (iPureIntro; apply NoDup_seq).
      iSplit; first (iPureIntro; exact Hts).
      iSplit; first (iPureIntro; exact Hhome_ctx).
      iSplit; first (iPureIntro; exact Hhomes').
      iSplit; first (iPureIntro; exact Hin).
      iFrame "Hpool Hact Hstatics Hwords Hsched". iSplit; last iExact "Htrap".
      iModIntro. iExact "Hentry". }
    iPoseProof (ctx_resume_specs_hold (swlayout := swl) C_sched _ _ _ (seq 0 (S n))
                  ltac:(done) with "Henv") as "#Hresume".
    iClear "Henv Hswitcher_key Hswitcher_sealing Htstacks_key Hexit_prop".
    (* The registers of the call *)
    set (lreg := lword_of_word <$> regs).
    assert (dom lreg = all_registers_s) as Hdom.
    { rewrite /lreg dom_fmap_L. apply set_eq. intros r. split; intros _; last apply elem_of_dom.
      + apply all_registers_s_correct.
      + destruct (decide (r ∈ ({[cra; cgp; csp; ca0; ca1; ca2; ca3]} : gset RegName))) as [Hr|Hr];
          last by rewrite Hzero.
        rewrite !elem_of_union !elem_of_singleton in Hr.
        destruct Hr as [ [ [ [ [ [-> | ->] | ->] | ->] | ->] | ->] | ->]; eauto. }
    assert (∀ r, r ∈ registers_scheduler_call → lreg !! r = Some (lword_of_word (WInt 0)))
      as Hclear.
    { intros r Hr.
      rewrite -registers_except_scheduler_call /registers_except list_elem_of_filter in Hr.
      destruct Hr as [ [_ Hr] _]. rewrite /lreg lookup_fmap Hzero //.
      rewrite !elem_of_union !elem_of_singleton. intros Hx.
      apply Hr. rewrite !elem_of_cons. tauto. }
    iAssert (□ ∀ (r : RegName) (w : LWord), ⌜r ∈ [ca0; ca1; ca2; ca3]⌝ → ⌜lreg !! r = Some w⌝ →
               interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
                 (CR := crit_route_full (swlayout := swl)) W C_sched w)%I as "#Hargs".
    { iIntros "!>" (r w Hr Hw). rewrite /lreg lookup_fmap in Hw.
      rewrite !elem_of_cons in Hr.
      destruct Hr as [-> | [-> | [-> | [-> | Hr] ] ] ]; last by apply elem_of_nil in Hr.
      - rewrite Hca0 fw_length_eq in Hw. injection Hw as <-.
        iApply (thread_handle_valid fw img _ n W C_sched Hok ltac:(done)).
        iApply (big_sepL_elem_of with "Hstatics"). apply elem_of_seq. lia.
      - rewrite Hca1 in Hw. injection Hw as <-. iApply interp_int.
      - rewrite Hca2 in Hw. injection Hw as <-. iApply interp_int.
      - rewrite Hca3 in Hw. injection Hw as <-. iApply interp_int. }
    (* The jump to the scheduler *)
    iEval (rewrite -(world_resources_exclusive (th := CtxSwitch) _ _ Hexcl)) in "Hworld".
    iPoseProof (shared_credit_exclusive _ Hexcl) as "Hcred".
    iPoseProof (ctx_scheduler_jump_spec (swlayout := swl) C_sched
                  (lword_of_word (sched_pcc_word fw img)) (lword_of_word (sched_cgp_word fw img))
                  (lword_of_word (sched_csp_word img)) W
                  (entry_cstack (sched_entry_frame img s)) [] [] lreg Hin Hdom
                  ltac:(by rewrite /lreg lookup_fmap Hcra) ltac:(by rewrite /lreg lookup_fmap Hcsp)
                  ltac:(by rewrite /lreg lookup_fmap Hcgp) Hclear ltac:(done)
                 with "[$HPC $Hswitcher_code $Htrap $Hresume $Hargs $Hreg $HMIE $Hmtdc $Hlent $Hho
                        $Hna $Hworld $Hcred $Hcstk $Htop $Hcsp]") as "Hwp".
    { rewrite /scheduler_entry_valid. iModIntro. iExact "Hentry". }
    (* The virtualisation of the switcher *)
    assert (wellshaped (Exec : thread_langs.expr CtxK)) as Hws by (left; by eexists).
    iApply (virtualise_scheduler (swlayout := swl) C_sched
              (lword_of_word (sched_pcc_word fw img)) (lword_of_word (sched_cgp_word fw img))
              (lword_of_word (sched_csp_word img)) (seq 0 (S n)) CtxSwitch Exec 0 W FwdDisable RX
              (cmpt_b_pcc s) (cmpt_e_pcc s) (cmpt_b_pcc s) (cmpt_b_pcc s) (cmpt_e_pcc s) a_e
              ltac:(done) (NoDup_seq _ _) Hts Hhome_ctx Hus Hhomes' Hin Hpcc_eq
              (icl_pcc_not_heap _ Hc) eq_refl ltac:(solve_addr) ltac:(solve_addr) ltac:(done)
              Hcgp_loc ltac:(lia) Hws (or_introl eq_refl)
             with "Hpool Hact Hstatics Hwords Hsched Hpcc Hcgp Htr Hwp").
  Qed.
End stages.

Section adequacy.
  (* The context-switch thread and the user threads meet here: every form
     names its thread. *)
  #[local] Remove Hints ceriseG_of : typeclass_instances.

(** The template: a firmware whose trusted code meets its per-thread
    obligations, started from a state satisfying [firmware_ok] at the
    switcher's call of the scheduler, never sets the assert flag. *)
Theorem firmware_adequacy (Σ : gFunctors)
    {inv_preg : invGpreS Σ}
    {cerise_preg : ceriseGpreS Σ}
    {na_invg : na_invariants.na_invG Σ}
    {cur_preg : inG Σ curUR}
    {saved_preg : savedPropG Σ}
    {running_preg : ghost_varG Σ Thread}
    {window_preg : ghost_varG Σ bool}
    {Cname : CmptNameG}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG Σ}
    {cstack_preg : CSTACK_preG Σ}
    {relpreg : relGpreS Σ}
    `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  fw_obligations Σ fw →
  firmware_ok fw img σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! img_flag img = Some (WInt 0).
Proof.
  intros (Hlibs_ok & cthreads & C_sched & Hin & Hexcl & Hobl) Hok Hstep.
  pose proof Hok as (_ & _ & Hstart & Hwf).
  pose proof (img_wf_threads_nonempty _ _ Hwf) as Hne.
  destruct (img_wf_idle_boot _ _ Hwf) as [_ (_ & Hboot & _)].
  destruct (fw_sched_of (fw_cmpts fw)) as [ [fc sb] |] eqn:Hsched; last by rewrite /note in Hboot.
  destruct σ as [w_pc regs sregs m sh td].
  destruct (firmware_ok_ghost_init_cond _ _ _ _ _ _ _ _ Hlibs_ok Hok) as [Hinit Hnull].
  rewrite /start_ok /note in Hstart.
  destruct Hstart as (_ & Hcra & Hcgp & Hcsp & Hca0 & (z1 & z2 & z3 & Hca1 & Hca2 & Hca3) &
                      Hzero & Hmtdc & _ & (mpie & Hmstatus) & _).
  cbn [pcc reg sreg] in *.
  set (swl := fw_switcher_layout img).
  set (n := length (fw_threads fw)).
  set (vs := imap (λ i _, fw_start_vals fw img i) (fw_threads fw) ++
               [idle_start_vals (swlayout := swl)]).
  assert (length vs = S n) as Hlen_vs by rewrite /vs length_app length_imap /= Nat.add_1_r //.
  apply (cerise_flag_adequacy Σ (TV := fw_trap_vector img) (swlayout := swl)
           Nassert_flag (img_flag img) (fw_set (fw_heap_roots fw))
           (MkExecConf w_pc regs sregs m sh td) σ' vs es);
    [exact Hinit | exact Hnull | | exact Hmtdc | | by destruct (fw_threads fw) | | exact Hstep].
  - (* Every register has a value *)
    apply set_eq. intros r. split; intros _; last (apply elem_of_dom; cbn [reg]).
    + apply all_registers_s_correct.
    + destruct (decide (r ∈ ({[cra; cgp; csp; ca0; ca1; ca2; ca3]} : gset RegName))) as [Hr|Hr];
        last by rewrite Hzero.
      rewrite !elem_of_union !elem_of_singleton in Hr.
      destruct Hr as [ [ [ [ [ [-> | ->] | ->] | ->] | ->] | ->] | ->]; eauto.
  - by rewrite /mie_st /= Hmstatus /= mie_of_mstatus_enc.
  - intros ceriseb Htv Hhome_ctx Hus Hhomes.
    iIntros "HPC Hreg Hmtdc HMIE Hho Hlent Hna Hmem Hshadow Hclaims Hsusp Hexits Hsched".
    (* The seal store, the call stacks and the worlds *)
    iMod (initialise_world C_sched
            ({[ot_switcher (img_sw img); (ot_switcher (img_sw img) ^+ 1)%ot]} ∪
               list_to_set (fw_otypes fw))
            (sched_entry_frame img (cmpt_of img (fc_name fc)))
            (imap (λ i _, fw_entry_frame fw img i) (fw_threads fw) ++ [fw_entry_frame fw img n]))
      as (sealsg relg stsg cstackg)
        "(Hots & _ & Hcstk_ctx & Hcstks & Hworld_ctx & Hworlds & Hlocals)".
    { intros [_ Hnil]%app_eq_nil. done. }
    iMod (template_stage1 (cthreads := cthreads) fw img _ fc sb C_sched Hok Hsched Hin Htv Hhomes
            (Hobl img _ ceriseb sealsg stsg relg cstackg Hok)
           with "Hmem Hshadow Hclaims Hsusp Hexits Hsched Hots Hcstk_ctx Hcstks Hworld_ctx Hworlds
                 Hlocals")
      as "(Hslots & Hflag & Hres)".
    iModIntro. iFrame "Hslots Hflag".
    iIntros "Hpool Hact Htr".
    rewrite Hlen_vs.
    iApply (template_stage2 (cthreads := cthreads) fw img _ fc sb C_sched Hok Hsched Hin Hexcl
              Hhome_ctx Hus
             with "Hres HPC Hreg Hmtdc HMIE Hho Hlent Hna Hpool Hact Htr").
    intros t Ht. apply Hhomes. by rewrite Hlen_vs.
Qed.
End adequacy.

(** ** The ghost state of the template

    A case study with ghost state [Σcs] proves [fw_obligations] at
    [ #[firmwarePreΣ; Σcs] ] and concludes with [firmware_adequacy_closed]. *)
Definition curΣ : gFunctors := #[GFunctor curUR].
#[global] Instance subG_curΣ {Σ} : subG curΣ Σ → inG Σ curUR.
Proof. solve_inG. Qed.

Definition firmwarePreΣ {Cname : CmptNameG} : gFunctors :=
  #[invΣ; ceriseGpreΣ; CSTACK_preΣ; na_invΣ; sealStorePreΣ;
    STS_preΣ; relPreΣ;
    savedPredΣ (WorldT * CmptName * LWord);
    curΣ; savedPropΣ; ghost_varΣ Thread; ghost_varΣ bool].

Theorem firmware_adequacy_closed (Σcs : gFunctors) {Cname : CmptNameG}
    `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ σ' : ExecConf)
    (es : list (language.expr griotte_hw_lang)) :
  fw_obligations #[firmwarePreΣ; Σcs] fw →
  firmware_ok fw img σ →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! img_flag img = Some (WInt 0).
Proof.
  intros Hobl Hok Hstep.
  eapply (firmware_adequacy #[firmwarePreΣ; Σcs]); eauto; typeclasses eauto.
Qed.

(** ** The scheduler starts with no interrupt-enabling sentry *)

(** A word that is not a sentry enabling interrupts. *)
#[local] Definition no_enabling_sentry (w : Word) : Prop :=
  ∀ sk p g b e a, w = Sentry sk p g b e a → sentry_kind_mie sk ≠ Some InterruptEnabled.

#[local] Lemma no_enabling_sentry_int w : is_z w → no_enabling_sentry w.
Proof. intros Hz sk p g b e a ->. done. Qed.

#[local] Lemma no_enabling_sentry_handle `{MP : MachineParameters} fw img w :
  w ∈ thread_handles fw img → no_enabling_sentry w.
Proof.
  intros (j & _ & ->)%elem_of_thread_handles sk p g b e a.
  rewrite /thread_handle /note. by case_match.
Qed.

#[local] Lemma no_enabling_sentry_time_dev `{MP : MachineParameters} fw w :
  w ∈ sched_time_dev_words fw → no_enabling_sentry w.
Proof. by intros [-> | ->]%sched_time_dev_words_cases sk p g b e a. Qed.

(** A sanity check on the scheduler: no word it starts with (its imports,
    code and globals, its boot stack, the registers the switcher hands it)
    is a sentry that enables interrupts. *)
Lemma firmware_ok_sched_no_enabling `{MP : MachineParameters} fw img σ fc sb :
  firmware_ok fw img σ →
  fw_sched_of (fw_cmpts fw) = Some (fc, sb) →
  let s := cmpt_of img (fc_name fc) in
  Forall (λ w, ∀ sk p g b e a, w = Sentry sk p g b e a → sentry_kind_mie sk ≠ Some InterruptEnabled)
    (cmpt_imports s ++ cmpt_code s ++ cmpt_data s ++ img_boot_stack_words (img_boot img) ++
     [sched_pcc_word fw img; sched_cgp_word fw img; sched_csp_word img] ++
     [thread_handle fw img (fw_length (fw_threads fw))]).
Proof.
  intros Hok Hsched s. fold no_enabling_sentry.
  pose proof Hok as (Hcmpts_ok & _ & _ & Hwf).
  destruct (fw_sched_of_in _ _ _ Hsched) as [Hfc_in Hbody].
  apply big_and_fw_map in Hcmpts_ok. rewrite Forall_forall in Hcmpts_ok.
  destruct (cmpt_ok_inv _ _ _ (Hcmpts_ok fc Hfc_in)) as (_ & Himports & _ & Hbody_ok).
  rewrite Hbody /body_ok /note in Hbody_ok.
  destruct Hbody_ok as (Hcode & Hdata & _ & _ & Hboot).
  destruct (img_wf_sched_imports _ _ _ _ Hwf Hsched) as [Himps _].
  rewrite !Forall_app. split_and!.
  - rewrite /s Himports.
    destruct Himps as [-> | ->]; cbn [fw_imap fw_imap_from];
      repeat apply Forall_cons_2; try apply Forall_nil_2; intros sk p g b e a;
      rewrite /fw_word_of /note; intros Heq; first [done | injection Heq as <-; done].
  - eapply Forall_impl; first exact Hcode. intros w. apply no_enabling_sentry_int.
  - eapply Forall_impl; first exact Hdata.
    intros w [ [Hz | Hr] | Hw].
    + by apply no_enabling_sentry_int.
    + intros sk p g b e a ->. by cbn in Hr.
    + rewrite fw_app_eq elem_of_app in Hw.
      destruct Hw as [Hw | Hw];
        [by eapply no_enabling_sentry_handle | by eapply no_enabling_sentry_time_dev].
  - eapply Forall_impl; first exact Hboot.
    intros w [Hz | Hw]; [by apply no_enabling_sentry_int | by eapply no_enabling_sentry_handle].
  - repeat apply Forall_cons_2; try apply Forall_nil_2; intros sk p g b e a.
    + rewrite /sched_pcc_word Hsched /note. intros Heq. injection Heq as <-. done.
    + rewrite /sched_cgp_word Hsched /note. done.
    + rewrite /sched_csp_word /note. done.
  - apply Forall_singleton. eapply no_enabling_sentry_handle.
    rewrite /thread_handles fw_app_eq elem_of_app. right. by apply list_elem_of_singleton.
Qed.
