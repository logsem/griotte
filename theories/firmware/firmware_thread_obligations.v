From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import assert_spec.
From griotte Require Import world_interp_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common_obligations.
From griotte Require Import allocator_resources heap_region.
From griotte Require Import context_switch_layout_instance context_switching_support.
From griotte Require Import context_switching_hyps context_switching_scheduler_valid.
From griotte Require Import switcher_spec_return mkregion_helpers lib_static locks_spec.
From griotte Require Import libraries firmware_ok firmware_adequacy_obligations firmware_obligations.
(* Imported last: the fields of the image records shadow the fields of the
   layout records of [compartment_layout] and of [switcherLayout]. *)
From griotte Require Import image firmware.

(** * The save area of a thread at its entry *)

(** The registers that a save area of [save_area_content] resumes with:
    [cra], [csp], [cgp] its words 1–3, every other register zero. *)
#[local] Lemma resume_regs_of_save_area `{MP : MachineParameters} a b c d h m :
  resume_regs_of (lword_of_word <$> save_area_content a b c d h m) =
  <[cra := lword_of_word b]> (<[csp := lword_of_word c]> (<[cgp := lword_of_word d]> fw_cleared_regs)).
Proof.
  apply map_eq. intros r. rewrite resume_regs_of_lookup.
  pose proof (all_registers_correct r) as Hr. unfold all_registers in Hr.
  repeat (apply elem_of_cons in Hr as [-> | Hr];
          [first [reflexivity | vm_compute; reflexivity] |]).
  by apply elem_of_nil in Hr.
Qed.

(** A save area of [save_area_content] whose PC word is a legal PC, with
    MIE disabled, MPIE [mpie] and [mcause] 0, resumes with its words. *)
#[local] Lemma save_area_resume_ok `{MP : MachineParameters}
    (wpc w_cra w_csp w_cgp w_hz : Word) (mpie : InterruptStatus) :
  pc_ok wpc →
  saved_mie_ok
    (lword_of_word <$>
       save_area_content wpc w_cra w_csp w_cgp w_hz (WInt (mstatus_enc InterruptDisabled mpie))) ∧
  resume_ok_full
    (lword_of_word <$>
       save_area_content wpc w_cra w_csp w_cgp w_hz (WInt (mstatus_enc InterruptDisabled mpie)))
    {| rv_regs := <[cra := lword_of_word w_cra]>
                    (<[csp := lword_of_word w_csp]> (<[cgp := lword_of_word w_cgp]> fw_cleared_regs));
       rv_pc := lword_of_word wpc;
       rv_mie := mpie |}.
Proof.
  intros Hpc. split; [|split; [|split] ].
  - intros w Hw. rewrite save_area_lookup_mstatus in Hw. injection Hw as <-.
    exact (mie_of_mstatus_enc InterruptDisabled mpie).
  - cbn [rv_regs]. by rewrite resume_regs_of_save_area.
  - cbn [rv_mie]. rewrite save_area_word_mstatus.
    exact (eq_sym (mpie_of_mstatus_enc InterruptDisabled mpie)).
  - cbn [rv_pc]. split.
    + rewrite /resume_pc_word save_area_word_mepcc save_area_word_mcause.
      case_decide as Hc; first (vm_compute in Hc; discriminate Hc).
      cbv beta iota zeta. symmetry. apply legalise_pc_ok_id. exact Hpc.
    + intros _. reflexivity.
Qed.

Section save_area.
  Context `{MP : MachineParameters}.

  (** The save area of the firmware thread [i], as the loader writes it. *)
  Definition fw_save_area (fw : firmware) (img : fw_image) (i : nat) : list LWord :=
    let t := thread_of img i in
    lword_of_word <$>
      save_area_content (fw_entry_pc fw img i) (fw_thread_cra img) (fw_thread_csp img i)
        (fw_entry_cgp fw img i) (Cap WO Global (b_hazard t) (e_hazard t) (b_hazard t))
        (WInt (mstatus_enc InterruptDisabled (fw_entry_posture fw img i))).

  (** The start values of the firmware thread [i]: the values of
      [fw_thread_res]. *)
  Definition fw_start_vals (fw : firmware) (img : fw_image) (i : nat) : resume_vals :=
    {| rv_regs := <[cra := lword_of_word (fw_thread_cra img)]>
                    (<[csp := lword_of_word (fw_thread_csp img i)]>
                       (<[cgp := lword_of_word (fw_entry_cgp fw img i)]> fw_cleared_regs));
       rv_pc := lword_of_word (fw_entry_pc fw img i);
       rv_mie := fw_entry_posture fw img i |}.

  Lemma fw_save_area_resume_ok fw img i :
    saved_mie_ok (fw_save_area fw img i) ∧
    resume_ok_full (fw_save_area fw img i) (fw_start_vals fw img i).
  Proof.
    rewrite /fw_save_area /fw_start_vals.
    apply save_area_resume_ok. rewrite /fw_entry_pc. done.
  Qed.

  (** The trusted entry of a thread is the one of its start: [img_wf]
      rules out an unknown export of an untrusted compartment and an entry
      in the scheduler. *)
  #[local] Lemma thread_entry_eq fw img i ft :
    img_wf fw img →
    fw_threads fw !! i = Some ft →
    thread_entry fw img ft = (fw_entry_pc fw img i, fw_entry_posture fw img i).
  Proof.
    intros Hwf Hi.
    pose proof (fw_thread_of_lookup fw i ft Hi) as Hft.
    destruct Hwf as (_ & _ & _ & Hthreads & _).
    pose proof (big_and_fw_imap_lookup _ _ _ _ Hthreads Hi) as Hthread.
    rewrite /thread_wf /section /note in Hthread.
    rewrite /thread_entry /fw_entry_pc /fw_entry_posture /fw_entry_offset /fw_entry_word
      /fw_entry_fc /fw_entry_cmpt Hft.
    destruct (fc_body (fw_cmpt_of (fw_cmpts fw) (ft_cmpt ft))) as [tb|ub|sb].
    - reflexivity.
    - destruct (fw_index_of ue_name (ft_entry ft) (ub_exports ub)) as [k|];
        last (exfalso; exact Hthread).
      rewrite /img_entry_word. reflexivity.
    - exfalso. exact Hthread.
  Qed.

  (** The first words of the trusted stack of the thread [i] are its save
      area as checked by [fw_save_area_resume_ok]. *)
  Lemma fw_tstack_content_save_area fw img i ft :
    img_wf fw img →
    fw_threads fw !! i = Some ft →
    lword_of_word <$> take (Z.to_nat TrustedStack_offset_frameoffset) (fw_tstack_content fw img i ft)
      = fw_save_area fw img i.
  Proof.
    intros Hwf Hi.
    rewrite /fw_tstack_content (thread_entry_eq fw img i ft Hwf Hi).
    rewrite /initial_trusted_stack_content take_app_length'; last first.
    { by rewrite length_save_area_content. }
    rewrite /fw_save_area /fw_entry_cgp /fw_entry_cmpt (fw_thread_of_lookup fw i ft Hi).
    reflexivity.
  Qed.
End save_area.

(** The allocation of the world of the scheduler's compartment: its code
    and globals Permanent, its imports Permanent with the safety the caller
    proves. The globals are initial globals or words of [hs], valid and
    not Local in every world. *)
Section sched_world_alloc.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads}
    `{MP : MachineParameters}
    {swlayout : switcherLayout}.

  (** An initial global of [C_cmpt] is valid and not Local, from the
      Permanent regions of the globals. *)
  #[local] Lemma initial_data_word_nonlocal (C_cmpt : cmpt) (C : CmptName) (w : Word) :
    is_initial_data_word C_cmpt w →
    ([∗ list] k ∈ finz.seq_between (compartment_layout.cmpt_b_cgp C_cmpt) (compartment_layout.cmpt_e_cgp C_cmpt),
       LNonHeap k ↪ᵖ[C]{RW} safeGC interp_nonlocal) -∗
    interp_nonlocal ∅ C (lword_of_word w).
  Proof.
    pose proof (cmpt_cgp_disjoint_from_mmio C_cmpt) as Hcgp_shadow.
    pose proof (cmpt_cgp_disjoint_from_heap C_cmpt) as Hcgp_heap.
    intros Hw. iIntros "#Hrels".
    destruct w as [z | [tag p g b e a | tag p g b e a] | k tag p g b e a | ot sb];
      cbn in Hw; destruct Hw as [Hw|Hw]; cbn in Hw; try done
    ; [|destruct g ; last done].
    - iApply interp_nonlocal_int.
    - rewrite /interp_nonlocal /=. iSplit; first by destruct tag.
      destruct tag; last (iApply interp_untagged; done).
      rewrite interp_unfold interp1_eq.
      destruct Hw as (Hp & Hb & He).
      destruct (isO p) eqn:HpO.
      { assert (Hsub : finz.seq_between b e ⊆
            finz.seq_between (compartment_layout.cmpt_b_cgp C_cmpt) (compartment_layout.cmpt_e_cgp C_cmpt)).
        { intros x Hx. apply elem_of_finz_seq_between in Hx.
          apply elem_of_finz_seq_between. solve_addr. }
        assert (Hdisjoint : disjoint_from_heap b e).
        { rewrite /disjoint_from_heap in Hcgp_heap |- *.
          set_solver+Hsub Hcgp_heap. }
        iSplit; first by iApply heap_cap_ok_disjoint.
        iApply big_sepL_intro. iIntros "!>" (i x Hx%list_elem_of_lookup_2 Hheap).
        rewrite /disjoint_from_heap elem_of_disjoint in Hdisjoint.
        exfalso. eapply Hdisjoint; first exact Hx.
        apply withinBounds_true_iff in Hheap.
        apply elem_of_finz_seq_between. solve_addr. }
      destruct (has_sreg_access p) eqn:HpXSR.
      { destruct p as [ [] w dl dro ]; cbn in *; done. }
      assert (isWL p = false) as Hwl.
      { destruct p as [ rx [] dl dro ]; cbn in *; auto.
        rewrite !andb_True in Hp.
        destruct Hp as [ [ [] ] ]; done. }
      rewrite Hwl. iLeft.
      iSplitR; cycle 1.
      { assert (finz.seq_between b e ⊆
          finz.seq_between (compartment_layout.cmpt_b_cgp C_cmpt) (compartment_layout.cmpt_e_cgp C_cmpt)) as Hbounds.
        { intros a' Ha'. apply elem_of_finz_seq_between in Ha'.
          apply elem_of_finz_seq_between; solve_addr. }
        iSplit.
        - iPureIntro. split; first done.
          eapply disjoint_from_mmio_weaken; [| | exact Hcgp_shadow]; solve_addr.
        - iApply heap_cap_ok_disjoint.
          rewrite /disjoint_from_heap in Hcgp_heap |- *.
          set_solver+Hbounds Hcgp_heap. }
      iApply big_sepL_intro; iModIntro.
      iIntros (k a' Ha').
      apply list_elem_of_lookup_2, elem_of_finz_seq_between in Ha'.
      assert (a' ∈ₐ [(compartment_layout.cmpt_b_cgp C_cmpt), (compartment_layout.cmpt_e_cgp C_cmpt))) as Ha'' by solve_addr.
      apply elem_of_finz_seq_between in Ha''.
      rewrite /addr_key.
      iDestruct (big_sepL_elem_of with "Hrels") as "Hrel_a'"; eauto.
      iExists RW, interp_nonlocal; cbn.
      iSplit; first done.
      iSplit; first (iPureIntro; apply persistent_cond_interp_nonlocal).
      iSplit; first by rewrite /region_rel Hwl.
      iSplit; first iApply zcond_interp_nonlocal.
      iSplit; first by iApply rcond_g_interp_nonlocal.
      iApply wcond_nwl_interp_nonlocal.
  Qed.

  (** The world of the compartment [C_cmpt] owned by [C], with its code and
      globals Permanent, and its imports Permanent at the safety the caller
      gives: its PCC and CGP are valid. *)
  Lemma initialise_scheduler_world {E : coPset} (W : WORLD) (C_cmpt : cmpt) (C : CmptName)
      (hs : list Word) :
    let imports_addrs := finz.seq_between (compartment_layout.cmpt_b_pcc C_cmpt) (compartment_layout.cmpt_a_code C_cmpt) in
    let code_addrs := finz.seq_between (compartment_layout.cmpt_a_code C_cmpt) (compartment_layout.cmpt_e_pcc C_cmpt) in
    let data_addrs := finz.seq_between (compartment_layout.cmpt_b_cgp C_cmpt) (compartment_layout.cmpt_e_cgp C_cmpt) in
    Forall is_z (compartment_layout.cmpt_code C_cmpt) →
    Forall (λ w, is_initial_data_word C_cmpt w ∨ w ∈ hs) (compartment_layout.cmpt_data C_cmpt) →
    ([∗ list] h ∈ hs, interp_nonlocal ∅ C (lword_of_word h)) -∗
    ([∗ list] v ∈ lword_of_word <$> compartment_layout.cmpt_imports C_cmpt, safeGC interp_cmpt_threads (C, v)) -∗
    ([∗ list] k;v ∈ imports_addrs ; lword_of_word <$> compartment_layout.cmpt_imports C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ code_addrs ; lword_of_word <$> compartment_layout.cmpt_code C_cmpt, k ↦ₐ v) -∗
    ([∗ list] k;v ∈ data_addrs ; lword_of_word <$> compartment_layout.cmpt_data C_cmpt, k ↦ₐ v) -∗
    world_interp W C
    ={E}=∗
    world_interp W C ∗
    interp W C (Cap RX Global (compartment_layout.cmpt_b_pcc C_cmpt) (compartment_layout.cmpt_e_pcc C_cmpt) (compartment_layout.cmpt_b_pcc C_cmpt)) ∗
    interp W C (Cap RW Global (compartment_layout.cmpt_b_cgp C_cmpt) (compartment_layout.cmpt_e_cgp C_cmpt) (compartment_layout.cmpt_b_cgp C_cmpt)).
  Proof.
    intros imports_addrs code_addrs data_addrs Hcode Hdata.
    iIntros "#Hhs #Himports HC_imports HC_code HC_data Hworld".
    iMod (world_interp_extend_perm_sepL2 W C
            code_addrs (lword_of_word <$> compartment_layout.cmpt_code C_cmpt)
            RX (safeGC interp_cmpt_threads)
           with "Hworld [HC_code]") as "(Hworld & #HC_code)".
    { rewrite !big_sepL2_fmap_r.
      iApply (big_sepL2_mono with "HC_code").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros "Hv".
      pose proof (Forall_lookup_1 _ _ _ _ Hcode Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      rewrite /PermRes key_pointsto_nonheap.
      iFrame "Hv".
      iSplit; first done.
      iApply bi.later_intro. iApply interp_cmpt_threads_int. }
    iMod (world_interp_extend_perm_sepL2_open W C
            data_addrs (lword_of_word <$> compartment_layout.cmpt_data C_cmpt)
            RW (safeGC interp_nonlocal)
           with "Hworld HC_data []") as "(Hworld & #HC_data & _)".
    { apply finz_seq_between_NoDup. }
    { done. }
    { iIntros "#Hrels".
      rewrite big_sepL_fmap.
      iApply big_sepL_intro. iIntros "!>" (k w Hk).
      apply list_lookup_fmap_Some in Hk as (w' & -> & Hk).
      destruct (Forall_lookup_1 _ _ _ _ Hdata Hk) as [Hw | Hw].
      - by iApply (initial_data_word_nonlocal with "Hrels").
      - by iApply (big_sepL_elem_of with "Hhs"). }
    iMod (world_interp_extend_perm_sepL2_open W C
            imports_addrs (lword_of_word <$> compartment_layout.cmpt_imports C_cmpt)
            RX (safeGC interp_cmpt_threads)
           with "Hworld HC_imports []") as "(Hworld & #HC_imports & _)".
    { apply finz_seq_between_NoDup. }
    { done. }
    { iIntros "_". iExact "Himports". }
    iDestruct (big_sepL_app _ imports_addrs code_addrs with "[$HC_imports $HC_code]") as "HC_PCC".
    iDestruct (cmpt_caps_interp W C_cmpt C with "HC_PCC HC_data") as "[#Hpcc #Hcgp]".
    iModIntro. iFrame "Hworld Hpcc Hcgp".
  Qed.
End sched_world_alloc.

Section sched_world.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The switcher's call sentry is safe to import in the scheduler's
      compartment [C_sched]: its only thread is the context-switch thread,
      at which the call faults. *)
  Lemma fw_switcher_call_safe_ctx fw img σ c (C_sched : CmptName) :
    let swl := fw_switcher_layout img in
    firmware_ok fw img σ →
    CtxSwitch ∈ cmpt_threads C_sched →
    switcher_code_at CtxSwitch -∗
    ctx_trap_vector_safe (swlayout := swl) -∗
    fw_import_safe (swlayout := swl) C_sched (fw_word_of fw img [] c ISwitcherCall).
  Proof.
    intros swl Hok Hin.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    iIntros "#Hcode #Htrap".
    rewrite /fw_import_safe /fw_word_of /note.
    iEval (cbn [fst snd]; rewrite /interp_cmpt_threads /=).
    iIntros "!>" (t') "Ht'". iDestruct (thread_in_elim with "Ht'") as %Ht'.
    destruct t' as [k|].
    - exfalso. exact (cmpt_threads_sep C_sched k Ht' Hin).
    - iApply (interp_switcher_call_ctx (swlayout := swl) with "[$Hcode $Htrap]").
  Qed.

  (** The handle of the user thread [j], or of the idle thread when [j] is
      the number of threads, is valid at the context-switch thread. *)
  Lemma thread_handle_valid fw img σ j W C :
    let swl := fw_switcher_layout img in
    firmware_ok fw img σ →
    j ≤ length (fw_threads fw) →
    switcher_static (th := UserThread j) (swlayout := swl) -∗
    interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
      (CR := crit_route_full (swlayout := swl)) W C (lword_of_word (thread_handle fw img j)).
  Proof.
    intros swl Hok Hj.
    pose proof Hok as (_ & _ & _ & Hwf).
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    pose proof (img_wf_threads_length _ _ Hwf) as Hlen.
    pose proof (img_wf_threads_nonempty _ _ Hwf) as Hne.
    iIntros "#Hstatic".
    iPoseProof (tstack_handle_sealed_valid (swlayout := swl) W C Global j with "Hstatic") as "Hv".
    { change (j < S (length (img_threads img))). lia. }
    rewrite /thread_handle fw_length_eq /note.
    destruct (Nat.eqb_spec j (length (fw_threads fw))) as [-> | Hneq].
    - rewrite -Hlen fw_tlayout_idle;
        last (rewrite Hlen; destruct (fw_threads fw); [done | cbn [length]; lia]).
      iExact "Hv".
    - rewrite fw_tlayout_lt; last lia.
      iExact "Hv".
  Qed.

  (** The time-device capabilities that the scheduler imports. *)
  Lemma sched_time_dev_words_cases fw w :
    w ∈ sched_time_dev_words fw →
    w = time_dev_cap mtime_addr ∨ w = time_dev_cap mtimecmp_addr.
  Proof.
    rewrite /sched_time_dev_words.
    destruct (fw_sched_of (fw_cmpts fw)) as [ [fc sb] |]; last by intros Hw%elem_of_nil.
    induction (fc_imports fc) as [|x xs IH]; cbn [fw_flat_map]; first by intros Hw%elem_of_nil.
    rewrite fw_app_eq elem_of_app. intros [Hx | Hx]; last by apply IH.
    destruct x; try by apply elem_of_nil in Hx.
    all: apply list_elem_of_singleton in Hx; auto.
  Qed.

  (** A time-device capability is valid at the context-switch thread: it
      reaches only an exposed device. *)
  #[local] Lemma time_dev_cap_valid swl W C a :
    a = mtime_addr ∨ a = mtimecmp_addr →
    ⊢ interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
        (CR := crit_route_full (swlayout := swl)) W C (lword_of_word (time_dev_cap a)).
  Proof.
    intros Ha. rewrite /time_dev_cap.
    iApply (interp_exposed_mmio_cap (th := CtxSwitch)); [done | done |].
    split_and!; [done | done | done |].
    apply Forall_forall. intros x Hx%elem_of_finz_seq_between.
    assert (x = a) as -> by solve_addr.
    rewrite /is_exposed_mmio_address.
    by rewrite (proj2 (is_time_device_address_spec a) Ha).
  Qed.

  (** The words other than initial globals that the scheduler's globals
      may hold, the thread handles and the imported time-device
      capabilities, are valid and not Local at the context-switch thread,
      in every world. *)
  #[local] Lemma sched_hs_valid fw img σ W C w :
    let swl := fw_switcher_layout img in
    firmware_ok fw img σ →
    w ∈ fw_app (thread_handles fw img) (sched_time_dev_words fw) →
    ([∗ list] t ∈ seq 0 (S (length (fw_threads fw))),
       switcher_static (th := UserThread t) (swlayout := swl)) -∗
    interp_nonlocal (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
      (CR := crit_route_full (swlayout := swl)) W C (lword_of_word w).
  Proof.
    intros swl Hok Hw. iIntros "#Hstatics".
    rewrite fw_app_eq elem_of_app in Hw.
    iEval (rewrite /interp_nonlocal /=).
    destruct Hw as [Hw | Hw].
    - destruct (elem_of_thread_handles _ _ _ Hw) as (j & Hj & ->).
      iSplit.
      + rewrite /thread_handle /note. by case_match.
      + iApply (thread_handle_valid with "[]"); [exact Hok | exact Hj |].
        iApply (big_sepL_elem_of with "Hstatics"). apply elem_of_seq. lia.
    - iSplit; first by destruct (sched_time_dev_words_cases _ _ Hw) as [-> | ->].
      destruct (sched_time_dev_words_cases _ _ Hw) as [-> | ->];
        iApply time_dev_cap_valid; auto.
  Qed.

  (** The scheduler's imports, written by the firmware: the switcher call,
      and the two time devices or neither; no static sealed object. *)
  Lemma img_wf_sched_imports fw img fc sb :
    img_wf fw img →
    fw_sched_of (fw_cmpts fw) = Some (fc, sb) →
    (fc_imports fc = [ISwitcherCall] ∨ fc_imports fc = [ISwitcherCall; IMtime; IMtimecmp]) ∧
    fc_static_sealed fc = [].
  Proof.
    intros (_ & _ & _ & _ & Himg) Hsched.
    rewrite /section in Himg. do 6 apply big_and_fw_app in Himg as [_ Himg].
    apply big_and_fw_app in Himg as [Himg _].
    rewrite Hsched in Himg.
    destruct (Nat.eqb (fw_sched_count (fw_cmpts fw)) 1); last done.
    revert Himg. generalize (fc_imports fc) (fc_static_sealed fc).
    intros imps ss. repeat case_match; simplify_eq; try done; auto.
  Qed.

  (** The world of the scheduler's compartment [fc] at the context-switch
      thread, owned by [C_sched]: its imports, code and globals become
      permanent, the boot stack temporary. Its PCC, its globals and its
      stack are then valid in that world. *)
  Lemma fw_close_sched_world {E : coPset} fw img σ fc sb (C_sched : CmptName) :
    let swl := fw_switcher_layout img in
    let s := cmpt_of img (fc_name fc) in
    let bs := img_boot img in
    let W_init := std_update_multiple fw_world0
                    (finz.seq_between (img_b_boot_stack bs) (img_e_boot_stack bs)) Temporary in
    firmware_ok fw img σ →
    fw_sched_of (fw_cmpts fw) = Some (fc, sb) →
    CtxSwitch ∈ cmpt_threads C_sched →
    switcher_code_at CtxSwitch -∗
    ctx_trap_vector_safe (swlayout := swl) -∗
    ([∗ list] t ∈ seq 0 (S (length (fw_threads fw))),
       switcher_static (th := UserThread t) (swlayout := swl)) -∗
    fw_cmpt_mem_res (th := UserThread 0) s -∗
    region_pointsto (ceriseg := ceriseG_of CtxSwitch) (img_b_boot_stack bs) (img_e_boot_stack bs)
      (lword_of_word <$> img_boot_stack_words bs) -∗
    world_interp (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch) fw_world0 C_sched
    ={E}=∗
    world_interp (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch) W_init C_sched ∗
    interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl)) (CR := crit_route_full (swlayout := swl))
      W_init C_sched (lword_of_word (Cap RX Global (cmpt_b_pcc s) (cmpt_e_pcc s) (cmpt_b_pcc s))) ∗
    interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl)) (CR := crit_route_full (swlayout := swl))
      W_init C_sched (lword_of_word (sched_cgp_word fw img)) ∗
    interp (th := CtxSwitch) (CL := crit_link_full (swlayout := swl)) (CR := crit_route_full (swlayout := swl))
      W_init C_sched (lword_of_word (sched_csp_word img)).
  Proof.
    intros swl s bs W_init Hok Hsched Hin.
    pose proof Hok as (Hcmpts_ok & _ & _ & Hwf).
    destruct (fw_sched_of_in _ _ _ Hsched) as [Hfc_in Hbody].
    pose proof (img_wf_cmpt_layout _ _ _ Hwf Hfc_in) as Hc.
    apply big_and_fw_map in Hcmpts_ok. rewrite Forall_forall in Hcmpts_ok.
    pose proof (Hcmpts_ok fc Hfc_in) as Hfc_ok.
    destruct (cmpt_ok_inv _ _ _ Hfc_ok) as (_ & _ & _ & Hbody_ok).
    rewrite Hbody in Hbody_ok.
    destruct Hbody_ok as (Hcode & Hdata & _ & _ & Hboot).
    destruct (img_wf_idle_boot _ _ Hwf) as [_ (_ & _ & Hrange)].
    destruct (img_wf_sched_imports _ _ _ _ Hwf Hsched) as [Himps Hss].
    iIntros "#Hswitcher #Htrap #Hstatics (Himports & Hcode_mem & Hdata_mem) Hboot Hworld".
    (* The boot stack, Temporary *)
    iMod (world_interp_extend_temp_sepL2 (th := CtxSwitch) fw_world0 C_sched
            (finz.seq_between (img_b_boot_stack bs) (img_e_boot_stack bs))
            (lword_of_word <$> img_boot_stack_words bs) RWL
            (safeC (interp_in_mem (th := CtxSwitch) (CL := crit_link_full (swlayout := swl))
                      (CR := crit_route_full (swlayout := swl)) RWL))
           with "Hworld [Hboot]") as "(Hworld & #Hrel_stk)".
    { done. }
    { apply Forall_forall. intros a _. rewrite /fw_world0 /=. by rewrite lookup_empty. }
    { rewrite big_sepL2_fmap_r.
      iEval (rewrite /region_pointsto big_sepL2_fmap_r) in "Hboot".
      iApply (big_sepL2_impl with "Hboot").
      iIntros "!>" (k a w Ha Hw) "Hv". rewrite /TmpRes key_pointsto_nonheap.
      iFrame "Hv". iSplit; first done.
      iSplit; last (iApply bi.later_intro; iApply mono_pub_interp_in_mem).
      iNext. iApply interp_to_in_mem.
      destruct (Forall_lookup_1 _ _ _ _ Hboot Hw) as [Hz | Hh].
      - destruct w; try done. iApply interp_int.
      - iDestruct (sched_hs_valid fw img σ fw_world0 C_sched w with "Hstatics") as "[_ $]";
          first exact Hok.
        rewrite fw_app_eq elem_of_app. by left. }
    (* The compartment, Permanent *)
    iMod (initialise_scheduler_world (th := CtxSwitch) (swlayout := swl) W_init
            (layout_cmpt_of s Hc) C_sched (fw_app (thread_handles fw img) (sched_time_dev_words fw))
           with "[] [] [Himports] [Hcode_mem] [Hdata_mem] Hworld") as "(Hworld & Hpcc & Hcgp)".
    { exact Hcode. }
    { exact Hdata. }
    { iApply big_sepL_intro. iIntros "!>" (k w Hw%list_elem_of_lookup_2).
      by iApply (sched_hs_valid with "Hstatics"). }
    { iApply fw_imports_safe_words; first exact Hfc_ok.
      rewrite Hss.
      destruct Himps as [Himps_eq | Himps_eq]; rewrite Himps_eq !big_sepL_cons.
      - iSplit; last done. by iApply (fw_switcher_call_safe_ctx with "Hswitcher Htrap").
      - iSplit; first by iApply (fw_switcher_call_safe_ctx with "Hswitcher Htrap").
        iSplit; first by iApply fw_time_dev_import_safe; left.
        iSplit; last done. by iApply fw_time_dev_import_safe; right. }
    { iExact "Himports". }
    { iExact "Hcode_mem". }
    { iExact "Hdata_mem". }
    iModIntro. iFrame "Hworld Hpcc".
    iSplit.
    - rewrite /sched_cgp_word Hsched /note. iExact "Hcgp".
    - rewrite /sched_csp_word /note.
      iApply (interp_weakening_same_bounds_same_loc W_init C_sched true RWL RWL Local _ _
                (stk_start_a (img_b_boot_stack bs) (img_e_boot_stack bs)) with "[]");
        [done | done | done |].
      iApply interp_stack_temporary.
      + exact (range_ok_mmio _ _ Hrange).
      + exact (proj2 (range_ok_not_heap _ _ Hrange)).
      + apply Forall_forall. intros a Ha. by apply std_sta_update_multiple_lookup_in_i.
      + iExact "Hrel_stk".
  Qed.
End sched_world.

Section cmpt_res_user.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** A compartment other than the scheduler, initialised; the scheduler's
      resources are the template's. *)
  Definition fw_cmpt_res_user (img : fw_image) (fc : fw_cmpt) : iProp Σ :=
    match fc_body fc with
    | SchedulerBody _ => emp
    | _ => fw_cmpt_res img fc
    end.
End cmpt_res_user.

Section resources_pt.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The resources shared by the threads of a firmware whose scheduler runs
      in [C_sched]: the switcher's static facts and the trusted-stack
      invariant of every thread, the libraries (their import tables and
      code, persistent), the shared objects but the assert flag (which the
      template keeps), the compartments but the scheduler's, initialised,
      the sealing types, the maps of Permanent regions of the compartments
      but [C_sched], and the heap. Each thread's local maps are in its
      [fw_thread_res]. *)
  Definition fw_shared_res (fw : firmware) (img : fw_image) (C_sched : CmptName) : iProp Σ :=
    "Hswitcher_static" ∷
      ([∗ list] i ↦ _ ∈ fw_threads fw,
         switcher_static (th := UserThread i) (swlayout := fw_switcher_layout img)) ∗
    "Hswitcher_tstacks" ∷
      ([∗ list] i ↦ _ ∈ fw_threads fw,
         na_inv (tpool (UserThread i)) Ntstack
           (trusted_stack_inv (th := UserThread i) (swlayout := fw_switcher_layout img))) ∗
    "Hlibs" ∷
      ([∗ list] l ∈ fw_libs fw, [∗ map] a↦w ∈ lib_mem fw img l, a ↦ₐ□ lword_of_word w) ∗
    "Hshared" ∷
      ([∗ list] o ∈ fw_shared fw,
         if String.eqb (so_name o) "assert_flag" then emp
         else [∗ map] a↦w ∈ shared_mem img o, a ↦ₐ lword_of_word w) ∗
    "Hcmpts" ∷ ([∗ list] fc ∈ fw_cmpts fw, fw_cmpt_res_user (th := UserThread 0) img fc) ∗
    "Hotypes" ∷ ([∗ list] o ∈ fw_otypes fw, can_alloc_pred o) ∗
    "Hworlds" ∷
      ([∗ set] C ∈ CNames ∖ {[C_sched]},
         perm_region_map (allocg := @cerise_registryG Σ (ceriseG_of (UserThread 0)))
           (memg := @mem_gen_memG Σ (ceriseG_of (UserThread 0))) C ∅) ∗
    "Hheap" ∷ ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) ∗
    "Hshadow" ∷ ([∗ map] a↦s ∈ initial_heap_shadow, a ↦ₛ s) ∗
    "Hclaims" ∷ ([∗ map] a↦c ∈ init_claims (fw_set (fw_heap_roots fw)), addr_alloc a c).
End resources_pt.

(** The obligations of the trusted code of a firmware, per thread, for the
    ghost state [Σ]: its libraries are integer code with imports of the
    switcher, of library exports and of shared objects ([fw_lib_ok]); for
    some assignment [cthreads] of threads to the
    compartments and some compartment [C_sched] of the context-switch
    thread, in exclusive mode, for every image and initial state satisfying
    [firmware_ok], the shared resources give, after an update, for each
    thread [i] of the firmware, its safe run from its resources and a later
    credit. *)
Definition fw_obligations (Σ : gFunctors) {Cname : CmptNameG} `{MP : MachineParameters}
    (fw : firmware) : Prop :=
  Forall fw_lib_ok (fw_libs fw) ∧
  ∃ (cthreads : CmptThreads) (C_sched : CmptName),
  CtxSwitch ∈ cmpt_threads C_sched ∧
  cmpt_shared C_sched = false ∧
  ∀ (img : fw_image) (σ : ExecConf)
    (ceriseb : ceriseBaseG Σ) (sealsg : sealStoreG Σ)
    (stsg : STSG Σ) (relg : relGS Σ)
    (cstackg : CSTACKG Σ),
    firmware_ok fw img σ →
    ⊢ fw_shared_res fw img C_sched
      ={⊤}=∗
      [∗ list] i ↦ _ ∈ fw_threads fw,
        (fw_thread_res fw img i -∗
         £ 1
         ={⊤}=∗
         let _ : switcherLayout := fw_switcher_layout img in safe[u i]).

(** The static part of a library of a firmware, from its memory, at any
    thread. *)
Lemma fw_lib_static {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ : ExecConf) (th : Thread) (l : fw_lib) :
  firmware_ok fw img σ →
  l ∈ fw_libs fw →
  ([∗ map] a↦w ∈ lib_mem fw img l, a ↦ₐ□ lword_of_word w) -∗
  lib_static (ceriseg := ceriseG_of th)
    (lib_b (lib_of img (fl_name l))) (lib_e (lib_of img (fl_name l)))
    (fw_map (fw_word_of fw img [] default_img_cmpt) (fl_imports l)) (fl_code l).
Proof.
  iIntros (Hok Hin) "Hl".
  pose proof Hok as (_ & _ & _ & Hwf).
  destruct (img_wf_lib_inv _ _ _ Hwf Hin) as (Hsize & _ & Hheap & _).
  rewrite -(length_fmap (fw_word_of fw img [] default_img_cmpt)) -fw_map_eq in Hsize.
  assert ((lib_b (lib_of img (fl_name l)) +
             length (fw_app (fw_word_of fw img [] default_img_cmpt ISwitcherCall ::
                             fw_map (fw_word_of fw img [] default_img_cmpt) (fl_imports l))
                       (fl_code l)))%a = Some (lib_e (lib_of img (fl_name l)))) as Hsize'.
  { rewrite fw_app_eq length_app /=. solve_addr+Hsize. }
  rewrite /lib_mem /note (mem_region_mkregion _ _ _ Hsize').
  iDestruct (mkregion_sepM_to_sepL2 with "Hl") as "Hl"; first exact Hsize'.
  iApply (lib_static_of_region _ _ (fw_word_of fw img [] default_img_cmpt ISwitcherCall)
            with "[Hl]"); [done | done |].
  rewrite /region_pointsto_pers big_sepL2_fmap_r fw_app_eq. iExact "Hl".
Qed.

(** The static part of the assert library, from the libraries of a firmware
    that has it, at any thread. *)
Lemma fw_assert_static {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ : ExecConf) (th : Thread) :
  firmware_ok fw img σ →
  assert_lib ∈ fw_libs fw →
  ([∗ list] l ∈ fw_libs fw, [∗ map] a↦w ∈ lib_mem fw img l, a ↦ₐ□ lword_of_word w) -∗
  assert_static (ceriseg := ceriseG_of th)
    (lib_b (lib_of img "assert")) (lib_e (lib_of img "assert")) (img_flag img).
Proof.
  iIntros (Hok Hin) "Hlibs".
  pose proof Hok as (_ & _ & _ & Hwf).
  destruct (img_wf_flag_layout _ _ Hwf) as [Hflag _].
  iDestruct (big_sepL_elem_of with "Hlibs") as "Hl"; first exact Hin.
  iDestruct (fw_lib_static _ _ _ th _ Hok Hin with "Hl") as "Hl".
  assert (sh_e (shared_of img "assert_flag") = (img_flag img ^+ 1)%a) as Hflag_e
    by solve_addr+Hflag.
  rewrite /assert_static /fw_map /fw_word_of /note /= Hflag_e.
  iSplit; first (iPureIntro; by eexists).
  iExact "Hl".
Qed.

(** The static part of the lock library, from the libraries of a firmware
    that has it, at any thread. *)
Lemma fw_lock_static {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ : ExecConf) (th : Thread) :
  firmware_ok fw img σ →
  try_lock_lib ∈ fw_libs fw →
  ([∗ list] l ∈ fw_libs fw, [∗ map] a↦w ∈ lib_mem fw img l, a ↦ₐ□ lword_of_word w) -∗
  lock_static (th := th) (LK := fw_locks_layout img).
Proof.
  iIntros (Hok Hin) "Hlibs".
  iDestruct (big_sepL_elem_of with "Hlibs") as "Hl"; first exact Hin.
  iDestruct (fw_lib_static _ _ _ th _ Hok Hin with "Hl") as "Hl".
  rewrite /lock_static. iExact "Hl".
Qed.

(** The libraries of the case studies are integer code with imports of
    shared objects only. *)
Lemma assert_lib_ok `{MP : MachineParameters} : fw_lib_ok assert_lib.
Proof.
  split.
  - apply Forall_fmap, Forall_true. by intros i.
  - by repeat constructor.
Qed.

Lemma try_lock_lib_ok `{MP : MachineParameters} : fw_lib_ok try_lock_lib.
Proof.
  split.
  - apply Forall_fmap, Forall_true. by intros i.
  - by repeat constructor.
Qed.

(** A compartment whose threads are threads of the firmware has the
    switcher's resources at each of its threads. *)
Lemma fw_switcher_threads {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}
    {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters} (fw : firmware) (img : fw_image) (C : CmptName) :
  let swl := fw_switcher_layout img in
  (∀ t, t ∈ cmpt_threads C → ∃ i, t = UserThread i ∧ i < length (fw_threads fw)) →
  ([∗ list] i ↦ _ ∈ fw_threads fw,
     switcher_static (th := UserThread i) (swlayout := swl)) -∗
  ([∗ list] i ↦ _ ∈ fw_threads fw,
     na_inv (tpool (UserThread i)) Ntstack
       (trusted_stack_inv (th := UserThread i) (swlayout := swl))) -∗
  switcher_threads (swlayout := swl) C.
Proof.
  iIntros (swl Hthreads) "#Hstatics #Htstacks !>".
  iIntros (t') "#Ht'".
  iDestruct (thread_in_elim with "Ht'") as %Ht'.
  destruct (Hthreads t' Ht') as (i & -> & Hi).
  destruct (lookup_lt_is_Some_2 _ _ Hi) as [ft Hft].
  iDestruct (big_sepL_lookup _ _ i ft Hft with "Hstatics") as "Hstatic".
  iDestruct (big_sepL_lookup _ _ i ft Hft with "Htstacks") as "Htstack".
  iFrame "Hstatic Htstack".
Qed.

Section prepared_pt.
  Context
    {Σ : gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** The resources of [fw_shared_res] and [fw_thread_res] at the first
      thread, run as the thread [th], with the compartments but the
      scheduler's initialised, the worlds of the compartments but
      [C_sched], and the first thread at the code of its compartment, at
      the posture of its entry. *)
  Definition fw_init_res (fw : firmware) (img : fw_image) (C_sched : CmptName) : iProp Σ :=
    let m := fw_entry_cmpt fw img 0 in
    let t := thread_of img 0 in
    "#Hswitcher" ∷
      na_inv (tpool th) Ntstack (trusted_stack_inv (swlayout := fw_switcher_layout img)) ∗
    "#Hswitcher_static" ∷ switcher_static (swlayout := fw_switcher_layout img) ∗
    "#Hassert" ∷
      assert_static (lib_b (lib_of img "assert")) (lib_e (lib_of img "assert")) (img_flag img) ∗
    "Hcmpts" ∷ ([∗ list] fc ∈ fw_cmpts fw, fw_cmpt_res_user img fc) ∗
    "Hotypes" ∷ ([∗ list] o ∈ fw_otypes fw, can_alloc_pred o) ∗
    "Hworlds" ∷ ([∗ set] C ∈ CNames ∖ {[C_sched]}, world_interp fw_world0 C) ∗
    "Hheap" ∷ ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) ∗
    "Hshadow" ∷ ([∗ map] a↦s ∈ initial_heap_shadow, a ↦ₛ s) ∗
    "Hclaims" ∷ ([∗ map] a↦c ∈ init_claims (fw_set (fw_heap_roots fw)), addr_alloc a c) ∗
    "HPC" ∷ PC ↦ₚ[th] Cap RX Global (cmpt_b_pcc m) (cmpt_e_pcc m) (cmpt_a_code m) ∗
    "Hcgp" ∷ cgp ↦ᵣ[th] Cap RW Global (cmpt_b_cgp m) (cmpt_e_cgp m) (cmpt_b_cgp m) ∗
    "Hcsp" ∷
      csp ↦ᵣ[th] Cap RWL Local (b_stack t) (e_stack t) (stk_start_a (b_stack t) (e_stack t)) ∗
    "Hcra" ∷ cra ↦ᵣ[th] thread_return_sentry (swlayout := fw_switcher_layout img) ∗
    "Hregs" ∷ regs[th] fw_cleared_regs ∗
    "Hstack" ∷
      [[ b_stack t, e_stack t ]] ↦ₐ
        [[ lword_of_word <$> replicate (ft_stack_size (fw_thread0 fw)) (WInt 0) ]] ∗
    "%Hstack_min" ∷
      ⌜ (b_stack t + Z.of_nat (fw_entry_min_stack fw 0) + StackEntry_reserved_space
         <= e_stack t)%Z ⌝ ∗
    "Hcstk" ∷
      ◯(CSTK)[th]
        (entry_cstack {| tf_csp := Cap RWL Local (b_stack t) (e_stack t) (stk_start_a (b_stack t) (e_stack t));
                         tf_export_tbl :=
                           Cap RW Global (cmpt_exp_tbl_pcc m)
                             (cmpt_exp_tbl_entries_end m) (cmpt_exp_tbl_pcc m);
                         tf_error_count := 0 |}) ∗
    "Hna" ∷ na_own (tpool th) ⊤ ∗
    "HMIE" ∷ MIE ↦ₜ[th] fw_entry_posture fw img 0 ∗
    "Hheld" ∷
      held (th := th)
        (CL := crit_link_full (swlayout := fw_switcher_layout img) th)
        (CR := crit_route_full (swlayout := fw_switcher_layout img) th)
        (fw_entry_posture fw img 0).

  (** The resources of [fw_init_res] that set up the worlds: those of a
      firmware whose first thread starts in an untrusted compartment,
      without the thread's registers, call stack and non-atomic token
      ([fw_obligations_of_untrusted]). The stack is there: the case study
      closes it in the world of the entry compartment. *)
  Definition fw_setup_res (fw : firmware) (img : fw_image) (C_sched : CmptName) : iProp Σ :=
    let t := thread_of img 0 in
    "#Hswitcher" ∷
      na_inv (tpool th) Ntstack (trusted_stack_inv (swlayout := fw_switcher_layout img)) ∗
    "#Hswitcher_static" ∷ switcher_static (swlayout := fw_switcher_layout img) ∗
    "#Hassert" ∷
      assert_static (lib_b (lib_of img "assert")) (lib_e (lib_of img "assert")) (img_flag img) ∗
    "Hcmpts" ∷ ([∗ list] fc ∈ fw_cmpts fw, fw_cmpt_res_user img fc) ∗
    "Hotypes" ∷ ([∗ list] o ∈ fw_otypes fw, can_alloc_pred o) ∗
    "Hworlds" ∷ ([∗ set] C ∈ CNames ∖ {[C_sched]}, world_interp fw_world0 C) ∗
    "Hheap" ∷ ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) ∗
    "Hshadow" ∷ ([∗ map] a↦s ∈ initial_heap_shadow, a ↦ₛ s) ∗
    "Hclaims" ∷ ([∗ map] a↦c ∈ init_claims (fw_set (fw_heap_roots fw)), addr_alloc a c) ∗
    "Hstack" ∷
      [[ b_stack t, e_stack t ]] ↦ₐ
        [[ lword_of_word <$> replicate (ft_stack_size (fw_thread0 fw)) (WInt 0) ]].

  (** The export table of a compartment that is not the scheduler, beside
      the compartments. *)
  #[local] Lemma fw_cmpts_res_user_pers img (fcs : list fw_cmpt) fc :
    fc ∈ fcs →
    (∀ sb, fc_body fc ≠ SchedulerBody sb) →
    ([∗ list] fc ∈ fcs, fw_cmpt_res_user img fc) ⊢
    ([∗ list] fc ∈ fcs, fw_cmpt_res_user img fc) ∗ fw_cmpt_pers_res img fc.
  Proof.
    intros Hin Hnsched. apply list_elem_of_lookup in Hin as [k Hk].
    iIntros "Hcmpts".
    iDestruct (big_sepL_lookup_acc with "Hcmpts") as "[Hfc Hclose]"; first exact Hk.
    rewrite /fw_cmpt_res_user /fw_cmpt_res.
    destruct (fc_body fc) as [tb|ub|sb] eqn:Hbody; last by destruct (Hnsched sb).
    all: iDestruct "Hfc" as "(Hm & Hs & #Hp)"; iFrame "Hp"; iApply "Hclose"; iFrame "Hm Hs Hp".
  Qed.
End prepared_pt.

Section worlds_join.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ} `{MP : MachineParameters}.
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The worlds of the thread [t] of the compartments [S], from their maps
      of Permanent regions and the local maps of [t]. *)
  Lemma fw_worlds_join (t : Thread) (S : gset CmptName) (W : WORLD) :
    ([∗ set] C ∈ S,
       perm_region_map (allocg := @cerise_registryG Σ (ceriseG_of t))
         (memg := @mem_gen_memG Σ (ceriseG_of t)) C ∅) -∗
    ([∗ set] C ∈ S,
       local_region_map (allocg := @cerise_registryG Σ (ceriseG_of t))
         (memg := @mem_gen_memG Σ (ceriseG_of t)) t W C ∅) -∗
    [∗ set] C ∈ S, world_interp (ceriseg := ceriseG_of t) (th := t) W C.
  Proof.
    iIntros "Hperms Hlocals".
    iCombine "Hperms Hlocals" as "H".
    rewrite -big_sepS_sep.
    iApply (big_sepS_impl with "H").
    iIntros "!>" (C HC) "[Hperm Hlocal]".
    rewrite world_interp_eq. iFrame.
  Qed.
End worlds_join.

(** The obligations of a firmware with one thread, from an obligation over
    the resources [fw_init_res] of its first thread, for an assignment
    [cthreads] with the context-switch thread in [C_sched], in exclusive
    mode. *)
Lemma fw_obligations_of (Σ : gFunctors) {Cname : CmptNameG} {cthreads : CmptThreads}
    `{MP : MachineParameters} (fw : firmware) (C_sched : CmptName) :
  fw_entry_at_code fw →
  fw_threads fw = [fw_thread0 fw] →
  Forall fw_lib_ok (fw_libs fw) →
  assert_lib ∈ fw_libs fw →
  CtxSwitch ∈ cmpt_threads C_sched →
  cmpt_shared C_sched = false →
  (∀ (img : fw_image) (σ : ExecConf)
     (ceriseb : ceriseBaseG Σ) (sealsg : sealStoreG Σ)
     (stsg : STSG Σ) (relg : relGS Σ)
     (cstackg : CSTACKG Σ),
     firmware_ok fw img σ →
     ⊢ fw_init_res (th := UserThread 0) fw img C_sched
       ={⊤}=∗
       let _ : switcherLayout := fw_switcher_layout img in safe[u 0]) →
  fw_obligations Σ fw.
Proof.
  intros Hentry Hthreads Hlibs_ok Hassert_in Hin Hexcl Hprep.
  split; first exact Hlibs_ok. exists cthreads, C_sched.
  split; first exact Hin. split; first exact Hexcl.
  intros img σ ceriseb sealsg stsg relg cstackg Hok.
  iIntros "Hshared". iNamed "Hshared". iModIntro.
  iDestruct (fw_assert_static fw img σ (UserThread 0) Hok Hassert_in with "Hlibs")
    as "#Hassert".
  rewrite Hthreads !big_sepL_singleton.
  iIntros "Hthread _". iNamed "Hthread".
  (* The worlds of the user thread 0 *)
  iDestruct (big_sepS_delete _ CNames C_sched with "Hlocals") as "[_ Hlocals]".
  { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
  iDestruct (fw_worlds_join (UserThread 0) with "Hworlds Hlocals") as "Hworlds".
  iEval (rewrite (fw_entry_pc_code fw img σ Hentry Hok)) in "HPC".
  iEval (rewrite fw_thread_cra_eq) in "Hcra".
  iEval (rewrite fw_thread_of_0) in "Hstack".
  pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hstack_min.
  iApply (Hprep img σ ceriseb sealsg stsg relg cstackg Hok).
  iDestruct "Hswitcher_static" as "#Hswitcher_static".
  iFrame "∗ # %".
Qed.

(** The assignment of threads of a one-thread firmware whose scheduler runs
    in [C_sched]: the context-switch thread in [C_sched], the user thread 0
    everywhere else, in exclusive mode. *)
Definition fw_cthreads_pinned {Cname : CmptNameG} (C_sched : CmptName) : CmptThreads :=
  {| cmpt_threads := λ C, if decide (C = C_sched) then {[CtxSwitch]} else {[UserThread 0]};
     cmpt_shared := λ _, false;
     cmpt_threads_sep := ltac:(intros C t; cbv beta; case_decide; set_solver) |}.

(** The obligations of a firmware with one thread, from an obligation over
    the resources [fw_init_res] of its first thread, with every compartment
    but [C_sched] run by the user thread 0 only, and [C_sched] by the
    context-switch thread only, in exclusive mode: the obligation receives
    this pinning of the threads, not the assignment itself. *)
Lemma fw_obligations_of_pinned (Σ : gFunctors) {Cname : CmptNameG}
    `{MP : MachineParameters} (fw : firmware) (C_sched : CmptName) :
  fw_entry_at_code fw →
  fw_threads fw = [fw_thread0 fw] →
  Forall fw_lib_ok (fw_libs fw) →
  assert_lib ∈ fw_libs fw →
  (∀ (cthreads : CmptThreads),
     (∀ C, C ≠ C_sched → cmpt_threads C ⊆ {[UserThread 0]}) →
     (∀ C, C ≠ C_sched → UserThread 0 ∈ cmpt_threads C) →
     cmpt_threads C_sched = {[CtxSwitch]} →
     (∀ C, cmpt_shared C = false) →
     ∀ (img : fw_image) (σ : ExecConf)
       (ceriseb : ceriseBaseG Σ) (sealsg : sealStoreG Σ)
       (stsg : STSG Σ) (relg : relGS Σ)
       (cstackg : CSTACKG Σ),
       firmware_ok fw img σ →
       ⊢ fw_init_res (th := UserThread 0) fw img C_sched
         ={⊤}=∗
         let _ : switcherLayout := fw_switcher_layout img in safe[u 0]) →
  fw_obligations Σ fw.
Proof.
  intros Hentry Hthreads Hlibs_ok Hassert_in Hprep.
  apply (fw_obligations_of Σ (cthreads := fw_cthreads_pinned C_sched) fw C_sched Hentry Hthreads
           Hlibs_ok Hassert_in).
  - cbn. rewrite decide_True; last done. set_solver.
  - reflexivity.
  - apply Hprep.
    + intros C HC. cbn. by rewrite decide_False.
    + intros C HC. cbn. rewrite decide_False; last done. set_solver.
    + cbn. by rewrite decide_True.
    + intros C. reflexivity.
Qed.

(** The obligations of a firmware with one thread whose first thread starts
    in an untrusted compartment. The case study sets up the worlds from
    [fw_setup_res] and returns the world [W] of a logical compartment [C]
    other than [C_sched] in which the PCC and the CGP of the entry
    compartment and the thread's stack are safe
    ([fw_close_adv_world_entry]). The thread then runs by the FTLR
    ([fundamental_untrusted_thread]): no main specification is needed.
    Every compartment but [C_sched] runs on the user thread [0] only. *)
Lemma fw_obligations_of_untrusted (Σ : gFunctors) {Cname : CmptNameG} {cthreads : CmptThreads}
    `{MP : MachineParameters} (fw : firmware) (C_sched : CmptName) :
  fw_entry_untrusted fw →
  fw_threads fw = [fw_thread0 fw] →
  Forall fw_lib_ok (fw_libs fw) →
  assert_lib ∈ fw_libs fw →
  CtxSwitch ∈ cmpt_threads C_sched →
  (∀ C, C ≠ C_sched → cmpt_threads C = {[UserThread 0]}) →
  (∀ C, cmpt_shared C = false) →
  (∀ (img : fw_image) (σ : ExecConf)
     (ceriseb : ceriseBaseG Σ) (sealsg : sealStoreG Σ)
     (stsg : STSG Σ) (relg : relGS Σ)
     (cstackg : CSTACKG Σ),
     firmware_ok fw img σ →
     ⊢ fw_setup_res (th := UserThread 0) fw img C_sched
       ={⊤}=∗
       ∃ (W : WORLD) (C : CmptName),
         ⌜C ≠ C_sched⌝ ∗
         world_interp (ceriseg := ceriseG_of (UserThread 0)) (th := UserThread 0) W C ∗
         interp (th := UserThread 0)
           (CL := crit_link_full (swlayout := fw_switcher_layout img))
           (CR := crit_route_full (swlayout := fw_switcher_layout img))
           W C (fw_entry_pcc fw img 0) ∗
         interp (th := UserThread 0)
           (CL := crit_link_full (swlayout := fw_switcher_layout img))
           (CR := crit_route_full (swlayout := fw_switcher_layout img))
           W C (fw_entry_cgp fw img 0) ∗
         interp (th := UserThread 0)
           (CL := crit_link_full (swlayout := fw_switcher_layout img))
           (CR := crit_route_full (swlayout := fw_switcher_layout img))
           W C (fw_thread_csp img 0)) →
  fw_obligations Σ fw.
Proof.
  intros Huntrusted Hthreads Hlibs_ok Hassert_in Hin Hpin Hshared Hsetup.
  split; first exact Hlibs_ok. exists cthreads, C_sched.
  split; first exact Hin. split; first exact (Hshared C_sched).
  intros img σ ceriseb sealsg stsg relg cstackg Hok.
  pose proof Hok as (_ & _ & _ & Hwf).
  destruct (firmware_ok_threads_inv _ _ _ Hok) as (_ & Hentries).
  destruct (Hentries 0 (fw_thread0 fw)) as [Hin_fc Hname]; first by rewrite Hthreads.
  rewrite /fw_entry_untrusted in Huntrusted.
  destruct (fc_body (fw_entry_fc fw 0)) as [|ub|] eqn:Hbody; [by destruct Huntrusted | |
    by destruct Huntrusted].
  pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
  assert (cmpt_of img (fc_name (fw_entry_fc fw 0)) = fw_entry_cmpt fw img 0) as Hm.
  { by rewrite Hname /fw_entry_cmpt fw_thread_of_0. }
  pose proof (img_wf_cmpt_layout _ _ _ Hwf Hin_fc) as Hc. rewrite Hm in Hc.
  pose proof (icl_exp_tbl_pcc_size _ Hc) as Htbl_cgp_size.
  assert (cmpt_exp_tbl_cgp (fw_entry_cmpt fw img 0) =
            (cmpt_exp_tbl_pcc (fw_entry_cmpt fw img 0) ^+ ExportTable_offset_cgp)%a)
    as Hcgp_eq by solve_addr+Htbl_cgp_size.
  pose proof (proj2 (icl_cgp_not_heap _ Hc)) as Hcgp_heap.
  iIntros "Hshared". iNamed "Hshared". iModIntro.
  rewrite Hthreads !big_sepL_singleton.
  iIntros "Hthread _". iNamed "Hthread".
  (* The worlds of the user thread 0 *)
  iDestruct (big_sepS_delete _ CNames C_sched with "Hlocals") as "[_ Hlocals]".
  { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
  iDestruct (fw_worlds_join (UserThread 0) with "Hworlds Hlocals") as "Hworlds".
  iDestruct "Hswitcher" as "#Hswitcher".
  iDestruct "Hswitcher_static" as "#Hswitcher_static".
  iDestruct (fw_assert_static fw img σ (UserThread 0) Hok Hassert_in with "Hlibs")
    as "#Hassert".
  (* The export table of the entry compartment *)
  iDestruct (fw_cmpts_res_user_pers with "Hcmpts") as "[Hcmpts #Hpers]";
    [exact Hin_fc | by rewrite Hbody |].
  iEval (rewrite /fw_cmpt_pers_res /fw_handler_res Hbody Hm Hcgp_eq) in "Hpers".
  iDestruct "Hpers" as "(#Htbl_pcc & #Htbl_cgp & (%eh & %ehs & #Heh & #Hehs) & _)".
  (* The case study's worlds *)
  iEval (rewrite fw_thread_of_0) in "Hstack".
  iMod (Hsetup img σ ceriseb sealsg stsg relg cstackg Hok
         with "[Hcmpts Hotypes Hworlds Hheap Hshadow Hclaims Hstack]")
    as (W C) "(%HC & Hworld & #Hpcc_i & #Hcgp_i & #Hcsp_i)".
  { iFrame "Hswitcher_static". iFrame "∗ #". }
  (* The thread's stack, outside the heap *)
  iAssert (entry_stack_interp
             (interp (th := UserThread 0)
                (CL := crit_link_full (swlayout := fw_switcher_layout img))
                (CR := crit_route_full (swlayout := fw_switcher_layout img)))
             W C (fw_entry_frame fw img 0))
    as "#Hstk".
  { iEval (rewrite /fw_thread_csp) in "Hcsp_i".
    iDestruct (interp_cap_disjoint_wl with "Hcsp_i") as %[_ Hheap]; first done.
    iExists RWL, Local, _, _, _.
    iSplit; first done. iSplit; first done.
    iModIntro. iExact "Hcsp_i". }
  (* The registers *)
  set (regs := <[cra := lword_of_word (fw_thread_cra img)]>
                 (<[csp := lword_of_word (fw_thread_csp img 0)]>
                    (<[cgp := lword_of_word (fw_entry_cgp fw img 0)]> fw_cleared_regs))).
  iAssert (registers_pointsto (th := UserThread 0) regs)
    with "[Hcgp Hcsp Hcra Hregs]" as "Hrmap".
  { rewrite /registers_pointsto /regs.
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u 0] w)%I with "Hcra").
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u 0] w)%I with "Hcsp").
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u 0] w)%I with "Hcgp").
    iExact "Hregs". }
  assert (∀ r, is_Some (regs !! r)) as Hfull.
  { intros r. rewrite /regs.
    destruct (decide (r = cra)) as [->|Hr_cra]; first by simplify_map_eq.
    destruct (decide (r = csp)) as [->|Hr_csp]; first by simplify_map_eq.
    destruct (decide (r = cgp)) as [->|Hr_cgp]; first by simplify_map_eq.
    rewrite !lookup_insert_ne //.
    rewrite fw_cleared_regs_lookup; first done.
    rewrite fw_cleared_regs_dom.
    pose proof (all_registers_s_correct r). set_solver. }
  assert (∀ r, r ∉ ({[cra; cgp; csp]} : gset RegName) →
            regs !! r = Some (lword_of_word (WInt 0))) as Hzero.
  { intros r Hr. rewrite /regs !lookup_insert_ne; [|set_solver..].
    apply fw_cleared_regs_lookup. rewrite fw_cleared_regs_dom.
    pose proof (all_registers_s_correct r). set_solver. }
  (* The first thread runs in [C] *)
  iPoseProof (thread_in_intro (Σ := Σ) (UserThread 0) C) as "#Hthread0".
  { rewrite (Hpin C HC). set_solver. }
  iEval (rewrite /fw_entry_pc Hbody) in "HPC".
  iEval (rewrite /fw_entry_pcc) in "Hpcc_i".
  iEval (rewrite /fw_entry_cgp) in "Hcgp_i".
  iModIntro.
  iApply (fundamental_untrusted_thread (swlayout := fw_switcher_layout img)
            (swlayoutWf := Hswl_wf) W C (fw_entry_frame fw img 0)
            _ _ _ _ _ eh ehs regs (fw_entry_posture fw img 0) Hcgp_heap
           with "Hthread0 Hswitcher Hswitcher_static Htbl_pcc Htbl_cgp Heh Hehs Hpcc_i Hcgp_i Hstk
                 HPC Hrmap Hworld Hna Hcstk [%] HMIE Hheld").
  - by rewrite /fw_entry_frame /fw_entry_tbl.
  - exact Hfull.
  - by rewrite /regs; simplify_map_eq.
  - by rewrite /regs; simplify_map_eq.
  - rewrite /regs lookup_insert_eq. by rewrite fw_thread_cra_eq.
  - exact Hzero.
  - exact (Hshared C).
  - by intros [=].
Qed.

(** ** A thread alone in an untrusted compartment *)

(** A user thread [k] that starts in an untrusted compartment importing
    only the switcher call, and that is the only thread of the logical
    compartment [C], in exclusive mode, runs safely by the FTLR. It takes
    that compartment's resources and its map of Permanent regions as
    [fw_shared_res] gives them, at the user thread [0]; the world of [C] at
    the thread [k] joins that map with the thread's local map of [C], and
    is closed with the thread's own stack. *)
Lemma fw_isolated_thread_obligation {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}
    {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ : ExecConf) (k : nat) (ft : fw_thread)
    (ub : fw_untrusted) (C : CmptName) :
  let swl := fw_switcher_layout img in
  let fc := fw_entry_fc fw k in
  firmware_ok fw img σ →
  fw_threads fw !! k = Some ft →
  fc_body fc = UntrustedBody ub →
  Forall (λ n, n < 7) (fw_map ue_nargs (ub_exports ub)) →
  Forall (λ w, w = ISwitcherCall) (fc_imports fc) →
  cmpt_threads C = {[UserThread k]} →
  cmpt_shared C = false →
  ⊢ switcher_static (th := UserThread k) (swlayout := swl) -∗
    fw_cmpt_res (th := UserThread 0) img fc -∗
    perm_region_map (allocg := @cerise_registryG Σ (ceriseG_of (UserThread 0)))
      (memg := @mem_gen_memG Σ (ceriseG_of (UserThread 0))) C ∅ -∗
    (fw_thread_res fw img k -∗
     £ 1
     ={⊤}=∗
     let _ : switcherLayout := swl in safe[u k]).
Proof.
  intros swl fc Hok Hk Hbody Hnargs Himports Hpin Hexcl.
  subst swl fc.
  pose proof Hok as (_ & _ & _ & Hwf).
  destruct (firmware_ok_threads_inv _ _ _ Hok) as (_ & Hentries).
  destruct (Hentries k ft Hk) as [Hin_fc Hname].
  destruct (list_elem_of_lookup_1 _ _ Hin_fc) as [j Hj].
  pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
  assert (cmpt_of img (fc_name (fw_entry_fc fw k)) = fw_entry_cmpt fw img k) as Hm.
  { by rewrite Hname /fw_entry_cmpt (fw_thread_of_lookup _ _ _ Hk). }
  (* The layout of the compartment, as the closing takes it, and as the
     thread's entry names it *)
  pose proof (img_wf_cmpt_layout _ _ _ Hwf Hin_fc) as Hc.
  pose proof Hc as Hc'. rewrite Hm in Hc'.
  pose proof (icl_exp_tbl_pcc_size _ Hc') as Htbl_cgp_size.
  assert (cmpt_exp_tbl_cgp (fw_entry_cmpt fw img k) =
            (cmpt_exp_tbl_pcc (fw_entry_cmpt fw img k) ^+ ExportTable_offset_cgp)%a)
    as Hcgp_eq by solve_addr+Htbl_cgp_size.
  pose proof (proj2 (icl_cgp_not_heap _ Hc')) as Hcgp_heap.
  assert (cmpt_pcc_cap (layout_cmpt_of _ Hc) = fw_entry_pcc fw img k ∧
          cmpt_cgp_cap (layout_cmpt_of _ Hc) = fw_entry_cgp fw img k) as [Hpcc_eq Hcgp_cap_eq].
  { by rewrite /fw_entry_pcc /fw_entry_cgp -Hm. }
  assert (∀ a, a ∈ cmpt_region (layout_cmpt_of _ Hc) ∨
               a ∈ finz.seq_between (b_stack (thread_of img k)) (e_stack (thread_of img k)) →
               std fw_world0 !! LNonHeap a = None) as Hfree.
  { intros a _. by rewrite /fw_world0 lookup_empty. }
  iIntros "#Hstatic Hcmpt Hperm Hthread _". iNamed "Hthread".
  iDestruct "Hswitcher" as "#Hswitcher".
  (* The compartment and the world of [C], at the thread [k] *)
  iEval (rewrite (fw_cmpt_res_thread_indep (UserThread 0) (UserThread k))) in "Hcmpt".
  iEval (rewrite (perm_region_map_thread_indep (UserThread 0) (UserThread k))) in "Hperm".
  iDestruct (big_sepS_elem_of _ _ C with "Hlocals") as "Hlocal".
  { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
  iAssert (world_interp (ceriseg := ceriseG_of (UserThread k)) (th := UserThread k) fw_world0 C)
    with "[Hperm Hlocal]" as "Hworld".
  { rewrite world_interp_eq. iFrame. }
  (* The thread [k] is the only thread of [C] *)
  iPoseProof (switcher_threads_pinned (swlayout := fw_switcher_layout img) (UserThread k) C
              with "Hswitcher Hstatic") as "#Hswitcher_threads".
  { by rewrite Hpin. }
  iPoseProof (thread_in_intro (Σ := Σ) (UserThread k) C) as "#Hthread_in".
  { rewrite Hpin. set_solver. }
  (* The export table of the entry compartment *)
  iEval (rewrite /fw_cmpt_res) in "Hcmpt".
  iDestruct "Hcmpt" as "(Hmem & _ & #Hpers)".
  iPoseProof "Hpers" as "Hpers_tbl".
  iEval (rewrite /fw_cmpt_pers_res /fw_handler_res Hbody Hm Hcgp_eq) in "Hpers_tbl".
  iDestruct "Hpers_tbl" as "(#Htbl_pcc & #Htbl_cgp & (%eh & %ehs & #Heh & #Hehs) & _)".
  (* The world of [C], closed with the stack of the thread [k] *)
  iEval (rewrite (fw_thread_of_lookup _ _ _ Hk)) in "Hstack".
  iMod (fw_close_adv_world_entry_at (th := UserThread k) (E := ⊤) fw img σ k ft j
          (fw_entry_fc fw k) ub Hc fw_world0 C Hok Hk Hj Hbody Hnargs Hfree
         with "Hswitcher_threads Hstatic Hmem Hpers Hstack [] Hthread_in Hworld")
    as "(Hworld & #Hpcc_i & #Hcgp_i & #Hcsp_i & _)".
  { iIntros "_". iApply big_sepL_intro. iIntros "!>" (n w Hw).
    pose proof (Forall_lookup_1 _ _ _ _ Himports Hw) as ->.
    iApply (fw_switcher_call_safe fw img σ (cmpt_of img (fc_name (fw_entry_fc fw k))) C Hok
             with "Hswitcher_threads"). }
  set (Wadv := std_update_multiple fw_world0
                 (finz.seq_between (b_stack (thread_of img k)) (e_stack (thread_of img k)))
                 Temporary).
  iEval (rewrite Hpcc_eq) in "Hpcc_i".
  iEval (rewrite Hcgp_cap_eq) in "Hcgp_i".
  (* The thread's stack, outside the heap *)
  iAssert (entry_stack_interp
             (interp (th := UserThread k)
                (CL := crit_link_full (swlayout := fw_switcher_layout img))
                (CR := crit_route_full (swlayout := fw_switcher_layout img)))
             Wadv C (fw_entry_frame fw img k))
    as "#Hstk".
  { iEval (rewrite /fw_thread_csp) in "Hcsp_i".
    iDestruct (interp_cap_disjoint_wl with "Hcsp_i") as %[_ Hheap]; first done.
    iExists RWL, Local, _, _, _.
    iSplit; first done. iSplit; first done.
    iModIntro. iExact "Hcsp_i". }
  (* The registers *)
  set (regs := <[cra := lword_of_word (fw_thread_cra img)]>
                 (<[csp := lword_of_word (fw_thread_csp img k)]>
                    (<[cgp := lword_of_word (fw_entry_cgp fw img k)]> fw_cleared_regs))).
  iAssert (registers_pointsto (th := UserThread k) regs)
    with "[Hcgp Hcsp Hcra Hregs]" as "Hrmap".
  { rewrite /registers_pointsto /regs.
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u k] w)%I with "Hcra").
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u k] w)%I with "Hcsp").
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u k] w)%I with "Hcgp").
    iExact "Hregs". }
  assert (∀ r, is_Some (regs !! r)) as Hfull.
  { intros r. rewrite /regs.
    destruct (decide (r = cra)) as [->|Hr_cra]; first by simplify_map_eq.
    destruct (decide (r = csp)) as [->|Hr_csp]; first by simplify_map_eq.
    destruct (decide (r = cgp)) as [->|Hr_cgp]; first by simplify_map_eq.
    rewrite !lookup_insert_ne //.
    rewrite fw_cleared_regs_lookup; first done.
    rewrite fw_cleared_regs_dom.
    pose proof (all_registers_s_correct r). set_solver. }
  assert (∀ r, r ∉ ({[cra; cgp; csp]} : gset RegName) →
            regs !! r = Some (lword_of_word (WInt 0))) as Hzero.
  { intros r Hr. rewrite /regs !lookup_insert_ne; [|set_solver..].
    apply fw_cleared_regs_lookup. rewrite fw_cleared_regs_dom.
    pose proof (all_registers_s_correct r). set_solver. }
  (* The thread runs in [C] by the FTLR *)
  iEval (rewrite /fw_entry_pc Hbody) in "HPC".
  iEval (rewrite /fw_entry_pcc) in "Hpcc_i".
  iEval (rewrite /fw_entry_cgp) in "Hcgp_i".
  iModIntro.
  iApply (fundamental_untrusted_thread (th := UserThread k) (swlayout := fw_switcher_layout img)
            (swlayoutWf := Hswl_wf) Wadv C (fw_entry_frame fw img k)
            _ _ _ _ _ eh ehs regs (fw_entry_posture fw img k) Hcgp_heap
           with "Hthread_in Hswitcher Hstatic Htbl_pcc Htbl_cgp Heh Hehs Hpcc_i Hcgp_i Hstk
                 HPC Hrmap Hworld Hna Hcstk [%] HMIE Hheld").
  - by rewrite /fw_entry_frame /fw_entry_tbl.
  - exact Hfull.
  - by rewrite /regs; simplify_map_eq.
  - by rewrite /regs; simplify_map_eq.
  - rewrite /regs lookup_insert_eq. by rewrite fw_thread_cra_eq.
  - exact Hzero.
  - exact Hexcl.
  - by intros [=].
Qed.

(** ** Threads in a shared compartment *)

(** A user thread [k] that starts in an untrusted compartment of the shared
    logical compartment [C] runs safely by the FTLR. The compartment was
    opened beforehand on its map of Permanent regions, now in [wg_inv C]
    ([fw_open_adv_cmpt_perm]); the thread's world of [C] is its own local
    map, with its stack, joined with that invariant; the later credit of the
    thread's slot pays for the shared mode. *)
Lemma fw_shared_thread_obligation {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}
    {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}
    (fw : firmware) (img : fw_image) (σ : ExecConf) (k : nat) (ft : fw_thread)
    (ub : fw_untrusted) (C : CmptName) (W : WORLD)
    (Hc : img_cmpt_layout (cmpt_of img (fc_name (fw_entry_fc fw k)))) :
  let swl := fw_switcher_layout img in
  let fc := fw_entry_fc fw k in
  let C_cmpt := layout_cmpt_of (cmpt_of img (fc_name fc)) Hc in
  firmware_ok fw img σ →
  fw_threads fw !! k = Some ft →
  fc_body fc = UntrustedBody ub →
  UserThread k ∈ cmpt_threads C →
  cmpt_shared C = true →
  ⊢ switcher_static (th := UserThread k) (swlayout := swl) -∗
    fw_cmpt_pers_res (th := UserThread 0) img fc -∗
    interp (th := UserThread 0) W C (cmpt_pcc_cap C_cmpt) -∗
    interp (th := UserThread 0) W C (cmpt_cgp_cap C_cmpt) -∗
    wg_inv C -∗
    (fw_thread_res fw img k -∗
     £ 1
     ={⊤}=∗
     let _ : switcherLayout := swl in safe[u k]).
Proof.
  intros swl fc C_cmpt Hok Hk Hbody Hin Hsh.
  subst swl.
  destruct (firmware_ok_threads_inv _ _ _ Hok) as (_ & Hentries).
  destruct (Hentries k ft Hk) as [_ Hname].
  pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
  assert (cmpt_of img (fc_name (fw_entry_fc fw k)) = fw_entry_cmpt fw img k) as Hm.
  { by rewrite Hname /fw_entry_cmpt (fw_thread_of_lookup _ _ _ Hk). }
  (* The layout of the compartment, as the opening takes it, and as the
     thread's entry names it *)
  pose proof Hc as Hc'. rewrite Hm in Hc'.
  pose proof (icl_exp_tbl_pcc_size _ Hc') as Htbl_cgp_size.
  assert (cmpt_exp_tbl_cgp (fw_entry_cmpt fw img k) =
            (cmpt_exp_tbl_pcc (fw_entry_cmpt fw img k) ^+ ExportTable_offset_cgp)%a)
    as Hcgp_eq by solve_addr+Htbl_cgp_size.
  pose proof (proj2 (icl_cgp_not_heap _ Hc')) as Hcgp_heap.
  assert (cmpt_pcc_cap C_cmpt = fw_entry_pcc fw img k ∧
          cmpt_cgp_cap C_cmpt = fw_entry_cgp fw img k) as [Hpcc_eq Hcgp_cap_eq].
  { by rewrite /C_cmpt /fc /fw_entry_pcc /fw_entry_cgp -Hm. }
  iIntros "#Hstatic #Hpers #Hpcc_i #Hcgp_i #Hinv Hthread Hcred". iNamed "Hthread".
  iDestruct "Hswitcher" as "#Hswitcher".
  (* The export table of the entry compartment, at the thread [k] *)
  iEval (rewrite /fw_cmpt_pers_res /fw_handler_res Hbody Hm Hcgp_eq) in "Hpers".
  iDestruct "Hpers" as "(#Htbl_pcc & #Htbl_cgp & (%eh & %ehs & #Heh & #Hehs) & _)".
  iEval (rewrite (pointsto_pers_thread_indep (UserThread 0) (UserThread k))) in "Htbl_pcc".
  iEval (rewrite (pointsto_pers_thread_indep (UserThread 0) (UserThread k))) in "Htbl_cgp".
  iEval (rewrite (handler_stackful_thread_indep (UserThread 0) (UserThread k))) in "Heh".
  iEval (rewrite (handler_stackless_thread_indep (UserThread 0) (UserThread k))) in "Hehs".
  (* The PCC and the CGP, at the thread [k] in the thread's world *)
  set (la := finz.seq_between (b_stack (thread_of img k)) (e_stack (thread_of img k))).
  set (Wadv := std_update_multiple fw_world0 la Temporary).
  iEval (rewrite Hpcc_eq
           (interp_global_thread_world_free (UserThread 0) (UserThread k) W Wadv)) in "Hpcc_i".
  iEval (rewrite Hcgp_cap_eq
           (interp_global_thread_world_free (UserThread 0) (UserThread k) W Wadv)) in "Hcgp_i".
  (* The local map of [C], closed with the stack of the thread [k] *)
  iDestruct (big_sepS_elem_of _ _ C with "Hlocals") as "Hlocal".
  { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
  iEval (rewrite (fw_thread_of_lookup _ _ _ Hk)) in "Hstack".
  assert (Forall (λ a, std fw_world0 !! LNonHeap a = None) la) as Hfree_stack.
  { apply Forall_forall. intros a _. by rewrite /fw_world0 lookup_empty. }
  iMod (local_extend_temp_sepL2 (ceriseg := ceriseG_of (UserThread k)) (th := UserThread k)
          fw_world0 C la (lword_of_word <$> replicate (ft_stack_size ft) (WInt 0)) RWL
          (safeC (interp_in_mem (th := UserThread k)
             (CL := crit_link_full (swlayout := fw_switcher_layout img))
             (CR := crit_route_full (swlayout := fw_switcher_layout img)) RWL))
         with "Hlocal [Hstack]") as "(Hlocal & #Hrel_stk)".
  { done. }
  { exact Hfree_stack. }
  { rewrite big_sepL2_fmap_r.
    iEval (rewrite /region_pointsto big_sepL2_fmap_r) in "Hstack".
    iApply (big_sepL2_mono with "Hstack").
    intros n a w Ha Hw. cbn. iIntros "Hv".
    apply lookup_replicate in Hw as [-> _].
    rewrite /TmpRes key_pointsto_nonheap.
    iFrame "Hv".
    iSplit; first done.
    iSplit.
    { iApply bi.later_intro. iEval (rewrite /interp_in_mem_pre /=).
      iApply interp_int. }
    iApply bi.later_intro. iApply future_pub_mono_interp_in_mem_z. }
  (* The world of [C]: the local map joined with the invariant of [C] *)
  iPoseProof (world_resources_join (th := UserThread k) Wadv C Hsh with "Hinv Hlocal")
    as "Hworld".
  (* The thread's stack, outside the heap *)
  iAssert (entry_stack_interp
             (interp (th := UserThread k)
                (CL := crit_link_full (swlayout := fw_switcher_layout img))
                (CR := crit_route_full (swlayout := fw_switcher_layout img)))
             Wadv C (fw_entry_frame fw img k))
    as "#Hstk".
  { iAssert (interp (th := UserThread k)
               (CL := crit_link_full (swlayout := fw_switcher_layout img))
               (CR := crit_route_full (swlayout := fw_switcher_layout img))
               Wadv C (fw_thread_csp img k)) as "#Hcsp_i".
    { iApply (interp_stack_temporary (th := UserThread k) (swlayout := fw_switcher_layout img)
                Wadv C with "Hrel_stk").
      - exact (stack_disjoint_from_mmio (fw_switcher_cmpt_at fw img σ k ft Hok Hk)).
      - exact (stack_disjoint_from_heap (fw_switcher_cmpt_at fw img σ k ft Hok Hk)).
      - apply Forall_forall. intros a Ha.
        by apply std_sta_update_multiple_lookup_in_i. }
    iEval (rewrite /fw_thread_csp) in "Hcsp_i".
    iDestruct (interp_cap_disjoint_wl with "Hcsp_i") as %[_ Hheap]; first done.
    iExists RWL, Local, _, _, _.
    iSplit; first done. iSplit; first done.
    iModIntro. iExact "Hcsp_i". }
  (* The registers *)
  set (regs := <[cra := lword_of_word (fw_thread_cra img)]>
                 (<[csp := lword_of_word (fw_thread_csp img k)]>
                    (<[cgp := lword_of_word (fw_entry_cgp fw img k)]> fw_cleared_regs))).
  iAssert (registers_pointsto (th := UserThread k) regs)
    with "[Hcgp Hcsp Hcra Hregs]" as "Hrmap".
  { rewrite /registers_pointsto /regs.
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u k] w)%I with "Hcra").
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u k] w)%I with "Hcsp").
    iApply (big_sepM_insert_2 (λ r w, r ↦ᵣ[u k] w)%I with "Hcgp").
    iExact "Hregs". }
  assert (∀ r, is_Some (regs !! r)) as Hfull.
  { intros r. rewrite /regs.
    destruct (decide (r = cra)) as [->|Hr_cra]; first by simplify_map_eq.
    destruct (decide (r = csp)) as [->|Hr_csp]; first by simplify_map_eq.
    destruct (decide (r = cgp)) as [->|Hr_cgp]; first by simplify_map_eq.
    rewrite !lookup_insert_ne //.
    rewrite fw_cleared_regs_lookup; first done.
    rewrite fw_cleared_regs_dom.
    pose proof (all_registers_s_correct r). set_solver. }
  assert (∀ r, r ∉ ({[cra; cgp; csp]} : gset RegName) →
            regs !! r = Some (lword_of_word (WInt 0))) as Hzero.
  { intros r Hr. rewrite /regs !lookup_insert_ne; [|set_solver..].
    apply fw_cleared_regs_lookup. rewrite fw_cleared_regs_dom.
    pose proof (all_registers_s_correct r). set_solver. }
  (* The thread runs in [C] by the FTLR, in shared mode *)
  iPoseProof (thread_in_intro (Σ := Σ) (UserThread k) C Hin) as "#Hthread_in".
  iEval (rewrite /fw_entry_pc Hbody) in "HPC".
  iEval (rewrite /fw_entry_pcc) in "Hpcc_i".
  iEval (rewrite /fw_entry_cgp) in "Hcgp_i".
  iModIntro.
  iApply (fundamental_untrusted_thread_shared (th := UserThread k)
            (swlayout := fw_switcher_layout img) (swlayoutWf := Hswl_wf)
            Wadv C (fw_entry_frame fw img k)
            _ _ _ _ _ eh ehs regs (fw_entry_posture fw img k) Hcgp_heap
           with "Hthread_in Hswitcher Hstatic Htbl_pcc Htbl_cgp Heh Hehs Hpcc_i Hcgp_i Hstk
                 HPC Hrmap Hworld Hcred Hna Hcstk [%] HMIE Hheld").
  - by rewrite /fw_entry_frame /fw_entry_tbl.
  - exact Hfull.
  - by rewrite /regs; simplify_map_eq.
  - by rewrite /regs; simplify_map_eq.
  - rewrite /regs lookup_insert_eq. by rewrite fw_thread_cra_eq.
  - exact Hzero.
  - exact Hsh.
  - by intros [=].
Qed.

(** A trusted user thread [k] that calls into the shared logical
    compartment [C]: its world of [C] is its own local map, with its stack
    revoked (the trusted code keeps the stack), joined with the invariant
    of [C]. *)
Lemma fw_shared_caller_world {Σ : gFunctors} {ceriseb : ceriseBaseG Σ}
    {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    `{MP : MachineParameters} {E : coPset} (img : fw_image) (k : nat) (C : CmptName) :
  let t := thread_of img k in
  let la := finz.seq_between (b_stack t) (e_stack t) in
  let Wk := std_update_multiple fw_world0 la Revoked in
  cmpt_shared C = true →
  wg_inv C -∗
  local_region_map (allocg := @cerise_registryG Σ (ceriseG_of (UserThread k)))
    (memg := @mem_gen_memG Σ (ceriseG_of (UserThread k))) (UserThread k) fw_world0 C ∅
  ={E}=∗
  world_resources (th := UserThread k) Wk C ∗
  StackRevokedResources (th := UserThread k)
    (CL := crit_link_full (swlayout := fw_switcher_layout img))
    (CR := crit_route_full (swlayout := fw_switcher_layout img)) Wk C la.
Proof.
  iIntros (t la Wk Hsh) "#Hinv Hlocal".
  assert (Forall (λ a, std fw_world0 !! LNonHeap a = None) la) as Hfree_stack.
  { apply Forall_forall. intros a _. by rewrite /fw_world0 lookup_empty. }
  iMod (local_extend_revoked_sepL2 (ceriseg := ceriseG_of (UserThread k)) (th := UserThread k)
          fw_world0 C la RWL
          (safeC (interp_in_mem (th := UserThread k)
             (CL := crit_link_full (swlayout := fw_switcher_layout img))
             (CR := crit_route_full (swlayout := fw_switcher_layout img)) RWL))
          Hfree_stack with "Hlocal") as "[Hlocal Hrel_stk]".
  iModIntro.
  iSplitL "Hlocal".
  - iApply (world_resources_join (th := UserThread k) Wk C Hsh with "Hinv Hlocal").
  - iApply (StackWorldResources_from_rel_stack (th := UserThread k) with "Hrel_stk").
Qed.
