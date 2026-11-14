From stdpp Require Import finite.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
(* First: the fields of [compartment_layout]'s record [cmptSwitcher] are
   named as the switcher's addresses, which the later imports shadow. *)
From griotte Require Import compartment_layout adequacy_helpers.
From griotte Require Import logrel.
From griotte Require Import hw_lang hw_instance pool context_switch_layout_instance.
From griotte Require Import switcher_preamble context_switching_support
  context_switching_hyps context_switching_exit_tail.
From griotte Require Export adequacy_common_obligations.

(** * The generic part of the end-to-end adequacy

    Iris adequacy over the hardware, with one later per step; the ghost
    state of a Suspended user thread and its slot in the pool; the idle
    thread's slot; the initial worlds and call stacks, with those of the
    context-switch thread; and the adequacy theorem for the assert flag,
    from the start of the machine at the context-switch thread. *)

(** ** Iris adequacy, with one later per step *)

(** Iris's invariance theorem, with one later per step. *)
Lemma wp_invariance_hw Σ Λ `{!invGpreS Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invGS_gen HasLc Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS_gen HasLc Λ Σ := IrisG Hinv (λ σ _, stateI σ) fork_post
              (λ _, 1) (λ _ _ _ _, fupd_intro _ _) in
       stateI σ1 κs 0 ∗
       WP e1 @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?] ]%erased_steps_nsteps.
  eapply (wp_strong_adequacy_gen HasLc Σ _ _ _ _ _ _ _ _ _ (λ _, 1%nat)); [| done] => ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists (λ σ _, stateI σ), [(λ _, True)%I], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.

(** ** The names of the context-switch thread in the initial worlds *)

Section world_interp_init_ctx.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {Cname : CmptNameG} {sts_preg : STS_preG Σ} {relpreg : relGpreS Σ}
    {sealstorepreg : sealStorePreG Σ}.
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The worlds of the start: the scheduler's compartment [C_sched] at the
      context-switch thread, the maps of Permanent regions of the other
      compartments, and empty local maps of every compartment for the user
      threads [k < nthreads]. *)
  #[local] Lemma world_interp_init_ctx (oset : gset OType) (nthreads : nat) (C_sched : CmptName) :
    ⊢ |==> ∃ (relg : relGS Σ) (stsg : STSG Σ) (sstoreg : sealStoreG Σ),
        world_interp (th := CtxSwitch)
          (MkWorld ∅ (∅,∅)) C_sched ∗
        ([∗ set] C ∈ CNames ∖ {[C_sched]},
           perm_region_map C ∅) ∗
        ([∗ list] k ∈ seq 0 nthreads, [∗ set] C ∈ CNames,
           local_region_map (UserThread k) (MkWorld ∅ (∅,∅)) C ∅) ∗
        ([∗ set] o ∈ oset, can_alloc_pred o).
  Proof.
    assert (C_sched ∈ CNames) as Hin.
    { rewrite /CNames elem_of_list_to_set. apply elem_of_enum. }
    iMod (gen_sts_init_ctx (A:=LAddr) (B:=region_type) nthreads) as (stsg) "[Hstsc Hsts]".
    iMod (rel_init_ctx nthreads) as (relg) "(Hg & Hlc & HRELS)".
    iMod seal_store_init as (sstoreg) "Hseals".
    iExists relg, stsg, sstoreg; iFrame "Hseals".
    rewrite !(big_sepS_delete _ CNames C_sched) //.
    iDestruct "Hg" as "[Hg_s Hg]". iDestruct "Hlc" as "[Hlc_s _]".
    iDestruct "Hstsc" as "[Hstsc_s _]".
    iModIntro. iSplitL "Hg_s Hlc_s Hstsc_s".
    { rewrite world_interp_eq. iSplitL "Hg_s".
      - iExists ∅. rewrite /perm_region_map_M /rmap !big_sepM_empty. by iFrame.
      - iExists ∅. rewrite /local_region_map_M /rmap !big_sepM_empty /=. iFrame.
        iPureIntro. by rewrite !dom_empty_L. }
    iSplitL "Hg".
    - iApply (big_sepS_impl with "Hg").
      iModIntro; iIntros (C HC) "Hg".
      iExists ∅. rewrite /perm_region_map_M /rmap !big_sepM_empty. by iFrame.
    - iCombine "HRELS" "Hsts" as "H".
      rewrite -big_sepL_sep.
      iApply (big_sepL_impl with "H").
      iModIntro; iIntros (i k Hk) "[Hl Hsts]".
      iCombine "Hl" "Hsts" as "H".
      rewrite -big_sepS_sep.
      iApply (big_sepS_impl with "H").
      iModIntro; iIntros (C HC) "[Hl Hsts]".
      iExists ∅. rewrite /local_region_map_M /rmap !big_sepM_empty /=. iFrame.
      iPureIntro. by rewrite !dom_empty_L.
  Qed.
End world_interp_init_ctx.

(** ** A Suspended user thread *)
Section suspended.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout}.
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The ghost state of user thread [t], Suspended with the values [v]:
      its authorities and its fragments at [v], with its mtdc at home, its
      mtdc token, the token of its pool, and the tokens of its zone. *)
  Definition suspended_res (t : nat) (v : resume_vals) : iProp Σ :=
    "Hauths" ∷ auths_at t v ∗
    "HPC" ∷ PC ↦ₚ[u t] v.(rv_pc) ∗
    "Hregs" ∷ regs[u t] v.(rv_regs) ∗
    "Hmtdc" ∷ mtdc ↦ₜ[u t] mtdc_home_at (th := UserThread t) ∗
    "HMIE" ∷ MIE ↦ₜ[u t] v.(rv_mie) ∗
    "Hhwmb" ∷ mshwmb ↦ₜ[u t] v.(rv_hwmb) ∗
    "Hhwm" ∷ mshwm ↦ₜ[u t] v.(rv_hwm) ∗
    "Hztok" ∷ ([∗ set] a ∈ v.(rv_zone), zone_token[u t] a) ∗
    "Hlent" ∷ mtdc_lent_at (th := UserThread t) ∗
    "Hna" ∷ na_own (tpool (UserThread t)) ⊤.

  (** A Suspended slot for user thread [t], with no last owner: its save
      area, whose word [mshwmb] is the stack base [v.(rv_hwmb)], its mtdc
      token, its authorities at the values [v] it resumes with, the halves
      of its zone, and its run, which receives what it holds at its MIE and
      a later credit. *)
  Lemma slot_suspended_intro (t : nat) (ws : list LWord) (v : resume_vals) :
    saved_mie_ok ws →
    resume_ok_full ws v →
    ws !! 20%nat = Some (lword_of_word (WInt v.(rv_hwmb))) →
    save_area_holed (UserThread t) ws -∗
    mtdc_lent_at (th := UserThread t) -∗
    auths_at t v -∗
    zone_halves[CtxSwitch] v.(rv_zone) -∗
    ▷ (held (ceriseg := ceriseG_of (UserThread t)) (th := UserThread t)
         (CL := crit_link_full (UserThread t)) (CR := crit_route_full (UserThread t))
         v.(rv_mie) -∗
       £ 1
       ={⊤}=∗
       safe[u t]) -∗
    slot None t None.
  Proof.
    iIntros (Hmie Hok Hhb) "Hsa Hlent Hauths Hhalves Hrun".
    iAssert (hwm_base[u t] v.(rv_hwmb))%I as "#Hbase".
    { iDestruct "Hauths" as "(_ & _ & $)". }
    rewrite /slot. iExists ws, v. iFrame "Hsa Hlent Hauths Hhalves".
    iSplit; first done.
    iSplitR; first (iSplit; first done; iExists v.(rv_hwmb); by iFrame "Hbase").
    iIntros "!> Hpost Hlc".
    iApply fupd_wp. iApply ("Hrun" with "[Hpost] Hlc").
    destruct (rv_mie v); first done.
    rewrite posture_res_gen_unfold held_disabled.
    iDestruct "Hpost" as "[(%p & %c & %vl & %b & _ & _ & _ & _ & Hh) $]".
    by iApply handover_res_intro.
  Qed.
End suspended.

Section suspended_ghost.
  Context {Σ : gFunctors}.

  (** The ghost state of a Suspended user thread, at the names [g]: its PC,
      registers, mtdc at [m] and MIE at the values [v], authority and
      fragment of each, and its mtdc token, whose home value is [m]. *)
  Definition suspended_ghost
      (g : pcG Σ * gen_heapGS RegName LWord Σ * mtdcG Σ * mieG Σ * mtdcLentG Σ)
      (v : resume_vals) (m : mtdc_val) : iProp Σ :=
    ⌜@mtdc_home Σ g.2 = m⌝ ∗
    @PC_auth Σ g.1.1.1.1 v.(rv_pc) ∗ @PC_frag Σ g.1.1.1.1 v.(rv_pc) ∗
    gen_heap_interp (hG := g.1.1.1.2) v.(rv_regs) ∗
    ([∗ map] r ↦ w ∈ v.(rv_regs), pointsto (hG := g.1.1.1.2) r (DfracOwn 1) w) ∗
    @mtdc_auth Σ g.1.1.2 m ∗ @mtdc_frag Σ g.1.1.2 m ∗
    @MIE_auth Σ g.1.2 v.(rv_mie) ∗ @MIE_frag Σ g.1.2 v.(rv_mie) ∗
    @mtdc_lent Σ g.2.

  (** The ghost state of a list of Suspended user threads, each with its
      values and the home value of its mtdc. *)
  Lemma suspended_ghost_init {cerise_preg : ceriseGpreS Σ} (vms : list (resume_vals * mtdc_val)) :
    ⊢ |==> ∃ gs, [∗ list] g; vm ∈ gs; vms, suspended_ghost g vm.1 vm.2.
  Proof.
    iInduction vms as [|[v m] vms] "IH".
    - iModIntro. by iExists [].
    - iMod (PC_init v.(rv_pc)) as (pg) "[HPCa HPCf]".
      iMod (gen_heap_init v.(rv_regs)) as (rg) "(Hregs & Hpts & _)".
      iMod (mtdc_init m) as (mtg) "[Hmtdca Hmtdcf]".
      iMod (MIE_init v.(rv_mie)) as (mieg) "[HMIEa HMIEf]".
      iMod (mtdc_lent_init m) as (mlg Hhome) "Hlent".
      iMod "IH" as (gs) "Hgs".
      iModIntro. iExists ((pg, rg, mtg, mieg, mlg) :: gs).
      rewrite big_sepL2_cons /suspended_ghost /=. by iFrame.
  Qed.

  (** The high-water-mark ghost state of a Suspended user thread, at the
      name [g]: MSHWMB, MSHWM and its zone at the values [v], authority and
      fragment of each, the tokens of its zone, its rest and its stack
      base. *)
  Definition suspended_hwm_ghost (g : hwmG Σ) (v : resume_vals) : iProp Σ :=
    @mshwmb_auth Σ g v.(rv_hwmb) ∗ @mshwmb_frag Σ g v.(rv_hwmb) ∗
    @mshwm_auth Σ g v.(rv_hwm) ∗ @mshwm_frag Σ g v.(rv_hwm) ∗
    @zone_auth Σ g v.(rv_zone) ∗ ([∗ set] a ∈ v.(rv_zone), @zone_token Σ g a) ∗
    @hwm_rest Σ g ∗ @hwm_base Σ g v.(rv_hwmb).

  (** The high-water-mark ghost state of a list of Suspended user threads,
      each at its values. *)
  Lemma suspended_hwm_ghost_init {cerise_preg : ceriseGpreS Σ} (vs : list resume_vals) :
    ⊢ |==> ∃ hs, [∗ list] g; v ∈ hs; vs, suspended_hwm_ghost g v.
  Proof.
    iInduction vs as [|v vs] "IH".
    - iModIntro. by iExists [].
    - iMod (hwm_init_zone v.(rv_hwmb) v.(rv_hwm) v.(rv_zone))
        as (hg) "(Hba & Hbf & Hha & Hhf & Hza & Hzt & Hrest & _ & _ & Hbase)".
      iMod "IH" as (hs) "Hhs".
      iModIntro. iExists (hg :: hs).
      rewrite big_sepL2_cons /suspended_hwm_ghost. by iFrame.
  Qed.
End suspended_ghost.

(** ** The idle thread *)

(** The idle thread: registers zero, at the loop of an exited thread, MIE enabled. *)
Definition idle_save_area (swl : switcherLayout) (b_hz e_hz : Addr) : list LWord :=
  lword_of_word <$>
    save_area_content (@exited_thread_pcc swl) (WInt 0) (WInt 0) (WInt 0)
      (Cap WO Global b_hz e_hz b_hz) (WInt (mstatus_enc InterruptDisabled InterruptEnabled))
      (WInt 0) (WInt 0).

(** A save area with zero in [cra], [csp] and [cgp] resumes with every
    register null. *)
#[local] Lemma resume_regs_of_zero a mshwm_v m x y :
  resume_regs_of (lword_of_word <$> save_area_content a (WInt 0) (WInt 0) (WInt 0) mshwm_v m x y) =
  gset_to_gmap lnull all_registers_s.
Proof.
  apply map_eq. intros r. rewrite resume_regs_of_lookup.
  pose proof (all_registers_correct r) as Hr. unfold all_registers in Hr.
  repeat (apply elem_of_cons in Hr as [-> | Hr];
          [first [reflexivity | vm_compute; reflexivity] |]).
  by apply elem_of_nil in Hr.
Qed.

Lemma idle_save_area_resume_ok (swl : switcherLayout) b_hz e_hz :
  saved_mie_ok (idle_save_area swl b_hz e_hz) ∧
  resume_ok_full (idle_save_area swl b_hz e_hz)
    {| rv_regs := gset_to_gmap lnull all_registers_s;
       rv_pc := lword_of_word (@exited_thread_pcc swl);
       rv_mie := InterruptEnabled;
       rv_hwmb := 0;
       rv_hwm := 0;
       rv_zone := ∅ |}.
Proof.
  rewrite /idle_save_area. split; [|split; [|split; [|split; [|split] ] ] ].
  - intros w Hw. rewrite save_area_lookup_mstatus in Hw. injection Hw as <-.
    exact (mie_of_mstatus_enc InterruptDisabled InterruptEnabled).
  - cbn [rv_regs]. by rewrite resume_regs_of_zero.
  - cbn [rv_mie]. rewrite save_area_word_mstatus.
    exact (eq_sym (mpie_of_mstatus_enc InterruptDisabled InterruptEnabled)).
  - cbn [rv_pc]. split.
    + rewrite /resume_pc_word save_area_word_mepcc save_area_word_mcause.
      case_decide as Hc; first (vm_compute in Hc; discriminate Hc).
      cbv beta iota zeta. symmetry. apply legalise_pc_ok_id.
      rewrite /exited_thread_pcc. done.
    + intros _. reflexivity.
  - cbn [rv_hwmb]. by rewrite save_area_word_mshwmb.
  - cbn [rv_hwm]. by rewrite save_area_word_mshwm.
Qed.

Section idle.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The values the idle thread resumes with: registers zero, the PC of
      the loop of an exited thread, interrupts enabled. *)
  Definition idle_start_vals : resume_vals :=
    {| rv_regs := gset_to_gmap lnull all_registers_s;
       rv_pc := lword_of_word exited_thread_pcc;
       rv_mie := InterruptEnabled;
       rv_hwmb := 0;
       rv_hwm := 0;
       rv_zone := ∅ |}.

  (** The idle thread [n] is Suspended at the loop of an exited thread: its
      save area as the loader writes it, its hazard slots at [b_hz, e_hz),
      its zone empty. *)
  Lemma idle_slot (n : nat) (b_hz e_hz : Addr) :
    codefrag_pers (ceriseg := ceriseG_of (UserThread n)) a_switcher_call switcher_instrs -∗
    save_area_holed (UserThread n) (idle_save_area swlayout b_hz e_hz) -∗
    suspended_res n idle_start_vals -∗
    slot None n None.
  Proof.
    iIntros "#Hcode Hsa Hres". iNamed "Hres".
    destruct (idle_save_area_resume_ok swlayout b_hz e_hz) as [Hmie Hok].
    iAssert (zone_halves[CtxSwitch] ∅)%I as "Hhalves".
    { by rewrite /zone_halves big_sepS_empty. }
    iApply (slot_suspended_intro n _ idle_start_vals Hmie Hok eq_refl
             with "Hsa Hlent Hauths Hhalves").
    iIntros "!> _ _ !>".
    iApply (exited_tail_safe n with "Hcode [] [] HPC HMIE Hregs []").
    - by iLeft.
    - by rewrite dom_gset_to_gmap.
    - done.
  Qed.
End idle.

(** ** Initial world, seal store and call stack *)

(** A big separating conjunction over the indices of [l]. *)
#[local] Lemma big_sepL_seq_index_gen {PROP : bi} {A} (Φ : nat → PROP) (n : nat) (l : list A) :
  ([∗ list] k ∈ seq n (length l), Φ k) ⊣⊢ [∗ list] k ↦ _ ∈ l, Φ (n + k).
Proof.
  revert n. induction l as [|x l IH]; intros n; first done.
  rewrite /= IH Nat.add_0_r. f_equiv.
  apply big_sepL_proper => k _ _. by rewrite Nat.add_succ_r.
Qed.

#[local] Lemma big_sepL_seq_index {PROP : bi} {A} (Φ : nat → PROP) (l : list A) :
  ([∗ list] k ∈ seq 0 (length l), Φ k) ⊣⊢ [∗ list] k ↦ _ ∈ l, Φ k.
Proof. apply (big_sepL_seq_index_gen Φ 0 l). Qed.

Section world_init.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG Σ} {relpreg : relGpreS Σ}
    {cstack_preg : CSTACK_preG Σ}
    `{MP: MachineParameters}.
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The call stack of the context-switch thread starts with the entry
      frame [ef_c] only, that of the user thread [k] with [efs !! k] only;
      the stack of each thread is the one of its entry frame.
      The world of the scheduler's compartment [C_sched] is the
      context-switch thread's; the maps of Permanent regions of the other
      compartments are given once; each user thread [k] with a frame in
      [efs] has an empty local map of every compartment. *)
  Lemma initialise_world (C_sched : CmptName) (ots : gset OType) (ef_c : trusted_frame)
      (efs : list trusted_frame) :
    efs ≠ [] →
    ⊢ |==> ∃ (seal_storeg : sealStoreG Σ) (relg : relGS Σ)
            (stsg : STSG Σ) (cstackg : CSTACKG Σ),
      ([∗ set] o ∈ ots, can_alloc_pred o) ∗
      ●(CSTK)[CtxSwitch] (entry_cstack ef_c) ∗
      ◯(CSTK)[CtxSwitch] (entry_cstack ef_c) ∗
      thread_stack_bounds (th := CtxSwitch) (cstk_hwm_base (entry_cstack ef_c))
        (cstk_hwm_top (entry_cstack ef_c)) ∗
      ([∗ list] k ↦ ef ∈ efs,
         ●(CSTK)[u k] (entry_cstack ef) ∗ ◯(CSTK)[u k] (entry_cstack ef)) ∗
      ([∗ list] k ↦ ef ∈ efs,
         thread_stack_bounds (th := UserThread k) (cstk_hwm_base (entry_cstack ef))
           (cstk_hwm_top (entry_cstack ef))) ∗
      world_interp (th := CtxSwitch)
        (MkWorld ∅ (∅,∅)) C_sched ∗
      ([∗ set] C ∈ CNames ∖ {[C_sched]},
         perm_region_map C ∅) ∗
      [∗ list] k ↦ _ ∈ efs, [∗ set] C ∈ CNames,
        local_region_map (UserThread k) (MkWorld ∅ (∅,∅)) C ∅.
  Proof.
    intros _.
    iMod (gen_cstack_init_ctx (entry_cstack ef_c) ((λ ef, entry_cstack ef) <$> efs))
      as (cstackg) "(Hcstk_full & Hcstk_frag & #Htstk_ctx & Hcstks)".
    iEval (rewrite big_sepL_fmap) in "Hcstks".
    iEval (setoid_rewrite bi.sep_assoc) in "Hcstks".
    iDestruct (big_sepL_sep with "Hcstks") as "[Hcstks #Htstks]".
    iMod (world_interp_init_ctx ots (length efs) C_sched) as (relg stsg seal_storeg)
      "(Hctx & Hworlds & Hlocals & Hseal_store)".
    iEval (rewrite (big_sepL_seq_index
             (λ k, [∗ set] C ∈ CNames,
                local_region_map (UserThread k) (MkWorld ∅ (∅,∅)) C ∅)%I efs)) in "Hlocals".
    iModIntro; iExists seal_storeg, relg, stsg, cstackg; iFrame "∗ #".
  Qed.
End world_init.

(** ** Iris adequacy for the assert flag *)

(** A big separating conjunction over [imap]. *)
Lemma big_sepL_imap_index {PROP : bi} {A B} (f : nat → A → B) (Φ : nat → B → PROP)
    (l : list A) :
  ([∗ list] k ↦ y ∈ imap f l, Φ k y) ⊣⊢ [∗ list] k ↦ x ∈ l, Φ k (f k x).
Proof.
  revert f Φ. induction l as [|x l IH]; intros f Φ; first done.
  rewrite /= IH. done.
Qed.

Section flag_adequacy_helpers.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout}.
  #[local] Remove Hints ceriseG_of : typeclass_instances.

  (** The pool of the user threads [vs], all Suspended, with no last
      owner. *)
  #[local] Lemma pool_inv_alloc (vs : list resume_vals) :
    cur_auth None -∗
    ctx_last_owner_auth None -∗
    ([∗ list] t ↦ _ ∈ vs, slot None t None)
    ={⊤}=∗
    inv Npool (Pool (seq 0 (length vs))).
  Proof.
    iIntros "Hcur Hlast_owner Hslots". iApply inv_alloc. iApply bi.later_intro.
    rewrite /Pool. iExists None, None. iFrame "Hcur Hlast_owner".
    iSplit; first (iPureIntro; by intros ? ? ?).
    iSplit; first (iPureIntro; split_and!; done).
    iApply (big_sepL_seq_index (λ t, slot None t None) vs with "Hslots").
  Qed.

  (** The open pool token of the context-switch thread. *)
  #[local] Lemma inv_CtxSwitch_alloc : cur_frag None ={⊤}=∗ inv_CtxSwitch.
  Proof. iIntros "Hcur". iApply na_inv_alloc. by iNext. Qed.

  (** The thread resources of the context-switch thread, out of its
      switch window. *)
  #[local] Lemma thread_res_ctx_intro :
    running_frag CtxSwitch -∗
    resume_window_frag false -∗
    thread_res CtxSwitch (Exec : thread_langs.expr CtxK).
  Proof.
    iIntros "Hrun Hwin". rewrite /thread_res. iFrame "Hrun".
    iExists false. iFrame "Hwin". by iPureIntro.
  Qed.

  (** The flag, from its invariant and the hardware's state interpretation
      at any running thread. *)
  #[local] Lemma flag_from_SI_hw (flagN : namespace) (flag : Addr) (σ' : ExecConf) :
    inv flagN (flag ↦ₐ WInt 0) -∗
    SI_hw σ' -∗
    ∃ E, |={⊤,E}=> ⌜mem σ' !! flag = Some (WInt 0)⌝.
  Proof.
    iIntros "#Hflag Hσ". iNamed "Hσ". rewrite /thread_si /=.
    iDestruct "Hsi" as "[Hσ _]".
    iDestruct (SI_open with "Hσ") as (lpc lreg lsreg lmem R C Her) "(_ & _ & _ & Hm & _)".
    iExists (⊤ ∖ ↑flagN).
    iInv flagN as ">Hflag'" "Hclose".
    iDestruct (gen_heap_valid with "Hm Hflag'") as %Hm'_flag.
    iModIntro. iPureIntro.
    destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hm'_flag)
      as (pw & Hpw & _ & _ & Hnonheap & _).
    destruct (Hnonheap eq_refl) as [Heq | (_ & Hb)]; last by destruct Hb.
    rewrite Hpw Heq //.
  Qed.
End flag_adequacy_helpers.

Section flag_adequacy.
  (* The context-switch thread and the user threads meet here: every form
     names its thread. *)
  #[local] Remove Hints ceriseG_of : typeclass_instances.

(** Iris adequacy for the assert flag, over the hardware. The machine starts
    at the context-switch thread with interrupts disabled and mtdc zero,
    every user thread Suspended with the values [vs], whose zones cover
    their high-water marks. The premise receives the resources of the
    initial state (the context-switch thread's fragments, posture, mtdc
    token, high-water-mark resources and pool; the memory, with the cells of
    the zone [init_zone] of the context-switch thread, the shadow table and
    the address claims; each user thread's ghost state at its values,
    with its stack base; each user thread's exit part; the scheduler's
    state name, to be set),
    and returns the slots of the user threads and the flag's invariant;
    then, from the pool, the context-switch thread's open pool token and
    its thread resources, the hardware's WP. *)
Lemma cerise_flag_adequacy (Σ : gFunctors)
  {inv_preg : invGpreS Σ}
  {cerise_preg : ceriseGpreS Σ}
  {na_invg : na_invariants.na_invG Σ}
  {cur_preg : inG Σ curUR}
  {saved_preg : savedPropG Σ}
  {running_preg : ghost_varG Σ Thread}
  {window_preg : ghost_varG Σ bool}
  `{MP : MachineParameters} {TV : trapVector} {swlayout : switcherLayout}
  (flagN : namespace) (flag : Addr) (H : gset Addr)
  (σ σ' : ExecConf) (vs : list resume_vals) (es : list griotte_lang.expr) :
  ghost_init_cond σ H →
  reg σ !! cnull = Some (WInt 0) →
  dom (reg σ) = all_registers_s →
  sreg σ !! mtdc = Some (WInt 0) →
  mie_st σ = InterruptDisabled →
  vs ≠ [] →
  Forall (λ v, zone_covers v.(rv_hwmb) v.(rv_hwm) v.(rv_zone)) vs →
  (∀ (ceriseb : ceriseBaseG Σ),
     (* the trap vector of [ceriseb] is the one of the initial state *)
     @mtcc_vec (@cb_trapVector Σ ceriseb) = @mtcc_vec TV →
     (* the home values of the mtdc tokens *)
     mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
     (∀ t, ∃ p b e a, mtdc_home_at (th := UserThread t) = TStack p b e a) →
     (∀ t, t < length vs → mtdc_home_at (th := UserThread t) = tstack_home t) →
     (* the context-switch thread *)
     PC ↦ₚ[CtxSwitch] lword_of_word (pcc σ) -∗
     regs[CtxSwitch] (lword_of_word <$> reg σ) -∗
     mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) -∗
     MIE ↦ₜ[CtxSwitch] InterruptDisabled -∗
     handover_res (ceriseg := ceriseG_of CtxSwitch) -∗
     mtdc_lent_at (th := CtxSwitch) -∗
     hwm_res_ctx (th := CtxSwitch) -∗
     (* the pool of the context-switch thread in [ceriseb], not the [na_invg]
        parameter *)
     @na_own Σ (@cb_na_invG Σ ceriseb) (tpool CtxSwitch) ⊤ -∗
     (* the shared resources *)
     ([∗ map] a↦w ∈ mem σ,
        if decide (a ∈ init_zone (sreg σ)) then zone_cell[CtxSwitch] a
        else a ↦ₐ lword_of_word w) -∗
     ([∗ map] a↦s ∈ shadowtbl σ, a ↦ₛ s) -∗
     ([∗ map] a↦c ∈ init_claims H, addr_alloc a c) -∗
     (* the user threads *)
     ([∗ list] t ↦ v ∈ vs, suspended_res t v) -∗
     (* the saved propositions in [ceriseb], not the [saved_preg] parameter *)
     ([∗ list] t ↦ _ ∈ vs,
        @saved_prop_own Σ (@cb_saved_prop Σ ceriseb) (γ_exit (UserThread t))
          DfracDiscarded (exit_concrete (th := UserThread t))) -∗
     (* the scheduler's state between two activations, to be set *)
     @saved_prop_own Σ (@cb_saved_prop Σ ceriseb) γ_scheduler (DfracOwn 1) True%I
     ={⊤}=∗
     ([∗ list] t ↦ _ ∈ vs, slot None t None) ∗
     inv flagN (flag ↦ₐ WInt 0) ∗
     (inv Npool (Pool (seq 0 (length vs))) -∗
      inv_CtxSwitch -∗
      thread_res CtxSwitch (Exec : thread_langs.expr CtxK)
      ={⊤}=∗
      WP_hw griotte_lang.Exec {{ _, True }})) →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hinit Hnull Hdom Hmtdc Hmie Hvs Hcov Hwp Hstep.
  apply (wp_invariance_hw Σ griotte_hw_lang NotStuck griotte_lang.Exec σ es σ'
           (mem σ' !! flag = Some (WInt 0))); last exact Hstep.
  intros Hinv κs.
  (* The user threads: Suspended at [vs], the mtdc of thread [t] at home
     in its trusted stack; one default for the threads past [vs], at home
     in the trusted stack of the first of them. *)
  iMod (suspended_ghost_init (imap (λ t v, (v, tstack_home t)) vs)) as (gs) "Hgs".
  iMod (suspended_ghost_init [(ResumeVals ∅ lnull InterruptDisabled 0 0 ∅,
                               tstack_home (length vs))])
    as (gds) "Hgd".
  iDestruct (big_sepL2_cons_inv_r with "Hgd") as (gd gds' ->) "[Hgd _]".
  iDestruct "Hgd" as (Hhome_d) "_".
  iDestruct (big_sepL2_length with "Hgs") as %Hlen_gs.
  rewrite length_imap in Hlen_gs.
  iDestruct (big_sepL2_nth_l _ _ _ gd with "Hgs") as "Hgs".
  rewrite big_sepL_imap_index /suspended_ghost /=.
  iDestruct (big_sepL_sep with "Hgs") as "[Hhomes Hgs]".
  iDestruct (big_sepL_pure_1 with "Hhomes") as %Hhomes_g.
  iClear "Hhomes".
  (* Their high-water-mark ghost state, at [vs]; one default. *)
  iMod (suspended_hwm_ghost_init vs) as (hs) "Hhs".
  iMod (hwm_init 0 0) as (hd) "_".
  iDestruct (big_sepL2_nth_l _ _ _ hd with "Hhs") as "Hhs".
  (* Their pools, one default. *)
  iMod (na_pools_alloc vs) as (ps) "Hps".
  iMod (@na_alloc Σ na_invg) as (pool_d) "_".
  iDestruct (big_sepL2_nth_l _ _ _ pool_d with "Hps") as "Hps".
  (* Their exit parts and the scheduler's state, at [True] for now; one
     default, also the context-switch thread's exit part. *)
  iMod (saved_prop_alloc True%I (DfracOwn 1)) as (γd) "_"; first done.
  iMod (alloc_thread_names (λ γ, saved_prop_own γ (DfracOwn 1) True%I) γd (length vs)
          (saved_prop_alloc True%I (DfracOwn 1) ltac:(done))) as (γs) "Hexits".
  iMod (saved_prop_alloc True%I (DfracOwn 1)) as (γsched) "Hsched"; first done.
  (* The context-switch thread: its pool; the names of the postures, whose
     MTCC one-shot [cerise_ghost_init] consumes; its mtdc token, at home
     at zero. *)
  iMod (@na_alloc Σ na_invg) as (pool_c) "Hna".
  iMod (@posture_init Σ (@cerise_preG_excl Σ cerise_preg) (@cerise_preG_oneshot Σ cerise_preg)
          na_invg) as (postureg) "(Hcrit & Hunw & Hpending)".
  iMod (@mtdc_lent_init Σ (@cerise_preG_excl Σ cerise_preg)
          (ExceptionScratch (lword_of_word (WInt 0)))) as (mlg Hhome) "Hlent".
  pose cerise_na_invs := Build_cerise_na_invs _ na_invg pool_c.
  (* The heaps, its PC, mtdc and MIE, MPIE: [cerise_state_interp σ]. *)
  iMod (cerise_ghost_init σ H (ExceptionScratch (lword_of_word (WInt 0))) (WInt 0)
          Hinit Hmtdc eq_refl Hhome with "Hpending")
    as (mem_heapg shadow_heapg pc_g reg_heapg sreg_heapg registryg addr_allocg mtdcg mieg mpieg
        hwmg)
       "(Hσ & HPC & Hreg & Hmtdc & Hmem & Hshadow & Hclaims & Hmst & Hmepcc & Hmcause & Hmtval &
         Hhwm_ctx)".
  iDestruct "Hhwm_ctx" as
    "(%zb & %zh & [%Hzb %Hzh] & Hmshwmb & Hmshwm & Hpend_cl & Hpend_f & Hlent_f & Hlast_owner_a & Hlast_owner_f & _)".
  iDestruct "Hmst" as (mie0 mpie0 Hmst) "[HMIE HMPIE]".
  iDestruct "Hmepcc" as (vepcc) "Hmepcc".
  iDestruct "Hmcause" as (vcause) "Hmcause".
  iDestruct "Hmtval" as (ztval) "Hmtval".
  assert (mie_st σ = mie0) as Hmie0.
  { rewrite /mie_st /= in Hmst |- *. by rewrite Hmst /= mie_of_mstatus_enc. }
  iEval (rewrite init_lmem_pointsto_cond) in "Hmem".
  rewrite (init_lregs_cnull (reg σ) Hnull).
  (* [cur], the running thread and the switch window. *)
  iMod (cur_alloc None) as (γcur) "[Hcur_a Hcur_f]".
  iMod (ghost_var_alloc CtxSwitch) as (γrun) "[Hrun_a Hrun_f]".
  iMod (ghost_var_alloc false) as (γwin) "[Hwin_a Hwin_f]".
  pose (ceriseb := {|
    cb_invG := Hinv;
    cb_na_invG := na_invg;
    cb_mem := mem_heapg;
    cb_shadow := shadow_heapg;
    cb_sreg := sreg_heapg;
    cb_registry := registryg;
    cb_addr_alloc := addr_allocg;
    cb_trapVector := TV;
    cb_mpie := mpieg;
    cb_posture := postureg;
    cb_pc_of th := match th with CtxSwitch => pc_g | UserThread t => (nth t gs gd).1.1.1.1 end;
    cb_regs_of th := match th with
                     | CtxSwitch => reg_heapg | UserThread t => (nth t gs gd).1.1.1.2 end;
    cb_mtdc_of th := match th with CtxSwitch => mtdcg | UserThread t => (nth t gs gd).1.1.2 end;
    cb_mie_of th := match th with CtxSwitch => mieg | UserThread t => (nth t gs gd).1.2 end;
    cb_mtdc_lent_of th := match th with CtxSwitch => mlg | UserThread t => (nth t gs gd).2 end;
    cb_hwm_of th := match th with CtxSwitch => hwmg | UserThread t => nth t hs hd end;
    tpool th := match th with CtxSwitch => pool_c | UserThread t => nth t ps pool_d end;
    cb_cur_inG := cur_preg;
    cb_cur_name := γcur;
    cb_saved_prop := saved_preg;
    γ_exit th := match th with CtxSwitch => γd | UserThread t => nth t γs γd end;
    γ_scheduler := γsched;
    cb_running_inG := running_preg;
    γ_running := γrun;
    cb_resume_window_inG := window_preg;
    γ_resume_window := γwin |}).
  (* The home values of the user threads' mtdc tokens. *)
  assert (∀ t, t < length vs →
            mtdc_home_at (ceriseb := ceriseb) (th := UserThread t) = tstack_home t)
    as Hhomes.
  { intros t Ht. destruct (lookup_lt_is_Some_2 vs t Ht) as [v Hv].
    exact (Hhomes_g t v Hv). }
  assert (∀ t, ∃ p b e a, mtdc_home_at (ceriseb := ceriseb) (th := UserThread t) = TStack p b e a)
    as Htstack.
  { intros t. destruct (decide (t < length vs)) as [Ht|Ht].
    - rewrite (Hhomes t Ht) /tstack_home. by eexists _, _, _, _.
    - assert (mtdc_home_at (ceriseb := ceriseb) (th := UserThread t) = tstack_home (length vs))
        as ->.
      { change (mtdc_home_at (ceriseb := ceriseb) (th := UserThread t)) with
          (@mtdc_home Σ (nth t gs gd).2).
        rewrite nth_overflow; last lia. exact Hhome_d. }
      rewrite /tstack_home. by eexists _, _, _, _. }
  (* The exit part of each user thread, set and persisted. *)
  iAssert (|==> [∗ list] t ↦ _ ∈ vs,
            @saved_prop_own Σ (@cb_saved_prop Σ ceriseb) (γ_exit (UserThread t))
              DfracDiscarded (exit_concrete (ceriseb := ceriseb) (th := UserThread t)))%I
    with "[Hexits]" as ">Hexits".
  { iApply big_sepL_bupd.
    iApply (big_sepL_seq_index (λ t, |==> @saved_prop_own Σ (@cb_saved_prop Σ ceriseb)
              (γ_exit (UserThread t)) DfracDiscarded
              (exit_concrete (ceriseb := ceriseb) (th := UserThread t)))%I vs).
    iApply (big_sepL_impl with "Hexits"). iIntros "!>" (k t _) "Hexit".
    iMod (saved_prop_update (exit_concrete (ceriseb := ceriseb) (th := UserThread t))
            with "Hexit") as "Hexit".
    iApply (saved_prop_persist with "Hexit"). }
  (* The user threads' ghost state, at the base. *)
  iAssert ([∗ list] t ↦ v ∈ vs, suspended_res (ceriseb := ceriseb) t v)%I
    with "[Hgs Hhs Hps]" as "Hsusp".
  { iCombine "Hgs Hhs" as "Hgs". rewrite -big_sepL_sep.
    iCombine "Hgs Hps" as "Hgs". rewrite -big_sepL_sep.
    iApply (big_sepL_impl with "Hgs"). iIntros "!>" (t v Hv) "[ [Hg Hh] Hp]".
    iDestruct "Hg" as "(HPCa & HPCf & Hra & Hrf & Hma & Hmf & HMa & HMf & Hl)".
    iDestruct "Hh" as "(Hba & Hbf & Hha & Hhf & Hza & Hzt & Hrest & #Hbase)".
    assert (t < length vs) as Ht by (by eapply lookup_lt_Some).
    pose proof (Forall_lookup_1 _ _ _ _ Hcov Hv) as Hcov_t.
    rewrite /suspended_res /auths_at /thread_auths (Hhomes t Ht).
    iFrame "HPCa Hra Hma HMa Hba Hha Hza Hrest HPCf Hrf Hmf HMf Hbf Hhf Hzt Hl Hp Hbase".
    by iPureIntro. }
  (* The hardware's state interpretation, at the context-switch thread. *)
  subst mie0. iEval (rewrite Hmie) in "HMIE".
  iAssert (SI_hw (ceriseb := ceriseb) σ)%I with "[Hσ Hrun_a Hwin_a Hpend_cl]" as "HSI".
  { rewrite /SI_hw. iExists CtxSwitch. iFrame "Hrun_a". iSplitL "Hwin_a".
    { iExists false. iFrame "Hwin_a". by iPureIntro. }
    iSplitL; last done.
    rewrite /thread_si. iFrame "Hσ".
    iSplitR; first done.
    iSplitR; first by iApply csl_full_link_disabled.
    iSplitR; first by iLeft.
    iExists None. by iFrame "Hpend_cl". }
  (* The high-water-mark resources of the context-switch thread. *)
  iAssert (hwm_res_ctx (ceriseb := ceriseb) (th := CtxSwitch))%I
    with "[Hmshwmb Hmshwm Hpend_f Hlent_f Hlast_owner_f]" as "Hhwm_ctx".
  { iExists zb, zh, None. iFrame "Hmshwmb Hmshwm Hpend_f Hlent_f Hlast_owner_f". }
  (* The first stage: the slots and the flag's invariant. *)
  iMod (Hwp ceriseb eq_refl Hhome Htstack Hhomes
          with "HPC Hreg Hmtdc HMIE [Hcrit Hunw Hmepcc Hmcause Hmtval HMPIE] Hlent Hhwm_ctx Hna
                Hmem Hshadow Hclaims Hsusp Hexits Hsched")
    as "(Hslots & #Hflag & Hwp)".
  { iApply (handover_res_intro vepcc vcause ztval mpie0). iFrame. }
  (* The second stage: the pool, the context-switch thread's open pool
     token and its thread resources give the hardware's WP. *)
  iMod (pool_inv_alloc (ceriseb := ceriseb) vs with "Hcur_a Hlast_owner_a Hslots") as "#Hpool".
  iMod (inv_CtxSwitch_alloc (ceriseb := ceriseb) with "Hcur_f") as "#Hact".
  iMod ("Hwp" with "Hpool Hact [Hrun_f Hwin_f]") as "Hwp".
  { iApply (thread_res_ctx_intro (ceriseb := ceriseb) with "Hrun_f Hwin_f"). }
  (* [stateI] is [SI_hw]: the instance of [wp_invariance_hw] is then
     [hw_irisGS], by conversion. *)
  iModIntro. iExists (λ σ _ _, SI_hw (ceriseb := ceriseb) σ), (λ _, True%I).
  iFrame "HSI". iSplitL "Hwp"; first iExact "Hwp".
  iIntros "HSI'". iApply (flag_from_SI_hw (ceriseb := ceriseb) with "Hflag HSI'").
Qed.
End flag_adequacy.
