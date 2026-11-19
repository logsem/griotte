From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import fundamental switcher_preamble.
From griotte Require Import context_switching_support context_switching_hyps.
From griotte Require Import virtualise context_switching_wedge context_switching_specs.

(** * The scheduler's entry at the context-switch thread

    The scheduler's entry and globals are valid in every world from their
    validity in one world. *)

Section ctx_scheduler_valid.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** The scheduler's entry and globals are valid in every world, from
      the validity in one world of its code capability, under which its
      entry is a Global sentry that does not enable interrupts, and of its
      globals, which are not Local. *)
  Lemma scheduler_entry_valid_intro (C_sched : CmptName) (w_pcc w_cgp : LWord) (W : WORLD)
      (sk : SentryKind) (p : Perm) (b e a b' e' a' : Addr) :
    w_pcc = lword_of_word (Sentry sk p Global b' e' a') →
    not_heap_range b' e' →
    isO p = false →
    (b <= b')%a →
    (e' <= e)%a →
    sentry_kind_mie sk ≠ Some InterruptEnabled →
    isLocalWord w_cgp.(lw) = false →
    interp (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full) W C_sched
      (lword_of_word (Cap p Global b e a)) -∗
    interp (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full) W C_sched w_cgp -∗
    scheduler_entry_valid C_sched w_pcc w_cgp.
  Proof.
    iIntros (-> Hnh HnO Hb He Hmie Hcgp) "#Hcap #Hcgp_v".
    rewrite /scheduler_entry_valid.
    iIntros "!>" (W').
    iSplit.
    - iApply (interp_global_world_free (th := CtxSwitch) W W'); first done.
      iApply (interp_weakeningSentry (th := CtxSwitch) W C_sched sk true p Global Global
                b b' e e' a a' with "[] Hcap"); [done | done | done | done | done | |].
      { intros Hk. by destruct Hmie. }
      iModIntro. iNext. iApply fundamental_all_threads.
    - iApply (interp_global_world_free (th := CtxSwitch) W W' with "Hcgp_v"). exact Hcgp.
  Qed.

  (** [virtualise] at the switcher, with the context-switch thread's trap
      vector proved and the scheduler's entry reduced to the validity of
      its code capability and globals in one world. *)
  Theorem virtualise_scheduler (C_sched : CmptName) (w_pcc w_cgp w_csp : LWord)
      (ts : list nat) (th : Thread) (e : thread_langs.expr (kind_of th)) (k : nat)
      (W : WORLD) (sk : SentryKind) (p_c : Perm) (b_c e_c a_c b_s e_s a_s : Addr) :
    ts ≠ [] →
    NoDup ts →
    (∀ B, B ∈ ts ↔ B < swl_nthreads) →
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    (∀ t, ∃ p b e' a, mtdc_home_at (th := UserThread t) = TStack p b e' a) →
    (∀ B, B ∈ ts → mtdc_home_at (th := UserThread B) = tstack_home B) →
    CtxSwitch ∈ cmpt_threads C_sched →
    w_pcc = lword_of_word (Sentry sk p_c Global b_s e_s a_s) →
    not_heap_range b_s e_s →
    isO p_c = false →
    (b_c <= b_s)%a →
    (e_s <= e_c)%a →
    sentry_kind_mie sk ≠ Some InterruptEnabled →
    isLocalWord w_cgp.(lw) = false →
    k ≤ 2 →
    wellshaped e →
    k = 0 ∨ thread_langs.to_val e = None →
    inv Npool (Pool ts) -∗
    inv_CtxSwitch -∗
    ([∗ list] B ∈ ts, switcher_static (th := UserThread B)) -∗
    scheduler_words w_pcc w_cgp w_csp -∗
    saved_prop_own γ_scheduler DfracDiscarded (scheduler_concrete C_sched w_csp) -∗
    interp (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full) W C_sched
      (lword_of_word (Cap p_c Global b_c e_c a_c)) -∗
    interp (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full) W C_sched w_cgp -∗
    thread_res th e -∗
    ▷^k WP e @[th] {{ HO th }} -∗
    WP_hw (hw_of e) {{ _, True }}.
  Proof.
    iIntros (Hne Hnd Hts Hhome_ctx Hus Hhomes Hsched_in Hpcc Hnh HnO Hb He Hmie Hcgp Hk Hws Hkv)
      "#Hpool #Hact #Hstatic #Hwords #Hsched #Hcap #Hcgp_v Htr Hwp".
    (* The switcher's code and trap vector, from the head of [ts] *)
    destruct ts as [|B ts']; first done.
    iDestruct (big_sepL_lookup _ _ 0 B with "Hstatic") as "HB"; first done.
    iEval (rewrite /switcher_static) in "HB". iNamed "HB".
    iEval (rewrite (codefrag_pers_thread_indep (UserThread B) CtxSwitch)) in "Hswitcher_code".
    iPoseProof (ctx_trap_vector_safe_holds Hmtcc_vec with "Hswitcher_code") as "#Htrap".
    iPoseProof (scheduler_entry_valid_intro C_sched w_pcc w_cgp W sk p_c b_c e_c a_c b_s e_s a_s
                  Hpcc Hnh HnO Hb He Hmie Hcgp with "Hcap Hcgp_v") as "#Hentry".
    iApply (virtualise_switcher C_sched w_pcc w_cgp w_csp (B :: ts') th e k Hne Hnd Hts Hhome_ctx
              Hus Hhomes Hsched_in Hk Hws Hkv
              with "Hpool Hact Hstatic Hwords Hsched Hentry Htrap Htr Hwp").
  Qed.

End ctx_scheduler_valid.
