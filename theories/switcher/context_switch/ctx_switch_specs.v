From iris.proofmode Require Import proofmode.
From griotte Require Import logrel switcher_preamble virtualise.
From griotte Require Import context_switch_layout_instance ctx_support.
From griotte Require Import ctx_hyps.
From griotte Require Import ctx_scheduler_call ctx_resume.
From griotte Require Import ctx_exit.

(** * The entry specs of the context-switch thread

    The entry specs of the context-switch thread hold for the switcher,
    and [virtualise] holds with them. *)

Section ctx_switch_specs.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    (C_sched : CmptName) (w_pcc w_cgp w_csp : LWord).

  (** The entry specs of the context-switch thread hold for the switcher,
      for the user threads [ts]: at least one, without duplicates, exactly
      those below the layout's number of threads; their mtdc homes their
      trusted stacks, the context-switch thread's 0; the context-switch
      thread runs in the scheduler's compartment [C_sched]; the pool and
      the open pool token of the context-switch thread are invariants; the
      switcher's static facts for every thread; the scheduler's words, its
      state between activations as a saved proposition, the validity of
      its entry and globals; and the safety of the context-switch thread's
      trap vector. *)
  Theorem ctx_switch_entry_specs_hold (ts : list nat) :
    ts ≠ [] →
    NoDup ts →
    (∀ B, B ∈ ts ↔ B < swl_nthreads) →
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    (∀ B, B ∈ ts → mtdc_home_at (th := UserThread B) = tstack_home B) →
    CtxSwitch ∈ cmpt_threads C_sched →
    inv Npool (Pool ts) -∗
    inv_CtxSwitch -∗
    ([∗ list] B ∈ ts, switcher_static (th := UserThread B)) -∗
    scheduler_words w_pcc w_cgp w_csp -∗
    saved_prop_own γ_scheduler DfracDiscarded (scheduler_concrete C_sched w_csp) -∗
    scheduler_entry_valid C_sched w_pcc w_cgp -∗
    ctx_trap_vector_safe -∗
    □ ctx_switch_entry_specs (CL := crit_link_full) (CR := crit_route_full).
  Proof.
    iIntros (Hne Hnd Hts Hhome_ctx Hhomes Hsched_in)
      "#Hpool #Hact #Hstatic #Hwords #Hsched #Hentry #Htrap".
    iAssert (ctx_switch_env C_sched w_pcc w_cgp w_csp ts) as "#Henv".
    { rewrite /ctx_switch_env. iFrame "#%". }
    iDestruct (ctx_resume_specs_hold C_sched w_pcc w_cgp w_csp ts Hne with "Henv") as "#Hres".
    iIntros "!>" (t k v) "Hpre".
    destruct k as [|b p|].
    - iApply (ctx_switch_entry_irq_spec C_sched w_pcc w_cgp w_csp ts t v with "Henv Hres Hpre").
    - iApply (ctx_switch_entry_yield_spec C_sched w_pcc w_cgp w_csp ts t b p v
                with "Henv Hres Hpre").
    - iApply (ctx_switch_entry_exit_spec C_sched w_pcc w_cgp w_csp ts t v with "Henv Hres Hpre").
  Qed.

  (** The hardware runs safely from the running thread's safe run, for the
      switcher: [virtualise], with the entry specs of the context-switch
      thread given by [ctx_switch_entry_specs_hold]. *)
  Theorem virtualise_switcher (ts : list nat) (th : Thread)
      (e : thread_langs.expr (kind_of th)) (k : nat) :
    ts ≠ [] →
    NoDup ts →
    (∀ B, B ∈ ts ↔ B < swl_nthreads) →
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    (∀ t, ∃ p b e' a, mtdc_home_at (th := UserThread t) = TStack p b e' a) →
    (∀ B, B ∈ ts → mtdc_home_at (th := UserThread B) = tstack_home B) →
    CtxSwitch ∈ cmpt_threads C_sched →
    k ≤ 2 →
    wellshaped e →
    k = 0 ∨ thread_langs.to_val e = None →
    inv Npool (Pool ts) -∗
    inv_CtxSwitch -∗
    ([∗ list] B ∈ ts, switcher_static (th := UserThread B)) -∗
    scheduler_words w_pcc w_cgp w_csp -∗
    saved_prop_own γ_scheduler DfracDiscarded (scheduler_concrete C_sched w_csp) -∗
    scheduler_entry_valid C_sched w_pcc w_cgp -∗
    ctx_trap_vector_safe -∗
    thread_res th e -∗
    ▷^k WP e @[th] {{ HO th }} -∗
    WP_hw (hw_of e) {{ _, True }}.
  Proof.
    iIntros (Hne Hnd Hts Hhome_ctx Hus Hhomes Hsched_in Hk Hws Hkv)
      "#Hpool #Hact #Hstatic #Hwords #Hsched #Hentry #Htrap Htr Hwp".
    iDestruct (ctx_switch_entry_specs_hold ts Hne Hnd Hts Hhome_ctx Hhomes Hsched_in
                 with "Hpool Hact Hstatic Hwords Hsched Hentry Htrap") as "#Hspecs".
    iApply (virtualise (CL := crit_link_full) (CR := crit_route_full)
              (CSL := context_switch_layout_full) ts th e k Hnd Hhome_ctx Hus Hk Hws Hkv
              with "Hpool Hspecs Htr Hwp").
  Qed.
End ctx_switch_specs.
