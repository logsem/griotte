From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import fundamental.
From griotte Require Import switcher_call_states switch_csp_check switch_entry_first_spill.
From griotte Require Import common_force_unwind switcher_call_world switcher_registers.
From griotte Require Import context_switching_support context_switching_hyps.
From griotte Require Import virtualise context_switching_wedge context_switching_specs.

(** * The switcher's call sentry and the scheduler's entry at the
      context-switch thread

    The context-switch thread holds zero in mtdc: a call through the
    switcher's call sentry faults at the latest at the dereference of that
    zero, before it enables interrupts and before any world step, and the
    fault goes to the trap vector. The scheduler's entry and globals are
    valid in every world from their validity in one world. *)

Section ctx_scheduler_valid.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** From [switcher_after_compartment_call] at the context-switch thread:
      [ctp] receives mtdc's zero, and the load of the hazard slots through
      it faults. *)
  #[local] Lemma ctx_after_call_fault (wctp wct2 : LWord) :
    PC ↦ₚ[CtxSwitch] switcher_label_pc "switcher_after_compartment_call" ∗
    ctp ↦ᵣ[CtxSwitch] wctp ∗
    ct2 ↦ᵣ[CtxSwitch] wct2 ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    switcher_code_at CtxSwitch ∗
    (∀ w : LWord,
       ctp ↦ᵣ[CtxSwitch] lword_of_word (WInt 0) -∗
       ct2 ↦ᵣ[CtxSwitch] wct2 -∗
       mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) -∗
       trap_safe w ⊤ (HO CtxSwitch))
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros "(HPC & Hctp & Hct2 & Hmtdc & #Hswitcher & Hcont)".
    pin_thread_instances CtxSwitch.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_ret Ha_ret.
    (* SpecialRW ctp mtdc cnull *)
    iInstrStart "Hcode".
    iInstrApply (wp_readsr_mtdc _ _ _ _ _ _ _ _ _ ctp wctp
                   (ExceptionScratch (lword_of_word (WInt 0))))
      with "[$HPC $Hctp $Hmtdc]" as (vm) "(%Hmatch & HPC & Hctp & Hmtdc)".
    cbn in Hmatch; subst vm.
    (* CLoad ct2 ctp TrustedStack_offset_hazardPointers *)
    iInstrStart "Hcode".
    iInstrApply (wp_load_fail_not_cap_imm _ ct2 ctp) with "[$HPC $Hct2 $Hctp]"
      as "(HPC & Hct2 & Hctp)".
    { done. }
    iDestruct ("Hcont" with "Hctp Hct2 Hmtdc") as "Hts".
    iTrap.
  Qed.

  (** From [.Lswitch_trusted_stack_load] at the context-switch thread: [ct2]
      receives mtdc's zero, and the load of the hazard slots through it
      faults. *)
  #[local] Lemma ctx_tstack_load_fault (wct2 wctp : LWord) :
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lswitch_trusted_stack_load" ∗
    ct2 ↦ᵣ[CtxSwitch] wct2 ∗
    ctp ↦ᵣ[CtxSwitch] wctp ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    switcher_code_at CtxSwitch ∗
    (∀ w : LWord,
       ct2 ↦ᵣ[CtxSwitch] lword_of_word (WInt 0) -∗
       ctp ↦ᵣ[CtxSwitch] wctp -∗
       mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) -∗
       trap_safe w ⊤ (HO CtxSwitch))
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros "(HPC & Hct2 & Hctp & Hmtdc & #Hswitcher & Hcont)".
    pin_thread_instances CtxSwitch.
    switcher_open_label ".Lswitch_trusted_stack_load" "Hswitcher" as "Hcode" a_load Ha_load.
    (* SpecialRW ct2 mtdc cnull *)
    iInstrStart "Hcode".
    iInstrApply (wp_readsr_mtdc _ _ _ _ _ _ _ _ _ ct2 wct2
                   (ExceptionScratch (lword_of_word (WInt 0))))
      with "[$HPC $Hct2 $Hmtdc]" as (vm) "(%Hmatch & HPC & Hct2 & Hmtdc)".
    cbn in Hmatch; subst vm.
    (* CLoad ctp ct2 TrustedStack_offset_hazardPointers *)
    iInstrStart "Hcode".
    iInstrApply (wp_load_fail_not_cap_imm _ ctp ct2) with "[$HPC $Hctp $Hct2]"
      as "(HPC & Hctp & Hct2)".
    { done. }
    iDestruct ("Hcont" with "Hct2 Hctp Hmtdc") as "Hts".
    iTrap.
  Qed.

  (** From [.Lcommon_force_unwind] at the context-switch thread: the
      return values are set, and the return routine faults at mtdc's
      zero. *)
  #[local] Lemma ctx_force_unwind_fault (wca0 wca1 wctp wct2 : LWord) :
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lcommon_force_unwind" ∗
    ca0 ↦ᵣ[CtxSwitch] wca0 ∗
    ca1 ↦ᵣ[CtxSwitch] wca1 ∗
    ctp ↦ᵣ[CtxSwitch] wctp ∗
    ct2 ↦ᵣ[CtxSwitch] wct2 ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    switcher_code_at CtxSwitch ∗
    (∀ w : LWord,
       ca0 ↦ᵣ[CtxSwitch] lword_of_word (WInt ECOMPARTMENTFAIL) -∗
       ca1 ↦ᵣ[CtxSwitch] lword_of_word (WInt 0) -∗
       ctp ↦ᵣ[CtxSwitch] lword_of_word (WInt 0) -∗
       ct2 ↦ᵣ[CtxSwitch] wct2 -∗
       mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) -∗
       trap_safe w ⊤ (HO CtxSwitch))
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros "(HPC & Hca0 & Hca1 & Hctp & Hct2 & Hmtdc & #Hswitcher & Hcont)".
    pin_thread_instances CtxSwitch.
    iApply (common_force_unwind_spec (th := CtxSwitch) with "[- $HPC $Hca0 $Hca1 $Hswitcher]").
    iIntros "!> (HPC & Hca0 & Hca1)".
    iApply (ctx_after_call_fault with "[$HPC $Hctp $Hct2 $Hmtdc $Hswitcher Hca0 Hca1 Hcont]").
    iIntros (w) "Hctp Hct2 Hmtdc".
    iApply ("Hcont" with "Hca0 Hca1 Hctp Hct2 Hmtdc").
  Qed.

  (** The call through the switcher's call sentry at the context-switch
      thread faults, and the fault goes to the trap vector. *)
  #[local] Lemma interp_expr_switcher_call_ctx (W : WORLD) (C : CmptName) :
    ctx_trap_vector_safe ∗
    switcher_code_at CtxSwitch
    ⊢ interp_expr_at (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full)
        InterruptDisabled (interp (th := CtxSwitch))
        (interp_cont (th := CtxSwitch) (interp (th := CtxSwitch))) W C
        (Cap XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "[#Htrap #Hswitcher] %cstk %Ws %Cs %regs
      (_ & _ & Hregs & _ & HPC & Hrmap & Hworld_res & _ & _ & Hna & Hcstk & _ & _ & Hmie & Hheld)".
    iDestruct "Hregs" as "[%Hfull_rmap #Hreg]".
    pin_thread_instances CtxSwitch.
    iEval (rewrite held_disabled) in "Hheld".
    iDestruct "Hheld" as "(Hho & Hmtdc & Hlent)".

    (* The registers of the call path, and the return values *)
    destruct (Hfull_rmap ca0) as [wca0 Hwca0].
    destruct (Hfull_rmap ca1) as [wca1 Hwca1].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca0 with "Hrmap")
      as "[Hca0 Hrmap]"; first exact Hwca0.
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca1 with "Hrmap")
      as "[Hca1 Hrmap]"; first by rewrite lookup_delete_ne.
    destruct (Hfull_rmap csp) as [wcsp Hwcsp].
    destruct (Hfull_rmap ct2) as [wct2 Hwct2].
    destruct (Hfull_rmap ctp) as [wctp Hwctp].
    destruct (Hfull_rmap cs0) as [wcs0 Hwcs0].
    destruct (Hfull_rmap cs1) as [wcs1 Hwcs1].
    destruct (Hfull_rmap cra) as [wcra Hwcra].
    destruct (Hfull_rmap cgp) as [wcgp Hwcgp].
    destruct (Hfull_rmap ct1) as [wct1 Hwct1].
    iDestruct (call_regs_extract (th := CtxSwitch) (delete ca1 (delete ca0 regs)) with "Hrmap")
      as "(Hcsp & Hct2 & Hctp & Hcs0 & Hcs1 & Hcra & Hcgp & Hct1 & Hrmap)";
      [by rewrite !lookup_delete_ne..|].

    (* A fault goes to the trap vector, which is safe for any fault; the
       world's resources and the opened stack are dropped *)
    iAssert (∀ (w wcsp' wct2' wctp' wcs0' wcs1' wcra' wcgp' wct1' wca0' wca1' : LWord),
               csp ↦ᵣ[CtxSwitch] wcsp' -∗ ct2 ↦ᵣ[CtxSwitch] wct2' -∗
               ctp ↦ᵣ[CtxSwitch] wctp' -∗ cs0 ↦ᵣ[CtxSwitch] wcs0' -∗
               cs1 ↦ᵣ[CtxSwitch] wcs1' -∗ cra ↦ᵣ[CtxSwitch] wcra' -∗
               cgp ↦ᵣ[CtxSwitch] wcgp' -∗ ct1 ↦ᵣ[CtxSwitch] wct1' -∗
               ca0 ↦ᵣ[CtxSwitch] wca0' -∗ ca1 ↦ᵣ[CtxSwitch] wca1' -∗
               mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) -∗
               trap_safe w ⊤ (HO CtxSwitch))%I
      with "[Hrmap Hna Hcstk Hmie Hho Hlent]" as "Hfault".
    { iIntros (w wcsp' wct2' wctp' wcs0' wcs1' wcra' wcgp' wct1' wca0' wca1')
        "Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1 Hca0 Hca1 Hmtdc".
      iDestruct (call_regs_insert with "Hrmap Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1")
        as "Hrmap".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca1 with "Hca1 Hrmap")
        as "Hrmap".
      iDestruct (big_sepM_insert_2 (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ ca0 with "Hca0 Hrmap")
        as "Hrmap".
      iApply (interp_trap_safe (th := CtxSwitch) with "Htrap"); cycle 1.
      { iModIntro. iFrame "Hrmap Hna Hcstk". iSplitR; first by iRight.
        iExists InterruptDisabled. rewrite held_disabled. iFrame. done. }
      intros r. rewrite /call_regs_with !lookup_insert_is_Some'.
      destruct (decide (r = ca0)) as [|Hr0]; first naive_solver.
      destruct (decide (r = ca1)) as [|Hr1]; first naive_solver.
      rewrite !lookup_delete_ne //. naive_solver. }

    (* Is the stack pointer a valid stack capability, whose cursor is not
       above its top? *)
    iDestruct ("Hreg" $! csp with "[//]") as "#Hspv".
    iEval (rewrite -switcher_call_entry_label) in "HPC".
    iAssert (⌜(∃ b e a, wcsp = Cap RWL Local b e a ∧ (b < e)%a ∧ (a <= e)%a)
            ∨ (∀ b e a, wcsp.(lw) = Cap RWL Local b e a → (e <= b)%a ∨ (e < a)%a)⌝)%I
      as %[(b & e & a & -> & Hbe & Hae) | Hnot_stk].
    { destruct wcsp as [ [| [t p g b e a|] | |] π]; try (iPureIntro; right; intros; discriminate).
      destruct t; [|iPureIntro; right; intros; discriminate].
      destruct (decide (p = RWL ∧ g = Local)) as [ [-> ->] | Hpg].
      - destruct (decide (b < e ∧ a <= e)%a) as [ [Hbe Hae] | Hbae].
        + iDestruct (interp_wl_noid with "Hspv") as %->; [done|solve_addr|].
          iPureIntro; left; by eexists _, _, _.
        + iPureIntro; right; intros ??? Heq; inversion Heq; subst; solve_addr.
      - iPureIntro; right; intros ??? Heq; inversion Heq; subst; tauto. }
    - (* A valid stack: the spill faults when it does not fit; otherwise the
         read of mtdc's zero, at [.Lswitch_trusted_stack_load], faults *)
      iDestruct (interp_cap_disjoint_wl with "Hspv") as %[Hstk_mmio _]; first done.
      iDestruct (world_resources_split with "Hworld_res") as "[Hlocal _]".
      iDestruct (local_call_stk_open _ _ b e a (stk_free_b b a) (stk_free_e e a)
                  with "Hspv Hlocal")
        as (lv) "(Hstk & _)"; [rewrite /stk_free_b; solve_addr | exact Hae |].
      iApply (switch_csp_check_spec (th := CtxSwitch)
               with "[- $HPC $Hcsp $Hct2 $Hctp $Hswitcher]").
      iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp) | (%Hcontra & _)]";
        last (exfalso; apply Hcontra, switcher_csp_checked_stk).
      iApply (switch_entry_first_spill_spec (th := CtxSwitch)
               with "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hcsp $Hstk $Hswitcher]");
        [exact Hstk_mmio | exact Hae |].
      iSplit.
      + iIntros "!> (HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & _)".
        iApply (ctx_tstack_load_fault with "[- $HPC $Hct2 $Hctp $Hmtdc $Hswitcher]").
        iIntros (w) "Hct2 Hctp Hmtdc".
        iApply ("Hfault" with "Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1 Hca0 Hca1 Hmtdc").
      + iIntros (_) "(Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & _)".
        iApply ("Hfault" with "Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1 Hca0 Hca1 Hmtdc").
    - (* Not a valid stack: is the furthest cell of the spill within its
         bounds? *)
      iAssert (⌜(∃ b e a, wcsp = Cap RWL Local b e a ∧
                          stk_spill_ok a ∧ stk_spill_a a ∈ₐ [b, e))
             ∨ (∀ b e a a4, wcsp.(lw) = Cap RWL Local b e a →
                            (a + (SpillSlot_cs0 - SpillSlot_size))%a = Some a4 →
                            (a4 < b)%a ∨ (e <= a4)%a)⌝)%I
        as %[(b & e & a & -> & Ha4 & Ha4_in) | Hfirst].
      { destruct wcsp as [ [| [t p g b e a|] | |] π]; try (iPureIntro; right; intros; discriminate).
        destruct t; [|iPureIntro; right; intros; discriminate].
        destruct (decide (p = RWL ∧ g = Local)) as [ [-> ->] | Hpg]; cycle 1.
        { iPureIntro; right; intros ???? Heq; inversion Heq; subst; tauto. }
        destruct (a + (SpillSlot_cs0 - SpillSlot_size))%a as [a4|] eqn:Ha4; cycle 1.
        { iPureIntro; right; intros ???? Heq Ha4'; inversion Heq; subst. congruence. }
        destruct (decide (a4 ∈ₐ [b, e))) as [Ha4_in|Ha4_out]; cycle 1.
        { iPureIntro; right; intros ???? Heq Ha4'; inversion Heq; subst.
          rewrite Ha4 in Ha4'; simplify_eq; solve_addr. }
        iDestruct (interp_wl_noid with "Hspv") as %->; [done|solve_addr|].
        iPureIntro; left; exists b, e, a; split; first done.
        stk_unfold. split; solve_addr. }
      + (* The cursor is above the top, and the furthest cell within bounds:
           the store at the top faults *)
        destruct (Hnot_stk b e a eq_refl) as [Heb|Hea];
          first (revert Ha4_in; stk_unfold; solve_addr).
        iDestruct (interp_cap_disjoint_wl with "Hspv") as %[Hstk_mmio _]; first done.
        iDestruct (world_resources_split with "Hworld_res") as "[Hlocal _]".
        iDestruct (local_call_stk_open _ _ b e a (stk_spill_a a) e with "Hspv Hlocal")
          as (lv) "(Hstk & _)"; [solve_addr | solve_addr |].
        iApply (switch_csp_check_spec (th := CtxSwitch)
                 with "[- $HPC $Hcsp $Hct2 $Hctp $Hswitcher]").
        iNext; iIntros "[(_ & HPC & Hcsp & Hct2 & Hctp) | (%Hcontra & _)]";
          last (exfalso; apply Hcontra, switcher_csp_checked_stk).
        iApply (switch_entry_first_spill_above_spec (th := CtxSwitch)
                 with "[- $HPC $Hcsp $Hcs0 $Hcs1 $Hcgp $Hcra $Hstk $Hswitcher]");
          [exact Hstk_mmio | done..|].
        iIntros (k off _ _) "(Hcsp & Hcs0 & Hcs1 & Hcgp & Hcra & _)".
        iApply ("Hfault" with "Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1 Hca0 Hca1 Hmtdc").
      + (* The checks fail and the return routine faults at mtdc's zero, or
           the first store faults *)
        iApply (switch_csp_check_spec (th := CtxSwitch)
                 with "[- $HPC $Hcsp $Hct2 $Hctp $Hswitcher]").
        iNext; iIntros "[(%Hchecked & HPC & Hcsp & Hct2 & Hctp)
                        | (_ & %zct2 & %zctp & HPC & Hcsp & Hct2 & Hctp)]".
        * iApply (switch_entry_first_spill_fail_spec (th := CtxSwitch)
                   with "[- $HPC $Hcsp $Hcs0 $Hswitcher]"); [done | done |].
          iIntros "[Hcsp Hcs0]".
          iApply ("Hfault" with "Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1 Hca0 Hca1 Hmtdc").
        * iApply (ctx_force_unwind_fault
                   with "[- $HPC $Hca0 $Hca1 $Hctp $Hct2 $Hmtdc $Hswitcher]").
          iIntros (w) "Hca0 Hca1 Hctp Hct2 Hmtdc".
          iApply ("Hfault" with "Hcsp Hct2 Hctp Hcs0 Hcs1 Hcra Hcgp Hct1 Hca0 Hca1 Hmtdc").
  Qed.

  (** The switcher's call sentry is valid at the context-switch thread:
      the call path faults at the latest at the dereference of mtdc's zero,
      before it enables interrupts and before any world step; the fault goes
      to the context-switch thread's trap vector. *)
  Lemma interp_switcher_call_ctx (W : WORLD) (C : CmptName) :
    codefrag_pers (ceriseg := ceriseG_of CtxSwitch) a_switcher_call switcher_instrs ∗
    ctx_trap_vector_safe
    ⊢ interp (th := CtxSwitch) (CL := crit_link_full) (CR := crit_route_full) W C
        switcher_entry_call.
  Proof.
    iIntros "[#Hswitcher #Htrap]".
    rewrite interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    (* An interrupt-disabling sentry *)
    iSplit; last (iPureIntro; done).
    iIntros "!> %W' %Hrelated %g' %Hflows".
    destruct g'; first done.
    iIntros (m); cbn [default sentry_kind_mie].
    iNext; iApply (interp_expr_switcher_call_ctx with "[$Htrap $Hswitcher]").
  Qed.

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
