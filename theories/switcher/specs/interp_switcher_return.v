From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base list_relations.
From griotte Require Export logrel monotone.
From griotte Require Import fundamental.
From griotte Require Import switcher_preamble.
From griotte Require Import switcher_return_states.
From griotte.switcher.callback Require Import callback_path.
From griotte Require Import map_simpl register_tactics proofmode switcher_registers.
From griotte Require Export world_ghost_theory world_interp_stack switcher_helpers.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** Informal proof of the interp of the return-to-switcher entry point.
      When we call an adversary entry point, we first need to prove that it is safe (see [ot_switcher_interp]),
      which is defined by [ot_switcher_prop].
      Concretely, it means when the adversary starts the execution,
      it contains (among others) the return-to-switcher entry point,
      and so it must be safe-to-share.
      Because the entry point is a Sentry, we must prove that it is safe-to-execute.

      We initially start with a state where all the registers contain safe-to-share words,
      with a PC pointing to the the switcher's return address [a_switcher_return].
      We also have some call-stack [cstk] with the fragmental view [cstack_frag cstk].

      We extract the registers used in the code out of the map into individual resources.
      Only the return values [ca0] and [ca1] must be safe-to-share: this is all
      [switcher_return_unwind] asks of the register file, and safe-to-exec
      provides it, since all registers are then safe-to-share.
      We open the trusted-stack invariant, giving the points-to of the code region,
      allowing us to execute through the code.
      We obtain the authoritative view of the call-stack [cstack_full cstk'],
      which we can unify with [cstk].
      We obtain some current trusted stack address [a_tstk],
      which matches the size of the call-stack [cstk].

      To execute the code, we need to have the points-to resources of the top-most
      frame of the call stack:
      - the top-most address of the trusted stack
      - the 4 addresses of the callee-save registers area in the compartment's stack.

      We can distinguish 2 cases.
      1) The call-stack is empty: the frame to pop is the entry frame of
         the thread. The switcher exits the thread, and we close the
         trusted-stack invariant, which gives back [na_own (tpool th) ⊤].
      2) The call-stack is not empty,
         in which case we can derive information about the top-most frame
         with [cframe_interp].

      From now, we can (again) distinguish 2 cases
      (the Rocq proof combines them with a clever way to derive the points-to resources):
      1) If the caller was untrusted, the callee-save area is owned the caller,
         and the points-to are therefore in the world.
         We know that the only (untrusted) caller being able to call an untrusted callee
         has to be itself, so we have access to the right world (for the right compartment).
         In this case, we open the world, and obtain the points-to:
         theirs values don't have to be the ones stored in the (logical) call-frame,
         but we know that they are safe values
      2) If the caller was trusted, the callee-save area is owned by the switcher,
         and we know that their content has to be the one from the (logical) call-frame.

      From that point, the proof consists on executing the code,
      up-to the final jump.
      We update the call-stack (depop the topmost stack frame),
      and we can close the trusted-stack invariant.
      To finish the proof, we have to use a form of continuation.

      In the case of a trusted caller, we can finish the proof by using
      the continuation relation K.
      In the case of an untrusted caller, we finish by using the FTLR itself.
      We need, in particular, to close the world,
      which requires to massage the context.

   *)

  (* TODO: move to logrel/call_stack.v *)
  (** When every caller's stack starts at the base of the thread's stack, so
      does the floor. *)
  Lemma frames_hwm_floor_base (ef : trusted_frame) (frms : list cframe) :
    Forall (λ frm, cf_stk_b frm = tf_stk_b ef) frms →
    frames_hwm_floor ef frms = tf_stk_b ef.
  Proof.
    induction 1 as [|frm frms Hfrm _ IH]; first done.
    cbn. by destruct (is_untrusted_caller_frm frm).
  Qed.

  (* TODO: move to logrel/logrel.v *)
  (** The continuation records that every caller's stack starts at the base
      of the thread's stack. *)
  Lemma interp_cont_bases (ef : trusted_frame) (frms : list cframe)
    (Ws : list WORLD) (Cs : list CmptName) :
    interp_cont_aux interp ef frms Ws Cs ⊢
    interp_cont_aux interp ef frms Ws Cs ∗ ⌜Forall (λ frm, cf_stk_b frm = tf_stk_b ef) frms⌝.
  Proof.
    revert Ws Cs; induction frms as [|frm frms IH]; intros Ws Cs; first by iIntros "$".
    destruct Ws as [|Wt Ws], Cs as [|Ct Cs]; cbn; try by iIntros "[]".
    iIntros "[Hrest Hfrm]".
    iDestruct (IH with "Hrest") as "[$ %Hfrms]".
    destruct (is_known_to_known_frm frm).
    { iDestruct "Hfrm" as %Hb. iSplit; first done. iPureIntro. by constructor. }
    iDestruct "Hfrm" as "[Hcallee Hfrm]".
    destruct (is_untrusted_caller_frm frm).
    - iDestruct "Hfrm" as "(Htop & %Hzone & %Hb)". iFrame. iPureIntro.
      split_and!; [done|done|by constructor].
    - iDestruct "Hfrm" as "[%Hb Hexec]". iFrame. iPureIntro.
      split; [done|by constructor].
  Qed.

  (* TODO: move to logrel/logrel.v *)
  (** When MSHWM is at or above the base of the thread's stack, the weak
      continuation is the continuation: the return to an untrusted topmost
      caller, whose stack starts at that base, does not fault. *)
  Lemma interp_cont_weak_strong (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (h : Z) :
    (cstk_hwm_base cstk <= h)%Z →
    interp_cont_weak cstk Ws Cs h -∗ interp_continuation cstk Ws Cs.
  Proof.
    iIntros (Hh) "Hcont". rewrite /interp_cont_weak.
    destruct cstk as [ef [|frm frms] ]; cbn; first done.
    destruct Ws as [|Wt Ws], Cs as [|Ct Cs]; try done.
    destruct (is_untrusted_caller_frm frm) eqn:Hfrm; last done.
    iDestruct "Hcont" as "(Hrest & Hcallee & Htop & %Hb & %Hzone)".
    rewrite /cstk_hwm_base /= in Hb Hh.
    destruct Hzone as [Hzone|Hlt]; last (exfalso; rewrite Hb in Hlt; lia).
    destruct frm as [tf saved [ | | | ] ]; cbn in Hfrm |- *; try discriminate.
    all: iFrame; iPureIntro; split; done.
  Qed.

  (* TODO: move to switcher/code/clear_stack_spec.v *)
  (** Everything is zeroed from an address below the cells. *)
  Lemma stack_zeroed_from_below (b : Addr) (v : Z) (ws : list LWord) :
    (v <= b)%Z →
    stack_zeroed_from b v ws = replicate (length ws) (lword_of_word (WInt 0)).
  Proof.
    intros Hv. rewrite /stack_zeroed_from Z2Nat.nonpos; last lia.
    by rewrite take_0 Nat.sub_0_r.
  Qed.

  (* TODO: move to switcher/code/clear_stack_spec.v *)
  (** The cells of a stack region above MSHWMB and below MSHWM are cells of
      the zone, which hold 0: zeroing them from MSHWM zeroes them all. *)
  Lemma stack_region_below_hwm E (b e : Addr) (ws : list LWord) (hb h : Z) :
    (hb <= b)%Z →
    stack_region b e ws -∗
    hwm_regs hb h -∗
    |~{E}~>
    ⌜stack_zeroed_from b h ws = replicate (length ws) (lword_of_word (WInt 0))⌝ ∗
    stack_region b e ws ∗
    hwm_regs hb h.
  Proof.
    iInduction ws as [|w ws] "IH" forall (b); iIntros (Hhb) "Hstk Hhwm".
    { iModIntro. iFrame. iPureIntro. by rewrite /stack_zeroed_from take_nil. }
    destruct (decide (h <= b)%Z) as [Hh | Hh].
    { iModIntro. iFrame. iPureIntro. by apply stack_zeroed_from_below. }
    iDestruct (stack_region_length with "Hstk") as %Hlen.
    rewrite finz_seq_between_length /= in Hlen.
    assert (b < e)%a as Hbe by (rewrite /finz.dist in Hlen; solve_addr).
    destruct (b + 1)%a as [b'|] eqn:Hb'; last solve_addr.
    iDestruct (stack_region_cons b b' e with "Hstk") as "[[Hb | [Hb ->]] Hstk]"; [done|done|..].
    - (* A full points-to is outside the zone *)
      iDestruct "Hhwm" as "[Hhb Hh]".
      iMod (hwm_pointsto_outside with "Hb Hhb Hh") as "(%Hout & _)".
      exfalso; lia.
    - iMod ("IH" $! b' with "[%] Hstk Hhwm") as "(%Hz & Hstk & Hhwm)"; first solve_addr.
      iModIntro. iFrame "Hhwm".
      iSplit.
      + iPureIntro. revert Hz. rewrite /stack_zeroed_from.
        rewrite (_ : Z.to_nat (h - b) = S (Z.to_nat (h - b'))); last solve_addr.
        cbn. by intros ->.
      + iApply (stack_region_cons b b' e); [done|done|]. iFrame.
        by iApply stack_cell_of_zone.
  Qed.

  (* TODO: move to logrel/logrel.v *)
  (** The cells of a stack region are the cells of Temporary keys. *)
  Lemma stack_region_temp_cells (b e : Addr) (ws : list LWord) :
    stack_region b e ws ⊣⊢
    [∗ list] a;v ∈ finz.seq_between b e; ws, temp_cell th (LNonHeap a) v.
  Proof.
    rewrite /stack_region. apply big_sepL2_proper. intros. apply stack_cell_temp_cell.
  Qed.

  (* TODO: move to switcher/common/switcher_preamble.v *)
  #[global] Instance cframe_stk_own_timeless (a : Addr) (saved : callee_saved_registers)
    (ccrel : caller_callee_relation) :
    Timeless (cframe_stk_own a saved ccrel).
  Proof. rewrite /cframe_stk_own. destruct (is_untrusted_caller ccrel); apply _. Qed.

  (* TODO: move to program_logic/stack_cells.v *)
  (** No cell is locked between an address and itself. *)
  Lemma hwm_locked_empty (x : Addr) : hwm_locked x x ⊣⊢ emp.
  Proof. by rewrite /hwm_locked finz_seq_between_empty; last solve_addr. Qed.

  (** The return routine, from its entry point: from a full register file
      whose return values [ca0] and [ca1] are safe, the switcher pops the
      caller's frame and returns to it, or exits the thread when the frame to
      pop is the entry frame. No other register is read. MSHWM is [h]. *)
  Lemma switcher_return_unwind (trusted_fault : CSTK → LWord → LReg → Z → iProp Σ)
    (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (wca0 wca1 : LWord) (h : Z) :
    (∀ r, is_Some (rmap !! r)) ->
    rmap !! ca0 = Some wca0 ->
    rmap !! ca1 = Some wca1 ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    registers_pointsto rmap ∗
    interp W C wca0 ∗
    interp W C wca1 ∗
    thread_in th C ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) ∗
    world_interp W C ∗
    interp_cont_weak cstk Ws Cs h ∗
    hwm_res cstk h ∗
    na_own (tpool th) ⊤ ∗
    ◯(CSTK)[th] cstk
    ⊢ safe[th].
  Proof.
    (* Outline of the proof:
       - open the trusted-stack invariant;
       - when the frame to pop is the entry frame, the thread exits:
         [switcher_return_exit_path_spec], [switcher_return_exit_close];
       - otherwise, obtain the caller's stack frame
         ([open_world_interp_cframe], [open_world_interp_callee_stack]): its
         cells below MSHWM hold 0, since the caller's stack starts at the
         base of the thread's stack;
       - [switcher_return_path_world_spec]: pop the trusted stack, restore
         the callee-save registers, clear the stack frame and the registers,
         and jump to the caller; the zeroing does not fault;
       - close the trusted-stack invariant ([switcher_return_pop_close]);
       - when the caller is trusted, use the continuation relation;
       - when the caller is untrusted, close the world and
         [switcher_jump_to_caller_cases_spec]. *)
    iIntros (Hfull_rmap Hwca0 Hwca1 Hfreq)
      "(HPC & Hrmap & #Hinterp_wca0 & #Hinterp_wca1 & #Hthread & #Hinv_switcher & #[Hcode _] & #Htrap
        & Hworld_interp & Hcont_K & Hhwm & Hna & Hcstk)".
    (* MSHWM is at or above the base of the thread's stack *)
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hhwm_ord & Hlocked) #Hts]".
    iDestruct (interp_cont_weak_strong with "Hcont_K") as "Hcont_K";
      first (destruct Hhwm_ord; solve_addr).
    iDestruct (ret_regs_extract_full with "Hrmap")
      as "(Hca0 & Hca1 & [%wcsp Hcsp] & [%wcgp Hcgp] & [%wcra Hcra] & [%wcs0 Hcs0] & [%wcs1 Hcs1]
          & %rmap0 & %Hrmap0 & Hrmap)"; [done|done|done|].
    (* Open the trusted-stack invariant *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed trusted_stack_inv_open "Hswitcher_inv".
    iDestruct (switcher_hazard_open with "Hsave_area Hhazard_slots") as "[Hhazard Hsave_area]";
      first done.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq; subst cstk'.

    iEval (rewrite switcher_return_block_13) in "HPC".
    destruct cstk as [ef [|frm frms] ].
    { (* No caller: the frame to pop is the entry frame, the thread exits *)
      iApply (switcher_return_exit_path_spec with
        "[$HPC $Hrmap $Hmtdc $Hframeoffset $Hhazard $Hcode
          Hna Hclose_switcher_inv Hsave_area HthreadID Htstk Hcstk_full Hstk_interp]");
        first done.
      iIntros "!> (Hmtdc & Hframeoffset & Hhazard)".
      subst hclose_switcher_inv.
      iMod (switcher_return_exit_close ⊤ (entry_cstack ef) with
             "Hsave_mshwmb Hclose_switcher_inv Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htstk
              Hcstk_full Hstk_interp") as "Hna"; [done|done|].
      iModIntro; iIntros (_); iExact "Hna".
    }
    iEval (rewrite /cstack_interp; cbn) in "Hstk_interp".
    cbn in Hlen_cstk.

    (* A frame pushed above the entry frame *)
    destruct Ws;[done|].
    destruct Cs;[done|].
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm as [ [w_csp w_tbl n_cnt] [wret_saved wcgp_saved wcs0_saved wcs1_saved] ccrel].
    rewrite /cframe_interp.
    iDestruct "Hcframe_interp" as "[>Hcframe_top Hcframe_interp]".
    iNamed "Hcframe_top". iNamed "Hcf_tframe".
    iDestruct "Htf_tbl" as (wtbl) "[Htf_tbl _]".
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "(%b_stk & %e_stk & %a_stk & >%HWF & Hcframe_interp)".
    cbn in HWF.
    destruct HWF as (-> & Hstk_bounds & Hstk_mmio & Hstk_heap & Hret_ok).
    assert (∀ tf, tf.(tf_csp).(lw) = Cap RWL Local b_stk e_stk (stk_saved_a a_stk) →
                  tf_caller_a tf = a_stk) as Hspill.
    { intros tf Htf. eapply tf_caller_a_saved; [apply Hstk_bounds | exact Htf]. }
    simpl in Hfreq. destruct Hfreq as (Hfrelated & <- & Hccrel_known_to_known & Hfreq).
    pose proof Hstk_bounds as (Hb_a4 & He_a1 & Ha4).
    stk_unfold. change (4 - 1)%Z with 3%Z in He_a1.

    (* The caller's stack, and the stacks of the frames below, start at the
       base of the thread's stack: so does the floor *)
    iDestruct (interp_monotone_continuation with "Hcont_K") as "Hcont_K"; eauto.
    rewrite /interp_continuation /interp_cont.
    iDestruct (interp_cont_bases with "Hcont_K") as "[Hcont_K %Hbases]".
    apply Forall_cons in Hbases as [Hbase Hbases].
    cbn in Hbase.
    pose proof (frames_hwm_floor_base _ _ Hbases) as Hfloor_next.
    rewrite /cstk_hwm_base /cstk_hwm_floor /= in Hhwm_ord.
    iEval (rewrite /cstk_hwm_base /cstk_hwm_floor /=) in "Hlocked Hts Hmshwmb".
    cbn in Hbases, Hfloor_next.
    rewrite /is_untrusted_caller_frm /= in Hhwm_ord.
    iEval (rewrite /is_untrusted_caller_frm /=) in "Hlocked".
    iEval (cbn) in "Hcont_K". rewrite Hspill; last done.
    stk_unfold.
    rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    iDestruct "Hcont_K" as "(Hcont_K & #Hinterp_callee_wstk & Htopmost_frm)".
    iEval (cbn) in "Hinterp_callee_wstk".
    iDestruct "Hinterp_callee_wstk" as "[%Hstk_nonheap #Hinterp_callee_wstk]".
    (* The floor of the call stack is the base of the thread's stack *)
    assert ((if is_untrusted_caller ccrel then frames_hwm_floor ef frms else b_stk) = tf_stk_b ef)
      as Hfloor by (destruct (is_untrusted_caller ccrel); by rewrite ?Hfloor_next).
    rewrite Hfloor in Hhwm_ord.
    iEval (rewrite Hfloor hwm_locked_empty) in "Hlocked".
    destruct Hhwm_ord as [_ Hhwm_ord].

    (* Obtain the caller's stack frame *)
    iMod "Hcframe_interp" as "Hcframe_interp".
    iDestruct (open_world_interp_cframe with "[$Hcframe_interp $Hworld_interp]")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3
          & Hstk'
          & Hclose_res & %Hwastks & Hworld_interp)";
    eauto.
    iDestruct (open_world_interp_callee_stack
                with "[$Hinterp_callee_wstk $Hworld_interp]")
      as "(Hworld_interp & (%lv & Hstk & Hres))"; eauto.
    set (s := a_stk ^+ - (4)).
    assert ((s + 4)%a = Some a_stk) as Hs4 by (subst s; solve_addr+Ha4).
    rewrite /callee_stk_region. stk_unfold.
    iEval (rewrite -stack_region_temp_cells) in "Hstk".
    (* The cells of the caller's stack below MSHWM hold 0 *)
    iMod (stack_region_below_hwm with "Hstk [$Hmshwmb $Hmshwm]")
      as "(%Hzero & Hstk & Hhwm_regs)"; first solve_addr.
    iMod (stack_region_below_hwm with "Hstk' Hhwm_regs")
      as "(%Hzero' & Hstk' & Hhwm_regs)"; first solve_addr.

    (* Pop the trusted stack, restore, clear and return *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    iApply (switcher_return_path_world_spec W W C ccrel (length frms) with
      "[- $HPC $Hcsp $Hcgp $Hcra $Hcs0 $Hcs1 $Hrmap $Hmtdc $Hframeoffset $Hhazard $Htf_csp
          $Hhwm_regs $Hcode]");
      [done|done|done|done|done|done| split; [solve_addr|lia] |].
    iIntros "!> (Hmtdc & Hframeoffset & Hhazard & Htf_csp & _)".
    rewrite -/(interp_cont).
    iDestruct "Hclose_res" as "[#Hsave Hstates]".
    iCombine "Hsave Hstates" as "Hclose_res".
    iAssert (if is_untrusted_caller ccrel then
        interp_in_mem RWL W C wastk2 ∗
        interp_in_mem RWL W C wastk3 ∗
        interp_in_mem RWL W C wastk1 ∗
        interp_in_mem RWL W C wastk
      else True)%I as "#Hnormal".
    { destruct (is_untrusted_caller ccrel) eqn:Huntrusted; simpl; last done.
      rewrite /StackWorldResources.
      stk_unfold.
      do 4 (rewrite (finz_seq_between_cons _ (s ^+ 4)); last solve_addr+Hs4).
      rewrite (finz_seq_between_empty _ (s ^+ 4)); last solve_addr+Hs4.
      replace ((s ^+ 1) ^+ 1) with (s ^+ 2) by solve_addr+Hs4.
      replace ((s ^+ 2) ^+ 1) with (s ^+ 3) by solve_addr+Hs4.
      iDestruct (big_sepL2_cons with "Hsave") as "[Hsave0 Hsave_tail1]".
      iDestruct (big_sepL2_cons with "Hsave_tail1") as "[Hsave1 Hsave_tail2]".
      iDestruct (big_sepL2_cons with "Hsave_tail2") as "[Hsave2 Hsave_tail3]".
      iDestruct (big_sepL2_cons with "Hsave_tail3") as "[Hsave3 _]".
      iDestruct (StackWorldResource_interp_in_mem with "Hsave2") as "$".
      iDestruct (StackWorldResource_interp_in_mem with "Hsave3") as "$".
      iDestruct (StackWorldResource_interp_in_mem with "Hsave1") as "$".
      iDestruct (StackWorldResource_interp_in_mem with "Hsave0") as "$". }
    iModIntro.
    iExists _, wastk, wastk1, wastk2, wastk3, lv.
    iFrame "Hstk' Hstk Hworld_interp Hnormal".
    iNext; iSplit; cycle 1.
    { (* The caller's stack starts at the base of the thread's stack, at or
         below MSHWM: the zeroing does not fault *)
      iIntros (rmap1 rcgp rcra rcs1 rcs0 off) "(_ & %Hlt & _)". exfalso.
      rewrite Hbase in Hlt; lia. }
    iIntros (arg_rmap' rstk3 rstk2 rstk1 rstk0)
      "(%Hloaded & _ & Hworld_interp & Hinterp_loaded & %Harg_rmap' & Hcra & Hcgp & Hcs0 & Hcs1
      & Hcsp & Hstk_register_save & Hstk & Hhwm_regs & Hrmap & _)".
    destruct Hloaded as (Hr3 & Hr2 & Hr1 & Hr0).
    iEval (rewrite Hzero') in "Hstk_register_save".
    iEval (rewrite Hzero) in "Hstk".

    (* Depop the topmost frame of the call-stack and close the switcher's
       invariant, after the jump or the exception entry *)
    iAssert (|={⊤}=> na_own (tpool th) ⊤ ∗
                     cstack_frag {| cstk_entry := ef; cstk_frames := frms |})%I
      with "[Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htf_csp Htf_tbl Htf_cnt Htstk
             Hcstk_full Hstk_interp_next Hcstk Hclose_switcher_inv]" as "Hupd".
    { subst hclose_switcher_inv.
      iApply (switcher_return_pop_close ⊤ _ {| cstk_entry := ef; cstk_frames := frms |} with
             "Hsave_mshwmb Hclose_switcher_inv Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htf_csp Htf_tbl
              Htf_cnt Htstk Hcstk_full Hcstk Hstk_interp_next");
        [done|done|done]. }

    (* MSHWM is the caller's cursor *)
    iAssert (hwm_res {| cstk_entry := ef; cstk_frames := frms |} a_stk)%I
      with "[Hhwm_regs Hlocked]" as "Hhwm".
    { iDestruct "Hhwm_regs" as "[Hmshwmb Hmshwm]".
      rewrite /hwm_res /hwm_res_at /cstk_hwm_base /cstk_hwm_floor /cstk_hwm_top /= Hfloor_next
        hwm_locked_empty.
      iFrame "Hmshwmb Hmshwm Hts". iPureIntro. split; solve_addr. }

    set (lv' := region_addrs_zeroes b_stk s).
    assert (Forall (λ y : LWord, y = WInt 0) lv') as Hlv'.
    { subst lv'.
      rewrite /region_addrs_zeroes.
      by apply Forall_replicate.
    }
    iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv".
    rewrite length_replicate in Hlen_lv.
    rewrite (_ : replicate (length lv) (lword_of_word (WInt 0)) = lv');
      last (subst lv'; by rewrite /region_addrs_zeroes -Hlen_lv finz_seq_between_length).

    destruct (is_untrusted_caller ccrel) eqn:Hccrel ; cycle 1.
    - (* Case where caller is trusted, we use the continuation relation K *)
      destruct Hwastks as (-> & -> & -> & ->).
      iEval (rewrite app_nil_r) in "Hworld_interp".

      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv lv' with "Hres") as "Hres"; auto.

      iSplit; cycle 1.
      { (* The return address of a trusted caller is a valid target *)
        iIntros "%Hjalr".
        destruct (Hret_ok Hccrel) as [Hret_jalr Hret_heap].
        apply load_heap_in_world_nonheap in Hr2; last done.
        subst rstk2; congruence. }
      iIntros "[HPC _]".
      iMod "Hupd" as "[Hna Hcstk_frag]".
      iDestruct "Htopmost_frm" as "[_ Htopmost_frm]".
      iSpecialize ("Htopmost_frm" $! W (related_sts_pub_refl_world W)).
      iEval (rewrite /interp_cont_exec /is_untrusted_caller_frm /= ?Hccrel)
        in "Htopmost_frm".
      stk_unfold.
      (* The caller's cells between the floor and its stack: none *)
      iAssert (hwm_locked (frames_hwm_floor ef frms) b_stk) as "Hlocked'".
      { by rewrite Hfloor_next -Hbase hwm_locked_empty. }
      iApply ("Htopmost_frm" with "[%] [%] [%] [%]
               [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_wca0 $Hinterp_wca1
      $Hrmap $Hhwm $Hlocked' $Hstk_register_save $Hstk $Hworld_interp $Hres $Hcont_K $Hcstk_frag $Hna $Hthread]");
        [exact Hr3|exact Hr2|exact Hr0|exact Hr1|].
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we close the world and jump to the
         return address *)
      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv lv' with "Hres") as "Hres"; auto.
      iEval (rewrite stack_region_temp_cells) in "Hstk".
      iDestruct (close_world_interp_opening_resources with "[$Hworld_interp $Hstk $Hres]") as "Hworld_interp".
      { apply finz_seq_between_NoDup. }
      { clear -He_a1 Ha4 Hs4.
        intros a Ha Ha'.
        apply elem_of_finz_seq_between in Ha, Ha'.
        stk_unfold. solve_addr.
      }
      { subst lv'. by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }

      iDestruct "Hinterp_loaded" as
        "#(Hinterp_wstk3 & Hinterp_wstk2 & Hinterp_wstk1 & Hinterp_wstk0)".

      clear Hlen_lv' Hlv' lv'.
      set (lv' := region_addrs_zeroes s (s ^+ 4)).
      assert (Forall (λ y : LWord, y = WInt 0) lv') as Hlv'.
      { subst lv'; rewrite /region_addrs_zeroes; by apply Forall_replicate. }
      assert (replicate (length [wastk; wastk1; wastk2; wastk3]) (lword_of_word (WInt 0)) = lv')
        as Hlv'_eq.
      { subst lv'; rewrite /region_addrs_zeroes /finz.dist; f_equal; cbn; solve_addr+Hs4. }
      iEval (rewrite Hlv'_eq) in "Hstk_register_save".

      iDestruct (big_sepL2_length with "Hstk_register_save") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ _ lv' with "Hclose_res") as "Hclose_res"; auto.
      iEval (rewrite stack_region_temp_cells) in "Hstk_register_save".
      iEval (rewrite -(app_nil_r (finz.seq_between s (s ^+ 4)))) in "Hworld_interp".
      iDestruct (close_world_interp_opening_resources with "[$Hworld_interp $Hstk_register_save $Hclose_res]") as "Hworld_interp".
      { apply finz_seq_between_NoDup. }
      { set_solver. }
      { subst lv'; by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }
      rewrite fmap_nil -open_world_interp_empty.

      rewrite /is_untrusted_caller_frm /= Hccrel in Hfreq.
      (* The untrusted caller recorded that its topmost compartment is
         untrusted, and that its stack addresses between the floor and its
         cursor are Temporary *)
      iDestruct "Htopmost_frm" as "(#Htop_caller & %Hzone & _)".
      iApply (switcher_jump_to_caller_cases_spec with
               "Htrap Hthread Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk
                Hinterp_wca0 Hinterp_wca1 Htop_caller Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
                Hrmap [Hhwm] Hcont_K [Hupd Hworld_interp]"); [done|done| |].
      { iExists a_stk. iFrame "Hhwm". iPureIntro. exact Hzone. }
      iMod "Hupd" as "[Hna Hcstk_frag]".
      by iFrame.
  Qed.

End fundamental.
