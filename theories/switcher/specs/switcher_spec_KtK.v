From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import
  switcher_spec_KtK_call switcher_spec_KtK_return switcher_load_spec
  switcher_error_handler.
From griotte Require Import map_simpl register_tactics.


Section Switcher_KtK.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The unwind continuation of a known callee's frame [frame], pushed on
      [cstk], with the callee's stack $[b_callee, e_callee)$: the switcher
      force-unwinds a fault of the callee and returns ECOMPARTMENTFAIL to
      the caller, which needs the callee's whole stack back. *)
  Definition ktk_fault_cont (F : coPset) (frame : cframe) (cstk : CSTK)
    (b_callee e_callee : Addr) : iProp Σ :=
    unwind_cont F (cstack_push frame cstk)
      (∃ stk_mem : list LWord, [[ b_callee , e_callee ]] ↦ₐ [[ stk_mem ]]).

  (** Shape of the higher-order specification for entry points
      in the case of known-to-known cross-compartment calls.
      [P] is the precondition of the callee,
      and [Q] is the postcondition, parameterised by the returned values.
      When [may_fault] holds, the callee may fault: it also receives the
      unwind continuation of its frame ([ktk_fault_cont]), and the
      trusted-stack invariant and the switcher's static resources, to close
      its faults with [trap_safe_exception_entry]; the switcher returns
      ECOMPARTMENTFAIL to the caller.
      The callee's stack is at least its minimum stack size [minstk] plus
      the space reserved at its top.
      The callee returns through [return_cont] at any error handler count
      [n] of its frame: a callee with an error handler may fault and resume.

      The machine frame records only the saved words. The allocator owns all
      shadow entries; their states may change between the call and return.
   **)
  Definition switcher_cc_specification_known_to_known_function
    (may_fault : bool)
    (P : iProp Σ) (Q : LWord -> LWord -> iProp Σ)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap : LReg)
    (cstk : CSTK)
    (nargs minstk : nat)
    (F : coPset)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z)
    (w_callee_exp_tbl : LWord)
    : iProp Σ :=
    let frame :=
           {| cf_tframe :=
                {| tf_csp := Cap RWL Local b_stk e_stk (stk_saved_a a_stk);
                   tf_export_tbl := w_callee_exp_tbl;
                   tf_error_count := 0 |};
              cf_saved :=
                {| cs_cra := wcra_caller;
                   cs_cgp := wcgp_caller;
                   cs_cs0 := wcs0_caller;
                   cs_cs1 := wcs1_caller |};
              ccrel := Known_to_Known
           |}
    in
    let return_cont :=
      (▷ (∀ (n : Z) (wca0 wca1 : LWord) (rmap_ret : LReg)
               (stk_mem_ret : list LWord),
             ⌜ dom rmap_ret =
                   all_registers_s ∖
                     {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
             ∗ na_own (tpool th) F
             ∗ PC ↦ₚ[th] Cap XSRW_ Local
                         b_switcher e_switcher a_switcher_return
             ∗ cgp ↦ᵣ[th] - ∗ cra ↦ᵣ[th] - ∗ cs0 ↦ᵣ[th] - ∗ cs1 ↦ᵣ[th] -
             ∗ csp ↦ᵣ[th] callee_csp b_stk e_stk a_stk
             ∗ ca0 ↦ᵣ[th] wca0
             ∗ ca1 ↦ᵣ[th] wca1
             ∗ regs[th] rmap_ret
             ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ stk_mem_ret ]]
             ∗ ◯(CSTK)[th] (cstack_set_top_count (cstack_push frame cstk) n)
             ∗ Q wca0 wca1
               -∗ safe[th]))%I
    in
    (* FAULT --- the callee faults; the switcher force-unwinds its frame and
       returns ECOMPARTMENTFAIL to the caller *)
    let fault_cont :=
      ktk_fault_cont F frame cstk (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk) in
    (∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
       ⌜ (Z.of_nat minstk + StackEntry_reserved_space <=
            stk_callee_e e_stk a_stk - stk_callee_b b_stk a_stk)%Z ⌝
       ∗ ⌜ is_arg_rmap arg_rmap' 8 ⌝
       ∗ ⌜ dom rmap' =
             all_registers_s ∖
               ({[ cgp ; cra ; csp ]} ∪ dom_arg_rmap 8) ⌝
       ∗ na_own (tpool th) F
       ∗ PC ↦ₚ[th] Cap RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)
       ∗ cgp ↦ᵣ[th] Cap RW Global bcgp_tgt ecgp_tgt bcgp_tgt
       ∗ cra ↦ᵣ[th] Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return
       ∗ csp ↦ᵣ[th] callee_csp b_stk e_stk a_stk
       ∗ ([∗ map] rarg↦warg ∈ arg_rmap',
            rarg ↦ᵣ[th] warg
            ∗ if decide (rarg ∈ dom_arg_rmap nargs)
              then ⌜ arg_rmap !! rarg = Some warg ⌝
              else ⌜ warg = WInt 0 ⌝)
       ∗ regs₀[th] rmap'
       ∗ [[ stk_callee_b b_stk a_stk , stk_callee_e e_stk a_stk ]] ↦ₐ [[ 0…0 ]]
       ∗ ◯(CSTK)[th] (cstack_push frame cstk)
       ∗ P
       ∗ (if may_fault then (return_cont ∧ fault_cont) ∗ switcher_res F else return_cont)
       -∗ safe[th])%I.


  #[local] Lemma if_and_sep_intro (b : bool) (R Q S : iProp Σ) :
    (if b then S else True) -∗
    R ∧ (if b then Q else True) -∗
    if b then (R ∧ Q) ∗ S else R.
  Proof. destruct b; iIntros "HS H"; [iFrame | by iDestruct "H" as "[$ _]"]. Qed.

  (** Specification of the switcher for known-to-known cross compartment call,
      with higher-order specification of the callee. *)
  (** A successful return, trusted-stack exhaustion, and, when [may_fault]
      holds, a fault of the callee all restore the four saved registers
      according to [load_heap].
      When the callee faults, the caller gets ECOMPARTMENTFAIL back, and
      neither [P] nor [Q]. *)
  Lemma switcher_cc_specification_known_to_known_end_to_end
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK)
    (nargs minstk_tgt : nat)
    (F : coPset)
    (btbl_tgt atbl_tgt etbl_tgt : Addr)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z) (posture_tgt : InterruptStatus)
    (may_fault : bool) (P : iProp Σ) (Q : LWord -> LWord -> iProp Σ)
    :
    let a_tbl_cgp := (btbl_tgt ^+ ExportTable_offset_cgp) in
    let a_tbl_ehs := (btbl_tgt ^+ ExportTable_offset_errorHandlerStackless) in
    let wct1_caller :=
      Sealed ot_switcher RO Global btbl_tgt etbl_tgt atbl_tgt in
    (* The callee returned *)
    let returned :=
      (∃ (rcgp rcra rcs0 rcs1 wca0_ret wca1_ret : LWord) (rmap_ret : LReg),
         "%Hdom_rmap_ret" ∷ ⌜ dom rmap_ret =
               all_registers_s ∖
                 {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
         ∗ "Hna" ∷ na_own (tpool th) F
         ∗ "HPC" ∷ PC ↦ₚ[th] lupdatePcPerm (rcra)
         ∗ "Hcgp" ∷ cgp ↦ᵣ[th] rcgp
         ∗ "Hcra" ∷ cra ↦ᵣ[th] rcra
         ∗ "Hcs0" ∷ cs0 ↦ᵣ[th] rcs0
         ∗ "Hcs1" ∷ cs1 ↦ᵣ[th] rcs1
         ∗ "Hcsp" ∷ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
         ∗ "Hca0" ∷ ca0 ↦ᵣ[th] wca0_ret
         ∗ "Hca1" ∷ ca1 ↦ᵣ[th] wca1_ret
         ∗ "Hrmap" ∷ regs₀[th] rmap_ret
         ∗ "Hstk" ∷ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ 0…0 ]]
         ∗ "Hcstk" ∷ ◯(CSTK)[th] cstk
         ∗ "%Hrestored" ∷ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
             load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
         ∗ "HQ" ∷ Q wca0_ret wca1_ret)%I
    in
    (* The trusted stack is exhausted; the callee did not run *)
    let stack_exhausted :=
      (∃ (rmap_ret : LReg) (stk_mem' : list LWord) rcgp rcra rcs0 rcs1,
         "%Hdom_rmap_ret" ∷ ⌜ dom rmap_ret =
               all_registers_s ∖
                 {[ cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
         ∗ "Hna" ∷ na_own (tpool th) F
         ∗ "HPC" ∷ PC ↦ₚ[th] lupdatePcPerm (rcra)
         ∗ "Hcgp" ∷ cgp ↦ᵣ[th] rcgp
         ∗ "Hcra" ∷ cra ↦ᵣ[th] rcra
         ∗ "Hcsp" ∷ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
         ∗ "Hcs0" ∷ cs0 ↦ᵣ[th] rcs0
         ∗ "Hcs1" ∷ cs1 ↦ᵣ[th] rcs1
         ∗ "Hca0" ∷ ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK
         ∗ "Hca1" ∷ ca1 ↦ᵣ[th] WInt 0
         ∗ "Hrmap" ∷ regs₀[th] rmap_ret
         ∗ "Hstk" ∷ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem' ]]
         ∗ "Hcstk" ∷ ◯(CSTK)[th] cstk
         ∗ "%Hrestored" ∷ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
             load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
         ∗ "HP" ∷ P)%I
    in
    (* The callee faulted: the exception entry of the switcher returned
       ECOMPARTMENTFAIL *)
    let callee_faulted :=
      (∃ (rmap_ret : LReg) rcgp rcra rcs0 rcs1,
         "%Hdom_rmap_ret" ∷ ⌜ dom rmap_ret =
               all_registers_s ∖
                 {[ cgp ; cra ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
         ∗ "Hna" ∷ na_own (tpool th) F
         ∗ "HPC" ∷ PC ↦ₚ[th] lupdatePcPerm (rcra)
         ∗ "Hcgp" ∷ cgp ↦ᵣ[th] rcgp
         ∗ "Hcra" ∷ cra ↦ᵣ[th] rcra
         ∗ "Hcsp" ∷ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
         ∗ "Hcs0" ∷ cs0 ↦ᵣ[th] rcs0
         ∗ "Hcs1" ∷ cs1 ↦ᵣ[th] rcs1
         ∗ "Hca0" ∷ ca0 ↦ᵣ[th] WInt ECOMPARTMENTFAIL
         ∗ "Hca1" ∷ ca1 ↦ᵣ[th] WInt 0
         ∗ "Hrmap" ∷ regs₀[th] rmap_ret
         ∗ "Hstk" ∷ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ 0…0 ]]
         ∗ "Hcstk" ∷ ◯(CSTK)[th] cstk
         ∗ "%Hrestored" ∷ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
             load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝)%I
    in
    disjoint_from_heap b_stk e_stk ->
    disjoint_from_mmio b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    is_shadow_address atbl_tgt = false ->
    is_shadow_address btbl_tgt = false ->
    is_shadow_address a_tbl_cgp = false ->
    disjoint_from_shadow btbl_tgt etbl_tgt ->
    is_heap_address bpcc_tgt = false ->
    is_heap_address bcgp_tgt = false ->
    ↑Ntstack ⊆ F ->
    ↑Ntrap ⊆ F ->
    atbl_tgt ∈ₐ [btbl_tgt, etbl_tgt) ->
    (btbl_tgt < a_tbl_cgp)%a ->
    (a_tbl_ehs < atbl_tgt)%a ->
    (0 <= nargs <= 7)%nat ->
    is_Some (bpcc_tgt + off_tgt)%a ->
    (* The callee's stack is at least its minimum stack size plus the
       reserved space *)
    stk_callee_fits b_stk e_stk a_stk minstk_tgt ->
    dom rmap =
      all_registers_s ∖
        ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static
    ∗ btbl_tgt ↦ₐ□ Cap RX Global bpcc_tgt epcc_tgt bpcc_tgt
    ∗ a_tbl_cgp ↦ₐ□ Cap RW Global bcgp_tgt ecgp_tgt bcgp_tgt
    ∗ atbl_tgt ↦ₐ□ WInt (encode_entry_point posture_tgt (Z.of_nat nargs) (Z.of_nat minstk_tgt) off_tgt)
    ∗ na_own (tpool th) F
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ[th] wcgp_caller
    ∗ cra ↦ᵣ[th] wcra_caller
    ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
    ∗ ct1 ↦ᵣ[th] wct1_caller
    ∗ cs0 ↦ᵣ[th] wcs0_caller
    ∗ cs1 ↦ᵣ[th] wcs1_caller
    ∗ regs[th] arg_rmap
    ∗ regs[th] rmap
    ∗ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ ◯(CSTK)[th] cstk
    ∗ P
    ∗ switcher_cc_specification_known_to_known_function
        may_fault P Q wcgp_caller wcra_caller wcs0_caller wcs1_caller
        b_stk e_stk a_stk arg_rmap cstk nargs minstk_tgt F
        bpcc_tgt epcc_tgt bcgp_tgt ecgp_tgt off_tgt (Cap RO Global btbl_tgt etbl_tgt atbl_tgt)
    ∗ ▷ ((if may_fault
          then returned ∨ stack_exhausted ∨ callee_faulted
          else returned ∨ stack_exhausted)
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    intros a_tbl_cgp a_tbl_ehs wct1_caller returned stack_exhausted callee_faulted.
    subst a_tbl_cgp a_tbl_ehs.
    subst returned stack_exhausted callee_faulted.
    iIntros (Hstk_heap Hstk_shadow Hb_a Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow Htbl_shadow
             Hbpcc_nonheap Hbcgp_nonheap
             HE HEtrap Hatbl Hbtbl_cgp Hbtbl_ehs Hnargs Hentry Hminstk Hdom Harg_rmap Hret_jalr Hret_heap)
      "(#Hswitcher & #Hstatic & #Hinv_pcc & #Hinv_cgp & #Hinv_entry
       & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & Hcs0 & Hcs1
       & Hargs & Hregs & Hstk & Hcstk & HP & Hf & Hpost)".

    iApply (switcher_cc_specification_known_to_known
              wcgp_caller wcra_caller wcs0_caller wcs1_caller
              b_stk e_stk a_stk stk_mem arg_rmap rmap cstk nargs minstk_tgt F
              btbl_tgt atbl_tgt etbl_tgt
              bpcc_tgt epcc_tgt bcgp_tgt ecgp_tgt off_tgt posture_tgt);
      try assumption.
    iFrame "Hswitcher Hstatic Hinv_pcc Hinv_cgp Hinv_entry
            Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1
            Hargs Hregs Hstk Hcstk".
    iNext.
    iIntros "[
      (%mie & %arg_rmap' & %rmap' & %Harg_rmap' & %Hrmap'
       & Hna & HPC & Hcgp & Hcra & Hcsp & Hargs & Hregs & Hstk & Hcstk)
      |
      (%rmap' & %stk_mem' & %rcgp & %rcra & %rcs0 & %rcs1 & %Hrmap'
       & Hna & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hregs & Hstk & Hcstk & %Hrestored)
      ]".
    - iApply ("Hf" $! mie arg_rmap' rmap').
      iFrame "Hna HPC Hcgp Hcra Hcsp Hargs Hregs Hstk Hcstk HP".
      iSplit.
      { iPureIntro. apply stk_callee_fits_callee; last done.
        by apply (stk_callee_fits_spill_ok b_stk e_stk a_stk minstk_tgt); [lia |]. }
      iSplit; first done.
      iSplit; first (iPureIntro; rewrite Hrmap' Hdom; set_solver).
      iApply (if_and_sep_intro with "[]").
      { destruct may_fault; last done.
        iFrame "Hswitcher Hstatic". by iPureIntro. }
      iSplit.
      { (* The callee returns *)
        iNext.
        iIntros (n wca0 wca1 rmap_ret stk_mem_ret)
          "(%Hrmap_ret & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1
           & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk & HQ)".
        iAssert (
          ▷ (∀ (rmap_final : LReg) rcgp rcra rcs0 rcs1,
               ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
               load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
               ∗ ⌜ dom rmap_final =
                     all_registers_s ∖
                       {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
               ∗ na_own (tpool th) F
               ∗ PC ↦ₚ lupdatePcPerm (rcra)
               ∗ cgp ↦ᵣ rcgp
               ∗ cra ↦ᵣ rcra
               ∗ cs0 ↦ᵣ rcs0
               ∗ cs1 ↦ᵣ rcs1
               ∗ csp ↦ᵣ Cap RWL Local b_stk e_stk a_stk
               ∗ ca0 ↦ᵣ wca0
               ∗ ca1 ↦ᵣ wca1
               ∗ ([∗ map] r↦w ∈ rmap_final,
                    r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
               ∗ [[ stk_free_b b_stk a_stk , stk_free_e e_stk a_stk ]] ↦ₐ [[ 0…0 ]]
               ∗ cstack_frag cstk
                 -∗ WP Exec
                       {{ HO th }}))%I
          with "[HQ Hpost]" as "Hretpost".
        { iNext.
          iIntros (rmap_final rcgp rcra rcs0 rcs1)
            "(%Hrestored & %Hrmap_final & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1
             & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk )".
          iApply "Hpost".
          destruct may_fault; iLeft;
            iExists rcgp, rcra, rcs0, rcs1, wca0, wca1, rmap_final;
            iFrame "∗#%".
        }
        iApply (switcher_cc_specification_return_known_to_known_gen
                  wcgp_caller wcra_caller wcs0_caller wcs1_caller
                  wca0 wca1 b_stk e_stk a_stk stk_mem_ret rmap_ret cstk
                  (Cap RO Global btbl_tgt etbl_tgt atbl_tgt) F n
                  with
                  "[$Hswitcher $Hstatic $Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1
                    $Hcsp $Hca0 $Hca1 $Hregs $Hstk $Hcstk $Hretpost]").
        { exact Hstk_heap. }
        { exact Hstk_shadow. }
        { apply (stk_callee_fits_spill_ok b_stk e_stk a_stk minstk_tgt); [lia | exact Hminstk]. }
        { exact HE. }
        { exact Hrmap_ret. }
      }
      (* The callee faults: the exception entry returns ECOMPARTMENTFAIL *)
      destruct may_fault; last done.
      iIntros (n rmap_fault Hfull_rmap_fault Hca0' Hca1')
        "HPC Hrmap_fault Hcstk [%stk_mem_ret Hstk] Hna".
      rewrite /registers_pointsto.
      getRegValList [cgp;cra;cs0;cs1;csp].
      iExtractList "Hrmap_fault" [cgp;cra;cs0;cs1;csp;ca0;ca1]
        as ["Hcgp";"Hcra";"Hcs0";"Hcs1";"Hcsp";"Hca0";"Hca1"].
      iApply (switcher_cc_specification_return_known_to_known_gen
                wcgp_caller wcra_caller wcs0_caller wcs1_caller
                (WInt ECOMPARTMENTFAIL) (WInt 0) b_stk e_stk a_stk stk_mem_ret _ cstk
                (Cap RO Global btbl_tgt etbl_tgt atbl_tgt) F n
                with
                "[$Hswitcher $Hstatic $Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1
                  $Hcsp $Hca0 $Hca1 $Hrmap_fault $Hstk $Hcstk Hpost]");
        [exact Hstk_heap | exact Hstk_shadow
        | apply (stk_callee_fits_spill_ok b_stk e_stk a_stk minstk_tgt); [lia | exact Hminstk] | exact HE | |].
      { rewrite !dom_delete_L (lregmap_full_dom _ Hfull_rmap_fault). set_solver. }
      iNext.
      iIntros (rmap_final rcgp rcra rcs0 rcs1)
        "(%Hrestored & %Hrmap_final & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1
         & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk)".
      iApply "Hpost".
      iRight; iRight.
      iExists rmap_final, rcgp, rcra, rcs0, rcs1.
      iFrame "∗%".
    - iApply "Hpost".
      destruct may_fault; [iRight; iLeft | iRight];
        iExists rmap', stk_mem', rcgp, rcra, rcs0, rcs1;
        iFrame "∗#%".
  Qed.


End Switcher_KtK.
