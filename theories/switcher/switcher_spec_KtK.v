From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import
  switcher_spec_KtK_call switcher_spec_KtK_return switcher_load_spec
  switcher_exception_stub.
From griotte Require Import map_simpl register_tactics.


Section Switcher_KtK.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Shape of the higher-order specification for entry points
      in the case of known-to-known cross-compartment calls.
      [P] is the precondition of the callee,
      and [Q] is the postcondition, parameterised by the returned values.
      When [may_fault] holds, the callee may fault: its continuation also
      covers the exception entry of the switcher, which returns
      ECOMPARTMENTFAIL to the caller.
      The callee's stack is at least its minimum stack size [minstk].

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
    (E : coPset)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z)
    (b_callee_exp_tbl : Addr)
    : iProp Σ :=
    let a_stk4 := (a_stk ^+ 4)%a in
    let frame :=
           {| wret := wcra_caller;
              wcgp := wcgp_caller;
              wcs0 := wcs0_caller;
              wcs1 := wcs1_caller;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              b_callee_exp_tbl := b_callee_exp_tbl;
              ccrel := Known_to_Known
           |}
    in
    let return_cont :=
      (▷ (∀ (wca0 wca1 : LWord) (rmap_ret : LReg)
               (stk_mem_ret : list LWord),
             ⌜ dom rmap_ret =
                   all_registers_s ∖
                     {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
             ∗ na_own cerise_nais E
             ∗ PC ↦ₚ WCap true XSRW_ Local
                         b_switcher e_switcher a_switcher_return
             ∗ cgp ↦ᵣ - ∗ cra ↦ᵣ - ∗ cs0 ↦ᵣ - ∗ cs1 ↦ᵣ -
             ∗ csp ↦ᵣ WCap true RWL Local a_stk4 e_stk a_stk4
             ∗ ca0 ↦ᵣ wca0
             ∗ ca1 ↦ᵣ wca1
             ∗ ([∗ map] r↦w ∈ rmap_ret, r ↦ᵣ w)
             ∗ [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem_ret ]]
             ∗ cstack_frag (frame :: cstk)
             ∗ Q wca0 wca1
               -∗ WP Seq (Instr Executable)
                     {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}))%I
    in
    (* FAULT --- the callee faults; the exception entry of the switcher
       returns ECOMPARTMENTFAIL to the caller *)
    let fault_cont :=
      (∀ (wpc : LWord),
         (|={⊤}=>
            ∃ (rmap_ret : LReg) (stk_mem_ret : list LWord),
              ⌜ dom rmap_ret =
                  all_registers_s ∖
                    {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
              na_own cerise_nais E ∗
              cgp ↦ᵣ - ∗
              cra ↦ᵣ - ∗
              cs0 ↦ᵣ - ∗
              cs1 ↦ᵣ - ∗
              csp ↦ᵣ WCap true RWL Local a_stk4 e_stk a_stk4 ∗
              ca0 ↦ᵣ - ∗
              ca1 ↦ᵣ - ∗
              ([∗ map] r↦w ∈ rmap_ret, r ↦ᵣ w) ∗
              [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem_ret ]] ∗
              cstack_frag (frame :: cstk)) -∗
         trap_safe wpc ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤))%I
    in
    (∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
       ⌜ (Z.of_nat minstk <= e_stk - a_stk4)%Z ⌝
       ∗ ⌜ is_arg_rmap arg_rmap' 8 ⌝
       ∗ ⌜ dom rmap' =
             all_registers_s ∖
               ({[ cgp ; cra ; csp ]} ∪ dom_arg_rmap 8) ⌝
       ∗ na_own cerise_nais E
       ∗ PC ↦ₚ WCap true RX Global bpcc_tgt epcc_tgt (bpcc_tgt ^+ off_tgt)%a
       ∗ cgp ↦ᵣ WCap true RW Global bcgp_tgt ecgp_tgt bcgp_tgt
       ∗ cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return
       ∗ csp ↦ᵣ WCap true RWL Local a_stk4 e_stk a_stk4
       ∗ ([∗ map] rarg↦warg ∈ arg_rmap',
            rarg ↦ᵣ warg
            ∗ if decide (rarg ∈ dom_arg_rmap nargs)
              then ⌜ arg_rmap !! rarg = Some warg ⌝
              else ⌜ warg = WInt 0 ⌝)
       ∗ ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
       ∗ [[ a_stk4 , e_stk ]] ↦ₐ
           [[ region_addrs_zeroes a_stk4 e_stk ]]
       ∗ cstack_frag (frame :: cstk)
       ∗ P
       ∗ (if may_fault then return_cont ∧ fault_cont else return_cont)
       -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.


  #[local] Lemma if_and_intro (b : bool) (R F : iProp Σ) :
    R ∧ (if b then F else True) ⊢ if b then R ∧ F else R.
  Proof. destruct b; first done. by iIntros "[$ _]". Qed.

  (** Specification of the switcher for known-to-known cross compartment call,
      with higher-order specification of the callee. *)
  (** A successful return, trusted-stack exhaustion, and, when [may_fault]
      holds, a fault of the callee all restore the four saved registers
      according to [load_heap].
      When the callee faults, the caller gets ECOMPARTMENTFAIL back, and
      neither [P] nor [Q]. *)
  Lemma switcher_cc_specification_known_to_known_end_to_end
    (Nswitcher : namespace)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK)
    (nargs minstk_tgt : nat)
    (E : coPset)
    (btbl_tgt atbl_tgt etbl_tgt : Addr)
    (bpcc_tgt epcc_tgt : Addr)
    (bcgp_tgt ecgp_tgt : Addr)
    (off_tgt : Z) (posture_tgt : InterruptStatus)
    (may_fault : bool) (P : iProp Σ) (Q : LWord -> LWord -> iProp Σ)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let a_tbl_cgp := (btbl_tgt ^+ ExportTable_offset_cgp)%a in
    let a_tbl_ehs := (btbl_tgt ^+ ExportTable_offset_errorHandlerStackless)%a in
    let wct1_caller :=
      WSealed ot_switcher (SCap true RO Global btbl_tgt etbl_tgt atbl_tgt) in
    (* The callee returned *)
    let returned :=
      (∃ (rcgp rcra rcs0 rcs1 wca0_ret wca1_ret : LWord) (rmap_ret : LReg),
         "%Hdom_rmap_ret" ∷ ⌜ dom rmap_ret =
               all_registers_s ∖
                 {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
         ∗ "Hna" ∷ na_own cerise_nais E
         ∗ "HPC" ∷ PC ↦ₚ lupdatePcPerm (rcra)
         ∗ "Hcgp" ∷ cgp ↦ᵣ rcgp
         ∗ "Hcra" ∷ cra ↦ᵣ rcra
         ∗ "Hcs0" ∷ cs0 ↦ᵣ rcs0
         ∗ "Hcs1" ∷ cs1 ↦ᵣ rcs1
         ∗ "Hcsp" ∷ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
         ∗ "Hca0" ∷ ca0 ↦ᵣ wca0_ret
         ∗ "Hca1" ∷ ca1 ↦ᵣ wca1_ret
         ∗ "Hrmap" ∷ ([∗ map] r↦w ∈ rmap_ret, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
         ∗ "Hstk" ∷ [[ a_stk , e_stk ]] ↦ₐ
             [[ region_addrs_zeroes a_stk e_stk ]]
         ∗ "Hcstk" ∷ cstack_frag cstk
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
         ∗ "Hna" ∷ na_own cerise_nais E
         ∗ "HPC" ∷ PC ↦ₚ lupdatePcPerm (rcra)
         ∗ "Hcgp" ∷ cgp ↦ᵣ rcgp
         ∗ "Hcra" ∷ cra ↦ᵣ rcra
         ∗ "Hcsp" ∷ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
         ∗ "Hcs0" ∷ cs0 ↦ᵣ rcs0
         ∗ "Hcs1" ∷ cs1 ↦ᵣ rcs1
         ∗ "Hca0" ∷ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
         ∗ "Hca1" ∷ ca1 ↦ᵣ WInt 0
         ∗ "Hrmap" ∷ ([∗ map] r↦w ∈ rmap_ret, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
         ∗ "Hstk" ∷ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem' ]]
         ∗ "Hcstk" ∷ cstack_frag cstk
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
         ∗ "Hna" ∷ na_own cerise_nais E
         ∗ "HPC" ∷ PC ↦ₚ lupdatePcPerm (rcra)
         ∗ "Hcgp" ∷ cgp ↦ᵣ rcgp
         ∗ "Hcra" ∷ cra ↦ᵣ rcra
         ∗ "Hcsp" ∷ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
         ∗ "Hcs0" ∷ cs0 ↦ᵣ rcs0
         ∗ "Hcs1" ∷ cs1 ↦ᵣ rcs1
         ∗ "Hca0" ∷ ca0 ↦ᵣ WInt ECOMPARTMENTFAIL
         ∗ "Hca1" ∷ ca1 ↦ᵣ WInt 0
         ∗ "Hrmap" ∷ ([∗ map] r↦w ∈ rmap_ret, r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
         ∗ "Hstk" ∷ [[ a_stk , e_stk ]] ↦ₐ
             [[ region_addrs_zeroes a_stk e_stk ]]
         ∗ "Hcstk" ∷ cstack_frag cstk
         ∗ "%Hrestored" ∷ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
             load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝)%I
    in
    disjoint_from_heap b_stk e_stk ->
    disjoint_from_mmio b_stk e_stk ->
    (* The caller's stack pointer is not below the base of its stack *)
    (b_stk <= a_stk)%a ->
    is_shadow_address atbl_tgt = false ->
    is_shadow_address btbl_tgt = false ->
    is_shadow_address a_tbl_cgp = false ->
    disjoint_from_shadow btbl_tgt etbl_tgt ->
    is_heap_address bpcc_tgt = false ->
    is_heap_address bcgp_tgt = false ->
    ↑Nswitcher ⊆ E ->
    ↑N_trap ⊆ E ->
    (btbl_tgt <= atbl_tgt < etbl_tgt)%a ->
    (btbl_tgt < a_tbl_cgp)%a ->
    (a_tbl_ehs < atbl_tgt)%a ->
    (0 <= nargs <= 7)%nat ->
    is_Some (bpcc_tgt + off_tgt)%a ->
    (* The callee's stack is at least its minimum stack size *)
    (a_stk + 4 + minstk_tgt <= e_stk)%Z ->
    dom rmap =
      all_registers_s ∖
        ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static
    ∗ btbl_tgt ↦ₐ□ WCap true RX Global bpcc_tgt epcc_tgt bpcc_tgt
    ∗ a_tbl_cgp ↦ₐ□ WCap true RW Global bcgp_tgt ecgp_tgt bcgp_tgt
    ∗ atbl_tgt ↦ₐ□ WInt (encode_entry_point posture_tgt (Z.of_nat nargs) (Z.of_nat minstk_tgt) off_tgt)
    ∗ na_own cerise_nais E
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    ∗ ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg)
    ∗ ([∗ map] r↦w ∈ rmap, r ↦ᵣ w)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ cstack_frag cstk
    ∗ P
    ∗ switcher_cc_specification_known_to_known_function
        may_fault P Q wcgp_caller wcra_caller wcs0_caller wcs1_caller
        b_stk e_stk a_stk arg_rmap cstk nargs minstk_tgt E
        bpcc_tgt epcc_tgt bcgp_tgt ecgp_tgt off_tgt btbl_tgt
    ∗ ▷ ((if may_fault
          then returned ∨ stack_exhausted ∨ callee_faulted
          else returned ∨ stack_exhausted)
        -∗ WP Seq (Instr Executable)
              {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_stk4 a_tbl_cgp a_tbl_ehs wct1_caller returned stack_exhausted callee_faulted.
    subst a_tbl_cgp a_tbl_ehs.
    subst returned stack_exhausted callee_faulted.
    iIntros (Hstk_heap Hstk_shadow Hb_a Hatbl_shadow Hbtbl_shadow Hbtbl_cgp_shadow Htbl_shadow
             Hbpcc_nonheap Hbcgp_nonheap
             HE HEtrap Hatbl Hbtbl_cgp Hbtbl_ehs Hnargs Hentry Hminstk Hdom Harg_rmap Hret_jalr Hret_heap)
      "(#Hswitcher & #Hstatic & #Hinv_pcc & #Hinv_cgp & #Hinv_entry
       & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & Hcs0 & Hcs1
       & Hargs & Hregs & Hstk & Hcstk & HP & Hf & Hpost)".

    iApply (switcher_cc_specification_known_to_known
              Nswitcher wcgp_caller wcra_caller wcs0_caller wcs1_caller
              b_stk e_stk a_stk stk_mem arg_rmap rmap cstk nargs minstk_tgt E
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
      iSplit; first (iPureIntro; solve_addr+Hminstk).
      iSplit; first done.
      iSplit; first (iPureIntro; rewrite Hrmap' Hdom; set_solver).
      iApply if_and_intro.
      iSplit.
      { (* The callee returns *)
        iNext.
        iIntros (wca0 wca1 rmap_ret stk_mem_ret)
          "(%Hrmap_ret & Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1
           & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk & HQ)".
        iAssert (
          ▷ (∀ (rmap_final : LReg) rcgp rcra rcs0 rcs1,
               ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
               load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
               ∗ ⌜ dom rmap_final =
                     all_registers_s ∖
                       {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝
               ∗ na_own cerise_nais E
               ∗ PC ↦ₚ lupdatePcPerm (rcra)
               ∗ cgp ↦ᵣ rcgp
               ∗ cra ↦ᵣ rcra
               ∗ cs0 ↦ᵣ rcs0
               ∗ cs1 ↦ᵣ rcs1
               ∗ csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk
               ∗ ca0 ↦ᵣ wca0
               ∗ ca1 ↦ᵣ wca1
               ∗ ([∗ map] r↦w ∈ rmap_final,
                    r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝)
               ∗ [[ a_stk , e_stk ]] ↦ₐ
                   [[ region_addrs_zeroes a_stk e_stk ]]
               ∗ cstack_frag cstk
                 -∗ WP Seq (Instr Executable)
                       {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}))%I
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
        iApply (switcher_cc_specification_return_known_to_known
                  Nswitcher wcgp_caller wcra_caller wcs0_caller wcs1_caller
                  wca0 wca1 b_stk e_stk a_stk stk_mem_ret rmap_ret cstk btbl_tgt E
                  with
                  "[$Hswitcher $Hstatic $Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1
                    $Hcsp $Hca0 $Hca1 $Hregs $Hstk $Hcstk $Hretpost]").
        { exact Hstk_heap. }
        { exact Hstk_shadow. }
        { exact HE. }
        { exact Hrmap_ret. }
      }
      (* The callee faults: the exception entry returns ECOMPARTMENTFAIL *)
      destruct may_fault; last done.
      iIntros (wpc) "Hres".
      iApply (trap_safe_exception_entry E with "Hstatic"); first done.
      iMod "Hres" as "(%rmap_ret & %stk_mem_ret & %Hrmap_ret & Hna & Hcgp & Hcra & Hcs0 & Hcs1
                       & Hcsp & Hca0 & Hca1 & Hregs & Hstk & Hcstk)".
      iModIntro; iFrame "Hna Hca0 Hca1".
      iIntros "(HPC & Hca0 & Hca1 & Hna)".
      iApply (switcher_cc_specification_return_known_to_known
                Nswitcher wcgp_caller wcra_caller wcs0_caller wcs1_caller
                (WInt ECOMPARTMENTFAIL) (WInt 0) b_stk e_stk a_stk stk_mem_ret rmap_ret cstk btbl_tgt E
                with
                "[$Hswitcher $Hstatic $Hna $HPC $Hcgp $Hcra $Hcs0 $Hcs1
                  $Hcsp $Hca0 $Hca1 $Hregs $Hstk $Hcstk Hpost]");
        [exact Hstk_heap|exact Hstk_shadow|exact HE|exact Hrmap_ret|].
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
