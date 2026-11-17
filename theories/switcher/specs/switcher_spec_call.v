From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region rules proofmode monotone.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import map_simpl register_tactics.
From griotte Require Export switcher_spec_call_gen.
From griotte Require Import switcher_exception.

(** * Functional specification of the switcher's call routine

    The specifications of [switcher_spec_call_gen], instantiated with the
    trap safety of the switcher ([switcher_trap_safety_intro]). *)

Section Switcher.
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

  Lemma switcher_cc_specification
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (w_entry_point : Sealable)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (nargs : nat)
    (mshwm_v : Z)
    :
    let wct1_caller := WSealed ot_switcher w_entry_point in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    (* The caller's stack starts at the base of the thread's stack, and ends
       in it *)
    b_stk = cstk_hwm_base cstk ->
    (e_stk <= cstk_hwm_top cstk)%a ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->
    (* The caller's compartment is in exclusive mode *)
    cmpt_shared C = false ->

    (* The thread runs in the caller's compartment *)
    thread_in th C
    (* Trusted-stack invariant *)
    ∗ na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    ∗ na_own (tpool th) ⊤
    (* Registers *)
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ[th] wcgp_caller
    ∗ cra ↦ᵣ[th] wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ[th] wct1_caller ∗ interp W C wct1_caller
    ∗ w_entry_point ↦ₑ□{nargs} nargs
    ∗ cs0 ↦ᵣ[th] wcs0_caller
    ∗ cs1 ↦ᵣ[th] wcs1_caller
    (* Argument registers, need to be safe-to-share *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg
                                      ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                                        then interp W C warg
                                        else True )
    (* All the other registers *)
    ∗ regs[th] rmap

    (* Stack frame *)
    ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
    (* The high-water-mark registers *)
    ∗ hwm_res cstk mshwm_v

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
    ∗ ⌜ revoked_addresses W (stk_free b_stk e_stk a_stk) ⌝
    ∗ ◯(CSTK)[th] cstk
    ∗ interp_continuation cstk Ws Cs
    (* The switcher's entry disables interrupts *)
    ∗ MIE ↦ₜ[th] InterruptDisabled
    ∗ held (th := th) InterruptDisabled

    (* POST-CONDITION *)
    ∗ ( ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem : list LWord) l' rcgp rcra rcs0 rcs1
              (m : InterruptStatus),
              (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2
                (l' ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_keys (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world
                  (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region b_stk e_stk a_stk,
                 ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (stk_free b_stk e_stk a_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (stk_free b_stk e_stk a_stk) ⌝
            ∗ na_own (tpool th) ⊤
            ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ ◯(CSTK)[th] cstk
            ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ[th] rcgp
            ∗ cra ↦ᵣ[th] rcra
            ∗ cs0 ↦ᵣ[th] rcs0
            ∗ cs1 ↦ᵣ[th] rcs1
            ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ[th] warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ[th] warg1 ∗ interp W2 C warg1)
            ∗ regs₀[th] rmap'
            ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
            (* MSHWM is the caller's stack pointer when the call went
               through, and at most its value at the call otherwise *)
            ∗ (∃ mshwm_v' : Z, ⌜ (mshwm_v' <= Z.max mshwm_v a_stk)%Z ⌝ ∗ hwm_res cstk mshwm_v')
            ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
            (* The caller resumes at the posture of its return sentry *)
            ∗ ⌜route_pre th (default m (jalr_target_mie rcra.(lw)))⌝
            ∗ MIE ↦ₜ[th] default m (jalr_target_mie rcra.(lw))
            ∗ held (th := th) (default m (jalr_target_mie rcra.(lw)))
              -∗ safe[th])
        ∧
        (* FAULT --- the callee-save registers do not fit on the caller's stack *)
        switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
          b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v )

    ⊢ safe[th].
  Proof.
    iIntros (target Hstk_shadow Hstk_heap Hb_a Hbase Htop Hdom Hrdom Hret_jalr Hret_heap Hsh)
      "(#Hthread & #Hswitcher & #Hstatic & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & #Hentry & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hhwm & Hworld_interp & Hstk_val & % & Hcstk
    & Hcont & Hmie & Hheld & Hpost)".
    iPoseProof (switcher_trap_safety_intro with "[$Hswitcher $Hstatic]") as "#Hsafety".
    iEval (rewrite -(world_resources_exclusive W C Hsh)) in "Hworld_interp".
    iApply (switcher_cc_specification_gen_revoked W C
      wcgp_caller wcra_caller wcs0_caller wcs1_caller target
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs true mshwm_v).
    1-9: eauto.
    iFrame "Hthread Hsafety Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1 Hargs Hregs
      Hstk Hhwm Hworld_interp Hstk_val Hcstk Hcont Hmie Hheld".
    iFrame "Hentry".
    iFrame "%".
    iSplitR.
    { subst target; cbn.
      destruct ((ot_switcher =? ot_switcher)%Z); eauto. }
    iSplitR; first done.
    iSplit; last by iDestruct "Hpost" as "[_ $]".
    iDestruct "Hpost" as "[Hpost _]".
    iNext.
    iIntros (W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1 m) "Hnew".
    iDestruct "Hnew" as
      "(%Hextract & Hrev & %Hrevoked & %Hrelated & Hstd & %Hdom_ret
      & Hstack & %Hrevstack & Hna & %Hbounds & Hworld & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Harg0 & Harg1
      & Hrmap & Hstk & Hhwm & Hcont & %Hloaded & %Hpre_ret & Hmie & Hheld)".
    destruct Hloaded as (Hgp & Hra & Hs0 & Hs1).
    assert (load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
            load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1)
      as Hloaded by (repeat split; assumption).
    iAssert (world_interp (revoke W2) C) with "[Hworld]" as "Hworld".
    { iEval (rewrite world_resources_split perm_resources_exclusive //) in "Hworld".
      rewrite world_interp_eq. iDestruct "Hworld" as "[$ $]". }
    iApply ("Hpost" $! W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1 m with
      "[$Hrev $Hstd $Hstack $Hna $Hworld $Hcstk $HPC $Hcgp $Hcra
        $Hcs0 $Hcs1 $Hcsp $Harg0 $Harg1 $Hrmap $Hstk $Hhwm $Hcont $Hmie $Hheld]").
    iFrame "%".
  Qed.

  (** [switcher_cc_specification] for a caller that holds its world as the
      world premise of its regime: in a shared compartment, its local map
      and the invariant of the map of Permanent regions. *)
  Lemma switcher_cc_specification_shared
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (w_entry_point : Sealable)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (nargs : nat)
    (mshwm_v : Z)
    :
    let wct1_caller := WSealed ot_switcher w_entry_point in
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    (* The caller's stack starts at the base of the thread's stack, and ends
       in it *)
    b_stk = cstk_hwm_base cstk ->
    (e_stk <= cstk_hwm_top cstk)%a ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->

    (* The thread runs in the caller's compartment *)
    thread_in th C
    (* Trusted-stack invariant *)
    ∗ na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    ∗ na_own (tpool th) ⊤
    (* Registers *)
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ[th] wcgp_caller
    ∗ cra ↦ᵣ[th] wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ[th] wct1_caller ∗ interp W C wct1_caller
    ∗ w_entry_point ↦ₑ□{nargs} nargs
    ∗ cs0 ↦ᵣ[th] wcs0_caller
    ∗ cs1 ↦ᵣ[th] wcs1_caller
    (* Argument registers, need to be safe-to-share *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg
                                      ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                                        then interp W C warg
                                        else True )
    (* All the other registers *)
    ∗ regs[th] rmap

    (* Stack frame *)
    ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
    (* The high-water-mark registers *)
    ∗ hwm_res cstk mshwm_v

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_resources W C
    ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
    ∗ ⌜ revoked_addresses W (stk_free b_stk e_stk a_stk) ⌝
    ∗ ◯(CSTK)[th] cstk
    ∗ interp_continuation cstk Ws Cs
    (* The switcher's entry disables interrupts *)
    ∗ MIE ↦ₜ[th] InterruptDisabled
    ∗ held (th := th) InterruptDisabled

    (* POST-CONDITION *)
    ∗ ( ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem : list LWord) l' rcgp rcra rcs0 rcs1
              (m : InterruptStatus),
              (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2
                (l' ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_keys (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world
                  (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region b_stk e_stk a_stk,
                 ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (stk_free b_stk e_stk a_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (stk_free b_stk e_stk a_stk) ⌝
            ∗ na_own (tpool th) ⊤
            ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
            (* Interpretation of the world *)
            ∗ world_resources (revoke W2) C
            ∗ ◯(CSTK)[th] cstk
            ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ[th] rcgp
            ∗ cra ↦ᵣ[th] rcra
            ∗ cs0 ↦ᵣ[th] rcs0
            ∗ cs1 ↦ᵣ[th] rcs1
            ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ[th] warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ[th] warg1 ∗ interp W2 C warg1)
            ∗ regs₀[th] rmap'
            ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
            (* MSHWM is the caller's stack pointer when the call went
               through, and at most its value at the call otherwise *)
            ∗ (∃ mshwm_v' : Z, ⌜ (mshwm_v' <= Z.max mshwm_v a_stk)%Z ⌝ ∗ hwm_res cstk mshwm_v')
            ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1⌝
            (* The caller resumes at the posture of its return sentry *)
            ∗ ⌜route_pre th (default m (jalr_target_mie rcra.(lw)))⌝
            ∗ MIE ↦ₜ[th] default m (jalr_target_mie rcra.(lw))
            ∗ held (th := th) (default m (jalr_target_mie rcra.(lw)))
              -∗ safe[th])
        ∧
        (* FAULT --- the callee-save registers do not fit on the caller's stack *)
        switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
          b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v )

    ⊢ safe[th].
  Proof.
    iIntros (target Hstk_shadow Hstk_heap Hb_a Hbase Htop Hdom Hrdom Hret_jalr Hret_heap)
      "(#Hthread & #Hswitcher & #Hstatic & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & #Hentry & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hhwm & Hworld_interp & Hstk_val & % & Hcstk
    & Hcont & Hmie & Hheld & Hpost)".
    iPoseProof (switcher_trap_safety_intro with "[$Hswitcher $Hstatic]") as "#Hsafety".
    iApply (switcher_cc_specification_gen_revoked W C
      wcgp_caller wcra_caller wcs0_caller wcs1_caller target
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs true mshwm_v).
    1-9: eauto.
    iFrame "Hthread Hsafety Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1 Hargs Hregs
      Hstk Hhwm Hworld_interp Hstk_val Hcstk Hcont Hmie Hheld".
    iFrame "Hentry".
    iFrame "%".
    iSplitR.
    { subst target; cbn.
      destruct ((ot_switcher =? ot_switcher)%Z); eauto. }
    iSplitR; first done.
    iSplit; last by iDestruct "Hpost" as "[_ $]".
    iDestruct "Hpost" as "[Hpost _]".
    iNext.
    iIntros (W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1 m) "Hnew".
    iDestruct "Hnew" as
      "(%Hextract & Hrev & %Hrevoked & %Hrelated & Hstd & %Hdom_ret
      & Hstack & %Hrevstack & Hna & %Hbounds & Hworld & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Harg0 & Harg1
      & Hrmap & Hstk & Hhwm & Hcont & %Hloaded & %Hpre_ret & Hmie & Hheld)".
    destruct Hloaded as (Hgp & Hra & Hs0 & Hs1).
    assert (load_heap wcgp_caller rcgp ∧ load_heap wcra_caller rcra ∧
            load_heap wcs0_caller rcs0 ∧ load_heap wcs1_caller rcs1)
      as Hloaded by (repeat split; assumption).
    iApply ("Hpost" $! W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1 m with
      "[$Hrev $Hstd $Hstack $Hna $Hworld $Hcstk $HPC $Hcgp $Hcra
        $Hcs0 $Hcs1 $Hcsp $Harg0 $Harg1 $Hrmap $Hstk $Hhwm $Hcont $Hmie $Hheld]").
    iFrame "%".
  Qed.

  Lemma switcher_cc_specification_alt
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list LWord)
    (arg_rmap rmap : LReg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (mshwm_v : Z)
    :
    disjoint_from_mmio b_stk e_stk ->
    disjoint_from_heap b_stk e_stk ->
    (* The caller's stack pointer is in the stack, on the side of its used part *)
    stk_cursor_ok b_stk e_stk a_stk ->
    (* The caller's stack starts at the base of the thread's stack, and ends
       in it *)
    b_stk = cstk_hwm_base cstk ->
    (e_stk <= cstk_hwm_top cstk)%a ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    (* The caller returns to a valid target, outside the heap *)
    jalr_target_ok cnull cra wcra_caller.(lw) = true ->
    is_heap_cap wcra_caller.(lw) = false ->
    (* The caller's compartment is in exclusive mode *)
    cmpt_shared C = false ->

    (* The thread runs in the caller's compartment *)
    thread_in th C
    (* Trusted-stack invariant *)
    ∗ na_inv (tpool th) Ntstack trusted_stack_inv
    ∗ switcher_static

    (* PRE-CONDITION *)
    ∗ na_own (tpool th) ⊤
    (* Registers *)
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ[th] wcgp_caller
    ∗ cra ↦ᵣ[th] wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ[th] wct1_caller ∗ (if is_sealed_with_o wct1_caller.(lw) ot_switcher then interp W C wct1_caller else True)
    ∗ cs0 ↦ᵣ[th] wcs0_caller
    ∗ cs1 ↦ᵣ[th] wcs1_caller
    (* Argument registers, need to be safe-to-share *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗ interp W C warg )
    (* All the other registers *)
    ∗ regs[th] rmap

    (* Stack frame *)
    ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
    (* The high-water-mark registers *)
    ∗ hwm_res cstk mshwm_v

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (stk_free b_stk e_stk a_stk)
    ∗ ⌜ revoked_addresses W (stk_free b_stk e_stk a_stk) ⌝
    ∗ ◯(CSTK)[th] cstk
    ∗ interp_continuation cstk Ws Cs
    (* The switcher's entry disables interrupts *)
    ∗ MIE ↦ₜ[th] InterruptDisabled
    ∗ held (th := th) InterruptDisabled

    (* POST-CONDITION *)
    ∗ ( ▷ ( ∀ (W2 : WORLD) (rmap' : LReg) (stk_mem : list LWord) l' rcgp rcra rcs0 rcs1
              (m : InterruptStatus),
            (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2
                (l' ++ (LNonHeap <$> callee_stk_region b_stk e_stk a_stk)) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_keys (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world
                  (std_update_multiple W (callee_stk_region b_stk e_stk a_stk) Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region b_stk e_stk a_stk,
                 ⌜ std W2 !! LNonHeap a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (stk_free b_stk e_stk a_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (stk_free b_stk e_stk a_stk) ⌝
            ∗ na_own (tpool th) ⊤
            ∗ ⌜ callee_stk_bounds b_stk e_stk a_stk ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ ◯(CSTK)[th] cstk
            ∗ PC ↦ₚ[th] lupdatePcPerm (rcra)
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ[th] rcgp
            ∗ cra ↦ᵣ[th] rcra
            ∗ cs0 ↦ᵣ[th] rcs0
            ∗ cs1 ↦ᵣ[th] rcs1
            ∗ csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ[th] warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ[th] warg1 ∗ interp W2 C warg1)
            ∗ regs₀[th] rmap'
            ∗ stack_region (stk_free_b b_stk a_stk) (stk_free_e e_stk a_stk) stk_mem
            (* MSHWM is the caller's stack pointer when the call went
               through, and at most its value at the call otherwise *)
            ∗ (∃ mshwm_v' : Z, ⌜ (mshwm_v' <= Z.max mshwm_v a_stk)%Z ⌝ ∗ hwm_res cstk mshwm_v')
            ∗ interp_continuation cstk Ws Cs
              ∗ ⌜load_heap wcgp_caller rcgp ∧
                load_heap wcra_caller rcra ∧
                load_heap wcs0_caller rcs0 ∧
                load_heap wcs1_caller rcs1⌝
            (* The caller resumes at the posture of its return sentry *)
            ∗ ⌜route_pre th (default m (jalr_target_mie rcra.(lw)))⌝
            ∗ MIE ↦ₜ[th] default m (jalr_target_mie rcra.(lw))
            ∗ held (th := th) (default m (jalr_target_mie rcra.(lw)))
              -∗ safe[th])
        ∧
        (* FAULT --- the callee-save registers do not fit on the caller's stack *)
        switcher_cc_fault W C wcgp_caller wcra_caller wcs0_caller wcs1_caller
          b_stk e_stk a_stk stk_mem cstk Ws Cs mshwm_v )

    ⊢ safe[th].
  Proof.
    iIntros (Hstk_shadow Hstk_heap Hb_a Hbase Htop Hdom Hrdom Hret_jalr Hret_heap Hsh)
      "(#Hthread & #Hswitcher & #Hstatic & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hhwm & Hworld_interp & Hstk_val & % & Hcstk & Hcont
    & Hmie & Hheld & Hpost)".
    iPoseProof (switcher_trap_safety_intro with "[$Hswitcher $Hstatic]") as "#Hsafety".
    iEval (rewrite -(world_resources_exclusive W C Hsh)) in "Hworld_interp".
    iApply (switcher_cc_specification_gen_revoked W C
      wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
      b_stk e_stk a_stk stk_mem arg_rmap rmap cstk Ws Cs false mshwm_v).
    1-9: eauto.
    iFrame "Hthread Hsafety Hna HPC Hcgp Hcra Hcsp Hct1 Hcs0 Hcs1 Hargs Hregs
      Hstk Hhwm Hworld_interp Hstk_val Hcstk Hcont Hmie Hheld".
    iFrame "Htarget_v".
    iFrame "%".
    iSplit; last by iDestruct "Hpost" as "[_ $]".
    iDestruct "Hpost" as "[Hpost _]".
    iNext.
    iIntros (W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1 m) "Hnew".
    iDestruct "Hnew" as
      "(%Hextract & Hrev & %Hrevoked & %Hrelated & Hstd & %Hdom_ret
      & Hstack & %Hrevstack & Hna & %Hbounds & Hworld & Hcstk
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Harg0 & Harg1
      & Hrmap & Hstk & Hhwm & Hcont & %Hloaded & %Hpre_ret & Hmie & Hheld)".
    iAssert (world_interp (revoke W2) C) with "[Hworld]" as "Hworld".
    { iEval (rewrite world_resources_split perm_resources_exclusive //) in "Hworld".
      rewrite world_interp_eq. iDestruct "Hworld" as "[$ $]". }
    iApply ("Hpost" $! W2 rmap' stk_mem0 l' rcgp rcra rcs0 rcs1 m with
      "[$Hrev $Hstd $Hstack $Hna $Hworld $Hcstk $HPC $Hcgp $Hcra
        $Hcs0 $Hcs1 $Hcsp $Harg0 $Harg1 $Hrmap $Hstk $Hhwm $Hcont $Hmie $Hheld]").
    iFrame "%".
  Qed.

End Switcher.
