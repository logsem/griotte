From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import switcher_spec_call_binary.

(** * Calling an untrusted compartment with identical caller-saved registers

    The trusted callers of the binary case studies call the switcher with
    the same [cgp], [cra], [cs0] and [cs1] in both runs. This file states
    the switcher-call specification for such callers, and helper lemmas to
    build the argument registers of the call. *)

Section Switcher_call_diag.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** [switcher_cc_specification], when the caller-saved registers hold the
      same words in both runs. *)
  Lemma switcher_cc_specification_diag
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (w_entry_point : Sealable)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (nargs : nat)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher w_entry_point in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cgp ↣ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    ∗ cra ↣ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ interp W C (wct1_caller, wct1_caller)
    ∗ wct1_caller ↦□ₑ nargs
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs0 ↣ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    ∗ cs1 ↣ᵣ wcs1_caller
    (* Argument registers, need to be related *)
    ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
          rarg ↦ᵣ warg
          ∗ rarg ↣ᵣ sarg
          ∗ if decide (rarg ∈ dom_arg_rmap nargs)
            then interp W C (warg, sarg)
            else True )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem stk_mem_spec : list Word) l',
            ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_addresses (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⤇ Seq (Instr Executable)
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag (map fst stk)
            ∗ cstack_frag_spec (map snd stk)
            ∗ PC ↦ᵣ updatePcPerm wcra_caller
            ∗ PC ↣ᵣ updatePcPerm wcra_caller
            ∗ cgp ↦ᵣ wcgp_caller
            ∗ cgp ↣ᵣ wcgp_caller
            ∗ cra ↦ᵣ wcra_caller
            ∗ cra ↣ᵣ wcra_caller
            ∗ cs0 ↦ᵣ wcs0_caller
            ∗ cs0 ↣ᵣ wcs0_caller
            ∗ cs1 ↦ᵣ wcs1_caller
            ∗ cs1 ↣ᵣ wcs1_caller
            ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0.1 ∗ ca0 ↣ᵣ warg0.2 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1.1 ∗ ca1 ↣ᵣ warg1.2 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]
            ∗ interp_continuation stk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    exact (switcher_cc_specification Nswitcher W C
             (wcgp_caller, wcgp_caller) (wcra_caller, wcra_caller)
             (wcs0_caller, wcs0_caller) (wcs1_caller, wcs1_caller)
             b_stk e_stk a_stk w_entry_point stk_mem stk_mem_spec
             arg_rmap arg_smap rmap smap stk Ws Cs nargs).
  Qed.

  (** ** Argument registers *)

  Lemma arg_rmap_interp (W : WORLD) (C : CmptName) (nargs : nat) (r : RegName) (ww : Word * Word) :
    interp W C ww -∗
    if decide (r ∈ dom_arg_rmap nargs) then interp W C ww else True.
  Proof. iIntros "H". by destruct (decide _). Qed.

  Lemma arg_rmap_zero_interp (W : WORLD) (C : CmptName) (nargs : nat) (r : RegName) :
    ⊢ if decide (r ∈ dom_arg_rmap nargs) then interp W C (WInt 0, WInt 0) else True.
  Proof. iApply arg_rmap_interp. iApply interp_int. Qed.

  Lemma arg_rmap_notin_interp (W : WORLD) (C : CmptName) (nargs : nat) (r : RegName) (ww : Word * Word) :
    r ∉ dom_arg_rmap nargs →
    ⊢ if decide (r ∈ dom_arg_rmap nargs) then interp W C ww else True.
  Proof. intros Hr. by rewrite decide_False. Qed.

  (** The map of the argument registers of a call, built from its registers. *)
  Definition arg_rmap_of (w0 w1 w2 w3 w4 w5 w6 : Word) : Reg :=
    {[ ca0 := w0; ca1 := w1; ca2 := w2; ca3 := w3; ca4 := w4; ca5 := w5; ct0 := w6 ]}.

  Lemma is_arg_rmap_of (w0 w1 w2 w3 w4 w5 w6 : Word) :
    is_arg_rmap (arg_rmap_of w0 w1 w2 w3 w4 w5 w6) 8.
  Proof. rewrite /is_arg_rmap /arg_rmap_of /dom_arg_rmap /=. set_solver. Qed.

  Lemma arg_rmap_prepare (W : WORLD) (C : CmptName) (nargs : nat)
    (w0 w1 w2 w3 w4 w5 w6 s0 s1 s2 s3 s4 s5 s6 : Word) :
    ca0 ↦ᵣ w0 -∗ ca0 ↣ᵣ s0 -∗
    (if decide (ca0 ∈ dom_arg_rmap nargs) then interp W C (w0, s0) else True) -∗
    ca1 ↦ᵣ w1 -∗ ca1 ↣ᵣ s1 -∗
    (if decide (ca1 ∈ dom_arg_rmap nargs) then interp W C (w1, s1) else True) -∗
    ca2 ↦ᵣ w2 -∗ ca2 ↣ᵣ s2 -∗
    (if decide (ca2 ∈ dom_arg_rmap nargs) then interp W C (w2, s2) else True) -∗
    ca3 ↦ᵣ w3 -∗ ca3 ↣ᵣ s3 -∗
    (if decide (ca3 ∈ dom_arg_rmap nargs) then interp W C (w3, s3) else True) -∗
    ca4 ↦ᵣ w4 -∗ ca4 ↣ᵣ s4 -∗
    (if decide (ca4 ∈ dom_arg_rmap nargs) then interp W C (w4, s4) else True) -∗
    ca5 ↦ᵣ w5 -∗ ca5 ↣ᵣ s5 -∗
    (if decide (ca5 ∈ dom_arg_rmap nargs) then interp W C (w5, s5) else True) -∗
    ct0 ↦ᵣ w6 -∗ ct0 ↣ᵣ s6 -∗
    (if decide (ct0 ∈ dom_arg_rmap nargs) then interp W C (w6, s6) else True) -∗
    ( [∗ map] rarg↦warg;sarg ∈ arg_rmap_of w0 w1 w2 w3 w4 w5 w6; arg_rmap_of s0 s1 s2 s3 s4 s5 s6,
        rarg ↦ᵣ warg
        ∗ rarg ↣ᵣ sarg
        ∗ if decide (rarg ∈ dom_arg_rmap nargs)
          then interp W C (warg, sarg)
          else True ).
  Proof.
    iIntros "H0 Hs0 Hi0 H1 Hs1 Hi1 H2 Hs2 Hi2 H3 Hs3 Hi3 H4 Hs4 Hi4 H5 Hs5 Hi5 H6 Hs6 Hi6".
    rewrite /arg_rmap_of.
    repeat (rewrite big_sepM2_insert; [|by simplify_map_eq|by simplify_map_eq]).
    rewrite big_sepM2_empty.
    iFrame.
  Qed.

End Switcher_call_diag.
