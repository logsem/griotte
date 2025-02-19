From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening addr_reg_sample rules proofmode.
(* From cap_machine Require Import multiple_updates region_invariants_frozen region_invariants_allocation. *)
From cap_machine Require Import switcher.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).
  Implicit Types WC : CVIEW.
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* TODO should depend on the number of registers used by entry point. *)
  Definition is_arg_rmap (rmap : Reg) :=
    dom rmap = {[ ca0 ; ca1 ; ca2 ; ca3 ; ca4 ; ca5 ; ca5 ; ct0 ]}.

  (* TODO:
     - How do we treat our own stack frame?
       I think the ideas is that, we can just to frame it.
     - What are the constraints about w_entry_point?
       I think we just want it to be safe-to-share for
       private transitions of the world.
     - How to encode the number of registers to pass as arguments?
       A possibility is to use a resource that encodes it.
     - Where is the code? Where is MTDC and trusted stack?
       We need to have a switcher state invariant.
   *)
  Lemma switcher_cc_specification
    (E : coPset)
    (W0 W1 : WORLD)
    (C : CmptName)
    (g_switcher : Locality)
    (b_switcher e_switcher a_switcher_cc : Addr)
    (b_stk e_stk a_stk : Addr)
    (ot_switcher : OType)
    (wcgp_caller wcra_caller : Word)
    (w_entry_point : Word)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (φ : val -> iPropI Σ) :

    is_arg_rmap arg_rmap ->
    dom rmap = all_registers_s ∖ ((dom arg_rmap) ∪ {[ PC ; cgp ; cra ; csp ; cs0 ]} ) ->
    (
      PC ↦ᵣ WCap XSRW_ g_switcher b_switcher e_switcher a_switcher_cc
      ∗ cgp ↦ᵣ wcgp_caller
      ∗ cra ↦ᵣ wcra_caller
      ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
      ∗ cs0 ↦ᵣ w_entry_point (* TODO what to write here exactly? *)
      ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W1 C warg )
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

      ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

      ∗ region W0 C ∗ sts_full_world W0 C

      ∗ ( [[ a_stk , e_stk ]] ↦ₐ [[ region_addrs_zeroes a_stk e_stk ]]
          ∗ region W0 C ∗ sts_full_world W0 C
          -∗ region W1 C ∗ sts_full_world W1 C)
      ∗ ▷ ( ∃ (W2 : WORLD) (rmap' : Reg),
              ⌜ related_sts_pub_world W1 W2 C ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ]} ⌝
              ∗ region W2 C ∗ sts_full_world W2 C
              ∗ PC ↦ᵣ updatePcPerm wcra_caller
              ∗ cgp ↦ᵣ wcgp_caller ∗ (∃ wret, cra ↦ᵣ wret)
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ WInt 0 )
              ∗ [[ a_stk , a_stk ]] ↦ₐ [[ region_addrs_zeroes a_stk e_stk ]]
            -∗ WP Seq (Instr Executable) {{ φ }}
          )
    )
    ⊢ WP Seq (Instr Executable) {{ λ v, φ v ∨ ⌜v = FailedV⌝ }}%I.
  Proof.
  Admitted.




End Switcher.
