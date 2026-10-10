From iris.proofmode Require Import proofmode.
From griotte Require Import logrel_binary.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import memory_region memory_region_binary stack_world_resources_binary.
From griotte Require Import stack_secret_spec_states_binary.

(** * Logical steps of the proof of [stack_secret_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [stack_secret_spec_<segment>_blocks_<n>_binary] in the
    proof of [stack_secret_spec]. *)

Section Stack_secret_World.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Splitting the stack

      In both runs, the stack is split into the frame word of [main] at
      [csp_b], the four words spilled by the switcher, the word at
      [csp_b + 5] where [main] leaves a stale copy of the secret, and the
      rest of the stack. *)
  Lemma stack_secret_stack_split (csp_b csp_e : Addr) (stk_mem stk_mem_spec : list Word) :
    (csp_b ^+ 5 < csp_e)%a ->
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]] -∗
    [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]] -∗
    ∃ w_stk0 sw_stk0 stk_lo sstk_lo w_stk5 sw_stk5 stk_hi sstk_hi,
      ⌜ length stk_lo = finz.dist (csp_b ^+ 1)%a (csp_b ^+ 5)%a ⌝ ∗
      ⌜ length sstk_lo = finz.dist (csp_b ^+ 1)%a (csp_b ^+ 5)%a ⌝ ∗
      csp_b ↦ₐ w_stk0 ∗
      csp_b ↣ₐ sw_stk0 ∗
      [[ (csp_b ^+ 1)%a , (csp_b ^+ 5)%a ]] ↦ₐ [[ stk_lo ]] ∗
      [[ (csp_b ^+ 1)%a , (csp_b ^+ 5)%a ]] ↣ₐ [[ sstk_lo ]] ∗
      (csp_b ^+ 5)%a ↦ₐ w_stk5 ∗
      (csp_b ^+ 5)%a ↣ₐ sw_stk5 ∗
      [[ ((csp_b ^+ 5) ^+ 1)%a , csp_e ]] ↦ₐ [[ stk_hi ]] ∗
      [[ ((csp_b ^+ 5) ^+ 1)%a , csp_e ]] ↣ₐ [[ sstk_hi ]].
  Proof.
    iIntros (Hcsp_size) "Hcsp_stk Hscsp_stk".
    iDestruct (big_sepL2_length with "Hcsp_stk") as "%Hlen_stack".
    iDestruct (big_sepL2_length with "Hscsp_stk") as "%Hlen_stack_spec".
    assert ((csp_b + 1)%a = Some (csp_b ^+ 1)%a) as Hcsp1 by solve_addr.
    assert (5 < length stk_mem) as Hlen5.
    { rewrite -Hlen_stack finz_seq_between_length /finz.dist. solve_addr. }
    assert (5 < length stk_mem_spec) as Hlen5_spec.
    { rewrite -Hlen_stack_spec finz_seq_between_length /finz.dist. solve_addr. }
    destruct stk_mem as [|w_stk0 stk_mem]; first (cbn in Hlen5; lia).
    destruct stk_mem_spec as [|sw_stk0 stk_mem_spec]; first (cbn in Hlen5_spec; lia).
    cbn in Hlen5, Hlen5_spec.

    (* The frame word of [main] *)
    iDestruct (region_pointsto_cons csp_b (csp_b ^+ 1)%a csp_e with "Hcsp_stk")
      as "[Hstk0 Hcsp_stk]"; [exact Hcsp1|solve_addr|].
    iDestruct (spec_region_pointsto_cons csp_b (csp_b ^+ 1)%a csp_e with "Hscsp_stk")
      as "[Hsstk0 Hscsp_stk]"; [exact Hcsp1|solve_addr|].

    (* The four words spilled by the switcher, and the rest *)
    assert (length (take 4 stk_mem) = finz.dist (csp_b ^+ 1)%a (csp_b ^+ 5)%a) as Hlen_lo.
    { rewrite length_take Nat.min_l; last lia. rewrite /finz.dist. solve_addr. }
    assert (length (take 4 stk_mem_spec) = finz.dist (csp_b ^+ 1)%a (csp_b ^+ 5)%a)
      as Hlen_lo_spec.
    { rewrite length_take Nat.min_l; last lia. rewrite /finz.dist. solve_addr. }
    rewrite -{1}(take_drop 4 stk_mem).
    iDestruct (region_pointsto_split (csp_b ^+ 1)%a csp_e (csp_b ^+ 5)%a with "Hcsp_stk")
      as "[Hstk_lo Hstk_hi]"; [solve_addr|exact Hlen_lo|].
    rewrite -{1}(take_drop 4 stk_mem_spec).
    iDestruct (spec_region_pointsto_split (csp_b ^+ 1)%a csp_e (csp_b ^+ 5)%a with "Hscsp_stk")
      as "[Hsstk_lo Hsstk_hi]"; [solve_addr|exact Hlen_lo_spec|].

    (* The word at [csp_b + 5] *)
    destruct (drop 4 stk_mem) as [|w_stk5 stk_hi] eqn:Hdrop.
    { exfalso. apply (f_equal length) in Hdrop. rewrite length_drop /= in Hdrop. lia. }
    destruct (drop 4 stk_mem_spec) as [|sw_stk5 sstk_hi] eqn:Hsdrop.
    { exfalso. apply (f_equal length) in Hsdrop. rewrite length_drop /= in Hsdrop. lia. }
    iDestruct (region_pointsto_cons with "Hstk_hi") as "[Hstk5 Hstk_hi]";
      [transitivity (Some ((csp_b ^+ 5) ^+ 1)%a); auto; solve_addr|solve_addr|].
    iDestruct (spec_region_pointsto_cons with "Hsstk_hi") as "[Hsstk5 Hsstk_hi]";
      [transitivity (Some ((csp_b ^+ 5) ^+ 1)%a); auto; solve_addr|solve_addr|].
    iExists w_stk0, sw_stk0, (take 4 stk_mem), (take 4 stk_mem_spec),
      w_stk5, sw_stk5, stk_hi, sstk_hi.
    by iFrame.
  Qed.

  (** ** Preparing the call to [B.f]

      The frame word at [csp_b] stays with [main] during the call: only the
      stack above it, which contains the stale copy of the secret, is given
      to the switcher. It is still revoked in the world of the callee. *)
  Lemma stack_secret_world_call W C (csp_b csp_e : Addr)
    (stk_lo sstk_lo stk_hi sstk_hi : list Word) (w_stk5 sw_stk5 : Word) :
    (csp_b ^+ 5 < csp_e)%a ->
    length stk_lo = finz.dist (csp_b ^+ 1)%a (csp_b ^+ 5)%a ->
    length sstk_lo = finz.dist (csp_b ^+ 1)%a (csp_b ^+ 5)%a ->
    revoked_addresses W (finz.seq_between csp_b csp_e) ->
    StackRevokedResources W C (finz.seq_between csp_b csp_e) -∗
    [[ (csp_b ^+ 1)%a , (csp_b ^+ 5)%a ]] ↦ₐ [[ stk_lo ]] -∗
    [[ (csp_b ^+ 1)%a , (csp_b ^+ 5)%a ]] ↣ₐ [[ sstk_lo ]] -∗
    (csp_b ^+ 5)%a ↦ₐ w_stk5 -∗
    (csp_b ^+ 5)%a ↣ₐ sw_stk5 -∗
    [[ ((csp_b ^+ 5) ^+ 1)%a , csp_e ]] ↦ₐ [[ stk_hi ]] -∗
    [[ ((csp_b ^+ 5) ^+ 1)%a , csp_e ]] ↣ₐ [[ sstk_hi ]] -∗
    StackRevokedResources W C (finz.seq_between (csp_b ^+ 1)%a csp_e) ∗
    ⌜ revoked_addresses W (finz.seq_between (csp_b ^+ 1)%a csp_e) ⌝ ∗
    [[ (csp_b ^+ 1)%a , csp_e ]] ↦ₐ [[ stk_lo ++ w_stk5 :: stk_hi ]] ∗
    [[ (csp_b ^+ 1)%a , csp_e ]] ↣ₐ [[ sstk_lo ++ sw_stk5 :: sstk_hi ]].
  Proof.
    iIntros (Hcsp_size Hlen_lo Hlen_lo_spec Hrevoked_stack)
      "#Hstack_revoked Hstk_lo Hsstk_lo Hstk5 Hsstk5 Hstk_hi Hsstk_hi".
    assert (finz.seq_between csp_b csp_e = [csp_b] ++ finz.seq_between (csp_b ^+ 1)%a csp_e)
      as Hstk_cons.
    { apply finz_seq_between_cons; solve_addr. }
    rewrite Hstk_cons revoked_addresses_app in Hrevoked_stack.
    destruct Hrevoked_stack as [_ Hrevoked_stack].
    iEval (rewrite Hstk_cons StackRevokedResources_app) in "Hstack_revoked".
    iDestruct "Hstack_revoked" as "[_ $]".
    iSplit; first done.
    iSplitL "Hstk_lo Hstk5 Hstk_hi".
    - iApply (region_pointsto_reassemble (csp_b ^+ 1)%a (csp_b ^+ 5)%a csp_e _ _ _
                ltac:(solve_addr) ltac:(solve_addr) ltac:(solve_addr) Hlen_lo
               with "Hstk_lo Hstk5 Hstk_hi").
    - iApply (spec_region_pointsto_reassemble (csp_b ^+ 1)%a (csp_b ^+ 5)%a csp_e _ _ _
                ltac:(solve_addr) ltac:(solve_addr) ltac:(solve_addr) Hlen_lo_spec
               with "Hsstk_lo Hsstk5 Hsstk_hi").
  Qed.

End Stack_secret_World.
