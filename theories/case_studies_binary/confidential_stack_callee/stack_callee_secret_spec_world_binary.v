From iris.proofmode Require Import proofmode.
From griotte Require Import logrel_binary.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import memory_region memory_region_binary.
From griotte Require Import region_invariants_revocation_binary world_interp_stack_binary.
From griotte Require Import stack_callee_secret_spec_states_binary.

(** * Logical steps of the proofs of [stack_callee_secret_run_spec] and
    [stack_callee_secret_f_spec]

    The lemmas of this file do not execute code:
    - [stack_callee_secret_imports_split], [stack_callee_secret_imports_merge]:
      the two imports of [T], in both runs, used around the block groups
      of [T.run];
    - [stack_callee_secret_world_f]: used at the entry point of [T.f].
      Revoke the world, to get the stack frame of [T.f] in both runs, and
      the revoked temporary addresses [l]. Closing them in the revoked
      world yields a public future world of the initial world, for the
      return of [T.f]. *)

Section Stack_callee_secret_World.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** The imports of [T], in both runs *)
  Lemma stack_callee_secret_imports_cells (pc_b pc_a : Addr) (B_adv : Sealable) :
    (pc_b + 2)%a = Some pc_a ->
    [[ pc_b , pc_a ]] ↦ₐ [[ stack_callee_secret_imports B_adv ]] ∗
    [[ pc_b , pc_a ]] ↣ₐ [[ stack_callee_secret_imports B_adv ]]
    ⊣⊢
    pc_b ↦ₐ stack_callee_secret_switcher_entry ∗
    pc_b ↣ₐ stack_callee_secret_switcher_entry ∗
    (pc_b ^+ 1)%a ↦ₐ WSealed ot_switcher B_adv ∗
    (pc_b ^+ 1)%a ↣ₐ WSealed ot_switcher B_adv.
  Proof.
    intros Himports_contiguous.
    rewrite /stack_callee_secret_imports /stack_callee_secret_switcher_entry.
    rewrite (region_pointsto_cons pc_b (pc_b ^+ 1)%a pc_a); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (pc_b ^+ 1)%a pc_a pc_a); [|solve_addr|solve_addr].
    rewrite (spec_region_pointsto_cons pc_b (pc_b ^+ 1)%a pc_a); [|solve_addr|solve_addr].
    rewrite (spec_region_pointsto_cons (pc_b ^+ 1)%a pc_a pc_a); [|solve_addr|solve_addr].
    rewrite /region_pointsto /spec_region_pointsto finz_seq_between_empty; last solve_addr.
    iSplit.
    - iIntros "[(H0 & H1 & _) (Hs0 & Hs1 & _)]"; iFrame.
    - iIntros "(H0 & Hs0 & H1 & Hs1)"; iFrame.
      by rewrite !big_sepL2_nil.
  Qed.

  Lemma stack_callee_secret_imports_split (pc_b pc_a : Addr) (B_adv : Sealable) :
    (pc_b + 2)%a = Some pc_a ->
    [[ pc_b , pc_a ]] ↦ₐ [[ stack_callee_secret_imports B_adv ]] -∗
    [[ pc_b , pc_a ]] ↣ₐ [[ stack_callee_secret_imports B_adv ]] -∗
    pc_b ↦ₐ stack_callee_secret_switcher_entry ∗
    pc_b ↣ₐ stack_callee_secret_switcher_entry ∗
    (pc_b ^+ 1)%a ↦ₐ WSealed ot_switcher B_adv ∗
    (pc_b ^+ 1)%a ↣ₐ WSealed ot_switcher B_adv.
  Proof.
    iIntros (Himports_contiguous) "H Hs".
    iApply (bi.equiv_entails_1_1 _ _ (stack_callee_secret_imports_cells _ _ _ Himports_contiguous)).
    iFrame.
  Qed.

  Lemma stack_callee_secret_imports_merge (pc_b pc_a : Addr) (B_adv : Sealable) :
    (pc_b + 2)%a = Some pc_a ->
    pc_b ↦ₐ stack_callee_secret_switcher_entry -∗
    pc_b ↣ₐ stack_callee_secret_switcher_entry -∗
    (pc_b ^+ 1)%a ↦ₐ WSealed ot_switcher B_adv -∗
    (pc_b ^+ 1)%a ↣ₐ WSealed ot_switcher B_adv -∗
    [[ pc_b , pc_a ]] ↦ₐ [[ stack_callee_secret_imports B_adv ]] ∗
    [[ pc_b , pc_a ]] ↣ₐ [[ stack_callee_secret_imports B_adv ]].
  Proof.
    iIntros (Himports_contiguous) "H0 Hs0 H1 Hs1".
    iApply (bi.equiv_entails_1_2 _ _ (stack_callee_secret_imports_cells _ _ _ Himports_contiguous)).
    iFrame.
  Qed.

  (** ** Entry point of [T.f]

      Revoke the world, to get the stack frame of [T.f], in both runs. *)
  Lemma stack_callee_secret_world_f W C (csp_b csp_e : Addr) :
    interp W C (WCap RWL Local csp_b csp_e csp_b, WCap RWL Local csp_b csp_e csp_b) -∗
    world_interp W C
    ={⊤}=∗
    ∃ l stk_mem stk_mem_spec,
      ⌜extract_temporaries_condition W (l ++ finz.seq_between csp_b csp_e)⌝ ∗
      ⌜related_sts_pub_world W
         (close_list (l ++ finz.seq_between csp_b csp_e) (revoke W))⌝ ∗
      world_interp (revoke W) C ∗
      ▷ RevokedResources W C l ∗
      [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]] ∗
      [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]].
  Proof.
    iIntros "#Hinterp_csp Hworld_interp".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp]")
      as (l) "(%Hextract & Hworld_interp & _ & _
               & >(%stk_mem & %stk_mem_spec & Hstk & Hsstk) & Hrevoked_l & _)".
    iModIntro.
    iExists l, stk_mem, stk_mem_spec.
    iFrame "Hworld_interp Hstk Hsstk Hrevoked_l".
    iSplit; first done.
    iPureIntro.
    apply related_pub_revoke_close_list.
    by destruct Hextract.
  Qed.

End Stack_callee_secret_World.
