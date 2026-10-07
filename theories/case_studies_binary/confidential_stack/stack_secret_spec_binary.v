From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary map_simpl.
From griotte Require Import switcher_preamble_binary switcher_spec_call_binary.
From griotte Require Import fetch_spec_binary switcher_spec_call_diag_binary stack_secret_binary.

(** * Binary specification of the stack confidentiality example

    Both runs execute [stack_secret_main_code], with a different secret in
    the private data of the trusted compartment ([secret1] in the
    implementation run, [secret2] in the specification run). The
    specification holds for arbitrary secrets, and is used in both
    directions of the adequacy theorem.

    [main] calls the adversary with its stack pointer at [csp_b + 1]: the
    word at [csp_b], which holds the secret, stays privately owned by [main]
    during the call, and the switcher receives the stack from [csp_b + 1] to
    [csp_e], whose word at [csp_b + 5] also holds the secret. *)

(** Splitting a region at one address, in both runs. *)
Section Region_reassemble.
  Context {Σ:gFunctors} {ceriseg:ceriseG Σ} {specg : specG Σ} `{MP: MachineParameters}.

  Lemma region_pointsto_reassemble (b a e : Addr) (lo hi : list Word) (w : Word) :
    (b <= a)%a →
    (a ^+ 1 <= e)%a →
    (a + 1)%a = Some (a ^+ 1)%a →
    length lo = finz.dist b a →
    [[ b, a ]] ↦ₐ [[ lo ]] -∗
    a ↦ₐ w -∗
    [[ (a ^+ 1)%a, e ]] ↦ₐ [[ hi ]] -∗
    [[ b, e ]] ↦ₐ [[ lo ++ w :: hi ]].
  Proof.
    iIntros (Hba Hae Ha Hlen) "Hlo Hw Hhi".
    rewrite (region_pointsto_split b e a lo (w :: hi)); [|solve_addr|done].
    rewrite (region_pointsto_cons a (a ^+ 1)%a e); [|done|done].
    iFrame.
  Qed.

  Lemma spec_region_pointsto_reassemble (b a e : Addr) (lo hi : list Word) (w : Word) :
    (b <= a)%a →
    (a ^+ 1 <= e)%a →
    (a + 1)%a = Some (a ^+ 1)%a →
    length lo = finz.dist b a →
    [[ b, a ]] ↣ₐ [[ lo ]] -∗
    a ↣ₐ w -∗
    [[ (a ^+ 1)%a, e ]] ↣ₐ [[ hi ]] -∗
    [[ b, e ]] ↣ₐ [[ lo ++ w :: hi ]].
  Proof.
    iIntros (Hba Hae Ha Hlen) "Hlo Hw Hhi".
    rewrite (spec_region_pointsto_split b e a lo (w :: hi)); [|solve_addr|done].
    rewrite (spec_region_pointsto_cons a (a ^+ 1)%a e); [|done|done].
    iFrame.
  Qed.

End Region_reassemble.

Section Stack_secret.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .
  Context {B : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The stack must contain the frame word of [main], the four words
      spilled by the switcher, and the stale copy. *)
  Lemma stack_secret_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (B_f : Sealable)

    (W_init : WORLD)

    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)

    (stk_mem stk_mem_spec : list Word)
    (secret1 secret2 : Z)

    (Nswitcher : namespace)
    :

    let imports := stack_secret_main_imports B_f in

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_secret_main_code)%a ->

    (cgp_b + length (stack_secret_main_data secret1))%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->
    (csp_b ^+ 5 < csp_e)%a ->

    (* The stack region is revoked in the world of B. *)
    revoked_addresses W_init (finz.seq_between csp_b csp_e) ->

    (
      na_inv cerise_nais Nswitcher switcher_inv_binary
      ∗ spec_ctx
      ∗ na_own cerise_nais ⊤
      ∗ ⤇ Seq (Instr Executable)

      (* initial register files *)
      ∗ PC ↦ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ PC ↣ᵣ WCap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )

      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ [[ pc_b , pc_a ]] ↣ₐ [[ imports ]]
      ∗ codefrag pc_a stack_secret_main_code
      ∗ spec_codefrag pc_a stack_secret_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ stack_secret_main_data secret1 ]]
      ∗ [[ cgp_b , cgp_e ]] ↣ₐ [[ stack_secret_main_data secret2 ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      ∗ [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]]

      ∗ world_interp W_init B
      ∗ interp_continuation stk Ws Cs
      ∗ cstack_frag (map fst stk)
      ∗ cstack_frag_spec (map snd stk)

      ∗ interp W_init B (WSealed ot_switcher B_f, WSealed ot_switcher B_f)
      ∗ (WSealed ot_switcher B_f) ↦□ₑ stack_secret_B_f_args
      ∗ StackRevokedResources W_init B (finz.seq_between csp_b csp_e)

      ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (Hrmap_dom HsubBounds Hcgp_contiguous Himports_contiguous Hcsp_size Hrevoked_stack)
      "(#Hswitcher & #Hspec & Hna & Hj
      & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hrmap
      & Himports_main & Hsimports_main & Hcode_main & Hscode_main
      & Hcgp_main & Hscgp_main & Hcsp_stk & Hscsp_stk
      & Hworld_interp_B & HK & Hcstk_frag & Hcstk_frag_spec
      & #Hinterp_Winit_B_f & #HentryB_f & #Hstack_revoked_B)".
    codefrag_facts "Hcode_main".
    rewrite /stack_secret_main_data /= in Hcgp_contiguous.
    rewrite /stack_secret_main_imports /= in Himports_contiguous.
    iDestruct (big_sepL2_length with "Hcsp_stk") as "%Hlen_stack".
    iDestruct (big_sepL2_length with "Hscsp_stk") as "%Hlen_stack_spec".

    (* Extract the needed registers from the register map *)
    iExtractList "Hrmap" [ctp;ct0;ct1;cs0;cs1;cra]
      as ["Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra"].
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".
    iDestruct "Hcs0" as "(Hcs0 & Hscs0 & ->)".
    iDestruct "Hcs1" as "(Hcs1 & Hscs1 & ->)".
    iDestruct "Hcra" as "(Hcra & Hscra & ->)".

    (* Extract the secret *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hsecret _]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hscgp_main") as "[Hssecret _]".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

    (* Extract the imports *)
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_switcher Himports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (region_pointsto_cons with "Himports_main") as "[Himport_B_f _]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hsimports_main") as "[Hsimport_switcher Hsimports_main]".
    { transitivity (Some (pc_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hsimports_main") as "[Hsimport_B_f _]".
    { transitivity (Some (pc_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Split the stack: [csp_b] is the frame word of [main], [csp_b + 5] the
       stale copy, the rest is untouched. *)
    assert ((csp_b + 1)%a = Some (csp_b ^+ 1)%a) as Hcsp1 by solve_addr.
    assert (((csp_b ^+ 1) + 4)%a = Some (csp_b ^+ 5)%a) as Hcsp5 by solve_addr.
    assert (((csp_b ^+ 5) + -4)%a = Some (csp_b ^+ 1)%a) as Hcsp5' by solve_addr.
    assert (5 < length stk_mem) as Hlen5.
    { rewrite -Hlen_stack finz_seq_between_length /finz.dist. solve_addr. }
    assert (5 < length stk_mem_spec) as Hlen5_spec.
    { rewrite -Hlen_stack_spec finz_seq_between_length /finz.dist. solve_addr. }
    destruct stk_mem as [|w_stk0 stk_mem]; first (cbn in Hlen5; lia).
    destruct stk_mem_spec as [|sw_stk0 stk_mem_spec]; first (cbn in Hlen5_spec; lia).
    cbn in Hlen5, Hlen5_spec.
    iDestruct (region_pointsto_cons csp_b (csp_b ^+ 1)%a csp_e with "Hcsp_stk")
      as "[Hstk0 Hcsp_stk]".
    { exact Hcsp1. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons csp_b (csp_b ^+ 1)%a csp_e with "Hscsp_stk")
      as "[Hsstk0 Hscsp_stk]".
    { exact Hcsp1. }
    { solve_addr. }

    assert (length (take 4 stk_mem) = finz.dist (csp_b ^+ 1)%a (csp_b ^+ 5)%a) as Hlen_lo.
    { rewrite length_take Nat.min_l; last lia. rewrite /finz.dist. solve_addr. }
    assert (length (take 4 stk_mem_spec) = finz.dist (csp_b ^+ 1)%a (csp_b ^+ 5)%a) as Hlen_lo_spec.
    { rewrite length_take Nat.min_l; last lia. rewrite /finz.dist. solve_addr. }
    rewrite -{1}(take_drop 4 stk_mem).
    iDestruct (region_pointsto_split (csp_b ^+ 1)%a csp_e (csp_b ^+ 5)%a with "Hcsp_stk")
      as "[Hstk_lo Hstk_hi]".
    { solve_addr. }
    { exact Hlen_lo. }
    destruct (drop 4 stk_mem) as [|w_stk5 stk_hi] eqn:Hdrop.
    { exfalso. apply (f_equal length) in Hdrop. rewrite length_drop /= in Hdrop. lia. }
    iDestruct (region_pointsto_cons with "Hstk_hi") as "[Hstk5 Hstk_hi]".
    { transitivity (Some ((csp_b ^+ 5) ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    rewrite -{1}(take_drop 4 stk_mem_spec).
    iDestruct (spec_region_pointsto_split (csp_b ^+ 1)%a csp_e (csp_b ^+ 5)%a with "Hscsp_stk")
      as "[Hsstk_lo Hsstk_hi]".
    { solve_addr. }
    { exact Hlen_lo_spec. }
    destruct (drop 4 stk_mem_spec) as [|sw_stk5 sstk_hi] eqn:Hsdrop.
    { exfalso. apply (f_equal length) in Hsdrop. rewrite length_drop /= in Hsdrop. lia. }
    iDestruct (spec_region_pointsto_cons with "Hsstk_hi") as "[Hsstk5 Hsstk_hi]".
    { transitivity (Some ((csp_b ^+ 5) ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }

    (* The frame word at [csp_b] stays with [main] during the call: only
       the stack above it is given to the switcher. *)
    assert (finz.seq_between csp_b csp_e = [csp_b] ++ finz.seq_between (csp_b ^+ 1)%a csp_e)
      as Hstk_cons.
    { apply finz_seq_between_cons; solve_addr. }
    rewrite Hstk_cons revoked_addresses_app in Hrevoked_stack.
    destruct Hrevoked_stack as [_ Hrevoked_stack].
    iEval (rewrite Hstk_cons StackRevokedResources_app) in "Hstack_revoked_B".
    iDestruct "Hstack_revoked_B" as "[_ #Hstack_revoked_B']".

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ------------ BLOCK 0 : SECRET ON STACK ------------ *)
    (* --------------------------------------------------- *)

    focus_block_0_lockstep "Hscode_main" "Hcode_main" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Load ct0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [done| solve_addr].

    (* Store csp ct0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Lea csp 4 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Store csp ct0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* Lea csp (-4) *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* Reassemble the stack given to the switcher, which contains the stale
       copies of the secrets *)
    iDestruct (region_pointsto_reassemble (csp_b ^+ 1)%a (csp_b ^+ 5)%a csp_e _ _ _
                 ltac:(solve_addr) ltac:(solve_addr) ltac:(solve_addr) Hlen_lo
                with "Hstk_lo Hstk5 Hstk_hi") as "Hcsp_stk".
    iDestruct (spec_region_pointsto_reassemble (csp_b ^+ 1)%a (csp_b ^+ 5)%a csp_e _ _ _
                 ltac:(solve_addr) ltac:(solve_addr) ltac:(solve_addr) Hlen_lo_spec
                with "Hsstk_lo Hsstk5 Hsstk_hi") as "Hscsp_stk".

    (* --------------------------------------------------- *)
    (* -------------- BLOCK 1 and 2 : FETCH -------------- *)
    (* --------------------------------------------------- *)

    focus_block_lockstep 1 "Hscode_main" "Hcode_main" as a_fetch1 Ha_fetch1
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcode $Hscode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher Hsimport_switcher".
    iNext ; iIntros "(Hj & HPC & HsPC & Hctp & Hsctp & Hct0 & Hsct0 & Hct1 & Hsct1
                      & Hcode & Hscode & Himport_switcher & Hsimport_switcher)".
    iEval (cbn) in "Hctp".
    iEval (cbn) in "Hsctp".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    focus_block_lockstep 2 "Hscode_main" "Hcode_main" as a_fetch2 Ha_fetch2
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (fetch_spec_lockstep with
             "[- $Hspec $Hj $HPC $HsPC $Hct1 $Hsct1 $Hct0 $Hsct0 $Hcs0 $Hscs0 $Hcode $Hscode
                 $Himport_B_f $Hsimport_B_f]"); eauto.
    { solve_addr. }
    iNext ; iIntros "(Hj & HPC & HsPC & Hct1 & Hsct1 & Hct0 & Hsct0 & Hcs0 & Hscs0
                      & Hcode & Hscode & Himport_B_f & Hsimport_B_f)".
    iEval (cbn) in "Hct1".
    iEval (cbn) in "Hsct1".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

    (* --------------------------------------------------- *)
    (* ----------------- BLOCK 3: CALL B ----------------- *)
    (* --------------------------------------------------- *)

    focus_block_lockstep 3 "Hscode_main" "Hcode_main" as a_callB Ha_callB
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Jalr cra ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Prepare the argument registers for the call to the adversary *)
    iExtractList "Hrmap" [ca0;ca1;ca2;ca3;ca4;ca5]
      as ["Hca0";"Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].
    iDestruct "Hca0" as "(Hca0 & Hsca0 & ->)".
    iDestruct "Hca1" as "(Hca1 & Hsca1 & ->)".
    iDestruct "Hca2" as "(Hca2 & Hsca2 & ->)".
    iDestruct "Hca3" as "(Hca3 & Hsca3 & ->)".
    iDestruct "Hca4" as "(Hca4 & Hsca4 & ->)".
    iDestruct "Hca5" as "(Hca5 & Hsca5 & ->)".
    iPoseProof (arg_rmap_zero_interp W_init B stack_secret_B_f_args ca0) as "Hi0".
    iPoseProof (arg_rmap_zero_interp W_init B stack_secret_B_f_args ca1) as "Hi1".
    iPoseProof (arg_rmap_zero_interp W_init B stack_secret_B_f_args ca2) as "Hi2".
    iPoseProof (arg_rmap_zero_interp W_init B stack_secret_B_f_args ca3) as "Hi3".
    iPoseProof (arg_rmap_zero_interp W_init B stack_secret_B_f_args ca4) as "Hi4".
    iPoseProof (arg_rmap_zero_interp W_init B stack_secret_B_f_args ca5) as "Hi5".
    iPoseProof (arg_rmap_zero_interp W_init B stack_secret_B_f_args ct0) as "Hi6".
    iDestruct (arg_rmap_prepare W_init B stack_secret_B_f_args
                with "Hca0 Hsca0 Hi0 Hca1 Hsca1 Hi1 Hca2 Hsca2 Hi2 Hca3 Hsca3 Hi3
                      Hca4 Hsca4 Hi4 Hca5 Hsca5 Hi5 Hct0 Hsct0 Hi6")
      as "Hrmap_arg".

    (* The other registers *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertList "Hrmap" [ctp].
    iInsertListSpec "Hsrmap" [ctp].

    iApply (switcher_cc_specification_diag _ W_init B with
             "[- $Hswitcher $Hspec $Hna $Hj $Hinterp_Winit_B_f $HentryB_f
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_B $Hstack_revoked_B'
              $Hcstk_frag $Hcstk_frag_spec $HK]"); eauto; iFrame "%".
    { repeat first [rewrite dom_insert_L | rewrite dom_delete_L].
      rewrite Hrmap_dom; set_solver. }
    { repeat first [rewrite dom_insert_L | rewrite dom_delete_L].
      rewrite Hrmap_dom; set_solver. }
    { apply is_arg_rmap_of. }
    { apply is_arg_rmap_of. }

    iNext.
    iIntros (W2 rmap' stk_mem' stk_mem_spec' l')
      "( _ & _ & _ & _ & _ & _ & _ & _
      & Hna & Hj & _ & _ & _ & _
      & HPC & HsPC
      & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _)".
    iEval (cbn) in "HPC".
    iEval (cbn) in "HsPC".

    (* Halt *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_halt with "[$Hspec $Hj $HsPC $Hsi]") as "(Hj & HsPC & Hsi)";
      [solve_ndisj|solve_pure|solve_pure|].
    iSpecialize ("Hscode" with "Hsi").
    (* Halt *)
    iInstr "Hcode".
    wp_end.
    iIntros "_".
    iFrame.
  Qed.

End Stack_secret.
