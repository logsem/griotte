From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary interp_weakening_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Import rules proofmode proofmode_binary register_tactics_binary map_simpl.
From griotte Require Import world_ghost_theory_binary world_interp_stack_binary stack_world_resources_binary.
From griotte Require Import switcher_preamble_binary switcher_spec_call_binary.
From griotte Require Import fetch_spec_binary switcher_spec_call_diag_binary write_only_secret_binary.

(** * Binary specification of the write-only sharing example

    Both runs execute [write_only_secret_main_code], with a different secret
    in the private data of [main] ([secret1] in the implementation run,
    [secret2] in the specification run). The specification holds for
    arbitrary secrets, and is used in both directions of the adequacy
    theorem.

    The cell holding the secret is shared with [B] as a permanent region of
    the world of [B], with the safety predicate [write_only_pred]: a pair of
    safe words, or any pair of integers. The two runs may store different
    integers in the cell. Since the capability given to [B] cannot read the
    cell, the region does not need to satisfy the read condition of the
    logical relation. *)

(** ** Safety predicate of the shared cell *)
Section Write_only_pred.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).

  (** Either a pair of safe words, or any pair of integers. *)
  Program Definition write_only_pred : V :=
    λne (W : WORLD) (C : leibnizO CmptName) (ww : leibnizO (Word * Word)),
      (interp W C ww ∨ ⌜∃ z1 z2 : Z, ww = (WInt z1, WInt z2)⌝)%I.
  Solve All Obligations with solve_proper.

  Lemma persistent_cond_write_only_pred : persistent_cond write_only_pred.
  Proof. intros WCv; apply _. Qed.

  Lemma zcond_write_only_pred C : ⊢ zcond write_only_pred C.
  Proof.
    iModIntro; iIntros (W1 W2 z1 z2) "_".
    iRight; iPureIntro; by exists z1, z2.
  Qed.

  Lemma wcond_write_only_pred C : ⊢ wcond write_only_pred C interp.
  Proof. iModIntro; iIntros (W w) "Hw"; by iLeft. Qed.

  Lemma future_priv_mono_write_only_pred_z C (z1 z2 : Z) :
    ⊢ future_priv_mono C (safeC write_only_pred) (WInt z1, WInt z2).
  Proof.
    iModIntro; iIntros (W W') "_ _".
    iRight; iPureIntro; by exists z1, z2.
  Qed.

  Lemma monoReq_write_only_pred W C a :
    std W !! a = Some Permanent →
    ⊢ monoReq W C a WO write_only_pred.
  Proof.
    intros Ha.
    rewrite /monoReq Ha.
    iIntros (w [Hw1 _] W1 W2 Hrelated) "!> [Hw | Hw]".
    - iLeft.
      iApply (interp_monotone_nl with "[//] [] Hw").
      iPureIntro.
      rewrite /canStore in Hw1.
      cbn; by destruct (isLocalWord w.1).
    - by iRight.
  Qed.

  (** The write-only capability to a permanent cell with predicate
      [write_only_pred] is safe to share. *)
  Lemma interp_write_only_cap W C (a a' : Addr) :
    (a + 1)%a = Some a' →
    std W !! a = Some Permanent →
    rel C a WO (safeC write_only_pred) -∗
    interp W C (WCap WO Global a a' a, WCap WO Global a a' a).
  Proof.
    iIntros (Ha' Hstd) "#Hrel".
    iEval (rewrite interp_diag_eq // /interp1_diag /=).
    rewrite (finz_seq_between_cons a); last solve_addr.
    rewrite (finz_seq_between_empty (a ^+ 1)%a); last solve_addr.
    iApply big_sepL_singleton.
    iExists WO, write_only_pred.
    iSplit; first done.
    iSplit; first (iPureIntro; apply persistent_cond_write_only_pred).
    iSplit; first iFrame "Hrel".
    iSplit; first (iNext; iApply zcond_write_only_pred).
    iSplit; first done.
    iSplit; first (iNext; iApply wcond_write_only_pred).
    iSplit; first (by iApply monoReq_write_only_pred).
    done.
  Qed.

End Write_only_pred.

(** ** Specification of [main] *)
Section Write_only_secret.
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

  Lemma write_only_secret_spec

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

    let imports := write_only_secret_main_imports B_f in

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length write_only_secret_main_code)%a ->

    (cgp_b + length (write_only_secret_main_data secret1))%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    cgp_b ∉ dom (std W_init) ->

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
      ∗ codefrag pc_a write_only_secret_main_code
      ∗ spec_codefrag pc_a write_only_secret_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ write_only_secret_main_data secret1 ]]
      ∗ [[ cgp_b , cgp_e ]] ↣ₐ [[ write_only_secret_main_data secret2 ]]
      ∗ [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
      ∗ [[ csp_b , csp_e ]] ↣ₐ [[ stk_mem_spec ]]

      ∗ world_interp W_init B
      ∗ interp_continuation stk Ws Cs
      ∗ cstack_frag (map fst stk)
      ∗ cstack_frag_spec (map snd stk)

      ∗ interp W_init B (WSealed ot_switcher B_f, WSealed ot_switcher B_f)
      ∗ (WSealed ot_switcher B_f) ↦□ₑ write_only_secret_B_f_args
      ∗ StackRevokedResources W_init B (finz.seq_between csp_b csp_e)

      ⊢ WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (Hrmap_dom HsubBounds Hcgp_contiguous Himports_contiguous Hcgp_b Hrevoked_stack)
      "(#Hswitcher & #Hspec & Hna & Hj
      & HPC & HsPC & Hcgp & Hscgp & Hcsp & Hscsp & Hrmap
      & Himports_main & Hsimports_main & Hcode_main & Hscode_main
      & Hcgp_main & Hscgp_main & Hcsp_stk & Hscsp_stk
      & Hworld_interp_B & HK & Hcstk_frag & Hcstk_frag_spec
      & #Hinterp_Winit_B_f & #HentryB_f & #Hstack_revoked_B)".
    codefrag_facts "Hcode_main".
    rewrite /write_only_secret_main_data /= in Hcgp_contiguous.
    rewrite /write_only_secret_main_imports /= in Himports_contiguous.

    (* Extract the needed registers from the register map *)
    iExtractList "Hrmap" [ctp;ct0;ct1;cs0;cs1;cra;ca0]
      as ["Hctp";"Hct0";"Hct1";"Hcs0";"Hcs1";"Hcra";"Hca0"].
    iDestruct "Hctp" as "(Hctp & Hsctp & ->)".
    iDestruct "Hct0" as "(Hct0 & Hsct0 & ->)".
    iDestruct "Hct1" as "(Hct1 & Hsct1 & ->)".
    iDestruct "Hcs0" as "(Hcs0 & Hscs0 & ->)".
    iDestruct "Hcs1" as "(Hcs1 & Hscs1 & ->)".
    iDestruct "Hcra" as "(Hcra & Hscra & ->)".
    iDestruct "Hca0" as "(Hca0 & Hsca0 & ->)".

    (* Extract the secret *)
    iDestruct (region_pointsto_cons with "Hcgp_main") as "[Hsecret _]".
    { exact Hcgp_contiguous. }
    { solve_addr. }
    iDestruct (spec_region_pointsto_cons with "Hscgp_main") as "[Hssecret _]".
    { exact Hcgp_contiguous. }
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

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* --------------------------------------------------- *)
    (* ------------ BLOCK 0 : WRITE-ONLY CAP ------------- *)
    (* --------------------------------------------------- *)

    focus_block_0_lockstep "Hscode_main" "Hcode_main" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* Mov ca0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Restrict ca0 (encodePermPair (WO, Global)) *)
    iInstr_lockstep "Hscode" "Hcode".
    1,4: by rewrite decode_encode_permPair_inv.
    1-4: solve_pure.

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode_main" "Hcode_main".

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

    (* Share the secret cell with B, as a permanent region whose two runs
       may hold different integers *)
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hcsp_stk $Hsecret]") as "%Hcgp_b_stk".
    iDestruct ( init_PermRes W_init B cgp_b WO (safeC write_only_pred) (WInt secret1, WInt secret2)
                with "[] [$Hsecret] [$Hssecret] []" ) as "Hcgp_b".
    { done. }
    { iApply future_priv_mono_write_only_pred_z. }
    { iRight; iPureIntro; by eexists _, _. }
    iMod (world_interp_extend_perm with "Hworld_interp_B Hcgp_b")
      as "(Hworld_interp_B & #Hrel_cgp_b)"; auto.

    set (W1 := (<s[cgp_b:=Permanent]s>W_init)).
    assert (related_sts_priv_world W_init W1) as HWinit_priv_W1.
    { subst W1; eapply related_sts_priv_world_fresh_Permanent. }

    iAssert (interp W1 B (WCap WO Global cgp_b cgp_e cgp_b,
                          WCap WO Global cgp_b cgp_e cgp_b)) as "#Hinterp_W1_wo".
    { iApply (interp_write_only_cap with "Hrel_cgp_b"); first done.
      subst W1; by rewrite /= lookup_insert_eq.
    }

    (* Prove that the adversary's entry point is safe to share *)
    iAssert (interp W1 B (WSealed ot_switcher B_f, WSealed ot_switcher B_f)) as "#Hinterp_W1_B_f".
    { iApply (interp_monotone_sd with "[%] Hinterp_Winit_B_f"); eauto. }

    (* Prepare the argument registers for the call to the adversary *)
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5] as ["Hca1";"Hca2";"Hca3";"Hca4";"Hca5"].
    iDestruct "Hca1" as "(Hca1 & Hsca1 & ->)".
    iDestruct "Hca2" as "(Hca2 & Hsca2 & ->)".
    iDestruct "Hca3" as "(Hca3 & Hsca3 & ->)".
    iDestruct "Hca4" as "(Hca4 & Hsca4 & ->)".
    iDestruct "Hca5" as "(Hca5 & Hsca5 & ->)".
    iPoseProof (arg_rmap_interp W1 B write_only_secret_B_f_args ca0 with "Hinterp_W1_wo") as "Hi0".
    iPoseProof (arg_rmap_zero_interp W1 B write_only_secret_B_f_args ca1) as "Hi1".
    iPoseProof (arg_rmap_zero_interp W1 B write_only_secret_B_f_args ca2) as "Hi2".
    iPoseProof (arg_rmap_zero_interp W1 B write_only_secret_B_f_args ca3) as "Hi3".
    iPoseProof (arg_rmap_zero_interp W1 B write_only_secret_B_f_args ca4) as "Hi4".
    iPoseProof (arg_rmap_zero_interp W1 B write_only_secret_B_f_args ca5) as "Hi5".
    iPoseProof (arg_rmap_zero_interp W1 B write_only_secret_B_f_args ct0) as "Hi6".
    iDestruct (arg_rmap_prepare W1 B write_only_secret_B_f_args
                with "Hca0 Hsca0 Hi0 Hca1 Hsca1 Hi1 Hca2 Hsca2 Hi2 Hca3 Hsca3 Hi3
                      Hca4 Hsca4 Hi4 Hca5 Hsca5 Hi5 Hct0 Hsct0 Hi6")
      as "Hrmap_arg".

    (* The other registers *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsrmap]".
    iDestruct (big_sepM_sep with "Hsrmap") as "[Hsrmap _]".
    iInsertList "Hrmap" [ctp].
    iInsertListSpec "Hsrmap" [ctp].

    (* The stack is still revoked in the world extended with the secret cell *)
    assert ( revoked_addresses W1 (finz.seq_between csp_b csp_e) ) as Hrevoked_stack_W1.
    { rewrite /revoked_addresses Forall_forall.
      rewrite /revoked_addresses Forall_forall in Hrevoked_stack.
      intros a Ha; cbn in *.
      rewrite lookup_insert_ne; last (intros ->; set_solver+Hcgp_b_stk Ha).
      by apply Hrevoked_stack.
    }
    iDestruct (StackRevokedResources_mono_priv with "Hstack_revoked_B") as "Hstack_revoked_B_W1"; eauto.

    iApply (switcher_cc_specification_diag _ W1 B with
             "[- $Hswitcher $Hspec $Hna $Hj
              $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcsp $Hscsp $Hct1 $Hsct1
              $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hrmap $Hsrmap $Hrmap_arg
              $Hcsp_stk $Hscsp_stk $Hworld_interp_B $Hstack_revoked_B_W1
              $Hcstk_frag $Hcstk_frag_spec
              $Hinterp_W1_B_f $HentryB_f $HK]"); eauto; iFrame "%".
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

End Write_only_secret.
